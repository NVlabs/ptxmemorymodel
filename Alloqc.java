import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4SolutionReader;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;

import java.util.List;
import java.util.ArrayList;
import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.HashMap;
import java.util.Deque;
import java.util.LinkedList;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.SubsetSig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.ast.*;

public class Alloqc {
    private static final int recursion_depth = 10;

    private static Set<String> emptySet = new HashSet<String>();
    private static List<String> sigs = new ArrayList<String>();
    private static List<String> rels = new ArrayList<String>();

    private static Map<String, Func> all_funs = new HashMap<String, Func>();
    private static Set<String> funs_with_deps_satisfied = new HashSet<String>();

    private static Map<String, Set<String> > dependees =
        new HashMap<String, Set<String> >();

    private static Map<String, Set<String> > dependents =
        new HashMap<String, Set<String> >();

    private static List<String> axioms = new ArrayList<String>();

    private static void debug_msg(String s) {
        //System.out.println("(* DEBUG: " + s + " *)");
    }

    private static void error(String s) {
        System.err.println("(* Error: " + s + " *)");
        System.out.println("(* Error: " + s + " *)");
        System.err.println("Terminating due to unexpected error\n");
        System.exit(1);
    }

    private static String make_printable(String s) {
        return s.replaceAll("this/", "").replaceAll("/", "__").replaceAll("\\$", "_");
    }

    private static String make_printable(Sig s) {
        return make_printable(s.toString());
    }

    private static String f_of_instance(Sig s) {
        if (s.builtin) {
            return make_printable(s);
        } else {
            return "(" + make_printable(s) + " _i)";
        }
    }

    /* Find a dependency cycle by doing naive depth-first search.  This node
     * will be the first in the mutually recursive "Fixpoint ... with ..." list */
    private static Set<String> FindCycle(Deque<String> path) {
        debug_msg("Searching for node in dependency cycle: " + path);

        // Continue the search
        for (String dependent : dependents.get(path.getLast())) {

            if (path.contains(dependent)) {
                // Success: found a cycle
                debug_msg("Found node in dependency cycle: " + dependent);

                // Retrace the path to find the cycle, but drop any nodes from
                // earlier in the path which aren't part of the cycle
                Set<String> cycle_nodes = new HashSet<String>();
                while (path.size() > 0) {
                    String i = path.getLast();
                    cycle_nodes.add(i);
                    if (i.equals(dependent)) {
                        break;
                    }
                    path.removeLast();
                }
                return cycle_nodes;
            } else {
                // Recurse depth-first
                path.addLast(dependent);
                Set<String> r = FindCycle(path);

                // If recursion found a cycle, return it.
                if (r.size() > 0) {
                    return r;
                }
                // Else, back up a step and try the next branch
                else {
                    path.removeLast();
                }
            }
        }

        // no cycle found along this path
        return new HashSet<String>(); // empty set
    }

    private static void Emit(String f, Set<String> recursive_funs, boolean first) {
        // Emit the appropriate keyword: Definition, Fixpoint, with, etc.
        String body = "";
        boolean is_recursive = recursive_funs.contains(f);
        if (is_recursive) {
            if (first) {
                body += "Fixpoint";
            } else {
                body += "with";
            }
            body += " _rec_" + make_printable(f) + " (_recursion_depth : nat) (_i : Instance) ";
        } else {
            body += "Definition " + make_printable(f) + " (_i : Instance) ";
        }

        // FIXME
        Func func = all_funs.get(f);
        if (func == null) {
            if (recursive_funs.contains(f)) {
                debug_msg("FIXME already emitted recursive function " + f);
                funs_with_deps_satisfied.remove(f);
                return;
            } else {
                debug_msg("FIXME null function " + f);
                funs_with_deps_satisfied.remove(f);
                return;
            }
        }

        // Emit the function arguments
        for (Decl d : func.decls) {
            for (ExprHasName n : d.names) {
                body += n + " ";
            }
        }

        // Start the body
        body += ":=\n";
        
        // Emit the original Alloy definition within a comment, for comparison
        body += "(* " + func.getBody() + " *)\n";

        // If the function is recursive, the outermost contents should be a check
        // of the recursion depth.  The match is closed separately below.
        if (is_recursive) {
            body += "match _recursion_depth with\n";
            body += "| 0 => fun _ => False (* RECURSION LIMIT EXCEEDED! *)\n";
            body += "| S _recursion_depth' =>\n";
        }

        // Emit the actual body of the function
        body += ExprToCoq(recursive_funs, func.getBody()).a;

        // Close the recursion handler, if necessary
        if (is_recursive) {
            body += "\nend\n";
        } else {
            body += ".\n";
        }

        // If the body contains something that we don't currently support, then
        // emit it within a comment so it can be examined.  Otherwise, just
        // print it out
        if (body.contains("?)")) {
            debug_msg("some feature not yet supported");
            System.out.println("(*\n" + body + "*)\n");
        } else if (f.contains("integer")) {
            debug_msg("integers not yet supported");
            System.out.println("(*\n" + body + "*)\n");
        } else {
            System.out.println(body);
        }

        // Now that this function has been emitted, remove any dependencies
        // of other functions on this one
        if (dependees.keySet().contains(f)) {
            for (String dependent : dependees.get(f)) {
                Set<String> r = dependents.get(dependent);
                r.remove(f);
                debug_msg("removing dependency of " + dependent + " on " + f);
                if (r.isEmpty()) {
                    funs_with_deps_satisfied.add(dependent);
                    dependents.remove(dependent);
                    debug_msg("     " + dependent + " is now ready to be emitted");
                } else {
                    dependents.put(dependent, r);
                }
            }
        } else {
            debug_msg("no dependencies on " + f);
        }

        // Remove it from the list of functions that need to be emitted
        if (is_recursive) {
            // ...unless it's a recursive function.  In that case, leave it in
            // all_funs so we can emit the non-recursive version
        } else {
            all_funs.remove(f);
        }
        funs_with_deps_satisfied.remove(f);
    }

    private static Pair<String, Set<String>> ExprToCoq(Set<String> recursive_funs, Expr e) {
        if (e instanceof ExprUnary) {
            ExprUnary e_u = (ExprUnary)e;
            Pair<String, Set<String> > r = ExprToCoq(recursive_funs, e_u.sub);
            if (e_u.op == ExprUnary.Op.NOOP) {
                return r;
            } else if (e_u.op == ExprUnary.Op.ONE) {
                return new Pair<String, Set<String> >("(one " + r.a + ")", r.b);
            } else if (e_u.op == ExprUnary.Op.LONE) {
                return new Pair<String, Set<String> >("(lone " + r.a + ")", r.b);
            } else if (e_u.op == ExprUnary.Op.SOME) {
                return new Pair<String, Set<String> >("(some " + r.a + ")", r.b);
            } else if (e_u.op == ExprUnary.Op.ONEOF) {
                return new Pair<String, Set<String> >("(oneof " + r.a + ")", r.b);
            } else if (e_u.op == ExprUnary.Op.LONEOF) {
                return new Pair<String, Set<String> >("(loneof " + r.a + ")", r.b);
            } else if (e_u.op == ExprUnary.Op.SETOF) {
                return new Pair<String, Set<String> >("(setof " + r.a + ")", r.b);
            } else if (e_u.op == ExprUnary.Op.NO) {
                return new Pair<String, Set<String> >("(no " + r.a + ")", r.b);
            } else if (e_u.op == ExprUnary.Op.NOT) {
                return new Pair<String, Set<String> >("(~ " + r.a + ")", r.b);
            } else if (e_u.op == ExprUnary.Op.TRANSPOSE) {
                int n = e_u.type().arity() - 1;
                if (n < 0) {
                    error("Range argument n = " + n + "\nExpr = " + e);
                }
                return new Pair<String, Set<String> >("(transpose (n:=" + n + ") " + r.a + ")", r.b);
            } else if (e_u.op == ExprUnary.Op.CLOSURE) {
                return new Pair<String, Set<String> >("(tc " + r.a + ")", r.b);
            } else if (e_u.op == ExprUnary.Op.RCLOSURE) {
                return new Pair<String, Set<String> >("(rtc " + r.a + ")", r.b);
            } else if (e_u.op == ExprUnary.Op.CARDINALITY) {
                int n = e_u.sub.type().arity();
                return new Pair<String, Set<String> >("(cardinality " + n + " " + r.a + ")", r.b);
            } else if (e_u.op == ExprUnary.Op.CAST2INT || e_u.op == ExprUnary.Op.CAST2SIGINT) {
                return r;
            } else {
                return new Pair<String, Set<String> >("(U?" + e_u.op + "? " + r.a + " ?)", r.b);
            }
        } else if (e instanceof ExprBinary) {
            ExprBinary e_b = (ExprBinary)e;
            Pair<String, Set<String> > l = ExprToCoq(recursive_funs, e_b.left);
            Pair<String, Set<String> > r = ExprToCoq(recursive_funs, e_b.right);
            Set<String> d = new HashSet<String>(l.b);
            d.addAll(r.b);
            if (e_b.op == ExprBinary.Op.JOIN) {
                int m = e_b.left.type().arity() - 1;
                int n = e_b.right.type().arity() - 1;
                return new Pair<String, Set<String> >("(join (m:=" + m + ") (n:=" + n + ") " + l.a + " " + r.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.IMPLIES) {
                return new Pair<String, Set<String> >("(" + l.a + " -> " + r.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.RANGE) {
                int m = e_b.left.type().arity() - 1;
                if (m < 0) {
                    error("Range argument m = " + m + "\nExpr = " + e);
                }
                int n = e_b.right.type().arity() - 1;
                if (n < 0) {
                    error("Range argument n = " + n + "\nExpr = " + e);
                }
                return new Pair<String, Set<String> >("(range (m:=" + m + ") (n:=" + n + ") " + l.a + " " + r.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.DOMAIN) {
                return new Pair<String, Set<String> >("(domain " + l.a + " " + r.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.IN) {
                return new Pair<String, Set<String> >("(inside " + r.a + " " + l.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.NOT_IN) {
                return new Pair<String, Set<String> >("(~inside " + r.a + " " + l.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.MINUS) {
                return new Pair<String, Set<String> >("(difference " + l.a + " " + r.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.PLUS) {
                int n = e_b.left.type().arity(); // m should be the same
                return new Pair<String, Set<String> >("(union (n:=" + n + ") " + l.a + " " + r.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.INTERSECT) {
                return new Pair<String, Set<String> >("(intersect " + l.a + " " + r.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.ARROW) {
                int m = e_b.left.type().arity() - 1;
                if (m < 0) {
                    error("Range argument m = " + m + "\nExpr = " + e);
                }
                int n = e_b.right.type().arity() - 1;
                if (n < 0) {
                    error("Range argument n = " + n + "\nExpr = " + e);
                }
                return new Pair<String, Set<String> >("(arrow (m:=" + m + ") (n:=" + n + ") " + l.a + " " + r.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.IFF) {
                return new Pair<String, Set<String> >("(iff " + l.a + " " + r.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.EQUALS) {
                if (e_b.left.type().is_int() || e_b.left.type().is_small_int()) {
                    return new Pair<String, Set<String> >("(" + l.a + " = " + r.a + ")", d);
                } else {
                    return new Pair<String, Set<String> >("(equal (n:=" + e_b.left.type().arity() + ") " + l.a + " " + r.a + ")", d);
                }
            } else if (e_b.op == ExprBinary.Op.NOT_EQUALS) {
                if (e_b.left.type().is_int() || e_b.left.type().is_small_int()) {
                    return new Pair<String, Set<String> >("(" + l.a + " <> " + r.a + ")", d);
                } else {
                    return new Pair<String, Set<String> >("(~equal (n:=" + e_b.left.type().arity() + ") " + l.a + " " + r.a + ")", d);
                }
            } else if (e_b.op == ExprBinary.Op.LTE) {
                return new Pair<String, Set<String> >("(le " + l.a + " " + r.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.GTE) {
                return new Pair<String, Set<String> >("(ge " + l.a + " " + r.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.LT) {
                return new Pair<String, Set<String> >("(lt " + l.a + " " + r.a + ")", d);
            } else if (e_b.op == ExprBinary.Op.GT) {
                return new Pair<String, Set<String> >("(gt " + l.a + " " + r.a + ")", d);
            } else {
                return new Pair<String, Set<String> >("(B?" + e_b.op + "? " + e_b + " ?)", d);
            }
        } else if (e instanceof ExprQt) {
            ExprQt e_q = (ExprQt)e;
            Set<String> dep = new HashSet<String>();
            String s = "";
            String parens = "";
            if (e_q.op == ExprQt.Op.ALL) {
                for (Decl d : e_q.decls) {
                    Set<String> vars = new HashSet<String>();
                    for (ExprHasName n : d.names) {
                        Pair<String, Set<String> > r = ExprToCoq(recursive_funs, d.expr);
                        dep.addAll(r.b);
                        // Quantified differently depending on the arity?
                        if (d.expr.type().arity() == 1) {
                          s += "(forall " + n + ", " + r.a + " " + n + " -> ";
                        } else {
                          s += "(forall " + n + ", inside " + r.a + " " + n + " -> ";
                        }
                        if (d.disjoint != null) {
                            for (String v : vars) {
                                s += n + " <> " + v + " ->";
                            }
                            vars.add(n.toString());
                        }
                        parens += ")";
                    }
                }
                Pair<String, Set<String> > r = ExprToCoq(recursive_funs, e_q.sub);
                dep.addAll(r.b);
                s += r.a + parens;
                return new Pair<String, Set<String> >(s, dep);
            } else if (e_q.op == ExprQt.Op.SOME) {
                for (Decl d : e_q.decls) {
                    for (ExprHasName n : d.names) {
                        Pair<String, Set<String> > r = ExprToCoq(recursive_funs, d.expr);
                        // Quantified differently depending on the arity?
                        if (d.expr.type().arity() == 1) {
                            s += "(exists (" + n + " : Relation 1), (" + r.a + " " + n + ") /\\";
                        } else if (d.expr.type().arity() == 2) {
                            s += "(exists (" + n + " : Relation 2), (inside " + r.a + " " + n + ") /\\";
                        } else {
                            s += "(exists (? " + n + " : ? ?), (" + r.a + " " + n + ") /\\";
                        }
                        parens += ")";
                    }
                }
                Pair<String, Set<String> > r = ExprToCoq(recursive_funs, e_q.sub);
                dep.addAll(r.b);
                s += r.a + parens;
                return new Pair<String, Set<String> >(s, dep);
            } else if (e_q.op == ExprQt.Op.NO) {
                for (Decl d : e_q.decls) {
                    for (ExprHasName n : d.names) {
                        Pair<String, Set<String> > r = ExprToCoq(recursive_funs, d.expr);
                        // Quantified differently depending on the arity?
                        if (d.expr.type().arity() == 1) {
                            s += "(~exists (" + n + " : Relation 1), (" + r.a + " " + n + ") /\\";
                        } else if (d.expr.type().arity() == 2) {
                            s += "(~exists (" + n + " : Relation 2), (inside " + r.a + " " + n + ") /\\";
                        } else {
                            s += "(~exists (? " + n + " : ? ?), (" + r.a + " " + n + ") /\\";
                        }
                        parens += ")";
                    }
                }
                Pair<String, Set<String> > r = ExprToCoq(recursive_funs, e_q.sub);
                dep.addAll(r.b);
                s += r.a + parens;
                return new Pair<String, Set<String> >(s, dep);
            } else if (e_q.op == ExprQt.Op.ONE) {
                for (Decl d : e_q.decls) {
                    for (ExprHasName n : d.names) {
                        Pair<String, Set<String> > r = ExprToCoq(recursive_funs, d.expr);
                        dep.addAll(r.b);
                        s += "(exists! " + n + ", (" + r.a + " " + n  + ") /\\ ";
                        parens += ")";
                    }
                }
                Pair<String, Set<String> > r = ExprToCoq(recursive_funs, e_q.sub);
                dep.addAll(r.b);
                s += r.a + parens;
                return new Pair<String, Set<String> >(s, dep);
            } else if (e_q.op == ExprQt.Op.LONE) {
                for (Decl d : e_q.decls) {
                    for (ExprHasName n : d.names) {
                        Pair<String, Set<String> > r = ExprToCoq(recursive_funs, d.expr);
                        dep.addAll(r.b);
                        s += "(unique_if (fun " + n + " => (" + r.a + " " + n + ") /\\ ";
                        parens += "))";
                    }
                }
                Pair<String, Set<String> > r = ExprToCoq(recursive_funs, e_q.sub);
                dep.addAll(r.b);
                s += r.a + parens;
                return new Pair<String, Set<String> >(s, dep);
            } else {
                return new Pair<String, Set<String> >("(Q? " + e_q.op + " : " + e_q + " ?)", dep);
            }
        } else if (e instanceof ExprList) {
            ExprList e_l = (ExprList)e;
            Set<String> dep = new HashSet<String>();
            if (e_l.op == ExprList.Op.AND) {
                String s = "(";
                boolean first = true;
                for (Expr arg : e_l.args) {
                    if (first) {
                        first = false;
                    } else {
                        s += " /\\";
                    }
                    Pair<String, Set<String> > r = ExprToCoq(recursive_funs, arg);
                    dep.addAll(r.b);
                    s += " " + r.a;
                }
                s += ")";
                return new Pair<String, Set<String> >(s, dep);
            } else if (e_l.op == ExprList.Op.OR) {
                String s = "(";
                boolean first = true;
                for (Expr arg : e_l.args) {
                    if (first) {
                        first = false;
                    } else {
                        s += " \\/";
                    }
                    Pair<String, Set<String> > r = ExprToCoq(recursive_funs, arg);
                    dep.addAll(r.b);
                    s += " " + r.a;
                }
                s += ")";
                return new Pair<String, Set<String> >(s, dep);
            } else {
                return new Pair<String, Set<String> >("(?L? " + e_l + " ?)", dep);
            }
        } else if (e instanceof ExprITE) {
            ExprITE e_i = (ExprITE)e;
            Set<String> dep = new HashSet<String>();
            Pair<String, Set<String> > c = ExprToCoq(recursive_funs, e_i.cond);
            dep.addAll(c.b);
            Pair<String, Set<String> > l = ExprToCoq(recursive_funs, e_i.left);
            dep.addAll(l.b);
            Pair<String, Set<String> > r = ExprToCoq(recursive_funs, e_i.right);
            dep.addAll(r.b);
            String s = "(ite " + c.a + " " + l.a + " " + r.a + ")";
            return new Pair<String, Set<String> >(s, dep);
        } else if (e instanceof ExprHasName) {
            ExprHasName e_h = (ExprHasName)e;
            String s;
            if (e_h instanceof ExprVar) {
                s = make_printable(e_h.label);
            } else if (e_h instanceof Sig.Field) {
                s = "(" + make_printable(((Sig.Field)e_h).sig) + "__" + e_h.label + " _i)";
            } else {
                s = " (* unknown ExprVar " + e_h + " *) ";
            }
            return new Pair<String, Set<String> >(s, emptySet);
        } else if (e instanceof ExprConstant) {
            ExprConstant e_c = (ExprConstant)e;
            switch (e_c.op) {
                case EMPTYNESS:
                case IDEN:
                    return new Pair<String, Set<String> >(e_c.op.toString(), emptySet);
                case NEXT:
                    return new Pair<String, Set<String> >("S", emptySet);
                case NUMBER:
                    return new Pair<String, Set<String> >(e_c.num + "", emptySet);
                case TRUE:
                    return new Pair<String, Set<String> >("True", emptySet);
                case FALSE:
                    return new Pair<String, Set<String> >("False", emptySet);
                default:
                    return new Pair<String, Set<String> >("(C? " + e_c + " ?)", emptySet);
            }
        } else if (e instanceof ExprCall) {
            ExprCall e_c = (ExprCall)e;
            Set<String> dep = new HashSet<String>();
            dep.add(make_printable(e_c.fun.label));
            String s = "(";
            if (recursive_funs.contains(make_printable(e_c.fun.label))) {
                s += "_rec_" + make_printable(e_c.fun.label) + " " + "_recursion_depth'";
            } else {
                s += make_printable(e_c.fun.label);
            }
            s += " _i";
            for (Expr arg : e_c.args) {
                Pair<String, Set<String> > r = ExprToCoq(recursive_funs, arg);
                s += " " + r.a;
                dep.addAll(r.b);
            }
            s += ")";
            return new Pair<String, Set<String> >(s, dep);
        } else if (e instanceof ExprLet) {
            ExprLet e_l = (ExprLet)e;
            Pair<String, Set<String> > l = ExprToCoq(recursive_funs, e_l.expr);
            Pair<String, Set<String> > r = ExprToCoq(recursive_funs, e_l.sub);
            Set<String> dep = new HashSet<String>();
            dep.addAll(l.b);
            dep.addAll(r.b);
            String s = "(let " + e_l.var.label + " := " + l.a + " in " + r.a + ")";
            return new Pair<String, Set<String> >(s, dep);
        } else if (e instanceof Sig) {
            Sig e_s = (Sig)e;
            return new Pair<String, Set<String> >(f_of_instance(e_s), emptySet);
        } else {
            return new Pair<String, Set<String> >("(?? " + e + " ?)", emptySet);
        }
    }

    public static void main(String[] args) throws Exception {
        A4Reporter rep = new A4Reporter();
        String filename = args[0];
        CompModule world = CompUtil.parseEverything_fromFile(rep, null, filename);

        // The original "modules" is read-only
        List<CompModule> modules = world.getAllReachableModules().makeCopy();
        modules.add(world);

        // Record all the sigs and relations
        for (Sig sig : world.getAllReachableSigs()) {
            if (!sig.builtin) {
                sigs.add(make_printable(sig));
            }

            for (Decl d : sig.getFieldDecls()) {
                for (ExprHasName n : d.names) {
                    // To avoid name conflicts, prepend the relation name with
                    // the sig name
                    String s = make_printable(sig) + "__" + n.label;
                    rels.add(s);
                }
            }

            if (sig instanceof PrimSig) {
                if (sig.builtin) {
                    continue;
                }
                PrimSig parent = ((PrimSig)sig).parent;
                if (parent == Sig.UNIV) {
                    boolean found = false;
                    for (Sig sig2 : world.getAllReachableSigs()) {
                        if (!(sig2 instanceof PrimSig)) {
                            continue;
                        }
                        if (sig2.builtin) {
                            continue;
                        }
                        if (((PrimSig)sig2).parent != Sig.UNIV) {
                            continue;
                        }
                        if (found) {
                            String s = "Axiom _" + make_printable(sig) + "_disjoint_" + make_printable(sig2) + " :\n" +
                                "forall (_i : Instance) x, " + f_of_instance(sig) + " x -> ~(" + f_of_instance(sig2) + " x).\n";
                            axioms.add(s);
                            s = "Axiom _" + make_printable(sig2) + "_disjoint_" + make_printable(sig) + " :\n" +
                                "forall (_i : Instance) x, " + f_of_instance(sig2) + " x -> ~(" + f_of_instance(sig) + " x).\n";
                            axioms.add(s);
                        }
                        if (sig.label.equals(sig2.label)) {
                            found = true;
                        }
                    }
                }
                if (parent != null) {
                    String s = "Axiom _" + make_printable(parent) + "_subsig_" + make_printable(sig) + " :\n" +
                            "  forall (_i : Instance) x, " + f_of_instance(sig) + " x -> " + f_of_instance(parent) + " x.\n";
                    axioms.add(s);

                    for (PrimSig c1 : ((PrimSig)sig).children()) {
                        if (c1.builtin) {
                            continue;
                        }
                        boolean found = false;
                        for (PrimSig c2 : ((PrimSig)sig).children()) {
                            if (c2.builtin) {
                                continue;
                            }
                            if (found) {
                                s = "Axiom _" + make_printable(c1) + "_disjoint_" + make_printable(c2) + " :\n" +
                                    "  forall (_i : Instance) x, " + f_of_instance(c1) + " x -> ~(" + f_of_instance(c2) + " x).\n";
                                axioms.add(s);
                                s = "Axiom _" + make_printable(c2) + "_disjoint_" + make_printable(c1) + " :\n" +
                                    "  forall (_i : Instance) x, " + f_of_instance(c2) + " x -> ~(" + f_of_instance(c1) + " x).\n";
                                axioms.add(s);
                            }
                            if (c1 == c2) {
                                found = true;
                            }
                        }
                    }
                }
                if (sig.isAbstract != null) {
                    String s = "Axiom _" + make_printable(sig) + "_abstract :\n" +
                        "  forall (_i : Instance) x, " + make_printable(sig) + " _i x -> ";
                    String last = "False";
                    String parens = "";
                    for (PrimSig c : ((PrimSig)sig).children()) {
                        if (!last.equals("False")) {
                            s += "(union " + last + " ";
                            parens += ")";
                        }
                        last = "(" + make_printable(c) + " _i)";
                    }
                    s += last + parens + " x.\n";
                    axioms.add(s);
                }
            } else {
                debug_msg("skipping non-primitive sig " + sig);
            }
        }

        Set<String> axioms_generated = new HashSet<String>();
        for (CompModule m : modules) {
            for (Func func : m.getAllFunc()) {
                all_funs.put(make_printable(func.label), func);
                Pair<String, Set<String> > r = ExprToCoq(emptySet, func.getBody());

                if (r.b.isEmpty()) {
                    funs_with_deps_satisfied.add(make_printable(func.label));
                } else {
                    for (String c : r.b) {
                        if (dependees.containsKey(c)) {
                            Set<String> v = dependees.get(c);
                            v.add(make_printable(func.label));
                            dependees.put(c, v);
                        } else {
                            Set<String> v = new HashSet<String>();
                            v.add(make_printable(func.label));
                            dependees.put(c, v);
                        }
                        if (dependents.containsKey(make_printable(func.label))) {
                            Set<String> v = dependents.get(make_printable(func.label));
                            v.add(c);
                            dependents.put(make_printable(func.label), v);
                        } else {
                            Set<String> v = new HashSet<String>();
                            v.add(c);
                            dependents.put(make_printable(func.label), v);
                        }
                    }
                }

                for (Decl d : func.decls) {
                    for (ExprHasName n : d.names) {
                        String name = "_" + make_printable(func.label) + "__arg_" + n;
                        if (axioms_generated.contains(name)) {
                            debug_msg("duplicate axiom " + name + "?");
                            continue;
                        }
                        String a = "Axiom " + name + " : forall (_i : Instance)";
                        for (Decl d2 : func.decls) {
                            for (ExprHasName n2 : d2.names) {
                                a += " " + n2;
                            }
                        }
                        if (!func.isPred) {
                            a += " _x";
                        }
                        a += ",\n  " + make_printable(func.label) + " _i";
                        for (Decl d2 : func.decls) {
                            for (ExprHasName n2 : d2.names) {
                                a += " " + n2;
                            }
                        }
                        if (!func.isPred) {
                            a += " _x";
                        }
                        a += " ->\n  inside " + (ExprToCoq(emptySet, d.expr).a) + " " + n + ".\n";
                        Expr e = d.expr;
                        while (true) {
                            // arguments of builtin type (esp. Int) are encoded as "NOOP Int"
                            if (e instanceof ExprUnary) {
                                if (((ExprUnary)e).op == ExprUnary.Op.NOOP) {
                                    e = ((ExprUnary)e).sub;
                                    continue;
                                }
                            }
                            break;
                        }
                        if (e instanceof Sig) {
                            if (((Sig)e).builtin) {
                                a = "(* skipping axiom for unsupported builtin argument type *)\n(*\n" + a + "*)\n";
                            }
                        }
                        if (ExprToCoq(emptySet, e).a.contains("?)")) {
                            a = "(* some feature not yet supported *)\n(*" + a + "*)\n";
                        } else if (func.label.contains("integer")) {
                            a = "(* some feature not yet supported *)\n(*" + a + "*)\n";
                        }
                        axioms.add(a);
                        axioms_generated.add(name);
                    }
                }
            }
        }

        int facts = 0;
        for (CompModule m : modules) {
            for (Pair<java.lang.String,Expr> f : m.getAllFacts()) {
                String name;
                if (f.a.contains("$")) {
                    // fact numbers are not unique across modules
                    name = make_printable("_" + m.getModelName() + "_fact" + facts);
                } else {
                    name = f.a;
                }

                if (axioms_generated.contains(name)) {
                    System.out.println(" (* duplicate axiom " + name + "? *)");
                    continue;
                }

                String s = "Axiom " + name + " : forall (_i : Instance),\n";
                s += "(* " + f.b + "*)\n";
                Pair<String, Set<String> > r = ExprToCoq(emptySet, f.b);
                for (String dep : r.b) {
                    s += "(* dep: " + dep + " *)\n";
                }
                s += r.a + ".\n";
                facts++;
                axioms.add(s);
                axioms_generated.add(name);
            }
        }

        System.out.println("Require Import alloy.\n");

        boolean first = true;
        System.out.println("Record Instance : Type := mkInstance {");
        Set<String> sigs_emitted = new HashSet<String>();
        for (String s : sigs) {
            if (first) {
                first = false;
            } else {
                System.out.println(";");
            }
            if (sigs_emitted.contains(s)) {
                System.out.println("  (* duplicate sig " + s + " *)");
            } else {
                System.out.print("  " + s + " : Relation 1");
                sigs_emitted.add(s);
            }
        }
        for (String r : rels) {
            System.out.println(";");
            if (sigs_emitted.contains(r)) {
                System.out.println("  (* duplicate sig " + r + " *)");
            } else {
                System.out.print("  " + r + " : Relation 2");
                sigs_emitted.add(r);
            }
        }
        System.out.println("\n}.\n");

        while (!all_funs.isEmpty()) {
            while (!funs_with_deps_satisfied.isEmpty()) {
                String f = "";
                for (String s : funs_with_deps_satisfied) {
                    f = s;
                    break;
                }
                Emit(f, emptySet, false /* don't care */);
            }

            if (all_funs.isEmpty()) {
                break;
            }

            // otherwise, we have a dependency cycle
            List<String> depth_first_search = new ArrayList<String>();
            String random_start = null;
            for (String x : all_funs.keySet()) {
                random_start = x;
                break;
            }
            Deque<String> path = new LinkedList<String>();
            path.addLast(random_start);
            Set<String> cycle = FindCycle(path);
            if (cycle.size() < 2) {
                error("Could not find dependency cycle");
            } else {
                debug_msg("(* dependency cycle is " + cycle + " *)");
            }

            // Emit the nodes in the cycle
            boolean first_in_cycle = true;
            for (String x : cycle) {
                Emit(x, cycle, first_in_cycle);
                first_in_cycle = false;
            }
            System.out.println("."); // end the Fixpoint...with...with... chain

            // now emit the non-recursive versions
            for (String x : cycle) {
                String body = "";
                body += "Definition " + make_printable(x) + " (_i : Instance) ";
                Func func = all_funs.get(x);

                for (Decl d : func.decls) {
                    for (ExprHasName n : d.names) {
                        body += n + " ";
                    }
                }

                body += ":=\n_rec_" + x + " " + recursion_depth + " _i";

                for (Decl d : func.decls) {
                    for (ExprHasName n : d.names) {
                        body += " " + n;
                    }
                }

                body += ".\n";

                System.out.println(body);
                all_funs.remove(x);
            }
        }

        for (Sig sig : world.getAllReachableSigs()) {
            if (sig.isOne != null) {
                System.out.println("Axiom _one_sig_" + make_printable(sig.label) + " : forall (_i : Instance),");
                System.out.println("one (" + make_printable(sig.label) + " _i).\n");
            }

            for (Decl d : sig.getFieldDecls()) {
                for (ExprHasName n : d.names) {
                    System.out.println("Axiom _" + make_printable(sig) + "__" + n.label + "_domain" + " : ");
                    System.out.print("forall (_i : Instance) (x : Tuple 2), " + make_printable(sig) + "__" + n.label + " _i x -> ");
                    System.out.print("(" + make_printable(sig) + " _i (fst x))");
                    System.out.println(".\n");

                    System.out.println("Axiom _" + make_printable(sig) + "__" + n.label + "_range" + " : ");
                    System.out.println("forall (_i : Instance) x, oneof (" + make_printable(sig.label) + " _i) x -> " + (ExprToCoq(emptySet, d.expr).a));

                    System.out.println(" (join (m:=0) (n:=1) x (" + make_printable(sig) + "__" + n.label + " _i)).\n");
                }
            }

            int num = 0;
            for (Expr f : sig.getFacts()) {
                System.out.println("Axiom _" + make_printable(sig.label) + "_fact" + num + " :");
                System.out.println("(* " + f + " *)");
                System.out.println("forall (_i : Instance) (this : Relation 1), oneof (" + make_printable(sig.label) + " _i) this -> " + 
                        ExprToCoq(emptySet, f) + ".\n");
                ++num;
            }
        }

        for (String a : axioms) {
            System.out.println(a);
        }

        Set<String> commands_emitted = new HashSet<String>();
        Set<String> assertions = new HashSet<String>();
        for (CompModule m : modules) {
            for (Pair<String, Expr> p : m.getAllAssertions()) {
                if (commands_emitted.contains(p.a)) {
                    debug_msg("duplicate theorem " + p.a + "?");
                } else {
                    System.out.println("Definition " + make_printable(p.a) + "_statement : Prop := forall (_i : Instance),");
                    System.out.println(ExprToCoq(emptySet, p.b) + ".\n");
                    //System.out.println("Proof.\n(* FILL ME IN *)\nAbort. (* Qed. *)\n");
                    commands_emitted.add(p.a);
                    assertions.add(p.a);
                }
            }
        }

        for (CompModule m : modules) {
            String p = m.path();
            if (!p.equals("")) {
                p += "__";
            }

            for (Command c : m.getAllCommands()) {
                String n = p + /* (c.check ? "check_" : "run_") + */ make_printable(c.label);
                if (commands_emitted.contains(n)) {
                    debug_msg("duplicate theorem " + n + "?");
                } else if (c.check) {
                    boolean emitted = false;

                    if (c.formula instanceof ExprList && ((ExprList)(c.formula)).op == ExprList.Op.AND) {
                        System.out.println("Definition " + n + "_statement : Prop := forall (_i : Instance),");

                        ExprList e_l = (ExprList)(c.formula);

                        // the actual expression to prove is the last in the list; the front of the list
                        // is filled up with the facts of the model repeated.  ignore them.
                        Expr last = null;
                        for (Expr dummy : e_l.args) {
                            last = dummy;
                        }
                        if (last != null) {
                            if (last instanceof ExprUnary && ((ExprUnary)last).op == ExprUnary.Op.NOT) {
                                ExprUnary e_u = (ExprUnary)last;
                                System.out.println("(* " + e_u.sub + " *)");
                                System.out.println(ExprToCoq(emptySet, e_u.sub).a + ".\n");
                            }
                        }
                        //System.out.println("Proof.\n(* FILL ME IN *)\nAbort. (* Qed. *)\n");

                        emitted = true;
                    } else if (c.formula instanceof ExprHasName) {
                        ExprHasName e_n = (ExprHasName)(c.formula);
                        if (assertions.contains(e_n.label)) {
                            debug_msg(e_n.label + " already emitted as an assertion");
                            emitted = true;
                        }
                    }

                    if (!emitted) {
                        System.out.println("Definition " + n + " : Prop := forall (_i : Instance),");
                        System.out.println("(* " + c.formula + " *)");
                        debug_msg("theorem to prove is not a conjunctive list ending with a negation?");
                        System.out.println(ExprToCoq(emptySet, c.formula).a + ".\n");
                        //System.out.println("Proof.\n(* FILL ME IN *)\nAbort. (* Qed. *)\n");
                    }
                } else {
                    System.out.println("Definition " + n + "_statement : Prop := exists _i,");
                    System.out.println("(* " + c.formula + " *)");
                    if (c.formula instanceof ExprHasName) {
                        System.out.println(p + ExprToCoq(emptySet, c.formula).a + " _i.\n");
                    } else {
                        debug_msg("existence theorem to prove is not a simple reference?");
                        System.out.println("" + ExprToCoq(emptySet, c.formula).a + ".\n");
                    }
                    //System.out.println("Proof.\n(* FILL ME IN *)\nAbort. (* Qed. *)\n");
                }

                commands_emitted.add(n);
            }
        }
    }
}

