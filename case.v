(* Case tactics derived from Pierce et al, Software Foundations, http://softwarefoundations.cis.upenn.edu *)
Require Export String.
Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name
  | fail 1 "because we are working on a different case." ].

Ltac Case name := Case_aux case name.
Ltac SCase name := Case_aux subcase name.
Ltac SSCase name := Case_aux subsubcase name.
Ltac SSSCase name := Case_aux subsubsubcase name.
Ltac SSSSCase name := Case_aux subsubsubsubcase name.
Ltac SSSSSCase name := Case_aux subsubsubsubsubcase name.
