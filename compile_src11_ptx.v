 (* duplicate axiom scope_inclusion? *)
Require Import alloy.

Record Instance : Type := mkInstance {
  Univ : Relation 1;
  hw__Address : Relation 1;
  hw__Scope : Relation 1;
  hw__Thread : Relation 1;
  hw__Event : Relation 1;
  hw__Fence : Relation 1;
  hw__MemoryEvent : Relation 1;
  hw__Read : Relation 1;
  hw__Write : Relation 1;
  hw__FenceAcq : Relation 1;
  hw__FenceRel : Relation 1;
  hw__FenceAcqRel : Relation 1;
  hw__FenceSC : Relation 1;
  hw__Acquire : Relation 1;
  hw__Release : Relation 1;
  hw__Barrier : Relation 1;
  hw__BarrierArrive : Relation 1;
  hw__BarrierWait : Relation 1;
  sw__Address : Relation 1;
  sw__Scope : Relation 1;
  sw__Thread : Relation 1;
  sw__MemoryOrder : Relation 1;
  sw__MemoryOrderNonAtomic : Relation 1;
  sw__MemoryOrderRelaxed : Relation 1;
  sw__MemoryOrderAcquire : Relation 1;
  sw__MemoryOrderRelease : Relation 1;
  sw__MemoryOrderAcqRel : Relation 1;
  sw__MemoryOrderSeqCst : Relation 1;
  sw__Event : Relation 1;
  sw__MemoryEvent : Relation 1;
  sw__Write : Relation 1;
  sw__Read : Relation 1;
  sw__Fence : Relation 1;
  hw__Scope__subscope : Relation 2;
  hw__Thread__start : Relation 2;
  hw__Event__po : Relation 2;
  hw__Event__scope : Relation 2;
  hw__MemoryEvent__address : Relation 2;
  hw__MemoryEvent__observation : Relation 2;
  hw__Read__rmw : Relation 2;
  hw__Read__dep : Relation 2;
  hw__Write__rf : Relation 2;
  hw__Write__co : Relation 2;
  hw__FenceSC__sc : Relation 2;
  hw__BarrierArrive__synchronizes : Relation 2;
  sw__Address__addrmap : Relation 2;
  sw__Scope__subscope : Relation 2;
  sw__Scope__scopemap : Relation 2;
  sw__Thread__start : Relation 2;
  sw__Event__map : Relation 2;
  sw__Event__sb : Relation 2;
  sw__Event__memory_order : Relation 2;
  sw__Event__scope : Relation 2;
  sw__MemoryEvent__address : Relation 2;
  sw__Write__rf : Relation 2;
  sw__Write__mo : Relation 2;
  sw__Read__rmw : Relation 2
}.

Definition sw__rb (_i : Instance) :=
(* ~ (sw/Write <: rf) . (sw/Write <: mo) + sw/Read - sw/Write . (sw/Write <: rf) <: (sw/MemoryEvent <: address) . ~ (sw/MemoryEvent <: address) :> sw/Write *)
(union (n:=2) (join (m:=1) (n:=1) (transpose (n:=1) (sw__Write__rf _i)) (sw__Write__mo _i)) (domain (difference (sw__Read _i) (join (m:=0) (n:=1) (sw__Write _i) (sw__Write__rf _i))) (range (m:=1) (n:=0) (join (m:=1) (n:=1) (sw__MemoryEvent__address _i) (transpose (n:=1) (sw__MemoryEvent__address _i))) (sw__Write _i)))).

Definition wf_map_scope (_i : Instance) :=
(* (sw/Scope <: scopemap) . ~ (sw/Scope <: scopemap) in iden *)
(inside iden (join (m:=1) (n:=1) (sw__Scope__scopemap _i) (transpose (n:=1) (sw__Scope__scopemap _i)))).

(*
Definition integer__lt (_i : Instance) n1 n2 :=
(* int[n1] < int[n2] *)
(lt n1 n2).
*)

Definition hw__fr (_i : Instance) :=
(* ~ (hw/Write <: rf) . ^ (hw/Write <: co) + hw/Read - hw/Write . (hw/Write <: rf) <: (hw/MemoryEvent <: address) . ~ (hw/MemoryEvent <: address) :> hw/Write *)
(union (n:=2) (join (m:=1) (n:=1) (transpose (n:=1) (hw__Write__rf _i)) (tc (hw__Write__co _i))) (domain (difference (hw__Read _i) (join (m:=0) (n:=1) (hw__Write _i) (hw__Write__rf _i))) (range (m:=1) (n:=0) (join (m:=1) (n:=1) (hw__MemoryEvent__address _i) (transpose (n:=1) (hw__MemoryEvent__address _i))) (hw__Write _i)))).

(*
Definition integer__negate (_i : Instance) n :=
(* Int[0 @- int[n]] *)
(B?@-? 0 @- int[n] ?).
*)

(*
Definition integer__next (_i : Instance) :=
(* next *)
S.
*)

Definition sw__atomicity (_i : Instance) :=
(* no (sw/Read <: rmw) & sw/rb . (sw/Write <: mo) *)
(no (intersect (sw__Read__rmw _i) (join (m:=1) (n:=1) (sw__rb _i) (sw__Write__mo _i)))).

Definition hw__location (_i : Instance) rel :=
(* rel & (hw/MemoryEvent <: address) . ~ (hw/MemoryEvent <: address) *)
(intersect rel (join (m:=1) (n:=1) (hw__MemoryEvent__address _i) (transpose (n:=1) (hw__MemoryEvent__address _i)))).

Definition hw__System (_i : Instance) :=
(* hw/Scope - hw/Scope . (hw/Scope <: subscope) *)
(difference (hw__Scope _i) (join (m:=0) (n:=1) (hw__Scope _i) (hw__Scope__subscope _i))).

Definition sw__loc (_i : Instance) :=
(* (sw/MemoryEvent <: address) . ~ (sw/MemoryEvent <: address) *)
(join (m:=1) (n:=1) (sw__MemoryEvent__address _i) (transpose (n:=1) (sw__MemoryEvent__address _i))).

(*
Definition integer__nexts (_i : Instance) e :=
(* e . ^ integer/next *)
(join (m:=0) (n:=1) e (tc (integer__next _i))).
*)

Definition util__symmetric (_i : Instance) r :=
(* r & ~ r *)
(intersect r (transpose (n:=1) r)).

Definition hw__strong_r (_i : Instance) :=
(* util/symmetric[(hw/Event <: scope) . * (hw/Scope <: subscope) . (hw/Thread <: start) . * (hw/Event <: po)] *)
(util__symmetric _i (join (m:=1) (n:=1) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (hw__Event__scope _i) (rtc (hw__Scope__subscope _i))) (hw__Thread__start _i)) (rtc (hw__Event__po _i)))).

Definition hw__is_strong (_i : Instance) r :=
(* r in hw/strong_r *)
(inside (hw__strong_r _i) r).

Definition sw__strong_r (_i : Instance) :=
(* util/symmetric[(sw/Event <: scope) . * (sw/Scope <: subscope) . (sw/Thread <: start) . * (sw/Event <: sb)] *)
(util__symmetric _i (join (m:=1) (n:=1) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__Event__scope _i) (rtc (sw__Scope__subscope _i))) (sw__Thread__start _i)) (rtc (sw__Event__sb _i)))).

(*
Definition integer__minus (_i : Instance) n1 n2 :=
(* Int[int[n1] @- int[n2]] *)
(B?@-? int[n1] @- int[n2] ?).
*)

Definition hw__FenceAcqs (_i : Instance) :=
(* hw/FenceAcqRel + hw/FenceAcq + hw/BarrierWait *)
(union (n:=1) (union (n:=1) (hw__FenceAcqRel _i) (hw__FenceAcq _i)) (hw__BarrierWait _i)).

Definition hw__Acquirers (_i : Instance) :=
(* hw/Acquire + hw/FenceAcqs *)
(union (n:=1) (hw__Acquire _i) (hw__FenceAcqs _i)).

(*
Definition integer__mul (_i : Instance) n1 n2 :=
(* Int[int[n1] * int[n2]] *)
(B?*? int[n1] * int[n2] ?).
*)

Definition reverse_map_rf (_i : Instance) :=
(* AND[(hw/Write <: rf) in ~ (sw/Event <: map) . (sw/Write <: rf) . (sw/Event <: map), hw/Read - hw/Write . (hw/Write <: rf) = sw/Read - sw/Write . (sw/Write <: rf) . (sw/Event <: map)] *)
( (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (transpose (n:=1) (sw__Event__map _i)) (sw__Write__rf _i)) (sw__Event__map _i)) (hw__Write__rf _i)) /\ (equal (n:=1) (difference (hw__Read _i) (join (m:=0) (n:=1) (hw__Write _i) (hw__Write__rf _i))) (join (m:=0) (n:=1) (difference (sw__Read _i) (join (m:=0) (n:=1) (sw__Write _i) (sw__Write__rf _i))) (sw__Event__map _i)))).

(*
Definition integer__sub (_i : Instance) n1 n2 :=
(* integer/minus[n1, n2] *)
(integer__minus _i n1 n2).
*)

(*
Definition integer__plus (_i : Instance) n1 n2 :=
(* Int[int[n1] @+ int[n2]] *)
(B?@+? int[n1] @+ int[n2] ?).
*)

(*
Definition integer__add (_i : Instance) n1 n2 :=
(* integer/plus[n1, n2] *)
(integer__plus _i n1 n2).
*)

(*
Definition integer__gt (_i : Instance) n1 n2 :=
(* int[n1] > int[n2] *)
(gt n1 n2).
*)

Definition sw__sbnl (_i : Instance) :=
(* (sw/Event <: sb) - (sw/Event <: sb) & sw/loc *)
(difference (sw__Event__sb _i) (intersect (sw__Event__sb _i) (sw__loc _i))).

Definition hw__weak (_i : Instance) r :=
(* r - hw/strong_r *)
(difference r (hw__strong_r _i)).

Definition util__ident (_i : Instance) e :=
(* iden & e -> e *)
(intersect iden (arrow (m:=0) (n:=0) e e)).

(*
Definition integer__pos (_i : Instance) n :=
(* int[n] > 0 *)
(gt n 0).
*)

(*
Definition integer__min (_i : Instance) es :=
(* es - es . ^ integer/next *)
(difference es (join (m:=0) (n:=1) es (tc (integer__next _i)))).
*)

(*
Definition integer__smaller (_i : Instance) e1 e2 :=
(* (let a= Int[int[e1]] | (let b= Int[int[e2]] | (int[a] < int[b] => a else b))) *)
(let a := e1 in (let b := e2 in (ite (lt a b) a b))).
*)

(*
Definition integer__lte (_i : Instance) n1 n2 :=
(* int[n1] <= int[n2] *)
(le n1 n2).
*)

Definition sw__conflict (_i : Instance) :=
(* (sw/MemoryEvent <: address) . ~ (sw/MemoryEvent <: address) - iden - sw/Read -> sw/Read *)
(difference (difference (join (m:=1) (n:=1) (sw__MemoryEvent__address _i) (transpose (n:=1) (sw__MemoryEvent__address _i))) iden) (arrow (m:=0) (n:=0) (sw__Read _i) (sw__Read _i))).

(*
Definition integer__larger (_i : Instance) e1 e2 :=
(* (let a= Int[int[e1]] | (let b= Int[int[e2]] | (int[a] < int[b] => b else a))) *)
(let a := e1 in (let b := e2 in (ite (lt a b) b a))).
*)

Definition hw__typed (_i : Instance) rel type :=
(* type <: rel :> type *)
(domain type (range (m:=1) (n:=0) rel type)).

(*
Definition integer__nonpos (_i : Instance) n :=
(* int[n] <= 0 *)
(le n 0).
*)

(*
Definition integer__max (_i : Instance) es :=
(* es - es . ^ integer/prev *)
(difference es (join (m:=0) (n:=1) es (tc (integer__prev _i)))).
*)

Definition util__optional (_i : Instance) f :=
(* iden + f *)
(union (n:=2) iden f).

Definition wf_map_addrs (_i : Instance) :=
(* (sw/MemoryEvent <: address) = (sw/Event <: map) . (hw/MemoryEvent <: address) . ~ (sw/Address <: addrmap) *)
(equal (n:=2) (sw__MemoryEvent__address _i) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__Event__map _i) (hw__MemoryEvent__address _i)) (transpose (n:=1) (sw__Address__addrmap _i)))).

(*
Definition integer__prev (_i : Instance) :=
(* ~ integer/next *)
(transpose (n:=1) (integer__next _i)).
*)

(*
Definition integer__elem2int (_i : Instance) e next :=
(* Int[# ^ next . e] *)
(cardinality 1 (join (m:=1) (n:=0) (tc next) e)).
*)

Definition hw__FenceRels (_i : Instance) :=
(* hw/FenceAcqRel + hw/FenceRel + hw/BarrierWait *)
(union (n:=1) (union (n:=1) (hw__FenceAcqRel _i) (hw__FenceRel _i)) (hw__BarrierWait _i)).

Definition hw__Releasers (_i : Instance) :=
(* hw/Release + hw/FenceRels + hw/FenceRels . (hw/Event <: po) . (hw/Read <: rmw) *)
(union (n:=1) (union (n:=1) (hw__Release _i) (hw__FenceRels _i)) (join (m:=0) (n:=1) (join (m:=0) (n:=1) (hw__FenceRels _i) (hw__Event__po _i)) (hw__Read__rmw _i))).

Definition hw__same_thread (_i : Instance) rel :=
(* rel & iden + ^ (hw/Event <: po) + ~ ^ (hw/Event <: po) *)
(intersect rel (union (n:=2) (union (n:=2) iden (tc (hw__Event__po _i))) (transpose (n:=1) (tc (hw__Event__po _i))))).

Definition hw__rfi (_i : Instance) :=
(* hw/same_thread[(hw/Write <: rf)] *)
(hw__same_thread _i (hw__Write__rf _i)).

Definition hw__rfe (_i : Instance) :=
(* (hw/Write <: rf) - hw/rfi *)
(difference (hw__Write__rf _i) (hw__rfi _i)).

Definition util__imm (_i : Instance) rel :=
(* rel - rel . rel *)
(difference rel (join (m:=1) (n:=1) rel rel)).

Definition sw__com (_i : Instance) :=
(* (sw/Write <: rf) + (sw/Write <: mo) + sw/rb *)
(union (n:=2) (union (n:=2) (sw__Write__rf _i) (sw__Write__mo _i)) (sw__rb _i)).

Definition sw__eco (_i : Instance) :=
(* ^ sw/com *)
(tc (sw__com _i)).

Definition reverse_map_fr (_i : Instance) :=
(* hw/fr in ~ (sw/Event <: map) . sw/rb . (sw/Event <: map) *)
(inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (transpose (n:=1) (sw__Event__map _i)) (sw__rb _i)) (sw__Event__map _i)) (hw__fr _i)).

Definition util__transitive (_i : Instance) rel :=
(* rel = ^ rel *)
(equal (n:=2) rel (tc rel)).

Definition sw__System (_i : Instance) :=
(* sw/Scope - sw/Scope . (sw/Scope <: subscope) *)
(difference (sw__Scope _i) (join (m:=0) (n:=1) (sw__Scope _i) (sw__Scope__subscope _i))).

(*
Definition integer__signum (_i : Instance) n :=
(* (int[n] < 0 => 0 @- 1 else (int[n] > 0 => 1 else 0)) *)
(ite (lt n 0) (B?@-? 0 @- 1 ?) (ite (gt n 0) 1 0)).
*)

Definition wf_map_insts (_i : Instance) :=
(* AND[sw/Event . (sw/Event <: map) = hw/Event, (all e | some e . (sw/Event <: map)), (all e | one e . ~ (sw/Event <: map)), (sw/Event <: sb) in (sw/Event <: map) . ^ (hw/Event <: po) . ~ (sw/Event <: map)] *)
( (equal (n:=1) (join (m:=0) (n:=1) (sw__Event _i) (sw__Event__map _i)) (hw__Event _i)) /\ (forall e, (oneof (sw__Event _i)) e -> (some (join (m:=0) (n:=1) e (sw__Event__map _i)))) /\ (forall e, (oneof (hw__Event _i)) e -> (one (join (m:=0) (n:=1) e (transpose (n:=1) (sw__Event__map _i))))) /\ (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__Event__map _i) (tc (hw__Event__po _i))) (transpose (n:=1) (sw__Event__map _i))) (sw__Event__sb _i))).

Definition wf_map (_i : Instance) :=
(* AND[this/wf_map_insts, this/wf_map_addrs, this/wf_map_scope] *)
( (wf_map_insts _i) /\ (wf_map_addrs _i) /\ (wf_map_scope _i)).

Definition hw__po_loc (_i : Instance) :=
(* ^ (hw/Event <: po) & (hw/MemoryEvent <: address) . ~ (hw/MemoryEvent <: address) *)
(intersect (tc (hw__Event__po _i)) (join (m:=1) (n:=1) (hw__MemoryEvent__address _i) (transpose (n:=1) (hw__MemoryEvent__address _i)))).

Definition hw__prefix (_i : Instance) :=
(* hw/Release <: util/optional[hw/po_loc] :> hw/Write + hw/FenceRels <: ^ (hw/Event <: po) :> hw/Write *)
(union (n:=2) (domain (hw__Release _i) (range (m:=1) (n:=0) (util__optional _i (hw__po_loc _i)) (hw__Write _i))) (domain (hw__FenceRels _i) (range (m:=1) (n:=0) (tc (hw__Event__po _i)) (hw__Write _i)))).

Definition hw__suffix (_i : Instance) :=
(* hw/Read <: util/optional[hw/po_loc] :> hw/Acquire + hw/Read <: ^ (hw/Event <: po) :> hw/FenceAcqs *)
(union (n:=2) (domain (hw__Read _i) (range (m:=1) (n:=0) (util__optional _i (hw__po_loc _i)) (hw__Acquire _i))) (domain (hw__Read _i) (range (m:=1) (n:=0) (tc (hw__Event__po _i)) (hw__FenceAcqs _i)))).

(*
Definition integer__zero (_i : Instance) n :=
(* n = 0 *)
(n = 0).
*)

(*
Definition integer__eq (_i : Instance) n1 n2 :=
(* Int[int[n1]] = Int[int[n2]] *)
(n1 = n2).
*)

(*
Definition integer__int2elem (_i : Instance) i next s :=
(* {e | # ^ next . e = Int[int[i]]} *)
(Q? comprehension : {e | # ^ next . e = Int[int[i]]} ?).
*)

Definition compile_scope (_i : Instance) :=
(* AND[(sw/Thread <: start) . (sw/Event <: map) = (sw/Scope <: scopemap) . (hw/Thread <: start), (sw/Event <: scope) . (sw/Scope <: scopemap) = (sw/Event <: map) . (hw/Event <: scope), (sw/Scope <: subscope) . (sw/Scope <: scopemap) in (sw/Scope <: scopemap) . (hw/Scope <: subscope)] *)
( (equal (n:=2) (join (m:=1) (n:=1) (sw__Thread__start _i) (sw__Event__map _i)) (join (m:=1) (n:=1) (sw__Scope__scopemap _i) (hw__Thread__start _i))) /\ (equal (n:=2) (join (m:=1) (n:=1) (sw__Event__scope _i) (sw__Scope__scopemap _i)) (join (m:=1) (n:=1) (sw__Event__map _i) (hw__Event__scope _i))) /\ (inside (join (m:=1) (n:=1) (sw__Scope__scopemap _i) (hw__Scope__subscope _i)) (join (m:=1) (n:=1) (sw__Scope__subscope _i) (sw__Scope__scopemap _i)))).

Definition hw__com (_i : Instance) :=
(* (hw/Write <: rf) + ^ (hw/Write <: co) + hw/fr *)
(union (n:=2) (union (n:=2) (hw__Write__rf _i) (tc (hw__Write__co _i))) (hw__fr _i)).

(*
Definition integer__div (_i : Instance) n1 n2 :=
(* Int[int[n1] / int[n2]] *)
(B?/? int[n1] / int[n2] ?).
*)

Definition compile_rmw (_i : Instance) :=
(* (sw/Read <: rmw) = (sw/Event <: map) . (hw/Read <: rmw) . ~ (sw/Event <: map) *)
(equal (n:=2) (sw__Read__rmw _i) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__Event__map _i) (hw__Read__rmw _i)) (transpose (n:=1) (sw__Event__map _i)))).

(*
Definition integer__neg (_i : Instance) n :=
(* int[n] < 0 *)
(lt n 0).
*)

Definition hw__scoped (_i : Instance) s :=
(* s . * ~ (hw/Scope <: subscope) . ~ (hw/Event <: scope) *)
(join (m:=0) (n:=1) (join (m:=0) (n:=1) s (rtc (transpose (n:=1) (hw__Scope__subscope _i)))) (transpose (n:=1) (hw__Event__scope _i))).

Definition util__irreflexive (_i : Instance) rel :=
(* no iden & rel *)
(no (intersect iden rel)).

Definition util__acyclic (_i : Instance) rel :=
(* util/irreflexive[^ rel] *)
(util__irreflexive _i (tc rel)).

Definition hw__no_thin_air (_i : Instance) :=
(* util/acyclic[(hw/Write <: rf) + (hw/Read <: dep)] *)
(util__acyclic _i (union (n:=2) (hw__Write__rf _i) (hw__Read__dep _i))).

Definition util__total (_i : Instance) rel bag :=
(* AND[(all e,e' | e -> e' + e' -> e in ^ rel + ^ ~ rel), util/acyclic[rel]] *)
( (forall e, (oneof bag) e -> (forall e', (oneof bag) e' -> e' <> e ->(inside (union (n:=2) (tc rel) (tc (transpose (n:=1) rel))) (union (n:=2) (arrow (m:=0) (n:=0) e e') (arrow (m:=0) (n:=0) e' e))))) /\ (util__acyclic _i rel)).

Definition sw__no_thin_air (_i : Instance) :=
(* util/acyclic[(sw/Event <: sb) + (sw/Write <: rf)] *)
(util__acyclic _i (union (n:=2) (sw__Event__sb _i) (sw__Write__rf _i))).

Definition util__strict_partial (_i : Instance) rel :=
(* AND[util/irreflexive[rel], util/transitive[rel]] *)
( (util__irreflexive _i rel) /\ (util__transitive _i rel)).

Definition sw__ord (_i : Instance) :=
(* ~ (sw/Event <: memory_order) *)
(transpose (n:=1) (sw__Event__memory_order _i)).

Definition sw__NA (_i : Instance) :=
(* sw/MemoryOrderNonAtomic . sw/ord *)
(join (m:=0) (n:=1) (sw__MemoryOrderNonAtomic _i) (sw__ord _i)).

Definition sw__AR (_i : Instance) :=
(* sw/MemoryOrderAcqRel . sw/ord *)
(join (m:=0) (n:=1) (sw__MemoryOrderAcqRel _i) (sw__ord _i)).

Definition compile_read_na (_i : Instance) :=
(* sw/Read & sw/NA . (sw/Event <: map) in hw/Read *)
(inside (hw__Read _i) (join (m:=0) (n:=1) (intersect (sw__Read _i) (sw__NA _i)) (sw__Event__map _i))).

Definition sw__ACQ (_i : Instance) :=
(* sw/MemoryOrderAcquire . sw/ord *)
(join (m:=0) (n:=1) (sw__MemoryOrderAcquire _i) (sw__ord _i)).

Definition compile_read_aq (_i : Instance) :=
(* sw/Read & sw/ACQ . (sw/Event <: map) in hw/Acquire *)
(inside (hw__Acquire _i) (join (m:=0) (n:=1) (intersect (sw__Read _i) (sw__ACQ _i)) (sw__Event__map _i))).

Definition sw__REL (_i : Instance) :=
(* sw/MemoryOrderRelease . sw/ord *)
(join (m:=0) (n:=1) (sw__MemoryOrderRelease _i) (sw__ord _i)).

Definition compile_write_rl (_i : Instance) :=
(* sw/Write & sw/REL . (sw/Event <: map) in hw/Release *)
(inside (hw__Release _i) (join (m:=0) (n:=1) (intersect (sw__Write _i) (sw__REL _i)) (sw__Event__map _i))).

Definition sw__SC (_i : Instance) :=
(* sw/MemoryOrderSeqCst . sw/ord *)
(join (m:=0) (n:=1) (sw__MemoryOrderSeqCst _i) (sw__ord _i)).

Definition compile_fence_sc (_i : Instance) :=
(* sw/Fence & sw/SC . (sw/Event <: map) in hw/FenceSC *)
(inside (hw__FenceSC _i) (join (m:=0) (n:=1) (intersect (sw__Fence _i) (sw__SC _i)) (sw__Event__map _i))).

Definition compile_fence_ar (_i : Instance) :=
(* sw/Fence & sw/AR . (sw/Event <: map) in hw/FenceAcqRel *)
(inside (hw__FenceAcqRel _i) (join (m:=0) (n:=1) (intersect (sw__Fence _i) (sw__AR _i)) (sw__Event__map _i))).

Definition compile_fence_aq (_i : Instance) :=
(* sw/Fence & sw/ACQ . (sw/Event <: map) in hw/FenceAcq *)
(inside (hw__FenceAcq _i) (join (m:=0) (n:=1) (intersect (sw__Fence _i) (sw__ACQ _i)) (sw__Event__map _i))).

Definition compile_write_na (_i : Instance) :=
(* sw/Write & sw/NA . (sw/Event <: map) in hw/Write *)
(inside (hw__Write _i) (join (m:=0) (n:=1) (intersect (sw__Write _i) (sw__NA _i)) (sw__Event__map _i))).

Definition sw__strong (_i : Instance) r :=
(* r & sw/strong_r *)
(intersect r (sw__strong_r _i)).

Definition reverse_map_co (_i : Instance) :=
(* (hw/Write <: co) in ~ (sw/Event <: map) . (sw/Write <: mo) . (sw/Event <: map) *)
(inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (transpose (n:=1) (sw__Event__map _i)) (sw__Write__mo _i)) (sw__Event__map _i)) (hw__Write__co _i)).

Definition reverse_map (_i : Instance) :=
(* AND[this/reverse_map_rf, this/reverse_map_co, this/reverse_map_fr] *)
( (reverse_map_rf _i) /\ (reverse_map_co _i) /\ (reverse_map_fr _i)).

(*
Definition integer__nonneg (_i : Instance) n :=
(* int[n] >= 0 *)
(ge n 0).
*)

(*
Definition integer__rem (_i : Instance) n1 n2 :=
(* Int[int[n1] % int[n2]] *)
(B?%? int[n1] % int[n2] ?).
*)

Definition hw__strong (_i : Instance) r :=
(* r & hw/strong_r *)
(intersect r (hw__strong_r _i)).

Definition hw__location_sc (_i : Instance) :=
(* util/acyclic[hw/strong[hw/com] + hw/po_loc] *)
(util__acyclic _i (union (n:=2) (hw__strong _i (hw__com _i)) (hw__po_loc _i))).

Definition hw__sync (_i : Instance) head tail :=
(* head <: hw/strong[hw/prefix . ^ (hw/MemoryEvent <: observation) . hw/suffix] :> tail *)
(domain head (range (m:=1) (n:=0) (hw__strong _i (join (m:=1) (n:=1) (join (m:=1) (n:=1) (hw__prefix _i) (tc (hw__MemoryEvent__observation _i))) (hw__suffix _i))) tail)).

Definition syncacqrel (_i : Instance) :=
(* * (hw/Event <: po) . hw/sync[hw/Releasers, hw/Acquirers] . * (hw/Event <: po) *)
(join (m:=1) (n:=1) (join (m:=1) (n:=1) (rtc (hw__Event__po _i)) (hw__sync _i (hw__Releasers _i) (hw__Acquirers _i))) (rtc (hw__Event__po _i))).

Definition hw__cause_base (_i : Instance) :=
(* ^ * (hw/Event <: po) . (hw/BarrierArrive <: synchronizes) + (hw/FenceSC <: sc) + hw/sync[hw/Releasers, hw/Acquirers] . * (hw/Event <: po) *)
(tc (join (m:=1) (n:=1) (join (m:=1) (n:=1) (rtc (hw__Event__po _i)) (union (n:=2) (union (n:=2) (hw__BarrierArrive__synchronizes _i) (hw__FenceSC__sc _i)) (hw__sync _i (hw__Releasers _i) (hw__Acquirers _i)))) (rtc (hw__Event__po _i)))).

Definition hw__cause (_i : Instance) :=
(* hw/cause_base + (hw/MemoryEvent <: observation) . hw/po_loc + hw/cause_base *)
(union (n:=2) (hw__cause_base _i) (join (m:=1) (n:=1) (hw__MemoryEvent__observation _i) (union (n:=2) (hw__po_loc _i) (hw__cause_base _i)))).

Definition hw__causality (_i : Instance) :=
(* util/irreflexive[util/optional[hw/fr + (hw/Write <: rf)] . hw/cause] *)
(util__irreflexive _i (join (m:=1) (n:=1) (util__optional _i (union (n:=2) (hw__fr _i) (hw__Write__rf _i))) (hw__cause _i))).

Definition hw__atomicity (_i : Instance) :=
(* no hw/strong[hw/fr] . hw/strong[(hw/Write <: co)] & (hw/Read <: rmw) *)
(no (intersect (join (m:=1) (n:=1) (hw__strong _i (hw__fr _i)) (hw__strong _i (hw__Write__co _i))) (hw__Read__rmw _i))).

Definition hw__coherence (_i : Instance) :=
(* hw/location[hw/Write <: hw/cause :> hw/Write] in ^ (hw/Write <: co) *)
(inside (tc (hw__Write__co _i)) (hw__location _i (domain (hw__Write _i) (range (m:=1) (n:=0) (hw__cause _i) (hw__Write _i))))).

Definition hw__ptx_mm (_i : Instance) :=
(* AND[hw/no_thin_air, hw/location_sc, hw/atomicity, hw/coherence, hw/causality] *)
( (hw__no_thin_air _i) /\ (hw__location_sc _i) /\ (hw__atomicity _i) /\ (hw__coherence _i) /\ (hw__causality _i)).

(*
Definition integer__gte (_i : Instance) n1 n2 :=
(* int[n1] >= int[n2] *)
(ge n1 n2).
*)

Definition hw__inside (_i : Instance) s :=
(* s . * (hw/Scope <: subscope) . (hw/Thread <: start) . * (hw/Event <: po) *)
(join (m:=0) (n:=1) (join (m:=0) (n:=1) (join (m:=0) (n:=1) s (rtc (hw__Scope__subscope _i))) (hw__Thread__start _i)) (rtc (hw__Event__po _i))).

Definition compile_fence_rl (_i : Instance) :=
(* sw/Fence & sw/REL . (sw/Event <: map) in hw/FenceRel *)
(inside (hw__FenceRel _i) (join (m:=0) (n:=1) (intersect (sw__Fence _i) (sw__REL _i)) (sw__Event__map _i))).

(*
Definition integer__prevs (_i : Instance) e :=
(* e . ^ integer/prev *)
(join (m:=0) (n:=1) e (tc (integer__prev _i))).
*)

Definition sw__RLX (_i : Instance) :=
(* sw/MemoryOrderRelaxed . sw/ord *)
(join (m:=0) (n:=1) (sw__MemoryOrderRelaxed _i) (sw__ord _i)).

Definition compile_read_rx (_i : Instance) :=
(* sw/Read & sw/RLX . (sw/Event <: map) in hw/Read *)
(inside (hw__Read _i) (join (m:=0) (n:=1) (intersect (sw__Read _i) (sw__RLX _i)) (sw__Event__map _i))).

Definition compile_write_rx (_i : Instance) :=
(* sw/Write & sw/RLX . (sw/Event <: map) in hw/Write *)
(inside (hw__Write _i) (join (m:=0) (n:=1) (intersect (sw__Write _i) (sw__RLX _i)) (sw__Event__map _i))).

Definition compile_MemoryEvents (_i : Instance) :=
(* AND[this/compile_read_na, this/compile_read_rx, this/compile_read_aq, this/compile_write_na, this/compile_write_rx, this/compile_write_rl, this/compile_write_na, this/compile_fence_aq, this/compile_fence_rl, this/compile_fence_ar, this/compile_fence_sc, this/compile_rmw, this/compile_scope] *)
( (compile_read_na _i) /\ (compile_read_rx _i) /\ (compile_read_aq _i) /\ (compile_write_na _i) /\ (compile_write_rx _i) /\ (compile_write_rl _i) /\ (compile_write_na _i) /\ (compile_fence_aq _i) /\ (compile_fence_rl _i) /\ (compile_fence_ar _i) /\ (compile_fence_sc _i) /\ (compile_rmw _i) /\ (compile_scope _i)).

Definition sw__A (_i : Instance) :=
(* sw/RLX + sw/ACQ + sw/REL + sw/AR + sw/SC *)
(union (n:=1) (union (n:=1) (union (n:=1) (union (n:=1) (sw__RLX _i) (sw__ACQ _i)) (sw__REL _i)) (sw__AR _i)) (sw__SC _i)).

Definition sw__rs (_i : Instance) :=
(* util/ident[sw/Write] . util/optional[(sw/Event <: sb) & sw/loc] . util/ident[sw/Write & sw/A] . * sw/strong[(sw/Write <: rf)] . (sw/Read <: rmw) *)
(join (m:=1) (n:=1) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (util__ident _i (sw__Write _i)) (util__optional _i (intersect (sw__Event__sb _i) (sw__loc _i)))) (util__ident _i (intersect (sw__Write _i) (sw__A _i)))) (rtc (join (m:=1) (n:=1) (sw__strong _i (sw__Write__rf _i)) (sw__Read__rmw _i)))).

Definition sw__sw (_i : Instance) :=
(* util/ident[sw/REL + sw/AR + sw/SC] . util/optional[util/ident[sw/Fence] . (sw/Event <: sb)] . sw/rs . sw/strong[(sw/Write <: rf)] . util/ident[sw/Read & sw/A] . util/optional[(sw/Event <: sb) . util/ident[sw/Fence]] . util/ident[sw/ACQ + sw/AR + sw/SC] *)
(join (m:=1) (n:=1) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (util__ident _i (union (n:=1) (union (n:=1) (sw__REL _i) (sw__AR _i)) (sw__SC _i))) (util__optional _i (join (m:=1) (n:=1) (util__ident _i (sw__Fence _i)) (sw__Event__sb _i)))) (sw__rs _i)) (sw__strong _i (sw__Write__rf _i))) (util__ident _i (intersect (sw__Read _i) (sw__A _i)))) (util__optional _i (join (m:=1) (n:=1) (sw__Event__sb _i) (util__ident _i (sw__Fence _i))))) (util__ident _i (union (n:=1) (union (n:=1) (sw__ACQ _i) (sw__AR _i)) (sw__SC _i)))).

Definition sw__hb (_i : Instance) :=
(* ^ (sw/Event <: sb) + sw/strong[sw/sw] *)
(tc (union (n:=2) (sw__Event__sb _i) (sw__strong _i (sw__sw _i)))).

Definition sw__scb (_i : Instance) :=
(* (sw/Event <: sb) + sw/sbnl + sw/hb . sw/sbnl . sw/hb + (sw/Write <: mo) + sw/rb *)
(union (n:=2) (union (n:=2) (union (n:=2) (union (n:=2) (sw__Event__sb _i) (sw__sbnl _i)) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__hb _i) (sw__sbnl _i)) (sw__hb _i))) (sw__Write__mo _i)) (sw__rb _i)).

Definition sw__pscbase (_i : Instance) :=
(* util/ident[sw/SC] + util/ident[sw/Fence & sw/SC] . util/optional[sw/hb] . sw/scb . util/ident[sw/SC] + util/optional[sw/hb] . util/ident[sw/Fence & sw/SC] *)
(join (m:=1) (n:=1) (join (m:=1) (n:=1) (union (n:=2) (util__ident _i (sw__SC _i)) (join (m:=1) (n:=1) (util__ident _i (intersect (sw__Fence _i) (sw__SC _i))) (util__optional _i (sw__hb _i)))) (sw__scb _i)) (union (n:=2) (util__ident _i (sw__SC _i)) (join (m:=1) (n:=1) (util__optional _i (sw__hb _i)) (util__ident _i (intersect (sw__Fence _i) (sw__SC _i)))))).

Definition sw__race (_i : Instance) :=
(* sw/conflict - sw/hb - ~ sw/hb *)
(difference (difference (sw__conflict _i) (sw__hb _i)) (transpose (n:=1) (sw__hb _i))).

Definition sw__racy (_i : Instance) :=
(* some sw/race - sw/strong_r *)
(some (difference (sw__race _i) (sw__strong_r _i))).

Definition sw__coherence (_i : Instance) :=
(* util/irreflexive[sw/hb . util/optional[sw/eco]] *)
(util__irreflexive _i (join (m:=1) (n:=1) (sw__hb _i) (util__optional _i (sw__eco _i)))).

Definition compile_src11_ptx (_i : Instance) :=
(* AND[! sw/racy, this/wf_map, this/compile_MemoryEvents, hw/ptx_mm, this/reverse_map] *)
( (~ (sw__racy _i)) /\ (wf_map _i) /\ (compile_MemoryEvents _i) /\ (hw__ptx_mm _i) /\ (reverse_map _i)).

Definition run_3 (_i : Instance) :=
(* AND[some hw/Read, this/compile_src11_ptx] *)
( (some (hw__Read _i)) /\ (compile_src11_ptx _i)).

Definition sw__pscF (_i : Instance) :=
(* util/ident[sw/Fence & sw/SC] . sw/hb + sw/hb . sw/eco . sw/hb . util/ident[sw/Fence & sw/SC] *)
(join (m:=1) (n:=1) (join (m:=1) (n:=1) (util__ident _i (intersect (sw__Fence _i) (sw__SC _i))) (union (n:=2) (sw__hb _i) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__hb _i) (sw__eco _i)) (sw__hb _i)))) (util__ident _i (intersect (sw__Fence _i) (sw__SC _i)))).

Definition sw__psc (_i : Instance) :=
(* sw/pscbase + sw/pscF *)
(union (n:=2) (sw__pscbase _i) (sw__pscF _i)).

Definition sw__sc (_i : Instance) :=
(* util/acyclic[sw/strong[sw/psc]] *)
(util__acyclic _i (sw__strong _i (sw__psc _i))).

Definition sw__src11 (_i : Instance) :=
(* AND[sw/coherence, sw/atomicity, sw/sc, sw/no_thin_air] *)
( (sw__coherence _i) /\ (sw__atomicity _i) /\ (sw__sc _i) /\ (sw__no_thin_air _i)).

Definition run_12 (_i : Instance) :=
(* AND[some sw/NA <: (sw/Event <: sb) . sw/sw . (sw/Event <: sb) :> sw/NA & (sw/Write <: rf), some (sw/Scope <: subscope), this/compile_src11_ptx, sw/src11] *)
( (some (intersect (domain (sw__NA _i) (range (m:=1) (n:=0) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__Event__sb _i) (sw__sw _i)) (sw__Event__sb _i)) (sw__NA _i))) (sw__Write__rf _i))) /\ (some (sw__Scope__subscope _i)) /\ (compile_src11_ptx _i) /\ (sw__src11 _i)).

Definition run_13 (_i : Instance) :=
(* AND[this/compile_src11_ptx, some (sw/Scope <: scopemap) . ~ (sw/Scope <: scopemap) - iden] *)
( (compile_src11_ptx _i) /\ (some (difference (join (m:=1) (n:=1) (sw__Scope__scopemap _i) (transpose (n:=1) (sw__Scope__scopemap _i))) iden))).

Axiom _hw__Address_fact0 :
(* AND[# (hw/MemoryEvent <: address) :> this > 1, # hw/Write <: (hw/MemoryEvent <: address) :> this > 0] *)
forall (_i : Instance) (this : Relation 1), oneof (hw__Address _i) this -> ( (gt (cardinality 2 (range (m:=1) (n:=0) (hw__MemoryEvent__address _i) this)) 1) /\ (gt (cardinality 2 (domain (hw__Write _i) (range (m:=1) (n:=0) (hw__MemoryEvent__address _i) this))) 0)).

Axiom _hw__Scope__subscope_domain : 
forall (_i : Instance) (x : Tuple 2), hw__Scope__subscope _i x -> (hw__Scope _i (fst x)).

Axiom _hw__Scope__subscope_range : 
forall (_i : Instance) x, oneof (hw__Scope _i) x -> (setof (hw__Scope _i))
 (join (m:=0) (n:=1) x (hw__Scope__subscope _i)).

Axiom _hw__Thread__start_domain : 
forall (_i : Instance) (x : Tuple 2), hw__Thread__start _i x -> (hw__Thread _i (fst x)).

Axiom _hw__Thread__start_range : 
forall (_i : Instance) x, oneof (hw__Thread _i) x -> (oneof (hw__Event _i))
 (join (m:=0) (n:=1) x (hw__Thread__start _i)).

Axiom _hw__Event__po_domain : 
forall (_i : Instance) (x : Tuple 2), hw__Event__po _i x -> (hw__Event _i (fst x)).

Axiom _hw__Event__po_range : 
forall (_i : Instance) x, oneof (hw__Event _i) x -> (loneof (hw__Event _i))
 (join (m:=0) (n:=1) x (hw__Event__po _i)).

Axiom _hw__Event__scope_domain : 
forall (_i : Instance) (x : Tuple 2), hw__Event__scope _i x -> (hw__Event _i (fst x)).

Axiom _hw__Event__scope_range : 
forall (_i : Instance) x, oneof (hw__Event _i) x -> (oneof (hw__Scope _i))
 (join (m:=0) (n:=1) x (hw__Event__scope _i)).

Axiom _hw__Fence_fact0 :
(* some hw/Scope - hw/Thread => this . (hw/Event <: scope) !in hw/Thread *)
forall (_i : Instance) (this : Relation 1), oneof (hw__Fence _i) this -> ((some (difference (hw__Scope _i) (hw__Thread _i))) -> (~inside (hw__Thread _i) (join (m:=0) (n:=1) this (hw__Event__scope _i)))).

Axiom _hw__MemoryEvent__address_domain : 
forall (_i : Instance) (x : Tuple 2), hw__MemoryEvent__address _i x -> (hw__MemoryEvent _i (fst x)).

Axiom _hw__MemoryEvent__address_range : 
forall (_i : Instance) x, oneof (hw__MemoryEvent _i) x -> (oneof (hw__Address _i))
 (join (m:=0) (n:=1) x (hw__MemoryEvent__address _i)).

Axiom _hw__MemoryEvent__observation_domain : 
forall (_i : Instance) (x : Tuple 2), hw__MemoryEvent__observation _i x -> (hw__MemoryEvent _i (fst x)).

Axiom _hw__MemoryEvent__observation_range : 
forall (_i : Instance) x, oneof (hw__MemoryEvent _i) x -> (setof (hw__MemoryEvent _i))
 (join (m:=0) (n:=1) x (hw__MemoryEvent__observation _i)).

Axiom _hw__Read__rmw_domain : 
forall (_i : Instance) (x : Tuple 2), hw__Read__rmw _i x -> (hw__Read _i (fst x)).

Axiom _hw__Read__rmw_range : 
forall (_i : Instance) x, oneof (hw__Read _i) x -> (loneof (hw__Write _i))
 (join (m:=0) (n:=1) x (hw__Read__rmw _i)).

Axiom _hw__Read__dep_domain : 
forall (_i : Instance) (x : Tuple 2), hw__Read__dep _i x -> (hw__Read _i (fst x)).

Axiom _hw__Read__dep_range : 
forall (_i : Instance) x, oneof (hw__Read _i) x -> (setof (hw__Event _i))
 (join (m:=0) (n:=1) x (hw__Read__dep _i)).

Axiom _hw__Write__rf_domain : 
forall (_i : Instance) (x : Tuple 2), hw__Write__rf _i x -> (hw__Write _i (fst x)).

Axiom _hw__Write__rf_range : 
forall (_i : Instance) x, oneof (hw__Write _i) x -> (setof (hw__Read _i))
 (join (m:=0) (n:=1) x (hw__Write__rf _i)).

Axiom _hw__Write__co_domain : 
forall (_i : Instance) (x : Tuple 2), hw__Write__co _i x -> (hw__Write _i (fst x)).

Axiom _hw__Write__co_range : 
forall (_i : Instance) x, oneof (hw__Write _i) x -> (setof (hw__Write _i))
 (join (m:=0) (n:=1) x (hw__Write__co _i)).

Axiom _hw__FenceSC__sc_domain : 
forall (_i : Instance) (x : Tuple 2), hw__FenceSC__sc _i x -> (hw__FenceSC _i (fst x)).

Axiom _hw__FenceSC__sc_range : 
forall (_i : Instance) x, oneof (hw__FenceSC _i) x -> (setof (hw__FenceSC _i))
 (join (m:=0) (n:=1) x (hw__FenceSC__sc _i)).

Axiom _hw__Acquire_fact0 :
(* this . (hw/Event <: scope) !in hw/Thread *)
forall (_i : Instance) (this : Relation 1), oneof (hw__Acquire _i) this -> (~inside (hw__Thread _i) (join (m:=0) (n:=1) this (hw__Event__scope _i))).

Axiom _hw__Release_fact0 :
(* this . (hw/Event <: scope) !in hw/Thread *)
forall (_i : Instance) (this : Relation 1), oneof (hw__Release _i) this -> (~inside (hw__Thread _i) (join (m:=0) (n:=1) this (hw__Event__scope _i))).

Axiom _hw__BarrierArrive__synchronizes_domain : 
forall (_i : Instance) (x : Tuple 2), hw__BarrierArrive__synchronizes _i x -> (hw__BarrierArrive _i (fst x)).

Axiom _hw__BarrierArrive__synchronizes_range : 
forall (_i : Instance) x, oneof (hw__BarrierArrive _i) x -> (setof (hw__BarrierWait _i))
 (join (m:=0) (n:=1) x (hw__BarrierArrive__synchronizes _i)).

Axiom _sw__Address__addrmap_domain : 
forall (_i : Instance) (x : Tuple 2), sw__Address__addrmap _i x -> (sw__Address _i (fst x)).

Axiom _sw__Address__addrmap_range : 
forall (_i : Instance) x, oneof (sw__Address _i) x -> (oneof (hw__Address _i))
 (join (m:=0) (n:=1) x (sw__Address__addrmap _i)).

Axiom _sw__Scope__subscope_domain : 
forall (_i : Instance) (x : Tuple 2), sw__Scope__subscope _i x -> (sw__Scope _i (fst x)).

Axiom _sw__Scope__subscope_range : 
forall (_i : Instance) x, oneof (sw__Scope _i) x -> (setof (sw__Scope _i))
 (join (m:=0) (n:=1) x (sw__Scope__subscope _i)).

Axiom _sw__Scope__scopemap_domain : 
forall (_i : Instance) (x : Tuple 2), sw__Scope__scopemap _i x -> (sw__Scope _i (fst x)).

Axiom _sw__Scope__scopemap_range : 
forall (_i : Instance) x, oneof (sw__Scope _i) x -> (oneof (hw__Scope _i))
 (join (m:=0) (n:=1) x (sw__Scope__scopemap _i)).

Axiom _sw__Thread__start_domain : 
forall (_i : Instance) (x : Tuple 2), sw__Thread__start _i x -> (sw__Thread _i (fst x)).

Axiom _sw__Thread__start_range : 
forall (_i : Instance) x, oneof (sw__Thread _i) x -> (oneof (sw__Event _i))
 (join (m:=0) (n:=1) x (sw__Thread__start _i)).

Axiom _one_sig_sw__MemoryOrderNonAtomic : forall (_i : Instance),
one (sw__MemoryOrderNonAtomic _i).

Axiom _one_sig_sw__MemoryOrderRelaxed : forall (_i : Instance),
one (sw__MemoryOrderRelaxed _i).

Axiom _one_sig_sw__MemoryOrderAcquire : forall (_i : Instance),
one (sw__MemoryOrderAcquire _i).

Axiom _one_sig_sw__MemoryOrderRelease : forall (_i : Instance),
one (sw__MemoryOrderRelease _i).

Axiom _one_sig_sw__MemoryOrderAcqRel : forall (_i : Instance),
one (sw__MemoryOrderAcqRel _i).

Axiom _one_sig_sw__MemoryOrderSeqCst : forall (_i : Instance),
one (sw__MemoryOrderSeqCst _i).

Axiom _sw__Event__map_domain : 
forall (_i : Instance) (x : Tuple 2), sw__Event__map _i x -> (sw__Event _i (fst x)).

Axiom _sw__Event__map_range : 
forall (_i : Instance) x, oneof (sw__Event _i) x -> (oneof (hw__Event _i))
 (join (m:=0) (n:=1) x (sw__Event__map _i)).

Axiom _sw__Event__sb_domain : 
forall (_i : Instance) (x : Tuple 2), sw__Event__sb _i x -> (sw__Event _i (fst x)).

Axiom _sw__Event__sb_range : 
forall (_i : Instance) x, oneof (sw__Event _i) x -> (setof (sw__Event _i))
 (join (m:=0) (n:=1) x (sw__Event__sb _i)).

Axiom _sw__Event__memory_order_domain : 
forall (_i : Instance) (x : Tuple 2), sw__Event__memory_order _i x -> (sw__Event _i (fst x)).

Axiom _sw__Event__memory_order_range : 
forall (_i : Instance) x, oneof (sw__Event _i) x -> (oneof (sw__MemoryOrder _i))
 (join (m:=0) (n:=1) x (sw__Event__memory_order _i)).

Axiom _sw__Event__scope_domain : 
forall (_i : Instance) (x : Tuple 2), sw__Event__scope _i x -> (sw__Event _i (fst x)).

Axiom _sw__Event__scope_range : 
forall (_i : Instance) x, oneof (sw__Event _i) x -> (oneof (sw__Scope _i))
 (join (m:=0) (n:=1) x (sw__Event__scope _i)).

Axiom _sw__MemoryEvent__address_domain : 
forall (_i : Instance) (x : Tuple 2), sw__MemoryEvent__address _i x -> (sw__MemoryEvent _i (fst x)).

Axiom _sw__MemoryEvent__address_range : 
forall (_i : Instance) x, oneof (sw__MemoryEvent _i) x -> (oneof (sw__Address _i))
 (join (m:=0) (n:=1) x (sw__MemoryEvent__address _i)).

Axiom _sw__Write__rf_domain : 
forall (_i : Instance) (x : Tuple 2), sw__Write__rf _i x -> (sw__Write _i (fst x)).

Axiom _sw__Write__rf_range : 
forall (_i : Instance) x, oneof (sw__Write _i) x -> (setof (sw__Read _i))
 (join (m:=0) (n:=1) x (sw__Write__rf _i)).

Axiom _sw__Write__mo_domain : 
forall (_i : Instance) (x : Tuple 2), sw__Write__mo _i x -> (sw__Write _i (fst x)).

Axiom _sw__Write__mo_range : 
forall (_i : Instance) x, oneof (sw__Write _i) x -> (setof (sw__Write _i))
 (join (m:=0) (n:=1) x (sw__Write__mo _i)).

Axiom _sw__Read__rmw_domain : 
forall (_i : Instance) (x : Tuple 2), sw__Read__rmw _i x -> (sw__Read _i (fst x)).

Axiom _sw__Read__rmw_range : 
forall (_i : Instance) x, oneof (sw__Read _i) x -> (loneof (sw__Write _i))
 (join (m:=0) (n:=1) x (sw__Read__rmw _i)).

Axiom _Univ_disjoint_hw__Address :
forall (_i : Instance) x, (Univ _i) x -> ~((hw__Address _i) x).

Axiom _hw__Address_disjoint_Univ :
forall (_i : Instance) x, (hw__Address _i) x -> ~((Univ _i) x).

Axiom _Univ_disjoint_hw__Scope :
forall (_i : Instance) x, (Univ _i) x -> ~((hw__Scope _i) x).

Axiom _hw__Scope_disjoint_Univ :
forall (_i : Instance) x, (hw__Scope _i) x -> ~((Univ _i) x).

Axiom _Univ_disjoint_hw__Event :
forall (_i : Instance) x, (Univ _i) x -> ~((hw__Event _i) x).

Axiom _hw__Event_disjoint_Univ :
forall (_i : Instance) x, (hw__Event _i) x -> ~((Univ _i) x).

Axiom _Univ_disjoint_sw__Address :
forall (_i : Instance) x, (Univ _i) x -> ~((sw__Address _i) x).

Axiom _sw__Address_disjoint_Univ :
forall (_i : Instance) x, (sw__Address _i) x -> ~((Univ _i) x).

Axiom _Univ_disjoint_sw__Scope :
forall (_i : Instance) x, (Univ _i) x -> ~((sw__Scope _i) x).

Axiom _sw__Scope_disjoint_Univ :
forall (_i : Instance) x, (sw__Scope _i) x -> ~((Univ _i) x).

Axiom _Univ_disjoint_sw__MemoryOrder :
forall (_i : Instance) x, (Univ _i) x -> ~((sw__MemoryOrder _i) x).

Axiom _sw__MemoryOrder_disjoint_Univ :
forall (_i : Instance) x, (sw__MemoryOrder _i) x -> ~((Univ _i) x).

Axiom _Univ_disjoint_sw__Event :
forall (_i : Instance) x, (Univ _i) x -> ~((sw__Event _i) x).

Axiom _sw__Event_disjoint_Univ :
forall (_i : Instance) x, (sw__Event _i) x -> ~((Univ _i) x).

Axiom _univ_subsig_Univ :
  forall (_i : Instance) x, (Univ _i) x -> univ x.

Axiom _hw__Address_disjoint_hw__Scope :
forall (_i : Instance) x, (hw__Address _i) x -> ~((hw__Scope _i) x).

Axiom _hw__Scope_disjoint_hw__Address :
forall (_i : Instance) x, (hw__Scope _i) x -> ~((hw__Address _i) x).

Axiom _hw__Address_disjoint_hw__Event :
forall (_i : Instance) x, (hw__Address _i) x -> ~((hw__Event _i) x).

Axiom _hw__Event_disjoint_hw__Address :
forall (_i : Instance) x, (hw__Event _i) x -> ~((hw__Address _i) x).

Axiom _hw__Address_disjoint_sw__Address :
forall (_i : Instance) x, (hw__Address _i) x -> ~((sw__Address _i) x).

Axiom _sw__Address_disjoint_hw__Address :
forall (_i : Instance) x, (sw__Address _i) x -> ~((hw__Address _i) x).

Axiom _hw__Address_disjoint_sw__Scope :
forall (_i : Instance) x, (hw__Address _i) x -> ~((sw__Scope _i) x).

Axiom _sw__Scope_disjoint_hw__Address :
forall (_i : Instance) x, (sw__Scope _i) x -> ~((hw__Address _i) x).

Axiom _hw__Address_disjoint_sw__MemoryOrder :
forall (_i : Instance) x, (hw__Address _i) x -> ~((sw__MemoryOrder _i) x).

Axiom _sw__MemoryOrder_disjoint_hw__Address :
forall (_i : Instance) x, (sw__MemoryOrder _i) x -> ~((hw__Address _i) x).

Axiom _hw__Address_disjoint_sw__Event :
forall (_i : Instance) x, (hw__Address _i) x -> ~((sw__Event _i) x).

Axiom _sw__Event_disjoint_hw__Address :
forall (_i : Instance) x, (sw__Event _i) x -> ~((hw__Address _i) x).

Axiom _univ_subsig_hw__Address :
  forall (_i : Instance) x, (hw__Address _i) x -> univ x.

Axiom _hw__Scope_disjoint_hw__Event :
forall (_i : Instance) x, (hw__Scope _i) x -> ~((hw__Event _i) x).

Axiom _hw__Event_disjoint_hw__Scope :
forall (_i : Instance) x, (hw__Event _i) x -> ~((hw__Scope _i) x).

Axiom _hw__Scope_disjoint_sw__Address :
forall (_i : Instance) x, (hw__Scope _i) x -> ~((sw__Address _i) x).

Axiom _sw__Address_disjoint_hw__Scope :
forall (_i : Instance) x, (sw__Address _i) x -> ~((hw__Scope _i) x).

Axiom _hw__Scope_disjoint_sw__Scope :
forall (_i : Instance) x, (hw__Scope _i) x -> ~((sw__Scope _i) x).

Axiom _sw__Scope_disjoint_hw__Scope :
forall (_i : Instance) x, (sw__Scope _i) x -> ~((hw__Scope _i) x).

Axiom _hw__Scope_disjoint_sw__MemoryOrder :
forall (_i : Instance) x, (hw__Scope _i) x -> ~((sw__MemoryOrder _i) x).

Axiom _sw__MemoryOrder_disjoint_hw__Scope :
forall (_i : Instance) x, (sw__MemoryOrder _i) x -> ~((hw__Scope _i) x).

Axiom _hw__Scope_disjoint_sw__Event :
forall (_i : Instance) x, (hw__Scope _i) x -> ~((sw__Event _i) x).

Axiom _sw__Event_disjoint_hw__Scope :
forall (_i : Instance) x, (sw__Event _i) x -> ~((hw__Scope _i) x).

Axiom _univ_subsig_hw__Scope :
  forall (_i : Instance) x, (hw__Scope _i) x -> univ x.

Axiom _hw__Scope_subsig_hw__Thread :
  forall (_i : Instance) x, (hw__Thread _i) x -> (hw__Scope _i) x.

Axiom _hw__Event_disjoint_sw__Address :
forall (_i : Instance) x, (hw__Event _i) x -> ~((sw__Address _i) x).

Axiom _sw__Address_disjoint_hw__Event :
forall (_i : Instance) x, (sw__Address _i) x -> ~((hw__Event _i) x).

Axiom _hw__Event_disjoint_sw__Scope :
forall (_i : Instance) x, (hw__Event _i) x -> ~((sw__Scope _i) x).

Axiom _sw__Scope_disjoint_hw__Event :
forall (_i : Instance) x, (sw__Scope _i) x -> ~((hw__Event _i) x).

Axiom _hw__Event_disjoint_sw__MemoryOrder :
forall (_i : Instance) x, (hw__Event _i) x -> ~((sw__MemoryOrder _i) x).

Axiom _sw__MemoryOrder_disjoint_hw__Event :
forall (_i : Instance) x, (sw__MemoryOrder _i) x -> ~((hw__Event _i) x).

Axiom _hw__Event_disjoint_sw__Event :
forall (_i : Instance) x, (hw__Event _i) x -> ~((sw__Event _i) x).

Axiom _sw__Event_disjoint_hw__Event :
forall (_i : Instance) x, (sw__Event _i) x -> ~((hw__Event _i) x).

Axiom _univ_subsig_hw__Event :
  forall (_i : Instance) x, (hw__Event _i) x -> univ x.

Axiom _hw__Fence_disjoint_hw__MemoryEvent :
  forall (_i : Instance) x, (hw__Fence _i) x -> ~((hw__MemoryEvent _i) x).

Axiom _hw__MemoryEvent_disjoint_hw__Fence :
  forall (_i : Instance) x, (hw__MemoryEvent _i) x -> ~((hw__Fence _i) x).

Axiom _hw__Fence_disjoint_hw__Barrier :
  forall (_i : Instance) x, (hw__Fence _i) x -> ~((hw__Barrier _i) x).

Axiom _hw__Barrier_disjoint_hw__Fence :
  forall (_i : Instance) x, (hw__Barrier _i) x -> ~((hw__Fence _i) x).

Axiom _hw__MemoryEvent_disjoint_hw__Barrier :
  forall (_i : Instance) x, (hw__MemoryEvent _i) x -> ~((hw__Barrier _i) x).

Axiom _hw__Barrier_disjoint_hw__MemoryEvent :
  forall (_i : Instance) x, (hw__Barrier _i) x -> ~((hw__MemoryEvent _i) x).

Axiom _hw__Event_abstract :
  forall (_i : Instance) x, hw__Event _i x -> (union (hw__Fence _i) (union (hw__MemoryEvent _i) (hw__Barrier _i))) x.

Axiom _hw__Event_subsig_hw__Fence :
  forall (_i : Instance) x, (hw__Fence _i) x -> (hw__Event _i) x.

Axiom _hw__FenceAcq_disjoint_hw__FenceRel :
  forall (_i : Instance) x, (hw__FenceAcq _i) x -> ~((hw__FenceRel _i) x).

Axiom _hw__FenceRel_disjoint_hw__FenceAcq :
  forall (_i : Instance) x, (hw__FenceRel _i) x -> ~((hw__FenceAcq _i) x).

Axiom _hw__FenceAcq_disjoint_hw__FenceAcqRel :
  forall (_i : Instance) x, (hw__FenceAcq _i) x -> ~((hw__FenceAcqRel _i) x).

Axiom _hw__FenceAcqRel_disjoint_hw__FenceAcq :
  forall (_i : Instance) x, (hw__FenceAcqRel _i) x -> ~((hw__FenceAcq _i) x).

Axiom _hw__FenceRel_disjoint_hw__FenceAcqRel :
  forall (_i : Instance) x, (hw__FenceRel _i) x -> ~((hw__FenceAcqRel _i) x).

Axiom _hw__FenceAcqRel_disjoint_hw__FenceRel :
  forall (_i : Instance) x, (hw__FenceAcqRel _i) x -> ~((hw__FenceRel _i) x).

Axiom _hw__Fence_abstract :
  forall (_i : Instance) x, hw__Fence _i x -> (union (hw__FenceAcq _i) (union (hw__FenceRel _i) (hw__FenceAcqRel _i))) x.

Axiom _hw__Event_subsig_hw__MemoryEvent :
  forall (_i : Instance) x, (hw__MemoryEvent _i) x -> (hw__Event _i) x.

Axiom _hw__Read_disjoint_hw__Write :
  forall (_i : Instance) x, (hw__Read _i) x -> ~((hw__Write _i) x).

Axiom _hw__Write_disjoint_hw__Read :
  forall (_i : Instance) x, (hw__Write _i) x -> ~((hw__Read _i) x).

Axiom _hw__MemoryEvent_abstract :
  forall (_i : Instance) x, hw__MemoryEvent _i x -> (union (hw__Read _i) (hw__Write _i)) x.

Axiom _hw__MemoryEvent_subsig_hw__Read :
  forall (_i : Instance) x, (hw__Read _i) x -> (hw__MemoryEvent _i) x.

Axiom _hw__MemoryEvent_subsig_hw__Write :
  forall (_i : Instance) x, (hw__Write _i) x -> (hw__MemoryEvent _i) x.

Axiom _hw__Fence_subsig_hw__FenceAcq :
  forall (_i : Instance) x, (hw__FenceAcq _i) x -> (hw__Fence _i) x.

Axiom _hw__Fence_subsig_hw__FenceRel :
  forall (_i : Instance) x, (hw__FenceRel _i) x -> (hw__Fence _i) x.

Axiom _hw__Fence_subsig_hw__FenceAcqRel :
  forall (_i : Instance) x, (hw__FenceAcqRel _i) x -> (hw__Fence _i) x.

Axiom _hw__FenceAcqRel_subsig_hw__FenceSC :
  forall (_i : Instance) x, (hw__FenceSC _i) x -> (hw__FenceAcqRel _i) x.

Axiom _hw__Read_subsig_hw__Acquire :
  forall (_i : Instance) x, (hw__Acquire _i) x -> (hw__Read _i) x.

Axiom _hw__Write_subsig_hw__Release :
  forall (_i : Instance) x, (hw__Release _i) x -> (hw__Write _i) x.

Axiom _hw__Event_subsig_hw__Barrier :
  forall (_i : Instance) x, (hw__Barrier _i) x -> (hw__Event _i) x.

Axiom _hw__BarrierArrive_disjoint_hw__BarrierWait :
  forall (_i : Instance) x, (hw__BarrierArrive _i) x -> ~((hw__BarrierWait _i) x).

Axiom _hw__BarrierWait_disjoint_hw__BarrierArrive :
  forall (_i : Instance) x, (hw__BarrierWait _i) x -> ~((hw__BarrierArrive _i) x).

Axiom _hw__Barrier_abstract :
  forall (_i : Instance) x, hw__Barrier _i x -> (union (hw__BarrierArrive _i) (hw__BarrierWait _i)) x.

Axiom _hw__Barrier_subsig_hw__BarrierArrive :
  forall (_i : Instance) x, (hw__BarrierArrive _i) x -> (hw__Barrier _i) x.

Axiom _hw__Barrier_subsig_hw__BarrierWait :
  forall (_i : Instance) x, (hw__BarrierWait _i) x -> (hw__Barrier _i) x.

Axiom _sw__Address_disjoint_sw__Scope :
forall (_i : Instance) x, (sw__Address _i) x -> ~((sw__Scope _i) x).

Axiom _sw__Scope_disjoint_sw__Address :
forall (_i : Instance) x, (sw__Scope _i) x -> ~((sw__Address _i) x).

Axiom _sw__Address_disjoint_sw__MemoryOrder :
forall (_i : Instance) x, (sw__Address _i) x -> ~((sw__MemoryOrder _i) x).

Axiom _sw__MemoryOrder_disjoint_sw__Address :
forall (_i : Instance) x, (sw__MemoryOrder _i) x -> ~((sw__Address _i) x).

Axiom _sw__Address_disjoint_sw__Event :
forall (_i : Instance) x, (sw__Address _i) x -> ~((sw__Event _i) x).

Axiom _sw__Event_disjoint_sw__Address :
forall (_i : Instance) x, (sw__Event _i) x -> ~((sw__Address _i) x).

Axiom _univ_subsig_sw__Address :
  forall (_i : Instance) x, (sw__Address _i) x -> univ x.

Axiom _sw__Scope_disjoint_sw__MemoryOrder :
forall (_i : Instance) x, (sw__Scope _i) x -> ~((sw__MemoryOrder _i) x).

Axiom _sw__MemoryOrder_disjoint_sw__Scope :
forall (_i : Instance) x, (sw__MemoryOrder _i) x -> ~((sw__Scope _i) x).

Axiom _sw__Scope_disjoint_sw__Event :
forall (_i : Instance) x, (sw__Scope _i) x -> ~((sw__Event _i) x).

Axiom _sw__Event_disjoint_sw__Scope :
forall (_i : Instance) x, (sw__Event _i) x -> ~((sw__Scope _i) x).

Axiom _univ_subsig_sw__Scope :
  forall (_i : Instance) x, (sw__Scope _i) x -> univ x.

Axiom _sw__Scope_subsig_sw__Thread :
  forall (_i : Instance) x, (sw__Thread _i) x -> (sw__Scope _i) x.

Axiom _sw__MemoryOrder_disjoint_sw__Event :
forall (_i : Instance) x, (sw__MemoryOrder _i) x -> ~((sw__Event _i) x).

Axiom _sw__Event_disjoint_sw__MemoryOrder :
forall (_i : Instance) x, (sw__Event _i) x -> ~((sw__MemoryOrder _i) x).

Axiom _univ_subsig_sw__MemoryOrder :
  forall (_i : Instance) x, (sw__MemoryOrder _i) x -> univ x.

Axiom _sw__MemoryOrderNonAtomic_disjoint_sw__MemoryOrderRelaxed :
  forall (_i : Instance) x, (sw__MemoryOrderNonAtomic _i) x -> ~((sw__MemoryOrderRelaxed _i) x).

Axiom _sw__MemoryOrderRelaxed_disjoint_sw__MemoryOrderNonAtomic :
  forall (_i : Instance) x, (sw__MemoryOrderRelaxed _i) x -> ~((sw__MemoryOrderNonAtomic _i) x).

Axiom _sw__MemoryOrderNonAtomic_disjoint_sw__MemoryOrderAcquire :
  forall (_i : Instance) x, (sw__MemoryOrderNonAtomic _i) x -> ~((sw__MemoryOrderAcquire _i) x).

Axiom _sw__MemoryOrderAcquire_disjoint_sw__MemoryOrderNonAtomic :
  forall (_i : Instance) x, (sw__MemoryOrderAcquire _i) x -> ~((sw__MemoryOrderNonAtomic _i) x).

Axiom _sw__MemoryOrderNonAtomic_disjoint_sw__MemoryOrderRelease :
  forall (_i : Instance) x, (sw__MemoryOrderNonAtomic _i) x -> ~((sw__MemoryOrderRelease _i) x).

Axiom _sw__MemoryOrderRelease_disjoint_sw__MemoryOrderNonAtomic :
  forall (_i : Instance) x, (sw__MemoryOrderRelease _i) x -> ~((sw__MemoryOrderNonAtomic _i) x).

Axiom _sw__MemoryOrderNonAtomic_disjoint_sw__MemoryOrderAcqRel :
  forall (_i : Instance) x, (sw__MemoryOrderNonAtomic _i) x -> ~((sw__MemoryOrderAcqRel _i) x).

Axiom _sw__MemoryOrderAcqRel_disjoint_sw__MemoryOrderNonAtomic :
  forall (_i : Instance) x, (sw__MemoryOrderAcqRel _i) x -> ~((sw__MemoryOrderNonAtomic _i) x).

Axiom _sw__MemoryOrderNonAtomic_disjoint_sw__MemoryOrderSeqCst :
  forall (_i : Instance) x, (sw__MemoryOrderNonAtomic _i) x -> ~((sw__MemoryOrderSeqCst _i) x).

Axiom _sw__MemoryOrderSeqCst_disjoint_sw__MemoryOrderNonAtomic :
  forall (_i : Instance) x, (sw__MemoryOrderSeqCst _i) x -> ~((sw__MemoryOrderNonAtomic _i) x).

Axiom _sw__MemoryOrderRelaxed_disjoint_sw__MemoryOrderAcquire :
  forall (_i : Instance) x, (sw__MemoryOrderRelaxed _i) x -> ~((sw__MemoryOrderAcquire _i) x).

Axiom _sw__MemoryOrderAcquire_disjoint_sw__MemoryOrderRelaxed :
  forall (_i : Instance) x, (sw__MemoryOrderAcquire _i) x -> ~((sw__MemoryOrderRelaxed _i) x).

Axiom _sw__MemoryOrderRelaxed_disjoint_sw__MemoryOrderRelease :
  forall (_i : Instance) x, (sw__MemoryOrderRelaxed _i) x -> ~((sw__MemoryOrderRelease _i) x).

Axiom _sw__MemoryOrderRelease_disjoint_sw__MemoryOrderRelaxed :
  forall (_i : Instance) x, (sw__MemoryOrderRelease _i) x -> ~((sw__MemoryOrderRelaxed _i) x).

Axiom _sw__MemoryOrderRelaxed_disjoint_sw__MemoryOrderAcqRel :
  forall (_i : Instance) x, (sw__MemoryOrderRelaxed _i) x -> ~((sw__MemoryOrderAcqRel _i) x).

Axiom _sw__MemoryOrderAcqRel_disjoint_sw__MemoryOrderRelaxed :
  forall (_i : Instance) x, (sw__MemoryOrderAcqRel _i) x -> ~((sw__MemoryOrderRelaxed _i) x).

Axiom _sw__MemoryOrderRelaxed_disjoint_sw__MemoryOrderSeqCst :
  forall (_i : Instance) x, (sw__MemoryOrderRelaxed _i) x -> ~((sw__MemoryOrderSeqCst _i) x).

Axiom _sw__MemoryOrderSeqCst_disjoint_sw__MemoryOrderRelaxed :
  forall (_i : Instance) x, (sw__MemoryOrderSeqCst _i) x -> ~((sw__MemoryOrderRelaxed _i) x).

Axiom _sw__MemoryOrderAcquire_disjoint_sw__MemoryOrderRelease :
  forall (_i : Instance) x, (sw__MemoryOrderAcquire _i) x -> ~((sw__MemoryOrderRelease _i) x).

Axiom _sw__MemoryOrderRelease_disjoint_sw__MemoryOrderAcquire :
  forall (_i : Instance) x, (sw__MemoryOrderRelease _i) x -> ~((sw__MemoryOrderAcquire _i) x).

Axiom _sw__MemoryOrderAcquire_disjoint_sw__MemoryOrderAcqRel :
  forall (_i : Instance) x, (sw__MemoryOrderAcquire _i) x -> ~((sw__MemoryOrderAcqRel _i) x).

Axiom _sw__MemoryOrderAcqRel_disjoint_sw__MemoryOrderAcquire :
  forall (_i : Instance) x, (sw__MemoryOrderAcqRel _i) x -> ~((sw__MemoryOrderAcquire _i) x).

Axiom _sw__MemoryOrderAcquire_disjoint_sw__MemoryOrderSeqCst :
  forall (_i : Instance) x, (sw__MemoryOrderAcquire _i) x -> ~((sw__MemoryOrderSeqCst _i) x).

Axiom _sw__MemoryOrderSeqCst_disjoint_sw__MemoryOrderAcquire :
  forall (_i : Instance) x, (sw__MemoryOrderSeqCst _i) x -> ~((sw__MemoryOrderAcquire _i) x).

Axiom _sw__MemoryOrderRelease_disjoint_sw__MemoryOrderAcqRel :
  forall (_i : Instance) x, (sw__MemoryOrderRelease _i) x -> ~((sw__MemoryOrderAcqRel _i) x).

Axiom _sw__MemoryOrderAcqRel_disjoint_sw__MemoryOrderRelease :
  forall (_i : Instance) x, (sw__MemoryOrderAcqRel _i) x -> ~((sw__MemoryOrderRelease _i) x).

Axiom _sw__MemoryOrderRelease_disjoint_sw__MemoryOrderSeqCst :
  forall (_i : Instance) x, (sw__MemoryOrderRelease _i) x -> ~((sw__MemoryOrderSeqCst _i) x).

Axiom _sw__MemoryOrderSeqCst_disjoint_sw__MemoryOrderRelease :
  forall (_i : Instance) x, (sw__MemoryOrderSeqCst _i) x -> ~((sw__MemoryOrderRelease _i) x).

Axiom _sw__MemoryOrderAcqRel_disjoint_sw__MemoryOrderSeqCst :
  forall (_i : Instance) x, (sw__MemoryOrderAcqRel _i) x -> ~((sw__MemoryOrderSeqCst _i) x).

Axiom _sw__MemoryOrderSeqCst_disjoint_sw__MemoryOrderAcqRel :
  forall (_i : Instance) x, (sw__MemoryOrderSeqCst _i) x -> ~((sw__MemoryOrderAcqRel _i) x).

Axiom _sw__MemoryOrder_abstract :
  forall (_i : Instance) x, sw__MemoryOrder _i x -> (union (sw__MemoryOrderNonAtomic _i) (union (sw__MemoryOrderRelaxed _i) (union (sw__MemoryOrderAcquire _i) (union (sw__MemoryOrderRelease _i) (union (sw__MemoryOrderAcqRel _i) (sw__MemoryOrderSeqCst _i)))))) x.

Axiom _sw__MemoryOrder_subsig_sw__MemoryOrderNonAtomic :
  forall (_i : Instance) x, (sw__MemoryOrderNonAtomic _i) x -> (sw__MemoryOrder _i) x.

Axiom _sw__MemoryOrder_subsig_sw__MemoryOrderRelaxed :
  forall (_i : Instance) x, (sw__MemoryOrderRelaxed _i) x -> (sw__MemoryOrder _i) x.

Axiom _sw__MemoryOrder_subsig_sw__MemoryOrderAcquire :
  forall (_i : Instance) x, (sw__MemoryOrderAcquire _i) x -> (sw__MemoryOrder _i) x.

Axiom _sw__MemoryOrder_subsig_sw__MemoryOrderRelease :
  forall (_i : Instance) x, (sw__MemoryOrderRelease _i) x -> (sw__MemoryOrder _i) x.

Axiom _sw__MemoryOrder_subsig_sw__MemoryOrderAcqRel :
  forall (_i : Instance) x, (sw__MemoryOrderAcqRel _i) x -> (sw__MemoryOrder _i) x.

Axiom _sw__MemoryOrder_subsig_sw__MemoryOrderSeqCst :
  forall (_i : Instance) x, (sw__MemoryOrderSeqCst _i) x -> (sw__MemoryOrder _i) x.

Axiom _univ_subsig_sw__Event :
  forall (_i : Instance) x, (sw__Event _i) x -> univ x.

Axiom _sw__MemoryEvent_disjoint_sw__Fence :
  forall (_i : Instance) x, (sw__MemoryEvent _i) x -> ~((sw__Fence _i) x).

Axiom _sw__Fence_disjoint_sw__MemoryEvent :
  forall (_i : Instance) x, (sw__Fence _i) x -> ~((sw__MemoryEvent _i) x).

Axiom _sw__Event_abstract :
  forall (_i : Instance) x, sw__Event _i x -> (union (sw__MemoryEvent _i) (sw__Fence _i)) x.

Axiom _sw__Event_subsig_sw__MemoryEvent :
  forall (_i : Instance) x, (sw__MemoryEvent _i) x -> (sw__Event _i) x.

Axiom _sw__Write_disjoint_sw__Read :
  forall (_i : Instance) x, (sw__Write _i) x -> ~((sw__Read _i) x).

Axiom _sw__Read_disjoint_sw__Write :
  forall (_i : Instance) x, (sw__Read _i) x -> ~((sw__Write _i) x).

Axiom _sw__MemoryEvent_abstract :
  forall (_i : Instance) x, sw__MemoryEvent _i x -> (union (sw__Write _i) (sw__Read _i)) x.

Axiom _sw__MemoryEvent_subsig_sw__Write :
  forall (_i : Instance) x, (sw__Write _i) x -> (sw__MemoryEvent _i) x.

Axiom _sw__MemoryEvent_subsig_sw__Read :
  forall (_i : Instance) x, (sw__Read _i) x -> (sw__MemoryEvent _i) x.

Axiom _sw__Event_subsig_sw__Fence :
  forall (_i : Instance) x, (sw__Fence _i) x -> (sw__Event _i) x.

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__add__arg_n1 : forall (_i : Instance) n1 n2 _x,
  integer__add _i n1 n2 _x ->
  inside Int n1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__add__arg_n2 : forall (_i : Instance) n1 n2 _x,
  integer__add _i n1 n2 _x ->
  inside Int n2.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__plus__arg_n1 : forall (_i : Instance) n1 n2 _x,
  integer__plus _i n1 n2 _x ->
  inside Int n1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__plus__arg_n2 : forall (_i : Instance) n1 n2 _x,
  integer__plus _i n1 n2 _x ->
  inside Int n2.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__sub__arg_n1 : forall (_i : Instance) n1 n2 _x,
  integer__sub _i n1 n2 _x ->
  inside Int n1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__sub__arg_n2 : forall (_i : Instance) n1 n2 _x,
  integer__sub _i n1 n2 _x ->
  inside Int n2.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__minus__arg_n1 : forall (_i : Instance) n1 n2 _x,
  integer__minus _i n1 n2 _x ->
  inside Int n1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__minus__arg_n2 : forall (_i : Instance) n1 n2 _x,
  integer__minus _i n1 n2 _x ->
  inside Int n2.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__mul__arg_n1 : forall (_i : Instance) n1 n2 _x,
  integer__mul _i n1 n2 _x ->
  inside Int n1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__mul__arg_n2 : forall (_i : Instance) n1 n2 _x,
  integer__mul _i n1 n2 _x ->
  inside Int n2.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__div__arg_n1 : forall (_i : Instance) n1 n2 _x,
  integer__div _i n1 n2 _x ->
  inside Int n1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__div__arg_n2 : forall (_i : Instance) n1 n2 _x,
  integer__div _i n1 n2 _x ->
  inside Int n2.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__rem__arg_n1 : forall (_i : Instance) n1 n2 _x,
  integer__rem _i n1 n2 _x ->
  inside Int n1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__rem__arg_n2 : forall (_i : Instance) n1 n2 _x,
  integer__rem _i n1 n2 _x ->
  inside Int n2.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__negate__arg_n : forall (_i : Instance) n _x,
  integer__negate _i n _x ->
  inside Int n.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__eq__arg_n1 : forall (_i : Instance) n1 n2,
  integer__eq _i n1 n2 ->
  inside Int n1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__eq__arg_n2 : forall (_i : Instance) n1 n2,
  integer__eq _i n1 n2 ->
  inside Int n2.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__gt__arg_n1 : forall (_i : Instance) n1 n2,
  integer__gt _i n1 n2 ->
  inside Int n1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__gt__arg_n2 : forall (_i : Instance) n1 n2,
  integer__gt _i n1 n2 ->
  inside Int n2.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__lt__arg_n1 : forall (_i : Instance) n1 n2,
  integer__lt _i n1 n2 ->
  inside Int n1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__lt__arg_n2 : forall (_i : Instance) n1 n2,
  integer__lt _i n1 n2 ->
  inside Int n2.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__gte__arg_n1 : forall (_i : Instance) n1 n2,
  integer__gte _i n1 n2 ->
  inside Int n1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__gte__arg_n2 : forall (_i : Instance) n1 n2,
  integer__gte _i n1 n2 ->
  inside Int n2.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__lte__arg_n1 : forall (_i : Instance) n1 n2,
  integer__lte _i n1 n2 ->
  inside Int n1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__lte__arg_n2 : forall (_i : Instance) n1 n2,
  integer__lte _i n1 n2 ->
  inside Int n2.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__zero__arg_n : forall (_i : Instance) n,
  integer__zero _i n ->
  inside Int n.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__pos__arg_n : forall (_i : Instance) n,
  integer__pos _i n ->
  inside Int n.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__neg__arg_n : forall (_i : Instance) n,
  integer__neg _i n ->
  inside Int n.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__nonpos__arg_n : forall (_i : Instance) n,
  integer__nonpos _i n ->
  inside Int n.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__nonneg__arg_n : forall (_i : Instance) n,
  integer__nonneg _i n ->
  inside Int n.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__signum__arg_n : forall (_i : Instance) n _x,
  integer__signum _i n _x ->
  inside Int n.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__int2elem__arg_i : forall (_i : Instance) i next s _x,
  integer__int2elem _i i next s _x ->
  inside Int i.
*)
*)

(* some feature not yet supported *)
(*Axiom _integer__int2elem__arg_next : forall (_i : Instance) i next s _x,
  integer__int2elem _i i next s _x ->
  inside (arrow (m:=0) (n:=0) univ univ) next.
*)

(* some feature not yet supported *)
(*Axiom _integer__int2elem__arg_s : forall (_i : Instance) i next s _x,
  integer__int2elem _i i next s _x ->
  inside (setof univ) s.
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__elem2int__arg_e : forall (_i : Instance) e next _x,
  integer__elem2int _i e next _x ->
  inside univ e.
*)
*)

(* some feature not yet supported *)
(*Axiom _integer__elem2int__arg_next : forall (_i : Instance) e next _x,
  integer__elem2int _i e next _x ->
  inside (arrow (m:=0) (n:=0) univ univ) next.
*)

(* some feature not yet supported *)
(*Axiom _integer__max__arg_es : forall (_i : Instance) es _x,
  integer__max _i es _x ->
  inside (setof Int) es.
*)

(* some feature not yet supported *)
(*Axiom _integer__min__arg_es : forall (_i : Instance) es _x,
  integer__min _i es _x ->
  inside (setof Int) es.
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__prevs__arg_e : forall (_i : Instance) e _x,
  integer__prevs _i e _x ->
  inside Int e.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__nexts__arg_e : forall (_i : Instance) e _x,
  integer__nexts _i e _x ->
  inside Int e.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__larger__arg_e1 : forall (_i : Instance) e1 e2 _x,
  integer__larger _i e1 e2 _x ->
  inside Int e1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__larger__arg_e2 : forall (_i : Instance) e1 e2 _x,
  integer__larger _i e1 e2 _x ->
  inside Int e2.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__smaller__arg_e1 : forall (_i : Instance) e1 e2 _x,
  integer__smaller _i e1 e2 _x ->
  inside Int e1.
*)
*)

(* some feature not yet supported *)
(*(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _integer__smaller__arg_e2 : forall (_i : Instance) e1 e2 _x,
  integer__smaller _i e1 e2 _x ->
  inside Int e2.
*)
*)

Axiom _util__symmetric__arg_r : forall (_i : Instance) r _x,
  util__symmetric _i r _x ->
  inside (arrow (m:=0) (n:=0) univ univ) r.

Axiom _util__optional__arg_f : forall (_i : Instance) f _x,
  util__optional _i f _x ->
  inside (arrow (m:=0) (n:=0) univ univ) f.

Axiom _util__irreflexive__arg_rel : forall (_i : Instance) rel,
  util__irreflexive _i rel ->
  inside (arrow (m:=0) (n:=0) univ univ) rel.

Axiom _util__acyclic__arg_rel : forall (_i : Instance) rel,
  util__acyclic _i rel ->
  inside (arrow (m:=0) (n:=0) univ univ) rel.

Axiom _util__total__arg_rel : forall (_i : Instance) rel bag,
  util__total _i rel bag ->
  inside (arrow (m:=0) (n:=0) univ univ) rel.

(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _util__total__arg_bag : forall (_i : Instance) rel bag,
  util__total _i rel bag ->
  inside univ bag.
*)

(* skipping axiom for unsupported builtin argument type *)
(*
Axiom _util__ident__arg_e : forall (_i : Instance) e _x,
  util__ident _i e _x ->
  inside univ e.
*)

Axiom _util__imm__arg_rel : forall (_i : Instance) rel _x,
  util__imm _i rel _x ->
  inside (arrow (m:=0) (n:=0) univ univ) rel.

Axiom _util__transitive__arg_rel : forall (_i : Instance) rel,
  util__transitive _i rel ->
  inside (arrow (m:=0) (n:=0) univ univ) rel.

Axiom _util__strict_partial__arg_rel : forall (_i : Instance) rel,
  util__strict_partial _i rel ->
  inside (arrow (m:=0) (n:=0) univ univ) rel.

Axiom _hw__same_thread__arg_rel : forall (_i : Instance) rel _x,
  hw__same_thread _i rel _x ->
  inside (arrow (m:=0) (n:=0) (hw__Event _i) (hw__Event _i)) rel.

Axiom _hw__location__arg_rel : forall (_i : Instance) rel _x,
  hw__location _i rel _x ->
  inside (arrow (m:=0) (n:=0) (hw__Event _i) (hw__Event _i)) rel.

Axiom _hw__sync__arg_head : forall (_i : Instance) head tail _x,
  hw__sync _i head tail _x ->
  inside (hw__Event _i) head.

Axiom _hw__sync__arg_tail : forall (_i : Instance) head tail _x,
  hw__sync _i head tail _x ->
  inside (hw__Event _i) tail.

Axiom _hw__typed__arg_rel : forall (_i : Instance) rel type _x,
  hw__typed _i rel type _x ->
  inside (arrow (m:=0) (n:=0) (hw__Event _i) (hw__Event _i)) rel.

Axiom _hw__typed__arg_type : forall (_i : Instance) rel type _x,
  hw__typed _i rel type _x ->
  inside (hw__Event _i) type.

Axiom _hw__inside__arg_s : forall (_i : Instance) s _x,
  hw__inside _i s _x ->
  inside (hw__Scope _i) s.

Axiom _hw__scoped__arg_s : forall (_i : Instance) s _x,
  hw__scoped _i s _x ->
  inside (hw__Scope _i) s.

Axiom _hw__weak__arg_r : forall (_i : Instance) r _x,
  hw__weak _i r _x ->
  inside (arrow (m:=0) (n:=0) (hw__Event _i) (hw__Event _i)) r.

Axiom _hw__strong__arg_r : forall (_i : Instance) r _x,
  hw__strong _i r _x ->
  inside (arrow (m:=0) (n:=0) (hw__Event _i) (hw__Event _i)) r.

Axiom _hw__is_strong__arg_r : forall (_i : Instance) r,
  hw__is_strong _i r ->
  inside (arrow (m:=0) (n:=0) (hw__Event _i) (hw__Event _i)) r.

Axiom _sw__strong__arg_r : forall (_i : Instance) r _x,
  sw__strong _i r _x ->
  inside (arrow (m:=0) (n:=0) (sw__Event _i) (sw__Event _i)) r.

Axiom one_system : forall (_i : Instance),
(* one hw/System*)
(* dep: hw__System *)
(one (hw__System _i)).

Axiom com_addr : forall (_i : Instance),
(* (hw/Write <: co) + (hw/Write <: rf) + hw/fr in (hw/MemoryEvent <: address) . ~ (hw/MemoryEvent <: address)*)
(* dep: hw__fr *)
(inside (join (m:=1) (n:=1) (hw__MemoryEvent__address _i) (transpose (n:=1) (hw__MemoryEvent__address _i))) (union (n:=2) (union (n:=2) (hw__Write__co _i) (hw__Write__rf _i)) (hw__fr _i))).

Axiom po_acyclic : forall (_i : Instance),
(* util/acyclic[(hw/Event <: po)]*)
(* dep: util__acyclic *)
(util__acyclic _i (hw__Event__po _i)).

Axiom some_thread : forall (_i : Instance),
(* (all e | (one t | t -> e in (hw/Thread <: start) . * (hw/Event <: po)))*)
(forall e, (oneof (hw__Event _i)) e -> (exists! t, ((oneof (hw__Thread _i)) t) /\ (inside (join (m:=1) (n:=1) (hw__Thread__start _i) (rtc (hw__Event__po _i))) (arrow (m:=0) (n:=0) t e)))).

Axiom lone_source_write : forall (_i : Instance),
(* (hw/Write <: rf) . ~ (hw/Write <: rf) in iden*)
(inside iden (join (m:=1) (n:=1) (hw__Write__rf _i) (transpose (n:=1) (hw__Write__rf _i)))).

Axiom dep_facts : forall (_i : Instance),
(* (hw/Read <: dep) in ^ (hw/Event <: po)*)
(inside (tc (hw__Event__po _i)) (hw__Read__dep _i)).

Axiom rmw_facts : forall (_i : Instance),
(* (hw/Read <: rmw) in (hw/Event <: po) & (hw/Read <: dep) & (hw/MemoryEvent <: address) . ~ (hw/MemoryEvent <: address) & (hw/Event <: scope) . ~ (hw/Event <: scope)*)
(inside (intersect (intersect (intersect (hw__Event__po _i) (hw__Read__dep _i)) (join (m:=1) (n:=1) (hw__MemoryEvent__address _i) (transpose (n:=1) (hw__MemoryEvent__address _i)))) (join (m:=1) (n:=1) (hw__Event__scope _i) (transpose (n:=1) (hw__Event__scope _i)))) (hw__Read__rmw _i)).

Axiom inv_subscope : forall (_i : Instance),
(* (hw/Scope <: subscope) . ~ (hw/Scope <: subscope) in iden*)
(inside iden (join (m:=1) (n:=1) (hw__Scope__subscope _i) (transpose (n:=1) (hw__Scope__subscope _i)))).

Axiom thread_subscope : forall (_i : Instance),
(* no hw/Thread . (hw/Scope <: subscope)*)
(no (join (m:=0) (n:=1) (hw__Thread _i) (hw__Scope__subscope _i))).

Axiom subscope_acyclic : forall (_i : Instance),
(* util/acyclic[(hw/Scope <: subscope)]*)
(* dep: util__acyclic *)
(util__acyclic _i (hw__Scope__subscope _i)).

Axiom obs_in_rf_rmw : forall (_i : Instance),
(* (hw/MemoryEvent <: observation) in ^ hw/strong[(hw/Write <: rf)] + (hw/Read <: rmw)*)
(* dep: hw__strong *)
(inside (tc (union (n:=2) (hw__strong _i (hw__Write__rf _i)) (hw__Read__rmw _i))) (hw__MemoryEvent__observation _i)).

Axiom rf_obs : forall (_i : Instance),
(* hw/strong[(hw/Write <: rf)] in (hw/MemoryEvent <: observation)*)
(* dep: hw__strong *)
(inside (hw__MemoryEvent__observation _i) (hw__strong _i (hw__Write__rf _i))).

Axiom rmw_obs : forall (_i : Instance),
(* (hw/MemoryEvent <: observation) . (hw/Read <: rmw) . (hw/MemoryEvent <: observation) in (hw/MemoryEvent <: observation)*)
(inside (hw__MemoryEvent__observation _i) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (hw__MemoryEvent__observation _i) (hw__Read__rmw _i)) (hw__MemoryEvent__observation _i))).

Axiom co_per_scope : forall (_i : Instance),
(* (all a | (all s | util/total[(hw/Write <: co), hw/scoped[s] & hw/inside[s] & a . ~ (hw/MemoryEvent <: address) & hw/Write]))*)
(* dep: util__total *)
(* dep: hw__scoped *)
(* dep: hw__inside *)
(forall a, (oneof (hw__Address _i)) a -> (forall s, (oneof (hw__Scope _i)) s -> (util__total _i (hw__Write__co _i) (intersect (intersect (hw__scoped _i s) (hw__inside _i s)) (intersect (join (m:=0) (n:=1) a (transpose (n:=1) (hw__MemoryEvent__address _i))) (hw__Write _i)))))).

Axiom scope_inclusion : forall (_i : Instance),
(* (hw/Event <: scope) in * ~ (hw/Event <: po) . ~ (hw/Thread <: start) . * ~ (hw/Scope <: subscope)*)
(inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (rtc (transpose (n:=1) (hw__Event__po _i))) (transpose (n:=1) (hw__Thread__start _i))) (rtc (transpose (n:=1) (hw__Scope__subscope _i)))) (hw__Event__scope _i)).

Axiom _ptx_fact15 : forall (_i : Instance),
(* (all b | some b . (hw/BarrierArrive <: synchronizes))*)
(forall b, (oneof (hw__BarrierArrive _i)) b -> (some (join (m:=0) (n:=1) b (hw__BarrierArrive__synchronizes _i)))).

Axiom _ptx_fact16 : forall (_i : Instance),
(* (all b | some b . ~ (hw/BarrierArrive <: synchronizes))*)
(forall b, (oneof (hw__BarrierWait _i)) b -> (some (join (m:=0) (n:=1) b (transpose (n:=1) (hw__BarrierArrive__synchronizes _i))))).

Axiom _ptx_fact17 : forall (_i : Instance),
(* hw/BarrierWait in hw/BarrierArrive . (hw/Event <: po) & (hw/BarrierArrive <: synchronizes)*)
(inside (join (m:=0) (n:=1) (hw__BarrierArrive _i) (intersect (hw__Event__po _i) (hw__BarrierArrive__synchronizes _i))) (hw__BarrierWait _i)).

Axiom _ptx_fact18 : forall (_i : Instance),
(* (hw/BarrierArrive <: synchronizes) . ~ (hw/BarrierArrive <: synchronizes) . (hw/BarrierArrive <: synchronizes) in (hw/BarrierArrive <: synchronizes)*)
(inside (hw__BarrierArrive__synchronizes _i) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (hw__BarrierArrive__synchronizes _i) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i))) (hw__BarrierArrive__synchronizes _i))).

Axiom _ptx_fact19 : forall (_i : Instance),
(* ~ (hw/BarrierArrive <: synchronizes) . (hw/BarrierArrive <: synchronizes) . ~ (hw/BarrierArrive <: synchronizes) in ~ (hw/BarrierArrive <: synchronizes)*)
(inside (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)) (hw__BarrierArrive__synchronizes _i)) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)))).

Axiom _ptx_fact20 : forall (_i : Instance),
(* no ^ (hw/Event <: po) & (hw/BarrierArrive <: synchronizes) . ~ (hw/BarrierArrive <: synchronizes)*)
(no (intersect (tc (hw__Event__po _i)) (join (m:=1) (n:=1) (hw__BarrierArrive__synchronizes _i) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i))))).

Axiom _ptx_fact21 : forall (_i : Instance),
(* no ^ (hw/Event <: po) & ~ (hw/BarrierArrive <: synchronizes) . (hw/BarrierArrive <: synchronizes)*)
(no (intersect (tc (hw__Event__po _i)) (join (m:=1) (n:=1) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)) (hw__BarrierArrive__synchronizes _i)))).

Axiom _ptx_fact22 : forall (_i : Instance),
(* hw/is_strong[(hw/BarrierArrive <: synchronizes)]*)
(* dep: hw__is_strong *)
(hw__is_strong _i (hw__BarrierArrive__synchronizes _i)).

Axiom wf_sc : forall (_i : Instance),
(* AND[(all f1,f2 | f1 -> f2 in hw/strong_r => OR[f1 -> f2 in (hw/FenceSC <: sc), f2 -> f1 in (hw/FenceSC <: sc)]), (hw/FenceSC <: sc) in hw/typed[hw/strong_r, hw/FenceSC], util/acyclic[(hw/FenceSC <: sc)]]*)
(* dep: util__acyclic *)
(* dep: hw__strong_r *)
(* dep: hw__typed *)
( (forall f1, (oneof (hw__FenceSC _i)) f1 -> (forall f2, (oneof (hw__FenceSC _i)) f2 -> f2 <> f1 ->((inside (hw__strong_r _i) (arrow (m:=0) (n:=0) f1 f2)) -> ( (inside (hw__FenceSC__sc _i) (arrow (m:=0) (n:=0) f1 f2)) \/ (inside (hw__FenceSC__sc _i) (arrow (m:=0) (n:=0) f2 f1)))))) /\ (inside (hw__typed _i (hw__strong_r _i) (hw__FenceSC _i)) (hw__FenceSC__sc _i)) /\ (util__acyclic _i (hw__FenceSC__sc _i))).

Axiom _src11_fact24 : forall (_i : Instance),
(* one sw/System*)
(* dep: sw__System *)
(one (sw__System _i)).

Axiom _src11_fact25 : forall (_i : Instance),
(* (sw/Scope <: subscope) . ~ (sw/Scope <: subscope) in iden*)
(inside iden (join (m:=1) (n:=1) (sw__Scope__subscope _i) (transpose (n:=1) (sw__Scope__subscope _i)))).

Axiom _src11_fact26 : forall (_i : Instance),
(* no sw/Thread . (sw/Scope <: subscope)*)
(no (join (m:=0) (n:=1) (sw__Thread _i) (sw__Scope__subscope _i))).

Axiom _src11_fact27 : forall (_i : Instance),
(* util/acyclic[(sw/Scope <: subscope)]*)
(* dep: util__acyclic *)
(util__acyclic _i (sw__Scope__subscope _i)).

Axiom _src11_fact28 : forall (_i : Instance),
(* no sw/A . (sw/Event <: scope) & sw/Thread*)
(* dep: sw__A *)
(no (intersect (join (m:=0) (n:=1) (sw__A _i) (sw__Event__scope _i)) (sw__Thread _i))).

Axiom _src11_fact29 : forall (_i : Instance),
(* sw/NA . (sw/Event <: scope) in sw/Thread*)
(* dep: sw__NA *)
(inside (sw__Thread _i) (join (m:=0) (n:=1) (sw__NA _i) (sw__Event__scope _i))).

Axiom threads_unique : forall (_i : Instance),
(* (sw/Thread <: start) . ~ (sw/Thread <: start) in iden*)
(inside iden (join (m:=1) (n:=1) (sw__Thread__start _i) (transpose (n:=1) (sw__Thread__start _i)))).

Axiom events_in_threads : forall (_i : Instance),
(* (all e | one e . * ~ (sw/Event <: sb) . ~ (sw/Thread <: start))*)
(forall e, (oneof (sw__Event _i)) e -> (one (join (m:=0) (n:=1) (join (m:=0) (n:=1) e (rtc (transpose (n:=1) (sw__Event__sb _i)))) (transpose (n:=1) (sw__Thread__start _i))))).

Axiom WriteMO : forall (_i : Instance),
(* (all w | w . (sw/Event <: memory_order) in sw/MemoryOrderNonAtomic + sw/MemoryOrderRelaxed + sw/MemoryOrderRelease)*)
(forall w, (oneof (sw__Write _i)) w -> (inside (union (n:=1) (union (n:=1) (sw__MemoryOrderNonAtomic _i) (sw__MemoryOrderRelaxed _i)) (sw__MemoryOrderRelease _i)) (join (m:=0) (n:=1) w (sw__Event__memory_order _i)))).

Axiom ReadMO : forall (_i : Instance),
(* (all r | r . (sw/Event <: memory_order) in sw/MemoryOrderNonAtomic + sw/MemoryOrderRelaxed + sw/MemoryOrderAcquire)*)
(forall r, (oneof (sw__Read _i)) r -> (inside (union (n:=1) (union (n:=1) (sw__MemoryOrderNonAtomic _i) (sw__MemoryOrderRelaxed _i)) (sw__MemoryOrderAcquire _i)) (join (m:=0) (n:=1) r (sw__Event__memory_order _i)))).

Axiom RMWMO : forall (_i : Instance),
(* (sw/Read <: rmw) in (sw/Event <: memory_order) . sw/MemoryOrderRelaxed -> sw/MemoryOrderRelaxed + sw/MemoryOrderAcquire -> sw/MemoryOrderRelaxed + sw/MemoryOrderRelaxed -> sw/MemoryOrderRelease + sw/MemoryOrderAcquire -> sw/MemoryOrderRelease + sw/MemoryOrderSeqCst -> sw/MemoryOrderSeqCst . ~ (sw/Event <: memory_order)*)
(inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__Event__memory_order _i) (union (n:=2) (union (n:=2) (union (n:=2) (union (n:=2) (arrow (m:=0) (n:=0) (sw__MemoryOrderRelaxed _i) (sw__MemoryOrderRelaxed _i)) (arrow (m:=0) (n:=0) (sw__MemoryOrderAcquire _i) (sw__MemoryOrderRelaxed _i))) (arrow (m:=0) (n:=0) (sw__MemoryOrderRelaxed _i) (sw__MemoryOrderRelease _i))) (arrow (m:=0) (n:=0) (sw__MemoryOrderAcquire _i) (sw__MemoryOrderRelease _i))) (arrow (m:=0) (n:=0) (sw__MemoryOrderSeqCst _i) (sw__MemoryOrderSeqCst _i)))) (transpose (n:=1) (sw__Event__memory_order _i))) (sw__Read__rmw _i)).

Axiom FenceMO : forall (_i : Instance),
(* (all f | f . (sw/Event <: memory_order) in sw/MemoryOrderAcquire + sw/MemoryOrderRelease + sw/MemoryOrderAcqRel + sw/MemoryOrderSeqCst)*)
(forall f, (oneof (sw__Fence _i)) f -> (inside (union (n:=1) (union (n:=1) (union (n:=1) (sw__MemoryOrderAcquire _i) (sw__MemoryOrderRelease _i)) (sw__MemoryOrderAcqRel _i)) (sw__MemoryOrderSeqCst _i)) (join (m:=0) (n:=1) f (sw__Event__memory_order _i)))).

Axiom com_loc : forall (_i : Instance),
(* (sw/Write <: rf) + (sw/Write <: mo) + sw/rb in sw/loc*)
(* dep: sw__rb *)
(* dep: sw__loc *)
(inside (sw__loc _i) (union (n:=2) (union (n:=2) (sw__Write__rf _i) (sw__Write__mo _i)) (sw__rb _i))).

Axiom strict_partial_sb : forall (_i : Instance),
(* util/strict_partial[(sw/Event <: sb)]*)
(* dep: util__strict_partial *)
(util__strict_partial _i (sw__Event__sb _i)).

Axiom one_source_write : forall (_i : Instance),
(* (sw/Write <: rf) . ~ (sw/Write <: rf) in iden*)
(inside iden (join (m:=1) (n:=1) (sw__Write__rf _i) (transpose (n:=1) (sw__Write__rf _i)))).

Axiom strict_partial_mo : forall (_i : Instance),
(* util/strict_partial[(sw/Write <: mo)]*)
(* dep: util__strict_partial *)
(util__strict_partial _i (sw__Write__mo _i)).

Axiom mo_total_per_address : forall (_i : Instance),
(* (all a | util/total[(sw/Write <: mo), a . ~ (sw/MemoryEvent <: address) :> sw/Write])*)
(* dep: util__total *)
(forall a, (oneof (sw__Address _i)) a -> (util__total _i (sw__Write__mo _i) (range (m:=0) (n:=0) (join (m:=0) (n:=1) a (transpose (n:=1) (sw__MemoryEvent__address _i))) (sw__Write _i)))).

Axiom rmw_sbimm : forall (_i : Instance),
(* AND[(sw/Read <: rmw) in util/imm[(sw/Event <: sb)] & sw/loc, (sw/Event <: sb) . ~ (sw/Read <: rmw) in (sw/Event <: sb)]*)
(* dep: util__imm *)
(* dep: sw__loc *)
( (inside (intersect (util__imm _i (sw__Event__sb _i)) (sw__loc _i)) (sw__Read__rmw _i)) /\ (inside (sw__Event__sb _i) (join (m:=1) (n:=1) (sw__Event__sb _i) (transpose (n:=1) (sw__Read__rmw _i))))).

Definition compile_src11_ptx_legal_statement : Prop := forall (_i : Instance),
((compile_src11_ptx _i) -> (sw__src11 _i)).

Definition compile_src11_ptx_nonta_legal_statement : Prop := forall (_i : Instance),
((compile_src11_ptx _i) -> ( (sw__coherence _i) /\ (sw__atomicity _i) /\ (sw__sc _i))).

Definition src11_ptx_legal_coherence_statement : Prop := forall (_i : Instance),
((compile_src11_ptx _i) -> (sw__coherence _i)).

Definition src11_ptx_legal_atomicity_statement : Prop := forall (_i : Instance),
((compile_src11_ptx _i) -> (sw__atomicity _i)).

Definition src11_ptx_legal_sc_statement : Prop := forall (_i : Instance),
((compile_src11_ptx _i) -> (sw__sc _i)).

Definition src11_ptx_legal_no_thin_air_statement : Prop := forall (_i : Instance),
((compile_src11_ptx _i) -> (sw__no_thin_air _i)).

Definition sb_syncacqrel_statement : Prop := forall (_i : Instance),
((compile_src11_ptx _i) -> (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__Event__map _i) (tc (hw__Event__po _i))) (transpose (n:=1) (sw__Event__map _i))) (sw__Event__sb _i))).

Definition sw_syncacqrel_statement : Prop := forall (_i : Instance),
((compile_src11_ptx _i) -> (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__Event__map _i) (syncacqrel _i)) (transpose (n:=1) (sw__Event__map _i))) (sw__strong _i (sw__sw _i)))).

Definition hb_syncacqrel_statement : Prop := forall (_i : Instance),
((compile_src11_ptx _i) -> (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__Event__map _i) (union (n:=2) (tc (hw__Event__po _i)) (tc (syncacqrel _i)))) (transpose (n:=1) (sw__Event__map _i))) (sw__hb _i))).

Definition psc_F_statement : Prop := forall (_i : Instance),
((compile_src11_ptx _i) -> (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (util__optional _i (sw__hb _i)) (union (n:=2) (sw__hb _i) (sw__eco _i))) (util__optional _i (sw__hb _i))) (sw__psc _i))).

Definition ecos_equal_statement : Prop := forall (_i : Instance),
(equal (n:=2) (sw__eco _i) (join (m:=1) (n:=1) (union (n:=2) (union (n:=2) (sw__Write__rf _i) (sw__Write__mo _i)) (sw__rb _i)) (util__optional _i (sw__Write__rf _i)))).

Definition sanity_statement : Prop := exists _i,
(* AND[one hw/System, (hw/Write <: co) + (hw/Write <: rf) + hw/fr in (hw/MemoryEvent <: address) . ~ (hw/MemoryEvent <: address), util/acyclic[(hw/Event <: po)], (all e | (one t | t -> e in (hw/Thread <: start) . * (hw/Event <: po))), (hw/Write <: rf) . ~ (hw/Write <: rf) in iden, (hw/Read <: dep) in ^ (hw/Event <: po), (hw/Read <: rmw) in (hw/Event <: po) & (hw/Read <: dep) & (hw/MemoryEvent <: address) . ~ (hw/MemoryEvent <: address) & (hw/Event <: scope) . ~ (hw/Event <: scope), (hw/Scope <: subscope) . ~ (hw/Scope <: subscope) in iden, no hw/Thread . (hw/Scope <: subscope), util/acyclic[(hw/Scope <: subscope)], (hw/MemoryEvent <: observation) in ^ hw/strong[(hw/Write <: rf)] + (hw/Read <: rmw), hw/strong[(hw/Write <: rf)] in (hw/MemoryEvent <: observation), (hw/MemoryEvent <: observation) . (hw/Read <: rmw) . (hw/MemoryEvent <: observation) in (hw/MemoryEvent <: observation), (all a | (all s | util/total[(hw/Write <: co), hw/scoped[s] & hw/inside[s] & a . ~ (hw/MemoryEvent <: address) & hw/Write])), (hw/Event <: scope) in * ~ (hw/Event <: po) . ~ (hw/Thread <: start) . * ~ (hw/Scope <: subscope), (all b | some b . (hw/BarrierArrive <: synchronizes)), (all b | some b . ~ (hw/BarrierArrive <: synchronizes)), hw/BarrierWait in hw/BarrierArrive . (hw/Event <: po) & (hw/BarrierArrive <: synchronizes), (hw/BarrierArrive <: synchronizes) . ~ (hw/BarrierArrive <: synchronizes) . (hw/BarrierArrive <: synchronizes) in (hw/BarrierArrive <: synchronizes), ~ (hw/BarrierArrive <: synchronizes) . (hw/BarrierArrive <: synchronizes) . ~ (hw/BarrierArrive <: synchronizes) in ~ (hw/BarrierArrive <: synchronizes), no ^ (hw/Event <: po) & (hw/BarrierArrive <: synchronizes) . ~ (hw/BarrierArrive <: synchronizes), no ^ (hw/Event <: po) & ~ (hw/BarrierArrive <: synchronizes) . (hw/BarrierArrive <: synchronizes), hw/is_strong[(hw/BarrierArrive <: synchronizes)], (all f1,f2 | f1 -> f2 in hw/strong_r => OR[f1 -> f2 in (hw/FenceSC <: sc), f2 -> f1 in (hw/FenceSC <: sc)]), (hw/FenceSC <: sc) in hw/typed[hw/strong_r, hw/FenceSC], util/acyclic[(hw/FenceSC <: sc)], one sw/System, (sw/Event <: scope) in * ~ (sw/Event <: sb) . ~ (sw/Thread <: start) . * ~ (sw/Scope <: subscope), (sw/Scope <: subscope) . ~ (sw/Scope <: subscope) in iden, no sw/Thread . (sw/Scope <: subscope), util/acyclic[(sw/Scope <: subscope)], no sw/A . (sw/Event <: scope) & sw/Thread, sw/NA . (sw/Event <: scope) in sw/Thread, (sw/Thread <: start) . ~ (sw/Thread <: start) in iden, (all e | one e . * ~ (sw/Event <: sb) . ~ (sw/Thread <: start)), (all w | w . (sw/Event <: memory_order) in sw/MemoryOrderNonAtomic + sw/MemoryOrderRelaxed + sw/MemoryOrderRelease), (all r | r . (sw/Event <: memory_order) in sw/MemoryOrderNonAtomic + sw/MemoryOrderRelaxed + sw/MemoryOrderAcquire), (sw/Read <: rmw) in (sw/Event <: memory_order) . sw/MemoryOrderRelaxed -> sw/MemoryOrderRelaxed + sw/MemoryOrderAcquire -> sw/MemoryOrderRelaxed + sw/MemoryOrderRelaxed -> sw/MemoryOrderRelease + sw/MemoryOrderAcquire -> sw/MemoryOrderRelease + sw/MemoryOrderSeqCst -> sw/MemoryOrderSeqCst . ~ (sw/Event <: memory_order), (all f | f . (sw/Event <: memory_order) in sw/MemoryOrderAcquire + sw/MemoryOrderRelease + sw/MemoryOrderAcqRel + sw/MemoryOrderSeqCst), (sw/Write <: rf) + (sw/Write <: mo) + sw/rb in sw/loc, util/strict_partial[(sw/Event <: sb)], (sw/Write <: rf) . ~ (sw/Write <: rf) in iden, util/strict_partial[(sw/Write <: mo)], (all a | util/total[(sw/Write <: mo), a . ~ (sw/MemoryEvent <: address) :> sw/Write]), (sw/Read <: rmw) in util/imm[(sw/Event <: sb)] & sw/loc, (sw/Event <: sb) . ~ (sw/Read <: rmw) in (sw/Event <: sb), some hw/Read, this/compile_src11_ptx] *)
( (one (hw__System _i)) /\ (inside (join (m:=1) (n:=1) (hw__MemoryEvent__address _i) (transpose (n:=1) (hw__MemoryEvent__address _i))) (union (n:=2) (union (n:=2) (hw__Write__co _i) (hw__Write__rf _i)) (hw__fr _i))) /\ (util__acyclic _i (hw__Event__po _i)) /\ (forall e, (oneof (hw__Event _i)) e -> (exists! t, ((oneof (hw__Thread _i)) t) /\ (inside (join (m:=1) (n:=1) (hw__Thread__start _i) (rtc (hw__Event__po _i))) (arrow (m:=0) (n:=0) t e)))) /\ (inside iden (join (m:=1) (n:=1) (hw__Write__rf _i) (transpose (n:=1) (hw__Write__rf _i)))) /\ (inside (tc (hw__Event__po _i)) (hw__Read__dep _i)) /\ (inside (intersect (intersect (intersect (hw__Event__po _i) (hw__Read__dep _i)) (join (m:=1) (n:=1) (hw__MemoryEvent__address _i) (transpose (n:=1) (hw__MemoryEvent__address _i)))) (join (m:=1) (n:=1) (hw__Event__scope _i) (transpose (n:=1) (hw__Event__scope _i)))) (hw__Read__rmw _i)) /\ (inside iden (join (m:=1) (n:=1) (hw__Scope__subscope _i) (transpose (n:=1) (hw__Scope__subscope _i)))) /\ (no (join (m:=0) (n:=1) (hw__Thread _i) (hw__Scope__subscope _i))) /\ (util__acyclic _i (hw__Scope__subscope _i)) /\ (inside (tc (union (n:=2) (hw__strong _i (hw__Write__rf _i)) (hw__Read__rmw _i))) (hw__MemoryEvent__observation _i)) /\ (inside (hw__MemoryEvent__observation _i) (hw__strong _i (hw__Write__rf _i))) /\ (inside (hw__MemoryEvent__observation _i) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (hw__MemoryEvent__observation _i) (hw__Read__rmw _i)) (hw__MemoryEvent__observation _i))) /\ (forall a, (oneof (hw__Address _i)) a -> (forall s, (oneof (hw__Scope _i)) s -> (util__total _i (hw__Write__co _i) (intersect (intersect (hw__scoped _i s) (hw__inside _i s)) (intersect (join (m:=0) (n:=1) a (transpose (n:=1) (hw__MemoryEvent__address _i))) (hw__Write _i)))))) /\ (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (rtc (transpose (n:=1) (hw__Event__po _i))) (transpose (n:=1) (hw__Thread__start _i))) (rtc (transpose (n:=1) (hw__Scope__subscope _i)))) (hw__Event__scope _i)) /\ (forall b, (oneof (hw__BarrierArrive _i)) b -> (some (join (m:=0) (n:=1) b (hw__BarrierArrive__synchronizes _i)))) /\ (forall b, (oneof (hw__BarrierWait _i)) b -> (some (join (m:=0) (n:=1) b (transpose (n:=1) (hw__BarrierArrive__synchronizes _i))))) /\ (inside (join (m:=0) (n:=1) (hw__BarrierArrive _i) (intersect (hw__Event__po _i) (hw__BarrierArrive__synchronizes _i))) (hw__BarrierWait _i)) /\ (inside (hw__BarrierArrive__synchronizes _i) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (hw__BarrierArrive__synchronizes _i) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i))) (hw__BarrierArrive__synchronizes _i))) /\ (inside (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)) (hw__BarrierArrive__synchronizes _i)) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)))) /\ (no (intersect (tc (hw__Event__po _i)) (join (m:=1) (n:=1) (hw__BarrierArrive__synchronizes _i) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i))))) /\ (no (intersect (tc (hw__Event__po _i)) (join (m:=1) (n:=1) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)) (hw__BarrierArrive__synchronizes _i)))) /\ (hw__is_strong _i (hw__BarrierArrive__synchronizes _i)) /\ (forall f1, (oneof (hw__FenceSC _i)) f1 -> (forall f2, (oneof (hw__FenceSC _i)) f2 -> f2 <> f1 ->((inside (hw__strong_r _i) (arrow (m:=0) (n:=0) f1 f2)) -> ( (inside (hw__FenceSC__sc _i) (arrow (m:=0) (n:=0) f1 f2)) \/ (inside (hw__FenceSC__sc _i) (arrow (m:=0) (n:=0) f2 f1)))))) /\ (inside (hw__typed _i (hw__strong_r _i) (hw__FenceSC _i)) (hw__FenceSC__sc _i)) /\ (util__acyclic _i (hw__FenceSC__sc _i)) /\ (one (sw__System _i)) /\ (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (rtc (transpose (n:=1) (sw__Event__sb _i))) (transpose (n:=1) (sw__Thread__start _i))) (rtc (transpose (n:=1) (sw__Scope__subscope _i)))) (sw__Event__scope _i)) /\ (inside iden (join (m:=1) (n:=1) (sw__Scope__subscope _i) (transpose (n:=1) (sw__Scope__subscope _i)))) /\ (no (join (m:=0) (n:=1) (sw__Thread _i) (sw__Scope__subscope _i))) /\ (util__acyclic _i (sw__Scope__subscope _i)) /\ (no (intersect (join (m:=0) (n:=1) (sw__A _i) (sw__Event__scope _i)) (sw__Thread _i))) /\ (inside (sw__Thread _i) (join (m:=0) (n:=1) (sw__NA _i) (sw__Event__scope _i))) /\ (inside iden (join (m:=1) (n:=1) (sw__Thread__start _i) (transpose (n:=1) (sw__Thread__start _i)))) /\ (forall e, (oneof (sw__Event _i)) e -> (one (join (m:=0) (n:=1) (join (m:=0) (n:=1) e (rtc (transpose (n:=1) (sw__Event__sb _i)))) (transpose (n:=1) (sw__Thread__start _i))))) /\ (forall w, (oneof (sw__Write _i)) w -> (inside (union (n:=1) (union (n:=1) (sw__MemoryOrderNonAtomic _i) (sw__MemoryOrderRelaxed _i)) (sw__MemoryOrderRelease _i)) (join (m:=0) (n:=1) w (sw__Event__memory_order _i)))) /\ (forall r, (oneof (sw__Read _i)) r -> (inside (union (n:=1) (union (n:=1) (sw__MemoryOrderNonAtomic _i) (sw__MemoryOrderRelaxed _i)) (sw__MemoryOrderAcquire _i)) (join (m:=0) (n:=1) r (sw__Event__memory_order _i)))) /\ (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__Event__memory_order _i) (union (n:=2) (union (n:=2) (union (n:=2) (union (n:=2) (arrow (m:=0) (n:=0) (sw__MemoryOrderRelaxed _i) (sw__MemoryOrderRelaxed _i)) (arrow (m:=0) (n:=0) (sw__MemoryOrderAcquire _i) (sw__MemoryOrderRelaxed _i))) (arrow (m:=0) (n:=0) (sw__MemoryOrderRelaxed _i) (sw__MemoryOrderRelease _i))) (arrow (m:=0) (n:=0) (sw__MemoryOrderAcquire _i) (sw__MemoryOrderRelease _i))) (arrow (m:=0) (n:=0) (sw__MemoryOrderSeqCst _i) (sw__MemoryOrderSeqCst _i)))) (transpose (n:=1) (sw__Event__memory_order _i))) (sw__Read__rmw _i)) /\ (forall f, (oneof (sw__Fence _i)) f -> (inside (union (n:=1) (union (n:=1) (union (n:=1) (sw__MemoryOrderAcquire _i) (sw__MemoryOrderRelease _i)) (sw__MemoryOrderAcqRel _i)) (sw__MemoryOrderSeqCst _i)) (join (m:=0) (n:=1) f (sw__Event__memory_order _i)))) /\ (inside (sw__loc _i) (union (n:=2) (union (n:=2) (sw__Write__rf _i) (sw__Write__mo _i)) (sw__rb _i))) /\ (util__strict_partial _i (sw__Event__sb _i)) /\ (inside iden (join (m:=1) (n:=1) (sw__Write__rf _i) (transpose (n:=1) (sw__Write__rf _i)))) /\ (util__strict_partial _i (sw__Write__mo _i)) /\ (forall a, (oneof (sw__Address _i)) a -> (util__total _i (sw__Write__mo _i) (range (m:=0) (n:=0) (join (m:=0) (n:=1) a (transpose (n:=1) (sw__MemoryEvent__address _i))) (sw__Write _i)))) /\ (inside (intersect (util__imm _i (sw__Event__sb _i)) (sw__loc _i)) (sw__Read__rmw _i)) /\ (inside (sw__Event__sb _i) (join (m:=1) (n:=1) (sw__Event__sb _i) (transpose (n:=1) (sw__Read__rmw _i)))) /\ (some (hw__Read _i)) /\ (compile_src11_ptx _i)).

Definition MP_statement : Prop := exists _i,
(* AND[one hw/System, (hw/Write <: co) + (hw/Write <: rf) + hw/fr in (hw/MemoryEvent <: address) . ~ (hw/MemoryEvent <: address), util/acyclic[(hw/Event <: po)], (all e | (one t | t -> e in (hw/Thread <: start) . * (hw/Event <: po))), (hw/Write <: rf) . ~ (hw/Write <: rf) in iden, (hw/Read <: dep) in ^ (hw/Event <: po), (hw/Read <: rmw) in (hw/Event <: po) & (hw/Read <: dep) & (hw/MemoryEvent <: address) . ~ (hw/MemoryEvent <: address) & (hw/Event <: scope) . ~ (hw/Event <: scope), (hw/Scope <: subscope) . ~ (hw/Scope <: subscope) in iden, no hw/Thread . (hw/Scope <: subscope), util/acyclic[(hw/Scope <: subscope)], (hw/MemoryEvent <: observation) in ^ hw/strong[(hw/Write <: rf)] + (hw/Read <: rmw), hw/strong[(hw/Write <: rf)] in (hw/MemoryEvent <: observation), (hw/MemoryEvent <: observation) . (hw/Read <: rmw) . (hw/MemoryEvent <: observation) in (hw/MemoryEvent <: observation), (all a | (all s | util/total[(hw/Write <: co), hw/scoped[s] & hw/inside[s] & a . ~ (hw/MemoryEvent <: address) & hw/Write])), (hw/Event <: scope) in * ~ (hw/Event <: po) . ~ (hw/Thread <: start) . * ~ (hw/Scope <: subscope), (all b | some b . (hw/BarrierArrive <: synchronizes)), (all b | some b . ~ (hw/BarrierArrive <: synchronizes)), hw/BarrierWait in hw/BarrierArrive . (hw/Event <: po) & (hw/BarrierArrive <: synchronizes), (hw/BarrierArrive <: synchronizes) . ~ (hw/BarrierArrive <: synchronizes) . (hw/BarrierArrive <: synchronizes) in (hw/BarrierArrive <: synchronizes), ~ (hw/BarrierArrive <: synchronizes) . (hw/BarrierArrive <: synchronizes) . ~ (hw/BarrierArrive <: synchronizes) in ~ (hw/BarrierArrive <: synchronizes), no ^ (hw/Event <: po) & (hw/BarrierArrive <: synchronizes) . ~ (hw/BarrierArrive <: synchronizes), no ^ (hw/Event <: po) & ~ (hw/BarrierArrive <: synchronizes) . (hw/BarrierArrive <: synchronizes), hw/is_strong[(hw/BarrierArrive <: synchronizes)], (all f1,f2 | f1 -> f2 in hw/strong_r => OR[f1 -> f2 in (hw/FenceSC <: sc), f2 -> f1 in (hw/FenceSC <: sc)]), (hw/FenceSC <: sc) in hw/typed[hw/strong_r, hw/FenceSC], util/acyclic[(hw/FenceSC <: sc)], one sw/System, (sw/Event <: scope) in * ~ (sw/Event <: sb) . ~ (sw/Thread <: start) . * ~ (sw/Scope <: subscope), (sw/Scope <: subscope) . ~ (sw/Scope <: subscope) in iden, no sw/Thread . (sw/Scope <: subscope), util/acyclic[(sw/Scope <: subscope)], no sw/A . (sw/Event <: scope) & sw/Thread, sw/NA . (sw/Event <: scope) in sw/Thread, (sw/Thread <: start) . ~ (sw/Thread <: start) in iden, (all e | one e . * ~ (sw/Event <: sb) . ~ (sw/Thread <: start)), (all w | w . (sw/Event <: memory_order) in sw/MemoryOrderNonAtomic + sw/MemoryOrderRelaxed + sw/MemoryOrderRelease), (all r | r . (sw/Event <: memory_order) in sw/MemoryOrderNonAtomic + sw/MemoryOrderRelaxed + sw/MemoryOrderAcquire), (sw/Read <: rmw) in (sw/Event <: memory_order) . sw/MemoryOrderRelaxed -> sw/MemoryOrderRelaxed + sw/MemoryOrderAcquire -> sw/MemoryOrderRelaxed + sw/MemoryOrderRelaxed -> sw/MemoryOrderRelease + sw/MemoryOrderAcquire -> sw/MemoryOrderRelease + sw/MemoryOrderSeqCst -> sw/MemoryOrderSeqCst . ~ (sw/Event <: memory_order), (all f | f . (sw/Event <: memory_order) in sw/MemoryOrderAcquire + sw/MemoryOrderRelease + sw/MemoryOrderAcqRel + sw/MemoryOrderSeqCst), (sw/Write <: rf) + (sw/Write <: mo) + sw/rb in sw/loc, util/strict_partial[(sw/Event <: sb)], (sw/Write <: rf) . ~ (sw/Write <: rf) in iden, util/strict_partial[(sw/Write <: mo)], (all a | util/total[(sw/Write <: mo), a . ~ (sw/MemoryEvent <: address) :> sw/Write]), (sw/Read <: rmw) in util/imm[(sw/Event <: sb)] & sw/loc, (sw/Event <: sb) . ~ (sw/Read <: rmw) in (sw/Event <: sb), some sw/NA <: (sw/Event <: sb) . sw/sw . (sw/Event <: sb) :> sw/NA & (sw/Write <: rf), some (sw/Scope <: subscope), this/compile_src11_ptx, sw/src11] *)
( (one (hw__System _i)) /\ (inside (join (m:=1) (n:=1) (hw__MemoryEvent__address _i) (transpose (n:=1) (hw__MemoryEvent__address _i))) (union (n:=2) (union (n:=2) (hw__Write__co _i) (hw__Write__rf _i)) (hw__fr _i))) /\ (util__acyclic _i (hw__Event__po _i)) /\ (forall e, (oneof (hw__Event _i)) e -> (exists! t, ((oneof (hw__Thread _i)) t) /\ (inside (join (m:=1) (n:=1) (hw__Thread__start _i) (rtc (hw__Event__po _i))) (arrow (m:=0) (n:=0) t e)))) /\ (inside iden (join (m:=1) (n:=1) (hw__Write__rf _i) (transpose (n:=1) (hw__Write__rf _i)))) /\ (inside (tc (hw__Event__po _i)) (hw__Read__dep _i)) /\ (inside (intersect (intersect (intersect (hw__Event__po _i) (hw__Read__dep _i)) (join (m:=1) (n:=1) (hw__MemoryEvent__address _i) (transpose (n:=1) (hw__MemoryEvent__address _i)))) (join (m:=1) (n:=1) (hw__Event__scope _i) (transpose (n:=1) (hw__Event__scope _i)))) (hw__Read__rmw _i)) /\ (inside iden (join (m:=1) (n:=1) (hw__Scope__subscope _i) (transpose (n:=1) (hw__Scope__subscope _i)))) /\ (no (join (m:=0) (n:=1) (hw__Thread _i) (hw__Scope__subscope _i))) /\ (util__acyclic _i (hw__Scope__subscope _i)) /\ (inside (tc (union (n:=2) (hw__strong _i (hw__Write__rf _i)) (hw__Read__rmw _i))) (hw__MemoryEvent__observation _i)) /\ (inside (hw__MemoryEvent__observation _i) (hw__strong _i (hw__Write__rf _i))) /\ (inside (hw__MemoryEvent__observation _i) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (hw__MemoryEvent__observation _i) (hw__Read__rmw _i)) (hw__MemoryEvent__observation _i))) /\ (forall a, (oneof (hw__Address _i)) a -> (forall s, (oneof (hw__Scope _i)) s -> (util__total _i (hw__Write__co _i) (intersect (intersect (hw__scoped _i s) (hw__inside _i s)) (intersect (join (m:=0) (n:=1) a (transpose (n:=1) (hw__MemoryEvent__address _i))) (hw__Write _i)))))) /\ (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (rtc (transpose (n:=1) (hw__Event__po _i))) (transpose (n:=1) (hw__Thread__start _i))) (rtc (transpose (n:=1) (hw__Scope__subscope _i)))) (hw__Event__scope _i)) /\ (forall b, (oneof (hw__BarrierArrive _i)) b -> (some (join (m:=0) (n:=1) b (hw__BarrierArrive__synchronizes _i)))) /\ (forall b, (oneof (hw__BarrierWait _i)) b -> (some (join (m:=0) (n:=1) b (transpose (n:=1) (hw__BarrierArrive__synchronizes _i))))) /\ (inside (join (m:=0) (n:=1) (hw__BarrierArrive _i) (intersect (hw__Event__po _i) (hw__BarrierArrive__synchronizes _i))) (hw__BarrierWait _i)) /\ (inside (hw__BarrierArrive__synchronizes _i) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (hw__BarrierArrive__synchronizes _i) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i))) (hw__BarrierArrive__synchronizes _i))) /\ (inside (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)) (hw__BarrierArrive__synchronizes _i)) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)))) /\ (no (intersect (tc (hw__Event__po _i)) (join (m:=1) (n:=1) (hw__BarrierArrive__synchronizes _i) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i))))) /\ (no (intersect (tc (hw__Event__po _i)) (join (m:=1) (n:=1) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)) (hw__BarrierArrive__synchronizes _i)))) /\ (hw__is_strong _i (hw__BarrierArrive__synchronizes _i)) /\ (forall f1, (oneof (hw__FenceSC _i)) f1 -> (forall f2, (oneof (hw__FenceSC _i)) f2 -> f2 <> f1 ->((inside (hw__strong_r _i) (arrow (m:=0) (n:=0) f1 f2)) -> ( (inside (hw__FenceSC__sc _i) (arrow (m:=0) (n:=0) f1 f2)) \/ (inside (hw__FenceSC__sc _i) (arrow (m:=0) (n:=0) f2 f1)))))) /\ (inside (hw__typed _i (hw__strong_r _i) (hw__FenceSC _i)) (hw__FenceSC__sc _i)) /\ (util__acyclic _i (hw__FenceSC__sc _i)) /\ (one (sw__System _i)) /\ (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (rtc (transpose (n:=1) (sw__Event__sb _i))) (transpose (n:=1) (sw__Thread__start _i))) (rtc (transpose (n:=1) (sw__Scope__subscope _i)))) (sw__Event__scope _i)) /\ (inside iden (join (m:=1) (n:=1) (sw__Scope__subscope _i) (transpose (n:=1) (sw__Scope__subscope _i)))) /\ (no (join (m:=0) (n:=1) (sw__Thread _i) (sw__Scope__subscope _i))) /\ (util__acyclic _i (sw__Scope__subscope _i)) /\ (no (intersect (join (m:=0) (n:=1) (sw__A _i) (sw__Event__scope _i)) (sw__Thread _i))) /\ (inside (sw__Thread _i) (join (m:=0) (n:=1) (sw__NA _i) (sw__Event__scope _i))) /\ (inside iden (join (m:=1) (n:=1) (sw__Thread__start _i) (transpose (n:=1) (sw__Thread__start _i)))) /\ (forall e, (oneof (sw__Event _i)) e -> (one (join (m:=0) (n:=1) (join (m:=0) (n:=1) e (rtc (transpose (n:=1) (sw__Event__sb _i)))) (transpose (n:=1) (sw__Thread__start _i))))) /\ (forall w, (oneof (sw__Write _i)) w -> (inside (union (n:=1) (union (n:=1) (sw__MemoryOrderNonAtomic _i) (sw__MemoryOrderRelaxed _i)) (sw__MemoryOrderRelease _i)) (join (m:=0) (n:=1) w (sw__Event__memory_order _i)))) /\ (forall r, (oneof (sw__Read _i)) r -> (inside (union (n:=1) (union (n:=1) (sw__MemoryOrderNonAtomic _i) (sw__MemoryOrderRelaxed _i)) (sw__MemoryOrderAcquire _i)) (join (m:=0) (n:=1) r (sw__Event__memory_order _i)))) /\ (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__Event__memory_order _i) (union (n:=2) (union (n:=2) (union (n:=2) (union (n:=2) (arrow (m:=0) (n:=0) (sw__MemoryOrderRelaxed _i) (sw__MemoryOrderRelaxed _i)) (arrow (m:=0) (n:=0) (sw__MemoryOrderAcquire _i) (sw__MemoryOrderRelaxed _i))) (arrow (m:=0) (n:=0) (sw__MemoryOrderRelaxed _i) (sw__MemoryOrderRelease _i))) (arrow (m:=0) (n:=0) (sw__MemoryOrderAcquire _i) (sw__MemoryOrderRelease _i))) (arrow (m:=0) (n:=0) (sw__MemoryOrderSeqCst _i) (sw__MemoryOrderSeqCst _i)))) (transpose (n:=1) (sw__Event__memory_order _i))) (sw__Read__rmw _i)) /\ (forall f, (oneof (sw__Fence _i)) f -> (inside (union (n:=1) (union (n:=1) (union (n:=1) (sw__MemoryOrderAcquire _i) (sw__MemoryOrderRelease _i)) (sw__MemoryOrderAcqRel _i)) (sw__MemoryOrderSeqCst _i)) (join (m:=0) (n:=1) f (sw__Event__memory_order _i)))) /\ (inside (sw__loc _i) (union (n:=2) (union (n:=2) (sw__Write__rf _i) (sw__Write__mo _i)) (sw__rb _i))) /\ (util__strict_partial _i (sw__Event__sb _i)) /\ (inside iden (join (m:=1) (n:=1) (sw__Write__rf _i) (transpose (n:=1) (sw__Write__rf _i)))) /\ (util__strict_partial _i (sw__Write__mo _i)) /\ (forall a, (oneof (sw__Address _i)) a -> (util__total _i (sw__Write__mo _i) (range (m:=0) (n:=0) (join (m:=0) (n:=1) a (transpose (n:=1) (sw__MemoryEvent__address _i))) (sw__Write _i)))) /\ (inside (intersect (util__imm _i (sw__Event__sb _i)) (sw__loc _i)) (sw__Read__rmw _i)) /\ (inside (sw__Event__sb _i) (join (m:=1) (n:=1) (sw__Event__sb _i) (transpose (n:=1) (sw__Read__rmw _i)))) /\ (some (intersect (domain (sw__NA _i) (range (m:=1) (n:=0) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__Event__sb _i) (sw__sw _i)) (sw__Event__sb _i)) (sw__NA _i))) (sw__Write__rf _i))) /\ (some (sw__Scope__subscope _i)) /\ (compile_src11_ptx _i) /\ (sw__src11 _i)).

Definition sm_statement : Prop := exists _i,
(* AND[one hw/System, (hw/Write <: co) + (hw/Write <: rf) + hw/fr in (hw/MemoryEvent <: address) . ~ (hw/MemoryEvent <: address), util/acyclic[(hw/Event <: po)], (all e | (one t | t -> e in (hw/Thread <: start) . * (hw/Event <: po))), (hw/Write <: rf) . ~ (hw/Write <: rf) in iden, (hw/Read <: dep) in ^ (hw/Event <: po), (hw/Read <: rmw) in (hw/Event <: po) & (hw/Read <: dep) & (hw/MemoryEvent <: address) . ~ (hw/MemoryEvent <: address) & (hw/Event <: scope) . ~ (hw/Event <: scope), (hw/Scope <: subscope) . ~ (hw/Scope <: subscope) in iden, no hw/Thread . (hw/Scope <: subscope), util/acyclic[(hw/Scope <: subscope)], (hw/MemoryEvent <: observation) in ^ hw/strong[(hw/Write <: rf)] + (hw/Read <: rmw), hw/strong[(hw/Write <: rf)] in (hw/MemoryEvent <: observation), (hw/MemoryEvent <: observation) . (hw/Read <: rmw) . (hw/MemoryEvent <: observation) in (hw/MemoryEvent <: observation), (all a | (all s | util/total[(hw/Write <: co), hw/scoped[s] & hw/inside[s] & a . ~ (hw/MemoryEvent <: address) & hw/Write])), (hw/Event <: scope) in * ~ (hw/Event <: po) . ~ (hw/Thread <: start) . * ~ (hw/Scope <: subscope), (all b | some b . (hw/BarrierArrive <: synchronizes)), (all b | some b . ~ (hw/BarrierArrive <: synchronizes)), hw/BarrierWait in hw/BarrierArrive . (hw/Event <: po) & (hw/BarrierArrive <: synchronizes), (hw/BarrierArrive <: synchronizes) . ~ (hw/BarrierArrive <: synchronizes) . (hw/BarrierArrive <: synchronizes) in (hw/BarrierArrive <: synchronizes), ~ (hw/BarrierArrive <: synchronizes) . (hw/BarrierArrive <: synchronizes) . ~ (hw/BarrierArrive <: synchronizes) in ~ (hw/BarrierArrive <: synchronizes), no ^ (hw/Event <: po) & (hw/BarrierArrive <: synchronizes) . ~ (hw/BarrierArrive <: synchronizes), no ^ (hw/Event <: po) & ~ (hw/BarrierArrive <: synchronizes) . (hw/BarrierArrive <: synchronizes), hw/is_strong[(hw/BarrierArrive <: synchronizes)], (all f1,f2 | f1 -> f2 in hw/strong_r => OR[f1 -> f2 in (hw/FenceSC <: sc), f2 -> f1 in (hw/FenceSC <: sc)]), (hw/FenceSC <: sc) in hw/typed[hw/strong_r, hw/FenceSC], util/acyclic[(hw/FenceSC <: sc)], one sw/System, (sw/Event <: scope) in * ~ (sw/Event <: sb) . ~ (sw/Thread <: start) . * ~ (sw/Scope <: subscope), (sw/Scope <: subscope) . ~ (sw/Scope <: subscope) in iden, no sw/Thread . (sw/Scope <: subscope), util/acyclic[(sw/Scope <: subscope)], no sw/A . (sw/Event <: scope) & sw/Thread, sw/NA . (sw/Event <: scope) in sw/Thread, (sw/Thread <: start) . ~ (sw/Thread <: start) in iden, (all e | one e . * ~ (sw/Event <: sb) . ~ (sw/Thread <: start)), (all w | w . (sw/Event <: memory_order) in sw/MemoryOrderNonAtomic + sw/MemoryOrderRelaxed + sw/MemoryOrderRelease), (all r | r . (sw/Event <: memory_order) in sw/MemoryOrderNonAtomic + sw/MemoryOrderRelaxed + sw/MemoryOrderAcquire), (sw/Read <: rmw) in (sw/Event <: memory_order) . sw/MemoryOrderRelaxed -> sw/MemoryOrderRelaxed + sw/MemoryOrderAcquire -> sw/MemoryOrderRelaxed + sw/MemoryOrderRelaxed -> sw/MemoryOrderRelease + sw/MemoryOrderAcquire -> sw/MemoryOrderRelease + sw/MemoryOrderSeqCst -> sw/MemoryOrderSeqCst . ~ (sw/Event <: memory_order), (all f | f . (sw/Event <: memory_order) in sw/MemoryOrderAcquire + sw/MemoryOrderRelease + sw/MemoryOrderAcqRel + sw/MemoryOrderSeqCst), (sw/Write <: rf) + (sw/Write <: mo) + sw/rb in sw/loc, util/strict_partial[(sw/Event <: sb)], (sw/Write <: rf) . ~ (sw/Write <: rf) in iden, util/strict_partial[(sw/Write <: mo)], (all a | util/total[(sw/Write <: mo), a . ~ (sw/MemoryEvent <: address) :> sw/Write]), (sw/Read <: rmw) in util/imm[(sw/Event <: sb)] & sw/loc, (sw/Event <: sb) . ~ (sw/Read <: rmw) in (sw/Event <: sb), this/compile_src11_ptx, some (sw/Scope <: scopemap) . ~ (sw/Scope <: scopemap) - iden] *)
( (one (hw__System _i)) /\ (inside (join (m:=1) (n:=1) (hw__MemoryEvent__address _i) (transpose (n:=1) (hw__MemoryEvent__address _i))) (union (n:=2) (union (n:=2) (hw__Write__co _i) (hw__Write__rf _i)) (hw__fr _i))) /\ (util__acyclic _i (hw__Event__po _i)) /\ (forall e, (oneof (hw__Event _i)) e -> (exists! t, ((oneof (hw__Thread _i)) t) /\ (inside (join (m:=1) (n:=1) (hw__Thread__start _i) (rtc (hw__Event__po _i))) (arrow (m:=0) (n:=0) t e)))) /\ (inside iden (join (m:=1) (n:=1) (hw__Write__rf _i) (transpose (n:=1) (hw__Write__rf _i)))) /\ (inside (tc (hw__Event__po _i)) (hw__Read__dep _i)) /\ (inside (intersect (intersect (intersect (hw__Event__po _i) (hw__Read__dep _i)) (join (m:=1) (n:=1) (hw__MemoryEvent__address _i) (transpose (n:=1) (hw__MemoryEvent__address _i)))) (join (m:=1) (n:=1) (hw__Event__scope _i) (transpose (n:=1) (hw__Event__scope _i)))) (hw__Read__rmw _i)) /\ (inside iden (join (m:=1) (n:=1) (hw__Scope__subscope _i) (transpose (n:=1) (hw__Scope__subscope _i)))) /\ (no (join (m:=0) (n:=1) (hw__Thread _i) (hw__Scope__subscope _i))) /\ (util__acyclic _i (hw__Scope__subscope _i)) /\ (inside (tc (union (n:=2) (hw__strong _i (hw__Write__rf _i)) (hw__Read__rmw _i))) (hw__MemoryEvent__observation _i)) /\ (inside (hw__MemoryEvent__observation _i) (hw__strong _i (hw__Write__rf _i))) /\ (inside (hw__MemoryEvent__observation _i) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (hw__MemoryEvent__observation _i) (hw__Read__rmw _i)) (hw__MemoryEvent__observation _i))) /\ (forall a, (oneof (hw__Address _i)) a -> (forall s, (oneof (hw__Scope _i)) s -> (util__total _i (hw__Write__co _i) (intersect (intersect (hw__scoped _i s) (hw__inside _i s)) (intersect (join (m:=0) (n:=1) a (transpose (n:=1) (hw__MemoryEvent__address _i))) (hw__Write _i)))))) /\ (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (rtc (transpose (n:=1) (hw__Event__po _i))) (transpose (n:=1) (hw__Thread__start _i))) (rtc (transpose (n:=1) (hw__Scope__subscope _i)))) (hw__Event__scope _i)) /\ (forall b, (oneof (hw__BarrierArrive _i)) b -> (some (join (m:=0) (n:=1) b (hw__BarrierArrive__synchronizes _i)))) /\ (forall b, (oneof (hw__BarrierWait _i)) b -> (some (join (m:=0) (n:=1) b (transpose (n:=1) (hw__BarrierArrive__synchronizes _i))))) /\ (inside (join (m:=0) (n:=1) (hw__BarrierArrive _i) (intersect (hw__Event__po _i) (hw__BarrierArrive__synchronizes _i))) (hw__BarrierWait _i)) /\ (inside (hw__BarrierArrive__synchronizes _i) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (hw__BarrierArrive__synchronizes _i) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i))) (hw__BarrierArrive__synchronizes _i))) /\ (inside (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)) (join (m:=1) (n:=1) (join (m:=1) (n:=1) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)) (hw__BarrierArrive__synchronizes _i)) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)))) /\ (no (intersect (tc (hw__Event__po _i)) (join (m:=1) (n:=1) (hw__BarrierArrive__synchronizes _i) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i))))) /\ (no (intersect (tc (hw__Event__po _i)) (join (m:=1) (n:=1) (transpose (n:=1) (hw__BarrierArrive__synchronizes _i)) (hw__BarrierArrive__synchronizes _i)))) /\ (hw__is_strong _i (hw__BarrierArrive__synchronizes _i)) /\ (forall f1, (oneof (hw__FenceSC _i)) f1 -> (forall f2, (oneof (hw__FenceSC _i)) f2 -> f2 <> f1 ->((inside (hw__strong_r _i) (arrow (m:=0) (n:=0) f1 f2)) -> ( (inside (hw__FenceSC__sc _i) (arrow (m:=0) (n:=0) f1 f2)) \/ (inside (hw__FenceSC__sc _i) (arrow (m:=0) (n:=0) f2 f1)))))) /\ (inside (hw__typed _i (hw__strong_r _i) (hw__FenceSC _i)) (hw__FenceSC__sc _i)) /\ (util__acyclic _i (hw__FenceSC__sc _i)) /\ (one (sw__System _i)) /\ (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (rtc (transpose (n:=1) (sw__Event__sb _i))) (transpose (n:=1) (sw__Thread__start _i))) (rtc (transpose (n:=1) (sw__Scope__subscope _i)))) (sw__Event__scope _i)) /\ (inside iden (join (m:=1) (n:=1) (sw__Scope__subscope _i) (transpose (n:=1) (sw__Scope__subscope _i)))) /\ (no (join (m:=0) (n:=1) (sw__Thread _i) (sw__Scope__subscope _i))) /\ (util__acyclic _i (sw__Scope__subscope _i)) /\ (no (intersect (join (m:=0) (n:=1) (sw__A _i) (sw__Event__scope _i)) (sw__Thread _i))) /\ (inside (sw__Thread _i) (join (m:=0) (n:=1) (sw__NA _i) (sw__Event__scope _i))) /\ (inside iden (join (m:=1) (n:=1) (sw__Thread__start _i) (transpose (n:=1) (sw__Thread__start _i)))) /\ (forall e, (oneof (sw__Event _i)) e -> (one (join (m:=0) (n:=1) (join (m:=0) (n:=1) e (rtc (transpose (n:=1) (sw__Event__sb _i)))) (transpose (n:=1) (sw__Thread__start _i))))) /\ (forall w, (oneof (sw__Write _i)) w -> (inside (union (n:=1) (union (n:=1) (sw__MemoryOrderNonAtomic _i) (sw__MemoryOrderRelaxed _i)) (sw__MemoryOrderRelease _i)) (join (m:=0) (n:=1) w (sw__Event__memory_order _i)))) /\ (forall r, (oneof (sw__Read _i)) r -> (inside (union (n:=1) (union (n:=1) (sw__MemoryOrderNonAtomic _i) (sw__MemoryOrderRelaxed _i)) (sw__MemoryOrderAcquire _i)) (join (m:=0) (n:=1) r (sw__Event__memory_order _i)))) /\ (inside (join (m:=1) (n:=1) (join (m:=1) (n:=1) (sw__Event__memory_order _i) (union (n:=2) (union (n:=2) (union (n:=2) (union (n:=2) (arrow (m:=0) (n:=0) (sw__MemoryOrderRelaxed _i) (sw__MemoryOrderRelaxed _i)) (arrow (m:=0) (n:=0) (sw__MemoryOrderAcquire _i) (sw__MemoryOrderRelaxed _i))) (arrow (m:=0) (n:=0) (sw__MemoryOrderRelaxed _i) (sw__MemoryOrderRelease _i))) (arrow (m:=0) (n:=0) (sw__MemoryOrderAcquire _i) (sw__MemoryOrderRelease _i))) (arrow (m:=0) (n:=0) (sw__MemoryOrderSeqCst _i) (sw__MemoryOrderSeqCst _i)))) (transpose (n:=1) (sw__Event__memory_order _i))) (sw__Read__rmw _i)) /\ (forall f, (oneof (sw__Fence _i)) f -> (inside (union (n:=1) (union (n:=1) (union (n:=1) (sw__MemoryOrderAcquire _i) (sw__MemoryOrderRelease _i)) (sw__MemoryOrderAcqRel _i)) (sw__MemoryOrderSeqCst _i)) (join (m:=0) (n:=1) f (sw__Event__memory_order _i)))) /\ (inside (sw__loc _i) (union (n:=2) (union (n:=2) (sw__Write__rf _i) (sw__Write__mo _i)) (sw__rb _i))) /\ (util__strict_partial _i (sw__Event__sb _i)) /\ (inside iden (join (m:=1) (n:=1) (sw__Write__rf _i) (transpose (n:=1) (sw__Write__rf _i)))) /\ (util__strict_partial _i (sw__Write__mo _i)) /\ (forall a, (oneof (sw__Address _i)) a -> (util__total _i (sw__Write__mo _i) (range (m:=0) (n:=0) (join (m:=0) (n:=1) a (transpose (n:=1) (sw__MemoryEvent__address _i))) (sw__Write _i)))) /\ (inside (intersect (util__imm _i (sw__Event__sb _i)) (sw__loc _i)) (sw__Read__rmw _i)) /\ (inside (sw__Event__sb _i) (join (m:=1) (n:=1) (sw__Event__sb _i) (transpose (n:=1) (sw__Read__rmw _i)))) /\ (compile_src11_ptx _i) /\ (some (difference (join (m:=1) (n:=1) (sw__Scope__scopemap _i) (transpose (n:=1) (sw__Scope__scopemap _i))) iden))).

