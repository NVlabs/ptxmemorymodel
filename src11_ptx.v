Require Import Classical.
Require Import case.
Require Import alloy.
Require Import alloy_util.
Require Import compile_src11_ptx.

Notation "A ; B" := (join A B) (at level 50).
Notation "A \ B" := (difference A B) (at level 50).
Notation "A 'U' B" := (union A B) (at level 50).
Notation "x --( r )--> y" := (r (x, y)) (at level 50).
Definition tr := transpose (n:=1).
Hint Unfold tr.

Hint Resolve oneof_singleton_atom.
Hint Resolve untranspose_pair.

Ltac clean H x' :=
  match type of H with
  | exists x, ?f => destruct H as [x' H]; try clean H x'
  | exists x, ?f x => destruct H as [x' H]; try clean H x'
  | exists y, ?f (?x, y) => destruct H as [x' H]; try clean H x'
  | exists x, ?f (x, ?y) => destruct H as [x' H]; try clean H x'
  | some ?x => destruct H as [x' H]; try clean H x'
  | (singleton_atom ?x; ?f) x' => apply join12_r2 in H; try clean H x'
  end.

Ltac choose X := assert X; [|solve [lr]].

Ltac contradiction_types :=
match goal with
| [ H : hw__Write ?i ?x |- _ ] =>
  apply _hw__MemoryEvent_subsig_hw__Write in H; contradiction_types
| [ H : sw__Write ?i ?x |- _ ] =>
  apply _sw__MemoryEvent_subsig_sw__Write in H; contradiction_types
| [ H : hw__Release ?i ?x |- _ ] =>
  apply _hw__Write_subsig_hw__Release in H; contradiction_types
| [ H : hw__Read ?i ?x |- _ ] =>
  apply _hw__MemoryEvent_subsig_hw__Read in H; contradiction_types
| [ H : sw__Read ?i ?x |- _ ] =>
  apply _sw__MemoryEvent_subsig_sw__Read in H; contradiction_types
| [ H : hw__Acquire ?i ?x |- _ ] =>
  apply _hw__Read_subsig_hw__Acquire in H; contradiction_types
| [ H : hw__Release ?i ?x |- _ ] =>
  apply _hw__Write_subsig_hw__Release in H; contradiction_types
| [ H : hw__BarrierWait ?i ?x |- _ ] =>
  apply _hw__Barrier_subsig_hw__BarrierWait in H; contradiction_types
| [ H : hw__BarrierArrive ?i ?x |- _ ] =>
  apply _hw__Barrier_subsig_hw__BarrierArrive in H; contradiction_types
| [ H : hw__FenceSC ?i ?x |- _ ] =>
  apply _hw__FenceAcqRel_subsig_hw__FenceSC in H; contradiction_types
| [ H : hw__FenceAcqRel ?i ?x |- _ ] =>
  apply _hw__Fence_subsig_hw__FenceAcqRel in H; contradiction_types
| [ H : hw__FenceAcq ?i ?x |- _ ] =>
  apply _hw__Fence_subsig_hw__FenceAcq in H; contradiction_types
| [ H : hw__FenceRel ?i ?x |- _ ] =>
  apply _hw__Fence_subsig_hw__FenceRel in H; contradiction_types
| [ H1 : sw__Write ?i ?x, H2 : sw__Read ?i ?x |- _ ] =>
  apply _sw__Write_disjoint_sw__Read in H1; auto; contradiction
| [ H1 : sw__MemoryEvent ?i ?x, H2 : sw__Fence ?i ?x |- _ ] =>
  apply _sw__MemoryEvent_disjoint_sw__Fence in H1; auto; contradiction
| [ H1 : hw__Barrier ?i ?x, H2 : hw__MemoryEvent ?i ?x |- _ ] =>
  apply _hw__Barrier_disjoint_hw__MemoryEvent in H2; auto; contradiction
| [ H1 : hw__Fence ?i ?x, H2 : hw__MemoryEvent ?i ?x |- _ ] =>
  apply _hw__MemoryEvent_disjoint_hw__Fence in H2; auto; contradiction
| [ H1 : hw__Read ?i ?x, H2 : hw__Write ?i ?x |- _ ] =>
  apply _hw__Read_disjoint_hw__Write in H1; contradiction
| [ H1 : sw__MemoryOrderRelaxed ?i ?o, H2 : sw__MemoryOrderNonAtomic ?i ?o |- _ ] =>
  apply _sw__MemoryOrderRelaxed_disjoint_sw__MemoryOrderNonAtomic in H1; contradiction
| [ H1 : sw__MemoryOrderAcquire ?i ?o, H2 : sw__MemoryOrderNonAtomic ?i ?o |- _ ] =>
  apply _sw__MemoryOrderAcquire_disjoint_sw__MemoryOrderNonAtomic in H1; contradiction
| [ H1 : sw__MemoryOrderRelease ?i ?o, H2 : sw__MemoryOrderNonAtomic ?i ?o |- _ ] =>
  apply _sw__MemoryOrderRelease_disjoint_sw__MemoryOrderNonAtomic in H1; contradiction
| [ H1 : sw__MemoryOrderSeqCst ?i ?o, H2 : sw__MemoryOrderNonAtomic ?i ?o |- _ ] =>
  apply _sw__MemoryOrderSeqCst_disjoint_sw__MemoryOrderNonAtomic in H1; contradiction
| [ H1 : sw__MemoryOrderAcquire ?i ?o, H2 : sw__MemoryOrderRelaxed ?i ?o |- _ ] =>
  apply _sw__MemoryOrderAcquire_disjoint_sw__MemoryOrderRelaxed in H1; contradiction
| [ H1 : sw__MemoryOrderAcquire ?i ?o, H2 : sw__MemoryOrderRelease ?i ?o |- _ ] =>
  apply _sw__MemoryOrderAcquire_disjoint_sw__MemoryOrderRelease in H1; contradiction
| [ H1 : sw__MemoryOrderRelaxed ?i ?o, H2 : sw__MemoryOrderRelease ?i ?o |- _ ] =>
  apply _sw__MemoryOrderRelaxed_disjoint_sw__MemoryOrderRelease in H1; contradiction
| [ H1 : sw__MemoryOrderAcquire ?i ?o, H2 : sw__MemoryOrderSeqCst ?i ?o |- _ ] =>
  apply _sw__MemoryOrderAcquire_disjoint_sw__MemoryOrderSeqCst in H1; contradiction
| [ H1 : sw__MemoryOrderAcqRel ?i ?o, H2 : sw__MemoryOrderNonAtomic ?i ?o |- _ ] =>
  apply _sw__MemoryOrderAcqRel_disjoint_sw__MemoryOrderNonAtomic in H1; contradiction
| [ H1 : sw__MemoryOrderAcqRel ?i ?o, H2 : sw__MemoryOrderRelaxed ?i ?o |- _ ] =>
  apply _sw__MemoryOrderAcqRel_disjoint_sw__MemoryOrderRelaxed in H1; contradiction
| [ H1 : sw__MemoryOrderAcqRel ?i ?o, H2 : sw__MemoryOrderAcquire ?i ?o |- _ ] =>
  apply _sw__MemoryOrderAcqRel_disjoint_sw__MemoryOrderAcquire in H1; contradiction
| [ H1 : sw__MemoryOrderAcqRel ?i ?o, H2 : sw__MemoryOrderRelease ?i ?o |- _ ] =>
  apply _sw__MemoryOrderAcqRel_disjoint_sw__MemoryOrderRelease in H1; contradiction
| [ H1 : sw__MemoryOrderAcqRel ?i ?o, H2 : sw__MemoryOrderSeqCst ?i ?o |- _ ] =>
  apply _sw__MemoryOrderAcqRel_disjoint_sw__MemoryOrderSeqCst in H1; contradiction
| [ H1 : sw__MemoryOrderRelaxed ?i ?o, H2 : sw__MemoryOrderSeqCst ?i ?o |- _ ] =>
  apply _sw__MemoryOrderRelaxed_disjoint_sw__MemoryOrderSeqCst in H1; contradiction
| [ H1 : sw__MemoryOrderRelease ?i ?o, H2 : sw__MemoryOrderSeqCst ?i ?o |- _ ] =>
  apply _sw__MemoryOrderRelease_disjoint_sw__MemoryOrderSeqCst in H1; contradiction
| [ H1 : ?f ?i ?x, H2 : union ?g ?h ?x |- _ ] =>
  destruct H2 as [H2|H2]; contradiction_types
end.

Ltac subsig := match goal with
| [ H : hw__Read ?i ?x |- hw__Event ?i ?x ] =>
  apply _hw__Event_subsig_hw__MemoryEvent; subsig
| [ H : hw__Write ?i ?x |- hw__Event ?i ?x ] =>
  apply _hw__Event_subsig_hw__MemoryEvent; subsig
| [ H : hw__Read ?i ?x |- hw__MemoryEvent ?i ?x ] =>
  apply _hw__MemoryEvent_subsig_hw__Read; subsig
| [ H : hw__Acquire ?i ?x |- hw__Read ?i ?x ] =>
  apply _hw__Read_subsig_hw__Acquire; subsig
| [ H : hw__Acquire ?i ?x |- hw__Event ?i ?x ] =>
  apply _hw__Event_subsig_hw__MemoryEvent; subsig
| [ H : hw__Acquire ?i ?x |- hw__MemoryEvent ?i ?x ] =>
  apply _hw__MemoryEvent_subsig_hw__Read; subsig
| [ H : hw__Release ?i ?x |- hw__Event ?i ?x ] =>
  apply _hw__Event_subsig_hw__MemoryEvent; subsig
| [ H : hw__Release ?i ?x |- hw__MemoryEvent ?i ?x ] =>
  apply _hw__MemoryEvent_subsig_hw__Write; subsig
| [ H : hw__Release ?i ?x |- hw__Write ?i ?x ] =>
  apply _hw__Write_subsig_hw__Release; subsig
| [ H : hw__Write ?i ?x |- hw__MemoryEvent ?i ?x ] =>
  apply _hw__MemoryEvent_subsig_hw__Write; subsig
| [ H : hw__MemoryEvent ?i ?x |- hw__Event ?i ?x ] =>
  apply _hw__Event_subsig_hw__MemoryEvent; subsig
| [ H : hw__Fence ?i ?x |- hw__Event ?i ?x ] =>
  apply _hw__Event_subsig_hw__Fence; subsig
| [ H : hw__FenceRel ?i ?x |- hw__Fence ?i ?x ] =>
  apply _hw__Fence_subsig_hw__FenceRel; subsig
| [ H : hw__FenceAcq ?i ?x |- hw__Fence ?i ?x ] =>
  apply _hw__Fence_subsig_hw__FenceAcq; subsig
| [ H : hw__FenceAcqRel ?i ?x |- hw__Fence ?i ?x ] =>
  apply _hw__Fence_subsig_hw__FenceAcqRel; subsig
| [ H : hw__FenceSC ?i ?x |- hw__FenceAcqRel ?i ?x ] =>
  apply _hw__FenceAcqRel_subsig_hw__FenceSC; subsig
| [ H : hw__FenceSC ?i ?x |- hw__Event ?i ?x ] =>
  apply _hw__Event_subsig_hw__Fence; subsig
| [ H : hw__FenceSC ?i ?x |- hw__Fence ?i ?x ] =>
  apply _hw__Fence_subsig_hw__FenceAcqRel; subsig
| [ H : hw__FenceRel ?i ?x |- hw__Event ?i ?x ] =>
  apply _hw__Event_subsig_hw__Fence; subsig
| [ H : hw__FenceAcq ?i ?x |- hw__Event ?i ?x ] =>
  apply _hw__Event_subsig_hw__Fence; subsig
| [ H : hw__FenceAcqRel ?i ?x |- hw__Event ?i ?x ] =>
  apply _hw__Event_subsig_hw__Fence; subsig
| [ H : hw__FenceSC ?i ?x |- hw__Event ?i ?x ] =>
  apply _hw__Event_subsig_hw__Fence; subsig
| [ H : hw__FenceSC ?i ?x |- hw__Fence ?i ?x ] =>
  apply _hw__Fence_subsig_hw__FenceAcqRel; subsig
| [ H : sw__Read ?i ?x |- sw__Event ?i ?x ] =>
  apply _sw__Event_subsig_sw__MemoryEvent; subsig
| [ H : sw__Write ?i ?x |- sw__Event ?i ?x ] =>
  apply _sw__Event_subsig_sw__MemoryEvent; subsig
| [ H : sw__Read ?i ?x |- sw__MemoryEvent ?i ?x ] =>
  apply _sw__MemoryEvent_subsig_sw__Read; subsig
| [ H : sw__Write ?i ?x |- sw__MemoryEvent ?i ?x ] =>
  apply _sw__MemoryEvent_subsig_sw__Write; subsig
| [ H : sw__MemoryEvent ?i ?x |- sw__Event ?i ?x ] =>
  apply _sw__Event_subsig_sw__MemoryEvent; subsig
| [ H : sw__Fence ?i ?x |- sw__Event ?i ?x ] =>
  apply _sw__Event_subsig_sw__Fence; subsig
| _ => solve [lr]
end.

Ltac assert_conclusion_helper CONC ORIG NAME := assert CONC as NAME; [apply ORIG|]; auto.

Ltac assert_conclusion H NAME :=
match type of H with
| ?A -> ?B -> ?C -> ?D -> ?E -> ?F -> ?G -> ?HH -> ?I -> ?J -> ?K -> ?X => assert_conclusion_helper X H NAME
| ?A -> ?B -> ?C -> ?D -> ?E -> ?F -> ?G -> ?HH -> ?I -> ?J -> ?X => assert_conclusion_helper X H NAME
| ?A -> ?B -> ?C -> ?D -> ?E -> ?F -> ?G -> ?HH -> ?I -> ?X => assert_conclusion_helper X H NAME
| ?A -> ?B -> ?C -> ?D -> ?E -> ?F -> ?G -> ?HH -> ?X => assert_conclusion_helper X H NAME
| ?A -> ?B -> ?C -> ?D -> ?E -> ?F -> ?G -> ?X => assert_conclusion_helper X H NAME
| ?A -> ?B -> ?C -> ?D -> ?E -> ?F -> ?X => assert_conclusion_helper X H NAME
| ?A -> ?B -> ?C -> ?D -> ?E -> ?X => assert_conclusion_helper X H NAME
| ?A -> ?B -> ?C -> ?D -> ?X => assert_conclusion_helper X H NAME
| ?A -> ?B -> ?C -> ?X => assert_conclusion_helper X H NAME
| ?A -> ?B -> ?X => assert_conclusion_helper X H NAME
| ?A -> ?X => assert_conclusion_helper X H NAME
| ?A => assert_conclusion_helper H H NAME
| _ => generalize H; intros NAME
end.

Ltac blast_types := try subsig; try contradiction_types; lr.

Ltac split_1 H AB b BC :=
  split_join_hyp H b AB BC; lr.

Ltac split_2 H AB b BC c CD :=
  split_1 H H c CD; split_1 H AB b BC.

Ltac split_3 H AB b BC c CD d DE :=
  split_1 H H d DE; split_2 H AB b BC c CD.

Ltac split_4 H AB b BC c CD d DE e EF :=
  split_1 H H e EF; split_3 H AB b BC c CD d DE.

Ltac split_5 H AB b BC c CD d DE e EF f FG :=
  split_1 H H f FG; split_4 H AB b BC c CD d DE e EF.

Ltac split_6 H AB b BC c CD d DE e EF f FG g GH :=
  split_1 H H g GH; split_5 H AB b BC c CD d DE e EF f FG.

Ltac join_1 a := apply r2_r2_join22 with a; lr.
Ltac join_2 a b := apply r2_r2_join22 with b; [join_1 a|]; lr.
Ltac join_3 a b c := apply r2_r2_join22 with c; [join_2 a b|]; lr.

Lemma sw_ident_self : forall _i (f : Relation 1) (x : Atom),
  f x -> util__ident _i f (x, x).
Proof.
  intros _i f x F.  split.
    unfold_ident.
    apply f_arrow_f; auto.
Qed.

Ltac unfold_iden :=
unfold_ident ||
match goal with
| [ H : util__ident ?i ?f (?x, ?y) |- _ ] =>
  unfold util__ident in H; destruct H as [? H]; unfold_iden
| [ H : ?f ?x |- util__ident ?f (?x, ?x) ] =>
  apply sw_ident_self; auto
| [ H : _ |- util__optional ?i ?f (?x, ?x) ] =>
  left; unfold_iden
end.

Ltac cycle_with x := exists (x, x); split; repeat unfold_iden; lr.

Lemma range_setof : forall (f : Relation 2) x y R,
  f (x, y)
  -> setof R (singleton_atom x; f)
  -> R y.
Proof.
  intros f x y r XY R.
  apply R.  apply r1_r2_join12 with x; auto.  apply singleton_self.
Qed.

Lemma range_oneof : forall (f : Relation 2) x y R,
  f (x, y)
  -> oneof R (singleton_atom x; f)
  -> R y.
Proof.
  intros f x y r XY R.
    destruct R as [R _].  apply R.  apply r1_r2_join12 with x; auto.  apply singleton_self.
Qed.

Ltac range_auto :=
  match goal with
  [ H1 : ?f (?x, ?y), H2 : setof ?R (singleton_atom ?x; ?f) |- _] =>
    try apply range_setof with f x y R in H2; auto
  | [ H1 : ?f (?x, ?y), H2 : oneof ?R (singleton_atom ?x; ?f) |- _] =>
    try apply range_oneof with f x y R in H2; auto
  end.

Lemma tc_co_domain : forall _i x y,
  compile_src11_ptx _i ->
  tc (hw__Write__co _i) (x, y) ->
  hw__Write _i x.
Proof.
  intros _i x y COMPILE XY.
  rem x y xy.  induction XY as [[x y] XY | [x y] a XA IHXA AY IHAY]; auto.
  Case "base".  apply _hw__Write__co_domain in XY; auto.
Qed.

Lemma fr_domain : forall _i x y,
  sw__rb _i (x, y) ->
  sw__Read _i x.
Proof.
  intros _i x y FR.  destruct FR as [FR|FR].
  Case "non-init".
    split_1 FR XA a AY.  apply transpose_pair in XA.
    assert_conclusion (_sw__Write__rf_range _i (singleton_atom a)) R;
      [apply oneof_singleton_atom; apply _sw__Write__rf_domain in XA; auto|].
    range_auto.
  Case "init".
    unfold_domain FR FR X.  unfold_range FR FR Y.  destruct X; auto.
Qed.

Lemma hw_fr_domain : forall _i x y,
  hw__fr _i (x, y) ->
  hw__Read _i x.
Proof.
  intros _i x y FR.  destruct FR as [FR|FR].
  Case "non-init".
    split_1 FR XA a AY.  apply transpose_pair in XA.
    assert_conclusion (_hw__Write__rf_range _i (singleton_atom a)) R;
      [apply oneof_singleton_atom; apply _hw__Write__rf_domain in XA; auto|].
    range_auto.
  Case "init".
    unfold_domain FR FR X.  unfold_range FR FR Y.  destruct X; auto.
Qed.

Ltac domain x :=
  match goal with
  | [ H : sw__Event__sb ?i (x, ?y) |- _ ] => apply _sw__Event__sb_domain in H; blast_types
  | [ H : sw__Write__rf ?i (x, ?y) |- _ ] => apply _sw__Write__rf_domain in H; blast_types
  | [ H : sw__Write__mo ?i (x, ?y) |- _ ] => apply _sw__Write__mo_domain in H; blast_types
  | [ H : sw__rb ?i (x, ?y) |- _ ] => apply fr_domain in H; blast_types
  | [ H : sw__Read__rmw ?i (x, ?y) |- _ ] => apply _sw__Read__rmw_domain in H; blast_types
  | [ H : sw__Event__map ?i (x, ?y) |- _ ] => apply _sw__Event__map_domain in H; blast_types
  | [ H : transpose (sw__Event__map ?i) (?y, x) |- _ ] => apply transpose_pair in H; domain x
  | [ H : hw__Event__po ?i (x, ?y) |- _ ] => apply _hw__Event__po_domain in H; blast_types
  | [ H : hw__Write__rf ?i (x, ?y) |- _ ] => apply _hw__Write__rf_domain in H; blast_types
  | [ H : hw__Write__co ?i (x, ?y) |- _ ] => apply _hw__Write__co_domain in H; blast_types
  | [ H : hw__Thread__start ?i (x, ?y) |- _ ] => apply _hw__Thread__start_domain in H; blast_types
  | [ H : sw__Thread__start ?i (x, ?y) |- _ ] => apply _sw__Thread__start_domain in H; blast_types
  | [ H : hw__fr ?i (x, ?y) |- _ ] => apply hw_fr_domain in H; blast_types
  | [ H : tc (hw__Write__co ?i) (x, ?y) |- _ ] => apply tc_co_domain in H; auto; blast_types
  | [ H : hw__Read__rmw ?i (x, ?y) |- _ ] => apply _hw__Read__rmw_domain in H; blast_types
  | [ H : sw__MemoryEvent__address ?i (x, ?y) |- _ ] => apply _sw__MemoryEvent__address_domain in H; blast_types
  | [ H : hw__MemoryEvent__address ?i (x, ?y) |- _ ] => apply _hw__MemoryEvent__address_domain in H; blast_types
  | [ H : hw__Event__scope ?i (x, ?y) |- _ ] => apply _hw__Event__scope_domain in H; blast_types
  | [ H : sw__Event__scope ?i (x, ?y) |- _ ] => apply _sw__Event__scope_domain in H; blast_types
  | [ H : sw__Scope__scopemap ?i (x, ?y) |- _ ] => apply _sw__Scope__scopemap_domain in H; blast_types
  | [ H : sw__Scope__subscope ?i (x, ?y) |- _ ] => apply _sw__Scope__subscope_domain in H; blast_types
  | [ H : sw__Event__memory_order ?i (x, ?y) |- _ ] => apply _sw__Event__memory_order_domain in H; blast_types
  | [ H : sw__ord ?i (?y, x) |- _ ] => apply transpose_pair in H; domain x
  end.

Ltac oneof_auto_domain :=
  match goal with
  [ H : _ |- oneof ?f (singleton_atom ?x) ] => apply oneof_singleton_atom; domain x
  end.

Ltac range_setof_helper FR :=
  match goal with
  [ H : ?f ?i (?x, ?y) |- ?r ?i ?y ] =>
    let R := fresh in let R2 := fresh in
    assert_conclusion (FR i (singleton_atom x)) R; try oneof_auto_domain;
    assert_conclusion (R y) R2; try (apply r1_r2_join12 with x; auto; apply singleton_self)
  end.

Ltac range_oneof_helper FR :=
  match goal with
  [ H : ?f ?i (?x, ?y) |- ?r ?i ?y ] =>
    let R := fresh in let R2 := fresh in
    assert_conclusion (FR i (singleton_atom x)) R; try oneof_auto_domain; destruct R as [R _];
    assert_conclusion (R y) R2; try (apply r1_r2_join12 with x; auto; apply singleton_self)
  end.

Ltac auto_range :=
  try solve [try range_setof_helper _hw__Write__rf_range];
  try solve [try range_oneof_helper _hw__Event__po_range];
  try solve [try range_oneof_helper _hw__Event__scope_range];
  try solve [try range_oneof_helper _hw__MemoryEvent__address_range];
  try solve [try range_setof_helper _hw__Write__co_range];
  try solve [try range_setof_helper _sw__Event__sb_range];
  try solve [try range_setof_helper _sw__Write__rf_range];
  try solve [try range_setof_helper _sw__Write__mo_range];
  try solve [try range_oneof_helper _sw__Event__map_range];
  try solve [try range_oneof_helper _sw__Thread__start_range];
  try solve [try range_setof_helper _sw__Scope__subscope_range].

Ltac oneof_auto :=
  match goal with
  [ H : _ |- oneof ?f (singleton_atom ?x) ] => apply oneof_singleton_atom; domain x
  | [ H : _ |- oneof ?f (singleton_atom ?x) ] => apply oneof_singleton_atom; auto_range
  end.

Lemma co_range : forall _i x y,
  hw__Write__co _i (x, y)
  -> hw__Write _i y.
Proof.
  intros _i x y XY.  auto_range.
Qed.

Lemma map_range : forall _i x y,
  sw__Event__map _i (x, y)
  -> hw__Event _i y.
Proof.
  intros _i x y XY.  auto_range.
Qed.

Lemma sb_range : forall _i x y,
  sw__Event__sb _i (x, y)
  -> sw__Event _i y.
Proof.
  intros _i x y XY.  auto_range.
Qed.

Lemma po_range : forall _i x y,
  hw__Event__po _i (x, y)
  -> hw__Event _i y.
Proof.
  intros _i x y XY.  auto_range.
Qed.

Lemma tc_co_range : forall _i x y,
  compile_src11_ptx _i ->
  tc (hw__Write__co _i) (x, y) ->
  hw__Write _i y.
Proof.
  intros _i x y COMPILE XY.
  rem x y xy.  induction XY as [[x y] XY | [x y] a XA IHXA AY IHAY]; auto.
  Case "base".  auto_range.
Qed.

Lemma fr_range : forall _i x y,
  sw__rb _i (x, y) ->
  sw__Write _i y.
Proof.
  intros _i x y FR.  destruct FR as [FR|FR].
  Case "non-init".
    split_1 FR XA a AY.  auto_range.
  Case "init".
    unfold_domain FR FR X.  unfold_range FR FR Y; auto.
Qed.

Lemma hw_fr_range : forall _i x y,
  compile_src11_ptx _i ->
  hw__fr _i (x, y) ->
  hw__Write _i y.
Proof.
  intros _i x y COMPILE FR.
  destruct FR as [FR|FR].
  Case "non-init".
    split_1 FR XA a AY.  apply tc_co_range in AY; auto.
  Case "init".
    unfold_domain FR FR X.  unfold_range FR FR Y.  auto.
Qed.

(*
Ltac do_r R y :=
match goal with
| [ F : ?f ?i (?x, y) |- _ ] =>
  generalize (R i (singleton_atom x)); intros ?RR; apply r2_join12, RR in F; try domain x; auto
end.

Ltac range y :=
  match goal with
  | [ H : sw__Event__sb ?i (?x, y) |- _ ] => do_r _sw__Event__sb_range y; blast_types
  | [ H : sw__Write__rf ?i (?x, y) |- _ ] => do_r _sw__Write__rf_range y; blast_types
  | [ H : sw__Write__mo ?i (?x, y) |- _ ] => do_r _sw__Write__mo_range y; blast_types
  | [ H : sw__rb ?i (?x, y) |- _ ] => apply fr_range in H; blast_types
  | [ H : sw__Read__rmw ?i (?x, y) |- _ ] => do_r _sw__Read__rmw_range y; blast_types
  | [ H : sw__Event__map ?i (?x, y) |- _ ] => do_r _sw__Event__map_range y; blast_types
  | [ H : hw__Read__rmw ?i (?x, y) |- _ ] => do_r _hw__Read__rmw_range y; blast_types
  | [ H : hw__Event__po ?i (?x, y) |- _ ] => do_r _hw__Event__po_range y; blast_types
  | [ H : hw__Write__rf ?i (?x, y) |- _ ] => do_r _hw__Write__rf_range y; blast_types
  | [ H : hw__Write__co ?i (?x, y) |- _ ] => do_r _hw__Write__co_range y; blast_types
  | [ H : hw__Thread__start ?i (?x, y) |- _ ] => do_r _hw__Thread__start_range y; blast_types
  | [ H : hw__fr ?i (?x, y) |- _ ] => apply hw_fr_range in H; blast_types
  | [ H : tc (hw__Write__co ?i) (?x, y) |- _ ] => apply tc_co_range in H; auto; try domain x; blast_types
  | [ H : hw__MemoryEvent__address ?i (?x, y) |- _ ] => do_r _hw__MemoryEvent__address_range y; blast_types
  | [ H : hw__Event__scope ?i (?x, y) |- _ ] => do_r _hw__Event__scope_range y; blast_types
  end.
*)

Ltac blast_dr x :=
  try apply oneof_singleton_atom;
  match goal with
  [ H : _ |- _ ] =>
    first [
        solve [destruct H as [H|H]; blast_dr x]
      | solve [destruct H as [H|H]; blast_dr x]
      | solve [domain x]
      | solve [auto_range]
    ]
  end.

Ltac auto_cases H :=
  first [
      solve [lr]
    | destruct H as [H|H]; [solve [auto_cases H]|]; auto_cases H
    | destruct H as [H|H]; [|solve [auto_cases H]]; auto_cases H
    | lr
  ].

(******************************************************************************)

Ltac compile x X o COM :=
match goal with
| [ COMPILE : compile_src11_ptx ?_i |- _ ] =>
  assert (X _i) as C by (destructs COMPILE);
  assert_conclusion (C (singleton_atom x)) COM; [
    apply oneof_singleton_atom; split; auto; apply r1_r2_join12 with o; auto;
    apply untranspose_pair; apply join12_r2; auto|]
end.

Ltac ic x COM :=
match goal with
| [ XE: sw__Event ?_i x, COMPILE: compile_src11_ptx ?_i |- _ ] =>
  apply _sw__Event_abstract in XE; destruct XE as [XE|XE]; [
    apply _sw__MemoryEvent_abstract in XE; destruct XE as [XE|XE]; [
      Case "Write";
        assert (oneof (sw__MemoryOrder _i) (join (singleton_atom x) (sw__Event__memory_order _i)))
          as ORD by (apply _sw__Event__memory_order_range);
        destruct ORD as [O [[o XO] _]]; generalize XO; intros MO;
        apply WriteMO in MO; [|apply oneof_singleton_atom; auto];
        destruct MO as [[NA|RLX]|REL]; [
          SCase "NA";  compile x compile_write_na o COM |
          SCase "RLX";  compile x compile_write_rx o COM | 
          SCase "REL";  compile x compile_write_rl o COM ]
      |
      Case "Read";
        assert (oneof (sw__MemoryOrder _i) (join (singleton_atom x) (sw__Event__memory_order _i)))
          as ORD by (apply _sw__Event__memory_order_range);
        destruct ORD as [O [[o XO] _]]; generalize XO; intros MO;
        apply ReadMO in MO; [|apply oneof_singleton_atom; auto];
        destruct MO as [[NA|RLX]|ACQ]; [
          SCase "NA";  compile x compile_read_na o COM |
          SCase "RLX";  compile x compile_read_rx o COM | 
          SCase "ACQ";  compile x compile_read_aq o COM ]
      ]
    |
    Case "Fence";
      assert (oneof (sw__MemoryOrder _i) (join (singleton_atom x) (sw__Event__memory_order _i)))
        as ORD by (apply _sw__Event__memory_order_range);
      destruct ORD as [O [[o XO] _]]; generalize XO; intros MO;
      apply FenceMO in MO; [|apply oneof_singleton_atom; auto];
      destruct MO as [[[ACQ|REL]|AR]|SCST]; [
          SCase "ACQ";  compile x compile_fence_aq o COM | 
          SCase "REL";  compile x compile_fence_rl o COM |
          SCase "AR";  compile x compile_fence_ar o COM |
          SCase "SC";  compile x compile_fence_sc o COM ]
    ]
    end.

(******************************************************************************)

Ltac drs AB A B :=
  apply domain_split in AB; destruct AB as [AB A];
  apply range_split in AB; destruct AB as [AB B].

Ltac drj := apply domain_unsplit; lr; try (apply range_unsplit; lr).

Lemma sw__Event__map_unique : forall _i x x1' x2',
  compile_src11_ptx _i ->
  sw__Event__map _i (x, x1') ->
  sw__Event__map _i (x, x2') ->
  x1' = x2'.
Proof.
  intros _i x x1' x2' COMPILE X1 X2.
  assert (sw__Event _i x) as X by (domain x).
  assert_conclusion (_sw__Event__map_range _i (singleton_atom x)) R.
  assert (lone (singleton_atom x; sw__Event__map _i)) as L by (destructs R).
  apply L; apply r1_r2_join12 with x; try apply singleton_self; auto.
Qed.

Lemma sw__Scope__scopemap_unique : forall _i s s1' s2',
  compile_src11_ptx _i ->
  sw__Scope__scopemap _i (s, s1') ->
  sw__Scope__scopemap _i (s, s2') ->
  s1' = s2'.
Proof.
  intros _i s s1' s2' COMPILE S1 S2.
  assert (sw__Scope _i s) as S by (domain s).
  assert_conclusion (_sw__Scope__scopemap_range _i (singleton_atom s)) R.
  assert (lone (singleton_atom s; sw__Scope__scopemap _i)) as L by (destructs R).
  apply L; apply r1_r2_join12 with s; try apply singleton_self; auto.
Qed.

Lemma join_auto : forall (f : Relation 2) x y,
  f (x, y)
  -> (singleton_atom x; f) y.
Proof.
  intros f x y XY.
  apply r1_r2_join12 with x; auto; apply singleton_self; auto.
Qed.
Ltac join_auto := apply join_auto.

Lemma lone_inv_map : forall _i x1 x2 x',
  compile_src11_ptx _i ->
  sw__Event__map _i (x1, x') ->
  sw__Event__map _i (x2, x') ->
  x1 = x2.
Proof.
  intros _i x1 x2 x' COMPILE X1 X2.
  assert (wf_map_insts _i) as WF by (destructs COMPILE).
  assert (forall e, oneof (hw__Event _i) e -> one (e; tr (sw__Event__map _i)))
    as R by (destructs WF).
  assert_conclusion (R (singleton_atom x')) RX.
    apply oneof_singleton_atom.  auto_range.
  assert (lone (singleton_atom x'; tr (sw__Event__map _i))) as L by (destructs RX).
  apply L; join_auto; auto.
Qed.

Lemma lone_inv_scopemap : forall _i s1 s2 s',
  compile_src11_ptx _i ->
  sw__Scope__scopemap _i (s1, s') ->
  sw__Scope__scopemap _i (s2, s') ->
  s1 = s2.
Proof.
  intros _i s1 s2 s' COMPILE S1 S2.
  assert (wf_map_scope _i) as WF by (destructs COMPILE).
  assert_conclusion (WF (s1, s2)) WF1.
  join_1 s'.
Qed.

Lemma reuse_sw__Event__maps : forall _i (f : Relation 2) x y x' y',
  compile_src11_ptx _i
  -> x --(sw__Event__map _i)--> x'
  -> y --(sw__Event__map _i)--> y'
  -> x --(sw__Event__map _i; f; tr (sw__Event__map _i))--> y
  -> x' --(f)--> y'.
Proof.
  intros _i f x y x' y' COMPILE X' Y' XY.
  split_2 XY X2' x2' XY y2' Y2'.
  assert (x2' = x') by (apply (sw__Event__map_unique _i) with x; auto); unfold_iden; clear X2'.
  assert (y2' = y') by (apply (sw__Event__map_unique _i) with y; auto); unfold_iden; clear Y2'.
  auto.
Qed.

Ltac unfold_map := match goal with
| [ H1 : sw__Event__map ?i (?x1, ?x), H2 : sw__Event__map ?i (?x2, ?x) |- _ ] =>
  assert (x2 = x1) as _I by (apply (lone_inv_map i) with x; auto); unfold_iden; clear H2
| [ H1 : sw__Event__map ?i (?x1, ?x), H2 : sw__Event__map ?i (?x2, ?x) |- _ ] =>
  assert (x2 = x1) as _I by (destruct H1; apply (lone_inv_map i) with x; auto); unfold_iden; clear H2
| [ H1 : sw__Event__map ?i (?x1, ?x), H2 : sw__Event__map ?i (?x2, ?x) |- _ ] =>
  assert (x2 = x1) as _I by (destruct H1; destruct H2; apply (lone_inv_map i) with x; auto); unfold_iden; clear H2
| [ H1 : sw__Event__map ?i (?x, ?x1), H2 : sw__Event__map ?i (?x, ?x2) |- _ ] =>
  assert (x2 = x1) as _I by (apply (sw__Event__map_unique i x); auto); unfold_iden; clear H2
| [ H1 : sw__Event__map ?i (?x, ?x1), H2 : sw__Event__map ?i (?x, ?x2) |- _ ] =>
  assert (x2 = x1) as _I by (apply (sw__Event__map_unique i x); auto); unfold_iden; clear H2
| [ H1 : sw__Scope__scopemap ?i (?x1, ?x), H2 : sw__Scope__scopemap ?i (?x2, ?x) |- _ ] =>
  assert (x2 = x1) as _I by (apply (lone_inv_map i) with x; auto); unfold_iden; clear H2
| [ H1 : sw__Scope__scopemap ?i (?x1, ?x), H2 : sw__Scope__scopemap ?i (?x2, ?x) |- _ ] =>
  assert (x2 = x1) as _I by (destruct H1; apply (lone_inv_map i) with x; auto); unfold_iden; clear H2
| [ H1 : sw__Scope__scopemap ?i (?x1, ?x), H2 : sw__Scope__scopemap ?i (?x2, ?x) |- _ ] =>
  assert (x2 = x1) as _I by (destruct H1; destruct H2; apply (lone_inv_map i) with x; auto); unfold_iden; clear H2
| [ H1 : sw__Scope__scopemap ?i (?x, ?x1), H2 : sw__Scope__scopemap ?i (?x, ?x2) |- _ ] =>
  assert (x2 = x1) as _I by (apply (sw__Scope__scopemap_unique i x); auto); unfold_iden; clear H2
| [ H1 : sw__Scope__scopemap ?i (?x, ?x1), H2 : sw__Scope__scopemap ?i (?x, ?x2) |- _ ] =>
  assert (x2 = x1) as _I by (apply (sw__Scope__scopemap_unique i x); auto); unfold_iden; clear H2
| [ H1 : sw__Scope__scopemap ?i (?x, ?x1), H2 : tr (sw__Scope__scopemap ?i) (?x2, ?x) |- _ ] =>
  apply transpose_pair in H2; unfold_map
| [ H : transpose (sw__Event__map ?i) (?x, ?x1) |- _ ] =>
  apply transpose_pair in H; unfold_map
| [ H : transpose (sw__Event__map ?i) (?x, ?x1) |- _ ] =>
  apply transpose_pair in H; unfold_map
| [ H : tr (sw__Event__map ?i) (?x, ?x1) |- _ ] =>
  apply transpose_pair in H; unfold_map
| [ H1 : ?x --(sw__Event__map ?i)--> ?x', H2: ?y --(sw__Event__map ?i)--> ?y', H3: ?x --(sw__Event__map ?i; ?f; tr (sw__Event__map ?i))--> ?y |- _ ] =>
  apply reuse_sw__Event__maps with i f x y x' y' in H3; auto
| [ H1 : ?x --(sw__Event__map ?i)--> ?x', H2: ?y --(sw__Event__map ?i)--> ?y', H3: ?x --(sw__Event__map ?i; ?f; transpose (sw__Event__map ?i))--> ?y |- _ ] =>
  apply reuse_sw__Event__maps with i f x y x' y' in H3; auto
end.

(******************************************************************************)

Lemma A_Event : forall _i x,
  sw__A _i x ->
  sw__Event _i x.
Proof.
  intros _i x X.  destruct X as [[[[X|X]|X]|X]|X];
  apply join12_r1_r2 in X; destruct X as [o [O X]]; domain x.
Qed.
Hint Resolve A_Event.

Lemma lone_ord : forall _i x o1 o2,
  o1 --(sw__ord _i)--> x
  -> o2 --(sw__ord _i)--> x
  -> o1 = o2.
Proof.
  intros _i x o1 o2 X1 X2.  apply transpose_pair in X1; apply transpose_pair in X2.
  assert_conclusion (_sw__Event__memory_order_range _i (singleton_atom x)) R.
    oneof_auto.
  apply R; apply r2_join12; auto.
Qed.

Lemma map_singleton : forall _i x x',
  x --(sw__Event__map _i)--> x'
  -> (singleton_atom x; sw__Event__map _i) x'.
Proof.
  intros _i x x' X'.  apply r2_join12.  destructs X'.
Qed.
Hint Resolve map_singleton.

(*
Lemma A_map_strong : forall _i x y x' y',
  compile_src11_ptx _i
  -> sw__A _i x
  -> sw__A _i y
  -> x --(sw__Event__map _i)--> x'
  -> y --(sw__Event__map _i)--> y'
  -> hw__strong_r _i (x', y').
Proof.
  intros _i x y x' y' COMPILE X_A Y_A X' Y'.
  assert (compile_scope _i) as A_SCOPE by (destructs COMPILE).
  assert_conclusion (_hw__Event__scope_range _i (singleton_atom x')) SX.
  assert_conclusion (_hw__Event__scope_range _i (singleton_atom y')) SY.
  apply singleton_atom_oneof in SX.  destruct SX as [sx [SX1 [SX2 SX3]]].
  apply singleton_atom_oneof in SY.  destruct SY as [sy [SY1 [SY2 SY3]]].
  destruct A_SCOPE as [_ A_SCOPE].

  assert_conclusion (A_SCOPE sx sy) SCOPE.
    apply r1_r2_join12 with x'; auto.
      apply r1_r2_join12 with x; auto.
    apply join12_r2; auto.
    apply r1_r2_join12 with y'; auto.
      apply r1_r2_join12 with y; auto.
    apply join12_r2; auto.
  unfold_iden.

  split.
    repeat apply join_assoc_l.  join_1 sy.
      apply join12_r2; auto.
    apply join12, untranspose_pair, scope_inclusion in SY1.
    repeat apply join_assoc_r; auto.
    repeat apply join_assoc_l.  join_1 sy.
      apply join12_r2; auto.
    apply join12, untranspose_pair, scope_inclusion in SX1.
    repeat apply join_assoc_r; auto.
Qed.
Hint Resolve A_map_strong.
*)

(******************************************************************************)

Inductive tc_l (a : Relation 2) (x : Tuple 2) : Prop :=
| tc_l_one : a x -> tc_l a x
| tc_l_more y : tc_l a (fst x, y) -> a (y, snd x) -> tc_l a x.

Inductive tc_r (a : Relation 2) (x : Tuple 2) : Prop :=
| tc_r_one : a x -> tc_r a x
| tc_r_more y : a (fst x, y) -> tc_r a (y, snd x) -> tc_r a x.

Lemma tc_l_tc_l (f : Relation 2) (x y z : Atom) : tc_l f (x, y) -> tc_l f (y, z) -> tc_l f (x, z).
Proof.
  intros XY YZ.  rem y z yz.
  induction YZ as [[y z] YZ|[y z] a H1 IH H2].
  Case "Base".
    right with y; lr.
  Case "Ind".
    unfold fst, snd in *.  apply IH in XY.  right with a; lr.
Qed.

Lemma tc_r_tc_r (f : Relation 2) (x y z : Atom) : tc_r f (x, y) -> tc_r f (y, z) -> tc_r f (x, z).
Proof.
  intros XY YZ.  rem x y xy.
  induction XY as [[x y] XY|[x y] a H1 H2 IH].
  Case "Base".
    right with y; lr.
  Case "Ind".
    unfold fst, snd in *.  apply IH in YZ.  right with a; lr.
Qed.

Lemma tc_tc_l (f : Relation 2) (x : Tuple 2) : tc f x <-> tc_l f x.
Proof.
  split; intros H.
  Case "tc -> tc_l".
    induction H as [x H|[x z] y H1 IH1 H2 IH2]; lr.
    SCase "inductive".
      destruct IH2 as [IH2|b IH2].
      SSCase "base".
        right with y; lr.
      SSCase "ind".
        unfold fst, snd in *.  right with b; lr.  apply tc_l_tc_l with y; lr.
  Case "tc_l -> tc".
    induction H as [xy H|[x y] a H1 IH H2]; lr.
    SCase "ind".
      unfold fst, snd in *.  right with a; lr.
Qed.

Lemma tc_tc_r (f : Relation 2) (x : Tuple 2) : tc f x <-> tc_r f x.
Proof.
  split; intros H.
  Case "tc -> tc_r".
    induction H as [x H|[x z] y H1 IH1 H2 IH2]; lr.
    SCase "inductive".
      destruct IH1 as [IH1|b IH1].
      SSCase "base".
        right with y; lr.
      SSCase "ind".
        unfold fst, snd in *.  right with b; lr.  apply tc_r_tc_r with y; lr.
  Case "tc_r -> tc".
    induction H as [xy H|[x y] a H1 H2 IH]; lr.
    SCase "ind".
      unfold fst, snd in *.  right with a; lr.
Qed.

(******************************************************************************)

Lemma oneof_exists : forall (f : Relation 1) r,
  oneof f r
  -> exists x, r x.
Proof.
  intros f r F.  destruct F as [INSIDE [[x SOME] LONE]].  exists x; auto.
Qed.

Lemma low_read_read : forall _i x x',
  compile_src11_ptx _i
  -> sw__Read _i x
  -> x --(sw__Event__map _i)--> x'
  -> hw__Read _i x'.
Proof.
  intros _i x x' COMPILE X X'.
  assert_conclusion (_sw__Event__memory_order_range _i (singleton_atom x)) ORD.
    oneof_auto.
  apply oneof_exists in ORD.  destruct ORD as [o ORD].
  assert_conclusion (ReadMO _i (singleton_atom x)) R.
  destruct R with o as [[NA|RLX]|ACQ]; auto.
  Case "NA".
    assert (compile_read_na _i) as C by (destructs COMPILE).
    apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    apply r1_r2_join12 with o; auto.  apply untranspose_pair, join12_r2; auto.
  Case "RLX".
    assert (compile_read_rx _i) as C by (destructs COMPILE).
    apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    apply r1_r2_join12 with o; auto.  apply untranspose_pair, join12_r2; auto.
  Case "ACQ".
    assert (compile_read_aq _i) as C by (destructs COMPILE).
    apply _hw__Read_subsig_hw__Acquire.
    apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    apply r1_r2_join12 with o; auto.  apply untranspose_pair, join12_r2; auto.
Qed.

Lemma low_write_write : forall _i x x',
  compile_src11_ptx _i
  -> sw__Write _i x
  -> x --(sw__Event__map _i)--> x'
  -> hw__Write _i x'.
Proof.
  intros _i x x2' COMPILE X X'.
  assert_conclusion (_sw__Event__memory_order_range _i (singleton_atom x)) ORD.
    oneof_auto.
  apply oneof_exists in ORD.  destruct ORD as [o ORD].
  assert_conclusion (WriteMO _i (singleton_atom x)) R.
  destruct R with o as [[NA|RLX]|REL]; auto.
  Case "NA".
    assert (compile_write_na _i) as C by (destructs COMPILE).
    apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    apply r1_r2_join12 with o; auto.  apply untranspose_pair, join12_r2; auto.
  Case "RLX".
    assert (compile_write_rx _i) as C by (destructs COMPILE).
    apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    apply r1_r2_join12 with o; auto.  apply untranspose_pair, join12_r2; auto.
  Case "Rel".
    assert (compile_write_rl _i) as C by (destructs COMPILE).
    apply _hw__Write_subsig_hw__Release.
    apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    apply r1_r2_join12 with o; auto.  apply untranspose_pair, join12_r2; auto.
Qed.

(******************************************************************************)

(** ** Lemmas about syncacqrel *)

(** *** Lemma [tc_po_cause_base] *)
(** ^po.^cause_base is ^cause_base *)
Lemma tc_po_cause_base : forall _i x y z,
  compile_src11_ptx _i ->
  tc (hw__Event__po _i) (x, y) ->
  hw__cause_base _i (y, z) ->
  hw__cause_base _i (x, z).
Proof.
  intros _i x y z COMPILE_src11_ptx XY YZ.
  (* proof by induction *)
  rem y z yz.  induction YZ as [[y z] YZ|[y z] a H1 IH1 H2 IH2].
  Case "base".
    (* split up syncacqrel into its components *)
    split_join_hyp_twice YZ a b YA AB BZ.
    (* reassemble it, but stick the extra ^po in the front *)
    left.  apply r2_r2_join22 with b; lr.  apply r2_r2_join22 with a; lr.
    right; apply tc_rtc with y; lr.
  Case "ind".
    (* just stick the two ^syncacqrel's back together *)
    unfold fst, snd in *.  apply IH1 in XY.  right with a; lr.
Qed.

(** *** Lemma [tc_po_syncacqrel] *)
(** ^po.^syncacqrel is ^syncacqrel *)
Lemma tc_po_syncacqrel : forall _i x y z,
  compile_src11_ptx _i ->
  tc (hw__Event__po _i) (x, y) ->
  tc (syncacqrel _i) (y, z) ->
  tc (syncacqrel _i) (x, z).
Proof.
  intros _i x y z COMPILE_src11_ptx XY YZ.
  (* proof by induction *)
  rem y z yz.  induction YZ as [[y z] YZ|[y z] a H1 IH1 H2 IH2].
  Case "base".
    (* split up syncacqrel into its components *)
    split_join_hyp_twice YZ a b YA AB BZ.
    (* reassemble it, but stick the extra ^po in the front *)
    left.  apply r2_r2_join22 with b; lr.  apply r2_r2_join22 with a; lr.
    right; apply tc_rtc with y; lr.
  Case "ind".
    (* just stick the two ^syncacqrel's back together *)
    unfold fst, snd in *.  apply IH1 in XY.  right with a; lr.
Qed.

(** *** Lemma [cause_base_tc_po] *)
(** ^cause_base.^po is ^cause_base *)
Lemma cause_base_tc_po : forall _i x y z,
  compile_src11_ptx _i ->
  hw__cause_base _i (x, y) ->
  tc (hw__Event__po _i) (y, z) ->
  hw__cause_base _i (x, z).
Proof.
  intros _i x y z COMPILE_src11_ptx XY YZ.  rem x y xy.
  (* proof by induction *)
  induction XY as [[x y] XY|[x y] a H1 IH1 H2 IH2].
  Case "base".
    (* split up cause_base into its components *)
    split_join_hyp_twice XY a b XA AB BY.
    (* reassemble it, but stick the extra ^po at the end *)
    left.  apply r2_r2_join22 with b; lr.  apply r2_r2_join22 with a; lr.
    right; apply rtc_tc with y; lr.
  Case "ind".
    (* just stick the two ^cause_base's back together *)
    unfold fst, snd in *.  apply IH2 in YZ.  right with a; lr.
Qed.

(** *** Lemma [syncacqrel_tc_po] *)
(** ^syncacqrel.^po is ^syncacqrel *)
Lemma syncacqrel_tc_po : forall _i x y z,
  compile_src11_ptx _i ->
  tc (syncacqrel _i) (x, y) ->
  tc (hw__Event__po _i) (y, z) ->
  tc (syncacqrel _i) (x, z).
Proof.
  intros _i x y z COMPILE_src11_ptx XY YZ.  rem x y xy.
  (* proof by induction *)
  induction XY as [[x y] XY|[x y] a H1 IH1 H2 IH2].
  Case "base".
    (* split up syncacqrel into its components *)
    split_join_hyp_twice XY a b XA AB BY.
    (* reassemble it, but stick the extra ^po at the end *)
    left.  apply r2_r2_join22 with b; lr.  apply r2_r2_join22 with a; lr.
    right; apply rtc_tc with y; lr.
  Case "ind".
    (* just stick the two ^syncacqrel's back together *)
    unfold fst, snd in *.  apply IH2 in YZ.  right with a; lr.
Qed.

Lemma po_syncacqrel_po_syncacqrel : forall _i x y,
  compile_src11_ptx _i
  -> (((tc (hw__Event__po _i)) U (tc (syncacqrel _i)));
      ((tc (hw__Event__po _i)) U (tc (syncacqrel _i)))) (x, y)
  -> (tc (hw__Event__po _i) U (tc (syncacqrel _i))) (x, y).
Proof.
  intros _i x y COMPILE XY.  split_1 XY XM m MY.
  destruct XM as [XM|XM]; destruct MY as [MY|MY].
  Case "po;po".
    choose (tc (hw__Event__po _i) (x, y)).  right with m; auto.
  Case "po;syncacqrel".
    choose (tc (syncacqrel _i) (x, y)).  apply tc_po_syncacqrel with m; auto.
  Case "syncacqrel;po".
    choose (tc (syncacqrel _i) (x, y)).  apply syncacqrel_tc_po with m; auto.
  Case "syncacqrel;syncacqrel".
    choose (tc (syncacqrel _i) (x, y)).  right with m; auto.
Qed.
Hint Resolve po_syncacqrel_po_syncacqrel.

Lemma syncacqrel_cause_base : forall _i x y,
  syncacqrel _i (x, y) ->
  hw__cause_base _i (x, y).
Proof.
  intros _i x y syncacqrel.
  split_join_hyp_twice syncacqrel a b XA AB BY.
  left.  apply r2_r2_join22 with b; lr.  apply r2_r2_join22 with a; lr.
Qed.

Lemma tc_syncacqrel_cause_base : forall _i x y,
  tc (syncacqrel _i) (x, y) ->
  hw__cause_base _i (x, y).
Proof.
  intros _i x y XY.
  rem x y xy.  induction XY as [[x y] XY | [x y] a XA IHXA AY IHAY].
  Case "Base".
    apply syncacqrel_cause_base; auto.
  Case "ind".
    right with a; lr.
Qed.

Lemma tc_syncacqrel_syncacqrel : forall _i x' y',
  tc (syncacqrel _i) (x', y') ->
  hw__cause _i (x', y').
Proof.
  intros _i x' y' syncacqrel.
  apply tc_syncacqrel_cause_base in syncacqrel; lr.
Qed.

(******************************************************************************)

Lemma some_map : forall _i x,
  compile_src11_ptx _i
  -> sw__Event _i x
  -> exists x', x --(sw__Event__map _i)--> x'.
Proof.
  intros _i x COMPILE X.
  assert (forall e, oneof (sw__Event _i) e -> some (e; sw__Event__map _i))
    as WF by (destructs COMPILE).
  assert_conclusion (WF (singleton_atom x)) X'.  clean X' x'.  exists x'; auto.
Qed.

Lemma sb_po : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__Event__sb _i)--> y
  -> x --(sw__Event__map _i; tc (hw__Event__po _i); tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE XY.
  assert (wf_map_insts _i) as WF by (destructs COMPILE).
  apply WF; auto.
Qed.

Lemma loc_map : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__loc _i)--> y
  -> x --(sw__Event__map _i; (hw__MemoryEvent__address _i; tr (hw__MemoryEvent__address _i)); tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE XY.
  split_1 XY XA a YA.  apply transpose_pair in YA.
  assert (wf_map_addrs _i) as WF by (destructs COMPILE).
  apply WF in XA.  apply WF in YA.  clear WF.
  split_2 XA X' x' XA xa' XA'.  split_2 YA Y' y' YA ya' YA'.
  apply transpose_pair in XA'.  apply transpose_pair in YA'.

  assert (xa' = ya'); try unfold_iden.
    assert_conclusion (_sw__Address__addrmap_range _i (singleton_atom a)) R.
      apply oneof_singleton_atom.  apply _sw__Address__addrmap_domain in YA'; auto.
    assert (lone (singleton_atom a; sw__Address__addrmap _i)) as L by (destructs R).
    apply r2_join12 in XA'.  apply r2_join12 in YA'.  apply L; auto.

  join_2 x' y'.  join_1 ya'.
Qed.

Lemma low_release : forall _i x x',
  compile_src11_ptx _i
  -> ((sw__REL _i U sw__AR _i) U sw__SC _i) x
  -> x --(sw__Event__map _i)--> x'
  -> sw__MemoryEvent _i x
  -> hw__Release _i x'.
Proof.
  intros _i x x' COMPILE X XM X'.
  assert (sw__Event _i x) as XE by (domain x).
  apply _sw__Event_abstract in XE.  destruct XE as [XE|XE].
  apply _sw__MemoryEvent_abstract in XE.  destruct XE as [XE|XE].
  Case "Write".
    destruct X as [[X|X]|X].
    SCase "REL".
      assert (compile_write_rl _i) as C by (destructs COMPILE).
      apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    SCase "AR".
      assert_conclusion (WriteMO _i (singleton_atom x)) MO.
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
    SCase "SC".
      assert_conclusion (WriteMO _i (singleton_atom x)) MO.
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
  Case "Read".
    assert_conclusion (ReadMO _i (singleton_atom x)) MO.
    destruct X as [[X|X]|X].
    SCase "REL".
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
    SCase "AR".
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
    SCase "SC".
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
  Case "Fence".
    contradiction_types.
Qed.

Lemma low_rel_fence : forall _i x x',
  compile_src11_ptx _i
  -> ((sw__REL _i U sw__AR _i) U sw__SC _i) x
  -> sw__Fence _i x
  -> sw__Event__map _i (x, x')
  -> hw__FenceRels _i x'.
Proof.
  intros _i x x1' COMPILE X_MO X_F X1'.
  destruct X_MO as [[X_MO|X_MO]|X_MO].
  Case "REL".
    assert (compile_fence_rl _i) as C by (destructs COMPILE).
    choose (hw__FenceRel _i x1').  apply C.
    apply r1_r2_join12 with x; auto.  split; auto.
  Case "AR".
    assert (compile_fence_ar _i) as C by (destructs COMPILE).
    choose (hw__FenceAcqRel _i x1').  apply C.
    apply r1_r2_join12 with x; auto.  split; auto.
  Case "SC".
    assert (compile_fence_sc _i) as C by (destructs COMPILE).
    choose (hw__FenceAcqRel _i x1').
    apply _hw__FenceAcqRel_subsig_hw__FenceSC.
    apply C.
    apply r1_r2_join12 with x; auto.  split; auto.
Qed.

Lemma fsb_sbloc_prefix : forall _i x y z,
  compile_src11_ptx _i
  -> ((sw__REL _i) U (sw__AR _i) U (sw__SC _i)) x
  -> util__optional _i (util__ident _i (sw__Fence _i); sw__Event__sb _i) (x, y)
  -> util__optional _i (intersect (sw__Event__sb _i) (sw__loc _i)) (y, z)
  -> sw__Write _i z
  -> x --((sw__Event__map _i; hw__prefix _i; tr (sw__Event__map _i)))--> z.
Proof.
  intros _i x y z COMPILE X XY YZ ZW.
  destruct XY as [XY|XY].
  Case "x=y".
    unfold_iden.
    assert (sw__Event _i y) as Y by (destruct X as [[X|X]|X];
      apply join12_r1_r2 in X; destruct X as [o [O X]]; apply transpose_pair in X; domain y).
    assert (sw__Event _i z) as ZE.
      destruct YZ as [YZ|YZ]; try solve [unfold_iden; auto].
      destruct YZ; auto_range.
    apply some_map in Y; auto.  destruct Y as [y' Y'].
    apply some_map in ZE; auto.  destruct ZE as [z' Z'].
    join_2 y' z'.  destruct YZ as [YZ|YZ].
    SCase "y=z".
      unfold_iden.  unfold_map.  left.  drj.
      SSCase "Release".
        apply low_release with z; auto.  subsig.
      SSCase "optional".
        unfold_iden.
      SSCase "Write".
        apply low_write_write with z; auto.
    SCase "y->z".
      left.  drj.
      SSCase "Release".
        apply low_release with y; auto.
        destruct YZ as [SB LOC].  split_1 LOC YA a AZ.
        apply _sw__MemoryEvent__address_domain in YA; auto.
      SSCase "po_loc".
        destruct YZ as [SB LOC].  apply sb_po in SB; auto.  unfold_map.
        choose (hw__po_loc _i (y', z')).  split; auto.  apply loc_map in LOC; auto.
        split_2 LOC Y1' y1' ADDR z1' Z1'; repeat unfold_map; auto.
      SSCase "Write".
        apply low_write_write with z; auto.
  Case "x--Fsb-->y".
    split_1 XY X_F a XY; repeat unfold_iden; rename a into x.
    apply sb_po in XY; auto.
    assert (y --(sw__Event__map _i; rtc (hw__Event__po _i); tr (sw__Event__map _i))--> z) as YZ'.
      destruct YZ as [YZ|YZ].
      SCase "y=z".
        unfold_iden.  assert_conclusion (some_map _i z) Z.
          split_2 XY X' x' XY y' Y'.  apply transpose_pair in Y'.  domain z.
        clean Z z'.  join_2 z' z'.
      SCase "y->z".
        destruct YZ as [YZ _].  apply sb_po in YZ; auto.
        split_2 YZ Y' y' YZ z' Z'.  join_2 y' z'.
    split_2 XY X' x' XY y' Y'.  split_2 YZ' Y2' y2' YZ' z' Z'.
    unfold_map.  join_2 x' z'.
    right.  drj.
    SCase "FenceRels".
      apply low_rel_fence with x; auto.
    SCase "po".
      apply tc_rtc with y'; auto.
    SCase "Write".
      apply low_write_write with z; auto.
Qed.

Lemma rf_map : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__Write__rf _i)--> y
  -> x --(sw__Event__map _i; hw__Write__rf _i; tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE XY.
  assert_conclusion (some_map _i y) Y'.
    assert_conclusion (_sw__Write__rf_range _i (singleton_atom x)) R.
      oneof_auto.
    assert_conclusion (R y) RY.
      apply r1_r2_join12 with x; auto; apply singleton_self.
    subsig.
  destruct Y' as [y' Y'].
  assert_conclusion (low_read_read _i y y') R.  auto_range.
  assert ((exists w', w' --(hw__Write__rf _i)--> y') \/
    ~exists w', w' --(hw__Write__rf _i)--> y') as W by (apply classic).
  destruct W as [W|NO_W].
  Case "w".
    clean W w'.  assert (reverse_map_rf _i) as REV by (destructs COMPILE).
    assert_conclusion W RF.  apply REV in W.  split_2 W W' w WY y2 Y2'.  unfold_map.
    assert_conclusion (one_source_write _i (x, w)) ONE.
      join_1 y.
    unfold_iden.  join_2 w' y'.
  Case "no w".
    assert ((hw__Read _i \ (hw__Write _i ; hw__Write__rf _i)) y') as Y.
      split; auto.  intros CON.  contradict NO_W.  apply join12_r1_r2 in CON.
      destruct CON as [w' CON]; exists w'; destructs CON.
    assert (reverse_map_rf _i) as REV by (destructs COMPILE).
    apply REV in Y.  apply join12_r1_r2 in Y.  destruct Y as [y2 [Y2 Y2']].
    unfold_map.  destruct Y2 as [Y2R Y2W].  contradict Y2W.
    apply r1_r2_join12 with x; auto.  domain x.
Qed.

Lemma rmw_map : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__Read__rmw _i)--> y
  -> x --(sw__Event__map _i; hw__Read__rmw _i; tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE XY.
  assert (compile_rmw _i) as RMW by (destructs COMPILE).
  apply RMW in XY; clear RMW.  split_2 XY X' x' XY y' Y'.  join_2 x' y'.
Qed.

Lemma rmw_A : forall _i x y,
  sw__Read__rmw _i (x, y) ->
  sw__A _i x /\ sw__A _i y.
Proof.
  intros _i x y XY.  apply RMWMO in XY.
  split_2 XY X xo XY yo Y.  destruct XY as [[[[XY|XY]|XY]|XY]|XY];
    apply arrow_each in XY; destruct XY as [XO YO];
    apply r1_r2_join12 with _ (sw__ord _i) _ x in XO; auto;
    apply r1_r2_join12 with _ (sw__ord _i) _ y in YO; auto;
    split; lr.
Qed.

Lemma tc_rtc_one : forall f x y,
  tc f (x, y) ->
  join (rtc f) f (x, y).
Proof.
  intros f x y XY.  apply tc_tc_l in XY.
  rem x y xy.  induction XY as [[x y] XY | [x y] a XA AY IHAY].
  Case "base".
    apply r2_r2_join22 with x; lr.
  Case "ind".
    apply r2_r2_join22 with a; lr.  apply tc_tc_l in XA; lr.
Qed.

Lemma tc_one_rtc : forall f x y,
  tc f (x, y) ->
  join f (rtc f) (x, y).
Proof.
  intros f x y XY.  apply tc_tc_l in XY.
  (* proof by induction *)
  rem x y xy.  induction XY as [[x y] XY | [x y] b XB IHXB BY IHBY].
  Case "base".
    apply r2_r2_join22 with y; lr.
  Case "ind".
    split_1 IHXB XA a AB.  apply r2_r2_join22 with a; lr.
    apply rtc_rtc with b; lr.
Qed.

Lemma some_hw_scope : forall _i x,
  hw__Event _i x
  -> exists s, x --(hw__Event__scope _i)--> s.
Proof.
  intros _i x X.
  assert_conclusion (_hw__Event__scope_range _i (singleton_atom x)) SCOPE.
  apply oneof_exists in SCOPE.  clean SCOPE s.
  exists s; auto.
Qed.

Lemma map_subscope : forall _i s1 s2 s1' s2',
  compile_src11_ptx _i
  -> sw__Scope__subscope _i (s1, s2)
  -> sw__Scope__scopemap _i (s1, s1')
  -> sw__Scope__scopemap _i (s2, s2')
  -> hw__Scope__subscope _i (s1', s2').
Proof.
  intros _i s1 s2 s1' s2' COMPILE S12 S1 S2.
  assert (compile_scope _i) as C by (destructs COMPILE).
  destruct C as [_ [_ C]].  assert_conclusion (C (s1, s2')) C1.
    join_1 s2.
  split_1 C1 C1 s' C2.
  assert (s' = s1'); try unfold_iden; auto.
  assert_conclusion (_sw__Scope__scopemap_range _i (singleton_atom s1)) ONE.
    oneof_auto.
  assert (lone (singleton_atom s1; sw__Scope__scopemap _i)) as L by (destructs ONE).
  apply L; apply r1_r2_join12 with s1; auto; apply singleton_self.
Qed.

Lemma map_rtc_subscope : forall _i s1 s2,
  compile_src11_ptx _i
  -> sw__Scope _i s1
  -> rtc (sw__Scope__subscope _i) (s1, s2)
  -> s1 --(sw__Scope__scopemap _i; rtc (hw__Scope__subscope _i); tr (sw__Scope__scopemap _i))--> s2.
Proof.
  intros _i s1 s2 COMPILE S1 S12.
  destruct S12 as [S12|S12].
    unfold_iden.  assert_conclusion (_sw__Scope__scopemap_range _i (singleton_atom s2)) S2.
    apply oneof_exists in S2.  clean S2 s'.  join_2 s' s'.
  rem s1 s2 ss.  clear S1.  induction S12 as [[s1 s2] S12 | [s1 s2] m SM IHSM MS IHMS].
  Case "base".
    assert_conclusion (_sw__Scope__scopemap_range _i (singleton_atom s1)) S1.
      oneof_auto.
    apply oneof_exists in S1.  clean S1 s1'.
    assert_conclusion (_sw__Scope__scopemap_range _i (singleton_atom s2)) S2.
      oneof_auto.
    apply oneof_exists in S2.  clean S2 s2'.
    assert_conclusion (map_subscope _i s1 s2 s1' s2') SS.
    join_2 s1' s2'.
  Case "ind".
    simpl fst in *; simpl snd in *.
    clear SM MS.
    split_2 IHSM S1 s1' SM m1' M1.  split_2 IHMS M2 m2' MS s2' S2.
    repeat unfold_map.  join_2 s1' s2'.  apply rtc_rtc with m1'; auto.
Qed.

Lemma map_scope : forall _i x s x' s',
  compile_src11_ptx _i
  -> sw__Event__map _i (x, x')
  -> sw__Event__scope _i (x, s)
  -> hw__Event__scope _i (x', s')
  -> sw__Scope__scopemap _i (s, s').
Proof.
  intros _i x s x' s' COMPILE X XS XS'.
  assert (compile_scope _i) as C by (destructs COMPILE).
  destruct C as [_ [C _]].  destruct C with (x, s') as [_ C1].
  assert_conclusion C1 C2.
    join_1 x'.
  split_1 C2 C3 s1 C4.
  assert (s = s1); try unfold_iden; auto.
  assert_conclusion (_sw__Event__scope_range _i (singleton_atom x)) SX.
    oneof_auto.
  assert (lone (singleton_atom x; sw__Event__scope _i)) as L by (destructs SX).
  apply L; apply r1_r2_join12 with x; auto; apply singleton_self.
Qed.

Lemma map_start : forall _i t x t' x',
  compile_src11_ptx _i
  -> sw__Event__map _i (x, x')
  -> sw__Scope__scopemap _i (t, t')
  -> sw__Thread__start _i (t, x)
  -> hw__Thread__start _i (t', x').
Proof.
  intros _i t x t' x' COMPILE X T TX.
  assert (compile_scope _i) as C by (destructs COMPILE).
  destruct C as [C _].  destruct C with (t, x') as [C1 _].
  assert_conclusion C1 C2.
    join_1 x.
  split_1 C2 C3 t1' C4.
  assert (t' = t1'); try unfold_iden; auto.
  assert_conclusion (_sw__Scope__scopemap_range _i (singleton_atom t)) ST.
    oneof_auto.  apply _sw__Scope_subsig_sw__Thread; auto.
  assert (lone (singleton_atom t; sw__Scope__scopemap _i)) as L by (destructs ST).
  apply L; apply r1_r2_join12 with t; auto; apply singleton_self.
Qed.

Lemma sb_map : forall _i x y x' y',
  compile_src11_ptx _i
  -> x --(sw__Event__sb _i)--> y
  -> x --(sw__Event__map _i)--> x'
  -> y --(sw__Event__map _i)--> y'
  -> x' --(tc (hw__Event__po _i))--> y'.
Proof.
  intros _i x y x' y' COMPILE XY X Y.
  assert (inside (sw__Event__map _i; tc (hw__Event__po _i); tr (sw__Event__map _i)) (sw__Event__sb _i))
    as WF by (destructs COMPILE).
  apply WF in XY.  split_2 XY X' x1' XY y1' Y'.  repeat unfold_map.  auto.
Qed.

Lemma rtc_sb_map : forall _i x y x' y',
  compile_src11_ptx _i
  -> x --(rtc (sw__Event__sb _i))--> y
  -> x --(sw__Event__map _i)--> x'
  -> y --(sw__Event__map _i)--> y'
  -> x' --(rtc (hw__Event__po _i))--> y'.
Proof.
  intros _i x y x' y' COMPILE XY X Y.
  destruct XY as [XY|XY].
    unfold_iden; lr.  assert (x' = y'); lr.
    assert_conclusion (_sw__Event__map_range _i (singleton_atom y)) R.
      oneof_auto.
    apply R; apply r1_r2_join12 with y; auto; apply singleton_self.
  assert (util__transitive _i (sw__Event__sb _i)) as SB by (apply strict_partial_sb).
  apply SB in XY.  right.  apply sb_map with x y; auto.
Qed.

Lemma strong_map : forall _i x y x' y',
  compile_src11_ptx _i
  -> x --(sw__strong_r _i)--> y
  -> x --(sw__Event__map _i)--> x'
  -> y --(sw__Event__map _i)--> y'
  -> x' --(hw__strong_r _i)--> y'.
Proof.
  intros _i x y x' y' COMPILE XY X' Y'.
  destruct XY as [XY YX].  split.
  Case "x->y".
    split_3 XY XS s ST t TH h HX.
    assert_conclusion (some_hw_scope _i x') X'S.
      auto_range.
    clean X'S s'.
    assert_conclusion (map_scope _i x s x' s') XS'.
    apply map_rtc_subscope in ST; auto.
    split_2 ST S1' s1' ST t' T.  unfold_map.
    assert_conclusion (some_map _i h) H.
      auto_range.
    clean H h'.
    assert_conclusion (map_start _i t h t' h') HT; auto.
    join_1 h'.  join_1 t'.  join_1 s1'.
    apply rtc_sb_map with h y; auto.
    domain s.
  Case "y->x".
    split_3 YX YS s ST t TH h HY.
    assert_conclusion (some_hw_scope _i y') Y'S.
      auto_range.
    clean Y'S s'.
    assert_conclusion (map_scope _i y s y' s') YS'.
    apply map_rtc_subscope in ST; auto.
    split_2 ST S1' s1' ST t' T.  unfold_map.
    assert_conclusion (some_map _i h) H.
      auto_range.
    clean H h'.
    assert_conclusion (map_start _i t h t' h') HT; auto.
    join_1 h'.  join_1 t'.  join_1 s1'.
    apply rtc_sb_map with h x; auto.
    domain s.
Qed.

Lemma rtc_of_tr : forall f x y,
  x --(rtc (tr f))--> y
  -> y --(rtc f)--> x.
Proof.
  intros f x y XY.  destruct XY as [XY|XY]; lr.  right.
  rem x y xy.  induction XY as [[x y] XY|[x y] m XM IHXM MY IHMY]; lr.
  Case "ind".
    simpl in *.  right with m; auto.
Qed.

Lemma any_scoped_down : forall _i e,
  hw__Event _i e ->
  e --(hw__Event__scope _i; rtc (hw__Scope__subscope _i); hw__Thread__start _i; rtc (hw__Event__po _i))--> e.
Proof.
  intros _i e EVENT.

  assert_conclusion (_hw__Event__scope_range _i (singleton_atom e)) R.
  destruct R as [R_IN [[s R_SOME] R_LONE]].
  assert_conclusion (scope_inclusion _i (e, s)) SS.
    clean R_SOME s; auto.

  clean R_SOME s.
  split_2 SS SA a AB b BS.  join_3 s b a.
  apply rtc_of_tr; auto.  apply rtc_of_tr; auto.
Qed.

Lemma po_same : forall _i x y z,
  hw__Event__po _i (x, y) ->
  hw__Event__po _i (x, z) ->
  y = z.
Proof.
  intros _i x y z XY XZ.
  assert_conclusion (_hw__Event__po_range _i (singleton_atom x)) R.
    oneof_auto.
  apply r2_join12 in XY.  apply r2_join12 in XZ.  apply R; auto.
Qed.

Lemma po_head : forall _i x y z,
  rtc (hw__Event__po _i) (x, y) ->
  rtc (hw__Event__po _i) (x, z) ->
  rtc (hw__Event__po _i) (y, z) \/ rtc (hw__Event__po _i) (z, y).
Proof.
  intros _i x y z XY XZ.
  destruct XY as [XY|XY].
  Case "iden".
    unfold_iden; lr.
  destruct XZ as [XZ|XZ].
  Case "iden".
    unfold_iden; lr.
  apply tc_tc_l in XY.
  rem x y xy.  induction XY as [[x y] XY | [x y] a XA IHXA AY IHAY]; unfold fst, snd in *.
  Case "base".
    apply tc_tc_l in XZ.  rem x z xz.
    assert (tc_l (hw__Event__po _i) xz) as XZ'.
      destruct xz; auto.
    clear XZ; rename XZ' into XZ.  left.
    induction XZ as [[x z] XZ | [x z] a XA IHXA AZ IHAZ]; unfold fst, snd in *.
    SCase "base".  assert_conclusion (po_same _i x y z) R; unfold_iden; lr.
    SCase "ind".
      apply IHXA in XY.  clear IHXA.  apply rtc_rtc with a; lr.
  Case "ind".
    apply IHXA in XZ.  clear IHXA.  destruct XZ as [XZ|XZ].
    SCase "az".
      destruct XZ as [XZ|XZ].
      SSCase "iden".
        unfold_iden.  lr.
      SSCase "tc".
        apply tc_tc_r in XZ.  destruct XZ as [XZ|b XB BZ].
        SSSCase "one".
          assert_conclusion (po_same _i a y z) R; unfold_iden; lr.
        SSSCase "tc".
          assert_conclusion (po_same _i a b y) R; unfold_iden.
          apply tc_tc_r in BZ.  lr.
    SCase "za".
      right.  apply rtc_rtc with a; lr.
Qed.

Lemma po_tail : forall _i x y z,
  rtc (hw__Event__po _i) (x, z) ->
  rtc (hw__Event__po _i) (y, z) ->
  rtc (hw__Event__po _i) (x, y) \/ rtc (hw__Event__po _i) (y, x).
Proof.
  intros _i x y z XZ YZ.
  destruct XZ as [XZ|XZ], YZ as [YZ|YZ]; try repeat unfold_iden; lr.
  assert (hw__Event _i x) as X.
    clear YZ.  rem x z xz.  induction XZ as [[x z] XZ |]; auto.
      apply _hw__Event__po_domain in XZ; auto.
  assert (hw__Event _i y) as Y.
    clear XZ.  rem y z yz.  induction YZ as [[y z] YZ |]; auto.
      apply _hw__Event__po_domain in YZ; auto.
  assert (hw__Event _i z) as Z.
    clear XZ.  rem y z yz.  induction YZ as [[y z] YZ |]; auto.
      do_range _hw__Event__po_range R.
  assert_conclusion (some_thread _i (singleton_atom x)) XT.
  destruct XT as [txr [[XTR XT] XT_UNIQUE]].
  assert_conclusion (some_thread _i (singleton_atom y)) YT.
  destruct YT as [tyr [[YTR YT] YT_UNIQUE]].
  assert_conclusion (some_thread _i (singleton_atom z)) ZT.
  destruct ZT as [tzr [[ZTR ZT] ZT_UNIQUE]].

  assert (equal txr tyr \/ ~equal txr tyr) as XY by (apply classic).
  destruct XY as [XY|XY].
  Case "equal".
    destruct XTR as [_ [[tx XTR] XTRL]].  destruct YTR as [_ [[ty YTR] YTRL]].
    assert (join (hw__Thread__start _i) (rtc (hw__Event__po _i)) (tx, x)) as TX.
      apply inside_arrow with txr (singleton_atom x); auto; try unfold_iden.
    assert (join (hw__Thread__start _i) (rtc (hw__Event__po _i)) (ty, y)) as TY.
      apply inside_arrow with tyr (singleton_atom y); auto; try unfold_iden.
    assert (txr ty) as TXY by (apply XY; auto).
    assert (tx = ty) by (apply XTRL; auto).
    unfold_iden.  rename ty into t.
    split_join_hyp TX hx THX TX.  split_join_hyp TY hy THY TY.
    assert (hx = hy) as H.
      apply r2_join12 in THX.  apply r2_join12 in THY.
      assert_conclusion (_hw__Thread__start_range _i (singleton_atom t)) R.
        oneof_auto.  apply join12_r2 in THX.  domain t.
      destruct R as [_ [_ L]].  apply L; auto.
    unfold_iden.  rename hy into h.
    apply po_head with h; auto.
  Case "not equal".
    destruct XTR as [XTH [[tx XTR] XTRL]].  destruct YTR as [YTH [[ty YTR] YTRL]].
    assert (join (hw__Thread__start _i) (rtc (hw__Event__po _i)) (tx, x)) as TX.
      apply inside_arrow with txr (singleton_atom x); auto; try unfold_iden.
    assert (join (hw__Thread__start _i) (rtc (hw__Event__po _i)) (ty, y)) as TY.
      apply inside_arrow with tyr (singleton_atom y); auto; try unfold_iden.

    assert_conclusion (ZT_UNIQUE txr) TXZ.
      split; auto.
      SCase "thread".
        repeat split; auto.  exists tx; auto.
      SCase "start.*po".
        intros [a b] AB.  split_join_hyp TX hx THX HX.
        apply arrow_each in AB.  destruct AB as [A B].
        assert (tx = a) by (apply XTRL; auto).  repeat unfold_iden.
        apply r2_r2_join22 with hx; auto.  apply rtc_rtc with x; lr.
    unfold_iden.

    assert_conclusion (ZT_UNIQUE tyr) TYZ.
      split; auto.
      SCase "thread".
        repeat split; auto.  exists ty; auto.
      SCase "start.*po".
        intros [a b] AB.  split_join_hyp TY hy THY HY.
        apply arrow_each in AB.  destruct AB as [A B].
        assert (ty = a) by (apply YTRL; auto).  repeat unfold_iden.
        apply r2_r2_join22 with hy; auto.  apply rtc_rtc with y; lr.
    unfold_iden.

    destruct XY.  split; auto.
Qed.

Lemma singleton_atom_eq : forall x y,
  singleton_atom x = singleton_atom y ->
  x = y.
Proof.
  intros x y XY.
  apply NNPP; intros C.
  apply singleton_atoms_neq in C.  destruct C.  rewrite XY.  split; auto.
Qed.

Lemma start_tr_po : forall _i t y,
  t --(hw__Thread__start _i)--> y
  -> ~exists x, x --(hw__Event__po _i)--> y.
Proof.
  intros _i ty y TY CON.
  clean CON x.  assert_conclusion (some_thread _i (singleton_atom x)) TXR.
    apply oneof_singleton_atom.  domain x.
  destruct TXR as [txr [TX UNIQUE]].  destruct TX as [TX_ONEOF TX_IN].
  destruct TX_ONEOF as [TXR [[tx TX_SOME] TX_LONE]].
  assert (tx --(hw__Thread__start _i; rtc (hw__Event__po _i))--> x) as TX.
    apply TX_IN.  apply arrow_112; auto.  apply singleton_self.

  assert (tx = ty).
    assert_conclusion (some_thread _i (singleton_atom y)) TYR.
      oneof_auto.
    destruct TYR as [tyr [TY2 TY_UNIQUE]].  destruct TY2 as [TY_ONEOF TY_IN].
    destruct TY_ONEOF as [TYR [[ty2 TY_SOME] TY_LONE]].
    assert_conclusion (TY_UNIQUE (singleton_atom tx)) TYU.
      split; auto.
      apply inside_arrow_2; auto.  split_1 TX TS s SX.
      join_1 s.  apply rtc_rtc with x; lr.
    repeat unfold_iden.
    assert_conclusion (TY_UNIQUE (singleton_atom ty)) TYU.
      split; auto.
        apply oneof_singleton_atom.  domain ty.
        apply inside_arrow_2; auto.  join_1 y.
    apply singleton_atom_eq in TYU; auto.
  unfold_iden.  rename ty into t.

  split_1 TX TS s SX.  assert (s = y) as SY.
    assert_conclusion (_hw__Thread__start_range _i (singleton_atom t)) R.
    apply R; apply r2_join12; auto.
  unfold_iden.

  contradiction (po_acyclic _i).  cycle_with x.  apply tc_rtc with y; lr.
Qed.

Lemma po_strong : forall _i x y,
  x --(tc (hw__Event__po _i))--> y
  -> hw__strong_r _i (x, y).
Proof.
  intros _i x y XY.  split.
  Case "->".
    assert_conclusion (any_scoped_down _i x) X.
      apply tc_one_rtc in XY.  split_1 XY XM m MY.  domain x.
    split_3 X XS s ST t TF f FX.  join_3 s t f.  apply rtc_rtc with x; lr.
  Case "<-".
    assert_conclusion (any_scoped_down _i y) Y.
      apply tc_rtc_one in XY.  split_1 XY XM m MY.  auto_range.
    split_3 Y YS s ST t TF f FXY.  join_3 s t f.
    assert_conclusion (po_tail _i f x y) PO; lr.
    destruct PO as [PO|PO]; lr.
    destruct PO as [PO|PO]; lr.
    apply tc_rtc_one in PO.  split_1 PO XA a AF.
    apply start_tr_po in TF.  contradiction TF.  exists a; auto.
Qed.

Lemma rf_map_obs : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__strong _i (sw__Write__rf _i))--> y
  -> x --(sw__Event__map _i; hw__MemoryEvent__observation _i; tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE XY.
  destruct XY as [XY STRONG].
  apply rf_map in XY; auto.  split_2 XY X' x' XY y' Y'.
  apply strong_map with _i x y x' y' in STRONG; auto.
  join_2 x' y'.  apply rf_obs.  split; auto.
Qed.

Lemma rf_rmw_obs : forall _i x y,
  compile_src11_ptx _i
  -> sw__A _i x
  -> x --(tc (sw__strong _i (sw__Write__rf _i); sw__Read__rmw _i))--> y
  -> x --(sw__Event__map _i; hw__MemoryEvent__observation _i; hw__Read__rmw _i; tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE X XY.
  rem x y xy.  induction XY as [[x y] XY | [x y] c XC IHXC CY IHCY].
  Case "x --(rf.rmw)--> y".
    split_1 XY XA a AY.  assert_conclusion (rmw_A _i a y) A.  destruct A as [A_A Y_A].
    destruct XA as [XA STRONG].
    apply rf_map in XA; auto.  split_2 XA X' x' XA a1' A1'.
    apply rmw_map in AY; auto.  split_2 AY A2' a2' AY y' Y'.
    unfold_map.  join_3 x' a1' y'.
    apply rf_obs.  split; auto.  apply strong_map with x a; auto.
  Case "x --^(rf.rmw).^(rf.rmw)--> y".
    assert (sw__A _i c) as C_A.
      apply tc_rtc_one in XC.  split_1 XC XA a AC.  split_1 AC AB b BC.
      apply rmw_A in BC.  destructs BC.
    clear XC CY.
    apply IHXC in X.  split_2 X X' x' XC c1' C1'.
    apply IHCY in C_A.  split_2 C_A C2' c2' CY y' Y'.
    split_1 X' X' x1' X1'.
    split_1 C2' C' c' C2'.
    unfold fst, snd in *.  unfold_map.
    join_3 x1' c2' y'.  apply rmw_obs.  join_2 x' c1'.
Qed.

Lemma rf_obs_map : forall _i x y,
  compile_src11_ptx _i
  -> sw__A _i x
  -> x --(sw__strong _i (sw__Write__rf _i))--> y
  -> sw__A _i y
  -> x --(sw__Event__map _i; hw__MemoryEvent__observation _i; tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE X XY Y.
  destruct XY as [XY STRONG].
  apply rf_map in XY; auto.  split_2 XY X' x' XY y' Y'.
  join_2 x' y'.  apply rf_obs.  split; auto.
  apply strong_map with x y; auto.
Qed.

Lemma low_acq_fence : forall _i x x',
  compile_src11_ptx _i
  -> ((sw__ACQ _i U sw__AR _i) U sw__SC _i) x
  -> sw__Fence _i x
  -> sw__Event__map _i (x, x')
  -> hw__FenceAcqs _i x'.
Proof.
  intros _i x x1' COMPILE X_MO X_F X1'.
  destruct X_MO as [[X_MO|X_MO]|X_MO].
  Case "ACQ".
    assert (compile_fence_aq _i) as C by (destructs COMPILE).
    choose (hw__FenceAcq _i x1').  apply C.
    apply r1_r2_join12 with x; auto.  split; auto.
  Case "AR".
    assert (compile_fence_ar _i) as C by (destructs COMPILE).
    choose (hw__FenceAcqRel _i x1').  apply C.
    apply r1_r2_join12 with x; auto.  split; auto.
  Case "SC".
    assert (compile_fence_sc _i) as C by (destructs COMPILE).
    choose (hw__FenceAcqRel _i x1').
    apply _hw__FenceAcqRel_subsig_hw__FenceSC.
    apply C.
    apply r1_r2_join12 with x; auto.  split; auto.
Qed.

Lemma low_acquire : forall _i x x',
  compile_src11_ptx _i
  -> ((sw__ACQ _i U sw__AR _i) U sw__SC _i) x
  -> x --(sw__Event__map _i)--> x'
  -> sw__MemoryEvent _i x
  -> hw__Acquire _i x'.
Proof.
  intros _i x x' COMPILE X XM X'.
  assert (sw__Event _i x) as XE by (domain x).
  apply _sw__Event_abstract in XE.  destruct XE as [XE|XE].
  apply _sw__MemoryEvent_abstract in XE.  destruct XE as [XE|XE].
  Case "Write".
    assert_conclusion (WriteMO _i (singleton_atom x)) MO.
    destruct X as [[X|X]|X].
    SCase "ACQ".
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
    SCase "AR".
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
    SCase "SC".
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
  Case "Read".
    assert_conclusion (ReadMO _i (singleton_atom x)) MO.
    destruct X as [[X|X]|X].
    SCase "ACQ".
      assert (compile_read_aq _i) as C by (destructs COMPILE).
      apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    SCase "AR".
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
    SCase "SC".
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
  Case "Fence".
    contradiction_types.
Qed.

Lemma sbf_map : forall _i x y,
  compile_src11_ptx _i
  -> util__optional _i (sw__Event__sb _i; util__ident _i (sw__Fence _i)) (x, y)
  -> ((sw__ACQ _i) U (sw__AR _i) U (sw__SC _i)) y
  -> sw__Read _i x
  -> x --((sw__Event__map _i; hw__suffix _i; tr (sw__Event__map _i)))--> y.
Proof.
  intros _i x y COMPILE XY Y XR.
  destruct XY as [XY|XY].
  Case "x=y".
    unfold_iden.
    assert (sw__Event _i y) as Y_E by (
      destruct Y as [[Y|Y]|Y]; apply join12_r1_r2 in Y;
      destruct Y as [o [O YO]]; apply transpose_pair in YO; domain y).
    apply some_map in Y_E; auto.  clean Y_E y'.  join_2 y' y'.
    left.  drj.
    SCase "Read".
      apply low_read_read with y; auto.
    SCase "po_loc".
      unfold_iden.
    SCase "Acquire".
      apply low_acquire with y; auto.  subsig.
  Case "x--Fsb-->y".
    split_1 XY XY a Y_F; repeat unfold_iden.
    apply sb_po in XY; auto.  split_2 XY X' x' XY y' Y'.  join_2 x' y'.
    right.  drj.
    SCase "Read".
      apply low_read_read with x; auto.
    SCase "FenceAcqs".
      apply low_acq_fence with y; auto.
Qed.

Lemma rs_range_A : forall _i x y,
     intersect (sw__Write _i) (sw__A _i) x
  -> rtc (sw__strong _i (sw__Write__rf _i); sw__Read__rmw _i) (x, y)
  -> sw__A _i y.
Proof.
  intros _i x y X XY.
  destruct XY as [XY|XY].
  Case "x=y".
    unfold_iden; destructs X.
  Case "x->y".
    apply tc_rtc_one in XY.  split_1 XY XA a AY.  split_1 AY AB b BY.
    apply rmw_A in BY; destructs BY.
Qed.

Lemma last_last : forall _i (f g : Relation 2) x y z,
  compile_src11_ptx _i
  -> x --(sw__Event__map _i; f; tr (sw__Event__map _i))--> y
  -> y --(sw__Event__map _i; g; tr (sw__Event__map _i))--> z
  -> x --(sw__Event__map _i; (f; g); tr (sw__Event__map _i))--> z.
Proof.
  intros _i f g x y z COMPILE XY YZ.
  split_2 XY X' x' XY y' Y'.  split_2 YZ Y1' y1' YZ z' Z'.  unfold_map.
  join_2 x' z'.  join_1 y'.
Qed.

Ltac merge_lasts :=
match goal with
  [ COMPILE : compile_src11_ptx ?i,
    XY : ?x --(sw__Event__map ?i; ?f; tr (sw__Event__map ?i))--> ?y,
    YZ : ?y --(sw__Event__map ?i; ?g; tr (sw__Event__map ?i))--> ?z |- _ ] =>
  assert (x --(sw__Event__map i; (f; g); tr (sw__Event__map i))--> z) as _XYZ by (apply last_last with y; auto);
  clear XY YZ; rename _XYZ into XY
  | [ COMPILE : compile_src11_ptx ?i,
    XY : ?x --(sw__Event__map ?i; ?f; transpose (sw__Event__map ?i))--> ?y,
    YZ : ?y --(sw__Event__map ?i; ?g; transpose (sw__Event__map ?i))--> ?z |- _ ] =>
  assert (x --(sw__Event__map i; (f; g); tr (sw__Event__map i))--> z) as _XYZ by (apply last_last with y; auto);
  clear XY YZ; rename _XYZ into XY
  | [ COMPILE : compile_src11_ptx ?i,
    XY : ?x --(sw__Event__map ?i; ?f; transpose (sw__Event__map ?i))--> ?y,
    YZ : ?y --(sw__Event__map ?i; ?g; tr (sw__Event__map ?i))--> ?z |- _ ] =>
  assert (x --(sw__Event__map i; (f; g); tr (sw__Event__map i))--> z) as _XYZ by (apply last_last with y; auto);
  clear XY YZ; rename _XYZ into XY
  | [ COMPILE : compile_src11_ptx ?i,
    XY : ?x --(sw__Event__map ?i; ?f; tr (sw__Event__map ?i))--> ?y,
    YZ : ?y --(sw__Event__map ?i; ?g; transpose (sw__Event__map ?i))--> ?z |- _ ] =>
  assert (x --(sw__Event__map i; (f; g); tr (sw__Event__map i))--> z) as _XYZ by (apply last_last with y; auto);
  clear XY YZ; rename _XYZ into XY
end.

Lemma low_releaser : forall _i x x',
  compile_src11_ptx _i
  -> ((sw__REL _i U sw__AR _i) U sw__SC _i) x
  -> x --(sw__Event__map _i)--> x'
  -> hw__Releasers _i x'.
Proof.
  intros _i x x1' COMPILE X X'.
  assert (sw__A _i x) as X_A by (auto_cases X).
  assert (sw__Event _i x) as X_E by (destructs X_A).
  apply _sw__Event_abstract in X_E.  destruct X_E as [X_E|X_E].
  apply _sw__MemoryEvent_abstract in X_E.  destruct X_E as [X_E|X_E].
  Case "Write".
    destruct X as [[X|X]|X].
    SCase "REL".
      assert (compile_write_rl _i) as C by (destructs COMPILE).
      choose (hw__Release _i x1').
      apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    SCase "AR".
      assert_conclusion (WriteMO _i (singleton_atom x)) MO.
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
    SCase "SC".
      assert_conclusion (WriteMO _i (singleton_atom x)) MO.
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
  Case "Read".
    assert_conclusion (ReadMO _i (singleton_atom x)) MO.
    destruct X as [[X|X]|X].
    SCase "ACQ".
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
    SCase "AR".
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
    SCase "SC".
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
  Case "Fence".
    destruct X as [[X|X]|X].
    SCase "REL".
      assert (compile_fence_rl _i) as C by (destructs COMPILE).
      choose (hw__FenceRel _i x1').
      apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    SCase "AR".
      assert (compile_fence_ar _i) as C by (destructs COMPILE).
      choose (hw__FenceAcqRel _i x1').
      apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    SCase "SC".
      assert (compile_fence_sc _i) as C by (destructs COMPILE).
      choose (hw__FenceAcqRel _i x1').
      apply _hw__FenceAcqRel_subsig_hw__FenceSC.
      apply C.  apply r1_r2_join12 with x; auto.  split; auto.
Qed.

Lemma low_acquirer : forall _i x x',
  compile_src11_ptx _i
  -> ((sw__ACQ _i U sw__AR _i) U sw__SC _i) x
  -> x --(sw__Event__map _i)--> x'
  -> hw__Acquirers _i x'.
Proof.
  intros _i x x1' COMPILE X X'.
  assert (sw__A _i x) as X_A by (auto_cases X).
  assert (sw__Event _i x) as X_E by (destructs X_A).
  apply _sw__Event_abstract in X_E.  destruct X_E as [X_E|X_E].
  apply _sw__MemoryEvent_abstract in X_E.  destruct X_E as [X_E|X_E].
  Case "Write".
    destruct X as [[X|X]|X].
    SCase "REL".
      assert_conclusion (WriteMO _i (singleton_atom x)) MO.
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
    SCase "AR".
      assert_conclusion (WriteMO _i (singleton_atom x)) MO.
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
    SCase "SC".
      assert_conclusion (WriteMO _i (singleton_atom x)) MO.
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
  Case "Read".
    assert_conclusion (ReadMO _i (singleton_atom x)) MO.
    destruct X as [[X|X]|X].
    SCase "ACQ".
      assert (compile_read_aq _i) as C by (destructs COMPILE).
      choose (hw__Acquire _i x1').
      apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    SCase "AR".
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
    SCase "SC".
      apply join12_r1_r2 in X.  clean X o.  destruct X as [AR XO].
      apply transpose_pair, r2_join12, MO in XO.
      destruct XO as [[XO|XO]|XO]; contradiction_types.
  Case "Fence".
    destruct X as [[X|X]|X].
    SCase "ACQ".
      assert (compile_fence_aq _i) as C by (destructs COMPILE).
      choose (hw__FenceAcq _i x1').
      apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    SCase "AR".
      assert (compile_fence_ar _i) as C by (destructs COMPILE).
      choose (hw__FenceAcqRel _i x1').
      apply C.  apply r1_r2_join12 with x; auto.  split; auto.
    SCase "SC".
      assert (compile_fence_sc _i) as C by (destructs COMPILE).
      choose (hw__FenceAcqRel _i x1').
      apply _hw__FenceAcqRel_subsig_hw__FenceSC.
      apply C.  apply r1_r2_join12 with x; auto.  split; auto.
Qed.

Lemma rf_rmw_rf_obs : forall _i e f h,
  compile_src11_ptx _i ->
  intersect (sw__Write _i) (sw__A _i) e ->
  rtc (sw__strong _i (sw__Write__rf _i); sw__Read__rmw _i) (e, f) ->
  sw__strong _i (sw__Write__rf _i) (f, h) ->
  intersect (sw__Read _i) (sw__A _i) h ->
  e --(sw__Event__map _i; hw__MemoryEvent__observation _i; tr (sw__Event__map _i))--> h.
Proof.
  intros _i e f h E COMPILE EF FH H.
  destruct EF as [EF|EF].
  Case "base".
    unfold_iden.  apply rf_map_obs in FH; auto.
  Case "ind".
    apply rf_rmw_obs in EF; auto; try (destructs COMPILE).
    apply rf_map_obs in FH; auto.
    split_2 EF E' e' EF f' F'.  split_2 FH F2' f2' FH h' H'.
    unfold_map.  split_1 E' E' e1' E1'.  join_2 e1' h'.
    apply rmw_obs.  join_2 e' f'.
Qed.

Lemma sw_syncacqrel : sw_syncacqrel_statement.
Proof.
  intros _i COMPILE [x y] XY.
  destruct XY as [XY STRONG].
  split_6 XY XA a AB b BF f FG g GH h HI i IY.  repeat unfold_iden.

  split_3 BF BC c CD d DE e EF.  repeat unfold_iden.

  assert (sw__A _i f) as F_A by (apply rs_range_A with e; auto).
  assert (sw__Write _i e) as E_W by (destructs DE).

  assert_conclusion (fsb_sbloc_prefix _i a c e) AE.
  apply rf_rmw_rf_obs with _i e f h in EF; auto.
  apply sbf_map in HI; auto.

  repeat merge_lasts.

  split_2 AE A' a' AY y' Y'.  join_2 a' y'.  join_2 a' y'.  drj.
  Case "Releaser".  apply low_releaser with a; auto.
  Case "strong[prefix.^observation.suffix]".
    split.
    SCase "prefix.^observation.suffix".
      split_1 AY AB' b' BY.  split_1 BY BC' c' CY.
      join_2 b' c'.
    SCase "strong".
      apply strong_map with a y; auto.
        auto_cases XA.
        auto_cases IY.
  Case "Acquirer".
    apply low_acquirer with y; auto.
  Case "Read".
    destructs GH.
Qed.

Lemma hb_syncacqrel : forall _i,
  compile_src11_ptx _i
  -> inside ((sw__Event__map _i; (tc (hw__Event__po _i) U tc (syncacqrel _i)));
       transpose (sw__Event__map _i)) (sw__hb _i).
Proof.
  intros _i COMPILE [x y] XY.
  rem x y xy.  induction XY as [[x y] [XY|XY] | [x y] m XM IHXM MY IHMY].
  Case "sb".
    apply sb_po in XY; auto.  split_2 XY X' x' XY y' Y'.  join_2 x' y'.
  Case "sw".
    apply sw_syncacqrel in XY; auto.  split_2 XY X' x' XY y' Y'.  join_2 x' y'.
  Case "tc".
    merge_lasts.  split_2 IHXM X' x' XY y' Y'.  join_2 x' y'.
Qed.

(******************************************************************************)

Lemma not_difference {n} : forall f g h x,
  ~difference (n:=n) (difference (n:=n) f g) h x -> ~f x \/ g x \/ h x.
Proof.
  intros f g h x DIFF.  apply NNPP; intros FGH.  destruct DIFF.
  split.
    split.
      apply NNPP; intros F; destruct FGH; lr.
      intros G; destruct FGH; lr.
    intros H; destruct FGH; lr.
Qed.

Lemma not_some_difference {n} : forall f g,
  ~some (difference (n:=n) f g) -> inside g f.
Proof.
  intros f g DIFF x F.  apply NNPP; intros G.  destruct DIFF.
  exists x.  split; auto.
Qed.

(******************************************************************************)

Lemma loc_transitive : forall _i x y z,
  sw__loc _i (x, y) ->
  sw__loc _i (y, z) ->
  sw__loc _i (x, z).
Proof.
  intros _i x y z XY YZ.
  split_1 XY XA a AY.  split_1 YZ YB b BZ.
  assert_conclusion (_sw__MemoryEvent__address_range _i (singleton_atom y)) R.
    oneof_auto.
  destruct R as [INSIDE [SOME LONE]].
  apply transpose_pair, r2_join12 in AY.  apply r2_join12 in YB.
  apply (LONE b) in AY; auto.  unfold_iden.
  apply r2_r2_join22 with a; auto.
Qed.

Lemma com_eco : forall _i x y,
  union (sw__Write__rf _i) (union (sw__Write__mo _i) (sw__rb _i)) (x, y) ->
  sw__eco _i (x, y).
Proof.
  intros _i x y COM.  repeat destruct COM as [COM|COM]; lr.
Qed.

Lemma eco_loc : forall _i x y,
  sw__eco _i (x, y) ->
  sw__loc _i (x, y).
Proof.
  intros _i x y ECO.  induction ECO as [[x' y'] ECO|[x' y'] m' IHH1 IHH2].
  Case "com".
    apply (com_loc _i); lr.
  Case "tc".
    apply loc_transitive with m'; auto.
Qed.

Lemma loc_symmetric : forall _i x y,
  x --(sw__loc _i)--> y
  -> y --(sw__loc _i)--> x.
Proof.
  intros _i x y XY.  split_1 XY XA a YA.  join_1 a.
Qed.

Lemma addr_tr_addr_symmetric : forall _i x' y',
  join (hw__MemoryEvent__address _i) (transpose (hw__MemoryEvent__address _i)) (x', y') ->
  join (hw__MemoryEvent__address _i) (transpose (hw__MemoryEvent__address _i)) (y', x').
Proof.
  intros _i x' y' XY.  split_1 XY XA a AY.
  apply r2_r2_join22 with a; lr.
Qed.

Lemma addr_tr_addr_transitive : forall _i x y z,
  join (hw__MemoryEvent__address _i) (transpose (hw__MemoryEvent__address _i)) (x, y) ->
  join (hw__MemoryEvent__address _i) (transpose (hw__MemoryEvent__address _i)) (y, z) ->
  join (hw__MemoryEvent__address _i) (transpose (hw__MemoryEvent__address _i)) (x, z).
Proof.
  intros _i x y z XY YZ.
  split_1 XY XA a AY.  split_1 YZ YB b BZ.
  assert_conclusion (_hw__MemoryEvent__address_range _i (singleton_atom y)) R.
    oneof_auto.
  apply transpose_pair, r2_join12 in AY.  apply r2_join12 in YB.
  destruct R as [INSIDE [SOME LONE]].
  apply (LONE b) in AY; auto.  unfold_iden.
  Case "address".
    apply r2_r2_join22 with a; auto.
Qed.

Lemma tc_com_addr : forall _i x y,
  compile_src11_ptx _i ->
  tc (hw__com _i) (x, y) ->
  join (hw__MemoryEvent__address _i) (transpose (hw__MemoryEvent__address _i)) (x, y).
Proof.
  intros _i x y COMPILE XY.
  rem x y xy.  induction XY as [[x y] XY | [x y] a XA IHXA AY IHAY].
  Case "Base".
    assert_conclusion (com_addr _i) ADDR.
    destruct XY as [[XY|XY]|XY]; try solve [apply ADDR; lr].
    SCase "tc (hw__Write__co _i)".
      rem x y xy.  induction XY as [[x y] XY | [x y] a XA IHXA AY IHAY].
      SSCase "base".
        apply ADDR; lr.
      SSCase "ind".
        unfold fst, snd in *.  apply addr_tr_addr_transitive with a; lr.
  Case "ind".
    apply addr_tr_addr_transitive with a; lr.
Qed.

(******************************************************************************)

Lemma mo_cycle : forall _i x,
  sw__Write__mo _i (x, x) -> False.
Proof.
  intros _i x XX.
  assert_conclusion (strict_partial_mo _i) MO.
  assert (util__irreflexive _i (sw__Write__mo _i)) as MO2 by (destructs MO).
  contradiction MO2.  exists (x, x); split; try unfold_iden; auto.
Qed.

Lemma mo_transitive : forall _i x y,
  tc (sw__Write__mo _i) (x, y) ->
  sw__Write__mo _i (x, y).
Proof.
  intros _i x y XY.
  assert_conclusion (strict_partial_mo _i) MO.
  assert (util__transitive _i (sw__Write__mo _i)) as T by (destructs MO).
  apply T; auto.
Qed.

Lemma com_com : forall _i x y z,
  x --(sw__com _i)--> y
  -> y --(sw__com _i)--> z
  -> x --(sw__com _i; util__optional _i (sw__Write__rf _i))--> z.
Proof.
  intros _i x y z XY YZ.
  destruct XY as [[XY|XY]|XY]; destruct YZ as [[YZ|YZ]|YZ];
  try solve [join_1 y];
  try solve [
    try assert (sw__Read _i y) as Y1 by (domain y);
    try assert (sw__Read _i y) as Y1 by (auto_range);
    try assert (sw__Write _i y) as Y2 by (domain y);
    try assert (sw__Write _i y) as Y2 by (auto_range);
    contradiction_types].
  Case "rf;rb".
    destruct YZ as [YZ|YZ_INIT].
    SCase "non-init".
      split_1 YZ YM m MZ.
      assert_conclusion (one_source_write _i (x, m)) XM.
        join_1 y.
      unfold_iden.  join_1 z; unfold_iden.
    SCase "init".
      drs YZ_INIT Y Z.  destruct Y as [Y INIT].  contradiction INIT.
      apply r1_r2_join12 with x; auto.  domain x.
  Case "mo;mo".
    join_1 z; repeat unfold_iden.  choose (sw__Write__mo _i (x, z)).
    apply mo_transitive.  right with y; lr.
  Case "rb;mo".
    destruct XY as [XY|XY_INIT].
    SCase "non-init".
      split_1 XY XM m MY.  join_1 z; repeat unfold_iden.
      choose (sw__rb _i (x, z)).  left.  join_1 m.
      apply mo_transitive; right with y; lr.
    SCase "init".
      drs XY_INIT X Y.  join_1 z; repeat unfold_iden.
      choose (sw__rb _i (x, z)).  right.  drj.
      SSCase "x --loc--> z".
        apply loc_transitive with y; auto.
        apply eco_loc; lr.
      SSCase "z Write".
        auto_range.
  Case "rb;rb".
    assert_conclusion (fr_domain _i y z) YR.
    assert_conclusion (fr_range _i x y) YW.
    contradiction_types.
Qed.

Lemma opt_rf_opt_rf : forall _i x y z,
  x --(util__optional _i (sw__Write__rf _i))--> y
  -> y --(util__optional _i (sw__Write__rf _i))--> z
  -> x --(util__optional _i (sw__Write__rf _i))--> z.
Proof.
  intros _i x y z XY YZ.
  destruct XY as [XY|XY]; destruct YZ as [YZ|YZ]; repeat unfold_iden; lr.
  Case "rf;rf".
    assert (sw__Write _i y) as Y1 by (domain y).
    assert (sw__Read _i y) as Y2 by (auto_range).
    contradiction_types.
Qed.

Lemma ecos_equal : ecos_equal_statement.
Proof.
  intros _i [x y].  split; intros XY.
  Case "->".
    apply tc_tc_r in XY.  rem x y xy.
    induction XY as [[x y] XY | [x y] m XM MY IH].
    SCase "base".
      join_1 y; unfold_iden.
    SCase "ind".
      clear MY.  split_1 IH MN n NY.  simpl fst in *; simpl snd in *.
      assert_conclusion (com_com _i x m n) XN.  clear XM MN m.
      split_1 XN XM m MN.  join_1 m.  apply opt_rf_opt_rf with n; auto.
  Case "<-".
    split_1 XY XM m MY.  apply tc_rtc with m; lr.
    destruct MY; lr.
Qed.

Lemma eco_cycle : forall _i x,
  ~sw__eco _i (x, x).
Proof.
  intros _i x ECO.
  apply ecos_equal in ECO.  split_1 ECO XY y YX.
  destruct YX as [YX|YX].
  Case "com".
    unfold_iden.  destruct XY as [[RF|MO]|RB].
    SCase "rf".
      assert (sw__Write _i x) as W by (apply _sw__Write__rf_domain in RF; auto).
      assert (sw__Read _i x) as R by (do_range _sw__Write__rf_range R).
      contradiction_types.
    SCase "mo".
      apply mo_cycle in MO; auto.
    SCase "rb".
      assert (sw__Read _i x) as W by (apply fr_domain in RB; auto).
      assert (sw__Write _i x) as R by (apply fr_range in RB; auto).
      contradiction_types.
  Case "tc".
    destruct XY as [[RF|MO]|RB].
    SCase "rf".
      assert (sw__Write _i x) as W by (apply _sw__Write__rf_domain in RF; auto).
      assert (sw__Read _i x) as R by (auto_range).
      contradiction_types.
    SCase "mo".
      assert (sw__Write _i x) as W by (apply _sw__Write__mo_domain in MO; auto).
      assert (sw__Read _i x) as R by (auto_range).
      contradiction_types.
    SCase "rb".
      destruct RB as [RB|RB].
      SSCase "non-init".
        split_join_hyp RB a XA AY.
        assert (iden (a, y)) as YA by (apply (one_source_write _i); apply r2_r2_join22 with x; lr).
        unfold_iden.  apply mo_cycle with _i y; auto.
      SSCase "init".
        unfold_domain RB XY X.  unfold_range XY XY Y.  destruct X as [X RF].
        destruct RF.  apply r1_r2_join12 with y; lr.
Qed.

Lemma com_domain : forall _i x y,
  sw__com _i (x, y)
  -> sw__Event _i x.
Proof.
  intros _i x y XY.  destruct XY as [[XY|XY]|XY]; domain x.
Qed.

Lemma com_range : forall _i x y,
  sw__com _i (x, y)
  -> sw__Event _i y.
Proof.
  intros _i x y XY.  destruct XY as [[XY|XY]|XY].
    apply _sw__Event_subsig_sw__MemoryEvent, _sw__MemoryEvent_subsig_sw__Read; auto_range.
    apply _sw__Event_subsig_sw__MemoryEvent, _sw__MemoryEvent_subsig_sw__Write; auto_range.
    apply _sw__Event_subsig_sw__MemoryEvent, _sw__MemoryEvent_subsig_sw__Write; apply fr_range with x; auto.
Qed.

Lemma com_strong_hb_or_hb : forall _i (x y : Atom),
  compile_src11_ptx _i
  -> x --(sw__com _i)--> y
  -> x --(sw__hb _i)--> y
  \/ y --(sw__hb _i)--> x
  \/ x --(sw__Event__map _i ; hw__strong_r _i ; tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE X_COM_Y.

  assert (~sw__racy _i) as RACE_FREE by (destructs COMPILE).

  assert (x --(sw__strong_r _i)--> y \/ ~x --(sw__strong_r _i)--> y) as STRONG by (apply classic).

  destruct STRONG as [STRONG | WEAK].

  Case "STRONG".
    assert_conclusion (some_map _i x) X'.  apply com_domain with y; auto.  clean X' x'.
    assert_conclusion (some_map _i y) Y'.  apply com_range with x; auto.  clean Y' y'.
    choose ((sw__Event__map _i; hw__strong_r _i; tr (sw__Event__map _i)) (x, y)).
    join_2 x' y'.  apply strong_map with x y; auto.

  Case "WEAK".
    (* x->y is not a race *)
    assert (~sw__race _i (x, y)) as NO_RACE.
      (* any race is inside A->A *)
      apply not_some_difference in RACE_FREE.
      (* by assumption for this part, x->y is not in A->A *)
      intros CONTRADICTION_HYPOTHESIS.  apply RACE_FREE in CONTRADICTION_HYPOTHESIS.
      contradiction.
    (* if neither hb nor ~hb, then (x, y) must not be a conflict *)
    apply not_difference in NO_RACE.  auto_cases NO_RACE.
    (* but (x, y) must be a conflict because it's in com *)
    contradict NO_RACE.  repeat split.
    SCase "same address".  apply com_loc; auto.
    SCase "not the same".
      intros CONTRADICTION_HYPOTHESIS.  unfold_iden.
      contradiction (eco_cycle _i y).  apply com_eco; auto_cases X_COM_Y.
    SCase "not Read->Read".
      intros CONTRADICTION_HYPOTHESIS.  apply arrow_each in CONTRADICTION_HYPOTHESIS.
      destruct CONTRADICTION_HYPOTHESIS as [X_R Y_R].
      destruct X_COM_Y as [[H|H]|H]; try blast_dr x; try blast_dr y.
        apply fr_range in H.  contradiction_types.
Qed.

Lemma scoped_down_two : forall _i xs ys s,
  xs --(rtc (hw__Scope__subscope _i))--> s
  -> ys --(rtc (hw__Scope__subscope _i))--> s
  -> xs --(rtc (hw__Scope__subscope _i))--> ys \/ ys --(rtc (hw__Scope__subscope _i))--> xs.
Proof.
  intros _i xs ys s XS YS.

  destruct XS as [XS|XS].
    unfold_iden; lr.
  destruct YS as [YS|YS].
    unfold_iden; lr.
  rem xs s x.  induction XS as [[x1 x2] XS|].
    simpl fst in *.  simpl snd in *.
    apply tc_rtc_one in YS.  split_1 YS YM m MS.
    assert (m = x1); try unfold_iden; lr.
      assert_conclusion (inv_subscope _i (x1, m)) XM.  join_1 x2.
  simpl fst in *; simpl snd in *.
  apply IHXS2 in YS.  destruct YS as [YS|YS].
    left.  apply rtc_rtc with y; lr.
  destruct YS as [YS|YS].
    unfold_iden; lr.
  apply IHXS1 in YS.  auto.
Qed.

Lemma strong_scope_down : forall _i x y xs ys,
  x --(hw__strong_r _i)--> y
  -> x --(hw__Event__scope _i)--> xs
  -> y --(hw__Event__scope _i)--> ys
  -> xs --(rtc (hw__Scope__subscope _i))--> ys \/ ys --(rtc (hw__Scope__subscope _i))--> xs.
Proof.
  intros _i x y xs1 ys1 STRONG XS1 YS1.
  destruct STRONG as [XY YX].  split_3 XY XS xs XSYT yt YTH yh YH.
  apply transpose_pair in YX.  split_3 YX YS ys YSXT xt XTH xh XH.

  assert (xs1 = xs); repeat unfold_iden.
    assert_conclusion (_hw__Event__scope_range _i (singleton_atom x)) R.
      oneof_auto.
    apply R; apply r2_join12; auto.
  assert (ys1 = ys); repeat unfold_iden.
    assert_conclusion (_hw__Event__scope_range _i (singleton_atom y)) R.
      oneof_auto.
    apply R; apply r2_join12; auto.
  clear XS1 YS1.

  assert (rtc (hw__Scope__subscope _i) (ys, yt)) as YST.
    assert_conclusion (scope_inclusion _i (y, ys)) Y.
    split_2 Y YT1 yh1 YTH1 yt1 YH1.
    assert (yt = yt1).
      assert_conclusion (some_thread _i (singleton_atom y)) Y.
        apply oneof_singleton_atom.  domain y.
      destruct Y as [tr [Y UNIQUE]].
      assert_conclusion (UNIQUE (singleton_atom yt)) U1.
        split.
          apply oneof_singleton_atom.  domain yt.
        apply inside_arrow_2.  join_1 yh.
      unfold_iden.
      assert_conclusion (UNIQUE (singleton_atom yt1)) U1.
        split.
          apply oneof_singleton_atom.  apply transpose_pair in YTH1.  domain yt1.
        apply inside_arrow_2.  join_1 yh1.  apply rtc_of_tr; auto.
      apply singleton_atom_eq in U1; auto.
    unfold_iden; auto.  apply rtc_of_tr; auto.

  apply scoped_down_two with yt; auto.
Qed.

Lemma rtc_tr : forall f x y,
  x --(rtc f)--> y
  -> y --(rtc (tr f))--> x.
Proof.
  intros f x y XY.  destruct XY as [XY|XY]; lr.  right.
  rem x y xy.  induction XY as [[x y] XY|[x y] m XM IHXM MY IHMY]; lr.
  Case "ind".
    simpl in *.  right with m; auto.
Qed.

Lemma scoped_down_up : forall _i x y,
  x --(rtc (hw__Scope__subscope _i))--> y
  -> y --(rtc (tr (hw__Scope__subscope _i)))--> x.
Proof.
  intros _i x y XY.  apply rtc_tr; auto.
Qed.

Lemma strong_scope : forall _i x y a,
  hw__Write _i x
  -> hw__Write _i y
  -> x --(hw__strong_r _i)--> y
  -> x --(hw__MemoryEvent__address _i)--> a
  -> y --(hw__MemoryEvent__address _i)--> a
  -> exists s, oneof (hw__Scope _i) s
  /\ (intersect (intersect (hw__scoped _i s) (hw__inside _i s))
       (intersect (singleton_atom a; transpose (hw__MemoryEvent__address _i))
         (hw__Write _i))) x
  /\ (intersect (intersect (hw__scoped _i s) (hw__inside _i s))
       (intersect (singleton_atom a; transpose (hw__MemoryEvent__address _i))
         (hw__Write _i))) y.
Proof.
  intros _i x y a X Y XY XA YA.
  assert_conclusion XY STRONG.
  destruct XY as [XY YX].  split_3 XY XS xs XST xt XTH xh XHY.
  apply transpose_pair in YX.  split_3 YX YS ys YST yt YTH yh YHX.
  assert (xs --(rtc (hw__Scope__subscope _i))--> ys \/ ys --(rtc (hw__Scope__subscope _i))--> xs)
    as S by (apply strong_scope_down with x y; auto).
  destruct S as [S|S].
  Case "xs->ys".
    assert_conclusion (scope_inclusion _i (y, ys)) YSI.
    exists (singleton_atom ys).  split; auto.
      apply oneof_singleton_atom.  auto_range.
    repeat split; auto.
    SCase "scoped[ys] x".
      apply r1_r2_join12 with xs; auto.  apply scoped_down_up in S.
      apply r1_r2_join12 with ys; auto; unfold_iden.
    SCase "inside[ys] x".
      apply r1_r2_join12 with yh; auto.  apply r1_r2_join12 with yt; auto.
      apply r1_r2_join12 with ys; auto.  unfold_iden.
    SCase "x->a".  apply r2_join12; auto.
    SCase "scoped[ys] y".
      apply r1_r2_join12 with ys; auto.  apply r1_r2_join12 with ys; try unfold_iden; lr.
    SCase "inside[ys] y".
      clear - YSI.  split_2 YSI ST t TH h HY.  apply r1_r2_join12 with t; auto.
      apply r1_r2_join12 with h; auto.  apply r1_r2_join12 with ys; auto.
      apply singleton_self.  apply rtc_of_tr; auto.  apply rtc_of_tr; auto.
    SCase "y->a".  apply r2_join12; auto.
  Case "ys->xs".
    assert_conclusion (scope_inclusion _i (x, xs)) XSI.
    exists (singleton_atom xs).  split; auto.
      apply oneof_singleton_atom.  auto_range.
    repeat split; auto.
    SCase "scoped[xs] x".
      apply r1_r2_join12 with xs; auto.  apply r1_r2_join12 with xs; try unfold_iden; lr.
    SCase "inside[xs] x".
      clear - XSI.  split_2 XSI ST t TH h HX.  apply r1_r2_join12 with t; auto.
      apply r1_r2_join12 with h; auto.  apply r1_r2_join12 with xs; auto.
      apply singleton_self.  apply rtc_of_tr; auto.  apply rtc_of_tr; auto.
    SCase "x->a".  apply r2_join12; auto.
    SCase "scoped[xs] y".
      apply r1_r2_join12 with ys; auto.  apply scoped_down_up in S.
      apply r1_r2_join12 with xs; auto; unfold_iden.
    SCase "inside[xs] y".
      apply r1_r2_join12 with xh; auto.  apply r1_r2_join12 with xt; auto.
      apply r1_r2_join12 with xs; auto.  unfold_iden.
    SCase "y->a".  apply r2_join12; auto.
Qed.

Lemma co_left_or_right : forall _i x' y',
  hw__Write _i x'
  -> hw__Write _i y'
  -> x' --(hw__strong_r _i)--> y'
  -> x' --(hw__MemoryEvent__address _i; tr (hw__MemoryEvent__address _i))--> y'
  -> x' = y' \/ tc (hw__Write__co _i) (x', y') \/ tc (hw__Write__co _i) (y', x').
Proof.
  intros _i x' y' X' Y' STRONG ADDR.
  split_1 ADDR XA a YA.  apply transpose_pair in YA.
  assert_conclusion (strong_scope _i x' y' a) SCOPE.
  destruct SCOPE as [s SCOPE].

  assert_conclusion (co_per_scope _i (singleton_atom a)) CO.
    oneof_auto.
  destruct STRONG as [XS YS].

  assert_conclusion (CO s) CO2.
    destructs SCOPE.
  destruct CO2 as [CO2 _].
  assert_conclusion (CO2 (singleton_atom x')) CO3.
    apply oneof_singleton_atom.  repeat split; auto.
    Case "scoped".  destructs SCOPE.
    Case "inside".  destructs SCOPE.
    Case "address".
      apply r1_r2_join12 with a; auto.  apply singleton_self.
  assert (x' = y' \/ x' <> y') as XY by (apply classic).  auto_cases XY.
  clear CO CO2.

  assert_conclusion (CO3 (singleton_atom y')) CO4.
    apply oneof_singleton_atom.  repeat split; auto.
    Case "scoped".  destructs SCOPE.
    Case "inside".  destructs SCOPE.
    Case "address".
      apply r1_r2_join12 with a; auto.  apply singleton_self.
      intros CONTRA.  apply singleton_atom_eq in CONTRA.  contradiction XY; auto.

  assert_conclusion (CO4 (x', y')) CO5.
    left; apply arrow_112; unfold_iden.
  destruct CO5 as [CO5|CO5]; lr.  apply tc_transpose in CO5; lr.
Qed.

Lemma strong_symmetric : forall _i x y,
  hw__strong_r _i (x, y)
  -> hw__strong_r _i (y, x).
Proof.
  intros _i x y [XY YX].  split; lr.
Qed.

Lemma co_po : forall _i x y,
  compile_src11_ptx _i
  -> hw__Write _i x
  -> hw__Write _i y
  -> x --(tc (hw__Event__po _i))--> y
  -> x --(hw__MemoryEvent__address _i; tr (hw__MemoryEvent__address _i))--> y
  -> x --(tc (hw__Write__co _i))--> y.
Proof.
  intros _i x y COMPILE X Y XY ADDR.
  assert_conclusion (co_left_or_right _i x y) CO.
  Case "strong".
    apply po_strong; auto.
  destruct CO as [CO|[CO|CO]].
  Case "x=y".
    unfold_iden.  contradiction (po_acyclic _i).  exists (y, y).  split; auto; unfold_iden.
  Case "x->y".
    auto.
  Case "y->x".
    assert (hw__location_sc _i) as SC_PER_LOC by (destructs COMPILE).
    destruct SC_PER_LOC.  exists (x, x).  split; try unfold_iden.
    right with y.
    SCase "x->y".
      choose (hw__po_loc _i (x, y)).  split; auto.
    SCase "y->x".
      choose (hw__strong _i (hw__com _i) (y, x)).
      split; lr.
      apply strong_symmetric, po_strong; auto.
Qed.

Lemma hb_co : forall _i x y,
  compile_src11_ptx _i
  -> sw__Write _i x
  -> sw__Write _i y
  -> x --(sw__loc _i)--> y
  -> x --(sw__hb _i)--> y
  -> x --(sw__Event__map _i; tc (hw__Write__co _i); tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE X Y LOC HB.

  apply hb_syncacqrel in HB; auto.  split_2 HB X' x' XY y' Y'.
  destruct XY as [XY|XY].
  Case "po".
    join_2 x' y'.  apply co_po; auto.
      apply low_write_write with x; auto.
      apply low_write_write with y; auto.
      apply loc_map in LOC; auto.  unfold_map.
  Case "sync".
    join_2 x' y'.
    assert (hw__coherence _i) as COHERENCE by (destructs COMPILE).
    apply COHERENCE.  split; try drj.
      apply low_write_write with x; auto.
      left.  apply tc_syncacqrel_cause_base; auto.
      apply low_write_write with y; auto.
      apply loc_map in LOC; auto.  unfold_map.
Qed.

Lemma reverse_map_tc_co : forall _i,
  compile_src11_ptx _i
  -> inside (tr (sw__Event__map _i); sw__Write__mo _i; sw__Event__map _i) (tc (hw__Write__co _i)).
Proof.
  intros _i COMPILE [x' y'] X'Y'.
  rem x' y' x'y'.  induction X'Y' as [[x' y'] X'Y' | [x' y'] a' X'A' IHX'A' A'Y' IHA'Y'].
  Case "base".
    assert (reverse_map_co _i) as REV by (destructs COMPILE).
    assert (hw__Write _i x') as X_W by (domain x').
    assert (hw__Write _i y') as Y_W by (auto_range).
    apply REV in X'Y'.  split_2 X'Y' X' x XY y Y'.  join_2 x y.
  Case "ind".
    split_2 IHX'A' X x XA1 a1 A1.  split_2 IHA'Y' A2 a2 A2Y y Y.
    unfold_map.  join_2 x y.
    assert_conclusion (strict_partial_mo _i) MO.  apply MO.
    right with a1; lr.
Qed.

Lemma optional_transpose : forall _i f x y,
  util__optional _i f (x, y)
  -> util__optional _i (tr f) (y, x).  
Proof.
  intros _i f x y XY.  destruct XY; lr.  repeat unfold_iden.
Qed.

Lemma optional_two_compare : forall _i f x y z,
  x --(util__optional _i f)--> z
  -> y --(util__optional _i f)--> z
  -> (f (x, z) -> one (singleton_atom z; tr f))
  -> (y = z /\ x --(f)--> y) \/ (x = z /\ y --(f)--> x) \/ x = y.
Proof.
  intros _i f x y z XY YZ ONE.
  destruct XY as [XY|XY]; destruct YZ as [YZ|YZ]; repeat unfold_iden; lr.
    choose (x = y).  apply ONE; auto; apply r2_join12; auto.
Qed.

Lemma scope_inside : forall _i x s,
  x --(hw__Event__scope _i)--> s
  -> hw__inside _i (singleton_atom s) x.
Proof.
  intros _i x s XS.  apply scope_inclusion in XS.
  split_2 XS XH h HT t TX.
  apply r1_r2_join12 with h.  apply r1_r2_join12 with t; auto.
  apply r1_r2_join12 with s.
    apply singleton_self.
    apply rtc_of_tr; auto.
    apply rtc_of_tr; auto.
Qed.

Lemma mo_map : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__Write__mo _i)--> y
  -> x --(sw__Event__map _i; tc (hw__Write__co _i); tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE XY.
  assert_conclusion (some_map _i x) X.  domain x.  clean X x'.
  assert_conclusion (low_write_write _i x x') X'.  domain x.
  assert_conclusion (some_map _i y) Y.
    apply _sw__Event_subsig_sw__MemoryEvent, _sw__MemoryEvent_subsig_sw__Write.  auto_range.
  clean Y y'.
  assert_conclusion (low_write_write _i y y') Y'.  auto_range.
  join_2 x' y'.

  assert_conclusion (com_strong_hb_or_hb _i x y) XY'; lr.
  destruct XY' as [HB|[HB|STRONG]].
  Case "hb".
    apply hb_co in HB; auto.
    SCase "main".  unfold_map; auto.
    SCase "x".  domain x.
    SCase "y".  auto_range.
    SCase "loc".  apply eco_loc, com_eco; lr.
  Case "~hb".
    apply hb_co in HB; auto.
    SCase "main".
      unfold_map.  apply reverse_map_tc_co in HB; auto.
      split_2 HB Y2' y2' YX x2' X2'; repeat unfold_map.
      assert_conclusion (strict_partial_mo _i) MO.
      assert (util__irreflexive _i (sw__Write__mo _i)) as MO_IRR by (destructs MO).
      assert (util__transitive _i (sw__Write__mo _i)) as MO_TR by (destructs MO).
      contradiction MO_IRR.  cycle_with x.
      apply MO_TR.  right with y; lr.
    SCase "y".  auto_range.
    SCase "x".  domain x.
    SCase "loc".  apply loc_symmetric, eco_loc, com_eco; lr.
  Case "strong".
    assert_conclusion (co_left_or_right _i x' y') CO.
      unfold_map.
      assert (sw__eco _i (x, y)) as ECO by lr.
      apply eco_loc, loc_map in ECO; auto.  unfold_map.
    destruct CO as [CO|[CO|CO]]; lr.
    SCase "x' = y'".
      unfold_iden.  unfold_map.  contradiction (mo_cycle _i x).
    SCase "y'->x'".
      apply reverse_map_tc_co in CO; auto.  split_2 CO Y1 y1 YX x1 X1; repeat unfold_map.
      contradiction (mo_cycle _i x).  apply mo_transitive; right with y; lr.
Qed.

Lemma fr_map : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__rb _i)--> y
  -> x --(sw__Event__map _i; hw__fr _i; tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE XY.
  destruct XY as [XY|XY].
  Case "~rf.mo".
    split_1 XY XA a AY.
    apply transpose_pair, rf_map in XA; auto.  split_2 XA A' a' AX x' X'.
    apply mo_map in AY; auto.  split_2 AY A1' a1' AY y' Y'.  repeat unfold_map.
    join_2 x' y'.  choose ((tr (hw__Write__rf _i); tc (hw__Write__co _i)) (x', y')).
    join_1 a'.
  Case "no ~rf".
    drs XY X Y.  assert_conclusion (some_map _i x) X'.
      destruct X; subsig.
    assert_conclusion (some_map _i y) Y'.
      subsig.
    clean X' x'.  clean Y' y'.  join_2 x' y'.
    right.  drj.
    SCase "domain".
      split.
      SSCase "read".
        apply low_read_read with x; auto.  destruct X; domain x.
      SSCase "no ~rf".
        intros CON.  apply join12_r1_r2 in CON.  destruct CON as [w' [W WX]].
        destruct X as [X CON].  contradiction CON.
        assert (reverse_map_rf _i) as REV by (destructs COMPILE).
        apply REV in WX; auto.  split_2 WX W' w WX x1 X1.  repeat unfold_map.
        apply r1_r2_join12 with w; auto.  domain w.
    SCase "addr".
      apply loc_map in XY; auto.  unfold_map.
    SCase "range".
      apply low_write_write with y; auto.
Qed.

Lemma com_map : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__com _i)--> y
  -> x --(sw__Event__map _i; hw__com _i; tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE XY.
  destruct XY as [[RF|MO]|FR].
    apply rf_map in RF; auto.  split_2 RF X' x' XY y' Y'.  join_2 x' y'.
    apply mo_map in MO; auto.  split_2 MO X' x' XY y' Y'.  join_2 x' y'.
    apply fr_map in FR; auto.  split_2 FR X' x' XY y' Y'.  join_2 x' y'.
Qed.

Lemma one_exists : forall (f : Relation 1),
  one f
  -> exists x, f x.
Proof.
  intros f F.  destruct F as [[x SOME] LONE].  exists x; auto.
Qed.

Lemma co_acyclic : forall _i x,
  compile_src11_ptx _i
  -> tc (hw__Write__co _i) (x, x)
  -> False.
Proof.
  intros _i x COMPILE X.
  assert_conclusion (_hw__MemoryEvent__address_range _i (singleton_atom x)) X_A.
    oneof_auto.
  apply oneof_exists in X_A.  clean X_A a.
  assert_conclusion (co_per_scope _i (singleton_atom a)) CO.  auto_range.
    oneof_auto.
  assert_conclusion (_hw__Event__scope_range _i (singleton_atom x)) X_S.
    oneof_auto.
  apply oneof_exists in X_S.  clean X_S s.
  assert_conclusion (CO (singleton_atom s)) CO_TOTAL.
    oneof_auto.
  assert (util__acyclic _i (hw__Write__co _i)) as CO_ACYCLIC by (destructs CO_TOTAL).
  contradiction CO_ACYCLIC.  cycle_with x.
Qed.

Lemma acyclic_com_syncacqrel : forall _i x y,
  compile_src11_ptx _i
  -> x --(hw__com _i)--> y
  -> y --(hw__cause _i)--> x
  -> False.
Proof.
  intros _i x y COMPILE XY YX.
  assert (hw__causality _i) as CAUSALITY by (destructs COMPILE).
  destruct XY as [[RF|CO]|FR].
  Case "rf".
    contradiction CAUSALITY.  cycle_with x.  join_1 y.
  Case "^co".
    assert (hw__coherence _i) as COHERENCE by (destructs COMPILE).
    assert_conclusion (COHERENCE (y, x)) YX2.  split; try drj.
      SCase "y".  apply tc_co_range with x; auto.
      SCase "x".  domain x.
      SCase "addr".  apply addr_tr_addr_symmetric, tc_com_addr; lr.
    apply co_acyclic with _i x; auto.  right with y; auto.
  Case "fr".
    contradiction CAUSALITY.  cycle_with x.  join_1 y.
Qed.

Lemma acyclic_com_po_cause_base : forall _i x y,
  compile_src11_ptx _i
  -> x --(hw__com _i)--> y
  -> y --(tc (hw__Event__po _i) U (hw__cause_base _i))--> x
  -> False.
Proof.
  intros _i x y COMPILE XY YX.
  assert (hw__location_sc _i) as SC_PER_LOC by (destructs COMPILE).
  assert (hw__cause _i (y, x)) as CAUSE.
    destruct YX as [YX|YX]; lr.
    Case "po".
      destruct SC_PER_LOC.  exists (x, x).  split; try unfold_iden.
      right with y; lr.
      SCase "xy".
        left.  left.  split; auto.  apply strong_symmetric, po_strong; auto.
      SCase "yx".
        left.  right.  split; auto.
        apply addr_tr_addr_symmetric, tc_com_addr; lr.
  apply acyclic_com_syncacqrel with _i x y; auto.
Qed.

Lemma acyclic_com_po_syncacqrel : forall _i x y,
  compile_src11_ptx _i
  -> x --(hw__com _i)--> y
  -> y --(tc (hw__Event__po _i) U (tc (syncacqrel _i)))--> x
  -> False.
Proof.
  intros _i x y COMPILE XY YX.
  apply acyclic_com_po_cause_base with _i x y; auto.
  auto_cases YX.  choose (hw__cause_base _i (y, x)).
  apply tc_syncacqrel_cause_base; auto.
Qed.

Lemma acyclic_po_syncacqrel : forall _i x,
  compile_src11_ptx _i
  -> x --(tc (hw__Event__po _i) U (tc (syncacqrel _i)))--> x
  -> False.
Proof.
  intros _i x COMPILE XX.
  destruct XX as [PO|syncacqrel].
  Case "po".
    assert_conclusion (po_acyclic _i) WF.  contradiction WF.
    cycle_with x.
  Case "syncacqrel".
    assert (hw__causality _i) as CAUSALITY by (destructs COMPILE).
    contradiction CAUSALITY.  cycle_with x.  join_1 x; try unfold_iden.
    apply tc_syncacqrel_cause_base in syncacqrel; lr.
Qed.

Lemma com_strong_or_hb : forall _i (x y : Atom),
  compile_src11_ptx _i
  -> x --(sw__com _i)--> y
  -> x --(sw__hb _i)--> y
  \/ x --(sw__Event__map _i ; hw__strong_r _i ; tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE X_COM_Y.

  assert_conclusion (com_strong_hb_or_hb _i x y) YX.  auto_cases YX.

  apply hb_syncacqrel in YX; auto.  apply com_map in X_COM_Y; auto.
  split_2 X_COM_Y X' x' XY y' Y'.  split_2 YX Y1' y1' YX x1' X1'.
  repeat unfold_map.  clear X' Y'.

  assert_conclusion (acyclic_com_po_syncacqrel _i x' y') CONTRA.  contradiction CONTRA.
Qed.

Lemma rf_map_obs_or_syncacqrel : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__Write__rf _i)--> y
  -> x --(sw__Event__map _i;
      (hw__MemoryEvent__observation _i U hw__po_loc _i U hw__cause_base _i);
      tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE XY.
  assert_conclusion (com_strong_or_hb _i x y) XY2; lr.
  destruct XY2 as [HB|STRONG].
  Case "hb".
    apply hb_syncacqrel in HB; auto.  split_2 HB X' x' XY' y' Y'.  join_2 x' y'.
    destruct XY' as [PO|SYNC].
    SCase "po".
      choose (x' --(hw__po_loc _i)--> y').  split; auto.
      apply com_addr.  apply rf_map in XY; auto; unfold_map; lr.
    SCase "syncacqrel".
      choose (x' --(hw__cause_base _i)--> y').
      apply tc_syncacqrel_cause_base; auto.
  Case "strong".
    split_2 STRONG X' x' XY' y' Y'.  join_2 x' y'.
    choose (x' --(hw__MemoryEvent__observation _i)--> y').
    apply rf_map in XY; auto; unfold_map; lr.  apply rf_obs; split; auto.
Qed.

Lemma obs_addr : forall _i x' y',
  hw__MemoryEvent__observation _i (x', y')
  -> (hw__MemoryEvent__address _i; transpose (hw__MemoryEvent__address _i)) (x', y').
Proof.
  intros _i x' y' XY.
  apply obs_in_rf_rmw in XY.  rem x' y' xy.
  induction XY as [[x y] XY |[x y] a XA IHXA AY IHAY].
  Case "Base".
    destruct XY as [XY|XY].
    SCase "rf".
      apply com_addr.  destruct XY; lr.
    SCase "rmw".
      apply rmw_facts; auto.
  Case "ind".
    apply addr_tr_addr_transitive with a; auto.
Qed.

Lemma cause_base_po : forall _i x y z,
  compile_src11_ptx _i
  -> x --(hw__cause_base _i)--> y
  -> y --(tc (hw__Event__po _i))--> z
  -> x --(hw__cause_base _i)--> z.
Proof.
  intros _i a e f COMPILE AE EF.
  apply tc_rtc_one in AE.  split_1 AE AB b BE.  split_2 BE BC c CD d DE.
  apply rtc_tc with b; lr.  left.  join_2 c d.  right.  apply rtc_tc with e; auto.
Qed.

Lemma rf_hb : forall _i x y z,
  compile_src11_ptx _i
  -> x --(sw__Write__rf _i)--> y
  -> y --(sw__hb _i)--> z
  -> x --(sw__loc _i)--> z
  -> x --(sw__Event__map _i; (hw__po_loc _i U hw__cause _i); tr (sw__Event__map _i))--> z.
Proof.
  intros _i x y z COMPILE XY YZ LOC.
  apply rf_map_obs_or_syncacqrel in XY; auto.  apply hb_syncacqrel in YZ; auto.
  merge_lasts.  split_2 XY X' x' XZ z' Z'.  join_2 x' z'.
  split_1 XZ XY y' YZ.
  assert (hw__MemoryEvent__observation _i (x', y') \/ (hw__po_loc _i U hw__cause_base _i) (x', y'))
    as XY2 by (destruct XY as [[XY|XY]|XY]; lr).
  destruct XY2 as [OBS|XY2].
  Case "obs".
    destruct YZ as [YZ|YZ].
    SCase "po".
      right.  right.  join_1 y'.
      choose (y' --(hw__po_loc _i)--> z').  split; auto.
      apply addr_tr_addr_transitive with x'.
        apply addr_tr_addr_symmetric, obs_addr; auto.
        apply loc_map in LOC; auto; unfold_map; auto.
    SCase "syncacqrel".
      right.  right.  join_1 y'.
      choose (y' --(hw__cause_base _i)--> z').
      apply tc_syncacqrel_cause_base; auto.
  Case "po_loc or cause_base".
    clear XY.  destruct XY2 as [XY|XY]; destruct YZ as [YZ|YZ].
    SCase "po_loc;po".
      choose (x' --(hw__po_loc _i)--> z').
      split.
        right with y'; destructs XY.
        apply loc_map in LOC; auto; unfold_map.
    SCase "po_loc;syncacqrel".
      right.  apply tc_syncacqrel_syncacqrel, tc_po_syncacqrel with y'; auto.  destructs XY.
    SCase "cause_base;po".
      choose (x' --(hw__cause_base _i)--> z').
      apply cause_base_po with y'; auto.
    SCase "cause_base;syncacqrel".
      choose (x' --(hw__cause_base _i)--> z').
      right with y'; auto.  apply tc_syncacqrel_cause_base; auto.
Qed.

Lemma acyclic_hb_com : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__hb _i)--> y
  -> y --(sw__com _i)--> x
  -> False.
Proof.
  intros _i x y COMPILE XY YX.
  apply hb_syncacqrel in XY; auto.  split_2 XY X' x' XY y' Y'.
  apply com_map in YX; auto.  split_2 YX Y1' y1' YX x1' X1'.
  repeat unfold_map.  destruct XY as [XY|XY].
  Case "po".
    assert (x' --(hw__po_loc _i)--> y') as POLOC.
      split; auto.  apply addr_tr_addr_symmetric, tc_com_addr; lr.
    contradiction (acyclic_com_po_syncacqrel _i y' x').
    choose (tc (hw__Event__po _i) (x', y')).
    destructs POLOC.
  Case "syncacqrel".
    apply acyclic_com_syncacqrel with _i y' x'; auto.
    apply tc_syncacqrel_syncacqrel; auto.
Qed.

Lemma acyclic_hb : forall _i x,
  compile_src11_ptx _i
  -> x --(sw__hb _i)--> x
  -> False.
Proof.
  intros _i x COMPILE XX.
  apply hb_syncacqrel in XX; auto.  split_2 XX X' x' XX x1' X1'.
  unfold_map.  apply acyclic_po_syncacqrel in XX; auto.
Qed.

Lemma acyclic_com_po : forall _i x y,
  compile_src11_ptx _i
  -> x --(tc (hw__Event__po _i))--> y
  -> y --(hw__com _i)--> x
  -> False.
Proof.
  intros _i x y COMPILE XY YX.
  assert (hw__location_sc _i) as SC_PER_LOC by (destructs COMPILE).
  destruct SC_PER_LOC.  exists (x, x).  split; try unfold_iden.
  right with y.
  Case "x->y".
    choose (hw__po_loc _i (x, y)).  split; auto.
    apply addr_tr_addr_symmetric, tc_com_addr; lr.
  Case "y->x".
    choose (hw__strong _i (hw__com _i) (y, x)).
    split; lr.  apply strong_symmetric, po_strong; auto.
Qed.

Theorem src11_ptx_legal_coherence : src11_ptx_legal_coherence_statement.
Proof.
  intros _i COMPILE [[x1 x] [IDEN XX]]; unfold_iden.
  split_1 XX XY y YX.

  (* x --hb--> y --eco?--> x *)
  destruct YX as [NO_ECO|ECO].
  Case "no eco".
    unfold_iden.  apply acyclic_hb in XY; auto.
  Case "eco".
    apply ecos_equal in ECO.  split_1 ECO YZ z ZX.
    destruct ZX as [ZX|ZX].
    SCase "z=x".
      unfold_iden.  apply acyclic_hb_com with _i x y; auto.
    SCase "z --rf--> x".
      assert_conclusion (rf_hb _i z x y) RF.
        apply loc_symmetric, eco_loc; lr.
      split_2 RF Z' z' ZY y' Y'.
      apply com_map in YZ; auto.  split_2 YZ Y1' y1' YX x1' X1'.
      repeat unfold_map.
      destruct ZY as [ZY|ZY].
      SSCase "po_loc".
        apply acyclic_com_po with _i x1' y1'; auto.  destructs ZY.
      SSCase "cause".
        apply acyclic_com_syncacqrel with _i y1' x1'; auto.
Qed.

(******************************************************************************)

Lemma fr_co_fr : forall _i x y z,
  compile_src11_ptx _i
  -> x --(hw__fr _i)--> y
  -> y --(tc (hw__Write__co _i))--> z
  -> x --(hw__fr _i)--> z.
Proof.
  intros _i x y z COMPILE XY YZ.
  destruct XY as [XY|XY].
  Case "~rf.^co".
    split_1 XY XM m MY.
    choose (x --(tr (hw__Write__rf _i); tc (hw__Write__co _i))--> z).
    join_1 m.  right with y; auto.
  Case "no ~rf".
    right.  drs XY X Y.  drj.
      apply addr_tr_addr_transitive with y; auto.  apply tc_com_addr; lr.
      apply tc_co_range with y; auto.
Qed.

Lemma fr_co_fr_co : forall _i x z,
  compile_src11_ptx _i
  -> x --(hw__fr _i; tc (hw__Write__co _i))--> z
  -> x --(hw__fr _i; hw__Write__co _i)--> z.
Proof.
  intros _i x z COMPILE XZ.
  split_1 XZ XY y YZ.
  apply tc_rtc_one in YZ.  split_1 YZ YM m MZ.  join_1 m.
  destruct YM as [YM|YM].
  Case "y=m".
    unfold_iden; auto.
  Case "y->m".
    apply fr_co_fr with y; auto.
Qed.

Lemma sw_range : forall _i x y,
     x --(sw__sw _i)--> y
  -> sw__Read _i y \/ sw__Fence _i y.
Proof.
  intros _i x y XY.
  split_1 XY XA a AY.  repeat unfold_iden.  clear XA.
  assert (sw__Event _i y) as Y by (
    destruct AY as [[AY|AY]|AY];
      apply join12_r1_r2 in AY; destruct AY as [o [O AY]]; domain y).
  apply _sw__Event_abstract in Y.  auto_cases Y.
  apply _sw__MemoryEvent_abstract in Y.  auto_cases Y.

  Case "Write".
    assert_conclusion (WriteMO _i (singleton_atom y)) Y_MO.
    destruct AY as [[AY|AY]|AY];
      apply join12_r1_r2 in AY; destruct AY as [o [O AY]];
      apply transpose_pair, r2_join12, Y_MO in AY;
      destruct AY as [[AY|AY]|AY]; contradiction_types.
Qed.

Lemma hb_write : forall _i x y,
     x --(sw__hb _i)--> y
  -> sw__Write _i y
  -> x --(util__optional _i (sw__hb _i); sw__Event__sb _i)--> y.
Proof.
  intros _i x y XY Y.
  apply tc_rtc_one in XY.  split_1 XY XM m MY.
  join_1 m.
  Case "x->m".
    destruct XM; lr.
  Case "m->y".
    auto_cases MY.  destruct MY as [MY STRONG].
    apply sw_range in MY; destruct MY; blast_types.
Qed.

Lemma sb_rmw : forall _i x y a,
     x --(sw__Read__rmw _i)--> y
  -> a --(sw__Event__sb _i)--> y
  -> a --(util__optional _i (sw__Event__sb _i))--> x.
Proof.
  intros _i x y a XY AY.
  assert_conclusion (rmw_sbimm _i) RMW.
  assert (inside (sw__Event__sb _i)
    (sw__Event__sb _i; transpose (sw__Read__rmw _i))) as RMW2 by (destructs RMW).
  assert_conclusion (RMW2 (a, x)) AX.
    join_1 y.
  lr.
Qed.

Lemma rmw_strong_head : forall _i x y a,
  compile_src11_ptx _i
  -> x --(hw__Read__rmw _i)--> y
  -> a --(hw__strong_r _i)--> x
  -> a --(hw__strong_r _i)--> y.
Proof.
  intros _i x y a COMPILE XY AX.
  split.
  Case "a->y".
    destruct AX as [AX _].  split_1 AX AB b BY.  join_1 b.
    apply rtc_rtc with x; lr.  choose (hw__Event__po _i (x, y)).
    apply rmw_facts in XY.  destructs XY.
  Case "y->a".
    apply untranspose_pair.  destruct AX as [_ AX].  apply transpose_pair in AX.
    split_3 AX AB b BC c CD d DY.  join_3 b c d.
    assert (x --(hw__Event__scope _i; tr (hw__Event__scope _i))--> y) as XY_SCOPE
      by (apply rmw_facts in XY; destructs XY).
    split_1 XY_SCOPE XS s YS.  apply transpose_pair in YS.
    assert (s = b); [|solve [unfold_iden; auto]].
    assert_conclusion (_hw__Event__scope_range _i (singleton_atom x)) X.
      oneof_auto.
    apply X; apply r2_join12; auto.
Qed.

Lemma lone_inv_po : forall _i x y z,
  x --(hw__Event__po _i)--> y
  -> z --(hw__Event__po _i)--> y
  -> x = z.
Proof.
  intros _i x y z XY YZ.
  assert_conclusion (po_tail _i x z y) PO; lr.
  destruct PO as [[PO|PO]|[PO|PO]]; lr.
  Case "XZ".
    assert (rtc (hw__Event__po _i) (y, z)) as CYCLE.
      apply tc_tc_r in PO.  destruct PO as [PO | y' PO1 PO2].
      SCase "one".
        assert_conclusion (_hw__Event__po_range _i (singleton_atom x)) R.
          oneof_auto.
        destruct R as [_ R].  apply r2_join12 in XY.  apply r2_join12 in PO.
        assert (y = z) by (apply R; auto); unfold_iden; lr.
      SCase "more".
        unfold fst, snd in *.
        assert_conclusion (_hw__Event__po_range _i (singleton_atom x)) R.
          oneof_auto.
        destruct R as [_ R].  apply r2_join12 in XY.  apply r2_join12 in PO1.
        assert (y = y') by (apply R; auto); unfold_iden.  apply tc_tc_r in PO2.  lr.
    contradiction (po_acyclic _i).  exists (z, z).  split; try unfold_iden.
    destruct CYCLE as [CYCLE|CYCLE]; try unfold_iden; lr.
    right with y; lr.
  Case "ZX".
    assert (rtc (hw__Event__po _i) (y, x)) as CYCLE.
      apply tc_tc_r in PO.  destruct PO as [PO | y' PO1 PO2].
      SCase "one".
        assert_conclusion (_hw__Event__po_range _i (singleton_atom z)) R.
          oneof_auto.
        destruct R as [_ R].  apply r2_join12 in YZ.  apply r2_join12 in PO.
        assert (x = y) by (apply R; auto); unfold_iden.  lr.
      SCase "more".
        unfold fst, snd in *.
        assert_conclusion (_hw__Event__po_range _i (singleton_atom z)) R.
          oneof_auto.
        destruct R as [_ R].  apply r2_join12 in YZ.  apply r2_join12 in PO1.
        assert (y = y') by (apply R; auto); unfold_iden.  apply tc_tc_r in PO2.  lr.
    contradiction (po_acyclic _i).  exists (x, x).  split; try unfold_iden.
    destruct CYCLE as [CYCLE|CYCLE]; try unfold_iden; lr.
    right with y; lr.
Qed.

Lemma rmw_strong_tail : forall _i x y a,
  compile_src11_ptx _i
  -> x --(hw__Read__rmw _i)--> y
  -> a --(hw__strong_r _i)--> y
  -> a --(hw__strong_r _i)--> x.
Proof.
  intros _i x y a COMPILE XY AY.
  split.
  Case "a->x".
    destruct AY as [AY _].  split_1 AY AB b BY.  join_1 b.
    destruct BY as [BY|BY].
    SCase "b=y".
      unfold_iden.  (* no start.~po *)
      split_1 AB AB b BY.  apply start_tr_po in BY.
      contradiction BY.  exists x.  apply rmw_facts; auto.
    SCase "b->y".
      apply tc_rtc_one in BY.  split_1 BY BM m MY.
      assert (x = m); [|solve [unfold_iden; auto]].
      apply lone_inv_po with _i y; auto.  apply rmw_facts; auto.
  Case "x->a".
    apply untranspose_pair.  destruct AY as [_ AY].  apply transpose_pair in AY.
    split_3 AY AB b BC c CD d DY.  join_3 b c d.
    assert (x --(hw__Event__scope _i; tr (hw__Event__scope _i))--> y) as XY_SCOPE
      by (apply rmw_facts in XY; destructs XY).
    split_1 XY_SCOPE XS s YS.  apply transpose_pair in YS.
    assert (s = b); [|solve [unfold_iden; auto]].
    assert_conclusion (_hw__Event__scope_range _i (singleton_atom y)) Y.
      oneof_auto.
    apply Y; apply r2_join12; auto.
Qed.

Lemma com_unlowering : forall _i x' y',
  compile_src11_ptx _i
  -> x' --(hw__com _i)--> y'
  -> x' --(tr (sw__Event__map _i); sw__com _i; sw__Event__map _i)--> y'.
Proof.
  intros _i x' y' COMPILE XY'.
  assert (hw__MemoryEvent _i x') as X_E by (destruct XY' as [[RF|CO]|FR]; domain x').
  assert (hw__MemoryEvent _i y') as Y_E.
    destruct XY' as [[RF|CO]|FR].
      apply _hw__MemoryEvent_subsig_hw__Read; auto_range.
      apply _hw__MemoryEvent_subsig_hw__Write, tc_co_range with x'; auto.
      apply _hw__MemoryEvent_subsig_hw__Write, hw_fr_range with x'; auto.
  destruct XY' as [[RF|CO]|FR].
  Case "rf".
    assert (reverse_map_rf _i) as REV by (destructs COMPILE).
    apply REV in RF.  split_2 RF X' x XY y Y'.  join_2 x y.
  Case "co".
    assert_conclusion (reverse_map_tc_co _i) REV.
    apply REV in CO.  split_2 CO X' x XY y Y'.  join_2 x y.
  Case "fr".
    assert (reverse_map_fr _i) as REV by (destructs COMPILE).
    apply REV in FR.  split_2 FR X' x XY y Y'.  join_2 x y.
Qed.

Lemma weak_com_syncacqrel : forall _i x' y',
  compile_src11_ptx _i
  -> x' --(hw__com _i)--> y'
  -> ~(x' --(hw__strong_r _i)--> y')
  -> x' --(tr (sw__Event__map _i); sw__hb _i; sw__Event__map _i)--> y'.
Proof.
  intros _i x' y' COMPILE XY' WEAK.
  assert_conclusion (com_unlowering _i x' y') XY.
  split_2 XY X' x XY y Y'.  apply com_strong_or_hb in XY; auto.
  destruct XY as [XY|XY].
  Case "hb".
    join_2 x y.
  Case "strong".
    apply transpose_pair in X'.  repeat unfold_map.  contradiction.
Qed.

Theorem src11_ptx_legal_atomicity : src11_ptx_legal_atomicity_statement.
Proof.
  intros _i COMPILE [[x y] [RMW FR_MO]].
  split_1 FR_MO XA a AY.

  assert_conclusion (rmw_map _i x y) XY'.
  assert_conclusion (fr_map _i x a) XA'.
  assert_conclusion (mo_map _i a y) AY'.
  merge_lasts.  split_2 XY' X' x' XY y' Y'.
  split_2 XA' X1' x1' XY' y1' Y1'; repeat unfold_map.
  apply fr_co_fr_co in XY'; auto.  split_1 XY' XM' m' MY'.

  assert (m' --(hw__strong_r _i)--> y' \/ ~(m' --(hw__strong_r _i)--> y'))
    as STRONG by (apply classic).
  destruct STRONG as [STRONG|NOT_STRONG].
  Case "strong".
    assert_conclusion (rmw_strong_tail _i x' y' m') MX.
    assert (hw__atomicity _i) as ATOM by (destructs COMPILE).
    contradiction ATOM.  exists (x', y'); split; lr.
    join_1 m'; split; auto.  split; destructs MX.
  Case "not strong".
    assert_conclusion (weak_com_syncacqrel _i m' y') MY; lr.
    split_2 MY M' m MY y2' Y2'; repeat unfold_map.
    assert (~(x' --(hw__strong_r _i)--> m')) as XM.
      intros CON.
      assert (m' --(hw__strong_r _i)--> x') as MX by (split; destructs CON).
      assert_conclusion (rmw_strong_head _i x' y' m') XM.
    apply weak_com_syncacqrel with _i _ m' in XM; lr.
    split_2 XM X1' x1 XM m1 M1'; repeat unfold_map.
    apply hb_write in MY; auto; try solve [auto_range].
    split_1 MY MN n NY.  assert_conclusion (sb_rmw _i x y n) NX.
    contradiction (src11_ptx_legal_coherence _i).  cycle_with x.
    join_1 x; try unfold_iden.  apply tc_rtc with m; lr.
    apply rtc_rtc with n.
      destruct MN; lr.
      destruct NX; lr.
Qed.

(******************************************************************************)

Lemma scoped_inside : forall _i x' s,
  join s (transpose (hw__Event__scope _i)) x' ->
  intersect (hw__scoped _i s) (hw__inside _i s) x'.
Proof.
  intros _i x' s X.
  apply join12_r1_r2 in X.  destruct X as [s' [S X]].
  split.
  Case "scoped".
    apply r1_r2_join12 with s'; auto.  apply r1_r2_join12 with s'; lr.
  Case "inside".
    unfold hw__inside.
    apply scope_inclusion in X.  split_2 X XS s1' SH h' HX.
    apply r1_r2_join12 with s1'; auto.  apply r1_r2_join12 with h'; auto.
    apply r1_r2_join12 with s'; auto.
    apply rtc_of_tr; auto.  apply rtc_of_tr; auto.
Qed.

Lemma arrow_f : forall f x y,
  inside f (arrow (singleton_atom x) (singleton_atom y))
  -> f (x, y).
Proof.
  intros f x y XY.
  apply inside_arrow with (singleton_atom x) (singleton_atom y); auto; apply singleton_self.
Qed.

Lemma sc_or_tr_sc : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__strong_r _i)--> y
  -> intersect (sw__Fence _i) (sw__SC _i) x
  -> intersect (sw__Fence _i) (sw__SC _i) y
  -> x = y
  \/ x --(sw__Event__map _i; tc (hw__FenceSC__sc _i); tr (sw__Event__map _i))--> y
  \/ y --(sw__Event__map _i; tc (hw__FenceSC__sc _i); tr (sw__Event__map _i))--> x.
Proof.
  intros _i x y COMPILE STRONG X Y.
  assert (compile_fence_sc _i) as C by (destructs COMPILE).
  assert_conclusion (some_map _i x) X'.
    destruct X; subsig.
  assert_conclusion (some_map _i y) Y'.
    destruct Y; subsig.
  clean X' x'.  clean Y' y'.
  apply strong_map with _i x y x' y' in STRONG; auto.
  assert_conclusion (C x') CX.  apply r1_r2_join12 with x; auto.
  assert_conclusion (C y') CY.  apply r1_r2_join12 with y; auto.
  assert (compile_scope _i) as A_SCOPE by (destructs COMPILE).

  assert (x = y \/ x <> y) as EQ by (apply classic).
  destruct EQ as [EQ|EQ]; auto.  right.

  assert_conclusion (wf_sc _i) WF.  destruct WF as [WF _].
  assert_conclusion (WF (singleton_atom x')) WFX.
  assert_conclusion (WFX (singleton_atom y')) WFXY.
    intros CONTRA.  apply singleton_atom_eq in CONTRA.
      unfold_iden.  assert_conclusion (lone_inv_map _i x y x') M.
    apply inside_arrow_2; auto.
  clear WF WFX.  destruct WFXY as [XY|XY].
  Case "xy".
    left.  join_2 x' y'.  left.  apply arrow_f; auto.
    right.  join_2 y' x'.  left.  apply arrow_f; auto.
Qed.

Lemma only_fence_sc : forall _i x,
  sw__SC _i x
  -> sw__Fence _i x.
Proof.
  intros _i x X.
  assert (sw__Event _i x) as X_E.
    apply join12_r1_r2 in X.  destruct X as [o [O X_O]].
    apply transpose_pair in X_O.  domain x.
  apply _sw__Event_abstract in X_E.  auto_cases X_E.
  apply _sw__MemoryEvent_abstract in X_E.  destruct X_E as [X_E|X_E].
  Case "Write".
    assert_conclusion (WriteMO _i (singleton_atom x)) X_MO.
    apply join12_r1_r2 in X.  destruct X as [o [O X]].
    apply untranspose_pair, r2_join12, X_MO in X.
    destruct X as [[X|X]|X]; contradiction_types.
  Case "Read".
    assert_conclusion (ReadMO _i (singleton_atom x)) X_MO.
    apply join12_r1_r2 in X.  destruct X as [o [O X]].
    apply untranspose_pair, r2_join12, X_MO in X.
    destruct X as [[X|X]|X]; contradiction_types.
Qed.

Lemma efhb_fhb : forall _i x y,
  x --(util__ident _i (sw__SC _i)
       U (util__ident _i (intersect (sw__Fence _i) (sw__SC _i));
          util__optional _i (sw__hb _i)))--> y
  -> x --(util__ident _i (intersect (sw__Fence _i) (sw__SC _i));
             util__optional _i (sw__hb _i))--> y.
Proof.
  intros _i x y XY.  destruct XY as [XY|XY]; auto.
  repeat unfold_iden.  join_1 y.
  Case "Fsc".
    split; repeat unfold_iden.
    apply f_arrow_f.  split; auto.  apply only_fence_sc; auto.
  Case "hb".
    unfold_iden.
Qed.

Lemma ehbf_hbf : forall _i x y,
  x --(util__ident _i (sw__SC _i)
       U (util__optional _i (sw__hb _i);
          util__ident _i (intersect (sw__Fence _i) (sw__SC _i))))--> y
  -> x --(util__optional _i (sw__hb _i);
          util__ident _i (intersect (sw__Fence _i) (sw__SC _i)))--> y.
Proof.
  intros _i x y XY.  destruct XY as [XY|XY]; auto.
  repeat unfold_iden.  join_1 y.
  Case "hb".
    unfold_iden.
  Case "Fsc".
    split; repeat unfold_iden.
    apply f_arrow_f.  split; auto.  apply only_fence_sc; auto.
Qed.

Lemma scb_hb_eco : forall _i x y,
  x --(sw__scb _i)--> y
  -> x --(sw__hb _i U sw__com _i)--> y.
Proof.
  intros _i x y XY.  destruct XY as [[[[XY|XY]|XY]|XY]|XY]; lr.
  Case "sbnl".
    destruct XY as [SB NL]; lr.
  Case "sb; hb; sb".
    choose (sw__hb _i (x, y)).
    split_2 XY XA a AB b BY.  destruct AB as [AB NL].
    right with a; lr.  right with b; lr.
Qed.

Lemma cause_base_tc_po_syncacqrel : forall _i x y z,
  compile_src11_ptx _i ->
  hw__cause_base _i (x, y) ->
  (tc (hw__Event__po _i) U tc (syncacqrel _i)) (y, z) ->
  hw__cause_base _i (x, z).
Proof.
  intros _i x y z COMPILE_src11_ptx XY YZ.
  destruct YZ as [YZ|YZ].
  Case "po".
    apply cause_base_tc_po with y; lr.
  Case "syncacqrel".
    right with y; lr.  apply tc_in with (syncacqrel _i); auto.
    clear; intros [x y] XY.  split_2 XY XA a AB b BY.  join_2 a b.
Qed.

Lemma tc_po_syncacqrel_cause_base : forall _i x y z,
  compile_src11_ptx _i ->
  (tc (hw__Event__po _i) U tc (syncacqrel _i)) (x, y) ->
  hw__cause_base _i (y, z) ->
  hw__cause_base _i (x, z).
Proof.
  intros _i x y z COMPILE_src11_ptx XY YZ.
  destruct XY as [XY|XY].
  Case "po".
    apply tc_po_cause_base with y; lr.
  Case "syncacqrel".
    right with y; lr.  apply tc_in with (syncacqrel _i); auto.
    clear; intros [x y] XY.  split_2 XY XA a AB b BY.  join_2 a b.
Qed.

Lemma tc_sc_cause_base : forall _i x y,
  tc (hw__FenceSC__sc _i) (x, y) ->
  hw__cause_base _i (x, y).
Proof.
  intros _i x y XY.
  rem x y xy.  induction XY as [[x y] XY | [x y] a XA IHXA AY IHAY].
  Case "Base".  left.  join_2 x y.
  Case "ind".  right with a; lr.
Qed.

Lemma hbopt_hbeco_hbopt : forall _i x a b y,
  compile_src11_ptx _i
  -> x --(sw__strong_r _i)--> y
  -> intersect (sw__Fence _i) (sw__SC _i) x
  -> util__optional _i (sw__hb _i) (x, a)
  -> (sw__hb _i U sw__eco _i) (a, b)
  -> util__optional _i (sw__hb _i) (b, y)
  -> intersect (sw__Fence _i) (sw__SC _i) y
  -> x --(sw__Event__map _i; tc (hw__FenceSC__sc _i); tr (sw__Event__map _i))--> y.
Proof.
  intros _i x a b y COMPILE STRONG X XA AB BY Y.

  assert_conclusion (sc_or_tr_sc _i x y) SC.  destruct SC as [XY|[XY|XY]]; auto.
  Case "x=y".
    unfold_iden.  destruct AB as [AB|AB].
    SCase "hb".
      contradiction (src11_ptx_legal_coherence _i).  cycle_with y.
      join_1 y; repeat unfold_iden.
      apply tc_rtc with b; lr.  apply rtc_tc with a; lr.
      destruct XA as [XA|XA]; lr.
      destruct BY as [BY|BY]; lr.
    SCase "com".
      assert (util__optional _i (sw__hb _i) (b, a)) as BA.
        destruct XA as [XA|XA]; destruct BY as [BY|BY]; repeat unfold_iden; lr.
        right; right with y; lr.
      destruct BA as [BA|BA].
      SSCase "b=a".
        unfold_iden.  contradiction (eco_cycle _i a); lr.
      SSCase "b->a".
        contradiction (src11_ptx_legal_coherence _i).  cycle_with b.
      join_1 a; repeat unfold_iden.

  Case "~sc".
    assert ((sw__Event__map _i; hw__cause_base _i; tr (sw__Event__map _i)) (y, a)) as YA.
      destruct XA as [XA|XA].
      SCase "iden".
        unfold_iden.  split_2 XY X' x' XY y' Y'.  join_2 x' y'.
        apply tc_in with (hw__FenceSC__sc _i); auto.
        clear; intros [x y] H.  join_2 x y.
      SCase "hb".
        apply hb_syncacqrel in XA; auto.
        split_2 XA X' x' XA a' A'.  split_2 XY Y' y' YA a1' A1'.  unfold_map.
        join_2 y' a'.  apply cause_base_tc_po_syncacqrel with x'; auto.
        apply tc_sc_cause_base; auto.

    assert ((sw__Event__map _i; hw__cause_base _i; tr (sw__Event__map _i)) (b, a)) as BA.
      destruct BY as [BY|BY].
      SCase "iden".
        unfold_iden.  auto.
      SCase "hb".
        apply hb_syncacqrel in BY; auto.
        split_2 BY B' b' BY y' Y'.  split_2 YA Y1' y1' YA a' A'.  unfold_map.
        join_2 b' a'.  apply tc_po_syncacqrel_cause_base with y'; auto.

    clear - AB BA COMPILE.

    destruct AB as [AB|AB].
    Case "hb".
      apply hb_syncacqrel in AB; auto.
      split_2 AB A' a' AB b' B'.  split_2 BA B1' b1' BA a1' A1'.
      repeat unfold_map.  clear a b A' B'.
      assert (hw__causality _i) as CAUSALITY by (destructs COMPILE).
      contradiction CAUSALITY.  cycle_with a'.  join_1 a'; try unfold_iden.
      choose (hw__cause_base _i (a', a')).
      apply tc_po_syncacqrel_cause_base with b'; auto.
    Case "eco".
      apply ecos_equal in AB.  split_1 AB AM m MB.
      destruct MB as [MB|MB].
      SCase "iden".
        unfold_iden.  apply com_map in AM; auto.
        split_2 AM A1' a1' AM m' M'.  repeat unfold_map.
        contradiction (acyclic_com_syncacqrel _i a1' m').
        lr.
      SCase "rf".
        apply rf_map_obs_or_syncacqrel in MB; auto.
        apply com_map in AM; auto.
        split_2 AM A1' a1' AM m' M'.  split_2 MB M1' m1' MB b' B'.
        split_2 BA B1' b1' BA a' A'.  repeat unfold_map.
        contradiction (acyclic_com_syncacqrel _i a1' m').
        destruct MB as [[MB|MB]|MB].
        SSCase "obs".
          right.  join_1 b'.
        SSCase "po_loc".
          choose (hw__cause_base _i (m', a1')).
          apply tc_po_cause_base with b'; auto.  destructs MB.
        SSCase "cause_base".
          choose (hw__cause_base _i (m', a1')).
          right with b'; auto.
Qed.

Lemma pscbase_sc : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__strong_r _i)--> y
  -> x --(sw__pscbase _i)--> y
  -> x --(sw__Event__map _i; tc (hw__FenceSC__sc _i); tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE STRONG XY.

  split_2 XY XA a AB b BY.
  apply efhb_fhb in XA.  apply ehbf_hbf in BY.
  split_1 XA X x1 XA; repeat unfold_iden.  rename x1 into x.
  split_1 BY BY y1 Y; repeat unfold_iden.
  apply scb_hb_eco in AB.  apply hbopt_hbeco_hbopt with a b; auto.
  destruct AB; lr.
Qed.

Lemma pscF_sc : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__strong_r _i)--> y
  -> x --(sw__pscF _i)--> y
  -> x --(sw__Event__map _i; tc (hw__FenceSC__sc _i); tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE STRONG XY.

  split_2 XY XA a AB b BY.  repeat unfold_iden.
  destruct AB as [AB|AB].
  Case "hb".
    apply hbopt_hbeco_hbopt with a y; lr; repeat unfold_iden.
  Case "hb; eco; hb".
    split_2 AB AB b BC c CY.
    apply hbopt_hbeco_hbopt with b c; lr; repeat unfold_iden.
Qed.

Lemma psc_sc : forall _i x y,
  compile_src11_ptx _i
  -> x --(sw__strong_r _i)--> y
  -> x --(sw__psc _i)--> y
  -> x --(sw__Event__map _i; tc (hw__FenceSC__sc _i); tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE STRONG XY.
  destruct XY as [XY|XY].
    apply pscbase_sc; auto.
    apply pscF_sc; auto.
Qed.

Lemma tc_psc_f_sc : forall _i x y,
  compile_src11_ptx _i
  -> x --(tc (sw__strong _i (sw__psc _i)))--> y
  -> x --(sw__Event__map _i; tc (hw__FenceSC__sc _i); tr (sw__Event__map _i))--> y.
Proof.
  intros _i x y COMPILE XY.
  rem x y xy.  induction XY as [[x y] XY | [x y] a XA IHXA AY IHAY].
  Case "base".
    apply psc_sc; destructs XY.
  Case "ind".
    merge_lasts.  split_2 IHXA X' x' XY y' Y'.  join_2 x' y'.
    split_1 XY XM m' MY.  right with m'; auto.
Qed.

Theorem src11_ptx_legal_sc : forall _i,
  compile_src11_ptx _i
  -> sw__sc _i.
Proof.
  intros _i COMPILE [[x1 x] [IDEN X]]; unfold_iden.
  apply tc_psc_f_sc in X; auto.  split_2 X X' x' X x1' X1'; unfold_map.
  assert (hw__causality _i) as CAUSALITY by (destructs COMPILE).
  contradiction CAUSALITY.  cycle_with x'.  join_1 x'; try unfold_iden.
  choose (hw__cause_base _i (x', x')).  apply tc_sc_cause_base; auto.
Qed.
