Require Import alloy.

Ltac u :=
match goal with
| [ H : _ |- ?f ] => unfold f
| [ H : _ |- ?f ?x1 ] => unfold f
| [ H : _ |- ?f ?x1 ?x2 ] => unfold f
| [ H : _ |- ?f ?x1 ?x2 ?x3 ] => unfold f
| [ H : _ |- ?f ?x1 ?x2 ?x3 ?x4 ] => unfold f
end.

Definition singleton {n : nat} (t : Tuple n) : Relation n := fun x => t = x.
Definition singleton_atom (a : Atom) : Relation 1 := singleton (_atom_tuple a).

Lemma singleton_self : forall n x, singleton (n:=n) x x.
Proof.
  intros n x.  unfold singleton.  auto.
Qed.

Lemma singleton_atom_self : forall x, singleton_atom x x.
Proof.
  intros x.  unfold singleton_atom.  apply singleton_self.
Qed.

Lemma singleton_atoms_equal : forall x y,
  equal (singleton_atom x) (singleton_atom y) ->
  x = y.
Proof.
  intros x y H.  apply H, singleton_self.
Qed.

Lemma singleton_atom_xy : forall x y, singleton_atom x y -> x = y.
Proof.
  intros x y H.  unfold singleton_atom, singleton, _atom_tuple in H; auto.
Qed.

Lemma equal_singleton_atoms : forall x y,
  x = y ->
  equal (singleton_atom x) (singleton_atom y).
Proof.
  intros x y H.  split.
    intros X.  apply singleton_atom_xy in X.  rewrite <- X, <- H in *.  apply singleton_self.
    intros X.  apply singleton_atom_xy in X.  rewrite <- X, <- H in *.  apply singleton_self.
Qed.

Lemma singleton_atoms_neq : forall x y,
  x <> y ->
  ~equal (singleton_atom x) (singleton_atom y).
Proof.
  intros x y H.  intros C; contradiction H.  apply singleton_atoms_equal; auto.
Qed.

Definition Pair (x y : Atom) : Tuple (1 + 1) := (x, y).

Lemma tuple_atom : forall (x : Tuple 1), exists! (a: Atom), x=a.
Proof.
  intros x.  exists x.  split; auto.
Qed.

Lemma atom_tuple : forall (a: Atom), exists! (x: Tuple 1), x=a.
Proof.
  intros a.  exists a.  split; auto.
Qed.

Lemma domain2 : forall (x y : Atom) (f : Relation 2) (d : Relation 1), f (x, y) -> d x -> domain d f (x, y).
Proof.
  intros x y f d F D.  exists x, y.  repeat split; auto.  symmetry.  apply tuple_join_cast.
Qed.

Ltac prove_hyp H := match goal with
| [ X : ?A -> ?B |- _ ] => assert A as PROVE_HYP; [|apply H in PROVE_HYP; clear H; rename PROVE_HYP into H]
end.

Lemma and_dup : forall A, A /\ A -> A.
Proof.  intros A H.  destruct H; auto.
Qed.

Lemma f_arrow : forall (x y : Atom),
  arrow (singleton_atom x) (singleton_atom y) (x, y).
Proof.
  intros x y.  exists x, y.  repeat split; auto.  rewrite tuple_join_cast; auto.
Qed.

Ltac destructs H :=
try solve [auto];
try solve [destruct H as [H _]; destructs H];
solve [destruct H as [_ H]; destructs H].

Lemma arrow_each : forall (f g : Relation 1) (x y : Atom), arrow f g (x, y) -> f x /\ g y.
Proof.
  intros f g x y ARROW.  destruct ARROW as [x' [y' [F [G TUPLE]]]].
  rewrite tuple_join_cast in F; inversion F as [[X Y]].
  split; auto.
Qed.

Lemma arrow_each_tc : forall (f g : Relation 1) (x y : Atom), tc (arrow f g) (x, y) -> f x /\ g y.
Proof.
  intros f g x y ARROW.  remember (x, y) as xy.
  assert (x = fst xy) as X by (rewrite Heqxy; auto); rewrite X in *.
  assert (y = snd xy) as Y by (rewrite Heqxy; auto); rewrite Y in *.
  clear X Y Heqxy x y.
  induction ARROW as [[x y] ARROW | [x y] a XA IHXA AY IHAY].
  (* base *)
    apply arrow_each; auto.
  (* ind *)
    destruct IHXA, IHAY; auto.
Qed.

Lemma arrow_same : forall (f : Relation 1) (x : Atom), arrow f f (x, x) -> f x.
Proof.
  intros f x ARROW.  apply arrow_each in ARROW.  destructs ARROW.
Qed.

Ltac unfold_ident :=
match goal with
| [ H : ?x = ?y |- _ ] =>
  rewrite H in *; clear H x
| [ H : ?x = ?y |- _ ] =>
  rewrite <- H in *; clear H x
| [ H : iden (Pair ?x ?y) |- _ ] =>
  unfold iden in H; simpl in H; rewrite H in *; clear H x
| [ H : iden (?x, ?y) |- _ ] =>
  unfold iden in H; simpl in H; rewrite H in *; clear H x
| [ H : singleton ?x ?y |- _ ] =>
  unfold singleton in H; rewrite H in *; clear H x
| [ H : singleton_atom ?x ?y |- _ ] =>
  unfold singleton_atom, singleton, _atom_tuple in H; unfold_ident
| [ H : arrow (singleton_atom ?x) (singleton_atom ?y) (?a, ?b) |- _ ] =>
  destruct H as [? [? [? [? ?]]]]; repeat unfold_ident
| [ H : _tuple_join ?x1 ?y1 = (?x2, ?y2) |- _ ] =>
  rewrite tuple_join_cast in H; inversion H as [[_TEMP1 _TEMP2]];
  clear H; repeat unfold_ident
| [ H : (?x1, ?y1) = _tuple_join ?x2 ?y2 |- _ ] =>
  rewrite tuple_join_cast in H; inversion H as [[_TEMP1 _TEMP2]];
  clear H; repeat unfold_ident
| [ H : fst (?x, ?y) = snd (?x, ?y) |- _ ] =>
  simpl in H; unfold_ident
| [ _ : _ |- (?x, ?y) = _tuple_join ?x ?y ] =>
  rewrite tuple_join_cast; solve [auto]
| [ _ : _ |- singleton_atom ?x ?x ] =>
  unfold singleton_atom, singleton, _atom_tuple; solve [auto]
| [ _ : _ |- ?x = _tuple_join_cast_0plus ?x (plus0b 0) ] =>
  rewrite cast0b; solve [auto]
| [ _ : _ |- arrow (singleton_atom ?x) (singleton_atom ?y) (?x, ?y) ] =>
  apply f_arrow
| [ H : ?A /\ ?A |- _ ] =>
  apply and_dup in H
| [ H1 : ?f ?x, H2: ?f ?y, H3: one ?f |- _ ] =>
  assert (lone f) as _LONE by (destructs H3);
  unfold lone in _LONE; specialize _LONE with x y;
  apply _LONE in H1; auto; unfold_ident; clear _LONE
| [ H : _ |- iden (?x, ?x) ] =>
  unfold iden; auto
| [ H : iden (?x, ?y) |- _ ] =>
  unfold iden in H; simpl in H; unfold_ident
| [ H : _ |- iden (?x, ?y) ] =>
  unfold iden; simpl; auto
| [ H : arrow ?f ?f (?x, ?x) |- _ ] =>
  apply arrow_same in H
| [ H : equal (singleton_atom ?x) (singleton_atom ?y) |- _ ] =>
  apply singleton_atoms_equal in H; unfold_ident
| [ H1 : lone ?f, H2 : ?f ?x, H3 : ?f ?y |- _ ] =>
  assert (x = y) as _TEMP by (apply H1; auto); unfold_ident
end.

Lemma f_arrow_f : forall (f : Relation 1) (x : Atom), f x -> arrow f f (x, x).
Proof.
  intros f x ARROW.  exists x, x.  split; auto.  unfold_ident.
Qed.

Lemma each_arrow : forall (f g : Relation 1) (x y : Atom), f x -> g y -> arrow f g (x, y).
Proof.
  intros f g x y X Y.  exists x, y.  split; auto.  symmetry.  apply tuple_join_cast; auto.
Qed.

Lemma join12_r2 : forall x y (f: Relation 2), join (singleton_atom x) f y -> f (x, y).
Proof.
  intros x y f H.  destruct H as [y' [x' H]].  destruct H as [SINGLETON [F Y]].
  simpl in F.  unfold singleton_atom, singleton, _atom_tuple in SINGLETON.
  repeat unfold_ident.  rewrite cast0b.  auto.
Qed.

Lemma join_unsplit : forall (f g: Relation 2) (x z : Atom), join f g (x, z) -> exists y, f (x, y) /\ g (y, z).
Proof.
  intros f g x z FGXZ.  destruct FGXZ as [x' [z' [y FGXZ]]].  destruct FGXZ as [F [G XZ]].
  symmetry in XZ.  apply tuple_join_cast_indiv in XZ.  destruct XZ as [X Z].
  rewrite X, Z in *; clear x' X z' Z.
  exists y.  auto.
Qed.

Lemma r2_r2_join22 : forall (f g: Relation 2) (x y z : Atom), f (x, y) -> g (y, z) -> join f g (x, z).
Proof.
  intros f g x y z FXY GYZ.  exists x, z, y.  repeat split; auto.
  symmetry; apply tuple_join_cast.
Qed.

Lemma r2_join12 : forall (f : Relation 2) (x y : Atom), f (x, y) -> join (singleton_atom x) f y.
Proof.
  intros f x y FXY.  exists y, x.  repeat split; auto.
  rewrite cast0b.  auto.
Qed.

Lemma join_some_1 : forall f (x : Atom), some (join (singleton_atom x) f) -> exists y, f (Pair x y).
Proof.
  intros f x H.  destruct H as [y H].  exists y.  unfold Pair.
  destruct H as [y' [x' [X [F Y]]]].  repeat unfold_ident.
  rewrite cast0b.  auto.
Qed.

Lemma join_unjoin : forall f g (x z : Atom), join f g (Pair x z) -> exists y, f (Pair x y) /\ g (Pair y z).
Proof.
  intros f g x z FG.  destruct FG as [x' [z' [y FG]]].
  exists y.  destruct FG as [F [G XZ]].  rewrite tuple_join_cast in XZ.  simpl in *.
  unfold Pair in XZ.  inversion XZ as [[X Z]].  unfold Pair.  auto.
Qed.

Lemma join_join : forall (f : Relation 2) (x : Tuple 1) (y : Atom), join (singleton x) f y -> f (x, y).
  intros f x y FXY.  destruct FXY as [y' [x' FXY]].  destruct FXY as [SINGLETON [FXY TUPLE]].
  simpl in FXY.  unfold singleton in SINGLETON.  rewrite <- SINGLETON in *.
  rewrite cast0b in TUPLE.  rewrite TUPLE in *; auto.
Qed.

Lemma join_pair : forall (f : Relation 2) (x y : Atom), f (Pair x y) -> join (singleton_atom x) f y.
Proof.
  intros f x y XY.  exists y, x.  split.
    unfold singleton_atom, singleton, _atom_tuple; auto.
  split; auto.
  symmetry.  apply cast0b.
Qed.

Lemma join12 : forall (f : Relation 2) (x : Tuple 1) (y : Atom),
  join (singleton x) f y -> f (x, y).
Proof.
  intros f x y H.  destruct H as [y' [x' [X [Y H]]]].  repeat unfold_ident.
  rewrite cast0b.  auto.
Qed.

Lemma r1_r2_join12 : forall (f : Relation 1) (g : Relation 2) (x y : Atom),
  f x -> g (x, y) -> join f g y.
Proof.
  intros f g x y F G.  exists y, x.  split; auto.  split; auto.  rewrite cast0b; auto.
Qed.

Lemma join12_r1_r2 : forall (f : Relation 1) (g : Relation 2) (x : Atom),
  join f g x -> exists y, f y /\ g (y, x).
Proof.
  intros f g x FG.  destruct FG as [x' [y' [FY [GXY TUPLE]]]].  exists y'.
  split; auto.  unfold_ident.  rewrite cast0b.  apply GXY.
Qed.

Ltac split_join_hyp H x H1 H2 :=
  apply join_unjoin in H; destruct H as [x [H1 H2]]; unfold Pair in H1, H2.

Ltac split_join_hyp_twice H x y H1 H2 H3 :=
  split_join_hyp H y H1 H3; split_join_hyp H1 x H1 H2.

Ltac split_join1_hyp H x H1 H2 :=
  apply join12_r1_r2 in H; destruct H as [x [H1 H2]]; unfold Pair in H1, H2.

Lemma reverse_pair : forall x y, _tuple_reverse (Pair x y) = Pair y x.
Proof.
  intros x y.  unfold Pair.  auto.
Qed.

(******************************************************************************)
(* Domain and range *)

Lemma domain_split : forall (f : Relation 1) (g : Relation 2) (x y : Tuple 1),
  domain f g (x, y) ->
  g (x, y) /\ f x.
Proof.
  intros f g x y D.  destruct D as [x' [y' [F [G XY]]]].
  rewrite tuple_join_cast in XY.  inversion XY as [[X Y]].
  repeat unfold_ident.  auto.
Qed.

Lemma domain_unsplit : forall (f : Relation 1) (g : Relation 2) (x y : Tuple 1),
  f x -> g (x, y) -> domain f g (x, y).
Proof.
  intros f g x y F G.  exists x, y.  split; auto.  split; auto.
  rewrite tuple_join_cast; auto.
Qed.

Ltac unfold_domain H H1 H2 :=
  apply domain_split in H; destruct H as [H1 H2].

Lemma range_split : forall (f : Relation 2) (g : Relation 1) (x y : Tuple 1),
  range (m:=1) f g (x, y) ->
  f (x, y) /\ g y.
Proof.
  intros f g x y R.  destruct R as [x' [y' [F [G XY]]]].
  rewrite tuple_join_cast in XY.  inversion XY as [[X Y]].
  repeat unfold_ident.  auto.
Qed.

Lemma range_unsplit : forall (f : Relation 2) (g : Relation 1) (x y : Tuple 1),
  f (x, y) -> g y -> range (m:=1) f g (x, y).
Proof.
  intros f g x y F G.  exists x, y.  split; auto.  split; auto.
  rewrite tuple_join_cast; auto.
Qed.

Ltac unfold_range H H1 H2 :=
  apply range_split in H; destruct H as [H1 H2].

Lemma range_split_pair : forall (f : Relation 2) (g : Relation 1) (xy : Tuple 2),
  range (m:=1) f g xy ->
  f xy /\ g (snd xy).
Proof.
  intros f g [x y] R.  apply range_split.  auto.
Qed.

Ltac unfold_range_pair H H1 H2 :=
  apply range_split_pair in H; destruct H as [H1 H2].

Lemma f_range : forall (f : Relation 2) (g : Relation 1) (x y : Atom),
  f (x, y) -> g y -> range (m:=1) f g (x, y).
Proof.
  intros f g x y F G.  exists x, y.  split; auto.  split; auto.  rewrite tuple_join_cast; auto.
Qed.

Lemma oneof_singleton_atom : forall (f : Relation 1) (x : Atom),
  f x -> oneof f (singleton_atom x).
Proof.
  intros f x F.  split; [|split].
  intros x' X.  unfold_ident; auto.
  exists x.  unfold_ident.
  intros x1 x2 X1 X2.  repeat unfold_ident; auto.
Qed.

Lemma ranges : forall (f : Relation 2) x y r,
  f (x, y) ->
  setof r (join (singleton_atom x) f) ->
  oneof r (singleton_atom y).
Proof.
  intros f x y r F R.
  split; [|split].
  intros y' S.  unfold_ident.  apply R.
    exists y', x.  split; [|split]; auto; try unfold_ident.
  exists y; unfold_ident.
  intros y1 y2 Y1 Y2; repeat unfold_ident; auto.
Qed.

Lemma inside_split : forall (f a b : Relation 2),
  inside f a -> inside f b -> inside f (union a b).
Proof.
  intros f a b A B x AB.  destruct AB; auto.
Qed.

Lemma inside_arrow : forall (f : Relation 2) (x y : Relation 1) (x' y' : Atom),
  inside f (arrow x y) ->
  x x' ->
  y y' ->
  f (x', y').
Proof.
  intros f x y x' y' F X Y.  apply F.  exists x', y'.  repeat split; auto.
  symmetry.  apply tuple_join_cast.
Qed.

Lemma inside_arrow_2 : forall (f : Relation 2) (x y : Atom),
  f (x, y) -> inside f (arrow (singleton_atom x) (singleton_atom y)).
Proof.
  intros f x y F [x' y'] ARROW.
  destruct ARROW as [x1 [y1 [TUPLE [X1 Y1]]]]; repeat unfold_ident; auto.
Qed.

Lemma inside_singleton_atom : forall (f : Relation 1) (x : Atom),
  f x -> inside f (singleton_atom x).
Proof.
  intros f x F x' X.  unfold_ident.  auto.
Qed.

Lemma singleton_atom_inside : forall (f : Relation 1) (x : Atom),
  inside f (singleton_atom x) -> f x.
Proof.
  intros f x F.  apply F.  unfold_ident.
Qed.

Lemma range_f : forall (f : Relation 2) (r : Relation 1) (x y : Atom),
  range (m:=1) f r (x, y) -> f (x, y).
Proof.
  intros f r x y RANGE.  destruct RANGE as [x' [y' [XY [Y TUPLE]]]].
  repeat unfold_ident.  auto.
Qed.

Ltac lr := auto; try solve [left; lr]; try solve [right; lr].

Lemma rtc_rtc : forall (f : Relation 2) (x y z : Atom),
  rtc f (x, y) -> rtc f (y, z) -> rtc f (x, z).
Proof.
  intros f x y z XY YZ.  destruct XY as [XY|XY], YZ as [YZ|YZ].
  repeat unfold_ident.  left; auto.
  repeat unfold_ident.  right; auto.
  repeat unfold_ident.  right; auto.
  right.  right with y; auto.
Qed.

Lemma tc_rtc : forall (f : Relation 2) (x y z : Atom),
  tc f (x, y) -> rtc f (y, z) -> tc f (x, z).
Proof.
  intros f x y z XY YZ.  destruct YZ as [YZ|YZ].
  repeat unfold_ident; auto.
  right with y; auto.
Qed.

Lemma rtc_tc : forall (f : Relation 2) (x y z : Atom),
  rtc f (x, y) -> tc f (y, z) -> tc f (x, z).
Proof.
  intros f x y z XY YZ.  destruct XY as [XY|XY].
  repeat unfold_ident; auto.
  right with y; auto.
Qed.

Lemma rtc_of_tc : forall f x, rtc (tc f) x -> rtc f x.
Proof.
  intros f x H.  destruct H as [H|H]; lr.
  induction H as [x H|[x z] y H1 IH1 H2 IH2]; lr.
  apply rtc_rtc with y; lr.
Qed.

Lemma rtc_int_l : forall f g x, rtc (intersect f g) x -> rtc f x.
Proof.
  intros f g x F.  destruct F as [F|F]; lr.
  induction F as [x F|[x z] y F1 IH1 F2 IH2].
    destruct F; lr.
    apply rtc_rtc with y; auto.
Qed.

Lemma tc_int_l : forall f g x, tc (intersect f g) x -> tc f x.
Proof.
  intros f g x F.
  induction F as [x F|[x z] y F1 IH1 F2 IH2].
    destruct F; lr.
    right with y; auto.
Qed.

Lemma rtc_sub_l : forall f g x, rtc f x -> rtc (union f g) x.
Proof.
  intros f g x F.  destruct F as [F|F]; lr.
  induction F as [x F|[x z] y F1 IH1 F2 IH2]; lr.
  apply rtc_rtc with y; auto.
Qed.

Lemma rtc_sub_r : forall f g x, rtc g x -> rtc (union f g) x.
Proof.
  intros f g x G.  destruct G as [G|G]; lr.
  induction G as [x G|[x z] y G1 IH1 G2 IH2]; lr.
  apply rtc_rtc with y; auto.
Qed.

Lemma tc_sub_l : forall f g x, tc f x -> tc (union f g) x.
Proof.
  intros f g x F.
  induction F as [x F|[x z] y F1 IH1 F2 IH2]; lr.
  right with y; auto.
Qed.

Lemma tc_sub_r : forall f g x, tc g x -> tc (union f g) x.
Proof.
  intros f g x G.
  induction G as [x G|[x z] y G1 IH1 G2 IH2]; lr.
  right with y; auto.
Qed.

Lemma tc_in : forall (f g : Relation 2) x,
  tc f x -> inside g f -> tc g x.
Proof.
  intros f g x F FG.  induction F.
    left; apply FG; auto.
    right with y; auto.
Qed.

Ltac spec H y := match goal with [ H : ?f ?x |- _ ] => unfold f in H; specialize H with y end.

Lemma join_assoc : forall (f g h : Relation 2),
  equal (join f (join g h)) (join (join f g) h).
Proof.
  intros f g h.  split; destruct x as [x y]; intros H.
  (* -> *)
    split_join_hyp H a1 XA AY.  split_join_hyp AY a2 A AY.
    apply r2_r2_join22 with a2; auto.  apply r2_r2_join22 with a1; auto.
  (* <- *)
    split_join_hyp H a2 XA AY.  split_join_hyp XA a1 XA A.
    apply r2_r2_join22 with a1; auto.  apply r2_r2_join22 with a2; auto.
Qed.

Lemma join_assoc_l : forall (f g h : Relation 2) (x : Tuple 2),
  join f (join g h) x -> join (join f g) h x.
Proof.
  intros f g h [x y] H.
  split_join_hyp H a1 XA AY.  split_join_hyp AY a2 A AY.
  apply r2_r2_join22 with a2; auto.  apply r2_r2_join22 with a1; auto.
Qed.

Lemma join_assoc_r : forall (f g h : Relation 2) (x : Tuple 2),
  join (join f g) h x -> join f (join g h) x.
Proof.
  intros f g h [x y] H.
  split_join_hyp H a2 XA AY.  split_join_hyp XA a1 XA A.
  apply r2_r2_join22 with a1; auto.  apply r2_r2_join22 with a2; auto.
Qed.

Lemma transpose_pair : forall (f : Relation 2) (x y : Atom), transpose f (x, y) -> f (y, x).
Proof.
  intros f x y F.  auto.
Qed.

Lemma untranspose_pair : forall (f : Relation 2) (x y : Atom), f (x, y) -> transpose f (y, x).
Proof.
  intros f x y F.  auto.
Qed.

Lemma singleton_atom_oneof {n} : forall f x, oneof (n:=n) f x -> exists x', x x' /\ f x' /\ one x.
Proof.
  intros f x ONEOF.
  assert (some x) as SOME by (destructs ONEOF).  destruct SOME as [x' SOME].  exists x'.
  split; auto.
  split.
    assert (inside f x) as INSIDE by (destructs ONEOF).  apply INSIDE.  auto.
  destructs ONEOF.
Qed.

Lemma one_some : forall {n} x, one (n:=n) x -> some x.
Proof.  intros n x H; destructs H.  Qed.

Lemma oneof_lone : forall (f g : Relation 1) (x y : Atom),
  oneof f g ->
  g x ->
  g y ->
  x = y.
Proof.
  intros f g x y ONEOF X Y.  assert (lone g) as LONE by (destructs ONEOF).
  apply LONE; auto.
Qed.

Lemma oneof_f : forall (f : Relation 1) x x', oneof f x -> x x' -> f x'.
Proof.
  intros f x x' F X; destructs F.
Qed.

Lemma f_oneof : forall (f x : Relation 1) (x' : Atom), one x -> x x' -> f x' -> oneof f x.
Proof.
  intros f x x' ONE X F.  split; auto.
  (* inside *)
    intros x'' H.  assert (lone x) as LONE by (destructs ONE).
    assert (x' = x'') as X'' by (destructs LONE).  rewrite <- X''; auto.
Qed.

Ltac do_range R RANGE :=
match goal with
| [ F : ?f ?i (?x, ?y) |- _ ] =>
  generalize (R i (singleton_atom x)); intros RANGE; apply r2_join12, RANGE in F; auto
end.

Lemma f_tr_f_refl : forall (f : Relation 2) x y,
  join f (transpose f) (x, y) -> join f (transpose f) (y, x).
Proof.
  intros f x y XY.  split_join_hyp XY a XA AY.  apply r2_r2_join22 with a; lr.
Qed.

Ltac rem x y xy :=
  remember (x, y) as xy eqn:_Heqxy;
  assert (x = fst xy) as _X by (rewrite _Heqxy; lr); rewrite _X in *; clear x _X;
  assert (y = snd xy) as _Y by (rewrite _Heqxy; lr); rewrite _Y in *; clear y _Y;
  clear _Heqxy.

Lemma tc_transpose : forall f x y,
  tc (transpose f) (x, y) ->
  transpose (tc f) (x, y).
Proof.
  intros f x y XY.  rem x y xy.  induction XY as [[x y] XY | [x y] a XA IHXA AY IHAY].
  (* base *)
    apply transpose_pair in XY.  apply untranspose_pair.  lr.
  (* ind *)
    unfold fst, snd in *.
    apply transpose_pair in IHXA.  apply transpose_pair in IHAY.
    apply untranspose_pair.  right with a; lr.
Qed.

Lemma join_exists : forall (a : Relation 1) (f : Relation 2) (x : Atom),
  join a f x ->
  exists a', a a' /\ f (a', x).
Proof.
  intros a f x H.  destruct H as [x' [a' [A [F H]]]].  exists a'.  split; auto.
  rewrite cast0b in H.  unfold_ident.  auto.
Qed.

Lemma arrow_112 : forall (a b : Relation 1) (x y : Atom),
  a x -> b y -> arrow a b (x, y).
Proof.
  intros a b x y AX BY.  exists x, y.  split; auto.
  symmetry.  apply tuple_join_cast.
Qed.
