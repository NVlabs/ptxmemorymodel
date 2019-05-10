Require Import Eqdep_dec.

(** Basic Datatypes *)
Inductive EmptySet :=.

Inductive Atom := atom : nat -> Atom.

Fixpoint Tuple (n : nat) : Type :=
  match n with
  | 0    => EmptySet
  | 1    => Atom
  | S n' => ((Tuple n') * Atom) % type
  end.

Definition Relation (n : nat) : Type := (Tuple n) -> Prop.

(* Type casting helper functions : need to prove, e.g., that Tuple n = Tuple (n + 0) *)

Lemma no_tuple_0 : Tuple 0 -> False.  Proof.  intros H; inversion H.  Qed.

Definition _tuple_join_cast_plus0 {n : nat} (x : Tuple (S (n + 0))) (pf : n + 0 = n) : Tuple (S n) :=
  match pf with
  | eq_refl => x
  end.

Definition _tuple_join_cast_plus1 {m : nat} (x : Tuple (S m)) (pf : S m = (m + 1)) : Tuple (m + 1) :=
  match pf with
  | eq_refl => x
  end.

Definition _tuple_join_cast_mn {m n : nat} (x : Tuple (S m + S n)) (pf : (S m + S n) = (m + S (S n))) : Tuple (m + S (S n)) :=
  match pf with
  | eq_refl => x
  end.

Definition _tuple_join_cast_0plus {n : nat} (x : Tuple (S n)) (pf : (S n) = (0 + S n)) : Tuple (0 + S n) :=
  match pf with
  | eq_refl => x
  end.

Definition _atom_tuple (a : Atom) : Tuple 1 := a.

Lemma plus0 (n : nat) : n + 0 = n.  Proof.  auto.  Qed.

Lemma plus1 (n : nat) : S n = n + 1.
Proof.
  induction n; auto.
  rewrite plus_Sn_m.  rewrite IHn.  auto.
Qed.

Lemma plus_mn (m n : nat) : (S m + S n) = (m + S (S n)).
Proof.
  (* FIXME for fun, code golf this a little... *)
  assert (m + S (S n) = S (m + S n)) as H.  rewrite plus_n_Sm.  auto.
  rewrite H.  rewrite plus_Sn_m.  auto.
Qed.

Lemma plus0b (n : nat) : S n = 0 + S n.  Proof.  auto.  Qed.

(* Internal Tuple operations *)

Fixpoint _tuple_fst {n : nat} : Tuple (S (S n)) -> Atom :=
  match n with
  | 0 => fun x => fst x
  | _ => fun x => _tuple_fst (fst x)
  end.

Definition _tuple_last {n : nat} (x : Tuple (S (S n))) : Atom :=
  match x with
  (_, x') => x'
  end.

Definition _tuple_hd {n : nat} (x : Tuple (S (S n))) : Tuple (S n) :=
  match x with
  (x', _) => x'
  end.

Definition _tuple_append {n : nat} : Tuple n -> Atom -> Tuple (S n) :=
  match n with
  | 0 => fun x y => y
  | _ => fun x y => (x, y)
  end.

Fixpoint _tuple_prepend {n : nat} : Tuple (S n) -> Atom -> Tuple (S (S n)) :=
  match n with
  | 0 => fun x y => (y, x)
  | _ => fun x y => _tuple_append (_tuple_prepend (_tuple_hd x) y) (_tuple_last x)
  end.

Fixpoint _tuple_tl {n : nat} : Tuple (S (S n)) -> Tuple (S n) :=
  match n with
  | 0 => fun x => snd x
  | _ => fun x => _tuple_append (_tuple_tl (_tuple_hd x)) (_tuple_last x)
  end.

Fixpoint _tuple_shift {m n : nat} : Tuple m -> Tuple (S (S n)) -> (Tuple (S m) * Tuple (S n)) :=
  fun x y => (_tuple_append x (_tuple_fst y), _tuple_tl y).

Fixpoint _tuple_reverse {n : nat} : Tuple (S n) -> Tuple (S n) :=
  match n with
  | 0 => fun x => x
  | _ => fun x => _tuple_prepend (_tuple_reverse (_tuple_hd x)) (_tuple_last x)
  end.

Fixpoint _tuple_join {m n : nat} : Tuple m -> Tuple (S n) -> Tuple (m + (S n)) :=
  match n with
  | 0 => fun x y => _tuple_join_cast_plus1 (_tuple_append x (_tuple_join_cast_plus1 y (plus1 0))) (plus1 m)
  | (S n') => fun x y =>
    match _tuple_shift x y with
    | (x', y') => _tuple_join_cast_mn (_tuple_join x' y') (plus_mn m n')
    end
  end.

(* Multiplicities and Set Comparison *)

Definition inside {n : nat} (super sub : Relation n) : Prop :=
  forall (x : Tuple n), sub x -> super x.

Definition lone {n : nat} (r : Relation n) : Prop :=
  forall (x y : Tuple n), r x -> r y -> x = y.

Definition some {n : nat} (r : Relation n) : Prop :=
  exists (x : Tuple n), r x.

Definition one {n : nat} (r : Relation n) : Prop :=
  some r /\ lone r.

Definition no {n : nat} (r : Relation n) : Prop :=
  ~some r.

Definition oneof {n : nat} (super sub : Relation n) : Prop :=
  inside super sub /\ one sub.

Definition loneof {n : nat} (super sub : Relation n) : Prop :=
  inside super sub /\ lone sub.

Definition setof {n : nat} (super sub : Relation n) : Prop :=
  inside super sub.

Definition union {n : nat} (a b : Relation n) (x : Tuple n) :=
  a x \/ b x.

Definition intersect {n : nat} (a b : Relation n) (x : Tuple n) :=
  a x /\ b x.

Definition difference {n : nat} (a b : Relation n) (x : Tuple n) :=
  a x /\ ~b x.

Definition equal {n : nat} (a b : Relation n) :=
  forall (x : Tuple n), a x <-> b x.

(** Other operators *)

Definition arrow {m n: nat} : Relation (S m) -> Relation (S n) -> Tuple ((S m) + (S n)) -> Prop :=
  fun a b x => exists x1 x2, x = _tuple_join x1 x2 /\ a x1 /\ b x2.

Definition transpose {n : nat} (f : Relation (S n)) (x : Tuple (S n)) : Prop :=
  f (_tuple_reverse x).

Definition join {m n : nat} : Relation (S m) -> Relation (S n) -> Tuple (m+n) -> Prop :=
  match n with
  | 0 =>
    fun (a : Relation (S m)) (b : Relation 1) (x : Tuple (m + 0)) =>
    exists y, a (_tuple_join_cast_plus0 (_tuple_append x y) (plus0 m)) /\ b y
  | S n' =>
    match m with
    | 0 => 
      fun a b x =>
        exists (x2 : Tuple (S n')) (y : Tuple 1),
        a y /\ b (_tuple_prepend x2 y) /\ x = (_tuple_join_cast_0plus x2 (plus0b n'))
    | S m' =>
      fun a b x =>
        exists (x1 : Tuple (S m')) (x2 : Tuple (S n')) (y : Atom),
        a (_tuple_append x1 y) /\ b (_tuple_prepend x2 y) /\ x = _tuple_join x1 x2
    end
  end.

Definition ite (a b c : Prop) : Prop :=
  (a /\ b) \/ ((~a) /\ c).

Definition domain {m n : nat} (a : Relation (S m)) (b : Relation ((S m) + (S n))) : Relation ((S m) + (S n)) :=
  fun (x : Tuple ((S m) + (S n))) =>
    exists (x1 : Tuple (S m)) (x2 : Tuple (S n)),
    a x1 /\ b x /\ x = _tuple_join x1 x2.

Definition range {m n : nat} : Relation (m + S n) -> Relation (S n) -> Relation (m + (S n)) :=
  match m with
  | 0 => fun a b => intersect a b
  | S m' => fun a b (x : Tuple ((S m') + (S n))) =>
    exists (x1 : Tuple (S m')) (x2 : Tuple (S n)),
    a x /\ b x2 /\ x = _tuple_join x1 x2
  end.

Inductive tc (a : Relation 2) (x : Tuple 2) : Prop :=
| tc_one : a x -> tc a x
| tc_more y : tc a (fst x, y) -> tc a (y, snd x) -> tc a x.

Inductive rtc (a : Relation 2) (x : Tuple 2) : Prop :=
| rtx_zero : fst x = snd x -> rtc a x
| rtc_some : tc a x -> rtc a x.

(* Built-in relations *)

Definition none : Relation 1 := fun _ => False.
Definition univ : Relation 1 := fun _ => True.
Definition iden : Relation 2 := fun x => _tuple_fst x = _tuple_last x.

(* Cardinality *)
(* FIXME currently incomplete *)

Axiom cardinality : forall (n : nat), Relation n -> nat.

Axiom card_ge1_exists : forall n f, cardinality n f >= 1 -> exists x, f x.

(* Other *)

Definition and_arg {A : Type} (a b : A -> Prop) : A -> Prop := fun x => a x /\ b x.
Definition or_arg {A : Type} (a b : A -> Prop) : A -> Prop := fun x => a x \/ b x.

Definition unique_if {A : Type} (P : A->Prop) := exists x, forall (x':A), P x' -> x=x'.

Fixpoint fst_tuple {n : nat} : Tuple (S n) -> Tuple 1 :=
  match n return (Tuple (S n) -> Tuple 1) with
  | 0 => (fun x => x)
  | S n' => (fun x => fst_tuple (_tuple_hd x))
  end.

Fixpoint lst_tuple {n : nat} : Tuple (S n) -> Tuple 1 :=
  match n return (Tuple (S n) -> Tuple 1) with
  | 0 => (fun x => x)
  | S n' => (fun x => _tuple_last x)
  end.

(******************************************************************************)

Module NatDec.
Definition U := nat.
Lemma eq_dec : forall x y:U, {x = y} + {x <> y}.
decide equality.
Qed.
End NatDec.

Module TupleDec := DecidableEqDep NatDec.

Lemma cast0 : forall y, _tuple_join_cast_plus1 y (plus1 0) = y.
Proof.
  intros y.
  generalize (plus1 0).
  intros p.
  assert (1 = 1) as p' by auto.
  assert (p = p') as H by apply TupleDec.UIP.
  rewrite H in *.
  clear p H.
  unfold _tuple_join_cast_plus1.
  symmetry.
  rewrite (TupleDec.UIP_refl _ p').
  auto.
Qed.

Lemma cast0b : forall n y, _tuple_join_cast_0plus (n:=n) y (plus0b n) = y.
Proof.
  intros n y.
  generalize (plus0b n).
  intros p.
  assert (S n = S n) as p' by auto.
  assert (p = p') as H by apply TupleDec.UIP.
  rewrite H in *.
  clear p H.
  unfold _tuple_join_cast_0plus.
  symmetry.
  rewrite (TupleDec.UIP_refl _ p').
  auto.
Qed.

Lemma cast1 : forall y, _tuple_join_cast_plus1 y (plus1 1) = y.
Proof.
  intros y.
  generalize (plus1 1).
  intros p.
  assert (2 = 2) as p' by auto.
  assert (p = p') as H by apply TupleDec.UIP.
  rewrite H in *.
  clear p H.
  unfold _tuple_join_cast_plus1.
  symmetry.
  rewrite (TupleDec.UIP_refl _ p').
  auto.
Qed.

Lemma cast_n : forall m y pf, _tuple_join_cast_plus1 (m:=m) y pf =
  match pf in (_ = n') return (Tuple n') with
  | eq_refl => y
  end.
Proof.
  intros m y pf.
  unfold _tuple_join_cast_plus1.
  auto.
Qed.

Lemma tuple_join_cast : forall (x y : Atom),
  _tuple_join (m:=1) (n:=0) x y = (x, y).
Proof.
  intros x y.  unfold _tuple_join.  rewrite cast0.  rewrite cast1.  simpl.  auto.
Qed.

Lemma tuple_join_cast_indiv : forall (a b x y : Atom),
  _tuple_join (m:=1) (n:=0) a b = (x, y) ->
  a = x /\ b = y.
Proof.
  intros a b x y H.  rewrite tuple_join_cast in H.  inversion H.  auto.
Qed.

Lemma tuple_append_cast : forall (x : Tuple 1) (y : Atom),
  _tuple_append x y = (x, y).
Proof.
  intros x y.  unfold _tuple_append.  auto.
Qed.

Lemma tuple_prepend_cast : forall (x : Tuple 1) (y : Atom),
  _tuple_prepend x y = (y, x).
Proof.
  intros x y.  unfold _tuple_prepend.  auto.
Qed.
