Inductive bool :=
  | true
  | false.

Definition negb(b: bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Eval compute in negb (negb false).

(* negb (negb b) = b *)

Theorem negb_negb : forall (b: bool), negb (negb b) = b.
Proof.
  intro b.
  destruct b.
  + simpl. reflexivity.
  + simpl. reflexivity.
Qed.

Theorem negb_thrice : forall(b: bool), negb (negb (negb b)) = negb b.
Proof.
  intro b.
  destruct b.
  + simpl. reflexivity.
  + simpl. reflexivity.
Qed.


Definition andb (b1 b2: bool): bool :=
  match b1, b2 with
    | true, true => true
    | false, true => false
    | true, false => false
    | false, false => false
  end.

Theorem andb_true_both_arg_true : forall (b1 b2 : bool), 
  b1 = true -> b2 = true -> andb b1 b2 = true.
Proof.
  intros b1 b2 Hb1 Hb2.
  rewrite Hb1. rewrite Hb2.
  simpl. reflexivity.
Qed.

Theorem andb_true_otherside: forall(b1 b2: bool),
  andb b1 b2 = true -> b1 = true /\ b2 = true. 
Proof. 
  intros b1 b2 Hb.
  destruct b1. 
  destruct b2.
  split.
  reflexivity.
  reflexivity.
  split.
  reflexivity.
  simpl in Hb.
  inversion Hb.
  destruct b2.
  simpl in Hb.
  inversion Hb.
  inversion Hb.
Qed.

Theorem andb_associative: forall(a b c : bool),
  andb a (andb b c) = andb (andb a b) c.
Proof.
 intros [|] [|] [|]; simpl; reflexivity.
 Qed.


Theorem andb_commutative : forall(a b : bool),
  andb a b = andb b a.
Proof.
  intros a b.
  refine(
      match a, b with
        | true, true => eq_refl
        | true, fase => eq_refl
        | false, true => eq_refl
        | false, false =>  eq_refl
      end
    ).
Qed.


Definition orb(b1 b2 : bool) : bool :=
  match b1,b2 with
    | false, false => false
    | _,_ => true
  end.

Theorem andb_negb_orb: forall(a b : bool),
  negb (andb a b) = orb (negb a) (negb b).
Proof.
  intros a b.
  destruct a eqn:Ha.
  destruct b eqn:Hb.
  simpl.reflexivity.
  simpl.reflexivity.
  destruct b eqn:Hb.
  simpl.reflexivity.
  simpl.reflexivity.
Qed.
