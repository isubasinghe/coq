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
