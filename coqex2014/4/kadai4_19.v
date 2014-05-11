Parameter A : Set.
Definition Eq : A -> A -> Prop :=
  (fun a b => forall P : A -> Prop, P a -> P b)
.

Lemma Eq_eq : forall x y, Eq x y <-> x = y.
Proof.
  intros.
  unfold Eq.
  intuition auto.

  apply H.
  reflexivity.
  
  rewrite <-H.
  apply H0.

Qed.