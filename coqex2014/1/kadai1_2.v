Theorem Modus_toolens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P.
unfold not.
Proof.
  intros.
  apply H.
  intros.
  destruct H.
  apply H1.
  apply H0.
Qed.