Theorem NotNot_LEM : forall P : Prop, ~ ~(P \/ ~P).
unfold not.
Proof.
  intros.
  apply H.
  right.
  intro.
  apply H.
  left.
  apply H0.
  
Qed.