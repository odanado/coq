Theorem DeMorgan3 : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
unfold not.
Proof.
  intros.
  split.
  intros.
  apply H.
  left.
  apply H0.

  intros.
  apply H.
  right.
  apply H0.
Qed.
Theorem DeMorgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
unfold not.
Proof.
  intros.
  destruct H.
  destruct H0.
  apply H.
  apply H0.
  apply H1.
  apply H0.


Qed.

Theorem DeMorgan1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
unfold not.
Proof.
  intros.
  destruct H0.
  destruct H.
  apply H.
  apply H0.
  apply H.
  apply H1.
Qed.
