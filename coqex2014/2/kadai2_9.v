Require Import Arith.

Goal forall n m : nat, (n + m) * (n + m) = n * n + m * m + 2 * n * m.
Proof.
  intros.
  rewrite mult_plus_distr_r.

  assert (2 * n * m = n * m + n * m).
  simpl.
  rewrite plus_assoc.
  rewrite NPeano.Nat.add_0_r.
  rewrite mult_plus_distr_r.
  reflexivity.  

  rewrite H.
  rewrite plus_assoc.

  assert ( n * n + m * m + n * m = n * n + n * m + m * m ).
  apply NPeano.Nat.add_shuffle0.
  rewrite H0.

  rewrite <-mult_plus_distr_l.

  assert ( m * (n + m) = m * m + n * m ).
  rewrite plus_comm.
  rewrite mult_comm.
  rewrite mult_plus_distr_r.
  reflexivity.
  rewrite H1.

  rewrite plus_assoc.
  reflexivity.

Qed.

Goal forall n m p q : nat, (n + m) + (p + q) = (n + p) + (m + q).
Proof.
  intros.
  apply plus_permute_2_in_4.
Qed.