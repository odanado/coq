(* コンストラクタの名前は例えば、SOとSにするとよい。 *)
Inductive pos : Set :=
  | SO : pos
  | S  : pos -> pos
  (* posの定義を書く *) .

Fixpoint plus(n m:pos) : pos := 
  match n with
  | SO => S m
  | S p => S (plus p m)
  end.

Infix "+" := plus.

Theorem plus_assoc : forall n m p, n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
