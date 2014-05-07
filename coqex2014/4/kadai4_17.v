Theorem hoge : forall P Q R : Prop, P \/ ~(Q \/ R) -> (P \/ ~Q) /\ (P \/ ~R).
Proof.
  (* 例 : 最初の1行は refine (fun P Q R => _). に置き換えられる *)
  refine (fun P Q R => _).
  refine (fun H => _).
  refine (match H with
  | or_introl HP => _
  | or_intror HnQR => _ end).
  - refine (conj _ _).
    + refine (or_introl _ _).
      refine (HP ).
    + refine (or_introl _ _).
      refine (HP).
  - refine (conj _ _).
    + refine (or_intror _ _).
      refine (fun HQ => _).
      refine (HnQR _).
      refine (or_introl _ _).
      refine (HQ).
    + refine (or_intror _ _).
      refine (fun HR => _).
      refine (HnQR _).
      refine (or_intror _ _).
      refine (HR).
Qed.