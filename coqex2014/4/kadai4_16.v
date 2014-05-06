
Definition tautology : forall P : Prop, P -> P
  := fun P x => x.


Definition Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P
  := (fun (P Q : Prop) (H : (Q -> False) /\ (P -> Q)) (H0 : P) =>
 match H with
 | conj H1 H2 => H1 (H2 H0)
 end).

Definition Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q
  := (fun (P Q : Prop) (H : P \/ Q) (H0 : P -> False) =>
 match H with
 | or_introl H1 => match H0 H1 return Q with
                   end
 | or_intror H1 => H1
 end).

Definition tautology_on_Set : forall A : Set, A -> A
  := (fun (A : Set) (H : A) => H).

Definition Modus_tollens_on_Set : forall A B : Set, (B -> Empty_set) * (A -> B) -> (A -> Empty_set)
  := (fun (A B : Set) (H : (B -> Empty_set) * (A -> B)) (H0 : A) =>
 let (e, b) := H in e (b H0)).

Definition Disjunctive_syllogism_on_Set : forall A B : Set, (A + B) -> (A -> Empty_set) -> B
  := (fun (A B : Set) (H : A + B) (H0 : A -> Empty_set) =>
 match H with
 | inl a => match H0 a return B with
            end
 | inr b => b
 end).
