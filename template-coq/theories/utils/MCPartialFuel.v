Require Import Coq.Init.Wf.
Local Set Implicit Arguments.
Variant PartiallyFueled {R : Prop} {A} := finished (_ : A) | needs_acc (_ : R -> A).
Arguments PartiallyFueled : clear implicits.
Definition partially_fueled_bind {R A A'} (v : PartiallyFueled R A) (k : A -> PartiallyFueled R A') : PartiallyFueled R A'
  := match v with
     | finished v => k v
     | needs_acc f
       => needs_acc (fun acc => match k (f acc) with
                                | finished v => v
                                | needs_acc f' => f' acc
                                end)
     end.
Definition partially_fueled_bind_inspect {R A A'} (v : PartiallyFueled R A) (k : { y : A | finished y = v \/ exists f, needs_acc f = v /\ exists acc, y = f acc } -> PartiallyFueled R A') : PartiallyFueled R A'
  := match exist _ v eq_refl : { y | y = v } with
     | exist _ (finished v) eq => k (exist _ v (or_introl eq))
     | exist _ (needs_acc f) eq
       => needs_acc (fun acc => match k (exist _ (f acc) (or_intror (ex_intro _ f (conj eq (ex_intro _ acc eq_refl))))) with
                                | finished v => v
                                | needs_acc f' => f' acc
                                end)
     end.
Definition fully_fuel {R:Prop} {A} (r : R) (v : PartiallyFueled R A) : A
  := match v with
     | finished v => v
     | needs_acc f => f r
     end.

Definition Fix_fueled {A} {R : A -> A -> Prop} (P : A -> Type)
           (F : forall x : A, (forall y : A, R y x -> PartiallyFueled (well_founded R) (P y)) -> PartiallyFueled (well_founded R) (P x))
  : forall (x : A) (fuel : nat), PartiallyFueled (well_founded R) (P x)
  := fix Fix_fueled (x : A) (fuel : nat) : PartiallyFueled (well_founded R) (P x)
    := F x (fun y _ => match fuel with
                       | O => needs_acc (fun rwf => @Fix A R rwf P (fun x f => fully_fuel rwf (F x (fun y h => finished (f y h)))) y)
                       | S fuel' => Fix_fueled y fuel'
                       end).
