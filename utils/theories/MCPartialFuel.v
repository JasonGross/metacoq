Require Import Coq.Init.Wf.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Wellfounded.Inclusion.
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
Definition map_acc {R1 R2 : Prop} (F : R2 -> R1) {A} (v : PartiallyFueled R1 A) : PartiallyFueled R2 A
  := match v with
     | finished v => finished v
     | needs_acc f => needs_acc (fun acc => f (F acc))
     end.

Definition Fix_fueled {A} {R : A -> A -> Prop} (P : A -> Type) (Q : forall x : A, P x -> Type)
           (F : forall (x : A) (p : P x), (forall (y : A) (q : P y), R y x -> PartiallyFueled (well_founded R) (Q y q)) -> PartiallyFueled (well_founded R) (Q x p))
  : forall (x : A) (p : P x) (fuel : nat), PartiallyFueled (well_founded R) (Q x p)
  := fix Fix_fueled (x : A) (p : P x) (fuel : nat) : PartiallyFueled (well_founded R) (Q x p)
    := F x p (fun y q _
              => match fuel with
                 | O => needs_acc
                          (fun rwf
                           => @Fix A R rwf (fun a => forall (p : P a), Q a p)
                                   (fun x f p => fully_fuel rwf (F x p (fun y q h => finished (f y h q))))
                                   y q)
                 | S fuel' => Fix_fueled y q fuel'
                 end).

Definition Fix_fueled_simple {A} {R : A -> A -> Prop} (P : A -> Type)
           (F : forall x : A, (forall y : A, R y x -> PartiallyFueled (well_founded R) (P y)) -> PartiallyFueled (well_founded R) (P x))
  : forall (x : A) (fuel : nat), PartiallyFueled (well_founded R) (P x)
  := fun x => @Fix_fueled A R (fun _ => unit) (fun x _ => P x) (fun x _ rec => F x ltac:(auto with nocore)) x tt.

Definition on_PartiallyFueled {R A} (P : A -> Prop) (v : PartiallyFueled R A) : Prop
  := match v with
     | finished v => P v
     | needs_acc f => forall acc, P (f acc)
     end.
Definition on_partially_fueled {R A} (P : A -> Type) (v : PartiallyFueled R A) : Type
  := match v with
     | finished v => P v
     | needs_acc f => forall acc, P (f acc)
     end.
