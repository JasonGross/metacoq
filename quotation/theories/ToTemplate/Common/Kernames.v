From MetaCoq.Quotation.ToTemplate Require Export Init.
From MetaCoq.Quotation.ToTemplate Require Export (hints) Coq.Init Coq.MSets Coq.FSets bytestring.
From MetaCoq.Common Require Import Kernames.

#[export] Instance quote_modpath : ground_quotable modpath := ltac:(induction 1; exact _).

Module qKername <: QuotationOfOrderedType Kername.
  MetaCoq Run (tmMakeQuotationOfModule false "Kername").
End qKername.
(* Error: Universe inconsistency. Cannot enforce Set =
MetaCoq.Quotation.ToTemplate.Coq.Structures.1 because
MetaCoq.Quotation.ToTemplate.Coq.Structures.1 < KernameSet.E.t.u0
<= MetaCoq.Quotation.ToTemplate.Coq.Structures.1 = Set.*)

(T : OrderedType) (M : MSetAVL.MakeSig T) (Import MOrdProperties : OrdPropertiesSig M) (Import qT : QuotationOfOrderedType T) (Import qM : MSetAVL.QuotationOfMake T M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties qT).

Module QuoteKernameSet := QuoteMSetAVL Kername KernameSet.
Export QuoteKernameSet.Instances.
Module QuoteKernameMap := QuoteFMapAVL Kername.OT KernameMap.
Export QuoteKernameMap.Instances.

#[export] Instance quote_inductive : ground_quotable inductive := ltac:(destruct 1; exact _).
#[export] Instance quote_projection : ground_quotable projection := ltac:(destruct 1; exact _).
#[export] Instance quote_global_reference : ground_quotable global_reference := ltac:(destruct 1; exact _).
