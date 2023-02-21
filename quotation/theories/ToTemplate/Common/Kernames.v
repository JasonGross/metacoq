From MetaCoq.Quotation.ToTemplate Require Export Init.
From MetaCoq.Quotation.ToTemplate Require Export (hints) Coq.Init Coq.Structures Coq.MSets Coq.FSets bytestring.
From MetaCoq.Common Require Import Kernames.

#[export] Instance quote_modpath : ground_quotable modpath := ltac:(induction 1; exact _).
From MetaCoq.Utils Require Export bytestring.
From MetaCoq.Utils Require Import utils MCList.
From MetaCoq.Template Require Import MonadBasicAst MonadAst TemplateMonad Ast Loader.
From MetaCoq.Quotation Require Export CommonUtils.
Require Import Equations.Prop.Classes.
Require Import Coq.Lists.List.
Import ListNotations.

Local Set Primitive Projections.
Local Open Scope bs.
Import MCMonadNotation.


Module qKername <: QuotationOfOrderedType Kername.
  MetaCoq Run (tmMakeQuotationOfModule false "Kername").
  Module qOT <: QuotationOfOrderedTypeOrig Kername.OT.
    Module M. Include Kername.OT. End M.
    Goal True.

      run_template_program (tmQuoteModule "M"%bs) (fun v => pose v).
    MetaCoq Run (tmMakeQuotationOfModule false "Kername.OT").
    Print Kername.OT
  End qOT.
End qKername.
Module qKernameSet <: MSetAVL.QuotationOfMake Kername KernameSet.
  MetaCoq Run (tmMakeQuotationOfModule false "KernameSet").
End qKername.
Fail Check KernameSetOrdProp.gtb.
Module KernameSetOrdProp := MSetProperties.OrdProperties KernameSet.
Module qKernameSetOrdProp <: MSets.QuotationOfOrdProperties KernameSet KernameSetOrdProp qKername.
  Module qME := QuotationOfOrderedTypeFacts KernameSet.E KernameSetOrdProp.ME qKernameSet.
  (*Module qML := QuotationOfOrderedTypeLists M.E F.ML.*)
  Module qP <: MSets.QuotationOfWProperties KernameSet KernameSetOrdProp.P.
    MetaCoq Run (tmMakeQuotationOfModule false "KernameSetOrdProp.P").
  End qP.
  MetaCoq Run (tmMakeQuotationOfModule false "KernameSetOrdProp").
End qKernameSetOrdProp.
Module qKernameMap <: FMapAVL.QuotationOfMake Kername.OT KernameMap qKername.qOT.
  Module qRaw.
    MetaCoq Run (tmMakeQuotationOfModule false "KernameMap.Raw").
  End qRaw.
  MetaCoq Run (tmMakeQuotationOfModule false "KernameMap").
End qKernameMap.
Module qKernameMapFact <: QuotationOfWFacts_fun Kername.OT KernameMap KernameMapFact.
  MetaCoq Run (tmMakeQuotationOfModule false "KernameMapFact").
End qKernameMapFact.

Module QuoteKernameSet := QuoteMSetAVL Kername KernameSet KernameSetOrdProp qKername qKernameSet qKernameSetOrdProp.
Export (hints) QuoteKernameSet.
Module QuoteKernameMap := QuoteFMapAVL Kername.OT KernameMap KernameMapFact qKername.qOT qKernameMap qKernameMapFact.
Export (hints) QuoteKernameMap.

#[export] Instance quote_inductive : ground_quotable inductive := ltac:(destruct 1; exact _).
#[export] Instance quote_projection : ground_quotable projection := ltac:(destruct 1; exact _).
#[export] Instance quote_global_reference : ground_quotable global_reference := ltac:(destruct 1; exact _).
