From Coq.FSets Require Import FMapList.
From Coq.Structures Require Import Equalities OrdersAlt.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.Structures Require Import OrdersAlt.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module FMapList.
  Module Type RawSig (T : OrderedTypeOrig) := Nop <+ FMapList.Raw T.

  Module Type QuotationOfRaw (T : OrderedTypeOrig) (M : RawSig T).
    Module qMX := Nop <+ QuotationOfOrderedTypeOrigFacts T M.MX.
    Module qPX := Nop <+ QuotationOfKeyOrderedTypeOrig T M.PX.
    Export (hints) qMX qPX.
    MetaCoq Run (tmDeclareQuotationOfModule (all_submodules_except [["MX"]; ["PX"]]%bs) (Some export) "M").
  End QuotationOfRaw.
End FMapList.
