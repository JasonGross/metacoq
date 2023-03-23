From MetaCoq.Common Require Import Environment EnvironmentTyping.
From MetaCoq.Quotation.ToTemplate Require Import Init.

Module Type QuotationOfLookup (T : Term) (E : EnvironmentSig T) (L : LookupSig T E).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "L").
End QuotationOfLookup.
Locate Module TermUtils.
Module Type QuotationOfEnvTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E).

Module Type QuoteTerm (T : Term).
  #[export] Declare Instance quote_term : ground_quotable T.term.
End QuoteTerm.

Module Type QuotationOfEnvironment (T : Term) (Import E : EnvironmentSig T).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "E").
End QuotationOfEnvironment.
