From MetaCoq.Common Require Import Environment.
From MetaCoq.Quotation.ToTemplate Require Export Init.

Module Type QuotationOfTerm (T : Term).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "T").
End QuotationOfTerm.

Module Type QuoteTerm (T : Term).
  #[export] Declare Instance quote_term : ground_quotable T.term.
End QuoteTerm.

Module Type QuotationOfEnvironment (T : Term) (Import E : EnvironmentSig T).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "E").
End QuotationOfEnvironment.
