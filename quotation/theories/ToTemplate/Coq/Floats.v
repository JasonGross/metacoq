From Coq.Floats Require Import FloatClass Floats PrimFloat SpecFloat.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate Require Import (hints) Coq.Init Coq.Numbers.

#[export] Instance quote_float : ground_quotable float := Ast.tFloat.
#[export] Instance quote_float_class : ground_quotable float_class := ltac:(destruct 1; exact _).
#[export] Instance quote_float_comparison : ground_quotable float_comparison := ltac:(destruct 1; exact _).
#[export] Instance quote_float_wrapper : ground_quotable float_wrapper := ltac:(destruct 1; exact _).
#[export] Instance quote_spec_float : ground_quotable spec_float := ltac:(destruct 1; exact _).
#[export] Instance quote_location : ground_quotable location := ltac:(destruct 1; exact _).
#[export] Instance quote_shr_record : ground_quotable shr_record := ltac:(destruct 1; exact _).
