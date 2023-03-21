From MetaCoq.Quotation.ToTemplate Require Import Coq.Init.
From MetaCoq.Utils Require Import All_Forall.

#[export] Instance quote_All {A R ls} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x, ground_quotable (R x)} : ground_quotable (@All A R ls) := ltac:(induction 1; exact _).
#[export] Instance quote_Alli {A P n ls} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall n x, ground_quotable (P n x)} : ground_quotable (@Alli A P n ls) := ltac:(induction 1; exact _).
#[export] Instance quote_All2 {A B R lsA lsB} {qA : quotation_of A} {qB : quotation_of B} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteR : forall x y, ground_quotable (R x y)} : ground_quotable (@All2 A B R lsA lsB) := ltac:(induction 1; exact _).
#[export] Instance quote_All2i {A B R n lsA lsB} {qA : quotation_of A} {qB : quotation_of B} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteR : forall n x y, ground_quotable (R n x y)} : ground_quotable (@All2i A B R n lsA lsB) := ltac:(induction 1; exact _).
#[export] Instance quote_All3 {A B C R lsA lsB lsC} {qA : quotation_of A} {qB : quotation_of B} {qB : quotation_of C} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteC : ground_quotable C} {quoteR : forall x y z, ground_quotable (R x y z)} : ground_quotable (@All3 A B C R lsA lsB lsC) := ltac:(induction 1; exact _).
#[export] Instance quote_OnOne2 {A R lsA lsB} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} : ground_quotable (@OnOne2 A R lsA lsB) := ltac:(induction 1; exact _).
#[export] Instance quote_OnOne2i {A R n lsA lsB} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall n x y, ground_quotable (R n x y)} : ground_quotable (@OnOne2i A R n lsA lsB) := ltac:(induction 1; exact _).
#[export] Instance quote_OnOne2All {A B P lsB lsA1 lsA2} {qA : quotation_of A} {qB : quotation_of B} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteP : forall b x y, ground_quotable (P b x y)} : ground_quotable (@OnOne2All A B P lsB lsA1 lsA2) := ltac:(induction 1; exact _).
#[export] Instance quote_All2i_len {A B R lsA lsB} {qA : quotation_of A} {qB : quotation_of B} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteR : forall n x y, ground_quotable (R n x y)} : ground_quotable (@All2i_len A B R lsA lsB) := ltac:(induction 1; exact _).
#[export] Instance quote_All_fold {A P ls} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x y, ground_quotable (P x y)} : ground_quotable (@All_fold A P ls) := ltac:(induction 1; exact _).
#[export] Instance quote_All2_fold {A P ls1 ls2} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x y z w, ground_quotable (P x y z w)} : ground_quotable (@All2_fold A P ls1 ls2) := ltac:(induction 1; exact _).
