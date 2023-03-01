From MetaCoq.Quotation.ToTemplate Require Export Init.
From MetaCoq.Quotation.ToTemplate.Coq Require Export (hints) Init MSets.
From MetaCoq.Quotation.ToTemplate.Utils Require Export (hints) MCOption bytestring.
From MetaCoq.Quotation.ToTemplate.Common Require Export (hints) BasicAst config.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import Universes.Instances.
From MetaCoq.Common Require Import Kernames Universes UniversesDec.
From MetaCoq.Utils Require Import bytestring monad_utils.
From MetaCoq.Template Require Import Loader TemplateMonad.

Local Open Scope bs.
Import MCMonadNotation.

(* Grrr, [valuation]s cause so much trouble, because they're not quotable *)
(*
Record valuation :=
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat }.
Class Evaluable (A : Type) := val : valuation -> A -> nat.
 *)

Module QuoteLevelSet := MSets.QuoteMSetAVL Level LevelSet LevelSetOrdProp qLevel qLevelSet qLevelSetOrdProp.
Export (hints) QuoteLevelSet.
Module QuoteLevelExprSet := MSets.QuoteMSetListWithLeibniz LevelExpr LevelExprSet LevelExprSetOrdProp qLevelExpr qLevelExprSet qLevelExprSetOrdProp.
Export (hints) QuoteLevelExprSet.
Module QuoteConstraintSet := MSets.QuoteMSetAVL UnivConstraint ConstraintSet ConstraintSetOrdProp qUnivConstraint qConstraintSet qConstraintSetOrdProp.
Export (hints) QuoteConstraintSet.

Module QuoteUniverses1.
  Module Import Level.
    #[export] Instance quote_t : ground_quotable Level.t := ltac:(destruct 1; exact _).
    #[export] Instance quote_lt {x y} : ground_quotable (Level.lt x y).
    Proof.
      destruct x, y;
        solve [ intro pf; exfalso; inversion pf
              | adjust_ground_quotable_by_econstructor_inversion () ].
    Defined.
  End Level.
  Export (hints) Level.

  Module Import PropLevel.
    #[export] Instance quote_t : ground_quotable PropLevel.t := ltac:(destruct 1; exact _).
    #[export] Instance quote_lt {x y} : ground_quotable (PropLevel.lt x y).
    Proof.
      destruct x, y;
        solve [ intro pf; exfalso; inversion pf
              | adjust_ground_quotable_by_econstructor_inversion () ].
    Defined.
  End PropLevel.
  Export (hints) PropLevel.

  Module Import LevelExpr.
    #[export] Instance quote_t : ground_quotable LevelExpr.t := _.
    #[export] Typeclasses Opaque LevelExpr.t.
    #[export] Instance quote_lt {x y} : ground_quotable (LevelExpr.lt x y)
      := ground_quotable_of_dec (@LevelExprSet.Raw.MX.lt_dec x y).
  End LevelExpr.
  Export (hints) LevelExpr.
End QuoteUniverses1.
Export (hints) QuoteUniverses1.

#[export] Instance quote_nonEmptyLevelExprSet : ground_quotable nonEmptyLevelExprSet := ltac:(destruct 1; exact _).

#[export] Instance quote_concreteUniverses : ground_quotable concreteUniverses := ltac:(destruct 1; exact _).
Import StrongerInstances.
#[export] Instance quote_leq_cuniverse_n {cf n u u'} : ground_quotable (@leq_cuniverse_n cf n u u') := ltac:(cbv [leq_cuniverse_n]; exact _).
#[export] Typeclasses Opaque leq_cuniverse_n.
#[export] Instance quote_is_uprop {u} : ground_quotable (@is_uprop u) := ltac:(cbv [is_uprop]; exact _).
#[export] Typeclasses Opaque is_uprop.
#[export] Instance quote_is_usprop {u} : ground_quotable (@is_usprop u) := ltac:(cbv [is_usprop]; exact _).
#[export] Instance quote_is_uproplevel {u} : ground_quotable (@is_uproplevel u) := ltac:(cbv [is_uproplevel]; exact _).
#[export] Typeclasses Opaque is_uproplevel.
#[export] Instance quote_is_uproplevel_or_set {u} : ground_quotable (@is_uproplevel_or_set u) := ltac:(cbv [is_uproplevel_or_set]; exact _).
#[export] Typeclasses Opaque is_uproplevel_or_set.
#[export] Instance quote_is_utype {u} : ground_quotable (@is_utype u) := ltac:(cbv [is_utype]; exact _).
#[export] Typeclasses Opaque is_utype.

#[export] Instance quote_allowed_eliminations : ground_quotable allowed_eliminations := ltac:(destruct 1; exact _).
#[export] Instance quote_is_allowed_elimination_cuniv {allowed u} : ground_quotable (is_allowed_elimination_cuniv allowed u) := ltac:(destruct allowed; exact _).
#[export] Typeclasses Opaque is_allowed_elimination_cuniv.

Module QuoteUniverses2.
  Module Import Universe.
    #[export] Instance quote_t : ground_quotable Universe.t := ltac:(destruct 1; exact _).
    #[local] Hint Constructors or eq : typeclass_instances.
    #[export] Instance quote_on_sort {P def s} {quoteP : forall l, s = Universe.lType l -> ground_quotable (P l:Prop)} {quote_def : s = Universe.lProp \/ s = Universe.lSProp -> ground_quotable (def:Prop)} : ground_quotable (@Universe.on_sort P def s) := ltac:(cbv [Universe.on_sort]; exact _).
    #[export] Typeclasses Opaque Universe.on_sort.
  End Universe.
  Export (hints) Universe.

  Module Import ConstraintType.
    #[export] Instance quote_t : ground_quotable ConstraintType.t := ltac:(destruct 1; exact _).

    #[export] Instance quote_lt {x y} : ground_quotable (ConstraintType.lt x y).
    Proof.
      destruct x, y;
        solve [ intro pf; exfalso; inversion pf
              | adjust_ground_quotable_by_econstructor_inversion () ].
    Defined.
  End ConstraintType.
  Export (hints) ConstraintType.

  Module Import UnivConstraint.
    #[export] Instance quote_t : ground_quotable UnivConstraint.t := _.
    #[export] Typeclasses Opaque UnivConstraint.t.
    #[export] Instance quote_lt {x y} : ground_quotable (UnivConstraint.lt x y)
    := ground_quotable_of_dec (@ConstraintSet.Raw.MX.lt_dec x y).
  End UnivConstraint.
  Export (hints) UnivConstraint.

  Module Import Variance.
    #[export] Instance quote_t : ground_quotable Variance.t := ltac:(destruct 1; exact _).
  End Variance.
  Export (hints) Variance.
End QuoteUniverses2.
Export (hints) QuoteUniverses2.

#[export] Instance quote_declared_cstr_levels {levels cstr} : ground_quotable (declared_cstr_levels levels cstr)
  := ltac:(cbv [declared_cstr_levels]; exact _).
#[export] Typeclasses Opaque declared_cstr_levels.
#[export] Instance quote_universes_decl : ground_quotable universes_decl := ltac:(destruct 1; exact _).
#[export] Instance quote_satisfies0 {v s} {qv : quotation_of v} : ground_quotable (@satisfies0 v s)
  := ground_quotable_of_iff (iff_sym (@uGraph.gc_of_constraint_spec config.default_checker_flags v s)).
#[export] Instance quote_satisfies {v s} {qv : quotation_of v} : ground_quotable (@satisfies v s)
  := ground_quotable_of_iff (iff_sym (@uGraph.gc_of_constraints_spec config.default_checker_flags v s)).
#[export] Typeclasses Opaque satisfies.
#[export] Instance quote_consistent {ctrs} : ground_quotable (@consistent ctrs)
  := ground_quotable_of_dec (@consistent_dec ctrs).
#[export] Typeclasses Opaque consistent.
#[export] Instance quote_consistent_extension_on {cs cstr} : ground_quotable (@consistent_extension_on cs cstr)
  := ground_quotable_of_dec (@consistent_extension_on_dec cs cstr).
#[export] Typeclasses Opaque consistent_extension_on.
#[export] Instance quote_leq_levelalg_n {cf n ϕ u u'} : ground_quotable (@leq_levelalg_n cf (uGraph.Z_of_bool n) ϕ u u')
  := ground_quotable_of_dec (@leq_levelalg_n_dec cf _ ϕ u u').
#[export] Typeclasses Opaque leq_levelalg_n uGraph.Z_of_bool.
#[export] Instance quote_leq_universe_n_ {cf CS leq_levelalg_n n ϕ s s'} {quote_leq_levelalg_n : forall u u', ground_quotable (leq_levelalg_n n ϕ u u':Prop)} : ground_quotable (@leq_universe_n_ cf CS leq_levelalg_n n ϕ s s') := ltac:(cbv [leq_universe_n_]; exact _).
#[export] Typeclasses Opaque leq_universe_n_.
#[export] Instance quote_leq_universe_n {cf n ϕ s s'} : ground_quotable (@leq_universe_n cf (uGraph.Z_of_bool n) ϕ s s') := _.
#[export] Typeclasses Opaque leq_universe_n.
#[export] Instance quote_leq_universe {cf ϕ s s'} : ground_quotable (@leq_universe cf ϕ s s') := @quote_leq_universe_n cf false ϕ s s'.
#[export] Typeclasses Opaque leq_universe.
#[export] Instance quote_eq_levelalg {cf ϕ u u'} : ground_quotable (@eq_levelalg cf ϕ u u')
  := ground_quotable_of_dec (@eq_levelalg_dec cf ϕ u u').
#[export] Typeclasses Opaque eq_levelalg.
#[export] Instance quote_eq_universe_ {CS eq_levelalg ϕ s s'} {quote_eq_levelalg : forall u u', ground_quotable (eq_levelalg ϕ u u':Prop)} : ground_quotable (@eq_universe_ CS eq_levelalg ϕ s s') := ltac:(cbv [eq_universe_]; exact _).
#[export] Typeclasses Opaque eq_universe_.
#[export] Instance quote_eq_universe {cf ϕ s s'} : ground_quotable (@eq_universe cf ϕ s s') := _.
#[export] Typeclasses Opaque eq_universe.
#[export] Instance quote_compare_universe {cf pb ϕ u u'} : ground_quotable (@compare_universe cf pb ϕ u u') := ltac:(destruct pb; exact _).
#[export] Typeclasses Opaque compare_universe.
#[export] Instance quote_valid_constraints0 {ϕ ctrs} : ground_quotable (@valid_constraints0 ϕ ctrs)
  := ground_quotable_of_dec (@valid_constraints0_dec ϕ ctrs).
#[export] Typeclasses Opaque valid_constraints0.
#[export] Instance quote_valid_constraints {cf ϕ ctrs} : ground_quotable (@valid_constraints cf ϕ ctrs)
  := ground_quotable_of_dec (@valid_constraints_dec cf ϕ ctrs).
#[export] Typeclasses Opaque valid_constraints.
#[export] Instance quote_is_lSet {cf φ s} : ground_quotable (@is_lSet cf φ s) := _.
#[export] Typeclasses Opaque is_lSet.
#[export] Instance quote_is_allowed_elimination {cf ϕ allowed u} : ground_quotable (@is_allowed_elimination cf ϕ allowed u)
  := ground_quotable_of_dec (@is_allowed_elimination_dec cf ϕ allowed u).
#[export] Typeclasses Opaque is_allowed_elimination.

#[export] Instance quote_universes_entry : ground_quotable universes_entry := ltac:(destruct 1; exact _).
