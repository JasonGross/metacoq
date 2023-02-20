From Coq Require Import Structures.Equalities FMapInterface FMapList FMapAVL FMapFullAVL FMapFacts.
From MetaCoq.Utils Require Import MCUtils.
From MetaCoq.Quotation.ToTemplate Require Export Init.
From MetaCoq.Quotation.ToTemplate Require Export (hints) Coq.Numbers Coq.Init Coq.Lists Coq.Structures.
From MetaCoq.Quotation.ToTemplate Require Import Coq.Structures.

Module Type QuotationOfWSfun (E : DecidableTypeOrig) (Import M : WSfun E).
  #[export] Declare Instance qkey : quotation_of M.key.
  #[export] Declare Instance qt : quotation_of M.t.
  #[export] Declare Instance qempty : quotation_of M.empty.
  #[export] Declare Instance qis_empty : quotation_of M.is_empty.
  #[export] Declare Instance qadd : quotation_of M.add.
  #[export] Declare Instance qfind : quotation_of M.find.
  #[export] Declare Instance qremove : quotation_of M.remove.
  #[export] Declare Instance qmem : quotation_of M.mem.
  #[export] Declare Instance qmap : quotation_of M.map.
  #[export] Declare Instance qmapi : quotation_of M.mapi.
  #[export] Declare Instance qmap2 : quotation_of M.map2.
  #[export] Declare Instance qelements : quotation_of M.elements.
  #[export] Declare Instance qcardinal : quotation_of M.cardinal.
  #[export] Declare Instance qfold : quotation_of M.fold.
  #[export] Declare Instance qequal : quotation_of M.equal.
  #[export] Declare Instance qMapsTo : quotation_of M.MapsTo.
  #[export] Declare Instance qIn : quotation_of M.In.
  #[export] Declare Instance qEmpty : quotation_of M.Empty.
  #[export] Declare Instance qeq_key : quotation_of M.eq_key.
  #[export] Declare Instance qeq_key_elt : quotation_of M.eq_key_elt.
  #[export] Declare Instance qMapsTo_1 : quotation_of M.MapsTo_1.
  #[export] Declare Instance qmem_1 : quotation_of M.mem_1.
  #[export] Declare Instance qmem_2 : quotation_of M.mem_2.
  #[export] Declare Instance qempty_1 : quotation_of M.empty_1.
  #[export] Declare Instance qis_empty_1 : quotation_of M.is_empty_1.
  #[export] Declare Instance qis_empty_2 : quotation_of M.is_empty_2.
  #[export] Declare Instance qadd_1 : quotation_of M.add_1.
  #[export] Declare Instance qadd_2 : quotation_of M.add_2.
  #[export] Declare Instance qadd_3 : quotation_of M.add_3.
  #[export] Declare Instance qremove_1 : quotation_of M.remove_1.
  #[export] Declare Instance qremove_2 : quotation_of M.remove_2.
  #[export] Declare Instance qremove_3 : quotation_of M.remove_3.
  #[export] Declare Instance qfind_1 : quotation_of M.find_1.
  #[export] Declare Instance qfind_2 : quotation_of M.find_2.
  #[export] Declare Instance qelements_1 : quotation_of M.elements_1.
  #[export] Declare Instance qelements_2 : quotation_of M.elements_2.
  #[export] Declare Instance qelements_3w : quotation_of M.elements_3w.
  #[export] Declare Instance qcardinal_1 : quotation_of M.cardinal_1.
  #[export] Declare Instance qfold_1 : quotation_of M.fold_1.
  #[export] Declare Instance qEqual : quotation_of M.Equal.
  #[export] Declare Instance qEquiv : quotation_of M.Equiv.
  #[export] Declare Instance qEquivb : quotation_of M.Equivb.
  #[export] Declare Instance qequal_1 : quotation_of M.equal_1.
  #[export] Declare Instance qequal_2 : quotation_of M.equal_2.
  #[export] Declare Instance qmap_1 : quotation_of M.map_1.
  #[export] Declare Instance qmap_2 : quotation_of M.map_2.
  #[export] Declare Instance qmapi_1 : quotation_of M.mapi_1.
  #[export] Declare Instance qmapi_2 : quotation_of M.mapi_2.
  #[export] Declare Instance qmap2_1 : quotation_of M.map2_1.
  #[export] Declare Instance qmap2_2 : quotation_of M.map2_2.
End QuotationOfWSfun.

Module Type WFacts_funSig (E : DecidableTypeOrig) (M : WSfun E) := Nop <+ WFacts_fun E M.

Module Type QuotationOfWFacts_fun (E : DecidableTypeOrig) (M : WSfun E) (F : WFacts_funSig E M).
  #[export] Declare Instance qeqb : quotation_of F.eqb.
  #[export] Declare Instance qeq_bool_alt : quotation_of F.eq_bool_alt.
  #[export] Declare Instance qeq_option_alt : quotation_of F.eq_option_alt.
  #[export] Declare Instance qMapsTo_fun : quotation_of F.MapsTo_fun.
  #[export] Declare Instance qIn_iff : quotation_of F.In_iff.
  #[export] Declare Instance qMapsTo_iff : quotation_of F.MapsTo_iff.
  #[export] Declare Instance qmem_in_iff : quotation_of F.mem_in_iff.
  #[export] Declare Instance qnot_mem_in_iff : quotation_of F.not_mem_in_iff.
  #[export] Declare Instance qIn_dec : quotation_of F.In_dec.
  #[export] Declare Instance qfind_mapsto_iff : quotation_of F.find_mapsto_iff.
  #[export] Declare Instance qnot_find_in_iff : quotation_of F.not_find_in_iff.
  #[export] Declare Instance qin_find_iff : quotation_of F.in_find_iff.
  #[export] Declare Instance qequal_iff : quotation_of F.equal_iff.
  #[export] Declare Instance qempty_mapsto_iff : quotation_of F.empty_mapsto_iff.
  #[export] Declare Instance qempty_in_iff : quotation_of F.empty_in_iff.
  #[export] Declare Instance qis_empty_iff : quotation_of F.is_empty_iff.
  #[export] Declare Instance qadd_mapsto_iff : quotation_of F.add_mapsto_iff.
  #[export] Declare Instance qadd_in_iff : quotation_of F.add_in_iff.
  #[export] Declare Instance qadd_neq_mapsto_iff : quotation_of F.add_neq_mapsto_iff.
  #[export] Declare Instance qadd_neq_in_iff : quotation_of F.add_neq_in_iff.
  #[export] Declare Instance qremove_mapsto_iff : quotation_of F.remove_mapsto_iff.
  #[export] Declare Instance qremove_in_iff : quotation_of F.remove_in_iff.
  #[export] Declare Instance qremove_neq_mapsto_iff : quotation_of F.remove_neq_mapsto_iff.
  #[export] Declare Instance qremove_neq_in_iff : quotation_of F.remove_neq_in_iff.
  #[export] Declare Instance qelements_mapsto_iff : quotation_of F.elements_mapsto_iff.
  #[export] Declare Instance qelements_in_iff : quotation_of F.elements_in_iff.
  #[export] Declare Instance qmap_mapsto_iff : quotation_of F.map_mapsto_iff.
  #[export] Declare Instance qmap_in_iff : quotation_of F.map_in_iff.
  #[export] Declare Instance qmapi_in_iff : quotation_of F.mapi_in_iff.
  #[export] Declare Instance qmapi_inv : quotation_of F.mapi_inv.
  #[export] Declare Instance qmapi_1bis : quotation_of F.mapi_1bis.
  #[export] Declare Instance qmapi_mapsto_iff : quotation_of F.mapi_mapsto_iff.
  #[export] Declare Instance qmem_find_b : quotation_of F.mem_find_b.
  #[export] Declare Instance qmem_b : quotation_of F.mem_b.
  #[export] Declare Instance qfind_o : quotation_of F.find_o.
  #[export] Declare Instance qempty_o : quotation_of F.empty_o.
  #[export] Declare Instance qempty_a : quotation_of F.empty_a.
  #[export] Declare Instance qadd_eq_o : quotation_of F.add_eq_o.
  #[export] Declare Instance qadd_neq_o : quotation_of F.add_neq_o.
  #[export] Declare Instance qadd_o : quotation_of F.add_o.
  #[export] Declare Instance qadd_eq_b : quotation_of F.add_eq_b.
  #[export] Declare Instance qadd_neq_b : quotation_of F.add_neq_b.
  #[export] Declare Instance qadd_b : quotation_of F.add_b.
  #[export] Declare Instance qremove_eq_o : quotation_of F.remove_eq_o.
  #[export] Declare Instance qremove_neq_o : quotation_of F.remove_neq_o.
  #[export] Declare Instance qremove_o : quotation_of F.remove_o.
  #[export] Declare Instance qremove_eq_b : quotation_of F.remove_eq_b.
  #[export] Declare Instance qremove_neq_b : quotation_of F.remove_neq_b.
  #[export] Declare Instance qremove_b : quotation_of F.remove_b.
  #[export] Declare Instance qmap_o : quotation_of F.map_o.
  #[export] Declare Instance qmap_b : quotation_of F.map_b.
  #[export] Declare Instance qmapi_b : quotation_of F.mapi_b.
  #[export] Declare Instance qmapi_o : quotation_of F.mapi_o.
  #[export] Declare Instance qmap2_1bis : quotation_of F.map2_1bis.
  #[export] Declare Instance qelements_o : quotation_of F.elements_o.
  #[export] Declare Instance qelements_b : quotation_of F.elements_b.
  #[export] Declare Instance qEqual_mapsto_iff : quotation_of F.Equal_mapsto_iff.
  #[export] Declare Instance qEqual_Equiv : quotation_of F.Equal_Equiv.
  #[export] Declare Instance qcompat_cmp : quotation_of F.compat_cmp.
  #[export] Declare Instance qEquiv_Equivb : quotation_of F.Equiv_Equivb.
  #[export] Declare Instance qEqual_Equivb : quotation_of F.Equal_Equivb.
  #[export] Declare Instance qEqual_Equivb_eqdec : quotation_of F.Equal_Equivb_eqdec.
  #[export] Declare Instance qEqual_refl : quotation_of F.Equal_refl.
  #[export] Declare Instance qEqual_sym : quotation_of F.Equal_sym.
  #[export] Declare Instance qEqual_trans : quotation_of F.Equal_trans.
  #[export] Declare Instance qEqual_ST : quotation_of F.Equal_ST.
  #[export] Declare Instance qKeySetoid_relation : quotation_of F.KeySetoid_relation.
  #[export] Declare Instance qKeySetoid_Reflexive : quotation_of F.KeySetoid_Reflexive.
  #[export] Declare Instance qKeySetoid_Symmetric : quotation_of F.KeySetoid_Symmetric.
  #[export] Declare Instance qKeySetoid_Transitive : quotation_of F.KeySetoid_Transitive.
  #[export] Declare Instance qKeySetoid : quotation_of F.KeySetoid.
  #[export] Declare Instance qEqualSetoid_relation : quotation_of F.EqualSetoid_relation.
  #[export] Declare Instance qEqualSetoid_Reflexive : quotation_of F.EqualSetoid_Reflexive.
  #[export] Declare Instance qEqualSetoid_Symmetric : quotation_of F.EqualSetoid_Symmetric.
  #[export] Declare Instance qEqualSetoid_Transitive : quotation_of F.EqualSetoid_Transitive.
  #[export] Declare Instance qEqualSetoid : quotation_of F.EqualSetoid.
  #[export] Declare Instance qIn_m_Proper : quotation_of F.In_m_Proper.
  #[export] Declare Instance qIn_m : quotation_of F.In_m.
  #[export] Declare Instance qMapsTo_m_Proper : quotation_of F.MapsTo_m_Proper.
  #[export] Declare Instance qMapsTo_m : quotation_of F.MapsTo_m.
  #[export] Declare Instance qEmpty_m_Proper : quotation_of F.Empty_m_Proper.
  #[export] Declare Instance qEmpty_m : quotation_of F.Empty_m.
  #[export] Declare Instance qis_empty_m_Proper : quotation_of F.is_empty_m_Proper.
  #[export] Declare Instance qis_empty_m : quotation_of F.is_empty_m.
  #[export] Declare Instance qmem_m_Proper : quotation_of F.mem_m_Proper.
  #[export] Declare Instance qmem_m : quotation_of F.mem_m.
  #[export] Declare Instance qfind_m_Proper : quotation_of F.find_m_Proper.
  #[export] Declare Instance qfind_m : quotation_of F.find_m.
  #[export] Declare Instance qadd_m_Proper : quotation_of F.add_m_Proper.
  #[export] Declare Instance qadd_m : quotation_of F.add_m.
  #[export] Declare Instance qremove_m_Proper : quotation_of F.remove_m_Proper.
  #[export] Declare Instance qremove_m : quotation_of F.remove_m.
  #[export] Declare Instance qmap_m_Proper : quotation_of F.map_m_Proper.
  #[export] Declare Instance qmap_m : quotation_of F.map_m.
End QuotationOfWFacts_fun.

Module QuoteWSfun (E : DecidableTypeOrig) (Import W : WSfun E) (Import WFacts : WFacts_funSig E W) (qE : QuotationOfDecidableTypeOrig E) (qW : QuotationOfWSfun E W) (qWFacts : QuotationOfWFacts_fun E W WFacts).
  Export (hints) qE qW qWFacts.

  Section with_quote.
    Context {elt : Type}
            {qelt : quotation_of elt}.

    #[export] Instance quote_MapsTo {x y z} {qx : quotation_of x} {qy : quotation_of y} {qz : quotation_of z} : ground_quotable (@MapsTo elt x y z)
      := ground_quotable_of_iff (iff_sym (@find_mapsto_iff _ _ _ _)).
    #[export] Instance quote_In {k m} {qk : quotation_of k} {qm : quotation_of m} : ground_quotable (@In elt k m)
      := ground_quotable_of_iff (iff_sym (@mem_in_iff _ _ _)).
    #[export] Instance quote_neg_In {k m} {qk : quotation_of k} {qm : quotation_of m} : ground_quotable (~@In elt k m)
      := quote_neg_of_iff (iff_sym (@mem_in_iff _ _ _)).

    #[export] Instance quote_Empty {m} {qm : quotation_of m} : ground_quotable (@Empty elt m)
      := ground_quotable_of_iff (iff_sym (@is_empty_iff _ _)).
    #[export] Instance quote_neg_Empty {m} {qm : quotation_of m} : ground_quotable (~@Empty elt m)
      := quote_neg_of_iff (iff_sym (@is_empty_iff _ _)).

    Definition Equiv_alt (eq_elt : elt -> elt -> Prop) m m' :=
      let eq_opt_elt x y := match x, y with
                            | Some x, Some y => eq_elt x y
                            | None, None => True
                            | Some _, None | None, Some _ => False
                            end in
      List.Forall (fun '(k, _) => eq_opt_elt (find k m) (find k m')) (@elements elt m)
      /\ List.Forall (fun '(k, _) => eq_opt_elt (find k m) (find k m')) (@elements elt m').
    Import StrongerInstances.
    Lemma Equiv_alt_iff {eq_elt m m'} : Equiv_alt eq_elt m m' <-> Equiv eq_elt m m'.
    Proof using Type.
      cbv [Equiv Equiv_alt].
      cbv [In] in *.
      setoid_rewrite find_mapsto_iff.
      rewrite !Forall_forall.
      pose proof (@find_o elt m).
      pose proof (@find_o elt m').
      transitivity
        (let eq_opt_elt x y := match x, y with
                               | Some x, Some y => eq_elt x y
                               | None, None => True
                               | Some _, None | None, Some _ => False
                               end in
         (forall k, In k m -> eq_opt_elt (find k m) (find k m'))
         /\ (forall k, In k m' -> eq_opt_elt (find k m) (find k m'))).
      1: cbv [In]; setoid_rewrite elements_mapsto_iff; setoid_rewrite InA_alt; cbv [eq_key_elt]; cbn [fst snd].
      2: cbv [In]; setoid_rewrite find_mapsto_iff.
      all: repeat (split || intros || destruct_head'_and || split_iff || destruct_head'_prod || destruct_head'_ex || subst).
      all: specialize_dep_under_binders_by eapply ex_intro.
      all: specialize_dep_under_binders_by eapply conj.
      all: specialize_dep_under_binders_by eapply eq_refl.
      all: specialize_dep_under_binders_by eapply pair.
      all: cbn [fst snd] in *.
      all: specialize_all_ways_under_binders_by apply E.eq_refl.
      all: repeat first [ progress destruct_head'_ex
                        | match goal with
                          | [ H : List.In _ _ |- _ ]
                            => progress specialize_under_binders_by exact H
                          | [ H : E.eq _ _ |- _ ]
                            => progress specialize_under_binders_by exact H
                          | [ H : find _ _ = Some _ |- _ ]
                            => progress specialize_under_binders_by exact H
                          end ].
      all: try solve [ repeat destruct ?; subst; try congruence; eauto ].
    Qed.

    #[export] Instance quote_Equiv_alt {eq_elt} {m m'} {qeq_elt : quotation_of eq_elt} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} {quote_eq_elt : forall x y, ground_quotable (eq_elt x y:Prop)} {qm : quotation_of m} {qm' : quotation_of m'} : ground_quotable (@Equiv_alt eq_elt m m') := _.
    #[export] Instance qEquiv_alt : quotation_of (@Equiv_alt) := ltac:(unfold_quotation_of (); exact _).
    (* too slow :-( *)
    (*#[export] Instance qEquiv_alt_iff : quotation_of (@Equiv_alt_iff) := ltac:(unfold_quotation_of (); exact _).*)

    #[export] Instance quote_Equiv {qEquiv_alt_iff : quotation_of (@Equiv_alt_iff)} {qEquiv_alt_iff : quotation_of (@Equiv_alt_iff)} {eq_elt m m'} {qm : quotation_of m} {qm' : quotation_of m'} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} {qeq_elt : quotation_of eq_elt} {quote_eq_elt : forall x y, ground_quotable (eq_elt x y:Prop)} : ground_quotable (@Equiv elt eq_elt m m') := ground_quotable_of_iff Equiv_alt_iff.

    #[export] Instance quote_Equal {qEquiv_alt_iff : quotation_of (@Equiv_alt_iff)} {m m'} {qm : quotation_of m} {qm' : quotation_of m'} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} : ground_quotable (@Equal elt m m') := ground_quotable_of_iff (iff_sym (@Equal_Equiv elt m m')).

    #[export] Instance quote_Equivb {qEquiv_alt_iff : quotation_of (@Equiv_alt_iff)} {cmp m m'} {qm : quotation_of m} {qm' : quotation_of m'} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} {qcmp : quotation_of cmp} : ground_quotable (@Equivb elt cmp m m') := _.
  End with_quote.

  #[export] Existing Instances
    qEquiv_alt
    quote_MapsTo
    quote_In
    quote_neg_In
    quote_Empty
    quote_neg_Empty
    quote_Equiv_alt
    quote_Equiv
    quote_Equal
    quote_Equivb
  .
End QuoteWSfun.

Module Export FSets.
  Module FMapList.
    Module Type RawSig (T : OrderedType) := Nop <+ FMapList.Raw T.
    Module Type QuotationOfRaw (T : OrderedType) (M : RawSig T) (qT : QuotationOfOrderedTypeOrig T).
      Module qMX := QuotationOfOrderedTypeOrigFacts T M.MX qT.
      Module qPX := QuotationOfKeyOrderedTypeOrig T M.PX qT.
      Export (hints) qMX qPX.
      #[export] Declare Instance qkey : quotation_of M.key.
      #[export] Declare Instance qt : quotation_of M.t.
      #[export] Declare Instance qempty : quotation_of M.empty.
      #[export] Declare Instance qEmpty : quotation_of M.Empty.
      #[export] Declare Instance qempty_1 : quotation_of M.empty_1.
      #[export] Declare Instance qempty_sorted : quotation_of M.empty_sorted.
      #[export] Declare Instance qis_empty : quotation_of M.is_empty.
      #[export] Declare Instance qis_empty_1 : quotation_of M.is_empty_1.
      #[export] Declare Instance qis_empty_2 : quotation_of M.is_empty_2.
      #[export] Declare Instance qmem : quotation_of M.mem.
      #[export] Declare Instance qR_mem : inductive_quotation_of M.R_mem.
      #[export] Declare Instance qR_mem_rect : quotation_of M.R_mem_rect.
      #[export] Declare Instance qR_mem_ind : quotation_of M.R_mem_ind.
      #[export] Declare Instance qR_mem_rec : quotation_of M.R_mem_rec.
      #[export] Declare Instance qmem_equation : quotation_of M.mem_equation.
      #[export] Declare Instance qmem_rect : quotation_of M.mem_rect.
      #[export] Declare Instance qmem_ind : quotation_of M.mem_ind.
      #[export] Declare Instance qmem_rec : quotation_of M.mem_rec.
      #[export] Declare Instance qR_mem_correct : quotation_of M.R_mem_correct.
      #[export] Declare Instance qR_mem_complete : quotation_of M.R_mem_complete.
      #[export] Declare Instance qmem_1 : quotation_of M.mem_1.
      #[export] Declare Instance qmem_2 : quotation_of M.mem_2.
      #[export] Declare Instance qfind : quotation_of M.find.
      #[export] Declare Instance qR_find : inductive_quotation_of M.R_find.
      #[export] Declare Instance qR_find_rect : quotation_of M.R_find_rect.
      #[export] Declare Instance qR_find_ind : quotation_of M.R_find_ind.
      #[export] Declare Instance qR_find_rec : quotation_of M.R_find_rec.
      #[export] Declare Instance qfind_equation : quotation_of M.find_equation.
      #[export] Declare Instance qfind_rect : quotation_of M.find_rect.
      #[export] Declare Instance qfind_ind : quotation_of M.find_ind.
      #[export] Declare Instance qfind_rec : quotation_of M.find_rec.
      #[export] Declare Instance qR_find_correct : quotation_of M.R_find_correct.
      #[export] Declare Instance qR_find_complete : quotation_of M.R_find_complete.
      #[export] Declare Instance qfind_2 : quotation_of M.find_2.
      #[export] Declare Instance qfind_1 : quotation_of M.find_1.
      #[export] Declare Instance qadd : quotation_of M.add.
      #[export] Declare Instance qR_add : inductive_quotation_of M.R_add.
      #[export] Declare Instance qR_add_rect : quotation_of M.R_add_rect.
      #[export] Declare Instance qR_add_ind : quotation_of M.R_add_ind.
      #[export] Declare Instance qR_add_rec : quotation_of M.R_add_rec.
      #[export] Declare Instance qadd_equation : quotation_of M.add_equation.
      #[export] Declare Instance qadd_rect : quotation_of M.add_rect.
      #[export] Declare Instance qadd_ind : quotation_of M.add_ind.
      #[export] Declare Instance qadd_rec : quotation_of M.add_rec.
      #[export] Declare Instance qR_add_correct : quotation_of M.R_add_correct.
      #[export] Declare Instance qR_add_complete : quotation_of M.R_add_complete.
      #[export] Declare Instance qadd_1 : quotation_of M.add_1.
      #[export] Declare Instance qadd_2 : quotation_of M.add_2.
      #[export] Declare Instance qadd_3 : quotation_of M.add_3.
      #[export] Declare Instance qadd_Inf : quotation_of M.add_Inf.
      #[export] Declare Instance qadd_sorted : quotation_of M.add_sorted.
      #[export] Declare Instance qremove : quotation_of M.remove.
      #[export] Declare Instance qR_remove : inductive_quotation_of M.R_remove.
      #[export] Declare Instance qR_remove_rect : quotation_of M.R_remove_rect.
      #[export] Declare Instance qR_remove_ind : quotation_of M.R_remove_ind.
      #[export] Declare Instance qR_remove_rec : quotation_of M.R_remove_rec.
      #[export] Declare Instance qremove_equation : quotation_of M.remove_equation.
      #[export] Declare Instance qremove_rect : quotation_of M.remove_rect.
      #[export] Declare Instance qremove_ind : quotation_of M.remove_ind.
      #[export] Declare Instance qremove_rec : quotation_of M.remove_rec.
      #[export] Declare Instance qR_remove_correct : quotation_of M.R_remove_correct.
      #[export] Declare Instance qR_remove_complete : quotation_of M.R_remove_complete.
      #[export] Declare Instance qremove_1 : quotation_of M.remove_1.
      #[export] Declare Instance qremove_2 : quotation_of M.remove_2.
      #[export] Declare Instance qremove_3 : quotation_of M.remove_3.
      #[export] Declare Instance qremove_Inf : quotation_of M.remove_Inf.
      #[export] Declare Instance qremove_sorted : quotation_of M.remove_sorted.
      #[export] Declare Instance qelements : quotation_of M.elements.
      #[export] Declare Instance qelements_1 : quotation_of M.elements_1.
      #[export] Declare Instance qelements_2 : quotation_of M.elements_2.
      #[export] Declare Instance qelements_3 : quotation_of M.elements_3.
      #[export] Declare Instance qelements_3w : quotation_of M.elements_3w.
      #[export] Declare Instance qfold : quotation_of M.fold.
      #[export] Declare Instance qR_fold : inductive_quotation_of M.R_fold.
      #[export] Declare Instance qR_fold_rect : quotation_of M.R_fold_rect.
      #[export] Declare Instance qR_fold_ind : quotation_of M.R_fold_ind.
      #[export] Declare Instance qR_fold_rec : quotation_of M.R_fold_rec.
      #[export] Declare Instance qfold_equation : quotation_of M.fold_equation.
      #[export] Declare Instance qfold_rect : quotation_of M.fold_rect.
      #[export] Declare Instance qfold_ind : quotation_of M.fold_ind.
      #[export] Declare Instance qfold_rec : quotation_of M.fold_rec.
      #[export] Declare Instance qR_fold_correct : quotation_of M.R_fold_correct.
      #[export] Declare Instance qR_fold_complete : quotation_of M.R_fold_complete.
      #[export] Declare Instance qfold_1 : quotation_of M.fold_1.
      #[export] Declare Instance qequal : quotation_of M.equal.
      #[export] Declare Instance qR_equal : inductive_quotation_of M.R_equal.
      #[export] Declare Instance qR_equal_rect : quotation_of M.R_equal_rect.
      #[export] Declare Instance qR_equal_ind : quotation_of M.R_equal_ind.
      #[export] Declare Instance qR_equal_rec : quotation_of M.R_equal_rec.
      #[export] Declare Instance qequal_equation : quotation_of M.equal_equation.
      #[export] Declare Instance qequal_rect : quotation_of M.equal_rect.
      #[export] Declare Instance qequal_ind : quotation_of M.equal_ind.
      #[export] Declare Instance qequal_rec : quotation_of M.equal_rec.
      #[export] Declare Instance qR_equal_correct : quotation_of M.R_equal_correct.
      #[export] Declare Instance qR_equal_complete : quotation_of M.R_equal_complete.
      #[export] Declare Instance qEquivb : quotation_of M.Equivb.
      #[export] Declare Instance qequal_1 : quotation_of M.equal_1.
      #[export] Declare Instance qequal_2 : quotation_of M.equal_2.
      #[export] Declare Instance qequal_cons : quotation_of M.equal_cons.
      #[export] Declare Instance qmap : quotation_of M.map.
      #[export] Declare Instance qmapi : quotation_of M.mapi.
      #[export] Declare Instance qmap_1 : quotation_of M.map_1.
      #[export] Declare Instance qmap_2 : quotation_of M.map_2.
      #[export] Declare Instance qmap_lelistA : quotation_of M.map_lelistA.
      #[export] Declare Instance qmap_sorted : quotation_of M.map_sorted.
      #[export] Declare Instance qmapi_1 : quotation_of M.mapi_1.
      #[export] Declare Instance qmapi_2 : quotation_of M.mapi_2.
      #[export] Declare Instance qmapi_lelistA : quotation_of M.mapi_lelistA.
      #[export] Declare Instance qmapi_sorted : quotation_of M.mapi_sorted.
      #[export] Declare Instance qoption_cons : quotation_of M.option_cons.
      #[export] Declare Instance qmap2_l : quotation_of M.map2_l.
      #[export] Declare Instance qmap2_r : quotation_of M.map2_r.
      #[export] Declare Instance qmap2 : quotation_of M.map2.
      #[export] Declare Instance qcombine : quotation_of M.combine.
      #[export] Declare Instance qfold_right_pair : quotation_of M.fold_right_pair.
      #[export] Declare Instance qmap2_alt : quotation_of M.map2_alt.
      #[export] Declare Instance qmap2_alt_equiv : quotation_of M.map2_alt_equiv.
      #[export] Declare Instance qcombine_lelistA : quotation_of M.combine_lelistA.
      #[export] Declare Instance qcombine_sorted : quotation_of M.combine_sorted.
      #[export] Declare Instance qmap2_sorted : quotation_of M.map2_sorted.
      #[export] Declare Instance qat_least_one : quotation_of M.at_least_one.
      #[export] Declare Instance qcombine_1 : quotation_of M.combine_1.
      #[export] Declare Instance qat_least_one_then_f : quotation_of M.at_least_one_then_f.
      #[export] Declare Instance qmap2_0 : quotation_of M.map2_0.
      #[export] Declare Instance qmap2_1 : quotation_of M.map2_1.
      #[export] Declare Instance qmap2_2 : quotation_of M.map2_2.
    End QuotationOfRaw.
  End FMapList.

  Module FMapAVL.
    Module Type MakeSig (T : OrderedType) := Nop <+ FMapAVL.Make T.
    Module Type QuotationOfMake (T : OrderedType) (M : MakeSig T) (qT : QuotationOfOrderedTypeOrig T).
      Module qRaw.
        #[export] Declare Instance qkey : quotation_of M.Raw.key.
        #[export] Declare Instance qtree : inductive_quotation_of M.Raw.tree.
        #[export] Declare Instance qheight : quotation_of M.Raw.height.
        #[export] Declare Instance qcardinal : quotation_of M.Raw.cardinal.
        #[export] Declare Instance qempty : quotation_of M.Raw.empty.
        #[export] Declare Instance qis_empty : quotation_of M.Raw.is_empty.
        #[export] Declare Instance qmem : quotation_of M.Raw.mem.
        #[export] Declare Instance qfind : quotation_of M.Raw.find.
        #[export] Declare Instance qcreate : quotation_of M.Raw.create.
        #[export] Declare Instance qassert_false : quotation_of M.Raw.assert_false.
        #[export] Declare Instance qbal : quotation_of M.Raw.bal.
        #[export] Declare Instance qadd : quotation_of M.Raw.add.
        #[export] Declare Instance qremove_min : quotation_of M.Raw.remove_min.
        #[export] Declare Instance qmerge : quotation_of M.Raw.merge.
        #[export] Declare Instance qremove : quotation_of M.Raw.remove.
        #[export] Declare Instance qjoin : quotation_of M.Raw.join.
        #[export] Declare Instance qt_left : quotation_of M.Raw.t_left.
        #[export] Declare Instance qt_opt : quotation_of M.Raw.t_opt.
        #[export] Declare Instance qt_right : quotation_of M.Raw.t_right.
        #[export] Declare Instance qsplit : quotation_of M.Raw.split.
        #[export] Declare Instance qconcat : quotation_of M.Raw.concat.
        #[export] Declare Instance qelements_aux : quotation_of M.Raw.elements_aux.
        #[export] Declare Instance qelements : quotation_of M.Raw.elements.
        #[export] Declare Instance qfold : quotation_of M.Raw.fold.
        #[export] Declare Instance qenumeration : inductive_quotation_of M.Raw.enumeration.
        #[export] Declare Instance qcons : quotation_of M.Raw.cons.
        #[export] Declare Instance qequal_more : quotation_of M.Raw.equal_more.
        #[export] Declare Instance qequal_cont : quotation_of M.Raw.equal_cont.
        #[export] Declare Instance qequal_end : quotation_of M.Raw.equal_end.
        #[export] Declare Instance qequal : quotation_of M.Raw.equal.
        #[export] Declare Instance qmap : quotation_of M.Raw.map.
        #[export] Declare Instance qmapi : quotation_of M.Raw.mapi.
        #[export] Declare Instance qmap_option : quotation_of M.Raw.map_option.
        #[export] Declare Instance qmap2_opt : quotation_of M.Raw.map2_opt.
        #[export] Declare Instance qmap2 : quotation_of M.Raw.map2.
        #[export] Declare Instance qMapsTo : inductive_quotation_of M.Raw.MapsTo.
        #[export] Declare Instance qIn : inductive_quotation_of M.Raw.In.
        #[export] Declare Instance qIn0 : quotation_of M.Raw.In0.
        #[export] Declare Instance qlt_tree : quotation_of M.Raw.lt_tree.
        #[export] Declare Instance qgt_tree : quotation_of M.Raw.gt_tree.
        #[export] Declare Instance qbst : inductive_quotation_of M.Raw.bst.
        Module qProofs.
          Module qMX := QuotationOfOrderedTypeOrigFacts T M.Raw.Proofs.MX qT.
          Module qPX := QuotationOfKeyOrderedTypeOrig T M.Raw.Proofs.PX qT.
          Module qL := Nop <+ FMapList.QuotationOfRaw T M.Raw.Proofs.L qT.
          Export (hints) qMX qPX qL.
          #[export] Declare Instance qR_mem : inductive_quotation_of M.Raw.Proofs.R_mem.
          #[export] Declare Instance qR_mem_rect : quotation_of M.Raw.Proofs.R_mem_rect.
          #[export] Declare Instance qR_mem_ind : quotation_of M.Raw.Proofs.R_mem_ind.
          #[export] Declare Instance qR_mem_rec : quotation_of M.Raw.Proofs.R_mem_rec.
          #[export] Declare Instance qmem_equation : quotation_of M.Raw.Proofs.mem_equation.
          #[export] Declare Instance qmem_ind : quotation_of M.Raw.Proofs.mem_ind.
          #[export] Declare Instance qR_find_rect : quotation_of M.Raw.Proofs.R_find_rect.
          #[export] Declare Instance qR_find_ind : quotation_of M.Raw.Proofs.R_find_ind.
          #[export] Declare Instance qR_find_rec : quotation_of M.Raw.Proofs.R_find_rec.
          #[export] Declare Instance qfind_equation : quotation_of M.Raw.Proofs.find_equation.
          #[export] Declare Instance qfind_ind : quotation_of M.Raw.Proofs.find_ind.
          #[export] Declare Instance qR_bal_rect : quotation_of M.Raw.Proofs.R_bal_rect.
          #[export] Declare Instance qR_bal_ind : quotation_of M.Raw.Proofs.R_bal_ind.
          #[export] Declare Instance qR_bal_rec : quotation_of M.Raw.Proofs.R_bal_rec.
          #[export] Declare Instance qbal_ind : quotation_of M.Raw.Proofs.bal_ind.
          #[export] Declare Instance qR_add_rect : quotation_of M.Raw.Proofs.R_add_rect.
          #[export] Declare Instance qR_add_ind : quotation_of M.Raw.Proofs.R_add_ind.
          #[export] Declare Instance qR_add_rec : quotation_of M.Raw.Proofs.R_add_rec.
          #[export] Declare Instance qadd_equation : quotation_of M.Raw.Proofs.add_equation.
          #[export] Declare Instance qadd_ind : quotation_of M.Raw.Proofs.add_ind.
          #[export] Declare Instance qR_remove_min_rect : quotation_of M.Raw.Proofs.R_remove_min_rect.
          #[export] Declare Instance qR_remove_min_ind : quotation_of M.Raw.Proofs.R_remove_min_ind.
          #[export] Declare Instance qR_remove_min_rec : quotation_of M.Raw.Proofs.R_remove_min_rec.
          #[export] Declare Instance qremove_min_equation : quotation_of M.Raw.Proofs.remove_min_equation.
          #[export] Declare Instance qremove_min_ind : quotation_of M.Raw.Proofs.remove_min_ind.
          #[export] Declare Instance qR_merge_rect : quotation_of M.Raw.Proofs.R_merge_rect.
          #[export] Declare Instance qR_merge_ind : quotation_of M.Raw.Proofs.R_merge_ind.
          #[export] Declare Instance qR_merge_rec : quotation_of M.Raw.Proofs.R_merge_rec.
          #[export] Declare Instance qmerge_ind : quotation_of M.Raw.Proofs.merge_ind.
          #[export] Declare Instance qR_remove_rect : quotation_of M.Raw.Proofs.R_remove_rect.
          #[export] Declare Instance qR_remove_ind : quotation_of M.Raw.Proofs.R_remove_ind.
          #[export] Declare Instance qR_remove_rec : quotation_of M.Raw.Proofs.R_remove_rec.
          #[export] Declare Instance qremove_equation : quotation_of M.Raw.Proofs.remove_equation.
          #[export] Declare Instance qremove_ind : quotation_of M.Raw.Proofs.remove_ind.
          #[export] Declare Instance qR_concat_rect : quotation_of M.Raw.Proofs.R_concat_rect.
          #[export] Declare Instance qR_concat_ind : quotation_of M.Raw.Proofs.R_concat_ind.
          #[export] Declare Instance qR_concat_rec : quotation_of M.Raw.Proofs.R_concat_rec.
          #[export] Declare Instance qconcat_ind : quotation_of M.Raw.Proofs.concat_ind.
          #[export] Declare Instance qR_split_rect : quotation_of M.Raw.Proofs.R_split_rect.
          #[export] Declare Instance qR_split_ind : quotation_of M.Raw.Proofs.R_split_ind.
          #[export] Declare Instance qR_split_rec : quotation_of M.Raw.Proofs.R_split_rec.
          #[export] Declare Instance qsplit_equation : quotation_of M.Raw.Proofs.split_equation.
          #[export] Declare Instance qsplit_ind : quotation_of M.Raw.Proofs.split_ind.
          #[export] Declare Instance qR_map_option : inductive_quotation_of M.Raw.Proofs.R_map_option.
          #[export] Declare Instance qR_map_option_rect : quotation_of M.Raw.Proofs.R_map_option_rect.
          #[export] Declare Instance qR_map_option_ind : quotation_of M.Raw.Proofs.R_map_option_ind.
          #[export] Declare Instance qR_map_option_rec : quotation_of M.Raw.Proofs.R_map_option_rec.
          #[export] Declare Instance qmap_option_equation : quotation_of M.Raw.Proofs.map_option_equation.
          #[export] Declare Instance qmap_option_ind : quotation_of M.Raw.Proofs.map_option_ind.
          #[export] Declare Instance qR_map2_opt_rect : quotation_of M.Raw.Proofs.R_map2_opt_rect.
          #[export] Declare Instance qR_map2_opt_ind : quotation_of M.Raw.Proofs.R_map2_opt_ind.
          #[export] Declare Instance qR_map2_opt_rec : quotation_of M.Raw.Proofs.R_map2_opt_rec.
          #[export] Declare Instance qmap2_opt_equation : quotation_of M.Raw.Proofs.map2_opt_equation.
          #[export] Declare Instance qmap2_opt_ind : quotation_of M.Raw.Proofs.map2_opt_ind.
          #[export] Declare Instance qMapsTo_In : quotation_of M.Raw.Proofs.MapsTo_In.
          #[export] Declare Instance qIn_MapsTo : quotation_of M.Raw.Proofs.In_MapsTo.
          #[export] Declare Instance qIn_alt : quotation_of M.Raw.Proofs.In_alt.
          #[export] Declare Instance qMapsTo_1 : quotation_of M.Raw.Proofs.MapsTo_1.
          #[export] Declare Instance qIn_1 : quotation_of M.Raw.Proofs.In_1.
          #[export] Declare Instance qIn_node_iff : quotation_of M.Raw.Proofs.In_node_iff.
          #[export] Declare Instance qlt_leaf : quotation_of M.Raw.Proofs.lt_leaf.
          #[export] Declare Instance qgt_leaf : quotation_of M.Raw.Proofs.gt_leaf.
          #[export] Declare Instance qlt_tree_node : quotation_of M.Raw.Proofs.lt_tree_node.
          #[export] Declare Instance qgt_tree_node : quotation_of M.Raw.Proofs.gt_tree_node.
          #[export] Declare Instance qlt_left : quotation_of M.Raw.Proofs.lt_left.
          #[export] Declare Instance qlt_right : quotation_of M.Raw.Proofs.lt_right.
          #[export] Declare Instance qgt_left : quotation_of M.Raw.Proofs.gt_left.
          #[export] Declare Instance qgt_right : quotation_of M.Raw.Proofs.gt_right.
          #[export] Declare Instance qlt_tree_not_in : quotation_of M.Raw.Proofs.lt_tree_not_in.
          #[export] Declare Instance qlt_tree_trans : quotation_of M.Raw.Proofs.lt_tree_trans.
          #[export] Declare Instance qgt_tree_not_in : quotation_of M.Raw.Proofs.gt_tree_not_in.
          #[export] Declare Instance qgt_tree_trans : quotation_of M.Raw.Proofs.gt_tree_trans.
          #[export] Declare Instance qEmpty : quotation_of M.Raw.Proofs.Empty.
          #[export] Declare Instance qempty_bst : quotation_of M.Raw.Proofs.empty_bst.
          #[export] Declare Instance qempty_1 : quotation_of M.Raw.Proofs.empty_1.
          #[export] Declare Instance qis_empty_1 : quotation_of M.Raw.Proofs.is_empty_1.
          #[export] Declare Instance qis_empty_2 : quotation_of M.Raw.Proofs.is_empty_2.
          #[export] Declare Instance qmem_1 : quotation_of M.Raw.Proofs.mem_1.
          #[export] Declare Instance qmem_2 : quotation_of M.Raw.Proofs.mem_2.
          #[export] Declare Instance qfind_1 : quotation_of M.Raw.Proofs.find_1.
          #[export] Declare Instance qfind_2 : quotation_of M.Raw.Proofs.find_2.
          #[export] Declare Instance qfind_iff : quotation_of M.Raw.Proofs.find_iff.
          #[export] Declare Instance qfind_in : quotation_of M.Raw.Proofs.find_in.
          #[export] Declare Instance qin_find : quotation_of M.Raw.Proofs.in_find.
          #[export] Declare Instance qfind_in_iff : quotation_of M.Raw.Proofs.find_in_iff.
          #[export] Declare Instance qnot_find_iff : quotation_of M.Raw.Proofs.not_find_iff.
          #[export] Declare Instance qfind_find : quotation_of M.Raw.Proofs.find_find.
          #[export] Declare Instance qfind_mapsto_equiv : quotation_of M.Raw.Proofs.find_mapsto_equiv.
          #[export] Declare Instance qfind_in_equiv : quotation_of M.Raw.Proofs.find_in_equiv.
          #[export] Declare Instance qcreate_bst : quotation_of M.Raw.Proofs.create_bst.
          #[export] Declare Instance qcreate_in : quotation_of M.Raw.Proofs.create_in.
          #[export] Declare Instance qbal_bst : quotation_of M.Raw.Proofs.bal_bst.
          #[export] Declare Instance qbal_in : quotation_of M.Raw.Proofs.bal_in.
          #[export] Declare Instance qbal_mapsto : quotation_of M.Raw.Proofs.bal_mapsto.
          #[export] Declare Instance qbal_find : quotation_of M.Raw.Proofs.bal_find.
          #[export] Declare Instance qadd_in : quotation_of M.Raw.Proofs.add_in.
          #[export] Declare Instance qadd_bst : quotation_of M.Raw.Proofs.add_bst.
          #[export] Declare Instance qadd_1 : quotation_of M.Raw.Proofs.add_1.
          #[export] Declare Instance qadd_2 : quotation_of M.Raw.Proofs.add_2.
          #[export] Declare Instance qadd_3 : quotation_of M.Raw.Proofs.add_3.
          #[export] Declare Instance qadd_find : quotation_of M.Raw.Proofs.add_find.
          #[export] Declare Instance qremove_min_in : quotation_of M.Raw.Proofs.remove_min_in.
          #[export] Declare Instance qremove_min_mapsto : quotation_of M.Raw.Proofs.remove_min_mapsto.
          #[export] Declare Instance qremove_min_bst : quotation_of M.Raw.Proofs.remove_min_bst.
          #[export] Declare Instance qremove_min_gt_tree : quotation_of M.Raw.Proofs.remove_min_gt_tree.
          #[export] Declare Instance qremove_min_find : quotation_of M.Raw.Proofs.remove_min_find.
          #[export] Declare Instance qmerge_in : quotation_of M.Raw.Proofs.merge_in.
          #[export] Declare Instance qmerge_mapsto : quotation_of M.Raw.Proofs.merge_mapsto.
          #[export] Declare Instance qmerge_bst : quotation_of M.Raw.Proofs.merge_bst.
          #[export] Declare Instance qremove_in : quotation_of M.Raw.Proofs.remove_in.
          #[export] Declare Instance qremove_bst : quotation_of M.Raw.Proofs.remove_bst.
          #[export] Declare Instance qremove_1 : quotation_of M.Raw.Proofs.remove_1.
          #[export] Declare Instance qremove_2 : quotation_of M.Raw.Proofs.remove_2.
          #[export] Declare Instance qremove_3 : quotation_of M.Raw.Proofs.remove_3.
          #[export] Declare Instance qjoin_in : quotation_of M.Raw.Proofs.join_in.
          #[export] Declare Instance qjoin_bst : quotation_of M.Raw.Proofs.join_bst.
          #[export] Declare Instance qjoin_find : quotation_of M.Raw.Proofs.join_find.
          #[export] Declare Instance qsplit_in_1 : quotation_of M.Raw.Proofs.split_in_1.
          #[export] Declare Instance qsplit_in_2 : quotation_of M.Raw.Proofs.split_in_2.
          #[export] Declare Instance qsplit_in_3 : quotation_of M.Raw.Proofs.split_in_3.
          #[export] Declare Instance qsplit_bst : quotation_of M.Raw.Proofs.split_bst.
          #[export] Declare Instance qsplit_lt_tree : quotation_of M.Raw.Proofs.split_lt_tree.
          #[export] Declare Instance qsplit_gt_tree : quotation_of M.Raw.Proofs.split_gt_tree.
          #[export] Declare Instance qsplit_find : quotation_of M.Raw.Proofs.split_find.
          #[export] Declare Instance qconcat_in : quotation_of M.Raw.Proofs.concat_in.
          #[export] Declare Instance qconcat_bst : quotation_of M.Raw.Proofs.concat_bst.
          #[export] Declare Instance qconcat_find : quotation_of M.Raw.Proofs.concat_find.
          #[export] Declare Instance qelements_aux_mapsto : quotation_of M.Raw.Proofs.elements_aux_mapsto.
          #[export] Declare Instance qelements_mapsto : quotation_of M.Raw.Proofs.elements_mapsto.
          #[export] Declare Instance qelements_in : quotation_of M.Raw.Proofs.elements_in.
          #[export] Declare Instance qelements_aux_sort : quotation_of M.Raw.Proofs.elements_aux_sort.
          #[export] Declare Instance qelements_sort : quotation_of M.Raw.Proofs.elements_sort.
          #[export] Declare Instance qelements_nodup : quotation_of M.Raw.Proofs.elements_nodup.
          #[export] Declare Instance qelements_aux_cardinal : quotation_of M.Raw.Proofs.elements_aux_cardinal.
          #[export] Declare Instance qelements_cardinal : quotation_of M.Raw.Proofs.elements_cardinal.
          #[export] Declare Instance qelements_app : quotation_of M.Raw.Proofs.elements_app.
          #[export] Declare Instance qelements_node : quotation_of M.Raw.Proofs.elements_node.
          #[export] Declare Instance qfold' : quotation_of M.Raw.Proofs.fold'.
          #[export] Declare Instance qfold_equiv_aux : quotation_of M.Raw.Proofs.fold_equiv_aux.
          #[export] Declare Instance qfold_equiv : quotation_of M.Raw.Proofs.fold_equiv.
          #[export] Declare Instance qfold_1 : quotation_of M.Raw.Proofs.fold_1.
          #[export] Declare Instance qflatten_e : quotation_of M.Raw.Proofs.flatten_e.
          #[export] Declare Instance qflatten_e_elements : quotation_of M.Raw.Proofs.flatten_e_elements.
          #[export] Declare Instance qcons_1 : quotation_of M.Raw.Proofs.cons_1.
          #[export] Declare Instance qIfEq : quotation_of M.Raw.Proofs.IfEq.
          #[export] Declare Instance qcons_IfEq : quotation_of M.Raw.Proofs.cons_IfEq.
          #[export] Declare Instance qequal_end_IfEq : quotation_of M.Raw.Proofs.equal_end_IfEq.
          #[export] Declare Instance qequal_more_IfEq : quotation_of M.Raw.Proofs.equal_more_IfEq.
          #[export] Declare Instance qequal_cont_IfEq : quotation_of M.Raw.Proofs.equal_cont_IfEq.
          #[export] Declare Instance qequal_IfEq : quotation_of M.Raw.Proofs.equal_IfEq.
          #[export] Declare Instance qEquivb : quotation_of M.Raw.Proofs.Equivb.
          #[export] Declare Instance qEquivb_elements : quotation_of M.Raw.Proofs.Equivb_elements.
          #[export] Declare Instance qequal_Equivb : quotation_of M.Raw.Proofs.equal_Equivb.
          #[export] Declare Instance qmap_1 : quotation_of M.Raw.Proofs.map_1.
          #[export] Declare Instance qmap_2 : quotation_of M.Raw.Proofs.map_2.
          #[export] Declare Instance qmap_bst : quotation_of M.Raw.Proofs.map_bst.
          #[export] Declare Instance qmapi_1 : quotation_of M.Raw.Proofs.mapi_1.
          #[export] Declare Instance qmapi_2 : quotation_of M.Raw.Proofs.mapi_2.
          #[export] Declare Instance qmapi_bst : quotation_of M.Raw.Proofs.mapi_bst.
          #[export] Declare Instance qmap_option_2 : quotation_of M.Raw.Proofs.map_option_2.
          #[export] Declare Instance qmap_option_bst : quotation_of M.Raw.Proofs.map_option_bst.
          #[export] Declare Instance qmap_option_find : quotation_of M.Raw.Proofs.map_option_find.
          #[export] Declare Instance qmap2_opt_2 : quotation_of M.Raw.Proofs.map2_opt_2.
          #[export] Declare Instance qmap2_opt_bst : quotation_of M.Raw.Proofs.map2_opt_bst.
          #[export] Declare Instance qmap2_opt_1 : quotation_of M.Raw.Proofs.map2_opt_1.
          #[export] Declare Instance qmap2_bst : quotation_of M.Raw.Proofs.map2_bst.
          #[export] Declare Instance qmap2_1 : quotation_of M.Raw.Proofs.map2_1.
          #[export] Declare Instance qmap2_2 : quotation_of M.Raw.Proofs.map2_2.
        End qProofs.
        Export (hints) qProofs.
      End qRaw.
      Export (hints) qRaw.
      #[export] Declare Instance qbst : inductive_quotation_of M.bst.
      #[export] Declare Instance qthis : quotation_of M.this.
      #[export] Declare Instance qis_bst : quotation_of M.is_bst.
      #[export] Declare Instance qt : quotation_of M.t.
      #[export] Declare Instance qkey : quotation_of M.key.
      #[export] Declare Instance qempty : quotation_of M.empty.
      #[export] Declare Instance qis_empty : quotation_of M.is_empty.
      #[export] Declare Instance qadd : quotation_of M.add.
      #[export] Declare Instance qremove : quotation_of M.remove.
      #[export] Declare Instance qmem : quotation_of M.mem.
      #[export] Declare Instance qfind : quotation_of M.find.
      #[export] Declare Instance qmap : quotation_of M.map.
      #[export] Declare Instance qmapi : quotation_of M.mapi.
      #[export] Declare Instance qmap2 : quotation_of M.map2.
      #[export] Declare Instance qelements : quotation_of M.elements.
      #[export] Declare Instance qcardinal : quotation_of M.cardinal.
      #[export] Declare Instance qfold : quotation_of M.fold.
      #[export] Declare Instance qequal : quotation_of M.equal.
      #[export] Declare Instance qMapsTo : quotation_of M.MapsTo.
      #[export] Declare Instance qIn : quotation_of M.In.
      #[export] Declare Instance qEmpty : quotation_of M.Empty.
      #[export] Declare Instance qeq_key : quotation_of M.eq_key.
      #[export] Declare Instance qeq_key_elt : quotation_of M.eq_key_elt.
      #[export] Declare Instance qlt_key : quotation_of M.lt_key.
      #[export] Declare Instance qMapsTo_1 : quotation_of M.MapsTo_1.
      #[export] Declare Instance qmem_1 : quotation_of M.mem_1.
      #[export] Declare Instance qmem_2 : quotation_of M.mem_2.
      #[export] Declare Instance qempty_1 : quotation_of M.empty_1.
      #[export] Declare Instance qis_empty_1 : quotation_of M.is_empty_1.
      #[export] Declare Instance qis_empty_2 : quotation_of M.is_empty_2.
      #[export] Declare Instance qadd_1 : quotation_of M.add_1.
      #[export] Declare Instance qadd_2 : quotation_of M.add_2.
      #[export] Declare Instance qadd_3 : quotation_of M.add_3.
      #[export] Declare Instance qremove_1 : quotation_of M.remove_1.
      #[export] Declare Instance qremove_2 : quotation_of M.remove_2.
      #[export] Declare Instance qremove_3 : quotation_of M.remove_3.
      #[export] Declare Instance qfind_1 : quotation_of M.find_1.
      #[export] Declare Instance qfind_2 : quotation_of M.find_2.
      #[export] Declare Instance qfold_1 : quotation_of M.fold_1.
      #[export] Declare Instance qelements_1 : quotation_of M.elements_1.
      #[export] Declare Instance qelements_2 : quotation_of M.elements_2.
      #[export] Declare Instance qelements_3 : quotation_of M.elements_3.
      #[export] Declare Instance qelements_3w : quotation_of M.elements_3w.
      #[export] Declare Instance qcardinal_1 : quotation_of M.cardinal_1.
      #[export] Declare Instance qEqual : quotation_of M.Equal.
      #[export] Declare Instance qEquiv : quotation_of M.Equiv.
      #[export] Declare Instance qEquivb : quotation_of M.Equivb.
      #[export] Declare Instance qEquivb_Equivb : quotation_of M.Equivb_Equivb.
      #[export] Declare Instance qequal_1 : quotation_of M.equal_1.
      #[export] Declare Instance qequal_2 : quotation_of M.equal_2.
      #[export] Declare Instance qmap_1 : quotation_of M.map_1.
      #[export] Declare Instance qmap_2 : quotation_of M.map_2.
      #[export] Declare Instance qmapi_1 : quotation_of M.mapi_1.
      #[export] Declare Instance qmapi_2 : quotation_of M.mapi_2.
      #[export] Declare Instance qmap2_1 : quotation_of M.map2_1.
      #[export] Declare Instance qmap2_2 : quotation_of M.map2_2.
    End QuotationOfMake.
  End FMapAVL.
End FSets.

Module QuoteFMapAVL (T : OrderedType) (M : FMapAVL.MakeSig T) (Import WFacts : WFacts_funSig T M) (qT : QuotationOfOrderedTypeOrig T) (qM : FMapAVL.QuotationOfMake T M qT) (qWFacts : QuotationOfWFacts_fun T M WFacts).
  Export (hints) qT qM qWFacts.
  Include QuoteWSfun T M WFacts qT qM qWFacts.

  Module Raw.
    Scheme Induction for M.Raw.tree Sort Type.
    Scheme Induction for M.Raw.tree Sort Set.
    Scheme Induction for M.Raw.tree Sort Prop.
    Scheme Case for M.Raw.tree Sort Type.
    Scheme Case for M.Raw.tree Sort Prop.
    Scheme Minimality for M.Raw.tree Sort Type.
    Scheme Minimality for M.Raw.tree Sort Set.
    Scheme Minimality for M.Raw.tree Sort Prop.

    Section with_t.
      Context {elt : Type}
              {qelt : quotation_of elt}
              {quote_elt : ground_quotable elt} {quote_T_t : ground_quotable T.t}.

      Fixpoint lt_tree_dec x t : { @M.Raw.lt_tree elt x t } + {~ @M.Raw.lt_tree elt x t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node l k n r z
                 => match T.compare k x, lt_tree_dec x l, lt_tree_dec x r with
                    | LT p1, left p2, left p3 => left _
                    | _, right pf, _ => right _
                    | _, _, right pf => right _
                    | _, _, _ => right _
                    end
               end;
          try solve [ inversion 1
                    | inversion 1; subst; auto;
                      match goal with
                      | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                        => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                      end
                    | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                    | intro f; eapply M.Raw.Proofs.MX.lt_antirefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
      Defined.
      Fixpoint gt_tree_dec x t : { @M.Raw.gt_tree elt x t } + {~ @M.Raw.gt_tree elt x t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node l k n r z
                 => match T.compare k x, gt_tree_dec x l, gt_tree_dec x r with
                    | GT p1, left p2, left p3 => left _
                    | _, right pf, _ => right _
                    | _, _, right pf => right _
                    | _, _, _ => right _
                    end
               end;
          try solve [ inversion 1
                    | inversion 1; subst; auto;
                      match goal with
                      | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                        => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                      end
                    | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                    | intro f; eapply M.Raw.Proofs.MX.lt_antirefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
      Defined.
      Fixpoint bst_dec t : { @M.Raw.bst elt t } + {~ @M.Raw.bst elt t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node l k n r z
                 => match bst_dec l, bst_dec r, lt_tree_dec k l, gt_tree_dec k r with
                    | right pf, _, _, _ => right _
                    | _, right pf, _, _ => right _
                    | _, _, right pf, _ => right _
                    | _, _, _, right pf => right _
                    | left p1, left p2, left p3, left p4 => left _
                    end
               end;
          try solve [ constructor; assumption
                    | inversion 1; subst; auto ].
      Defined.
      #[export] Instance quote_tree : ground_quotable (M.Raw.tree elt) := (ltac:(induction 1; exact _)).
      (* very slow :-( *)
      #[export] Instance qlt_tree_dec : quotation_of (@lt_tree_dec) := ltac:(unfold_quotation_of (); exact _).
      #[export] Instance qgt_tree_dec : quotation_of (@gt_tree_dec) := ltac:(unfold_quotation_of (); exact _).
      #[export] Instance qbst_dec : quotation_of (@bst_dec) := ltac:(unfold_quotation_of (); exact _).
      #[export] Instance quote_bst t : ground_quotable (M.Raw.bst t)
        := ground_quotable_of_dec (@bst_dec t).
    End with_t.
    #[export] Existing Instances
      qlt_tree_dec
      qgt_tree_dec
      qbst_dec
      quote_bst
    .
  End Raw.
  Export (hints) Raw.

  #[export] Instance quote_t
    {elt : Type}
    {qelt : quotation_of elt}
    {quote_elt : ground_quotable elt} {quote_T_t : ground_quotable T.t}
    : ground_quotable (M.t elt) := (ltac:(induction 1; exact _)).
End QuoteFMapAVL.
