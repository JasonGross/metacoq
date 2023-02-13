Local Set Warnings Append "-masking-absolute-name".
From Coq Require Import MSetInterface MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From MetaCoq.Quotation.ToTemplate Require Export Init.
From MetaCoq.Quotation.ToTemplate Require Export (hints) Coq.Numbers Coq.Init Coq.Lists Coq.Structures.
From MetaCoq.Quotation.ToTemplate Require Import Coq.Structures.

(* The parameters *)
Module Type QuotationOfWSetsOn (E : DecidableType) (Import W : WSetsOn E).
  #[export] Declare Instance qt : quotation_of t.
  #[export] Declare Instance qempty : quotation_of empty.
  #[export] Declare Instance qis_empty : quotation_of is_empty.
  #[export] Declare Instance qmem : quotation_of mem.
  #[export] Declare Instance qadd : quotation_of add.
  #[export] Declare Instance qsingleton : quotation_of singleton.
  #[export] Declare Instance qremove : quotation_of remove.
  #[export] Declare Instance qunion : quotation_of union.
  #[export] Declare Instance qinter : quotation_of inter.
  #[export] Declare Instance qdiff : quotation_of diff.
  #[export] Declare Instance qequal : quotation_of equal.
  #[export] Declare Instance qsubset : quotation_of subset.
  #[export] Declare Instance qfold : quotation_of fold.
  #[export] Declare Instance qfor_all : quotation_of for_all.
  #[export] Declare Instance qexists_ : quotation_of exists_.
  #[export] Declare Instance qfilter : quotation_of filter.
  #[export] Declare Instance qpartition : quotation_of partition.
  #[export] Declare Instance qcardinal : quotation_of cardinal.
  #[export] Declare Instance qelements : quotation_of elements.
  #[export] Declare Instance qchoose : quotation_of choose.
  #[export] Declare Instance qIn : quotation_of In.
  #[export] Declare Instance qIn_compat : quotation_of In_compat.
  #[export] Declare Instance qeq_equiv : quotation_of eq_equiv.
  #[export] Declare Instance qeq_dec : quotation_of eq_dec.
  #[export] Declare Instance qmem_spec : quotation_of mem_spec.
  #[export] Declare Instance qequal_spec : quotation_of equal_spec.
  #[export] Declare Instance qsubset_spec : quotation_of subset_spec.
  #[export] Declare Instance qempty_spec : quotation_of empty_spec.
  #[export] Declare Instance qis_empty_spec : quotation_of is_empty_spec.
  #[export] Declare Instance qadd_spec : quotation_of add_spec.
  #[export] Declare Instance qremove_spec : quotation_of remove_spec.
  #[export] Declare Instance qsingleton_spec : quotation_of singleton_spec.
  #[export] Declare Instance qunion_spec : quotation_of union_spec.
  #[export] Declare Instance qinter_spec : quotation_of inter_spec.
  #[export] Declare Instance qdiff_spec : quotation_of diff_spec.
  #[export] Declare Instance qfold_spec : quotation_of fold_spec.
  #[export] Declare Instance qcardinal_spec : quotation_of cardinal_spec.
  #[export] Declare Instance qfilter_spec : quotation_of filter_spec.
  #[export] Declare Instance qfor_all_spec : quotation_of for_all_spec.
  #[export] Declare Instance qexists_spec : quotation_of exists_spec.
  #[export] Declare Instance qpartition_spec1 : quotation_of partition_spec1.
  #[export] Declare Instance qpartition_spec2 : quotation_of partition_spec2.
  #[export] Declare Instance qelements_spec1 : quotation_of elements_spec1.
  #[export] Declare Instance qelements_spec2w : quotation_of elements_spec2w.
  #[export] Declare Instance qchoose_spec1 : quotation_of choose_spec1.
  #[export] Declare Instance qchoose_spec2 : quotation_of choose_spec2.
End QuotationOfWSetsOn.

Module Type WFactsOnSig (E : DecidableType) (M : WSetsOn E) := Nop <+ WFactsOn E M.
Module Type WFactsSig (M : WSets) := Nop <+ WFacts M.
Module Type FactsSig (M : WSets) := Nop <+ Facts M.
Module Type WDecideOnSig (E : DecidableType) (M : WSetsOn E) := Nop <+ WDecideOn E M.
Module Type WDecideSig (M : WSets) := Nop <+ WDecide M.
Module Type DecideSig (M : WSets) := Nop <+ Decide M.
Module Type WPropertiesOnSig (E : DecidableType) (M : WSetsOn E) := Nop <+ WPropertiesOn E M.
Module Type WPropertiesSig (M : WSets) := Nop <+ WProperties M.
Module Type PropertiesSig (M : WSets) := Nop <+ Properties M.
Module Type OrdPropertiesSig (M : Sets) := Nop <+ OrdProperties M.

(* the definitions *)
Module ExtraQuotationOfWSetsOn (E : DecidableType) (Import W : WSetsOn E) (qE : QuotationOfDecidableType E) (Import qW : QuotationOfWSetsOn E W).
  Import (hints) qE.

  #[export] Instance qelt : quotation_of W.elt := ltac:(cbv [W.elt]; exact _).
  #[export] Instance qEqual : quotation_of W.Equal := ltac:(cbv [W.Equal]; exact _).
  #[export] Instance qSubset : quotation_of W.Subset := ltac:(cbv [W.Subset]; exact _).
  #[export] Instance qEmpty : quotation_of W.Empty := ltac:(cbv [W.Empty]; exact _).
  #[export] Instance qFor_all : quotation_of W.For_all := ltac:(cbv [W.For_all]; exact _).
  #[export] Instance qExists : quotation_of W.Exists := ltac:(cbv [W.Exists]; exact _).
  #[export] Instance qeq : quotation_of W.eq := ltac:(cbv [W.eq]; exact _).

  Module QuotationOfWFactsOn (WFacts : WFactsOnSig E W).
    #[export] Instance qeqb : quotation_of WFacts.eqb := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qIn_1 : quotation_of WFacts.In_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qmem_1 : quotation_of WFacts.mem_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qmem_2 : quotation_of WFacts.mem_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qequal_1 : quotation_of WFacts.equal_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qequal_2 : quotation_of WFacts.equal_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_1 : quotation_of WFacts.subset_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_2 : quotation_of WFacts.subset_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qis_empty_1 : quotation_of WFacts.is_empty_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qis_empty_2 : quotation_of WFacts.is_empty_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_1 : quotation_of WFacts.add_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_2 : quotation_of WFacts.add_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_3 : quotation_of WFacts.add_3 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_1 : quotation_of WFacts.remove_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_2 : quotation_of WFacts.remove_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_3 : quotation_of WFacts.remove_3 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsingleton_1 : quotation_of WFacts.singleton_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsingleton_2 : quotation_of WFacts.singleton_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_1 : quotation_of WFacts.union_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_2 : quotation_of WFacts.union_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_3 : quotation_of WFacts.union_3 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_1 : quotation_of WFacts.inter_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_2 : quotation_of WFacts.inter_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_3 : quotation_of WFacts.inter_3 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qdiff_1 : quotation_of WFacts.diff_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qdiff_2 : quotation_of WFacts.diff_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qdiff_3 : quotation_of WFacts.diff_3 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfilter_1 : quotation_of WFacts.filter_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfilter_2 : quotation_of WFacts.filter_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfilter_3 : quotation_of WFacts.filter_3 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfor_all_1 : quotation_of WFacts.for_all_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfor_all_2 : quotation_of WFacts.for_all_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qexists_1 : quotation_of WFacts.exists_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qexists_2 : quotation_of WFacts.exists_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qelements_1 : quotation_of WFacts.elements_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qelements_2 : quotation_of WFacts.elements_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qIn_eq_iff : quotation_of WFacts.In_eq_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qmem_iff : quotation_of WFacts.mem_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qnot_mem_iff : quotation_of WFacts.not_mem_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qequal_iff : quotation_of WFacts.equal_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_iff : quotation_of WFacts.subset_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qempty_iff : quotation_of WFacts.empty_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qis_empty_iff : quotation_of WFacts.is_empty_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsingleton_iff : quotation_of WFacts.singleton_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_iff : quotation_of WFacts.add_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_neq_iff : quotation_of WFacts.add_neq_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_iff : quotation_of WFacts.remove_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_neq_iff : quotation_of WFacts.remove_neq_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfor_all_iff : quotation_of WFacts.for_all_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qexists_iff : quotation_of WFacts.exists_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qelements_iff : quotation_of WFacts.elements_iff := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qmem_b : quotation_of WFacts.mem_b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qempty_b : quotation_of WFacts.empty_b := ltac:(unfold_quotation_of (); exact _).
     (* too slow *)
     (*
     #[export] Instance qadd_b : quotation_of WFacts.add_b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_neq_b : quotation_of WFacts.add_neq_b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_b : quotation_of WFacts.remove_b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_neq_b : quotation_of WFacts.remove_neq_b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsingleton_b : quotation_of WFacts.singleton_b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_b : quotation_of WFacts.union_b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_b : quotation_of WFacts.inter_b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qdiff_b : quotation_of WFacts.diff_b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qelements_b : quotation_of WFacts.elements_b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfilter_b : quotation_of WFacts.filter_b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfor_all_b : quotation_of WFacts.for_all_b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qexists_b : quotation_of WFacts.exists_b := ltac:(unfold_quotation_of (); exact _).*)
     #[export] Instance qIn_m : quotation_of WFacts.In_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qEmpty_m : quotation_of WFacts.Empty_m := ltac:(unfold_quotation_of (); exact _).
     (* too slow *)
     (*
     #[export] Instance qis_empty_m : quotation_of WFacts.is_empty_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qmem_m : quotation_of WFacts.mem_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsingleton_m : quotation_of WFacts.singleton_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_m : quotation_of WFacts.add_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_m : quotation_of WFacts.remove_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_m : quotation_of WFacts.union_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_m : quotation_of WFacts.inter_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qdiff_m : quotation_of WFacts.diff_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qSubset_m : quotation_of WFacts.Subset_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_m : quotation_of WFacts.subset_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qequal_m : quotation_of WFacts.equal_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qSubsetSetoid : quotation_of WFacts.SubsetSetoid := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qSubset_refl : quotation_of WFacts.Subset_refl := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qSubset_trans : quotation_of WFacts.Subset_trans := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qIn_s_m : quotation_of WFacts.In_s_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qEmpty_s_m : quotation_of WFacts.Empty_s_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_s_m : quotation_of WFacts.add_s_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_s_m : quotation_of WFacts.remove_s_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_s_m : quotation_of WFacts.union_s_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_s_m : quotation_of WFacts.inter_s_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qdiff_s_m : quotation_of WFacts.diff_s_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfilter_equal : quotation_of WFacts.filter_equal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfilter_subset : quotation_of WFacts.filter_subset := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfilter_ext : quotation_of WFacts.filter_ext := ltac:(unfold_quotation_of (); exact _).
      *)
  End QuotationOfWFactsOn.

  Module QuotationOfWDecideOn (WDecide : WDecideOnSig E W).
    Module qF := QuotationOfWFactsOn WDecide.F.
    Export (hints) qF.
    Module qMSetDecideAuxiliary.
      (*#[export] Declare Instance qMSet_elt_Prop : inductive_quotation_of WDecide.MSetDecideAuxiliary.MSet_elt_Prop.
      #[export] Declare Instance qMSet_Prop : inductive_quotation_of WDecide.MSetDecideAuxiliary.MSet_Prop.*)
      #[export] Instance qeq_refl_iff : quotation_of WDecide.MSetDecideAuxiliary.eq_refl_iff := ltac:(unfold_quotation_of (); exact _).
      #[export] Instance qdec_In : quotation_of WDecide.MSetDecideAuxiliary.dec_In := ltac:(unfold_quotation_of (); exact _).
      #[export] Instance qdec_eq : quotation_of WDecide.MSetDecideAuxiliary.dec_eq := ltac:(unfold_quotation_of (); exact _).
    End qMSetDecideAuxiliary.
    Export (hints) qMSetDecideAuxiliary.
  End QuotationOfWDecideOn.

  Module QuotationOfWPropertiesOn (WProperties : WPropertiesOnSig E W).
    Module qDec := QuotationOfWDecideOn WProperties.Dec.
    Export (hints) qDec.
    #[export] Instance qIn_dec : quotation_of WProperties.In_dec := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qAdd : quotation_of WProperties.Add := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qAdd_Equal : quotation_of WProperties.Add_Equal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qequal_refl : quotation_of WProperties.equal_refl := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qequal_sym : quotation_of WProperties.equal_sym := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qequal_trans : quotation_of WProperties.equal_trans := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_refl : quotation_of WProperties.subset_refl := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_trans : quotation_of WProperties.subset_trans := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_antisym : quotation_of WProperties.subset_antisym := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_equal : quotation_of WProperties.subset_equal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_empty : quotation_of WProperties.subset_empty := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_remove_3 : quotation_of WProperties.subset_remove_3 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_diff : quotation_of WProperties.subset_diff := ltac:(unfold_quotation_of (); exact _).
     (*
     #[export] Instance qsubset_add_3 : quotation_of WProperties.subset_add_3 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_add_2 : quotation_of WProperties.subset_add_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qin_subset : quotation_of WProperties.in_subset := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qdouble_inclusion : quotation_of WProperties.double_inclusion := ltac:(unfold_quotation_of (); exact _).*)
     #[export] Instance qempty_is_empty_1 : quotation_of WProperties.empty_is_empty_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qempty_is_empty_2 : quotation_of WProperties.empty_is_empty_2 := ltac:(unfold_quotation_of (); exact _).
     (*
     #[export] Instance qadd_equal : quotation_of WProperties.add_equal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_add : quotation_of WProperties.add_add := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_equal : quotation_of WProperties.remove_equal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qEqual_remove : quotation_of WProperties.Equal_remove := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_remove : quotation_of WProperties.add_remove := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_add : quotation_of WProperties.remove_add := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsingleton_equal_add : quotation_of WProperties.singleton_equal_add := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_singleton_empty : quotation_of WProperties.remove_singleton_empty := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_sym : quotation_of WProperties.union_sym := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_subset_equal : quotation_of WProperties.union_subset_equal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_equal_1 : quotation_of WProperties.union_equal_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_equal_2 : quotation_of WProperties.union_equal_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_assoc : quotation_of WProperties.union_assoc := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_union_singleton : quotation_of WProperties.add_union_singleton := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_add : quotation_of WProperties.union_add := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_remove_add_1 : quotation_of WProperties.union_remove_add_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_remove_add_2 : quotation_of WProperties.union_remove_add_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_subset_1 : quotation_of WProperties.union_subset_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_subset_2 : quotation_of WProperties.union_subset_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_subset_3 : quotation_of WProperties.union_subset_3 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_subset_4 : quotation_of WProperties.union_subset_4 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_subset_5 : quotation_of WProperties.union_subset_5 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qempty_union_1 : quotation_of WProperties.empty_union_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qempty_union_2 : quotation_of WProperties.empty_union_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qnot_in_union : quotation_of WProperties.not_in_union := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_sym : quotation_of WProperties.inter_sym := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_subset_equal : quotation_of WProperties.inter_subset_equal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_equal_1 : quotation_of WProperties.inter_equal_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_equal_2 : quotation_of WProperties.inter_equal_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_assoc : quotation_of WProperties.inter_assoc := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_inter_1 : quotation_of WProperties.union_inter_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_inter_2 : quotation_of WProperties.union_inter_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_add_1 : quotation_of WProperties.inter_add_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_add_2 : quotation_of WProperties.inter_add_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qempty_inter_1 : quotation_of WProperties.empty_inter_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qempty_inter_2 : quotation_of WProperties.empty_inter_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_subset_1 : quotation_of WProperties.inter_subset_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_subset_2 : quotation_of WProperties.inter_subset_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_subset_3 : quotation_of WProperties.inter_subset_3 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qempty_diff_1 : quotation_of WProperties.empty_diff_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qempty_diff_2 : quotation_of WProperties.empty_diff_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qdiff_subset : quotation_of WProperties.diff_subset := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qdiff_subset_equal : quotation_of WProperties.diff_subset_equal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_diff_singleton : quotation_of WProperties.remove_diff_singleton := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qdiff_inter_empty : quotation_of WProperties.diff_inter_empty := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qdiff_inter_all : quotation_of WProperties.diff_inter_all := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qAdd_add : quotation_of WProperties.Add_add := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qAdd_remove : quotation_of WProperties.Add_remove := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_Add : quotation_of WProperties.union_Add := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_Add : quotation_of WProperties.inter_Add := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_Equal : quotation_of WProperties.union_Equal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qinter_Add_2 : quotation_of WProperties.inter_Add_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qelements_Empty : quotation_of WProperties.elements_Empty := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qelements_empty : quotation_of WProperties.elements_empty := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qof_list : quotation_of WProperties.of_list := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qto_list : quotation_of WProperties.to_list := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qof_list_1 : quotation_of WProperties.of_list_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qof_list_2 : quotation_of WProperties.of_list_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qof_list_3 : quotation_of WProperties.of_list_3 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_spec_right : quotation_of WProperties.fold_spec_right := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_rec : quotation_of WProperties.fold_rec := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_rec_bis : quotation_of WProperties.fold_rec_bis := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_rec_nodep : quotation_of WProperties.fold_rec_nodep := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_rec_weak : quotation_of WProperties.fold_rec_weak := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_rel : quotation_of WProperties.fold_rel := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qset_induction : quotation_of WProperties.set_induction := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qset_induction_bis : quotation_of WProperties.set_induction_bis := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_identity : quotation_of WProperties.fold_identity := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_0 : quotation_of WProperties.fold_0 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_1 : quotation_of WProperties.fold_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_2 : quotation_of WProperties.fold_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_1b : quotation_of WProperties.fold_1b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_commutes : quotation_of WProperties.fold_commutes := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_init : quotation_of WProperties.fold_init := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_equal : quotation_of WProperties.fold_equal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_empty : quotation_of WProperties.fold_empty := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_add : quotation_of WProperties.fold_add := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_fold : quotation_of WProperties.add_fold := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_fold_1 : quotation_of WProperties.remove_fold_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_fold_2 : quotation_of WProperties.remove_fold_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_union_inter : quotation_of WProperties.fold_union_inter := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_diff_inter : quotation_of WProperties.fold_diff_inter := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_union : quotation_of WProperties.fold_union := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qfold_plus : quotation_of WProperties.fold_plus := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qcardinal_fold : quotation_of WProperties.cardinal_fold := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qcardinal_0 : quotation_of WProperties.cardinal_0 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qcardinal_1 : quotation_of WProperties.cardinal_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qcardinal_2 : quotation_of WProperties.cardinal_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qcardinal_Empty : quotation_of WProperties.cardinal_Empty := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qcardinal_inv_1 : quotation_of WProperties.cardinal_inv_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qcardinal_inv_2 : quotation_of WProperties.cardinal_inv_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qcardinal_inv_2b : quotation_of WProperties.cardinal_inv_2b := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qEqual_cardinal : quotation_of WProperties.Equal_cardinal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qcardinal_m : quotation_of WProperties.cardinal_m := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qempty_cardinal : quotation_of WProperties.empty_cardinal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsingleton_cardinal : quotation_of WProperties.singleton_cardinal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qdiff_inter_cardinal : quotation_of WProperties.diff_inter_cardinal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_cardinal : quotation_of WProperties.union_cardinal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_cardinal : quotation_of WProperties.subset_cardinal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qsubset_cardinal_lt : quotation_of WProperties.subset_cardinal_lt := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_inter_cardinal : quotation_of WProperties.union_inter_cardinal := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_cardinal_inter : quotation_of WProperties.union_cardinal_inter := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qunion_cardinal_le : quotation_of WProperties.union_cardinal_le := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_cardinal_1 : quotation_of WProperties.add_cardinal_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qadd_cardinal_2 : quotation_of WProperties.add_cardinal_2 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_cardinal_1 : quotation_of WProperties.remove_cardinal_1 := ltac:(unfold_quotation_of (); exact _).
     #[export] Instance qremove_cardinal_2 : quotation_of WProperties.remove_cardinal_2 := ltac:(unfold_quotation_of (); exact _).*)
  End QuotationOfWPropertiesOn.
End ExtraQuotationOfWSetsOn.

Module Type QuotationOfSetsOn (E : Orders.OrderedType) (Import W : SetsOn E).
    Parameter compare : t -> t -> comparison.
  (** Total ordering between sets. Can be used as the ordering function
  for doing sets of sets. *)

  Parameter min_elt : t -> option elt.
  (** Return the smallest element of the given set
  (with respect to the [E.compare] ordering),
  or [None] if the set is empty. *)

  Parameter max_elt : t -> option elt.
  (** Same as [min_elt], but returns the largest element of the
  given set. *)

End HasOrdOps.

Module Type Ops (E : OrderedType) := WOps E <+ HasOrdOps.


Module Type SetsOn (E : OrderedType).
  Include WSetsOn E <+ HasOrdOps <+ HasLt <+ IsStrOrder.

  Section Spec.
  Variable s s': t.
  Variable x y : elt.

  Parameter compare_spec : CompSpec eq lt s s' (compare s s').

  (** Additional specification of [elements] *)
  Parameter elements_spec2 : sort E.lt (elements s).

  (** Remark: since [fold] is specified via [elements], this stronger
   specification of [elements] has an indirect impact on [fold],
   which can now be proved to receive elements in increasing order.
  *)

  Parameter min_elt_spec1 : min_elt s = Some x -> In x s.
  Parameter min_elt_spec2 : min_elt s = Some x -> In y s -> ~ E.lt y x.
  Parameter min_elt_spec3 : min_elt s = None -> Empty s.

  Parameter max_elt_spec1 : max_elt s = Some x -> In x s.
  Parameter max_elt_spec2 : max_elt s = Some x -> In y s -> ~ E.lt x y.
  Parameter max_elt_spec3 : max_elt s = None -> Empty s.

  (** Additional specification of [choose] *)
  Parameter choose_spec3 : choose s = Some x -> choose s' = Some y ->
    Equal s s' -> E.eq x y.



(* the definitions *)
Module ExtraQuotationOfSetsOn (E : Orders.OrderedType) (Import W : SetsOn E) (qE : QuotationOfOrderedType E) (Import qW : QuotationOfWSetsOn E W).
  Import (hints) qE.


Module QuoteWSetsOn (E : DecidableType) (Import W : WSetsOn E) (qE : QuotationOfDecidableType E) (qW : QuotationOfWSetsOn E W).
  Export (hints) qE.
  Export (hints) qW.
  Module qW' := ExtraQuotationOfWSetsOn E W qE qW.
  Export (hints) qW'.
  Module WFacts := WFactsOn E W.
  Module WProperties := WPropertiesOn E W.
  Module WDecide := WDecideOn E W.
  Module qWFacts := qW'.QuotationOfWFactsOn WFacts.
  Module qWProperties := qW'.QuotationOfWPropertiesOn WProperties.
  Module qWDecide := qW'.QuotationOfWDecideOn WDecide.
  Export (hints) qWFacts qWProperties qWDecide.

  #[export] Instance quote_In {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (In x y)
    := ground_quotable_of_dec (WProperties.In_dec x y).
  #[export] Instance quote_neg_In {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (~In x y)
    := ground_quotable_neg_of_dec (WProperties.In_dec x y).
  #[export] Instance quote_Equal {x y} {qx : quotation_of x} {qy : quotation_of y}  : ground_quotable (Equal x y)
    := ground_quotable_of_dec (eq_dec x y).
  #[export] Instance quote_neg_Equal {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (~Equal x y)
    := ground_quotable_neg_of_dec (eq_dec x y).
  #[export] Instance quote_Subset {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (Subset x y) := ground_quotable_of_iff (@subset_spec x y).
  #[export] Instance quote_neg_Subset {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (~Subset x y) := quote_neg_of_iff (@subset_spec x y).
  #[export] Instance quote_Empty {x} {qx : quotation_of x} : ground_quotable (Empty x) := ground_quotable_of_iff (conj (@WProperties.empty_is_empty_2 x) (@WProperties.empty_is_empty_1 x)).
  #[export] Instance quote_neg_Empty {x} {qx : quotation_of x} : ground_quotable (~Empty x) := quote_neg_of_iff (conj (@WProperties.empty_is_empty_2 x) (@WProperties.empty_is_empty_1 x)).
  #[export] Instance quote_Add {x s s'} {qx : quotation_of x} {qs : quotation_of s} {qs' : quotation_of s'} : ground_quotable (WProperties.Add x s s')
    := ground_quotable_of_iff (iff_sym (WProperties.Add_Equal _ _ _)).
  #[export] Instance quote_neg_Add {x s s'} {qx : quotation_of x} {qs : quotation_of s} {qs' : quotation_of s'} : ground_quotable (~WProperties.Add x s s')
    := quote_neg_of_iff (iff_sym (WProperties.Add_Equal _ _ _)).
  Definition For_all_alt (P : elt -> Prop) (s : t) : Prop
    := List.Forall P (elements s).
  #[local] Hint Extern 1 (E.eq _ _) => reflexivity : core.
  Lemma For_all_alt_iff {P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {s}
    : For_all_alt P s <-> For_all P s.
  Proof using Type.
    cbv [For_all_alt For_all].
    setoid_rewrite WFacts.elements_iff.
    induction (elements s) as [|x xs IH].
    { split; solve [ constructor | inversion 2 ]. }
    { setoid_rewrite Forall_cons_iff; setoid_rewrite InA_cons; setoid_rewrite IH.
      intuition auto.
      eapply P_Proper; (idtac + symmetry); eassumption. }
  Qed.
  #[export] Instance qFor_all_alt : quotation_of For_all_alt := ltac:(cbv [For_all_alt]; exact _).
  #[export] Instance qForall_all_iff : quotation_of (@For_all_alt_iff) := ltac:(unfold_quotation_of (); exact _).
  Definition quote_For_all {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {qP_Proper : quotation_of P_Proper} {qs : quotation_of s} : ground_quotable (For_all P s)
    := ground_quotable_of_iff For_all_alt_iff.
  Lemma For_all_forall_iff {P s} : (For_all P s) <-> (forall v, In v s -> P v).
  Proof using Type. reflexivity. Qed.
  Lemma For_all_forall2_iff {P s} : (For_all (fun v1 => For_all (P v1) s) s) <-> (forall v1 v2, In v1 s -> In v2 s -> P v1 v2).
  Proof using Type. cbv [For_all]; intuition eauto. Qed.
  #[export] Instance qFor_all_forall_iff : quotation_of (@For_all_forall_iff) := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qFor_all_forall2_iff : quotation_of (@For_all_forall2_iff) := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance quote_forall2_In {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_For_all : ground_quotable (For_all (fun v1 => For_all (P v1) s) s)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2)
    := ground_quotable_of_iff For_all_forall2_iff.

  Definition Exists_alt (P : elt -> Prop) (s : t) : Prop
    := List.Exists P (elements s).
  Lemma Exists_alt_iff {P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {s}
    : Exists_alt P s <-> Exists P s.
  Proof.
    cbv [Exists_alt Exists].
    setoid_rewrite WFacts.elements_iff.
    induction (elements s) as [|x xs IH].
    { split; try solve [ constructor | inversion 1 | intros [x [H H']]; inversion H ]. }
    { setoid_rewrite Exists_cons; setoid_rewrite InA_cons; setoid_rewrite IH.
      firstorder intuition auto. }
  Qed.
  Definition Exists_dec {P s} (P_dec : forall x, {P x} + {~P x}) {P_Proper : Proper (E.eq ==> Basics.impl) P} : {Exists P s} + {~Exists P s}.
  Proof.
    destruct (List.Exists_dec P (elements s) P_dec) as [H|H]; [ left | right ]; revert H.
    { intro H; apply Exists_alt_iff, H. }
    { intros H H'; apply H, Exists_alt_iff, H'. }
  Defined.
  #[export] Instance qExists_alt : quotation_of (@Exists_alt) := ltac:(cbv [Exists_alt]; exact _).
  #[export] Instance qExists_alt_iff : quotation_of (@Exists_alt_iff) := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qExists_dec : quotation_of (@Exists_dec) := ltac:(cbv [Exists_dec]; exact _).

  Definition quote_Exists_dec {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {qP_Proper : quotation_of P_Proper} {qs : quotation_of s} : ground_quotable (Exists P s)
    := ground_quotable_of_dec (Exists_dec P_dec).

  #[export] Hint Extern 13 (ground_quotable (For_all _ _))
  => simple notypeclasses refine (@quote_For_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) : typeclass_instances.
End QuoteWSetsOn.

Module QuoteSetsOn (E : OrderedType) (Import M : SetsOn E) (qE : QuotationOfOrderedType E) (qM : QuotationOfWSetsOn E M).
  Module Import QuoteSetsOnInner := QuoteWSetsOn E M qE qM.
  Export (hints) qE.
  Export (hints) QuoteSetsOnInner.
  Locate Module OrdProperties.
  Module Import MOrdProperties. Module E := E. Include M <+ OrdProperties. End MOrdProperties.

  Definition above x s : bool := for_all (fun y => if ME.lt_dec y x then true else false) s.
  Definition below x s : bool := for_all (fun y => if ME.lt_dec x y then true else false) s.
  Lemma above_spec x s : above x s = true <-> Above x s.
  Proof.
    cbv [Above above].
    rewrite for_all_spec
      by (intros ?? H; repeat (let H' := fresh in destruct ME.lt_dec as [H'|H']; rewrite ?H in H'); try reflexivity; tauto).
    cbv [For_all].
    split; intros H y H'; generalize (H y H'); destruct ME.lt_dec; try reflexivity; eauto; congruence.
  Qed.
  Lemma below_spec x s : below x s = true <-> Below x s.
  Proof.
    cbv [Below below].
    rewrite for_all_spec
      by (intros ?? H; repeat (let H' := fresh in destruct ME.lt_dec as [H'|H']; rewrite ?H in H'); try reflexivity; tauto).
    cbv [For_all].
    split; intros H y H'; generalize (H y H'); destruct ME.lt_dec; try reflexivity; eauto; congruence.
  Qed.
  #[export] Instance qabove : quotation_of above := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qAbove : quotation_of Above := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qabove_spec : quotation_of above_spec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance quote_Above {x s} {qx : quotation_of x} {qs : quotation_of s} : ground_quotable (Above x s)
    := ground_quotable_of_iff (above_spec x s).
    #[export] Instance quote_Below {x s} {qx : quotation_of x} {qs : quotation_of s} : ground_quotable (Below x s)
      := ground_quotable_of_iff (below_spec x s).
  End OnlyOrdDefinitions.

  Module OrdDefinitions.
    Include Definitions.
    Include OnlyOrdDefinitions.
  End OrdDefinitions.

  Include OnlyOrdDefinitions.

  Module Export OnlyOrdInstances.
    #[export] Existing Instances
     quote_Above
     quote_Below
    .
  End OnlyOrdInstances.
  Module Export OrdInstances.
    Export Instances.
    Export OnlyOrdInstances.
  End OrdInstances.
End QuoteSetsOn.

Module Type MSetAVL_MakeSig (T : OrderedType). Include MSetAVL.Make T. End MSetAVL_MakeSig.

Module QuoteMSetAVL (T : OrderedType) (M : MSetAVL_MakeSig T).
  Module Import QM := QuoteSetsOn T M.

  Module Definitions.
    Include QM.OrdDefinitions.

    Scheme Induction for M.Raw.tree Sort Type.
    Scheme Induction for M.Raw.tree Sort Set.
    Scheme Induction for M.Raw.tree Sort Prop.
    Scheme Case for M.Raw.tree Sort Type.
    Scheme Case for M.Raw.tree Sort Prop.
    Scheme Minimality for M.Raw.tree Sort Type.
    Scheme Minimality for M.Raw.tree Sort Set.
    Scheme Minimality for M.Raw.tree Sort Prop.

    Section with_t.
      Context {quote_T_t : ground_quotable T.t}
              {qRaw_tree : inductive_quotation_of M.Raw.tree}
              {qRaw_bst : inductive_quotation_of M.Raw.bst}
              {qt_ : inductive_quotation_of M.t_}.

      #[export] Instance quote_M_Raw_t : ground_quotable M.Raw.t := (ltac:(induction 1; exact _)).
      Fixpoint M_Raw_lt_tree_dec x t : { M.Raw.lt_tree x t } + {~ M.Raw.lt_tree x t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node z l n r
                 => match T.compare n x as c, M_Raw_lt_tree_dec x l, M_Raw_lt_tree_dec x r return CompareSpec _ _ _ c -> _ with
                    | Lt, left p2, left p3 => fun pfc => left _
                    | _, right pf, _ => fun pfc => right _
                    | _, _, right pf => fun pfc => right _
                    | _, _, _ => fun pfc => right _
                    end (T.compare_spec _ _)
               end;
          try solve [ inversion 1; inversion pfc
                    | inversion 1; inversion pfc; subst; auto;
                      match goal with
                      | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                        => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                      end
                    | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                    | intro f; inversion pfc; eapply M.Raw.MX.lt_irrefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
      Defined.
      Fixpoint M_Raw_gt_tree_dec x t : { M.Raw.gt_tree x t } + {~ M.Raw.gt_tree x t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node z l n r
                 => match T.compare n x as c, M_Raw_gt_tree_dec x l, M_Raw_gt_tree_dec x r return CompareSpec _ _ _ c -> _ with
                    | Gt, left p2, left p3 => fun pfc => left _
                    | _, right pf, _ => fun pfc => right _
                    | _, _, right pf => fun pfc => right _
                    | _, _, _ => fun pfc => right _
                    end (T.compare_spec _ _)
               end;
          try solve [ inversion 1; inversion pfc
                    | inversion 1; inversion pfc; subst; auto;
                      match goal with
                      | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                        => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                      end
                    | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                    | intro f; inversion pfc; eapply M.Raw.MX.lt_irrefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
      Defined.
      Fixpoint M_Raw_bst_dec t : { M.Raw.bst t } + {~ M.Raw.bst t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node z l n r
                 => match M_Raw_bst_dec l, M_Raw_bst_dec r, M_Raw_lt_tree_dec n l, M_Raw_gt_tree_dec n r with
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
      #[export] Instance quote_Raw_bst t : ground_quotable (M.Raw.bst t)
        := ground_quotable_of_dec (@M_Raw_bst_dec t).
      #[export] Instance quote_Raw_Ok s : ground_quotable (M.Raw.Ok s) := (ltac:(cbv [M.Raw.Ok]; exact _)).
      #[export] Instance quote_t : ground_quotable M.t := ltac:(induction 1; exact _).
    End with_t.
  End Definitions.
  Include Definitions.
  Module Export Instances.
    Export QM.OrdInstances.
    #[export] Existing Instances
     quote_M_Raw_t
     quote_Raw_bst
     quote_Raw_Ok
     quote_t
    .
  End Instances.
End QuoteMSetAVL.

Module QuoteUsualWSetsOn (E : UsualDecidableType) (Import M : WSetsOn E).
  Module Import QM := QuoteWSetsOn E M.

  Module Definitions.
    Notation quote_In := QM.quote_In.
    Notation quote_Equal := QM.quote_Equal.
    Notation quote_Subset := QM.quote_Subset.
    Notation quote_Empty := QM.quote_Empty.
    Notation quote_Add := QM.quote_Add.
    Notation quote_neg_In := QM.quote_neg_In.
    Notation quote_neg_Equal := QM.quote_neg_Equal.
    Notation quote_neg_Subset := QM.quote_neg_Subset.
    Notation quote_neg_Empty := QM.quote_neg_Empty.
    Notation quote_neg_Add := QM.quote_neg_Add.

    Section with_quote.
      Context {qelt : quotation_of elt} {qt : quotation_of t}
              {qIn : quotation_of In}
              {qeq_dec : quotation_of eq_dec}
              {qsubset_spec : quotation_of subset_spec}
              {qempty : quotation_of empty}
              {qadd : quotation_of add} {qelements : quotation_of elements}.

      #[export] Instance quote_For_all {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (For_all P s)
        := QM.quote_For_all.
      Definition quote_Exists_dec {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (Exists P s)
        := QM.quote_Exists_dec P_dec.
      #[export] Instance quote_forall2_In {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_elt : ground_quotable elt} {quote_P : forall x y, ground_quotable (P x y:Prop)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2) := _.
    End with_quote.
  End Definitions.

  Include Definitions.

  Module Export Instances.
    #[export] Existing Instances
     QM.quote_In
     QM.quote_Equal
     QM.quote_Subset
     QM.quote_Empty
     QM.quote_Add
     QM.quote_neg_In
     QM.quote_neg_Equal
     QM.quote_neg_Subset
     QM.quote_neg_Empty
     QM.quote_neg_Add
     quote_For_all
     quote_forall2_In
    .
  End Instances.
End QuoteUsualWSetsOn.

Module QuoteUsualSetsOn (E : UsualOrderedType) (Import M : SetsOn E).
  Module QM := QuoteUsualWSetsOn E M.
  Module QM' := QuoteSetsOn E M.

  Module Definitions := QM.Definitions <+ QM'.OnlyOrdDefinitions.
  Include Definitions.

  Module Export Instances := QM.Instances <+ QM'.OnlyOrdInstances.
End QuoteUsualSetsOn.

Module QuoteSetsOnWithLeibniz (E : OrderedTypeWithLeibniz) (Import M : SetsOn E).
  Module Import QM := QuoteSetsOn E M.

  Module Definitions.
    Notation quote_In := QM.quote_In.
    Notation quote_Equal := QM.quote_Equal.
    Notation quote_Subset := QM.quote_Subset.
    Notation quote_Empty := QM.quote_Empty.
    Notation quote_Add := QM.quote_Add.
    Notation quote_neg_In := QM.quote_neg_In.
    Notation quote_neg_Equal := QM.quote_neg_Equal.
    Notation quote_neg_Subset := QM.quote_neg_Subset.
    Notation quote_neg_Empty := QM.quote_neg_Empty.
    Notation quote_neg_Add := QM.quote_neg_Add.
    Notation quote_Above := QM.quote_Above.
    Notation quote_Below := QM.quote_Below.


    #[local] Instance all_P_Proper {P : E.t -> Prop} : Proper (E.eq ==> Basics.impl) P.
    Proof.
      intros ?? H.
      apply E.eq_leibniz in H; subst; exact id.
    Defined.

    Section with_quote.
      Context {qelt : quotation_of elt} {qt : quotation_of t}
              {qIn : quotation_of In}
              {qeq_dec : quotation_of eq_dec}
              {qsubset_spec : quotation_of subset_spec}
              {qempty : quotation_of empty}
              {qadd : quotation_of add} {qelements : quotation_of elements}.

      #[export] Instance quote_For_all {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (For_all P s)
        := QM.quote_For_all.
      Definition quote_Exists_dec {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (Exists P s)
        := QM.quote_Exists_dec P_dec.
      #[export] Instance quote_forall2_In {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_elt : ground_quotable elt} {quote_P : forall x y, ground_quotable (P x y:Prop)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2) := _.
    End with_quote.
  End Definitions.

  Include Definitions.

  Module Export Instances.
    #[export] Existing Instances
     QM.quote_In
     QM.quote_Equal
     QM.quote_Subset
     QM.quote_Empty
     QM.quote_Add
     QM.quote_neg_In
     QM.quote_neg_Equal
     QM.quote_neg_Subset
     QM.quote_neg_Empty
     QM.quote_neg_Add
     quote_For_all
     quote_forall2_In
     QM.quote_Above
     QM.quote_Below
    .
  End Instances.
End QuoteSetsOnWithLeibniz.

Module Type MSetList_MakeSig (T : OrderedType). Include MSetList.Make T. End MSetList_MakeSig.

Module QuoteMSetList (E : OrderedType) (Import M : MSetList_MakeSig E).
  Module Import QM := QuoteSetsOn E M.

  Module OnlyMSetListDefinitions.
    #[export] Instance quote_Ok {qE_compare : quotation_of E.compare} {qE_t : quotation_of E.t} {v} : ground_quotable (Raw.Ok v) := ltac:(cbv [Raw.Ok]; exact _).

    #[export] Instance quote_t_ {qE_t : quotation_of E.t} {qE_compare : quotation_of E.compare} {quoteE_t : ground_quotable E.t} {qM_Mkt : quotation_of M.Mkt} : ground_quotable t_ := ltac:(destruct 1; exact _).
  End OnlyMSetListDefinitions.

  Module Definitions := QM.Definitions <+ OnlyMSetListDefinitions.
  Include Definitions.

  Module OnlyMSetListInstances.
    #[export] Existing Instances
     quote_Ok
     quote_t_
    .
  End OnlyMSetListInstances.

  Module Export Instances := QM.Instances <+ OnlyMSetListInstances.
End QuoteMSetList.

Module QuoteMSetListWithLeibniz (E : OrderedTypeWithLeibniz) (Import M : MSetList_MakeSig E).
  Module QM := QuoteSetsOnWithLeibniz E M.
  Module QM' := QuoteMSetList E M.

  Module Definitions := QM.Definitions <+ QM'.OnlyMSetListDefinitions.
  Include Definitions.

  Module Export Instances := QM.Instances <+ QM'.OnlyMSetListInstances.
End QuoteMSetListWithLeibniz.
