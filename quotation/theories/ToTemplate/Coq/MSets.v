From Coq Require Import MSetInterface MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From MetaCoq.Quotation.ToTemplate Require Export Init.
From MetaCoq.Quotation.ToTemplate Require Export (hints) Coq.Numbers Coq.Init Coq.Lists Coq.Structures.
From MetaCoq.Quotation.ToTemplate Require Import Coq.Structures.

(* The parameters *)
Module Type QuotationOfWSetsOn (E : DecidableType) (Import W : WSetsOn E).
HERE  MetaCoq Run (tmDeclareQuotationOfModule (Some export) "W").
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

Module Type QuotationOfWSets (W : WSets) := QuotationOfWSetsOn W.E W.

Module Type QuotationOfSetsOn (E : OrderedType) (Import M : SetsOn E).
  Include QuotationOfWSetsOn E M.
  #[export] Declare Instance qcompare : quotation_of M.compare.
  #[export] Declare Instance qmin_elt : quotation_of M.min_elt.
  #[export] Declare Instance qmax_elt : quotation_of M.max_elt.
  #[export] Declare Instance qcompare_spec : quotation_of M.compare_spec.
  #[export] Declare Instance qelements_spec2 : quotation_of M.elements_spec2.
  #[export] Declare Instance qmin_elt_spec1 : quotation_of M.min_elt_spec1.
  #[export] Declare Instance qmin_elt_spec2 : quotation_of M.min_elt_spec2.
  #[export] Declare Instance qmin_elt_spec3 : quotation_of M.min_elt_spec3.
  #[export] Declare Instance qmax_elt_spec1 : quotation_of M.max_elt_spec1.
  #[export] Declare Instance qmax_elt_spec2 : quotation_of M.max_elt_spec2.
  #[export] Declare Instance qmax_elt_spec3 : quotation_of M.max_elt_spec3.
  #[export] Declare Instance qchoose_spec3 : quotation_of M.choose_spec3.
End QuotationOfSetsOn.

Module Type QuotationOfSets (M : Sets) := QuotationOfSetsOn M.E M.

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

Module Type QuotationOfWFactsOn (E : DecidableType) (M : WSetsOn E) (F : WFactsOnSig E M).
  #[export] Declare Instance qeqb : quotation_of F.eqb.
  #[export] Declare Instance qIn_1 : quotation_of F.In_1.
  #[export] Declare Instance qmem_1 : quotation_of F.mem_1.
  #[export] Declare Instance qmem_2 : quotation_of F.mem_2.
  #[export] Declare Instance qequal_1 : quotation_of F.equal_1.
  #[export] Declare Instance qequal_2 : quotation_of F.equal_2.
  #[export] Declare Instance qsubset_1 : quotation_of F.subset_1.
  #[export] Declare Instance qsubset_2 : quotation_of F.subset_2.
  #[export] Declare Instance qis_empty_1 : quotation_of F.is_empty_1.
  #[export] Declare Instance qis_empty_2 : quotation_of F.is_empty_2.
  #[export] Declare Instance qadd_1 : quotation_of F.add_1.
  #[export] Declare Instance qadd_2 : quotation_of F.add_2.
  #[export] Declare Instance qadd_3 : quotation_of F.add_3.
  #[export] Declare Instance qremove_1 : quotation_of F.remove_1.
  #[export] Declare Instance qremove_2 : quotation_of F.remove_2.
  #[export] Declare Instance qremove_3 : quotation_of F.remove_3.
  #[export] Declare Instance qsingleton_1 : quotation_of F.singleton_1.
  #[export] Declare Instance qsingleton_2 : quotation_of F.singleton_2.
  #[export] Declare Instance qunion_1 : quotation_of F.union_1.
  #[export] Declare Instance qunion_2 : quotation_of F.union_2.
  #[export] Declare Instance qunion_3 : quotation_of F.union_3.
  #[export] Declare Instance qinter_1 : quotation_of F.inter_1.
  #[export] Declare Instance qinter_2 : quotation_of F.inter_2.
  #[export] Declare Instance qinter_3 : quotation_of F.inter_3.
  #[export] Declare Instance qdiff_1 : quotation_of F.diff_1.
  #[export] Declare Instance qdiff_2 : quotation_of F.diff_2.
  #[export] Declare Instance qdiff_3 : quotation_of F.diff_3.
  #[export] Declare Instance qfilter_1 : quotation_of F.filter_1.
  #[export] Declare Instance qfilter_2 : quotation_of F.filter_2.
  #[export] Declare Instance qfilter_3 : quotation_of F.filter_3.
  #[export] Declare Instance qfor_all_1 : quotation_of F.for_all_1.
  #[export] Declare Instance qfor_all_2 : quotation_of F.for_all_2.
  #[export] Declare Instance qexists_1 : quotation_of F.exists_1.
  #[export] Declare Instance qexists_2 : quotation_of F.exists_2.
  #[export] Declare Instance qelements_1 : quotation_of F.elements_1.
  #[export] Declare Instance qelements_2 : quotation_of F.elements_2.
  #[export] Declare Instance qIn_eq_iff : quotation_of F.In_eq_iff.
  #[export] Declare Instance qmem_iff : quotation_of F.mem_iff.
  #[export] Declare Instance qnot_mem_iff : quotation_of F.not_mem_iff.
  #[export] Declare Instance qequal_iff : quotation_of F.equal_iff.
  #[export] Declare Instance qsubset_iff : quotation_of F.subset_iff.
  #[export] Declare Instance qempty_iff : quotation_of F.empty_iff.
  #[export] Declare Instance qis_empty_iff : quotation_of F.is_empty_iff.
  #[export] Declare Instance qsingleton_iff : quotation_of F.singleton_iff.
  #[export] Declare Instance qadd_iff : quotation_of F.add_iff.
  #[export] Declare Instance qadd_neq_iff : quotation_of F.add_neq_iff.
  #[export] Declare Instance qremove_iff : quotation_of F.remove_iff.
  #[export] Declare Instance qremove_neq_iff : quotation_of F.remove_neq_iff.
  #[export] Declare Instance qfor_all_iff : quotation_of F.for_all_iff.
  #[export] Declare Instance qexists_iff : quotation_of F.exists_iff.
  #[export] Declare Instance qelements_iff : quotation_of F.elements_iff.
  #[export] Declare Instance qmem_b : quotation_of F.mem_b.
  #[export] Declare Instance qempty_b : quotation_of F.empty_b.
  #[export] Declare Instance qadd_b : quotation_of F.add_b.
  #[export] Declare Instance qadd_neq_b : quotation_of F.add_neq_b.
  #[export] Declare Instance qremove_b : quotation_of F.remove_b.
  #[export] Declare Instance qremove_neq_b : quotation_of F.remove_neq_b.
  #[export] Declare Instance qsingleton_b : quotation_of F.singleton_b.
  #[export] Declare Instance qunion_b : quotation_of F.union_b.
  #[export] Declare Instance qinter_b : quotation_of F.inter_b.
  #[export] Declare Instance qdiff_b : quotation_of F.diff_b.
  #[export] Declare Instance qelements_b : quotation_of F.elements_b.
  #[export] Declare Instance qfilter_b : quotation_of F.filter_b.
  #[export] Declare Instance qfor_all_b : quotation_of F.for_all_b.
  #[export] Declare Instance qexists_b : quotation_of F.exists_b.
  #[export] Declare Instance qIn_m : quotation_of F.In_m.
  #[export] Declare Instance qEmpty_m : quotation_of F.Empty_m.
  #[export] Declare Instance qis_empty_m : quotation_of F.is_empty_m.
  #[export] Declare Instance qmem_m : quotation_of F.mem_m.
  #[export] Declare Instance qsingleton_m : quotation_of F.singleton_m.
  #[export] Declare Instance qadd_m : quotation_of F.add_m.
  #[export] Declare Instance qremove_m : quotation_of F.remove_m.
  #[export] Declare Instance qunion_m : quotation_of F.union_m.
  #[export] Declare Instance qinter_m : quotation_of F.inter_m.
  #[export] Declare Instance qdiff_m : quotation_of F.diff_m.
  #[export] Declare Instance qSubset_m : quotation_of F.Subset_m.
  #[export] Declare Instance qsubset_m : quotation_of F.subset_m.
  #[export] Declare Instance qequal_m : quotation_of F.equal_m.
  #[export] Declare Instance qSubsetSetoid : quotation_of F.SubsetSetoid.
  #[export] Declare Instance qSubset_refl : quotation_of F.Subset_refl.
  #[export] Declare Instance qSubset_trans : quotation_of F.Subset_trans.
  #[export] Declare Instance qIn_s_m : quotation_of F.In_s_m.
  #[export] Declare Instance qEmpty_s_m : quotation_of F.Empty_s_m.
  #[export] Declare Instance qadd_s_m : quotation_of F.add_s_m.
  #[export] Declare Instance qremove_s_m : quotation_of F.remove_s_m.
  #[export] Declare Instance qunion_s_m : quotation_of F.union_s_m.
  #[export] Declare Instance qinter_s_m : quotation_of F.inter_s_m.
  #[export] Declare Instance qdiff_s_m : quotation_of F.diff_s_m.
  #[export] Declare Instance qfilter_equal : quotation_of (@F.filter_equal).
  #[export] Declare Instance qfilter_subset : quotation_of (@F.filter_subset).
  #[export] Declare Instance qfilter_ext : quotation_of F.filter_ext.
End QuotationOfWFactsOn.

Module Type QuotationOfWFacts (M : WSets) (F : WFactsSig M) := QuotationOfWFactsOn M.E M F.

Module Type QuotationOfWDecideOn (E : DecidableType) (M : WSetsOn E) (F : WDecideOnSig E M).
  Module qF := Nop <+ QuotationOfWFactsOn E M F.F.
  Module qMSetDecideAuxiliary.
    #[export] Declare Instance qMSet_elt_Prop : inductive_quotation_of F.MSetDecideAuxiliary.MSet_elt_Prop.
    #[export] Declare Instance qMSet_Prop : inductive_quotation_of F.MSetDecideAuxiliary.MSet_Prop.
    #[export] Declare Instance qeq_refl_iff : quotation_of F.MSetDecideAuxiliary.eq_refl_iff.
    #[export] Declare Instance qdec_In : quotation_of F.MSetDecideAuxiliary.dec_In.
    #[export] Declare Instance qdec_eq : quotation_of F.MSetDecideAuxiliary.dec_eq.
  End qMSetDecideAuxiliary.
  Export (hints) qF qMSetDecideAuxiliary.
End QuotationOfWDecideOn.

Module Type QuotationOfWDecide (M : WSets) (F : WDecideSig M) := QuotationOfWDecideOn M.E M F.

Module Type QuotationOfWPropertiesOn (E : DecidableType) (M : WSetsOn E) (F : WPropertiesOnSig E M).
  Module qDec := Nop <+ QuotationOfWDecideOn E M F.Dec.
  Module qFM := Nop <+ QuotationOfWFactsOn E M F.FM.
  Export (hints) qDec qFM.
  #[export] Declare Instance qIn_dec : quotation_of F.In_dec.
  #[export] Declare Instance qAdd : quotation_of F.Add.
  #[export] Declare Instance qAdd_Equal : quotation_of F.Add_Equal.
  #[export] Declare Instance qequal_refl : quotation_of F.equal_refl.
  #[export] Declare Instance qequal_sym : quotation_of F.equal_sym.
  #[export] Declare Instance qequal_trans : quotation_of F.equal_trans.
  #[export] Declare Instance qsubset_refl : quotation_of F.subset_refl.
  #[export] Declare Instance qsubset_trans : quotation_of F.subset_trans.
  #[export] Declare Instance qsubset_antisym : quotation_of F.subset_antisym.
  #[export] Declare Instance qsubset_equal : quotation_of F.subset_equal.
  #[export] Declare Instance qsubset_empty : quotation_of F.subset_empty.
  #[export] Declare Instance qsubset_remove_3 : quotation_of F.subset_remove_3.
  #[export] Declare Instance qsubset_diff : quotation_of F.subset_diff.
  #[export] Declare Instance qsubset_add_3 : quotation_of F.subset_add_3.
  #[export] Declare Instance qsubset_add_2 : quotation_of F.subset_add_2.
  #[export] Declare Instance qin_subset : quotation_of F.in_subset.
  #[export] Declare Instance qdouble_inclusion : quotation_of F.double_inclusion.
  #[export] Declare Instance qempty_is_empty_1 : quotation_of F.empty_is_empty_1.
  #[export] Declare Instance qempty_is_empty_2 : quotation_of F.empty_is_empty_2.
  #[export] Declare Instance qadd_equal : quotation_of F.add_equal.
  #[export] Declare Instance qadd_add : quotation_of F.add_add.
  #[export] Declare Instance qremove_equal : quotation_of F.remove_equal.
  #[export] Declare Instance qEqual_remove : quotation_of F.Equal_remove.
  #[export] Declare Instance qadd_remove : quotation_of F.add_remove.
  #[export] Declare Instance qremove_add : quotation_of F.remove_add.
  #[export] Declare Instance qsingleton_equal_add : quotation_of F.singleton_equal_add.
  #[export] Declare Instance qremove_singleton_empty : quotation_of F.remove_singleton_empty.
  #[export] Declare Instance qunion_sym : quotation_of F.union_sym.
  #[export] Declare Instance qunion_subset_equal : quotation_of F.union_subset_equal.
  #[export] Declare Instance qunion_equal_1 : quotation_of F.union_equal_1.
  #[export] Declare Instance qunion_equal_2 : quotation_of F.union_equal_2.
  #[export] Declare Instance qunion_assoc : quotation_of F.union_assoc.
  #[export] Declare Instance qadd_union_singleton : quotation_of F.add_union_singleton.
  #[export] Declare Instance qunion_add : quotation_of F.union_add.
  #[export] Declare Instance qunion_remove_add_1 : quotation_of F.union_remove_add_1.
  #[export] Declare Instance qunion_remove_add_2 : quotation_of F.union_remove_add_2.
  #[export] Declare Instance qunion_subset_1 : quotation_of F.union_subset_1.
  #[export] Declare Instance qunion_subset_2 : quotation_of F.union_subset_2.
  #[export] Declare Instance qunion_subset_3 : quotation_of F.union_subset_3.
  #[export] Declare Instance qunion_subset_4 : quotation_of F.union_subset_4.
  #[export] Declare Instance qunion_subset_5 : quotation_of F.union_subset_5.
  #[export] Declare Instance qempty_union_1 : quotation_of F.empty_union_1.
  #[export] Declare Instance qempty_union_2 : quotation_of F.empty_union_2.
  #[export] Declare Instance qnot_in_union : quotation_of F.not_in_union.
  #[export] Declare Instance qinter_sym : quotation_of F.inter_sym.
  #[export] Declare Instance qinter_subset_equal : quotation_of F.inter_subset_equal.
  #[export] Declare Instance qinter_equal_1 : quotation_of F.inter_equal_1.
  #[export] Declare Instance qinter_equal_2 : quotation_of F.inter_equal_2.
  #[export] Declare Instance qinter_assoc : quotation_of F.inter_assoc.
  #[export] Declare Instance qunion_inter_1 : quotation_of F.union_inter_1.
  #[export] Declare Instance qunion_inter_2 : quotation_of F.union_inter_2.
  #[export] Declare Instance qinter_add_1 : quotation_of F.inter_add_1.
  #[export] Declare Instance qinter_add_2 : quotation_of F.inter_add_2.
  #[export] Declare Instance qempty_inter_1 : quotation_of F.empty_inter_1.
  #[export] Declare Instance qempty_inter_2 : quotation_of F.empty_inter_2.
  #[export] Declare Instance qinter_subset_1 : quotation_of F.inter_subset_1.
  #[export] Declare Instance qinter_subset_2 : quotation_of F.inter_subset_2.
  #[export] Declare Instance qinter_subset_3 : quotation_of F.inter_subset_3.
  #[export] Declare Instance qempty_diff_1 : quotation_of F.empty_diff_1.
  #[export] Declare Instance qempty_diff_2 : quotation_of F.empty_diff_2.
  #[export] Declare Instance qdiff_subset : quotation_of F.diff_subset.
  #[export] Declare Instance qdiff_subset_equal : quotation_of F.diff_subset_equal.
  #[export] Declare Instance qremove_diff_singleton : quotation_of F.remove_diff_singleton.
  #[export] Declare Instance qdiff_inter_empty : quotation_of F.diff_inter_empty.
  #[export] Declare Instance qdiff_inter_all : quotation_of F.diff_inter_all.
  #[export] Declare Instance qAdd_add : quotation_of F.Add_add.
  #[export] Declare Instance qAdd_remove : quotation_of F.Add_remove.
  #[export] Declare Instance qunion_Add : quotation_of F.union_Add.
  #[export] Declare Instance qinter_Add : quotation_of F.inter_Add.
  #[export] Declare Instance qunion_Equal : quotation_of F.union_Equal.
  #[export] Declare Instance qinter_Add_2 : quotation_of F.inter_Add_2.
  #[export] Declare Instance qelements_Empty : quotation_of F.elements_Empty.
  #[export] Declare Instance qelements_empty : quotation_of F.elements_empty.
  #[export] Declare Instance qof_list : quotation_of F.of_list.
  #[export] Declare Instance qto_list : quotation_of F.to_list.
  #[export] Declare Instance qof_list_1 : quotation_of F.of_list_1.
  #[export] Declare Instance qof_list_2 : quotation_of F.of_list_2.
  #[export] Declare Instance qof_list_3 : quotation_of F.of_list_3.
  #[export] Declare Instance qfold_spec_right : quotation_of F.fold_spec_right.
  #[export] Declare Instance qfold_rec : quotation_of F.fold_rec.
  #[export] Declare Instance qfold_rec_bis : quotation_of F.fold_rec_bis.
  #[export] Declare Instance qfold_rec_nodep : quotation_of F.fold_rec_nodep.
  #[export] Declare Instance qfold_rec_weak : quotation_of F.fold_rec_weak.
  #[export] Declare Instance qfold_rel : quotation_of F.fold_rel.
  #[export] Declare Instance qset_induction : quotation_of F.set_induction.
  #[export] Declare Instance qset_induction_bis : quotation_of F.set_induction_bis.
  #[export] Declare Instance qfold_identity : quotation_of F.fold_identity.
  #[export] Declare Instance qfold_0 : quotation_of F.fold_0.
  #[export] Declare Instance qfold_1 : quotation_of F.fold_1.
  #[export] Declare Instance qfold_2 : quotation_of F.fold_2.
  #[export] Declare Instance qfold_1b : quotation_of F.fold_1b.
  #[export] Declare Instance qfold_commutes : quotation_of F.fold_commutes.
  #[export] Declare Instance qfold_init : quotation_of F.fold_init.
  #[export] Declare Instance qfold_equal : quotation_of F.fold_equal.
  #[export] Declare Instance qfold_empty : quotation_of F.fold_empty.
  #[export] Declare Instance qfold_add : quotation_of F.fold_add.
  #[export] Declare Instance qadd_fold : quotation_of F.add_fold.
  #[export] Declare Instance qremove_fold_1 : quotation_of F.remove_fold_1.
  #[export] Declare Instance qremove_fold_2 : quotation_of F.remove_fold_2.
  #[export] Declare Instance qfold_union_inter : quotation_of F.fold_union_inter.
  #[export] Declare Instance qfold_diff_inter : quotation_of F.fold_diff_inter.
  #[export] Declare Instance qfold_union : quotation_of F.fold_union.
  #[export] Declare Instance qfold_plus : quotation_of F.fold_plus.
  #[export] Declare Instance qcardinal_fold : quotation_of F.cardinal_fold.
  #[export] Declare Instance qcardinal_0 : quotation_of F.cardinal_0.
  #[export] Declare Instance qcardinal_1 : quotation_of F.cardinal_1.
  #[export] Declare Instance qcardinal_2 : quotation_of F.cardinal_2.
  #[export] Declare Instance qcardinal_Empty : quotation_of F.cardinal_Empty.
  #[export] Declare Instance qcardinal_inv_1 : quotation_of F.cardinal_inv_1.
  #[export] Declare Instance qcardinal_inv_2 : quotation_of F.cardinal_inv_2.
  #[export] Declare Instance qcardinal_inv_2b : quotation_of F.cardinal_inv_2b.
  #[export] Declare Instance qEqual_cardinal : quotation_of F.Equal_cardinal.
  #[export] Declare Instance qcardinal_m : quotation_of F.cardinal_m.
  #[export] Declare Instance qempty_cardinal : quotation_of F.empty_cardinal.
  #[export] Declare Instance qsingleton_cardinal : quotation_of F.singleton_cardinal.
  #[export] Declare Instance qdiff_inter_cardinal : quotation_of F.diff_inter_cardinal.
  #[export] Declare Instance qunion_cardinal : quotation_of F.union_cardinal.
  #[export] Declare Instance qsubset_cardinal : quotation_of F.subset_cardinal.
  #[export] Declare Instance qsubset_cardinal_lt : quotation_of F.subset_cardinal_lt.
  #[export] Declare Instance qunion_inter_cardinal : quotation_of F.union_inter_cardinal.
  #[export] Declare Instance qunion_cardinal_inter : quotation_of F.union_cardinal_inter.
  #[export] Declare Instance qunion_cardinal_le : quotation_of F.union_cardinal_le.
  #[export] Declare Instance qadd_cardinal_1 : quotation_of F.add_cardinal_1.
  #[export] Declare Instance qadd_cardinal_2 : quotation_of F.add_cardinal_2.
  #[export] Declare Instance qremove_cardinal_1 : quotation_of F.remove_cardinal_1.
  #[export] Declare Instance qremove_cardinal_2 : quotation_of F.remove_cardinal_2.
End QuotationOfWPropertiesOn.

Module Type QuotationOfWProperties (M : WSets) (F : WPropertiesSig M) := QuotationOfWPropertiesOn M.E M F.

Module Type QuotationOfOrdProperties (M : Sets) (F : OrdPropertiesSig M) (qE : QuotationOfOrderedType M.E).
  Module qME := QuotationOfOrderedTypeFacts M.E F.ME qE.
  (*Module qML := QuotationOfOrderedTypeLists M.E F.ML.*)
  Module qP := Nop <+ QuotationOfWProperties M F.P.
  Export (hints) qME (*qML*) qP.
  #[export] Declare Instance qsort_equivlistA_eqlistA : quotation_of F.sort_equivlistA_eqlistA.
  #[export] Declare Instance qgtb : quotation_of F.gtb.
  #[export] Declare Instance qleb : quotation_of F.leb.
  #[export] Declare Instance qelements_lt : quotation_of F.elements_lt.
  #[export] Declare Instance qelements_ge : quotation_of F.elements_ge.
  #[export] Declare Instance qgtb_1 : quotation_of F.gtb_1.
  #[export] Declare Instance qleb_1 : quotation_of F.leb_1.
  #[export] Declare Instance qgtb_compat : quotation_of F.gtb_compat.
  #[export] Declare Instance qleb_compat : quotation_of F.leb_compat.
  #[export] Declare Instance qelements_split : quotation_of F.elements_split.
  #[export] Declare Instance qelements_Add : quotation_of F.elements_Add.
  #[export] Declare Instance qAbove : quotation_of F.Above.
  #[export] Declare Instance qBelow : quotation_of F.Below.
  #[export] Declare Instance qelements_Add_Above : quotation_of F.elements_Add_Above.
  #[export] Declare Instance qelements_Add_Below : quotation_of F.elements_Add_Below.
  #[export] Declare Instance qset_induction_max : quotation_of F.set_induction_max.
  #[export] Declare Instance qset_induction_min : quotation_of F.set_induction_min.
  #[export] Declare Instance qfold_3 : quotation_of F.fold_3.
  #[export] Declare Instance qfold_4 : quotation_of F.fold_4.
  #[export] Declare Instance qfold_equal : quotation_of F.fold_equal.
  #[export] Declare Instance qadd_fold : quotation_of F.add_fold.
  #[export] Declare Instance qremove_fold_2 : quotation_of F.remove_fold_2.
  #[export] Declare Instance qchoose_equal : quotation_of F.choose_equal.
End QuotationOfOrdProperties.

Module QuoteWSetsOn (E : DecidableType) (Import W : WSetsOn E) (WProperties : WPropertiesOnSig E W) (qE : QuotationOfDecidableType E) (qW : QuotationOfWSetsOn E W) (qWProperties : QuotationOfWPropertiesOn E W WProperties).
  Export (hints) qE.
  Export (hints) qW.
  Export (hints) qWProperties.
  (*
  Module qW' := ExtraQuotationOfWSetsOn E W qE qW.
  Export (hints) qW'.
  Module WFacts := WFactsOn E W.
  Module WProperties := WPropertiesOn E W.
  Module WDecide := WDecideOn E W.
  Module qWFacts := qW'.QuotationOfWFactsOn WFacts.
  Module qWProperties := qW'.QuotationOfWPropertiesOn WProperties.
  Module qWDecide := qW'.QuotationOfWDecideOn WDecide.
  Export (hints) qWFacts qWProperties qWDecide.
   *)
  #[export] Instance qelt : quotation_of W.elt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qEqual : quotation_of W.Equal := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qSubset : quotation_of W.Subset := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qEmpty : quotation_of W.Empty := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qFor_all : quotation_of W.For_all := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qExists : quotation_of W.Exists := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq : quotation_of W.eq := ltac:(unfold_quotation_of (); exact _).

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
    setoid_rewrite WProperties.FM.elements_iff.
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
    setoid_rewrite WProperties.FM.elements_iff.
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

Module QuoteSets (Import M : Sets) (Import MOrdProperties : OrdPropertiesSig M) (qE : QuotationOfOrderedType M.E) (qM : QuotationOfSets M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties qE).
  Export (hints) qE qM qMOrdProperties.
  Include QuoteWSetsOn M.E M MOrdProperties.P qE qM qMOrdProperties.qP.

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
  #[export] Instance qbelow : quotation_of below := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qBelow : quotation_of Below := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qabove_spec : quotation_of above_spec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qbelow_spec : quotation_of below_spec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance quote_Above {x s} {qx : quotation_of x} {qs : quotation_of s} : ground_quotable (Above x s)
    := ground_quotable_of_iff (above_spec x s).
  #[export] Instance quote_Below {x s} {qx : quotation_of x} {qs : quotation_of s} : ground_quotable (Below x s)
    := ground_quotable_of_iff (below_spec x s).
End QuoteSets.

Module Export MSets.
  Module MSetAVL.
    Module Type MakeSig (T : OrderedType) := Nop <+ MSetAVL.Make T.
    Module Type QuotationOfMake (T : OrderedType) (M : MakeSig T).
      Module qRaw.
        #[export] Declare Instance qelt : quotation_of M.Raw.elt.
        #[export] Declare Instance qtree : inductive_quotation_of M.Raw.tree.
        #[export] Declare Instance qempty : quotation_of M.Raw.empty.
        #[export] Declare Instance qis_empty : quotation_of M.Raw.is_empty.
        #[export] Declare Instance qmem : quotation_of M.Raw.mem.
        #[export] Declare Instance qmin_elt : quotation_of M.Raw.min_elt.
        #[export] Declare Instance qmax_elt : quotation_of M.Raw.max_elt.
        #[export] Declare Instance qchoose : quotation_of M.Raw.choose.
        #[export] Declare Instance qfold : quotation_of (@M.Raw.fold).
        #[export] Declare Instance qelements_aux : quotation_of M.Raw.elements_aux.
        #[export] Declare Instance qelements : quotation_of M.Raw.elements.
        #[export] Declare Instance qrev_elements_aux : quotation_of M.Raw.rev_elements_aux.
        #[export] Declare Instance qrev_elements : quotation_of M.Raw.rev_elements.
        #[export] Declare Instance qcardinal : quotation_of M.Raw.cardinal.
        #[export] Declare Instance qmaxdepth : quotation_of M.Raw.maxdepth.
        #[export] Declare Instance qmindepth : quotation_of M.Raw.mindepth.
        #[export] Declare Instance qfor_all : quotation_of M.Raw.for_all.
        #[export] Declare Instance qexists_ : quotation_of M.Raw.exists_.
        #[export] Declare Instance qenumeration : inductive_quotation_of M.Raw.enumeration.
        #[export] Declare Instance qcons : quotation_of M.Raw.cons.
        #[export] Declare Instance qcompare_more : quotation_of M.Raw.compare_more.
        #[export] Declare Instance qcompare_cont : quotation_of M.Raw.compare_cont.
        #[export] Declare Instance qcompare_end : quotation_of M.Raw.compare_end.
        #[export] Declare Instance qcompare : quotation_of M.Raw.compare.
        #[export] Declare Instance qequal : quotation_of M.Raw.equal.
        #[export] Declare Instance qsubsetl : quotation_of M.Raw.subsetl.
        #[export] Declare Instance qsubsetr : quotation_of M.Raw.subsetr.
        #[export] Declare Instance qsubset : quotation_of M.Raw.subset.
        #[export] Declare Instance qheight : quotation_of M.Raw.height.
        #[export] Declare Instance qsingleton : quotation_of M.Raw.singleton.
        #[export] Declare Instance qcreate : quotation_of M.Raw.create.
        #[export] Declare Instance qassert_false : quotation_of M.Raw.assert_false.
        #[export] Declare Instance qbal : quotation_of M.Raw.bal.
        #[export] Declare Instance qadd : quotation_of M.Raw.add.
        #[export] Declare Instance qjoin : quotation_of M.Raw.join.
        #[export] Declare Instance qremove_min : quotation_of M.Raw.remove_min.
        #[export] Declare Instance qmerge : quotation_of M.Raw.merge.
        #[export] Declare Instance qremove : quotation_of M.Raw.remove.
        #[export] Declare Instance qconcat : quotation_of M.Raw.concat.
        #[export] Declare Instance qt_left : quotation_of M.Raw.t_left.
        #[export] Declare Instance qt_in : quotation_of M.Raw.t_in.
        #[export] Declare Instance qt_right : quotation_of M.Raw.t_right.
        #[export] Declare Instance qsplit : quotation_of M.Raw.split.
        #[export] Declare Instance qinter : quotation_of M.Raw.inter.
        #[export] Declare Instance qdiff : quotation_of M.Raw.diff.
        #[export] Declare Instance qunion : quotation_of M.Raw.union.
        #[export] Declare Instance qfilter : quotation_of M.Raw.filter.
        #[export] Declare Instance qpartition : quotation_of M.Raw.partition.
        #[export] Declare Instance qInT : inductive_quotation_of M.Raw.InT.
        #[export] Declare Instance qIn : quotation_of M.Raw.In.
        #[export] Declare Instance qEqual : quotation_of M.Raw.Equal.
        #[export] Declare Instance qSubset : quotation_of M.Raw.Subset.
        #[export] Declare Instance qEmpty : quotation_of M.Raw.Empty.
        #[export] Declare Instance qFor_all : quotation_of M.Raw.For_all.
        #[export] Declare Instance qExists : quotation_of M.Raw.Exists.
        #[export] Declare Instance qlt_tree : quotation_of M.Raw.lt_tree.
        #[export] Declare Instance qgt_tree : quotation_of M.Raw.gt_tree.
        #[export] Declare Instance qbst : inductive_quotation_of M.Raw.bst.
        #[export] Declare Instance qIsOk : quotation_of M.Raw.IsOk.
        #[export] Declare Instance qOk : quotation_of M.Raw.Ok.
        #[export] Declare Instance qok : quotation_of (@M.Raw.ok).
        #[export] Declare Instance qbst_Ok : quotation_of M.Raw.bst_Ok.
        #[export] Declare Instance qltb_tree : quotation_of M.Raw.ltb_tree.
        #[export] Declare Instance qgtb_tree : quotation_of M.Raw.gtb_tree.
        #[export] Declare Instance qisok : quotation_of M.Raw.isok.
        #[export] Declare Instance qltb_tree_iff : quotation_of M.Raw.ltb_tree_iff.
        #[export] Declare Instance qgtb_tree_iff : quotation_of M.Raw.gtb_tree_iff.
        #[export] Declare Instance qisok_iff : quotation_of M.Raw.isok_iff.
        #[export] Declare Instance qisok_Ok : quotation_of M.Raw.isok_Ok.
        #[export] Declare Instance qIn_1 : quotation_of M.Raw.In_1.
        #[export] Declare Instance qIn_compat : quotation_of M.Raw.In_compat.
        #[export] Declare Instance qIn_node_iff : quotation_of M.Raw.In_node_iff.
        #[export] Declare Instance qIn_leaf_iff : quotation_of M.Raw.In_leaf_iff.
        #[export] Declare Instance qlt_leaf : quotation_of M.Raw.lt_leaf.
        #[export] Declare Instance qgt_leaf : quotation_of M.Raw.gt_leaf.
        #[export] Declare Instance qlt_tree_node : quotation_of M.Raw.lt_tree_node.
        #[export] Declare Instance qgt_tree_node : quotation_of M.Raw.gt_tree_node.
        #[export] Declare Instance qlt_tree_not_in : quotation_of M.Raw.lt_tree_not_in.
        #[export] Declare Instance qlt_tree_trans : quotation_of M.Raw.lt_tree_trans.
        #[export] Declare Instance qgt_tree_not_in : quotation_of M.Raw.gt_tree_not_in.
        #[export] Declare Instance qgt_tree_trans : quotation_of M.Raw.gt_tree_trans.
        #[export] Declare Instance qlt_tree_compat : quotation_of M.Raw.lt_tree_compat.
        #[export] Declare Instance qgt_tree_compat : quotation_of M.Raw.gt_tree_compat.
        #[export] Declare Instance qempty_spec : quotation_of M.Raw.empty_spec.
        #[export] Declare Instance qempty_ok : quotation_of M.Raw.empty_ok.
        #[export] Declare Instance qis_empty_spec : quotation_of M.Raw.is_empty_spec.
        #[export] Declare Instance qmem_spec : quotation_of M.Raw.mem_spec.
        #[export] Declare Instance qR_min_elt : inductive_quotation_of M.Raw.R_min_elt.
        #[export] Declare Instance qmin_elt_equation : quotation_of M.Raw.min_elt_equation.
        #[export] Declare Instance qR_max_elt : inductive_quotation_of M.Raw.R_max_elt.
        #[export] Declare Instance qmax_elt_equation : quotation_of M.Raw.max_elt_equation.
        #[export] Declare Instance qmin_elt_spec1 : quotation_of M.Raw.min_elt_spec1.
        #[export] Declare Instance qmin_elt_spec2 : quotation_of M.Raw.min_elt_spec2.
        #[export] Declare Instance qmin_elt_spec3 : quotation_of M.Raw.min_elt_spec3.
        #[export] Declare Instance qmax_elt_spec1 : quotation_of M.Raw.max_elt_spec1.
        #[export] Declare Instance qmax_elt_spec2 : quotation_of M.Raw.max_elt_spec2.
        #[export] Declare Instance qmax_elt_spec3 : quotation_of M.Raw.max_elt_spec3.
        #[export] Declare Instance qchoose_spec1 : quotation_of M.Raw.choose_spec1.
        #[export] Declare Instance qchoose_spec2 : quotation_of M.Raw.choose_spec2.
        #[export] Declare Instance qchoose_spec3 : quotation_of M.Raw.choose_spec3.
        #[export] Declare Instance qelements_spec1' : quotation_of M.Raw.elements_spec1'.
        #[export] Declare Instance qelements_spec1 : quotation_of M.Raw.elements_spec1.
        #[export] Declare Instance qelements_spec2' : quotation_of M.Raw.elements_spec2'.
        #[export] Declare Instance qelements_spec2 : quotation_of M.Raw.elements_spec2.
        #[export] Declare Instance qelements_spec2w : quotation_of M.Raw.elements_spec2w.
        #[export] Declare Instance qelements_aux_cardinal : quotation_of M.Raw.elements_aux_cardinal.
        #[export] Declare Instance qelements_cardinal : quotation_of M.Raw.elements_cardinal.
        #[export] Declare Instance qcardinal_spec : quotation_of M.Raw.cardinal_spec.
        #[export] Declare Instance qelements_app : quotation_of M.Raw.elements_app.
        #[export] Declare Instance qelements_node : quotation_of M.Raw.elements_node.
        #[export] Declare Instance qrev_elements_app : quotation_of M.Raw.rev_elements_app.
        #[export] Declare Instance qrev_elements_node : quotation_of M.Raw.rev_elements_node.
        #[export] Declare Instance qrev_elements_rev : quotation_of M.Raw.rev_elements_rev.
        #[export] Declare Instance qsorted_app_inv : quotation_of M.Raw.sorted_app_inv.
        #[export] Declare Instance qelements_sort_ok : quotation_of M.Raw.elements_sort_ok.
        #[export] Declare Instance qfor_all_spec : quotation_of M.Raw.for_all_spec.
        #[export] Declare Instance qexists_spec : quotation_of M.Raw.exists_spec.
        #[export] Declare Instance qfold_spec' : quotation_of (@M.Raw.fold_spec').
        #[export] Declare Instance qfold_spec : quotation_of M.Raw.fold_spec.
        #[export] Declare Instance qsubsetl_spec : quotation_of M.Raw.subsetl_spec.
        #[export] Declare Instance qsubsetr_spec : quotation_of M.Raw.subsetr_spec.
        #[export] Declare Instance qsubset_spec : quotation_of M.Raw.subset_spec.
        #[export] Declare Instance qeq : quotation_of M.Raw.eq.
        #[export] Declare Instance qeq_equiv : quotation_of M.Raw.eq_equiv.
        #[export] Declare Instance qeq_Leq : quotation_of M.Raw.eq_Leq.
        #[export] Declare Instance qlt : quotation_of M.Raw.lt.
        #[export] Declare Instance qlt_strorder : quotation_of M.Raw.lt_strorder.
        #[export] Declare Instance qlt_compat : quotation_of M.Raw.lt_compat.
        #[export] Declare Instance qflatten_e : quotation_of M.Raw.flatten_e.
        #[export] Declare Instance qflatten_e_elements : quotation_of M.Raw.flatten_e_elements.
        #[export] Declare Instance qcons_1 : quotation_of M.Raw.cons_1.
        #[export] Declare Instance qCmp : quotation_of M.Raw.Cmp.
        #[export] Declare Instance qcompare_end_Cmp : quotation_of M.Raw.compare_end_Cmp.
        #[export] Declare Instance qcompare_more_Cmp : quotation_of M.Raw.compare_more_Cmp.
        #[export] Declare Instance qcompare_cont_Cmp : quotation_of M.Raw.compare_cont_Cmp.
        #[export] Declare Instance qcompare_Cmp : quotation_of M.Raw.compare_Cmp.
        #[export] Declare Instance qcompare_spec : quotation_of M.Raw.compare_spec.
        #[export] Declare Instance qequal_spec : quotation_of M.Raw.equal_spec.
        #[export] Declare Instance qmindepth_maxdepth : quotation_of M.Raw.mindepth_maxdepth.
        #[export] Declare Instance qmaxdepth_cardinal : quotation_of M.Raw.maxdepth_cardinal.
        #[export] Declare Instance qmindepth_cardinal : quotation_of M.Raw.mindepth_cardinal.
        #[export] Declare Instance qmaxdepth_log_cardinal : quotation_of M.Raw.maxdepth_log_cardinal.
        #[export] Declare Instance qmindepth_log_cardinal : quotation_of M.Raw.mindepth_log_cardinal.
        #[export] Declare Instance qR_bal : inductive_quotation_of M.Raw.R_bal.
        #[export] Declare Instance qR_remove_min : inductive_quotation_of M.Raw.R_remove_min.
        #[export] Declare Instance qremove_min_equation : quotation_of M.Raw.remove_min_equation.
        #[export] Declare Instance qR_merge : inductive_quotation_of M.Raw.R_merge.
        #[export] Declare Instance qR_concat : inductive_quotation_of M.Raw.R_concat.
        #[export] Declare Instance qR_inter : inductive_quotation_of M.Raw.R_inter.
        #[export] Declare Instance qinter_equation : quotation_of M.Raw.inter_equation.
        #[export] Declare Instance qR_diff : inductive_quotation_of M.Raw.R_diff.
        #[export] Declare Instance qdiff_equation : quotation_of M.Raw.diff_equation.
        #[export] Declare Instance qR_union : inductive_quotation_of M.Raw.R_union.
        #[export] Declare Instance qunion_equation : quotation_of M.Raw.union_equation.
        #[export] Declare Instance qsingleton_spec : quotation_of M.Raw.singleton_spec.
        #[export] Declare Instance qsingleton_ok : quotation_of M.Raw.singleton_ok.
        #[export] Declare Instance qcreate_spec : quotation_of M.Raw.create_spec.
        #[export] Declare Instance qcreate_ok : quotation_of M.Raw.create_ok.
        #[export] Declare Instance qbal_spec : quotation_of M.Raw.bal_spec.
        #[export] Declare Instance qbal_ok : quotation_of M.Raw.bal_ok.
        #[export] Declare Instance qadd_spec' : quotation_of M.Raw.add_spec'.
        #[export] Declare Instance qadd_spec : quotation_of M.Raw.add_spec.
        #[export] Declare Instance qadd_ok : quotation_of M.Raw.add_ok.
        #[export] Declare Instance qjoin_spec : quotation_of M.Raw.join_spec.
        #[export] Declare Instance qjoin_ok : quotation_of M.Raw.join_ok.
        #[export] Declare Instance qremove_min_spec : quotation_of M.Raw.remove_min_spec.
        #[export] Declare Instance qremove_min_ok : quotation_of M.Raw.remove_min_ok.
        #[export] Declare Instance qremove_min_gt_tree : quotation_of M.Raw.remove_min_gt_tree.
        #[export] Declare Instance qmerge_spec : quotation_of M.Raw.merge_spec.
        #[export] Declare Instance qmerge_ok : quotation_of M.Raw.merge_ok.
        #[export] Declare Instance qremove_spec : quotation_of M.Raw.remove_spec.
        #[export] Declare Instance qremove_ok : quotation_of M.Raw.remove_ok.
        #[export] Declare Instance qconcat_spec : quotation_of M.Raw.concat_spec.
        #[export] Declare Instance qconcat_ok : quotation_of M.Raw.concat_ok.
        #[export] Declare Instance qsplit_spec1 : quotation_of M.Raw.split_spec1.
        #[export] Declare Instance qsplit_spec2 : quotation_of M.Raw.split_spec2.
        #[export] Declare Instance qsplit_spec3 : quotation_of M.Raw.split_spec3.
        #[export] Declare Instance qsplit_ok : quotation_of M.Raw.split_ok.
        #[export] Declare Instance qsplit_ok1 : quotation_of M.Raw.split_ok1.
        #[export] Declare Instance qsplit_ok2 : quotation_of M.Raw.split_ok2.
        #[export] Declare Instance qinter_spec_ok : quotation_of (@M.Raw.inter_spec_ok).
        #[export] Declare Instance qinter_spec : quotation_of M.Raw.inter_spec.
        #[export] Declare Instance qinter_ok : quotation_of M.Raw.inter_ok.
        #[export] Declare Instance qdiff_spec_ok : quotation_of (@M.Raw.diff_spec_ok).
        #[export] Declare Instance qdiff_spec : quotation_of M.Raw.diff_spec.
        #[export] Declare Instance qdiff_ok : quotation_of M.Raw.diff_ok.
        #[export] Declare Instance qunion_spec : quotation_of M.Raw.union_spec.
        #[export] Declare Instance qunion_ok : quotation_of M.Raw.union_ok.
        #[export] Declare Instance qfilter_spec : quotation_of M.Raw.filter_spec.
        #[export] Declare Instance qfilter_weak_spec : quotation_of M.Raw.filter_weak_spec.
        #[export] Declare Instance qfilter_ok : quotation_of M.Raw.filter_ok.
        #[export] Declare Instance qpartition_spec1' : quotation_of M.Raw.partition_spec1'.
        #[export] Declare Instance qpartition_spec2' : quotation_of M.Raw.partition_spec2'.
        #[export] Declare Instance qpartition_spec1 : quotation_of M.Raw.partition_spec1.
        #[export] Declare Instance qpartition_spec2 : quotation_of M.Raw.partition_spec2.
        #[export] Declare Instance qpartition_ok1 : quotation_of M.Raw.partition_ok1.
        #[export] Declare Instance qpartition_ok2 : quotation_of M.Raw.partition_ok2.
      End qRaw.
      Export (hints) qRaw.

      #[export] Declare Instance qelt : quotation_of M.elt.
      #[export] Declare Instance qt_ : inductive_quotation_of M.t_.
      #[export] Declare Instance qthis : quotation_of M.this.
      #[export] Declare Instance qis_ok : quotation_of M.is_ok.
      #[export] Declare Instance qt : quotation_of M.t.
      #[export] Declare Instance qIn : quotation_of M.In.
      #[export] Declare Instance qEqual : quotation_of M.Equal.
      #[export] Declare Instance qSubset : quotation_of M.Subset.
      #[export] Declare Instance qEmpty : quotation_of M.Empty.
      #[export] Declare Instance qFor_all : quotation_of M.For_all.
      #[export] Declare Instance qExists : quotation_of M.Exists.
      #[export] Declare Instance qmem : quotation_of M.mem.
      #[export] Declare Instance qadd : quotation_of M.add.
      #[export] Declare Instance qremove : quotation_of M.remove.
      #[export] Declare Instance qsingleton : quotation_of M.singleton.
      #[export] Declare Instance qunion : quotation_of M.union.
      #[export] Declare Instance qinter : quotation_of M.inter.
      #[export] Declare Instance qdiff : quotation_of M.diff.
      #[export] Declare Instance qequal : quotation_of M.equal.
      #[export] Declare Instance qsubset : quotation_of M.subset.
      #[export] Declare Instance qempty : quotation_of M.empty.
      #[export] Declare Instance qis_empty : quotation_of M.is_empty.
      #[export] Declare Instance qelements : quotation_of M.elements.
      #[export] Declare Instance qchoose : quotation_of M.choose.
      #[export] Declare Instance qfold : quotation_of M.fold.
      #[export] Declare Instance qcardinal : quotation_of M.cardinal.
      #[export] Declare Instance qfilter : quotation_of M.filter.
      #[export] Declare Instance qfor_all : quotation_of M.for_all.
      #[export] Declare Instance qexists_ : quotation_of M.exists_.
      #[export] Declare Instance qpartition : quotation_of M.partition.
      #[export] Declare Instance qIn_compat : quotation_of M.In_compat.
      #[export] Declare Instance qeq : quotation_of M.eq.
      #[export] Declare Instance qeq_equiv : quotation_of M.eq_equiv.
      #[export] Declare Instance qeq_dec : quotation_of M.eq_dec.
      #[export] Declare Instance qmem_spec : quotation_of M.mem_spec.
      #[export] Declare Instance qequal_spec : quotation_of M.equal_spec.
      #[export] Declare Instance qsubset_spec : quotation_of M.subset_spec.
      #[export] Declare Instance qempty_spec : quotation_of M.empty_spec.
      #[export] Declare Instance qis_empty_spec : quotation_of M.is_empty_spec.
      #[export] Declare Instance qadd_spec : quotation_of M.add_spec.
      #[export] Declare Instance qremove_spec : quotation_of M.remove_spec.
      #[export] Declare Instance qsingleton_spec : quotation_of M.singleton_spec.
      #[export] Declare Instance qunion_spec : quotation_of M.union_spec.
      #[export] Declare Instance qinter_spec : quotation_of M.inter_spec.
      #[export] Declare Instance qdiff_spec : quotation_of M.diff_spec.
      #[export] Declare Instance qfold_spec : quotation_of M.fold_spec.
      #[export] Declare Instance qcardinal_spec : quotation_of M.cardinal_spec.
      #[export] Declare Instance qfilter_spec : quotation_of M.filter_spec.
      #[export] Declare Instance qfor_all_spec : quotation_of M.for_all_spec.
      #[export] Declare Instance qexists_spec : quotation_of M.exists_spec.
      #[export] Declare Instance qpartition_spec1 : quotation_of M.partition_spec1.
      #[export] Declare Instance qpartition_spec2 : quotation_of M.partition_spec2.
      #[export] Declare Instance qelements_spec1 : quotation_of M.elements_spec1.
      #[export] Declare Instance qelements_spec2w : quotation_of M.elements_spec2w.
      #[export] Declare Instance qchoose_spec1 : quotation_of M.choose_spec1.
      #[export] Declare Instance qchoose_spec2 : quotation_of M.choose_spec2.
      #[export] Declare Instance qcompare : quotation_of M.compare.
      #[export] Declare Instance qmin_elt : quotation_of M.min_elt.
      #[export] Declare Instance qmax_elt : quotation_of M.max_elt.
      #[export] Declare Instance qlt : quotation_of M.lt.
      #[export] Declare Instance qlt_strorder : quotation_of M.lt_strorder.
      #[export] Declare Instance qlt_compat : quotation_of M.lt_compat.
      #[export] Declare Instance qcompare_spec : quotation_of M.compare_spec.
      #[export] Declare Instance qelements_spec2 : quotation_of M.elements_spec2.
      #[export] Declare Instance qmin_elt_spec1 : quotation_of M.min_elt_spec1.
      #[export] Declare Instance qmin_elt_spec2 : quotation_of M.min_elt_spec2.
      #[export] Declare Instance qmin_elt_spec3 : quotation_of M.min_elt_spec3.
      #[export] Declare Instance qmax_elt_spec1 : quotation_of M.max_elt_spec1.
      #[export] Declare Instance qmax_elt_spec2 : quotation_of M.max_elt_spec2.
      #[export] Declare Instance qmax_elt_spec3 : quotation_of M.max_elt_spec3.
      #[export] Declare Instance qchoose_spec3 : quotation_of M.choose_spec3.
    End QuotationOfMake.
  End MSetAVL.

  Module MSetList.
    Module Type MakeSig (T : OrderedType) := Nop <+ MSetList.Make T.
    Module Type QuotationOfMake (T : OrderedType) (M : MakeSig T).
      Module qRaw.
        (*Module qMX := QuotationOfOrderedTypeFacts T M.Raw.MX qT.*)
        (*Module qML := QuotationOfOrderedTypeLists T M.Raw.ML qT.*)
        #[export] Declare Instance qelt : quotation_of M.Raw.elt.
        #[export] Declare Instance qt : quotation_of M.Raw.t.
        #[export] Declare Instance qempty : quotation_of M.Raw.empty.
        #[export] Declare Instance qis_empty : quotation_of M.Raw.is_empty.
        #[export] Declare Instance qmem : quotation_of M.Raw.mem.
        #[export] Declare Instance qadd : quotation_of M.Raw.add.
        #[export] Declare Instance qsingleton : quotation_of M.Raw.singleton.
        #[export] Declare Instance qremove : quotation_of M.Raw.remove.
        #[export] Declare Instance qunion : quotation_of M.Raw.union.
        #[export] Declare Instance qinter : quotation_of M.Raw.inter.
        #[export] Declare Instance qdiff : quotation_of M.Raw.diff.
        #[export] Declare Instance qequal : quotation_of M.Raw.equal.
        #[export] Declare Instance qsubset : quotation_of M.Raw.subset.
        #[export] Declare Instance qfold : quotation_of M.Raw.fold.
        #[export] Declare Instance qfilter : quotation_of M.Raw.filter.
        #[export] Declare Instance qfor_all : quotation_of M.Raw.for_all.
        #[export] Declare Instance qexists_ : quotation_of M.Raw.exists_.
        #[export] Declare Instance qpartition : quotation_of M.Raw.partition.
        #[export] Declare Instance qcardinal : quotation_of M.Raw.cardinal.
        #[export] Declare Instance qelements : quotation_of M.Raw.elements.
        #[export] Declare Instance qmin_elt : quotation_of M.Raw.min_elt.
        #[export] Declare Instance qmax_elt : quotation_of M.Raw.max_elt.
        #[export] Declare Instance qchoose : quotation_of M.Raw.choose.
        #[export] Declare Instance qcompare : quotation_of M.Raw.compare.
        #[export] Declare Instance qinf : quotation_of M.Raw.inf.
        #[export] Declare Instance qisok : quotation_of M.Raw.isok.
        #[export] Declare Instance qIsOk : quotation_of M.Raw.IsOk.
        #[export] Declare Instance qOk : quotation_of M.Raw.Ok.
        #[export] Declare Instance qok : quotation_of (@M.Raw.ok).
        #[export] Declare Instance qSort_Ok : quotation_of M.Raw.Sort_Ok.
        #[export] Declare Instance qinf_iff : quotation_of M.Raw.inf_iff.
        #[export] Declare Instance qisok_iff : quotation_of M.Raw.isok_iff.
        #[export] Declare Instance qisok_Ok : quotation_of M.Raw.isok_Ok.
        #[export] Declare Instance qEqual : quotation_of M.Raw.Equal.
        #[export] Declare Instance qSubset : quotation_of M.Raw.Subset.
        #[export] Declare Instance qEmpty : quotation_of M.Raw.Empty.
        #[export] Declare Instance qFor_all : quotation_of M.Raw.For_all.
        #[export] Declare Instance qExists : quotation_of M.Raw.Exists.
        #[export] Declare Instance qmem_spec : quotation_of M.Raw.mem_spec.
        #[export] Declare Instance qadd_inf : quotation_of M.Raw.add_inf.
        #[export] Declare Instance qadd_ok : quotation_of M.Raw.add_ok.
        #[export] Declare Instance qadd_spec : quotation_of M.Raw.add_spec.
        #[export] Declare Instance qremove_inf : quotation_of M.Raw.remove_inf.
        #[export] Declare Instance qremove_ok : quotation_of M.Raw.remove_ok.
        #[export] Declare Instance qremove_spec : quotation_of M.Raw.remove_spec.
        #[export] Declare Instance qsingleton_ok : quotation_of M.Raw.singleton_ok.
        #[export] Declare Instance qsingleton_spec : quotation_of M.Raw.singleton_spec.
        #[export] Declare Instance qunion_inf : quotation_of M.Raw.union_inf.
        #[export] Declare Instance qunion_ok : quotation_of M.Raw.union_ok.
        #[export] Declare Instance qunion_spec : quotation_of M.Raw.union_spec.
        #[export] Declare Instance qinter_inf : quotation_of M.Raw.inter_inf.
        #[export] Declare Instance qinter_ok : quotation_of M.Raw.inter_ok.
        #[export] Declare Instance qinter_spec : quotation_of M.Raw.inter_spec.
        #[export] Declare Instance qdiff_inf : quotation_of M.Raw.diff_inf.
        #[export] Declare Instance qdiff_ok : quotation_of M.Raw.diff_ok.
        #[export] Declare Instance qdiff_spec : quotation_of M.Raw.diff_spec.
        #[export] Declare Instance qequal_spec : quotation_of M.Raw.equal_spec.
        #[export] Declare Instance qsubset_spec : quotation_of M.Raw.subset_spec.
        #[export] Declare Instance qempty_ok : quotation_of M.Raw.empty_ok.
        #[export] Declare Instance qempty_spec : quotation_of M.Raw.empty_spec.
        #[export] Declare Instance qis_empty_spec : quotation_of M.Raw.is_empty_spec.
        #[export] Declare Instance qelements_spec1 : quotation_of M.Raw.elements_spec1.
        #[export] Declare Instance qelements_spec2 : quotation_of M.Raw.elements_spec2.
        #[export] Declare Instance qelements_spec2w : quotation_of M.Raw.elements_spec2w.
        #[export] Declare Instance qmin_elt_spec1 : quotation_of M.Raw.min_elt_spec1.
        #[export] Declare Instance qmin_elt_spec2 : quotation_of M.Raw.min_elt_spec2.
        #[export] Declare Instance qmin_elt_spec3 : quotation_of M.Raw.min_elt_spec3.
        #[export] Declare Instance qmax_elt_spec1 : quotation_of M.Raw.max_elt_spec1.
        #[export] Declare Instance qmax_elt_spec2 : quotation_of M.Raw.max_elt_spec2.
        #[export] Declare Instance qmax_elt_spec3 : quotation_of M.Raw.max_elt_spec3.
        #[export] Declare Instance qchoose_spec1 : quotation_of M.Raw.choose_spec1.
        #[export] Declare Instance qchoose_spec2 : quotation_of M.Raw.choose_spec2.
        #[export] Declare Instance qchoose_spec3 : quotation_of M.Raw.choose_spec3.
        #[export] Declare Instance qfold_spec : quotation_of M.Raw.fold_spec.
        #[export] Declare Instance qcardinal_spec : quotation_of M.Raw.cardinal_spec.
        #[export] Declare Instance qfilter_inf : quotation_of M.Raw.filter_inf.
        #[export] Declare Instance qfilter_ok : quotation_of M.Raw.filter_ok.
        #[export] Declare Instance qfilter_spec : quotation_of M.Raw.filter_spec.
        #[export] Declare Instance qfor_all_spec : quotation_of M.Raw.for_all_spec.
        #[export] Declare Instance qexists_spec : quotation_of M.Raw.exists_spec.
        #[export] Declare Instance qpartition_inf1 : quotation_of M.Raw.partition_inf1.
        #[export] Declare Instance qpartition_inf2 : quotation_of M.Raw.partition_inf2.
        #[export] Declare Instance qpartition_ok1 : quotation_of M.Raw.partition_ok1.
        #[export] Declare Instance qpartition_ok2 : quotation_of M.Raw.partition_ok2.
        #[export] Declare Instance qpartition_spec1 : quotation_of M.Raw.partition_spec1.
        #[export] Declare Instance qpartition_spec2 : quotation_of M.Raw.partition_spec2.
        #[export] Declare Instance qIn : quotation_of M.Raw.In.
        #[export] Declare Instance qIn_compat : quotation_of M.Raw.In_compat.
        #[export] Declare Instance qeq : quotation_of M.Raw.eq.
        #[export] Declare Instance qeq_equiv : quotation_of M.Raw.eq_equiv.
        #[export] Declare Instance qlt : quotation_of M.Raw.lt.
        #[export] Declare Instance qlt_strorder : quotation_of M.Raw.lt_strorder.
        #[export] Declare Instance qlt_compat : quotation_of M.Raw.lt_compat.
        #[export] Declare Instance qcompare_spec_aux : quotation_of M.Raw.compare_spec_aux.
        #[export] Declare Instance qcompare_spec : quotation_of M.Raw.compare_spec.
      End qRaw.
      #[export] Declare Instance qelt : quotation_of M.elt.
      #[export] Declare Instance qt_ : inductive_quotation_of M.t_.
      #[export] Declare Instance qthis : quotation_of M.this.
      #[export] Declare Instance qis_ok : quotation_of M.is_ok.
      #[export] Declare Instance qt : quotation_of M.t.
      #[export] Declare Instance qIn : quotation_of M.In.
      #[export] Declare Instance qEqual : quotation_of M.Equal.
      #[export] Declare Instance qSubset : quotation_of M.Subset.
      #[export] Declare Instance qEmpty : quotation_of M.Empty.
      #[export] Declare Instance qFor_all : quotation_of M.For_all.
      #[export] Declare Instance qExists : quotation_of M.Exists.
      #[export] Declare Instance qmem : quotation_of M.mem.
      #[export] Declare Instance qadd : quotation_of M.add.
      #[export] Declare Instance qremove : quotation_of M.remove.
      #[export] Declare Instance qsingleton : quotation_of M.singleton.
      #[export] Declare Instance qunion : quotation_of M.union.
      #[export] Declare Instance qinter : quotation_of M.inter.
      #[export] Declare Instance qdiff : quotation_of M.diff.
      #[export] Declare Instance qequal : quotation_of M.equal.
      #[export] Declare Instance qsubset : quotation_of M.subset.
      #[export] Declare Instance qempty : quotation_of M.empty.
      #[export] Declare Instance qis_empty : quotation_of M.is_empty.
      #[export] Declare Instance qelements : quotation_of M.elements.
      #[export] Declare Instance qchoose : quotation_of M.choose.
      #[export] Declare Instance qfold : quotation_of M.fold.
      #[export] Declare Instance qcardinal : quotation_of M.cardinal.
      #[export] Declare Instance qfilter : quotation_of M.filter.
      #[export] Declare Instance qfor_all : quotation_of M.for_all.
      #[export] Declare Instance qexists_ : quotation_of M.exists_.
      #[export] Declare Instance qpartition : quotation_of M.partition.
      #[export] Declare Instance qIn_compat : quotation_of M.In_compat.
      #[export] Declare Instance qeq : quotation_of M.eq.
      #[export] Declare Instance qeq_equiv : quotation_of M.eq_equiv.
      #[export] Declare Instance qeq_dec : quotation_of M.eq_dec.
      #[export] Declare Instance qmem_spec : quotation_of M.mem_spec.
      #[export] Declare Instance qequal_spec : quotation_of M.equal_spec.
      #[export] Declare Instance qsubset_spec : quotation_of M.subset_spec.
      #[export] Declare Instance qempty_spec : quotation_of M.empty_spec.
      #[export] Declare Instance qis_empty_spec : quotation_of M.is_empty_spec.
      #[export] Declare Instance qadd_spec : quotation_of M.add_spec.
      #[export] Declare Instance qremove_spec : quotation_of M.remove_spec.
      #[export] Declare Instance qsingleton_spec : quotation_of M.singleton_spec.
      #[export] Declare Instance qunion_spec : quotation_of M.union_spec.
      #[export] Declare Instance qinter_spec : quotation_of M.inter_spec.
      #[export] Declare Instance qdiff_spec : quotation_of M.diff_spec.
      #[export] Declare Instance qfold_spec : quotation_of M.fold_spec.
      #[export] Declare Instance qcardinal_spec : quotation_of M.cardinal_spec.
      #[export] Declare Instance qfilter_spec : quotation_of M.filter_spec.
      #[export] Declare Instance qfor_all_spec : quotation_of M.for_all_spec.
      #[export] Declare Instance qexists_spec : quotation_of M.exists_spec.
      #[export] Declare Instance qpartition_spec1 : quotation_of M.partition_spec1.
      #[export] Declare Instance qpartition_spec2 : quotation_of M.partition_spec2.
      #[export] Declare Instance qelements_spec1 : quotation_of M.elements_spec1.
      #[export] Declare Instance qelements_spec2w : quotation_of M.elements_spec2w.
      #[export] Declare Instance qchoose_spec1 : quotation_of M.choose_spec1.
      #[export] Declare Instance qchoose_spec2 : quotation_of M.choose_spec2.
      #[export] Declare Instance qcompare : quotation_of M.compare.
      #[export] Declare Instance qmin_elt : quotation_of M.min_elt.
      #[export] Declare Instance qmax_elt : quotation_of M.max_elt.
      #[export] Declare Instance qlt : quotation_of M.lt.
      #[export] Declare Instance qlt_strorder : quotation_of M.lt_strorder.
      #[export] Declare Instance qlt_compat : quotation_of M.lt_compat.
      #[export] Declare Instance qcompare_spec : quotation_of M.compare_spec.
      #[export] Declare Instance qelements_spec2 : quotation_of M.elements_spec2.
      #[export] Declare Instance qmin_elt_spec1 : quotation_of M.min_elt_spec1.
      #[export] Declare Instance qmin_elt_spec2 : quotation_of M.min_elt_spec2.
      #[export] Declare Instance qmin_elt_spec3 : quotation_of M.min_elt_spec3.
      #[export] Declare Instance qmax_elt_spec1 : quotation_of M.max_elt_spec1.
      #[export] Declare Instance qmax_elt_spec2 : quotation_of M.max_elt_spec2.
      #[export] Declare Instance qmax_elt_spec3 : quotation_of M.max_elt_spec3.
      #[export] Declare Instance qchoose_spec3 : quotation_of M.choose_spec3.
    End QuotationOfMake.

    Module Type MakeWithLeibnizSig (T : OrderedTypeWithLeibniz) := Nop <+ MSetList.MakeWithLeibniz T.
    Module Type QuotationOfMakeWithLeibniz (T : OrderedTypeWithLeibniz) (M : MakeWithLeibnizSig T).
      Include QuotationOfMake T M.
      #[export] Declare Instance qeq_leibniz_list : quotation_of M.eq_leibniz_list.
      #[export] Declare Instance qeq_leibniz : quotation_of M.eq_leibniz.
    End QuotationOfMakeWithLeibniz.
  End MSetList.
End MSets.

Module QuoteMSetAVL (T : OrderedType) (M : MSetAVL.MakeSig T) (Import MOrdProperties : OrdPropertiesSig M) (Import qT : QuotationOfOrderedType T) (Import qM : MSetAVL.QuotationOfMake T M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties qT).
  Export (hints) qT qM qMOrdProperties.
  Include QuoteSets M MOrdProperties qT qM qMOrdProperties.

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
      Context {quote_T_t : ground_quotable T.t}.

      Fixpoint lt_tree_dec x t : { M.Raw.lt_tree x t } + {~ M.Raw.lt_tree x t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node z l n r
                 => match T.compare n x as c, lt_tree_dec x l, lt_tree_dec x r return CompareSpec _ _ _ c -> _ with
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
      Fixpoint gt_tree_dec x t : { M.Raw.gt_tree x t } + {~ M.Raw.gt_tree x t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node z l n r
                 => match T.compare n x as c, gt_tree_dec x l, gt_tree_dec x r return CompareSpec _ _ _ c -> _ with
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
      Fixpoint bst_dec t : { M.Raw.bst t } + {~ M.Raw.bst t}.
      Proof.
        refine match t with
               | M.Raw.Leaf => left _
               | M.Raw.Node z l n r
                 => match bst_dec l, bst_dec r, lt_tree_dec n l, gt_tree_dec n r with
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
      (* very slow :-( *)
      #[export] Instance qlt_tree_dec : quotation_of (@lt_tree_dec) := ltac:(unfold_quotation_of (); exact _).
      #[export] Instance qgt_tree_dec : quotation_of (@gt_tree_dec) := ltac:(unfold_quotation_of (); exact _).
      #[export] Instance qbst_dec : quotation_of (@bst_dec) := ltac:(unfold_quotation_of (); exact _).
      #[export] Instance quote_tree : ground_quotable M.Raw.tree := (ltac:(induction 1; exact _)).
      #[export] Instance quote_bst t : ground_quotable (M.Raw.bst t)
        := ground_quotable_of_dec (@bst_dec t).
      #[export] Instance quote_Ok s : ground_quotable (M.Raw.Ok s) := (ltac:(cbv [M.Raw.Ok]; exact _)).
    End with_t.
    #[export] Existing Instances
      qlt_tree_dec
      qgt_tree_dec
      qbst_dec
      quote_tree
      quote_bst
      quote_Ok
    .
  End Raw.
  Export (hints) Raw.

  #[export] Instance quote_t {quote_T_t : ground_quotable T.t} : ground_quotable M.t := ltac:(induction 1; exact _).
End QuoteMSetAVL.

Module QuoteUsualWSetsOn (E : UsualDecidableType) (Import M : WSetsOn E) (MProperties : WPropertiesOnSig E M) (qE : QuotationOfUsualDecidableType E) (qM : QuotationOfWSetsOn E M) (qMProperties : QuotationOfWPropertiesOn E M MProperties).
  Include QuoteWSetsOn E M MProperties qE qM qMProperties.

  #[export] Instance quote_For_all_usual {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (For_all P s)
    := quote_For_all.
  Definition quote_Exists_dec_usual {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (Exists P s)
    := quote_Exists_dec P_dec.
  #[export] Instance quote_forall2_In_usual {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_elt : ground_quotable elt} {quote_P : forall x y, ground_quotable (P x y:Prop)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2) := _.
End QuoteUsualWSetsOn.

Module Type UsualSets <: Sets.
  Declare Module E : UsualOrderedType.
  Include SetsOn E.
End UsualSets.

Module QuoteUsualSetsOn (Import M : UsualSets) (MProperties : OrdPropertiesSig M) (qE : QuotationOfUsualOrderedType M.E) (qM : QuotationOfSets M) (qMProperties : QuotationOfOrdProperties M MProperties qE).
  Include QuoteSets M MProperties qE qM qMProperties.
  Module InnerQuoteUsualSetsOn := QuoteUsualWSetsOn M.E M MProperties.P qE qM qMProperties.qP.
  Export (hints) InnerQuoteUsualSetsOn.
End QuoteUsualSetsOn.

Module Type QuotationOfOrderedTypeWithLeibniz (T : OrderedTypeWithLeibniz).
  Include QuotationOfOrderedType T.
  #[export] Declare Instance qeq_leibniz : quotation_of T.eq_leibniz.
End QuotationOfOrderedTypeWithLeibniz.

Module QuoteSWithLeibniz (Import M : SWithLeibniz) (MProperties : OrdPropertiesSig M) (qE : QuotationOfOrderedTypeWithLeibniz M.E) (qM : QuotationOfSets M) (qMProperties : QuotationOfOrdProperties M MProperties qE).
  Include QuoteSets M MProperties qE qM qMProperties.

  #[local] Instance all_P_Proper {P : E.t -> Prop} : Proper (E.eq ==> Basics.impl) P.
  Proof.
    intros ?? H.
    apply E.eq_leibniz in H; subst; exact id.
  Defined.
  #[export] Instance qall_P_Proper : quotation_of (@all_P_Proper) := ltac:(unfold_quotation_of (); exact _).

  #[export] Instance quote_For_all_leibniz {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (For_all P s)
    := quote_For_all.
  Definition quote_Exists_dec_leibniz {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (Exists P s)
    := quote_Exists_dec P_dec.
  #[export] Instance quote_forall2_In_leibniz {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_elt : ground_quotable elt} {quote_P : forall x y, ground_quotable (P x y:Prop)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2) := _.
End QuoteSWithLeibniz.

Module QuoteMSetList (T : OrderedType) (Import M : MSetList.MakeSig T) (Import MOrdProperties : OrdPropertiesSig M) (Import qT : QuotationOfOrderedType T) (Import qM : MSetList.QuotationOfMake T M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties qT).
  Export (hints) qT qM qMOrdProperties.
  Include QuoteSets M MOrdProperties qT qM qMOrdProperties.

  Module Raw.
    #[export] Instance quote_Ok {v} : ground_quotable (M.Raw.Ok v) := ltac:(cbv [M.Raw.Ok]; exact _).
  End Raw.
  Export (hints) Raw.
  #[export] Instance quote_t_ {quoteE_t : ground_quotable E.t} : ground_quotable t_ := ltac:(destruct 1; exact _).
End QuoteMSetList.

Module QuoteMSetListWithLeibniz (T : OrderedTypeWithLeibniz) (Import M : MSetList.MakeWithLeibnizSig T) (Import MOrdProperties : OrdPropertiesSig M) (Import qT : QuotationOfOrderedTypeWithLeibniz T) (Import qM : MSetList.QuotationOfMakeWithLeibniz T M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties qT).
  Export (hints) qT qM qMOrdProperties.
  Include QuoteMSetList T M MOrdProperties qT qM qMOrdProperties.
  Module InnerQuoteMSetListWithLeibniz := QuoteSWithLeibniz M MOrdProperties qT qM qMOrdProperties.
  Export (hints) InnerQuoteMSetListWithLeibniz.
End QuoteMSetListWithLeibniz.
