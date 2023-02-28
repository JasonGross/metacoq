From Coq Require Import MSetInterface MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From MetaCoq.Quotation.ToTemplate Require Export Init.
From MetaCoq.Quotation.ToTemplate Require Export (hints) Coq.Numbers Coq.Init Coq.Lists.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.Structures Require Import Orders.Sig.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.MSets Require Import MSetInterface.Sig MSetProperties.Sig MSetAVL.Sig MSetList.Sig.

Module QuoteWSetsOn (E : DecidableType) (Import W : WSetsOn E) (WProperties : WPropertiesOnSig E W) (qE : QuotationOfDecidableType E) (qW : QuotationOfWSetsOn E W) (qWProperties : QuotationOfWPropertiesOn E W WProperties).
  Export (hints) qE.
  Export (hints) qW.
  Export (hints) qWProperties.

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

Module QuoteSets (Import M : Sets) (Import MOrdProperties : OrdPropertiesSig M) (qE : QuotationOfOrderedType M.E) (qM : QuotationOfSets M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties).
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

Module QuoteMSetAVL (T : OrderedType) (M : MSetAVL.MakeSig T) (Import MOrdProperties : OrdPropertiesSig M) (Import qT : QuotationOfOrderedType T) (Import qM : MSetAVL.QuotationOfMake T M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties).
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

Module QuoteUsualSetsOn (Import M : UsualSets) (MProperties : OrdPropertiesSig M) (qE : QuotationOfUsualOrderedType M.E) (qM : QuotationOfSets M) (qMProperties : QuotationOfOrdProperties M MProperties).
  Include QuoteSets M MProperties qE qM qMProperties.
  Module InnerQuoteUsualSetsOn := QuoteUsualWSetsOn M.E M MProperties.P qE qM qMProperties.qP.
  Export (hints) InnerQuoteUsualSetsOn.
End QuoteUsualSetsOn.

Module QuoteSWithLeibniz (Import M : SWithLeibniz) (MProperties : OrdPropertiesSig M) (qE : QuotationOfOrderedTypeWithLeibniz M.E) (qM : QuotationOfSets M) (qMProperties : QuotationOfOrdProperties M MProperties).
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

Module QuoteMSetList (T : OrderedType) (Import M : MSetList.MakeSig T) (Import MOrdProperties : OrdPropertiesSig M) (Import qT : QuotationOfOrderedType T) (Import qM : MSetList.QuotationOfMake T M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties).
  Export (hints) qT qM qMOrdProperties.
  Include QuoteSets M MOrdProperties qT qM qMOrdProperties.

  Module Raw.
    #[export] Instance quote_Ok {v} : ground_quotable (M.Raw.Ok v) := ltac:(cbv [M.Raw.Ok]; exact _).
  End Raw.
  Export (hints) Raw.
  #[export] Instance quote_t_ {quoteE_t : ground_quotable E.t} : ground_quotable t_ := ltac:(destruct 1; exact _).
End QuoteMSetList.

Module QuoteMSetListWithLeibniz (T : OrderedTypeWithLeibniz) (Import M : MSetList.MakeWithLeibnizSig T) (Import MOrdProperties : OrdPropertiesSig M) (Import qT : QuotationOfOrderedTypeWithLeibniz T) (Import qM : MSetList.QuotationOfMakeWithLeibniz T M) (qMOrdProperties : QuotationOfOrdProperties M MOrdProperties).
  Export (hints) qT qM qMOrdProperties.
  Include QuoteMSetList T M MOrdProperties qT qM qMOrdProperties.
  Module InnerQuoteMSetListWithLeibniz := QuoteSWithLeibniz M MOrdProperties qT qM qMOrdProperties.
  Export (hints) InnerQuoteMSetListWithLeibniz.
End QuoteMSetListWithLeibniz.
