From Coq.Structures Require Equalities DecidableType Orders OrdersAlt OrderedType OrdersFacts.
From MetaCoq.Quotation.ToTemplate Require Export Coq.Init.

(** * Equalities *)
Import Coq.Structures.Equalities.
Module Type QuotationOfTyp (Import T : Typ).
  #[export] Declare Instance qt : quotation_of t.
End QuotationOfTyp.
Module Type QuotationOfHasEq (T : Typ) (Import E : HasEq T).
  #[export] Declare Instance qeq : quotation_of eq.
End QuotationOfHasEq.
Module Type QuotationOfEq (E : Eq) := QuotationOfTyp E <+ QuotationOfHasEq E E.
Module Type QuotationOfIsEq (E : Eq) (Import IE : IsEq E).
  #[export] Declare Instance qeq_equiv : quotation_of eq_equiv.
End QuotationOfIsEq.
Module Type QuotationOfIsEqOrig (E : Eq) (Import IEO : IsEqOrig E).
  #[export] Declare Instance qeq_refl : quotation_of eq_refl.
  #[export] Declare Instance qeq_sym : quotation_of eq_sym.
  #[export] Declare Instance qeq_trans : quotation_of eq_trans.
End QuotationOfIsEqOrig.

Module Type QuotationOfHasEqDec (E : Eq) (Import EDec : HasEqDec E).
  #[export] Declare Instance qeq_dec : quotation_of eq_dec.
End QuotationOfHasEqDec.

Module Type QuotationOfHasEqb (T : Typ) (Import E : HasEqb T).
  #[export] Declare Instance qeqb : quotation_of eqb.
End QuotationOfHasEqb.

Module Type QuotationOfEqbSpec (T : Typ) (X : HasEq T) (Y : HasEqb T) (Import ES : EqbSpec T X Y).
  #[export] Declare Instance qeqb_eq : quotation_of eqb_eq.
End QuotationOfEqbSpec.

Module Type QuotationOfHasEqBool (E : Eq) (EB : HasEqBool E) := QuotationOfHasEqb E EB <+ QuotationOfEqbSpec E E EB EB.

Module Type QuotationOfEqualityType (E : EqualityType) := QuotationOfEq E <+ QuotationOfIsEq E E.

Module Type QuotationOfEqualityTypeOrig (E : EqualityTypeOrig) := QuotationOfEq E <+ QuotationOfIsEqOrig E E.

Module Type QuotationOfEqualityTypeBoth (E : EqualityTypeBoth) <: QuotationOfEqualityType E <: QuotationOfEqualityTypeOrig E
  := QuotationOfEq E <+ QuotationOfIsEq E E <+ QuotationOfIsEqOrig E E.

Module Type QuotationOfDecidableType (E : DecidableType) <: QuotationOfEqualityType E
  := QuotationOfEq E <+ QuotationOfIsEq E E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfDecidableTypeOrig (E : DecidableTypeOrig) <: QuotationOfEqualityTypeOrig E
  := QuotationOfEq E <+ QuotationOfIsEqOrig E E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfDecidableTypeBoth (E : DecidableTypeBoth) <: QuotationOfDecidableType E <: QuotationOfDecidableTypeOrig E
  := QuotationOfEqualityTypeBoth E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfBooleanEqualityType (E : BooleanEqualityType) <: QuotationOfEqualityType E
  := QuotationOfEq E <+ QuotationOfIsEq E E <+ QuotationOfHasEqBool E E.

Module Type QuotationOfBooleanDecidableType (E : BooleanDecidableType) <: QuotationOfDecidableType E <: QuotationOfBooleanEqualityType E
  := QuotationOfEq E <+ QuotationOfIsEq E E <+ QuotationOfHasEqDec E E <+ QuotationOfHasEqBool E E.

Module Type QuotationOfDecidableTypeFull (E : DecidableTypeFull) <: QuotationOfDecidableTypeBoth E <: QuotationOfBooleanDecidableType E
  := QuotationOfEq E <+ QuotationOfIsEq E E <+ QuotationOfIsEqOrig E E <+ QuotationOfHasEqDec E E <+ QuotationOfHasEqBool E E.

Module Type BackportEqSig (E : Eq) (F : IsEq E) := Nop <+ BackportEq E F.

Module QuotationOfBackportEq (E : Eq) (F : IsEq E) (Import E' : BackportEqSig E F) (Import qE : QuotationOfEq E) (Import qF : QuotationOfIsEq E F) <: QuotationOfIsEqOrig E E'.
  #[export] Instance qeq_refl : quotation_of eq_refl := ltac:(cbv [eq_refl]; exact _).
  #[export] Instance qeq_sym : quotation_of eq_sym := ltac:(cbv [eq_sym]; exact _).
  #[export] Instance qeq_trans : quotation_of eq_trans := ltac:(cbv [eq_trans]; exact _).
End QuotationOfBackportEq.

Module Type UpdateEqSig (E : Eq) (F : IsEqOrig E) := Nop <+ UpdateEq E F.

Module QuotationOfUpdateEq (E : Eq) (F : IsEqOrig E) (Import E' : UpdateEqSig E F) (Import qE : QuotationOfEq E) (Import qF : QuotationOfIsEqOrig E F) <: QuotationOfIsEq E E'.
  #[export] Instance qeq_equiv : quotation_of E'.eq_equiv := ltac:(change (quotation_of (Build_Equivalence _ F.eq_refl F.eq_sym F.eq_trans)); exact _).
End QuotationOfUpdateEq.

Module Type Backport_ETSig (E:EqualityType) := Nop <+ Backport_ET E.
Module Type Update_ETSig (E:EqualityTypeOrig) := Nop <+ Update_ET E.
Module Type Backport_DTSig (E:DecidableType) := Nop <+ Backport_DT E.
Module Type Update_DTSig (E:DecidableTypeOrig) := Nop <+ Update_DT E.

Module QuotationOfBackport_ET (E : EqualityType) (E' : Backport_ETSig E) (qE : QuotationOfEqualityType E) <: QuotationOfEqualityTypeBoth E'
  := qE <+ QuotationOfBackportEq E E E'.

Module QuotationOfUpdate_ET (E : EqualityTypeOrig) (E' : Update_ETSig E) (qE : QuotationOfEqualityTypeOrig E) <: QuotationOfEqualityTypeBoth E'
  := qE <+ QuotationOfUpdateEq E E E'.

Module QuotationOfBackport_DT (E : DecidableType) (E' : Backport_DTSig E) (qE : QuotationOfDecidableType E) <: QuotationOfDecidableTypeBoth E'
  := qE <+ QuotationOfBackportEq E E E'.

Module QuotationOfUpdate_DT (E : DecidableTypeOrig) (E' : Update_DTSig E) (qE : QuotationOfDecidableTypeOrig E) <: QuotationOfDecidableTypeBoth E'
  := qE <+ QuotationOfUpdateEq E E E'.

Module Type HasEqDec2BoolSig (E : Eq) (F : HasEqDec E) <: HasEqBool E := Nop <+ HasEqDec2Bool E F.

Module QuotationOfHasEqDec2Bool (E : Eq) (F : HasEqDec E) (Import E' : HasEqDec2BoolSig E F) (Import qE : QuotationOfEq E) (Import qF : QuotationOfHasEqDec E F) <: QuotationOfHasEqBool E E'.
  Module Import InnerQuotationOfHasEqDec2Bool.
    Module E'' := HasEqDec2Bool E F.
  End InnerQuotationOfHasEqDec2Bool.
  #[export] Instance qeqb : quotation_of eqb := ltac:(cbv [eqb]; exact _).
  #[export] Instance qeqb_eq : quotation_of eqb_eq := ltac:(change (quotation_of E''.eqb_eq); unfold_quotation_of (); exact _).
End QuotationOfHasEqDec2Bool.

Module Type HasEqBool2DecSig (E : Eq) (F : HasEqBool E) <: HasEqDec E := Nop <+ HasEqBool2Dec E F.

Module QuotationOfHasEqBool2Dec (E : Eq) (F : HasEqBool E) (Import E' : HasEqBool2DecSig E F) (Import qE : QuotationOfEq E) (Import qF : QuotationOfHasEqBool E F) <: QuotationOfHasEqDec E E'.
  #[export] Instance qeq_dec : quotation_of eq_dec := ltac:(cbv [eq_dec]; exact _).
End QuotationOfHasEqBool2Dec.

Module Type Dec2BoolSig (E : DecidableType) <: BooleanDecidableType := Nop <+ Dec2Bool E.
Module Type Bool2DecSig (E : BooleanEqualityType) <: BooleanDecidableType := Nop <+ Bool2Dec E.

Module QuotationOfDec2Bool (E : DecidableType) (E' : Dec2BoolSig E) (qE : QuotationOfDecidableType E) <: QuotationOfBooleanDecidableType E'
  := qE <+ QuotationOfHasEqDec2Bool E E E'.

Module QuotationOfBool2Dec (E : BooleanEqualityType) (E' : Bool2DecSig E) (qE : QuotationOfBooleanEqualityType E) <: QuotationOfBooleanDecidableType E'
  := qE <+ QuotationOfHasEqBool2Dec E E E'.

Module Type BoolEqualityFactsSig (E : BooleanEqualityType) := Nop <+ BoolEqualityFacts E.

Module QuotationOfBoolEqualityFacts (Import E : BooleanEqualityType) (Import F : BoolEqualityFactsSig E) (Import qE : QuotationOfBooleanEqualityType E).
  #[export] Instance qeqb_compat : quotation_of F.eqb_compat := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb_spec : quotation_of F.eqb_spec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb_neq : quotation_of F.eqb_neq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb_refl : quotation_of F.eqb_refl := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb_sym : quotation_of F.eqb_sym := ltac:(unfold_quotation_of (); exact _).
End QuotationOfBoolEqualityFacts.

Module Type QuotationOfHasUsualEq (Import T : Typ) (Import E : HasUsualEq T) (Import qT : QuotationOfTyp T) <: QuotationOfHasEq T E.
  #[export] Instance qeq : quotation_of E.eq := ltac:(cbv [E.eq]; exact _).
End QuotationOfHasUsualEq.

Module Type QuotationOfUsualEq (E : UsualEq) <: QuotationOfEq E := QuotationOfTyp E <+ QuotationOfHasUsualEq E E.

Module Type QuotationOfUsualIsEq (E : UsualEq) (Import E' : UsualIsEq E) (Import qE : QuotationOfTyp E) <: QuotationOfIsEq E E'.
  #[export] Instance qeq_equiv : quotation_of eq_equiv := ltac:(cbv [eq_equiv]; exact _).
End QuotationOfUsualIsEq.

Module Type QuotationOfUsualIsEqOrig (E : UsualEq) (Import E' : UsualIsEqOrig E) (Import qE : QuotationOfTyp E) <: QuotationOfIsEqOrig E E'.
  #[export] Instance qeq_refl : quotation_of eq_refl := ltac:(cbv [eq_refl]; exact _).
  #[export] Instance qeq_sym : quotation_of eq_sym := ltac:(cbv [eq_sym]; exact _).
  #[export] Instance qeq_trans : quotation_of eq_trans := ltac:(cbv [eq_trans]; exact _).
End QuotationOfUsualIsEqOrig.

Module Type QuotationOfUsualEqualityType (E : UsualEqualityType) <: QuotationOfEqualityType E
    := QuotationOfUsualEq E <+ QuotationOfUsualIsEq E E.

Module Type QuotationOfUsualDecidableType (E : UsualDecidableType) <: QuotationOfDecidableType E
  := QuotationOfUsualEq E <+ QuotationOfUsualIsEq E E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfUsualDecidableTypeOrig (E : UsualDecidableTypeOrig) <: QuotationOfDecidableTypeOrig E
  := QuotationOfUsualEq E <+ QuotationOfUsualIsEqOrig E E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfUsualDecidableTypeBoth (E : UsualDecidableTypeBoth) <: QuotationOfDecidableTypeBoth E
  := QuotationOfUsualEq E <+ QuotationOfUsualIsEq E E <+ QuotationOfUsualIsEqOrig E E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfUsualBoolEq (E : UsualBoolEq) := QuotationOfUsualEq E <+ QuotationOfHasEqBool E E.

Module Type QuotationOfUsualDecidableTypeFull (E : UsualDecidableTypeFull) <: QuotationOfDecidableTypeFull E
  := QuotationOfUsualEq E <+ QuotationOfUsualIsEq E E <+ QuotationOfUsualIsEqOrig E E <+ QuotationOfHasEqDec E E <+ QuotationOfHasEqBool E E.

Module Type QuotationOfMiniDecidableType (Import M : MiniDecidableType).
  Include QuotationOfTyp M.
  #[export] Declare Instance qeq_dec : quotation_of eq_dec.
End QuotationOfMiniDecidableType.

Module Type Make_UDTSig (M : MiniDecidableType) <: UsualDecidableTypeBoth := Nop <+ Make_UDT M.
Module Type Make_UDTFSig (M : UsualBoolEq) <: UsualDecidableTypeFull := Nop <+ Make_UDTF M.

Module QuotationOfMake_UDT (M : MiniDecidableType) (M' : Make_UDTSig M) (qM : QuotationOfMiniDecidableType M) <: QuotationOfUsualDecidableTypeBoth M'
  := qM <+ QuotationOfHasUsualEq M' M' <+ QuotationOfUsualIsEq M' M' <+ QuotationOfUsualIsEqOrig M' M'.

Module QuotationOfMake_UDTF (M : UsualBoolEq) (M' : Make_UDTFSig M) (qM : QuotationOfUsualBoolEq M) <: QuotationOfUsualDecidableTypeFull M'
  := qM <+ QuotationOfUsualIsEq M M' <+ QuotationOfUsualIsEqOrig M' M' <+ QuotationOfHasEqBool2Dec M' M' M'.

(** * Orders *)
Import Coq.Structures.Orders.
Module Type QuotationOfHasLt (Import T : Typ) (Import E : HasLt T).
  #[export] Declare Instance qlt : quotation_of E.lt.
End QuotationOfHasLt.

Module Type QuotationOfHasLe (Import T : Typ) (Import E : HasLe T).
  #[export] Declare Instance qle : quotation_of E.le.
End QuotationOfHasLe.

Module Type QuotationOfEqLt (E : EqLt) := QuotationOfTyp E <+ QuotationOfHasEq E E <+ QuotationOfHasLt E E.
Module Type QuotationOfEqLe (E : EqLe) := QuotationOfTyp E <+ QuotationOfHasEq E E <+ QuotationOfHasLe E E.
Module Type QuotationOfEqLtLe (E : EqLtLe) := QuotationOfTyp E <+ QuotationOfHasEq E E <+ QuotationOfHasLt E E <+ QuotationOfHasLe E E.

Module Type QuotationOfIsStrOrder (Import E : EqLt) (Import S : IsStrOrder E).
  #[export] Declare Instance qlt_strorder : quotation_of S.lt_strorder.
  #[export] Declare Instance qlt_compat : quotation_of S.lt_compat.
End QuotationOfIsStrOrder.

Module Type QuotationOfLeIsLtEq (Import E : EqLtLe) (Import S : LeIsLtEq E).
  #[export] Declare Instance qle_lteq : quotation_of S.le_lteq.
End QuotationOfLeIsLtEq.

Module Type QuotationOfStrOrder (E : StrOrder) := QuotationOfEqualityType E <+ QuotationOfHasLt E E <+ QuotationOfIsStrOrder E E.

Module Type QuotationOfHasCmp (Import T : Typ) (S : HasCmp T).
  #[export] Declare Instance qcompare : quotation_of S.compare.
End QuotationOfHasCmp.

Module Type QuotationOfCmpSpec (Import E : EqLt) (Import C : HasCmp E) (S : CmpSpec E C).
  #[export] Declare Instance qcompare_spec : quotation_of S.compare_spec.
End QuotationOfCmpSpec.

Module Type QuotationOfHasCompare (E : EqLt) (C : HasCompare E) := QuotationOfHasCmp E C <+ QuotationOfCmpSpec E C C.

Module Type QuotationOfDecStrOrder (E : DecStrOrder) := QuotationOfStrOrder E <+ QuotationOfHasCompare E E.

Module Type QuotationOfOrderedType (E : Orders.OrderedType) <: QuotationOfDecidableType E := QuotationOfDecStrOrder E <+ QuotationOfHasEqDec E E.

Module Type QuotationOfOrderedTypeFull (E : OrderedTypeFull) := QuotationOfOrderedType E <+ QuotationOfHasLe E E <+ QuotationOfLeIsLtEq E E.

Module Type QuotationOfUsualStrOrder (E : UsualStrOrder) := QuotationOfUsualEqualityType E <+ QuotationOfHasLt E E <+ QuotationOfIsStrOrder E E.
Module Type QuotationOfUsualDecStrOrder (E : UsualDecStrOrder) := QuotationOfUsualStrOrder E <+ QuotationOfHasCompare E E.
Module Type QuotationOfUsualOrderedType (E : UsualOrderedType) <: QuotationOfUsualDecidableType E <: QuotationOfOrderedType E
 := QuotationOfUsualDecStrOrder E <+ QuotationOfHasEqDec E E.
Module Type QuotationOfUsualOrderedTypeFull (E : UsualOrderedTypeFull) := QuotationOfUsualOrderedType E <+ QuotationOfHasLe E E <+ QuotationOfLeIsLtEq E E.

Module Type QuotationOfLtIsTotal (Import E : EqLt) (S : LtIsTotal E).
  #[export] Declare Instance qlt_total : quotation_of S.lt_total.
End QuotationOfLtIsTotal.

Module Type QuotationOfTotalOrder (E : TotalOrder) := QuotationOfStrOrder E <+ QuotationOfHasLe E E <+ QuotationOfLeIsLtEq E E <+ QuotationOfLtIsTotal E E.
Module Type QuotationOfUsualTotalOrder (E : UsualTotalOrder) <: QuotationOfTotalOrder E
 := QuotationOfUsualStrOrder E <+ QuotationOfHasLe E E <+ QuotationOfLeIsLtEq E E <+ QuotationOfLtIsTotal E E.

Module Type Compare2EqBoolSig (O : DecStrOrder) <: HasEqBool O := Nop <+ Compare2EqBool O.

Module QuotationOfCompare2EqBool (O : DecStrOrder) (Import E : Compare2EqBoolSig O) (Import qE : QuotationOfDecStrOrder O) <: QuotationOfHasEqBool O E.
  #[export] Instance qeqb : quotation_of E.eqb := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb_eq : quotation_of E.eqb_eq := ltac:(unfold_quotation_of (); exact _).
End QuotationOfCompare2EqBool.

Module Type DSO_to_OTSig (O : DecStrOrder) <: Orders.OrderedType := Nop <+ DSO_to_OT O.
Module QuotationOfDSO_to_OT (O : DecStrOrder) (E : DSO_to_OTSig O) (qO : QuotationOfDecStrOrder O) <: QuotationOfOrderedType E :=
  qO <+ QuotationOfCompare2EqBool O E <+ QuotationOfHasEqBool2Dec O E E.

Local Set Warnings Append "-notation-overridden".
Module Type OT_to_FullSig (O : Orders.OrderedType) <: OrderedTypeFull := Nop <+ OT_to_Full O.
Module QuotationOfOT_to_Full (O : Orders.OrderedType) (E : OT_to_FullSig O) (qO : QuotationOfOrderedType O) <: QuotationOfOrderedTypeFull E.
  Include qO.
  #[export] Instance qle : quotation_of E.le := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_lteq : quotation_of E.le_lteq := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOT_to_Full.

Module Type OTF_LtIsTotalSig (O : OrderedTypeFull) <: LtIsTotal O := Nop <+ OTF_LtIsTotal O.

Module QuotationOfOTF_LtIsTotal (O : OrderedTypeFull) (S : OTF_LtIsTotalSig O) (Import qO : QuotationOfOrderedTypeFull O) <: QuotationOfLtIsTotal O S.
  #[export] Instance qlt_total : quotation_of S.lt_total := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOTF_LtIsTotal.

Module Type OTF_to_TotalOrderSig (O : OrderedTypeFull) <: TotalOrder := Nop <+ OTF_to_TotalOrder O.
Module QuotationOfOTF_to_TotalOrder (O : OrderedTypeFull) (S : OTF_to_TotalOrderSig O) (qO : QuotationOfOrderedTypeFull O) <: QuotationOfTotalOrder S
 := qO <+ QuotationOfOTF_LtIsTotal O S.

Module Type QuotationOfHasLeb (Import T : Typ) (Import S : HasLeb T).
 #[export] Declare Instance qleb : quotation_of S.leb.
End QuotationOfHasLeb.

Module Type QuotationOfHasLtb (Import T : Typ) (Import S : HasLtb T).
 #[export] Declare Instance qltb : quotation_of S.ltb.
End QuotationOfHasLtb.

Module Type QuotationOfLebSpec (T : Typ) (X : HasLe T) (Y : HasLeb T) (S : LebSpec T X Y).
 #[export] Declare Instance qleb_le : quotation_of S.leb_le.
End QuotationOfLebSpec.

Module Type QuotationOfLtbSpec (T : Typ) (X : HasLt T) (Y : HasLtb T) (S : LtbSpec T X Y).
 #[export] Declare Instance qltb_lt : quotation_of S.ltb_lt.
End QuotationOfLtbSpec.

Module Type QuotationOfLeBool (E : LeBool) := QuotationOfTyp E <+ QuotationOfHasLeb E E.
Module Type QuotationOfLtBool (E : LtBool) := QuotationOfTyp E <+ QuotationOfHasLtb E E.

Module Type QuotationOfLebIsTotal (Import X : LeBool) (Import S : LebIsTotal X).
 #[export] Declare Instance qleb_total : quotation_of S.leb_total.
End QuotationOfLebIsTotal.

Module Type QuotationOfTotalLeBool (E : TotalLeBool) := QuotationOfLeBool E <+ QuotationOfLebIsTotal E E.

Module Type QuotationOfLebIsTransitive (Import X : LeBool) (S : LebIsTransitive X).
 #[export] Declare Instance qleb_trans : quotation_of S.leb_trans.
End QuotationOfLebIsTransitive.

Module Type QuotationOfTotalTransitiveLeBool (E : TotalTransitiveLeBool) := QuotationOfTotalLeBool E <+ QuotationOfLebIsTransitive E E.

Module Type QuotationOfHasBoolOrdFuns (T : Typ) (S : HasBoolOrdFuns T) := QuotationOfHasEqb T S <+ QuotationOfHasLtb T S <+ QuotationOfHasLeb T S.

Module Type QuotationOfBoolOrdSpecs (O : EqLtLe) (F : HasBoolOrdFuns O) (S : BoolOrdSpecs O F) :=
 QuotationOfEqbSpec O O F S <+ QuotationOfLtbSpec O O F S <+ QuotationOfLebSpec O O F S.

Module Type QuotationOfOrderFunctions (E : EqLtLe) (S : OrderFunctions E) :=
  QuotationOfHasCompare E S <+ QuotationOfHasBoolOrdFuns E S <+ QuotationOfBoolOrdSpecs E S S.

Module Type OTF_to_TTLBSig (O : OrderedTypeFull) <: TotalTransitiveLeBool := Nop <+ OTF_to_TTLB O.

Module QuotationOfOTF_to_TTLB (Import O : OrderedTypeFull) (Import S : OTF_to_TTLBSig O) (Import qO : QuotationOfOrderedTypeFull O) <: QuotationOfTotalTransitiveLeBool S.
  #[export] Instance qleb : quotation_of S.leb := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qleb_le : quotation_of S.leb_le := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qleb_total : quotation_of S.leb_total := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qleb_trans : quotation_of S.leb_trans := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qt : quotation_of S.t := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOTF_to_TTLB.

Module Type TTLB_to_OTFSig (O : TotalTransitiveLeBool) <: OrderedTypeFull := Nop <+ TTLB_to_OTF O.

Module QuotationOfTTLB_to_OTF (Import O : TotalTransitiveLeBool) (Import S : TTLB_to_OTFSig O) (Import qO : QuotationOfTotalTransitiveLeBool O) <: QuotationOfOrderedTypeFull S.
  #[export] Instance qt : quotation_of S.t := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle : quotation_of S.le := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt : quotation_of S.lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq : quotation_of S.eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare : quotation_of S.compare := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_spec : quotation_of S.compare_spec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb : quotation_of S.eqb := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb_eq : quotation_of S.eqb_eq := ltac:(unfold_quotation_of (); exact _).
  Include QuotationOfHasEqBool2Dec S S S.
  #[export] Instance qeq_equiv : quotation_of S.eq_equiv := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_strorder : quotation_of S.lt_strorder := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_compat : quotation_of S.lt_compat := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_lteq : quotation_of S.le_lteq := ltac:(unfold_quotation_of (); exact _).
End QuotationOfTTLB_to_OTF.

(** * OrdersAlt *)
Import Coq.Structures.OrdersAlt.
Module Type QuotationOfOrderedTypeOrig (Import O : OrderedTypeOrig).
  #[export] Declare Instance qt : quotation_of O.t.
  #[export] Declare Instance qeq : quotation_of O.eq.
  #[export] Declare Instance qlt : quotation_of O.lt.
  #[export] Declare Instance qeq_refl : quotation_of O.eq_refl.
  #[export] Declare Instance qeq_sym : quotation_of O.eq_sym.
  #[export] Declare Instance qeq_trans : quotation_of O.eq_trans.
  #[export] Declare Instance qlt_trans : quotation_of O.lt_trans.
  #[export] Declare Instance qlt_not_eq : quotation_of O.lt_not_eq.
  #[export] Declare Instance qcompare : quotation_of O.compare.
  #[export] Declare Instance qeq_dec : quotation_of O.eq_dec.
End QuotationOfOrderedTypeOrig.

Module Type QuotationOfOrderedTypeAlt (Import O : OrderedTypeAlt).
 #[export] Declare Instance qt : quotation_of O.t.
 #[export] Declare Instance qcompare : quotation_of O.compare.
 #[export] Declare Instance qcompare_sym : quotation_of O.compare_sym.
 #[export] Declare Instance qcompare_trans : quotation_of O.compare_trans.
End QuotationOfOrderedTypeAlt.

Module Type Update_OTSig (O : OrderedTypeOrig) <: Orders.OrderedType := Nop <+ Update_OT O.
Module QuotationOfUpdate_OT (O : OrderedTypeOrig) (S : Update_OTSig O) (Import qO : QuotationOfOrderedTypeOrig O) <: QuotationOfOrderedType S.

  Include QuotationOfUpdate_DT O S qO.  (* Provides : qt qeq qeq_equiv qeq_dec *)
  #[export] Instance qlt : quotation_of S.lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_strorder : quotation_of S.lt_strorder := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_compat : quotation_of S.lt_compat := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare : quotation_of S.compare := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_spec : quotation_of S.compare_spec := ltac:(unfold_quotation_of (); exact _).
End QuotationOfUpdate_OT.

Module Type Backport_OTSig (O : Orders.OrderedType) <: OrderedTypeOrig := Nop <+ Backport_OT O.
Module QuotationOfBackport_OT (O : Orders.OrderedType) (S : Backport_OTSig O) (Import qO : QuotationOfOrderedType O) <: QuotationOfOrderedTypeOrig S.

  Include QuotationOfBackport_DT O S qO. (* Provides : qt qeq qeq_refl qeq_sym qeq_trans qeq_dec *)
  #[export] Instance qlt : quotation_of S.lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_not_eq : quotation_of S.lt_not_eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_trans : quotation_of S.lt_trans := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare : quotation_of S.compare := ltac:(unfold_quotation_of (); exact _).
End QuotationOfBackport_OT.

Module Type OT_from_AltSig (O : OrderedTypeAlt) <: Orders.OrderedType := Nop <+ OT_from_Alt O.

Module QuotationOfOT_from_Alt (O : OrderedTypeAlt) (S : OT_from_AltSig O) (Import qO : QuotationOfOrderedTypeAlt O) <: QuotationOfOrderedType S.
  #[export] Instance qt : quotation_of S.t := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq : quotation_of S.eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt : quotation_of S.lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_equiv : quotation_of S.eq_equiv := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_strorder : quotation_of S.lt_strorder := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_eq : quotation_of S.lt_eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_lt : quotation_of S.eq_lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_compat : quotation_of S.lt_compat := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare : quotation_of S.compare := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_spec : quotation_of S.compare_spec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_dec : quotation_of S.eq_dec := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOT_from_Alt.

Module Type OT_to_AltSig (O : Orders.OrderedType) <: OrderedTypeAlt := Nop <+ OT_to_Alt O.

Module QuotationOfOT_to_Alt (O : Orders.OrderedType) (S : OT_to_AltSig O) (Import qO : QuotationOfOrderedType O) <: QuotationOfOrderedTypeAlt S.
  #[export] Instance qt : quotation_of S.t := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare : quotation_of S.compare := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_sym : quotation_of S.compare_sym := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_Eq : quotation_of S.compare_Eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_Lt : quotation_of S.compare_Lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_Gt : quotation_of S.compare_Gt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_trans : quotation_of S.compare_trans := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOT_to_Alt.

(** * OrdersTac *)
Import Coq.Structures.OrdersTac.

Module Type QuotationOfIsTotalOrder (O : EqLtLe) (S : IsTotalOrder O) :=
 QuotationOfIsEq O S <+ QuotationOfIsStrOrder O S <+ QuotationOfLeIsLtEq O S <+ QuotationOfLtIsTotal O S.

Module Type OrderFactsSig (O : EqLtLe) (P : IsTotalOrder O) := Nop <+ OrderFacts O P.
Module QuotationOfOrderFacts (O : EqLtLe) (P : IsTotalOrder O) (S : OrderFactsSig O P) (Import qO : QuotationOfEqLtLe O) (Import qP : QuotationOfIsTotalOrder O P).
  #[export] Instance qeq_refl : quotation_of S.eq_refl := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_refl : quotation_of S.le_refl := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_irrefl : quotation_of S.lt_irrefl := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_sym : quotation_of S.eq_sym := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_antisym : quotation_of S.le_antisym := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qneq_sym : quotation_of S.neq_sym := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qinterp_ord : quotation_of S.interp_ord := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qtrans : quotation_of S.trans := ltac:(unfold_quotation_of (); exact _). (* takes about 20s :-( *)
  #[export] Instance qeq_trans : quotation_of S.eq_trans := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_trans : quotation_of S.le_trans := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_trans : quotation_of S.lt_trans := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_lt_trans : quotation_of S.le_lt_trans := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_le_trans : quotation_of S.lt_le_trans := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_lt : quotation_of S.eq_lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_eq : quotation_of S.lt_eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_le : quotation_of S.eq_le := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_eq : quotation_of S.le_eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_neq : quotation_of S.eq_neq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qneq_eq : quotation_of S.neq_eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qnot_neq_eq : quotation_of S.not_neq_eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qnot_ge_lt : quotation_of S.not_ge_lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qnot_gt_le : quotation_of S.not_gt_le := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_neq_lt : quotation_of S.le_neq_lt := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOrderFacts.

Module Type MakeOrderTacSig (O : EqLtLe) (P : IsTotalOrder O) := Nop <+ MakeOrderTac O P.

Module QuotationOfMakeOrderTac (O : EqLtLe) (P : IsTotalOrder O) (S : MakeOrderTacSig O P) (Import qO : QuotationOfEqLtLe O) (Import qP : QuotationOfIsTotalOrder O P).
  Include QuotationOfOrderFacts O P S qO qP.
End QuotationOfMakeOrderTac.

Module Type OTF_to_OrderTacSig (OTF : OrderedTypeFull) := Nop <+ OTF_to_OrderTac OTF.
Module QuotationOfOTF_to_OrderTac (OTF : OrderedTypeFull) (S : OTF_to_OrderTacSig OTF) (Import qOTF : QuotationOfOrderedTypeFull OTF).
  Module qTO := QuotationOfOTF_to_TotalOrder OTF S.TO qOTF.
  Export (hints) qTO.
  Include !QuotationOfMakeOrderTac OTF S.TO S qOTF qTO.
End QuotationOfOTF_to_OrderTac.

Module Type OT_to_OrderTacSig (OT : OrderedType) := Nop <+ OT_to_OrderTac OT.
Module QuotationOfOT_to_OrderTac (OT : OrderedType) (S : OT_to_OrderTacSig OT) (Import qOT : QuotationOfOrderedType OT).
  Module qOTF := QuotationOfOT_to_Full OT S.OTF qOT.
  Export (hints) qOTF.
  Include !QuotationOfOTF_to_OrderTac S.OTF S qOTF.
End QuotationOfOT_to_OrderTac.

(** * OrdersFacts *)
Import Coq.Structures.OrdersFacts.

Module QuotationOfCompareFacts (O : DecStrOrder) (F : CompareFacts O) (Import qO : QuotationOfDecStrOrder O).
  #[export] Instance qcompare_eq_iff : quotation_of F.compare_eq_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_eq : quotation_of F.compare_eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_lt_iff : quotation_of F.compare_lt_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_gt_iff : quotation_of F.compare_gt_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_nlt_iff : quotation_of F.compare_nlt_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_ngt_iff : quotation_of F.compare_ngt_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_compat : quotation_of F.compare_compat := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_refl : quotation_of F.compare_refl := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_antisym : quotation_of F.compare_antisym := ltac:(unfold_quotation_of (); exact _).
End QuotationOfCompareFacts.

Module Type OrderedTypeFullFactsSig (O : OrderedTypeFull) := Nop <+ OrderedTypeFullFacts O.

Module QuotationOfOrderedTypeFullFacts (O : OrderedTypeFull) (F : OrderedTypeFullFactsSig O) (Import qO : QuotationOfOrderedTypeFull O).
  Module qOrderTac := QuotationOfOTF_to_OrderTac O F.OrderTac qO.
  Export (hints) qOrderTac.
  #[export] Instance qle_compat : quotation_of F.le_compat := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_preorder : quotation_of F.le_preorder := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_order : quotation_of F.le_order := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_antisym : quotation_of F.le_antisym := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_not_gt_iff : quotation_of F.le_not_gt_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_not_ge_iff : quotation_of F.lt_not_ge_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_or_gt : quotation_of F.le_or_gt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_or_ge : quotation_of F.lt_or_ge := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_is_le_ge : quotation_of F.eq_is_le_ge := ltac:(unfold_quotation_of (); exact _).
  Include QuotationOfCompareFacts O F qO.
  #[export] Instance qcompare_le_iff : quotation_of F.compare_le_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_ge_iff : quotation_of F.compare_ge_iff := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOrderedTypeFullFacts.

Module Type OrderedTypeFactsSig (O : Orders.OrderedType) := Nop <+ OrderedTypeFacts O.

Module QuotationOfOrderedTypeFacts (O : Orders.OrderedType) (F : OrderedTypeFactsSig O) (Import qO : QuotationOfOrderedType O).
  Module qOrderTac := QuotationOfOT_to_OrderTac O F.OrderTac qO.
  Export (hints) qOrderTac.
  #[export] Instance qeq_refl : quotation_of F.eq_refl := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_sym : quotation_of F.eq_sym := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_trans : quotation_of F.eq_trans := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_trans : quotation_of F.lt_trans := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_irrefl : quotation_of F.lt_irrefl := ltac:(unfold_quotation_of (); exact _).
  Include QuotationOfCompareFacts O F qO.
  #[export] Instance qeq_dec : quotation_of F.eq_dec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_dec : quotation_of F.lt_dec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb : quotation_of F.eqb := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qif_eq_dec : quotation_of F.if_eq_dec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb_alt : quotation_of F.eqb_alt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb_compat : quotation_of F.eqb_compat := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOrderedTypeFacts.

Module Type OrderedTypeRevSig (O : OrderedTypeFull) <: OrderedTypeFull := Nop <+ OrderedTypeRev O.
Module QuotationOfOrderedTypeRev (O : OrderedTypeFull) (S : OrderedTypeRevSig O) (Import qO : QuotationOfOrderedTypeFull O) <: QuotationOfOrderedTypeFull S.
  #[export] Instance qt : quotation_of S.t := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq : quotation_of S.eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_equiv : quotation_of S.eq_equiv := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeq_dec : quotation_of S.eq_dec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt : quotation_of S.lt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle : quotation_of S.le := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_strorder : quotation_of S.lt_strorder := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_compat : quotation_of S.lt_compat := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qle_lteq : quotation_of S.le_lteq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare : quotation_of S.compare := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_spec : quotation_of S.compare_spec := ltac:(unfold_quotation_of (); exact _).
End QuotationOfOrderedTypeRev.

Module Type QuotationOfCompareBasedOrder (E : EqLtLe) (C : HasCmp E) (S : CompareBasedOrder E C).
 Include QuotationOfIsEq E S.
 #[export] Declare Instance qcompare_eq_iff : quotation_of S.compare_eq_iff.
 #[export] Declare Instance qcompare_lt_iff : quotation_of S.compare_lt_iff.
 #[export] Declare Instance qcompare_le_iff : quotation_of S.compare_le_iff.
 #[export] Declare Instance qcompare_antisym : quotation_of S.compare_antisym.
End QuotationOfCompareBasedOrder.

Module QuotationOfCompareBasedOrderFacts (E : EqLtLe) (C : HasCmp E) (O : CompareBasedOrder E C) (F : CompareBasedOrderFacts E C O) (Import qE : QuotationOfEqLtLe E) (Import qC : QuotationOfHasCmp E C) (Import qO : QuotationOfCompareBasedOrder E C O).
  #[export] Instance qcompare_spec : quotation_of F.compare_spec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_eq : quotation_of F.compare_eq := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_refl : quotation_of F.compare_refl := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_gt_iff : quotation_of F.compare_gt_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_ge_iff : quotation_of F.compare_ge_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_ngt_iff : quotation_of F.compare_ngt_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_nlt_iff : quotation_of F.compare_nlt_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_nle_iff : quotation_of F.compare_nle_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qcompare_nge_iff : quotation_of F.compare_nge_iff := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_irrefl : quotation_of F.lt_irrefl := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qlt_eq_cases : quotation_of F.lt_eq_cases := ltac:(unfold_quotation_of (); exact _).
End QuotationOfCompareBasedOrderFacts.

Module QuotationOfBoolOrderFacts
  (E : EqLtLe)
  (C : HasCmp E)
  (F : HasBoolOrdFuns E)
  (O : CompareBasedOrder E C)
  (S : BoolOrdSpecs E F)
  (Facts : BoolOrderFacts E C F O S)
  (Import qE : QuotationOfEqLtLe E)
  (Import qC : QuotationOfHasCmp E C)
  (Import qF : QuotationOfHasBoolOrdFuns E F)
  (Import qO : QuotationOfCompareBasedOrder E C O)
  (Import qS : QuotationOfBoolOrdSpecs E F S).

  Include QuotationOfCompareBasedOrderFacts E C O Facts qE qC qO.
  #[export] Instance qleb_spec0 : quotation_of Facts.leb_spec0 := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qleb_spec : quotation_of Facts.leb_spec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qltb_spec0 : quotation_of Facts.ltb_spec0 := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qltb_spec : quotation_of Facts.ltb_spec := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qleb_nle : quotation_of Facts.leb_nle := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qleb_gt : quotation_of Facts.leb_gt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qltb_nlt : quotation_of Facts.ltb_nlt := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qltb_ge : quotation_of Facts.ltb_ge := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qleb_refl : quotation_of Facts.leb_refl := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qleb_antisym : quotation_of Facts.leb_antisym := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qltb_irrefl : quotation_of Facts.ltb_irrefl := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qltb_antisym : quotation_of Facts.ltb_antisym := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qeqb_compare : quotation_of Facts.eqb_compare := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qltb_compare : quotation_of Facts.ltb_compare := ltac:(unfold_quotation_of (); exact _).
  #[export] Instance qleb_compare : quotation_of Facts.leb_compare := ltac:(unfold_quotation_of (); exact _).
End QuotationOfBoolOrderFacts.
