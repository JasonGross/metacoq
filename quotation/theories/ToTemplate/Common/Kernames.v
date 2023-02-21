From Coq Require Import Lists.List.
From MetaCoq.Quotation.ToTemplate Require Export Init.
From MetaCoq.Quotation.ToTemplate Require Export (hints) Coq.Init Coq.Structures Coq.MSets Coq.FSets bytestring.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Utils Require Import bytestring monad_utils.
From MetaCoq.Template Require Import Loader TemplateMonad.

Local Open Scope bs.
Import MCMonadNotation.
Import ListNotations.

#[export] Instance quote_modpath : ground_quotable modpath := ltac:(induction 1; exact _).

From MetaCoq.Utils Require Export bytestring.
From MetaCoq.Utils Require Import utils MCList.
From MetaCoq.Template Require Import MonadBasicAst MonadAst TemplateMonad Ast Loader.
From MetaCoq.Quotation Require Export CommonUtils.
Require Import Equations.Prop.Classes.
Require Import Coq.Lists.List.
Import ListNotations.

Local Set Primitive Projections.
Local Open Scope bs.
Import MCMonadNotation.

Print relevance.
Print mutual_inductive_body.
Definition tmMakeQuotationOfConstants {debug:debug_opt} (do_existing_instance : bool) (cs : list global_reference) : TemplateMonad unit
  := let warn_bad_ctx c ctx :=
       (_ <- tmMsg "tmMakeQuotationOfModule: cannot handle polymorphism";;
        _ <- tmPrint c;;
        _ <- tmPrint ctx;;
        tmReturn tt) in
     let tmDebugMsg s := (if debug
                          then tmMsg s
                          else tmReturn tt) in
     let tmDebugPrint {T} (v : T) := (if debug
                                      then tmPrint v
                                      else tmReturn tt) in
     let on_bad_relevance r :=
       (_ <- tmDebugMsg "skipping irrelevant constant";;
        _ <- tmDebugPrint r;;
        tmReturn []) in
     let cs := dedup_grefs cs in
     cs <- tmEval cbv cs;;
     _ <- tmDebugMsg "tmMakeQuotationOfConstants: looking up module constants";;
     ps <- monad_map
             (fun r
              => _ <- tmDebugMsg "tmMakeQuotationOfConstants: handling";;
                 _ <- tmDebugPrint r;;
                 match r with
                 | ConstRef ((mp, name) as c)
                   => '(inst, rel) <- (cb <- tmQuoteConstant c false;;
                                       inst <- match cb.(cst_universes) with
                                               | Monomorphic_ctx => tmReturn []
                                               | (Polymorphic_ctx (univs, constraints)) as ctx
                                                 => _ <- warn_bad_ctx r ctx;;
                                                    tmReturn []
                                               end;;
                                       tmReturn (inst, cb.(cst_relevance)));;
                      match rel with
                      | Irrelevant => on_bad_relevance r
                      | Relevant
                        => let c := tConst c inst in
                           _ <- tmDebugMsg "tmMakeQuotationOfConstants: tmUnquote";;
                           '{| my_projT1 := cty ; my_projT2 := cv |} <- tmUnquote c;;
                           _ <- tmDebugMsg "tmMakeQuotationOfConstants: tmUnquote done";;
                           let ty := @quotation_of cty cv in
                           tmReturn [("q" ++ name, {| my_projT1 := ty ; my_projT2 := c |})]
                      end
                 | IndRef ind
                   => inst <- (mib <- tmQuoteInductive ind.(inductive_mind);;
                               match mib.(ind_universes) with
                               | Monomorphic_ctx => tmReturn []
                               | (Polymorphic_ctx (univs, constraints)) as ctx
                                 => _ <- warn_bad_ctx r ctx;;
                                    tmReturn []
                               end);;
                      let '(mp, name) := ind.(inductive_mind) in
                      let c := tInd ind inst in
                      _ <- tmDebugMsg "tmMakeQuotationOfConstants: tmUnquote";;
                      '{| my_projT1 := cty ; my_projT2 := cv |} <- tmUnquote c;;
                      _ <- tmDebugMsg "tmMakeQuotationOfConstants: tmUnquote done";;
                      let ty := inductive_quotation_of cv in
                      let v : ty := {| qinductive := ind ; qinst := inst |} in
                      tmReturn [("q" ++ name, {| my_projT1 := ty ; my_projT2 := v |})]
                 | ConstructRef _ _ | VarRef _ => tmReturn []
                 end)
             cs;;
     let ps := flat_map (fun x => x) ps in
     _ <- tmDebugMsg "tmMakeQuotationOfConstants: relaxing Set and retyping module constants";;
     ps <- monad_map
             (fun '(name, {| my_projT1 := ty ; my_projT2 := v |})
              => _ <- tmDebugMsg ("tmMakeQuotationOfConstants: relaxing " ++ name);;
                 _ <- tmDebugPrint ("before"%bs, v, ":"%bs, ty);;
                 ty <- tmRetypeRelaxType ty;;
                 (* hack around https://github.com/MetaCoq/metacoq/issues/853 *)
                 v <- tmRetypeRelaxType v;;
                 v <- tmObj_magic v;;
                 _ <- tmDebugPrint ("after"%bs, v, ":"%bs, ty);;
                 tmReturn (name, {| my_projT1 := ty ; my_projT2 := v |}))
             ps;;
     _ <- tmDebugMsg "tmMakeQuotationOfConstants: defining module constants";;
     ps <- monad_map
             (fun '(name, {| my_projT1 := ty ; my_projT2 := v |})
              => (* debugging sanity checks for hack around https://github.com/MetaCoq/metacoq/issues/853 *)
                _ <- tmDebugPrint (tmRetype ty);;
                _ <- tmRetype ty;;
                _ <- tmDebugPrint (tmRetype v);;
                _ <- tmRetype v;;
                _ <- tmDebugPrint (@tmDefinition name ty v);;
                n <- @tmDefinition name ty v;;
                _ <- tmDebugMsg "tmMakeQuotationOfConstants: tmQuoteToGlobalReference";;
                qn <- tmQuoteToGlobalReference n;;
                tmReturn qn)
             ps;;
     _ <- (if do_existing_instance
           then
             _ <- tmDebugMsg "tmMakeQuotationOfConstants: making instances";;
             monad_map tmExistingInstance ps
           else tmReturn []);;
     tmReturn tt.

Definition tmMakeQuotationOfModule {debug:debug_opt} (do_existing_instance : bool) (m : qualid) : TemplateMonad _
  := cs <- tmQuoteModule m;;
     tmMakeQuotationOfConstants do_existing_instance cs.
Global Arguments tmMakeQuotationOfModule {_%bool} _%bool _%bs.

Definition tmMakeQuotationOfModuleAndRebase {debug:debug_opt} (do_existing_instance : bool) (reference_mp : qualid) (new_base_mp : modpath) : TemplateMonad _
  := cs <- tmQuoteModule reference_mp;;
     let cs := List.map (rebase_global_reference new_base_mp) cs in
     tmMakeQuotationOfConstants do_existing_instance cs.
Global Arguments tmMakeQuotationOfModuleAndRebase {_%bool} _%bool _%bs _.

Module qKername <: QuotationOfOrderedType Kername.
  MetaCoq Run (tmMakeQuotationOfModule false "Kername").
  Module qOT <: QuotationOfOrderedTypeOrig Kername.OT.
    (* kludge around https://github.com/MetaCoq/metacoq/issues/847 *)
    Module OT'. Include Kername.OT. End OT'.
    MetaCoq Run (Kername_mp <- tmExtractBaseModPathFromMod "Kername";; tmMakeQuotationOfModuleAndRebase false "OT'" (MPdot Kername_mp "OT")).
  End qOT.
End qKername.

Module qKernameSet <: MSetAVL.QuotationOfMake Kername KernameSet.
  (* kludge around https://github.com/MetaCoq/metacoq/issues/847 *)
  Module KernameSet'. Include KernameSet. End KernameSet'.
  Module qRaw.
    Module Raw'. Include KernameSet.Raw. End Raw'.
    MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "Raw'" (MPdot (MPdot Kernames_mp "KernameSet") "Raw")).
  End qRaw.
  MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "KernameSet'" (MPdot Kernames_mp "KernameSet")).
End qKernameSet.
Module qKernameSetOrdProp <: MSets.QuotationOfOrdProperties KernameSet KernameSetOrdProp qKername.
  Module qME := Structures.QuotationOfOrderedTypeFacts KernameSet.E KernameSetOrdProp.ME qKername.
  (*Module qML := QuotationOfOrderedTypeLists M.E F.ML.*)
  Module qP <: MSets.QuotationOfWProperties KernameSet KernameSetOrdProp.P.
    Module qDec <: MSets.QuotationOfWDecideOn Kername KernameSet KernameSetOrdProp.P.Dec.
      Module qF <: MSets.QuotationOfWFactsOn Kername KernameSet KernameSetOrdProp.P.Dec.F.
        Module F'. Include KernameSetOrdProp.P.Dec.F. End F'.
        MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "F'" (MPdot (MPdot (MPdot (MPdot Kernames_mp "KernameSetOrdProp") "P") "Dec") "F")).
      End qF.
      Module qMSetDecideAuxiliary.
        Module MSetDecideAuxiliary'. Include KernameSetOrdProp.P.Dec.MSetDecideAuxiliary. End MSetDecideAuxiliary'.
        MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "MSetDecideAuxiliary'" (MPdot (MPdot (MPdot (MPdot Kernames_mp "KernameSetOrdProp") "P") "Dec") "MSetDecideAuxiliary")).
      End qMSetDecideAuxiliary.
    End qDec.
    Module qFM <: MSets.QuotationOfWFactsOn Kername KernameSet KernameSetOrdProp.P.FM.
      Module FM'. Include KernameSetOrdProp.P.FM. End FM'.
      MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "FM'" (MPdot (MPdot (MPdot Kernames_mp "KernameSetOrdProp") "P") "FM")).
    End qFM.
    Module P'. Include KernameSetOrdProp.P. End P'.
    MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "P'" (MPdot (MPdot Kernames_mp "KernameSetOrdProp") "P")).
  End qP.
  Module KernameSetOrdProp'. Include KernameSetOrdProp. End KernameSetOrdProp'.
  MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "KernameSetOrdProp'" (MPdot Kernames_mp "KernameSetOrdProp")).
End qKernameSetOrdProp.
Module qKernameMap <: FMapAVL.QuotationOfMake Kername.OT KernameMap qKername.qOT.
  Module qRaw.
    Module Raw'. Include KernameMap.Raw. End Raw'.
    MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "Raw'" (MPdot (MPdot Kernames_mp "KernameMap") "Raw")).
  End qRaw.
  MetaCoq Run (tmMakeQuotationOfModule false "KernameMap").
End qKernameMap.
Module qKernameMapFact <: QuotationOfWFacts_fun Kername.OT KernameMap KernameMapFact.
  MetaCoq Run (tmMakeQuotationOfModule false "KernameMapFact").
End qKernameMapFact.

Module QuoteKernameSet := QuoteMSetAVL Kername KernameSet KernameSetOrdProp qKername qKernameSet qKernameSetOrdProp.
Export (hints) QuoteKernameSet.
Module QuoteKernameMap := QuoteFMapAVL Kername.OT KernameMap KernameMapFact qKername.qOT qKernameMap qKernameMapFact.
Export (hints) QuoteKernameMap.

#[export] Instance quote_inductive : ground_quotable inductive := ltac:(destruct 1; exact _).
#[export] Instance quote_projection : ground_quotable projection := ltac:(destruct 1; exact _).
#[export] Instance quote_global_reference : ground_quotable global_reference := ltac:(destruct 1; exact _).
