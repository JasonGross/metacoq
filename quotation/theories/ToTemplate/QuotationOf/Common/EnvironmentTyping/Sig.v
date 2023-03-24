From MetaCoq.Common Require Import BasicAst Environment EnvironmentTyping.
From MetaCoq.Quotation.ToTemplate Require Import Init.

Module Type QuotationOfLookup (T : Term) (E : EnvironmentSig T) (L : LookupSig T E).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "L").
End QuotationOfLookup.

Module Type QuoteLookupSig (Import T : Term) (Import E : EnvironmentSig T) (Import L : LookupSig T E).
  #[export] Declare Instance quote_consistent_instance {cf lvs ϕ uctx u} : ground_quotable (@consistent_instance cf lvs ϕ uctx u).
  #[export] Declare Instance quote_wf_universe {Σ s} : ground_quotable (@wf_universe Σ s).
  #[export] Declare Instance quote_declared_constant {Σ id decl} : ground_quotable (@declared_constant Σ id decl).
  #[export] Declare Instance quote_declared_minductive {Σ mind decl} : ground_quotable (@declared_minductive Σ mind decl).
  #[export] Declare Instance quote_declared_inductive {Σ ind mdecl decl} : ground_quotable (@declared_inductive Σ ind mdecl decl).
  #[export] Declare Instance quote_declared_constructor {Σ cstr mdecl idecl cdecl} : ground_quotable (@declared_constructor Σ cstr mdecl idecl cdecl).
  #[export] Declare Instance quote_declared_projection {Σ proj mdecl idecl cdecl pdecl} : ground_quotable (@declared_projection Σ proj mdecl idecl cdecl pdecl).
End QuoteLookupSig.

Module Type QuotationOfEnvTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).
  Instance: debug_opt := true. (*Set Printing Implicit. Set Printing Universes.*)
  Require Import monad_utils Loader.
  Import List.ListNotations.
  Open Scope list_scope.
  Import MetaCoq.Utils.bytestring MetaCoq.Utils.ReflectEq.
  Print bytestring.String.contains.
  Print bytestring.String.index.
  From MetaCoq.Utils Require Export bytestring.
From MetaCoq.Utils Require Import utils MCList.
From MetaCoq.Template Require Import MonadBasicAst MonadAst TemplateMonad Ast Loader.
Import MCMonadNotation.
  Compute String.index 0 "ctx_inst"%bs "ctx_inst_impl_gen"%bs.
  Axiom admit : forall {T}, T.
  Unset Universe Minimization ToSet.
  Polymorphic Definition tmRetypeMagicRelaxOnlyType'@{U a b t u} {A : Type@{a}} (B : Type@{b}) (x : A) : TemplateMonad@{t u} B
    := tmPrint x;;
       qx <- tmQuote x;;
       tmPrint qx;;
       qU <- tmQuoteUniverse@{U _ _};;
       tmPrint qU;;
       let qx := CommonUtils.WithTemplate.tmRelaxOnlyType (tSort qU) qx in
       qxe <- tmEval cbv qx;;
       let v := tmUnquoteTyped B qxe in
       tmPrint v;;
       tmMsg "unquoting";;
       v.
  Definition tmRetypeRelaxOnlyType' {A} x := @tmRetypeMagicRelaxOnlyType' A A x.
  Constraint tmRetypeRelaxOnlyType'.u0 = All_refl.u1.
  Set Printing Universes.
  Print All_refl.
  Check @All_Forall.All Type@{tmRetypeRelaxOnlyType'.u0}.
  Goal True.
    run_template_program (U <- tmQuote Type@{tmRetypeRelaxOnlyType'.u0};;
                          tmUnquote
                            (tApp
                               (tInd
                                  {|
                                    inductive_mind := (MPfile ["All_Forall"; "Utils"; "MetaCoq"], "All");
                                    inductive_ind := 0
                                  |} [])
                               [
                         ) (fun v => let v := eval cbv in v in pose v).
  MetaCoq Run (tmUnquote
  (tApp
     (tInd
        {|
          inductive_mind := (MPfile ["All_Forall"; "Utils"; "MetaCoq"], "All");
          inductive_ind := 0
        |} [])
     [tSort
        (Universe.lType
           {|
             t_set :=
               {|
                 LevelExprSet.this :=
                   [(Level.Level
                       "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                     0)];
                 LevelExprSet.is_ok :=
                   LevelExprSet.Raw.singleton_ok
                     (Level.Level
                        "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                      0)
               |};
             t_ne := @eq_refl bool false
           |})]);; @tmReturn unit tt
     : TemplateMonad unit).
  Definition foo : Core.TemplateMonad unit.
    pose (tmDeclareQuotationOfModule everything (Some export) "ET") as v.
    cbv [tmDeclareQuotationOfModule] in v.
    lazymatch (eval cbv [v] in v) with
    | monad_utils.bind ?p ?q
      => clear v;
         run_template_program p (fun p' => let p' := constr:(List.flat_map (fun r => match r with ConstRef (_, s) => match String.index 0 "ctx_inst"%bs s with Some _ => match String.index 0 "obligation"%bs s, String.index 0 "Confusion"%bs s with None, None => r :: nil | _, _ => nil end | None => nil end | _ => nil end) p') in
                                           pose (q (List.firstn 1 p' ++ List.skipn (List.length p' - 2) p')) as v)
    end.
    vm_compute List.flat_map in v.
    vm_compute List.app in v.
    cbn -[monad_utils.bind] in v.
    lazymatch (eval cbv [v] in v) with
    | monad_utils.bind ?p ?q
      => clear v;
         run_template_program p (fun p' => pose (q p') as v)
    end.
    cbv [tmDeclareQuotationOfConstants] in v.
    cbv [tmMakeQuotationOfConstants_gen] in v.
    do 2 lazymatch (eval cbv [v] in v) with
    | monad_utils.bind ?p ?q
      => clear v;
         run_template_program p (fun p' => pose (q p') as v)
      end; cbv beta in v.
    cbn -[monad_utils.bind] in v.
    repeat match (eval cbv [v] in v) with
    | context P[@monad_utils.bind ?m ?M ?t ?u (@monad_utils.bind ?m ?M ?t' ?u' ?x ?y)]
      => let P' := context P[fun z => @monad_utils.bind m M t' u x (fun x' => @monad_utils.bind m M u' u (y x') z)] in
         clear v; pose P' as v; cbv beta in v
           end.
    repeat match (eval cbv [v] in v) with
    | context P[tmPrint _]
      => let P' := context P[tmReturn tt] in
         clear v; pose P' as v; cbv beta in v
           end.
    repeat match (eval cbv [v] in v) with
    | context P[tmMsg _]
      => let P' := context P[tmReturn tt] in
         clear v; pose P' as v; cbv beta in v
           end.
    repeat match (eval cbv [v] in v) with
    | context P[@tmEval cbv ?A]
      => let P' := context P[@tmReturn A] in
         clear v; pose P' as v; cbv beta in v
           end.
    repeat match (eval cbv [v] in v) with
    | context P[tmExistingInstance _ _]
      => let P' := context P[tmReturn tt] in
         clear v; pose P' as v; cbv beta in v
           end.
    repeat match (eval cbv [v] in v) with
    | context P[tmQuoteToGlobalReference _]
      => let P' := context P[tmReturn (VarRef "")] in
         clear v; pose P' as v; cbv beta in v
           end.
    repeat match (eval cbv [v] in v) with
    | context P[@tmRetypeMagicRelaxOnlyType ?A]
      => let P' := context P[fun B (_ : A) => tmReturn (@admit B)] in
         clear v; pose P' as v; cbv beta in v
           end.
    cbv beta iota zeta in v.
    Ltac assoc v rest :=
      lazymatch (eval cbv beta iota zeta in v) with
      | @monad_utils.bind ?m ?M ?t ?u (tmReturn ?k) ?c
        => assoc (c k) rest
      | @monad_utils.bind ?m ?M ?t ?u (ret ?k) ?c
        => assoc (c k) rest
      | @monad_utils.bind ?m ?M ?t ?u ?k ?c
        => assoc k ltac:(fun kv => let kvn := fresh in idtac "binding" kv; refine (@monad_utils.bind m M t _ kv (fun kvn => ltac:(assoc (c kvn) rest))))
      | ?v => rest v
      end.
    do 5 (idtac; let v' := (eval cbv [v] in v) in
    let v' := constr:(ltac:(assoc v' ltac:(fun cv => refine cv)) : TemplateMonad unit) in
    clear v; pose v' as v; cbn [monad_map] in v).
    lazymatch (eval cbv [v] in v) with
    | v1 <- ?x1;; @?a1 v1;; v2 <- ?x2;; @?a2 v2;; v3 <- ?x3;; @?a3 v3;; tmReturn tt
      => clear v; pose (v1 <- x1;; v2 <- x2;; tmReturn tt) as v
    end.
    do 2 lazymatch (eval cbv [v] in v) with
           | context P[@tmRetypeRelaxOnlyType]
             => let P' := context P[@tmRetypeRelaxOnlyType'] in
                clear v; pose P' as v
      end.
    Set Printing Implicit. Set Printing Universes.
    cbv [tmRetypeRelaxOnlyType' tmRetypeMagicRelaxOnlyType'] in v.
    do 1 (idtac; let v' := (eval cbv [v] in v) in
    let v' := constr:(ltac:(assoc v' ltac:(fun cv => refine cv)) : TemplateMonad unit) in
    clear v; pose v' as v; cbn [monad_map] in v).
    do 17 lazymatch (eval cbv [v] in v) with
    | monad_utils.bind ?p ?q
      => clear v;
         run_template_program p (fun p' => pose (q p') as v)
      end; cbv beta in v.
    lazymatch (eval cbv [v] in v) with
    | @tmUnquoteTyped ?A ?x ;; tmReturn tt
      => clear v; pose (@tmUnquote x ;; tmReturn tt : TemplateMonad unit) as v
    end.
    Ltac run1 v :=
      lazymatch (eval cbv [v] in v) with
      | monad_utils.bind ?p ?q
        => clear v;
           run_template_program p (fun p' => pose (q p') as v)
      end.
    Ltac pose_unquote v x :=
      clear v;
      pose (@tmUnquote x ;; tmReturn tt : TemplateMonad unit) as v;
      cbv beta in v;
      assert_fails (idtac; run1 v).
    Ltac pose_unquote_list v x rebuild :=
      lazymatch x with
      | ?x :: ?xs
        => first [ let x := rebuild x in
                   pose_unquote v x
                 | pose_unquote_list v xs rebuild ]
      end.
    Ltac pose_unquote_list_chop_tail v x rebuild :=
      lazymatch x with
      | ?x :: ?xs
        => first [ pose_unquote_list_chop_tail v xs rebuild
                 | pose_unquote_list_chop_tail v xs ltac:(fun xs => rebuild (x :: xs)) ]
      | ?x => let x := rebuild x in
              pose_unquote v x
      end.
    Ltac walk v x rebuild :=
      lazymatch x with
      | tApp ?x ?y
        => first [ let x := rebuild x in
                   pose_unquote v x
                 | pose_unquote_list v y rebuild ]
      | tProd ?n ?x ?y
        => walk v (tLambda n x y) rebuild
      | tLambda ?n ?x ?y
        => first [ let x := rebuild x in
                   pose_unquote v x
                 | walk v y ltac:(fun y' => rebuild (tLambda n x y')) ]
      end.
    Ltac walkrm v x rebuild :=
      lazymatch x with
      | tApp ?x ?y
        => first [ let x := rebuild x in
                   pose_unquote v x
                 | pose_unquote_list v y rebuild
                 | lazymatch y with
                   | ?y :: @nil ?T
                     => walkrm v y ltac:(fun y => rebuild (tApp x (y :: @nil T)))
                   end ]
      | tProd ?n ?x ?y
        => first [ let y := rebuild y in
                   pose_unquote v y
                 | let x := rebuild x in
                   pose_unquote v x ]
      | tLambda ?n ?x ?y
        => first [ let y := rebuild y in
                   pose_unquote v y
                 | let x := rebuild x in
                   pose_unquote v x ]
      end.
    repeat lazymatch (eval cbv [v] in v) with
    | @tmUnquote ?x ;; tmReturn tt
      => walk v x ltac:(fun x => x)
           end.
    Set Printing Depth 100000.
    lazymatch (eval cbv [v] in v) with
    | context P[tLambda ?n0 ?ty0 (tLambda ?n ?ty (tApp ?x (?y :: ?z :: ?w)))]
      => idtac n0 n x y z w; let P' := context P[tLambda n0 ty0 (tLambda n ty (tApp x (y :: nil)))] in
         clear v; pose P' as v; assert_fails (idtac; run1 v)
    end.
    repeat lazymatch (eval cbv [v] in v) with
    | @tmUnquote (tLambda _ _ ?x) ;; tmReturn tt
      => clear v; pose (tmUnquote x ;; tmReturn tt : TemplateMonad unit) as v;
         assert_fails (idtac; run1 v)
           end.
    do 4 lazymatch (eval cbv [v] in v) with
    | @tmUnquote ?x ;; tmReturn tt
      => walkrm v x ltac:(fun x => x)
      end.
    (*run_template_program (tmQuote Type) (fun v => let v := eval cbv in v in pose v as U).
    run_template_program (tmUnquote
                            (tApp
                               (tInd
               {|
                 inductive_mind :=
                   (MPfile ["All_Forall"; "Utils"; "MetaCoq"], "All");
                 inductive_ind := 0
               |} [])
                               [tSort
                                  (Universe.lType
                                     {|
                                       t_set :=
                                         {|
                                           LevelExprSet.this :=
                                             [(Level.Level
                                                 "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                0)];
                                           LevelExprSet.is_ok :=
                                             LevelExprSet.Raw.singleton_ok
                                               (Level.Level
                                                  "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                 0)
                                         |};
                                       t_ne := @eq_refl bool false
                                     |})]);;
                          @tmReturn
                            unit tt) (fun x => pose x).
    run1 v.

           end.

      => walk v x ltac:(fun x => x)
           end.
    Check subst1.
    Search Ast.term.
    Print tProd.
                 assert_fails (run1 v)
               | pose (@tmUnquote y ;; tmReturn tt : TemplateMonad unit) as v;
                 assert_fails (run1 v)

         pose (@tmUnquote y ;; tmReturn tt : TemplateMonad unit) as v
    end.
    .*)
    let v' := (eval cbv [v] in v) in exact v'.
  Defined.
  Print Universes.

  Definition bar := Eval cbv [foo] in foo.
  Print bar.
  Print bar.
  Set Printing Implicit. Set Printing Universes.
  Print bar.
  Set Printing Depth 10000000.
  Print Options.
  Print Universes.
  Unset Printing Universes.
  Print bar.
  MetaCoq Run bar.
  Unset MetaCoq Strict Unquote Universe Mode.
  Fail MetaCoq Run bar.
  MetaCoq Run ((tmUnquoteTyped@{option_instance.u0 tmRetypeRelaxOnlyType'.u2}
   Type@{WithTemplate.tmRetypeAroundMetaCoqBug853.u3}
   (tApp
      (tConst
         (MPfile ["Init"; "ToTemplate"; "Quotation"; "MetaCoq"], "quotation_of") [])
      [tProd {| binder_name := nNamed "typing"; binder_relevance := Relevant |}
         (tProd {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
            (tConst
               (MPbound
                  ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                   "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "global_env_ext")
               [])
            (tProd {| binder_name := nNamed "Γ"; binder_relevance := Relevant |}
               (tConst
                  (MPbound
                     ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                      "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context") [])
               (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                  (tConst
                     (MPbound
                        ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                         "ToTemplate"; "Quotation"; "MetaCoq"] "T" 6, "term") [])
                  (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                     (tConst
                        (MPbound
                           ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                            "ToTemplate"; "Quotation"; "MetaCoq"] "T" 6, "term") [])
                     (tSort
                        (Universe.lType
                           {|
                             t_set :=
                               {|
                                 LevelExprSet.this :=
                                   [(Level.Level
                                       "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                     0)];
                                 LevelExprSet.is_ok :=
                                   LevelExprSet.Raw.singleton_ok
                                     (Level.Level
                                        "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                      0)
                               |};
                             t_ne := @eq_refl bool false
                           |}))))))
         (tProd {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
            (tConst
               (MPbound
                  ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                   "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "global_env_ext")
               [])
            (tProd {| binder_name := nNamed "Γ"; binder_relevance := Relevant |}
               (tConst
                  (MPbound
                     ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                      "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context") [])
               (tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
                  (tProd
                     {| binder_name := nNamed "l"; binder_relevance := Relevant |}
                     (tApp
                        (tInd
                           {|
                             inductive_mind :=
                               (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                             inductive_ind := 0
                           |} [])
                        [tConst
                           (MPbound
                              ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                               "ToTemplate"; "Quotation"; "MetaCoq"] "T" 6, "term")
                           []])
                     (tProd
                        {|
                          binder_name := nNamed "c"; binder_relevance := Relevant
                        |}
                        (tConst
                           (MPbound
                              ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                               "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                            "context") [])
                        (tProd
                           {|
                             binder_name := nNamed "c";
                             binder_relevance := Relevant
                           |}
                           (tApp
                              (tInd
                                 {|
                                   inductive_mind :=
                                     (MPbound
                                        ["Sig"; "EnvironmentTyping"; "Common";
                                         "QuotationOf"; "ToTemplate"; "Quotation";
                                         "MetaCoq"] "ET" 9, "ctx_inst");
                                   inductive_ind := 0
                                 |} []) [tRel 4; tRel 3; tRel 2; tRel 1; tRel 0])
                           (tSort
                              (Universe.lType
                                 {|
                                   t_set :=
                                     {|
                                       LevelExprSet.this :=
                                         [(Level.Level
                                             "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                           0)];
                                       LevelExprSet.is_ok :=
                                         LevelExprSet.Raw.singleton_ok
                                           (Level.Level
                                              "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                            0)
                                     |};
                                   t_ne := @eq_refl bool false
                                 |})))))
                  (tProd
                     {| binder_name := nNamed "f"; binder_relevance := Relevant |}
                     (tApp (tRel 0)
                        [tApp
                           (tConstruct
                              {|
                                inductive_mind :=
                                  (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                                inductive_ind := 0
                              |} 0 [])
                           [tConst
                              (MPbound
                                 ["Sig"; "EnvironmentTyping"; "Common";
                                  "QuotationOf"; "ToTemplate"; "Quotation";
                                  "MetaCoq"] "T" 6, "term") []];
                         tApp
                           (tConstruct
                              {|
                                inductive_mind :=
                                  (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                                inductive_ind := 0
                              |} 0 [])
                           [tApp
                              (tInd
                                 {|
                                   inductive_mind :=
                                     (MPfile ["BasicAst"; "Common"; "MetaCoq"],
                                      "context_decl");
                                   inductive_ind := 0
                                 |} [])
                              [tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common";
                                     "QuotationOf"; "ToTemplate"; "Quotation";
                                     "MetaCoq"] "T" 6, "term") []]];
                         tApp
                           (tConstruct
                              {|
                                inductive_mind :=
                                  (MPbound
                                     ["Sig"; "EnvironmentTyping"; "Common";
                                      "QuotationOf"; "ToTemplate"; "Quotation";
                                      "MetaCoq"] "ET" 9, "ctx_inst");
                                inductive_ind := 0
                              |} 0 []) [tRel 3; tRel 2; tRel 1]])
                     (tProd
                        {|
                          binder_name := nNamed "f0"; binder_relevance := Relevant
                        |}
                        (tProd
                           {|
                             binder_name := nNamed "na";
                             binder_relevance := Relevant
                           |}
                           (tConst
                              (MPfile ["BasicAst"; "Common"; "MetaCoq"], "aname")
                              [])
                           (tProd
                              {|
                                binder_name := nNamed "t";
                                binder_relevance := Relevant
                              |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common";
                                     "QuotationOf"; "ToTemplate"; "Quotation";
                                     "MetaCoq"] "T" 6, "term") [])
                              (tProd
                                 {|
                                   binder_name := nNamed "i";
                                   binder_relevance := Relevant
                                 |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common";
                                        "QuotationOf"; "ToTemplate"; "Quotation";
                                        "MetaCoq"] "T" 6, "term") [])
                                 (tProd
                                    {|
                                      binder_name := nNamed "inst";
                                      binder_relevance := Relevant
                                    |}
                                    (tApp
                                       (tInd
                                          {|
                                            inductive_mind :=
                                              (MPfile ["Datatypes"; "Init"; "Coq"],
                                               "list");
                                            inductive_ind := 0
                                          |} [])
                                       [tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common";
                                              "QuotationOf"; "ToTemplate";
                                              "Quotation"; "MetaCoq"] "T" 6, "term")
                                          []])
                                    (tProd
                                       {|
                                         binder_name := nNamed "Δ";
                                         binder_relevance := Relevant
                                       |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common";
                                              "QuotationOf"; "ToTemplate";
                                              "Quotation"; "MetaCoq"] "E" 7,
                                           "context") [])
                                       (tProd
                                          {|
                                            binder_name := nNamed "t";
                                            binder_relevance := Relevant
                                          |}
                                          (tApp (tRel 9)
                                             [tRel 8; tRel 7; tRel 2; tRel 3])
                                          (tProd
                                             {|
                                               binder_name := nNamed "c";
                                               binder_relevance := Relevant
                                             |}
                                             (tApp
                                                (tInd
                                                   {|
                                                     inductive_mind :=
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "ET" 9, "ctx_inst");
                                                     inductive_ind := 0
                                                   |} [])
                                                [tRel 10;
                                                 tRel 9;
                                                 tRel 8;
                                                 tRel 2;
                                                 tApp
                                                   (tConst
                                                      (
                                                      MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "E" 7,
                                                      "subst_telescope") [])
                                                   [tApp
                                                      (tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "list");
                                                      inductive_ind := 0
                                                      |} 1 [])
                                                      [
                                                      tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [];
                                                      tRel 3;
                                                      tApp
                                                      (tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "list");
                                                      inductive_ind := 0
                                                      |} 0 [])
                                                      [tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") []]];
                                                    tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "nat");
                                                      inductive_ind := 0
                                                      |} 0 [];
                                                    tRel 1]])
                                             (tProd
                                                {|
                                                  binder_name := nAnon;
                                                  binder_relevance := Relevant
                                                |}
                                                (tApp (tRel 8)
                                                   [tRel 3;
                                                    tApp
                                                      (tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "E" 7,
                                                      "subst_telescope") [])
                                                      [
                                                      tApp
                                                      (tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "list");
                                                      inductive_ind := 0
                                                      |} 1 [])
                                                      [tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [];
                                                      tRel 4;
                                                      tApp
                                                      (tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "list");
                                                      inductive_ind := 0
                                                      |} 0 [])
                                                      [tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") []]];
                                                      tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "nat");
                                                      inductive_ind := 0
                                                      |} 0 [];
                                                      tRel 2];
                                                    tRel 0])
                                                (tApp (tRel 9)
                                                   [tApp
                                                      (tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "list");
                                                      inductive_ind := 0
                                                      |} 1 [])
                                                      [
                                                      tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [];
                                                      tRel 5;
                                                      tRel 4];
                                                    tApp
                                                      (tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "list");
                                                      inductive_ind := 0
                                                      |} 1 [])
                                                      [
                                                      tApp
                                                      (tInd
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["BasicAst"; "Common";
                                                      "MetaCoq"], "context_decl");
                                                      inductive_ind := 0
                                                      |} [])
                                                      [tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") []];
                                                      tApp
                                                      (tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "E" 7, "vass") [])
                                                      [tRel 7; tRel 6];
                                                      tRel 3];
                                                    tApp
                                                      (tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "ET" 9, "ctx_inst");
                                                      inductive_ind := 0
                                                      |} 1 [])
                                                      [
                                                      tRel 12;
                                                      tRel 11;
                                                      tRel 10;
                                                      tRel 7;
                                                      tRel 6;
                                                      tRel 5;
                                                      tRel 4;
                                                      tRel 3;
                                                      tRel 2;
                                                      tRel 1]])))))))))
                        (tProd
                           {|
                             binder_name := nNamed "f1";
                             binder_relevance := Relevant
                           |}
                           (tProd
                              {|
                                binder_name := nNamed "na";
                                binder_relevance := Relevant
                              |}
                              (tConst
                                 (MPfile ["BasicAst"; "Common"; "MetaCoq"], "aname")
                                 [])
                              (tProd
                                 {|
                                   binder_name := nNamed "b";
                                   binder_relevance := Relevant
                                 |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common";
                                        "QuotationOf"; "ToTemplate"; "Quotation";
                                        "MetaCoq"] "T" 6, "term") [])
                                 (tProd
                                    {|
                                      binder_name := nNamed "t";
                                      binder_relevance := Relevant
                                    |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common";
                                           "QuotationOf"; "ToTemplate";
                                           "Quotation"; "MetaCoq"] "T" 6, "term")
                                       [])
                                    (tProd
                                       {|
                                         binder_name := nNamed "inst";
                                         binder_relevance := Relevant
                                       |}
                                       (tApp
                                          (tInd
                                             {|
                                               inductive_mind :=
                                                 (MPfile
                                                    ["Datatypes"; "Init"; "Coq"],
                                                  "list");
                                               inductive_ind := 0
                                             |} [])
                                          [tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping";
                                                 "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation";
                                                 "MetaCoq"] "T" 6, "term") []])
                                       (tProd
                                          {|
                                            binder_name := nNamed "Δ";
                                            binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping";
                                                 "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation";
                                                 "MetaCoq"] "E" 7, "context") [])
                                          (tProd
                                             {|
                                               binder_name := nNamed "c";
                                               binder_relevance := Relevant
                                             |}
                                             (tApp
                                                (tInd
                                                   {|
                                                     inductive_mind :=
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "ET" 9, "ctx_inst");
                                                     inductive_ind := 0
                                                   |} [])
                                                [tRel 10;
                                                 tRel 9;
                                                 tRel 8;
                                                 tRel 1;
                                                 tApp
                                                   (tConst
                                                      (
                                                      MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "E" 7,
                                                      "subst_telescope") [])
                                                   [tApp
                                                      (tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "list");
                                                      inductive_ind := 0
                                                      |} 1 [])
                                                      [
                                                      tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [];
                                                      tRel 3;
                                                      tApp
                                                      (tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "list");
                                                      inductive_ind := 0
                                                      |} 0 [])
                                                      [tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") []]];
                                                    tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "nat");
                                                      inductive_ind := 0
                                                      |} 0 [];
                                                    tRel 0]])
                                             (tProd
                                                {|
                                                  binder_name := nAnon;
                                                  binder_relevance := Relevant
                                                |}
                                                (tApp (tRel 8)
                                                   [tRel 2;
                                                    tApp
                                                      (tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "E" 7,
                                                      "subst_telescope") [])
                                                      [
                                                      tApp
                                                      (tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "list");
                                                      inductive_ind := 0
                                                      |} 1 [])
                                                      [tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [];
                                                      tRel 4;
                                                      tApp
                                                      (tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "list");
                                                      inductive_ind := 0
                                                      |} 0 [])
                                                      [tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") []]];
                                                      tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "nat");
                                                      inductive_ind := 0
                                                      |} 0 [];
                                                      tRel 1];
                                                    tRel 0])
                                                (tApp (tRel 9)
                                                   [tRel 3;
                                                    tApp
                                                      (tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["Datatypes"; "Init"; "Coq"],
                                                      "list");
                                                      inductive_ind := 0
                                                      |} 1 [])
                                                      [
                                                      tApp
                                                      (tInd
                                                      {|
                                                      inductive_mind :=
                                                      (MPfile
                                                      ["BasicAst"; "Common";
                                                      "MetaCoq"], "context_decl");
                                                      inductive_ind := 0
                                                      |} [])
                                                      [tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") []];
                                                      tApp
                                                      (tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "E" 7, "vdef") [])
                                                      [tRel 6; tRel 5; tRel 4];
                                                      tRel 2];
                                                    tApp
                                                      (tConstruct
                                                      {|
                                                      inductive_mind :=
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "ET" 9, "ctx_inst");
                                                      inductive_ind := 0
                                                      |} 2 [])
                                                      [
                                                      tRel 12;
                                                      tRel 11;
                                                      tRel 10;
                                                      tRel 6;
                                                      tRel 5;
                                                      tRel 4;
                                                      tRel 3;
                                                      tRel 2;
                                                      tRel 1]]))))))))
                           (tProd
                              {|
                                binder_name := nNamed "l";
                                binder_relevance := Relevant
                              |}
                              (tApp
                                 (tInd
                                    {|
                                      inductive_mind :=
                                        (MPfile ["Datatypes"; "Init"; "Coq"],
                                         "list");
                                      inductive_ind := 0
                                    |} [])
                                 [tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common";
                                        "QuotationOf"; "ToTemplate"; "Quotation";
                                        "MetaCoq"] "T" 6, "term") []])
                              (tProd
                                 {|
                                   binder_name := nNamed "c";
                                   binder_relevance := Relevant
                                 |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common";
                                        "QuotationOf"; "ToTemplate"; "Quotation";
                                        "MetaCoq"] "E" 7, "context") [])
                                 (tProd
                                    {|
                                      binder_name := nNamed "c0";
                                      binder_relevance := Relevant
                                    |}
                                    (tApp
                                       (tInd
                                          {|
                                            inductive_mind :=
                                              (MPbound
                                                 ["Sig"; "EnvironmentTyping";
                                                  "Common"; "QuotationOf";
                                                  "ToTemplate"; "Quotation";
                                                  "MetaCoq"] "ET" 9, "ctx_inst");
                                            inductive_ind := 0
                                          |} [])
                                       [tRel 8; tRel 7; tRel 6; tRel 1; tRel 0])
                                    (tApp (tRel 6) [tRel 2; tRel 1; tRel 0]))))))))));
       tConst
         (MPbound
            ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
             "Quotation"; "MetaCoq"] "ET" 9, "ctx_inst_rect") []]))).
unquoting
(@quotation_of
   (forall (Σ : E.global_env_ext) (Γ : E.context) (inst : list T.term)
      (Δ : E.context)
      (args : list
                (E.global_env_ext ->
                 E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u1}))
      (P : E.global_env_ext ->
           E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u2}),
    (∑
       P' : E.global_env_ext ->
            E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u0},
       ET.ctx_inst P' Σ Γ inst Δ) ->
    (forall t T : T.term,
     @All
       (E.global_env_ext ->
        E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u1})
       (fun
          P' : E.global_env_ext ->
               E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u1} =>
        P' Σ Γ t T) args -> P Σ Γ t T) ->
    @All
      (E.global_env_ext ->
       E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u3})
      (fun
         P' : E.global_env_ext ->
              E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u3} =>
       ET.ctx_inst P' Σ Γ inst Δ) args -> ET.ctx_inst P Σ Γ inst Δ)
   ET.ctx_inst_impl_gen)
(tApp
   (tConst (MPfile ["Init"; "ToTemplate"; "Quotation"; "MetaCoq"], "quotation_of")
      [])
   [tProd {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
      (tConst
         (MPbound
            ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
             "Quotation"; "MetaCoq"] "E" 7, "global_env_ext") [])
      (tProd {| binder_name := nNamed "Γ"; binder_relevance := Relevant |}
         (tConst
            (MPbound
               ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                "Quotation"; "MetaCoq"] "E" 7, "context") [])
         (tProd {| binder_name := nNamed "inst"; binder_relevance := Relevant |}
            (tApp
               (tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                    inductive_ind := 0
                  |} [])
               [tConst
                  (MPbound
                     ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                      "ToTemplate"; "Quotation"; "MetaCoq"] "T" 6, "term") []])
            (tProd {| binder_name := nNamed "Δ"; binder_relevance := Relevant |}
               (tConst
                  (MPbound
                     ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                      "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context") [])
               (tProd
                  {| binder_name := nNamed "args"; binder_relevance := Relevant |}
                  (tApp
                     (tInd
                        {|
                          inductive_mind :=
                            (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                          inductive_ind := 0
                        |} [])
                     [tProd
                        {|
                          binder_name := nNamed "x"; binder_relevance := Relevant
                        |}
                        (tConst
                           (MPbound
                              ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                               "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                            "global_env_ext") [])
                        (tProd
                           {|
                             binder_name := nNamed "x0";
                             binder_relevance := Relevant
                           |}
                           (tConst
                              (MPbound
                                 ["Sig"; "EnvironmentTyping"; "Common";
                                  "QuotationOf"; "ToTemplate"; "Quotation";
                                  "MetaCoq"] "E" 7, "context") [])
                           (tProd
                              {|
                                binder_name := nNamed "x1";
                                binder_relevance := Relevant
                              |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common";
                                     "QuotationOf"; "ToTemplate"; "Quotation";
                                     "MetaCoq"] "T" 6, "term") [])
                              (tProd
                                 {|
                                   binder_name := nNamed "x2";
                                   binder_relevance := Relevant
                                 |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common";
                                        "QuotationOf"; "ToTemplate"; "Quotation";
                                        "MetaCoq"] "T" 6, "term") [])
                                 (tSort
                                    (Universe.of_levels
                                       (@inr PropLevel.t Level.t
                                          (Level.Level
                                             "MetaCoq.Common.EnvironmentTyping.896")))))))])
                  (tProd
                     {| binder_name := nNamed "P"; binder_relevance := Relevant |}
                     (tProd
                        {|
                          binder_name := nNamed "x"; binder_relevance := Relevant
                        |}
                        (tConst
                           (MPbound
                              ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                               "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                            "global_env_ext") [])
                        (tProd
                           {|
                             binder_name := nNamed "x0";
                             binder_relevance := Relevant
                           |}
                           (tConst
                              (MPbound
                                 ["Sig"; "EnvironmentTyping"; "Common";
                                  "QuotationOf"; "ToTemplate"; "Quotation";
                                  "MetaCoq"] "E" 7, "context") [])
                           (tProd
                              {|
                                binder_name := nNamed "x1";
                                binder_relevance := Relevant
                              |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common";
                                     "QuotationOf"; "ToTemplate"; "Quotation";
                                     "MetaCoq"] "T" 6, "term") [])
                              (tProd
                                 {|
                                   binder_name := nNamed "x2";
                                   binder_relevance := Relevant
                                 |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common";
                                        "QuotationOf"; "ToTemplate"; "Quotation";
                                        "MetaCoq"] "T" 6, "term") [])
                                 (tSort
                                    (Universe.of_levels
                                       (@inr PropLevel.t Level.t
                                          (Level.Level
                                             "MetaCoq.Common.EnvironmentTyping.907"))))))))
                     (tProd
                        {| binder_name := nAnon; binder_relevance := Relevant |}
                        (tApp
                           (tInd
                              {|
                                inductive_mind :=
                                  (MPfile ["Specif"; "Init"; "Coq"], "sigT");
                                inductive_ind := 0
                              |} [])
                           [tProd
                              {|
                                binder_name := nNamed "Σ";
                                binder_relevance := Relevant
                              |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common";
                                     "QuotationOf"; "ToTemplate"; "Quotation";
                                     "MetaCoq"] "E" 7, "global_env_ext") [])
                              (tProd
                                 {|
                                   binder_name := nNamed "Γ";
                                   binder_relevance := Relevant
                                 |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common";
                                        "QuotationOf"; "ToTemplate"; "Quotation";
                                        "MetaCoq"] "E" 7, "context") [])
                                 (tProd
                                    {|
                                      binder_name := nAnon;
                                      binder_relevance := Relevant
                                    |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common";
                                           "QuotationOf"; "ToTemplate";
                                           "Quotation"; "MetaCoq"] "T" 6, "term")
                                       [])
                                    (tProd
                                       {|
                                         binder_name := nAnon;
                                         binder_relevance := Relevant
                                       |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common";
                                              "QuotationOf"; "ToTemplate";
                                              "Quotation"; "MetaCoq"] "T" 6, "term")
                                          [])
                                       (tSort
                                          (Universe.of_levels
                                             (@inr PropLevel.t Level.t
                                                (Level.Level
                                                   "MetaCoq.Common.EnvironmentTyping.883")))))));
                            tLambda
                              {|
                                binder_name := nNamed "P'";
                                binder_relevance := Relevant
                              |}
                              (tProd
                                 {|
                                   binder_name := nNamed "Σ";
                                   binder_relevance := Relevant
                                 |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common";
                                        "QuotationOf"; "ToTemplate"; "Quotation";
                                        "MetaCoq"] "E" 7, "global_env_ext") [])
                                 (tProd
                                    {|
                                      binder_name := nNamed "Γ";
                                      binder_relevance := Relevant
                                    |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common";
                                           "QuotationOf"; "ToTemplate";
                                           "Quotation"; "MetaCoq"] "E" 7, "context")
                                       [])
                                    (tProd
                                       {|
                                         binder_name := nAnon;
                                         binder_relevance := Relevant
                                       |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common";
                                              "QuotationOf"; "ToTemplate";
                                              "Quotation"; "MetaCoq"] "T" 6, "term")
                                          [])
                                       (tProd
                                          {|
                                            binder_name := nAnon;
                                            binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping";
                                                 "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation";
                                                 "MetaCoq"] "T" 6, "term") [])
                                          (tSort
                                             (Universe.of_levels
                                                (@inr PropLevel.t Level.t
                                                   (Level.Level
                                                      "MetaCoq.Common.EnvironmentTyping.883"))))))))
                              (tApp
                                 (tInd
                                    {|
                                      inductive_mind :=
                                        (MPbound
                                           ["Sig"; "EnvironmentTyping"; "Common";
                                            "QuotationOf"; "ToTemplate";
                                            "Quotation"; "MetaCoq"] "ET" 9,
                                         "ctx_inst");
                                      inductive_ind := 0
                                    |} []) [tRel 0; tRel 6; tRel 5; tRel 4; tRel 3])])
                        (tProd
                           {| binder_name := nAnon; binder_relevance := Relevant |}
                           (tProd
                              {|
                                binder_name := nNamed "t";
                                binder_relevance := Relevant
                              |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common";
                                     "QuotationOf"; "ToTemplate"; "Quotation";
                                     "MetaCoq"] "T" 6, "term") [])
                              (tProd
                                 {|
                                   binder_name := nNamed "T";
                                   binder_relevance := Relevant
                                 |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common";
                                        "QuotationOf"; "ToTemplate"; "Quotation";
                                        "MetaCoq"] "T" 6, "term") [])
                                 (tProd
                                    {|
                                      binder_name := nAnon;
                                      binder_relevance := Relevant
                                    |}
                                    (tApp
                                       (tInd
                                          {|
                                            inductive_mind :=
                                              (MPfile
                                                 ["All_Forall"; "Utils"; "MetaCoq"],
                                               "All");
                                            inductive_ind := 0
                                          |} [])
                                       [tProd
                                          {|
                                            binder_name := nNamed "x";
                                            binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping";
                                                 "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation";
                                                 "MetaCoq"] "E" 7, "global_env_ext")
                                             [])
                                          (tProd
                                             {|
                                               binder_name := nNamed "x0";
                                               binder_relevance := Relevant
                                             |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping";
                                                    "Common"; "QuotationOf";
                                                    "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "E" 7, "context") [])
                                             (tProd
                                                {|
                                                  binder_name := nNamed "x1";
                                                  binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      [
                                                      "Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [])
                                                (tProd
                                                   {|
                                                     binder_name := nNamed "x2";
                                                     binder_relevance := Relevant
                                                   |}
                                                   (tConst
                                                      (
                                                      MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [])
                                                   (tSort
                                                      (Universe.of_levels
                                                      (@inr PropLevel.t Level.t
                                                      (Level.Level
                                                      "MetaCoq.Common.EnvironmentTyping.896")))))));
                                        tLambda
                                          {|
                                            binder_name := nNamed "P'";
                                            binder_relevance := Relevant
                                          |}
                                          (tProd
                                             {|
                                               binder_name := nNamed "x";
                                               binder_relevance := Relevant
                                             |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping";
                                                    "Common"; "QuotationOf";
                                                    "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "E" 7,
                                                 "global_env_ext") [])
                                             (tProd
                                                {|
                                                  binder_name := nNamed "x0";
                                                  binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      [
                                                      "Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "E" 7, "context")
                                                   [])
                                                (tProd
                                                   {|
                                                     binder_name := nNamed "x1";
                                                     binder_relevance := Relevant
                                                   |}
                                                   (tConst
                                                      (
                                                      MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [])
                                                   (tProd
                                                      {|
                                                      binder_name := nNamed "x2";
                                                      binder_relevance := Relevant
                                                      |}
                                                      (tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [])
                                                      (tSort
                                                      (Universe.of_levels
                                                      (@inr PropLevel.t Level.t
                                                      (Level.Level
                                                      "MetaCoq.Common.EnvironmentTyping.896"))))))))
                                          (tApp (tRel 0)
                                             [tRel 9; tRel 8; tRel 2; tRel 1]);
                                        tRel 4])
                                    (tApp (tRel 4) [tRel 9; tRel 8; tRel 2; tRel 1]))))
                           (tProd
                              {|
                                binder_name := nAnon; binder_relevance := Relevant
                              |}
                              (tApp
                                 (tInd
                                    {|
                                      inductive_mind :=
                                        (MPfile ["All_Forall"; "Utils"; "MetaCoq"],
                                         "All");
                                      inductive_ind := 0
                                    |} [])
                                 [tProd
                                    {|
                                      binder_name := nNamed "Σ";
                                      binder_relevance := Relevant
                                    |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common";
                                           "QuotationOf"; "ToTemplate";
                                           "Quotation"; "MetaCoq"] "E" 7,
                                        "global_env_ext") [])
                                    (tProd
                                       {|
                                         binder_name := nNamed "Γ";
                                         binder_relevance := Relevant
                                       |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common";
                                              "QuotationOf"; "ToTemplate";
                                              "Quotation"; "MetaCoq"] "E" 7,
                                           "context") [])
                                       (tProd
                                          {|
                                            binder_name := nAnon;
                                            binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping";
                                                 "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation";
                                                 "MetaCoq"] "T" 6, "term") [])
                                          (tProd
                                             {|
                                               binder_name := nAnon;
                                               binder_relevance := Relevant
                                             |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping";
                                                    "Common"; "QuotationOf";
                                                    "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "T" 6, "term") [])
                                             (tSort
                                                (Universe.of_levels
                                                   (@inr PropLevel.t Level.t
                                                      (Level.Level
                                                      "MetaCoq.Common.EnvironmentTyping.908")))))));
                                  tLambda
                                    {|
                                      binder_name := nNamed "P'";
                                      binder_relevance := Relevant
                                    |}
                                    (tProd
                                       {|
                                         binder_name := nNamed "Σ";
                                         binder_relevance := Relevant
                                       |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common";
                                              "QuotationOf"; "ToTemplate";
                                              "Quotation"; "MetaCoq"] "E" 7,
                                           "global_env_ext") [])
                                       (tProd
                                          {|
                                            binder_name := nNamed "Γ";
                                            binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping";
                                                 "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation";
                                                 "MetaCoq"] "E" 7, "context") [])
                                          (tProd
                                             {|
                                               binder_name := nAnon;
                                               binder_relevance := Relevant
                                             |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping";
                                                    "Common"; "QuotationOf";
                                                    "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "T" 6, "term") [])
                                             (tProd
                                                {|
                                                  binder_name := nAnon;
                                                  binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      [
                                                      "Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [])
                                                (tSort
                                                   (Universe.of_levels
                                                      (@inr PropLevel.t Level.t
                                                      (Level.Level
                                                      "MetaCoq.Common.EnvironmentTyping.908"))))))))
                                    (tApp
                                       (tInd
                                          {|
                                            inductive_mind :=
                                              (MPbound
                                                 ["Sig"; "EnvironmentTyping";
                                                  "Common"; "QuotationOf";
                                                  "ToTemplate"; "Quotation";
                                                  "MetaCoq"] "ET" 9, "ctx_inst");
                                            inductive_ind := 0
                                          |} [])
                                       [tRel 0; tRel 8; tRel 7; tRel 6; tRel 5]);
                                  tRel 3])
                              (tApp
                                 (tInd
                                    {|
                                      inductive_mind :=
                                        (MPbound
                                           ["Sig"; "EnvironmentTyping"; "Common";
                                            "QuotationOf"; "ToTemplate";
                                            "Quotation"; "MetaCoq"] "ET" 9,
                                         "ctx_inst");
                                      inductive_ind := 0
                                    |} []) [tRel 3; tRel 8; tRel 7; tRel 6; tRel 5])))))))));
    tConst
      (MPbound
         ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
          "Quotation"; "MetaCoq"] "ET" 9, "ctx_inst_impl_gen") []])
(Universe.of_levels
   (@inr PropLevel.t Level.t
      (Level.Level
         "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159")))
(tmUnquoteTyped@{option_instance.u0 tmRetypeRelaxOnlyType'.u2}
   Type@{WithTemplate.tmRetypeAroundMetaCoqBug853.u3}
   (tApp
      (tConst
         (MPfile ["Init"; "ToTemplate"; "Quotation"; "MetaCoq"], "quotation_of") [])
      [tProd {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
         (tConst
            (MPbound
               ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                "Quotation"; "MetaCoq"] "E" 7, "global_env_ext") [])
         (tProd {| binder_name := nNamed "Γ"; binder_relevance := Relevant |}
            (tConst
               (MPbound
                  ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                   "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context") [])
            (tProd {| binder_name := nNamed "inst"; binder_relevance := Relevant |}
               (tApp
                  (tInd
                     {|
                       inductive_mind :=
                         (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                       inductive_ind := 0
                     |} [])
                  [tConst
                     (MPbound
                        ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                         "ToTemplate"; "Quotation"; "MetaCoq"] "T" 6, "term") []])
               (tProd {| binder_name := nNamed "Δ"; binder_relevance := Relevant |}
                  (tConst
                     (MPbound
                        ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                         "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context") [])
                  (tProd
                     {|
                       binder_name := nNamed "args"; binder_relevance := Relevant
                     |}
                     (tApp
                        (tInd
                           {|
                             inductive_mind :=
                               (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                             inductive_ind := 0
                           |} [])
                        [tProd
                           {|
                             binder_name := nNamed "x";
                             binder_relevance := Relevant
                           |}
                           (tConst
                              (MPbound
                                 ["Sig"; "EnvironmentTyping"; "Common";
                                  "QuotationOf"; "ToTemplate"; "Quotation";
                                  "MetaCoq"] "E" 7, "global_env_ext") [])
                           (tProd
                              {|
                                binder_name := nNamed "x0";
                                binder_relevance := Relevant
                              |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common";
                                     "QuotationOf"; "ToTemplate"; "Quotation";
                                     "MetaCoq"] "E" 7, "context") [])
                              (tProd
                                 {|
                                   binder_name := nNamed "x1";
                                   binder_relevance := Relevant
                                 |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common";
                                        "QuotationOf"; "ToTemplate"; "Quotation";
                                        "MetaCoq"] "T" 6, "term") [])
                                 (tProd
                                    {|
                                      binder_name := nNamed "x2";
                                      binder_relevance := Relevant
                                    |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common";
                                           "QuotationOf"; "ToTemplate";
                                           "Quotation"; "MetaCoq"] "T" 6, "term")
                                       [])
                                    (tSort
                                       (Universe.lType
                                          {|
                                            t_set :=
                                              {|
                                                LevelExprSet.this :=
                                                  [(Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                    0)];
                                                LevelExprSet.is_ok :=
                                                  LevelExprSet.Raw.singleton_ok
                                                    (Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                     0)
                                              |};
                                            t_ne := @eq_refl bool false
                                          |})))))])
                     (tProd
                        {|
                          binder_name := nNamed "P"; binder_relevance := Relevant
                        |}
                        (tProd
                           {|
                             binder_name := nNamed "x";
                             binder_relevance := Relevant
                           |}
                           (tConst
                              (MPbound
                                 ["Sig"; "EnvironmentTyping"; "Common";
                                  "QuotationOf"; "ToTemplate"; "Quotation";
                                  "MetaCoq"] "E" 7, "global_env_ext") [])
                           (tProd
                              {|
                                binder_name := nNamed "x0";
                                binder_relevance := Relevant
                              |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common";
                                     "QuotationOf"; "ToTemplate"; "Quotation";
                                     "MetaCoq"] "E" 7, "context") [])
                              (tProd
                                 {|
                                   binder_name := nNamed "x1";
                                   binder_relevance := Relevant
                                 |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common";
                                        "QuotationOf"; "ToTemplate"; "Quotation";
                                        "MetaCoq"] "T" 6, "term") [])
                                 (tProd
                                    {|
                                      binder_name := nNamed "x2";
                                      binder_relevance := Relevant
                                    |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common";
                                           "QuotationOf"; "ToTemplate";
                                           "Quotation"; "MetaCoq"] "T" 6, "term")
                                       [])
                                    (tSort
                                       (Universe.lType
                                          {|
                                            t_set :=
                                              {|
                                                LevelExprSet.this :=
                                                  [(Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                    0)];
                                                LevelExprSet.is_ok :=
                                                  LevelExprSet.Raw.singleton_ok
                                                    (Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                     0)
                                              |};
                                            t_ne := @eq_refl bool false
                                          |}))))))
                        (tProd
                           {| binder_name := nAnon; binder_relevance := Relevant |}
                           (tApp
                              (tInd
                                 {|
                                   inductive_mind :=
                                     (MPfile ["Specif"; "Init"; "Coq"], "sigT");
                                   inductive_ind := 0
                                 |} [])
                              [tProd
                                 {|
                                   binder_name := nNamed "Σ";
                                   binder_relevance := Relevant
                                 |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common";
                                        "QuotationOf"; "ToTemplate"; "Quotation";
                                        "MetaCoq"] "E" 7, "global_env_ext") [])
                                 (tProd
                                    {|
                                      binder_name := nNamed "Γ";
                                      binder_relevance := Relevant
                                    |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common";
                                           "QuotationOf"; "ToTemplate";
                                           "Quotation"; "MetaCoq"] "E" 7, "context")
                                       [])
                                    (tProd
                                       {|
                                         binder_name := nAnon;
                                         binder_relevance := Relevant
                                       |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common";
                                              "QuotationOf"; "ToTemplate";
                                              "Quotation"; "MetaCoq"] "T" 6, "term")
                                          [])
                                       (tProd
                                          {|
                                            binder_name := nAnon;
                                            binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping";
                                                 "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation";
                                                 "MetaCoq"] "T" 6, "term") [])
                                          (tSort
                                             (Universe.lType
                                                {|
                                                  t_set :=
                                                    {|
                                                      LevelExprSet.this :=
                                                      [(Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                      0)];
                                                      LevelExprSet.is_ok :=
                                                      LevelExprSet.Raw.singleton_ok
                                                      (Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                      0)
                                                    |};
                                                  t_ne := @eq_refl bool false
                                                |})))));
                               tLambda
                                 {|
                                   binder_name := nNamed "P'";
                                   binder_relevance := Relevant
                                 |}
                                 (tProd
                                    {|
                                      binder_name := nNamed "Σ";
                                      binder_relevance := Relevant
                                    |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common";
                                           "QuotationOf"; "ToTemplate";
                                           "Quotation"; "MetaCoq"] "E" 7,
                                        "global_env_ext") [])
                                    (tProd
                                       {|
                                         binder_name := nNamed "Γ";
                                         binder_relevance := Relevant
                                       |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common";
                                              "QuotationOf"; "ToTemplate";
                                              "Quotation"; "MetaCoq"] "E" 7,
                                           "context") [])
                                       (tProd
                                          {|
                                            binder_name := nAnon;
                                            binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping";
                                                 "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation";
                                                 "MetaCoq"] "T" 6, "term") [])
                                          (tProd
                                             {|
                                               binder_name := nAnon;
                                               binder_relevance := Relevant
                                             |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping";
                                                    "Common"; "QuotationOf";
                                                    "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "T" 6, "term") [])
                                             (tSort
                                                (Universe.lType
                                                   {|
                                                     t_set :=
                                                      {|
                                                      LevelExprSet.this :=
                                                      [(Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                      0)];
                                                      LevelExprSet.is_ok :=
                                                      LevelExprSet.Raw.singleton_ok
                                                      (Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                      0)
                                                      |};
                                                     t_ne := @eq_refl bool false
                                                   |}))))))
                                 (tApp
                                    (tInd
                                       {|
                                         inductive_mind :=
                                           (MPbound
                                              ["Sig"; "EnvironmentTyping";
                                               "Common"; "QuotationOf";
                                               "ToTemplate"; "Quotation"; "MetaCoq"]
                                              "ET" 9, "ctx_inst");
                                         inductive_ind := 0
                                       |} [])
                                    [tRel 0; tRel 6; tRel 5; tRel 4; tRel 3])])
                           (tProd
                              {|
                                binder_name := nAnon; binder_relevance := Relevant
                              |}
                              (tProd
                                 {|
                                   binder_name := nNamed "t";
                                   binder_relevance := Relevant
                                 |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common";
                                        "QuotationOf"; "ToTemplate"; "Quotation";
                                        "MetaCoq"] "T" 6, "term") [])
                                 (tProd
                                    {|
                                      binder_name := nNamed "T";
                                      binder_relevance := Relevant
                                    |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common";
                                           "QuotationOf"; "ToTemplate";
                                           "Quotation"; "MetaCoq"] "T" 6, "term")
                                       [])
                                    (tProd
                                       {|
                                         binder_name := nAnon;
                                         binder_relevance := Relevant
                                       |}
                                       (tApp
                                          (tInd
                                             {|
                                               inductive_mind :=
                                                 (MPfile
                                                    ["All_Forall"; "Utils";
                                                     "MetaCoq"], "All");
                                               inductive_ind := 0
                                             |} [])
                                          [tProd
                                             {|
                                               binder_name := nNamed "x";
                                               binder_relevance := Relevant
                                             |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping";
                                                    "Common"; "QuotationOf";
                                                    "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "E" 7,
                                                 "global_env_ext") [])
                                             (tProd
                                                {|
                                                  binder_name := nNamed "x0";
                                                  binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      [
                                                      "Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "E" 7, "context")
                                                   [])
                                                (tProd
                                                   {|
                                                     binder_name := nNamed "x1";
                                                     binder_relevance := Relevant
                                                   |}
                                                   (tConst
                                                      (
                                                      MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [])
                                                   (tProd
                                                      {|
                                                      binder_name := nNamed "x2";
                                                      binder_relevance := Relevant
                                                      |}
                                                      (tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [])
                                                      (tSort
                                                      (Universe.lType
                                                      {|
                                                      t_set :=
                                                      {|
                                                      LevelExprSet.this :=
                                                      [(Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                      0)];
                                                      LevelExprSet.is_ok :=
                                                      LevelExprSet.Raw.singleton_ok
                                                      (Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                      0)
                                                      |};
                                                      t_ne := @eq_refl bool false
                                                      |})))));
                                           tLambda
                                             {|
                                               binder_name := nNamed "P'";
                                               binder_relevance := Relevant
                                             |}
                                             (tProd
                                                {|
                                                  binder_name := nNamed "x";
                                                  binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      [
                                                      "Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "E" 7,
                                                    "global_env_ext") [])
                                                (tProd
                                                   {|
                                                     binder_name := nNamed "x0";
                                                     binder_relevance := Relevant
                                                   |}
                                                   (tConst
                                                      (
                                                      MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "E" 7, "context")
                                                      [])
                                                   (tProd
                                                      {|
                                                      binder_name := nNamed "x1";
                                                      binder_relevance := Relevant
                                                      |}
                                                      (tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [])
                                                      (tProd
                                                      {|
                                                      binder_name := nNamed "x2";
                                                      binder_relevance := Relevant
                                                      |}
                                                      (tConst
                                                      (MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [])
                                                      (tSort
                                                      (Universe.lType
                                                      {|
                                                      t_set :=
                                                      {|
                                                      LevelExprSet.this :=
                                                      [(Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                      0)];
                                                      LevelExprSet.is_ok :=
                                                      LevelExprSet.Raw.singleton_ok
                                                      (Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                      0)
                                                      |};
                                                      t_ne := @eq_refl bool false
                                                      |}))))))
                                             (tApp (tRel 0)
                                                [tRel 9; tRel 8; tRel 2; tRel 1]);
                                           tRel 4])
                                       (tApp (tRel 4)
                                          [tRel 9; tRel 8; tRel 2; tRel 1]))))
                              (tProd
                                 {|
                                   binder_name := nAnon;
                                   binder_relevance := Relevant
                                 |}
                                 (tApp
                                    (tInd
                                       {|
                                         inductive_mind :=
                                           (MPfile
                                              ["All_Forall"; "Utils"; "MetaCoq"],
                                            "All");
                                         inductive_ind := 0
                                       |} [])
                                    [tProd
                                       {|
                                         binder_name := nNamed "Σ";
                                         binder_relevance := Relevant
                                       |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common";
                                              "QuotationOf"; "ToTemplate";
                                              "Quotation"; "MetaCoq"] "E" 7,
                                           "global_env_ext") [])
                                       (tProd
                                          {|
                                            binder_name := nNamed "Γ";
                                            binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping";
                                                 "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation";
                                                 "MetaCoq"] "E" 7, "context") [])
                                          (tProd
                                             {|
                                               binder_name := nAnon;
                                               binder_relevance := Relevant
                                             |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping";
                                                    "Common"; "QuotationOf";
                                                    "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "T" 6, "term") [])
                                             (tProd
                                                {|
                                                  binder_name := nAnon;
                                                  binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      [
                                                      "Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [])
                                                (tSort
                                                   (Universe.lType
                                                      {|
                                                      t_set :=
                                                      {|
                                                      LevelExprSet.this :=
                                                      [(Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                      0)];
                                                      LevelExprSet.is_ok :=
                                                      LevelExprSet.Raw.singleton_ok
                                                      (Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                      0)
                                                      |};
                                                      t_ne := @eq_refl bool false
                                                      |})))));
                                     tLambda
                                       {|
                                         binder_name := nNamed "P'";
                                         binder_relevance := Relevant
                                       |}
                                       (tProd
                                          {|
                                            binder_name := nNamed "Σ";
                                            binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping";
                                                 "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation";
                                                 "MetaCoq"] "E" 7, "global_env_ext")
                                             [])
                                          (tProd
                                             {|
                                               binder_name := nNamed "Γ";
                                               binder_relevance := Relevant
                                             |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping";
                                                    "Common"; "QuotationOf";
                                                    "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "E" 7, "context") [])
                                             (tProd
                                                {|
                                                  binder_name := nAnon;
                                                  binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      [
                                                      "Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [])
                                                (tProd
                                                   {|
                                                     binder_name := nAnon;
                                                     binder_relevance := Relevant
                                                   |}
                                                   (tConst
                                                      (
                                                      MPbound
                                                      ["Sig"; "EnvironmentTyping";
                                                      "Common"; "QuotationOf";
                                                      "ToTemplate"; "Quotation";
                                                      "MetaCoq"] "T" 6, "term") [])
                                                   (tSort
                                                      (Universe.lType
                                                      {|
                                                      t_set :=
                                                      {|
                                                      LevelExprSet.this :=
                                                      [(Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                      0)];
                                                      LevelExprSet.is_ok :=
                                                      LevelExprSet.Raw.singleton_ok
                                                      (Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.159",
                                                      0)
                                                      |};
                                                      t_ne := @eq_refl bool false
                                                      |}))))))
                                       (tApp
                                          (tInd
                                             {|
                                               inductive_mind :=
                                                 (MPbound
                                                    ["Sig"; "EnvironmentTyping";
                                                     "Common"; "QuotationOf";
                                                     "ToTemplate"; "Quotation";
                                                     "MetaCoq"] "ET" 9, "ctx_inst");
                                               inductive_ind := 0
                                             |} [])
                                          [tRel 0; tRel 8; tRel 7; tRel 6; tRel 5]);
                                     tRel 3])
                                 (tApp
                                    (tInd
                                       {|
                                         inductive_mind :=
                                           (MPbound
                                              ["Sig"; "EnvironmentTyping";
                                               "Common"; "QuotationOf";
                                               "ToTemplate"; "Quotation"; "MetaCoq"]
                                              "ET" 9, "ctx_inst");
                                         inductive_ind := 0
                                       |} [])
                                    [tRel 3; tRel 8; tRel 7; tRel 6; tRel 5])))))))));
       tConst
         (MPbound
            ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
             "Quotation"; "MetaCoq"] "ET" 9, "ctx_inst_impl_gen") []])).
  MetaCoq Run (tmUnquoteTyped@{option_instance.u0 tmRetypeRelaxOnlyType'.u2}
   Type@{WithTemplate.tmRetypeAroundMetaCoqBug853.u3}
   (tApp (tConst (MPfile ["Init"; "ToTemplate"; "Quotation"; "MetaCoq"], "quotation_of") [])
      [tProd {| binder_name := nNamed "typing"; binder_relevance := Relevant |}
         (tProd {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
            (tConst
               (MPbound
                  ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate"; "Quotation";
                   "MetaCoq"] "E" 7, "global_env_ext") [])
            (tProd {| binder_name := nNamed "Γ"; binder_relevance := Relevant |}
               (tConst
                  (MPbound
                     ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate"; "Quotation";
                      "MetaCoq"] "E" 7, "context") [])
               (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                  (tConst
                     (MPbound
                        ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                         "Quotation"; "MetaCoq"] "T" 149, "term") [])
                  (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                     (tConst
                        (MPbound
                           ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                            "Quotation"; "MetaCoq"] "T" 149, "term") [])
                     (tSort
                        (Universe.lType
                           {|
                             t_set :=
                               {|
                                 LevelExprSet.this :=
                                   [(Level.Level
                                       "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                     0)];
                                 LevelExprSet.is_ok :=
                                   LevelExprSet.Raw.singleton_ok
                                     (Level.Level
                                        "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                      0)
                               |};
                             t_ne := @eq_refl bool false
                           |}))))))
         (tProd {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
            (tConst
               (MPbound
                  ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate"; "Quotation";
                   "MetaCoq"] "E" 7, "global_env_ext") [])
            (tProd {| binder_name := nNamed "Γ"; binder_relevance := Relevant |}
               (tConst
                  (MPbound
                     ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate"; "Quotation";
                      "MetaCoq"] "E" 7, "context") [])
               (tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
                  (tProd {| binder_name := nNamed "l"; binder_relevance := Relevant |}
                     (tApp
                        (tInd
                           {|
                             inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                             inductive_ind := 0
                           |} [])
                        [tConst
                           (MPbound
                              ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                               "Quotation"; "MetaCoq"] "T" 149, "term") []])
                     (tProd {| binder_name := nNamed "c"; binder_relevance := Relevant |}
                        (tConst
                           (MPbound
                              ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                               "Quotation"; "MetaCoq"] "E" 7, "context") [])
                        (tProd {| binder_name := nNamed "c"; binder_relevance := Relevant |}
                           (tApp
                              (tInd
                                 {|
                                   inductive_mind :=
                                     (MPbound
                                        ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                         "ToTemplate"; "Quotation"; "MetaCoq"] "ET" 152, "ctx_inst");
                                   inductive_ind := 0
                                 |} []) [tRel 4; tRel 3; tRel 2; tRel 1; tRel 0])
                           (tSort
                              (Universe.lType
                                 {|
                                   t_set :=
                                     {|
                                       LevelExprSet.this :=
                                         [(Level.Level
                                             "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                           0)];
                                       LevelExprSet.is_ok :=
                                         LevelExprSet.Raw.singleton_ok
                                           (Level.Level
                                              "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                            0)
                                     |};
                                   t_ne := @eq_refl bool false
                                 |})))))
                  (tProd {| binder_name := nNamed "f"; binder_relevance := Relevant |}
                     (tApp (tRel 0)
                        [tApp
                           (tConstruct
                              {|
                                inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                                inductive_ind := 0
                              |} 0 [])
                           [tConst
                              (MPbound
                                 ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                                  "Quotation"; "MetaCoq"] "T" 149, "term") []];
                         tApp
                           (tConstruct
                              {|
                                inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                                inductive_ind := 0
                              |} 0 [])
                           [tApp
                              (tInd
                                 {|
                                   inductive_mind :=
                                     (MPfile ["BasicAst"; "Common"; "MetaCoq"], "context_decl");
                                   inductive_ind := 0
                                 |} [])
                              [tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                     "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") []]];
                         tApp
                           (tConstruct
                              {|
                                inductive_mind :=
                                  (MPbound
                                     ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                      "ToTemplate"; "Quotation"; "MetaCoq"] "ET" 152, "ctx_inst");
                                inductive_ind := 0
                              |} 0 []) [tRel 3; tRel 2; tRel 1]])
                     (tProd {| binder_name := nNamed "f0"; binder_relevance := Relevant |}
                        (tProd {| binder_name := nNamed "na"; binder_relevance := Relevant |}
                           (tConst (MPfile ["BasicAst"; "Common"; "MetaCoq"], "aname") [])
                           (tProd {| binder_name := nNamed "t"; binder_relevance := Relevant |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                     "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                              (tProd {| binder_name := nNamed "i"; binder_relevance := Relevant |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                        "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                                 (tProd
                                    {| binder_name := nNamed "inst"; binder_relevance := Relevant |}
                                    (tApp
                                       (tInd
                                          {|
                                            inductive_mind :=
                                              (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                                            inductive_ind := 0
                                          |} [])
                                       [tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                              "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term")
                                          []])
                                    (tProd
                                       {| binder_name := nNamed "Δ"; binder_relevance := Relevant |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                              "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context")
                                          [])
                                       (tProd
                                          {|
                                            binder_name := nNamed "t"; binder_relevance := Relevant
                                          |} (tApp (tRel 9) [tRel 8; tRel 7; tRel 2; tRel 3])
                                          (tProd
                                             {|
                                               binder_name := nNamed "c"; binder_relevance := Relevant
                                             |}
                                             (tApp
                                                (tInd
                                                   {|
                                                     inductive_mind :=
                                                       (MPbound
                                                          ["Sig"; "EnvironmentTyping"; "Common";
                                                           "QuotationOf"; "ToTemplate"; "Quotation";
                                                           "MetaCoq"] "ET" 152, "ctx_inst");
                                                     inductive_ind := 0
                                                   |} [])
                                                [tRel 10; tRel 9; tRel 8;
                                                 tRel 2;
                                                 tApp
                                                   (tConst
                                                      (MPbound
                                                         ["Sig"; "EnvironmentTyping"; "Common";
                                                          "QuotationOf"; "ToTemplate"; "Quotation";
                                                          "MetaCoq"] "E" 7, "subst_telescope") [])
                                                   [tApp
                                                      (tConstruct
                                                         {|
                                                           inductive_mind :=
                                                             (MPfile ["Datatypes"; "Init"; "Coq"],
                                                              "list");
                                                           inductive_ind := 0
                                                         |} 1 [])
                                                      [tConst
                                                         (MPbound
                                                            ["Sig"; "EnvironmentTyping"; "Common";
                                                             "QuotationOf"; "ToTemplate"; "Quotation";
                                                             "MetaCoq"] "T" 149, "term") [];
                                                       tRel 3;
                                                       tApp
                                                         (tConstruct
                                                            {|
                                                              inductive_mind :=
                                                                (MPfile ["Datatypes"; "Init"; "Coq"],
                                                                 "list");
                                                              inductive_ind := 0
                                                            |} 0 [])
                                                         [tConst
                                                            (MPbound
                                                               ["Sig"; "EnvironmentTyping"; "Common";
                                                                "QuotationOf"; "ToTemplate";
                                                                "Quotation"; "MetaCoq"] "T" 149,
                                                             "term") []]];
                                                    tConstruct
                                                      {|
                                                        inductive_mind :=
                                                          (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                                                        inductive_ind := 0
                                                      |} 0 []; tRel 1]])
                                             (tProd
                                                {|
                                                  binder_name := nAnon; binder_relevance := Relevant
                                                |}
                                                (tApp (tRel 8)
                                                   [tRel 3;
                                                    tApp
                                                      (tConst
                                                         (MPbound
                                                            ["Sig"; "EnvironmentTyping"; "Common";
                                                             "QuotationOf"; "ToTemplate"; "Quotation";
                                                             "MetaCoq"] "E" 7, "subst_telescope") [])
                                                      [tApp
                                                         (tConstruct
                                                            {|
                                                              inductive_mind :=
                                                                (MPfile ["Datatypes"; "Init"; "Coq"],
                                                                 "list");
                                                              inductive_ind := 0
                                                            |} 1 [])
                                                         [tConst
                                                            (MPbound
                                                               ["Sig"; "EnvironmentTyping"; "Common";
                                                                "QuotationOf"; "ToTemplate";
                                                                "Quotation"; "MetaCoq"] "T" 149,
                                                             "term") []; tRel 4;
                                                          tApp
                                                            (tConstruct
                                                               {|
                                                                 inductive_mind :=
                                                                   (MPfile
                                                                      ["Datatypes"; "Init"; "Coq"],
                                                                    "list");
                                                                 inductive_ind := 0
                                                               |} 0 [])
                                                            [tConst
                                                               (MPbound
                                                                  ["Sig"; "EnvironmentTyping";
                                                                   "Common"; "QuotationOf";
                                                                   "ToTemplate"; "Quotation";
                                                                   "MetaCoq"] "T" 149, "term") []]];
                                                       tConstruct
                                                         {|
                                                           inductive_mind :=
                                                             (MPfile ["Datatypes"; "Init"; "Coq"],
                                                              "nat");
                                                           inductive_ind := 0
                                                         |} 0 []; tRel 2];
                                                    tRel 0])
                                                (tApp (tRel 9)
                                                   [tApp
                                                      (tConstruct
                                                         {|
                                                           inductive_mind :=
                                                             (MPfile ["Datatypes"; "Init"; "Coq"],
                                                              "list");
                                                           inductive_ind := 0
                                                         |} 1 [])
                                                      [tConst
                                                         (MPbound
                                                            ["Sig"; "EnvironmentTyping"; "Common";
                                                             "QuotationOf"; "ToTemplate"; "Quotation";
                                                             "MetaCoq"] "T" 149, "term") [];
                                                       tRel 5; tRel 4];
                                                    tApp
                                                      (tConstruct
                                                         {|
                                                           inductive_mind :=
                                                             (MPfile ["Datatypes"; "Init"; "Coq"],
                                                              "list");
                                                           inductive_ind := 0
                                                         |} 1 [])
                                                      [tApp
                                                         (tInd
                                                            {|
                                                              inductive_mind :=
                                                                (MPfile
                                                                   ["BasicAst"; "Common"; "MetaCoq"],
                                                                 "context_decl");
                                                              inductive_ind := 0
                                                            |} [])
                                                         [tConst
                                                            (MPbound
                                                               ["Sig"; "EnvironmentTyping"; "Common";
                                                                "QuotationOf"; "ToTemplate";
                                                                "Quotation"; "MetaCoq"] "T" 149,
                                                             "term") []];
                                                       tApp
                                                         (tConst
                                                            (MPbound
                                                               ["Sig"; "EnvironmentTyping"; "Common";
                                                                "QuotationOf"; "ToTemplate";
                                                                "Quotation"; "MetaCoq"] "E" 7,
                                                             "vass") []) [
                                                         tRel 7; tRel 6];
                                                       tRel 3];
                                                    tApp
                                                      (tConstruct
                                                         {|
                                                           inductive_mind :=
                                                             (MPbound
                                                                ["Sig"; "EnvironmentTyping"; "Common";
                                                                 "QuotationOf"; "ToTemplate";
                                                                 "Quotation"; "MetaCoq"] "ET" 152,
                                                              "ctx_inst");
                                                           inductive_ind := 0
                                                         |} 1 [])
                                                      [tRel 12; tRel 11; tRel 10;
                                                       tRel 7; tRel 6; tRel 5;
                                                       tRel 4; tRel 3; tRel 2;
                                                       tRel 1]])))))))))
                        (tProd {| binder_name := nNamed "f1"; binder_relevance := Relevant |}
                           (tProd {| binder_name := nNamed "na"; binder_relevance := Relevant |}
                              (tConst (MPfile ["BasicAst"; "Common"; "MetaCoq"], "aname") [])
                              (tProd {| binder_name := nNamed "b"; binder_relevance := Relevant |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                        "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                                 (tProd {| binder_name := nNamed "t"; binder_relevance := Relevant |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                           "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                                    (tProd
                                       {|
                                         binder_name := nNamed "inst"; binder_relevance := Relevant
                                       |}
                                       (tApp
                                          (tInd
                                             {|
                                               inductive_mind :=
                                                 (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                                               inductive_ind := 0
                                             |} [])
                                          [tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term")
                                             []])
                                       (tProd
                                          {|
                                            binder_name := nNamed "Δ"; binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                                              "context") [])
                                          (tProd
                                             {|
                                               binder_name := nNamed "c"; binder_relevance := Relevant
                                             |}
                                             (tApp
                                                (tInd
                                                   {|
                                                     inductive_mind :=
                                                       (MPbound
                                                          ["Sig"; "EnvironmentTyping"; "Common";
                                                           "QuotationOf"; "ToTemplate"; "Quotation";
                                                           "MetaCoq"] "ET" 152, "ctx_inst");
                                                     inductive_ind := 0
                                                   |} [])
                                                [tRel 10; tRel 9; tRel 8;
                                                 tRel 1;
                                                 tApp
                                                   (tConst
                                                      (MPbound
                                                         ["Sig"; "EnvironmentTyping"; "Common";
                                                          "QuotationOf"; "ToTemplate"; "Quotation";
                                                          "MetaCoq"] "E" 7, "subst_telescope") [])
                                                   [tApp
                                                      (tConstruct
                                                         {|
                                                           inductive_mind :=
                                                             (MPfile ["Datatypes"; "Init"; "Coq"],
                                                              "list");
                                                           inductive_ind := 0
                                                         |} 1 [])
                                                      [tConst
                                                         (MPbound
                                                            ["Sig"; "EnvironmentTyping"; "Common";
                                                             "QuotationOf"; "ToTemplate"; "Quotation";
                                                             "MetaCoq"] "T" 149, "term") [];
                                                       tRel 3;
                                                       tApp
                                                         (tConstruct
                                                            {|
                                                              inductive_mind :=
                                                                (MPfile ["Datatypes"; "Init"; "Coq"],
                                                                 "list");
                                                              inductive_ind := 0
                                                            |} 0 [])
                                                         [tConst
                                                            (MPbound
                                                               ["Sig"; "EnvironmentTyping"; "Common";
                                                                "QuotationOf"; "ToTemplate";
                                                                "Quotation"; "MetaCoq"] "T" 149,
                                                             "term") []]];
                                                    tConstruct
                                                      {|
                                                        inductive_mind :=
                                                          (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                                                        inductive_ind := 0
                                                      |} 0 []; tRel 0]])
                                             (tProd
                                                {|
                                                  binder_name := nAnon; binder_relevance := Relevant
                                                |}
                                                (tApp (tRel 8)
                                                   [tRel 2;
                                                    tApp
                                                      (tConst
                                                         (MPbound
                                                            ["Sig"; "EnvironmentTyping"; "Common";
                                                             "QuotationOf"; "ToTemplate"; "Quotation";
                                                             "MetaCoq"] "E" 7, "subst_telescope") [])
                                                      [tApp
                                                         (tConstruct
                                                            {|
                                                              inductive_mind :=
                                                                (MPfile ["Datatypes"; "Init"; "Coq"],
                                                                 "list");
                                                              inductive_ind := 0
                                                            |} 1 [])
                                                         [tConst
                                                            (MPbound
                                                               ["Sig"; "EnvironmentTyping"; "Common";
                                                                "QuotationOf"; "ToTemplate";
                                                                "Quotation"; "MetaCoq"] "T" 149,
                                                             "term") []; tRel 4;
                                                          tApp
                                                            (tConstruct
                                                               {|
                                                                 inductive_mind :=
                                                                   (MPfile
                                                                      ["Datatypes"; "Init"; "Coq"],
                                                                    "list");
                                                                 inductive_ind := 0
                                                               |} 0 [])
                                                            [tConst
                                                               (MPbound
                                                                  ["Sig"; "EnvironmentTyping";
                                                                   "Common"; "QuotationOf";
                                                                   "ToTemplate"; "Quotation";
                                                                   "MetaCoq"] "T" 149, "term") []]];
                                                       tConstruct
                                                         {|
                                                           inductive_mind :=
                                                             (MPfile ["Datatypes"; "Init"; "Coq"],
                                                              "nat");
                                                           inductive_ind := 0
                                                         |} 0 []; tRel 1];
                                                    tRel 0])
                                                (tApp (tRel 9)
                                                   [tRel 3;
                                                    tApp
                                                      (tConstruct
                                                         {|
                                                           inductive_mind :=
                                                             (MPfile ["Datatypes"; "Init"; "Coq"],
                                                              "list");
                                                           inductive_ind := 0
                                                         |} 1 [])
                                                      [tApp
                                                         (tInd
                                                            {|
                                                              inductive_mind :=
                                                                (MPfile
                                                                   ["BasicAst"; "Common"; "MetaCoq"],
                                                                 "context_decl");
                                                              inductive_ind := 0
                                                            |} [])
                                                         [tConst
                                                            (MPbound
                                                               ["Sig"; "EnvironmentTyping"; "Common";
                                                                "QuotationOf"; "ToTemplate";
                                                                "Quotation"; "MetaCoq"] "T" 149,
                                                             "term") []];
                                                       tApp
                                                         (tConst
                                                            (MPbound
                                                               ["Sig"; "EnvironmentTyping"; "Common";
                                                                "QuotationOf"; "ToTemplate";
                                                                "Quotation"; "MetaCoq"] "E" 7,
                                                             "vdef") []) [
                                                         tRel 6; tRel 5; tRel 4];
                                                       tRel 2];
                                                    tApp
                                                      (tConstruct
                                                         {|
                                                           inductive_mind :=
                                                             (MPbound
                                                                ["Sig"; "EnvironmentTyping"; "Common";
                                                                 "QuotationOf"; "ToTemplate";
                                                                 "Quotation"; "MetaCoq"] "ET" 152,
                                                              "ctx_inst");
                                                           inductive_ind := 0
                                                         |} 2 [])
                                                      [tRel 12; tRel 11; tRel 10;
                                                       tRel 6; tRel 5; tRel 4;
                                                       tRel 3; tRel 2; tRel 1]]))))))))
                           (tProd {| binder_name := nNamed "l"; binder_relevance := Relevant |}
                              (tApp
                                 (tInd
                                    {|
                                      inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                                      inductive_ind := 0
                                    |} [])
                                 [tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                        "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") []])
                              (tProd {| binder_name := nNamed "c"; binder_relevance := Relevant |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                        "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context") [])
                                 (tProd {| binder_name := nNamed "c0"; binder_relevance := Relevant |}
                                    (tApp
                                       (tInd
                                          {|
                                            inductive_mind :=
                                              (MPbound
                                                 ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                                  "ToTemplate"; "Quotation"; "MetaCoq"] "ET" 152,
                                               "ctx_inst");
                                            inductive_ind := 0
                                          |} []) [tRel 8; tRel 7; tRel 6; tRel 1; tRel 0])
                                    (tApp (tRel 6) [tRel 2; tRel 1; tRel 0]))))))))));
       tConst
         (MPbound
            ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate"; "Quotation"; "MetaCoq"]
            "ET" 152, "ctx_inst_rect") []])).
unquoting
(@quotation_of
   (forall (Σ : E.global_env_ext) (Γ : E.context) (inst : list T.term) (Δ : E.context)
      (args : list
                (E.global_env_ext -> E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u1}))
      (P : E.global_env_ext -> E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u2}),
    (∑ P' : E.global_env_ext -> E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u0},
       ET.ctx_inst P' Σ Γ inst Δ) ->
    (forall t T : T.term,
     @All (E.global_env_ext -> E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u1})
       (fun P' : E.global_env_ext -> E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u1}
        => P' Σ Γ t T) args -> P Σ Γ t T) ->
    @All (E.global_env_ext -> E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u3})
      (fun P' : E.global_env_ext -> E.context -> T.term -> T.term -> Type@{ET.ctx_inst_impl_gen.u3} =>
       ET.ctx_inst P' Σ Γ inst Δ) args -> ET.ctx_inst P Σ Γ inst Δ) ET.ctx_inst_impl_gen)
(tApp (tConst (MPfile ["Init"; "ToTemplate"; "Quotation"; "MetaCoq"], "quotation_of") [])
   [tProd {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
      (tConst
         (MPbound
            ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate"; "Quotation"; "MetaCoq"]
            "E" 7, "global_env_ext") [])
      (tProd {| binder_name := nNamed "Γ"; binder_relevance := Relevant |}
         (tConst
            (MPbound
               ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate"; "Quotation";
                "MetaCoq"] "E" 7, "context") [])
         (tProd {| binder_name := nNamed "inst"; binder_relevance := Relevant |}
            (tApp
               (tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                    inductive_ind := 0
                  |} [])
               [tConst
                  (MPbound
                     ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate"; "Quotation";
                      "MetaCoq"] "T" 149, "term") []])
            (tProd {| binder_name := nNamed "Δ"; binder_relevance := Relevant |}
               (tConst
                  (MPbound
                     ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate"; "Quotation";
                      "MetaCoq"] "E" 7, "context") [])
               (tProd {| binder_name := nNamed "args"; binder_relevance := Relevant |}
                  (tApp
                     (tInd
                        {|
                          inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                          inductive_ind := 0
                        |} [])
                     [tProd {| binder_name := nNamed "x"; binder_relevance := Relevant |}
                        (tConst
                           (MPbound
                              ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                               "Quotation"; "MetaCoq"] "E" 7, "global_env_ext") [])
                        (tProd {| binder_name := nNamed "x0"; binder_relevance := Relevant |}
                           (tConst
                              (MPbound
                                 ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                                  "Quotation"; "MetaCoq"] "E" 7, "context") [])
                           (tProd {| binder_name := nNamed "x1"; binder_relevance := Relevant |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                     "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                              (tProd {| binder_name := nNamed "x2"; binder_relevance := Relevant |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                        "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                                 (tSort
                                    (Universe.of_levels
                                       (@inr PropLevel.t Level.t
                                          (Level.Level "MetaCoq.Common.EnvironmentTyping.896")))))))])
                  (tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
                     (tProd {| binder_name := nNamed "x"; binder_relevance := Relevant |}
                        (tConst
                           (MPbound
                              ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                               "Quotation"; "MetaCoq"] "E" 7, "global_env_ext") [])
                        (tProd {| binder_name := nNamed "x0"; binder_relevance := Relevant |}
                           (tConst
                              (MPbound
                                 ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                                  "Quotation"; "MetaCoq"] "E" 7, "context") [])
                           (tProd {| binder_name := nNamed "x1"; binder_relevance := Relevant |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                     "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                              (tProd {| binder_name := nNamed "x2"; binder_relevance := Relevant |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                        "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                                 (tSort
                                    (Universe.of_levels
                                       (@inr PropLevel.t Level.t
                                          (Level.Level "MetaCoq.Common.EnvironmentTyping.907"))))))))
                     (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                        (tApp
                           (tInd
                              {|
                                inductive_mind := (MPfile ["Specif"; "Init"; "Coq"], "sigT");
                                inductive_ind := 0
                              |} [])
                           [tProd {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                     "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "global_env_ext")
                                 [])
                              (tProd {| binder_name := nNamed "Γ"; binder_relevance := Relevant |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                        "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context") [])
                                 (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                           "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                                    (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                              "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term")
                                          [])
                                       (tSort
                                          (Universe.of_levels
                                             (@inr PropLevel.t Level.t
                                                (Level.Level "MetaCoq.Common.EnvironmentTyping.883")))))));
                            tLambda {| binder_name := nNamed "P'"; binder_relevance := Relevant |}
                              (tProd {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                        "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                                     "global_env_ext") [])
                                 (tProd {| binder_name := nNamed "Γ"; binder_relevance := Relevant |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                           "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context")
                                       [])
                                    (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                              "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term")
                                          [])
                                       (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term")
                                             [])
                                          (tSort
                                             (Universe.of_levels
                                                (@inr PropLevel.t Level.t
                                                   (Level.Level "MetaCoq.Common.EnvironmentTyping.883"))))))))
                              (tApp
                                 (tInd
                                    {|
                                      inductive_mind :=
                                        (MPbound
                                           ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                            "ToTemplate"; "Quotation"; "MetaCoq"] "ET" 152, "ctx_inst");
                                      inductive_ind := 0
                                    |} []) [tRel 0; tRel 6; tRel 5; tRel 4; tRel 3])])
                        (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                           (tProd {| binder_name := nNamed "t"; binder_relevance := Relevant |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                     "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                              (tProd {| binder_name := nNamed "T"; binder_relevance := Relevant |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                        "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                                 (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                    (tApp
                                       (tInd
                                          {|
                                            inductive_mind :=
                                              (MPfile ["All_Forall"; "Utils"; "MetaCoq"], "All");
                                            inductive_ind := 0
                                          |} [])
                                       [tProd
                                          {|
                                            binder_name := nNamed "x"; binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                                              "global_env_ext") [])
                                          (tProd
                                             {|
                                               binder_name := nNamed "x0";
                                               binder_relevance := Relevant
                                             |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping"; "Common";
                                                    "QuotationOf"; "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "E" 7, "context") [])
                                             (tProd
                                                {|
                                                  binder_name := nNamed "x1";
                                                  binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      ["Sig"; "EnvironmentTyping"; "Common";
                                                       "QuotationOf"; "ToTemplate"; "Quotation";
                                                       "MetaCoq"] "T" 149, "term") [])
                                                (tProd
                                                   {|
                                                     binder_name := nNamed "x2";
                                                     binder_relevance := Relevant
                                                   |}
                                                   (tConst
                                                      (MPbound
                                                         ["Sig"; "EnvironmentTyping"; "Common";
                                                          "QuotationOf"; "ToTemplate"; "Quotation";
                                                          "MetaCoq"] "T" 149, "term") [])
                                                   (tSort
                                                      (Universe.of_levels
                                                         (@inr PropLevel.t Level.t
                                                            (Level.Level
                                                               "MetaCoq.Common.EnvironmentTyping.896")))))));
                                        tLambda
                                          {|
                                            binder_name := nNamed "P'"; binder_relevance := Relevant
                                          |}
                                          (tProd
                                             {|
                                               binder_name := nNamed "x"; binder_relevance := Relevant
                                             |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping"; "Common";
                                                    "QuotationOf"; "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "E" 7, "global_env_ext") [])
                                             (tProd
                                                {|
                                                  binder_name := nNamed "x0";
                                                  binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      ["Sig"; "EnvironmentTyping"; "Common";
                                                       "QuotationOf"; "ToTemplate"; "Quotation";
                                                       "MetaCoq"] "E" 7, "context") [])
                                                (tProd
                                                   {|
                                                     binder_name := nNamed "x1";
                                                     binder_relevance := Relevant
                                                   |}
                                                   (tConst
                                                      (MPbound
                                                         ["Sig"; "EnvironmentTyping"; "Common";
                                                          "QuotationOf"; "ToTemplate"; "Quotation";
                                                          "MetaCoq"] "T" 149, "term") [])
                                                   (tProd
                                                      {|
                                                        binder_name := nNamed "x2";
                                                        binder_relevance := Relevant
                                                      |}
                                                      (tConst
                                                         (MPbound
                                                            ["Sig"; "EnvironmentTyping"; "Common";
                                                             "QuotationOf"; "ToTemplate"; "Quotation";
                                                             "MetaCoq"] "T" 149, "term") [])
                                                      (tSort
                                                         (Universe.of_levels
                                                            (@inr PropLevel.t Level.t
                                                               (Level.Level
                                                                  "MetaCoq.Common.EnvironmentTyping.896"))))))))
                                          (tApp (tRel 0) [tRel 9; tRel 8; tRel 2; tRel 1]);
                                        tRel 4]) (tApp (tRel 4) [tRel 9; tRel 8; tRel 2; tRel 1]))))
                           (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                              (tApp
                                 (tInd
                                    {|
                                      inductive_mind :=
                                        (MPfile ["All_Forall"; "Utils"; "MetaCoq"], "All");
                                      inductive_ind := 0
                                    |} [])
                                 [tProd {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                           "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                                        "global_env_ext") [])
                                    (tProd
                                       {| binder_name := nNamed "Γ"; binder_relevance := Relevant |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                              "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context")
                                          [])
                                       (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term")
                                             [])
                                          (tProd
                                             {| binder_name := nAnon; binder_relevance := Relevant |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping"; "Common";
                                                    "QuotationOf"; "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "T" 149, "term") [])
                                             (tSort
                                                (Universe.of_levels
                                                   (@inr PropLevel.t Level.t
                                                      (Level.Level
                                                         "MetaCoq.Common.EnvironmentTyping.908")))))));
                                  tLambda
                                    {| binder_name := nNamed "P'"; binder_relevance := Relevant |}
                                    (tProd
                                       {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                              "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                                           "global_env_ext") [])
                                       (tProd
                                          {|
                                            binder_name := nNamed "Γ"; binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                                              "context") [])
                                          (tProd
                                             {| binder_name := nAnon; binder_relevance := Relevant |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping"; "Common";
                                                    "QuotationOf"; "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "T" 149, "term") [])
                                             (tProd
                                                {|
                                                  binder_name := nAnon; binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      ["Sig"; "EnvironmentTyping"; "Common";
                                                       "QuotationOf"; "ToTemplate"; "Quotation";
                                                       "MetaCoq"] "T" 149, "term") [])
                                                (tSort
                                                   (Universe.of_levels
                                                      (@inr PropLevel.t Level.t
                                                         (Level.Level
                                                            "MetaCoq.Common.EnvironmentTyping.908"))))))))
                                    (tApp
                                       (tInd
                                          {|
                                            inductive_mind :=
                                              (MPbound
                                                 ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                                  "ToTemplate"; "Quotation"; "MetaCoq"] "ET" 152,
                                               "ctx_inst");
                                            inductive_ind := 0
                                          |} []) [tRel 0; tRel 8; tRel 7; tRel 6; tRel 5]);
                                  tRel 3])
                              (tApp
                                 (tInd
                                    {|
                                      inductive_mind :=
                                        (MPbound
                                           ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                            "ToTemplate"; "Quotation"; "MetaCoq"] "ET" 152, "ctx_inst");
                                      inductive_ind := 0
                                    |} []) [tRel 3; tRel 8; tRel 7; tRel 6; tRel 5])))))))));
    tConst
      (MPbound
         ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate"; "Quotation"; "MetaCoq"]
         "ET" 152, "ctx_inst_impl_gen") []])
(Universe.of_levels
   (@inr PropLevel.t Level.t
      (Level.Level "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380")))
(tmUnquoteTyped@{option_instance.u0 tmRetypeRelaxOnlyType'.u2}
   Type@{WithTemplate.tmRetypeAroundMetaCoqBug853.u3}
   (tApp (tConst (MPfile ["Init"; "ToTemplate"; "Quotation"; "MetaCoq"], "quotation_of") [])
      [tProd {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
         (tConst
            (MPbound
               ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate"; "Quotation";
                "MetaCoq"] "E" 7, "global_env_ext") [])
         (tProd {| binder_name := nNamed "Γ"; binder_relevance := Relevant |}
            (tConst
               (MPbound
                  ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate"; "Quotation";
                   "MetaCoq"] "E" 7, "context") [])
            (tProd {| binder_name := nNamed "inst"; binder_relevance := Relevant |}
               (tApp
                  (tInd
                     {|
                       inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                       inductive_ind := 0
                     |} [])
                  [tConst
                     (MPbound
                        ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                         "Quotation"; "MetaCoq"] "T" 149, "term") []])
               (tProd {| binder_name := nNamed "Δ"; binder_relevance := Relevant |}
                  (tConst
                     (MPbound
                        ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                         "Quotation"; "MetaCoq"] "E" 7, "context") [])
                  (tProd {| binder_name := nNamed "args"; binder_relevance := Relevant |}
                     (tApp
                        (tInd
                           {|
                             inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
                             inductive_ind := 0
                           |} [])
                        [tProd {| binder_name := nNamed "x"; binder_relevance := Relevant |}
                           (tConst
                              (MPbound
                                 ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                                  "Quotation"; "MetaCoq"] "E" 7, "global_env_ext") [])
                           (tProd {| binder_name := nNamed "x0"; binder_relevance := Relevant |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                     "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context") [])
                              (tProd {| binder_name := nNamed "x1"; binder_relevance := Relevant |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                        "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                                 (tProd {| binder_name := nNamed "x2"; binder_relevance := Relevant |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                           "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                                    (tSort
                                       (Universe.lType
                                          {|
                                            t_set :=
                                              {|
                                                LevelExprSet.this :=
                                                  [(Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                    0)];
                                                LevelExprSet.is_ok :=
                                                  LevelExprSet.Raw.singleton_ok
                                                    (Level.Level
                                                       "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                     0)
                                              |};
                                            t_ne := @eq_refl bool false
                                          |})))))])
                     (tProd {| binder_name := nNamed "P"; binder_relevance := Relevant |}
                        (tProd {| binder_name := nNamed "x"; binder_relevance := Relevant |}
                           (tConst
                              (MPbound
                                 ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate";
                                  "Quotation"; "MetaCoq"] "E" 7, "global_env_ext") [])
                           (tProd {| binder_name := nNamed "x0"; binder_relevance := Relevant |}
                              (tConst
                                 (MPbound
                                    ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                     "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context") [])
                              (tProd {| binder_name := nNamed "x1"; binder_relevance := Relevant |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                        "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                                 (tProd {| binder_name := nNamed "x2"; binder_relevance := Relevant |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                           "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                                    (tSort
                                       (Universe.lType
                                          {|
                                            t_set :=
                                              {|
                                                LevelExprSet.this :=
                                                  [(Level.Level
                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                    0)];
                                                LevelExprSet.is_ok :=
                                                  LevelExprSet.Raw.singleton_ok
                                                    (Level.Level
                                                       "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                     0)
                                              |};
                                            t_ne := @eq_refl bool false
                                          |}))))))
                        (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                           (tApp
                              (tInd
                                 {|
                                   inductive_mind := (MPfile ["Specif"; "Init"; "Coq"], "sigT");
                                   inductive_ind := 0
                                 |} [])
                              [tProd {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                        "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                                     "global_env_ext") [])
                                 (tProd {| binder_name := nNamed "Γ"; binder_relevance := Relevant |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                           "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context")
                                       [])
                                    (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                              "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term")
                                          [])
                                       (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term")
                                             [])
                                          (tSort
                                             (Universe.lType
                                                {|
                                                  t_set :=
                                                    {|
                                                      LevelExprSet.this :=
                                                        [(Level.Level
                                                            "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                          0)];
                                                      LevelExprSet.is_ok :=
                                                        LevelExprSet.Raw.singleton_ok
                                                          (Level.Level
                                                             "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                           0)
                                                    |};
                                                  t_ne := @eq_refl bool false
                                                |})))));
                               tLambda {| binder_name := nNamed "P'"; binder_relevance := Relevant |}
                                 (tProd {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                           "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                                        "global_env_ext") [])
                                    (tProd
                                       {| binder_name := nNamed "Γ"; binder_relevance := Relevant |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                              "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7, "context")
                                          [])
                                       (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term")
                                             [])
                                          (tProd
                                             {| binder_name := nAnon; binder_relevance := Relevant |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping"; "Common";
                                                    "QuotationOf"; "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "T" 149, "term") [])
                                             (tSort
                                                (Universe.lType
                                                   {|
                                                     t_set :=
                                                       {|
                                                         LevelExprSet.this :=
                                                           [(Level.Level
                                                               "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                             0)];
                                                         LevelExprSet.is_ok :=
                                                           LevelExprSet.Raw.singleton_ok
                                                             (Level.Level
                                                                "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                              0)
                                                       |};
                                                     t_ne := @eq_refl bool false
                                                   |}))))))
                                 (tApp
                                    (tInd
                                       {|
                                         inductive_mind :=
                                           (MPbound
                                              ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                               "ToTemplate"; "Quotation"; "MetaCoq"] "ET" 152,
                                            "ctx_inst");
                                         inductive_ind := 0
                                       |} []) [tRel 0; tRel 6; tRel 5; tRel 4; tRel 3])])
                           (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                              (tProd {| binder_name := nNamed "t"; binder_relevance := Relevant |}
                                 (tConst
                                    (MPbound
                                       ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                        "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                                 (tProd {| binder_name := nNamed "T"; binder_relevance := Relevant |}
                                    (tConst
                                       (MPbound
                                          ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                           "ToTemplate"; "Quotation"; "MetaCoq"] "T" 149, "term") [])
                                    (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                       (tApp
                                          (tInd
                                             {|
                                               inductive_mind :=
                                                 (MPfile ["All_Forall"; "Utils"; "MetaCoq"], "All");
                                               inductive_ind := 0
                                             |} [])
                                          [tProd
                                             {|
                                               binder_name := nNamed "x"; binder_relevance := Relevant
                                             |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping"; "Common";
                                                    "QuotationOf"; "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "E" 7, "global_env_ext") [])
                                             (tProd
                                                {|
                                                  binder_name := nNamed "x0";
                                                  binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      ["Sig"; "EnvironmentTyping"; "Common";
                                                       "QuotationOf"; "ToTemplate"; "Quotation";
                                                       "MetaCoq"] "E" 7, "context") [])
                                                (tProd
                                                   {|
                                                     binder_name := nNamed "x1";
                                                     binder_relevance := Relevant
                                                   |}
                                                   (tConst
                                                      (MPbound
                                                         ["Sig"; "EnvironmentTyping"; "Common";
                                                          "QuotationOf"; "ToTemplate"; "Quotation";
                                                          "MetaCoq"] "T" 149, "term") [])
                                                   (tProd
                                                      {|
                                                        binder_name := nNamed "x2";
                                                        binder_relevance := Relevant
                                                      |}
                                                      (tConst
                                                         (MPbound
                                                            ["Sig"; "EnvironmentTyping"; "Common";
                                                             "QuotationOf"; "ToTemplate"; "Quotation";
                                                             "MetaCoq"] "T" 149, "term") [])
                                                      (tSort
                                                         (Universe.lType
                                                            {|
                                                              t_set :=
                                                                {|
                                                                  LevelExprSet.this :=
                                                                    [(Level.Level
                                                                        "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                                      0)];
                                                                  LevelExprSet.is_ok :=
                                                                    LevelExprSet.Raw.singleton_ok
                                                                      (Level.Level
                                                                         "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                                       0)
                                                                |};
                                                              t_ne := @eq_refl bool false
                                                            |})))));
                                           tLambda
                                             {|
                                               binder_name := nNamed "P'";
                                               binder_relevance := Relevant
                                             |}
                                             (tProd
                                                {|
                                                  binder_name := nNamed "x";
                                                  binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      ["Sig"; "EnvironmentTyping"; "Common";
                                                       "QuotationOf"; "ToTemplate"; "Quotation";
                                                       "MetaCoq"] "E" 7, "global_env_ext") [])
                                                (tProd
                                                   {|
                                                     binder_name := nNamed "x0";
                                                     binder_relevance := Relevant
                                                   |}
                                                   (tConst
                                                      (MPbound
                                                         ["Sig"; "EnvironmentTyping"; "Common";
                                                          "QuotationOf"; "ToTemplate"; "Quotation";
                                                          "MetaCoq"] "E" 7, "context") [])
                                                   (tProd
                                                      {|
                                                        binder_name := nNamed "x1";
                                                        binder_relevance := Relevant
                                                      |}
                                                      (tConst
                                                         (MPbound
                                                            ["Sig"; "EnvironmentTyping"; "Common";
                                                             "QuotationOf"; "ToTemplate"; "Quotation";
                                                             "MetaCoq"] "T" 149, "term") [])
                                                      (tProd
                                                         {|
                                                           binder_name := nNamed "x2";
                                                           binder_relevance := Relevant
                                                         |}
                                                         (tConst
                                                            (MPbound
                                                               ["Sig"; "EnvironmentTyping"; "Common";
                                                                "QuotationOf"; "ToTemplate";
                                                                "Quotation"; "MetaCoq"] "T" 149,
                                                             "term") [])
                                                         (tSort
                                                            (Universe.lType
                                                               {|
                                                                 t_set :=
                                                                   {|
                                                                     LevelExprSet.this :=
                                                                       [(Level.Level
                                                                         "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                                         0)];
                                                                     LevelExprSet.is_ok :=
                                                                       LevelExprSet.Raw.singleton_ok
                                                                         (
                                                                         Level.Level
                                                                         "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                                         0)
                                                                   |};
                                                                 t_ne := @eq_refl bool false
                                                               |}))))))
                                             (tApp (tRel 0) [tRel 9; tRel 8; tRel 2; tRel 1]);
                                           tRel 4]) (tApp (tRel 4) [tRel 9; tRel 8; tRel 2; tRel 1]))))
                              (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                                 (tApp
                                    (tInd
                                       {|
                                         inductive_mind :=
                                           (MPfile ["All_Forall"; "Utils"; "MetaCoq"], "All");
                                         inductive_ind := 0
                                       |} [])
                                    [tProd
                                       {| binder_name := nNamed "Σ"; binder_relevance := Relevant |}
                                       (tConst
                                          (MPbound
                                             ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                              "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                                           "global_env_ext") [])
                                       (tProd
                                          {|
                                            binder_name := nNamed "Γ"; binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                                              "context") [])
                                          (tProd
                                             {| binder_name := nAnon; binder_relevance := Relevant |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping"; "Common";
                                                    "QuotationOf"; "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "T" 149, "term") [])
                                             (tProd
                                                {|
                                                  binder_name := nAnon; binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      ["Sig"; "EnvironmentTyping"; "Common";
                                                       "QuotationOf"; "ToTemplate"; "Quotation";
                                                       "MetaCoq"] "T" 149, "term") [])
                                                (tSort
                                                   (Universe.lType
                                                      {|
                                                        t_set :=
                                                          {|
                                                            LevelExprSet.this :=
                                                              [(Level.Level
                                                                  "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                                0)];
                                                            LevelExprSet.is_ok :=
                                                              LevelExprSet.Raw.singleton_ok
                                                                (Level.Level
                                                                   "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                                 0)
                                                          |};
                                                        t_ne := @eq_refl bool false
                                                      |})))));
                                     tLambda
                                       {| binder_name := nNamed "P'"; binder_relevance := Relevant |}
                                       (tProd
                                          {|
                                            binder_name := nNamed "Σ"; binder_relevance := Relevant
                                          |}
                                          (tConst
                                             (MPbound
                                                ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                                 "ToTemplate"; "Quotation"; "MetaCoq"] "E" 7,
                                              "global_env_ext") [])
                                          (tProd
                                             {|
                                               binder_name := nNamed "Γ"; binder_relevance := Relevant
                                             |}
                                             (tConst
                                                (MPbound
                                                   ["Sig"; "EnvironmentTyping"; "Common";
                                                    "QuotationOf"; "ToTemplate"; "Quotation";
                                                    "MetaCoq"] "E" 7, "context") [])
                                             (tProd
                                                {|
                                                  binder_name := nAnon; binder_relevance := Relevant
                                                |}
                                                (tConst
                                                   (MPbound
                                                      ["Sig"; "EnvironmentTyping"; "Common";
                                                       "QuotationOf"; "ToTemplate"; "Quotation";
                                                       "MetaCoq"] "T" 149, "term") [])
                                                (tProd
                                                   {|
                                                     binder_name := nAnon;
                                                     binder_relevance := Relevant
                                                   |}
                                                   (tConst
                                                      (MPbound
                                                         ["Sig"; "EnvironmentTyping"; "Common";
                                                          "QuotationOf"; "ToTemplate"; "Quotation";
                                                          "MetaCoq"] "T" 149, "term") [])
                                                   (tSort
                                                      (Universe.lType
                                                         {|
                                                           t_set :=
                                                             {|
                                                               LevelExprSet.this :=
                                                                 [(Level.Level
                                                                     "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                                   0)];
                                                               LevelExprSet.is_ok :=
                                                                 LevelExprSet.Raw.singleton_ok
                                                                   (Level.Level
                                                                      "MetaCoq.Quotation.ToTemplate.QuotationOf.Common.EnvironmentTyping.Sig.17380",
                                                                    0)
                                                             |};
                                                           t_ne := @eq_refl bool false
                                                         |}))))))
                                       (tApp
                                          (tInd
                                             {|
                                               inductive_mind :=
                                                 (MPbound
                                                    ["Sig"; "EnvironmentTyping"; "Common";
                                                     "QuotationOf"; "ToTemplate"; "Quotation";
                                                     "MetaCoq"] "ET" 152, "ctx_inst");
                                               inductive_ind := 0
                                             |} []) [tRel 0; tRel 8; tRel 7; tRel 6; tRel 5]);
                                     tRel 3])
                                 (tApp
                                    (tInd
                                       {|
                                         inductive_mind :=
                                           (MPbound
                                              ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf";
                                               "ToTemplate"; "Quotation"; "MetaCoq"] "ET" 152,
                                            "ctx_inst");
                                         inductive_ind := 0
                                       |} []) [tRel 3; tRel 8; tRel 7; tRel 6; tRel 5])))))))));
       tConst
         (MPbound
            ["Sig"; "EnvironmentTyping"; "Common"; "QuotationOf"; "ToTemplate"; "Quotation"; "MetaCoq"]
            "ET" 152, "ctx_inst_impl_gen") []])).
  Fail MetaCoq Run bar.
  FIXME HERE
    lazymatch (eval cbv [v] in v) with
    | monad_utils.bind ?p ?q
      => clear v;
         run_template_program p (fun p' => let p' := constr:(List.flat_map (fun r => match r with ConstRef (_, s) => if ((s:IdentOT.t) == "ctx_inst_impl_gen"%bs) then r :: nil else nil | _ => nil end) p') in
                                           pose (q p') as v)
    end.
    vm_compute List.flat_map in v.
    lazymatch (eval cbv [v] in v) with
    | monad_utils.bind ?p ?q
      => clear v;
         run_template_program p (fun p' => pose (q p') as v)
    end.
    cbn -[tmDeclareQuotationOfConstants] in v.
    cbv [tmDeclareQuotationOfConstants] in v.
    cbv [tmMakeQuotationOfConstants_gen] in v.
    do 2 lazymatch (eval cbv [v] in v) with
    | monad_utils.bind ?p ?q
      => clear v;
         run_template_program p (fun p' => pose (q p') as v)
      end; cbv beta in v.
    exact v.
  Defined.
  MetaCoq Run foo.
    cbn in v.


    pose (List.flat_map (fun r => match r with ConstRef (_, s) => if ((s:IdentOT.t) == "ctx_inst_impl_gen"%bs) then r :: nil else nil | _ => nil end) l).
    compute in l0.
           (MPbound
              ("Sig"%bs
               :: "EnvironmentTyping"%bs
                  :: "Common"%bs
                     :: "QuotationOf"%bs
                        :: "ToTemplate"%bs :: "Quotation"%bs :: "MetaCoq"%bs :: @nil string)%list
              "ET"%bs 152, "ctx_inst_impl_gen"%bs)
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "ET").
End QuotationOfEnvTyping.
 *)

Module Type QuoteEnvTypingSig (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E) (Import ET : EnvTypingSig T E TU).

  #[export] Declare Instance quote_All_local_env {typing Γ} {qtyping : quotation_of typing} {quote_typing : forall Γ t T, ground_quotable (typing Γ t T)} : ground_quotable (@All_local_env typing Γ).
  #[export] Declare Instance quote_on_local_decl {P Γ d} {quoteP1 : forall b, d.(decl_body) = Some b -> ground_quotable (P Γ b (Typ d.(decl_type)))} {quoteP2 : d.(decl_body) = None -> ground_quotable (P Γ d.(decl_type) Sort)} : ground_quotable (@on_local_decl P Γ d).
  #[export] Declare Instance quote_lift_judgment {check infer_sort Σ Γ t T} {quote_check : forall T', T = Typ T' -> ground_quotable (check Σ Γ t T')} {quote_infer_sort : T = Sort -> ground_quotable (infer_sort Σ Γ t)} : ground_quotable (@lift_judgment check infer_sort Σ Γ t T).

  #[export] Declare Instance quote_All_local_env_over_gen
   {checking sorting cproperty sproperty Σ Γ H}
   {qchecking : quotation_of checking} {qsorting : quotation_of sorting} {qcproperty : quotation_of cproperty} {qsproperty : quotation_of sproperty}
   {quote_checking : forall Γ t T, ground_quotable (checking Σ Γ t T)} {quote_sorting : forall Γ T, ground_quotable (sorting Σ Γ T)} {quote_sproperty : forall Γ all t tu, ground_quotable (sproperty Σ Γ all t tu)} {quote_cproperty : forall Γ all b t tb, ground_quotable (cproperty Σ Γ all b t tb)}
    : ground_quotable (@All_local_env_over_gen checking sorting cproperty sproperty Σ Γ H).

  #[export] Declare Instance quote_All_local_env_over {typing property Σ Γ H}
   {qtyping : quotation_of typing} {qproperty : quotation_of property}
   {quote_typing : forall Γ t T, ground_quotable (typing Σ Γ t T)} {quote_property : forall Γ all b t tb, ground_quotable (property Σ Γ all b t tb)}
    : ground_quotable (@All_local_env_over typing property Σ Γ H).

  #[export] Declare Instance quote_All_local_env_over_sorting
   {checking sorting cproperty sproperty Σ Γ H}
   {qchecking : quotation_of checking} {qsorting : quotation_of sorting} {qcproperty : quotation_of cproperty} {qsproperty : quotation_of sproperty}
   {quote_checking : forall Γ t T, ground_quotable (checking Σ Γ t T)} {quote_sorting : forall Γ T U, ground_quotable (sorting Σ Γ T U)} {quote_sproperty : forall Γ all t tu U, ground_quotable (sproperty Σ Γ all t tu U)} {quote_cproperty : forall Γ all b t tb, ground_quotable (cproperty Σ Γ all b t tb)}
    : ground_quotable (@All_local_env_over_sorting checking sorting cproperty sproperty Σ Γ H).

  #[export] Declare Instance quote_ctx_inst {typing Σ Γ ctx inst}
   {qtyping : quotation_of typing}
   {quote_typing : forall i t, ground_quotable (typing Σ Γ i t)}
    : ground_quotable (@ctx_inst typing Σ Γ ctx inst).
End QuoteEnvTypingSig.

Module Type QuotationOfConversion (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU) (C : ConversionSig T E TU ET).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "C").
End QuotationOfConversion.

Module Type QuoteConversionSig (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E) (Import ET : EnvTypingSig T E TU) (Import C : ConversionSig T E TU ET).

  #[export] Declare Instance quote_All_decls_alpha_pb {pb P b b'} {qP : quotation_of P} {quoteP : forall pb t t', ground_quotable (P pb t t')}
    : ground_quotable (@All_decls_alpha_pb pb P b b').

  #[export] Declare Instance quote_cumul_pb_decls {cumul_gen pb Σ Γ Γ' x y}
   {qcumul_gen : quotation_of cumul_gen}
   {quote_cumul_gen : forall pb t t', ground_quotable (cumul_gen Σ Γ pb t t')}
    : ground_quotable (@cumul_pb_decls cumul_gen pb Σ Γ Γ' x y).

  #[export] Declare Instance quote_cumul_pb_context {cumul_gen pb Σ Γ Γ'}
   {qcumul_gen : quotation_of cumul_gen}
   {quote_cumul_gen : forall Γ pb t t', ground_quotable (cumul_gen Σ Γ pb t t')}
    : ground_quotable (@cumul_pb_context cumul_gen pb Σ Γ Γ').

  #[export] Declare Instance quote_cumul_ctx_rel {cumul_gen Σ Γ Δ Δ'}
   {qcumul_gen : quotation_of cumul_gen}
   {quote_cumul_gen : forall Γ pb t t', ground_quotable (cumul_gen Σ Γ pb t t')}
    : ground_quotable (@cumul_ctx_rel cumul_gen Σ Γ Δ Δ').
End QuoteConversionSig.

Module Type QuotationOfGlobalMaps (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU) (C : ConversionSig T E TU ET) (L : LookupSig T E) (GM : GlobalMapsSig T E TU ET C L).
  Set Printing All. Set Printing Universes.
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "GM").
End QuotationOfGlobalMaps.

Module QuoteGlobalMapsSig (Import T: Term) (Import E: EnvironmentSig T) (Import TU : TermUtils T E) (Import ET: EnvTypingSig T E TU) (Import C: ConversionSig T E TU ET) (Import L: LookupSig T E) (Import GM : GlobalMapsSig T E TU ET C L).

  Section GlobalMaps.
    Context {cf : config.checker_flags}
            {Pcmp: global_env_ext -> context -> conv_pb -> term -> term -> Type}
            {P : global_env_ext -> context -> term -> typ_or_sort -> Type}
            {qPcmp : quotation_of Pcmp} {qP : quotation_of P}
            {quotePcmp : forall Σ Γ pb t T, ground_quotable (Pcmp Σ Γ pb t T)}
            {quoteP : forall Σ Γ t T, ground_quotable (P Σ Γ t T)}.
FIXME
    #[export] Instance quote_on_context {P Σ ctx} {qP : quotation_of P} {quoteP :  : ground_quotable (@on_context P Σ ctx)
      := _.

    #[export] Instance qtype_local_ctx : quotation_of type_local_ctx := ltac:(cbv [type_local_ctx]; exact _).
    #[export] Instance qsorts_local_ctx : quotation_of sorts_local_ctx := ltac:(cbv [sorts_local_ctx]; exact _).
    #[export] Instance qunivs_ext_constraints : quotation_of univs_ext_constraints := ltac:(cbv [univs_ext_constraints]; exact _).
    #[export] Instance qsatisfiable_udecl : quotation_of satisfiable_udecl := ltac:(cbv [satisfiable_udecl]; exact _).
    #[export] Instance qvalid_on_mono_udecl : quotation_of valid_on_mono_udecl := ltac:(cbv [valid_on_mono_udecl]; exact _).
    #[export] Instance qsubst_instance_context : quotation_of subst_instance_context := ltac:(cbv [subst_instance_context]; exact _).
    #[export] Instance qarities_context : quotation_of arities_context := ltac:(cbv -[quotation_of]; exact _).
    #[export] Instance qind_arities : quotation_of ind_arities := ltac:(cbv -[quotation_of]; exact _).
    #[export] Instance qlift_level : quotation_of lift_level := ltac:(cbv [lift_level]; exact _).
    #[export] Instance qlift_constraint : quotation_of lift_constraint := ltac:(cbv [lift_constraint]; exact _).
    #[export] Instance qlift_constraints : quotation_of lift_constraints := ltac:(cbv [lift_constraints]; exact _).
    #[export] Instance qlift_instance : quotation_of lift_instance := ltac:(cbv [lift_instance]; exact _).
    #[export] Instance qvariance_cstrs : quotation_of variance_cstrs := ltac:(cbv [variance_cstrs]; exact _).
    #[export] Instance qlevel_var_instance : quotation_of level_var_instance := ltac:(cbv [level_var_instance]; exact _).
    #[export] Instance qvariance_universes : quotation_of variance_universes := ltac:(cbv [variance_universes]; exact _).
    #[export] Instance qcstr_respects_variance : quotation_of cstr_respects_variance := ltac:(cbv [cstr_respects_variance]; exact _).
    #[export] Instance qconstructor_univs : quotation_of constructor_univs := ltac:(cbv [constructor_univs]; exact _).
    #[export] Instance qind_respects_variance : quotation_of ind_respects_variance := ltac:(cbv [ind_respects_variance]; exact _).
    #[export] Instance qon_global_univs : quotation_of on_global_univs := ltac:(cbv [on_global_univs]; exact _).
    #[export] Instance qon_udecl : quotation_of on_udecl := ltac:(cbv [on_udecl]; exact _).
    #[export] Instance qon_global_env : quotation_of (@on_global_env) := ltac:(cbv [on_global_env retroknowledge]; exact _).

    #[export] Instance quote_constructor_univs : ground_quotable constructor_univs := _.

    #[export] Instance quote_type_local_ctx {Σ Γ Δ u} : ground_quotable (@type_local_ctx P Σ Γ Δ u)
      := ltac:(induction Δ; cbn [type_local_ctx]; exact _).

    #[export] Instance quote_sorts_local_ctx {Σ Γ Δ us} : ground_quotable (@sorts_local_ctx P Σ Γ Δ us)
      := ltac:(revert us; induction Δ, us; cbn [sorts_local_ctx]; exact _).

    #[export] Instance quote_on_type {Σ Γ T} : ground_quotable (@on_type P Σ Γ T) := _.

    #[export] Instance quote_on_udecl {univs udecl} : ground_quotable (@on_udecl univs udecl)
      := ltac:(cbv [on_udecl]; exact _).
    #[export] Instance quote_satisfiable_udecl {univs ϕ} : ground_quotable (@satisfiable_udecl univs ϕ) := _.
    #[export] Instance quote_valid_on_mono_udecl {univs ϕ} : ground_quotable (@valid_on_mono_udecl univs ϕ) := _.

    #[export] Instance quote_positive_cstr_arg {mdecl ctx t} : ground_quotable (@positive_cstr_arg mdecl ctx t) := ltac:(induction 1; exact _).
    #[export] Instance quote_positive_cstr {mdecl i ctx t} : ground_quotable (@positive_cstr mdecl i ctx t) := ltac:(induction 1; exact _).

    Import StrongerInstances.
    #[export] Instance quote_ind_respects_variance {Σ mdecl v indices} : ground_quotable (@ind_respects_variance Pcmp Σ mdecl v indices) := ltac:(cbv [ind_respects_variance]; exact _).
    #[export] Instance quote_cstr_respects_variance {Σ mdecl v cs} : ground_quotable (@cstr_respects_variance Pcmp Σ mdecl v cs) := ltac:(cbv [cstr_respects_variance]; exact _).
    #[export] Instance quote_on_constructor {Σ mdecl i idecl ind_indices cdecl cunivs} : ground_quotable (@on_constructor cf Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs) := ltac:(destruct 1; exact _).
    #[export] Instance quote_on_proj {mdecl mind i k p decl} : ground_quotable (@on_proj mdecl mind i k p decl) := ltac:(destruct 1; cbv [proj_type] in *; exact _).
    #[export] Instance quote_on_projection {mdecl mind i cdecl k p} : ground_quotable (@on_projection mdecl mind i cdecl k p) := ltac:(cbv [on_projection]; exact _).
    #[export] Instance quote_on_projections {mdecl mind i idecl ind_indices cdecl} : ground_quotable (@on_projections mdecl mind i idecl ind_indices cdecl) := ltac:(destruct 1; cbv [on_projection] in *; exact _).
    #[export] Instance quote_check_ind_sorts {Σ params kelim ind_indices cdecls ind_sort} : ground_quotable (@check_ind_sorts cf P Σ params kelim ind_indices cdecls ind_sort) := ltac:(cbv [check_ind_sorts check_constructors_smaller global_ext_constraints global_constraints] in *; exact _).
    #[export] Instance quote_on_ind_body {Σ mind mdecl i idecl} : ground_quotable (@on_ind_body cf Pcmp P Σ mind mdecl i idecl) := ltac:(destruct 1; cbv [it_mkProd_or_LetIn mkProd_or_LetIn ind_indices ind_sort] in *; exact _).
    #[export] Instance quote_on_variance {Σ univs variances} : ground_quotable (@on_variance cf Σ univs variances) := ltac:(cbv [on_variance consistent_instance_ext consistent_instance global_ext_constraints global_constraints]; exact _).
    #[export] Instance quote_on_inductive {Σ mind mdecl} : ground_quotable (@on_inductive cf Pcmp P Σ mind mdecl) := ltac:(destruct 1; exact _).
    #[export] Instance quote_on_constant_decl {Σ d} : ground_quotable (@on_constant_decl P Σ d) := ltac:(cbv [on_constant_decl]; exact _).
    #[export] Instance quote_on_global_decl {Σ kn d} : ground_quotable (@on_global_decl cf Pcmp P Σ kn d) := ltac:(cbv [on_global_decl]; exact _).
    #[export] Instance quote_on_global_decls_data {univs retro Σ kn d} : ground_quotable (@on_global_decls_data cf Pcmp P univs retro Σ kn d) := ltac:(destruct 1; exact _).
    #[export] Instance quote_on_global_decls {univs retro Σ} : ground_quotable (@on_global_decls cf Pcmp P univs retro Σ) := ltac:(induction 1; exact _).
    #[export] Instance quote_on_global_univs {univs} : ground_quotable (@on_global_univs univs) := ltac:(cbv [on_global_univs]; exact _).
    #[export] Instance quote_on_global_env {g} : ground_quotable (@on_global_env cf Pcmp P g) := ltac:(cbv [on_global_env]; exact _).
    #[export] Instance quote_on_global_env_ext {Σ} : ground_quotable (@on_global_env_ext cf Pcmp P Σ) := ltac:(cbv [on_global_env_ext]; exact _).
  End GlobalMaps.

  Module Instances.
    #[export] Existing Instances
     quote_on_context
     qtype_local_ctx
     qsorts_local_ctx
     qunivs_ext_constraints
     qsatisfiable_udecl
     qvalid_on_mono_udecl
     qsubst_instance_context
     qarities_context
     qind_arities
     qlift_level
     qlift_constraint
     qlift_constraints
     qlift_instance
     qvariance_cstrs
     qlevel_var_instance
     qvariance_universes
     qcstr_respects_variance
     qconstructor_univs
     qind_respects_variance
     qon_global_univs
     qon_udecl
     qon_global_env
     quote_constructor_univs
     quote_type_local_ctx
     quote_sorts_local_ctx
     quote_on_type
     quote_on_udecl
     quote_satisfiable_udecl
     quote_valid_on_mono_udecl
     quote_positive_cstr_arg
     quote_positive_cstr
     quote_ind_respects_variance
     quote_cstr_respects_variance
     quote_on_constructor
     quote_on_proj
     quote_on_projection
     quote_on_projections
     quote_check_ind_sorts
     quote_on_ind_body
     quote_on_variance
     quote_on_inductive
     quote_on_constant_decl
     quote_on_global_decl
     quote_on_global_decls_data
     quote_on_global_decls
     quote_on_global_univs
     quote_on_global_env
     quote_on_global_env_ext
    .
  End Instances.
End QuoteGlobalMapsSig.

Module Type QuotationOfConversionPar (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU) (CS : ConversionParSig T E TU ET).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "CS").
End QuotationOfConversionPar.

Module Type QuoteConversionPar (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU) (Import CS : ConversionParSig T E TU ET).
  #[export] Declare Instance quote_cumul_gen {cf Σ Γ pb t t'} : ground_quotable (@cumul_gen cf Σ Γ pb t t').
End QuoteConversionPar.

Module Type QuotationOfTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU)
  (CT : ConversionSig T E TU ET) (CS : ConversionParSig T E TU ET) (Ty : Typing T E TU ET CT CS).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "Ty").
End QuotationOfTyping.

Module Type QuoteTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU)
       (CT : ConversionSig T E TU ET) (CS : ConversionParSig T E TU ET) (Import Ty : Typing T E TU ET CT CS).

  #[export] Declare Instance quote_typing {cf Σ Γ t T} : ground_quotable (@typing cf Σ Γ t T).
End QuoteTyping.

Fail Module Type DeclarationTypingSig := DeclarationTypingSig.
Module Type DeclarationTypingSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E)
       (ET : EnvTypingSig T E TU) (CT : ConversionSig T E TU ET)
       (CS : ConversionParSig T E TU ET) (Ty : Typing T E TU ET CT CS)
       (L : LookupSig T E) (GM : GlobalMapsSig T E TU ET CT L).
  Include DeclarationTyping T E TU ET CT CS Ty L GM.
End DeclarationTypingSig.

Module Type QuotationOfDeclarationTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E)
  (ET : EnvTypingSig T E TU) (CT : ConversionSig T E TU ET)
  (CS : ConversionParSig T E TU ET) (Ty : Typing T E TU ET CT CS)
  (L : LookupSig T E) (GM : GlobalMapsSig T E TU ET CT L) (DT : DeclarationTypingSig T E TU ET CT CS Ty L GM).
  MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "DT").
End QuotationOfDeclarationTyping.

Module Type QuoteDeclarationTypingSig (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E)
       (Import ET : EnvTypingSig T E TU) (Import CT : ConversionSig T E TU ET)
       (Import CS : ConversionParSig T E TU ET) (Import Ty : Typing T E TU ET CT CS)
       (Import L : LookupSig T E) (Import GM : GlobalMapsSig T E TU ET CT L)
       (Import DT : DeclarationTypingSig T E TU ET CT CS Ty L GM).
  #[export] Declare Instance quote_type_local_decl {cf Σ Γ d} : ground_quotable (@type_local_decl cf Σ Γ d).
  #[export] Declare Instance quote_wf_local_rel {cf Σ Γ Γ'} : ground_quotable (@wf_local_rel cf Σ Γ Γ').
End QuoteDeclarationTyping.
