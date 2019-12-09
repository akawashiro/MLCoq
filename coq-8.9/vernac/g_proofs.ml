

open Glob_term
open Constrexpr
open Vernacexpr
open Hints
open Proof_global

open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pvernac.Vernac_

let thm_token = G_vernac.thm_token

let hint = Entry.create "hint"

let warn_deprecated_focus =
  CWarnings.create ~name:"deprecated-focus" ~category:"deprecated"
         (fun () ->
           Pp.strbrk
             "The Focus command is deprecated; use bullets or focusing brackets instead"
         )

let warn_deprecated_focus_n n =
  CWarnings.create ~name:"deprecated-focus" ~category:"deprecated"
         (fun () ->
           Pp.(str "The Focus command is deprecated;" ++ spc ()
               ++ str "use '" ++ int n ++ str ": {' instead")
         )

let warn_deprecated_unfocus =
  CWarnings.create ~name:"deprecated-unfocus" ~category:"deprecated"
         (fun () -> Pp.strbrk "The Unfocus command is deprecated")


let _ = let opt_hintbases = Gram.Entry.create "opt_hintbases"
        and reference_or_constr = Gram.Entry.create "reference_or_constr"
        and constr_body = Gram.Entry.create "constr_body"
        and mode = Gram.Entry.create "mode"
        in
        let () =
        Gram.gram_extend opt_hintbases
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.KEYWORD ":"))),
                              (Extend.Alist1 (Extend.Arules [Extend.Rules 
                                                            ({ Extend.norec_rule = Extend.Next 
                                                            (Extend.Stop,
                                                            (Extend.Atoken (Tok.IDENT ""))) },
                                                            (fun id loc ->
                                                             id ))]))),
                 (fun l _ loc ->  l ));
                Extend.Rule (Extend.Stop, (fun loc ->  [] ))])])
        in let () =
        Gram.gram_extend command
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.IDENT "Hint"))),
                                           (Extend.Aentry hint)),
                              (Extend.Aentry opt_hintbases)),
                 (fun dbnames h _ loc ->  VernacHints (dbnames, h) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Remove"))),
                                                       (Extend.Atoken (Tok.IDENT "Hints"))),
                                          (Extend.Alist1 (Extend.Aentry global))),
                             (Extend.Aentry opt_hintbases)),
                (fun dbnames ids _ _ loc ->
                 VernacRemoveHints (dbnames, ids) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Create"))),
                                                       (Extend.Atoken (Tok.IDENT "HintDb"))),
                                          (Extend.Atoken (Tok.IDENT ""))),
                             (Extend.Arules [Extend.Rules ({ Extend.norec_rule = Extend.Stop },
                                                          (fun loc ->
                                                           false ));
                                            Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD "discriminated"))) },
                                                         (fun _ loc ->
                                                          true ))])),
                (fun b id _ _ loc ->  VernacCreateHintDb (id, b) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Guarded"))),
                (fun _ loc ->  VernacCheckGuard ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Show"))),
                                          (Extend.Atoken (Tok.IDENT "Match"))),
                             (Extend.Aentry reference)),
                (fun id _ _ loc ->  VernacShow (ShowMatch id) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Show"))),
                             (Extend.Atoken (Tok.IDENT "Intros"))),
                (fun _ _ loc ->  VernacShow (ShowIntros true) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Show"))),
                             (Extend.Atoken (Tok.IDENT "Intro"))),
                (fun _ _ loc ->  VernacShow (ShowIntros false) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Show"))),
                             (Extend.Atoken (Tok.IDENT "Proof"))),
                (fun _ _ loc ->  VernacShow ShowProof ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Show"))),
                             (Extend.Atoken (Tok.IDENT "Conjectures"))),
                (fun _ _ loc ->  VernacShow ShowProofNames ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Show"))),
                             (Extend.Atoken (Tok.IDENT "Universes"))),
                (fun _ _ loc ->  VernacShow ShowUniverses ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Show"))),
                             (Extend.Atoken (Tok.IDENT "Existentials"))),
                (fun _ _ loc ->  VernacShow ShowExistentials ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Show"))),
                             (Extend.Atoken (Tok.IDENT "Script"))),
                (fun _ _ loc ->  VernacShow ShowScript ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Show"))),
                             (Extend.Aentry ident)),
                (fun id _ loc ->  VernacShow (ShowGoal (GoalId id)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Show"))),
                             (Extend.Aentry natural)),
                (fun n _ loc ->  VernacShow (ShowGoal (NthGoal n)) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Show"))),
                (fun _ loc ->  VernacShow (ShowGoal OpenSubgoals) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Unfocused"))),
                (fun _ loc ->  VernacUnfocused ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Unfocus"))),
                (fun _ loc ->
                 warn_deprecated_unfocus ~loc ();
         VernacUnfocus ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Focus"))),
                             (Extend.Aentry natural)),
                (fun n _ loc ->
                 warn_deprecated_focus_n n ~loc ();
         VernacFocus (Some n) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Focus"))),
                (fun _ loc ->
                 warn_deprecated_focus ~loc ();
         VernacFocus None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Undo"))),
                                          (Extend.Atoken (Tok.IDENT "To"))),
                             (Extend.Aentry natural)),
                (fun n _ _ loc ->  VernacUndoTo n ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Undo"))),
                             (Extend.Aentry natural)),
                (fun n _ loc ->  VernacUndo n ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Undo"))),
                (fun _ loc ->  VernacUndo 1 ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Restart"))),
                (fun _ loc ->  VernacRestart ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Defined"))),
                             (Extend.Aentry identref)),
                (fun id _ loc ->
                 VernacEndProof (Proved (Transparent,Some id)) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Defined"))),
                (fun _ loc ->  VernacEndProof (Proved (Transparent,None)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Save"))),
                             (Extend.Aentry identref)),
                (fun id _ loc ->  VernacEndProof (Proved (Opaque, Some id)) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.IDENT "Qed"))),
                (fun _ loc ->  VernacEndProof (Proved (Opaque,None)) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Admitted"))),
                (fun _ loc ->  VernacEndProof Admitted ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Existential"))),
                                          (Extend.Aentry natural)),
                             (Extend.Aentry constr_body)),
                (fun c n _ loc ->  VernacSolveExistential (n,c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Abort"))),
                             (Extend.Aentry identref)),
                (fun id _ loc ->  VernacAbort (Some id) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Abort"))),
                             (Extend.Atoken (Tok.IDENT "All"))),
                (fun _ _ loc ->  VernacAbortAll ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Abort"))),
                (fun _ loc ->  VernacAbort None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Proof"))),
                             (Extend.Aentry lconstr)),
                (fun c _ loc ->  VernacExactProof c ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Proof"))),
                                          (Extend.Atoken (Tok.IDENT "Mode"))),
                             (Extend.Aentry string)),
                (fun mn _ _ loc ->  VernacProofMode mn ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Proof"))),
                (fun _ loc ->  VernacProof (None,None) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Goal"))),
                             (Extend.Aentry lconstr)),
                (fun c _ loc ->
                 VernacDefinition (Decl_kinds.(NoDischarge, Definition), ((CAst.make ~loc Names.Anonymous), None), ProveBody ([], c)) ))])])
        in let () =
        Gram.gram_extend reference_or_constr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry constr)),
                 (fun c loc ->  HintsConstr c ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry global)),
                (fun r loc ->  HintsReference r ))])])
        in let () =
        Gram.gram_extend hint
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.IDENT "Constructors"))),
                              (Extend.Alist1 (Extend.Aentry global))),
                 (fun lc _ loc ->  HintsConstructors lc ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Unfold"))),
                             (Extend.Alist1 (Extend.Aentry global))),
                (fun lqid _ loc ->  HintsUnfold lqid ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Mode"))),
                                          (Extend.Aentry global)),
                             (Extend.Aentry mode)),
                (fun m l _ loc ->  HintsMode (l, m) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Opaque"))),
                             (Extend.Alist1 (Extend.Aentry global))),
                (fun lc _ loc ->
                 HintsTransparency (HintsReferences lc, false) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Transparent"))),
                             (Extend.Alist1 (Extend.Aentry global))),
                (fun lc _ loc ->
                 HintsTransparency (HintsReferences lc, true) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Constants"))),
                             (Extend.Atoken (Tok.IDENT "Opaque"))),
                (fun _ _ loc ->  HintsTransparency (HintsConstants, false) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Constants"))),
                             (Extend.Atoken (Tok.IDENT "Transparent"))),
                (fun _ _ loc ->  HintsTransparency (HintsConstants, true) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Variables"))),
                             (Extend.Atoken (Tok.IDENT "Opaque"))),
                (fun _ _ loc ->  HintsTransparency (HintsVariables, false) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Variables"))),
                             (Extend.Atoken (Tok.IDENT "Transparent"))),
                (fun _ _ loc ->  HintsTransparency (HintsVariables, true) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Immediate"))),
                             (Extend.Alist1 (Extend.Aentry reference_or_constr))),
                (fun lc _ loc ->  HintsImmediate lc ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Resolve"))),
                                                       (Extend.Atoken (Tok.KEYWORD "<-"))),
                                          (Extend.Alist1 (Extend.Aentry global))),
                             (Extend.Aopt (Extend.Aentry natural))),
                (fun n lc _ _ loc ->  HintsResolveIFF (false, lc, n) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Resolve"))),
                                                       (Extend.Atoken (Tok.KEYWORD "->"))),
                                          (Extend.Alist1 (Extend.Aentry global))),
                             (Extend.Aopt (Extend.Aentry natural))),
                (fun n lc _ _ loc ->  HintsResolveIFF (true, lc, n) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Resolve"))),
                                          (Extend.Alist1 (Extend.Aentry reference_or_constr))),
                             (Extend.Aentry hint_info)),
                (fun info lc _ loc ->
                 HintsResolve (List.map (fun x -> (info, true, x)) lc) ))])])
        in let () =
        Gram.gram_extend constr_body
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD ":"))),
                                                        (Extend.Aentry lconstr)),
                                           (Extend.Atoken (Tok.KEYWORD ":="))),
                              (Extend.Aentry lconstr)),
                 (fun c _ t _ loc ->  CAst.make ~loc @@ CCast(c,CastConv t) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD ":="))),
                             (Extend.Aentry lconstr)),
                (fun c _ loc ->  c ))])])
        in let () =
        Gram.gram_extend mode
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Alist1 (Extend.Arules [Extend.Rules 
                                                            ({ Extend.norec_rule = Extend.Next 
                                                            (Extend.Stop,
                                                            (Extend.Atoken (Tok.KEYWORD "-"))) },
                                                            (fun _ loc ->
                                                             ModeOutput ));
                                                            Extend.Rules 
                                                            ({ Extend.norec_rule = Extend.Next 
                                                            (Extend.Stop,
                                                            (Extend.Atoken (Tok.KEYWORD "!"))) },
                                                            (fun _ loc ->
                                                             ModeNoHeadEvar ));
                                                            Extend.Rules 
                                                            ({ Extend.norec_rule = Extend.Next 
                                                            (Extend.Stop,
                                                            (Extend.Atoken (Tok.KEYWORD "+"))) },
                                                            (fun _ loc ->
                                                             ModeInput ))]))),
                 (fun l loc ->  l ))])])
        in ()

