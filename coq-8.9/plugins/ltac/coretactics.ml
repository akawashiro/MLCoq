

open Util
open Locus
open Tactypes
open Genredexpr
open Stdarg
open Extraargs
open Tacarg
open Names
open Logic

let wit_hyp = wit_var


let __coq_plugin_name = "ltac_plugin"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "reflexivity" ~level:0 Tacentries.([
         (TyML (TyIdent ("reflexivity", TyNil), fun ist
                                                 ->  Tactics.intros_reflexivity ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "exact" ~level:0 Tacentries.([
         (TyML (TyIdent ("exact", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_casted_constr), "c", 
                                  TyNil)), fun c ist
                                            ->  Tactics.exact_no_check c ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "assumption" ~level:0 Tacentries.([
         (TyML (TyIdent ("assumption", TyNil), fun ist
                                                ->  Tactics.assumption ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "etransitivity" ~level:0 Tacentries.([
         (TyML (TyIdent ("etransitivity", TyNil), fun ist
                                                   ->  Tactics.intros_transitivity None ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "cut" ~level:0 Tacentries.([
         (TyML (TyIdent ("cut", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), "c", 
                                TyNil)), fun c ist  ->  Tactics.cut c ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "exact_no_check" ~level:0 Tacentries.([
         (TyML (TyIdent ("exact_no_check", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), "c", 
                                           TyNil)), fun c ist
                                                     ->  Tactics.exact_no_check c ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "vm_cast_no_check" ~level:0 Tacentries.([
         (TyML (TyIdent ("vm_cast_no_check", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), "c", 
                                             TyNil)), fun c ist
                                                       ->  Tactics.vm_cast_no_check c ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "native_cast_no_check" ~level:0 Tacentries.([
         (TyML (TyIdent ("native_cast_no_check", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), "c", 
                                                 TyNil)), fun c ist
                                                           ->  Tactics.native_cast_no_check c ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "casetype" ~level:0 Tacentries.([
         (TyML (TyIdent ("casetype", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), "c", 
                                     TyNil)), fun c ist
                                               ->  Tactics.case_type c ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "elimtype" ~level:0 Tacentries.([
         (TyML (TyIdent ("elimtype", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), "c", 
                                     TyNil)), fun c ist
                                               ->  Tactics.elim_type c ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "lapply" ~level:0 Tacentries.([
         (TyML (TyIdent ("lapply", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), "c", 
                                   TyNil)), fun c ist
                                             ->  Tactics.cut_and_apply c ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "transitivity" ~level:0 Tacentries.([
         (TyML (TyIdent ("transitivity", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), "c", 
                                         TyNil)), fun c ist
                                                   ->  Tactics.intros_transitivity (Some c) ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "left" ~level:0 Tacentries.([
         (TyML (TyIdent ("left", TyNil), fun ist
                                          ->  Tactics.left_with_bindings false NoBindings ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "eleft" ~level:0 Tacentries.([
         (TyML (TyIdent ("eleft", TyNil), fun ist
                                           ->  Tactics.left_with_bindings true NoBindings ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "left_with" ~level:0 Tacentries.([
         (TyML (TyIdent ("left", TyIdent ("with", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_bindings), "bl", 
                                                  TyNil))), fun bl ist
                                                             -> 
    Tacticals.New.tclDELAYEDWITHHOLES false bl (fun bl -> Tactics.left_with_bindings false bl)
  ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "eleft_with" ~level:0 Tacentries.([
         (TyML (TyIdent ("eleft", TyIdent ("with", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_bindings), "bl", 
                                                   TyNil))), fun bl ist
                                                              -> 
    Tacticals.New.tclDELAYEDWITHHOLES true bl (fun bl -> Tactics.left_with_bindings true bl)
  ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "right" ~level:0 Tacentries.([
         (TyML (TyIdent ("right", TyNil), fun ist
                                           ->  Tactics.right_with_bindings false NoBindings ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "eright" ~level:0 Tacentries.([
         (TyML (TyIdent ("eright", TyNil), fun ist
                                            ->  Tactics.right_with_bindings true NoBindings ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "right_with" ~level:0 Tacentries.([
         (TyML (TyIdent ("right", TyIdent ("with", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_bindings), "bl", 
                                                   TyNil))), fun bl ist
                                                              -> 
    Tacticals.New.tclDELAYEDWITHHOLES false bl (fun bl -> Tactics.right_with_bindings false bl)
  ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "eright_with" ~level:0 Tacentries.([
         (TyML (TyIdent ("eright", TyIdent ("with", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_bindings), "bl", 
                                                    TyNil))), fun bl ist
                                                               -> 
    Tacticals.New.tclDELAYEDWITHHOLES true bl (fun bl -> Tactics.right_with_bindings true bl)
  ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "constructor" ~level:0 Tacentries.([
         (TyML (TyIdent ("constructor", TyNil), fun ist
                                                 ->  Tactics.any_constructor false None ));
         (TyML (TyIdent ("constructor", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var), "i", 
                                        TyNil)), fun i ist
                                                  -> 
    Tactics.constructor_tac false None i NoBindings
  ));
         (TyML (TyIdent ("constructor", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var), "i", 
                                        TyIdent ("with", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_bindings), "bl", 
                                                         TyNil)))), fun i bl
                                                                    ist
                                                                     -> 
    let tac bl = Tactics.constructor_tac false None i bl in
    Tacticals.New.tclDELAYEDWITHHOLES false bl tac
  ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "econstructor" ~level:0 Tacentries.([
         (TyML (TyIdent ("econstructor", TyNil), fun ist
                                                  ->  Tactics.any_constructor true None ));
         (TyML (TyIdent ("econstructor", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var), "i", 
                                         TyNil)), fun i ist
                                                   -> 
    Tactics.constructor_tac true None i NoBindings
  ));
         (TyML (TyIdent ("econstructor", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var), "i", 
                                         TyIdent ("with", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_bindings), "bl", 
                                                          TyNil)))), 
          fun i bl ist
           -> 
    let tac bl = Tactics.constructor_tac true None i bl in
    Tacticals.New.tclDELAYEDWITHHOLES true bl tac
  ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "specialize" ~level:0 Tacentries.([
         (TyML (TyIdent ("specialize", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr_with_bindings), "c", 
                                       TyNil)), fun c ist
                                                 -> 
    Tacticals.New.tclDELAYEDWITHHOLES false c (fun c -> Tactics.specialize c None)
  ));
         (TyML (TyIdent ("specialize", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr_with_bindings), "c", 
                                       TyIdent ("as", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_intropattern), "ipat", 
                                                      TyNil)))), fun c ipat
                                                                 ist
                                                                  -> 
    Tacticals.New.tclDELAYEDWITHHOLES false c (fun c -> Tactics.specialize c (Some ipat))
  ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "symmetry" ~level:0 Tacentries.([
         (TyML (TyIdent ("symmetry", TyNil), fun ist
                                              ->  Tactics.intros_symmetry {onhyps=Some[];concl_occs=AllOccurrences} ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "symmetry_in" ~level:0 Tacentries.([
         (TyML (TyIdent ("symmetry", TyIdent ("in", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_in_clause), "cl", 
                                                    TyNil))), fun cl ist
                                                               ->  Tactics.intros_symmetry cl ))
         ])



let rec delayed_list = function
| [] -> fun _ sigma -> (sigma, [])
| x :: l ->
  fun env sigma ->
    let (sigma, x) = x env sigma in
    let (sigma, l) = delayed_list l env sigma in
    (sigma, x :: l)


let () = Tacentries.tactic_extend __coq_plugin_name "split" ~level:0 Tacentries.([
         (TyML (TyIdent ("split", TyNil), fun ist
                                           ->  Tactics.split_with_bindings false [NoBindings] ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "esplit" ~level:0 Tacentries.([
         (TyML (TyIdent ("esplit", TyNil), fun ist
                                            ->  Tactics.split_with_bindings true [NoBindings] ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "split_with" ~level:0 Tacentries.([
         (TyML (TyIdent ("split", TyIdent ("with", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_bindings), "bl", 
                                                   TyNil))), fun bl ist
                                                              -> 
    Tacticals.New.tclDELAYEDWITHHOLES false bl (fun bl -> Tactics.split_with_bindings false [bl])
  ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "esplit_with" ~level:0 Tacentries.([
         (TyML (TyIdent ("esplit", TyIdent ("with", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_bindings), "bl", 
                                                    TyNil))), fun bl ist
                                                               -> 
    Tacticals.New.tclDELAYEDWITHHOLES true bl (fun bl -> Tactics.split_with_bindings true [bl])
  ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "exists" ~level:0 Tacentries.([
         (TyML (TyIdent ("exists", TyNil), fun ist
                                            ->  Tactics.split_with_bindings false [NoBindings] ));
         (TyML (TyIdent ("exists", TyArg (Extend.TUlist1sep (Extend.TUentry (Genarg.get_arg_tag wit_bindings), ","), "bll", 
                                   TyNil)), fun bll ist
                                             -> 
    Tacticals.New.tclDELAYEDWITHHOLES false (delayed_list bll) (fun bll -> Tactics.split_with_bindings false bll)
  ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "eexists" ~level:0 Tacentries.([
         (TyML (TyIdent ("eexists", TyNil), fun ist
                                             ->  Tactics.split_with_bindings true [NoBindings] ));
         (TyML (TyIdent ("eexists", TyArg (Extend.TUlist1sep (Extend.TUentry (Genarg.get_arg_tag wit_bindings), ","), "bll", 
                                    TyNil)), fun bll ist
                                              -> 
    Tacticals.New.tclDELAYEDWITHHOLES true (delayed_list bll) (fun bll -> Tactics.split_with_bindings true bll)
  ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "intros_until" ~level:0 Tacentries.([
         (TyML (TyIdent ("intros", TyIdent ("until", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_quantified_hypothesis), "h", 
                                                     TyNil))), fun h ist
                                                                ->  Tactics.intros_until h ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "intro" ~level:0 Tacentries.([
         (TyML (TyIdent ("intro", TyNil), fun ist
                                           ->  Tactics.intro_move None MoveLast ));
         (TyML (TyIdent ("intro", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ident), "id", 
                                  TyNil)), fun id ist
                                            ->  Tactics.intro_move (Some id) MoveLast ));
         (TyML (TyIdent ("intro", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ident), "id", 
                                  TyIdent ("at", TyIdent ("top", TyNil)))), 
          fun id ist  ->  Tactics.intro_move (Some id) MoveFirst ));
         (TyML (TyIdent ("intro", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ident), "id", 
                                  TyIdent ("at", TyIdent ("bottom", TyNil)))), 
          fun id ist  ->  Tactics.intro_move (Some id) MoveLast ));
         (TyML (TyIdent ("intro", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ident), "id", 
                                  TyIdent ("after", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_hyp), "h", 
                                                    TyNil)))), fun id h ist
                                                                ->  Tactics.intro_move (Some id) (MoveAfter h) ));
         (TyML (TyIdent ("intro", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ident), "id", 
                                  TyIdent ("before", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_hyp), "h", 
                                                     TyNil)))), fun id h ist
                                                                 ->  Tactics.intro_move (Some id) (MoveBefore h) ));
         (TyML (TyIdent ("intro", TyIdent ("at", TyIdent ("top", TyNil))), 
          fun ist  ->  Tactics.intro_move None MoveFirst ));
         (TyML (TyIdent ("intro", TyIdent ("at", TyIdent ("bottom", TyNil))), 
          fun ist  ->  Tactics.intro_move None MoveLast ));
         (TyML (TyIdent ("intro", TyIdent ("after", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_hyp), "h", 
                                                    TyNil))), fun h ist
                                                               ->  Tactics.intro_move None (MoveAfter h) ));
         (TyML (TyIdent ("intro", TyIdent ("before", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_hyp), "h", 
                                                     TyNil))), fun h ist
                                                                ->  Tactics.intro_move None (MoveBefore h) ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "move" ~level:0 Tacentries.([
         (TyML (TyIdent ("move", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_hyp), "id", 
                                 TyIdent ("at", TyIdent ("top", TyNil)))), 
          fun id ist  ->  Tactics.move_hyp id MoveFirst ));
         (TyML (TyIdent ("move", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_hyp), "id", 
                                 TyIdent ("at", TyIdent ("bottom", TyNil)))), 
          fun id ist  ->  Tactics.move_hyp id MoveLast ));
         (TyML (TyIdent ("move", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_hyp), "id", 
                                 TyIdent ("after", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_hyp), "h", 
                                                   TyNil)))), fun id h ist
                                                               ->  Tactics.move_hyp id (MoveAfter h) ));
         (TyML (TyIdent ("move", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_hyp), "id", 
                                 TyIdent ("before", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_hyp), "h", 
                                                    TyNil)))), fun id h ist
                                                                ->  Tactics.move_hyp id (MoveBefore h) ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "rename" ~level:0 Tacentries.([
         (TyML (TyIdent ("rename", TyArg (Extend.TUlist1sep (Extend.TUentry (Genarg.get_arg_tag wit_rename), ","), "ids", 
                                   TyNil)), fun ids ist
                                             ->  Tactics.rename_hyp ids ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "revert" ~level:0 Tacentries.([
         (TyML (TyIdent ("revert", TyArg (Extend.TUlist1 (Extend.TUentry (Genarg.get_arg_tag wit_hyp)), "hl", 
                                   TyNil)), fun hl ist
                                             ->  Tactics.revert hl ))
         ])



let simple_induct h =
  Tacticals.New.tclTHEN (Tactics.intros_until h)
    (Tacticals.New.onLastHyp Tactics.simplest_elim)


let () = Tacentries.tactic_extend __coq_plugin_name "simple_induction" ~level:0 Tacentries.([
         (TyML (TyIdent ("simple", TyIdent ("induction", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_quantified_hypothesis), "h", 
                                                         TyNil))), fun h ist
                                                                    ->  simple_induct h ))
         ])



let simple_destruct h =
  Tacticals.New.tclTHEN (Tactics.intros_until h)
    (Tacticals.New.onLastHyp Tactics.simplest_case)


let () = Tacentries.tactic_extend __coq_plugin_name "simple_destruct" ~level:0 Tacentries.([
         (TyML (TyIdent ("simple", TyIdent ("destruct", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_quantified_hypothesis), "h", 
                                                        TyNil))), fun h ist
                                                                   ->  simple_destruct h ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "double_induction" ~level:0 Tacentries.([
         (TyML (TyIdent ("double", TyIdent ("induction", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_quantified_hypothesis), "h1", 
                                                         TyArg (Extend.TUentry (Genarg.get_arg_tag wit_quantified_hypothesis), "h2", 
                                                         TyNil)))), fun h1 h2
                                                                    ist
                                                                     ->  Elim.h_double_induction h1 h2 ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "admit" ~level:0 Tacentries.([
         (TyML (TyIdent ("admit", TyNil), fun ist  ->  Proofview.give_up ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "fix" ~level:0 Tacentries.([
         (TyML (TyIdent ("fix", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ident), "id", 
                                TyArg (Extend.TUentry (Genarg.get_arg_tag wit_natural), "n", 
                                TyNil))), fun id n ist  ->  Tactics.fix id n ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "cofix" ~level:0 Tacentries.([
         (TyML (TyIdent ("cofix", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ident), "id", 
                                  TyNil)), fun id ist  ->  Tactics.cofix id ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "clear" ~level:0 Tacentries.([
         (TyML (TyIdent ("clear", TyArg (Extend.TUlist0 (Extend.TUentry (Genarg.get_arg_tag wit_hyp)), "ids", 
                                  TyNil)), fun ids ist
                                            -> 
    if List.is_empty ids then Tactics.keep []
    else Tactics.clear ids
  ));
         (TyML (TyIdent ("clear", TyIdent ("-", TyArg (Extend.TUlist1 (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_hyp)), "ids", 
                                                TyNil))), fun ids ist
                                                           ->  Tactics.keep ids ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "clearbody" ~level:0 Tacentries.([
         (TyML (TyIdent ("clearbody", TyArg (Extend.TUlist1 (Extend.TUentry (Genarg.get_arg_tag wit_hyp)), "ids", 
                                      TyNil)), fun ids ist
                                                ->  Tactics.clear_body ids ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "generalize_dependent" ~level:0 Tacentries.([
         (TyML (TyIdent ("generalize", TyIdent ("dependent", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), "c", 
                                                             TyNil))), 
          fun c ist  ->  Tactics.generalize_dep c ))
         ])



open Tacexpr

let initial_atomic () =
  let nocl = {onhyps=Some[];concl_occs=AllOccurrences} in
  let iter (s, t) =
    let body = TacAtom (Loc.tag t) in
    Tacenv.register_ltac false false (Names.Id.of_string s) body
  in
  let () = List.iter iter
      [ "red", TacReduce(Red false,nocl);
        "hnf", TacReduce(Hnf,nocl);
        "simpl", TacReduce(Simpl (Redops.all_flags,None),nocl);
        "compute", TacReduce(Cbv Redops.all_flags,nocl);
        "intros", TacIntroPattern (false,[]);
      ]
  in
  let iter (s, t) = Tacenv.register_ltac false false (Names.Id.of_string s) t in
  List.iter iter
      [ "idtac",TacId [];
        "fail", TacFail(TacLocal,ArgArg 0,[]);
        "fresh", TacArg(Loc.tag @@ TacFreshId [])
      ]

let () = Mltop.declare_cache_obj initial_atomic "ltac_plugin"

(* First-class Ltac access to primitive blocks *)

let initial_name s = { mltac_plugin = "ltac_plugin"; mltac_tactic = s; }
let initial_entry s = { mltac_name = initial_name s; mltac_index = 0; }

let register_list_tactical name f =
  let tac args ist = match args with
  | [v] ->
    begin match Tacinterp.Value.to_list v with
    | None -> Tacticals.New.tclZEROMSG (Pp.str "Expected a list")
    | Some tacs ->
      let tacs = List.map (fun tac -> Tacinterp.tactic_of_value ist tac) tacs in
      f tacs
    end
  | _ -> assert false
  in
  Tacenv.register_ml_tactic (initial_name name) [|tac|]

let () = register_list_tactical "first" Tacticals.New.tclFIRST
let () = register_list_tactical "solve" Tacticals.New.tclSOLVE

let initial_tacticals () =
  let idn n = Id.of_string (Printf.sprintf "_%i" n) in
  let varn n = Reference (ArgVar (CAst.make (idn n))) in
  let iter (s, t) = Tacenv.register_ltac false false (Id.of_string s) t in
  List.iter iter [
    "first", TacFun ([Name (idn 0)], TacML (None, (initial_entry "first", [varn 0])));
    "solve", TacFun ([Name (idn 0)], TacML (None, (initial_entry "solve", [varn 0])));
  ]

let () = Mltop.declare_cache_obj initial_tacticals "ltac_plugin"


