let __coq_plugin_name = "romega_plugin"
let _ = Mltop.add_known_module __coq_plugin_name


open Ltac_plugin
open Names
open Refl_omega
open Stdarg

let eval_tactic name =
  let dp = DirPath.make (List.map Id.of_string ["PreOmega"; "omega"; "Coq"]) in
  let kn = KerName.make2 (ModPath.MPfile dp) (Label.make name) in
  let tac = Tacenv.interp_ltac kn in
  Tacinterp.eval_tactic tac

let romega_tactic unsafe l =
  let tacs = List.map
    (function
       | "nat" -> eval_tactic "zify_nat"
       | "positive" -> eval_tactic "zify_positive"
       | "N" -> eval_tactic "zify_N"
       | "Z" -> eval_tactic "zify_op"
       | s -> CErrors.user_err Pp.(str ("No ROmega knowledge base for type "^s)))
    (Util.List.sort_uniquize String.compare l)
  in
  Tacticals.New.tclTHEN
    (Tacticals.New.tclREPEAT (Proofview.tclPROGRESS (Tacticals.New.tclTHENLIST tacs)))
    (Tacticals.New.tclTHEN
       (* because of the contradiction process in (r)omega,
          we'd better leave as little as possible in the conclusion,
          for an easier decidability argument. *)
       (Tactics.intros)
       (total_reflexive_omega_tactic unsafe))

let romega_depr =
  Vernacinterp.mk_deprecation
    ~since:(Some "8.9")
    ~note:(Some "Use lia instead.")
    ()


let () = Tacentries.tactic_extend __coq_plugin_name "romega" ~level:0 ~deprecation:( romega_depr ) Tacentries.([
         (TyML (TyIdent ("romega", TyNil), fun ist
                                            ->  romega_tactic false [] ));
         (TyML (TyIdent ("unsafe_romega", TyNil), fun ist
                                                   ->  romega_tactic true [] ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "romega'" ~level:0 ~deprecation:( romega_depr ) Tacentries.([
         (TyML (TyIdent ("romega", TyIdent ("with", TyArg (Extend.TUlist1 (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_ident)), "l", 
                                                    TyNil))), fun l ist
                                                               ->  romega_tactic false (List.map Names.Id.to_string l) ));
         (TyML (TyIdent ("romega", TyIdent ("with", TyIdent ("*", TyNil))), 
          fun ist  ->  romega_tactic false ["nat";"positive";"N";"Z"] ))
         ])

