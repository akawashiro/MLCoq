

open Eqdecide
open Stdarg


let __coq_plugin_name = "ltac_plugin"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "decide_equality" ~level:0 Tacentries.([
         (TyML (TyIdent ("decide", TyIdent ("equality", TyNil)), fun ist
                                                                  ->  decideEqualityGoal ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "compare" ~level:0 Tacentries.([
         (TyML (TyIdent ("compare", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), "c1", 
                                    TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), "c2", 
                                    TyNil))), fun c1 c2 ist
                                               ->  compare c1 c2 ))
         ])

