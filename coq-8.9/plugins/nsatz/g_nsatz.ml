

open Ltac_plugin
open Stdarg


let __coq_plugin_name = "nsatz_plugin"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "nsatz_compute" ~level:0 Tacentries.([
         (TyML (TyIdent ("nsatz_compute", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), "lt", 
                                          TyNil)), fun lt ist
                                                    ->  Nsatz.nsatz_compute (EConstr.Unsafe.to_constr lt) ))
         ])

