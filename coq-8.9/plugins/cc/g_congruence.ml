

open Ltac_plugin
open Cctac
open Stdarg


let __coq_plugin_name = "cc_plugin"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "cc" ~level:0 Tacentries.([
         (TyML (TyIdent ("congruence", TyNil), fun ist
                                                ->  congruence_tac 1000 [] ));
         (TyML (TyIdent ("congruence", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_integer), "n", 
                                       TyNil)), fun n ist
                                                 ->  congruence_tac n [] ));
         (TyML (TyIdent ("congruence", TyIdent ("with", TyArg (Extend.TUlist1 (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_constr)), "l", 
                                                        TyNil))), fun l ist
                                                                   ->  congruence_tac 1000 l ));
         (TyML (TyIdent ("congruence", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_integer), "n", 
                                       TyIdent ("with", TyArg (Extend.TUlist1 (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_constr)), "l", 
                                                        TyNil)))), fun n l
                                                                   ist
                                                                    ->  congruence_tac n l ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "f_equal" ~level:0 Tacentries.([
         (TyML (TyIdent ("f_equal", TyNil), fun ist  ->  f_equal ))
         ])

