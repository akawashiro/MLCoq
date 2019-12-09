

open Ltac_plugin
open Stdarg
open Tacarg


let __coq_plugin_name = "micromega_plugin"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "RED" ~level:0 Tacentries.([
         (TyML (TyIdent ("myred", TyNil), fun ist  ->  Tactics.red_in_concl ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "PsatzZ" ~level:0 Tacentries.([
         (TyML (TyIdent ("psatz_Z", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var), "i", 
                                    TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                    TyNil))), fun i t ist
                                               ->   (Coq_micromega.psatz_Z i
                                               (Tacinterp.tactic_of_value ist t))
                                               ));
         (TyML (TyIdent ("psatz_Z", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                    TyNil)), fun t ist
                                              ->   (Coq_micromega.psatz_Z (-1)) (Tacinterp.tactic_of_value ist t) ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "Lia" ~level:0 Tacentries.([
         (TyML (TyIdent ("xlia", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                 TyNil)), fun t ist
                                           ->    (Coq_micromega.xlia (Tacinterp.tactic_of_value ist t)) ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "Nia" ~level:0 Tacentries.([
         (TyML (TyIdent ("xnlia", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                  TyNil)), fun t ist
                                            ->   (Coq_micromega.xnlia (Tacinterp.tactic_of_value ist t)) ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "NRA" ~level:0 Tacentries.([
         (TyML (TyIdent ("xnra", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                 TyNil)), fun t ist
                                           ->   (Coq_micromega.nra (Tacinterp.tactic_of_value ist t))))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "NQA" ~level:0 Tacentries.([
         (TyML (TyIdent ("xnqa", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                 TyNil)), fun t ist
                                           ->   (Coq_micromega.nqa (Tacinterp.tactic_of_value ist t))))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "Sos_Z" ~level:0 Tacentries.([
         (TyML (TyIdent ("sos_Z", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                  TyNil)), fun t ist
                                            ->  (Coq_micromega.sos_Z (Tacinterp.tactic_of_value ist t)) ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "Sos_Q" ~level:0 Tacentries.([
         (TyML (TyIdent ("sos_Q", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                  TyNil)), fun t ist
                                            ->    (Coq_micromega.sos_Q (Tacinterp.tactic_of_value ist t)) ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "Sos_R" ~level:0 Tacentries.([
         (TyML (TyIdent ("sos_R", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                  TyNil)), fun t ist
                                            ->    (Coq_micromega.sos_R (Tacinterp.tactic_of_value ist t)) ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "LRA_Q" ~level:0 Tacentries.([
         (TyML (TyIdent ("lra_Q", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                  TyNil)), fun t ist
                                            ->    (Coq_micromega.lra_Q (Tacinterp.tactic_of_value ist t)) ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "LRA_R" ~level:0 Tacentries.([
         (TyML (TyIdent ("lra_R", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                  TyNil)), fun t ist
                                            ->    (Coq_micromega.lra_R (Tacinterp.tactic_of_value ist t)) ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "PsatzR" ~level:0 Tacentries.([
         (TyML (TyIdent ("psatz_R", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var), "i", 
                                    TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                    TyNil))), fun i t ist
                                               ->    (Coq_micromega.psatz_R i (Tacinterp.tactic_of_value ist t)) ));
         (TyML (TyIdent ("psatz_R", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                    TyNil)), fun t ist
                                              ->    (Coq_micromega.psatz_R (-1) (Tacinterp.tactic_of_value ist t)) ))
         ])

let () = Tacentries.tactic_extend __coq_plugin_name "PsatzQ" ~level:0 Tacentries.([
         (TyML (TyIdent ("psatz_Q", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_int_or_var), "i", 
                                    TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                    TyNil))), fun i t ist
                                               ->   (Coq_micromega.psatz_Q i (Tacinterp.tactic_of_value ist t)) ));
         (TyML (TyIdent ("psatz_Q", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), "t", 
                                    TyNil)), fun t ist
                                              ->   (Coq_micromega.psatz_Q (-1) (Tacinterp.tactic_of_value ist t)) ))
         ])

