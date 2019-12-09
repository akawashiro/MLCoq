

open Ltac_plugin


let __coq_plugin_name = "rtauto_plugin"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "rtauto" ~level:0 Tacentries.([
         (TyML (TyIdent ("rtauto", TyNil), fun ist
                                            ->  Proofview.V82.tactic (Refl_tauto.rtauto_tac) ))
         ])

