DECLARE PLUGIN "tuto3_plugin"
open Pp

open Ltac_plugin

open Construction_game

(* This one is necessary, to avoid message about missing wit_string *)
open Stdarg

VERNAC COMMAND EXTEND ShowTypeConstruction CLASSIFIED AS QUERY
| [ "Tuto3_1" ] ->
  [ let env = Global.env () in
    let evd = Evd.from_env env in
    let evd, s = Evd.new_sort_variable Evd.univ_rigid evd in
    let new_type_2 = EConstr.mkSort s in
    let evd, _ =
      Typing.type_of (Global.env()) (Evd.from_env (Global.env())) new_type_2 in
    Feedback.msg_notice
      (Printer.pr_econstr_env env evd new_type_2) ]
END

VERNAC COMMAND EXTEND ShowOneConstruction CLASSIFIED AS QUERY
| [ "Tuto3_2" ] -> [ example_sort_app_lambda () ]
END

TACTIC EXTEND collapse_hyps
| [ "pack" "hypothesis" ident(i) ] ->
  [ Tuto_tactic.pack_tactic i ]
END

(* More advanced examples, where automatic proof happens but
   no tactic is being called explicitely.  The first one uses
   type classes. *)
VERNAC COMMAND EXTEND TriggerClasses CLASSIFIED AS QUERY
| [ "Tuto3_3" int(n) ] -> [ example_classes n ]
END

(* The second one uses canonical structures. *)
VERNAC COMMAND EXTEND TriggerCanonical CLASSIFIED AS QUERY
| [ "Tuto3_4" int(n) ] -> [ example_canonical n ]
END

TACTIC EXTEND BeginRecord 
| [ "begin_record" ]->
  [ let _ = Feedback.msg_notice (str "Begin Record") in
    Tacticals.New.tclIDTAC
  ]
END

TACTIC EXTEND EndRecord 
| [ "end_record" ]->
  [ let _ = Feedback.msg_notice (str "End Record") in
    Tacticals.New.tclIDTAC
  ]
END
