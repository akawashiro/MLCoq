DECLARE PLUGIN "tuto0_plugin"

open Pp
open Ltac_plugin
open Stdarg


VERNAC COMMAND EXTEND HelloWorld CLASSIFIED AS QUERY
| [ "HelloWorld" ] -> [ Feedback.msg_notice (strbrk Tuto0_main.message) ]
END

TACTIC EXTEND hello_world_tactic
| [ "hello_world" ] ->
  [ let _ = Feedback.msg_notice (str Tuto0_main.message) in
    Tacticals.New.tclIDTAC ]
END

TACTIC EXTEND BeginRecord 
| [ "begin_record" ident(i)  ]->
  [ let _ = Feedback.msg_notice (strbrk "Begin Record") in
    Tacticals.New.tclIDTAC
  ]
END

TACTIC EXTEND EndRecord 
| [ "end_record" ]->
  [ let _ = Feedback.msg_notice (strbrk "End Record") in
    Tacticals.New.tclIDTAC
  ]
END
