
open Pcoq
open Pcoq.Prim
open Vernacexpr

(* Vernaculars specific to the toplevel *)
type vernac_toplevel =
  | VernacBacktrack of int * int * int
  | VernacDrop
  | VernacQuit
  | VernacControl of vernac_control

module Toplevel_ : sig
  val vernac_toplevel : vernac_toplevel CAst.t Entry.t
end = struct
  let gec_vernac s = Entry.create ("toplevel:" ^ s)
  let vernac_toplevel = gec_vernac "vernac_toplevel"
end

open Toplevel_


let _ = let () =
        Gram.gram_extend vernac_toplevel
        (Some
        (Extend.First), [(None, None,
                         [Extend.Rule
                          (Extend.Next (Extend.Stop,
                                       (Extend.Aentry Pvernac.main_entry)),
                          (fun cmd loc ->
                           match cmd with
              | None -> raise Stm.End_of_input
              | Some (loc,c) -> CAst.make ~loc (VernacControl c) ));
                         Extend.Rule
                         (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                (Extend.Next 
                                                                (Extend.Stop,
                                                                (Extend.Atoken (Tok.IDENT "Backtrack"))),
                                                                (Extend.Aentry natural)),
                                                                (Extend.Aentry natural)),
                                                   (Extend.Aentry natural)),
                                      (Extend.Atoken (Tok.KEYWORD "."))),
                         (fun _ p m n _ loc ->
                          CAst.make (VernacBacktrack (n,m,p)) ));
                         Extend.Rule
                         (Extend.Next (Extend.Next (Extend.Stop,
                                                   (Extend.Atoken (Tok.IDENT "Quit"))),
                                      (Extend.Atoken (Tok.KEYWORD "."))),
                         (fun _ _ loc ->  CAst.make VernacQuit ));
                         Extend.Rule
                         (Extend.Next (Extend.Next (Extend.Stop,
                                                   (Extend.Atoken (Tok.IDENT "Drop"))),
                                      (Extend.Atoken (Tok.KEYWORD "."))),
                         (fun _ _ loc ->  CAst.make VernacDrop ))])])
        in ()



let parse_toplevel pa = Pcoq.Entry.parse vernac_toplevel pa


