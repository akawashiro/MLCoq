# 11 "tools/ocamllibdep.mll"
 
  exception Syntax_error of int*int

  let syntax_error lexbuf =
    raise (Syntax_error (Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf))

  [@@@ocaml.warning "-3"]       (* String.(un)capitalize_ascii since 4.03.0 GPR#124 *)
  let uncapitalize = String.uncapitalize

  let capitalize = String.capitalize
  [@@@ocaml.warning "+3"]

# 15 "tools/ocamllibdep.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base =
   "\000\000\250\255\251\255\002\000\000\000\052\000\160\000\000\000\
    \009\000\011\000\012\000\013\000\001\000\253\255";
  Lexing.lex_backtrk =
   "\255\255\255\255\255\255\003\000\005\000\000\000\001\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255";
  Lexing.lex_default =
   "\001\000\000\000\000\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\000\000";
  Lexing.lex_trans =
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\003\000\003\000\003\000\003\000\003\000\000\000\003\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \003\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\004\000\013\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\006\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\009\000\010\000\
    \007\000\011\000\008\000\012\000\000\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\000\000\
    \000\000\000\000\000\000\006\000\000\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\006\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\000\000\000\000\000\000\000\000\006\000\
    \002\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000";
  Lexing.lex_check =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\003\000\003\000\000\000\255\255\003\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\003\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\000\000\012\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\005\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\008\000\009\000\
    \004\000\010\000\007\000\011\000\255\255\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\255\255\
    \255\255\255\255\255\255\005\000\255\255\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\006\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\255\255\255\255\255\255\255\255\006\000\
    \000\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255";
  Lexing.lex_base_code =
   "";
  Lexing.lex_backtrk_code =
   "";
  Lexing.lex_default_code =
   "";
  Lexing.lex_trans_code =
   "";
  Lexing.lex_check_code =
   "";
  Lexing.lex_code =
   "";
}

let rec mllib_list lexbuf =
   __ocaml_lex_mllib_list_rec lexbuf 0
and __ocaml_lex_mllib_list_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 32 "tools/ocamllibdep.mll"
               ( let s = Lexing.lexeme lexbuf in
                 s :: mllib_list lexbuf )
# 156 "tools/ocamllibdep.ml"

  | 1 ->
# 34 "tools/ocamllibdep.mll"
                  ( let s = uncapitalize (Lexing.lexeme lexbuf)
		in s :: mllib_list lexbuf )
# 162 "tools/ocamllibdep.ml"

  | 2 ->
# 36 "tools/ocamllibdep.mll"
               ( mllib_list lexbuf )
# 167 "tools/ocamllibdep.ml"

  | 3 ->
# 37 "tools/ocamllibdep.mll"
           ( mllib_list lexbuf )
# 172 "tools/ocamllibdep.ml"

  | 4 ->
# 38 "tools/ocamllibdep.mll"
        ( [] )
# 177 "tools/ocamllibdep.ml"

  | 5 ->
# 39 "tools/ocamllibdep.mll"
      ( syntax_error lexbuf )
# 182 "tools/ocamllibdep.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_mllib_list_rec lexbuf __ocaml_lex_state

;;

# 41 "tools/ocamllibdep.mll"
 
open Printf
open Unix

(* Makefile's escaping rules are awful: $ is escaped by doubling and
   other special characters are escaped by backslash prefixing while
   backslashes themselves must be escaped only if part of a sequence
   followed by a special character (i.e. in case of ambiguity with a
   use of it as escaping character).  Moreover (even if not crucial)
   it is apparently not possible to directly escape ';' and leading '\t'. *)

let escape =
  let s' = Buffer.create 10 in
  fun s ->
    Buffer.clear s';
    for i = 0 to String.length s - 1 do
      let c = s.[i] in
      if c = ' ' || c = '#' || c = ':' (* separators and comments *)
        || c = '%' (* pattern *)
	|| c = '?' || c = '[' || c = ']' || c = '*' (* expansion in filenames *)
	|| i=0 && c = '~' && (String.length s = 1 || s.[1] = '/' || 
	    'A' <= s.[1] && s.[1] <= 'Z' || 
	    'a' <= s.[1] && s.[1] <= 'z') (* homedir expansion *)
      then begin
	let j = ref (i-1) in
	while !j >= 0 && s.[!j] = '\\' do 
	  Buffer.add_char s' '\\'; decr j (* escape all preceding '\' *)
	done;
	Buffer.add_char s' '\\';
      end;
      if c = '$' then Buffer.add_char s' '$';
      Buffer.add_char s' c
    done;
    Buffer.contents s'

(* Filename.concat but always with a '/' *)
let is_dir_sep s i =
  match Sys.os_type with
  | "Unix" -> s.[i] = '/'
  | "Cygwin" | "Win32" ->
    let c = s.[i] in c = '/' || c = '\\' || c = ':'
  | _ -> assert false

let (//) dirname filename =
  let l = String.length dirname in
  if l = 0 || is_dir_sep dirname (l-1)
  then dirname ^ filename
  else dirname ^ "/" ^ filename

(** [get_extension f l] checks whether [f] has one of the extensions
    listed in [l]. It returns [f] without its extension, alongside with
    the extension. When no extension match, [(f,"")] is returned *)

let rec get_extension f = function
  | [] -> (f, "")
  | s :: _ when Filename.check_suffix f s -> (Filename.chop_suffix f s, s)
  | _ :: l -> get_extension f l

let file_name s = function
  | None     -> s
  | Some "." -> s
  | Some d   -> d // s

type dir = string option

let add_directory add_file phys_dir =
  Array.iter (fun f ->
    (* we avoid all files starting by '.' *)
    if f.[0] <> '.' then
      let phys_f = if phys_dir = "." then f else phys_dir//f in
      match try (stat phys_f).st_kind with _ -> S_BLK with
      | S_REG -> add_file phys_dir f
      | _ -> ()) (Sys.readdir phys_dir)

let error_cannot_parse s (i,j) =
  Printf.eprintf "File \"%s\", characters %i-%i: Syntax error\n" s i j;
  exit 1

let same_path_opt s s' =
  let nf s = (* ./foo/a.ml and foo/a.ml are the same file *)
    if Filename.is_implicit s
    then "." // s
    else s
  in
  let s = match s with None -> "." | Some s -> nf s in
  let s' = match s' with None -> "." | Some s' -> nf s' in
  s = s'

let warning_ml_clash x s suff s' suff' =
  if suff = suff' && not (same_path_opt s s') then
  eprintf
    "*** Warning: %s%s already found in %s (discarding %s%s)\n" x suff
    (match s with None -> "." | Some d -> d)
    ((match s' with None -> "." | Some d -> d) // x) suff

let mkknown () =
  let h = (Hashtbl.create 19 : (string, dir * string) Hashtbl.t) in
  let add x s suff =
    try let s',suff' = Hashtbl.find h x in warning_ml_clash x s' suff' s suff
    with Not_found -> Hashtbl.add h x (s,suff)
  and search x =
    try Some (fst (Hashtbl.find h x))
    with Not_found -> None
  in add, search

let add_ml_known, search_ml_known = mkknown ()
let add_mlpack_known, search_mlpack_known = mkknown ()

let mllibAccu = ref ([] : (string * dir) list)
let mlpackAccu = ref ([] : (string * dir) list)

let add_caml_known phys_dir f =
  let basename,suff = get_extension f [".ml";".ml4";".mlpack"] in
  match suff with
    | ".ml"|".ml4" -> add_ml_known basename (Some phys_dir) suff
    | ".mlpack" -> add_mlpack_known basename (Some phys_dir) suff
    | _ -> ()

let add_caml_dir phys_dir =
  handle_unix_error (add_directory add_caml_known) phys_dir

let traite_fichier_modules md ext =
  try
    let chan = open_in (md ^ ext) in
    let list = mllib_list (Lexing.from_channel chan) in
    List.fold_left
      (fun acc str ->
       match search_mlpack_known str with
       | Some mldir -> (file_name str mldir) :: acc
       | None ->
	  match search_ml_known str with
	  | Some mldir -> (file_name str mldir) :: acc
	  | None -> acc) [] (List.rev list)
  with
    | Sys_error _ -> []
    | Syntax_error (i,j) -> error_cannot_parse (md^ext) (i,j)

let addQueue q v = q := v :: !q

let treat_file old_name =
  let name = Filename.basename old_name in
  let dirname = Some (Filename.dirname old_name) in
  match get_extension name [".mllib";".mlpack"] with
  | (base,".mllib") -> addQueue mllibAccu (base,dirname)
  | (base,".mlpack") -> addQueue mlpackAccu (base,dirname)
  | _ -> ()

let mllib_dependencies () =
  List.iter
    (fun (name,dirname) ->
       let fullname = file_name name dirname in
       let deps = traite_fichier_modules fullname ".mllib" in
       let sdeps = String.concat " " deps in
       let efullname = escape fullname in
       printf "%s_MLLIB_DEPENDENCIES:=%s\n" efullname sdeps;
       printf "%s.cma:$(addsuffix .cmo,$(%s_MLLIB_DEPENDENCIES))\n"
         efullname efullname;
       printf "%s.cmxa:$(addsuffix .cmx,$(%s_MLLIB_DEPENDENCIES))\n"
         efullname efullname;
       flush Pervasives.stdout)
    (List.rev !mllibAccu)

let mlpack_dependencies () =
  List.iter
    (fun (name,dirname) ->
       let fullname = file_name name dirname in
       let modname = capitalize name in
       let deps = traite_fichier_modules fullname ".mlpack" in
       let sdeps = String.concat " " deps in
       let efullname = escape fullname in
       printf "%s_MLPACK_DEPENDENCIES:=%s\n" efullname sdeps;
       List.iter (fun d -> printf "%s_FORPACK:= -for-pack %s\n" d modname) deps;
       printf "%s.cmo:$(addsuffix .cmo,$(%s_MLPACK_DEPENDENCIES))\n"
         efullname efullname;
       printf "%s.cmx:$(addsuffix .cmx,$(%s_MLPACK_DEPENDENCIES))\n"
         efullname efullname;
       flush Pervasives.stdout)
    (List.rev !mlpackAccu)

let rec parse = function
  | "-I" :: r :: ll ->
       (* To solve conflict (e.g. same filename in kernel and checker)
          we allow to state an explicit order *)
       add_caml_dir r;
       parse ll
  | f :: ll -> treat_file f; parse ll
  | [] -> ()

let main () =
  if Array.length Sys.argv < 2 then exit 1;
  parse (List.tl (Array.to_list Sys.argv));
  mllib_dependencies ();
  mlpack_dependencies ()

let _ = Printexc.catch main ()

# 386 "tools/ocamllibdep.ml"