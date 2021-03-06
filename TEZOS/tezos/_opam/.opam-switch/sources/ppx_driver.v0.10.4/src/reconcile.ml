open Import

module Context = struct
  type 'a t =
    | Extension          of 'a Extension.Context.t
    | Floating_attribute of 'a Attribute.Floating.Context.t

  let paren pp ppf x =
    Caml.Format.fprintf ppf "(%a)" pp x

  let printer
    : type a. a t -> Caml.Format.formatter -> a -> unit =
    let open Extension.Context in
    let open Attribute.Floating.Context in
    function
    | Extension Class_expr       -> Pprintast.class_expr
    | Extension Class_field      -> Pprintast.class_field
    | Extension Class_type       -> Pprintast.class_type
    | Extension Class_type_field -> Pprintast.class_type_field
    | Extension Core_type        -> paren Pprintast.core_type
    | Extension Expression       -> paren Pprintast.expression
    | Extension Module_expr      -> Pprintast.module_expr
    | Extension Module_type      -> Pprintast.module_type
    | Extension Pattern          -> paren Pprintast.pattern
    | Extension Signature_item   -> Pprintast.signature_item
    | Extension Structure_item   -> Pprintast.structure_item

    | Floating_attribute Structure_item   -> Pprintast.structure_item
    | Floating_attribute Signature_item   -> Pprintast.signature_item
    | Floating_attribute Class_field      -> Pprintast.class_field
    | Floating_attribute Class_type_field -> Pprintast.class_type_field
end

module Replacement = struct
  type t =
      T : { context        : 'a Context.t
          ; start          : Lexing.position
          ; stop           : Lexing.position
          ; generated      : 'a Context_free.Generated_code_hook.single_or_many
          ; is_expectation : bool
          } -> t

  let make ?(is_expectation=false) ~context ~start ~stop ~repl () =
    T { context; start; stop; generated = repl; is_expectation }

  let text =
    fun (T block) ->
      let printer = Context.printer block.context in
      let s =
        match block.generated with
        | Single x ->
          Caml.Format.asprintf "%a" printer x
        | Many l ->
          Caml.Format.asprintf "%a"
            (fun ppf l ->
               List.iter l ~f:(fun x ->
                 printer ppf x;
                 Caml.Format.pp_print_newline ppf ()))
            l
      in
      let is_ws = function (' '|'\t'|'\r') -> true | _ -> false in
      let strip_ws s i len =
        let len = ref len in
        while (!len > 0 && is_ws s.[i + !len - 1]) do len := !len - 1 done;
        String.sub s ~pos:i ~len:!len
      in
      let rec loop s pos =
        if pos >= String.length s
        then []
        else
          let idx =
            match String.index_from s pos '\n' with
            | Some i -> i
            | None -> String.length s
          in
          strip_ws s pos (idx - pos) :: "\n" :: loop s (idx + 1)
      in
      String.concat ~sep:"" (loop s 0)
end
open Replacement

module Replacements = struct
  type t = Replacement.t list

  (* Merge locations of the generated code. Overlapping locations are merged into one. The
     result is sorted from the beginning of the file to the end. *)
  let check_and_sort ~input_filename ~input_name repls =
    List.iter repls ~f:(fun (T repl) ->
      if String.(<>) repl.start.pos_fname input_name ||
         String.(<>) repl.stop .pos_fname input_name then
        Location.raise_errorf ~loc:(Location.in_file input_filename)
          "ppx_driver: the rewriting contains parts from another file.\n\
           It is too complicated to reconcile it with the source";
      assert (repl.start.pos_cnum <= repl.stop.pos_cnum));
    let repls =
      List.sort repls ~cmp:(fun (T a) (T b) ->
        let d = compare a.start.pos_cnum b.stop.pos_cnum in
        if d = 0 then
          (* Put the largest first, so that the following [filter] functions always picks up
             the lartest first when several generated repls start at the same position *)
          compare b.stop.pos_cnum a.stop.pos_cnum
        else
          d)
    in
    let rec filter (T prev) repls ~acc =
      match repls with
      | [] -> List.rev (T prev :: acc)
      | (T repl) :: repls ->
        if prev.stop.pos_cnum > repl.start.pos_cnum then begin
          if prev.stop.pos_cnum >= repl.stop.pos_cnum then
            (* [repl] is included in [prev] => skip [repl] *)
            filter (T prev) repls ~acc
          else
            Location.raise_errorf
              "ppx_driver: locations of generated code are overlapping, cannot reconcile"
              ~loc:{ loc_start = repl.start; loc_end = prev.stop; loc_ghost = false };
        end else
          filter (T repl) repls ~acc:(T prev :: acc)
    in
    match repls with
    | [] -> []
    | repl :: repls ->
      filter repl repls ~acc:[]
  ;;
end

let count_newlines s =
  let n = ref 0 in
  String.iter s ~f:(function
    | '\n' -> n := !n + 1
    | _    -> ());
  !n

let generated_code_begin =
  "(* -----{ GENERATED CODE BEGIN }------------------------------------- *)"
let generated_code_end =
  "(* -----{ GENERATED CODE END   }------------------------------------- *)"

type mode =
  | Using_line_directives
  | Delimiting_generated_blocks

type target =
  | Output of mode
  | Corrected

let skip_blank_eol contents (pos : Lexing.position) =
  let rec loop cnum =
    if cnum = String.length contents then
      { pos with pos_cnum = cnum }
    else
      match contents.[cnum] with
      | ' ' | '\t' | '\r' -> loop (cnum + 1)
      | '\n' ->
        { pos with
          pos_cnum = cnum + 1
        ; pos_lnum = pos.pos_lnum + 1
        ; pos_bol  = cnum + 1
        }
      | _ -> pos
  in
  loop pos.pos_cnum

let with_output ~styler ~(kind:Kind.t) fn ~f =
  match styler with
  | None -> with_output fn ~binary:false ~f
  | Some cmd ->
    let tmp_fn, oc =
      Caml.Filename.open_temp_file "ppx_driver"
        (match kind with Impl -> ".ml" | Intf -> ".mli")
    in
    let cmd =
      Printf.sprintf "%s %s%s" cmd (Caml.Filename.quote tmp_fn)
        (match fn with
         | None -> ""
         | Some fn -> " > " ^ Caml.Filename.quote fn)
    in
    let n =
      Exn.protectx tmp_fn ~finally:Caml.Sys.remove ~f:(fun _ ->
        Exn.protectx oc ~finally:Out_channel.close ~f:f;
        Caml.Sys.command cmd)
    in
    if n <> 0 then begin
      eprintf "command exited with code %d: %s\n" n cmd;
      Caml.exit 1
    end

let reconcile ?styler (repls : Replacements.t) ~kind ~contents ~input_filename
      ~output ~input_name ~target =
  let repls = Replacements.check_and_sort ~input_filename ~input_name repls in
  let output_name =
    match output with
    | None -> "<stdout>"
    | Some fn -> fn
  in
  with_output output ~styler ~kind ~f:(fun oc ->
    let copy_input pos ~up_to ~line =
      let pos = skip_blank_eol contents pos in
      if pos.pos_cnum < up_to then begin
        (match target with
         | Output Using_line_directives ->
           Out_channel.fprintf oc "# %d %S\n%*s" pos.pos_lnum input_name
             (pos.pos_cnum - pos.pos_bol) ""
         | Output Delimiting_generated_blocks | Corrected -> ());
        Out_channel.output_substring oc ~buf:contents ~pos:pos.pos_cnum ~len:(up_to - pos.pos_cnum);
        let line = ref (line + 1) in
        for i = pos.pos_cnum to up_to - 1 do
          if Char.equal contents.[i] '\n' then line := !line + 1
        done;
        let line = !line in
        if Char.(<>) contents.[up_to - 1] '\n' then
          (Out_channel.output_char oc '\n'; line + 1)
        else
          line
      end else
        line
    in
    let rec loop line (pos : Lexing.position) repls =
      match repls with
      | [] -> ignore (copy_input pos ~up_to:(String.length contents) ~line : int)
      | (T repl) :: repls ->
        let line = copy_input pos ~up_to:repl.start.pos_cnum ~line in
        let s = Replacement.text (T repl) in
        let line =
          match target with
          | Output Using_line_directives ->
            Out_channel.fprintf oc "# %d %S\n" (line + 1) output_name;
            line + 1
          | Output Delimiting_generated_blocks ->
            Out_channel.fprintf oc "%s\n" generated_code_begin;
            line + 1
          | Corrected ->
            line
        in
        Out_channel.output_string oc s;
        let line = line + count_newlines s in
        loop_consecutive_repls line repl.stop repls
    and loop_consecutive_repls line (pos : Lexing.position) repls =
      match repls with
      | [] -> end_consecutive_repls line pos repls
      | (T repl) :: repls' ->
        let pos = skip_blank_eol contents pos in
        if pos.pos_cnum < repl.start.pos_cnum then
          end_consecutive_repls line pos repls
        else begin
          let s = Replacement.text (T repl) in
          Out_channel.output_string oc s;
          let line = line + count_newlines s in
          loop_consecutive_repls line repl.stop repls'
        end
    and end_consecutive_repls line pos repls =
      (match target with
       | Output Using_line_directives | Corrected -> ()
       | Output Delimiting_generated_blocks ->
         Out_channel.fprintf oc "%s\n" generated_code_end);
      loop line pos repls
    in
    let pos =
      { Lexing.
        pos_fname = input_name
      ; pos_lnum  = 1
      ; pos_bol   = 0
      ; pos_cnum  = 0
      }
    in
    match repls with
    | (T { start = { pos_cnum = 0; _ }; _ }) :: _ ->
      (match target with
       | Output Using_line_directives | Corrected -> ()
       | Output Delimiting_generated_blocks ->
         Out_channel.fprintf oc "%s\n" generated_code_begin);
      loop_consecutive_repls 1 pos repls
    | _ ->
      loop 1 pos repls)
