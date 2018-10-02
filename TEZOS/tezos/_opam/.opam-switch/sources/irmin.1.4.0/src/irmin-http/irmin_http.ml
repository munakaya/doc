(*
 * Copyright (c) 2013-2017 Thomas Gazagnaire <thomas@gazagnaire.org>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

open Irmin_http_common
open Astring
open Lwt.Infix

let src = Logs.Src.create "irmin.http" ~doc:"Irmin HTTP REST interface"
module Log = (val Logs.src_log src : Logs.LOG)

module T = Irmin.Type

(* ~uri *)
let uri =
  Irmin.Private.Conf.key
    ~docv:"URI"
    ~doc:"Location of the remote store."
    "uri" Irmin.Private.Conf.(some uri) None

module Conf = Irmin.Private.Conf

let config ?(config=Irmin.Private.Conf.empty) x = Conf.add config uri (Some x)

let uri_append t path = match Uri.path t :: path with
  | []   -> t
  | path ->
    let buf = Buffer.create 10 in
    List.iter (function
        | "" -> ()
        | s  ->
          if s.[0] <> '/' then Buffer.add_char buf '/';
          Buffer.add_string buf s;
      ) path;
    let path = Buffer.contents buf in
    Uri.with_path t path

let err_no_uri () = invalid_arg "Irmin_http.create: No URI specified"

let get_uri config =
  match Conf.get config uri with
  | None   -> err_no_uri ()
  | Some u -> u

let invalid_arg fmt = Fmt.kstrf Lwt.fail_invalid_arg fmt

exception Escape of ((int * int) * (int * int)) * Jsonm.error

let json_stream (stream: string Lwt_stream.t): Jsonm.lexeme list Lwt_stream.t =
  let d = Jsonm.decoder `Manual in
  let rec lexeme () =
    match Jsonm.decode d with
    | `Lexeme l -> Lwt.return l
    | `Error e  -> Lwt.fail (Escape (Jsonm.decoded_range d, e))
    | `End      -> assert false
    | `Await    ->
      Lwt_stream.get stream >>= function
      | None    -> Lwt.fail (Escape (Jsonm.decoded_range d, (`Expected `Value)))
      | Some str ->
        Jsonm.Manual.src d (Bytes.of_string str) 0 (String.length str);
        lexeme ()
  in
  let lexemes e =
    let lexemes = ref [] in
    let objs = ref 0 in
    let arrs = ref 0 in
    let rec aux () =
      lexeme e >>= fun l ->
      lexemes := l :: !lexemes;
      let () = match l with
        | `Os -> incr objs
        | `As -> incr arrs
        | `Oe -> decr objs
        | `Ae -> decr arrs
        | `Name _
        | `Null
        | `Bool _
        | `String _
        | `Float _ -> ()
      in
      if !objs > 0 || !arrs > 0 then aux ()
      else Lwt.return ()
    in
    aux () >|= fun () ->
    List.rev !lexemes
  in
  let open_stream () =
    lexeme () >>= function
    | `As -> Lwt.return_unit
    | _   -> Lwt.fail (Escape (Jsonm.decoded_range d, `Expected (`Aval true)))
  in
  let opened = ref false in
  let open_and_get () =
    if not !opened then (
      open_stream () >>= fun () ->
      opened := true;
      lexemes () >|= fun ls -> Some ls
    ) else
      lexemes () >|= fun ls -> Some ls
  in
  Lwt_stream.from open_and_get

let of_json_string t str = T.decode_json t (Jsonm.decoder (`String str))
let to_json_string t = Fmt.to_to_string (T.pp_json t)

module Helper (Client: Cohttp_lwt.S.Client) = struct

  let err_bad_version v =
    invalid_arg "bad server version: expecting %s, but got %s"
      Irmin.version (match v with None -> "<none>" | Some v -> v)

  let check_version r =
    match Cohttp.Header.get (Cohttp.Response.headers r) irmin_version with
    | None   -> err_bad_version None
    | Some v ->
      if v <> Irmin.version then err_bad_version (Some v)
      else Lwt.return_unit

  let is_success r = match Cohttp.Response.status r with
    | `OK -> true
    | _  -> false

  let map_string_response parse (r, b) =
    check_version r >>= fun () ->
    Cohttp_lwt.Body.to_string b >>= fun b ->
    if is_success r then
      match parse b with
      | Ok x           -> Lwt.return x
      | Error (`Msg e) ->
        Lwt.fail_with (Fmt.strf "Error while parsing %S: %s" b e)
    else
      Lwt.fail_with ("Server error: " ^ b)

  let map_stream_response t (r, b) =
    check_version r >>= fun () ->
    if not (is_success r) then
      Cohttp_lwt.Body.to_string b >>= fun b ->
      Lwt.fail_with ("Server error: " ^ b)
    else
      let stream = Cohttp_lwt.Body.to_stream b in
      let stream = json_stream stream in
      let stream =
        let aux j =
          match T.decode_json_lexemes t j with
          | Error (`Msg e) -> Lwt.fail_with e
          | Ok c           -> Lwt.return c
        in
        Lwt_stream.map_s aux stream
      in
      Lwt.return stream

  let headers = Cohttp.Header.of_list [
      "Connection"  , "Keep-Alive";
      irmin_version , Irmin.version;
      "Content-type", "application/json";
    ]

  let map_call meth t ?body path fn =
    let uri = uri_append t path in
    let body = match body with None -> None | Some b -> Some (`String b) in
    Log.debug  (fun f ->
        f "%s %s" (Cohttp.Code.string_of_method meth) (Uri.path uri)
      );
    Client.call meth ~headers ?body uri >>= fn

  let call meth t ?body  path parse =
    map_call meth t ?body path (map_string_response parse)

  let call_stream meth t ?body path parse =
    map_call meth t ?body path (map_stream_response parse)

end

module RO (Client: Cohttp_lwt.S.Client)
    (K: Irmin.Contents.Conv)
    (V: Irmin.Contents.Conv)
= struct

  module HTTP = Helper (Client)

  type t = { uri: Uri.t; item: string; items: string }
  let uri t = t.uri
  let item t = t.item
  let items t = t.items

  type key = K.t
  type value = V.t

  let key_str = Fmt.to_to_string K.pp

  let find t key =
    HTTP.map_call `GET t.uri [t.item; key_str key] (fun (r, _ as x) ->
        if Cohttp.Response.status r = `Not_found then Lwt.return_none
        else HTTP.map_string_response V.of_string x >|= fun x -> Some x)

  let mem t key =
    HTTP.map_call `GET t.uri [t.item; key_str key] (fun (r, _ ) ->
        if Cohttp.Response.status r = `Not_found then Lwt.return_false
        else Lwt.return_true)

  let v uri item items =
    Lwt.return { uri; item; items }

end

module AO (Client: Cohttp_lwt.S.Client)
    (K: Irmin.Hash.S)
    (V: Irmin.Contents.Conv) =
struct
  include RO (Client)(K)(V)
  let add t value =
    let body = Fmt.to_to_string V.pp value in
    HTTP.call `POST t.uri [t.items] ~body K.of_string
end

module RW (Client: Cohttp_lwt.S.Client)
    (K: Irmin.Contents.Conv)
    (V: Irmin.Contents.Conv)
= struct

  module RO = RO (Client)(K)(V)
  module HTTP = RO.HTTP
  module W  = Irmin.Private.Watch.Make(K)(V)

  type key = RO.key
  type value = RO.value
  type watch = W.watch

  (* cache the stream connections to the server: we open only one
     connection per stream kind. *)
  type cache = { mutable stop: unit -> unit; }

  let empty_cache () = { stop = fun () -> (); }

  type t = { t: RO.t; w: W.t; keys: cache; glob: cache }

  let get t = HTTP.call `GET (RO.uri t.t)
  let put t = HTTP.call `PUT (RO.uri t.t)
  let get_stream t = HTTP.call_stream `GET (RO.uri t.t)
  let post_stream t = HTTP.call_stream `POST (RO.uri t.t)

  let v uri item items =
    RO.v uri item items >>= fun t ->
    let w = W.v () in
    let keys = empty_cache () in
    let glob = empty_cache () in
    Lwt.return { t; w; keys; glob }

  let find t = RO.find t.t
  let mem t = RO.mem t.t
  let key_str = Fmt.to_to_string K.pp
  let list t = get t [RO.items t.t] (of_json_string T.(list K.t))

  let set t key value =
    let value = { v = Some value; set = None; test = None } in
    let body = to_json_string (set_t V.t) value in
    put t [RO.item t.t; key_str key] ~body (of_json_string status_t)
    >>= function
    | "ok" -> Lwt.return_unit
    | e    -> Lwt.fail_with e

  let test_and_set t key ~test ~set =
    let value = { v = None; set; test } in
    let body = to_json_string (set_t V.t) value in
    put t [RO.item t.t; key_str key] ~body (of_json_string status_t)
    >>= function
    | "true"  -> Lwt.return true
    | "false" -> Lwt.return false
    | e       -> Lwt.fail_with e

  let remove t key =
    HTTP.map_call `DELETE (RO.uri t.t) [RO.item t.t; key_str key] (fun (r, b) ->
        match Cohttp.Response.status r with
        | `Not_found | `OK -> Lwt.return_unit
        | _ ->
          Cohttp_lwt.Body.to_string b >>= fun b ->
          Fmt.kstrf Lwt.fail_with "cannot remove %a: %s" K.pp key b
      )

  let nb_keys t = fst (W.stats t.w)
  let nb_glob t = snd (W.stats t.w)

  (* run [t] and returns an handler to stop the task. *)
  let stoppable t =
    let s, u = Lwt.task () in
    Lwt.async (fun () -> Lwt.pick ([s; t ()]));
    function () -> Lwt.wakeup u ()

  let watch_key t key ?init f =
    let key_str = Fmt.to_to_string K.pp key in
    let init_stream () =
      if nb_keys t <> 0 then Lwt.return_unit
      else
        (match init with
         | None      -> get_stream t ["watch"; key_str] (event_t K.t V.t)
         | Some init ->
           let body = to_json_string V.t init in
           post_stream t ["watch"; key_str] ~body (event_t K.t V.t))
        >>= fun s ->
        let stop () =
          Lwt_stream.iter_s (fun (_, v) ->
              let v = match v with
                | `Removed _ -> None
                | `Added v | `Updated (_, v) -> Some v
              in
              W.notify t.w key v
            ) s
        in
        t.keys.stop <- stoppable stop;
        Lwt.return_unit
    in
    init_stream () >>= fun () ->
    W.watch_key t.w key ?init f

  let watch t ?init f =
    let init_stream () =
      if nb_glob t <> 0 then Lwt.return_unit
      else
        (match init with
         | None      -> get_stream t ["watches"] (event_t K.t V.t)
         | Some init ->
           let body = to_json_string T.(list (init_t K.t V.t)) init in
           post_stream t ["watches"] ~body (event_t K.t V.t))
        >>= fun s ->
        let stop () =
          Lwt_stream.iter_s (fun (k, v) ->
              let v = match v with
                | `Removed _ -> None
                | `Added v | `Updated (_, v) -> Some v
              in
              W.notify t.w k v
            ) s
        in
        t.glob.stop <- stoppable stop;
        Lwt.return_unit
    in
    init_stream () >>= fun () ->
    W.watch t.w ?init f

  let stop x =
    let () = try x.stop () with _e -> () in
    x.stop <- fun () -> ()

  let unwatch t id =
    W.unwatch t.w id >>= fun () ->
    if nb_keys t = 0 then stop t.keys;
    if nb_glob t = 0 then stop t.glob;
    Lwt.return_unit

end

module Make
    (Client: Cohttp_lwt.S.Client)
    (M: Irmin.Metadata.S)
    (C: Irmin.Contents.S)
    (P: Irmin.Path.S)
    (B: Irmin.Branch.S)
    (H: Irmin.Hash.S) =
struct
  module X = struct
    module XContents = struct
      module Key = H
      module Val = C
      include AO(Client)(H)(C)
      let v config = v config "blob" "blobs"
    end
    module Contents = Irmin.Contents.Store(XContents)
    module Node = struct
      module X = struct
        module Key = H
        module Val = struct
          include Irmin.Private.Node.Make(H)(H)(P)(M)
          let pp = T.pp_json t
          let of_string = of_json_string t
        end
        include AO(Client)(Key)(Val)
      end
      include Irmin.Private.Node.Store(Contents)(P)(M)(X)
      let v config = X.v config "tree" "trees"
    end
    module Commit = struct
      module X = struct
        module Key = H
        module Val = struct
          include Irmin.Private.Commit.Make(H)(H)
          let pp = T.pp_json t
          let of_string = of_json_string t
        end
        include AO(Client)(Key)(Val)
      end
      include Irmin.Private.Commit.Store(Node)(X)
      let v config = X.v config "commit" "commits"
    end
    module Branch = struct
      module Key = B
      module Val = H
      include RW(Client)(Key)(Val)
      let v config = v config "branch" "branches"
    end
    module Slice = Irmin.Private.Slice.Make(Contents)(Node)(Commit)
    module Sync = Irmin.Private.Sync.None(H)(B)
    module Repo = struct
      type t = {
        config: Irmin.config;
        contents: Contents.t;
        node: Node.t;
        commit: Commit.t;
        branch: Branch.t;
      }
      let branch_t t = t.branch
      let commit_t t = t.commit
      let node_t t = t.node
      let contents_t t = t.contents

      let v config =
        let uri = get_uri config in
        XContents.v uri >>= fun contents ->
        Node.v uri      >>= fun node ->
        Commit.v uri    >>= fun commit ->
        Branch.v uri    >|= fun branch ->
        let node = contents, node in
        let commit = node, commit in
        { contents; node; commit; branch; config }

    end
  end
  include Irmin.Make_ext(X)
end

module KV (H: Cohttp_lwt.S.Client) (C: Irmin.Contents.S) =
  Make (H)
    (Irmin.Metadata.None)
    (C)
    (Irmin.Path.String_list)
    (Irmin.Branch.String)
    (Irmin.Hash.SHA1)
