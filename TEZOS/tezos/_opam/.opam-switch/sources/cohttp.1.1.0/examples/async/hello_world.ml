(* This file is in the public domain *)

open Core
open Async
open Cohttp_async

(* given filename: hello_world.ml compile with:
   $ corebuild hello_world.native -pkg cohttp.async
*)

let handler ~body:_ _sock req =
  let uri = Cohttp.Request.uri req in
  match Uri.path uri with
  | "/test" ->
       Uri.get_query_param uri "hello"
    |> Option.map ~f:(fun v -> "hello: " ^ v)
    |> Option.value ~default:"No param hello supplied"
    |> Server.respond_string
  | _ ->
    Server.respond_string ~status:`Not_found "Route not found"

let start_server port () =
  eprintf "Listening for HTTP on port %d\n" port;
  eprintf "Try 'curl http://localhost:%d/test?hello=xyz'\n%!" port;
  Cohttp_async.Server.create ~on_handler_error:`Raise
    (Tcp.Where_to_listen.of_port port) handler
  >>= fun _ -> Deferred.never ()

let () =
  Command.async_spec
    ~summary:"Start a hello world Async server"
    Command.Spec.(empty +>
      flag "-p" (optional_with_default 8080 int)
        ~doc:"int Source port to listen on"
    ) start_server

  |> Command.run
