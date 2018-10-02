(*****************************************************************************)
(*                                                                           *)
(* Open Source License                                                       *)
(* Copyright (c) 2018 Dynamic Ledger Solutions, Inc. <contact@tezos.com>     *)
(*                                                                           *)
(* Permission is hereby granted, free of charge, to any person obtaining a   *)
(* copy of this software and associated documentation files (the "Software"),*)
(* to deal in the Software without restriction, including without limitation *)
(* the rights to use, copy, modify, merge, publish, distribute, sublicense,  *)
(* and/or sell copies of the Software, and to permit persons to whom the     *)
(* Software is furnished to do so, subject to the following conditions:      *)
(*                                                                           *)
(* The above copyright notice and this permission notice shall be included   *)
(* in all copies or substantial portions of the Software.                    *)
(*                                                                           *)
(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR*)
(* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,  *)
(* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL   *)
(* THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER*)
(* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING   *)
(* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER       *)
(* DEALINGS IN THE SOFTWARE.                                                 *)
(*                                                                           *)
(*****************************************************************************)

let (//) = Filename.concat

let home =
  try Sys.getenv "HOME"
  with Not_found -> "/root"

let default_data_dir = home // ".tezos-node"
let default_p2p_port = 9732
let default_rpc_port = 8732

type t = {
  data_dir : string ;
  p2p : p2p ;
  rpc : rpc ;
  log : log ;
  shell : shell ;
}

and p2p = {
  expected_pow : float ;
  bootstrap_peers : string list ;
  listen_addr : string option ;
  private_mode : bool ;
  limits : P2p.limits ;
  disable_mempool : bool ;
}

and rpc = {
  listen_addr : string option ;
  cors_origins : string list ;
  cors_headers : string list ;
  tls : tls option ;
}

and tls = {
  cert : string ;
  key : string ;
}

and log = {
  output : Logging_unix.Output.t ;
  default_level : Logging.level ;
  rules : string option ;
  template : Logging.template ;
}

and shell = {
  block_validator_limits : Node.block_validator_limits ;
  prevalidator_limits : Node.prevalidator_limits ;
  peer_validator_limits : Node.peer_validator_limits ;
  chain_validator_limits : Node.chain_validator_limits ;
}

let default_p2p_limits : P2p.limits = {
  connection_timeout = 10. ;
  authentication_timeout = 5. ;
  greylist_timeout = 86400 ; (* one day *)
  min_connections = 10 ;
  expected_connections = 50 ;
  max_connections = 100 ;
  backlog = 20 ;
  max_incoming_connections = 20 ;
  max_download_speed = None ;
  max_upload_speed = None ;
  read_buffer_size = 1 lsl 14 ;
  read_queue_size = None ;
  write_queue_size = None ;
  incoming_app_message_queue_size = None ;
  incoming_message_queue_size = None ;
  outgoing_message_queue_size = None ;
  known_points_history_size = 500 ;
  known_peer_ids_history_size = 500 ;
  max_known_points = Some (400, 300) ;
  max_known_peer_ids = Some (400, 300) ;
  swap_linger = 30. ;
  binary_chunks_size = None ;
}

let default_p2p = {
  expected_pow = 26. ;
  bootstrap_peers  = [ "boot.tzbeta.net" ] ;
  listen_addr  = Some ("[::]:" ^ string_of_int default_p2p_port) ;
  private_mode  = false ;
  limits = default_p2p_limits ;
  disable_mempool = false ;
}

let default_rpc = {
  listen_addr = None ;
  cors_origins = [] ;
  cors_headers = [] ;
  tls = None ;
}

let default_log = {
  output = Stderr ;
  default_level = Notice ;
  rules = None ;
  template = Logging.default_template ;
}

let default_shell = {
  block_validator_limits = Node.default_block_validator_limits ;
  prevalidator_limits = Node.default_prevalidator_limits ;
  peer_validator_limits = Node.default_peer_validator_limits ;
  chain_validator_limits = Node.default_chain_validator_limits ;
}

let default_config = {
  data_dir = default_data_dir ;
  p2p = default_p2p ;
  rpc = default_rpc ;
  log = default_log ;
  shell = default_shell ;
}

let limit : P2p.limits Data_encoding.t =
  let open Data_encoding in
  conv
    (fun { P2p.connection_timeout ; authentication_timeout ; greylist_timeout ;
           min_connections ; expected_connections ; max_connections ;
           backlog ; max_incoming_connections ;
           max_download_speed ; max_upload_speed ;
           read_buffer_size ; read_queue_size ; write_queue_size ;
           incoming_app_message_queue_size ;
           incoming_message_queue_size ; outgoing_message_queue_size ;
           known_points_history_size ; known_peer_ids_history_size ;
           max_known_points ; max_known_peer_ids ;
           swap_linger ; binary_chunks_size
         } ->
      (((( connection_timeout, authentication_timeout,
           min_connections, expected_connections,
           max_connections, backlog, max_incoming_connections,
           max_download_speed, max_upload_speed, swap_linger),
         ( binary_chunks_size, read_buffer_size, read_queue_size, write_queue_size,
           incoming_app_message_queue_size,
           incoming_message_queue_size, outgoing_message_queue_size,
           known_points_history_size, known_peer_ids_history_size,
           max_known_points)),
        (  max_known_peer_ids, greylist_timeout))))
    (fun (((( connection_timeout, authentication_timeout,
              min_connections, expected_connections,
              max_connections, backlog, max_incoming_connections,
              max_download_speed, max_upload_speed, swap_linger),
            ( binary_chunks_size, read_buffer_size, read_queue_size, write_queue_size,
              incoming_app_message_queue_size,
              incoming_message_queue_size, outgoing_message_queue_size,
              known_points_history_size, known_peer_ids_history_size,
              max_known_points)),
           (  max_known_peer_ids, greylist_timeout))) ->
      { connection_timeout ; authentication_timeout ; greylist_timeout ;
        min_connections ; expected_connections ;
        max_connections ; backlog ; max_incoming_connections ;
        max_download_speed ; max_upload_speed ;
        read_buffer_size ; read_queue_size ; write_queue_size ;
        incoming_app_message_queue_size ;
        incoming_message_queue_size ; outgoing_message_queue_size ;
        known_points_history_size ; known_peer_ids_history_size ;
        max_known_points ; max_known_peer_ids ; swap_linger ;
        binary_chunks_size
      })
    (merge_objs
       (merge_objs
          (obj10
             (dft "connection-timeout"
                ~description: "Delay acceptable when initiating a \
                               connection to a new peer, in seconds."
                float default_p2p_limits.authentication_timeout)
             (dft "authentication-timeout"
                ~description: "Delay granted to a peer to perform authentication, \
                               in seconds."
                float default_p2p_limits.authentication_timeout)
             (dft "min-connections"
                ~description: "Strict minimum number of connections (triggers an \
                               urgent maintenance)."
                uint16
                default_p2p_limits.min_connections)
             (dft "expected-connections"
                ~description: "Targeted number of connections to reach when \
                               bootstrapping / maintaining."
                uint16
                default_p2p_limits.expected_connections)
             (dft "max-connections"
                ~description: "Maximum number of connections (exceeding peers are \
                               disconnected)."
                uint16
                default_p2p_limits.max_connections)
             (dft "backlog"
                ~description: "Number above which pending incoming connections are \
                               immediately rejected."
                uint8
                default_p2p_limits.backlog)
             (dft "max-incoming-connections"
                ~description: "Number above which pending incoming connections are \
                               immediately rejected."
                uint8
                default_p2p_limits.max_incoming_connections)
             (opt "max-download-speed"
                ~description: "Max download speeds in KiB/s."
                int31)
             (opt "max-upload-speed"
                ~description: "Max upload speeds in KiB/s."
                int31)
             (dft "swap-linger" float default_p2p_limits.swap_linger))
          (obj10
             (opt "binary-chunks-size" uint8)
             (dft "read-buffer-size"
                ~description: "Size of the buffer passed to read(2)."
                int31
                default_p2p_limits.read_buffer_size)
             (opt "read-queue-size" int31)
             (opt "write-queue-size" int31)
             (opt "incoming-app-message-queue-size" int31)
             (opt "incoming-message-queue-size" int31)
             (opt "outgoing-message-queue-size" int31)
             (dft "known_points_history_size" uint16
                default_p2p_limits.known_points_history_size)
             (dft "known_peer_ids_history_size" uint16
                default_p2p_limits.known_points_history_size)
             (opt "max_known_points" (tup2 uint16 uint16))
          ))
       (obj2
          (opt "max_known_peer_ids" (tup2 uint16 uint16))
          (dft "greylist-timeout"
             ~description: "GC delay for the greylists tables, in seconds."
             int31 default_p2p_limits.greylist_timeout)

       ))

let p2p =
  let open Data_encoding in
  conv
    (fun { expected_pow ; bootstrap_peers ;
           listen_addr ; private_mode ; limits ; disable_mempool } ->
      ( expected_pow, bootstrap_peers,
        listen_addr, private_mode, limits, disable_mempool ))
    (fun ( expected_pow, bootstrap_peers,
           listen_addr, private_mode, limits, disable_mempool ) ->
      { expected_pow ; bootstrap_peers ;
        listen_addr ; private_mode ; limits ; disable_mempool })
    (obj6
       (dft "expected-proof-of-work"
          ~description: "Floating point number between 0 and 256 that represents a \
                         difficulty, 24 signifies for example that at least 24 leading \
                         zeroes are expected in the hash."
          float default_p2p.expected_pow)
       (dft "bootstrap-peers"
          ~description: "List of hosts. Tezos can connect to both IPv6 and IPv4 hosts. \
                         If the port is not specified, default port 9732 will be assumed."
          (list string) default_p2p.bootstrap_peers)
       (opt "listen-addr"
          ~description: "Host to listen to. If the port is not \
                         specified, the default port 8732 will be \
                         assumed."
          string)
       (dft "private-mode"
          ~description: "Specify if the node is in private mode or \
                         not. A node in private mode rejects incoming \
                         connections from untrusted peers and only \
                         opens outgoing connections to peers listed in \
                         'bootstrap-peers' or provided with '--peer' \
                         option. Moreover, these peers will keep the \
                         identity and the address of the private node \
                         secret."
          bool false)
       (dft "limits"
          ~description: "Network limits"
          limit default_p2p_limits)
       (dft "disable_mempool"
          ~description: "If set to [true], the node will not participate in \
                         the propagation of pending operations (mempool). \
                         Default value is [false]. \
                         It can be used to decrease the memory and \
                         computation footprints of the node."
          bool false)
    )

let rpc : rpc Data_encoding.t =
  let open Data_encoding in
  conv
    (fun { cors_origins ; cors_headers ; listen_addr ; tls } ->
       let cert, key =
         match tls with
         | None -> None, None
         | Some { cert ; key } -> Some cert, Some key in
       (listen_addr, cors_origins, cors_headers, cert, key ))
    (fun (listen_addr, cors_origins, cors_headers, cert, key ) ->
       let tls =
         match cert, key with
         | None, _ | _, None -> None
         | Some cert, Some key -> Some { cert ; key } in
       { listen_addr ; cors_origins ; cors_headers ; tls })
    (obj5
       (opt "listen-addr"
          ~description: "Host to listen to. If the port is not specified, \
                         the default port 8732 will be assumed."
          string)
       (dft "cors-origin"
          ~description: "Cross Origin Resource Sharing parameters, see \
                         https://en.wikipedia.org/wiki/Cross-origin_resource_sharing."
          (list string) default_rpc.cors_origins)
       (dft "cors-headers"
          ~description: "Cross Origin Resource Sharing parameters, see \
                         https://en.wikipedia.org/wiki/Cross-origin_resource_sharing."
          (list string) default_rpc.cors_headers)
       (opt "crt"
          ~description: "Certificate file (necessary when TLS is used)."
          string)
       (opt "key"
          ~description: "Key file (necessary when TLS is used)."
          string)
    )

let level_encoding =
  let open Logging in
  let open Data_encoding in
  conv
    (function
      | Fatal -> "fatal"
      | Error -> "error"
      | Warning -> "warning"
      | Notice -> "notice"
      | Info -> "info"
      | Debug -> "debug")
    (function
      | "error" -> Error
      | "warn" -> Warning
      | "notice" -> Notice
      | "info" -> Info
      | "debug" -> Debug
      | "fatal" -> Fatal
      | _ -> invalid_arg "Logging.level")
    string

let log =
  let open Data_encoding in
  conv
    (fun {output ; default_level ; rules ; template } ->
       (output, default_level, rules, template))
    (fun (output, default_level, rules, template) ->
       { output ; default_level ; rules ; template })
    (obj4
       (dft "output"
          ~description: "Output for the logging function. Either 'stdout', \
                         'stderr' or the name of a log file ."
          Logging_unix.Output.encoding default_log.output)
       (dft "level"
          ~description: "Verbosity level: one of 'fatal', 'error', 'warn',\
                         'notice', 'info', 'debug'."
          level_encoding default_log.default_level)
       (opt "rules"
          ~description: "Fine-grained logging instructions. Same format as \
                         described in `tezos-node run --help`, DEBUG section. \
                         In the example below, sections 'p2p' and all sections \
                         starting by 'client' will have their messages logged \
                         up to the debug level, whereas the rest of log sections \
                         will be logged up to the notice level."
          string)
       (dft "template"
          ~description: "Format for the log file, see \
                         http://ocsigen.org/lwt/dev/api/Lwt_log_core#2_Logtemplates."
          string default_log.template)
    )


let worker_limits_encoding
    default_size
    default_level
    default_zombie_lifetime
    default_zombie_memory =
  let open Data_encoding in
  conv
    (fun { Worker_types.backlog_size ; backlog_level ; zombie_lifetime ; zombie_memory } ->
       (backlog_size, backlog_level, zombie_lifetime, zombie_memory))
    (fun (backlog_size, backlog_level, zombie_lifetime, zombie_memory) ->
       { backlog_size ; backlog_level ; zombie_lifetime ; zombie_memory })
    (obj4
       (dft "worker_backlog_size" uint16 default_size)
       (dft "worker_backlog_level" level_encoding default_level)
       (dft "worker_zombie_lifetime" float default_zombie_lifetime)
       (dft "worker_zombie_memory" float default_zombie_memory))

let timeout_encoding =
  Data_encoding.ranged_float 0. 500.

let block_validator_limits_encoding =
  let open Data_encoding in
  conv
    (fun { Node.protocol_timeout ; worker_limits } ->
       (protocol_timeout, worker_limits))
    (fun (protocol_timeout, worker_limits) ->
       { protocol_timeout ; worker_limits})
    (merge_objs
       (obj1
          (dft "protocol_request_timeout" timeout_encoding
             default_shell.block_validator_limits.protocol_timeout))
       (worker_limits_encoding
          default_shell.block_validator_limits.worker_limits.backlog_size
          default_shell.block_validator_limits.worker_limits.backlog_level
          default_shell.block_validator_limits.worker_limits.zombie_lifetime
          default_shell.block_validator_limits.worker_limits.zombie_memory))

let prevalidator_limits_encoding =
  let open Data_encoding in
  conv
    (fun { Node.operation_timeout ; max_refused_operations ; worker_limits } ->
       ((operation_timeout, max_refused_operations), worker_limits))
    (fun ((operation_timeout, max_refused_operations), worker_limits) ->
       { operation_timeout ; max_refused_operations ; worker_limits})
    (merge_objs
       (obj2
          (dft "operations_request_timeout" timeout_encoding
             default_shell.prevalidator_limits.operation_timeout)
          (dft "max_refused_operations" uint16
             default_shell.prevalidator_limits.max_refused_operations))
       (worker_limits_encoding
          default_shell.prevalidator_limits.worker_limits.backlog_size
          default_shell.prevalidator_limits.worker_limits.backlog_level
          default_shell.prevalidator_limits.worker_limits.zombie_lifetime
          default_shell.prevalidator_limits.worker_limits.zombie_memory))

let peer_validator_limits_encoding =
  let open Data_encoding in
  let default_limits = default_shell.peer_validator_limits in
  conv
    (fun { Node.block_header_timeout ; block_operations_timeout ;
           protocol_timeout ; new_head_request_timeout ; worker_limits } ->
      ((block_header_timeout, block_operations_timeout,
        protocol_timeout, new_head_request_timeout), worker_limits))
    (fun ((block_header_timeout, block_operations_timeout,
           protocol_timeout, new_head_request_timeout), worker_limits) ->
      { block_header_timeout ; block_operations_timeout ;
        protocol_timeout ; new_head_request_timeout ; worker_limits })
    (merge_objs
       (obj4
          (dft "block_header_request_timeout" timeout_encoding default_limits.block_header_timeout)
          (dft "block_operations_request_timeout" timeout_encoding default_limits.block_operations_timeout)
          (dft "protocol_request_timeout" timeout_encoding default_limits.protocol_timeout)
          (dft "new_head_request_timeout" timeout_encoding default_limits.new_head_request_timeout))
       (worker_limits_encoding
          default_limits.worker_limits.backlog_size
          default_limits.worker_limits.backlog_level
          default_limits.worker_limits.zombie_lifetime
          default_limits.worker_limits.zombie_memory))

let chain_validator_limits_encoding =
  let open Data_encoding in
  conv
    (fun { Node.bootstrap_threshold ; worker_limits } ->
       (bootstrap_threshold, worker_limits))
    (fun (bootstrap_threshold, worker_limits) ->
       { bootstrap_threshold ; worker_limits})
    (merge_objs
       (obj1
          (dft "bootstrap_threshold"
             ~description:
               "Set the number of peers with whom a chain synchronization must \
                be completed to bootstrap the node."
             uint8
             default_shell.chain_validator_limits.bootstrap_threshold))
       (worker_limits_encoding
          default_shell.chain_validator_limits.worker_limits.backlog_size
          default_shell.chain_validator_limits.worker_limits.backlog_level
          default_shell.chain_validator_limits.worker_limits.zombie_lifetime
          default_shell.chain_validator_limits.worker_limits.zombie_memory))

let shell =
  let open Data_encoding in
  conv
    (fun { peer_validator_limits ; block_validator_limits ;
           prevalidator_limits ; chain_validator_limits } ->
      (peer_validator_limits, block_validator_limits,
       prevalidator_limits, chain_validator_limits))
    (fun (peer_validator_limits, block_validator_limits,
          prevalidator_limits, chain_validator_limits) ->
      { peer_validator_limits ; block_validator_limits ;
        prevalidator_limits ; chain_validator_limits })
    (obj4
       (dft "peer_validator" peer_validator_limits_encoding default_shell.peer_validator_limits)
       (dft "block_validator" block_validator_limits_encoding default_shell.block_validator_limits)
       (dft "prevalidator" prevalidator_limits_encoding default_shell.prevalidator_limits)
       (dft "chain_validator" chain_validator_limits_encoding default_shell.chain_validator_limits)
    )

let encoding =
  let open Data_encoding in
  conv
    (fun { data_dir ; rpc ; p2p ; log ; shell } ->
       (data_dir, rpc, p2p, log, shell))
    (fun (data_dir, rpc, p2p, log, shell) ->
       { data_dir ; rpc ; p2p ; log ; shell })
    (obj5
       (dft "data-dir"
          ~description: "Location of the data dir on disk."
          string default_data_dir)
       (dft "rpc"
          ~description: "Configuration of rpc parameters"
          rpc default_rpc)
       (req "p2p"
          ~description: "Configuration of network parameters" p2p)
       (dft "log"
          ~description: "Configuration of network parameters"
          log default_log)
       (dft "shell"
          ~description: "Configuration of network parameters"
          shell default_shell))

let read fp =
  if Sys.file_exists fp then begin
    Lwt_utils_unix.Json.read_file fp >>=? fun json ->
    try return (Data_encoding.Json.destruct encoding json)
    with exn -> fail (Exn exn)
  end else
    return default_config

let write fp cfg =
  Node_data_version.ensure_data_dir (Filename.dirname fp) >>=? fun () ->
  Lwt_utils_unix.Json.write_file fp
    (Data_encoding.Json.construct encoding cfg)

let to_string cfg =
  Data_encoding.Json.to_string
    (Data_encoding.Json.construct encoding cfg)

let update
    ?data_dir
    ?min_connections
    ?expected_connections
    ?max_connections
    ?max_download_speed
    ?max_upload_speed
    ?binary_chunks_size
    ?peer_table_size
    ?expected_pow
    ?bootstrap_peers
    ?listen_addr
    ?rpc_listen_addr
    ?(private_mode = false)
    ?(disable_mempool = false)
    ?(cors_origins = [])
    ?(cors_headers = [])
    ?rpc_tls
    ?log_output
    ?bootstrap_threshold
    cfg = let data_dir = Option.unopt ~default:cfg.data_dir data_dir in
  Node_data_version.ensure_data_dir data_dir >>=? fun () ->
  let peer_table_size =
    Option.map peer_table_size ~f:(fun i -> i, i / 4 * 3) in
  let unopt_list ~default = function
    | [] -> default
    | l -> l in
  let limits : P2p.limits = {
    cfg.p2p.limits with
    min_connections =
      Option.unopt
        ~default:cfg.p2p.limits.min_connections
        min_connections ;
    expected_connections =
      Option.unopt
        ~default:cfg.p2p.limits.expected_connections
        expected_connections ;
    max_connections =
      Option.unopt
        ~default:cfg.p2p.limits.max_connections
        max_connections ;
    max_download_speed =
      Option.first_some
        max_download_speed cfg.p2p.limits.max_download_speed ;
    max_upload_speed =
      Option.first_some
        max_upload_speed cfg.p2p.limits.max_upload_speed ;
    max_known_points =
      Option.first_some
        peer_table_size cfg.p2p.limits.max_known_points ;
    max_known_peer_ids =
      Option.first_some
        peer_table_size cfg.p2p.limits.max_known_peer_ids ;
    binary_chunks_size =
      Option.map ~f:(fun x -> x lsl 10) binary_chunks_size ;
  } in
  let p2p : p2p = {
    expected_pow =
      Option.unopt ~default:cfg.p2p.expected_pow expected_pow ;
    bootstrap_peers =
      Option.unopt ~default:cfg.p2p.bootstrap_peers bootstrap_peers ;
    listen_addr =
      Option.first_some listen_addr cfg.p2p.listen_addr ;
    private_mode = cfg.p2p.private_mode || private_mode ;
    limits ;
    disable_mempool = cfg.p2p.disable_mempool || disable_mempool ;
  }
  and rpc : rpc = {
    listen_addr =
      Option.first_some rpc_listen_addr cfg.rpc.listen_addr ;
    cors_origins =
      unopt_list ~default:cfg.rpc.cors_origins cors_origins ;
    cors_headers =
      unopt_list ~default:cfg.rpc.cors_headers cors_headers ;
    tls =
      Option.first_some rpc_tls cfg.rpc.tls ;
  }
  and log : log = {
    cfg.log with
    output = Option.unopt ~default:cfg.log.output log_output ;
  }
  and shell : shell = {
    peer_validator_limits = cfg.shell.peer_validator_limits ;
    block_validator_limits = cfg.shell.block_validator_limits ;
    prevalidator_limits = cfg.shell.prevalidator_limits ;
    chain_validator_limits =
      Option.unopt_map
        ~default:cfg.shell.chain_validator_limits
        ~f:(fun bootstrap_threshold ->
            { cfg.shell.chain_validator_limits
              with bootstrap_threshold })
        bootstrap_threshold
  }
  in
  return { data_dir ; p2p ; rpc ; log ; shell }

let resolve_addr ?default_port ?(passive = false) peer =
  let addr, port = P2p_point.Id.parse_addr_port peer in
  let node = if addr = "" || addr = "_" then "::" else addr
  and service =
    match port, default_port with
    | "", None ->
        invalid_arg ""
    | "", Some default_port -> string_of_int default_port
    | port, _ -> port in
  Lwt_utils_unix.getaddrinfo ~passive ~node ~service

let resolve_addrs ?default_port ?passive peers =
  Lwt_list.fold_left_s begin fun a peer ->
    resolve_addr ?default_port ?passive peer >>= fun points ->
    Lwt.return (List.rev_append points a)
  end [] peers

let resolve_listening_addrs listen_addr =
  resolve_addr
    ~default_port:default_p2p_port
    ~passive:true
    listen_addr

let resolve_rpc_listening_addrs listen_addr =
  resolve_addr
    ~default_port:default_rpc_port
    ~passive:true
    listen_addr

let resolve_bootstrap_addrs peers =
  resolve_addrs
    ~default_port:default_p2p_port
    peers
let check_listening_addr config =
  match config.p2p.listen_addr with
  | None -> Lwt.return_unit
  | Some addr ->
      Lwt.catch begin fun () ->
        resolve_listening_addrs addr >>= function
        | [] ->
            Format.eprintf "Warning: failed to resolve %S\n@." addr ;
            Lwt.return_unit
        | _ :: _ ->
            Lwt.return_unit
      end begin function
        | (Invalid_argument msg) ->
            Format.eprintf "Warning: failed to parse %S:\   %s\n@." addr msg ;
            Lwt.return_unit
        | exn -> Lwt.fail exn
      end

let check_rpc_listening_addr config =
  match config.rpc.listen_addr with
  | None -> Lwt.return_unit
  | Some addr ->
      Lwt.catch begin fun () ->
        resolve_rpc_listening_addrs addr >>= function
        | [] ->
            Format.eprintf "Warning: failed to resolve %S\n@." addr ;
            Lwt.return_unit
        | _ :: _ ->
            Lwt.return_unit
      end begin function
        | (Invalid_argument msg) ->
            Format.eprintf "Warning: failed to parse %S:\   %s\n@." addr msg ;
            Lwt.return_unit
        | exn -> Lwt.fail exn
      end

let check_bootstrap_peer addr =
  Lwt.catch begin fun () ->
    resolve_bootstrap_addrs [addr] >>= function
    | [] ->
        Format.eprintf "Warning: cannot resolve %S\n@." addr ;
        Lwt.return_unit
    | _ :: _ ->
        Lwt.return_unit
  end begin function
    | (Invalid_argument msg) ->
        Format.eprintf "Warning: failed to parse %S:\   %s\n@." addr msg ;
        Lwt.return_unit
    | exn -> Lwt.fail exn
  end


let check_bootstrap_peers config =
  Lwt_list.iter_p check_bootstrap_peer config.p2p.bootstrap_peers


let fail fmt =
  Format.kasprintf (fun s -> prerr_endline s ; exit 1) fmt

let check_connections config =
  if config.p2p.limits.min_connections > config.p2p.limits.expected_connections then
    fail "Error: The minumum number of connections is greater than \
          the expected number of connections"
      config.p2p.limits.min_connections
      config.p2p.limits.expected_connections ;
  if config.p2p.limits.expected_connections > config.p2p.limits.max_connections then
    fail "Error: The expected number of connections is greater than \
          the maximum number of connections"
      config.p2p.limits.expected_connections
      config.p2p.limits.max_connections ;
  begin
    match config.p2p.limits.max_known_peer_ids with
    | None -> ()
    | Some (max_known_peer_ids, target_known_peer_ids) ->
        if target_known_peer_ids > max_known_peer_ids then
          fail "Error: The target number of known peer ids is greater than \
                the maximum number of known peer ids."
            target_known_peer_ids max_known_peer_ids ;
        if config.p2p.limits.max_connections > target_known_peer_ids then
          fail "Error: The target number of known peer ids is lower than \
                the maximum number of connections."
            target_known_peer_ids max_known_peer_ids ;
  end ;
  begin
    match config.p2p.limits.max_known_points with
    | None -> ()
    | Some (max_known_points, target_known_points) ->
        if target_known_points > max_known_points then
          fail "Error: The target number of known points is greater than \
                the maximum number of known points."
            target_known_points max_known_points ;
        if config.p2p.limits.max_connections > target_known_points then
          fail "Error: The target number of known points is lower than \
                the maximum number of connections."
            target_known_points max_known_points ;
  end


let check config =
  check_listening_addr config >>= fun () ->
  check_rpc_listening_addr config >>= fun () ->
  check_bootstrap_peers config >>= fun () ->
  check_connections config ;
  Lwt.return_unit
