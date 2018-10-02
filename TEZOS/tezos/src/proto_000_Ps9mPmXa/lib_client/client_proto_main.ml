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

open Proto_000_Ps9mPmXa

let protocol =
  Protocol_hash.of_b58check_exn
    "Ps9mPmXaRzmzk35gbAYNCAw6UXdE2qoABTHbN2oEEc1qM7CwT9P"

let bake cctxt ?(timestamp = Time.now ()) block command sk =
  let protocol_data = { command ; signature = Signature.zero } in
  Genesis_block_services.Helpers.Preapply.block
    cctxt ~block ~timestamp ~protocol_data
    [] >>=? fun (shell_header, _) ->
  let blk = Data.Command.forge shell_header command in
  Shell_services.Chain.chain_id cctxt ~chain:`Main () >>=? fun chain_id ->
  Client_keys.append cctxt sk ~watermark:(Block_header chain_id) blk >>=? fun signed_blk ->
  Shell_services.Injection.block cctxt signed_blk []

let int64_parameter =
  (Clic.parameter (fun _ p ->
       try return (Int64.of_string p)
       with _ -> failwith "Cannot read int64"))

let int_parameter =
  (Clic.parameter (fun _ p ->
       try return (int_of_string p)
       with _ -> failwith "Cannot read int"))

let file_parameter =
  Clic.parameter (fun _ p ->
      if not (Sys.file_exists p) then
        failwith "File doesn't exist: '%s'" p
      else
        return p)

let commands () =
  let open Clic in
  let args =
    args1
      (arg
         ~long:"timestamp"
         ~placeholder:"date"
         ~doc:"Set the timestamp of the block (and initial time of the chain)"
         (parameter (fun _ t ->
              match (Time.of_notation t) with
              | None -> Error_monad.failwith "Could not parse value provided to -timestamp option"
              | Some t -> return t))) in
  [

    command ~desc: "Activate a protocol"
      args
      (prefixes [ "activate" ; "protocol" ]
       @@ Protocol_hash.param ~name:"version" ~desc:"Protocol version (b58check)"
       @@ prefixes [ "with" ; "fitness" ]
       @@ param ~name:"fitness"
         ~desc:"Hardcoded fitness of the first block (integer)"
         int64_parameter
       @@ prefixes [ "and" ; "key" ]
       @@ Client_keys.Secret_key.source_param
         ~name:"password" ~desc:"Activator's key"
       @@ prefixes [ "and" ; "parameters" ]
       @@ param ~name:"parameters"
         ~desc:"Protocol parameters (as JSON file)"
         file_parameter
       @@ stop)
      begin fun timestamp hash fitness sk param_json_file (cctxt : Client_context.full) ->
        let fitness = Proto_alpha.Fitness_repr.from_int64 fitness in
        Tezos_stdlib_unix.Lwt_utils_unix.Json.read_file param_json_file >>=? fun json ->
        let protocol_parameters = Data_encoding.Binary.to_bytes_exn Data_encoding.json json in
        bake cctxt ?timestamp cctxt#block
          (Activate { protocol = hash ; fitness ; protocol_parameters })
          sk >>=? fun hash ->
        cctxt#answer "Injected %a" Block_hash.pp_short hash >>= fun () ->
        return_unit
      end ;

    command ~desc: "Fork a test protocol"
      args
      (prefixes [ "fork" ; "test" ; "protocol" ]
       @@ Protocol_hash.param ~name:"version" ~desc:"Protocol version (b58check)"
       @@ prefixes [ "with" ; "key" ]
       @@ Client_keys.Secret_key.source_param
         ~name:"password" ~desc:"Activator's key"
       @@ stop)
      begin fun timestamp hash sk cctxt ->
        bake cctxt ?timestamp cctxt#block
          (Activate_testchain { protocol = hash ;
                                delay = Int64.mul 24L 3600L })
          sk >>=? fun hash ->
        cctxt#answer "Injected %a" Block_hash.pp_short hash >>= fun () ->
        return_unit
      end ;

  ]

let () =
  Client_commands.register protocol @@ fun _network ->
  commands ()
