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

type t

type limits = {
  protocol_timeout: float ;
  worker_limits : Worker_types.limits ;
}

type error += Closed of unit

val create:
  limits -> Distributed_db.t -> t Lwt.t

val validate:
  t ->
  ?canceler:Lwt_canceler.t ->
  ?peer:P2p_peer.Id.t ->
  ?notify_new_block:(State.Block.t -> unit) ->
  Distributed_db.chain_db ->
  Block_hash.t -> Block_header.t -> Operation.t list list ->
  State.Block.t option tzresult Lwt.t

val fetch_and_compile_protocol:
  t ->
  ?peer:P2p_peer.Id.t ->
  ?timeout:float ->
  Protocol_hash.t -> Registered_protocol.t tzresult Lwt.t

val shutdown: t -> unit Lwt.t

val running_worker: unit -> t
val status: t -> Worker_types.worker_status

val pending_requests : t -> (Time.t * Block_validator_worker_state.Request.view) list
val current_request : t -> (Time.t * Time.t * Block_validator_worker_state.Request.view) option
val last_events : t -> (Lwt_log_core.level * Block_validator_worker_state.Event.t list) list

val may_patch_protocol:
  level:Int32.t ->
  Tezos_protocol_environment_shell.validation_result ->
  Tezos_protocol_environment_shell.validation_result tzresult Lwt.t
