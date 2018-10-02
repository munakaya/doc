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

val timestamp_tag : Time.t Tag.def
val valid_ops : int Tag.def
val refused_ops : int Tag.def
val bake_priorty_tag : int Tag.def
val fitness_tag : Fitness.t Tag.def
val current_slots_tag : int Tag.def
val future_slots_tag : int Tag.def

val operations_tag : error Preapply_result.t list Tag.def
val bake_op_count_tag : int Tag.def
val endorsement_slot_tag : int Tag.def
val endorsement_slots_tag : int list Tag.def
val denounced_endorsements_slots_tag : int list Tag.def
val denouncement_source_tag : string Tag.def
val level_tag : Proto_alpha.Alpha_context.Raw_level.t Tag.def
val worker_tag : string Tag.def

open Proto_alpha.Alpha_context
val conflicting_endorsements_tag : (Kind.endorsement operation * Kind.endorsement operation) Tag.def
