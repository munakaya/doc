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

module S = struct

  open Data_encoding

  let path = RPC_path.(root / "monitor")

  let bootstrapped =
    RPC_service.get_service
      ~description:
        "Wait for the node to have synchronized its chain with a few \
         peers (configured by the node's administrator), streaming \
         head updates that happen during the bootstrapping process, \
         and closing the stream at the end. If the node was already \
         bootstrapped, returns the current head immediately."
      ~query: RPC_query.empty
      ~output: (obj2
                  (req "block" Block_hash.encoding)
                  (req "timestamp" Time.encoding))
      RPC_path.(path / "bootstrapped")

  let valid_blocks_query =
    let open RPC_query in
    query (fun protocols next_protocols chains -> object
            method protocols = protocols
            method next_protocols = next_protocols
            method chains = chains
          end)
    |+ multi_field "protocol"
      Protocol_hash.rpc_arg (fun t -> t#protocols)
    |+ multi_field "next_protocol"
      Protocol_hash.rpc_arg (fun t -> t#next_protocols)
    |+ multi_field "chain"
      Chain_services.chain_arg (fun t -> t#chains)
    |> seal

  let valid_blocks =
    RPC_service.get_service
      ~description:"Monitor all blocks that are succesfully validated \
                    by the node, disregarding whether they were \
                    selected as the new head or not."
      ~query: valid_blocks_query
      ~output: (merge_objs
                  (obj2
                     (req "chain_id" Chain_id.encoding)
                     (req "hash" Block_hash.encoding))
                  Block_header.encoding)
      RPC_path.(path / "valid_blocks")

  let heads_query =
    let open RPC_query in
    query (fun next_protocols -> object
            method next_protocols = next_protocols
          end)
    |+ multi_field "next_protocol"
      Protocol_hash.rpc_arg (fun t -> t#next_protocols)
    |> seal

  let heads =
    RPC_service.get_service
      ~description:"Monitor all blocks that are succesfully validated \
                    by the node and selected as the new head of the \
                    given chain."
      ~query: heads_query
      ~output: (merge_objs
                  (obj1
                     (req "hash" Block_hash.encoding))
                  Block_header.encoding)
      RPC_path.(path / "heads" /: Chain_services.chain_arg)

  let protocols =
    RPC_service.get_service
      ~description:"Monitor all economic protocols that are retrieved \
                    and succesfully loaded and compiled by the node."
      ~query: RPC_query.empty
      ~output: Protocol_hash.encoding
      RPC_path.(path / "protocols")

end

open RPC_context

let bootstrapped ctxt =
  make_streamed_call S.bootstrapped ctxt () () ()

let valid_blocks
    ctxt ?(chains = [`Main]) ?(protocols = []) ?(next_protocols = []) () =
  make_streamed_call S.valid_blocks ctxt () (object
    method chains = chains
    method protocols = protocols
    method next_protocols = next_protocols
  end) ()

let heads ctxt ?(next_protocols = []) chain =
  make_streamed_call S.heads ctxt ((), chain) (object
    method next_protocols = next_protocols
  end) ()

let protocols ctxt =
  make_streamed_call S.protocols ctxt () () ()
