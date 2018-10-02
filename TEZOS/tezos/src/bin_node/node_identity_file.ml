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

type error += No_identity_file of string
type error += Insufficient_proof_of_work of { expected: float }

let () =
  register_error_kind
    `Permanent
    ~id:"main.identity.no_file"
    ~title:"TODO"
    ~description:"TODO"
    ~pp:(fun ppf file ->
        Format.fprintf ppf
          "Cannot read the identity file: `%s`. \
           See `%s identity --help` on how to generate an identity."
          file Sys.argv.(0))
    Data_encoding.(obj1 (req "file" string))
    (function No_identity_file file -> Some file | _ -> None)
    (fun file -> No_identity_file file)

let () =
  register_error_kind
    `Permanent
    ~id:"main.identity.insufficient_proof_of_work"
    ~title:"TODO"
    ~description:"TODO"
    ~pp:(fun ppf expected ->
        Format.fprintf ppf
          "The current identity does not embed a sufficient stamp of proof-of-work. \
           (expected level: %.2f). \
           See `%s identity --help` on how to generate a new identity."
          expected Sys.argv.(0))
    Data_encoding.(obj1 (req "expected" float))
    (function Insufficient_proof_of_work { expected } -> Some expected | _ -> None)
    (fun expected -> Insufficient_proof_of_work { expected })

let read ?expected_pow file =
  Lwt_unix.file_exists file >>= function
  | false ->
      fail (No_identity_file file)
  | true ->
      Lwt_utils_unix.Json.read_file file >>=? fun json ->
      let id = Data_encoding.Json.destruct P2p_identity.encoding json in
      match expected_pow with
      | None -> return id
      | Some expected ->
          let target = Crypto_box.make_target expected in
          if (Crypto_box.check_proof_of_work
                id.public_key id.proof_of_work_stamp target) then
            return id
          else
            fail (Insufficient_proof_of_work { expected })

type error += Existent_identity_file of string

let () =
  register_error_kind
    `Permanent
    ~id:"main.identity.existent_file"
    ~title:"TODO"
    ~description:"TODO"
    ~pp:(fun ppf file ->
        Format.fprintf ppf
          "Cannot implicitely overwrite the current identity file: '%s'. \
           See `%s identity --help` on how to generate a new identity."
          file Sys.argv.(0))
    Data_encoding.(obj1 (req "file" string))
    (function Existent_identity_file file -> Some file | _ -> None)
    (fun file -> Existent_identity_file file)

let write file identity =
  if Sys.file_exists file then
    fail (Existent_identity_file file)
  else
    Node_data_version.ensure_data_dir (Filename.dirname file) >>=? fun () ->
    Lwt_utils_unix.Json.write_file file
      (Data_encoding.Json.construct P2p_identity.encoding identity)
