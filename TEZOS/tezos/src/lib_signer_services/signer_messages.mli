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

module Sign : sig

  module Request : sig
    type t = {
      pkh: Signature.Public_key_hash.t ;
      data: MBytes.t ;
      signature: Signature.t option ;
    }
    val to_sign:
      pkh: Signature.Public_key_hash.t ->
      data: MBytes.t ->
      MBytes.t
    val encoding : t Data_encoding.t
  end

  module Response : sig
    type t = Signature.t
    val encoding : t Data_encoding.t
  end

end

module Public_key : sig

  module Request : sig
    type t = Signature.Public_key_hash.t
    val encoding : t Data_encoding.t
  end

  module Response : sig
    type t = Signature.Public_key.t
    val encoding : t Data_encoding.t
  end

end

module Authorized_keys : sig

  module Response : sig
    type t =
      | No_authentication
      | Authorized_keys of Signature.Public_key_hash.t list
    val encoding : t Data_encoding.t
  end

end

module Request : sig

  type t =
    | Sign of Sign.Request.t
    | Public_key of Public_key.Request.t
    | Authorized_keys
  val encoding : t Data_encoding.t

end