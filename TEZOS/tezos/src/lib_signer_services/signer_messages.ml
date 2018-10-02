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

module Sign = struct

  module Request = struct

    type t = {
      pkh: Signature.Public_key_hash.t ;
      data: MBytes.t ;
      signature: Signature.t option ;
    }

    let to_sign ~pkh ~data =
      MBytes.concat ""
        [ MBytes.of_string "\x04" ;
          Signature.Public_key_hash.to_bytes pkh ;
          data ]

    let encoding =
      let open Data_encoding in
      conv
        (fun { pkh ; data ; signature } ->
           (pkh, data, signature))
        (fun (pkh, data, signature)  ->
           { pkh ; data ; signature })
        (obj3
           (req "pkh" Signature.Public_key_hash.encoding)
           (req "data" bytes)
           (opt "signature" Signature.encoding))

  end

  module Response = struct

    type t = Signature.t

    let encoding =
      Data_encoding.(obj1 (req "signature" Signature.encoding))

  end

end

module Public_key = struct

  module Request = struct

    type t = Signature.Public_key_hash.t

    let encoding =
      Data_encoding.(obj1 (req "pkh" Signature.Public_key_hash.encoding))

  end

  module Response = struct

    type t = Signature.Public_key.t

    let encoding =
      Data_encoding.(obj1 (req "pubkey" Signature.Public_key.encoding))

  end

end

module Authorized_keys = struct

  module Response = struct

    type t =
      | No_authentication
      | Authorized_keys of Signature.Public_key_hash.t list

    let encoding =
      let open Data_encoding in
      union
        [ case (Tag 0)
            ~title: "No_authentication"
            (constant "no_authentication_required")
            (function No_authentication -> Some () | _ -> None)
            (fun () -> No_authentication) ;
          case (Tag 1)
            ~title: "Authorized_keys"
            (list Signature.Public_key_hash.encoding)
            (function Authorized_keys l -> Some l | _ -> None)
            (fun l -> Authorized_keys l) ]

  end

end

module Request = struct

  type t =
    | Sign of Sign.Request.t
    | Public_key of Public_key.Request.t
    | Authorized_keys

  let encoding =
    let open Data_encoding in
    union [
      case (Tag 0)
        ~title:"Sign"
        (merge_objs
           (obj1 (req "kind" (constant "sign")))
           Sign.Request.encoding)
        (function Sign req -> Some ((), req) | _ -> None)
        (fun ((), req) -> Sign req) ;
      case (Tag 1)
        ~title:"Public_key"
        (merge_objs
           (obj1 (req "kind" (constant "public_key")))
           Public_key.Request.encoding)
        (function Public_key req -> Some ((), req) | _ -> None)
        (fun ((), req) -> Public_key req) ;
      case (Tag 2)
        ~title:"Authorized_keys"
        (obj1 (req "kind" (constant "authorized_keys")))
        (function Authorized_keys -> Some () | _ -> None)
        (fun () -> Authorized_keys) ;
    ]

end
