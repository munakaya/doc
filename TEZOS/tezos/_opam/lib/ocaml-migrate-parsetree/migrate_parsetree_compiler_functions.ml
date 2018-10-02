# 1 "src/compiler-functions/ge_406.ml"
let error_of_exn exn =
  match Location.error_of_exn exn with
  | Some (`Ok exn) -> Some exn
  | Some `Already_displayed -> None
  | None -> None
