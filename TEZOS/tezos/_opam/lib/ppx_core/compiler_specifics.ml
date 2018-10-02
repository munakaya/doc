module O = Ocaml_common
let error_of_exn exn =
  match O.Location.error_of_exn exn with
  | None -> None
  | Some `Already_displayed -> None
  | Some (`Ok t) -> Some t
