
open Ezcmd.Modules


let toto = ref false

let () =
  Arg.parse ~name:"test3"
                   [
      "-toto", Arg.Set toto, "Documentation on toto";
    ]
            (fun _s -> assert false)
            "test3 [OPTIONS] [ARGUMENTS]"
