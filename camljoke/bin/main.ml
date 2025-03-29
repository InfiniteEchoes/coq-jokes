(* TODO: https://ocaml.org/docs/your-first-program *)

let () = print_endline "Hello, World!"
let () = Printf.printf "%s\n" "Hello, World!"

let exp1 = Sexplib.Sexp.of_string "(This (is an) (s expression))"
let () = Printf.printf "%s\n" "Hello, World!"

type expr =
  | And
  | Or
  | Is
  | Adj
  | Plain
  ;;

type sentence =
  | Say
  | Ask
  | Answer
  | Narrate
  | Follow
  ;;