open Tree;;
open Buffer;;
open Printf;;
open Str;;

let (>>) x f = f x;;

let _clear_ws s =
  Str.global_replace (Str.regexp "[\r\n\t ]") "" s;;


let string_of_tree tree = 
  let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" | Comma -> "," | Into -> "|-" in

  let buf = create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Neg t -> add_string buf "(!"; s_t t; add_char buf ')'
    | Binop (op,l,r) -> add_char buf '('; s_t l; bprintf buf "%s" (s_op op); s_t r; add_char buf ')'
  in
  s_t tree;
  contents buf;;


let (ic, oc) = (open_in "input.txt", open_out "output.txt");;


let orig = ref ("A" >> Lexing.from_string >> Parser.main Lexer.main);;
let alpha = ref ("A" >> Lexing.from_string >> Parser.main Lexer.main);;

let vars = [||]

 let prepare tree =
  orig := tree;
  let rec getalpha one = 
    match one with
    | Binop (Proof, a, b) -> Binop (Impl, (getalpha a), b)
    | Binop (Comma, a, b) -> Binop (Impl, a, (getalpha b))
    | _ -> one in
  alpha := getalpha tree;

  let rec _parse one = 
    alpha := one;
    match one with
    | Binop (_, a, b) -> (_parse a; _parse b) 
    | None -> ()
    | Neg (exp) -> (_parse exp)
    | Var (exp) -> (if !(Array.exists vars ((a) -> (a = exp))) then ) in
  _parse tree *);;
 
let _s_tmp = ref "";;
while (_clear_ws !_s_tmp) = "" do
  _s_tmp := input_line ic;
done;;



!_s_tmp >> _clear_ws >> Lexing.from_string >> Parser.main Lexer.main >> prepare;;





  


close_out oc;;
close_in ic;;