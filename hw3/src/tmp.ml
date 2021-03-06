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

(*
ic >> input_line >> Lexing.from_string >> Parser.main Lexer.main >> string_of_tree >> fprintf oc "%s\n";;
*)


let _base = Hashtbl.create 1024;;
let _made = Hashtbl.create 1024;;
let _mp = Hashtbl.create 1024;;
let _wait = Hashtbl.create 1024;;
let ttl = ref 1;;

let prepare tree =
  let rec _parse one = match one with
    | Binop (Impl, a, b) -> (Hashtbl.add _base one !ttl; ttl := !ttl + 1; (*one >> string_of_tree >> fprintf oc "added: %s\n" *)) 
    | Binop (Conj, a, b) -> (Hashtbl.add _base one !ttl; ttl := !ttl + 1)
    | Binop (Disj, a, b) -> (Hashtbl.add _base one !ttl; ttl := !ttl + 1)
    | Binop (Comma, a, b) -> (_parse a; _parse b)
    | Binop (Into, a, b) -> (_parse a)
    | None -> ()
    | Neg (exp) -> (Hashtbl.add _base one !ttl; ttl := !ttl + 1)
    | Var (exp) -> (Hashtbl.add _base one !ttl; ttl := !ttl + 1) in
  _parse tree;;


let _s_tmp = ref "";;
while (_clear_ws !_s_tmp) = "" do
  _s_tmp := input_line ic;
done;;

!_s_tmp >> _clear_ws >> Lexing.from_string >> Parser.main Lexer.main >> prepare;;


let check_base tree = 
  if Hashtbl.mem _base tree
  then Hashtbl.find _base tree
  else -1;;
  
let check_axiom tree =
  match tree with 
  | Binop (Impl, a1, Binop (Impl, b, a2)) when a1 = a2 -> 1
  | Binop (
    Impl,
    Binop (Impl, a1, b1),
    Binop (
      Impl,
      Binop (
        Impl,
        a2,
        Binop (Impl, b2, c1)
      ),
      Binop (Impl, a3, c2)
    )
  ) when (a1 = a2 && a1 = a3 && b1 = b2 && c1 = c2) -> 2
  | Binop (
    Impl,
    a1,
    Binop (
      Impl,
      b1,
      Binop (Conj, a2, b2)
    )
  ) when (a1 = a2 && b1 = b2) -> 3
  | Binop (
    Impl,
    Binop (Conj, a1, b1),
    a2
  ) when (a1 = a2) -> 4
  | Binop (
    Impl,
    Binop (Conj, a1, b1),
    b2
  ) when (b1 = b2) -> 5
  | Binop (
    Impl,
    a1,
    Binop (Disj, a2, b1)
  ) when (a1 = a2) -> 6
  | Binop (
    Impl,
    b1,
    Binop (Disj, a1, b2)
  ) when (b1 = b2) -> 7
  | Binop (
    Impl,
    Binop (Impl, a1, c1),
    Binop (
      Impl,
      Binop (Impl, b1, c2),
      Binop (
        Impl,
        Binop (Disj, a2, b2),
        c3
      )
    )
  ) when (a1 = a2 && b1 = b2 && c1 = c2 && c1 = c3) -> 8
  | Binop (
    Impl,
    Binop (Impl, a1, b1),
    Binop (
      Impl,
      Binop (Impl, a2, Neg(b2)),
      Neg(a3)
    )
  ) when (a1 = a2 && a1 = a3 && b1 = b2) -> 9
  | Binop(
    Impl,
    Neg(Neg(a1)),
    a2
  ) when (a1 = a2) -> 10
  | _ -> -1;;


ttl := 0;;

let check_mp tree =
  if Hashtbl.mem _mp tree
  then Hashtbl.find _mp tree
  else (-1, -1);;


let _put tree =
  Hashtbl.add _made tree !ttl;

  if Hashtbl.mem _wait tree then 
  begin
    let _list = Hashtbl.find_all _wait tree in
    let _f _one = (Hashtbl.add _mp _one (!ttl, (Hashtbl.find _made (Binop (Impl, tree, _one))))) in
    let _cl _one = (Hashtbl.remove _wait tree) in
    List.iter _f _list;
    List.iter _cl _list;
  end;

  match tree with
  | Binop (Impl, a, b) -> if Hashtbl.mem _made a then Hashtbl.add _mp b ((Hashtbl.find _made a), !ttl) else Hashtbl.add _wait a b
  | _ -> ();;




let _flag = ref true;;

let _find s =
  let cl_s = (_clear_ws s) in
  if cl_s <> "" then
  begin
    if !_flag then
      _flag := false
    else
      fprintf oc "\n";

    ttl := !ttl + 1;
    let tree = cl_s >> Lexing.from_string >> Parser.main Lexer.main in
    fprintf oc "(%d) %s " !ttl (string_of_tree tree);
    if (check_base tree) <> -1 then
      fprintf oc "(Предп. %d)" (check_base tree) (*TODO: fix this*)
    else if (check_axiom tree) <> -1 then
      fprintf oc "(Сх. акс. %d)" (check_axiom tree)
    else if (check_mp tree) <> (-1, -1) then
    begin
      let (a, b) = (check_mp tree) in
      fprintf oc "(M.P. %d, %d)" b a;
    end
    else
      fprintf oc "(Не доказано)";
    _put tree;
  end
  else ();;
  
    

(try
  while true 
  do
    ic >> input_line >> _find;
  done;
with End_of_file -> ());;


close_out oc;;
close_in ic;;