open Tree;;
open Buffer;;
open Printf;;
open Str;;

let (>>) x f = f x;;

let clear_ws s =
  Str.global_replace (Str.regexp "[\r\n\t ]") "" s;;


let string_of_tree tree = 
  let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" | Comma -> "," | Into -> "|-" | Proof -> "|=" in

  let buf = create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Neg t -> add_string buf "(!"; s_t t; add_char buf ')'
    | Binop (op, l, r) -> add_char buf '('; s_t l; bprintf buf "%s" (s_op op); s_t r; add_char buf ')'
    | None -> () in
  s_t tree; 
  contents buf;;


let (ic, oc) = (open_in "input.txt", open_out "output.txt");;

let var_table = Hashtbl.create 10;;
let ttl = ref 0;;
let base = ref [];;

let tail = ref ("A" >> Lexing.from_string >> Parser.main Lexer.main);;

let prepare tree =
  let rec check_vars one = match one with
    | Var (expr) -> (if(not (Hashtbl.mem var_table expr)) then (Hashtbl.add var_table expr !ttl; ttl := !ttl + 1)) 
    | Binop (op, a, b) -> (check_vars a; check_vars b)
    | Neg (expr) -> (check_vars expr)
    | _ -> ()
  in
  let rec prepare_main one = match one with
  | Binop (Proof, a, b) -> (prepare_main a; check_vars b; tail := b)
  | Binop (Comma, a, b) -> (prepare_main a; prepare_main b)
  | Binop (op, a, b) -> (check_vars one; base := !base @ [one])
  | Neg (exp) -> (check_vars one; base := !base @ [one])
  | Var (exp) -> (check_vars one; base := !base @ [one])
  | _ -> () in
  prepare_main tree;;

(*Reading*)
let s_tmp = ref "";;
while (clear_ws !s_tmp) = "" do
  s_tmp := input_line ic;
done;;

let i_tree = (!s_tmp >> clear_ws >> Lexing.from_string >> Parser.main Lexer.main);;

prepare i_tree;;

let rec eval tree values = match tree with
  | Binop (Impl, a, b) -> ((eval b values) || (not (eval a values)))
  | Binop (Disj, a, b) -> ((eval a values) || (eval b values))
  | Binop (Conj, a, b) -> ((eval a values) && (eval b values))
  | Neg (expr) -> (not (eval expr values))
  | Var (expr) -> (List.nth values (Hashtbl.find var_table expr))
  | _ -> false;;

let badlist = ref [];;
let rec check_all clist =
  if ((List.length clist) = !ttl) then 
    begin
      let bad = ref false in
      let set_bad tree = (if (not (eval tree clist)) then bad := true) in
      List.iter set_bad !base;
      if ((not !bad) && (not (eval i_tree clist))) then
        begin 
          badlist := clist;
          false;
        end
      else 
        true;
    end
    else ((check_all (clist @ [true])) && (check_all (clist @ [false])));;

fprintf oc "var_table size: %d\n" (Hashtbl.length var_table);; 

if (not(check_all [])) then
  fprintf oc "Высказывание ложно при";
  let tmp_ht = Hashtbl.create 10 in
  let f_print a b = fprintf oc " %s=%s" a (if (List.nth !badlist b) then "И" else "Л") in
  let f_store a b = Hashtbl.add tmp_ht a (List.nth !badlist b) in
  Hashtbl.iter f_print var_table;;


close_out oc;;
close_in ic;;