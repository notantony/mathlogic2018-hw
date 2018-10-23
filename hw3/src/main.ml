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

let vars = ref [||];;

let prepare tree =
  orig := tree;
  let rec getalpha one = 
    match one with
    | Binop (Proof, None, b) -> b
    | Binop (Proof, a, b) -> Binop (Impl, (getalpha a), b)
    | Binop (Comma, a, b) -> Binop (Impl, a, (getalpha b))
    | _ -> one in
  alpha := getalpha tree;

  let rec _parse one = 
    match one with
    | Binop (_, a, b) -> (_parse a; _parse b) 
    | None -> ()
    | Neg (exp) -> (_parse exp)
    | Var (exp) -> 
      begin
        let _flag = ref 0 in
        for i = 0 to (Array.length !vars - 1) do
          if exp = !vars.(i) then _flag := 1;
        done;
        if !_flag = 0 then (vars := (Array.append !vars [|exp|]));
      end
    in
  _parse tree;;
 
let _s_tmp = ref "";;
while (_clear_ws !_s_tmp) = "" do
  _s_tmp := input_line ic;
done;;

!_s_tmp >> _clear_ws >> Lexing.from_string >> Parser.main Lexer.main >> prepare;;

let _check tree _bitset = 
  let _get _ss =
    let _ret = ref false in
    for i = 0 to (Array.length !vars - 1) do
      if !vars.(i) = _ss then _ret := ((_bitset land (1 lsl i)) <> 0);
    done;
    (!_ret)
  in 

  let rec _dp tree =
    match tree with
    | Binop (Conj, a, b) -> ((_dp a) && (_dp b))
    | Binop (Disj, a, b) -> ((_dp a) || (_dp b))
    | Binop (Impl, a, b) -> ((not (_dp a)) || (_dp b))
    | Neg (exp) -> (not (_dp exp))
    | Var (exp) -> (_get exp)
  in
  _dp tree;;

let prf () = 
  let rec can tree =
    match tree with
    | Binop (Conj, a, b) ->
      begin
        if ()

let prep () =
  let _test = ref (-1) in 
  for i = 0 to ((1 lsl (Array.length !vars)) - 1) do
    if not (_check !alpha i) then _test := i
  done;
  if !_test <> -1 then 
  begin
    fprintf oc "Высказывание ложно при ";
    for i = 0 to (Array.length !vars - 1) do
      if i <> 0 then fprintf oc ", ";
      fprintf oc "%s=%s" !vars.(i) (if ((!_test land (1 lsl i)) <> 0) then "И" else "Л");
    done;
  end
  else prf ();;

prep ();;

close_out oc;;
close_in ic;;