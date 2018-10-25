open Tree;;
open Buffer;;
open Printf;;
open Str;;

let take2 sarr = 
  let bc = Buffer.create 64 in
  let sarr_i = ref 0 in
  
  let (>>) x f = f x in

  let _clear_ws s =
  Str.global_replace (Str.regexp "[\r\n\t ]") "" s in


  let string_of_tree tree = 
    let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" | Comma -> "," | Into -> "|-" in

    let buf = create 64 in
    let rec s_t t = match t with
      | Var v -> add_string buf v
      | Neg t -> add_string buf "(!"; s_t t; add_char buf ')'
      | Binop (op,l,r) -> add_char buf '('; s_t l; bprintf buf "%s" (s_op op); s_t r; add_char buf ')'
    in
    s_t tree;
    contents buf in

  let _base = Hashtbl.create 255 in
  let _made = Hashtbl.create 255 in
  let _mp = Hashtbl.create 255 in
  let _wait = Hashtbl.create 255 in
  let ttl = ref 1 in

  let alpha = ref ("A" >> Lexing.from_string >> Parser.main Lexer.main) in
  let _out = ref ("A" >> Lexing.from_string >> Parser.main Lexer.main) in

  let prepare tree =
    let rec _parse one = 
      alpha := one;
      match one with
      | Binop (Impl, a, b) -> (Hashtbl.add _base one !ttl; ttl := !ttl + 1) 
      | Binop (Conj, a, b) -> (Hashtbl.add _base one !ttl; ttl := !ttl + 1)
      | Binop (Disj, a, b) -> (Hashtbl.add _base one !ttl; ttl := !ttl + 1)
      | Binop (Comma, a, b) -> (_parse a; _parse b)
      | Binop (Into, a, b) -> (_parse a; _out := b)
      | None -> ()
      | Neg (exp) -> (Hashtbl.add _base one !ttl; ttl := !ttl + 1)
      | Var (exp) -> (Hashtbl.add _base one !ttl; ttl := !ttl + 1) in
    _parse tree in


  let prep_print ss =   
    if String.contains ss ',' then
    begin
      let x = String.rindex ss ',' in
      bprintf bc "%s" (String.sub ss 0 (x));
    end;
    bprintf bc "|-%s\n" (string_of_tree (Binop (Impl, !alpha, !_out))) in



  sarr.(0) >> _clear_ws >> Lexing.from_string >> Parser.main Lexer.main >> prepare;

  prep_print sarr.(!sarr_i);
  sarr_i := !sarr_i + 1;


  let check_base tree = 
    if Hashtbl.mem _base tree
    then Hashtbl.find _base tree
    else -1 in
    
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
    | _ -> -1 in


  ttl := 0;

  let check_mp tree =
    if Hashtbl.mem _mp tree
    then Hashtbl.find _mp tree
    else (-1, -1) in


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
    | _ -> () in




  let _flag = ref true in

  let sa = (string_of_tree !alpha) in

  let _store = ref [||] in

  let _find s =
    let cl_s = (_clear_ws s) in
    if cl_s <> "" then
    begin
      ttl := !ttl + 1;
      let tree = cl_s >> Lexing.from_string >> Parser.main Lexer.main in
      let _st = (string_of_tree tree) in
      if _st = sa then
        bprintf bc ""
      else if (check_base tree) <> -1 then
        bprintf bc "%s\n%s->(%s)->%s\n%s->%s\n" _st
        _st sa _st
        sa _st
      else if (check_axiom tree) <> -1 then
        bprintf bc "%s\n%s->(%s)->%s\n%s->%s\n" _st
        _st sa _st
        sa _st
      else if (check_mp tree) <> (-1, -1) then
      begin
        let (x, y) = (check_mp tree) in
        let sx = (!_store).(x - 1) in
        bprintf bc "(%s->%s)->((%s->(%s->%s))->(%s->%s))\n" sa sx sa sx _st sa _st;
        bprintf bc "((%s->(%s->%s))->(%s->%s))\n%s->%s\n" sa sx _st sa _st sa _st;
      end
      else
        bprintf bc "***(Не доказано):\n%s\n***\n" (string_of_tree tree);
      _put tree;
      _store := Array.append !_store [|_st|];
    end in

      bprintf bc "%s->(%s->%s)\n(%s->(%s->%s))->(%s->((%s->%s)->%s))->(%s->%s)\n(%s->((%s->%s)->%s))->(%s->%s)\n(%s->((%s->%s)->%s))\n%s->%s\n" sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa;
      while (!sarr_i < (Array.length sarr))
      do
        (_find sarr.(!sarr_i));
        sarr_i := !sarr_i + 1;
      done;
      bc;;
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
  contents buf
;;


let (ic, oc) = (open_in "input.txt", open_out "output.txt");;


let orig = ref ("A" >> Lexing.from_string >> Parser.main Lexer.main);;
let alpha = ref ("A" >> Lexing.from_string >> Parser.main Lexer.main);;
let tail = ref ("A" >> Lexing.from_string >> Parser.main Lexer.main);;

let vars = ref [||];;

let prepare tree =
  orig := tree;
  let rec getalpha one = 
    match one with
    | Binop (Proof, None, b) -> (tail := b; b)
    | Binop (Proof, a, b) -> (tail := b; Binop (Impl, (getalpha a), b))
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

let get12 va vb sa sb t =
  let buf = Buffer.create(256) in
  let tree = (va, vb, t) in 
  match tree with
  | (false, false, Conj) -> begin
    (bprintf buf "(!%s)\n((%s&%s)->%s)->((%s&%s)->!%s)->(!(%s&%s))\n(%s&%s)->%s\n((%s&%s)->(!%s))->(!(%s&%s))\n(!%s)->(%s&%s)->(!%s)\n(%s&%s)->(!%s)\n!(%s&%s)\n" sb sa sb sb sa sb sb sa sb sa sb sb sa sb sb sa sb sb sa sb sb sa sb sb sa sb);
    buf;
  end 
  | (false, true, Conj) -> begin
    (bprintf buf "(!%s)\n((%s&%s)->%s)->((%s&%s)->!%s)->(!(%s&%s))\n(%s&%s)->%s\n((%s&%s)->!%s)->(!(%s&%s))\n(!%s)->(%s&%s)->(!%s)\n(%s&%s)->(!%s)\n!(%s&%s)\n" sa sa sb sa sa sb sa sa sb sa sb sa sa sb sa sa sb sa sa sb sa sa sb sa sa sb);
    buf;
  end
  | (true, false, Conj) -> begin
    (bprintf buf "(!%s)\n((%s&%s)->%s)->((%s&%s)->!%s)->(!(%s&%s))\n(%s&%s)->%s\n((%s&%s)->(!%s))->(!(%s&%s))\n(!%s)->(%s&%s)->(!%s)\n(%s&%s)->(!%s)\n!(%s&%s)\n" sb sa sb sb sa sb sb sa sb sa sb sb sa sb sb sa sb sb sa sb sb sa sb sb sa sb);
    buf;
  end
  | (true, true, Conj) -> begin
    (bprintf buf "%s\n%s\n%s->%s->(%s&%s)\n%s->(%s&%s)\n(%s&%s)\n" sa sb sa sb sa sb sb sa sb sa sb);
    buf;
  end
  | (false, false, Disj) -> begin
    (bprintf buf "!%s\n!%s\n((%s|%s)->%s)->(((%s|%s)->!%s)->!(%s|%s))\n!%s->((%s|%s)->!%s)\n(%s|%s)->!%s\n(!%s->((%s|%s)->!%s))\n((%s|%s)->!%s)\n(!%s->((%s|%s)->!%s))\n((%s|%s)->!%s)\n((%s|%s)->((%s|%s)->(%s|%s)))\n((%s|%s)->(((%s|%s)->(%s|%s))->(%s|%s)))\n(((%s|%s)->((%s|%s)->(%s|%s)))->(((%s|%s)->(((%s|%s)->(%s|%s))->(%s|%s)))->((%s|%s)->(%s|%s))))\n(((%s|%s)->(((%s|%s)->(%s|%s))->(%s|%s)))->((%s|%s)->(%s|%s)))\n((%s|%s)->(%s|%s))\n(%s->(%s->%s))\n((%s->(%s->%s))->((%s|%s)->(%s->(%s->%s))))\n((%s|%s)->(%s->(%s->%s)))\n((%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s)))\n(((%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s)))->((%s|%s)->((%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s)))))\n((%s|%s)->((%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s))))\n(%s->((%s->%s)->%s))\n((%s->((%s->%s)->%s))->((%s|%s)->(%s->((%s->%s)->%s))))\n((%s|%s)->(%s->((%s->%s)->%s)))\n(((%s|%s)->(%s->(%s->%s)))->(((%s|%s)->((%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s))))->((%s|%s)->((%s->((%s->%s)->%s))->(%s->%s)))))\n(((%s|%s)->((%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s))))->((%s|%s)->((%s->((%s->%s)->%s))->(%s->%s))))\n((%s|%s)->((%s->((%s->%s)->%s))->(%s->%s)))\n(((%s|%s)->(%s->((%s->%s)->%s)))->(((%s|%s)->((%s->((%s->%s)->%s))->(%s->%s)))->((%s|%s)->(%s->%s))))\n(((%s|%s)->((%s->((%s->%s)->%s))->(%s->%s)))->((%s|%s)->(%s->%s)))\n((%s|%s)->(%s->%s))\n(!%s->(%s->!%s))\n((!%s->(%s->!%s))->((%s|%s)->(!%s->(%s->!%s))))\n((%s|%s)->(!%s->(%s->!%s)))\n(((%s|%s)->!%s)->(((%s|%s)->(!%s->(%s->!%s)))->((%s|%s)->(%s->!%s))))\n(((%s|%s)->(!%s->(%s->!%s)))->((%s|%s)->(%s->!%s)))\n((%s|%s)->(%s->!%s))\n(!%s->(%s->!%s))\n((!%s->(%s->!%s))->((%s|%s)->(!%s->(%s->!%s))))\n((%s|%s)->(!%s->(%s->!%s)))\n(((%s|%s)->!%s)->(((%s|%s)->(!%s->(%s->!%s)))->((%s|%s)->(%s->!%s))))\n(((%s|%s)->(!%s->(%s->!%s)))->((%s|%s)->(%s->!%s)))\n((%s|%s)->(%s->!%s))\n(%s->(%s->%s))\n((%s->(%s->%s))->((%s|%s)->(%s->(%s->%s))))\n((%s|%s)->(%s->(%s->%s)))\n(%s->((%s->%s)->%s))\n((%s->((%s->%s)->%s))->((%s|%s)->(%s->((%s->%s)->%s))))\n((%s|%s)->(%s->((%s->%s)->%s)))\n((%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s)))\n(((%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s)))->((%s|%s)->((%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s)))))\n((%s|%s)->((%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s))))\n(((%s|%s)->(%s->(%s->%s)))->(((%s|%s)->((%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s))))->((%s|%s)->((%s->((%s->%s)->%s))->(%s->%s)))))\n(((%s|%s)->((%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s))))->((%s|%s)->((%s->((%s->%s)->%s))->(%s->%s))))\n((%s|%s)->((%s->((%s->%s)->%s))->(%s->%s)))\n(((%s|%s)->(%s->((%s->%s)->%s)))->(((%s|%s)->((%s->((%s->%s)->%s))->(%s->%s)))->((%s|%s)->(%s->%s))))\n(((%s|%s)->((%s->((%s->%s)->%s))->(%s->%s)))->((%s|%s)->(%s->%s)))\n((%s|%s)->(%s->%s))\n((!%s->%s)->((!%s->!%s)->!!%s))\n(((!%s->%s)->((!%s->!%s)->!!%s))->((%s|%s)->((!%s->%s)->((!%s->!%s)->!!%s))))\n((%s|%s)->((!%s->%s)->((!%s->!%s)->!!%s)))\n(((!%s->%s)->((!%s->!%s)->!!%s))->(%s->((!%s->%s)->((!%s->!%s)->!!%s))))\n((((!%s->%s)->((!%s->!%s)->!!%s))->(%s->((!%s->%s)->((!%s->!%s)->!!%s))))->((%s|%s)->(((!%s->%s)->((!%s->!%s)->!!%s))->(%s->((!%s->%s)->((!%s->!%s)->!!%s))))))\n((%s|%s)->(((!%s->%s)->((!%s->!%s)->!!%s))->(%s->((!%s->%s)->((!%s->!%s)->!!%s)))))\n(((%s|%s)->((!%s->%s)->((!%s->!%s)->!!%s)))->(((%s|%s)->(((!%s->%s)->((!%s->!%s)->!!%s))->(%s->((!%s->%s)->((!%s->!%s)->!!%s)))))->((%s|%s)->(%s->((!%s->%s)->((!%s->!%s)->!!%s))))))\n(((%s|%s)->(((!%s->%s)->((!%s->!%s)->!!%s))->(%s->((!%s->%s)->((!%s->!%s)->!!%s)))))->((%s|%s)->(%s->((!%s->%s)->((!%s->!%s)->!!%s)))))\n((%s|%s)->(%s->((!%s->%s)->((!%s->!%s)->!!%s))))\n(%s->(!%s->%s))\n((%s->(!%s->%s))->((%s|%s)->(%s->(!%s->%s))))\n((%s|%s)->(%s->(!%s->%s)))\n((%s->(!%s->%s))->(%s->(%s->(!%s->%s))))\n(((%s->(!%s->%s))->(%s->(%s->(!%s->%s))))->((%s|%s)->((%s->(!%s->%s))->(%s->(%s->(!%s->%s))))))\n((%s|%s)->((%s->(!%s->%s))->(%s->(%s->(!%s->%s)))))\n(((%s|%s)->(%s->(!%s->%s)))->(((%s|%s)->((%s->(!%s->%s))->(%s->(%s->(!%s->%s)))))->((%s|%s)->(%s->(%s->(!%s->%s))))))\n(((%s|%s)->((%s->(!%s->%s))->(%s->(%s->(!%s->%s)))))->((%s|%s)->(%s->(%s->(!%s->%s)))))\n((%s|%s)->(%s->(%s->(!%s->%s))))\n((%s->%s)->((%s->(%s->(!%s->%s)))->(%s->(!%s->%s))))\n(((%s->%s)->((%s->(%s->(!%s->%s)))->(%s->(!%s->%s))))->((%s|%s)->((%s->%s)->((%s->(%s->(!%s->%s)))->(%s->(!%s->%s))))))\n((%s|%s)->((%s->%s)->((%s->(%s->(!%s->%s)))->(%s->(!%s->%s)))))\n(((%s|%s)->(%s->%s))->(((%s|%s)->((%s->%s)->((%s->(%s->(!%s->%s)))->(%s->(!%s->%s)))))->((%s|%s)->((%s->(%s->(!%s->%s)))->(%s->(!%s->%s))))))\n(((%s|%s)->((%s->%s)->((%s->(%s->(!%s->%s)))->(%s->(!%s->%s)))))->((%s|%s)->((%s->(%s->(!%s->%s)))->(%s->(!%s->%s)))))\n((%s|%s)->((%s->(%s->(!%s->%s)))->(%s->(!%s->%s))))\n(!%s->(!%s->!%s))\n((!%s->(!%s->!%s))->((%s|%s)->(!%s->(!%s->!%s))))\n((%s|%s)->(!%s->(!%s->!%s)))\n((!%s->(!%s->!%s))->(%s->(!%s->(!%s->!%s))))\n(((!%s->(!%s->!%s))->(%s->(!%s->(!%s->!%s))))->((%s|%s)->((!%s->(!%s->!%s))->(%s->(!%s->(!%s->!%s))))))\n((%s|%s)->((!%s->(!%s->!%s))->(%s->(!%s->(!%s->!%s)))))\n(((%s|%s)->(!%s->(!%s->!%s)))->(((%s|%s)->((!%s->(!%s->!%s))->(%s->(!%s->(!%s->!%s)))))->((%s|%s)->(%s->(!%s->(!%s->!%s))))))\n(((%s|%s)->((!%s->(!%s->!%s))->(%s->(!%s->(!%s->!%s)))))->((%s|%s)->(%s->(!%s->(!%s->!%s)))))\n((%s|%s)->(%s->(!%s->(!%s->!%s))))\n((%s->!%s)->((%s->(!%s->(!%s->!%s)))->(%s->(!%s->!%s))))\n(((%s->!%s)->((%s->(!%s->(!%s->!%s)))->(%s->(!%s->!%s))))->((%s|%s)->((%s->!%s)->((%s->(!%s->(!%s->!%s)))->(%s->(!%s->!%s))))))\n((%s|%s)->((%s->!%s)->((%s->(!%s->(!%s->!%s)))->(%s->(!%s->!%s)))))\n(((%s|%s)->(%s->!%s))->(((%s|%s)->((%s->!%s)->((%s->(!%s->(!%s->!%s)))->(%s->(!%s->!%s)))))->((%s|%s)->((%s->(!%s->(!%s->!%s)))->(%s->(!%s->!%s))))))\n(((%s|%s)->((%s->!%s)->((%s->(!%s->(!%s->!%s)))->(%s->(!%s->!%s)))))->((%s|%s)->((%s->(!%s->(!%s->!%s)))->(%s->(!%s->!%s)))))\n((%s|%s)->((%s->(!%s->(!%s->!%s)))->(%s->(!%s->!%s))))\n(((%s|%s)->(%s->(!%s->(!%s->!%s))))->(((%s|%s)->((%s->(!%s->(!%s->!%s)))->(%s->(!%s->!%s))))->((%s|%s)->(%s->(!%s->!%s)))))\n(((%s|%s)->((%s->(!%s->(!%s->!%s)))->(%s->(!%s->!%s))))->((%s|%s)->(%s->(!%s->!%s))))\n((%s|%s)->(%s->(!%s->!%s)))\n((%s->(!%s->%s))->((%s->((!%s->%s)->((!%s->!%s)->!!%s)))->(%s->((!%s->!%s)->!!%s))))\n(((%s->(!%s->%s))->((%s->((!%s->%s)->((!%s->!%s)->!!%s)))->(%s->((!%s->!%s)->!!%s))))->((%s|%s)->((%s->(!%s->%s))->((%s->((!%s->%s)->((!%s->!%s)->!!%s)))->(%s->((!%s->!%s)->!!%s))))))\n((%s|%s)->((%s->(!%s->%s))->((%s->((!%s->%s)->((!%s->!%s)->!!%s)))->(%s->((!%s->!%s)->!!%s)))))\n(((%s|%s)->(%s->(!%s->%s)))->(((%s|%s)->((%s->(!%s->%s))->((%s->((!%s->%s)->((!%s->!%s)->!!%s)))->(%s->((!%s->!%s)->!!%s)))))->((%s|%s)->((%s->((!%s->%s)->((!%s->!%s)->!!%s)))->(%s->((!%s->!%s)->!!%s))))))\n(((%s|%s)->((%s->(!%s->%s))->((%s->((!%s->%s)->((!%s->!%s)->!!%s)))->(%s->((!%s->!%s)->!!%s)))))->((%s|%s)->((%s->((!%s->%s)->((!%s->!%s)->!!%s)))->(%s->((!%s->!%s)->!!%s)))))\n((%s|%s)->((%s->((!%s->%s)->((!%s->!%s)->!!%s)))->(%s->((!%s->!%s)->!!%s))))\n(((%s|%s)->(%s->((!%s->%s)->((!%s->!%s)->!!%s))))->(((%s|%s)->((%s->((!%s->%s)->((!%s->!%s)->!!%s)))->(%s->((!%s->!%s)->!!%s))))->((%s|%s)->(%s->((!%s->!%s)->!!%s)))))\n(((%s|%s)->((%s->((!%s->%s)->((!%s->!%s)->!!%s)))->(%s->((!%s->!%s)->!!%s))))->((%s|%s)->(%s->((!%s->!%s)->!!%s))))\n((%s|%s)->(%s->((!%s->!%s)->!!%s)))\n((%s->(!%s->!%s))->((%s->((!%s->!%s)->!!%s))->(%s->!!%s)))\n(((%s->(!%s->!%s))->((%s->((!%s->!%s)->!!%s))->(%s->!!%s)))->((%s|%s)->((%s->(!%s->!%s))->((%s->((!%s->!%s)->!!%s))->(%s->!!%s)))))\n((%s|%s)->((%s->(!%s->!%s))->((%s->((!%s->!%s)->!!%s))->(%s->!!%s))))\n(((%s|%s)->(%s->(!%s->!%s)))->(((%s|%s)->((%s->(!%s->!%s))->((%s->((!%s->!%s)->!!%s))->(%s->!!%s))))->((%s|%s)->((%s->((!%s->!%s)->!!%s))->(%s->!!%s)))))\n(((%s|%s)->((%s->(!%s->!%s))->((%s->((!%s->!%s)->!!%s))->(%s->!!%s))))->((%s|%s)->((%s->((!%s->!%s)->!!%s))->(%s->!!%s))))\n((%s|%s)->((%s->((!%s->!%s)->!!%s))->(%s->!!%s)))\n(((%s|%s)->(%s->((!%s->!%s)->!!%s)))->(((%s|%s)->((%s->((!%s->!%s)->!!%s))->(%s->!!%s)))->((%s|%s)->(%s->!!%s))))\n(((%s|%s)->((%s->((!%s->!%s)->!!%s))->(%s->!!%s)))->((%s|%s)->(%s->!!%s)))\n((%s|%s)->(%s->!!%s))\n(!!%s->%s)\n((!!%s->%s)->((%s|%s)->(!!%s->%s)))\n((%s|%s)->(!!%s->%s))\n((!!%s->%s)->(%s->(!!%s->%s)))\n(((!!%s->%s)->(%s->(!!%s->%s)))->((%s|%s)->((!!%s->%s)->(%s->(!!%s->%s)))))\n((%s|%s)->((!!%s->%s)->(%s->(!!%s->%s))))\n(((%s|%s)->(!!%s->%s))->(((%s|%s)->((!!%s->%s)->(%s->(!!%s->%s))))->((%s|%s)->(%s->(!!%s->%s)))))\n(((%s|%s)->((!!%s->%s)->(%s->(!!%s->%s))))->((%s|%s)->(%s->(!!%s->%s))))\n((%s|%s)->(%s->(!!%s->%s)))\n((%s->!!%s)->((%s->(!!%s->%s))->(%s->%s)))\n(((%s->!!%s)->((%s->(!!%s->%s))->(%s->%s)))->((%s|%s)->((%s->!!%s)->((%s->(!!%s->%s))->(%s->%s)))))\n((%s|%s)->((%s->!!%s)->((%s->(!!%s->%s))->(%s->%s))))\n(((%s|%s)->(%s->!!%s))->(((%s|%s)->((%s->!!%s)->((%s->(!!%s->%s))->(%s->%s))))->((%s|%s)->((%s->(!!%s->%s))->(%s->%s)))))\n(((%s|%s)->((%s->!!%s)->((%s->(!!%s->%s))->(%s->%s))))->((%s|%s)->((%s->(!!%s->%s))->(%s->%s))))\n((%s|%s)->((%s->(!!%s->%s))->(%s->%s)))\n(((%s|%s)->(%s->(!!%s->%s)))->(((%s|%s)->((%s->(!!%s->%s))->(%s->%s)))->((%s|%s)->(%s->%s))))\n(((%s|%s)->((%s->(!!%s->%s))->(%s->%s)))->((%s|%s)->(%s->%s)))\n((%s|%s)->(%s->%s))\n((%s->%s)->((%s->%s)->((%s|%s)->%s)))\n(((%s->%s)->((%s->%s)->((%s|%s)->%s)))->((%s|%s)->((%s->%s)->((%s->%s)->((%s|%s)->%s)))))\n((%s|%s)->((%s->%s)->((%s->%s)->((%s|%s)->%s))))\n(((%s|%s)->(%s->%s))->(((%s|%s)->((%s->%s)->((%s->%s)->((%s|%s)->%s))))->((%s|%s)->((%s->%s)->((%s|%s)->%s)))))\n(((%s|%s)->((%s->%s)->((%s->%s)->((%s|%s)->%s))))->((%s|%s)->((%s->%s)->((%s|%s)->%s))))\n((%s|%s)->((%s->%s)->((%s|%s)->%s)))\n(((%s|%s)->(%s->%s))->(((%s|%s)->((%s->%s)->((%s|%s)->%s)))->((%s|%s)->((%s|%s)->%s))))\n(((%s|%s)->((%s->%s)->((%s|%s)->%s)))->((%s|%s)->((%s|%s)->%s)))\n((%s|%s)->((%s|%s)->%s))\n(((%s|%s)->(%s|%s))->(((%s|%s)->((%s|%s)->%s))->((%s|%s)->%s)))\n(((%s|%s)->((%s|%s)->%s))->((%s|%s)->%s))\n((%s|%s)->%s)\n((%s|%s)->!%s)->!(%s|%s)\n!(%s|%s)\n" sa sb sa sb sa sa sb sa sa sb sa sa sb sa sa sb sa sa sa sb sa sa sb sa sb sa sb sb sa sb sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sa sa sa sa sa sa sb sa sa sa sa sb sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sb sa sa sa sa sa sa sa sa sa sa sb sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sb sa sa sa sa sa sb sa sa sa sa sa sb sa sa sa sa sb sa sa sa sa sa sa sa sa sa sa sb sa sa sa sa sa sa sa sb sa sa sa sa sa sa sa sa sa sa sb sa sa sa sa sa sa sa sb sa sa sa sa sa sa sa sb sa sa sa sa sa sb sa sa sa sa sa sa sa sb sa sa sa sb sa sa sa sa sa sa sa sb sa sa sa sb sa sa sb sb sb sb sb sb sa sb sb sb sb sa sb sb sb sb sa sb sb sa sb sb sb sb sa sb sb sb sa sb sb sb sb sa sb sb sb sa sb sb sb sa sb sa sa sb sa sa sb sa sb sa sa sb sa sb sa sa sb sa sa sb sa sb sa sa sb sb sa sa sb sa sb sa sa sb sb sa sa sb sb sa sb sb sb sb sb sb sa sb sb sb sb sa sb sb sb sb sb sb sb sb sb sb sb sb sa sb sb sb sb sb sa sb sb sb sb sb sb sb sb sb sb sb sb sb sb sb sb sb sb sb sb sb sb sb sa sb sb sb sb sb sb sb sb sb sb sa sb sb sb sb sb sb sb sb sb sb sa sb sb sb sb sa sb sb sb sb sb sb sb sb sb sb sa sb sb sb sb sb sb sb sa sb sb sb sb sb sb sb sb sb sb sa sb sb sb sb sb sb sb sa sb sb sb sb sb sb sb sa sb sb sb sb sb sa sb sb sb sb sb sb sb sa sb sb sb sa sb sb sb sb sb sb sb sa sb sb sb sa sb sb sb sa sb sa sb sa sa sb sa sb sa sa sb sa sb sa sb sa sa sb sa sb sa sb sa sa sb sa sb sa sb sa sb sa sb sa sa sb sa sb sa sb sa sb sa sb sa sa sb sa sb sa sb sa sb sa sb sa sb sa sa sb sa sb sa sb sa sb sa sb sa sb sa sa sb sa sb sa sb sa sa sb sa sb sa sb sa sb sa sb sa sb sa sa sb sb sa sb sa sb sa sa sb sa sb sa sb sa sb sa sb sa sb sa sa sb sb sa sb sa sb sa sa sb sb sa sb sa sb sa sb sa sb sb sa sb sa sb sb sa sb sa sb sb sa sb sb sa sb sb sb sa sb sb sa sb sb sb sa sb sa sb sb sa sb sb sb sa sb sa sb sb sa sb sb sb sa sb sa sb sb sa sb sa sb sb sa sb sb sb sa sb sa sb sb sb sa sb sa sb sb sa sb sb sb sa sb sa sb sb sb sa sb sa sb sb sb sa sb sb sb sb sb sa sb sb sa sb sb sb sb sb sa sb sb sa sb sa sb sb sb sb sb sa sb sb sa sb sa sb sb sb sb sb sa sb sb sa sb sa sb sb sb sa sb sb sb sb sb sa sb sb sa sb sa sb sb sb sa sb sb sa sb sa sb sb sb sb sb sa sb sb sa sb sa sb sb sb sa sb sb sa sb sa sb sb sb sa sb sb sa sb sb sa sb sb sa sb sa sb sb sa sb sa sb sb sa sb sb sa sb sb sb sa sb sb sa sb sb sb sa sb sa sb sb sa sb sb sb sa sb sa sb sb sa sb sb sb sa sb sa sb sb sa sb sa sb sb sa sb sb sb sa sb sa sb sb sb sa sb sa sb sb sa sb sb sb sa sb sa sb sb sb sa sb sa sb sb sb sa sb sb sb sb sb sa sb sb sa sb sb sb sb sb sa sb sb sa sb sa sb sb sb sb sb sa sb sb sa sb sa sb sb sb sb sb sa sb sb sa sb sa sb sb sb sa sb sb sb sb sb sa sb sb sa sb sa sb sb sb sa sb sb sa sb sa sb sb sb sb sb sa sb sb sa sb sa sb sb sb sa sb sb sa sb sa sb sb sb sa sb sb sa sb sa sb sb sb sa sb sa sb sb sb sa sb sb sa sb sa sb sb sa sb sa sb sb sb sa sb sb sa sb sa sb sb sa sb sa sb sb sa sb sb sa sb sb sa sb sa sb sa sb sa sb sa sb sa sb sb sa sb sa sb sa sb sa sb sa sa sb sb sa sb sb sa sb sa sb sa sb sa sb sa sa sb sb sa sb sb sa sb sa sb sa sb sa sb sa sa sb sb sa sb sa sb sb sa sb sb sa sb sa sb sa sb sa sb sa sa sb sb sa sb sa sb sa sb sa sb sa sa sb sb sa sb sb sa sb sa sb sa sb sa sb sa sa sb sb sa sb sa sb sa sb sa sb sa sa sb sb sa sb sa sb sa sb sa sb sa sa sb sb sa sb sa sb sa sa sb sb sa sb sa sb sa sb sa sb sa sa sb sb sa sb sa sa sb sb sa sb sa sb sa sb sa sb sa sa sb sb sa sb sa sa sb sb sa sb sa sb sa sb sb sa sb sa sb sa sb sa sb sb sa sb sa sb sa sa sb sb sa sb sb sa sb sa sb sa sa sb sb sa sb sb sa sb sa sb sa sa sb sb sa sb sa sb sb sa sb sb sa sb sa sb sa sa sb sb sa sb sa sb sa sa sb sb sa sb sb sa sb sa sb sa sa sb sb sa sb sa sb sa sa sb sb sa sb sa sb sa sa sb sb sa sb sa sa sb sb sa sb sa sb sa sa sb sb sa sa sb sb sa sb sa sb sa sa sb sb sa sa sb sb sa sa sa sa sa sa sb sa sa sa sb sa sa sa sa sb sa sa sa sa sb sa sa sa sb sa sa sb sa sa sa sb sa sa sb sa sa sa sb sa sa sa sb sa sa sb sa sa sa sb sb sa sa sa sb sa sa sb sa sa sa sb sb sa sa sa sb sb sa sa sb sa sb sa sa sb sa sb sa sb sa sa sb sa sa sb sb sa sb sa sa sb sa sa sb sb sa sb sa sa sb sa sa sb sb sa sa sb sb sa sb sa sa sb sa sa sb sb sa sa sb sa sa sb sb sa sb sa sa sb sa sa sb sb sa sa sb sa sa sb sb sa sa sb sa sa sb sb sa sa sa sb sb sa sa sb sa sa sb sb sa sa sb sb sa sa sb sa sa sb sb sa sa sb sb sa sa sa sb sa sa sb sa sa sa sb sa sa sb sa sa sb sa sa sb sa sa sb sa sa sb sa sa sb sa sa sb sa sa sb sa sa sa sb sa sa sb sa sa sb sa sa sb sb sa sa sb sa sa sb sa sa sb sa sa sb sa sa sb sb sa sa sb sa sa sb sb sa sa sb sa sa sb sb sa sa sb sb sa sa sb sa sa sb sa sb sa sa sb sb sa sa sb sa sa sb sa sb sa sa sb sa sb sa sa sb sa sb sa sb sa sb sa sa sb sa sa sb sa sb sa sa sb sa sa sb sa sa sb sa sa sb sa sb);  
    buf;
  end 
  | (false, true, Disj) -> begin
    (bprintf buf "%s\n%s->%s|%s\n%s|%s\n" sb sb sa sb sa sb);
    buf;
  end
  | (true, false, Disj) -> begin
    (bprintf buf "%s\n%s->%s|%s\n%s|%s\n" sa sa sa sb sa sb);
    buf;
  end
  | (true, true, Disj) -> begin
    (bprintf buf "%s\n%s->%s|%s\n%s|%s\n" sa sa sa sb sa sb);
    buf;
  end
  | (false, false, Impl) -> begin
    (bprintf buf "!%s\n(!%s->(%s->!%s))\n(%s->!%s)\n!%s\n(!%s->(%s->!%s))\n(%s->!%s)\n(%s->(%s->%s))\n(%s->((%s->%s)->%s))\n((%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s)))\n((%s->((%s->%s)->%s))->(%s->%s))\n(%s->%s)\n((!%s->%s)->((!%s->!%s)->!!%s))\n(((!%s->%s)->((!%s->!%s)->!!%s))->(%s->((!%s->%s)->((!%s->!%s)->!!%s))))\n(%s->((!%s->%s)->((!%s->!%s)->!!%s)))\n(%s->(!%s->%s))\n((%s->(!%s->%s))->(%s->(%s->(!%s->%s))))\n(%s->(%s->(!%s->%s)))\n((%s->%s)->((%s->(%s->(!%s->%s)))->(%s->(!%s->%s))))\n((%s->(%s->(!%s->%s)))->(%s->(!%s->%s)))\n(%s->(!%s->%s))\n(!%s->(!%s->!%s))\n((!%s->(!%s->!%s))->(%s->(!%s->(!%s->!%s))))\n(%s->(!%s->(!%s->!%s)))\n((%s->!%s)->((%s->(!%s->(!%s->!%s)))->(%s->(!%s->!%s))))\n((%s->(!%s->(!%s->!%s)))->(%s->(!%s->!%s)))\n(%s->(!%s->!%s))\n((%s->(!%s->%s))->((%s->((!%s->%s)->((!%s->!%s)->!!%s)))->(%s->((!%s->!%s)->!!%s))))\n((%s->((!%s->%s)->((!%s->!%s)->!!%s)))->(%s->((!%s->!%s)->!!%s)))\n(%s->((!%s->!%s)->!!%s))\n((%s->(!%s->!%s))->((%s->((!%s->!%s)->!!%s))->(%s->!!%s)))\n((%s->((!%s->!%s)->!!%s))->(%s->!!%s))\n(%s->!!%s)\n(!!%s->%s)\n((!!%s->%s)->(%s->(!!%s->%s)))\n(%s->(!!%s->%s))\n((%s->!!%s)->((%s->(!!%s->%s))->(%s->%s)))\n((%s->(!!%s->%s))->(%s->%s))\n(%s->%s)\n" sa sa sa sa sa sa sb sb sa sb sa sb sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sb sa sb sa sb sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sa sb sa sa sa sb sa sa sa sb sa sa sa sa sa sb sa sa sb sa sa sa sb sa sa sb sa sa sb sa sa sb sa sa sb sa sa sa sb sa sa sa sb sa sa sa sa sa sb sa sa sb sa sa sa sb sa sa sb sa sa sb sa sa sb sa sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sa sb sa sb sa sb sa sb sa sb sa sb sa sb sb sb sb sb sa sb sb sa sb sb sa sb sa sb sb sa sb sa sb sb sa sb sa sb);
    buf;
  end 
  | (false, true, Impl) -> begin
    (bprintf buf "(%s)->((%s)->(%s))\n(%s)\n(%s)->(%s)\n" sb sa sb sb sa sb);
    buf;
  end
  | (true, false, Impl) -> begin
    (bprintf buf "%s\n!%s\n!%s->((%s->%s)->!%s)\n(%s->%s)->!%s\n(%s->((%s->%s)->%s))\n((%s->%s)->%s)\n((%s->%s)->((%s->%s)->(%s->%s)))\n(((%s->%s)->((%s->%s)->(%s->%s)))->(((%s->%s)->(((%s->%s)->(%s->%s))->(%s->%s)))->((%s->%s)->(%s->%s))))\n(((%s->%s)->(((%s->%s)->(%s->%s))->(%s->%s)))->((%s->%s)->(%s->%s)))\n((%s->%s)->(((%s->%s)->(%s->%s))->(%s->%s)))\n((%s->%s)->(%s->%s))\n(((%s->%s)->%s)->(((%s->%s)->(%s->%s))->((%s->%s)->%s)))\n(((%s->%s)->(%s->%s))->((%s->%s)->%s))\n((%s->%s)->%s)\n((%s->%s)->%s)->(((%s->%s)->!%s)->!(%s->%s))\n((%s->%s)->!%s)->!(%s->%s)\n!(%s->%s)\n" sa sb sb sa sb sb sa sb sb sa sa sb sa sa sb sa sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sb sa sa sb sa sb sa sb sb sa sb sa sb sa sb sb sa sb sb sa sb sb sa sb sb sa sb sa sb sb sa sb sa sb);
    buf;
  end
  | (true, true, Impl) -> begin
    (bprintf buf "(%s)->((%s)->(%s))\n(%s)\n(%s)->(%s)\n" sb sa sb sb sa sb);
    buf;
  end;;


let prf () = 
  let _get _ss bset =
    let _ret = ref false in
    for i = 0 to (Array.length !vars - 1) do
      if !vars.(i) = _ss then _ret := ((bset land (1 lsl i)) <> 0);
    done;
    (!_ret)
  in
  let rec gen tree bset =
    match tree with
    | Binop (Conj, a, b) -> begin
      let (va, sa) = (gen a bset) in
      let (vb, sb) = (gen b bset) in
      Buffer.add_buffer sa sb;
      Buffer.add_buffer sa (get12 va vb (string_of_tree a) (string_of_tree b) Conj);
      (va && vb, sa);        
    end
    | Binop (Disj, a, b) -> begin
      let (va, sa) = (gen a bset) in
      let (vb, sb) = (gen b bset) in
      Buffer.add_buffer sa sb;
      Buffer.add_buffer sa (get12 va vb (string_of_tree a) (string_of_tree b) Disj);
      (va || vb, sa);        
    end 
    | Binop (Impl, a, b) ->  begin
      let (va, sa) = (gen a bset) in
      let (vb, sb) = (gen b bset) in
      Buffer.add_buffer sa sb;
      Buffer.add_buffer sa (get12 va vb (string_of_tree a) (string_of_tree b) Impl);
      ((not va) || vb, sa);
    end
    | Neg (s) -> begin
      let buf = Buffer.create 2 in
      let (vv, ss) = (gen s bset) in
      let sa = (string_of_tree s) in
      Buffer.add_buffer buf ss;
      if (not vv) then (bprintf buf "!%s\n" sa) else (bprintf buf "%s\n%s->(!!!%s->%s)\n!!!%s->%s\n!!!%s->!%s\n(!!!%s->%s)->((!!!%s->!%s)->!!!!%s)\n(!!!%s->!%s)->!!!!%s\n!!!!%s\n!!!!%s->!!%s\n!!%s\n" sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa);
      ((not vv), buf)
    end
    | Var (s) -> begin
      let buf = Buffer.create 2 in
      let vv = (_get s bset) in
      Buffer.add_string buf (if vv then "" else "!");
      Buffer.add_string buf s;
      Buffer.add_string buf "\n";
      (vv, buf)
    end
    in
  for i = 0 to ((1 lsl (Array.length !vars)) - 1) do
    let ttlbuf = ref (Buffer.create 64) in
    let (vv, ss) = (gen !alpha i) in
    for j = 0 to (Array.length !vars - 1) do
      Buffer.add_string !ttlbuf (if (j > 0) then "," else "");
      Buffer.add_string !ttlbuf (if ((i land (1 lsl j)) <> 0) then "" else "!");
      Buffer.add_string !ttlbuf !vars.(j);
    done;
    Buffer.add_string !ttlbuf "|-";
    Buffer.add_string !ttlbuf (string_of_tree !alpha);
    Buffer.add_string !ttlbuf "\n";
    Buffer.add_buffer !ttlbuf ss;
    for j = 0 to (Array.length !vars - 1) do
      let list2 = ref (Array.make 0 "") in
      let ttls = Buffer.contents !ttlbuf in
      let lst = ref 0 in
      while !lst < (String.length ttls) do
        let nxt = (String.index_from ttls !lst '\n') in
        list2 := Array.append !list2 [|(String.sub ttls !lst (nxt - !lst))|];
        lst := nxt + 1;   
      done;
      ttlbuf := (take2 !list2);
    done;
    (* fprintf oc "%s\n"(Buffer.contents !ttlbuf); *)
    let tss = (Buffer.contents !ttlbuf) in
    fprintf oc "%s" (String.sub tss ((String.index tss '\n') + 1) ((String.length tss) - (String.index tss '\n') - 1));  
      
  done;
  for i = 0 to (Array.length !vars - 1) do
    let sa = !vars.(i) in
    fprintf oc "%s->(%s|!%s)\n(%s->(%s|(!%s)))->((%s->(%s|(!%s)))->(%s->(%s|(!%s))))\n((%s->(%s|(!%s)))->((%s->(%s|(!%s)))->(%s->(%s|(!%s)))))->((%s->(%s|(!%s)))->(((%s->(%s|(!%s)))->(%s->(%s|(!%s))))->(%s->(%s|(!%s)))))->((%s->(%s|(!%s)))->(%s->(%s|(!%s))))\n((%s->(%s|(!%s)))->(((%s->(%s|(!%s)))->(%s->(%s|(!%s))))->(%s->(%s|(!%s)))))->((%s->(%s|(!%s)))->(%s->(%s|(!%s))))\n((%s->(%s|(!%s)))->(((%s->(%s|(!%s)))->(%s->(%s|(!%s))))->(%s->(%s|(!%s)))))\n(%s->(%s|(!%s)))->(%s->(%s|(!%s)))\n((!(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s)))))\n((!(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s)))))->((%s->(%s|(!%s))))->((!(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s)))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s)))))\n(((!(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s)))))->(((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))->((!(%s|(!%s)))->(!(%s|(!%s))))))\n(((!(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s)))))->(((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))->((!(%s|(!%s)))->(!(%s|(!%s))))))->((%s->(%s|(!%s))))->(((!(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s)))))->(((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))->((!(%s|(!%s)))->(!(%s|(!%s))))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s)))))->(((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))->((!(%s|(!%s)))->(!(%s|(!%s))))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s))))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s)))))->(((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))->((!(%s|(!%s)))->(!(%s|(!%s)))))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))->((!(%s|(!%s)))->(!(%s|(!%s)))))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s)))))->(((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))->((!(%s|(!%s)))->(!(%s|(!%s)))))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))->((!(%s|(!%s)))->(!(%s|(!%s)))))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))->((!(%s|(!%s)))->(!(%s|(!%s)))))\n((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))\n((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))->((%s->(%s|(!%s))))->((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s))))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))->((!(%s|(!%s)))->(!(%s|(!%s))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s))))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(!(%s|(!%s)))))->((!(%s|(!%s)))->(!(%s|(!%s))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s))))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s))))\n((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))\n((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((%s->(%s|(!%s))))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))\n(%s->(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))\n(((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))))\n(((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))))->((%s->(%s|(!%s))))->(((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))))\n(%s->(%s|(!%s)))->(((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))))\n((%s->(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))->(((%s->(%s|(!%s)))->(((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))))\n(((%s->(%s|(!%s)))->(((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->(%s->(%s|(!%s)))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->(%s->(%s|(!%s)))))->((%s->(%s|(!%s))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(%s->(%s|(!%s)))))\n(%s->(%s|(!%s)))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(%s->(%s|(!%s)))))\n((%s->(%s|(!%s)))->(%s->(%s|(!%s))))->(((%s->(%s|(!%s)))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(%s->(%s|(!%s))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(%s->(%s|(!%s))))))\n(((%s->(%s|(!%s)))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(%s->(%s|(!%s))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(%s->(%s|(!%s))))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->(%s->(%s|(!%s))))\n(((!(%s|(!%s)))->(%s->(%s|(!%s))))->(((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))))\n(((!(%s|(!%s)))->(%s->(%s|(!%s))))->(((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))))->((%s->(%s|(!%s))))->(((!(%s|(!%s)))->(%s->(%s|(!%s))))->(((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->(%s->(%s|(!%s))))->(((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->(%s->(%s|(!%s)))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(%s->(%s|(!%s))))->(((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(%s->(%s|(!%s))))->(((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((%s->(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))\n((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))\n((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))->((%s->(%s|(!%s))))->((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))\n(((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))->((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))))\n(((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))->((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))))->((%s->(%s|(!%s))))->(((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))->((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))->((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))->((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))->((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))\n(((!(%s|(!%s)))->(!(%s|(!%s))))->(((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))->((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))))\n(((!(%s|(!%s)))->(!(%s|(!%s))))->(((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))->((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))))->((%s->(%s|(!%s))))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))->((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))->((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s)))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))\n(((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))->(((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->(!%s))))\n(((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))->(((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->(!%s))))->((%s->(%s|(!%s))))->(((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))->(((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->(!%s))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))->(((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->(!%s))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->(%s->(!(%s|(!%s))))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))->(((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->(!%s)))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->(!%s)))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(%s->(!(%s|(!%s)))))->(((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->(!%s)))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->(!%s)))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->(!%s)))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->(!%s))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(!%s))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((%s->(!(%s|(!%s))))->(!%s)))->((!(%s|(!%s)))->(!%s))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(!%s))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->(!%s))\n!(%s|!%s)->!%s\n(!%s)->(%s|!%s)\n(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))\n(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((%s->(%s|(!%s))))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))\n(%s->(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))\n((((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))))\n((((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))))->((%s->(%s|(!%s))))->((((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))))\n(%s->(%s|(!%s)))->((((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))))\n((%s->(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))->(((%s->(%s|(!%s)))->((((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))))\n(((%s->(%s|(!%s)))->((((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))\n((!%s)->(%s|(!%s)))\n((!%s)->(%s|(!%s)))->((%s->(%s|(!%s))))->((!%s)->(%s|(!%s)))\n(%s->(%s|(!%s)))->((!%s)->(%s|(!%s)))\n(((!%s)->(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(%s|(!%s)))))\n(((!%s)->(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(%s|(!%s)))))->((%s->(%s|(!%s))))->(((!%s)->(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(%s|(!%s)))))\n(%s->(%s|(!%s)))->(((!%s)->(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(%s|(!%s)))))\n((%s->(%s|(!%s)))->((!%s)->(%s|(!%s))))->(((%s->(%s|(!%s)))->(((!%s)->(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(%s|(!%s))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(%s|(!%s))))))\n(((%s->(%s|(!%s)))->(((!%s)->(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(%s|(!%s))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(%s|(!%s))))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(%s|(!%s))))\n(((!(%s|(!%s)))->((!%s)->(%s|(!%s))))->(((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))))\n(((!(%s|(!%s)))->((!%s)->(%s|(!%s))))->(((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))))->((%s->(%s|(!%s))))->(((!(%s|(!%s)))->((!%s)->(%s|(!%s))))->(((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!%s)->(%s|(!%s))))->(((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(%s|(!%s)))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!%s)->(%s|(!%s))))->(((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!%s)->(%s|(!%s))))->(((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!%s)->(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))\n((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))\n((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))->((%s->(%s|(!%s))))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))\n(((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))->((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))))\n(((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))->((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))))->((%s->(%s|(!%s))))->(((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))->((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))->((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))->((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))->((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))\n(((!(%s|(!%s)))->(!(%s|(!%s))))->(((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))))\n(((!(%s|(!%s)))->(!(%s|(!%s))))->(((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))))->((%s->(%s|(!%s))))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->(!(%s|(!%s)))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(!(%s|(!%s))))->(((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))\n(((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))->(((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(!(!%s)))))\n(((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))->(((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(!(!%s)))))->((%s->(%s|(!%s))))->(((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))->(((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(!(!%s)))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))->(((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(!(!%s)))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->((!%s)->(!(%s|(!%s))))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))->(((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(!(!%s))))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(!(!%s))))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->((!%s)->(!(%s|(!%s)))))->(((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(!(!%s))))))->((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(!(!%s))))))\n(%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(!(!%s))))\n((%s->(%s|(!%s)))->((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s)))))->(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(!(!%s)))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(!(!%s)))))\n(((%s->(%s|(!%s)))->(((!(%s|(!%s)))->(((!%s)->(!(%s|(!%s))))->(!(!%s))))->((!(%s|(!%s)))->(!(!%s)))))->((%s->(%s|(!%s)))->((!(%s|(!%s)))->(!(!%s)))))\n(%s->(%s|(!%s)))->((!(%s|(!%s)))->(!(!%s)))\n!(%s|!%s)->!!%s\n(!(%s|!%s)->!%s)->(!(%s|!%s)->!!%s)->(!!(%s|!%s))\n(!(%s|!%s)->!!%s)->!!(%s|!%s)\n!!(%s|!%s)\n!!(%s|!%s)->(%s|!%s)\n%s|!%s\n" sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa sa; 
  done;
  for i = 0 to (Array.length !vars - 1) do
    for j = 0 to ((1 lsl (Array.length !vars - i - 1)) - 1) do
      fprintf oc "(%s->" !vars.(i);
      for k = (i + 1) to (Array.length !vars - 1) do
        fprintf oc "%s" (if ((j land (1 lsl (k - i - 1))) <> 0) then "" else "!");
        fprintf oc "%s->" !vars.(k);
      done;
      fprintf oc "%s)->" (string_of_tree !alpha);

      fprintf oc "(!%s->" !vars.(i);
      for k = (i + 1) to (Array.length !vars - 1) do
        fprintf oc "%s" (if ((j land (1 lsl (k - i - 1))) <> 0) then "" else "!");
        fprintf oc "%s->" !vars.(k);
      done;
      fprintf oc "%s)->" (string_of_tree !alpha);

      fprintf oc "(%s|!%s)->" !vars.(i) !vars.(i);
      for k = (i + 1) to (Array.length !vars - 1) do
        fprintf oc "%s" (if ((j land (1 lsl (k - i - 1))) <> 0) then "" else "!");
        fprintf oc "%s->" !vars.(k);
      done;
      fprintf oc "%s" (string_of_tree !alpha);
      fprintf oc "\n";


      fprintf oc "(!%s->" !vars.(i);
      for k = (i + 1) to (Array.length !vars - 1) do
        fprintf oc "%s" (if ((j land (1 lsl (k - i - 1))) <> 0) then "" else "!");
        fprintf oc "%s->" !vars.(k);
      done;
      fprintf oc "%s)->" (string_of_tree !alpha);

      fprintf oc "(%s|!%s)->" !vars.(i) !vars.(i);
      for k = (i + 1) to (Array.length !vars - 1) do
        fprintf oc "%s" (if ((j land (1 lsl (k - i - 1))) <> 0) then "" else "!");
        fprintf oc "%s->" !vars.(k);
      done;
      fprintf oc "%s" (string_of_tree !alpha);
      fprintf oc "\n";



      fprintf oc "(%s|!%s)->" !vars.(i) !vars.(i);
      for k = (i + 1) to (Array.length !vars - 1) do
        fprintf oc "%s" (if ((j land (1 lsl (k - i - 1))) <> 0) then "" else "!");
        fprintf oc "%s->" !vars.(k);
      done;
      fprintf oc "%s" (string_of_tree !alpha);
      fprintf oc "\n";


      for k = (i + 1) to (Array.length !vars - 1) do
        fprintf oc "%s" (if ((j land (1 lsl (k - i - 1))) <> 0) then "" else "!");
        fprintf oc "%s->" !vars.(k);
      done;
      fprintf oc "%s" (string_of_tree !alpha);
      fprintf oc "\n";
    done;
  done;
  let cur = ref (!alpha) in
  while (!cur <> !tail) do
    match !cur with
    | Binop (Impl, a, b) -> begin
      fprintf oc "%s\n" (string_of_tree a);      
      fprintf oc "%s\n" (string_of_tree b);
      cur := b;
    end;
  done; 
  fprintf oc "%s" (string_of_tree !tail);   
  ;;


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
  else begin
    fprintf oc "%s-" (String.sub !_s_tmp 0 (String.index !_s_tmp '='));
    fprintf oc "%s\n" (String.sub !_s_tmp ((String.index !_s_tmp '=') + 1) ((String.length !_s_tmp) - ((String.index !_s_tmp '=') + 1)));
    prf ();
  end;;

prep ();;

close_out oc;;
close_in ic;;