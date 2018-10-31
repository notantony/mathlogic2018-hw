open Tree;;
open Buffer;;
open Printf;;
open Str;;


let (ic, oc) = (open_in "input.txt", open_out "output.txt");;
let (>>) x f = f x;;
let clear_ws s = Str.global_replace (Str.regexp "[\r\n\t ]") "" s;; 

let alpha = ref ("A" >> Lexing.from_string >> Parser.main Lexer.main);;

let xx = ref (-1);;
let sz = ref (0);;
let v = Array.make_matrix 17 17 0;;
let prev = Array.make 17 0;;
let heads = ref [];;

let vars = Array.make 17 ([||]);;

let ini_arr () =
	for i = 0 to (17 - 1) do
		for j = 0 to (17 - 1) do
			v.(i).(j) <- 0;
		done;
		prev.(i) <- (-1);
		vars.(i) <- [||];
	done; 
;;
ini_arr ();;


let read_data () =
	let build () = 
		let check_nodes bset =
			let rec dfs c = 
				let fail = ref false in
				if ((bset land (1 lsl c)) = 0) then fail := true;
				for i = 0 to (!sz - 1) do
					if (v.(c).(i) = 1) && (not (dfs i)) then fail := true;
				done;
				not !fail;
			in
			let fail = ref false in 
			for i = 0 to (!sz - 1) do 
				if ((bset land (1 lsl i)) <> 0) && (not (dfs i)) then fail := true;
			done;
			not !fail;
		in 
		let nodes = ref [] in
		for i = 0 to ((1 lsl !sz) - 1) do
			if (check_nodes i) then nodes := (i :: !nodes);
		done;
		
		let fail_a = ref (-1) in
		let fail_b = ref (-1) in
		let fail_c = ref (-1) in
		
		let one = ref (-1) in
		let zero = ref (-1) in
		

		let n = List.length !nodes in
		
		let leq = Array.make_matrix n n 0 in
		let geq = Array.make_matrix n n 0 in
		let sum = Array.make_matrix n n 0 in
		let mpl = Array.make_matrix n n 0 in
		let impl = Array.make_matrix n n 0 in
		let nt = Array.make n 0 in

		let ini_arr () =
			for i = 0 to (n - 1) do
				for j = 0 to (n - 1) do
					leq.(i).(j) <- 0;
					geq.(i).(j) <- 0;
					sum.(i).(j) <- -1;
					mpl.(i).(j) <- -1;
					impl.(i).(j) <- -1;
				done;
				nt.(i) <- -1;		
			done;
		in
		ini_arr ();

		let arr = Array.of_list !nodes in
		for i = 0 to (Array.length arr) - 1 do
			for j = 0 to (Array.length arr) - 1 do
				if ((arr.(i) land arr.(j)) = arr.(i)) && ((arr.(i) lor arr.(j)) = arr.(j)) then begin
					leq.(i).(j) <- 1;
					geq.(j).(i) <- 1;
				end;
			done;
		done;
		let check_sum () =
			let any_fail = ref false in
			for i = 0 to (n - 1) do
				for j = 0 to (n - 1) do
					for k = 0 to (n - 1) do
						if (leq.(i).(k) = 1) && (leq.(j).(k) = 1) then begin
							let bad = ref false in
							for tst = 0 to (n - 1) do
								if (leq.(i).(tst) = 1) && (leq.(j).(tst) = 1) && (leq.(k).(tst) <> 1) then bad := true;
							done;
							if (not !bad) then sum.(i).(j) <- k;
						end;
					done;
					if (sum.(i).(j) = -1) then begin
						any_fail := true;
						fail_a := i;
						fail_b := j;
					end;
				done;
			done;
			if (!any_fail = true) then fprintf oc "Операция '+' не определена: %d+%d" (!fail_a + 1) (!fail_b + 1);
			not !any_fail;
		in
		let check_mpl () =
			let any_fail = ref false in
			for i = 0 to (n - 1) do
				for j = 0 to (n - 1) do
					for k = 0 to (n - 1) do
						if (geq.(i).(k) = 1) && (geq.(j).(k) = 1) then begin
							let bad = ref false in
							for tst = 0 to (n - 1) do
								if (geq.(i).(tst) = 1) && (geq.(j).(tst) = 1) && (geq.(k).(tst) <> 1) then bad := true;
							done;
							if (not !bad) then mpl.(i).(j) <- k;
						end;
					done;
					if (mpl.(i).(j) = -1) then begin
						any_fail := true;
						fail_a := i;
						fail_b := j;
					end;
				done;
			done;
			if (!any_fail = true) then fprintf oc "Операция '*' не определена: %d*%d" (!fail_a + 1) (!fail_b + 1);
			not !any_fail;
		in
		let check_distr () =
			let any_fail = ref false in
			for i = 0 to (n - 1) do
				for j = 0 to (n - 1) do
					for k = 0 to (n - 1) do
						if (mpl.(i).(sum.(j).(k)) <> sum.(mpl.(i).(j)).(mpl.(i).(k))) then begin
							any_fail := true;
							fail_a := i;
							fail_b := j;
							fail_c := k;
						end;
					done;
				done;
			done;
			if (!any_fail = true) then fprintf oc "Нарушается дистрибутивность: %d*(%d+%d)" (!fail_a + 1) (!fail_b + 1) (!fail_c + 1);
			not !any_fail;		
		in
		let check_impl () =
			let any_fail = ref false in
			for i = 0 to (n - 1) do
				for j = 0 to (n - 1) do
					for k = 0 to (n - 1) do
						if (leq.(mpl.(i).(k)).(j) = 1) then begin
							let bad = ref false in
							for tst = 0 to (n - 1) do
								if (leq.(mpl.(i).(tst)).(j) = 1) && (geq.(k).(tst) <> 1) then bad := true;
							done;
							if (not !bad) then impl.(i).(j) <- k;
						end;
					done;
					if (impl.(i).(j) = -1) then begin
						any_fail := true;
						fail_a := i;
						fail_b := j;
					end;
				done;
			done;
			if (!any_fail = true) then fprintf oc "Операция '->' не определена: %d->%d" (!fail_a + 1) (!fail_b + 1);
			not !any_fail;
		in
		let find_one () = 
			for i = 0 to (n - 1) do
				let bad = ref false in
				for tst = 0 to (n - 1) do
					if (leq.(i).(tst) <> 1) then bad := true;
				done;
				if (not !bad) then zero := i;
			done;
		in
		let find_zero () = 
			for i = 0 to (n - 1) do
				let bad = ref false in
				for tst = 0 to (n - 1) do
					if (geq.(i).(tst) <> 1) then bad := true;
				done;
				if (not !bad) then one := i;
			done;
		in
		let check_not () = 
			for i = 0 to (n - 1) do
				nt.(i) <- impl.(i).(!zero)
			done;
		in

		let set_AA () =
			let stm = Hashtbl.create 16 in
			for i = 0 to (!sz - 1) do 
				for j = 0 to (Array.length vars.(i) - 1) do
					let mask = (1 lsl i) in
					Hashtbl.add stm vars.(i).(j) (mask lor (if (Hashtbl.mem stm vars.(i).(j)) then (Hashtbl.find stm vars.(i).(j)) else 0));
				done;
			done;
			let res = Hashtbl.create 16 in
			for i = 0 to (!sz - 1) do 
				for j = 0 to (Array.length vars.(i) - 1) do
					let mask = Hashtbl.find stm vars.(i).(j) in
					let found = ref (-1) in
					for k = 0 to (Array.length arr) - 1 do
						if (arr.(k) = mask) then found := k;
					done;
					Hashtbl.add res vars.(i).(j) !found;
					(* fprintf oc "%s->%d, mask:=%d\n" vars.(i).(j) !found mask; *)
				done;
			done;
			res;
		in

		check_sum ();
		check_mpl ();
		check_distr ();
		check_impl ();
		find_zero ();
		find_one ();
		check_not ();
		let homes = set_AA () in

		let run () = 
			let also = ref [] in
			let print_all () =
				fprintf oc "%d\n" n;
				for i = 0 to n - 1 do
					for k = 0 to n - 1 do
						if leq.(i).(k) = 1 then fprintf oc "%d " (k + 1);
					done;
					fprintf oc "\n";
				done;
				let flag = ref false in
				List.iter (fun x -> if not (Hashtbl.mem homes x) then begin
					Hashtbl.add homes x (!zero + 1);
					if (!flag) then fprintf oc ", " else flag := true;
					fprintf oc "%s=%d" x (!zero + 1);
				end;) !also;
				for i = 0 to (!sz - 1) do 
					for j = 0 to (Array.length vars.(i) - 1) do
						if (Hashtbl.mem homes vars.(i).(j)) then begin
							if (!flag) then fprintf oc ", " else flag := true;
							fprintf oc "%s=%d" vars.(i).(j) ((Hashtbl.find homes vars.(i).(j)) + 1);
							while (Hashtbl.mem homes vars.(i).(j)) do
								Hashtbl.remove homes vars.(i).(j);
							done;
						end;
					done;
				done;
			in
			let rec upd tree =
				match tree with
				| Binop(Conj, a, b) -> (mpl.(upd a).(upd b))
				| Binop(Disj, a, b) -> (sum.(upd a).(upd b))
				| Binop(Impl, a, b) -> (impl.(upd a).(upd b))
				| Neg(exp) -> (nt.(upd exp))
				| Var(s) -> (if Hashtbl.mem homes s then Hashtbl.find homes s else (also := (s :: !also); !zero))
			in
			if ((upd !alpha) = !one) then fprintf oc "Не опровергает формулу"
			else print_all ();
		in
		run();

		();
	in


	let rec get_vars tree =
		match tree with
		|	Binop(Comma, a, b) -> (Array.append (get_vars a) (get_vars b));
		|	Var(a) -> ([|a|]);
	in
	let cur = ref (-1) in
	let cur_h = ref (-1) in
	let read_one s = 
		let h = String.index s '*' in
		while (!cur_h >= h) do
			cur_h := (!cur_h - 1); cur := prev.(!cur);
		done;
		if (h = 0) then begin
			 heads := (!sz :: !heads)
		end
		else if (h = (!cur_h + 1)) then begin
			prev.(!sz) <- !cur;
			v.(!cur).(!sz) <- 1;
		end;
		let raw = (clear_ws (String.sub s (h + 1) ((String.length s) - h - 1))) in
		vars.(!sz) <- if (raw <> "") then (get_vars (raw >> Lexing.from_string >> Parser.main Lexer.main)) else [||];
		cur := !sz;
		sz := (!sz + 1);
		cur_h := h;
	in

	let check_AA () =
		let rec dfs c var =
			let found = ref false in
			for i = 0 to (Array.length vars.(c) - 1) do
				if (vars.(c).(i) = var) then found := true;
			done;
			for i = 0 to (!sz - 1) do
				if (v.(c).(i) = 1) && (not (dfs i var)) then found := false;
			done;
			!found;
		in
		let fail = ref false in
		for i = 0 to (!sz - 1) do 
			for j = 0 to (Array.length vars.(i) - 1) do
				if not (dfs i vars.(i).(j)) then fail := true;
			done;
		done;
		!fail;
	in

	alpha := (input_line ic) >> clear_ws >> Lexing.from_string >> Parser.main Lexer.main;
	(try
		while true
		do
			read_one (input_line ic);
		done;
	with End_of_file -> ());
	
	if (check_AA ()) then fprintf oc "Не модель Крипке"
	else build ();
;;



read_data ();;



close_out oc;;
close_in ic;;