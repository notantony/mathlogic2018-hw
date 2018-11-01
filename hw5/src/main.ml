open Tree;;
open Buffer;;
open Printf;;
open Str;;


let (ic, oc) = (open_in "input.txt", open_out "output.txt");;
let data = (open_in "src/data.txt")
let (>>) x f = f x;;
let clear_ws s = Str.global_replace (Str.regexp "[\r\n\t ]") "" s;; 

let alpha = ref ("A" >> Lexing.from_string >> Parser.main Lexer.main);;

let sz = ref (0);;
let v = Array.make_matrix 17 17 0;;
let prev = Array.make 17 0;;

let vars = Array.make 17 ([||]);;
let names = ref [];;
let anames = ref [||];;

let ini_arr () =
	sz := 0;
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

		check_sum ();
		check_mpl ();
		check_distr ();
		check_impl ();
		find_zero ();
		find_one ();
		check_not ();

		let any = ref false in
		let run_all () =
			let homes = Hashtbl.create 16 in
			let run () = 
				let print_all () =
					fprintf oc "%d\n" n;
					for i = 0 to n - 1 do
						for k = 0 to n - 1 do
							if leq.(i).(k) = 1 then fprintf oc "%d " (k + 1);
						done;
						fprintf oc "\n";
					done;
					let flag = ref false in
					for i = 0 to (Array.length !anames) - 1 do
						if (!flag) then fprintf oc ", " else flag := true;
						fprintf oc "%s=%d" !anames.(i) ((Hashtbl.find homes !anames.(i)) + 1);
					done;
				in
				let rec upd tree =
					match tree with
					| Binop(Conj, a, b) -> (mpl.(upd a).(upd b))
					| Binop(Disj, a, b) -> (sum.(upd a).(upd b))
					| Binop(Impl, a, b) -> (impl.(upd a).(upd b))
					| Neg(exp) -> (nt.(upd exp))
					| Var(s) -> (Hashtbl.find homes s)
				in
				if ((upd !alpha) = !one) then false
				else ((print_all ()); true);
			in
			let rec wh k =
				if (not !any) then begin
					if (k = (Array.length !anames)) then (if (run ()) then any := true;)
					else for i = 0 to n - 1 do 
						Hashtbl.add homes !anames.(k) i;
						wh (k + 1);
					done;
				end;
			in
			wh 0;
		in
		
		run_all ();
		!any;
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
			()
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

	let rec get_names tree = 
		match tree with
		| Binop(_, a, b) -> (get_names a; get_names b)
		| Neg(a) -> (get_names a)
		| Var(a) -> (if not (List.mem a !names) then names := (a :: !names);)
	in
	alpha := (input_line ic) >> clear_ws >> Lexing.from_string >> Parser.main Lexer.main;
	get_names !alpha;
	anames := Array.of_list !names;
	let ok = ref false in
	(try
		while true do
			let tmp = (input_line data) in
			if (not !ok) then begin
				if (tmp = "=") then begin
					if (build ()) then (ok := true)
					else (ini_arr (); cur := (-1); cur_h := (-1););
				end else (read_one tmp);
			end;
		done;
	with End_of_file -> ());
	if (not !ok) then fprintf oc "Формула общезначима";
;;



read_data ();;



close_out oc;;
close_in ic;;
close_in data;;
