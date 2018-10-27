open Tree;;
open Buffer;;
open Printf;;
open Str;;


let (ic, oc) = (open_in "input.txt", open_out "output.txt");;

let scan_int () =
	let s = (input_line ic) in
	(int_of_string s);
;;

let scan_ints () =
	let tmp = (input_line ic) in
	let s = (String.concat "" [tmp; if (tmp.[(String.length tmp) - 1] <> ' ') then " " else ""]) in
	let last = ref 0 in
	let arr = ref [] in
	while !last < (String.length s) do
		let nxt = (String.index_from s !last ' ') in
		arr := ((int_of_string (String.sub s !last (nxt - !last))) :: !arr);
		last := nxt + 1;	
	done;
	!arr;
;;

let n = scan_int ();;

let one = ref (-1);;
let zero = ref (-1);;

let a = Array.make_matrix n n 0;;
let leq = Array.make_matrix n n 0;;
let geq = Array.make_matrix n n 0;;
let sum = Array.make_matrix n n 0;;
let mpl = Array.make_matrix n n 0;;
let impl = Array.make_matrix n n 0;;
let st = Array.make n 0;;

let fail_a = ref (-1);;
let fail_b = ref (-1);;
let fail_c = ref (-1);;

let ini_arr () =
	for i = 0 to (n - 1) do
		for j = 0 to (n - 1) do
			a.(i).(j) <- 0;
			leq.(i).(j) <- 0;
			geq.(i).(j) <- 0;
			sum.(i).(j) <- -1;
			mpl.(i).(j) <- -1;
			impl.(i).(j) <- -1;
		done;
		a.(i).(i) <- 1;
		st.(i) <- 0;

	done; 
;;
ini_arr ();;

let fill_data () =
	for i = 0 to (n - 1) do
		let arr = scan_ints () in
		List.iter (fun (x) -> begin a.(i).(x - 1) <- 1; end) arr;
	done
;;
fill_data ();;

let ini_leq () =
	let rec dfs s c f =
		st.(c) <- 1;
		if (c = f) 
		then leq.(s).(f) <- 1
		else for i = 0 to (n - 1) do
			if ((st.(i) = 0) && (a.(c).(i) = 1)) then (dfs s i f);
		done;
	in
	for i = 0 to (n - 1) do
		for j = 0 to (n - 1) do
			for k = 0 to (n - 1) do
					st.(k) <- 0;
			done;
			dfs i i j;
		done;
	done;
;;
ini_leq ();;

let ini_geq () =
	for i = 0 to (n - 1) do
		for j = 0 to (n - 1) do
			geq.(i).(j) <- leq.(j).(i);
		done;
	done;
;;
ini_geq ();;

let check_sum () =
	let any_fail = ref false in
	for i = 0 to (n - 1) do
		for j = 0 to (n - 1) do
			for k = 0 to (n - 1) do
				if (leq.(i).(k) = 1) && (leq.(j).(k) = 1) then begin
					let bad = ref false in
					for tst = 0 to (n - 1) do
						if (leq.(i).(tst) = 1) && (leq.(j).(tst) = 1) && (leq.(k).(tst) <> 1) then bad := true;
					done; (* TODO: two !bad-s? *)
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
;;

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
;;

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
;;


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
;;


let find_one () = 
	for i = 0 to (n - 1) do
		let bad = ref false in
		for tst = 0 to (n - 1) do
			if (leq.(i).(tst) <> 1) then bad := true;
		done;
		if (not !bad) then zero := i;
	done;
;;

let find_zero () = 
	for i = 0 to (n - 1) do
		let bad = ref false in
		for tst = 0 to (n - 1) do
			if (geq.(i).(tst) <> 1) then bad := true;
		done;
		if (not !bad) then one := i;
	done;
;;


let check_not () =
	let any_fail = ref false in 
	for i = 0 to (n - 1) do
		if (sum.(i).(impl.(i).(!zero)) <> !one) then begin
			any_fail := true;
			fail_a := i;
		end;
	done;
	if (!any_fail = true) then fprintf oc "Не булева алгебра: %d+~%d" (!fail_a + 1) (!fail_a + 1);	
	not !any_fail;
;; 

if (check_sum ()) then begin
	if (check_mpl ()) then begin
		if (check_distr ()) then begin
			if (check_impl ()) then begin
				find_zero ();
				find_one ();
				if (check_not ()) then fprintf oc "Булева алгебра";
			end;
		end;
	end;
end;;

close_out oc;;
close_in ic;;