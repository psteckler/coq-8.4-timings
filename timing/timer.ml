type stack = Stack of float list * int

exception Bad_stack of string

let times_table : (string,stack) Hashtbl.t = Hashtbl.create 100
let cumulative_table : (string,float) Hashtbl.t = Hashtbl.create 100

let depth = ref 0

let dump_times_table () = 
  let _ = Printf.printf "*** Times table: ***\n%!" in 
  let _ = Hashtbl.iter (fun k _ -> Printf.printf "key: %s\n%!" k) times_table in
  Printf.printf "*** End times table: ***\n%!"

let push_time s tm = 
  try 
    let Stack (curr,ct) = Hashtbl.find times_table s in
    let ct_incr = ct + 1 in
    let _ = Hashtbl.replace times_table s (Stack (tm :: curr,ct_incr)) in
      (* let _ = dump_times_table () in  *)
    ct_incr
  with Not_found -> 
      (*      let _ = Printf.printf "Adding stack for %s\n%!" s in  *)
    let _ = Hashtbl.add times_table s (Stack ([tm],0)) in
      (*      let _ = dump_times_table () in *)
    0
	
let pop_time s =
  try
    (* let _ = dump_times_table () in *)
    let Stack (curr,ct) = Hashtbl.find times_table s in
    (* let _ = Printf.printf "Removing stack for %s\n%!" s in *)
    let _ = Hashtbl.remove times_table s in
    let _ = 
      if ct > 0 then (
(*	let _ = Printf.printf "Re-adding stack for %s\n%!" s in  *)
	Hashtbl.add times_table s (Stack (List.tl curr,ct - 1)) 
      )
    in
(*    let _ = dump_times_table () in  *)
    (List.hd curr,ct)
  with Not_found -> 
    let _ = Printf.printf "Warning: %s not found when popping stack\n%!" in
    let _ = flush stdout in
    let _ = dump_times_table () in
(*    (max_float,0) *) 
    raise (Bad_stack ("Name: " ^ s))

let max_indent = 12

let depth = ref 0

let indent n = 
  let bound = min n max_indent in
  for i = 0 to bound - 1 do
    Printf.printf " "
  done

let add_cumulative s tm_msec =
  try 
    let cum = Hashtbl.find cumulative_table s in
    Hashtbl.replace cumulative_table s (cum +. tm_msec) 
  with Not_found ->
    Hashtbl.add cumulative_table s tm_msec

let print_cumulative () =
  if Hashtbl.length cumulative_table > 0 then (
    Printf.printf " *** Cumulative times for callees:\n%!";
    let f s tm = Printf.printf " For %s, total is %0.3f msec\n%!" s tm in
    let _ = Hashtbl.iter f cumulative_table in
    Printf.printf " *** End cumulative times:\n%!"
  )

let start_timer s =
  let tm = Unix.gettimeofday () in
  let ct = push_time s tm in
  if !depth = 0 then (
    Hashtbl.clear cumulative_table
  );
  indent !depth;
  Printf.printf "Start: %s @ depth %d, total depth %d\n%!" s ct !depth;
  incr depth

let stop_timer s = 
  let tm1 = Unix.gettimeofday () in
  let (tm0,ct) = pop_time s in
  let tm_msec = (tm1 -. tm0) *. 1000.0 in 
  decr depth;
  if !depth = 0 then (
    print_cumulative ();
  )
  else if ct == 0 then (
    add_cumulative s tm_msec;
  );
  indent !depth;
  Printf.printf "Time:  %s @ depth %d, total depth %d = %0.3f msec\n%!" s ct !depth tm_msec
