(* timer.ml -- custom profiling code *)

type stack = Stack of float list * int

exception Bad_stack of string
exception Bad_argument of string
exception Bad_prefix of string
exception Events_stack_mismatch
exception Equal_paths
exception Unequal_paths

type start_event = { s_proc: string
		   ; s_depth: int
		   }
and time_event = { t_proc: string
		 ; t_depth: int
		 ; t_time: float
		 }
and all_events = Start_event of start_event | Time_event of time_event

(* globals *)
let the_events : all_events list ref = ref []
let times_table : (string,stack) Hashtbl.t = Hashtbl.create 100
let call_tbl = Hashtbl.create 100
let max_indent = 99
(* end globals *)

let flush_events () = the_events := []

(* depth of all calls to instrumented procedures *)
let total_depth = ref 0

let dump_times_table n = 
  let _ = Printf.printf "*** Times table %n: ***\n%!" n in 
  let _ = Hashtbl.iter (fun k _ -> Printf.printf "key: %s\n%!" k) times_table in
  Printf.printf "*** End times table: ***\n%!"

(* maintain stack of times for each instrumented procedure *)
(* return this procedure's recursion depth *)
let push_time s tm = 
  try 
    let Stack (curr,ct) = Hashtbl.find times_table s in
    let ct_incr = ct + 1 in
    let _ = Hashtbl.replace times_table s (Stack (tm :: curr,ct_incr)) in
    ct_incr
  with Not_found -> 
    let _ = Hashtbl.add times_table s (Stack ([tm],0)) in
    0
	
let pop_time s =
  try
(*    Printf.printf "Popping procedure: %s\n%!" s; *)
    let Stack (curr,ct) = Hashtbl.find times_table s in
(*    let _ = dump_times_table 1 in *)
    let _ = Hashtbl.remove times_table s in
    let _ = 
      if ct > 0 then (
	Hashtbl.add times_table s (Stack (List.tl curr,ct - 1)) 
      )
    in
(*    let _ = dump_times_table 2 in *)
    (List.hd curr,ct)
  with Not_found ->  (* should never happen *)
    let _ = Printf.printf "Warning: %s not found when popping stack\n%!" in
    let _ = flush stdout in
    let _ = dump_times_table 3 in
    raise (Bad_stack s)

(* cons start event onto list *)
let add_start_event ev =
  match ev with
  | Start_event _ -> the_events := ev :: !the_events
  | _ -> raise (Bad_argument "add_start_event")

(* cons time event onto list *)
let add_time_event ev =
  match ev with
  | Time_event _ -> the_events := ev :: !the_events
  | _ -> raise (Bad_argument "add_time_event")

(* length-n prefix of a list *)
let get_prefix lst n =
  let _ = if n < 0 then raise (Bad_prefix "Negative length") in
  let rec loop lst' ct accum =
    if ct = 0 then (
      List.rev accum
    )
    else (
      match lst' with
      | [] -> raise (Bad_prefix "Too long")
      | (h::rest) -> loop rest (ct - 1) (h :: accum)
    )
  in
  loop lst n []

let add_call_to_tbl path t_ev =
  try
    let tm = Hashtbl.find call_tbl path in
    Hashtbl.replace call_tbl path (tm +. t_ev.t_time)
  with Not_found -> 
    Hashtbl.add call_tbl path t_ev.t_time

let populate_call_tbl () =
  let rec populate_loop events path curr_depth =
    match events with
    | [] -> ()
    | ((Start_event s_ev)::rest) ->
      (* call *)
      populate_loop rest (s_ev.s_proc :: path) (curr_depth + 1)
    | ((Time_event t_ev)::rest) ->
      (* return *)
      if path = [] || t_ev.t_proc != List.hd path then (
	raise Events_stack_mismatch
      );
      let _ = add_call_to_tbl path t_ev in
      populate_loop rest (List.tl path) (curr_depth - 1)
  in
  let _ = Hashtbl.clear call_tbl in
  populate_loop (List.rev !the_events) [] 0

let rec is_path_prefix path_shorter path_longer =
  match (path_shorter,path_longer) with
  | ([],path_longer) -> true
  | (h1::t1,h2::t2) when h1 = h2 -> is_path_prefix t1 t2
  | _ -> false

(* compare equal-length paths *)
let compare_eqlen_paths lst1 lst2 =
  if lst1 = lst2 then ( (* should never happen *)
    raise Equal_paths
  )
  else if lst1 < lst2 then (
    -1
  )
  else (
    1
  )

let build_call_tree () = 
  let unsorted = ref [] in
  let _ = Hashtbl.iter (fun path tm -> unsorted := ((path,tm) :: !unsorted)) call_tbl in
  let cmp (path1,tm1) (path2,tm2) =
    let len1 = List.length path1 in
    let len2 = List.length path2 in
    let rev1 = List.rev path1 in
    let rev2 = List.rev path2 in
    try
      if len1 < len2 then (
	if is_path_prefix rev1 rev2 then (
	  -1
	)
	else (
	  compare_eqlen_paths rev1 (get_prefix rev2 len1)
	)
      )
      else if len2 < len1 then (
	if is_path_prefix rev2 rev1 then (
	  1 
	)
	else (
	  compare_eqlen_paths (get_prefix rev1 len2) rev2
	)
      )
      else (  
	compare_eqlen_paths rev1 rev2
      )
    with Equal_paths -> ( 
      Printf.printf "Original paths were: ";
      List.iter (Printf.printf "%s; ") path1;
      Printf.printf "\nand\n%!";
      List.iter (Printf.printf "%s; ") path2;
      Printf.printf "\n%!";
      raise Equal_paths
  )
  in
  List.sort cmp !unsorted

let indent ?(ch = '|') n =
  let bound = min n max_indent in
  for i = 0 to bound - 1 do
    Printf.printf "%c " ch
  done;
  Printf.printf "%d -> " n


(* the procedures we're interested in profiling *)
let interesting_procedures = [ "cl_rewrite_clause_tac" ]

let print_call_tree () =
  match !the_events with
  | ((Time_event t)::rest) -> 
    if List.mem t.t_proc interesting_procedures then (
      let _ = populate_call_tbl () in
      let call_tree = build_call_tree () in
      let prn_elt (path,tm) =
	let _ = indent ((List.length path) - 1) in
	Printf.printf "%s: %0.4f msec\n%!" (List.hd path) tm 
      in
      List.iter prn_elt call_tree
    )
  | _ -> raise (Bad_argument "print_call_tree")
 
let start_timer s =
  let tm = Unix.gettimeofday () in
  let ct = push_time s tm in
  if !total_depth = 0 then (
    flush_events ()
  );
  (* only want to track initial call if recursive *)
  if !total_depth = 0 || ct = 0 then (
    add_start_event (Start_event { s_proc = s; s_depth = !total_depth })
  );
  (* 
  indent !total_depth;
  Printf.printf "Start: %s @ total depth %d\n%!" s !total_depth;
  *)
  incr total_depth

let stop_timer s = 
  try 
    let tm1 = Unix.gettimeofday () in
    let (tm0,ct) = pop_time s in
    let tm_msec = (tm1 -. tm0) *. 1000.0 in 
    decr total_depth;
    (*
       indent !total_depth;
       Printf.printf "Time:  %s @ depth %d, total depth %d = %0.3f msec\n%!" s ct !total_depth tm_msec;
    *)
    if !total_depth = 0 || ct = 0 then (
      add_time_event (Time_event { t_proc = s; t_depth = !total_depth; t_time = tm_msec })
    );
    if !total_depth = 0 then (
      print_call_tree ()
    )
  with (* should not happen *)
  | Bad_stack s -> Printf.printf "Missing call on stack: %s\n%!" s
  | exn -> (
    Printf.printf "stop_timer, got exception: %s\n%!" (Printexc.to_string exn); 
    raise exn
  )
