(* timer.ml -- custom profiling code *)

type stack = Stack of float list * int

exception Bad_stack of string
exception Bad_prefix of string
exception No_timing_events
exception Equal_paths
exception Unequal_paths

type time_event_rec = { proc: string
		      ; depth: int
		      ; time: float
		      }
and time_event = Time_event of time_event_rec

(* globals *)
let time_events : time_event list ref = ref []
let times_table : (string,stack) Hashtbl.t = Hashtbl.create 100
let call_tbl = Hashtbl.create 100
let max_indent = 12
(* end globals *)

let flush_time_events () =
  time_events := []

(* depth of all calls to instrumented procedures *)
let total_depth = ref 0

let dump_times_table n = 
  let _ = Printf.printf "*** Times table %n: ***\n%!" n in 
  let _ = Hashtbl.iter (fun k _ -> Printf.printf "key: %s\n%!" k) times_table in
  Printf.printf "*** End times table: ***\n%!"

(* maintain stack of times for each instrumented procedure *)
let push_time s tm = 
  try 
    let Stack (curr,ct) = Hashtbl.find times_table s in
    let ct_incr = ct + 1 in
    Hashtbl.replace times_table s (Stack (tm :: curr,ct_incr))
  with Not_found -> 
    Hashtbl.add times_table s (Stack ([tm],0))
	
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

(* cons event onto list *)
let add_event t = 
  time_events := t :: !time_events

(* length-n prefix of a list *)
let get_prefix lst n =
  let _ = if n < 0 then raise (Bad_prefix "Negative length") in
  let len = List.length lst in
  let _ = if n > len then raise (Bad_prefix "Too long") in
  let rec tail_loop lst' ct accum =
    if ct = 0 then (
      List.rev accum
    )
    else (
      tail_loop (List.tl lst') (ct - 1) (List.hd lst' :: accum)
    )
  in
  tail_loop lst n []

(* length-n suffix of a list *)
let get_suffix lst n =
  let lst_rev = get_prefix (List.rev lst) n in
  List.rev lst_rev

let add_call_to_tbl path (Time_event t) =
  try
    let tm = Hashtbl.find call_tbl path in
    Hashtbl.replace call_tbl path (tm +. t.time)
  with Not_found ->
    Hashtbl.add call_tbl path t.time

let populate_call_tbl () =
  let rec populate_loop events path curr_depth =
    match events with
    | [] -> ()
    | ((Time_event t) as te::rest) ->
      let (new_path,new_depth) =
	(* invariant: curr_depth is length of path - 1 *)
	(* t.depth should be no greater than curr_depth + 1 *)
	if t.depth <= curr_depth then (
	  let suffix = get_suffix path t.depth in
	  (t.proc :: suffix,t.depth)
	)
	else if t.depth = curr_depth + 1 then (
	  (t.proc :: path,t.depth)
	)
	else ( (* should not happen, but pretend it's OK *)
	  let _ = 
	    Printf.printf "Unexpected increase in depth\n";
	    Printf.printf "Proc: %s  Current depth: %d  Event depth: %d\n" t.proc curr_depth t.depth;
	    Printf.printf "Path: ";
	    List.iter (Printf.printf "%s | ") path;
	    Printf.printf "\n%!"
	  in
	  (t.proc :: path,curr_depth + 1)
	)
      in
      let _ = add_call_to_tbl new_path te in
      populate_loop rest new_path new_depth
  in
  let _ = Hashtbl.clear call_tbl in
  populate_loop !time_events [] (-1)

let rec is_path_prefix path_shorter path_longer =
  match (path_shorter,path_longer) with
  | ([],path_longer) -> true
  | (h1::t1,h2::t2) when h1 = h2 -> is_path_prefix t1 t2
  | _ -> false

(* compare equal-length paths *)
let compare_equal_paths lst1 lst2 =
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
	  compare_equal_paths rev1 (get_prefix rev2 len1)
	)
      )
      else if len2 < len1 then (
	if is_path_prefix rev2 rev1 then (
	  1 
	)
	else (
	  compare_equal_paths (get_prefix rev1 len2) rev2
	)
      )
      else (  
	compare_equal_paths rev1 rev2
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

let indent n ?(ch = ' ') =
  let bound = min n max_indent in
  for i = 0 to bound - 1 do
    Printf.printf "%c" ch
  done

(* the procedures we're interested in profiling *)
let interesting_procedures = [ "cl_rewrite_clause_tac" ]

let print_call_tree () =
  match !time_events with
  | [] -> raise No_timing_events
  | ((Time_event t)::rest) -> 
    if List.mem t.proc interesting_procedures then (
      let _ = populate_call_tbl () in
      let call_tree = build_call_tree () in
      let prn_elt (path,tm) =
	let _ = indent ((List.length path) - 1) ~ch:'+' in
	Printf.printf "%s: %0.4f\n%!" (List.hd path) tm 
      in
      List.iter prn_elt call_tree
    )
 
let start_timer s =
  let tm = Unix.gettimeofday () in
  let _ = push_time s tm in
  if !total_depth = 0 then (
    flush_time_events ()
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
      add_event (Time_event { proc = s; depth = !total_depth; time = tm_msec })
    );
    if !total_depth = 0 then (
      print_call_tree ()
    )
  with (* should never get exception here *)
  | Bad_stack s -> Printf.printf "Missing call on stack: %s\n%!" s
  | exn -> (
    Printf.printf "stop_timer, got exception: %s\n%!" (Printexc.to_string exn); 
    (* raise exn *)
  )
