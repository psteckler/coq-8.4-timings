(*
   Compilation this file (pa_timed.ml)
     ocamlc -pp camlp5o -I `camlp5 -where` -c pa_timed.ml
   Compilation file foo.ml using TIMED_LET
     ocamlc -pp 'camlp5o ./pa_timed.cmo' foo.ml
   Checking generated source (e.g. by curiosity or for debugging)
     camlp5o ./pa_timed.cmo pr_o.cmo foo.ml
*)

#load "pa_extend.cmo";;
#load "q_MLast.cmo";;

open Pcaml

let rec expr_of_patt =
  function
  | <:patt:< $lid:s$ >> -> <:expr< $lid:s$ >>
  | <:patt:< ~{$p$ $opt:e$} >> -> <:expr< ~{$p$} >> 
  | <:patt:< ?{$p$ $opt:e$} >> -> <:expr< ~{$p$} >> 
  | p -> Ploc.raise (MLast.loc_of_patt p) (Stream.Error "case not impl")

EXTEND
  str_item: LEVEL "top"
    [ [ "TIMED_LET"; l = V (LIST1 let_binding SEP "and") ->
          let rev_l =
            List.fold_left
              (fun l (p, e) ->
               match p with
               | <:patt< $lid:f$ >> ->
                   let call =
                     let rec loop f = function
                       | <:expr< fun $p$ -> $e$ >> ->
                           loop <:expr< $f$ $expr_of_patt p$ >> e
                       | _ -> f
                     in
                     loop <:expr< $lid:f^"0"$ >> e
                   in
                   let e1 =
                     let name = <:expr< $str:f$ >> in
                     <:expr<
                       let _ = Timer.start_timer $name$ in
                       try
                         let result = $call$ in
                         let _ = Timer.stop_timer $name$ in
                         result
                       with exn ->
                         let _ = Timer.stop_timer $name$ in
                         raise exn >>
                  in
                  let e1 =
                    let rec loop = function
                      | <:expr< fun $p$ -> $e$ >> ->
                          <:expr< fun $p$ -> $loop e$ >>
                      | _ -> e1
                    in
                    loop e
                  in
                  (p, e1) ::( <:patt< $lid:f^"0"$ >>, e) :: l
               | _ ->
                   Ploc.raise (MLast.loc_of_patt p)
                     (Stream.Error "identifier expected"))
              [] (unvala l)
          in
          <:str_item< value rec $list:List.rev rev_l$ >> ] ]
  ;
END;
