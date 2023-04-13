(* ocamlc unix.cma main.ml -o a *)

open Stdlib
open Format
open Char
open String
open Unix

let retrieve_answer fd =
  let s= (Bytes.create 1) in 
  let rec retrieve_answer_aux fd acc =
try 
  (*  let _ = Format.print_string "in retrieve" in
  let _ = Format.print_flush () in *)
  
(*  let _ = Format.print_string acc in
  let _ = Format.print_flush () in *)
  let _ = Unix.read fd s 0 1 in
  (*if (c==0) then
    acc 
  else*)
(*    let _ = Format.print_string (Bytes.to_string s) in
    let _ = Format.print_string " " in 
    let _ = Format.print_flush () in *)
    retrieve_answer_aux fd (cat acc (Bytes.to_string s))
with Unix_error (EWOULDBLOCK,_,_) | Unix_error (EAGAIN,_,_) -> (*let  _ = Format.print_string "erreur" in let _ = Format.print_flush () in*) acc
in retrieve_answer_aux fd empty


let check s t nb =
  let l = length t in
let rec check_aux s t i =
  if(i<0) then true else s.[i+nb]=t.[i] && check_aux s t (i-1)in
check_aux s t (l-1);;

let rec inter min max =
  if (min=max) then [max] else min::(inter (min+1) max)

let is_empty l =
  match l with
    [] -> true
  | _::xs -> false

(* s corresponds to t from position nb in s : returns the position *)

let check_subterm s t =
  let di = length s - length t in 
  let l = inter 0 di in 
  List.filter (fun x -> (check s t x)) l 

let read_from_until s pos c =
  let rec read_next s pos c acc =
    if (s.[pos]==c) then acc else
      read_next s (pos+1) c (cat acc (make 1 s.[pos]))
in read_next s pos c empty

let rec check_barre s i nb =
if(nb=0) then true else s.[i+nb]='=' && check_barre s i (nb-1);;

let check_all s i =
  s.[i] = '\\' && s.[i+1]='n' && check_barre s (i+2) 27 && s.[i+30] = '\\' && s.[i+31]='n';;

let rec number_of_goals s i acc =
try
let p = String.index_from s i '\\' in 
if (check_all s p) then (number_of_goals s (p+28) (p::acc)) else number_of_goals s (p+1) acc
with _ -> acc;;

let query_ast n = cat "(Query ((sid " (cat (string_of_int n) ") (pp ((pp_format PpStr)))) Ast)")

let query_goals n = cat "(Query ((sid " (cat (string_of_int n) ") (pp ((pp_format PpStr)))) Goals)")
  
let clean_string s = 
  let ls = String.length s in
  let rec clean_aux s i acc =
    if (i>=ls)
    then acc
    else if (s.[i]=='\\' && s.[i+1]=='\\')
    then clean_aux s (i+2) (String.cat acc (String.make 1 s.[i]))
    else clean_aux s (i+1) (String.cat acc (String.make 1 s.[i]))
    in clean_aux s 0 String.empty
   
(*let display_string_char s =
  let rec display_aux s p =
    if (p>0) then
      let _ = display_aux s (p-1) in 
      let _ = Format.print_string "(" in
      let _ = Format.print_string (make 1 s.[p]) in 
      print_string ")" else ()
  
  in display_aux s ((String.length s) -1)
*)
let upper_case s =
  let c = s.[0] in
  c='A' || c='B' || c='C'|| c='D'|| c='E'|| c='F' || c='G' || c='H' || c='I' || c='J' || c='K' ||c='L'|| c='M' ||
    c='N' || c='O'|| c='P'|| c='Q'|| c='R' || c='S' || c='T' || c='U' || c='V' || c='W' ||c='X'|| c='Y' || c='Z'

let generate_proof_script fd_in fd_out nb result =
  let output = open_out result in
  let rec generate_proof_aux i nb subgoals =
    if (i>nb) then ()
    else
      let string_to_send = query_ast i in
      let _ = Format.print_string string_to_send in
      let _ = Format.print_flush () in 
      let _ = Unix.write_substring fd_out string_to_send 0 (length string_to_send) in
      let _ = Unix.sleepf (1./.10.) in (* random value to leave time for serapi to answer *)
      let ans = retrieve_answer fd_in in

      let ls = length "(ObjList((CoqString" in 
      let v = check_subterm ans "(ObjList((CoqString" in
      let st = if (not (is_empty v))
               then
                 let p = (List.hd v) in
                 read_from_until ans (p+(ls+1)) (if (ans.[p+ls]=' ') then ')' else '\"')
               else
             "IGNORE_AST" in 
      (*                let _ = output_string output "SCRIPT>" in*)
      (*let _ = output_string output (clean_string st) in*)
      (*                let _ = output_string output "<SCRIPT" in*)
      (*                                output_string output "\n"  in *)
      
      (*      let _ = Unix.sleepf (1./.2.) in*)
      let _ = Format.print_string st in
      let _ = Format.print_flush () in 
      let string2 = query_goals i in 
      let _ = Format.print_string string2 in
      let _ = Format.print_flush () in 
      let _ = Unix.write_substring fd_out string2 0 (length string2) in
      let _ = Unix.sleepf (1./.10.) in (* random value to leave time for serapi to answer *)
      let ans2 = retrieve_answer fd_in in

      let v2 = check_subterm ans2 "(ObjList((CoqString" in
      let st2 = if (not (is_empty v2)) then
                let p2 = (List.hd v2) in
                read_from_until ans2 (p2+(ls+1)) (if (ans2.[p2+ls]=' ') then ')' else '\"')
                else "IGNORE_GOALS" in
      (*let _ = output_string output "GOALS>" in 
        let _ = output_string output (clean_string st2) in
        let _ = output_string output "<GOALS" in*)
      (*                let _ = output_string output (cat (make 1 '%') (cat (make 1 st2.[6]) (make 1 '%'))) in *)
      (*                let w = check_barre st2 20 27 in if (w) then let _ = output_string output "HERE" in *)
      (*           let xx = clean_string st2 in 
                   let _ = display_string_char xx in*)
      (*      let _ = output_string output (clean_string st) in *)
      (*                let _ = output_string output "\n" in *)
      let newsubgoals =
        if ((st2<>"IGNORE_GOALS"))(* && (not (upper_case st)))*)
        then List.length (number_of_goals (clean_string st2) 0 [])
        else subgoals in
      
      let _ = if  (st="IGNORE_AST")
              then  ()
              else
                let _ = output_string output (cat (clean_string st) "\n") in
                let _ = if ((newsubgoals>subgoals))(* && (not (upper_case st)))*) then
                          output_string output " { " else () in
                if ((newsubgoals<subgoals) && (not (upper_case st))) then output_string output " } " else () in
      (*                let _ = output_string output (string_of_int (nb_goals)) in *)
       (*output_string output (clean_string st2) *)
  (*                let nb_goals = List.length (number_of_goals st2 0 []) in 
                    output_string output (string_of_int nb_goals) in *)
  
  (*      let _ = output_string output (make 1 '\n') in *)
  (* let _ = output_string output ans2 in*)
      
      generate_proof_aux (i+1) nb newsubgoals
  in generate_proof_aux 1 nb 0

(* build_string returns a Coq sentence - a sentence which finishes with ". " *)
(* without taking into account comments *) 
let rec build_string ic acc =
try
let c = input_char ic in
  if (c=='.') then
  (let d = input_char ic in
  if ((d==' ')||(d=='\n')||(d=='}'))
  then cat acc (cat (String.make 1 c) (String.make 1 d))
  else build_string ic (cat acc (cat (String.make 1 c) (String.make 1 d))))
  else build_string ic (cat acc (String.make 1 c))

with End_of_file -> close_in ic; acc

let rec read_eval_print ic fd_in fd_out nb_iter result =
  let output = open_out result in 
  let rec read_eval_print_aux ic fd_in fd_out nb_iter =  
    try
      let s = build_string ic empty in 
      let string_to_send = cat ("(Add () \"") (cat s "\")") in
      let _ = Format.print_string s in
      let _ = Format.print_flush () in 
      (* let _ = Format.print_string string_to_send in*)
      let _ =  Unix.write_substring fd_out string_to_send 0 (length string_to_send) in 
      (*  let _ = Unix.sleepf (1./.10.) in *)
      (*let _ = Format.print_string "IO:" in *)
      (*  let _ = Format.print_flush () in*)
      (*      let _ = Unix.sleepf (1./.10.) in (* random value to leave time for serapi to answer *)*)
      let _ = retrieve_answer fd_in in
      let _ = output_string output s in
      let _ = flush output in 
      (*  let _ = Format.print_string "atleastonce:" in *)
      (*  let _ = Format.print_flush () in *)
      (*  let _ = Format.print_string ans in*)
      (*let _ = Format.print_string ":" in*)
      let _ = Format.print_flush () in 
      (* print the "s" into a new file *)
      
      read_eval_print_aux ic fd_in fd_out (nb_iter+1)
    with _ (* Bad file descriptor exception *) -> nb_iter in
  read_eval_print_aux ic fd_in fd_out nb_iter

(*
let _ = Unix.write_substring fd_out string_to_send 0 (length string_to_send) in 
let  answer = (Bytes.create 10000) in 
let _ = read fd_in answer 0 10000 in 
Format.print_string (Bytes.to_string answer)
 *)
let main () =
let _ = Printf.printf "-*- Starting up coq-lint (very experimental : Mon Apr  3 14:01:22 CEST 2023) -*-\n" in
let _ = for i = 0 to Array.length Sys.argv - 1 do
Printf.printf "[%i] %s\n" i Sys.argv.(i) done in
let filename = Sys.argv.(1) in
let _ = Format.print_string filename in
let _ = print_newline () in
let ic = open_in filename in
(*let _ = reader ic in *)
let (sertop_reading_end, main_writing_end) = Unix.pipe () in (* sending info to serapi *)
let (main_reading_end, sertop_writing_end) = Unix.pipe () in (* receiving info from serapi *)
let _ = Unix.set_nonblock main_reading_end in 
let pid = fork () in

if (pid==0) then
(* child - an instance of sertop *)
let _ = close main_reading_end in
let _ = close main_writing_end in
let _ = dup2 sertop_reading_end stdin in 
let _ = dup2 sertop_writing_end stdout in
let _ = close sertop_reading_end in
let _ = close sertop_writing_end in 
(*let _  = Format.print_string "ok-child" in *)
let _ = (*Format.print_string "wait" *)execvp "sertop" [| "sertop" (*; "--printer=human"*)|] in
let _ = Format.print_string "oops\n" in
(*let w = (Bytes.create 26) in 
let  _ = read sertop_reading_end w 0 26 in
let  _ = Format.print_string (Bytes.to_string w) in*)
()

else
(* parent - our main program *)
(* useless ends *)
let _ = close sertop_reading_end in
let _ = close sertop_writing_end in
(* duplications *)
(*let _ = dup2 main_reading_end stdin in *)
(*let _ = dup2 main_writing_end stdout in*)
(* closing duplicated ends *)
(*let _ = close main_reading_end in*)
(*let _ = close main_writing_end in*)

(*let _  = Format.print_string "ok-parent" in*)

let nb = read_eval_print ic main_reading_end main_writing_end 0 "output.v" in

let whole_exec = (cat "(Exec " (cat (string_of_int nb) ")")) in
let _ = Unix.write_substring main_writing_end whole_exec 0 (length whole_exec) in 
let _ = generate_proof_script main_reading_end main_writing_end nb "output.v" in 
let _ = kill pid 15 in 
(*let _ = Format.print_string (string_of_int nb) in *)
let _ = wait () in 
let _ = Format.print_string "-*- end of execution -*-\n" in
Format.print_flush ()
;;
(*
let s = build_string ic empty in
let _ = Format.print_string s in
let string_to_send = cat ("(Add () \"") (cat s "\")") in
let _ = Format.print_string ("->:"^string_to_send^":") in
let _ = Format.print_string (string_of_int (length string_to_send)) in
let _ = read_eval_print ic stdin main_writing_end in
(*let _ = Unix.write_substring main_writing_end string_to_send 0 (length string_to_send)*)
()*)
;;


main ();;
(* add a wait in the parent to synchronize the exits *)



(*let ic = open_in filename in
let () =
  for i = 0 to Array.length Sys.argv - 1 do
    Printf.printf "[%i] %s\n" i Sys.argv.(i)
  done*)
