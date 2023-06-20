(* ocamlc unix.cma main.ml -o a *)

(* options to take into account : grep "^-R" _CoqProject | sed -e 's/ /,/2'  *)

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

(* computes the list of the elements between min and max = [min; ... ; max] *)
let rec inter min max =
  if (min=max) then [max] else min::(inter (min+1) max)

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
(*  let clean_string s = s*)
(* clean_string fixes the encoding of special characters such as \n or \ *)
let clean_string s = 
  let ls = String.length s in
  let rec clean_aux s i acc =
    if (i>=ls)
    then acc
    else
      if (s.[i]=='\\' && s.[i+1]=='n')
      then clean_aux s (i+2) (String.cat acc (String.make 1 '\n'))
      else
        if (s.[i]=='\\' && s.[i+1]=='\\')
        then clean_aux s (i+2) (String.cat acc (String.make 1 '\\')) (*(String.make 1 s.[i]))*)
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
  if (s=empty)
  then false
  else 
    let c = s.[0] in
    c='A' || c='B' || c='C'|| c='D'|| c='E'|| c='F' || c='G' || c='H' || c='I' || c='J' || c='K' ||c='L'|| c='M' ||
      c='N' || c='O'|| c='P'|| c='Q'|| c='R' || c='S' || c='T' || c='U' || c='V' || c='W' ||c='X'|| c='Y' || c='Z'

let lower_case s =
  if (s=empty)
  then false
  else 
    let c = s.[0] in
    c='a' || c='b' || c='c'|| c='d'|| c='e'|| c='f' || c='g' || c='h' || c='i' || c='j' || c='k' ||c='l'|| c='m' ||
      c='n' || c='o'|| c='p'|| c='q'|| c='r' || c='s' || c='t' || c='u' || c='v' || c='w' ||c='x'|| c='y' || c='z'

let remove_trailing_dot s = if (s=empty) then s else 
  let l=length s in 
  if s.[l-1]='.' then sub s 0 (l-1) else s

let remove_closing_par s = if (s=empty) then s else 
    let l=length s in 
    if s.[l-1]=')'then sub s 0 (l-1) else s

let remove_opening_par s = if (s=empty) then s else 
  let l=length s in 
  if (s.[0]=='(') then sub s 1 (l-1) else s

let strip_par_and_closing_dot s = if (s=empty) then s else 
  let without_dot =  remove_trailing_dot s in 
  if (without_dot.[0]=='(') then remove_opening_par (remove_closing_par without_dot) else without_dot

(* recognize the pattern tac1 by tac2., and write tac1 by (tac2) " by " *)
let split_on_string s t =
let rec split s t acc = 
  let ls = String.length s in
  let lt = String.length t in
  if (ls<lt) then [acc]  else
    if (starts_with ~prefix:t s) then [acc; sub s lt (ls-lt)] else split (sub s 1 (ls-1)) t (cat  acc (make 1 s.[0]))
in split s t empty
  
let my_secure_merge t1 t2 li =
  cat t1 (cat li (cat "(" (cat ( remove_trailing_dot t2) ").")))

let full_split s t =
  let l = split_on_string s t in
  match l with [a;b] -> my_secure_merge a b t | [a] -> s | _ -> failwith "full_split"

let rec closing_goals s =
if (s=[]) then [] else 
  let h = List.hd s in 
  if (h>0) then (h-1)::(List.tl s) else closing_goals (List.tl s) 

let rec closes_all output subgoals newsubgoals lsubgoals =
  if (lsubgoals=[])
  then output_string output " . "
  else let h =  List.hd lsubgoals in
       if (h>0)
       then if (newsubgoals<>0) then output_string output " | " else () 
       else let _ = output_string output " ]" in closes_all output subgoals newsubgoals (List.tl lsubgoals)
  
let connectives output subgoals newsubgoals lsubgoals =
(*  let _ = output_string output (string_of_int subgoals) in
  let _ = output_string output "AND" in
  let _ = output_string output (string_of_int newsubgoals) in*)
  if (newsubgoals>subgoals)
  then output_string output "; [ "
  else
    if (newsubgoals<subgoals)
    then closes_all output subgoals newsubgoals lsubgoals
    else 
      if (newsubgoals<>0) then output_string output " ; " else output_string output ""

let rec remove_structure_in_string s =
  if ((s=empty))(*||(s.[0]='\n'))*)
  then s
  else
    if (s.[0]=' ')
    then
      remove_structure_in_string (sub s 1 ((String.length s)-1))
    else
      if ((s.[0]='+')||(s.[0]='-')||(s.[0]='*'))
      then
        (sub s 1 ((String.length s)-1))
      else s
 
let output_string' x s =
  (*  let _ = Format.print_string (cat "Next line:" (cat s "\n")) in  *)
  output_string x s 

(* is_tactic checks whether the string correspond to a tactic *)
let is_tactic s =
  let s' = remove_structure_in_string s in
  (not (upper_case s'))
  
  
let generate_proof_script fd_in fd_out nb result acc =
  let output = open_out result in
  let rec generate_proof_aux i nb subgoals lsubgoals acc =
    if (i>nb) then ()
    else

        let _ = Format.print_string (cat "step #" (string_of_int i)) in
        let _ = Format.print_string "\n" in
      let string_to_send = query_ast i in
      let _ = Format.print_string string_to_send in
      let _ = Format.print_flush () in 
      let _ = Unix.write_substring fd_out string_to_send 0 (length string_to_send) in
      let _ = Unix.sleepf (1./.10.) in (* random value to leave time for serapi to answer *)
      let ans = retrieve_answer fd_in in
      let ls = length "(ObjList((CoqString" in 
      let v = check_subterm ans "(ObjList((CoqString" in
      let _ = Format.print_string (cat "ans:" ans) in
      let _ = Format.print_flush () in
      let st = if (v<>[])
               then
                 let p = (List.hd v) in
                 read_from_until ans (p+(ls+1)) (if (ans.[p+ls]=' ') then ')' else '\"')
               else
                 if (i==1) then "IGNORE_AST" else ans (*"IGNORE_AST"*) in 
      (*                let _ = output_string output "SCRIPT>" in*)
      (*let _ = output_string output (clean_string st) in*)
      (*                let _ = output_string output "<SCRIPT" in*)
      (*                                output_string output "\n"  in *)
       
      let _ = Format.print_string "st:" in 
      let _ = if (is_tactic st) then Format.print_string (cat "tactic:" st) else let _ = Format.print_string "command:" in Format.print_string (List.hd acc) in 
      let _ = Format.print_string "realst:" in 
      let _ = Format.print_string st in

      let _ = Format.print_flush () in
      let _ = Format.print_string "\n" in 
      let string2 = query_goals i in 
      (*      let _ = Format.print_string string2 in*)
      (*let _ = Format.print_string "string2:" in *)
      let _ = Format.print_string string2 in
      let _ = Format.print_flush () in
      let _ = Format.print_string "\n" in 
      let _ = Unix.write_substring fd_out string2 0 (length string2) in
      let _ = Unix.sleepf (1./.10.) in (* random value to leave time for serapi to answer *)
      let ans2 = retrieve_answer fd_in in
(*      let _ = Format.print_string "ans:" in 
      let _ = Format.print_string ans in
      let _ = Format.print_string "ans2:" in 
      let _ = Format.print_string ans2 in
      let _ = Format.print_flush () in*)
  
      let v2 = check_subterm ans2 "(ObjList((CoqString" in
      let st2 = if (v2<>[]) then
                let p2 = (List.hd v2) in
                read_from_until ans2 (p2+(ls+1)) (if (ans2.[p2+ls]=' ') then ')' else '\"')
                else "IGNORE_GOALS" in
      (*
      let _ = Format.print_string "\n" in 
      let _ = Format.print_string "st2:" in 
      let _ = Format.print_string st2 in
      let _ = Format.print_flush () in
      let _ = Format.print_string "\n" in 
      *)
      let newsubgoals =
        if ((st2<>"IGNORE_GOALS"))(* && (not (upper_case st)))*)
        then List.length (number_of_goals ((*(clean_string*) st2) 0 [])
        else subgoals in
      let newlsubgoals = if (newsubgoals>subgoals)
                         then (newsubgoals-subgoals)::lsubgoals
                         else
                           if (newsubgoals<subgoals)
                           then closing_goals lsubgoals
                           else lsubgoals in 
      let _ = if  (st="IGNORE_AST")
              then  ()
              else
                let os_aux = if (not (is_tactic st)) (*(upper_case st)*) then (List.hd acc) (*(clean_string st)*) else (strip_par_and_closing_dot (full_split (clean_string st) " by ")) in
                (*                let os = if ((newsubgoals=0) && (not (upper_case st)))then (cat os_aux ".") else os_aux in *)
                let _ = Format.print_string (cat "out:" os_aux) in
                let _ = Format.print_flush () in 
                let _ = output_string' output os_aux in
                let _ = if (upper_case st) then () else connectives output subgoals newsubgoals lsubgoals in 

               (*   if ((newsubgoals>subgoals) && (not (upper_case st)))
                        then
                          output_string output " ; [ "
                        else 
                          if ((newsubgoals<subgoals) && (not (upper_case st)))
                          then if ((lsubgoals<>[]) && (List.hd lsubgoals>0))
                               then output_string output " | "
                               else output_string output " ]"
                          else
                            if (not (upper_case st)) then output_string output " ;2 " else () in*)
                                let _ = if ((newsubgoals=0) && (not (upper_case st)))then output_string' output ".\n" else () in 
                                (*if (upper_case st) then output_string output "\n" else*) () in 
      let _ = Format.print_string (cat "end of step #" (string_of_int i)) in
      let _ = Format.print_string "\n" in 
      generate_proof_aux (i+1) nb newsubgoals newlsubgoals (List.tl acc)
  in generate_proof_aux 1 nb 0 [] ("VIGNORE_AST"::acc)

(* build_string returns a Coq sentence -
   a sentence which finishes with ". " taking comments into account *)
let rec build_string ic acc b =
  try
    let c = input_char ic in
    (*
      let _ = print_string (cat (string_of_int b) (cat ":" (make 1 c))) in 
     *)
    match c with
      '(' -> if (b<0)
           then build_string ic (cat acc (String.make 1 c)) 0
             else
               if (b mod 3 == 0)
             then build_string ic (cat acc (String.make 1 c)) (b+1)
             else
               if (b mod 3 == 1)
               then build_string ic (cat acc (String.make 1 c)) b
               else build_string ic (cat acc (String.make 1 c)) b
    | '*' -> if (b<0)
           then build_string ic (cat acc (String.make 1 c)) 0
             else
               if (b mod 3 == 0)
             then build_string ic (cat acc (String.make 1 c)) b
             else
               if (b mod 3 == 1)
               then build_string ic (cat acc (String.make 1 c)) (b+1)
               else build_string ic (cat acc (String.make 1 c)) (b-1)
    | ')' -> if (b<0)
           then build_string ic (cat acc (String.make 1 c)) 0
             else
               if (b mod 3 == 0)
             then build_string ic (cat acc (String.make 1 c)) b
             else
               if (b mod 3 == 1)
               then build_string ic (cat acc (String.make 1 c)) (b-1)
               else build_string ic (cat acc (String.make 1 c)) b
    | '.' -> if (b == 0)
             then build_string ic (cat acc (String.make 1 c)) (-1)
             else build_string ic (cat acc (String.make 1 c)) b
    | ' ' | '\n'  | '\t'  | '}' ->
       if (b == -1)
       then cat acc (String.make 1 c)
       else
         if (b mod 3 == 0)
         then build_string ic (cat acc (String.make 1 c)) b
         else
           if (b mod 3 == 1) 
           then build_string ic (cat acc (String.make 1 c)) b
           else build_string ic (cat acc (String.make 1 c)) b
    | _ -> if (b<0)
           then build_string ic (cat acc (String.make 1 c)) 0
           else 
       if (b mod 3 == 0)
           then build_string ic (cat acc (String.make 1 c)) b
           else
             if (b mod 3 == 1) 
             then build_string ic (cat acc (String.make 1 c)) (b-1)
             else build_string ic (cat acc (String.make 1 c)) b
  with End_of_file -> let _ = print_string (cat "-->" (cat acc "<--")) in close_in ic; acc



let rec list_char_to_string l =
  match l with
    [] -> empty
  | x::xs -> if (x='\\')
             then cat (make 1 '\\') (list_char_to_string xs)
             else cat (make 1 x) (list_char_to_string xs)

let rec string_to_list_char s =
  if(s=empty) then [] else s.[0]::(string_to_list_char (sub s 1 (length(s)-1)))

let rec next_is c s =
  (not (s=[])) && (List.hd s==c)
     

let rec remove_comments_aux s n acc =
  match s with
    [] -> acc
  | x::xs ->
     (*  let _ = Format.print_string (cat (string_of_int n) (cat  ":" (String.make 1 x))) in let _ = Format.print_flush () in *)
     match x with '(' ->
                   if (next_is '*' xs)
                   then remove_comments_aux (List.tl xs) (n+1) acc
                   else
                     if (n>0)
                     then remove_comments_aux xs n (acc)
                     else remove_comments_aux xs n (acc@['('])
                | '*' ->
                   (*if(n>0)
                   then *)
                   if (next_is ')' xs)
                   then if (n>0)
                        then remove_comments_aux (List.tl xs) (n-1) acc
                        else remove_comments_aux xs n  acc
                   else if (n>0)
                   then remove_comments_aux xs n acc
                   else remove_comments_aux xs n (acc@['*'])

                | ')' ->
                   if(n==0)
                   then remove_comments_aux xs n (acc@[')'])
                   else remove_comments_aux xs n (acc)
                | c -> if (n==0)
                       then remove_comments_aux xs n (acc@[c])
                       else remove_comments_aux xs n acc

let remove_comments s = list_char_to_string (remove_comments_aux (string_to_list_char s) 0 [])

let rec read_eval_print ic fd_in fd_out nb_iter result =
  (*  let output = open_out result in *)
  let rec read_eval_print_aux ic fd_in fd_out nb_iter acc =  
    try let s' = (build_string ic empty 0) in
        let _ = Format.print_string (cat "s':" s') in
        let _ = Format.print_string "\n" in 
        let _ = Format.print_string (cat "s'(without comments):" (remove_comments  s')) in
        let _ = Format.print_string "\n" in 
        let s  = remove_structure_in_string (remove_comments s') in 
        let string_to_send = (*if (s=empty) then "(Add () \" Check nat.\")" else *) cat ("(Add () \"") (cat s "\")") in
let _ = Format.print_string "->" in 
let _ = Format.print_string s in
let _ = Format.print_string "<-\n" in 
        (*        let _ = Format.print_string string_to_send in*)
      let _ = Format.print_flush () in 
      (* let _ = Format.print_string string_to_send in*)
      let _ = Unix.write_substring fd_out string_to_send 0 (length string_to_send) in
      (*  let _ = Unix.sleepf (1./.10.) in *)
      (*let _ = Format.print_string "IO:" in *)
      (*  let _ = Format.print_flush () in*)
      (*      let _ = Unix.sleepf (1./.10.) in (* random value to leave time for serapi to answer *)*)
      let _ = retrieve_answer fd_in in
      (*let _ = output_string output s in
      let _ = flush output in *)
      (*  let _ = Format.print_string "atleastonce:" in *)
      (*  let _ = Format.print_flush () in *)
      (*  let _ = Format.print_string ans in*)
      (*let _ = Format.print_string ":" in*)
      let _ = Format.print_flush () in 
      (* print the "s" into a new file *)
      (*      let _ = if (upper_case s) then output_string output (cat "uppercase" s) else () in *)
      read_eval_print_aux ic fd_in fd_out (nb_iter+1) (acc@[s'])
    with  _ (* Bad file descriptor exception *) -> let _ = print_string (cat (cat "#steps:" (string_of_int nb_iter)) "\n") in
                                                   (nb_iter,acc)  in
  read_eval_print_aux ic fd_in fd_out nb_iter []


let main () =
  let _ = print_string "-*- Starting up coq-lint (alpha version: Thu Jun  8 15:58:23 CEST 2023) -*-\n" in
  let _ = Format.print_flush () in 
  let nb_args = Array.length Sys.argv - 1 in 
  let _ = if (nb_args<1) then
            let _ = print_string (cat "usage: " (cat Sys.argv.(0) " <input.v> [ -o <output.v> ]\n")) in exit(1) in 
(*  let _ = for i = 0 to nb_args do
            Printf.printf "[%i] %s " i Sys.argv.(i) done in
  let _ = Format.print_string "\n" in *)
  let filename = Sys.argv.(1) in
  (*let _ = Format.print_string filename in*)
  (*let _ = print_newline () in*)
  let output_file = if ((nb_args>=3) && Sys.argv.(2)="-o") then Sys.argv.(3) else "one_liner.v" in 
  let _ = print_string (cat "NEW FILE:" output_file) in
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
    let current_dir = Sys.getcwd() in
    let option1 = "-R" in 
    let option2 = (cat current_dir ",GeoCoq") in 
    let _ = (*Format.print_string "wait" *)execvp "sertop" [| "sertop" ; option1; option2 (*; "--printer=human"*)|] in
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
    let vfile = output_file in (*cat "translated_files/" (Filename.basename Sys.argv.(1)) in *)
    let (nb,acc) = read_eval_print ic main_reading_end main_writing_end 0 vfile in
    
    let whole_exec = (cat "(Exec " (cat (string_of_int nb) ")")) in
    let _ = Unix.write_substring main_writing_end whole_exec 0 (length whole_exec) in 
(*    let _ = Format.print_string "running generate for this number of steps:" in 
    let _ = Format.print_string (string_of_int nb) in
    let _ = Format.print_string "\n" in *)
    let _ = Format.print_flush () in 
    let _ = generate_proof_script main_reading_end main_writing_end nb vfile acc in 
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

(*let ic = open_in filename in
let () =
  for i = 0 to Array.length Sys.argv - 1 do
    Printf.printf "[%i] %s\n" i Sys.argv.(i)
  done*)
