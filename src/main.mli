val retrieve_answer : Unix.file_descr -> string
val check : string -> string -> int -> bool
val inter : int -> int -> int list
val is_empty : 'a list -> bool
val check_subterm : string -> string -> int list
val read_from_until : string -> int -> char -> string
val check_barre : string -> int -> int -> bool
val check_all : string -> int -> bool
val number_of_goals : string -> int -> int list -> int list
val query_ast : int -> string
val query_goals : int -> string
val clean_string : string -> string
val upper_case : string -> bool
val generate_proof_script :
  Unix.file_descr -> Unix.file_descr -> int -> string -> unit
val build_string : in_channel -> string -> bool -> string
val read_eval_print :
  in_channel -> Unix.file_descr -> Unix.file_descr -> int -> string -> int
val main : unit -> unit
