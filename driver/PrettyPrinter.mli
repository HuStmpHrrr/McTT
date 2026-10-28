val format_expression : Format.formatter -> McttExtracted.Syntax.Cst.expression -> unit
val format_exp : Format.formatter -> McttExtracted.Syntax.exp -> unit
val format_nf : Format.formatter -> McttExtracted.Syntax.nf -> unit

val format_main_result :
  Format.formatter -> McttExtracted.Entrypoint.main_result -> unit

(* The parsed source of a unit, by its path, for the names its
   declarations give in messages; the driver sets it to its loader. *)
val unit_cst : (string list -> McttExtracted.Syntax.Cst.prog option) ref

(* The text [format_main_result] prints for each eval of a successful run,
   in order; [None] for any other result. *)
val eval_outputs : McttExtracted.Entrypoint.main_result -> string list option
