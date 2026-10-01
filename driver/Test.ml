(* Unit test cases for parsing *)

open Main
open McttExtracted.Entrypoint

(** Helper definitions *)

let main_of_example s = main_of_filename ("../examples/" ^ s)

(* The programs under [examples/multi] import units of their own, looked up
   from there. *)
let main_of_multi s =
  main_of_filename ~search_root:"../examples/multi" ("../examples/multi/" ^ s)

(* Every unit needs its top level module declaration, so the small inline cases
   get a throwaway one. *)
let main_of_body body = main_of_program_string ("module Test where " ^ body ^ " end")

(** Real tests *)
(* We never expect parser timeout. 2^500 fuel should be large enough! *)

let%expect_test "Type@0 is of Type@1" =
  let _ = main_of_body "eval Type@0 : Type@1" in
  [%expect {| Evaluate Type@0 --> Type@0 : Type@1 |}]

let%expect_test "zero is of Nat" =
  let _ = main_of_body "eval zero : Nat" in
  [%expect {| Evaluate 0 --> 0 : Nat |}]

let%expect_test "zero is not of Type@0" =
  let _ = main_of_body "eval zero : Type@0" in
  [%expect {| Error: 0 is not of type Type@0 |}]

let%expect_test "succ zero is of Nat" =
  let _ = main_of_body "eval succ zero : Nat" in
  [%expect {| Evaluate 1 --> 1 : Nat |}]

let%expect_test "succ Type@0 is not of Nat (as it is ill-typed)" =
  let _ = main_of_body "eval succ Type@0 : Nat" in
  [%expect {| Error: succ Type@0 is not of type Nat |}]

let%expect_test "succ Type@0 has no inferable type" =
  let _ = main_of_body "eval succ Type@0" in
  [%expect {| Error: succ Type@0 has no inferable type |}]

let%expect_test "an unascribed eval infers its type" =
  let _ = main_of_body "eval fun (y : Nat) -> y" in
  [%expect {|
    Evaluate fun (x1 : Nat) -> x1 --> fun (x1 : Nat) -> x1
      : forall (x1 : Nat) -> Nat
    |}]

let%expect_test "several evals are reported in order" =
  let _ = main_of_body "def two : Nat := 2 end eval two eval succ two" in
  [%expect {|
    Evaluate two --> 2 : Nat
    Evaluate succ two --> 3 : Nat
    |}]

let%expect_test "an eval does not see a later definition" =
  let _ = main_of_body "eval later def later : Nat := 0 end" in
  [%expect {| Error: unbound name later |}]

let%expect_test "definitions are not allowed outside a module" =
  let _ = main_of_program_string "def x : Nat := 0 end module Test where end" in
  [%expect {|
    Error: on "def" (at line 1, column 1 - line 1, column 4): This token is
      invalid for the beginning of a program.
    |}]

let%expect_test "variable x is ill-scoped" =
  let _ = main_of_body "eval x : Type@0" in
  [%expect {| Error: unbound name x |}]

let%expect_test "identity function of Nat is of forall (x : Nat) -> Nat" =
  let _ = main_of_body "eval fun (y : Nat) -> y : forall (x : Nat) -> Nat" in
  [%expect {|
    Evaluate fun (x1 : Nat) -> x1 --> fun (x1 : Nat) -> x1
      : forall (x1 : Nat) -> Nat
    |}]

let%expect_test "recursion on a natural number that always returns zero is of \
                 Nat" =
  let _ = main_of_body
    "eval rec 3 return y . Nat | zero => 0 | succ n, r => 0 end : Nat" in
  [%expect {| Evaluate rec 3 return x1 . Nat | zero => 0 | succ x2, x3 => 0 end --> 0 : Nat |}]

let%expect_test "simple_nat.mctt works" =
  let _ = main_of_example "simple_nat.mctt" in
  [%expect {| Evaluate 4 --> 4 : Nat |}]

let%expect_test "simple_rec.mctt works" =
  let _ = main_of_example "simple_rec.mctt" in
  [%expect {|
    Evaluate fun (x1 : Nat)
               -> rec x1 return x2 . Nat | zero => 1 | succ x3, x4 => succ x4 end
      --> fun (x1 : Nat)
            -> rec x1 return x2 . Nat | zero => 1 | succ x3, x4 => succ x4 end
      : forall (x1 : Nat) -> Nat
    |}]

let%expect_test "pair.mctt works" =
  let _ = main_of_example "pair.mctt" in
  [%expect {|
    Evaluate (fun (x1 : forall (A1 : Type@0)
                               (A2 : Type@0)
                          -> Type@1)
                  (x2 : forall (A3 : Type@0)
                               (A4 : Type@0)
                               (x3 : A3)
                               (x4 : A4)
                          -> x1 A3 A4)
                  (x5 : forall (A5 : Type@0)
                               (A6 : Type@0)
                               (x6 : x1 A5 A6)
                          -> A5)
                  (x7 : forall (A7 : Type@0)
                               (A8 : Type@0)
                               (x8 : x1 A7 A8)
                          -> A8)
               -> (fun (x9 : x1 Nat (forall (x10 : Nat) -> Nat))
                    -> x7 Nat (forall (x11 : Nat) -> Nat) x9
                         (x5 Nat (forall (x12 : Nat) -> Nat) x9))
                    (x2 Nat (forall (x13 : Nat) -> Nat) 3
                      (fun (x14 : Nat) -> succ (succ x14))))
               (fun (A9 : Type@0)
                    (A10 : Type@0)
                 -> forall (A11 : Type@0)
                           (x15 : forall (x16 : A9)
                                         (x17 : A10)
                                    -> A11)
                      -> A11)
               (fun (A12 : Type@0)
                    (A13 : Type@0)
                    (x18 : A12)
                    (x19 : A13)
                    (A14 : Type@0)
                    (x20 : forall (x21 : A12)
                                  (x22 : A13)
                             -> A14)
                 -> x20 x18 x19)
               (fun (A15 : Type@0)
                    (A16 : Type@0)
                    (x23 : forall (A17 : Type@0)
                                  (x24 : forall (x25 : A15)
                                                (x26 : A16)
                                           -> A17)
                             -> A17)
                 -> x23 A15 (fun (x27 : A15)
                                 (x28 : A16)
                              -> x27))
               (fun (A18 : Type@0)
                    (A19 : Type@0)
                    (x29 : forall (A20 : Type@0)
                                  (x30 : forall (x31 : A18)
                                                (x32 : A19)
                                           -> A20)
                             -> A20)
                 -> x29 A19 (fun (x33 : A18)
                                 (x34 : A19)
                              -> x34)) --> 5 : Nat
    |}]

let%expect_test "vector.mctt works" =
  let _ = main_of_example "vector.mctt" in
  [%expect {|
    Evaluate (fun (x1 : forall (A1 : Type@0)
                               (x2 : Nat)
                          -> Type@2)
                  (x3 : forall (A2 : Type@0) -> x1 A2 0)
                  (x4 : forall (A3 : Type@0)
                               (x5 : Nat)
                               (x6 : A3)
                               (x7 : x1 A3 x5)
                          -> x1 A3 (succ x5))
                  (x8 : forall (A4 : Type@0)
                               (x9 : Nat)
                               (x10 : x1 A4 x9)
                               (x11 : forall (x12 : Nat) -> Type@1)
                               (x13 : x11 0)
                               (x14 : forall (x15 : Nat)
                                             (x16 : A4)
                                             (x17 : x11 x15)
                                        -> x11 (succ x15))
                          -> x11 x9)
               -> (fun (x18 : forall (A5 : Type@0)
                                     (x19 : Nat)
                                     (x20 : x1 A5 (succ x19))
                                -> A5)
                       (x21 : x1 (forall (x22 : Nat) -> Nat) 3)
                    -> x18 (forall (x23 : Nat) -> Nat) 2 x21 4)
                    (fun (A6 : Type@0)
                         (x24 : Nat)
                         (x25 : x1 A6 (succ x24))
                      -> x8 A6 (succ x24) x25
                           (fun (x26 : Nat)
                             -> rec x26 return x27 . Type@0
                                | zero => Nat
                                | succ x28, A7 => A6
                                end)
                           0
                           (fun (x29 : Nat)
                                (x30 : A6)
                                (x31 : rec x29 return x32 . Type@0
                                       | zero => Nat
                                       | succ x33, A8 => A6
                                       end)
                             -> x30))
                    (x4 (forall (x34 : Nat) -> Nat) 2
                       (fun (x35 : Nat) -> succ (succ (succ x35)))
                      (x4 (forall (x36 : Nat) -> Nat) 1
                         (fun (x37 : Nat) -> succ x37)
                        (x4 (forall (x38 : Nat) -> Nat) 0
                           (fun (x39 : Nat) -> succ (succ x39))
                          (x3 (forall (x40 : Nat) -> Nat))))))
               (fun (A9 : Type@0)
                    (x41 : Nat)
                 -> forall (x42 : forall (x43 : Nat) -> Type@1)
                           (x44 : x42 0)
                           (x45 : forall (x46 : Nat)
                                         (x47 : A9)
                                         (x48 : x42 x46)
                                    -> x42 (succ x46))
                      -> x42 x41)
               (fun (A10 : Type@0)
                    (x49 : forall (x50 : Nat) -> Type@1)
                    (x51 : x49 0)
                    (x52 : forall (x53 : Nat)
                                  (x54 : A10)
                                  (x55 : x49 x53)
                             -> x49 (succ x53))
                 -> x51)
               (fun (A11 : Type@0)
                    (x56 : Nat)
                    (x57 : A11)
                    (x58 : forall (x59 : forall (x60 : Nat) -> Type@1)
                                  (x61 : x59 0)
                                  (x62 : forall (x63 : Nat)
                                                (x64 : A11)
                                                (x65 : x59 x63)
                                           -> x59 (succ x63))
                             -> x59 x56)
                    (x66 : forall (x67 : Nat) -> Type@1)
                    (x68 : x66 0)
                    (x69 : forall (x70 : Nat)
                                  (x71 : A11)
                                  (x72 : x66 x70)
                             -> x66 (succ x70))
                 -> x69 x56 x57 (x58 x66 x68 x69))
               (fun (A12 : Type@0)
                    (x73 : Nat)
                    (x74 : forall (x75 : forall (x76 : Nat) -> Type@1)
                                  (x77 : x75 0)
                                  (x78 : forall (x79 : Nat)
                                                (x80 : A12)
                                                (x81 : x75 x79)
                                           -> x75 (succ x79))
                             -> x75 x73)
                    (x82 : forall (x83 : Nat) -> Type@1)
                    (x84 : x82 0)
                    (x85 : forall (x86 : Nat)
                                  (x87 : A12)
                                  (x88 : x82 x86)
                             -> x82 (succ x86))
                 -> x74 x82 x84 x85) --> 7 : Nat
    |}]

let%expect_test "nary.mctt works" =
  let _ = main_of_example "nary.mctt" in
  [%expect {|
    Evaluate (fun (x1 : forall (x2 : Nat) -> Type@0)
                  (x3 : forall (x4 : x1 0) -> Nat)
                  (x5 : forall (x6 : Nat)
                               (x7 : x1 (succ x6))
                               (x8 : Nat)
                          -> x1 x6)
                  (x9 : Nat)
                  (x10 : x1 x9)
               -> (rec x9 return x11 . forall (x14 : x1 x11) -> Nat
                   | zero => x3
                   | succ x12, x13 =>
                     fun (x15 : x1 (succ x12)) -> x13 (x5 x12 x15 (succ x12))
                   end)
                    x10)
               (fun (x16 : Nat)
                 -> rec x16 return x17 . Type@0
                    | zero => Nat
                    | succ x18, A1 => forall (x19 : Nat) -> A1
                    end)
               (fun (x20 : Nat) -> x20)
               (fun (x21 : Nat)
                    (x22 : rec succ x21 return x23 . Type@0
                           | zero => Nat
                           | succ x24, A2 => forall (x25 : Nat) -> A2
                           end)
                    (x26 : Nat)
                 -> x22 x26)
               3
               ((fun (x27 : forall (x28 : Nat)
                                   (x29 : Nat)
                              -> Nat)
                     (x30 : Nat)
                     (x31 : Nat)
                     (x32 : Nat)
                  -> x27 x30 (x27 x31 x32))
                 (fun (x33 : Nat)
                      (x34 : Nat)
                   -> rec x33 return x35 . Nat
                      | zero => x34
                      | succ x36, x37 => succ x37
                      end)) --> 6 : Nat
    |}]

let%expect_test "simple_let.mctt works" =
  let _ = main_of_example "simple_let.mctt" in
  [%expect {| Evaluate (fun (x1 : Nat) -> succ x1) 0 --> 1 : Nat |}]

let%expect_test "let_two_vars.mctt works" =
  let _ = main_of_example "let_two_vars.mctt" in
  [%expect {|
    Evaluate (fun (x1 : Nat)
                  (x2 : forall (x3 : Nat) -> Nat)
               -> x2 x1) 0
               (fun (x4 : Nat) -> x4) --> 0 : Nat
    |}]

let%expect_test "let_nary.mctt works" =
  let _ = main_of_example "let_nary.mctt" in
  [%expect {|
    Evaluate (fun (x1 : forall (x2 : Nat) -> Type@0)
                  (x3 : forall (x4 : x1 0) -> Nat)
                  (x5 : forall (x6 : Nat)
                               (x7 : x1 (succ x6))
                               (x8 : Nat)
                          -> x1 x6)
                  (x9 : Nat)
                  (x10 : x1 x9)
               -> (rec x9 return x11 . forall (x14 : x1 x11) -> Nat
                   | zero => x3
                   | succ x12, x13 =>
                     fun (x15 : x1 (succ x12)) -> x13 (x5 x12 x15 (succ x12))
                   end)
                    x10)
               (fun (x16 : Nat)
                 -> rec x16 return x17 . Type@0
                    | zero => Nat
                    | succ x18, A1 => forall (x19 : Nat) -> A1
                    end)
               (fun (x20 : Nat) -> x20)
               (fun (x21 : Nat)
                    (x22 : rec succ x21 return x23 . Type@0
                           | zero => Nat
                           | succ x24, A2 => forall (x25 : Nat) -> A2
                           end)
                    (x26 : Nat)
                 -> x22 x26)
               3
               ((fun (x27 : forall (x28 : Nat)
                                   (x29 : Nat)
                              -> Nat)
                     (x30 : Nat)
                     (x31 : Nat)
                     (x32 : Nat)
                  -> x27 x30 (x27 x31 x32))
                 (fun (x33 : Nat)
                      (x34 : Nat)
                   -> rec x33 return x35 . Nat
                      | zero => x34
                      | succ x36, x37 => succ x37
                      end)) --> 6 : Nat
    |}]

let%expect_test "let_vector.mctt works" =
  let _ = main_of_example "let_vector.mctt" in
  [%expect {|
    Evaluate (fun (x1 : forall (A1 : Type@0)
                               (x2 : Nat)
                          -> Type@2)
                  (x3 : forall (A2 : Type@0) -> x1 A2 0)
                  (x4 : forall (A3 : Type@0)
                               (x5 : Nat)
                               (x6 : A3)
                               (x7 : x1 A3 x5)
                          -> x1 A3 (succ x5))
                  (x8 : forall (A4 : Type@0)
                               (x9 : Nat)
                               (x10 : x1 A4 x9)
                               (x11 : forall (x12 : Nat) -> Type@1)
                               (x13 : x11 0)
                               (x14 : forall (x15 : Nat)
                                             (x16 : A4)
                                             (x17 : x11 x15)
                                        -> x11 (succ x15))
                          -> x11 x9)
               -> (fun (x18 : forall (A5 : Type@0)
                                     (x19 : Nat)
                                     (x20 : x1 A5 (succ x19))
                                -> A5)
                       (x21 : x1 (forall (x22 : Nat) -> Nat) 3)
                    -> x18 (forall (x23 : Nat) -> Nat) 2 x21 4)
                    (fun (A6 : Type@0)
                         (x24 : Nat)
                         (x25 : x1 A6 (succ x24))
                      -> x8 A6 (succ x24) x25
                           (fun (x26 : Nat)
                             -> rec x26 return x27 . Type@0
                                | zero => Nat
                                | succ x28, A7 => A6
                                end)
                           0
                           (fun (x29 : Nat)
                                (x30 : A6)
                                (x31 : rec x29 return x32 . Type@0
                                       | zero => Nat
                                       | succ x33, A8 => A6
                                       end)
                             -> x30))
                    (x4 (forall (x34 : Nat) -> Nat) 2
                       (fun (x35 : Nat) -> succ (succ (succ x35)))
                      (x4 (forall (x36 : Nat) -> Nat) 1
                         (fun (x37 : Nat) -> succ x37)
                        (x4 (forall (x38 : Nat) -> Nat) 0
                           (fun (x39 : Nat) -> succ (succ x39))
                          (x3 (forall (x40 : Nat) -> Nat))))))
               (fun (A9 : Type@0)
                    (x41 : Nat)
                 -> forall (x42 : forall (x43 : Nat) -> Type@1)
                           (x44 : x42 0)
                           (x45 : forall (x46 : Nat)
                                         (x47 : A9)
                                         (x48 : x42 x46)
                                    -> x42 (succ x46))
                      -> x42 x41)
               (fun (A10 : Type@0)
                    (x49 : forall (x50 : Nat) -> Type@1)
                    (x51 : x49 0)
                    (x52 : forall (x53 : Nat)
                                  (x54 : A10)
                                  (x55 : x49 x53)
                             -> x49 (succ x53))
                 -> x51)
               (fun (A11 : Type@0)
                    (x56 : Nat)
                    (x57 : A11)
                    (x58 : forall (x59 : forall (x60 : Nat) -> Type@1)
                                  (x61 : x59 0)
                                  (x62 : forall (x63 : Nat)
                                                (x64 : A11)
                                                (x65 : x59 x63)
                                           -> x59 (succ x63))
                             -> x59 x56)
                    (x66 : forall (x67 : Nat) -> Type@1)
                    (x68 : x66 0)
                    (x69 : forall (x70 : Nat)
                                  (x71 : A11)
                                  (x72 : x66 x70)
                             -> x66 (succ x70))
                 -> x69 x56 x57 (x58 x66 x68 x69))
               (fun (A12 : Type@0)
                    (x73 : Nat)
                    (x74 : forall (x75 : forall (x76 : Nat) -> Type@1)
                                  (x77 : x75 0)
                                  (x78 : forall (x79 : Nat)
                                                (x80 : A12)
                                                (x81 : x75 x79)
                                           -> x75 (succ x79))
                             -> x75 x73)
                    (x82 : forall (x83 : Nat) -> Type@1)
                    (x84 : x82 0)
                    (x85 : forall (x86 : Nat)
                                  (x87 : A12)
                                  (x88 : x82 x86)
                             -> x82 (succ x86))
                 -> x74 x82 x84 x85) --> 7 : Nat
    |}]

let%expect_test "def_abstract.mctt works" =
  let _ = main_of_example "def_abstract.mctt" in
  [%expect {|
    Evaluate double four
      --> rec four return x1 . Nat
          | zero => 0
          | succ x2, x3 => succ (succ x3)
          end : Nat
    Evaluate double four
      --> rec four return x1 . Nat
          | zero => 0
          | succ x2, x3 => succ (succ x3)
          end : Nat
    |}]

let%expect_test "module_nested.mctt works" =
  let _ = main_of_example "module_nested.mctt" in
  [%expect {| Evaluate Ops.twice Ops.pred 5 --> 3 : Nat |}]

let%expect_test "module_param.mctt works" =
  let _ = main_of_example "module_param.mctt" in
  [%expect {| Evaluate Church.two Nat 0 (fun (x1 : Nat) -> succ x1) --> 2 : Nat |}]

let%expect_test "import_use.mctt works" =
  let _ = main_of_example "import_use.mctt" in
  [%expect {| Evaluate sum Impl.exposed Impl.exposed --> 8 : Nat |}]

let%expect_test "let_decl.mctt works" =
  let _ = main_of_example "let_decl.mctt" in
  [%expect {| Evaluate (fun (x1 : Nat) -> (fun (x2 : Nat) -> 4) 3) 2 --> 4 : Nat |}]

(* let%test "lambda" = *)
(*   parse "fun (x : Type 5).y" = Some (Coq_fn (x, Coq_typ 5, Coq_var y)) *)

(* let%test "lambda multiple args" = *)
(*   parse "fun (x : Nat) (y : Nat) . x" *)
(*   = Some (Coq_fn (x, Coq_nat, Coq_fn (y, Coq_nat, Coq_var x))) *)

(* let%test "lambda multiple args 2" = *)
(*   parse "fun (x : Nat) (y : Nat) (z : Nat) . z" *)
(*   = Some *)
(*       (Coq_fn (x, Coq_nat, Coq_fn (y, Coq_nat, Coq_fn (z, Coq_nat, Coq_var z)))) *)

(* let%test "application" = *)
(*   parse "(fun (x : Nat).x) Nat" *)
(*   = Some (Coq_app (Coq_fn (x, Coq_nat, Coq_var x), Coq_nat)) *)

(* let%test "nested 1" = *)
(*   parse "(Type 5) zero" = Some (Coq_app (Coq_typ 5, Coq_zero)) *)

(* let%test "nested 2" = *)
(*   parse "succ (succ (succ (succ zero)))" *)
(*   = Some (Coq_succ (Coq_succ (Coq_succ (Coq_succ Coq_zero)))) *)

(* let%test "pi" = parse "pi (x:Nat).x" = Some (Coq_pi (x, Coq_nat, Coq_var x)) *)

(* let%test "pi multiple args" = *)
(*   parse "pi (x : Nat) (y : Nat) (z : Nat) . z" *)
(*   = Some *)
(*       (Coq_pi (x, Coq_nat, Coq_pi (y, Coq_nat, Coq_pi (z, Coq_nat, Coq_var z)))) *)

(* (\* Some more finer details *\) *)

(* let%test "pi missing colon" = parse "pi (x Nat).x" = None *)

(* let%test "ignore whitespace" = *)
(*   parse "fun (x  \n                                     : Type 4).x" *)
(*   = Some (Coq_fn (x, Coq_typ 4, Coq_var x)) *)

let%expect_test "imports, sharing a diamond" =
  let _ = main_of_multi "Main.mctt" in
  [%expect {|
    Evaluate Lib::Arith.quadruple 2 --> 8 : Nat
    Evaluate Lib::Num.double 3 --> 6 : Nat
    Evaluate Lib::Num.Ops.pred (Lib::Num.double 5) --> 9 : Nat
    |}]

let%expect_test "a unit with parameters" =
  let _ = main_of_multi "Params.mctt" in
  [%expect {|
    Evaluate Lib::Poly.id Nat 3 --> 3 : Nat
    Evaluate Lib::Poly.id Nat 4 --> 4 : Nat
    |}]

let%expect_test "an import is not transitive" =
  let _ = main_of_multi "Transitive.mctt" in
  [%expect {| Error: the unit is not imported |}]

let%expect_test "a cyclic import is rejected" =
  let _ = main_of_multi "Cycle.mctt" in
  [%expect {| Error: cyclic import: Cyc::A -> Cyc::B -> Cyc::A |}]

let%expect_test "a missing unit is reported" =
  let _ = main_of_multi "Missing.mctt" in
  [%expect {| Error: Lib::Nowhere: cannot find unit |}]

let%expect_test "an ill-typed imported unit is reported" =
  let _ = main_of_multi "BadDep.mctt" in
  [%expect {| Error: the body of wrong, Type@0, is not of type Nat |}]

let%expect_test "a file declaring another unit is reported" =
  let _ = main_of_multi "Misnamed.mctt" in
  [%expect {| Error: Lib::Wrong: the file of the unit declares another unit |}]
