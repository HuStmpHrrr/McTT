(* Unit test cases for parsing *)

open Main
open McttExtracted.Entrypoint

(** Helper definitions *)

let main_of_example s = main_of_filename ("../examples/" ^ s)

(* The programs under [examples/multi] import units of their own, looked up
   from there. *)
let main_of_multi s =
  main_of_filename ~search_root:"../examples/multi" ("../examples/multi/" ^ s)

(* An inline program importing units from [examples/multi]. *)
let main_of_multi_string program =
  main_of_program_string ~search_root:"../examples/multi" program

(* The programs under [lib] use the [Prelude] library, looked up from there. *)
let main_of_lib s = main_of_filename ~search_root:"../lib" ("../lib/" ^ s)

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

let%expect_test "SimpleNat.mctt works" =
  let _ = main_of_example "SimpleNat.mctt" in
  [%expect {| Evaluate 4 --> 4 : Nat |}]

let%expect_test "SimpleRec.mctt works" =
  let _ = main_of_example "SimpleRec.mctt" in
  [%expect {|
    Evaluate fun (x1 : Nat)
               -> rec x1 return x2 . Nat | zero => 1 | succ x3, x4 => succ x4 end
      --> fun (x1 : Nat)
            -> rec x1 return x2 . Nat | zero => 1 | succ x3, x4 => succ x4 end
      : forall (x1 : Nat) -> Nat
    |}]

let%expect_test "TrueFalse.mctt works" =
  let _ = main_of_example "TrueFalse.mctt" in
  [%expect {|
    Evaluate true --> true : True
    Evaluate fun (x1 : True) -> x1 --> fun (x1 : True) -> true
      : forall (x1 : True) -> True
    Evaluate fun (x1 : False) -> exfalso x1 return x2 . Nat
      --> fun (x1 : False) -> exfalso x1 return x2 . Nat
      : forall (x1 : False) -> Nat
    |}]

let%expect_test "LetTrueFalse.mctt works" =
  let _ = main_of_example "LetTrueFalse.mctt" in
  [%expect {|
    Evaluate let x1 : True := true;
                 x2 : forall (x3 : False) -> Nat :=
                   fun (x4 : False) -> exfalso x4 return x5 . Nat
             in x1
             end --> true : True
    |}]

let%expect_test "lib/NatTheory.mctt" =
  let _ = main_of_lib "NatTheory.mctt" in
  [%expect {|
    Evaluate plusComm 2 3 --> true : True
    Evaluate sym 4 4 (refl 4) --> true : True
    Evaluate zeroNeSucc 5
      --> fun (x1 : False) -> Prelude::Arith::Equality.zeroNeSucc 5 x1
      : forall (x1 : False) -> False
    Evaluate iterSucc 3 4 --> true : True
    Evaluate Iter.iter Nat (fun (x1 : Nat) -> plus x1 x1) 3 1 --> 8 : Nat
    Evaluate let module M1 := Iter Nat (fun (x1 : Nat) -> plus x1 x1);
                 x2 := 2;
                 x3 : Eq (M1.iter x2 1) 4 := true
             in x3
             end --> true : True
    |}]

let%expect_test "zero is not of True" =
  let _ = main_of_body "eval zero : True" in
  [%expect {| Error: 0 is not of type True |}]

let%expect_test "exfalso needs a motive" =
  let _ = main_of_body "eval exfalso f end" in
  [%expect {|
    Error: on "end" (at line 1, column 34 - line 1, column 37): Either an
      expression or "return" keyword is expected.
      This token is invalid for the beginning of an expression.
    |}]

let%expect_test "Pair.mctt works" =
  let _ = main_of_example "Pair.mctt" in
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

let%expect_test "Vector.mctt works" =
  let _ = main_of_example "Vector.mctt" in
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

let%expect_test "Nary.mctt works" =
  let _ = main_of_example "Nary.mctt" in
  [%expect {|
    Evaluate sum 3 1 2 3 --> 6 : Nat
    Evaluate let module M1 := Arity Nat; x1 : M1.Fn 4 := sum 4 in x1 1 2 3 4 end
      --> 10 : Nat
    |}]

let%expect_test "SimpleLet.mctt works" =
  let _ = main_of_example "SimpleLet.mctt" in
  [%expect {| Evaluate let x1 : Nat := 0 in succ x1 end --> 1 : Nat |}]

let%expect_test "an unannotated let infers the type of its definiens" =
  let _ = main_of_body "eval let x := 0 in succ x end" in
  [%expect {| Evaluate let x1 := 0 in succ x1 end --> 1 : Nat |}]

let%expect_test "annotated and unannotated bindings mix in one let" =
  let _ = main_of_body
    "eval let A : Type@0 := Nat; z := 0; f := fun (n : A) -> succ z in f z end" in
  [%expect {|
    Evaluate let A1 : Type@0 := Nat; x1 := 0; x2 := fun (x3 : A1) -> succ x1
             in x2 x1
             end --> 1 : Nat
    |}]

let%expect_test "an unannotated let's body may need its delta-equation" =
  let _ = main_of_body "eval let A := Nat in fun (a : A) -> succ a end" in
  [%expect {|
    Evaluate let x1 := Nat in fun (x2 : x1) -> succ x2 end
      --> fun (x1 : Nat) -> succ x1 : forall (x1 : Nat) -> Nat
    |}]

let%expect_test "an unannotated let with an ill-typed body is rejected" =
  let _ = main_of_body "eval let A := Nat in succ A end" in
  [%expect {| Error: let x1 := Nat in succ x1 end has no inferable type |}]

let%expect_test "an unannotated local definition needs its body" =
  let _ = main_of_body "eval let x := in x end" in
  [%expect {|
    Error: on "in" (at line 1, column 33 - line 1, column 35): Expected the body
      of the local definition.
    |}]

let%expect_test "LetTwoVars.mctt works" =
  let _ = main_of_example "LetTwoVars.mctt" in
  [%expect {|
    Evaluate let x1 : Nat := 0;
                 x2 : forall (x3 : Nat) -> Nat := fun (x4 : Nat) -> x4
             in x2 x1
             end --> 0 : Nat
    |}]

let%expect_test "LetNary.mctt works" =
  let _ = main_of_example "LetNary.mctt" in
  [%expect {|
    Evaluate let x1 : forall (x2 : Nat) -> Type@0 :=
                   fun (x3 : Nat)
                     -> rec x3 return x4 . Type@0
                        | zero => Nat
                        | succ x5, A1 => forall (x6 : Nat) -> A1
                        end;
                 x7 : forall (x8 : x1 0) -> Nat := fun (x9 : Nat) -> x9;
                 x10 : forall (x11 : Nat)
                              (x12 : x1 (succ x11))
                              (x13 : Nat)
                         -> x1 x11 :=
                   fun (x14 : Nat)
                       (x15 : rec succ x14 return x16 . Type@0
                              | zero => Nat
                              | succ x17, A2 => forall (x18 : Nat) -> A2
                              end)
                       (x19 : Nat)
                     -> x15 x19;
                 x20 : Nat := 3;
                 x21 : x1 x20 :=
                   let x22 : forall (x23 : Nat)
                                    (x24 : Nat)
                               -> Nat :=
                         fun (x25 : Nat)
                             (x26 : Nat)
                           -> rec x25 return x27 . Nat
                              | zero => x26
                              | succ x28, x29 => succ x29
                              end
                   in fun (x30 : Nat)
                          (x31 : Nat)
                          (x32 : Nat)
                        -> x22 x30 (x22 x31 x32)
                   end
             in (rec x20 return x33 . forall (x36 : x1 x33) -> Nat
                 | zero => x7
                 | succ x34, x35 =>
                   fun (x37 : x1 (succ x34)) -> x35 (x10 x34 x37 (succ x34))
                 end)
                  x21
             end --> 6 : Nat
    |}]

let%expect_test "LetVector.mctt works" =
  let _ = main_of_example "LetVector.mctt" in
  [%expect {|
    Evaluate let x1 : forall (A1 : Type@0)
                             (x2 : Nat)
                        -> Type@2 :=
                   fun (A2 : Type@0)
                       (x3 : Nat)
                     -> forall (x4 : forall (x5 : Nat) -> Type@1)
                               (x6 : x4 0)
                               (x7 : forall (x8 : Nat)
                                            (x9 : A2)
                                            (x10 : x4 x8)
                                       -> x4 (succ x8))
                          -> x4 x3;
                 x11 : forall (A3 : Type@0) -> x1 A3 0 :=
                   fun (A4 : Type@0)
                       (x12 : forall (x13 : Nat) -> Type@1)
                       (x14 : x12 0)
                       (x15 : forall (x16 : Nat)
                                     (x17 : A4)
                                     (x18 : x12 x16)
                                -> x12 (succ x16))
                     -> x14;
                 x19 : forall (A5 : Type@0)
                              (x20 : Nat)
                              (x21 : A5)
                              (x22 : x1 A5 x20)
                         -> x1 A5 (succ x20) :=
                   fun (A6 : Type@0)
                       (x23 : Nat)
                       (x24 : A6)
                       (x25 : forall (x26 : forall (x27 : Nat) -> Type@1)
                                     (x28 : x26 0)
                                     (x29 : forall (x30 : Nat)
                                                   (x31 : A6)
                                                   (x32 : x26 x30)
                                              -> x26 (succ x30))
                                -> x26 x23)
                       (x33 : forall (x34 : Nat) -> Type@1)
                       (x35 : x33 0)
                       (x36 : forall (x37 : Nat)
                                     (x38 : A6)
                                     (x39 : x33 x37)
                                -> x33 (succ x37))
                     -> x36 x23 x24 (x25 x33 x35 x36);
                 x40 : forall (A7 : Type@0)
                              (x41 : Nat)
                              (x42 : x1 A7 x41)
                              (x43 : forall (x44 : Nat) -> Type@1)
                              (x45 : x43 0)
                              (x46 : forall (x47 : Nat)
                                            (x48 : A7)
                                            (x49 : x43 x47)
                                       -> x43 (succ x47))
                         -> x43 x41 :=
                   fun (A8 : Type@0)
                       (x50 : Nat)
                       (x51 : forall (x52 : forall (x53 : Nat) -> Type@1)
                                     (x54 : x52 0)
                                     (x55 : forall (x56 : Nat)
                                                   (x57 : A8)
                                                   (x58 : x52 x56)
                                              -> x52 (succ x56))
                                -> x52 x50)
                       (x59 : forall (x60 : Nat) -> Type@1)
                       (x61 : x59 0)
                       (x62 : forall (x63 : Nat)
                                     (x64 : A8)
                                     (x65 : x59 x63)
                                -> x59 (succ x63))
                     -> x51 x59 x61 x62;
                 x66 : forall (A9 : Type@0)
                              (x67 : Nat)
                              (x68 : x1 A9 (succ x67))
                         -> A9 :=
                   fun (A10 : Type@0)
                       (x69 : Nat)
                       (x70 : x1 A10 (succ x69))
                     -> x40 A10 (succ x69) x70
                          (fun (x71 : Nat)
                            -> rec x71 return x72 . Type@0
                               | zero => Nat
                               | succ x73, A11 => A10
                               end)
                          0
                          (fun (x74 : Nat)
                               (x75 : A10)
                               (x76 : rec x74 return x77 . Type@0
                                      | zero => Nat
                                      | succ x78, A12 => A10
                                      end)
                            -> x75);
                 x79 : x1 (forall (x80 : Nat) -> Nat) 3 :=
                   x19 (forall (x81 : Nat) -> Nat) 2
                     (fun (x82 : Nat) -> succ (succ (succ x82)))
                     (x19 (forall (x83 : Nat) -> Nat) 1
                        (fun (x84 : Nat) -> succ x84)
                       (x19 (forall (x85 : Nat) -> Nat) 0
                          (fun (x86 : Nat) -> succ (succ x86))
                         (x11 (forall (x87 : Nat) -> Nat))))
             in x66 (forall (x88 : Nat) -> Nat) 2 x79 4
             end --> 7 : Nat
    |}]

let%expect_test "DefAbstract.mctt works" =
  let _ = main_of_example "DefAbstract.mctt" in
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

let%expect_test "ModuleNested.mctt works" =
  let _ = main_of_example "ModuleNested.mctt" in
  [%expect {| Evaluate Ops.twice Ops.pred 5 --> 3 : Nat |}]

let%expect_test "ModuleParam.mctt works" =
  let _ = main_of_example "ModuleParam.mctt" in
  [%expect {|
    Evaluate let module M1 := Church Nat
             in M1.two 0 (fun (x1 : Nat) -> succ x1)
             end --> 2 : Nat
    |}]

let%expect_test "Universes.mctt works" =
  let _ = main_of_example "Universes.mctt" in
  [%expect {|
    Evaluate id 1l Type@0 Nat --> Nat : Type@0
    Evaluate atoms --> fun (x1 : Level)
                           (x2 : Level)
                         -> Type@{maxl (maxl 1l x2) x1}
      : forall (x1 : Level)
               (x2 : Level)
          -> Type@{maxl (maxl 2l (succl x2)) (succl x1)}
    Evaluate self 3 --> 3 : Nat
    Evaluate Dom --> Nat : Type@0
    Evaluate Type@{depth 3} --> Type@3 : Type@4
    Evaluate Endo 0l Nat --> forall (x1 : Nat) -> Nat : Type@0
    Evaluate fun (x1 : Level)
                 (A1 : Type@{x1})
               -> forall (x2 : A1) -> A1
      --> fun (x1 : Level)
              (A1 : Type@{x1})
            -> forall (x2 : A1) -> A1
      : forall (x1 : Level)
               (A1 : Type@{x1})
          -> Type@{x1}
    Evaluate forall (x1 : Level) -> Type@{x1}
      --> forall (x1 : Level) -> Type@{x1} : Type@ω
    Evaluate Type@2 --> Type@2 : Type@3
    Evaluate Type@2 --> Type@2 : Type@3
    Evaluate Type@2 --> Type@2 : Type@3
    Evaluate Type@ω --> Type@ω : Type@1L
    Evaluate Type@ω --> Type@ω : Type@1L
    Evaluate Type@ω --> Type@ω : Type@1L
    Evaluate Type@2L --> Type@2L : Type@3L
    Evaluate Type@2L --> Type@2L : Type@3L
    |}]

(* Levels are first class: a level literal is a term of [Level], [succl] and
   [maxl] compute on it, and a small universe accepts any level term. *)
let%expect_test "a level literal is a term of Level" =
  let _ = main_of_body "eval maxl 2l (succl 0l) : Level" in
  [%expect {| Evaluate maxl 2l (succl 0l) --> 2l : Level |}]

let%expect_test "a small universe at a literal level" =
  let _ = main_of_body "eval Type@{succl 1l} : Type@3" in
  [%expect {| Evaluate Type@{succl 1l} --> Type@2 : Type@3 |}]

(* [Type@ω] is the first large universe, above every small one; it has three
   other spellings, and the higher ones are [Type@{ω+n}] or [Type@nL]. *)
let%expect_test "the large universe holds a small one" =
  let _ = main_of_body "eval Type@5 : Type@ω" in
  [%expect {| Evaluate Type@5 --> Type@5 : Type@ω |}]

let%expect_test "every spelling of a large universe size" =
  let _ = main_of_body "eval Type@omega : Type@{ω+1}" in
  [%expect {| Evaluate Type@ω --> Type@ω : Type@1L |}]

let%expect_test "the shorthand for a large universe size" =
  let _ = main_of_body "eval Type@{omega} : Type@1L" in
  [%expect {| Evaluate Type@ω --> Type@ω : Type@1L |}]

let%expect_test "a large universe above the first" =
  let _ = main_of_body "eval Type@{ω+2}" in
  [%expect {| Evaluate Type@2L --> Type@2L : Type@3L |}]

(* A bare numeral is a small size, so a large universe is not below it. *)
let%expect_test "a large universe is not in a small one" =
  let _ = main_of_body "eval Type@ω : Type@3" in
  [%expect {| Error: Type@ω is not of type Type@3 |}]

(* A function type of small types is small at their level, also at a level
   variable; two levels join. *)
let%expect_test "a function type at a level variable is small" =
  let _ = main_of_body "def Endo (u : Level) (A : Type@{u}) : Type@{u} := forall (a : A) -> A end eval Endo" in
  [%expect {|
    Evaluate Endo --> fun (x1 : Level)
                          (A1 : Type@{x1})
                        -> forall (x2 : A1) -> A1
      : forall (x1 : Level)
               (A1 : Type@{x1})
          -> Type@{x1}
    |}]

let%expect_test "a function type between two small universes is at their join" =
  let _ = main_of_body "eval fun (u : Level) (v : Level) (A : Type@{u}) (B : Type@{v}) -> forall (a : A) -> B" in
  [%expect {|
    Evaluate fun (x1 : Level)
                 (x2 : Level)
                 (A1 : Type@{x1})
                 (A2 : Type@{x2})
               -> forall (x3 : A1) -> A2
      --> fun (x1 : Level)
              (x2 : Level)
              (A1 : Type@{x1})
              (A2 : Type@{x2})
            -> forall (x3 : A1) -> A2
      : forall (x1 : Level)
               (x2 : Level)
               (A1 : Type@{x1})
               (A2 : Type@{x2})
          -> Type@{maxl x2 x1}
    |}]

(* A codomain whose level mentions the bound variable has no small universe
   to be in. *)
let%expect_test "a type quantifying over levels is not small" =
  let _ = main_of_body "eval (forall (u : Level) -> Type@{u}) : Type@5" in
  [%expect {| Error: forall (x1 : Level) -> Type@{x1} is not of type Type@5 |}]

(* A large size is a size only: it is not a term of [Level]. *)
let%expect_test "a large size is not a level" =
  let _ = main_of_body "eval 1L : Level" in
  [%expect {|
    Error: on "1L" (at line 1, column 24 - line 1, column 26): This token is
      invalid for the beginning of a program.
    |}]

(* An unbraced [+] is rejected. *)
let%expect_test "an unbraced omega offset is a syntax error" =
  let _ = main_of_body "eval Type@ω+1" in
  [%expect {|
    Error: on "+" (at line 1, column 31 - line 1, column 32): Expected ":"
      followed by the type to check against, or the next command.
    |}]

(* A universe is not in itself. *)
let%expect_test "a small universe is not in itself" =
  let _ = main_of_body "eval Type@1 : Type@1" in
  [%expect {| Error: Type@1 is not of type Type@1 |}]

(* A level is not a type, and a type is not a level. *)
let%expect_test "a level is not a type" =
  let _ = main_of_body "eval zero : 0l" in
  [%expect {| Error: 0 is not of type 0l |}]

let%expect_test "Nat is not a level" =
  let _ = main_of_body "eval Nat : Level" in
  [%expect {| Error: Nat is not of type Level |}]

(* The level of a small universe may be any term of [Level], including an
   open one, so the normal form of a level has atoms. *)
let%expect_test "an open level normalizes with atoms" =
  let _ = main_of_body "eval fun (u : Level) (v : Level) -> Type@{maxl v (maxl 1l u)}" in
  [%expect {|
    Evaluate fun (x1 : Level)
                 (x2 : Level)
               -> Type@{maxl x2 (maxl 1l x1)}
      --> fun (x1 : Level)
              (x2 : Level)
            -> Type@{maxl (maxl 1l x2) x1}
      : forall (x1 : Level)
               (x2 : Level)
          -> Type@{maxl (maxl 2l (succl x2)) (succl x1)}
    |}]

let%expect_test "ModuleForms.mctt works" =
  let _ = main_of_example "ModuleForms.mctt" in
  [%expect {|
    Evaluate NatIter.twice (fun (x1 : Nat) -> succ x1) 0 --> 2 : Nat
    Evaluate Num.Ops.add 2 3 --> 5 : Nat
    Evaluate O.add 1 1 --> 2 : Nat
    Evaluate let module M1 (x1 : Nat) where
                   module Inner where
                     def m : Nat :=
                       succ x1
                     end
                   end
                   private def m : Nat :=
                     Inner.m
                   end
                   def doubled : Nat :=
                     Num.Ops.add m m
                   end
                 end
             in M1.doubled 2
             end --> 6 : Nat
    |}]

let%expect_test "ImportUse.mctt works" =
  let _ = main_of_example "ImportUse.mctt" in
  [%expect {| Evaluate sum I.exposed exposed --> 8 : Nat |}]

let%expect_test "LetDecl.mctt works" =
  let _ = main_of_example "LetDecl.mctt" in
  [%expect {| Evaluate let x1 : Nat := 2; x2 : Nat := succ x1 in succ x2 end --> 4 : Nat |}]

let%expect_test "LetDelta.mctt works" =
  let _ = main_of_example "LetDelta.mctt" in
  [%expect {|
    Evaluate let x1 : Nat := 3;
                 x2 : Nary x1 := fun (x3 : Nat)
                                     (x4 : Nat)
                                     (x5 : Nat)
                                   -> x3
             in x2 1 2 3
             end --> 1 : Nat
    |}]

let%expect_test "LetMulti.mctt works" =
  let _ = main_of_example "LetMulti.mctt" in
  [%expect {|
    Evaluate let A1 : Type@0 := Nat;
                 x1 : A1 := 2;
                 x2 : forall (x3 : A1) -> A1 :=
                   fun (x4 : A1)
                     -> rec x4 return x5 . A1
                        | zero => x1
                        | succ x6, x7 => succ x7
                        end
             in x2 x1
             end --> 4 : Nat
    |}]

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
    Evaluate quadruple 2 --> 8 : Nat
    Evaluate N.double 3 --> 6 : Nat
    Evaluate pred (N.double 5) --> 9 : Nat
    |}]

let%expect_test "a unit with parameters" =
  let _ = main_of_multi "Params.mctt" in
  [%expect {|
    Evaluate Lib::Poly.id Nat 3 --> 3 : Nat
    Evaluate id Nat 4 --> 4 : Nat
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

let%expect_test "lib/Arithmetic.mctt" =
  let _ = main_of_lib "Arithmetic.mctt" in
  [%expect {|
    Evaluate mult 6 7 --> 42 : Nat
    Evaluate plus (mult 3 4) (mult 2 5) --> 22 : Nat
    Evaluate plusAssoc 1 2 3 --> true : True
    Evaluate multComm 3 4 --> true : True
    Evaluate multAssoc 2 3 4 --> true : True
    Evaluate multDistribLeft 2 3 4 --> true : True
    Evaluate multDistribRight 2 3 4 --> true : True
    Evaluate cong (fun (x1 : Nat) -> mult x1 x1) 3 3 (refl 3) --> true : True
    Evaluate plusCancelLeft 2 3 3 true --> true : True
    Evaluate plusCancelRight 4 4 1 true --> true : True
    Evaluate plusEqZero 0 0 true --> true : True
    Evaluate multEqZero 2 0 true (fun (x1 : False) -> x1) --> true : True
    |}]

let%expect_test "lib/OrderParity.mctt" =
  let _ = main_of_lib "OrderParity.mctt" in
  [%expect {|
    Evaluate leTrans 1 2 5 true true --> true : True
    Evaluate leAntisym 3 3 true true --> true : True
    Evaluate leSucc 4 --> true : True
    Evaluate lePlusRight 2 3 --> true : True
    Evaluate orElim (Le 5 2) (Le 2 5) Nat (leTotal 5 2) (fun (x1 : Le 5 2) -> 0)
               (fun (x2 : Le 2 5) -> 1) --> 1 : Nat
    Evaluate ltIrrefl 3
      --> fun (x1 : False) -> Prelude::Arith::Order.LtLaws.ltIrrefl 3 x1
      : forall (x1 : False) -> False
    Evaluate notLtZero 2
      --> fun (x1 : False) -> Prelude::Arith::Order.LtLaws.notLtZero 2 x1
      : forall (x1 : False) -> False
    Evaluate leb 2 5 --> 1 : Nat
    Evaluate leb 5 2 --> 0 : Nat
    Evaluate lebComplete 2 5 true --> true : True
    Evaluate lebZero 5 2 true --> true : True
    Evaluate double 7 --> 14 : Nat
    Evaluate evenDouble 7 --> true : True
    Evaluate orElim (Even 7) (Odd 7) Nat (evenOrOdd 7) (fun (x1 : Even 7) -> 0)
               (fun (x2 : Odd 7) -> 1) --> 1 : Nat
    Evaluate evenSuccOdd 4 true --> true : True
    Evaluate evenPlus 4 6 true true --> true : True
    |}]

let%expect_test "a missing input file is reported" =
  let _ = main_of_filename "../examples/Missing.mctt" in
  [%expect {| Error: ../examples/Missing.mctt: No such file or directory |}]

let%expect_test "a directory is not an input file" =
  let _ = main_of_filename "../examples" in
  [%expect {| Error: ../examples is a directory |}]

let%expect_test "an unexpected character is reported" =
  let _ = main_of_body "eval 0 $ 1" in
  [%expect {| Error: unexpected character '$' at line 1, column 26 |}]

let%expect_test "an unterminated comment is reported" =
  let _ = main_of_body "eval 0 (* open" in
  [%expect {| Error: unterminated comment |}]

let%expect_test "a multi-line comment counts its lines" =
  let _ = main_of_program_string "module Test where\n(* one\n   two *)\n\neval 0 $ 1 end" in
  [%expect {| Error: unexpected character '$' at line 5, column 8 |}]

let%expect_test "a parse error after a multi-line comment is on its own line" =
  let _ = main_of_program_string "module Test where\n(* one\n   two *)\n\ndef end" in
  [%expect {|
    Error: on "end" (at line 5, column 5 - line 5, column 8): Expected a name for
      the definition.
    |}]

let%expect_test "lib/Programs.mctt" =
  let _ = main_of_lib "Programs.mctt" in
  [%expect {|
    Evaluate pred 5 --> 4 : Nat
    Evaluate sub 10 3 --> 7 : Nat
    Evaluate sub 3 10 --> 0 : Nat
    Evaluate min 4 9 --> 4 : Nat
    Evaluate max 4 9 --> 9 : Nat
    Evaluate ack 2 3 --> 9 : Nat
    Evaluate ack 3 3 --> 61 : Nat
    Evaluate plusSub 6 4 --> true : True
    Evaluate subSelf 7 --> true : True
    Evaluate subSuccRight 9 4 --> true : True
    Evaluate plusMinMax 3 8 --> true : True
    Evaluate minComm 2 5 --> true : True
    Evaluate maxComm 6 1 --> true : True
    Evaluate ackZero 4 --> true : True
    Evaluate ackTwo 5 --> true : True
    Evaluate iteratePlus (fun (x1 : Nat) -> plus x1 3) 2 3 1 --> true : True
    Evaluate iterateComm (fun (x1 : Nat) -> succ (succ x1)) 3 4 0 --> true : True
    Evaluate Generic.compose Nat Nat Nat (sub 20) (fun (x1 : Nat) -> max x1 5) 2
      --> 15 : Nat
    Evaluate Generic.const Nat Nat 7 100 --> 7 : Nat
    Evaluate Generic.iterate Nat (ack 1) 3 0 --> 6 : Nat
    |}]

let%expect_test "lib/Induction.mctt" =
  let _ = main_of_lib "Induction.mctt" in
  [%expect {|
    Evaluate half 7 --> 3 : Nat
    Evaluate half 20 --> 10 : Nat
    Evaluate halfTwo 7 --> 3 : Nat
    Evaluate halfTwo 20 --> 10 : Nat
    Evaluate twoStepInd (fun (x1 : Nat) -> Even (double x1)) true true
               (fun (x2 : Nat)
                    (x3 : Even (double x2))
                 -> x3)
               5 --> true : True
    Evaluate caseNat (fun (x1 : Nat) -> Nat) 0 (fun (x2 : Nat) -> x2) 9 --> 8
      : Nat
    Evaluate orElim (Eq 3 3) (Not (Eq 3 3)) Nat (decEq 3 3)
               (fun (x1 : Eq 3 3) -> 1)
               (fun (x2 : Not (Eq 3 3)) -> 0) --> 1 : Nat
    Evaluate orElim (Eq 3 4) (Not (Eq 3 4)) Nat (decEq 3 4)
               (fun (x1 : Eq 3 4) -> 1)
               (fun (x2 : Not (Eq 3 4)) -> 0) --> 0 : Nat
    Evaluate orElim (Le 2 5) (Not (Le 2 5)) Nat (decLe 2 5)
               (fun (x1 : Le 2 5) -> 1)
               (fun (x2 : Not (Le 2 5)) -> 0) --> 1 : Nat
    Evaluate orElim (Lt 5 5) (Not (Lt 5 5)) Nat (decLt 5 5)
               (fun (x1 : Lt 5 5) -> 1)
               (fun (x2 : Not (Lt 5 5)) -> 0) --> 0 : Nat
    Evaluate decStable (Eq 4 4) (decEq 4 4) (fun (x1 : Not (Eq 4 4)) -> x1 true)
      --> true : True
    Evaluate eqb 6 6 --> 1 : Nat
    Evaluate eqb 6 2 --> 0 : Nat
    Evaluate iffFwd (Eq (eqb 5 5) 1) (Eq 5 5) (eqbSpec 5 5) true --> true : True
    Evaluate iffBwd (Eq (eqb 5 5) 1) (Eq 5 5) (eqbSpec 5 5) true --> true : True
    Evaluate eqbZero 2 3 true
      --> fun (x1 : False) -> Prelude::Arith::Decide.EqbLaws.eqbZero 2 3 true x1
      : forall (x1 : False) -> False
    Evaluate existsElim (fun (x1 : Nat) -> Eq (plus x1 x1) 6) Nat
               (existsIntro (fun (x2 : Nat) -> Eq (plus x2 x2) 6) 3 true)
               (fun (x3 : Nat)
                    (x4 : Eq (plus x3 x3) 6)
                 -> x3) --> 3 : Nat
    |}]

let%expect_test "lib/Lattice.mctt" =
  let _ = main_of_lib "Lattice.mctt" in
  [%expect {|
    Evaluate min (max 2 7) (max 5 3) --> 5 : Nat
    Evaluate max (min 9 4) (min 6 8) --> 6 : Nat
    Evaluate plus (sub 9 4) 4 --> 9 : Nat
    Evaluate lePlusMono 1 2 3 4 true true --> true : True
    Evaluate lePlusCancel 3 2 5 true --> true : True
    Evaluate leMultMono 2 3 2 4 true true --> true : True
    Evaluate ltTrans 1 2 4 true true --> true : True
    Evaluate ltLeTrans 1 3 3 true true --> true : True
    Evaluate leLtTrans 2 2 5 true true --> true : True
    Evaluate ltSucc 6 --> true : True
    Evaluate ltPlus 4 2 --> true : True
    Evaluate subLe 7 3 --> true : True
    Evaluate subMonoLeft 4 6 2 true --> true : True
    Evaluate subMonoRight 8 2 5 true --> true : True
    Evaluate plusSubCancel 9 4 true --> true : True
    Evaluate subPlusCancel 9 4 true --> true : True
    Evaluate subPos 5 2 true --> true : True
    Evaluate minAssoc 4 2 7 --> true : True
    Evaluate maxAssoc 4 2 7 --> true : True
    Evaluate minMaxAbsorb 5 3 --> true : True
    Evaluate maxMinAbsorb 3 5 --> true : True
    Evaluate minMaxDistrib 4 2 6 --> true : True
    Evaluate maxMinDistrib 4 2 6 --> true : True
    Evaluate minLe 3 8 --> true : True
    Evaluate leMax 8 3 --> true : True
    Evaluate leMin 2 4 5 true true --> true : True
    Evaluate maxLe 3 4 6 true true --> true : True
    Evaluate minEqLeft 3 5 true --> true : True
    Evaluate maxEqRight 3 5 true --> true : True
    Evaluate minMono 2 3 4 6 true true --> true : True
    Evaluate maxMono 2 3 6 7 true true --> true : True
    |}]

let%expect_test "lib/Division.mctt" =
  let _ = main_of_lib "Division.mctt" in
  [%expect {|
    Evaluate div 17 5 --> 3 : Nat
    Evaluate mod 17 5 --> 2 : Nat
    Evaluate div 17 0 --> 0 : Nat
    Evaluate mod 17 0 --> 17 : Nat
    Evaluate div 20 4 --> 5 : Nat
    Evaluate mod 20 4 --> 0 : Nat
    Evaluate divSucc 17 3 --> 4 : Nat
    Evaluate modSucc 17 3 --> 1 : Nat
    Evaluate divZeroDivisor 17 --> true : True
    Evaluate modZeroDivisor 17 --> true : True
    Evaluate divZero 4 --> true : True
    Evaluate modZero 0 --> true : True
    Evaluate divModSpec 17 4 --> true : True
    Evaluate modLt 17 4 --> true : True
    Evaluate modSmall 3 4 true --> true : True
    Evaluate divSmall 3 4 true --> true : True
    Evaluate modSelf 6 --> true : True
    Evaluate modPlusDivisor 9 4 --> true : True
    Evaluate modOne 7 --> true : True
    Evaluate divOne 7 --> true : True
    Evaluate Divides 3 12 --> True : Type@0
    Evaluate Divides 3 13 --> False : Type@0
    Evaluate Divides 0 0 --> True : Type@0
    Evaluate Divides 0 5 --> False : Type@0
    Evaluate zeroDivides 0 true --> true : True
    Evaluate dividesRefl 5 --> true : True
    Evaluate dividesZero 4 --> true : True
    Evaluate oneDivides 9 --> true : True
    Evaluate dividesPlus 3 6 9 true true --> true : True
    Evaluate dividesMult 3 4 --> true : True
    Evaluate evenDividesTwo 8 true --> true : True
    Evaluate dividesTwoEven 10 true --> true : True
    |}]

let%expect_test "lib/Vectors.mctt" =
  let _ = main_of_lib "Vectors.mctt" in
  [%expect {|
    Evaluate sumVec 3 oneTwoThree --> 6 : Nat
    Evaluate NV.head 2 oneTwoThree --> 1 : Nat
    Evaluate NV.nth 3 oneTwoThree 2 true --> 3 : Nat
    Evaluate sumVec 2 (NV.tail 2 oneTwoThree) --> 5 : Nat
    Evaluate sumVec 3 (NV.map Nat square 3 oneTwoThree) --> 14 : Nat
    Evaluate NV.nth 5 (NV.append 3 2 oneTwoThree fourFive) 3 true --> 4 : Nat
    Evaluate sumVec 5 (NV.append 3 2 oneTwoThree fourFive) --> 15 : Nat
    Evaluate sumVec 4 (NV.replicate 4 6) --> 24 : Nat
    Evaluate NV.foldr Nat (fun (x1 : Nat)
                               (x2 : Nat)
                            -> succ x2) 0 5
               (NV.append 3 2 oneTwoThree fourFive) --> 5 : Nat
    Evaluate sumReplicate 4 6 --> true : True
    Evaluate sumAppend 3 2 oneTwoThree fourFive --> true : True
    Evaluate nthMap Nat square 3 oneTwoThree 1 true --> true : True
    Evaluate nthReplicate 4 6 3 true --> true : True
    Evaluate nthAppendLeft 3 2 oneTwoThree fourFive 1 true true --> true : True
    Evaluate nthAppendRight 3 2 oneTwoThree fourFive 1 true --> true : True
    Evaluate NV.nth 4 (NV.tabulate square 4) 3 true --> 9 : Nat
    Evaluate sumVec 4 (NV.tabulate square 4) --> 14 : Nat
    Evaluate sumVec 2
               (NV.zipWith Nat Nat mult 2 (NV.take 2 1 oneTwoThree) fourFive)
      --> 14 : Nat
    Evaluate NV.foldl Nat (fun (x1 : Nat)
                               (x2 : Nat)
                            -> plus (mult 10 x1) x2) 0 3
               oneTwoThree --> 123 : Nat
    Evaluate NV.last 4 oneToFive --> 5 : Nat
    Evaluate NV.last 3 (NV.snoc 3 oneTwoThree 7) --> 7 : Nat
    Evaluate sumVec 4 (NV.init 4 oneToFive) --> 10 : Nat
    Evaluate NV.head 4 (NV.reverse 5 oneToFive) --> 5 : Nat
    Evaluate NV.last 4 (NV.reverse 5 oneToFive) --> 1 : Nat
    Evaluate NV.nth 3 (NV.take 3 2 oneToFive) 2 true --> 3 : Nat
    Evaluate NV.nth 2 (NV.drop 3 2 oneToFive) 0 true --> 4 : Nat
    Evaluate NV.allb (fun (x1 : Nat) -> x1) 5 oneToFive --> 1 : Nat
    Evaluate NV.allb (fun (x1 : Nat) -> x1) 4 (NV.cons 3 0 oneTwoThree) --> 0
      : Nat
    Evaluate NV.anyb (fun (x1 : Nat) -> x1) 3 (NV.snoc 2 (NV.replicate 2 0) 9)
      --> 1 : Nat
    Evaluate NV.anyb (fun (x1 : Nat) -> x1) 3 (NV.replicate 3 0) --> 0 : Nat
    Evaluate nthTabulate square 4 3 true --> true : True
    Evaluate nthZipWith Nat Nat mult 2 (NV.take 2 1 oneTwoThree) fourFive 1 true
      --> true : True
    Evaluate nthReverse 5 oneToFive 1 true true --> true : True
    Evaluate takeAppend 3 2 oneTwoThree fourFive 2 true --> true : True
    Evaluate dropAppend 3 2 oneTwoThree fourFive 1 true --> true : True
    Evaluate appendTakeDrop 3 2 oneToFive 4 true --> true : True
    Evaluate lastSnoc 3 oneTwoThree 7 --> true : True
    Evaluate sumMapPlus 2 3 oneTwoThree --> true : True
    Evaluate sumMapScale 3 3 oneTwoThree --> true : True
    Evaluate sumZipWithPlus 2 fourFive (NV.tail 2 oneTwoThree) --> true : True
    Evaluate foldlPlus 4 3 oneTwoThree --> true : True
    Evaluate sumSnoc 3 oneTwoThree 7 --> true : True
    Evaluate sumInitLast 4 oneToFive --> true : True
    Evaluate sumReverse 5 oneToFive --> true : True
    Evaluate sumTabulate square 4 --> true : True
    Evaluate allbSound Nat (fun (x1 : Nat) -> x1) 5 oneToFive true 2 true
      --> true : True
    Evaluate allbComplete Nat (fun (x1 : Nat) -> x1) 4 (NV.replicate 4 3)
               (fun (x2 : Nat)
                    (x3 : Lt x2 4)
                 -> true) --> true : True
    Evaluate anybSound Nat (fun (x1 : Nat) -> x1) 3
               (NV.snoc 2 (NV.replicate 2 0) 9)
               true
               Nat
               (fun (x2 : Nat)
                    (x3 : Lt x2 3)
                    (x4 : Lt 0 (NV.snoc 2 (NV.replicate 2 0) 9 x2 x3))
                 -> x2) --> 2 : Nat
    |}]

let%expect_test "lib/Powers.mctt" =
  let _ = main_of_lib "Powers.mctt" in
  [%expect {|
    Evaluate pow 2 10 --> 1024 : Nat
    Evaluate pow 3 4 --> 81 : Nat
    Evaluate pow 0 0 --> 1 : Nat
    Evaluate sumTo NatFun.id 11 --> 55 : Nat
    Evaluate sumTo (fun (x1 : Nat) -> mult x1 x1) 6 --> 55 : Nat
    Evaluate factorial 5 --> 120 : Nat
    Evaluate factorial 0 --> 1 : Nat
    Evaluate powZero 7 --> true : True
    Evaluate powOne 9 --> true : True
    Evaluate onePow 6 --> true : True
    Evaluate powPlus 2 1 3 --> true : True
    Evaluate powMult 2 2 2 --> true : True
    Evaluate powMultBase 2 2 2 --> true : True
    Evaluate sumToPlus NatFun.id (fun (x1 : Nat) -> mult x1 x1) 4 --> true : True
    Evaluate sumToScale 3 NatFun.id 4 --> true : True
    Evaluate sumToConst 4 5 --> true : True
    Evaluate gauss 4 --> true : True
    Evaluate sumOdd 4 --> true : True
    Evaluate factSucc 3 --> true : True
    Evaluate factPos 4 --> true : True
    Evaluate factLeSucc 3 --> true : True
    Evaluate lePowFact 3 --> true : True
    |}]

let%expect_test "lib/Streams.mctt" =
  let _ = main_of_lib "Streams.mctt" in
  [%expect {|
    Evaluate sumVec 6 (S.take 6 nats) --> 15 : Nat
    Evaluate V.nth Nat 5 (S.take 5 evens) 4 true --> 8 : Nat
    Evaluate S.nth odds 6 --> 13 : Nat
    Evaluate sumVec 5 (S.take 5 squares) --> 30 : Nat
    Evaluate S.nth fibs 10 --> 55 : Nat
    Evaluate S.nth lucas 8 --> 47 : Nat
    Evaluate sumVec 10 (S.take 10 fibs) --> 88 : Nat
    Evaluate S.nth (S.scan Nat plus 0 squares) 5 --> 30 : Nat
    Evaluate S.nth (S.interleave evens odds) 7 --> 7 : Nat
    Evaluate S.nth (S.drop 4 squares) 3 --> 49 : Nat
    Evaluate S.nth (S.zipWith Nat Nat plus evens odds) 4 --> 17 : Nat
    Evaluate S.head (S.tail (S.cons 9 nats)) --> 0 : Nat
    Evaluate S.nth (S.const 3) 100 --> 3 : Nat
    Evaluate headCons 9 nats --> true : True
    Evaluate tailCons 9 squares 3 --> true : True
    Evaluate nthConst 3 100 --> true : True
    Evaluate nthMap square nats 4 --> true : True
    Evaluate nthZipWith plus evens odds 3 --> true : True
    Evaluate nthIterate (fun (x1 : Nat) -> succ (succ x1)) 1 4 --> true : True
    Evaluate tailIterate (fun (x1 : Nat) -> succ (succ x1)) 1 4 --> true : True
    Evaluate nthNats 12 --> true : True
    Evaluate nthDrop 3 squares 1 --> true : True
    Evaluate nthTake 5 squares 3 true --> true : True
    Evaluate scanSum squares 4 --> true : True
    Evaluate scanSum fibs 6 --> true : True
    Evaluate nthInterleaveEven 3 evens odds --> true : True
    Evaluate nthInterleaveOdd 3 evens odds --> true : True
    Evaluate sumToShift squares 3 --> true : True
    Evaluate sumTake 5 nats --> true : True
    |}]

let%expect_test "lib/Combinatorics.mctt" =
  let _ = main_of_lib "Combinatorics.mctt" in
  [%expect {|
    Evaluate choose 0 0 --> 1 : Nat
    Evaluate choose 1 0 --> 1 : Nat
    Evaluate choose 1 1 --> 1 : Nat
    Evaluate choose 2 0 --> 1 : Nat
    Evaluate choose 2 1 --> 2 : Nat
    Evaluate choose 2 2 --> 1 : Nat
    Evaluate choose 3 0 --> 1 : Nat
    Evaluate choose 3 1 --> 3 : Nat
    Evaluate choose 3 2 --> 3 : Nat
    Evaluate choose 3 3 --> 1 : Nat
    Evaluate choose 4 0 --> 1 : Nat
    Evaluate choose 4 1 --> 4 : Nat
    Evaluate choose 4 2 --> 6 : Nat
    Evaluate choose 4 3 --> 4 : Nat
    Evaluate choose 4 4 --> 1 : Nat
    Evaluate choose 5 0 --> 1 : Nat
    Evaluate choose 5 1 --> 5 : Nat
    Evaluate choose 5 2 --> 10 : Nat
    Evaluate choose 5 3 --> 10 : Nat
    Evaluate choose 5 4 --> 5 : Nat
    Evaluate choose 5 5 --> 1 : Nat
    Evaluate choose 6 0 --> 1 : Nat
    Evaluate choose 6 1 --> 6 : Nat
    Evaluate choose 6 2 --> 15 : Nat
    Evaluate choose 6 3 --> 20 : Nat
    Evaluate choose 6 4 --> 15 : Nat
    Evaluate choose 6 5 --> 6 : Nat
    Evaluate choose 6 6 --> 1 : Nat
    Evaluate choose 3 5 --> 0 : Nat
    Evaluate sumTo (choose 6) 7 --> 64 : Nat
    Evaluate fib 0 --> 0 : Nat
    Evaluate fib 1 --> 1 : Nat
    Evaluate fib 10 --> 55 : Nat
    Evaluate sumTo fib 10 --> 88 : Nat
    Evaluate chooseZero 5 --> true : True
    Evaluate chooseSelf 5 --> true : True
    Evaluate chooseOne 5 --> true : True
    Evaluate chooseOver 3 5 true --> true : True
    Evaluate pascal 4 2 --> true : True
    Evaluate chooseSymm 2 3 --> true : True
    Evaluate chooseSymmSub 5 2 true --> true : True
    Evaluate rowSum 4 --> true : True
    Evaluate fibSucc 5 --> true : True
    Evaluate fibPos 5 --> true : True
    Evaluate fibMono 5 --> true : True
    Evaluate fibMonoPlus 2 4 --> true : True
    Evaluate fibSum 5 --> true : True
    Evaluate fibPlus 3 2 --> true : True
    |}]

let%expect_test "lib/NumberTheory.mctt" =
  let _ = main_of_lib "NumberTheory.mctt" in
  [%expect {|
    Evaluate gcd 12 18 --> 6 : Nat
    Evaluate gcd 17 5 --> 1 : Nat
    Evaluate gcd 0 9 --> 9 : Nat
    Evaluate gcd 9 0 --> 9 : Nat
    Evaluate nthPrime 0 --> 2 : Nat
    Evaluate nthPrime 1 --> 3 : Nat
    Evaluate nthPrime 2 --> 5 : Nat
    Evaluate nthPrime 3 --> 7 : Nat
    Evaluate nthPrime 4 --> 11 : Nat
    Evaluate nthPrime 5 --> 13 : Nat
    Evaluate nthPrime 6 --> 17 : Nat
    Evaluate nthPrime 7 --> 19 : Nat
    Evaluate nthPrime 8 --> 23 : Nat
    Evaluate nthPrime 9 --> 29 : Nat
    Evaluate nthPrime 10 --> 31 : Nat
    Evaluate sumTo isPrime 30 --> 10 : Nat
    Evaluate sumTo (fun (x1 : Nat) -> mult x1 (isPrime x1)) 30 --> 129 : Nat
    Evaluate smallestDivisor 91 --> 7 : Nat
    Evaluate smallestDivisor 29 --> 29 : Nat
    Evaluate Prime 29 --> True : Type@0
    Evaluate Prime 27 --> False : Type@0
    Evaluate gcdZeroLeft 5 --> true : True
    Evaluate gcdZeroRight 5 --> true : True
    Evaluate gcdSelf 7 --> true : True
    Evaluate gcdOneRight 9 --> true : True
    Evaluate gcdDividesLeft 6 9 --> true : True
    Evaluate gcdDividesRight 6 9 --> true : True
    Evaluate gcdGreatest 2 8 12 true true --> true : True
    Evaluate gcdComm 6 9 --> true : True
    Evaluate dividesMultLeft 3 6 2 true --> true : True
    Evaluate dividesPlusCancel 3 6 9 true true --> true : True
    Evaluate twoPrime --> true : True
    Evaluate sevenPrime --> true : True
    Evaluate nineNotPrime
      --> fun (x1 : False) -> Prelude::Arith::Prime.Facts.nineNotPrime x1
      : forall (x1 : False) -> False
    Evaluate smallestDivisorDivides 15 --> true : True
    Evaluate primeGeTwo 13 true --> true : True
    Evaluate primeSmallestDivisor 13 true --> true : True
    |}]

(** Module forms *)

let%expect_test "a local module with parameters" =
  let _ = main_of_body "eval let module X (n : Nat) where def f : Nat := n end end in X.f 3 end" in
  [%expect {|
    Evaluate let module M1 (x1 : Nat) where
                   def f : Nat :=
                     x1
                   end
                 end
             in M1.f 3
             end --> 3 : Nat
    |}]

let%expect_test "a local alias of a submodule" =
  let _ =
    main_of_body
      "eval let module X (n : Nat) where module V where def f : Nat := n end end end in \
       let module P := X.V in P.f 3 end end"
  in
  [%expect {|
    Evaluate let module M1 (x1 : Nat) where
                   module V where
                     def f : Nat :=
                       x1
                     end
                   end
                 end;
                 module M2 := M1.V
             in M2.f 3
             end --> 3 : Nat
    |}]

let%expect_test "beta substitutes into a local module" =
  let _ = main_of_body "eval (fun (n : Nat) -> let module X where def f : Nat := n end end in X.f end) 3" in
  [%expect {|
    Evaluate (fun (x1 : Nat)
               -> let module M1 where
                        def f : Nat :=
                          x1
                        end
                      end in M1.f end)
               3 --> 3 : Nat
    |}]

let%expect_test "a nested parameterized module, selected through its parent" =
  let _ =
    main_of_body
      "eval let module M (A : Type@0) where def x : Nat := zero end \
       module N (B : Type@0) where def c (y : B) : B := y end end end in \
       M.N.c Nat Nat 3 end"
  in
  [%expect {|
    Evaluate let module M1 (A1 : Type@0) where
                   def x : Nat :=
                     0
                   end
                   module N (A2 : Type@0) where
                     def c : forall (x1 : A2) -> A2 :=
                       fun (x2 : A2) -> x2
                     end
                   end
                 end
             in M1.N.c Nat Nat 3
             end --> 3 : Nat
    |}]

let%expect_test "a module alias with parameters" =
  let _ =
    main_of_body
      "module M (A : Type@0) where def id (x : A) : A := x end end \
       module P (B : Type@0) := M B \
       eval P.id Nat 4"
  in
  [%expect {| Evaluate P.id Nat 4 --> 4 : Nat |}]

let%expect_test "a dotted module declaration" =
  let _ = main_of_body "module A.B (n : Nat) where def f : Nat := succ n end end eval A.B.f 1" in
  [%expect {| Evaluate A.B.f 1 --> 2 : Nat |}]

let%expect_test "a local body with an import" =
  let _ =
    main_of_body
      "eval let module L where module N where def y : Nat := 5 end end \
       open N use (y) def z : Nat := succ y end end in L.z end"
  in
  [%expect {|
    Evaluate let module M1 where
                   module N where
                     def y : Nat :=
                       5
                     end
                   end
                   private def y : Nat :=
                     N.y
                   end
                   def z : Nat :=
                     succ y
                   end
                 end
             in M1.z
             end --> 6 : Nat
    |}]

let%expect_test "a private definition in a local body" =
  let _ = main_of_body "eval let module L where private def s : Nat := 0 end end in L.s end" in
  [%expect {| Error: s is private in a local module, but it is used outside it |}]

let%expect_test "a private module in a local body" =
  let _ =
    main_of_body
      "eval let module L where private module N where def y : Nat := 0 end end end in L.N.y end"
  in
  [%expect {| Error: N is private in a local module, but it is used outside it |}]

let%expect_test "a local import uses a name twice" =
  let _ =
    main_of_body
      "eval let module L where module N where def y : Nat := 5 end end \
       open N use (y; y) def z : Nat := y end end in L.z end"
  in
  [%expect {| Error: y is already declared |}]

let%expect_test "a local body with public definitions and an import" =
  let _ =
    main_of_body
      "eval let module L where module N where def y : Nat := 5 end def w : Nat := 1 end end \
       open N use (y; w) def z : Nat := y end def v : Nat := w end end in L.v end"
  in
  [%expect {|
    Evaluate let module M1 where
                   module N where
                     def y : Nat :=
                       5
                     end
                     def w : Nat :=
                       1
                     end
                   end
                   private def y : Nat :=
                     N.y
                   end
                   private def w : let x1 : Nat := 5 in Nat end :=
                     N.w
                   end
                   def z : Nat :=
                     y
                   end
                   def v : Nat :=
                     w
                   end
                 end
             in M1.v
             end --> 1 : Nat
    |}]

let%expect_test "an import of a local module alias" =
  let _ =
    main_of_body
      "module M where def y : Nat := 7 end end module P := M open P as Q eval Q.y"
  in
  [%expect {| Evaluate Q.y --> 7 : Nat |}]

(** Imports declare definitions *)

let%expect_test "use declares a private definition" =
  let _ = main_of_multi_string "import Lib::Num use (double) module X where eval double 3 end" in
  [%expect {| Evaluate double 3 --> 6 : Nat |}]

let%expect_test "use as renames the definition" =
  let _ = main_of_multi_string "import Lib::Num use (double as dbl) module X where eval dbl 3 end" in
  [%expect {| Evaluate dbl 3 --> 6 : Nat |}]

let%expect_test "export declares a public definition" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where module M where import Lib::Num export (double) end \
       eval M.double 3 end"
  in
  [%expect {| Evaluate M.double 3 --> 6 : Nat |}]

let%expect_test "export as renames the public definition" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where module M where import Lib::Num export (double as dbl) end \
       eval M.dbl 3 end"
  in
  [%expect {| Evaluate M.dbl 3 --> 6 : Nat |}]

let%expect_test "a used definition is private to its module" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where module M where import Lib::Num use (double) end \
       eval M.double 3 end"
  in
  [%expect {| Error: X.M.double is private |}]

let%expect_test "use of a submodule declares a private alias" =
  let _ = main_of_multi_string "import Lib::Num use (Ops) module X where eval Ops.pred 3 end" in
  [%expect {| Evaluate Ops.pred 3 --> 2 : Nat |}]

let%expect_test "export of a submodule declares a public alias" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where module M where import Lib::Num export (Ops as P) end \
       eval M.P.pred 3 end"
  in
  [%expect {| Evaluate M.P.pred 3 --> 2 : Nat |}]

let%expect_test "import as declares a private alias" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where module M where import Lib::Num.Ops as O \
       def z : Nat := O.pred 3 end end eval M.z end"
  in
  [%expect {| Evaluate M.z --> 2 : Nat |}]

let%expect_test "an alias declared by import as is private" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where module M where import Lib::Num.Ops as O end \
       eval M.O.pred 3 end"
  in
  [%expect {| Error: X.M.O is private |}]

let%expect_test "an import with arguments and use" =
  let _ =
    main_of_multi_string
      "import Lib::Priv module X where module M where import Lib::Priv.F 4 use (g) \
       def z : Nat := succ g end end eval M.z end"
  in
  [%expect {| Evaluate M.z --> 5 : Nat |}]

let%expect_test "an import with arguments and export as" =
  let _ =
    main_of_multi_string
      "import Lib::Priv module X where module M where import Lib::Priv.F 4 export (g as h) end \
       eval M.h end"
  in
  [%expect {| Evaluate M.h --> 4 : Nat |}]

let%expect_test "a member used and exported under two names is rejected" =
  let _ =
    main_of_multi_string
      "import Lib::Priv module X where import Lib::Priv.F 4 use (g) export (g as h) end"
  in
  [%expect {| Error: g is used and exported |}]

let%expect_test "an imported member may have a private type" =
  let _ = main_of_multi_string "import Lib::Priv.Sub use (t) module X where eval t end" in
  [%expect {| Evaluate t --> 7 : Nat |}]

let%expect_test "a used name that is not a member is rejected" =
  let _ = main_of_multi_string "import Lib::Num use (q) module X where end" in
  [%expect {| Error: Lib::Num.q is not a member |}]

let%expect_test "a member both used and exported is rejected" =
  let _ = main_of_multi_string "module X where import Lib::Num use (double) export (double) end" in
  [%expect {| Error: double is used and exported |}]

let%expect_test "an import declaring a name twice is rejected" =
  let _ = main_of_multi_string "import Lib::Num use (double; double) module X where end" in
  [%expect {| Error: double is already declared |}]

let%expect_test "a used name must be fresh in its frame" =
  let _ =
    main_of_multi_string "import Lib::Num use (double) module X where def double : Nat := 0 end end"
  in
  [%expect {| Error: double is already declared |}]

let%expect_test "an import of a definition is rejected" =
  let _ = main_of_multi_string "import Lib::Num.double use (x) module X where end" in
  [%expect {| Error: ill-formed open |}]

let%expect_test "a private member is not used through an import" =
  let _ = main_of_multi_string "import Lib::Priv use (s) module X where end" in
  [%expect {| Error: Lib::Priv.s is private |}]

let%expect_test "a local use, use as and export" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num use (double as dbl) \
       export (Ops) def t : Nat := dbl 2 end end in L.Ops.pred L.t end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   private def dbl : forall (x1 : Nat) -> Nat :=
                     Lib::Num.double
                   end
                   module Ops := Lib::Num.Ops
                   def t : Nat :=
                     dbl 2
                   end
                 end
             in M1.Ops.pred M1.t
             end --> 3 : Nat
    |}]

let%expect_test "a local export as" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num export (double as dbl) \
       end in L.dbl 2 end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   def dbl : forall (x1 : Nat) -> Nat :=
                     Lib::Num.double
                   end
                 end
             in M1.dbl 2
             end --> 4 : Nat
    |}]

let%expect_test "a local submodule use" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num use (Ops) \
       def t : Nat := Ops.pred 5 end end in L.t end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   private module Ops := Lib::Num.Ops
                   def t : Nat :=
                     Ops.pred 5
                   end
                 end
             in M1.t
             end --> 4 : Nat
    |}]

let%expect_test "a local import as" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num as W \
       def t : Nat := W.double 1 end end in L.t end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   private module W := Lib::Num
                   def t : Nat :=
                     W.double 1
                   end
                 end
             in M1.t
             end --> 2 : Nat
    |}]

let%expect_test "a local use is private" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num use (double) end \
       in L.double 2 end end"
  in
  [%expect {| Error: double is private in a local module, but it is used outside it |}]

let%expect_test "a local submodule use is private" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num use (Ops) end \
       in L.Ops.pred 2 end end"
  in
  [%expect {| Error: Ops is private in a local module, but it is used outside it |}]

let%expect_test "a local import as is private" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num as W end \
       in L.W.double 2 end end"
  in
  [%expect {| Error: W is private in a local module, but it is used outside it |}]

let%expect_test "a local use of a missing member is rejected" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num use (q) end in 0 end end"
  in
  [%expect {| Error: Lib::Num.q is not a member |}]

let%expect_test "a local member both used and exported is rejected" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num use (double) \
       export (double) end in 0 end end"
  in
  [%expect {| Error: double is used and exported |}]

let%expect_test "a local import of a definition is rejected" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num.double use (x) end \
       in 0 end end"
  in
  [%expect {| Error: ill-formed open |}]

(** Privacy through local modules *)

let%expect_test "a private local definition is used inside its body" =
  let _ =
    main_of_body
      "eval let module L where private def s : Nat := 1 end def t : Nat := succ s end end in L.t end"
  in
  [%expect {|
    Evaluate let module M1 where
                   private def s : Nat :=
                     1
                   end
                   def t : Nat :=
                     succ s
                   end
                 end
             in M1.t
             end --> 2 : Nat
    |}]

let%expect_test "a private local definition is rejected outside its body" =
  let _ =
    main_of_body
      "eval let module L where private def s : Nat := 1 end def t : Nat := succ s end end in L.s end"
  in
  [%expect {| Error: s is private in a local module, but it is used outside it |}]

let%expect_test "a private member of a local submodule is used inside it" =
  let _ =
    main_of_body
      "eval let module L where module N where private def u : Nat := 1 end def v : Nat := u end \
       end end in L.N.v end"
  in
  [%expect {|
    Evaluate let module M1 where
                   module N where
                     private def u : Nat :=
                       1
                     end
                     def v : Nat :=
                       u
                     end
                   end
                 end
             in M1.N.v
             end --> 1 : Nat
    |}]

let%expect_test "a private member of a local submodule is rejected outside it" =
  let _ =
    main_of_body
      "eval let module L where module N where private def u : Nat := 1 end end end in L.N.u end"
  in
  [%expect {| Error: N.u is private in a local module, but it is used outside it |}]

let%expect_test "a private global member is rejected through a local alias" =
  let _ = main_of_multi_string "import Lib::Priv module X where eval let module L := Lib::Priv in L.s end end" in
  [%expect {| Error: Lib::Priv.s is private |}]

let%expect_test "a public global member is used through a local alias" =
  let _ = main_of_multi_string "import Lib::Priv module X where eval let module L := Lib::Priv in L.pub end end" in
  [%expect {| Evaluate let module M1 := Lib::Priv in M1.pub end --> 8 : Nat |}]

let%expect_test "a private member of a closed sibling is rejected" =
  let _ = main_of_body "module A where private def s : Nat := 0 end end def t : Nat := A.s end" in
  [%expect {| Error: Test.A.s is private |}]

(** Module rejections *)

let%expect_test "a private member is not selected from outside" =
  let _ = main_of_body "module M where private def s : Nat := 0 end end eval M.s" in
  [%expect {| Error: Test.M.s is private |}]

let%expect_test "a private member is not imported by use" =
  let _ = main_of_body "module M where private def s : Nat := 0 end end open M use (s)" in
  [%expect {| Error: Test.M.s is private |}]

let%expect_test "a private member is used in its unit and in a nested module" =
  let _ = main_of_body "module M where private def s : Nat := 0 end def p : Nat := s end module N where def t : Nat := s end end end eval M.p eval M.N.t" in
  [%expect {|
    Evaluate M.p --> 0 : Nat
    Evaluate M.N.t --> 0 : Nat
    |}]

let%expect_test "a private member of another unit is not used in a def" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where def x : Nat := P.s end end" in
  [%expect {| Error: Lib::Priv.s is private |}]

let%expect_test "a private member of another unit is not evaluated" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where eval P.s end" in
  [%expect {| Error: Lib::Priv.s is private |}]

let%expect_test "a private member of another unit is not named by its path" =
  let _ = main_of_multi_string "import Lib::Priv module X where eval Lib::Priv.s end" in
  [%expect {| Error: Lib::Priv.s is private |}]

let%expect_test "a private member of another unit is not used in a module body" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where module M where def y : Nat := P.s end end end" in
  [%expect {| Error: Lib::Priv.s is private |}]

let%expect_test "a private member of another unit is not used in module parameters" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where module M (x : P.T) where end end" in
  [%expect {| Error: Lib::Priv.T is private |}]

let%expect_test "a private member of another unit is not used in an alias" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where module A := P.F P.s end" in
  [%expect {| Error: Lib::Priv.s is private |}]

let%expect_test "a private member of another unit is not imported by use" =
  let _ = main_of_multi_string "import Lib::Priv use (s) module X where end" in
  [%expect {| Error: Lib::Priv.s is private |}]

let%expect_test "a private member of another unit is not imported by use in a local module" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where module L where open P use (s) end end" in
  [%expect {| Error: Lib::Priv.s is private |}]

let%expect_test "a private member is not reached through an alias declared outside" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where module Q := P.Sub eval Q.u end" in
  [%expect {| Error: Lib::Priv.Sub.u is private |}]

let%expect_test "a private member is not reached through an alias in its unit" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where eval P.A.u end" in
  [%expect {| Error: Lib::Priv.Sub.u is private |}]

let%expect_test "a public definition naming a private one is used from another unit" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where eval P.pub eval P.Sub.t end" in
  [%expect {|
    Evaluate P.pub --> 8 : Nat
    Evaluate P.Sub.t --> 7 : Nat
    |}]

let%expect_test "a module is applied to its parameters one at a time" =
  let _ = main_of_body "module F (A : Type@0) (f : forall (x : A) -> A) where def ap : forall (x : A) -> A := fun (x : A) -> f (f x) end end module G := F Nat module H := G (fun (x : Nat) -> succ x) eval H.ap 1 eval (F Nat (fun (x : Nat) -> succ x)).ap 3" in
  [%expect {|
    Evaluate H.ap 1 --> 3 : Nat
    Evaluate (F Nat (fun (x1 : Nat) -> succ x1)).ap 3 --> 5 : Nat
    |}]

let%expect_test "a module is not applied to more arguments than it has parameters" =
  let _ = main_of_body "module F (A : Type@0) where def a : Type@0 := A end end module G := F Nat Nat" in
  [%expect {| Error: ill-formed module expression for module G |}]

let%expect_test "a member of a module applied to too many arguments is rejected" =
  let _ = main_of_body "module F (A : Type@0) where def a : Type@0 := A end end eval (F Nat Nat).a" in
  [%expect {| Error: (F Nat Nat).a has no inferable type |}]

let%expect_test "a module argument is checked against the outermost parameter" =
  let _ = main_of_body "module F (A : Type@0) where def a : Type@0 := A end end module G := F 0" in
  [%expect {| Error: ill-formed module expression for module G |}]

let%expect_test "the modifiers of a definition are written in either order" =
  let _ = main_of_body "module M where abstract private def s : Nat := 1 end private abstract def u : Nat := 2 end def t : Nat := s end end eval M.t" in
  [%expect {| Evaluate M.t --> M.s : Nat |}]

let%expect_test "an abstract private definition is private" =
  let _ = main_of_body "module M where abstract private def s : Nat := 1 end end eval M.s" in
  [%expect {| Error: Test.M.s is private |}]

let%expect_test "a private module is used inside its unit" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where eval P.viaHidden end" in
  [%expect {| Evaluate P.viaHidden --> 2 : Nat |}]

let%expect_test "a member of a private module of another unit is rejected" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where eval P.Hidden.h end" in
  [%expect {| Error: Lib::Priv.Hidden is private |}]

let%expect_test "a private module of another unit is not aliased" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where module Q := P.Hidden end" in
  [%expect {| Error: Lib::Priv.Hidden is private |}]

let%expect_test "a private module alias of another unit is rejected" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where eval P.PA.t end" in
  [%expect {| Error: Lib::Priv.PA is private |}]

let%expect_test "a private module of another unit is not imported by use" =
  let _ = main_of_multi_string "import Lib::Priv use (Hidden) module X where end" in
  [%expect {| Error: Lib::Priv.Hidden is private |}]

let%expect_test "private module M.N makes only N private, to M" =
  let _ = main_of_body "private module M.N where def a : Nat := 1 end end module Q := M eval M.N.a" in
  [%expect {| Error: Test.M.N is private |}]

let%expect_test "a module alias of a term is rejected" =
  let _ = main_of_body "module P := Nat" in
  [%expect {| Error: not a module |}]

let%expect_test "an alias of a module is not a term" =
  let _ = main_of_body "module M where end open M as N eval N" in
  [%expect {| Error: N has no inferable type |}]

let%expect_test "a module argument of the wrong type is rejected" =
  let _ = main_of_body "module M (n : Nat) where def f : Nat := n end end eval (M Type@0).f" in
  [%expect {| Error: (M Type@0).f has no inferable type |}]

let%expect_test "a missing member is rejected" =
  let _ = main_of_body "module M where end eval M.f" in
  [%expect {| Error: M.f has no inferable type |}]

let%expect_test "a module alias may not reuse a name" =
  let _ = main_of_body "module M where end module M := M" in
  [%expect {| Error: M is already declared |}]

let%expect_test "a local module may not repeat a parameter" =
  let _ = main_of_body "eval let module X (n : Nat) (n : Nat) where end in 0 end" in
  [%expect {| Error: duplicate parameter n |}]

let%expect_test "an opaque definition is rejected in a local body" =
  let _ = main_of_body "eval let module X where abstract def f : Nat := 0 end end in X.f end" in
  [%expect {|
    Error: let module M1 where
                 abstract def f : Nat :=
                   0
                 end
               end in M1.f end has no inferable type
    |}]

let%expect_test "a local import of a unit that is not imported is rejected" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "module LocalImp where eval let module L where open Prelude::Arith::MinMax use (max) \
       def m : Nat := max 2 3 end end in L.m end end"
  in
  [%expect {| Error: the unit is not imported |}]

let%expect_test "a local import of a unit imported at the top level" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude::Arith::MinMax module LocalImp where eval let module L where \
       open Prelude::Arith::MinMax use (max) def m : Nat := max 2 3 end end in L.m end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   private def max : forall (x1 : Nat)
                                            (x2 : Nat)
                                       -> Nat :=
                     Prelude::Arith::MinMax.max
                   end
                   def m : Nat :=
                     max 2 3
                   end
                 end
             in M1.m
             end --> 3 : Nat
    |}]

let%expect_test "an eval is rejected in a local body" =
  let _ = main_of_body "eval let module X where eval 0 end in 0 end" in
  [%expect {| Error: eval is not allowed in a local module |}]

let%expect_test "a local module does not escape its let" =
  let _ = main_of_body "eval let module X where def f : Nat := 0 end end in X end" in
  [%expect {|
    Error: let module M1 where
                 def f : Nat :=
                   0
                 end
               end in M1 end has no inferable type
    |}]

let%expect_test "a use of a missing member is rejected" =
  let _ = main_of_body "module M where end open M use (f)" in
  [%expect {| Error: Test.M.f is not a member |}]

let%expect_test "a module expression is expected after :=" =
  let _ = main_of_body "module P := where" in
  [%expect {|
    Error: on "where" (at line 1, column 31 - line 1, column 36): Expected a
      module expression after ":=".
    |}]

let%expect_test "lib/Algebra.mctt" =
  let _ = main_of_lib "Algebra.mctt" in
  [%expect {|
    Evaluate Additive.pow 3 4 --> 12 : Nat
    Evaluate Multiplicative.pow 2 5 --> 32 : Nat
    Evaluate Maximum.pow 7 3 --> 7 : Nat
    Evaluate Composition.pow (fun (x1 : Nat) -> succ (succ x1)) 5 0 --> 10 : Nat
    Evaluate Sums.pow 6 3 --> 18 : Nat
    Evaluate Unfold.additivePow 3 4 --> true : True
    Evaluate Scaling.multPlusRight 2 3 2 --> true : True
    Evaluate Scaling.multAssocPow 2 3 2 --> true : True
    Evaluate Scaling.multPlusLeft 2 3 4 --> true : True
    Evaluate Exponents.powPlus 2 1 3 --> true : True
    Evaluate Exponents.powMult 2 2 2 --> true : True
    Evaluate Exponents.powOfProduct 2 2 2 --> true : True
    Evaluate Exponents.fourthPower 2 --> true : True
    Evaluate Iteration.iterPlus (fun (x1 : Nat) -> succ x1) 2 3 4 --> true : True
    Evaluate maxPowSucc 5 3 --> true : True
    |}]

let%expect_test "lib/Polynomials.mctt" =
  let _ = main_of_lib "Polynomials.mctt" in
  [%expect {|
    Evaluate At.horner 2 (cubic 1 2 3 4) 4 --> 49 : Nat
    Evaluate At.naive 2 (cubic 1 2 3 4) 4 --> 49 : Nat
    Evaluate let module M1 (x1 : Coeffs) where
                   private def max : forall (x2 : Nat)
                                            (x3 : Nat)
                                       -> Nat :=
                     Prelude::Arith::MinMax.max
                   end
                   def value : forall (x4 : Nat) -> Nat :=
                     fun (x5 : Nat) -> At.horner x5 x1 4
                   end
                   def total : forall (x6 : Nat) -> Nat :=
                     fun (x7 : Nat) -> sumTo value x7
                   end
                   def peak : forall (x8 : Nat) -> Nat :=
                     fun (x9 : Nat)
                       -> rec x9 return x10 . Nat
                          | zero => 0
                          | succ x11, x12 => max (value x11) x12
                          end
                   end
                 end
             in plus (M1.total (cubic 1 1 0 0) 4) (M1.peak (cubic 0 0 1 0) 5)
             end --> 26 : Nat
    Evaluate At.hornerNaive 2 (cubic 1 0 1 0) 4 --> true : True
    Evaluate At.hornerNaive 3 (cubic 2 1 0 0) 4 --> true : True
    Evaluate hornerAtOne (cubic 3 1 4 1) 4 --> true : True
    |}]

let%expect_test "lib/Binary.mctt" =
  let _ = main_of_lib "Binary.mctt" in
  [%expect {|
    Evaluate half 13 --> 6 : Nat
    Evaluate bit 13 --> 1 : Nat
    Evaluate bits 13 0 --> 1 : Nat
    Evaluate bits 13 1 --> 0 : Nat
    Evaluate bits 13 2 --> 1 : Nat
    Evaluate bits 13 3 --> 1 : Nat
    Evaluate fromBits (bits 13) 4 --> 13 : Nat
    Evaluate bitCount 13 --> 3 : Nat
    Evaluate bitCount 255 --> 8 : Nat
    Evaluate bitCount 256 --> 1 : Nat
    Evaluate fromBits oneZeroOneOne 4 --> 13 : Nat
    Evaluate powFast 3 5 --> 243 : Nat
    Evaluate powFast 2 10 --> 1024 : Nat
    Evaluate fromBitsDouble 6 3 --> true : True
    Evaluate powFastDouble 2 2 --> true : True
    Evaluate powFastDouble 3 1 --> true : True
    |}]

let%expect_test "lib/Groups.mctt" =
  let _ = main_of_lib "Groups.mctt" in
  [%expect {|
    Evaluate negative minusThree --> 1 : Nat
    Evaluate magnitude minusThree --> 3 : Nat
    Evaluate negative (Additive.Base.pow minusThree 4) --> 1 : Nat
    Evaluate magnitude (Additive.Base.pow minusThree 4) --> 12 : Nat
    Evaluate negative (minus (ofNat 4) (ofNat 9)) --> 1 : Nat
    Evaluate magnitude (minus (ofNat 4) (ofNat 9)) --> 5 : Nat
    Evaluate solve (ofNat 2) (ofNat 5) (ofNat 3) true --> true : True
    Evaluate solve minusThree (ofNat 1) (pair 4 0) true --> true : True
    Evaluate negateMinus (ofNat 3) minusThree --> true : True
    Evaluate Multiples.multipleNegate minusThree 3 --> true : True
    Evaluate Multiples.multipleAdd minusThree (ofNat 5) 2 --> true : True
    Evaluate Additive.Laws.invOp (ofNat 1) minusThree --> true : True
    |}]

(** Definition keywords *)

let%expect_test "every definition keyword, with parameters" =
  let _ =
    main_of_body
      "module M where \
       def a (n : Nat) : Nat := succ n end \
       theorem b (n : Nat) : Nat := n end \
       lemma c (n : Nat) : Nat := n end \
       fact d (n : Nat) : Nat := n end \
       remark e (n : Nat) : Nat := n end \
       let f (n : Nat) : Nat := succ n end \
       given g (n : Nat) : Nat := succ n end \
       def h : Nat := a (b (c (d (e (f (g 0)))))) end end \
       eval M.a 1 eval M.b 1 eval M.c 1 eval M.h"
  in
  [%expect {|
    Evaluate M.a 1 --> 2 : Nat
    Evaluate M.b 1 --> M.b 1 : Nat
    Evaluate M.c 1 --> M.c 1 : Nat
    Evaluate M.h --> succ (M.b (M.c (M.d (M.e 2)))) : Nat
    |}]

let%expect_test "let and given are private" =
  let _ = main_of_body "module M where let f : Nat := 1 end end eval M.f" in
  [%expect {| Error: Test.M.f is private |}];
  let _ = main_of_body "module M where given f : Nat := 1 end end eval M.f" in
  [%expect {| Error: Test.M.f is private |}]

let%expect_test "fact and remark are private" =
  let _ = main_of_body "module M where fact f : Nat := 1 end end eval M.f" in
  [%expect {| Error: Test.M.f is private |}];
  let _ = main_of_body "module M where remark f : Nat := 1 end end eval M.f" in
  [%expect {| Error: Test.M.f is private |}]

let%expect_test "the modifiers a keyword takes" =
  let _ =
    main_of_body
      "module M where private lemma b : Nat := 2 end abstract given d : Nat := 4 end \
       private abstract def e : Nat := 5 end abstract private def f : Nat := 6 end \
       def t : Nat := b end def u : Nat := d end def v : Nat := e end def w : Nat := f end end \
       eval M.t eval M.u eval M.v eval M.w"
  in
  [%expect {|
    Evaluate M.t --> M.b : Nat
    Evaluate M.u --> M.d : Nat
    Evaluate M.v --> M.e : Nat
    Evaluate M.w --> M.f : Nat
    |}];
  let _ =
    main_of_body
      "module M where private theorem a : Nat := 1 end abstract let c : Nat := 3 end \
       def t : Nat := succ (succ a) end def u : Nat := c end end eval M.t eval M.u"
  in
  [%expect {|
    Evaluate M.t --> succ (succ M.a) : Nat
    Evaluate M.u --> M.c : Nat
    |}]

let%expect_test "a modifier a keyword implies is rejected" =
  let _ = main_of_body "abstract theorem a : Nat := 1 end" in
  [%expect {| Error: theorem is already abstract |}];
  let _ = main_of_body "abstract private lemma a : Nat := 1 end" in
  [%expect {| Error: lemma is already abstract |}];
  let _ = main_of_body "private fact a : Nat := 1 end" in
  [%expect {| Error: fact takes no modifiers |}];
  let _ = main_of_body "abstract remark a : Nat := 1 end" in
  [%expect {| Error: remark takes no modifiers |}];
  let _ = main_of_body "private let a : Nat := 1 end" in
  [%expect {| Error: let is already private |}];
  let _ = main_of_body "private abstract given a : Nat := 1 end" in
  [%expect {| Error: given is already private |}]

let%expect_test "a command let needs a type" =
  let _ = main_of_body "let x := 1 end" in
  [%expect {|
    Error: on ":=" (at line 1, column 25 - line 1, column 27): Expected a
      parameter "(x : A)", or ":" followed by the type of the definition.
    |}]

let%expect_test "a command let and a term let" =
  let _ = main_of_body "let x : Nat := 1 end eval let y := succ x in y end let z : Nat := x end eval z" in
  [%expect {|
    Evaluate let x1 := succ x in x1 end --> 2 : Nat
    Evaluate z --> 1 : Nat
    |}]

let%expect_test "keywords in a local body" =
  let _ =
    main_of_body
      "eval let module L where let a (n : Nat) : Nat := succ n end given b : Nat := a 1 end \
       def c : Nat := b end end in L.c end"
  in
  [%expect {|
    Evaluate let module M1 where
                   private def a : forall (x1 : Nat) -> Nat :=
                     fun (x2 : Nat) -> succ x2
                   end
                   private def b : Nat :=
                     a 1
                   end
                   def c : Nat :=
                     b
                   end
                 end
             in M1.c
             end --> 2 : Nat
    |}];
  let _ = main_of_body "eval let module L where let a : Nat := 1 end end in L.a end" in
  [%expect {| Error: a is private in a local module, but it is used outside it |}]

let%expect_test "an abstract keyword is rejected in a local body" =
  let _ = main_of_body "eval let module L where theorem a : Nat := 1 end end in 0 end" in
  [%expect {|
    Error: let module M1 where
                 abstract def a : Nat :=
                   1
                 end
               end in 0 end has no inferable type
    |}];
  let _ = main_of_body "eval let module L where fact a : Nat := 1 end end in 0 end" in
  [%expect {|
    Error: let module M1 where
                 private abstract def a : Nat :=
                   1
                 end
               end in 0 end has no inferable type
    |}];
  let _ = main_of_body "eval let module L where abstract let a : Nat := 1 end end in 0 end" in
  [%expect {|
    Error: let module M1 where
                 private abstract def a : Nat :=
                   1
                 end
               end in 0 end has no inferable type
    |}]

let%expect_test "a rejected modifier in a local body" =
  let _ = main_of_body "eval let module L where private let a : Nat := 1 end end in 0 end" in
  [%expect {| Error: let is already private |}]

(** Open *)

let%expect_test "open with as and several lists in any order" =
  let _ =
    main_of_body
      "module M where def a : Nat := 1 end def b : Nat := 2 end def c : Nat := 3 end \
       module S where def s : Nat := 4 end end end \
       module N where open M as Z export (a) use (b; S) export (c as d) \
       def t : Nat := succ (succ (succ b)) end def u : Nat := S.s end def v : Nat := Z.c end end \
       eval N.a eval N.d eval N.t eval N.u eval N.v"
  in
  [%expect {|
    Evaluate N.a --> 1 : Nat
    Evaluate N.d --> 3 : Nat
    Evaluate N.t --> 5 : Nat
    Evaluate N.u --> 4 : Nat
    Evaluate N.v --> 3 : Nat
    |}]

let%expect_test "an open as is private" =
  let _ = main_of_body "module M where def a : Nat := 1 end end module N where open M as Z end eval N.Z.a" in
  [%expect {| Error: Test.N.Z is private |}]

let%expect_test "an open use is private" =
  let _ = main_of_body "module M where def a : Nat := 1 end end module N where open M use (a) end eval N.a" in
  [%expect {| Error: Test.N.a is private |}]

let%expect_test "an open of a missing member is rejected" =
  let _ = main_of_body "module M where end open M use (f)" in
  [%expect {| Error: Test.M.f is not a member |}];
  let _ = main_of_body "module M where end open M as Z use (f)" in
  [%expect {| Error: Test.Z.f is not a member |}]

let%expect_test "an open uses and exports one member" =
  let _ = main_of_body "module M where def a : Nat := 1 end end open M use (a) export (a as b)" in
  [%expect {| Error: a is used and exported |}]

let%expect_test "an open names one member twice" =
  let _ = main_of_body "module M where def a : Nat := 1 end end open M use (a) use (a)" in
  [%expect {| Error: a is already declared |}]

let%expect_test "an open declares one name twice" =
  let _ = main_of_body "module M where def a : Nat := 1 end def b : Nat := 2 end end open M use (a; b as a)" in
  [%expect {| Error: a is already declared |}];
  let _ = main_of_body "module M where def a : Nat := 1 end end open M as a use (a)" in
  [%expect {| Error: a is already declared |}]

let%expect_test "an open declares a name already declared" =
  let _ = main_of_body "module M where def a : Nat := 1 end end def a : Nat := 0 end open M use (a)" in
  [%expect {| Error: a is already declared |}]

let%expect_test "an open of a term is rejected" =
  let _ = main_of_body "def a : Nat := 1 end open a use (b)" in
  [%expect {| Error: ill-formed open |}]

let%expect_test "an open of a unit that is not imported is rejected" =
  let _ = main_of_multi_string "module X where open Lib::Num use (double) end" in
  [%expect {| Error: the unit is not imported |}]

let%expect_test "an open of a unit loaded by import" =
  let _ = main_of_multi_string "import Lib::Num module X where open Lib::Num use (double) open Lib::Num.Ops as O eval O.pred (double 2) end" in
  [%expect {| Evaluate O.pred (double 2) --> 3 : Nat |}]

let%expect_test "an open needs a target" =
  let _ = main_of_body "open use (a)" in
  [%expect {|
    Error: on "use" (at line 1, column 24 - line 1, column 27): Expected the
      module to open: a module in scope, a unit, or a module of a unit.
    |}]

let%expect_test "import names a unit" =
  let _ = main_of_body "module M where end import M" in
  [%expect {|
    Error: on "end" (at line 1, column 47 - line 1, column 50): Expected a
      further "::" or "." in the path, the arguments of the module, "as", "use",
      "export", or the next command.
      "import" names a unit, as in "import X::Y"; a module in scope is opened
      with "open".
    |}]

(** Import only loads *)

let%expect_test "an import declares nothing" =
  let _ = main_of_multi_string "import Lib::Num module X where eval double 1 end" in
  [%expect {| Error: unbound name double |}];
  let _ = main_of_multi_string "import Lib::Num module X where eval Lib::Num.double 1 end" in
  [%expect {| Evaluate Lib::Num.double 1 --> 2 : Nat |}]

let%expect_test "a repeated import does nothing" =
  let _ =
    main_of_multi_string
      "import Lib::Num import Lib::Num module X where import Lib::Num module M where import Lib::Num end \
       eval Lib::Num.double 2 end"
  in
  [%expect {| Evaluate Lib::Num.double 2 --> 4 : Nat |}]

let%expect_test "the long form of import is an import and an open" =
  let _ =
    main_of_multi_string
      "module X where import Lib::Num as N use (double) export (Ops) eval N.double 3 eval double 3 eval Ops.pred 3 end"
  in
  [%expect {|
    Evaluate N.double 3 --> 6 : Nat
    Evaluate double 3 --> 6 : Nat
    Evaluate Ops.pred 3 --> 2 : Nat
    |}];
  let _ = main_of_multi_string "module X where import Lib::Num as N use (nope) end" in
  [%expect {| Error: X.N.nope is not a member |}]

let%expect_test "an import is rejected in a local body" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where import Lib::Num end in 0 end end"
  in
  [%expect {| Error: import is not allowed in a local module; use open |}]

(** Leading imports and opens *)

let%expect_test "a leading open in a parameter type" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude::Arith::Equality open Prelude::Arith::Equality use (Eq) \
       module ScratchP (p : Eq 1 1) where def q : Eq 1 1 := p end eval q end"
  in
  [%expect {| Evaluate q $0 --> true : True |}];
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude::Arith::Equality as E use (Eq) \
       module ScratchP (p : Eq 1 1) (q : E.Eq 2 2) where def r : Eq 2 2 := q end eval r end"
  in
  [%expect {| Evaluate r $1 $0 --> true : True |}]

let%expect_test "a leading open sees no parameter" =
  let _ = main_of_multi_string "import Lib::Priv open Lib::Priv.F n as G module X (n : Nat) where end" in
  [%expect {| Error: unbound name n |}]

let%expect_test "a leading open of a unit that is not imported is rejected" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "open Prelude::Arith::Equality use (Eq) module ScratchP (p : Eq 1 1) where end"
  in
  [%expect {| Error: the unit is not imported |}]

let%expect_test "a leading open may not export" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude::Arith::Equality open Prelude::Arith::Equality use (Eq) export (refl) \
       module ScratchP where end"
  in
  [%expect {| Error: export is not allowed before the module header |}];
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude::Arith::Equality as E export (refl) module ScratchP where end"
  in
  [%expect {| Error: export is not allowed before the module header |}];
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude::Arith::Equality module ScratchP where \
       open Prelude::Arith::Equality export (refl) end"
  in
  [%expect {| |}]

let%expect_test "an axiom is a member with no body" =
  let _ =
    main_of_body
      "axiom P (n : Nat) : Type@0 axiom p : P 0 def q : P 0 := p end eval q eval p : P 0 \
       module N where axiom k : Nat eval succ k end"
  in
  [%expect {|
    Evaluate q --> p : P 0
    Evaluate p --> p : P 0
    Evaluate succ N.k --> succ N.k : Nat
    |}]

let%expect_test "an axiom of another unit" =
  let _ =
    main_of_multi_string
      "import Lib::Axioms module X where def d : Nat := succ Lib::Axioms.c end eval d \
       eval fun (x : Lib::Axioms.Inner.P 0) -> x end"
  in
  [%expect {|
    Evaluate d --> succ Lib::Axioms.c : Nat
    Evaluate fun (x1 : Lib::Axioms.Inner.P 0) -> x1
      --> fun (x1 : Lib::Axioms.Inner.P 0) -> x1
      : forall (x1 : Lib::Axioms.Inner.P 0) -> Lib::Axioms.Inner.P 0
    |}]

let%expect_test "an axiom of False makes False inhabited" =
  let _ = main_of_body "axiom bad : False def oops : False := bad end eval oops" in
  [%expect {| Evaluate oops --> bad : False |}]

let%expect_test "an axiom takes no modifiers" =
  let _ = main_of_body "private axiom x : Nat" in
  [%expect {| Error: axiom takes no modifiers |}];
  let _ = main_of_body "abstract axiom x : Nat" in
  [%expect {| Error: axiom takes no modifiers |}];
  let _ = main_of_body "private abstract axiom x : Nat" in
  [%expect {| Error: axiom takes no modifiers |}]

let%expect_test "an axiom is rejected in a local body" =
  let _ = main_of_body "eval let module L where axiom x : Nat end in 0 end" in
  [%expect {| Error: axioms are not allowed in a local module |}]

let%expect_test "an axiom is rejected before the module header" =
  let _ = main_of_program_string "axiom x : Nat module T where end" in
  [%expect {|
    Error: on "axiom" (at line 1, column 1 - line 1, column 6): This token is
      invalid for the beginning of a program.
    |}]

let%expect_test "the type of an axiom is a type" =
  let _ = main_of_body "axiom x : 0" in
  [%expect {| Error: the type of axiom x is not a type |}];
  let _ = main_of_body "axiom x : Nat axiom x : Nat" in
  [%expect {| Error: x is already declared |}]

let%expect_test "lib/Tutorial.mctt" =
  let _ = main_of_lib "Tutorial.mctt" in
  [%expect {|
    Evaluate 3 --> 3 : Nat
    Evaluate 3 --> 3 : Nat
    Evaluate Nat --> Nat : Type@0
    Evaluate Type@0 --> Type@0 : Type@1
    Evaluate (fun (A1 : Type@0)
                  (x1 : A1)
               -> x1) Nat 4 --> 4 : Nat
    Evaluate fun (A1 : Type@0)
                 (x1 : A1)
               -> x1 --> fun (A1 : Type@0)
                             (x1 : A1)
                           -> x1 : forall (A1 : Type@0)
                                          (x1 : A1)
                                     -> A1
    Evaluate rec 3 return x1 . Nat
             | zero => 0
             | succ x2, x3 => succ (succ x3)
             end --> 6 : Nat
    Evaluate rec 2 return x1 . Type@0
             | zero => Nat
             | succ x2, A1 => forall (x3 : Nat) -> A1
             end --> forall (x1 : Nat)
                            (x2 : Nat)
                       -> Nat : Type@0
    Evaluate true --> true : True
    Evaluate fun (x1 : False) -> exfalso x1 return x2 . Nat
      --> fun (x1 : False) -> exfalso x1 return x2 . Nat
      : forall (x1 : False) -> Nat
    Evaluate let x1 : Nat := 2;
                 x2 := fun (x3 : Nat) -> succ x3;
                 x4 : Eq (x2 x1) 3 := true
             in x2 (x2 x1)
             end --> 4 : Nat
    Evaluate double 3 --> 6 : Nat
    Evaluate double four
      --> rec four return x1 . Nat
          | zero => 0
          | succ x2, x3 => succ (succ x3)
          end : Nat
    Evaluate succ helper --> 2 : Nat
    Evaluate double two --> 4 : Nat
    Evaluate double (succ k)
      --> succ
            (succ
              (rec k return x1 . Nat
               | zero => 0
               | succ x2, x3 => succ (succ x3)
               end)) : Nat
    Evaluate Outer.Inner.next --> 11 : Nat
    Evaluate Twice.twice Nat double 1 --> 4 : Nat
    Evaluate (Twice Nat double).twice 1 --> 4 : Nat
    Evaluate Quadruple.twice 1 --> 4 : Nat
    Evaluate Shapes.Square.side --> 2 : Nat
    Evaluate Vault.reveal --> 8 : Nat
    Evaluate Vault.Inside.peek --> 7 : Nat
    Evaluate Prelude::Arith::Plus.plus 2 3 --> 5 : Nat
    Evaluate Adding.five --> 5 : Nat
    Evaluate Adding.Algebra.plusComm 1 2 --> true : True
    Evaluate Counting.seven --> 7 : Nat
    Evaluate let module M1 (x1 : Nat) where
                   private def twice : forall (x2 : Nat) -> Nat :=
                     (Twice Nat double).twice
                   end
                   private def base : Nat :=
                     twice x1
                   end
                   def sum : Nat :=
                     succ base
                   end
                 end;
                 module M2 := M1 1
             in M2.sum
             end --> 5 : Nat
    Evaluate let module M1 where
                   private def add : forall (x1 : Nat) -> Nat :=
                     (Adder 5).add
                   end
                   def addIter : forall (x2 : Nat)
                                   -> Eq (Adder.add 5 x2)
                                        (Iter.iter Nat
                                           (fun (x3 : Nat) -> succ x3)
                                           x2
                                          5) :=
                     (Adder 5).addIter
                   end
                   def eight : Nat :=
                     add 3
                   end
                 end
             in M1.addIter M1.eight
             end --> true : True
    |}]

(** The documentation generator ([Doc]) *)

let doc_lib = lazy (Doc.load "../lib")

let%expect_test "mctt-doc: every name of lib lines up, and every use resolves" =
  List.iter print_endline (Doc.problems (Lazy.force doc_lib));
  [%expect {||}]

let%expect_test "mctt-doc: every name of examples lines up" =
  List.iter print_endline (Doc.problems ~resolve:false (Doc.load ~check:false "../examples"));
  List.iter print_endline (Doc.problems ~resolve:false (Doc.load ~check:false "../examples/multi"));
  [%expect {||}]

let%expect_test "mctt-doc: the units the checker rejects are reported" =
  List.iter print_endline (Doc.problems (Doc.load "../examples/multi"));
  [%expect {|
    BadDep: not checked
    Cyc::A: not checked
    Cyc::B: not checked
    Cycle: not checked
    Lib::Bad: not checked
    Misnamed: not checked
    Missing: not checked
    Transitive: not checked
    |}]

(* The output boxes of a page, unescaped, in order. *)
let doc_find sub s i =
  let n = String.length sub in
  let rec go i = if i + n > String.length s then None
    else if String.sub s i n = sub then Some i else go (i + 1) in
  go i

let doc_boxes page =
  let opening = "<pre class=\"out\" onclick=\"this.parentElement.open=false\">" in
  let unesc s =
    let b = Buffer.create (String.length s) in
    let rec go i =
      if i < String.length s then
        match List.find_opt (fun (e, _) -> doc_find e s i = Some i)
                [ ("&lt;", '<'); ("&gt;", '>'); ("&quot;", '"'); ("&amp;", '&') ] with
        | Some (e, c) -> Buffer.add_char b c; go (i + String.length e)
        | None -> Buffer.add_char b s.[i]; go (i + 1) in
    go 0; Buffer.contents b in
  let rec go i acc =
    match doc_find opening page i with
    | Some k ->
        let a = k + String.length opening in
        let e = Option.get (doc_find "</pre>" page a) in
        go e (unesc (String.sub page a (e - a)) :: acc)
    | None -> List.rev acc
  in
  go 0 []

let doc_count sub s =
  let rec go i n = match doc_find sub s i with Some k -> go (k + 1) (n + 1) | None -> n in
  go 0 0

let%expect_test "mctt-doc: every eval of lib has one output box, with mctt's output" =
  let lib = Lazy.force doc_lib in
  let kinds = Doc.anchor_kinds lib in
  let evals = ref 0 and boxes = ref 0 and equal = ref 0 in
  List.iter (fun u ->
      let page = Doc.render_unit lib kinds u in
      let bs = doc_boxes page in
      let n = Array.fold_left (fun n t -> match t.Doc.t with McttExtracted.Parser.EVAL _ -> n + 1 | _ -> n) 0 u.Doc.u_toks in
      (* A unit with no eval prints nothing; only the others are run. *)
      let out = if n = 0 then "\n" else (ignore (main_of_lib (String.concat "/" u.Doc.u_file ^ ".mctt")); [%expect.output]) in
      let details = doc_count "<details class=\"eval\"" page in
      evals := !evals + n; boxes := !boxes + List.length bs;
      if details <> List.length bs || n <> List.length bs then
        Printf.printf "%s: %d evals, %d boxes, %d details\n" (Doc.unit_name u.Doc.u_path) n (List.length bs) details
      else if String.concat "\n" bs ^ "\n" = out then
        equal := !equal + n
      else Printf.printf "%s: the boxes differ from mctt's output\n" (Doc.unit_name u.Doc.u_path))
    lib.Doc.units;
  Printf.printf "%d evals, %d boxes, %d equal to mctt's output\n" !evals !boxes !equal;
  (* A spot check: the box of [eval Adding.five] in Tutorial. *)
  let tut = List.find (fun u -> u.Doc.u_path = [ "Tutorial" ]) lib.Doc.units in
  List.iter (fun b -> if String.starts_with ~prefix:"Evaluate Adding.five " b then print_endline b)
    (doc_boxes (Doc.render_unit lib kinds tut));
  [%expect {|
    396 evals, 396 boxes, 396 equal to mctt's output
    Evaluate Adding.five --> 5 : Nat
    |}]

let%expect_test "mctt-doc: a unit whose log is out of step with its evals is reported, unboxed" =
  let lib = Lazy.force doc_lib in
  let lib = { lib with Doc.outputs = Hashtbl.copy lib.Doc.outputs } in
  Hashtbl.replace lib.Doc.outputs [ "Tutorial" ] [ "Evaluate x --> 0 : Nat" ];
  List.iter print_endline (Doc.problems lib);
  let tut = List.find (fun u -> u.Doc.u_path = [ "Tutorial" ]) lib.Doc.units in
  Printf.printf "%d boxes\n" (List.length (doc_boxes (Doc.render_unit lib (Doc.anchor_kinds lib) tut)));
  [%expect {|
    Tutorial: 29 evals, 1 outputs
    0 boxes
    |}]

let%expect_test "mctt-doc: links" =
  let lib = Lazy.force doc_lib in
  let show u x ns = List.iter (fun n -> print_endline (x ^ " " ^ Doc.link_of lib u x n)) ns in
  (* The two [pow]s of one line: a monoid's, through the alias
     [Multiplicative], and the one [use]d from Prelude::Arith::Pow. *)
  show [ "Algebra" ] "pow" [ 7; 8 ];
  (* A member of an alias, [Additive.pow], is the functor's [pow]. *)
  show [ "Algebra" ] "Additive" [ 2 ];
  show [ "Algebra" ] "pow" [ 2 ];
  (* A local alias of a module, [P := Multiplicative.Power]. *)
  show [ "Algebra" ] "powPlus" [ 3 ];
  (* A name [use]d inside a module body: its item and a use go to the
     source unit; the alias [P] is declared by the open. *)
  show [ "Tutorial" ] "plus" [ 2; 3 ];
  show [ "Tutorial" ] "add" [ 1; 2 ];
  show [ "Tutorial" ] "P" [ 1; 2 ];
  (* An item of an open in a local body. *)
  show [ "Tutorial" ] "addIter" [ 3 ];
  (* A local binder. *)
  show [ "Tutorial" ] "x" [ 1; 2 ];
  [%expect {|
    pow line 35: Prelude::Algebra::Monoid#pow
    pow line 35: Prelude::Arith::Pow#pow
    Additive line 19: Prelude::Algebra::Instances#Additive
    pow line 19: Prelude::Algebra::Monoid#pow
    powPlus line 72: Prelude::Algebra::Monoid#Power.powPlus
    plus line 197: Prelude::Arith::Plus#plus
    plus line 198: Prelude::Arith::Plus#plus
    add line 197: declares #Adding.add
    add line 198: Prelude::Arith::Plus#plus
    P line 197: declares #Adding.P
    P line 198: Tutorial#Adding.P
    addIter line 269: Tutorial#Adder.addIter
    x line 34: declares #l11
    x line 34: Tutorial#l11
    |}]
