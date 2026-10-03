(* Unit test cases for parsing *)

open Main
open McttExtracted.Entrypoint

(** Helper definitions *)

let main_of_example s = main_of_filename ("../examples/" ^ s)

(* The programs under [examples/multi] import units of their own, looked up
   from there. *)
let main_of_multi s =
  main_of_filename ~search_root:"../examples/multi" ("../examples/multi/" ^ s)

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
    Evaluate Prelude::Arith::Plus.Algebra.plusComm 2 3 --> true : True
    Evaluate Prelude::Arith::Equality.sym 4 4 (Prelude::Arith::Equality.refl 4)
      --> true : True
    Evaluate Prelude::Arith::Equality.zeroNeSucc 5
      --> fun (x1 : False) -> Prelude::Arith::Equality.zeroNeSucc 5 x1
      : forall (x1 : False) -> False
    Evaluate iterSucc 3 4 --> true : True
    Evaluate Prelude::Function::Iter.iter Nat
               (fun (x1 : Nat) -> Prelude::Arith::Plus.plus x1 x1)
               3
               1 --> 8 : Nat
    Evaluate let module M1 :=
                   Prelude::Function::Iter Nat
                     (fun (x1 : Nat) -> Prelude::Arith::Plus.plus x1 x1);
                 x2 : Nat := 2;
                 x3 : Prelude::Arith::Equality.Eq (M1.iter x2 1) 4 := true
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

let%expect_test "ModuleForms.mctt works" =
  let _ = main_of_example "ModuleForms.mctt" in
  [%expect {|
    Evaluate NatIter.twice (fun (x1 : Nat) -> succ x1) 0 --> 2 : Nat
    Evaluate Num.Ops.add 2 3 --> 5 : Nat
    Evaluate Num.Ops.add 1 1 --> 2 : Nat
    Evaluate let module M1 (x1 : Nat) where
                   module Inner where
                     def m : Nat :=
                       succ x1
                     end
                   end
                   import Inner use (m)
                   def doubled : Nat :=
                     Num.Ops.add Inner.m Inner.m
                   end
                 end
             in M1.doubled 2
             end --> 6 : Nat
    |}]

let%expect_test "ImportUse.mctt works" =
  let _ = main_of_example "ImportUse.mctt" in
  [%expect {| Evaluate sum Impl.exposed Impl.exposed --> 8 : Nat |}]

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

let%expect_test "lib/Arithmetic.mctt" =
  let _ = main_of_lib "Arithmetic.mctt" in
  [%expect {|
    Evaluate Prelude::Arith::Mult.mult 6 7 --> 42 : Nat
    Evaluate Prelude::Arith::Plus.plus (Prelude::Arith::Mult.mult 3 4)
               (Prelude::Arith::Mult.mult 2 5) --> 22 : Nat
    Evaluate Prelude::Arith::Plus.Algebra.plusAssoc 1 2 3 --> true : True
    Evaluate Prelude::Arith::Mult.Algebra.multComm 3 4 --> true : True
    Evaluate Prelude::Arith::Mult.Algebra.multAssoc 2 3 4 --> true : True
    Evaluate Prelude::Arith::Mult.Algebra.multDistribLeft 2 3 4 --> true : True
    Evaluate Prelude::Arith::Mult.Algebra.multDistribRight 2 3 4 --> true : True
    Evaluate Prelude::Arith::Equality.cong
               (fun (x1 : Nat) -> Prelude::Arith::Mult.mult x1 x1)
               3
               3
               (Prelude::Arith::Equality.refl 3) --> true : True
    Evaluate Prelude::Arith::Plus.Cancel.plusCancelLeft 2 3 3 true --> true
      : True
    Evaluate Prelude::Arith::Plus.Cancel.plusCancelRight 4 4 1 true --> true
      : True
    Evaluate Prelude::Arith::Plus.Cancel.plusEqZero 0 0 true --> true : True
    Evaluate Prelude::Arith::Mult.Cancel.multEqZero 2 0 true
               (fun (x1 : False) -> x1) --> true : True
    |}]

let%expect_test "lib/OrderParity.mctt" =
  let _ = main_of_lib "OrderParity.mctt" in
  [%expect {|
    Evaluate Prelude::Arith::Order.LeLaws.leTrans 1 2 5 true true --> true : True
    Evaluate Prelude::Arith::Order.LeLaws.leAntisym 3 3 true true --> true : True
    Evaluate Prelude::Arith::Order.LeLaws.leSucc 4 --> true : True
    Evaluate Prelude::Arith::Order.LeLaws.lePlusRight 2 3 --> true : True
    Evaluate Prelude::Logic.Disj.orElim (Prelude::Arith::Order.Le 5 2)
               (Prelude::Arith::Order.Le 2 5)
               Nat
               (Prelude::Arith::Order.LeLaws.leTotal 5 2)
               (fun (x1 : Prelude::Arith::Order.Le 5 2) -> 0)
               (fun (x2 : Prelude::Arith::Order.Le 2 5) -> 1) --> 1 : Nat
    Evaluate Prelude::Arith::Order.LtLaws.ltIrrefl 3
      --> fun (x1 : False) -> Prelude::Arith::Order.LtLaws.ltIrrefl 3 x1
      : forall (x1 : False) -> False
    Evaluate Prelude::Arith::Order.LtLaws.notLtZero 2
      --> fun (x1 : False) -> Prelude::Arith::Order.LtLaws.notLtZero 2 x1
      : forall (x1 : False) -> False
    Evaluate Prelude::Arith::Order.leb 2 5 --> 1 : Nat
    Evaluate Prelude::Arith::Order.leb 5 2 --> 0 : Nat
    Evaluate Prelude::Arith::Order.LebLaws.lebComplete 2 5 true --> true : True
    Evaluate Prelude::Arith::Order.LebLaws.lebZero 5 2 true --> true : True
    Evaluate Prelude::Arith::Parity.double 7 --> 14 : Nat
    Evaluate Prelude::Arith::Parity.Laws.evenDouble 7 --> true : True
    Evaluate Prelude::Logic.Disj.orElim (Prelude::Arith::Parity.Even 7)
               (Prelude::Arith::Parity.Odd 7)
               Nat
               (Prelude::Arith::Parity.Laws.evenOrOdd 7)
               (fun (x1 : Prelude::Arith::Parity.Even 7) -> 0)
               (fun (x2 : Prelude::Arith::Parity.Odd 7) -> 1) --> 1 : Nat
    Evaluate Prelude::Arith::Parity.Laws.evenSuccOdd 4 true --> true : True
    Evaluate Prelude::Arith::Parity.Laws.evenPlus 4 6 true true --> true : True
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

let%expect_test "lib/Programs.mctt" =
  let _ = main_of_lib "Programs.mctt" in
  [%expect {|
    Evaluate Prelude::Arith::Sub.pred 5 --> 4 : Nat
    Evaluate Prelude::Arith::Sub.sub 10 3 --> 7 : Nat
    Evaluate Prelude::Arith::Sub.sub 3 10 --> 0 : Nat
    Evaluate Prelude::Arith::MinMax.min 4 9 --> 4 : Nat
    Evaluate Prelude::Arith::MinMax.max 4 9 --> 9 : Nat
    Evaluate Prelude::Arith::Ackermann.ack 2 3 --> 9 : Nat
    Evaluate Prelude::Arith::Ackermann.ack 3 3 --> 61 : Nat
    Evaluate Prelude::Arith::Sub.PlusSub.plusSub 6 4 --> true : True
    Evaluate Prelude::Arith::Sub.Laws.subSelf 7 --> true : True
    Evaluate Prelude::Arith::Sub.Laws.subSuccRight 9 4 --> true : True
    Evaluate Prelude::Arith::MinMax.Laws.plusMinMax 3 8 --> true : True
    Evaluate Prelude::Arith::MinMax.Laws.minComm 2 5 --> true : True
    Evaluate Prelude::Arith::MinMax.Laws.maxComm 6 1 --> true : True
    Evaluate Prelude::Arith::Ackermann.Equations.ackZero 4 --> true : True
    Evaluate Prelude::Arith::Ackermann.Rows.ackTwo 5 --> true : True
    Evaluate Prelude::Function::Combinators.IterateLaws.iteratePlus
               (fun (x1 : Nat) -> Prelude::Arith::Plus.plus x1 3)
               2
               3
               1 --> true : True
    Evaluate Prelude::Function::Combinators.IterateLaws.iterateComm
               (fun (x1 : Nat) -> succ (succ x1))
               3
               4
               0 --> true : True
    Evaluate Prelude::Function::Combinators.Generic.compose Nat Nat Nat
               (Prelude::Arith::Sub.sub 20)
               (fun (x1 : Nat) -> Prelude::Arith::MinMax.max x1 5)
               2 --> 15 : Nat
    Evaluate Prelude::Function::Combinators.Generic.const Nat Nat 7 100 --> 7
      : Nat
    Evaluate Prelude::Function::Combinators.Generic.iterate Nat
               (Prelude::Arith::Ackermann.ack 1)
               3
               0 --> 6 : Nat
    |}]

let%expect_test "lib/Induction.mctt" =
  let _ = main_of_lib "Induction.mctt" in
  [%expect {|
    Evaluate Halving.half 7 --> 3 : Nat
    Evaluate Halving.half 20 --> 10 : Nat
    Evaluate Halving.halfTwo 7 --> 3 : Nat
    Evaluate Halving.halfTwo 20 --> 10 : Nat
    Evaluate Prelude::Arith::Induction.twoStepInd
               (fun (x1 : Nat)
                 -> Prelude::Arith::Parity.Even
                      (Prelude::Arith::Parity.double x1))
               true
               true
               (fun (x2 : Nat)
                    (x3 : Prelude::Arith::Parity.Even
                            (Prelude::Arith::Parity.double x2))
                 -> x3)
               5 --> true : True
    Evaluate Prelude::Arith::Induction.caseNat (fun (x1 : Nat) -> Nat) 0
               (fun (x2 : Nat) -> x2)
               9 --> 8 : Nat
    Evaluate Prelude::Logic.Disj.orElim (Prelude::Arith::Equality.Eq 3 3)
               (Prelude::Logic.Not (Prelude::Arith::Equality.Eq 3 3))
               Nat
               (Prelude::Arith::Decide.Deciders.decEq 3 3)
               (fun (x1 : Prelude::Arith::Equality.Eq 3 3) -> 1)
               (fun (x2 : Prelude::Logic.Not (Prelude::Arith::Equality.Eq 3 3))
                 -> 0) --> 1 : Nat
    Evaluate Prelude::Logic.Disj.orElim (Prelude::Arith::Equality.Eq 3 4)
               (Prelude::Logic.Not (Prelude::Arith::Equality.Eq 3 4))
               Nat
               (Prelude::Arith::Decide.Deciders.decEq 3 4)
               (fun (x1 : Prelude::Arith::Equality.Eq 3 4) -> 1)
               (fun (x2 : Prelude::Logic.Not (Prelude::Arith::Equality.Eq 3 4))
                 -> 0) --> 0 : Nat
    Evaluate Prelude::Logic.Disj.orElim (Prelude::Arith::Order.Le 2 5)
               (Prelude::Logic.Not (Prelude::Arith::Order.Le 2 5))
               Nat
               (Prelude::Arith::Decide.Deciders.decLe 2 5)
               (fun (x1 : Prelude::Arith::Order.Le 2 5) -> 1)
               (fun (x2 : Prelude::Logic.Not (Prelude::Arith::Order.Le 2 5))
                 -> 0) --> 1 : Nat
    Evaluate Prelude::Logic.Disj.orElim (Prelude::Arith::Order.Lt 5 5)
               (Prelude::Logic.Not (Prelude::Arith::Order.Lt 5 5))
               Nat
               (Prelude::Arith::Decide.Deciders.decLt 5 5)
               (fun (x1 : Prelude::Arith::Order.Lt 5 5) -> 1)
               (fun (x2 : Prelude::Logic.Not (Prelude::Arith::Order.Lt 5 5))
                 -> 0) --> 0 : Nat
    Evaluate Prelude::Logic.Decidable.decStable (Prelude::Arith::Equality.Eq 4 4)
               (Prelude::Arith::Decide.Deciders.decEq 4 4)
               (fun (x1 : Prelude::Logic.Not (Prelude::Arith::Equality.Eq 4 4))
                 -> x1 true) --> true : True
    Evaluate Prelude::Arith::Decide.eqb 6 6 --> 1 : Nat
    Evaluate Prelude::Arith::Decide.eqb 6 2 --> 0 : Nat
    Evaluate Prelude::Logic.Equiv.iffFwd
               (Prelude::Arith::Equality.Eq (Prelude::Arith::Decide.eqb 5 5) 1)
               (Prelude::Arith::Equality.Eq 5 5)
               (Prelude::Arith::Decide.EqbLaws.eqbSpec 5 5)
               true --> true : True
    Evaluate Prelude::Logic.Equiv.iffBwd
               (Prelude::Arith::Equality.Eq (Prelude::Arith::Decide.eqb 5 5) 1)
               (Prelude::Arith::Equality.Eq 5 5)
               (Prelude::Arith::Decide.EqbLaws.eqbSpec 5 5)
               true --> true : True
    Evaluate Prelude::Arith::Decide.EqbLaws.eqbZero 2 3 true
      --> fun (x1 : False) -> Prelude::Arith::Decide.EqbLaws.eqbZero 2 3 true x1
      : forall (x1 : False) -> False
    Evaluate Prelude::Logic.Exist.existsElim
               (fun (x1 : Nat)
                 -> Prelude::Arith::Equality.Eq (Prelude::Arith::Plus.plus x1 x1)
                      6)
               Nat
               (Prelude::Logic.Exist.existsIntro
                  (fun (x2 : Nat)
                    -> Prelude::Arith::Equality.Eq
                         (Prelude::Arith::Plus.plus x2 x2)
                         6)
                  3
                 true)
               (fun (x3 : Nat)
                    (x4 : Prelude::Arith::Equality.Eq
                            (Prelude::Arith::Plus.plus x3 x3)
                            6)
                 -> x3) --> 3 : Nat
    |}]

let%expect_test "lib/Lattice.mctt" =
  let _ = main_of_lib "Lattice.mctt" in
  [%expect {|
    Evaluate Prelude::Arith::MinMax.min (Prelude::Arith::MinMax.max 2 7)
               (Prelude::Arith::MinMax.max 5 3) --> 5 : Nat
    Evaluate Prelude::Arith::MinMax.max (Prelude::Arith::MinMax.min 9 4)
               (Prelude::Arith::MinMax.min 6 8) --> 6 : Nat
    Evaluate Prelude::Arith::Plus.plus (Prelude::Arith::Sub.sub 9 4) 4 --> 9
      : Nat
    Evaluate Prelude::Arith::Monotone.Mono.lePlusMono 1 2 3 4 true true --> true
      : True
    Evaluate Prelude::Arith::Monotone.Mono.lePlusCancel 3 2 5 true --> true
      : True
    Evaluate Prelude::Arith::Monotone.Mono.leMultMono 2 3 2 4 true true --> true
      : True
    Evaluate Prelude::Arith::Monotone.Strict.ltTrans 1 2 4 true true --> true
      : True
    Evaluate Prelude::Arith::Monotone.Strict.ltLeTrans 1 3 3 true true --> true
      : True
    Evaluate Prelude::Arith::Monotone.Strict.leLtTrans 2 2 5 true true --> true
      : True
    Evaluate Prelude::Arith::Monotone.Strict.ltSucc 6 --> true : True
    Evaluate Prelude::Arith::Monotone.Strict.ltPlus 4 2 --> true : True
    Evaluate Prelude::Arith::Monotone.SubLaws.subLe 7 3 --> true : True
    Evaluate Prelude::Arith::Monotone.SubLaws.subMonoLeft 4 6 2 true --> true
      : True
    Evaluate Prelude::Arith::Monotone.SubLaws.subMonoRight 8 2 5 true --> true
      : True
    Evaluate Prelude::Arith::Monotone.SubLaws.plusSubCancel 9 4 true --> true
      : True
    Evaluate Prelude::Arith::Monotone.SubLaws.subPlusCancel 9 4 true --> true
      : True
    Evaluate Prelude::Arith::Monotone.SubLaws.subPos 5 2 true --> true : True
    Evaluate Prelude::Arith::Lattice.Algebra.minAssoc 4 2 7 --> true : True
    Evaluate Prelude::Arith::Lattice.Algebra.maxAssoc 4 2 7 --> true : True
    Evaluate Prelude::Arith::Lattice.Algebra.minMaxAbsorb 5 3 --> true : True
    Evaluate Prelude::Arith::Lattice.Algebra.maxMinAbsorb 3 5 --> true : True
    Evaluate Prelude::Arith::Lattice.Algebra.minMaxDistrib 4 2 6 --> true : True
    Evaluate Prelude::Arith::Lattice.Algebra.maxMinDistrib 4 2 6 --> true : True
    Evaluate Prelude::Arith::Lattice.Bounds.minLe 3 8 --> true : True
    Evaluate Prelude::Arith::Lattice.Bounds.leMax 8 3 --> true : True
    Evaluate Prelude::Arith::Lattice.Bounds.leMin 2 4 5 true true --> true : True
    Evaluate Prelude::Arith::Lattice.Bounds.maxLe 3 4 6 true true --> true : True
    Evaluate Prelude::Arith::Lattice.Bounds.minEqLeft 3 5 true --> true : True
    Evaluate Prelude::Arith::Lattice.Bounds.maxEqRight 3 5 true --> true : True
    Evaluate Prelude::Arith::Lattice.Mono.minMono 2 3 4 6 true true --> true
      : True
    Evaluate Prelude::Arith::Lattice.Mono.maxMono 2 3 6 7 true true --> true
      : True
    |}]

let%expect_test "lib/Division.mctt" =
  let _ = main_of_lib "Division.mctt" in
  [%expect {|
    Evaluate Prelude::Arith::Div.div 17 5 --> 3 : Nat
    Evaluate Prelude::Arith::Div.mod 17 5 --> 2 : Nat
    Evaluate Prelude::Arith::Div.div 17 0 --> 0 : Nat
    Evaluate Prelude::Arith::Div.mod 17 0 --> 17 : Nat
    Evaluate Prelude::Arith::Div.div 20 4 --> 5 : Nat
    Evaluate Prelude::Arith::Div.mod 20 4 --> 0 : Nat
    Evaluate Prelude::Arith::Div.divSucc 17 3 --> 4 : Nat
    Evaluate Prelude::Arith::Div.modSucc 17 3 --> 1 : Nat
    Evaluate Prelude::Arith::Div.Zero.divZeroDivisor 17 --> true : True
    Evaluate Prelude::Arith::Div.Zero.modZeroDivisor 17 --> true : True
    Evaluate Prelude::Arith::Div.Zero.divZero 4 --> true : True
    Evaluate Prelude::Arith::Div.Zero.modZero 0 --> true : True
    Evaluate Prelude::Arith::Div.Bounds.divModSpec 17 4 --> true : True
    Evaluate Prelude::Arith::Div.Bounds.modLt 17 4 --> true : True
    Evaluate Prelude::Arith::Div.Bounds.modSmall 3 4 true --> true : True
    Evaluate Prelude::Arith::Div.Bounds.divSmall 3 4 true --> true : True
    Evaluate Prelude::Arith::Div.Periodic.modSelf 6 --> true : True
    Evaluate Prelude::Arith::Div.Periodic.modPlusDivisor 9 4 --> true : True
    Evaluate Prelude::Arith::Div.One.modOne 7 --> true : True
    Evaluate Prelude::Arith::Div.One.divOne 7 --> true : True
    Evaluate Prelude::Arith::Divides.Divides 3 12 --> True : Type@0
    Evaluate Prelude::Arith::Divides.Divides 3 13 --> False : Type@0
    Evaluate Prelude::Arith::Divides.Divides 0 0 --> True : Type@0
    Evaluate Prelude::Arith::Divides.Divides 0 5 --> False : Type@0
    Evaluate Prelude::Arith::Divides.Basic.zeroDivides 0 true --> true : True
    Evaluate Prelude::Arith::Divides.Basic.dividesRefl 5 --> true : True
    Evaluate Prelude::Arith::Divides.Basic.dividesZero 4 --> true : True
    Evaluate Prelude::Arith::Divides.Basic.oneDivides 9 --> true : True
    Evaluate Prelude::Arith::Divides.Closure.dividesPlus 3 6 9 true true --> true
      : True
    Evaluate Prelude::Arith::Divides.Closure.dividesMult 3 4 --> true : True
    Evaluate Prelude::Arith::Divides.Two.evenDividesTwo 8 true --> true : True
    Evaluate Prelude::Arith::Divides.Two.dividesTwoEven 10 true --> true : True
    |}]

let%expect_test "lib/Vectors.mctt" =
  let _ = main_of_lib "Vectors.mctt" in
  [%expect {|
    Evaluate Prelude::Data::Vec::Properties.sumVec 3 oneTwoThree --> 6 : Nat
    Evaluate NV.head 2 oneTwoThree --> 1 : Nat
    Evaluate NV.nth 3 oneTwoThree 2 true --> 3 : Nat
    Evaluate Prelude::Data::Vec::Properties.sumVec 2 (NV.tail 2 oneTwoThree)
      --> 5 : Nat
    Evaluate Prelude::Data::Vec::Properties.sumVec 3
               (NV.map Nat square 3 oneTwoThree) --> 14 : Nat
    Evaluate NV.nth 5 (NV.append 3 2 oneTwoThree fourFive) 3 true --> 4 : Nat
    Evaluate Prelude::Data::Vec::Properties.sumVec 5
               (NV.append 3 2 oneTwoThree fourFive) --> 15 : Nat
    Evaluate Prelude::Data::Vec::Properties.sumVec 4 (NV.replicate 4 6) --> 24
      : Nat
    Evaluate NV.foldr Nat (fun (x1 : Nat)
                               (x2 : Nat)
                            -> succ x2) 0 5
               (NV.append 3 2 oneTwoThree fourFive) --> 5 : Nat
    Evaluate Prelude::Data::Vec::Properties.Sums.sumReplicate 4 6 --> true : True
    Evaluate Prelude::Data::Vec::Properties.Sums.sumAppend 3 2 oneTwoThree
               fourFive --> true : True
    Evaluate Prelude::Data::Vec::Properties.Nth.nthMap Nat square 3 oneTwoThree 1
               true --> true : True
    Evaluate Prelude::Data::Vec::Properties.Nth.nthReplicate 4 6 3 true --> true
      : True
    Evaluate Prelude::Data::Vec::Properties.Nth.nthAppendLeft 3 2 oneTwoThree
               fourFive
               1
               true
               true --> true : True
    Evaluate Prelude::Data::Vec::Properties.Nth.nthAppendRight 3 2 oneTwoThree
               fourFive
               1
               true --> true : True
    Evaluate NV.nth 4 (NV.tabulate square 4) 3 true --> 9 : Nat
    Evaluate Prelude::Data::Vec::Properties.sumVec 4 (NV.tabulate square 4)
      --> 14 : Nat
    Evaluate Prelude::Data::Vec::Properties.sumVec 2
               (NV.zipWith Nat Nat Prelude::Arith::Mult.mult 2
                  (NV.take 2 1 oneTwoThree)
                 fourFive) --> 14 : Nat
    Evaluate NV.foldl Nat
               (fun (x1 : Nat)
                    (x2 : Nat)
                 -> Prelude::Arith::Plus.plus (Prelude::Arith::Mult.mult 10 x1)
                      x2)
               0
               3
               oneTwoThree --> 123 : Nat
    Evaluate NV.last 4 oneToFive --> 5 : Nat
    Evaluate NV.last 3 (NV.snoc 3 oneTwoThree 7) --> 7 : Nat
    Evaluate Prelude::Data::Vec::Properties.sumVec 4 (NV.init 4 oneToFive) --> 10
      : Nat
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
    Evaluate Prelude::Data::Vec::Properties.Nth.nthTabulate square 4 3 true
      --> true : True
    Evaluate Prelude::Data::Vec::Properties.Nth.nthZipWith Nat Nat
               Prelude::Arith::Mult.mult
               2
               (NV.take 2 1 oneTwoThree)
               fourFive
               1
               true --> true : True
    Evaluate Prelude::Data::Vec::Properties.Nth.nthReverse 5 oneToFive 1 true
               true --> true : True
    Evaluate Prelude::Data::Vec::Properties.Slices.takeAppend 3 2 oneTwoThree
               fourFive
               2
               true --> true : True
    Evaluate Prelude::Data::Vec::Properties.Slices.dropAppend 3 2 oneTwoThree
               fourFive
               1
               true --> true : True
    Evaluate Prelude::Data::Vec::Properties.Slices.appendTakeDrop 3 2 oneToFive 4
               true --> true : True
    Evaluate Prelude::Data::Vec::Properties.Nth.lastSnoc 3 oneTwoThree 7 --> true
      : True
    Evaluate Prelude::Data::Vec::Properties.Sums.sumMapPlus 2 3 oneTwoThree
      --> true : True
    Evaluate Prelude::Data::Vec::Properties.Sums.sumMapScale 3 3 oneTwoThree
      --> true : True
    Evaluate Prelude::Data::Vec::Properties.Sums.sumZipWithPlus 2 fourFive
               (NV.tail 2 oneTwoThree) --> true : True
    Evaluate Prelude::Data::Vec::Properties.Sums.foldlPlus 4 3 oneTwoThree
      --> true : True
    Evaluate Prelude::Data::Vec::Properties.Sums.sumSnoc 3 oneTwoThree 7 --> true
      : True
    Evaluate Prelude::Data::Vec::Properties.Sums.sumInitLast 4 oneToFive --> true
      : True
    Evaluate Prelude::Data::Vec::Properties.Sums.sumReverse 5 oneToFive --> true
      : True
    Evaluate Prelude::Data::Vec::Properties.Sums.sumTabulate square 4 --> true
      : True
    Evaluate Prelude::Data::Vec::Properties.Tests.allbSound Nat
               (fun (x1 : Nat) -> x1)
               5
               oneToFive
               true
               2
               true --> true : True
    Evaluate Prelude::Data::Vec::Properties.Tests.allbComplete Nat
               (fun (x1 : Nat) -> x1)
               4
               (NV.replicate 4 3)
               (fun (x2 : Nat)
                    (x3 : Prelude::Arith::Order.Lt x2 4)
                 -> true) --> true : True
    Evaluate Prelude::Data::Vec::Properties.Tests.anybSound Nat
               (fun (x1 : Nat) -> x1)
               3
               (NV.snoc 2 (NV.replicate 2 0) 9)
               true
               Nat
               (fun (x2 : Nat)
                    (x3 : Prelude::Arith::Order.Lt x2 3)
                    (x4 : Prelude::Arith::Order.Lt 0
                            (NV.snoc 2 (NV.replicate 2 0) 9 x2 x3))
                 -> x2) --> 2 : Nat
    |}]

let%expect_test "lib/Powers.mctt" =
  let _ = main_of_lib "Powers.mctt" in
  [%expect {|
    Evaluate Prelude::Arith::Pow.pow 2 10 --> 1024 : Nat
    Evaluate Prelude::Arith::Pow.pow 3 4 --> 81 : Nat
    Evaluate Prelude::Arith::Pow.pow 0 0 --> 1 : Nat
    Evaluate Prelude::Arith::Sum.sumTo NatFun.id 11 --> 55 : Nat
    Evaluate Prelude::Arith::Sum.sumTo
               (fun (x1 : Nat) -> Prelude::Arith::Mult.mult x1 x1)
               6 --> 55 : Nat
    Evaluate Prelude::Arith::Factorial.fact 5 --> 120 : Nat
    Evaluate Prelude::Arith::Factorial.fact 0 --> 1 : Nat
    Evaluate Prelude::Arith::Pow.Basic.powZero 7 --> true : True
    Evaluate Prelude::Arith::Pow.Basic.powOne 9 --> true : True
    Evaluate Prelude::Arith::Pow.Basic.onePow 6 --> true : True
    Evaluate Prelude::Arith::Pow.Exp.powPlus 2 1 3 --> true : True
    Evaluate Prelude::Arith::Pow.Exp.powMult 2 2 2 --> true : True
    Evaluate Prelude::Arith::Pow.Exp.powMultBase 2 2 2 --> true : True
    Evaluate Prelude::Arith::Sum.Linear.sumToPlus NatFun.id
               (fun (x1 : Nat) -> Prelude::Arith::Mult.mult x1 x1)
               4 --> true : True
    Evaluate Prelude::Arith::Sum.Linear.sumToScale 3 NatFun.id 4 --> true : True
    Evaluate Prelude::Arith::Sum.Linear.sumToConst 4 5 --> true : True
    Evaluate Prelude::Arith::Sum.Closed.gauss 4 --> true : True
    Evaluate Prelude::Arith::Sum.Closed.sumOdd 4 --> true : True
    Evaluate Prelude::Arith::Factorial.Laws.factSucc 3 --> true : True
    Evaluate Prelude::Arith::Factorial.Bounds.factPos 4 --> true : True
    Evaluate Prelude::Arith::Factorial.Bounds.factLeSucc 3 --> true : True
    Evaluate Prelude::Arith::Factorial.Bounds.lePowFact 3 --> true : True
    |}]

let%expect_test "lib/Streams.mctt" =
  let _ = main_of_lib "Streams.mctt" in
  [%expect {|
    Evaluate Prelude::Data::Vec::Properties.sumVec 6
               (S.take 6 Prelude::Data::Stream::Properties.nats) --> 15 : Nat
    Evaluate Prelude::Data::Vec.nth Nat 5 (S.take 5 evens) 4 true --> 8 : Nat
    Evaluate S.nth odds 6 --> 13 : Nat
    Evaluate Prelude::Data::Vec::Properties.sumVec 5 (S.take 5 squares) --> 30
      : Nat
    Evaluate S.nth fibs 10 --> 55 : Nat
    Evaluate S.nth lucas 8 --> 47 : Nat
    Evaluate Prelude::Data::Vec::Properties.sumVec 10 (S.take 10 fibs) --> 88
      : Nat
    Evaluate S.nth (S.scan Nat Prelude::Arith::Plus.plus 0 squares) 5 --> 30
      : Nat
    Evaluate S.nth (S.interleave evens odds) 7 --> 7 : Nat
    Evaluate S.nth (S.drop 4 squares) 3 --> 49 : Nat
    Evaluate S.nth (S.zipWith Nat Nat Prelude::Arith::Plus.plus evens odds) 4
      --> 17 : Nat
    Evaluate S.head (S.tail (S.cons 9 Prelude::Data::Stream::Properties.nats))
      --> 0 : Nat
    Evaluate S.nth (S.const 3) 100 --> 3 : Nat
    Evaluate Prelude::Data::Stream::Properties.Elements.headCons 9
               Prelude::Data::Stream::Properties.nats --> true : True
    Evaluate Prelude::Data::Stream::Properties.Elements.tailCons 9 squares 3
      --> true : True
    Evaluate Prelude::Data::Stream::Properties.Elements.nthConst 3 100 --> true
      : True
    Evaluate Prelude::Data::Stream::Properties.Elements.nthMap square
               Prelude::Data::Stream::Properties.nats
               4 --> true : True
    Evaluate Prelude::Data::Stream::Properties.Elements.nthZipWith
               Prelude::Arith::Plus.plus
               evens
               odds
               3 --> true : True
    Evaluate Prelude::Data::Stream::Properties.Elements.nthIterate
               (fun (x1 : Nat) -> succ (succ x1))
               1
               4 --> true : True
    Evaluate Prelude::Data::Stream::Properties.Elements.tailIterate
               (fun (x1 : Nat) -> succ (succ x1))
               1
               4 --> true : True
    Evaluate Prelude::Data::Stream::Properties.Nats.nthNats 12 --> true : True
    Evaluate Prelude::Data::Stream::Properties.Slices.nthDrop 3 squares 1
      --> true : True
    Evaluate Prelude::Data::Stream::Properties.Slices.nthTake 5 squares 3 true
      --> true : True
    Evaluate Prelude::Data::Stream::Properties.Slices.scanSum squares 4 --> true
      : True
    Evaluate Prelude::Data::Stream::Properties.Slices.scanSum fibs 6 --> true
      : True
    Evaluate Prelude::Data::Stream::Properties.Slices.nthInterleaveEven 3 evens
               odds --> true : True
    Evaluate Prelude::Data::Stream::Properties.Slices.nthInterleaveOdd 3 evens
               odds --> true : True
    Evaluate Prelude::Arith::Sum.Basic.sumToShift squares 3 --> true : True
    Evaluate Prelude::Data::Stream::Properties.Slices.sumTake 5
               Prelude::Data::Stream::Properties.nats --> true : True
    |}]

let%expect_test "lib/Combinatorics.mctt" =
  let _ = main_of_lib "Combinatorics.mctt" in
  [%expect {|
    Evaluate Prelude::Arith::Binomial.choose 0 0 --> 1 : Nat
    Evaluate Prelude::Arith::Binomial.choose 1 0 --> 1 : Nat
    Evaluate Prelude::Arith::Binomial.choose 1 1 --> 1 : Nat
    Evaluate Prelude::Arith::Binomial.choose 2 0 --> 1 : Nat
    Evaluate Prelude::Arith::Binomial.choose 2 1 --> 2 : Nat
    Evaluate Prelude::Arith::Binomial.choose 2 2 --> 1 : Nat
    Evaluate Prelude::Arith::Binomial.choose 3 0 --> 1 : Nat
    Evaluate Prelude::Arith::Binomial.choose 3 1 --> 3 : Nat
    Evaluate Prelude::Arith::Binomial.choose 3 2 --> 3 : Nat
    Evaluate Prelude::Arith::Binomial.choose 3 3 --> 1 : Nat
    Evaluate Prelude::Arith::Binomial.choose 4 0 --> 1 : Nat
    Evaluate Prelude::Arith::Binomial.choose 4 1 --> 4 : Nat
    Evaluate Prelude::Arith::Binomial.choose 4 2 --> 6 : Nat
    Evaluate Prelude::Arith::Binomial.choose 4 3 --> 4 : Nat
    Evaluate Prelude::Arith::Binomial.choose 4 4 --> 1 : Nat
    Evaluate Prelude::Arith::Binomial.choose 5 0 --> 1 : Nat
    Evaluate Prelude::Arith::Binomial.choose 5 1 --> 5 : Nat
    Evaluate Prelude::Arith::Binomial.choose 5 2 --> 10 : Nat
    Evaluate Prelude::Arith::Binomial.choose 5 3 --> 10 : Nat
    Evaluate Prelude::Arith::Binomial.choose 5 4 --> 5 : Nat
    Evaluate Prelude::Arith::Binomial.choose 5 5 --> 1 : Nat
    Evaluate Prelude::Arith::Binomial.choose 6 0 --> 1 : Nat
    Evaluate Prelude::Arith::Binomial.choose 6 1 --> 6 : Nat
    Evaluate Prelude::Arith::Binomial.choose 6 2 --> 15 : Nat
    Evaluate Prelude::Arith::Binomial.choose 6 3 --> 20 : Nat
    Evaluate Prelude::Arith::Binomial.choose 6 4 --> 15 : Nat
    Evaluate Prelude::Arith::Binomial.choose 6 5 --> 6 : Nat
    Evaluate Prelude::Arith::Binomial.choose 6 6 --> 1 : Nat
    Evaluate Prelude::Arith::Binomial.choose 3 5 --> 0 : Nat
    Evaluate Prelude::Arith::Sum.sumTo (Prelude::Arith::Binomial.choose 6) 7
      --> 64 : Nat
    Evaluate Prelude::Arith::Fibonacci.fib 0 --> 0 : Nat
    Evaluate Prelude::Arith::Fibonacci.fib 1 --> 1 : Nat
    Evaluate Prelude::Arith::Fibonacci.fib 10 --> 55 : Nat
    Evaluate Prelude::Arith::Sum.sumTo Prelude::Arith::Fibonacci.fib 10 --> 88
      : Nat
    Evaluate Prelude::Arith::Binomial::Properties.Basic.chooseZero 5 --> true
      : True
    Evaluate Prelude::Arith::Binomial::Properties.Basic.chooseSelf 5 --> true
      : True
    Evaluate Prelude::Arith::Binomial::Properties.Basic.chooseOne 5 --> true
      : True
    Evaluate Prelude::Arith::Binomial::Properties.Basic.chooseOver 3 5 true
      --> true : True
    Evaluate Prelude::Arith::Binomial::Properties.Basic.pascal 4 2 --> true
      : True
    Evaluate Prelude::Arith::Binomial::Properties.Symmetry.chooseSymm 2 3
      --> true : True
    Evaluate Prelude::Arith::Binomial::Properties.Symmetry.chooseSymmSub 5 2 true
      --> true : True
    Evaluate Prelude::Arith::Binomial::Properties.Row.rowSum 4 --> true : True
    Evaluate Prelude::Arith::Fibonacci::Properties.Basic.fibSucc 5 --> true
      : True
    Evaluate Prelude::Arith::Fibonacci::Properties.Growth.fibPos 5 --> true
      : True
    Evaluate Prelude::Arith::Fibonacci::Properties.Growth.fibMono 5 --> true
      : True
    Evaluate Prelude::Arith::Fibonacci::Properties.Growth.fibMonoPlus 2 4
      --> true : True
    Evaluate Prelude::Arith::Fibonacci::Properties.Identities.fibSum 5 --> true
      : True
    Evaluate Prelude::Arith::Fibonacci::Properties.Identities.fibPlus 3 2
      --> true : True
    |}]

let%expect_test "lib/NumberTheory.mctt" =
  let _ = main_of_lib "NumberTheory.mctt" in
  [%expect {|
    Evaluate Prelude::Arith::Gcd.gcd 12 18 --> 6 : Nat
    Evaluate Prelude::Arith::Gcd.gcd 17 5 --> 1 : Nat
    Evaluate Prelude::Arith::Gcd.gcd 0 9 --> 9 : Nat
    Evaluate Prelude::Arith::Gcd.gcd 9 0 --> 9 : Nat
    Evaluate Primes.nthPrime 0 --> 2 : Nat
    Evaluate Primes.nthPrime 1 --> 3 : Nat
    Evaluate Primes.nthPrime 2 --> 5 : Nat
    Evaluate Primes.nthPrime 3 --> 7 : Nat
    Evaluate Primes.nthPrime 4 --> 11 : Nat
    Evaluate Primes.nthPrime 5 --> 13 : Nat
    Evaluate Primes.nthPrime 6 --> 17 : Nat
    Evaluate Primes.nthPrime 7 --> 19 : Nat
    Evaluate Primes.nthPrime 8 --> 23 : Nat
    Evaluate Primes.nthPrime 9 --> 29 : Nat
    Evaluate Primes.nthPrime 10 --> 31 : Nat
    Evaluate Prelude::Arith::Sum.sumTo Prelude::Arith::Prime.isPrime 30 --> 10
      : Nat
    Evaluate Prelude::Arith::Sum.sumTo
               (fun (x1 : Nat)
                 -> Prelude::Arith::Mult.mult x1
                      (Prelude::Arith::Prime.isPrime x1))
               30 --> 129 : Nat
    Evaluate Prelude::Arith::Prime.smallestDivisor 91 --> 7 : Nat
    Evaluate Prelude::Arith::Prime.smallestDivisor 29 --> 29 : Nat
    Evaluate Prelude::Arith::Prime.Prime 29 --> True : Type@0
    Evaluate Prelude::Arith::Prime.Prime 27 --> False : Type@0
    Evaluate Prelude::Arith::Gcd::Properties.Values.gcdZeroLeft 5 --> true : True
    Evaluate Prelude::Arith::Gcd::Properties.Values.gcdZeroRight 5 --> true
      : True
    Evaluate Prelude::Arith::Gcd::Properties.Values.gcdSelf 7 --> true : True
    Evaluate Prelude::Arith::Gcd::Properties.Values.gcdOneRight 9 --> true : True
    Evaluate Prelude::Arith::Gcd::Properties.Divisor.gcdDividesLeft 6 9 --> true
      : True
    Evaluate Prelude::Arith::Gcd::Properties.Divisor.gcdDividesRight 6 9 --> true
      : True
    Evaluate Prelude::Arith::Gcd::Properties.Divisor.gcdGreatest 2 8 12 true true
      --> true : True
    Evaluate Prelude::Arith::Gcd::Properties.Values.gcdComm 6 9 --> true : True
    Evaluate Prelude::Arith::Divides.Closure.dividesMultLeft 3 6 2 true --> true
      : True
    Evaluate Prelude::Arith::Divides.Closure.dividesPlusCancel 3 6 9 true true
      --> true : True
    Evaluate Prelude::Arith::Prime.Facts.twoPrime --> true : True
    Evaluate Prelude::Arith::Prime.Facts.sevenPrime --> true : True
    Evaluate Prelude::Arith::Prime.Facts.nineNotPrime
      --> fun (x1 : False) -> Prelude::Arith::Prime.Facts.nineNotPrime x1
      : forall (x1 : False) -> False
    Evaluate Prelude::Arith::Prime.Laws.smallestDivisorDivides 15 --> true : True
    Evaluate Prelude::Arith::Prime.Laws.primeGeTwo 13 true --> true : True
    Evaluate Prelude::Arith::Prime.Laws.primeSmallestDivisor 13 true --> true
      : True
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
       import N use (y) def z : Nat := succ y end end in L.z end"
  in
  [%expect {|
    Evaluate let module M1 where
                   module N where
                     def y : Nat :=
                       5
                     end
                   end
                   import N use (y)
                   def z : Nat :=
                     succ N.y
                   end
                 end
             in M1.z
             end --> 6 : Nat
    |}]

let%expect_test "an import of a local module alias" =
  let _ =
    main_of_body
      "module M where def y : Nat := 7 end end module P := M import P as Q eval Q.y"
  in
  [%expect {| Evaluate P.y --> 7 : Nat |}]

(** Module rejections *)

let%expect_test "a private member is not selected from outside" =
  let _ = main_of_body "module M where private def s : Nat := 0 end end eval M.s" in
  [%expect {| Error: M.s has no inferable type |}]

let%expect_test "a private member is not imported by use" =
  let _ = main_of_body "module M where private def s : Nat := 0 end end import M use (s)" in
  [%expect {| Error: ill-formed import |}]

let%expect_test "a module alias of a term is rejected" =
  let _ = main_of_body "module P := Nat" in
  [%expect {| Error: not a module |}]

let%expect_test "an alias of a module is not a term" =
  let _ = main_of_body "module M where end import M as N eval N" in
  [%expect {| Error: a module is not a term |}]

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

let%expect_test "an eval is rejected in a local body" =
  let _ = main_of_body "eval let module X where eval 0 end in 0 end" in
  [%expect {|
    Error: let module M1 where
                 eval 0
               end in 0 end has no inferable type
    |}]

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
  let _ = main_of_body "module M where end import M use (f)" in
  [%expect {| Error: ill-formed import |}]

let%expect_test "a module expression is expected after :=" =
  let _ = main_of_body "module P := where" in
  [%expect {|
    Error: on "where" (at line 1, column 31 - line 1, column 36): Expected a
      module expression after ":=".
    |}]
