(* Unit test cases for parsing *)

open Main
open McttExtracted.Entrypoint

(** Helper definitions *)

let main_of_example s = main_of_filename ("../examples/" ^ s)

(* Every unit needs its top level module declaration, so the small inline cases
   get a throwaway one. *)
let main_of_body body = main_of_program_string ("module Test where " ^ body ^ " end")

(** Real tests *)
(* We never expect parser timeout. 2^500 fuel should be large enough! *)

let%expect_test "Type@0 is of Type@1" =
  let _ = main_of_body "eval Type@0 : Type@1" in
  [%expect {|
    Parsed:
      module Test where
        eval Type@0 : Type@1
      end
    Elaborated:
      (fun (A1 : Type@1) -> A1) Type@0 : Type@1
    Normalized Result:
      Type@0 : Type@1
    |}]

let%expect_test "zero is of Nat" =
  let _ = main_of_body "eval zero : Nat" in
  [%expect {|
    Parsed:
      module Test where
        eval 0 : Nat
      end
    Elaborated:
      (fun (x1 : Nat) -> x1) 0 : Nat
    Normalized Result:
      0 : Nat
    |}]

let%expect_test "zero is not of Type@0" =
  let _ = main_of_body "eval zero : Type@0" in
  [%expect {|
    Parsed:
      module Test where
        eval 0 : Type@0
      end
    Type Checking Failure:
      (fun (A1 : Type@0) -> A1) 0
    is not of
      Type@0
    |}]

let%expect_test "succ zero is of Nat" =
  let _ = main_of_body "eval succ zero : Nat" in
  [%expect {|
    Parsed:
      module Test where
        eval 1 : Nat
      end
    Elaborated:
      (fun (x1 : Nat) -> x1) 1 : Nat
    Normalized Result:
      1 : Nat
    |}]

let%expect_test "succ Type@0 is not of Nat (as it is ill-typed)" =
  let _ = main_of_body "eval succ Type@0 : Nat" in
  [%expect {|
    Parsed:
      module Test where
        eval succ Type@0 : Nat
      end
    Type Checking Failure:
      (fun (x1 : Nat) -> x1) (succ Type@0)
    is not of
      Nat
    |}]

let%expect_test "succ Type@0 has no inferable type" =
  let _ = main_of_body "eval succ Type@0" in
  [%expect {|
    Parsed:
      module Test where
        eval succ Type@0
      end
    Type Inference Failure:
      succ Type@0
    has no inferable type
    |}]

let%expect_test "an unascribed eval infers its type" =
  let _ = main_of_body "eval fun (y : Nat) -> y" in
  [%expect {|
    Parsed:
      module Test where
        eval fun (y : Nat) -> y
      end
    Elaborated:
      fun (x1 : Nat) -> x1 : forall (x1 : Nat) -> Nat
    Normalized Result:
      fun (x1 : Nat) -> x1 : forall (x1 : Nat) -> Nat
    |}]

let%expect_test "several evals are reported in order" =
  let _ = main_of_body "def two : Nat := 2 end eval two eval succ two" in
  [%expect {|
    Parsed:
      module Test where
        def two : Nat :=
          2
        end
        eval two
        eval succ two
      end
    Elaborated:
      (fun (x1 : Nat) -> 2) 2 : Nat
    Normalized Result:
      2 : Nat
    Elaborated:
      (fun (x1 : Nat) -> 3) 2 : Nat
    Normalized Result:
      3 : Nat
    |}]

let%expect_test "an eval does not see a later definition" =
  let _ = main_of_body "eval later def later : Nat := 0 end" in
  [%expect {|
    Elaboration Failure:
      module Test where
        eval later
        def later : Nat :=
          0
        end
      end
    cannot be elaborated
    |}]

let%expect_test "definitions are not allowed outside a module" =
  let _ = main_of_program_string "def x : Nat := 0 end module Test where end" in
  [%expect {|
    Parser Failure:
      on "def" (at line 1, column 1 - line 1, column 4):

      This token is invalid for the beginning of a program.
    |}]

let%expect_test "variable x is ill-scoped" =
  let _ = main_of_body "eval x : Type@0" in
  [%expect {|
    Elaboration Failure:
      module Test where
        eval x : Type@0
      end
    cannot be elaborated
    |}]

let%expect_test "identity function of Nat is of forall (x : Nat) -> Nat" =
  let _ = main_of_body "eval fun (y : Nat) -> y : forall (x : Nat) -> Nat" in
  [%expect {|
    Parsed:
      module Test where
        eval fun (y : Nat) -> y : forall (x : Nat) -> Nat
      end
    Elaborated:
      (fun (x1 : forall (x2 : Nat) -> Nat) -> x1) (fun (x3 : Nat) -> x3)
      : forall (x1 : Nat) -> Nat
    Normalized Result:
      fun (x1 : Nat) -> x1 : forall (x1 : Nat) -> Nat
    |}]

let%expect_test "recursion on a natural number that always returns zero is of \
                 Nat" =
  let _ = main_of_body
    "eval rec 3 return y . Nat | zero => 0 | succ n, r => 0 end : Nat" in
  [%expect {|
    Parsed:
      module Test where
        eval rec 3 return y . Nat | zero => 0 | succ n, r => 0 end : Nat
      end
    Elaborated:
      (fun (x1 : Nat) -> x1)
        (rec 3 return x2 . Nat | zero => 0 | succ x3, x4 => 0 end)
      : Nat
    Normalized Result:
      0 : Nat
    |}]

let%expect_test "simple_nat.mctt works" =
  let _ = main_of_example "simple_nat.mctt" in
  [%expect {|
    Parsed:
      module SimpleNat where
        eval 4 : Nat
      end
    Elaborated:
      (fun (x1 : Nat) -> x1) 4 : Nat
    Normalized Result:
      4 : Nat
    |}]

let%expect_test "simple_rec.mctt works" =
  let _ = main_of_example "simple_rec.mctt" in
  [%expect {|
    Parsed:
      module SimpleRec where
        eval fun (x : Nat)
               -> rec x return y . Nat | zero => 1 | succ n, r => succ r end
          : forall (x : Nat) -> Nat
      end
    Elaborated:
      (fun (x1 : forall (x2 : Nat) -> Nat) -> x1)
        (fun (x3 : Nat)
          -> rec x3 return x4 . Nat | zero => 1 | succ x5, x6 => succ x6 end)
      : forall (x1 : Nat) -> Nat
    Normalized Result:
      fun (x1 : Nat)
        -> rec x1 return x2 . Nat | zero => 1 | succ x3, x4 => succ x4 end
      : forall (x1 : Nat) -> Nat
    |}]

let%expect_test "pair.mctt works" =
  let _ = main_of_example "pair.mctt" in
  [%expect {|
    Parsed:
      module Pair where
        eval (fun (Pair : forall (A : Type@0)
                                 (B : Type@0)
                            -> Type@1)
                  (pair : forall (A : Type@0)
                                 (B : Type@0)
                                 (a : A)
                                 (b : B)
                            -> Pair A B)
                  (fst : forall (A : Type@0)
                                (B : Type@0)
                                (p : Pair A B)
                           -> A)
                  (snd : forall (A : Type@0)
                                (B : Type@0)
                                (p : Pair A B)
                           -> B)
               -> (fun (p : Pair Nat (forall (x : Nat) -> Nat))
                    -> snd Nat (forall (x : Nat) -> Nat) p
                         (fst Nat (forall (x : Nat) -> Nat) p))
                    (pair Nat (forall (x : Nat) -> Nat) 3
                      (fun (x : Nat) -> succ (succ x))))
               (fun (A : Type@0)
                    (B : Type@0)
                 -> forall (C : Type@0)
                           (pair : forall (a : A)
                                          (b : B)
                                     -> C)
                      -> C)
               (fun (A : Type@0)
                    (B : Type@0)
                    (a : A)
                    (b : B)
                    (C : Type@0)
                    (pair : forall (a : A)
                                   (b : B)
                              -> C)
                 -> pair a b)
               (fun (A : Type@0)
                    (B : Type@0)
                    (p : forall (C : Type@0)
                                (pair : forall (a : A)
                                               (b : B)
                                          -> C)
                           -> C)
                 -> p A (fun (a : A)
                             (b : B)
                          -> a))
               (fun (A : Type@0)
                    (B : Type@0)
                    (p : forall (C : Type@0)
                                (pair : forall (a : A)
                                               (b : B)
                                          -> C)
                           -> C)
                 -> p B (fun (a : A)
                             (b : B)
                          -> b)) : Nat
      end
    Elaborated:
      (fun (x1 : Nat) -> x1)
        ((fun (x2 : forall (A1 : Type@0)
                           (A2 : Type@0)
                      -> Type@1)
              (x3 : forall (A3 : Type@0)
                           (A4 : Type@0)
                           (x4 : A3)
                           (x5 : A4)
                      -> x2 A3 A4)
              (x6 : forall (A5 : Type@0)
                           (A6 : Type@0)
                           (x7 : x2 A5 A6)
                      -> A5)
              (x8 : forall (A7 : Type@0)
                           (A8 : Type@0)
                           (x9 : x2 A7 A8)
                      -> A8)
           -> (fun (x10 : x2 Nat (forall (x11 : Nat) -> Nat))
                -> x8 Nat (forall (x12 : Nat) -> Nat) x10
                     (x6 Nat (forall (x13 : Nat) -> Nat) x10))
                (x3 Nat (forall (x14 : Nat) -> Nat) 3
                  (fun (x15 : Nat) -> succ (succ x15))))
           (fun (A9 : Type@0)
                (A10 : Type@0)
             -> forall (A11 : Type@0)
                       (x16 : forall (x17 : A9)
                                     (x18 : A10)
                                -> A11)
                  -> A11)
           (fun (A12 : Type@0)
                (A13 : Type@0)
                (x19 : A12)
                (x20 : A13)
                (A14 : Type@0)
                (x21 : forall (x22 : A12)
                              (x23 : A13)
                         -> A14)
             -> x21 x19 x20)
           (fun (A15 : Type@0)
                (A16 : Type@0)
                (x24 : forall (A17 : Type@0)
                              (x25 : forall (x26 : A15)
                                            (x27 : A16)
                                       -> A17)
                         -> A17)
             -> x24 A15 (fun (x28 : A15)
                             (x29 : A16)
                          -> x28))
          (fun (A18 : Type@0)
               (A19 : Type@0)
               (x30 : forall (A20 : Type@0)
                             (x31 : forall (x32 : A18)
                                           (x33 : A19)
                                      -> A20)
                        -> A20)
            -> x30 A19 (fun (x34 : A18)
                            (x35 : A19)
                         -> x35)))
      : Nat
    Normalized Result:
      5 : Nat
    |}]

let%expect_test "vector.mctt works" =
  let _ = main_of_example "vector.mctt" in
  [%expect {|
    Parsed:
      module Vector where
        eval (fun (Vec : forall (A : Type@0)
                                (n : Nat)
                           -> Type@2)
                  (nil : forall (A : Type@0) -> Vec A 0)
                  (cons : forall (A : Type@0)
                                 (n : Nat)
                                 (head : A)
                                 (tail : Vec A n)
                            -> Vec A (succ n))
                  (vecRec : forall (A : Type@0)
                                   (n : Nat)
                                   (vec : Vec A n)
                                   (C : forall (l : Nat) -> Type@1)
                                   (nil : C 0)
                                   (cons : forall (l : Nat)
                                                  (a : A)
                                                  (r : C l)
                                             -> C (succ l))
                              -> C n)
               -> (fun (totalHead : forall (A : Type@0)
                                           (n : Nat)
                                           (vec : Vec A (succ n))
                                      -> A)
                       (vec : Vec (forall (n : Nat) -> Nat) 3)
                    -> totalHead (forall (n : Nat) -> Nat) 2 vec 4)
                    (fun (A : Type@0)
                         (n : Nat)
                         (vec : Vec A (succ n))
                      -> vecRec A (succ n) vec
                           (fun (l : Nat)
                             -> rec l return r . Type@0
                                | zero => Nat
                                | succ l, r => A
                                end)
                           0
                           (fun (l : Nat)
                                (a : A)
                                (r : rec l return r . Type@0
                                     | zero => Nat
                                     | succ l, r => A
                                     end)
                             -> a))
                    (cons (forall (n : Nat) -> Nat) 2
                       (fun (n : Nat) -> succ (succ (succ n)))
                      (cons (forall (n : Nat) -> Nat) 1 (fun (n : Nat) -> succ n)
                        (cons (forall (n : Nat) -> Nat) 0
                           (fun (n : Nat) -> succ (succ n))
                          (nil (forall (n : Nat) -> Nat))))))
               (fun (A : Type@0)
                    (n : Nat)
                 -> forall (C : forall (l : Nat) -> Type@1)
                           (nil : C 0)
                           (cons : forall (l : Nat)
                                          (a : A)
                                          (r : C l)
                                     -> C (succ l))
                      -> C n)
               (fun (A : Type@0)
                    (C : forall (l : Nat) -> Type@1)
                    (nil : C 0)
                    (cons : forall (l : Nat)
                                   (a : A)
                                   (r : C l)
                              -> C (succ l))
                 -> nil)
               (fun (A : Type@0)
                    (n : Nat)
                    (head : A)
                    (tail : forall (C : forall (l : Nat) -> Type@1)
                                   (nil : C 0)
                                   (cons : forall (l : Nat)
                                                  (a : A)
                                                  (r : C l)
                                             -> C (succ l))
                              -> C n)
                    (C : forall (l : Nat) -> Type@1)
                    (nil : C 0)
                    (cons : forall (l : Nat)
                                   (a : A)
                                   (r : C l)
                              -> C (succ l))
                 -> cons n head (tail C nil cons))
               (fun (A : Type@0)
                    (n : Nat)
                    (vec : forall (C : forall (l : Nat) -> Type@1)
                                  (nil : C 0)
                                  (cons : forall (l : Nat)
                                                 (a : A)
                                                 (r : C l)
                                            -> C (succ l))
                             -> C n)
                    (C : forall (l : Nat) -> Type@1)
                    (nil : C 0)
                    (cons : forall (l : Nat)
                                   (a : A)
                                   (r : C l)
                              -> C (succ l))
                 -> vec C nil cons) : Nat
      end
    Elaborated:
      (fun (x1 : Nat) -> x1)
        ((fun (x2 : forall (A1 : Type@0)
                           (x3 : Nat)
                      -> Type@2)
              (x4 : forall (A2 : Type@0) -> x2 A2 0)
              (x5 : forall (A3 : Type@0)
                           (x6 : Nat)
                           (x7 : A3)
                           (x8 : x2 A3 x6)
                      -> x2 A3 (succ x6))
              (x9 : forall (A4 : Type@0)
                           (x10 : Nat)
                           (x11 : x2 A4 x10)
                           (x12 : forall (x13 : Nat) -> Type@1)
                           (x14 : x12 0)
                           (x15 : forall (x16 : Nat)
                                         (x17 : A4)
                                         (x18 : x12 x16)
                                    -> x12 (succ x16))
                      -> x12 x10)
           -> (fun (x19 : forall (A5 : Type@0)
                                 (x20 : Nat)
                                 (x21 : x2 A5 (succ x20))
                            -> A5)
                   (x22 : x2 (forall (x23 : Nat) -> Nat) 3)
                -> x19 (forall (x24 : Nat) -> Nat) 2 x22 4)
                (fun (A6 : Type@0)
                     (x25 : Nat)
                     (x26 : x2 A6 (succ x25))
                  -> x9 A6 (succ x25) x26
                       (fun (x27 : Nat)
                         -> rec x27 return x28 . Type@0
                            | zero => Nat
                            | succ x29, A7 => A6
                            end)
                       0
                       (fun (x30 : Nat)
                            (x31 : A6)
                            (x32 : rec x30 return x33 . Type@0
                                   | zero => Nat
                                   | succ x34, A8 => A6
                                   end)
                         -> x31))
                (x5 (forall (x35 : Nat) -> Nat) 2
                   (fun (x36 : Nat) -> succ (succ (succ x36)))
                  (x5 (forall (x37 : Nat) -> Nat) 1 (fun (x38 : Nat) -> succ x38)
                    (x5 (forall (x39 : Nat) -> Nat) 0
                       (fun (x40 : Nat) -> succ (succ x40))
                      (x4 (forall (x41 : Nat) -> Nat))))))
           (fun (A9 : Type@0)
                (x42 : Nat)
             -> forall (x43 : forall (x44 : Nat) -> Type@1)
                       (x45 : x43 0)
                       (x46 : forall (x47 : Nat)
                                     (x48 : A9)
                                     (x49 : x43 x47)
                                -> x43 (succ x47))
                  -> x43 x42)
           (fun (A10 : Type@0)
                (x50 : forall (x51 : Nat) -> Type@1)
                (x52 : x50 0)
                (x53 : forall (x54 : Nat)
                              (x55 : A10)
                              (x56 : x50 x54)
                         -> x50 (succ x54))
             -> x52)
           (fun (A11 : Type@0)
                (x57 : Nat)
                (x58 : A11)
                (x59 : forall (x60 : forall (x61 : Nat) -> Type@1)
                              (x62 : x60 0)
                              (x63 : forall (x64 : Nat)
                                            (x65 : A11)
                                            (x66 : x60 x64)
                                       -> x60 (succ x64))
                         -> x60 x57)
                (x67 : forall (x68 : Nat) -> Type@1)
                (x69 : x67 0)
                (x70 : forall (x71 : Nat)
                              (x72 : A11)
                              (x73 : x67 x71)
                         -> x67 (succ x71))
             -> x70 x57 x58 (x59 x67 x69 x70))
          (fun (A12 : Type@0)
               (x74 : Nat)
               (x75 : forall (x76 : forall (x77 : Nat) -> Type@1)
                             (x78 : x76 0)
                             (x79 : forall (x80 : Nat)
                                           (x81 : A12)
                                           (x82 : x76 x80)
                                      -> x76 (succ x80))
                        -> x76 x74)
               (x83 : forall (x84 : Nat) -> Type@1)
               (x85 : x83 0)
               (x86 : forall (x87 : Nat)
                             (x88 : A12)
                             (x89 : x83 x87)
                        -> x83 (succ x87))
            -> x75 x83 x85 x86))
      : Nat
    Normalized Result:
      7 : Nat
    |}]

let%expect_test "nary.mctt works" =
  let _ = main_of_example "nary.mctt" in
  [%expect {|
    Parsed:
      module Nary where
        eval (fun (Nary : forall (n : Nat) -> Type@0)
                  (toNat : forall (f : Nary 0) -> Nat)
                  (appNary : forall (n : Nat)
                                    (f : Nary (succ n))
                                    (arg : Nat)
                               -> Nary n)
                  (n : Nat)
                  (f : Nary n)
               -> (rec n return y . forall (g : Nary y) -> Nat
                   | zero => toNat
                   | succ m, r =>
                     fun (g : Nary (succ m)) -> r (appNary m g (succ m))
                   end)
                    f)
               (fun (n : Nat)
                 -> rec n return y . Type@0
                    | zero => Nat
                    | succ m, r => forall (a : Nat) -> r
                    end)
               (fun (f : Nat) -> f)
               (fun (n : Nat)
                    (f : rec succ n return y . Type@0
                         | zero => Nat
                         | succ m, r => forall (a : Nat) -> r
                         end)
                    (arg : Nat)
                 -> f arg)
               3
               ((fun (add : forall (a : Nat)
                                   (b : Nat)
                              -> Nat)
                     (a : Nat)
                     (b : Nat)
                     (c : Nat)
                  -> add a (add b c))
                 (fun (a : Nat)
                      (b : Nat)
                   -> rec a return y . Nat | zero => b | succ m, r => succ r end))
          : Nat
      end
    Elaborated:
      (fun (x1 : Nat) -> x1)
        ((fun (x2 : forall (x3 : Nat) -> Type@0)
              (x4 : forall (x5 : x2 0) -> Nat)
              (x6 : forall (x7 : Nat)
                           (x8 : x2 (succ x7))
                           (x9 : Nat)
                      -> x2 x7)
              (x10 : Nat)
              (x11 : x2 x10)
           -> (rec x10 return x12 . forall (x15 : x2 x12) -> Nat
               | zero => x4
               | succ x13, x14 =>
                 fun (x16 : x2 (succ x13)) -> x14 (x6 x13 x16 (succ x13))
               end)
                x11)
           (fun (x17 : Nat)
             -> rec x17 return x18 . Type@0
                | zero => Nat
                | succ x19, A1 => forall (x20 : Nat) -> A1
                end)
           (fun (x21 : Nat) -> x21)
           (fun (x22 : Nat)
                (x23 : rec succ x22 return x24 . Type@0
                       | zero => Nat
                       | succ x25, A2 => forall (x26 : Nat) -> A2
                       end)
                (x27 : Nat)
             -> x23 x27)
           3
          ((fun (x28 : forall (x29 : Nat)
                              (x30 : Nat)
                         -> Nat)
                (x31 : Nat)
                (x32 : Nat)
                (x33 : Nat)
             -> x28 x31 (x28 x32 x33))
            (fun (x34 : Nat)
                 (x35 : Nat)
              -> rec x34 return x36 . Nat
                 | zero => x35
                 | succ x37, x38 => succ x38
                 end)))
      : Nat
    Normalized Result:
      6 : Nat
    |}]

let%expect_test "simple_let.mctt works" =
  let _ = main_of_example "simple_let.mctt" in
  [%expect {|
    Parsed:
      module SimpleLet where
        eval (fun (x : Nat) -> succ x) 0 : Nat
      end
    Elaborated:
      (fun (x1 : Nat) -> x1) ((fun (x2 : Nat) -> succ x2) 0) : Nat
    Normalized Result:
      1 : Nat
    |}]

let%expect_test "let_two_vars.mctt works" =
  let _ = main_of_example "let_two_vars.mctt" in
  [%expect {|
    Parsed:
      module LetTwoVars where
        eval (fun (x : Nat)
                  (f : forall (y : Nat) -> Nat)
               -> f x) 0
               (fun (n : Nat) -> n) : Nat
      end
    Elaborated:
      (fun (x1 : Nat) -> x1)
        ((fun (x2 : Nat)
              (x3 : forall (x4 : Nat) -> Nat)
           -> x3 x2) 0
          (fun (x5 : Nat) -> x5))
      : Nat
    Normalized Result:
      0 : Nat
    |}]

let%expect_test "let_nary.mctt works" =
  let _ = main_of_example "let_nary.mctt" in
  [%expect {|
    Parsed:
      module LetNary where
        eval (fun (Nary : forall (n : Nat) -> Type@0)
                  (toNat : forall (f : Nary 0) -> Nat)
                  (appNary : forall (n : Nat)
                                    (f : Nary (succ n))
                                    (arg : Nat)
                               -> Nary n)
                  (n : Nat)
                  (f : Nary n)
               -> (rec n return y . forall (g : Nary y) -> Nat
                   | zero => toNat
                   | succ m, r =>
                     fun (g : Nary (succ m)) -> r (appNary m g (succ m))
                   end)
                    f)
               (fun (n : Nat)
                 -> rec n return y . Type@0
                    | zero => Nat
                    | succ m, r => forall (a : Nat) -> r
                    end)
               (fun (f : Nat) -> f)
               (fun (n : Nat)
                    (f : rec succ n return y . Type@0
                         | zero => Nat
                         | succ m, r => forall (a : Nat) -> r
                         end)
                    (arg : Nat)
                 -> f arg)
               3
               ((fun (add : forall (a : Nat)
                                   (b : Nat)
                              -> Nat)
                     (a : Nat)
                     (b : Nat)
                     (c : Nat)
                  -> add a (add b c))
                 (fun (a : Nat)
                      (b : Nat)
                   -> rec a return y . Nat | zero => b | succ m, r => succ r end))
          : Nat
      end
    Elaborated:
      (fun (x1 : Nat) -> x1)
        ((fun (x2 : forall (x3 : Nat) -> Type@0)
              (x4 : forall (x5 : x2 0) -> Nat)
              (x6 : forall (x7 : Nat)
                           (x8 : x2 (succ x7))
                           (x9 : Nat)
                      -> x2 x7)
              (x10 : Nat)
              (x11 : x2 x10)
           -> (rec x10 return x12 . forall (x15 : x2 x12) -> Nat
               | zero => x4
               | succ x13, x14 =>
                 fun (x16 : x2 (succ x13)) -> x14 (x6 x13 x16 (succ x13))
               end)
                x11)
           (fun (x17 : Nat)
             -> rec x17 return x18 . Type@0
                | zero => Nat
                | succ x19, A1 => forall (x20 : Nat) -> A1
                end)
           (fun (x21 : Nat) -> x21)
           (fun (x22 : Nat)
                (x23 : rec succ x22 return x24 . Type@0
                       | zero => Nat
                       | succ x25, A2 => forall (x26 : Nat) -> A2
                       end)
                (x27 : Nat)
             -> x23 x27)
           3
          ((fun (x28 : forall (x29 : Nat)
                              (x30 : Nat)
                         -> Nat)
                (x31 : Nat)
                (x32 : Nat)
                (x33 : Nat)
             -> x28 x31 (x28 x32 x33))
            (fun (x34 : Nat)
                 (x35 : Nat)
              -> rec x34 return x36 . Nat
                 | zero => x35
                 | succ x37, x38 => succ x38
                 end)))
      : Nat
    Normalized Result:
      6 : Nat
    |}]

let%expect_test "let_vector.mctt works" =
  let _ = main_of_example "let_vector.mctt" in
  [%expect {|
    Parsed:
      module LetVector where
        eval (fun (Vec : forall (A : Type@0)
                                (n : Nat)
                           -> Type@2)
                  (nil : forall (A : Type@0) -> Vec A 0)
                  (cons : forall (A : Type@0)
                                 (n : Nat)
                                 (head : A)
                                 (tail : Vec A n)
                            -> Vec A (succ n))
                  (vecRec : forall (A : Type@0)
                                   (n : Nat)
                                   (vec : Vec A n)
                                   (C : forall (l : Nat) -> Type@1)
                                   (nil : C 0)
                                   (cons : forall (l : Nat)
                                                  (a : A)
                                                  (r : C l)
                                             -> C (succ l))
                              -> C n)
               -> (fun (totalHead : forall (A : Type@0)
                                           (n : Nat)
                                           (vec : Vec A (succ n))
                                      -> A)
                       (vec : Vec (forall (n : Nat) -> Nat) 3)
                    -> totalHead (forall (n : Nat) -> Nat) 2 vec 4)
                    (fun (A : Type@0)
                         (n : Nat)
                         (vec : Vec A (succ n))
                      -> vecRec A (succ n) vec
                           (fun (l : Nat)
                             -> rec l return r . Type@0
                                | zero => Nat
                                | succ l, r => A
                                end)
                           0
                           (fun (l : Nat)
                                (a : A)
                                (r : rec l return r . Type@0
                                     | zero => Nat
                                     | succ l, r => A
                                     end)
                             -> a))
                    (cons (forall (n : Nat) -> Nat) 2
                       (fun (n : Nat) -> succ (succ (succ n)))
                      (cons (forall (n : Nat) -> Nat) 1 (fun (n : Nat) -> succ n)
                        (cons (forall (n : Nat) -> Nat) 0
                           (fun (n : Nat) -> succ (succ n))
                          (nil (forall (n : Nat) -> Nat))))))
               (fun (A : Type@0)
                    (n : Nat)
                 -> forall (C : forall (l : Nat) -> Type@1)
                           (nil : C 0)
                           (cons : forall (l : Nat)
                                          (a : A)
                                          (r : C l)
                                     -> C (succ l))
                      -> C n)
               (fun (A : Type@0)
                    (C : forall (l : Nat) -> Type@1)
                    (nil : C 0)
                    (cons : forall (l : Nat)
                                   (a : A)
                                   (r : C l)
                              -> C (succ l))
                 -> nil)
               (fun (A : Type@0)
                    (n : Nat)
                    (head : A)
                    (tail : forall (C : forall (l : Nat) -> Type@1)
                                   (nil : C 0)
                                   (cons : forall (l : Nat)
                                                  (a : A)
                                                  (r : C l)
                                             -> C (succ l))
                              -> C n)
                    (C : forall (l : Nat) -> Type@1)
                    (nil : C 0)
                    (cons : forall (l : Nat)
                                   (a : A)
                                   (r : C l)
                              -> C (succ l))
                 -> cons n head (tail C nil cons))
               (fun (A : Type@0)
                    (n : Nat)
                    (vec : forall (C : forall (l : Nat) -> Type@1)
                                  (nil : C 0)
                                  (cons : forall (l : Nat)
                                                 (a : A)
                                                 (r : C l)
                                            -> C (succ l))
                             -> C n)
                    (C : forall (l : Nat) -> Type@1)
                    (nil : C 0)
                    (cons : forall (l : Nat)
                                   (a : A)
                                   (r : C l)
                              -> C (succ l))
                 -> vec C nil cons) : Nat
      end
    Elaborated:
      (fun (x1 : Nat) -> x1)
        ((fun (x2 : forall (A1 : Type@0)
                           (x3 : Nat)
                      -> Type@2)
              (x4 : forall (A2 : Type@0) -> x2 A2 0)
              (x5 : forall (A3 : Type@0)
                           (x6 : Nat)
                           (x7 : A3)
                           (x8 : x2 A3 x6)
                      -> x2 A3 (succ x6))
              (x9 : forall (A4 : Type@0)
                           (x10 : Nat)
                           (x11 : x2 A4 x10)
                           (x12 : forall (x13 : Nat) -> Type@1)
                           (x14 : x12 0)
                           (x15 : forall (x16 : Nat)
                                         (x17 : A4)
                                         (x18 : x12 x16)
                                    -> x12 (succ x16))
                      -> x12 x10)
           -> (fun (x19 : forall (A5 : Type@0)
                                 (x20 : Nat)
                                 (x21 : x2 A5 (succ x20))
                            -> A5)
                   (x22 : x2 (forall (x23 : Nat) -> Nat) 3)
                -> x19 (forall (x24 : Nat) -> Nat) 2 x22 4)
                (fun (A6 : Type@0)
                     (x25 : Nat)
                     (x26 : x2 A6 (succ x25))
                  -> x9 A6 (succ x25) x26
                       (fun (x27 : Nat)
                         -> rec x27 return x28 . Type@0
                            | zero => Nat
                            | succ x29, A7 => A6
                            end)
                       0
                       (fun (x30 : Nat)
                            (x31 : A6)
                            (x32 : rec x30 return x33 . Type@0
                                   | zero => Nat
                                   | succ x34, A8 => A6
                                   end)
                         -> x31))
                (x5 (forall (x35 : Nat) -> Nat) 2
                   (fun (x36 : Nat) -> succ (succ (succ x36)))
                  (x5 (forall (x37 : Nat) -> Nat) 1 (fun (x38 : Nat) -> succ x38)
                    (x5 (forall (x39 : Nat) -> Nat) 0
                       (fun (x40 : Nat) -> succ (succ x40))
                      (x4 (forall (x41 : Nat) -> Nat))))))
           (fun (A9 : Type@0)
                (x42 : Nat)
             -> forall (x43 : forall (x44 : Nat) -> Type@1)
                       (x45 : x43 0)
                       (x46 : forall (x47 : Nat)
                                     (x48 : A9)
                                     (x49 : x43 x47)
                                -> x43 (succ x47))
                  -> x43 x42)
           (fun (A10 : Type@0)
                (x50 : forall (x51 : Nat) -> Type@1)
                (x52 : x50 0)
                (x53 : forall (x54 : Nat)
                              (x55 : A10)
                              (x56 : x50 x54)
                         -> x50 (succ x54))
             -> x52)
           (fun (A11 : Type@0)
                (x57 : Nat)
                (x58 : A11)
                (x59 : forall (x60 : forall (x61 : Nat) -> Type@1)
                              (x62 : x60 0)
                              (x63 : forall (x64 : Nat)
                                            (x65 : A11)
                                            (x66 : x60 x64)
                                       -> x60 (succ x64))
                         -> x60 x57)
                (x67 : forall (x68 : Nat) -> Type@1)
                (x69 : x67 0)
                (x70 : forall (x71 : Nat)
                              (x72 : A11)
                              (x73 : x67 x71)
                         -> x67 (succ x71))
             -> x70 x57 x58 (x59 x67 x69 x70))
          (fun (A12 : Type@0)
               (x74 : Nat)
               (x75 : forall (x76 : forall (x77 : Nat) -> Type@1)
                             (x78 : x76 0)
                             (x79 : forall (x80 : Nat)
                                           (x81 : A12)
                                           (x82 : x76 x80)
                                      -> x76 (succ x80))
                        -> x76 x74)
               (x83 : forall (x84 : Nat) -> Type@1)
               (x85 : x83 0)
               (x86 : forall (x87 : Nat)
                             (x88 : A12)
                             (x89 : x83 x87)
                        -> x83 (succ x87))
            -> x75 x83 x85 x86))
      : Nat
    Normalized Result:
      7 : Nat
    |}]

let%expect_test "def_abstract.mctt works" =
  let _ = main_of_example "def_abstract.mctt" in
  [%expect {|
    Parsed:
      module DefAbstract where
        def double : forall (x : Nat) -> Nat :=
          fun (x : Nat)
            -> rec x return y . Nat | zero => 0 | succ p, r => succ (succ r) end
        end
        abstract def four : Nat :=
          double 2
        end
        eval double four : Nat
        eval double four
      end
    Elaborated:
      (fun (x1 : forall (x2 : Nat) -> Nat)
        -> (fun (x3 : Nat)
             -> (fun (x4 : Nat) -> x4)
                  ((fun (x5 : Nat)
                     -> rec x5 return x6 . Nat
                        | zero => 0
                        | succ x7, x8 => succ (succ x8)
                        end)
                    x3))
             ((fun (x9 : Nat)
                -> rec x9 return x10 . Nat
                   | zero => 0
                   | succ x11, x12 => succ (succ x12)
                   end)
               2))
        (fun (x13 : Nat)
          -> rec x13 return x14 . Nat
             | zero => 0
             | succ x15, x16 => succ (succ x16)
             end)
      : Nat
    Normalized Result:
      8 : Nat
    Elaborated:
      (fun (x1 : forall (x2 : Nat) -> Nat)
        -> (fun (x3 : Nat)
             -> (fun (x4 : Nat)
                  -> rec x4 return x5 . Nat
                     | zero => 0
                     | succ x6, x7 => succ (succ x7)
                     end)
                  x3)
             ((fun (x8 : Nat)
                -> rec x8 return x9 . Nat
                   | zero => 0
                   | succ x10, x11 => succ (succ x11)
                   end)
               2))
        (fun (x12 : Nat)
          -> rec x12 return x13 . Nat
             | zero => 0
             | succ x14, x15 => succ (succ x15)
             end)
      : Nat
    Normalized Result:
      8 : Nat
    |}]

let%expect_test "module_nested.mctt works" =
  let _ = main_of_example "module_nested.mctt" in
  [%expect {|
    Parsed:
      module Arith where
        module Ops where
          def pred : forall (x : Nat) -> Nat :=
            fun (x : Nat)
              -> rec x return y . Nat | zero => 0 | succ p, r => p end
          end
          def twice : forall (f : forall (x : Nat) -> Nat)
                             (x : Nat)
                        -> Nat :=
            fun (f : forall (x : Nat) -> Nat)
                (x : Nat)
              -> f (f x)
          end
        end
        eval Ops.twice Ops.pred 5
      end
    Elaborated:
      (fun (x1 : forall (x2 : Nat) -> Nat)
        -> (fun (x3 : forall (x4 : forall (x5 : Nat) -> Nat)
                             (x6 : Nat)
                        -> Nat)
             -> (fun (x7 : forall (x8 : Nat) -> Nat)
                     (x9 : Nat)
                  -> x7 (x7 x9))
                  (fun (x10 : Nat)
                    -> rec x10 return x11 . Nat
                       | zero => 0
                       | succ x12, x13 => x12
                       end)
                  5)
             (fun (x14 : forall (x15 : Nat) -> Nat)
                  (x16 : Nat)
               -> x14 (x14 x16)))
        (fun (x17 : Nat)
          -> rec x17 return x18 . Nat | zero => 0 | succ x19, x20 => x19 end)
      : Nat
    Normalized Result:
      3 : Nat
    |}]

let%expect_test "module_param.mctt works" =
  let _ = main_of_example "module_param.mctt" in
  [%expect {|
    Parsed:
      module ModuleParam where
        module Church (A : Type@0) where
          def t : Type@0 :=
            forall (z : A)
                   (s : forall (x : A) -> A)
              -> A
          end
          def two : t A :=
            fun (z : A)
                (s : forall (x : A) -> A)
              -> s (s z)
          end
        end
        eval let
               module C := Church Nat
               in C.two 0 (fun (x : Nat) -> succ x)
             end : Nat
      end
    Elaborated:
      (fun (x1 : forall (A1 : Type@0) -> Type@0)
        -> (fun (x2 : forall (A2 : Type@0)
                        -> (fun (A3 : Type@0)
                             -> forall (x3 : A3)
                                       (x4 : forall (x5 : A3) -> A3)
                                  -> A3)
                             A2)
             -> (fun (x6 : Nat) -> x6)
                  ((fun (A4 : Type@0)
                        (x7 : A4)
                        (x8 : forall (x9 : A4) -> A4)
                     -> x8 (x8 x7))
                     Nat
                     0
                    (fun (x10 : Nat) -> succ x10)))
             (fun (A5 : Type@0)
                  (x11 : A5)
                  (x12 : forall (x13 : A5) -> A5)
               -> x12 (x12 x11)))
        (fun (A6 : Type@0)
          -> forall (x14 : A6)
                    (x15 : forall (x16 : A6) -> A6)
               -> A6)
      : Nat
    Normalized Result:
      2 : Nat
    |}]

let%expect_test "import_use.mctt works" =
  let _ = main_of_example "import_use.mctt" in
  [%expect {|
    Parsed:
      module ImportUse where
        module Impl where
          private def secret : Nat :=
            3
          end
          def exposed : Nat :=
            succ secret
          end
        end
        import Impl as I
        import Impl use (exposed)
        def sum : forall (x : Nat)
                         (y : Nat)
                    -> Nat :=
          fun (x : Nat)
              (y : Nat)
            -> rec x return z . Nat | zero => y | succ p, r => succ r end
        end
        eval sum I.exposed exposed : Nat
      end
    Elaborated:
      (fun (x1 : Nat)
        -> (fun (x2 : Nat)
             -> (fun (x3 : forall (x4 : Nat)
                                  (x5 : Nat)
                             -> Nat)
                  -> (fun (x6 : Nat) -> x6)
                       ((fun (x7 : Nat)
                             (x8 : Nat)
                          -> rec x7 return x9 . Nat
                             | zero => x8
                             | succ x10, x11 => succ x11
                             end)
                          4
                         4))
                  (fun (x12 : Nat)
                       (x13 : Nat)
                    -> rec x12 return x14 . Nat
                       | zero => x13
                       | succ x15, x16 => succ x16
                       end))
             4)
        3
      : Nat
    Normalized Result:
      8 : Nat
    |}]

let%expect_test "let_decl.mctt works" =
  let _ = main_of_example "let_decl.mctt" in
  [%expect {|
    Parsed:
      module LetDecl where
        eval let
               def n : Nat := 2
               def m : Nat := succ n
               in succ m
             end : Nat
      end
    Elaborated:
      (fun (x1 : Nat) -> x1) ((fun (x2 : Nat) -> (fun (x3 : Nat) -> 4) 3) 2)
      : Nat
    Normalized Result:
      4 : Nat
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
