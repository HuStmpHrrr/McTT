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
  [%expect {| Evaluate 0 --> 0 : ℕ |}]

let%expect_test "zero is not of Type@0" =
  let _ = main_of_body "eval zero : Type@0" in
  [%expect {| Error: 0 is not of type Type@0 |}]

let%expect_test "succ zero is of Nat" =
  let _ = main_of_body "eval succ zero : Nat" in
  [%expect {| Evaluate 1 --> 1 : ℕ |}]

let%expect_test "succ Type@0 is not of Nat (as it is ill-typed)" =
  let _ = main_of_body "eval succ Type@0 : Nat" in
  [%expect {| Error: succ Type@0 is not of type ℕ |}]

let%expect_test "succ Type@0 has no inferable type" =
  let _ = main_of_body "eval succ Type@0" in
  [%expect {| Error: succ Type@0 has no inferable type |}]

let%expect_test "an unascribed eval infers its type" =
  let _ = main_of_body "eval fun (y : Nat) -> y" in
  [%expect {| Evaluate λ (x1 : ℕ) → x1 --> λ (x1 : ℕ) → x1 : ∀ (x1 : ℕ) → ℕ |}]

(* Each Unicode spelling lexes to the same token as its ASCII one, and the
   printer prints the Unicode one. *)
let%expect_test "the ASCII spellings parse and print in Unicode" =
  let _ = main_of_body
    "def t : True := true end \
     def f : forall (b : False) -> Nat := fun (b : False) -> exfalso b return y . Nat end \
     eval rec 2 return y . Nat | zero => 0 | succ n, r => succ r end \
     eval t eval f" in
  [%expect {|
    Evaluate rec 2 return x1 . ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ x3 end --> 2 : ℕ
    Evaluate t --> ⋆ : ⊤
    Evaluate f --> λ (x1 : ⊥) → exfalso x1 return x2 . ℕ : ∀ (x1 : ⊥) → ℕ
    |}]

let%expect_test "each Unicode spelling parses" =
  let _ = main_of_body
    "def t : ⊤ ≔ ⋆ end \
     def f : ∀ (b : ⊥) → ℕ ≔ λ (b : ⊥) → exfalso b return y . ℕ end \
     def g : Π (x : ℕ) → ℕ ≔ λ (x : ℕ) → x end \
     def u : Type@ω ≔ Type@0 end \
     eval rec 2 return y . ℕ | zero ⇒ 0 | succ n, r ⇒ succ r end \
     eval t eval f eval g" in
  [%expect {|
    Evaluate rec 2 return x1 . ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ x3 end --> 2 : ℕ
    Evaluate t --> ⋆ : ⊤
    Evaluate f --> λ (x1 : ⊥) → exfalso x1 return x2 . ℕ : ∀ (x1 : ⊥) → ℕ
    Evaluate g --> λ (x1 : ℕ) → x1 : ∀ (x1 : ℕ) → ℕ
    |}]

(* Identifiers are ASCII letters, so no Unicode symbol needs a space. *)
let%expect_test "Unicode symbols need no spaces" =
  let _ = main_of_body "def g:∀(x:ℕ)→ℕ≔λ(x:ℕ)→x end eval g" in
  [%expect {| Evaluate g --> λ (x1 : ℕ) → x1 : ∀ (x1 : ℕ) → ℕ |}]

let%expect_test "a unit path may be spelled with ›" =
  let _ = main_of_multi_string "import Lib›Num module Test where eval Lib::Num.double 2 eval Lib›Num.Ops.pred 2 end" in
  [%expect {|
    Evaluate Lib›Num.double 2 --> 4 : ℕ
    Evaluate Lib›Num.Ops.pred 2 --> 1 : ℕ
    |}]

(* [∷] is not a path separator: only [::] and [›] are. *)
let%expect_test "a unit path spelled with ∷ is rejected" =
  let _ = main_of_multi_string "import Lib∷Num module Test where eval 0 end" in
  [%expect {| Error: unexpected character "∷" at line 1, column 11 |}]

let%expect_test "a Unicode character that is not a token is rejected" =
  let _ = main_of_body "eval λ (x : ℕ) ↦ x" in
  [%expect {| Error: unexpected character "↦" at line 1, column 34 |}]

(* Columns count characters: [→] is one column, as it is displayed. *)
let%expect_test "a syntax error after Unicode is located by characters" =
  let _ = main_of_body "eval λ (x : ℕ) → → x" in
  [%expect {|
    Error: on "→" (at line 1, column 36 - line 1, column 37): An expression is
      expected after "→".
      This token is invalid for the beginning of an expression.
    |}]

let%expect_test "several evals are reported in order" =
  let _ = main_of_body "def two : Nat := 2 end eval two eval succ two" in
  [%expect {|
    Evaluate two --> 2 : ℕ
    Evaluate succ two --> 3 : ℕ
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
  [%expect {| Evaluate λ (x1 : ℕ) → x1 --> λ (x1 : ℕ) → x1 : ∀ (x1 : ℕ) → ℕ |}]

let%expect_test "recursion on a natural number that always returns zero is of \
                 Nat" =
  let _ = main_of_body
    "eval rec 3 return y . Nat | zero => 0 | succ n, r => 0 end : Nat" in
  [%expect {| Evaluate rec 3 return x1 . ℕ | zero ⇒ 0 | succ x2, x3 ⇒ 0 end --> 0 : ℕ |}]

let%expect_test "SimpleNat.mctt works" =
  let _ = main_of_example "SimpleNat.mctt" in
  [%expect {| Evaluate 4 --> 4 : ℕ |}]

let%expect_test "SimpleRec.mctt works" =
  let _ = main_of_example "SimpleRec.mctt" in
  [%expect {|
    Evaluate λ (x1 : ℕ)
               → rec x1 return x2 . ℕ | zero ⇒ 1 | succ x3, x4 ⇒ succ x4 end
      --> λ (x1 : ℕ)
            → rec x1 return x2 . ℕ | zero ⇒ 1 | succ x3, x4 ⇒ succ x4 end
      : ∀ (x1 : ℕ) → ℕ
    |}]

let%expect_test "TrueFalse.mctt works" =
  let _ = main_of_example "TrueFalse.mctt" in
  [%expect {|
    Evaluate ⋆ --> ⋆ : ⊤
    Evaluate λ (x1 : ⊤) → x1 --> λ (x1 : ⊤) → ⋆ : ∀ (x1 : ⊤) → ⊤
    Evaluate λ (x1 : ⊥) → exfalso x1 return x2 . ℕ
      --> λ (x1 : ⊥) → exfalso x1 return x2 . ℕ : ∀ (x1 : ⊥) → ℕ
    |}]

let%expect_test "LetTrueFalse.mctt works" =
  let _ = main_of_example "LetTrueFalse.mctt" in
  [%expect {|
    Evaluate let x1 : ⊤ ≔ ⋆;
                 x2 : ∀ (x3 : ⊥) → ℕ ≔ λ (x4 : ⊥) → exfalso x4 return x5 . ℕ
             in x1
             end --> ⋆ : ⊤
    |}]

let%expect_test "lib/NatTheory.mctt" =
  let _ = main_of_lib "NatTheory.mctt" in
  [%expect {|
    Evaluate plusComm 2 3 --> ⋆ : ⊤
    Evaluate sym 4 4 (refl 4) --> ⋆ : ⊤
    Evaluate zeroNeSucc 5 --> λ (x1 : ⊥) → Prelude›Arith›Equality.zeroNeSucc 5 x1
      : ∀ (x1 : ⊥) → ⊥
    Evaluate iterSucc 3 4 --> ⋆ : ⊤
    Evaluate Iter.iter 0l ℕ (λ (x1 : ℕ) → plus x1 x1) 3 1 --> 8 : ℕ
    Evaluate let module M1 ≔ Iter 0l ℕ (λ (x1 : ℕ) → plus x1 x1);
                 x2 ≔ 2;
                 x3 : Eq (M1.iter x2 1) 4 ≔ ⋆
             in x3
             end --> ⋆ : ⊤
    |}]

let%expect_test "zero is not of True" =
  let _ = main_of_body "eval zero : True" in
  [%expect {| Error: 0 is not of type ⊤ |}]

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
    Evaluate (λ (x1 : ∀ (A1 : Type@0)
                        (A2 : Type@0)
                        → Type@1)
                (x2 : ∀ (A3 : Type@0)
                        (A4 : Type@0)
                        (x3 : A3)
                        (x4 : A4)
                        → x1 A3 A4)
                (x5 : ∀ (A5 : Type@0)
                        (A6 : Type@0)
                        (x6 : x1 A5 A6)
                        → A5)
                (x7 : ∀ (A7 : Type@0)
                        (A8 : Type@0)
                        (x8 : x1 A7 A8)
                        → A8)
               → (λ (x9 : x1 ℕ (∀ (x10 : ℕ) → ℕ))
                   → x7 ℕ (∀ (x11 : ℕ) → ℕ) x9 (x5 ℕ (∀ (x12 : ℕ) → ℕ) x9))
                   (x2 ℕ (∀ (x13 : ℕ) → ℕ) 3 (λ (x14 : ℕ) → succ (succ x14))))
               (λ (A9 : Type@0)
                  (A10 : Type@0)
                 → ∀ (A11 : Type@0)
                     (x15 : ∀ (x16 : A9)
                              (x17 : A10)
                              → A11)
                     → A11)
               (λ (A12 : Type@0)
                  (A13 : Type@0)
                  (x18 : A12)
                  (x19 : A13)
                  (A14 : Type@0)
                  (x20 : ∀ (x21 : A12)
                           (x22 : A13)
                           → A14)
                 → x20 x18 x19)
               (λ (A15 : Type@0)
                  (A16 : Type@0)
                  (x23 : ∀ (A17 : Type@0)
                           (x24 : ∀ (x25 : A15)
                                    (x26 : A16)
                                    → A17)
                           → A17)
                 → x23 A15 (λ (x27 : A15)
                              (x28 : A16)
                             → x27))
               (λ (A18 : Type@0)
                  (A19 : Type@0)
                  (x29 : ∀ (A20 : Type@0)
                           (x30 : ∀ (x31 : A18)
                                    (x32 : A19)
                                    → A20)
                           → A20)
                 → x29 A19 (λ (x33 : A18)
                              (x34 : A19)
                             → x34)) --> 5 : ℕ
    |}]

let%expect_test "Vector.mctt works" =
  let _ = main_of_example "Vector.mctt" in
  [%expect {|
    Evaluate (λ (x1 : ∀ (A1 : Type@0)
                        (x2 : ℕ)
                        → Type@2)
                (x3 : ∀ (A2 : Type@0) → x1 A2 0)
                (x4 : ∀ (A3 : Type@0)
                        (x5 : ℕ)
                        (x6 : A3)
                        (x7 : x1 A3 x5)
                        → x1 A3 (succ x5))
                (x8 : ∀ (A4 : Type@0)
                        (x9 : ℕ)
                        (x10 : x1 A4 x9)
                        (x11 : ∀ (x12 : ℕ) → Type@1)
                        (x13 : x11 0)
                        (x14 : ∀ (x15 : ℕ)
                                 (x16 : A4)
                                 (x17 : x11 x15)
                                 → x11 (succ x15))
                        → x11 x9)
               → (λ (x18 : ∀ (A5 : Type@0)
                             (x19 : ℕ)
                             (x20 : x1 A5 (succ x19))
                             → A5)
                    (x21 : x1 (∀ (x22 : ℕ) → ℕ) 3)
                   → x18 (∀ (x23 : ℕ) → ℕ) 2 x21 4)
                   (λ (A6 : Type@0)
                      (x24 : ℕ)
                      (x25 : x1 A6 (succ x24))
                     → x8 A6 (succ x24) x25
                         (λ (x26 : ℕ)
                           → rec x26 return x27 . Type@0
                             | zero ⇒ ℕ
                             | succ x28, A7 ⇒ A6
                             end)
                         0
                         (λ (x29 : ℕ)
                            (x30 : A6)
                            (x31 : rec x29 return x32 . Type@0
                                   | zero ⇒ ℕ
                                   | succ x33, A8 ⇒ A6
                                   end)
                           → x30))
                   (x4 (∀ (x34 : ℕ) → ℕ) 2 (λ (x35 : ℕ) → succ (succ (succ x35)))
                     (x4 (∀ (x36 : ℕ) → ℕ) 1 (λ (x37 : ℕ) → succ x37)
                       (x4 (∀ (x38 : ℕ) → ℕ) 0 (λ (x39 : ℕ) → succ (succ x39))
                         (x3 (∀ (x40 : ℕ) → ℕ))))))
               (λ (A9 : Type@0)
                  (x41 : ℕ)
                 → ∀ (x42 : ∀ (x43 : ℕ) → Type@1)
                     (x44 : x42 0)
                     (x45 : ∀ (x46 : ℕ)
                              (x47 : A9)
                              (x48 : x42 x46)
                              → x42 (succ x46))
                     → x42 x41)
               (λ (A10 : Type@0)
                  (x49 : ∀ (x50 : ℕ) → Type@1)
                  (x51 : x49 0)
                  (x52 : ∀ (x53 : ℕ)
                           (x54 : A10)
                           (x55 : x49 x53)
                           → x49 (succ x53))
                 → x51)
               (λ (A11 : Type@0)
                  (x56 : ℕ)
                  (x57 : A11)
                  (x58 : ∀ (x59 : ∀ (x60 : ℕ) → Type@1)
                           (x61 : x59 0)
                           (x62 : ∀ (x63 : ℕ)
                                    (x64 : A11)
                                    (x65 : x59 x63)
                                    → x59 (succ x63))
                           → x59 x56)
                  (x66 : ∀ (x67 : ℕ) → Type@1)
                  (x68 : x66 0)
                  (x69 : ∀ (x70 : ℕ)
                           (x71 : A11)
                           (x72 : x66 x70)
                           → x66 (succ x70))
                 → x69 x56 x57 (x58 x66 x68 x69))
               (λ (A12 : Type@0)
                  (x73 : ℕ)
                  (x74 : ∀ (x75 : ∀ (x76 : ℕ) → Type@1)
                           (x77 : x75 0)
                           (x78 : ∀ (x79 : ℕ)
                                    (x80 : A12)
                                    (x81 : x75 x79)
                                    → x75 (succ x79))
                           → x75 x73)
                  (x82 : ∀ (x83 : ℕ) → Type@1)
                  (x84 : x82 0)
                  (x85 : ∀ (x86 : ℕ)
                           (x87 : A12)
                           (x88 : x82 x86)
                           → x82 (succ x86))
                 → x74 x82 x84 x85) --> 7 : ℕ
    |}]

let%expect_test "Nary.mctt works" =
  let _ = main_of_example "Nary.mctt" in
  [%expect {|
    Evaluate sum 3 1 2 3 --> 6 : ℕ
    Evaluate let module M1 ≔ Arity ℕ; x1 : M1.Fn 4 ≔ sum 4 in x1 1 2 3 4 end
      --> 10 : ℕ
    |}]

let%expect_test "SimpleLet.mctt works" =
  let _ = main_of_example "SimpleLet.mctt" in
  [%expect {| Evaluate let x1 : ℕ ≔ 0 in succ x1 end --> 1 : ℕ |}]

let%expect_test "an unannotated let infers the type of its definiens" =
  let _ = main_of_body "eval let x := 0 in succ x end" in
  [%expect {| Evaluate let x1 ≔ 0 in succ x1 end --> 1 : ℕ |}]

let%expect_test "annotated and unannotated bindings mix in one let" =
  let _ = main_of_body
    "eval let A : Type@0 := Nat; z := 0; f := fun (n : A) -> succ z in f z end" in
  [%expect {|
    Evaluate let A1 : Type@0 ≔ ℕ; x1 ≔ 0; x2 ≔ λ (x3 : A1) → succ x1 in x2 x1 end
      --> 1 : ℕ
    |}]

let%expect_test "an unannotated let's body may need its delta-equation" =
  let _ = main_of_body "eval let A := Nat in fun (a : A) -> succ a end" in
  [%expect {|
    Evaluate let x1 ≔ ℕ in λ (x2 : x1) → succ x2 end --> λ (x1 : ℕ) → succ x1
      : ∀ (x1 : ℕ) → ℕ
    |}]

let%expect_test "an unannotated let with an ill-typed body is rejected" =
  let _ = main_of_body "eval let A := Nat in succ A end" in
  [%expect {| Error: let x1 ≔ ℕ in succ x1 end has no inferable type |}]

let%expect_test "an unannotated local definition needs its body" =
  let _ = main_of_body "eval let x := in x end" in
  [%expect {|
    Error: on "in" (at line 1, column 33 - line 1, column 35): Expected the body
      of the local definition.
    |}]

let%expect_test "LetTwoVars.mctt works" =
  let _ = main_of_example "LetTwoVars.mctt" in
  [%expect {|
    Evaluate let x1 : ℕ ≔ 0; x2 : ∀ (x3 : ℕ) → ℕ ≔ λ (x4 : ℕ) → x4 in x2 x1 end
      --> 0 : ℕ
    |}]

let%expect_test "LetNary.mctt works" =
  let _ = main_of_example "LetNary.mctt" in
  [%expect {|
    Evaluate let x1 : ∀ (x2 : ℕ) → Type@0 ≔
                   λ (x3 : ℕ)
                     → rec x3 return x4 . Type@0
                       | zero ⇒ ℕ
                       | succ x5, A1 ⇒ ∀ (x6 : ℕ) → A1
                       end;
                 x7 : ∀ (x8 : x1 0) → ℕ ≔ λ (x9 : ℕ) → x9;
                 x10 : ∀ (x11 : ℕ)
                         (x12 : x1 (succ x11))
                         (x13 : ℕ)
                         → x1 x11 ≔
                   λ (x14 : ℕ)
                     (x15 : rec succ x14 return x16 . Type@0
                            | zero ⇒ ℕ
                            | succ x17, A2 ⇒ ∀ (x18 : ℕ) → A2
                            end)
                     (x19 : ℕ)
                     → x15 x19;
                 x20 : ℕ ≔ 3;
                 x21 : x1 x20 ≔
                   let x22 : ∀ (x23 : ℕ)
                               (x24 : ℕ)
                               → ℕ ≔
                         λ (x25 : ℕ)
                           (x26 : ℕ)
                           → rec x25 return x27 . ℕ
                             | zero ⇒ x26
                             | succ x28, x29 ⇒ succ x29
                             end
                   in λ (x30 : ℕ)
                        (x31 : ℕ)
                        (x32 : ℕ)
                        → x22 x30 (x22 x31 x32)
                   end
             in (rec x20 return x33 . ∀ (x36 : x1 x33) → ℕ
                 | zero ⇒ x7
                 | succ x34, x35 ⇒
                   λ (x37 : x1 (succ x34)) → x35 (x10 x34 x37 (succ x34))
                 end)
                  x21
             end --> 6 : ℕ
    |}]

let%expect_test "LetVector.mctt works" =
  let _ = main_of_example "LetVector.mctt" in
  [%expect {|
    Evaluate let x1 : ∀ (A1 : Type@0)
                        (x2 : ℕ)
                        → Type@2 ≔
                   λ (A2 : Type@0)
                     (x3 : ℕ)
                     → ∀ (x4 : ∀ (x5 : ℕ) → Type@1)
                         (x6 : x4 0)
                         (x7 : ∀ (x8 : ℕ)
                                 (x9 : A2)
                                 (x10 : x4 x8)
                                 → x4 (succ x8))
                         → x4 x3;
                 x11 : ∀ (A3 : Type@0) → x1 A3 0 ≔
                   λ (A4 : Type@0)
                     (x12 : ∀ (x13 : ℕ) → Type@1)
                     (x14 : x12 0)
                     (x15 : ∀ (x16 : ℕ)
                              (x17 : A4)
                              (x18 : x12 x16)
                              → x12 (succ x16))
                     → x14;
                 x19 : ∀ (A5 : Type@0)
                         (x20 : ℕ)
                         (x21 : A5)
                         (x22 : x1 A5 x20)
                         → x1 A5 (succ x20) ≔
                   λ (A6 : Type@0)
                     (x23 : ℕ)
                     (x24 : A6)
                     (x25 : ∀ (x26 : ∀ (x27 : ℕ) → Type@1)
                              (x28 : x26 0)
                              (x29 : ∀ (x30 : ℕ)
                                       (x31 : A6)
                                       (x32 : x26 x30)
                                       → x26 (succ x30))
                              → x26 x23)
                     (x33 : ∀ (x34 : ℕ) → Type@1)
                     (x35 : x33 0)
                     (x36 : ∀ (x37 : ℕ)
                              (x38 : A6)
                              (x39 : x33 x37)
                              → x33 (succ x37))
                     → x36 x23 x24 (x25 x33 x35 x36);
                 x40 : ∀ (A7 : Type@0)
                         (x41 : ℕ)
                         (x42 : x1 A7 x41)
                         (x43 : ∀ (x44 : ℕ) → Type@1)
                         (x45 : x43 0)
                         (x46 : ∀ (x47 : ℕ)
                                  (x48 : A7)
                                  (x49 : x43 x47)
                                  → x43 (succ x47))
                         → x43 x41 ≔
                   λ (A8 : Type@0)
                     (x50 : ℕ)
                     (x51 : ∀ (x52 : ∀ (x53 : ℕ) → Type@1)
                              (x54 : x52 0)
                              (x55 : ∀ (x56 : ℕ)
                                       (x57 : A8)
                                       (x58 : x52 x56)
                                       → x52 (succ x56))
                              → x52 x50)
                     (x59 : ∀ (x60 : ℕ) → Type@1)
                     (x61 : x59 0)
                     (x62 : ∀ (x63 : ℕ)
                              (x64 : A8)
                              (x65 : x59 x63)
                              → x59 (succ x63))
                     → x51 x59 x61 x62;
                 x66 : ∀ (A9 : Type@0)
                         (x67 : ℕ)
                         (x68 : x1 A9 (succ x67))
                         → A9 ≔
                   λ (A10 : Type@0)
                     (x69 : ℕ)
                     (x70 : x1 A10 (succ x69))
                     → x40 A10 (succ x69) x70
                         (λ (x71 : ℕ)
                           → rec x71 return x72 . Type@0
                             | zero ⇒ ℕ
                             | succ x73, A11 ⇒ A10
                             end)
                         0
                         (λ (x74 : ℕ)
                            (x75 : A10)
                            (x76 : rec x74 return x77 . Type@0
                                   | zero ⇒ ℕ
                                   | succ x78, A12 ⇒ A10
                                   end)
                           → x75);
                 x79 : x1 (∀ (x80 : ℕ) → ℕ) 3 ≔
                   x19 (∀ (x81 : ℕ) → ℕ) 2 (λ (x82 : ℕ) → succ (succ (succ x82)))
                     (x19 (∀ (x83 : ℕ) → ℕ) 1 (λ (x84 : ℕ) → succ x84)
                       (x19 (∀ (x85 : ℕ) → ℕ) 0 (λ (x86 : ℕ) → succ (succ x86))
                         (x11 (∀ (x87 : ℕ) → ℕ))))
             in x66 (∀ (x88 : ℕ) → ℕ) 2 x79 4
             end --> 7 : ℕ
    |}]

let%expect_test "DefAbstract.mctt works" =
  let _ = main_of_example "DefAbstract.mctt" in
  [%expect {|
    Evaluate double four
      --> rec four return x1 . ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ (succ x3) end
      : ℕ
    Evaluate double four
      --> rec four return x1 . ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ (succ x3) end
      : ℕ
    |}]

let%expect_test "ModuleNested.mctt works" =
  let _ = main_of_example "ModuleNested.mctt" in
  [%expect {| Evaluate Ops.twice Ops.pred 5 --> 3 : ℕ |}]

let%expect_test "ModuleParam.mctt works" =
  let _ = main_of_example "ModuleParam.mctt" in
  [%expect {|
    Evaluate let module M1 ≔ Church ℕ in M1.two 0 (λ (x1 : ℕ) → succ x1) end
      --> 2 : ℕ
    |}]

let%expect_test "SortedLevels.mctt works" =
  let _ = main_of_example "SortedLevels.mctt" in
  [%expect {|
    Evaluate ω --> ω : Level@1
    Evaluate succl ω --> ω+1 : Level@1
    Evaluate maxl 3l ω·2+1 --> ω·2+1 : Level@2
    Evaluate maxl ω·2 ω --> ω·2 : Level@2
    Evaluate λ (x1 : Level) → maxl x1 ω --> λ (x1 : Level) → ω
      : ∀ (x1 : Level) → Level@1
    Evaluate λ (x1 : Level@1) → maxl x1 ω --> λ (x1 : Level@1) → maxl ω x1
      : ∀ (x1 : Level@1) → Level@1
    Evaluate PolyId --> ∀ (x1 : Level)
                          (A1 : Type@{x1})
                          (x2 : A1)
                          → A1 : Type@ω
    Evaluate polyId 3l Type@2 Type@1 --> Type@1 : Type@2
    Evaluate PolyIdUp --> ∀ (x1 : Level@1)
                            (A1 : Type@{x1})
                            (x2 : A1)
                            → A1 : Type@{ω·2}
    Evaluate polyIdUp ω PolyId polyId
      --> λ (x1 : Level)
            (A1 : Type@{x1})
            (x2 : A1)
            → x2 : ∀ (x1 : Level)
                     (A1 : Type@{x1})
                     (x2 : A1)
                     → A1
    Evaluate length ω PolyId fs --> 2 : ℕ
    Evaluate headOr ω PolyId twice fs 0l ℕ 5 --> 5 : ℕ
    Evaluate length ω+1 Type@ω ts --> 4 : ℕ
    Evaluate headOr ω+1 Type@ω ⊤ ts --> ℕ : Type@ω
    |}]

let%expect_test "Universes.mctt works" =
  let _ = main_of_example "Universes.mctt" in
  [%expect {|
    Evaluate id 1l Type@0 ℕ --> ℕ : Type@0
    Evaluate atoms --> λ (x1 : Level)
                         (x2 : Level)
                         → Type@{maxl (maxl 1l x2) x1}
      : ∀ (x1 : Level)
          (x2 : Level)
          → Type@{maxl (maxl 2l (succl x2)) (succl x1)}
    Evaluate self 3 --> 3 : ℕ
    Evaluate Dom --> ℕ : Type@0
    Evaluate Type@{depth 3} --> Type@3 : Type@4
    Evaluate Endo 0l ℕ --> ∀ (x1 : ℕ) → ℕ : Type@0
    Evaluate λ (x1 : Level)
               (A1 : Type@{x1})
               → ∀ (x2 : A1) → A1
      --> λ (x1 : Level)
            (A1 : Type@{x1})
            → ∀ (x2 : A1) → A1 : ∀ (x1 : Level)
                                   (A1 : Type@{x1})
                                   → Type@{x1}
    Evaluate ∀ (x1 : Level) → Type@{x1} --> ∀ (x1 : Level) → Type@{x1} : Type@ω
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

(* [Type@ω] is the universe at [ω], above every one at a finite level; it
   has three other spellings, and the higher ones are [Type@{ω+n}] or
   [Type@nL]. *)
let%expect_test "the universe at ω holds one at a finite level" =
  let _ = main_of_body "eval Type@5 : Type@ω" in
  [%expect {| Evaluate Type@5 --> Type@5 : Type@ω |}]

let%expect_test "every spelling of the universe at ω" =
  let _ = main_of_body "eval Type@omega : Type@{ω+1}" in
  [%expect {| Evaluate Type@ω --> Type@ω : Type@1L |}]

let%expect_test "the shorthand for a universe at ω+n" =
  let _ = main_of_body "eval Type@{omega} : Type@1L" in
  [%expect {| Evaluate Type@ω --> Type@ω : Type@1L |}]

let%expect_test "a universe above the one at ω" =
  let _ = main_of_body "eval Type@{ω+2}" in
  [%expect {| Evaluate Type@2L --> Type@2L : Type@3L |}]

(* A bare numeral is a finite level, so the universe at ω is not below it. *)
let%expect_test "the universe at ω is not in one at a finite level" =
  let _ = main_of_body "eval Type@ω : Type@3" in
  [%expect {| Error: Type@ω is not of type Type@3 |}]

(* A function type of small types is small at their level, also at a level
   variable; two levels join. *)
let%expect_test "a function type at a level variable is small" =
  let _ = main_of_body "def Endo (u : Level) (A : Type@{u}) : Type@{u} := forall (a : A) -> A end eval Endo" in
  [%expect {|
    Evaluate Endo --> λ (x1 : Level)
                        (A1 : Type@{x1})
                        → ∀ (x2 : A1) → A1
      : ∀ (x1 : Level)
          (A1 : Type@{x1})
          → Type@{x1}
    |}]

let%expect_test "a function type between two small universes is at their join" =
  let _ = main_of_body "eval fun (u : Level) (v : Level) (A : Type@{u}) (B : Type@{v}) -> forall (a : A) -> B" in
  [%expect {|
    Evaluate λ (x1 : Level)
               (x2 : Level)
               (A1 : Type@{x1})
               (A2 : Type@{x2})
               → ∀ (x3 : A1) → A2
      --> λ (x1 : Level)
            (x2 : Level)
            (A1 : Type@{x1})
            (A2 : Type@{x2})
            → ∀ (x3 : A1) → A2
      : ∀ (x1 : Level)
          (x2 : Level)
          (A1 : Type@{x1})
          (A2 : Type@{x2})
          → Type@{maxl x2 x1}
    |}]

(* A codomain whose level mentions the bound variable has no universe at a
   finite level to be in. *)
let%expect_test "a type quantifying over levels is not at a finite level" =
  let _ = main_of_body "eval (forall (u : Level) -> Type@{u}) : Type@5" in
  [%expect {| Error: ∀ (x1 : Level) → Type@{x1} is not of type Type@5 |}]

(* [<n>L] is the level literal [ω+n], wherever a level is accepted: the
   same core literal as [ω + n], so it prints as [ω+n]. *)
let%expect_test "<n>L is the level ω+n" =
  let _ = main_of_body "eval 1L : Level@1" in
  [%expect {| Evaluate ω+1 --> ω+1 : Level@1 |}]

let%expect_test "0L is ω" =
  let _ = main_of_body "eval succl 0L" in
  [%expect {| Evaluate succl ω --> ω+1 : Level@1 |}]

let%expect_test "<n>L joins with a finite level" =
  let _ = main_of_body "eval maxl 1L 3l" in
  [%expect {| Evaluate maxl ω+1 3l --> ω+1 : Level@1 |}]

let%expect_test "a braced <n>L is the universe at ω+n" =
  let _ = main_of_body "eval Type@{1L}" in
  [%expect {| Evaluate Type@1L --> Type@1L : Type@2L |}]

(* A definition of the level [1L] is [ω + 1]: the universes at the two are
   one type. *)
let%expect_test "a level defined as <n>L equals ω+n" =
  let _ = main_of_body "def foo : Level@1 := 1L end eval (fun (A : Type@{foo}) -> A) : forall (A : Type@{ω + 1}) -> Type@1L" in
  [%expect {|
    Evaluate λ (A1 : Type@{foo}) → A1 --> λ (A1 : Type@1L) → A1
      : ∀ (A1 : Type@1L) → Type@1L
    |}]

let%expect_test "<n>L is not a finite level" =
  let _ = main_of_body "eval 1L : Level" in
  [%expect {| Error: ω+1 is not of type Level |}]

(* The large universes, at ω²+i: [Type@{ω^2}] and [Type@{ω^2+i}], braced.
   Each is in the next, and holds every small universe. *)
let%expect_test "the large universe at ω²" =
  let _ = main_of_body "eval Type@{omega^2}" in
  [%expect {| Evaluate Type@{ω^2} --> Type@{ω^2} : Type@{ω^2+1} |}]

let%expect_test "a large universe at ω²+i" =
  let _ = main_of_body "eval Type@{ω^2 + 3}" in
  [%expect {| Evaluate Type@{ω^2+3} --> Type@{ω^2+3} : Type@{ω^2+4} |}]

let%expect_test "a small universe is in the large one" =
  let _ = main_of_body "eval Type@5 : Type@{ω^2}" in
  [%expect {| Evaluate Type@5 --> Type@5 : Type@{ω^2} |}]

let%expect_test "a function type over a large universe is large" =
  let _ = main_of_body "eval forall (A : Type@{ω^2}) -> A" in
  [%expect {| Evaluate ∀ (A1 : Type@{ω^2}) → A1 --> ∀ (A1 : Type@{ω^2}) → A1 : Type@{ω^2+1} |}]

let%expect_test "a large universe is not in itself" =
  let _ = main_of_body "eval Type@{ω^2} : Type@{ω^2}" in
  [%expect {| Error: Type@{ω^2} is not of type Type@{ω^2} |}]

(* [ω^2] is not a level, wherever it is written outside the braces of a
   large universe. *)
let%expect_test "ω^2 is not a level" =
  let _ = main_of_body "eval ω^2 : Level@1" in
  [%expect {|
    Error: on "ω^2" (at line 1, column 24 - line 1, column 27): ω^2 is not a
      level: every level is below it. It is written only in a large universe,
      "Type@{ω^2}" or "Type@{ω^2+i}".
    |}]

let%expect_test "an unbraced large universe" =
  let _ = main_of_body "eval Type@omega^2" in
  [%expect {|
    Error: on "ω^2" (at line 1, column 29 - line 1, column 36): ω^2 is not a
      level: every level is below it. It is written only in a large universe,
      "Type@{ω^2}" or "Type@{ω^2+i}".
    |}]

let%expect_test "a large universe without its offset" =
  let _ = main_of_body "eval Type@{ω^2+}" in
  [%expect {|
    Error: on "}" (at line 1, column 34 - line 1, column 35): A numeral is
      expected after "Type@{ω^2+": the large universe "Type@{ω^2+i}".
    |}]

let%expect_test "a large universe not closed" =
  let _ = main_of_body "eval Type@{ω^2 Nat}" in
  [%expect {|
    Error: on "ℕ" (at line 1, column 34 - line 1, column 37): A closing "}" or
      "+i" is expected after "Type@{ω^2": the large universe "Type@{ω^2}" or
      "Type@{ω^2+i}".
    |}]

(* An unbraced [+] is rejected. *)
let%expect_test "an unbraced omega offset is a syntax error" =
  let _ = main_of_body "eval Type@ω+1" in
  [%expect {|
    Error: on "+" (at line 1, column 30 - line 1, column 31): Expected ":"
      followed by the type to check against, or the next command.
    |}]

(* Sorted levels: the literals up to ω², the types [Level@n] of the levels
   below ω·(n+1), absorption at the sort, and the universes at ordinal
   levels. *)
let%expect_test "the ASCII spelling of an ordinal level literal" =
  let _ = main_of_body "eval omega * 2 + 3 : Level@2" in
  [%expect {| Evaluate ω·2+3 --> ω·2+3 : Level@2 |}]

let%expect_test "an ordinal literal abbreviates its zero parts" =
  let _ = main_of_body "eval maxl (ω + 0) (ω * 1) : Level@1" in
  [%expect {| Evaluate maxl ω ω --> ω : Level@1 |}]

let%expect_test "a literal at or above ω is not a finite level" =
  let _ = main_of_body "eval ω : Level" in
  [%expect {| Error: ω is not of type Level |}]

let%expect_test "ω·2 is not a level of Level@1" =
  let _ = main_of_body "eval ω·2 : Level@1" in
  [%expect {| Error: ω·2 is not of type Level@1 |}]

let%expect_test "every type of levels is in the lowest universe" =
  let _ = main_of_body "eval Level@3 : Type@0" in
  [%expect {| Evaluate Level@3 --> Level@3 : Type@0 |}]

let%expect_test "a finite level is a level of every sort" =
  let _ = main_of_body "eval (λ (u : Level) → u) : ∀ (u : Level) → Level@5" in
  [%expect {|
    Evaluate λ (x1 : Level) → x1 --> λ (x1 : Level) → x1
      : ∀ (x1 : Level) → Level@5
    |}]

let%expect_test "a level of a larger sort is not a finite level" =
  let _ = main_of_body "eval (λ (u : Level@1) → u) : ∀ (u : Level@1) → Level" in
  [%expect {| Error: λ (x1 : Level@1) → x1 is not of type ∀ (x1 : Level@1) → Level |}]

let%expect_test "ω absorbs a finite level variable" =
  let _ = main_of_body "eval λ (u : Level) → maxl (succl u) ω" in
  [%expect {|
    Evaluate λ (x1 : Level) → maxl (succl x1) ω --> λ (x1 : Level) → ω
      : ∀ (x1 : Level) → Level@1
    |}]

let%expect_test "ω does not absorb a level variable of a larger sort" =
  let _ = main_of_body "eval λ (u : Level@1) → maxl ω u" in
  [%expect {|
    Evaluate λ (x1 : Level@1) → maxl ω x1 --> λ (x1 : Level@1) → maxl ω x1
      : ∀ (x1 : Level@1) → Level@1
    |}]

let%expect_test "quantifying over the finite levels lands at ω" =
  let _ = main_of_body "eval (∀ (u : Level) → Type@{u}) : Type@ω" in
  [%expect {| Evaluate ∀ (x1 : Level) → Type@{x1} --> ∀ (x1 : Level) → Type@{x1} : Type@ω |}]

let%expect_test "quantifying over Level@1 lands at ω·2" =
  let _ = main_of_body "eval ∀ (u : Level@1) → Type@{u}" in
  [%expect {|
    Evaluate ∀ (x1 : Level@1) → Type@{x1} --> ∀ (x1 : Level@1) → Type@{x1}
      : Type@{ω·2}
    |}]

let%expect_test "quantifying over Level@1 does not land at ω" =
  let _ = main_of_body "eval (∀ (u : Level@1) → Type@{u}) : Type@ω" in
  [%expect {| Error: ∀ (x1 : Level@1) → Type@{x1} is not of type Type@ω |}]

let%expect_test "a universe at an ordinal level, in the next one up" =
  let _ = main_of_body "eval Type@{omega*3} : Type@{ω·3+1}" in
  [%expect {| Evaluate Type@{ω·3} --> Type@{ω·3} : Type@{ω·3+1} |}]

(* [Level@{n}] is [Level@n], and [Level] is [Level@{0}]; the type prints
   at its shortest. *)
let%expect_test "the braced type of levels" =
  let _ = main_of_body "eval 3l : Level@{1}" in
  [%expect {| Evaluate 3l --> 3l : Level@1 |}]

let%expect_test "Level is Level@{0}" =
  let _ = main_of_body "eval (fun (u : Level@{0}) -> u) : forall (u : Level) -> Level@0" in
  [%expect {| Evaluate λ (x1 : Level) → x1 --> λ (x1 : Level) → x1 : ∀ (x1 : Level) → Level |}]

let%expect_test "the braced type of levels needs a numeral" =
  let _ = main_of_body "eval Level@{u}" in
  [%expect {|
    Error: on "u" (at line 1, column 31 - line 1, column 32): A numeral is
      expected after "Level@{": the sort of the type of levels.
    |}]

let%expect_test "the braced type of levels needs its closing brace" =
  let _ = main_of_body "eval Level@{1 Nat}" in
  [%expect {|
    Error: on "ℕ" (at line 1, column 33 - line 1, column 36): A closing "}" is
      expected after the sort of "Level@{n".
    |}]

let%expect_test "Level@ needs a numeral" =
  let _ = main_of_body "eval Level@u" in
  [%expect {|
    Error: on "u" (at line 1, column 30 - line 1, column 31): A numeral is
      expected after "Level@": the sort of the type of levels.
    |}]

(* A universe is not in itself. *)
let%expect_test "a small universe is not in itself" =
  let _ = main_of_body "eval Type@1 : Type@1" in
  [%expect {| Error: Type@1 is not of type Type@1 |}]

(* A level is not a type, and a type is not a level. *)
let%expect_test "a level is not a type" =
  let _ = main_of_body "eval zero : 0l" in
  [%expect {| Error: the ascribed type of 0, 0l, is not a type |}]

(* A declared type is checked to be a type before the body is checked
   against it, and each failure has its own message. *)
let%expect_test "the declared type of a definition is a type" =
  let _ = main_of_program_string "module Repro where def t : Nat Nat := 1 end end" in
  [%expect {| Error: the type of t, ℕ ℕ, is not a type |}];
  let _ = main_of_body "def t : Nat := Type@0 end" in
  [%expect {| Error: the body of t, Type@0, is not of type ℕ |}];
  let _ = main_of_body "def t : Nat := 1 end eval t" in
  [%expect {| Evaluate t --> 1 : ℕ |}]

let%expect_test "the ascription of an eval is a type" =
  let _ = main_of_body "eval 1 : Nat Nat" in
  [%expect {| Error: the ascribed type of 1, ℕ ℕ, is not a type |}];
  let _ = main_of_body "eval Type@0 : Nat" in
  [%expect {| Error: Type@0 is not of type ℕ |}]

let%expect_test "Nat is not a level" =
  let _ = main_of_body "eval Nat : Level" in
  [%expect {| Error: ℕ is not of type Level |}]

(* The level of a small universe may be any term of [Level], including an
   open one, so the normal form of a level has atoms. *)
let%expect_test "an open level normalizes with atoms" =
  let _ = main_of_body "eval fun (u : Level) (v : Level) -> Type@{maxl v (maxl 1l u)}" in
  [%expect {|
    Evaluate λ (x1 : Level)
               (x2 : Level)
               → Type@{maxl x2 (maxl 1l x1)}
      --> λ (x1 : Level)
            (x2 : Level)
            → Type@{maxl (maxl 1l x2) x1}
      : ∀ (x1 : Level)
          (x2 : Level)
          → Type@{maxl (maxl 2l (succl x2)) (succl x1)}
    |}]

let%expect_test "ModuleForms.mctt works" =
  let _ = main_of_example "ModuleForms.mctt" in
  [%expect {|
    Evaluate NatIter.twice (λ (x1 : ℕ) → succ x1) 0 --> 2 : ℕ
    Evaluate Num.Ops.add 2 3 --> 5 : ℕ
    Evaluate O.add 1 1 --> 2 : ℕ
    Evaluate let module M1 (x1 : ℕ) where
                   module Inner where
                     def m : ℕ ≔
                       succ x1
                     end
                   end
                   private def m : ℕ ≔
                     Inner.m
                   end
                   def doubled : ℕ ≔
                     Num.Ops.add m m
                   end
                 end
             in M1.doubled 2
             end --> 6 : ℕ
    |}]

let%expect_test "ImportUse.mctt works" =
  let _ = main_of_example "ImportUse.mctt" in
  [%expect {| Evaluate sum I.exposed exposed --> 8 : ℕ |}]

let%expect_test "LetDecl.mctt works" =
  let _ = main_of_example "LetDecl.mctt" in
  [%expect {| Evaluate let x1 : ℕ ≔ 2; x2 : ℕ ≔ succ x1 in succ x2 end --> 4 : ℕ |}]

let%expect_test "LetDelta.mctt works" =
  let _ = main_of_example "LetDelta.mctt" in
  [%expect {|
    Evaluate let x1 : ℕ ≔ 3; x2 : Nary x1 ≔ λ (x3 : ℕ)
                                              (x4 : ℕ)
                                              (x5 : ℕ)
                                              → x3
             in x2 1 2 3
             end --> 1 : ℕ
    |}]

let%expect_test "LetMulti.mctt works" =
  let _ = main_of_example "LetMulti.mctt" in
  [%expect {|
    Evaluate let A1 : Type@0 ≔ ℕ;
                 x1 : A1 ≔ 2;
                 x2 : ∀ (x3 : A1) → A1 ≔
                   λ (x4 : A1)
                     → rec x4 return x5 . A1
                       | zero ⇒ x1
                       | succ x6, x7 ⇒ succ x7
                       end
             in x2 x1
             end --> 4 : ℕ
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
    Evaluate quadruple 2 --> 8 : ℕ
    Evaluate N.double 3 --> 6 : ℕ
    Evaluate pred (N.double 5) --> 9 : ℕ
    |}]

let%expect_test "a unit with parameters" =
  let _ = main_of_multi "Params.mctt" in
  [%expect {|
    Evaluate Lib›Poly.id ℕ 3 --> 3 : ℕ
    Evaluate id ℕ 4 --> 4 : ℕ
    |}]

let%expect_test "an import is not transitive" =
  let _ = main_of_multi "Transitive.mctt" in
  [%expect {| Error: the unit Lib›Num is not imported |}]

let%expect_test "a cyclic import is rejected" =
  let _ = main_of_multi "Cycle.mctt" in
  [%expect {| Error: cyclic import: Cyc›A → Cyc›B → Cyc›A |}]

let%expect_test "a missing unit is reported" =
  let _ = main_of_multi "Missing.mctt" in
  [%expect {| Error: Lib›Nowhere: cannot find unit |}]

let%expect_test "an ill-typed imported unit is reported" =
  let _ = main_of_multi "BadDep.mctt" in
  [%expect {| Error: the body of wrong, Type@0, is not of type ℕ |}]

let%expect_test "a file declaring another unit is reported" =
  let _ = main_of_multi "Misnamed.mctt" in
  [%expect {| Error: Lib›Wrong: the file of the unit declares another unit |}]

let%expect_test "lib/Arithmetic.mctt" =
  let _ = main_of_lib "Arithmetic.mctt" in
  [%expect {|
    Evaluate mult 6 7 --> 42 : ℕ
    Evaluate plus (mult 3 4) (mult 2 5) --> 22 : ℕ
    Evaluate plusAssoc 1 2 3 --> ⋆ : ⊤
    Evaluate multComm 3 4 --> ⋆ : ⊤
    Evaluate multAssoc 2 3 4 --> ⋆ : ⊤
    Evaluate multDistribLeft 2 3 4 --> ⋆ : ⊤
    Evaluate multDistribRight 2 3 4 --> ⋆ : ⊤
    Evaluate cong (λ (x1 : ℕ) → mult x1 x1) 3 3 (refl 3) --> ⋆ : ⊤
    Evaluate plusCancelLeft 2 3 3 ⋆ --> ⋆ : ⊤
    Evaluate plusCancelRight 4 4 1 ⋆ --> ⋆ : ⊤
    Evaluate plusEqZero 0 0 ⋆ --> ⋆ : ⊤
    Evaluate multEqZero 2 0 ⋆ (λ (x1 : ⊥) → x1) --> ⋆ : ⊤
    |}]

let%expect_test "lib/OrderParity.mctt" =
  let _ = main_of_lib "OrderParity.mctt" in
  [%expect {|
    Evaluate leTrans 1 2 5 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate leAntisym 3 3 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate leSucc 4 --> ⋆ : ⊤
    Evaluate lePlusRight 2 3 --> ⋆ : ⊤
    Evaluate orElim (Le 5 2) (Le 2 5) ℕ (leTotal 5 2) (λ (x1 : Le 5 2) → 0)
               (λ (x2 : Le 2 5) → 1) --> 1 : ℕ
    Evaluate ltIrrefl 3 --> λ (x1 : ⊥) → Prelude›Arith›Order.LtLaws.ltIrrefl 3 x1
      : ∀ (x1 : ⊥) → ⊥
    Evaluate notLtZero 2
      --> λ (x1 : ⊥) → Prelude›Arith›Order.LtLaws.notLtZero 2 x1 : ∀ (x1 : ⊥) → ⊥
    Evaluate leb 2 5 --> 1 : ℕ
    Evaluate leb 5 2 --> 0 : ℕ
    Evaluate lebComplete 2 5 ⋆ --> ⋆ : ⊤
    Evaluate lebZero 5 2 ⋆ --> ⋆ : ⊤
    Evaluate double 7 --> 14 : ℕ
    Evaluate evenDouble 7 --> ⋆ : ⊤
    Evaluate orElim (Even 7) (Odd 7) ℕ (evenOrOdd 7) (λ (x1 : Even 7) → 0)
               (λ (x2 : Odd 7) → 1) --> 1 : ℕ
    Evaluate evenSuccOdd 4 ⋆ --> ⋆ : ⊤
    Evaluate evenPlus 4 6 ⋆ ⋆ --> ⋆ : ⊤
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
    Evaluate pred 5 --> 4 : ℕ
    Evaluate sub 10 3 --> 7 : ℕ
    Evaluate sub 3 10 --> 0 : ℕ
    Evaluate min 4 9 --> 4 : ℕ
    Evaluate max 4 9 --> 9 : ℕ
    Evaluate ack 2 3 --> 9 : ℕ
    Evaluate ack 3 3 --> 61 : ℕ
    Evaluate plusSub 6 4 --> ⋆ : ⊤
    Evaluate subSelf 7 --> ⋆ : ⊤
    Evaluate subSuccRight 9 4 --> ⋆ : ⊤
    Evaluate plusMinMax 3 8 --> ⋆ : ⊤
    Evaluate minComm 2 5 --> ⋆ : ⊤
    Evaluate maxComm 6 1 --> ⋆ : ⊤
    Evaluate ackZero 4 --> ⋆ : ⊤
    Evaluate ackTwo 5 --> ⋆ : ⊤
    Evaluate iteratePlus (λ (x1 : ℕ) → plus x1 3) 2 3 1 --> ⋆ : ⊤
    Evaluate iterateComm (λ (x1 : ℕ) → succ (succ x1)) 3 4 0 --> ⋆ : ⊤
    Evaluate Generic.compose 0l ℕ ℕ ℕ (sub 20) (λ (x1 : ℕ) → max x1 5) 2 --> 15
      : ℕ
    Evaluate Generic.const 0l ℕ ℕ 7 100 --> 7 : ℕ
    Evaluate Generic.iterate 0l ℕ (ack 1) 3 0 --> 6 : ℕ
    |}]

let%expect_test "lib/Induction.mctt" =
  let _ = main_of_lib "Induction.mctt" in
  [%expect {|
    Evaluate half 7 --> 3 : ℕ
    Evaluate half 20 --> 10 : ℕ
    Evaluate halfTwo 7 --> 3 : ℕ
    Evaluate halfTwo 20 --> 10 : ℕ
    Evaluate twoStepInd (λ (x1 : ℕ) → Even (double x1)) ⋆ ⋆
               (λ (x2 : ℕ)
                  (x3 : Even (double x2))
                 → x3)
               5 --> ⋆ : ⊤
    Evaluate caseNat (λ (x1 : ℕ) → ℕ) 0 (λ (x2 : ℕ) → x2) 9 --> 8 : ℕ
    Evaluate orElim (Eq 3 3) (Not (Eq 3 3)) ℕ (decEq 3 3) (λ (x1 : Eq 3 3) → 1)
               (λ (x2 : Not (Eq 3 3)) → 0) --> 1 : ℕ
    Evaluate orElim (Eq 3 4) (Not (Eq 3 4)) ℕ (decEq 3 4) (λ (x1 : Eq 3 4) → 1)
               (λ (x2 : Not (Eq 3 4)) → 0) --> 0 : ℕ
    Evaluate orElim (Le 2 5) (Not (Le 2 5)) ℕ (decLe 2 5) (λ (x1 : Le 2 5) → 1)
               (λ (x2 : Not (Le 2 5)) → 0) --> 1 : ℕ
    Evaluate orElim (Lt 5 5) (Not (Lt 5 5)) ℕ (decLt 5 5) (λ (x1 : Lt 5 5) → 1)
               (λ (x2 : Not (Lt 5 5)) → 0) --> 0 : ℕ
    Evaluate decStable (Eq 4 4) (decEq 4 4) (λ (x1 : Not (Eq 4 4)) → x1 ⋆) --> ⋆
      : ⊤
    Evaluate eqb 6 6 --> 1 : ℕ
    Evaluate eqb 6 2 --> 0 : ℕ
    Evaluate iffFwd (Eq (eqb 5 5) 1) (Eq 5 5) (eqbSpec 5 5) ⋆ --> ⋆ : ⊤
    Evaluate iffBwd (Eq (eqb 5 5) 1) (Eq 5 5) (eqbSpec 5 5) ⋆ --> ⋆ : ⊤
    Evaluate eqbZero 2 3 ⋆
      --> λ (x1 : ⊥) → Prelude›Arith›Decide.EqbLaws.eqbZero 2 3 ⋆ x1
      : ∀ (x1 : ⊥) → ⊥
    Evaluate existsElim (λ (x1 : ℕ) → Eq (plus x1 x1) 6) ℕ
               (existsIntro (λ (x2 : ℕ) → Eq (plus x2 x2) 6) 3 ⋆)
               (λ (x3 : ℕ)
                  (x4 : Eq (plus x3 x3) 6)
                 → x3) --> 3 : ℕ
    |}]

let%expect_test "lib/Lattice.mctt" =
  let _ = main_of_lib "Lattice.mctt" in
  [%expect {|
    Evaluate min (max 2 7) (max 5 3) --> 5 : ℕ
    Evaluate max (min 9 4) (min 6 8) --> 6 : ℕ
    Evaluate plus (sub 9 4) 4 --> 9 : ℕ
    Evaluate lePlusMono 1 2 3 4 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate lePlusCancel 3 2 5 ⋆ --> ⋆ : ⊤
    Evaluate leMultMono 2 3 2 4 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate ltTrans 1 2 4 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate ltLeTrans 1 3 3 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate leLtTrans 2 2 5 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate ltSucc 6 --> ⋆ : ⊤
    Evaluate ltPlus 4 2 --> ⋆ : ⊤
    Evaluate subLe 7 3 --> ⋆ : ⊤
    Evaluate subMonoLeft 4 6 2 ⋆ --> ⋆ : ⊤
    Evaluate subMonoRight 8 2 5 ⋆ --> ⋆ : ⊤
    Evaluate plusSubCancel 9 4 ⋆ --> ⋆ : ⊤
    Evaluate subPlusCancel 9 4 ⋆ --> ⋆ : ⊤
    Evaluate subPos 5 2 ⋆ --> ⋆ : ⊤
    Evaluate minAssoc 4 2 7 --> ⋆ : ⊤
    Evaluate maxAssoc 4 2 7 --> ⋆ : ⊤
    Evaluate minMaxAbsorb 5 3 --> ⋆ : ⊤
    Evaluate maxMinAbsorb 3 5 --> ⋆ : ⊤
    Evaluate minMaxDistrib 4 2 6 --> ⋆ : ⊤
    Evaluate maxMinDistrib 4 2 6 --> ⋆ : ⊤
    Evaluate minLe 3 8 --> ⋆ : ⊤
    Evaluate leMax 8 3 --> ⋆ : ⊤
    Evaluate leMin 2 4 5 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate maxLe 3 4 6 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate minEqLeft 3 5 ⋆ --> ⋆ : ⊤
    Evaluate maxEqRight 3 5 ⋆ --> ⋆ : ⊤
    Evaluate minMono 2 3 4 6 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate maxMono 2 3 6 7 ⋆ ⋆ --> ⋆ : ⊤
    |}]

let%expect_test "lib/Division.mctt" =
  let _ = main_of_lib "Division.mctt" in
  [%expect {|
    Evaluate div 17 5 --> 3 : ℕ
    Evaluate mod 17 5 --> 2 : ℕ
    Evaluate div 17 0 --> 0 : ℕ
    Evaluate mod 17 0 --> 17 : ℕ
    Evaluate div 20 4 --> 5 : ℕ
    Evaluate mod 20 4 --> 0 : ℕ
    Evaluate divSucc 17 3 --> 4 : ℕ
    Evaluate modSucc 17 3 --> 1 : ℕ
    Evaluate divZeroDivisor 17 --> ⋆ : ⊤
    Evaluate modZeroDivisor 17 --> ⋆ : ⊤
    Evaluate divZero 4 --> ⋆ : ⊤
    Evaluate modZero 0 --> ⋆ : ⊤
    Evaluate divModSpec 17 4 --> ⋆ : ⊤
    Evaluate modLt 17 4 --> ⋆ : ⊤
    Evaluate modSmall 3 4 ⋆ --> ⋆ : ⊤
    Evaluate divSmall 3 4 ⋆ --> ⋆ : ⊤
    Evaluate modSelf 6 --> ⋆ : ⊤
    Evaluate modPlusDivisor 9 4 --> ⋆ : ⊤
    Evaluate modOne 7 --> ⋆ : ⊤
    Evaluate divOne 7 --> ⋆ : ⊤
    Evaluate Divides 3 12 --> ⊤ : Type@0
    Evaluate Divides 3 13 --> ⊥ : Type@0
    Evaluate Divides 0 0 --> ⊤ : Type@0
    Evaluate Divides 0 5 --> ⊥ : Type@0
    Evaluate zeroDivides 0 ⋆ --> ⋆ : ⊤
    Evaluate dividesRefl 5 --> ⋆ : ⊤
    Evaluate dividesZero 4 --> ⋆ : ⊤
    Evaluate oneDivides 9 --> ⋆ : ⊤
    Evaluate dividesPlus 3 6 9 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate dividesMult 3 4 --> ⋆ : ⊤
    Evaluate evenDividesTwo 8 ⋆ --> ⋆ : ⊤
    Evaluate dividesTwoEven 10 ⋆ --> ⋆ : ⊤
    |}]

let%expect_test "lib/Vectors.mctt" =
  let _ = main_of_lib "Vectors.mctt" in
  [%expect {|
    Evaluate sumVec 3 oneTwoThree --> 6 : ℕ
    Evaluate NV.head 2 oneTwoThree --> 1 : ℕ
    Evaluate NV.nth 3 oneTwoThree 2 ⋆ --> 3 : ℕ
    Evaluate sumVec 2 (NV.tail 2 oneTwoThree) --> 5 : ℕ
    Evaluate sumVec 3 (NV.map ℕ square 3 oneTwoThree) --> 14 : ℕ
    Evaluate NV.nth 5 (NV.append 3 2 oneTwoThree fourFive) 3 ⋆ --> 4 : ℕ
    Evaluate sumVec 5 (NV.append 3 2 oneTwoThree fourFive) --> 15 : ℕ
    Evaluate sumVec 4 (NV.replicate 4 6) --> 24 : ℕ
    Evaluate NV.foldr ℕ (λ (x1 : ℕ)
                           (x2 : ℕ)
                          → succ x2) 0 5
               (NV.append 3 2 oneTwoThree fourFive) --> 5 : ℕ
    Evaluate sumReplicate 4 6 --> ⋆ : ⊤
    Evaluate sumAppend 3 2 oneTwoThree fourFive --> ⋆ : ⊤
    Evaluate nthMap 0l ℕ square 3 oneTwoThree 1 ⋆ --> ⋆ : ⊤
    Evaluate nthReplicate 4 6 3 ⋆ --> ⋆ : ⊤
    Evaluate nthAppendLeft 3 2 oneTwoThree fourFive 1 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate nthAppendRight 3 2 oneTwoThree fourFive 1 ⋆ --> ⋆ : ⊤
    Evaluate NV.nth 4 (NV.tabulate square 4) 3 ⋆ --> 9 : ℕ
    Evaluate sumVec 4 (NV.tabulate square 4) --> 14 : ℕ
    Evaluate sumVec 2 (NV.zipWith ℕ ℕ mult 2 (NV.take 2 1 oneTwoThree) fourFive)
      --> 14 : ℕ
    Evaluate NV.foldl ℕ (λ (x1 : ℕ)
                           (x2 : ℕ)
                          → plus (mult 10 x1) x2) 0 3
               oneTwoThree --> 123 : ℕ
    Evaluate NV.last 4 oneToFive --> 5 : ℕ
    Evaluate NV.last 3 (NV.snoc 3 oneTwoThree 7) --> 7 : ℕ
    Evaluate sumVec 4 (NV.init 4 oneToFive) --> 10 : ℕ
    Evaluate NV.head 4 (NV.reverse 5 oneToFive) --> 5 : ℕ
    Evaluate NV.last 4 (NV.reverse 5 oneToFive) --> 1 : ℕ
    Evaluate NV.nth 3 (NV.take 3 2 oneToFive) 2 ⋆ --> 3 : ℕ
    Evaluate NV.nth 2 (NV.drop 3 2 oneToFive) 0 ⋆ --> 4 : ℕ
    Evaluate NV.allb (λ (x1 : ℕ) → x1) 5 oneToFive --> 1 : ℕ
    Evaluate NV.allb (λ (x1 : ℕ) → x1) 4 (NV.cons 3 0 oneTwoThree) --> 0 : ℕ
    Evaluate NV.anyb (λ (x1 : ℕ) → x1) 3 (NV.snoc 2 (NV.replicate 2 0) 9) --> 1
      : ℕ
    Evaluate NV.anyb (λ (x1 : ℕ) → x1) 3 (NV.replicate 3 0) --> 0 : ℕ
    Evaluate nthTabulate square 4 3 ⋆ --> ⋆ : ⊤
    Evaluate nthZipWith 0l ℕ ℕ mult 2 (NV.take 2 1 oneTwoThree) fourFive 1 ⋆
      --> ⋆ : ⊤
    Evaluate nthReverse 5 oneToFive 1 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate takeAppend 3 2 oneTwoThree fourFive 2 ⋆ --> ⋆ : ⊤
    Evaluate dropAppend 3 2 oneTwoThree fourFive 1 ⋆ --> ⋆ : ⊤
    Evaluate appendTakeDrop 3 2 oneToFive 4 ⋆ --> ⋆ : ⊤
    Evaluate lastSnoc 3 oneTwoThree 7 --> ⋆ : ⊤
    Evaluate sumMapPlus 2 3 oneTwoThree --> ⋆ : ⊤
    Evaluate sumMapScale 3 3 oneTwoThree --> ⋆ : ⊤
    Evaluate sumZipWithPlus 2 fourFive (NV.tail 2 oneTwoThree) --> ⋆ : ⊤
    Evaluate foldlPlus 4 3 oneTwoThree --> ⋆ : ⊤
    Evaluate sumSnoc 3 oneTwoThree 7 --> ⋆ : ⊤
    Evaluate sumInitLast 4 oneToFive --> ⋆ : ⊤
    Evaluate sumReverse 5 oneToFive --> ⋆ : ⊤
    Evaluate sumTabulate square 4 --> ⋆ : ⊤
    Evaluate allbSound 0l ℕ (λ (x1 : ℕ) → x1) 5 oneToFive ⋆ 2 ⋆ --> ⋆ : ⊤
    Evaluate allbComplete 0l ℕ (λ (x1 : ℕ) → x1) 4 (NV.replicate 4 3)
               (λ (x2 : ℕ)
                  (x3 : Lt x2 4)
                 → ⋆) --> ⋆ : ⊤
    Evaluate anybSound 0l ℕ (λ (x1 : ℕ) → x1) 3 (NV.snoc 2 (NV.replicate 2 0) 9)
               ⋆
               ℕ
               (λ (x2 : ℕ)
                  (x3 : Lt x2 3)
                  (x4 : Lt 0 (NV.snoc 2 (NV.replicate 2 0) 9 x2 x3))
                 → x2) --> 2 : ℕ
    |}]

let%expect_test "lib/Powers.mctt" =
  let _ = main_of_lib "Powers.mctt" in
  [%expect {|
    Evaluate pow 2 10 --> 1024 : ℕ
    Evaluate pow 3 4 --> 81 : ℕ
    Evaluate pow 0 0 --> 1 : ℕ
    Evaluate sumTo NatFun.id 11 --> 55 : ℕ
    Evaluate sumTo (λ (x1 : ℕ) → mult x1 x1) 6 --> 55 : ℕ
    Evaluate factorial 5 --> 120 : ℕ
    Evaluate factorial 0 --> 1 : ℕ
    Evaluate powZero 7 --> ⋆ : ⊤
    Evaluate powOne 9 --> ⋆ : ⊤
    Evaluate onePow 6 --> ⋆ : ⊤
    Evaluate powPlus 2 1 3 --> ⋆ : ⊤
    Evaluate powMult 2 2 2 --> ⋆ : ⊤
    Evaluate powMultBase 2 2 2 --> ⋆ : ⊤
    Evaluate sumToPlus NatFun.id (λ (x1 : ℕ) → mult x1 x1) 4 --> ⋆ : ⊤
    Evaluate sumToScale 3 NatFun.id 4 --> ⋆ : ⊤
    Evaluate sumToConst 4 5 --> ⋆ : ⊤
    Evaluate gauss 4 --> ⋆ : ⊤
    Evaluate sumOdd 4 --> ⋆ : ⊤
    Evaluate factSucc 3 --> ⋆ : ⊤
    Evaluate factPos 4 --> ⋆ : ⊤
    Evaluate factLeSucc 3 --> ⋆ : ⊤
    Evaluate lePowFact 3 --> ⋆ : ⊤
    |}]

let%expect_test "lib/Streams.mctt" =
  let _ = main_of_lib "Streams.mctt" in
  [%expect {|
    Evaluate sumVec 6 (S.take 6 nats) --> 15 : ℕ
    Evaluate V.nth 0l ℕ 5 (S.take 5 evens) 4 ⋆ --> 8 : ℕ
    Evaluate S.nth odds 6 --> 13 : ℕ
    Evaluate sumVec 5 (S.take 5 squares) --> 30 : ℕ
    Evaluate S.nth fibs 10 --> 55 : ℕ
    Evaluate S.nth lucas 8 --> 47 : ℕ
    Evaluate sumVec 10 (S.take 10 fibs) --> 88 : ℕ
    Evaluate S.nth (S.scan ℕ plus 0 squares) 5 --> 30 : ℕ
    Evaluate S.nth (S.interleave evens odds) 7 --> 7 : ℕ
    Evaluate S.nth (S.drop 4 squares) 3 --> 49 : ℕ
    Evaluate S.nth (S.zipWith ℕ ℕ plus evens odds) 4 --> 17 : ℕ
    Evaluate S.head (S.tail (S.cons 9 nats)) --> 0 : ℕ
    Evaluate S.nth (S.const 3) 100 --> 3 : ℕ
    Evaluate headCons 9 nats --> ⋆ : ⊤
    Evaluate tailCons 9 squares 3 --> ⋆ : ⊤
    Evaluate nthConst 3 100 --> ⋆ : ⊤
    Evaluate nthMap square nats 4 --> ⋆ : ⊤
    Evaluate nthZipWith plus evens odds 3 --> ⋆ : ⊤
    Evaluate nthIterate (λ (x1 : ℕ) → succ (succ x1)) 1 4 --> ⋆ : ⊤
    Evaluate tailIterate (λ (x1 : ℕ) → succ (succ x1)) 1 4 --> ⋆ : ⊤
    Evaluate nthNats 12 --> ⋆ : ⊤
    Evaluate nthDrop 3 squares 1 --> ⋆ : ⊤
    Evaluate nthTake 5 squares 3 ⋆ --> ⋆ : ⊤
    Evaluate scanSum squares 4 --> ⋆ : ⊤
    Evaluate scanSum fibs 6 --> ⋆ : ⊤
    Evaluate nthInterleaveEven 3 evens odds --> ⋆ : ⊤
    Evaluate nthInterleaveOdd 3 evens odds --> ⋆ : ⊤
    Evaluate sumToShift squares 3 --> ⋆ : ⊤
    Evaluate sumTake 5 nats --> ⋆ : ⊤
    |}]

let%expect_test "lib/Combinatorics.mctt" =
  let _ = main_of_lib "Combinatorics.mctt" in
  [%expect {|
    Evaluate choose 0 0 --> 1 : ℕ
    Evaluate choose 1 0 --> 1 : ℕ
    Evaluate choose 1 1 --> 1 : ℕ
    Evaluate choose 2 0 --> 1 : ℕ
    Evaluate choose 2 1 --> 2 : ℕ
    Evaluate choose 2 2 --> 1 : ℕ
    Evaluate choose 3 0 --> 1 : ℕ
    Evaluate choose 3 1 --> 3 : ℕ
    Evaluate choose 3 2 --> 3 : ℕ
    Evaluate choose 3 3 --> 1 : ℕ
    Evaluate choose 4 0 --> 1 : ℕ
    Evaluate choose 4 1 --> 4 : ℕ
    Evaluate choose 4 2 --> 6 : ℕ
    Evaluate choose 4 3 --> 4 : ℕ
    Evaluate choose 4 4 --> 1 : ℕ
    Evaluate choose 5 0 --> 1 : ℕ
    Evaluate choose 5 1 --> 5 : ℕ
    Evaluate choose 5 2 --> 10 : ℕ
    Evaluate choose 5 3 --> 10 : ℕ
    Evaluate choose 5 4 --> 5 : ℕ
    Evaluate choose 5 5 --> 1 : ℕ
    Evaluate choose 6 0 --> 1 : ℕ
    Evaluate choose 6 1 --> 6 : ℕ
    Evaluate choose 6 2 --> 15 : ℕ
    Evaluate choose 6 3 --> 20 : ℕ
    Evaluate choose 6 4 --> 15 : ℕ
    Evaluate choose 6 5 --> 6 : ℕ
    Evaluate choose 6 6 --> 1 : ℕ
    Evaluate choose 3 5 --> 0 : ℕ
    Evaluate sumTo (choose 6) 7 --> 64 : ℕ
    Evaluate fib 0 --> 0 : ℕ
    Evaluate fib 1 --> 1 : ℕ
    Evaluate fib 10 --> 55 : ℕ
    Evaluate sumTo fib 10 --> 88 : ℕ
    Evaluate chooseZero 5 --> ⋆ : ⊤
    Evaluate chooseSelf 5 --> ⋆ : ⊤
    Evaluate chooseOne 5 --> ⋆ : ⊤
    Evaluate chooseOver 3 5 ⋆ --> ⋆ : ⊤
    Evaluate pascal 4 2 --> ⋆ : ⊤
    Evaluate chooseSymm 2 3 --> ⋆ : ⊤
    Evaluate chooseSymmSub 5 2 ⋆ --> ⋆ : ⊤
    Evaluate rowSum 4 --> ⋆ : ⊤
    Evaluate fibSucc 5 --> ⋆ : ⊤
    Evaluate fibPos 5 --> ⋆ : ⊤
    Evaluate fibMono 5 --> ⋆ : ⊤
    Evaluate fibMonoPlus 2 4 --> ⋆ : ⊤
    Evaluate fibSum 5 --> ⋆ : ⊤
    Evaluate fibPlus 3 2 --> ⋆ : ⊤
    |}]

let%expect_test "lib/NumberTheory.mctt" =
  let _ = main_of_lib "NumberTheory.mctt" in
  [%expect {|
    Evaluate gcd 12 18 --> 6 : ℕ
    Evaluate gcd 17 5 --> 1 : ℕ
    Evaluate gcd 0 9 --> 9 : ℕ
    Evaluate gcd 9 0 --> 9 : ℕ
    Evaluate nthPrime 0 --> 2 : ℕ
    Evaluate nthPrime 1 --> 3 : ℕ
    Evaluate nthPrime 2 --> 5 : ℕ
    Evaluate nthPrime 3 --> 7 : ℕ
    Evaluate nthPrime 4 --> 11 : ℕ
    Evaluate nthPrime 5 --> 13 : ℕ
    Evaluate nthPrime 6 --> 17 : ℕ
    Evaluate nthPrime 7 --> 19 : ℕ
    Evaluate nthPrime 8 --> 23 : ℕ
    Evaluate nthPrime 9 --> 29 : ℕ
    Evaluate nthPrime 10 --> 31 : ℕ
    Evaluate sumTo isPrime 30 --> 10 : ℕ
    Evaluate sumTo (λ (x1 : ℕ) → mult x1 (isPrime x1)) 30 --> 129 : ℕ
    Evaluate smallestDivisor 91 --> 7 : ℕ
    Evaluate smallestDivisor 29 --> 29 : ℕ
    Evaluate Prime 29 --> ⊤ : Type@0
    Evaluate Prime 27 --> ⊥ : Type@0
    Evaluate gcdZeroLeft 5 --> ⋆ : ⊤
    Evaluate gcdZeroRight 5 --> ⋆ : ⊤
    Evaluate gcdSelf 7 --> ⋆ : ⊤
    Evaluate gcdOneRight 9 --> ⋆ : ⊤
    Evaluate gcdDividesLeft 6 9 --> ⋆ : ⊤
    Evaluate gcdDividesRight 6 9 --> ⋆ : ⊤
    Evaluate gcdGreatest 2 8 12 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate gcdComm 6 9 --> ⋆ : ⊤
    Evaluate dividesMultLeft 3 6 2 ⋆ --> ⋆ : ⊤
    Evaluate dividesPlusCancel 3 6 9 ⋆ ⋆ --> ⋆ : ⊤
    Evaluate twoPrime --> ⋆ : ⊤
    Evaluate sevenPrime --> ⋆ : ⊤
    Evaluate nineNotPrime
      --> λ (x1 : ⊥) → Prelude›Arith›Prime.Facts.nineNotPrime x1 : ∀ (x1 : ⊥) → ⊥
    Evaluate smallestDivisorDivides 15 --> ⋆ : ⊤
    Evaluate primeGeTwo 13 ⋆ --> ⋆ : ⊤
    Evaluate primeSmallestDivisor 13 ⋆ --> ⋆ : ⊤
    |}]

(** Module forms *)

let%expect_test "a local module with parameters" =
  let _ = main_of_body "eval let module X (n : Nat) where def f : Nat := n end end in X.f 3 end" in
  [%expect {|
    Evaluate let module M1 (x1 : ℕ) where
                   def f : ℕ ≔
                     x1
                   end
                 end in M1.f 3 end --> 3 : ℕ
    |}]

let%expect_test "a local alias of a submodule" =
  let _ =
    main_of_body
      "eval let module X (n : Nat) where module V where def f : Nat := n end end end in \
       let module P := X.V in P.f 3 end end"
  in
  [%expect {|
    Evaluate let module M1 (x1 : ℕ) where
                   module V where
                     def f : ℕ ≔
                       x1
                     end
                   end
                 end;
                 module M2 ≔ M1.V
             in M2.f 3
             end --> 3 : ℕ
    |}]

let%expect_test "beta substitutes into a local module" =
  let _ = main_of_body "eval (fun (n : Nat) -> let module X where def f : Nat := n end end in X.f end) 3" in
  [%expect {|
    Evaluate (λ (x1 : ℕ)
               → let module M1 where
                       def f : ℕ ≔
                         x1
                       end
                     end in M1.f end)
               3 --> 3 : ℕ
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
                   def x : ℕ ≔
                     0
                   end
                   module N (A2 : Type@0) where
                     def c : ∀ (x1 : A2) → A2 ≔
                       λ (x2 : A2) → x2
                     end
                   end
                 end
             in M1.N.c ℕ ℕ 3
             end --> 3 : ℕ
    |}]

let%expect_test "a module alias with parameters" =
  let _ =
    main_of_body
      "module M (A : Type@0) where def id (x : A) : A := x end end \
       module P (B : Type@0) := M B \
       eval P.id Nat 4"
  in
  [%expect {| Evaluate P.id ℕ 4 --> 4 : ℕ |}]

let%expect_test "a dotted module declaration" =
  let _ = main_of_body "module A.B (n : Nat) where def f : Nat := succ n end end eval A.B.f 1" in
  [%expect {| Evaluate A.B.f 1 --> 2 : ℕ |}]

let%expect_test "a local body with an import" =
  let _ =
    main_of_body
      "eval let module L where module N where def y : Nat := 5 end end \
       open N use (y) def z : Nat := succ y end end in L.z end"
  in
  [%expect {|
    Evaluate let module M1 where
                   module N where
                     def y : ℕ ≔
                       5
                     end
                   end
                   private def y : ℕ ≔
                     N.y
                   end
                   def z : ℕ ≔
                     succ y
                   end
                 end
             in M1.z
             end --> 6 : ℕ
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
                     def y : ℕ ≔
                       5
                     end
                     def w : ℕ ≔
                       1
                     end
                   end
                   private def y : ℕ ≔
                     N.y
                   end
                   private def w : let x1 : ℕ ≔ 5 in ℕ end ≔
                     N.w
                   end
                   def z : ℕ ≔
                     y
                   end
                   def v : ℕ ≔
                     w
                   end
                 end
             in M1.v
             end --> 1 : ℕ
    |}]

let%expect_test "an import of a local module alias" =
  let _ =
    main_of_body
      "module M where def y : Nat := 7 end end module P := M open P as Q eval Q.y"
  in
  [%expect {| Evaluate Q.y --> 7 : ℕ |}]

(** Imports declare definitions *)

let%expect_test "use declares a private definition" =
  let _ = main_of_multi_string "import Lib::Num use (double) module X where eval double 3 end" in
  [%expect {| Evaluate double 3 --> 6 : ℕ |}]

let%expect_test "use as renames the definition" =
  let _ = main_of_multi_string "import Lib::Num use (double as dbl) module X where eval dbl 3 end" in
  [%expect {| Evaluate dbl 3 --> 6 : ℕ |}]

let%expect_test "export declares a public definition" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where module M where import Lib::Num export (double) end \
       eval M.double 3 end"
  in
  [%expect {| Evaluate M.double 3 --> 6 : ℕ |}]

let%expect_test "export as renames the public definition" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where module M where import Lib::Num export (double as dbl) end \
       eval M.dbl 3 end"
  in
  [%expect {| Evaluate M.dbl 3 --> 6 : ℕ |}]

let%expect_test "a used definition is private to its module" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where module M where import Lib::Num use (double) end \
       eval M.double 3 end"
  in
  [%expect {| Error: X.M.double is private |}]

let%expect_test "use of a submodule declares a private alias" =
  let _ = main_of_multi_string "import Lib::Num use (Ops) module X where eval Ops.pred 3 end" in
  [%expect {| Evaluate Ops.pred 3 --> 2 : ℕ |}]

let%expect_test "export of a submodule declares a public alias" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where module M where import Lib::Num export (Ops as P) end \
       eval M.P.pred 3 end"
  in
  [%expect {| Evaluate M.P.pred 3 --> 2 : ℕ |}]

let%expect_test "import as declares a private alias" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where module M where import Lib::Num.Ops as O \
       def z : Nat := O.pred 3 end end eval M.z end"
  in
  [%expect {| Evaluate M.z --> 2 : ℕ |}]

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
  [%expect {| Evaluate M.z --> 5 : ℕ |}]

let%expect_test "an import with arguments and export as" =
  let _ =
    main_of_multi_string
      "import Lib::Priv module X where module M where import Lib::Priv.F 4 export (g as h) end \
       eval M.h end"
  in
  [%expect {| Evaluate M.h --> 4 : ℕ |}]

let%expect_test "a member used and exported under two names is rejected" =
  let _ =
    main_of_multi_string
      "import Lib::Priv module X where import Lib::Priv.F 4 use (g) export (g as h) end"
  in
  [%expect {| Error: g is used and exported |}]

let%expect_test "an imported member may have a private type" =
  let _ = main_of_multi_string "import Lib::Priv.Sub use (t) module X where eval t end" in
  [%expect {| Evaluate t --> 7 : ℕ |}]

let%expect_test "a used name that is not a member is rejected" =
  let _ = main_of_multi_string "import Lib::Num use (q) module X where end" in
  [%expect {| Error: Lib›Num.q is not a member |}]

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
  [%expect {| Error: Lib›Priv.s is private |}]

let%expect_test "a local use, use as and export" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num use (double as dbl) \
       export (Ops) def t : Nat := dbl 2 end end in L.Ops.pred L.t end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   private def dbl : ∀ (x1 : ℕ) → ℕ ≔
                     Lib›Num.double
                   end
                   module Ops ≔ Lib›Num.Ops
                   def t : ℕ ≔
                     dbl 2
                   end
                 end
             in M1.Ops.pred M1.t
             end --> 3 : ℕ
    |}]

let%expect_test "a local export as" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num export (double as dbl) \
       end in L.dbl 2 end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   def dbl : ∀ (x1 : ℕ) → ℕ ≔
                     Lib›Num.double
                   end
                 end
             in M1.dbl 2
             end --> 4 : ℕ
    |}]

let%expect_test "a local submodule use" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num use (Ops) \
       def t : Nat := Ops.pred 5 end end in L.t end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   private module Ops ≔ Lib›Num.Ops
                   def t : ℕ ≔
                     Ops.pred 5
                   end
                 end
             in M1.t
             end --> 4 : ℕ
    |}]

let%expect_test "a local import as" =
  let _ =
    main_of_multi_string
      "import Lib::Num module X where eval let module L where open Lib::Num as W \
       def t : Nat := W.double 1 end end in L.t end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   private module W ≔ Lib›Num
                   def t : ℕ ≔
                     W.double 1
                   end
                 end
             in M1.t
             end --> 2 : ℕ
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
  [%expect {| Error: Lib›Num.q is not a member |}]

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
                   private def s : ℕ ≔
                     1
                   end
                   def t : ℕ ≔
                     succ s
                   end
                 end
             in M1.t
             end --> 2 : ℕ
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
                     private def u : ℕ ≔
                       1
                     end
                     def v : ℕ ≔
                       u
                     end
                   end
                 end
             in M1.N.v
             end --> 1 : ℕ
    |}]

let%expect_test "a private member of a local submodule is rejected outside it" =
  let _ =
    main_of_body
      "eval let module L where module N where private def u : Nat := 1 end end end in L.N.u end"
  in
  [%expect {| Error: N.u is private in a local module, but it is used outside it |}]

let%expect_test "a private global member is rejected through a local alias" =
  let _ = main_of_multi_string "import Lib::Priv module X where eval let module L := Lib::Priv in L.s end end" in
  [%expect {| Error: Lib›Priv.s is private |}]

let%expect_test "a public global member is used through a local alias" =
  let _ = main_of_multi_string "import Lib::Priv module X where eval let module L := Lib::Priv in L.pub end end" in
  [%expect {| Evaluate let module M1 ≔ Lib›Priv in M1.pub end --> 8 : ℕ |}]

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
    Evaluate M.p --> 0 : ℕ
    Evaluate M.N.t --> 0 : ℕ
    |}]

let%expect_test "a private member of another unit is not used in a def" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where def x : Nat := P.s end end" in
  [%expect {| Error: Lib›Priv.s is private |}]

let%expect_test "a private member of another unit is not evaluated" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where eval P.s end" in
  [%expect {| Error: Lib›Priv.s is private |}]

let%expect_test "a private member of another unit is not named by its path" =
  let _ = main_of_multi_string "import Lib::Priv module X where eval Lib::Priv.s end" in
  [%expect {| Error: Lib›Priv.s is private |}]

let%expect_test "a private member of another unit is not used in a module body" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where module M where def y : Nat := P.s end end end" in
  [%expect {| Error: Lib›Priv.s is private |}]

let%expect_test "a private member of another unit is not used in module parameters" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where module M (x : P.T) where end end" in
  [%expect {| Error: Lib›Priv.T is private |}]

let%expect_test "a private member of another unit is not used in an alias" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where module A := P.F P.s end" in
  [%expect {| Error: Lib›Priv.s is private |}]

let%expect_test "a private member of another unit is not imported by use" =
  let _ = main_of_multi_string "import Lib::Priv use (s) module X where end" in
  [%expect {| Error: Lib›Priv.s is private |}]

let%expect_test "a private member of another unit is not imported by use in a local module" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where module L where open P use (s) end end" in
  [%expect {| Error: Lib›Priv.s is private |}]

let%expect_test "a private member is not reached through an alias declared outside" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where module Q := P.Sub eval Q.u end" in
  [%expect {| Error: Lib›Priv.Sub.u is private |}]

let%expect_test "a private member is not reached through an alias in its unit" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where eval P.A.u end" in
  [%expect {| Error: Lib›Priv.Sub.u is private |}]

let%expect_test "a public definition naming a private one is used from another unit" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where eval P.pub eval P.Sub.t end" in
  [%expect {|
    Evaluate P.pub --> 8 : ℕ
    Evaluate P.Sub.t --> 7 : ℕ
    |}]

let%expect_test "a module is applied to its parameters one at a time" =
  let _ = main_of_body "module F (A : Type@0) (f : forall (x : A) -> A) where def ap : forall (x : A) -> A := fun (x : A) -> f (f x) end end module G := F Nat module H := G (fun (x : Nat) -> succ x) eval H.ap 1 eval (F Nat (fun (x : Nat) -> succ x)).ap 3" in
  [%expect {|
    Evaluate H.ap 1 --> 3 : ℕ
    Evaluate (F ℕ (λ (x1 : ℕ) → succ x1)).ap 3 --> 5 : ℕ
    |}]

let%expect_test "a module is not applied to more arguments than it has parameters" =
  let _ = main_of_body "module F (A : Type@0) where def a : Type@0 := A end end module G := F Nat Nat" in
  [%expect {| Error: ill-formed module expression for module G |}]

let%expect_test "a member of a module applied to too many arguments is rejected" =
  let _ = main_of_body "module F (A : Type@0) where def a : Type@0 := A end end eval (F Nat Nat).a" in
  [%expect {| Error: (F ℕ ℕ).a has no inferable type |}]

let%expect_test "a module argument is checked against the outermost parameter" =
  let _ = main_of_body "module F (A : Type@0) where def a : Type@0 := A end end module G := F 0" in
  [%expect {| Error: ill-formed module expression for module G |}]

let%expect_test "the modifiers of a definition are written in either order" =
  let _ = main_of_body "module M where abstract private def s : Nat := 1 end private abstract def u : Nat := 2 end def t : Nat := s end end eval M.t" in
  [%expect {| Evaluate M.t --> M.s : ℕ |}]

let%expect_test "an abstract private definition is private" =
  let _ = main_of_body "module M where abstract private def s : Nat := 1 end end eval M.s" in
  [%expect {| Error: Test.M.s is private |}]

let%expect_test "a private module is used inside its unit" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where eval P.viaHidden end" in
  [%expect {| Evaluate P.viaHidden --> 2 : ℕ |}]

let%expect_test "a member of a private module of another unit is rejected" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where eval P.Hidden.h end" in
  [%expect {| Error: Lib›Priv.Hidden is private |}]

let%expect_test "a private module of another unit is not aliased" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where module Q := P.Hidden end" in
  [%expect {| Error: Lib›Priv.Hidden is private |}]

let%expect_test "a private module alias of another unit is rejected" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where eval P.PA.t end" in
  [%expect {| Error: Lib›Priv.PA is private |}]

let%expect_test "a private module of another unit is not imported by use" =
  let _ = main_of_multi_string "import Lib::Priv use (Hidden) module X where end" in
  [%expect {| Error: Lib›Priv.Hidden is private |}]

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
                 abstract def f : ℕ ≔
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
  [%expect {| Error: the unit Prelude›Arith›MinMax is not imported |}]

let%expect_test "a local import of a unit imported at the top level" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude::Arith::MinMax module LocalImp where eval let module L where \
       open Prelude::Arith::MinMax use (max) def m : Nat := max 2 3 end end in L.m end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   private def max : ∀ (x1 : ℕ)
                                       (x2 : ℕ)
                                       → ℕ ≔
                     Prelude›Arith›MinMax.max
                   end
                   def m : ℕ ≔
                     max 2 3
                   end
                 end
             in M1.m
             end --> 3 : ℕ
    |}]

let%expect_test "an eval is rejected in a local body" =
  let _ = main_of_body "eval let module X where eval 0 end in 0 end" in
  [%expect {| Error: eval is not allowed in a local module |}]

let%expect_test "a local module does not escape its let" =
  let _ = main_of_body "eval let module X where def f : Nat := 0 end end in X end" in
  [%expect {|
    Error: let module M1 where
                 def f : ℕ ≔
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
      module expression after "≔".
    |}]

let%expect_test "lib/Algebra.mctt" =
  let _ = main_of_lib "Algebra.mctt" in
  [%expect {|
    Evaluate Additive.pow 3 4 --> 12 : ℕ
    Evaluate Multiplicative.pow 2 5 --> 32 : ℕ
    Evaluate Maximum.pow 7 3 --> 7 : ℕ
    Evaluate Composition.pow (λ (x1 : ℕ) → succ (succ x1)) 5 0 --> 10 : ℕ
    Evaluate Sums.pow 6 3 --> 18 : ℕ
    Evaluate Unfold.additivePow 3 4 --> ⋆ : ⊤
    Evaluate Scaling.multPlusRight 2 3 2 --> ⋆ : ⊤
    Evaluate Scaling.multAssocPow 2 3 2 --> ⋆ : ⊤
    Evaluate Scaling.multPlusLeft 2 3 4 --> ⋆ : ⊤
    Evaluate Exponents.powPlus 2 1 3 --> ⋆ : ⊤
    Evaluate Exponents.powMult 2 2 2 --> ⋆ : ⊤
    Evaluate Exponents.powOfProduct 2 2 2 --> ⋆ : ⊤
    Evaluate Exponents.fourthPower 2 --> ⋆ : ⊤
    Evaluate Iteration.iterPlus (λ (x1 : ℕ) → succ x1) 2 3 4 --> ⋆ : ⊤
    Evaluate maxPowSucc 5 3 --> ⋆ : ⊤
    |}]

let%expect_test "lib/Polynomials.mctt" =
  let _ = main_of_lib "Polynomials.mctt" in
  [%expect {|
    Evaluate At.horner 2 (cubic 1 2 3 4) 4 --> 49 : ℕ
    Evaluate At.naive 2 (cubic 1 2 3 4) 4 --> 49 : ℕ
    Evaluate let module M1 (x1 : Coeffs) where
                   private def max : ∀ (x2 : ℕ)
                                       (x3 : ℕ)
                                       → ℕ ≔
                     Prelude›Arith›MinMax.max
                   end
                   def value : ∀ (x4 : ℕ) → ℕ ≔
                     λ (x5 : ℕ) → At.horner x5 x1 4
                   end
                   def total : ∀ (x6 : ℕ) → ℕ ≔
                     λ (x7 : ℕ) → sumTo value x7
                   end
                   def peak : ∀ (x8 : ℕ) → ℕ ≔
                     λ (x9 : ℕ)
                       → rec x9 return x10 . ℕ
                         | zero ⇒ 0
                         | succ x11, x12 ⇒ max (value x11) x12
                         end
                   end
                 end
             in plus (M1.total (cubic 1 1 0 0) 4) (M1.peak (cubic 0 0 1 0) 5)
             end --> 26 : ℕ
    Evaluate At.hornerNaive 2 (cubic 1 0 1 0) 4 --> ⋆ : ⊤
    Evaluate At.hornerNaive 3 (cubic 2 1 0 0) 4 --> ⋆ : ⊤
    Evaluate hornerAtOne (cubic 3 1 4 1) 4 --> ⋆ : ⊤
    |}]

let%expect_test "lib/Binary.mctt" =
  let _ = main_of_lib "Binary.mctt" in
  [%expect {|
    Evaluate half 13 --> 6 : ℕ
    Evaluate bit 13 --> 1 : ℕ
    Evaluate bits 13 0 --> 1 : ℕ
    Evaluate bits 13 1 --> 0 : ℕ
    Evaluate bits 13 2 --> 1 : ℕ
    Evaluate bits 13 3 --> 1 : ℕ
    Evaluate fromBits (bits 13) 4 --> 13 : ℕ
    Evaluate bitCount 13 --> 3 : ℕ
    Evaluate bitCount 255 --> 8 : ℕ
    Evaluate bitCount 256 --> 1 : ℕ
    Evaluate fromBits oneZeroOneOne 4 --> 13 : ℕ
    Evaluate powFast 3 5 --> 243 : ℕ
    Evaluate powFast 2 10 --> 1024 : ℕ
    Evaluate fromBitsDouble 6 3 --> ⋆ : ⊤
    Evaluate powFastDouble 2 2 --> ⋆ : ⊤
    Evaluate powFastDouble 3 1 --> ⋆ : ⊤
    |}]

let%expect_test "lib/Groups.mctt" =
  let _ = main_of_lib "Groups.mctt" in
  [%expect {|
    Evaluate negative minusThree --> 1 : ℕ
    Evaluate magnitude minusThree --> 3 : ℕ
    Evaluate negative (Additive.Base.pow minusThree 4) --> 1 : ℕ
    Evaluate magnitude (Additive.Base.pow minusThree 4) --> 12 : ℕ
    Evaluate negative (minus (ofNat 4) (ofNat 9)) --> 1 : ℕ
    Evaluate magnitude (minus (ofNat 4) (ofNat 9)) --> 5 : ℕ
    Evaluate solve (ofNat 2) (ofNat 5) (ofNat 3) ⋆ --> ⋆ : ⊤
    Evaluate solve minusThree (ofNat 1) (pair 4 0) ⋆ --> ⋆ : ⊤
    Evaluate negateMinus (ofNat 3) minusThree --> ⋆ : ⊤
    Evaluate Multiples.multipleNegate minusThree 3 --> ⋆ : ⊤
    Evaluate Multiples.multipleAdd minusThree (ofNat 5) 2 --> ⋆ : ⊤
    Evaluate Additive.Laws.invOp (ofNat 1) minusThree --> ⋆ : ⊤
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
    Evaluate M.a 1 --> 2 : ℕ
    Evaluate M.b 1 --> M.b 1 : ℕ
    Evaluate M.c 1 --> M.c 1 : ℕ
    Evaluate M.h --> succ (M.b (M.c (M.d (M.e 2)))) : ℕ
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
    Evaluate M.t --> M.b : ℕ
    Evaluate M.u --> M.d : ℕ
    Evaluate M.v --> M.e : ℕ
    Evaluate M.w --> M.f : ℕ
    |}];
  let _ =
    main_of_body
      "module M where private theorem a : Nat := 1 end abstract let c : Nat := 3 end \
       def t : Nat := succ (succ a) end def u : Nat := c end end eval M.t eval M.u"
  in
  [%expect {|
    Evaluate M.t --> succ (succ M.a) : ℕ
    Evaluate M.u --> M.c : ℕ
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
    Error: on "≔" (at line 1, column 25 - line 1, column 27): Expected a
      parameter "(x : A)", or ":" followed by the type of the definition.
    |}]

let%expect_test "a command let and a term let" =
  let _ = main_of_body "let x : Nat := 1 end eval let y := succ x in y end let z : Nat := x end eval z" in
  [%expect {|
    Evaluate let x1 ≔ succ x in x1 end --> 2 : ℕ
    Evaluate z --> 1 : ℕ
    |}]

let%expect_test "keywords in a local body" =
  let _ =
    main_of_body
      "eval let module L where let a (n : Nat) : Nat := succ n end given b : Nat := a 1 end \
       def c : Nat := b end end in L.c end"
  in
  [%expect {|
    Evaluate let module M1 where
                   private def a : ∀ (x1 : ℕ) → ℕ ≔
                     λ (x2 : ℕ) → succ x2
                   end
                   private def b : ℕ ≔
                     a 1
                   end
                   def c : ℕ ≔
                     b
                   end
                 end
             in M1.c
             end --> 2 : ℕ
    |}];
  let _ = main_of_body "eval let module L where let a : Nat := 1 end end in L.a end" in
  [%expect {| Error: a is private in a local module, but it is used outside it |}]

let%expect_test "an abstract keyword is rejected in a local body" =
  let _ = main_of_body "eval let module L where theorem a : Nat := 1 end end in 0 end" in
  [%expect {|
    Error: let module M1 where
                 abstract def a : ℕ ≔
                   1
                 end
               end in 0 end has no inferable type
    |}];
  let _ = main_of_body "eval let module L where fact a : Nat := 1 end end in 0 end" in
  [%expect {|
    Error: let module M1 where
                 private abstract def a : ℕ ≔
                   1
                 end
               end in 0 end has no inferable type
    |}];
  let _ = main_of_body "eval let module L where abstract let a : Nat := 1 end end in 0 end" in
  [%expect {|
    Error: let module M1 where
                 private abstract def a : ℕ ≔
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
    Evaluate N.a --> 1 : ℕ
    Evaluate N.d --> 3 : ℕ
    Evaluate N.t --> 5 : ℕ
    Evaluate N.u --> 4 : ℕ
    Evaluate N.v --> 3 : ℕ
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
  [%expect {| Error: the unit Lib›Num is not imported |}]

let%expect_test "an open of a unit loaded by import" =
  let _ = main_of_multi_string "import Lib::Num module X where open Lib::Num use (double) open Lib::Num.Ops as O eval O.pred (double 2) end" in
  [%expect {| Evaluate O.pred (double 2) --> 3 : ℕ |}]

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
      further "›" or "." in the path, the arguments of the module, "as", "use",
      "export", or the next command.
      "import" names a unit, as in "import X›Y"; a module in scope is opened with
      "open".
    |}]

(** Import only loads *)

let%expect_test "an import declares nothing" =
  let _ = main_of_multi_string "import Lib::Num module X where eval double 1 end" in
  [%expect {| Error: unbound name double |}];
  let _ = main_of_multi_string "import Lib::Num module X where eval Lib::Num.double 1 end" in
  [%expect {| Evaluate Lib›Num.double 1 --> 2 : ℕ |}]

let%expect_test "a repeated import does nothing" =
  let _ =
    main_of_multi_string
      "import Lib::Num import Lib::Num module X where import Lib::Num module M where import Lib::Num end \
       eval Lib::Num.double 2 end"
  in
  [%expect {| Evaluate Lib›Num.double 2 --> 4 : ℕ |}]

let%expect_test "the long form of import is an import and an open" =
  let _ =
    main_of_multi_string
      "module X where import Lib::Num as N use (double) export (Ops) eval N.double 3 eval double 3 eval Ops.pred 3 end"
  in
  [%expect {|
    Evaluate N.double 3 --> 6 : ℕ
    Evaluate double 3 --> 6 : ℕ
    Evaluate Ops.pred 3 --> 2 : ℕ
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
  [%expect {| Evaluate q $0 --> ⋆ : ⊤ |}];
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude::Arith::Equality as E use (Eq) \
       module ScratchP (p : Eq 1 1) (q : E.Eq 2 2) where def r : Eq 2 2 := q end eval r end"
  in
  [%expect {| Evaluate r $1 $0 --> ⋆ : ⊤ |}]

let%expect_test "a leading open sees no parameter" =
  let _ = main_of_multi_string "import Lib::Priv open Lib::Priv.F n as G module X (n : Nat) where end" in
  [%expect {| Error: unbound name n |}]

let%expect_test "a leading open of a unit that is not imported is rejected" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "open Prelude::Arith::Equality use (Eq) module ScratchP (p : Eq 1 1) where end"
  in
  [%expect {| Error: the unit Prelude›Arith›Equality is not imported |}]

let%expect_test "an open in a module names the unit that is not imported" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "module Scratch where open Prelude::Arith::Plus.Basic use (plusZero) end"
  in
  [%expect {| Error: the unit Prelude›Arith›Plus is not imported |}];
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude::Arith::Plus module Scratch where open Prelude::Arith::Plus.Basic use (plusZero) \
       eval plusZero 0 end"
  in
  [%expect {| Evaluate plusZero 0 --> ⋆ : ⊤ |}]

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
    Evaluate succ N.k --> succ N.k : ℕ
    |}]

let%expect_test "an axiom of another unit" =
  let _ =
    main_of_multi_string
      "import Lib::Axioms module X where def d : Nat := succ Lib::Axioms.c end eval d \
       eval fun (x : Lib::Axioms.Inner.P 0) -> x end"
  in
  [%expect {|
    Evaluate d --> succ Lib›Axioms.c : ℕ
    Evaluate λ (x1 : Lib›Axioms.Inner.P 0) → x1
      --> λ (x1 : Lib›Axioms.Inner.P 0) → x1
      : ∀ (x1 : Lib›Axioms.Inner.P 0) → Lib›Axioms.Inner.P 0
    |}]

let%expect_test "an axiom of False makes False inhabited" =
  let _ = main_of_body "axiom bad : False def oops : False := bad end eval oops" in
  [%expect {| Evaluate oops --> bad : ⊥ |}]

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
    Evaluate 3 --> 3 : ℕ
    Evaluate 3 --> 3 : ℕ
    Evaluate ℕ --> ℕ : Type@0
    Evaluate Type@0 --> Type@0 : Type@1
    Evaluate (λ (A1 : Type@0)
                (x1 : A1)
               → x1) ℕ 4 --> 4 : ℕ
    Evaluate λ (A1 : Type@0)
               (x1 : A1)
               → x1 --> λ (A1 : Type@0)
                          (x1 : A1)
                          → x1 : ∀ (A1 : Type@0)
                                   (x1 : A1)
                                   → A1
    Evaluate rec 3 return x1 . ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ (succ x3) end
      --> 6 : ℕ
    Evaluate rec 2 return x1 . Type@0
             | zero ⇒ ℕ
             | succ x2, A1 ⇒ ∀ (x3 : ℕ) → A1
             end --> ∀ (x1 : ℕ)
                       (x2 : ℕ)
                       → ℕ : Type@0
    Evaluate ⋆ --> ⋆ : ⊤
    Evaluate λ (x1 : ⊥) → exfalso x1 return x2 . ℕ
      --> λ (x1 : ⊥) → exfalso x1 return x2 . ℕ : ∀ (x1 : ⊥) → ℕ
    Evaluate let x1 : ℕ ≔ 2; x2 ≔ λ (x3 : ℕ) → succ x3; x4 : Eq (x2 x1) 3 ≔ ⋆
             in x2 (x2 x1)
             end --> 4 : ℕ
    Evaluate double 3 --> 6 : ℕ
    Evaluate double four
      --> rec four return x1 . ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ (succ x3) end
      : ℕ
    Evaluate succ helper --> 2 : ℕ
    Evaluate double two --> 4 : ℕ
    Evaluate double (succ k)
      --> succ
            (succ
              (rec k return x1 . ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ (succ x3) end))
      : ℕ
    Evaluate Outer.Inner.next --> 11 : ℕ
    Evaluate Twice.twice ℕ double 1 --> 4 : ℕ
    Evaluate (Twice ℕ double).twice 1 --> 4 : ℕ
    Evaluate Quadruple.twice 1 --> 4 : ℕ
    Evaluate Shapes.Square.side --> 2 : ℕ
    Evaluate Vault.reveal --> 8 : ℕ
    Evaluate Vault.Inside.peek --> 7 : ℕ
    Evaluate Prelude›Arith›Plus.plus 2 3 --> 5 : ℕ
    Evaluate Adding.five --> 5 : ℕ
    Evaluate Adding.Algebra.plusComm 1 2 --> ⋆ : ⊤
    Evaluate Counting.seven --> 7 : ℕ
    Evaluate let module M1 (x1 : ℕ) where
                   private def twice : ∀ (x2 : ℕ) → ℕ ≔
                     (Twice ℕ double).twice
                   end
                   private def base : ℕ ≔
                     twice x1
                   end
                   def sum : ℕ ≔
                     succ base
                   end
                 end;
                 module M2 ≔ M1 1
             in M2.sum
             end --> 5 : ℕ
    Evaluate let module M1 where
                   private def add : ∀ (x1 : ℕ) → ℕ ≔
                     (Adder 5).add
                   end
                   def addIter : ∀ (x2 : ℕ)
                                   → Eq (Adder.add 5 x2)
                                       (Iter.iter 0l ℕ (λ (x3 : ℕ) → succ x3) x2
                                         5) ≔
                     (Adder 5).addIter
                   end
                   def eight : ℕ ≔
                     add 3
                   end
                 end
             in M1.addIter M1.eight
             end --> ⋆ : ⊤
    Evaluate maxl 1l (succl 2l) --> 3l : Level
    Evaluate Type@{maxl 1l 2l} --> Type@2 : Type@3
    Evaluate applyTwice 0l ℕ double 1 --> 4 : ℕ
    Evaluate applyTwice 1l Type@0 (λ (A1 : Type@0) → ∀ (x1 : A1) → A1) ℕ
      --> ∀ (x1 : ∀ (x2 : ℕ) → ℕ)
            (x3 : ℕ)
            → ℕ : Type@0
    Evaluate Pointed.point 1l Type@0 ℕ --> ℕ : Type@0
    Evaluate ∀ (x1 : Level) → Type@{x1} --> ∀ (x1 : Level) → Type@{x1} : Type@ω
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
    Cyc›A: not checked
    Cyc›B: not checked
    Cycle: not checked
    Lib›Bad: not checked
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
    435 evals, 435 boxes, 435 equal to mctt's output
    Evaluate Adding.five --> 5 : ℕ
    |}]

let%expect_test "mctt-doc: a unit whose log is out of step with its evals is reported, unboxed" =
  let lib = Lazy.force doc_lib in
  let lib = { lib with Doc.outputs = Hashtbl.copy lib.Doc.outputs } in
  Hashtbl.replace lib.Doc.outputs [ "Tutorial" ] [ "Evaluate x --> 0 : Nat" ];
  List.iter print_endline (Doc.problems lib);
  let tut = List.find (fun u -> u.Doc.u_path = [ "Tutorial" ]) lib.Doc.units in
  Printf.printf "%d boxes\n" (List.length (doc_boxes (Doc.render_unit lib (Doc.anchor_kinds lib) tut)));
  [%expect {|
    Tutorial: 35 evals, 1 outputs
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
    pow line 38: Prelude›Algebra›Monoid#pow
    pow line 38: Prelude›Arith›Pow#pow
    Additive line 21: Prelude›Algebra›Instances#Additive
    pow line 21: Prelude›Algebra›Monoid#pow
    powPlus line 75: Prelude›Algebra›Monoid#Power.powPlus
    plus line 205: Prelude›Arith›Plus#plus
    plus line 206: Prelude›Arith›Plus#plus
    add line 205: declares #Adding.add
    add line 206: Prelude›Arith›Plus#plus
    P line 205: declares #Adding.P
    P line 206: Tutorial#Adding.P
    addIter line 281: Tutorial#Adder.addIter
    x line 42: declares #l11
    x line 42: Tutorial#l11
    |}]

(* The universe syntax: examples/Universes.mctt, and the spellings it does
   not use, as a second unit. *)
let doc_univ = lazy (
  let items = Hashtbl.create 16 in
  let spellings = "module Spellings where\n\
                   def f (u : Level) : Type@{succl (maxl u 3l)} := Type@{maxl 3l u} end\n\
                   eval Type@3l\neval Type@{ω}\neval Type@{omega+1}\neval Type@{3L}\neval f 0l\nend\n" in
  let us = [ Doc.walk [ "Universes" ] (Doc.read_file "../examples/Universes.mctt") items;
             Doc.walk [ "Spellings" ] spellings items ] in
  let thetas = Hashtbl.create 4 and outputs = Hashtbl.create 4 in
  Doc.check_units "../examples" us thetas outputs;
  { Doc.root = "../examples"; units = us; failed = []; thetas; outputs; items })

let%expect_test "mctt-doc: universes line up, link, and are highlighted" =
  let lib = Lazy.force doc_univ in
  List.iter print_endline (Doc.problems lib);
  let s = Doc.stats lib in
  Printf.printf "%d names: %d linked, %d binders\n" s.Doc.names s.Doc.linked s.Doc.binders;
  (* A level variable links to its binder: [u] and [v] of [Arr]'s
     [Type@{maxl u v}]. *)
  let show u x ns = List.iter (fun n -> print_endline (x ^ " " ^ Doc.link_of lib u x n)) ns in
  show [ "Universes" ] "u" [ 15; 16; 17 ];
  show [ "Universes" ] "v" [ 6; 7; 8 ];
  (* A function into [Level], used in a universe: [Type@{depth 3}]. *)
  show [ "Universes" ] "depth" [ 2 ];
  (* The class of each spelling, as rendered. *)
  let kinds = Doc.anchor_kinds lib in
  let pages = List.map (Doc.render_unit lib kinds) lib.Doc.units in
  List.iter (fun x ->
      let cs = List.filter (fun c ->
          List.exists (fun p -> doc_find (Printf.sprintf "<span class=\"%s\">%s</span>" c x) p 0 <> None) pages)
          [ "kw"; "ty"; "num"; "sym" ] in
      Printf.printf "%s: %s\n" x (String.concat " " cs))
    [ "Level"; "Type"; "maxl"; "succl"; "0l"; "3l"; "2L"; "3L"; "2"; "ω"; "omega"; "@"; "+" ];
  (* The boxes of the evals that print a universe. *)
  List.iter (fun p -> List.iter (fun b -> if doc_find "Type@" b 0 <> None then print_endline b) (doc_boxes p)) pages;
  [%expect {|
    111 names: 57 linked, 54 binders
    u line 57: declares #l58
    u line 57: Universes#l58
    u line 58: Universes#l58
    v line 57: declares #l59
    v line 57: Universes#l59
    v line 58: Universes#l59
    depth line 50: Universes#depth
    Level: ty
    Type: ty
    maxl: kw
    succl: kw
    0l: num
    3l: num
    2L: num
    3L: num
    2: num
    ω: num
    omega: num
    @: sym
    +: sym
    Evaluate id 1l Type@0 ℕ --> ℕ : Type@0
    Evaluate atoms --> λ (x1 : Level)
                         (x2 : Level)
                         → Type@{maxl (maxl 1l x2) x1}
      : ∀ (x1 : Level)
          (x2 : Level)
          → Type@{maxl (maxl 2l (succl x2)) (succl x1)}
    Evaluate Dom --> ℕ : Type@0
    Evaluate Type@{depth 3} --> Type@3 : Type@4
    Evaluate Endo 0l ℕ --> ∀ (x1 : ℕ) → ℕ : Type@0
    Evaluate λ (x1 : Level)
               (A1 : Type@{x1})
               → ∀ (x2 : A1) → A1
      --> λ (x1 : Level)
            (A1 : Type@{x1})
            → ∀ (x2 : A1) → A1 : ∀ (x1 : Level)
                                   (A1 : Type@{x1})
                                   → Type@{x1}
    Evaluate ∀ (x1 : Level) → Type@{x1} --> ∀ (x1 : Level) → Type@{x1} : Type@ω
    Evaluate Type@2 --> Type@2 : Type@3
    Evaluate Type@2 --> Type@2 : Type@3
    Evaluate Type@2 --> Type@2 : Type@3
    Evaluate Type@ω --> Type@ω : Type@1L
    Evaluate Type@ω --> Type@ω : Type@1L
    Evaluate Type@ω --> Type@ω : Type@1L
    Evaluate Type@2L --> Type@2L : Type@3L
    Evaluate Type@2L --> Type@2L : Type@3L
    Evaluate Type@3 --> Type@3 : Type@4
    Evaluate Type@ω --> Type@ω : Type@1L
    Evaluate Type@1L --> Type@1L : Type@2L
    Evaluate Type@3L --> Type@3L : Type@4L
    Evaluate f 0l --> Type@3 : Type@4
    |}]

let%expect_test "lib/Universes.mctt" =
  let _ = main_of_lib "Universes.mctt" in
  [%expect {|
    Evaluate ofNat 3 --> 3l : Level
    Evaluate maxl (ofNat 2) (succl 4l) --> 5l : Level
    Evaluate plusl 2 (maxl 1l 3l) --> 5l : Level
    Evaluate lrefl 3l --> λ (x1 : ∀ (x2 : Level) → Type@0)
                            (x3 : x1 3l)
                            → x3 : LEq (maxl 2l 3l) (succl 2l)
    Evaluate lrefl 3l --> λ (x1 : ∀ (x2 : Level) → Type@0)
                            (x3 : x1 3l)
                            → x3
      : LEq (ofNat (max 2 3)) (maxl (ofNat 2) (ofNat 3))
    Evaluate Arrow 0l 1l ℕ Type@0 --> ∀ (x1 : ℕ) → Type@0 : Type@1
    Evaluate Pi 1l 1l Type@0 (λ (A1 : Type@0) → Endo 0l A1)
      --> ∀ (A1 : Type@0)
            (x1 : A1)
            → A1 : Type@1
    Evaluate Fun 0l 3 ℕ ⊤ --> ∀ (x1 : ℕ)
                                (x2 : ℕ)
                                (x3 : ℕ)
                                → ⊤ : Type@0
    Evaluate Fun 1l 2 Type@0 Type@0 --> ∀ (A1 : Type@0)
                                          (A2 : Type@0)
                                          → Type@0 : Type@1
    Evaluate λ (A1 : Type@0)
               (A2 : Type@0)
               → ∀ (x1 : A1) → A2
      --> λ (A1 : Type@0)
            (A2 : Type@0)
            → ∀ (x1 : A1) → A2 : Fun 1l 2 Type@0 Type@0
    Evaluate Universe 2 --> Type@2 : Type@3
    Evaluate universeIn 1 --> Type@1 : Type@2
    Evaluate up 0l 2l ℕ 3 --> 3 : ℕ
    Evaluate Cj.andFst 1l Type@0 Type@0 natAndTrue --> ℕ : Type@0
    Evaluate Cj.andSnd 1l Type@0 Type@0 (Cj.andSwap 1l Type@0 Type@0 natAndTrue)
      --> ℕ : Type@0
    Evaluate first 1l Type@0 (λ (A1 : Type@0) → A1) pointedNat --> ℕ : Type@0
    Evaluate Ex.existsElim 1l Sums ℕ twoThree (λ (x1 : ℕ)
                                                 (x2 : Sums x1)
                                                → x1) --> 2 : ℕ
    Evaluate Ex.existsElim 1l Sums ℕ twoThree
               (λ (x1 : ℕ)
                  (x2 : Sums x1)
                 → Ex.existsElim 0l (λ (x3 : ℕ) → Eq (plus x1 x3) 5) ℕ x2
                     (λ (x4 : ℕ)
                        (x5 : Eq (plus x1 x4) 5)
                       → x4)) --> 3 : ℕ
    Evaluate Types.nth 3 threeTypes 1 ⋆ --> ⊤ : Type@0
    Evaluate Types.last 2 threeTypes --> ⊥ : Type@0
    Evaluate Types.map Type@0 (λ (A1 : Type@0) → ∀ (x1 : A1) → A1) 3 threeTypes 0
               ⋆ --> ∀ (x1 : ℕ) → ℕ : Type@0
    Evaluate Iter.iter 1l Type@0 (λ (A1 : Type@0) → ∀ (x1 : A1) → A1) 2 ℕ
      --> ∀ (x1 : ∀ (x2 : ℕ) → ℕ)
            (x3 : ℕ)
            → ℕ : Type@0
    Evaluate C.toNat 0l (C.cpow 0l (C.fromNat 0l 2) (C.fromNat 1l 5)) --> 32 : ℕ
    Evaluate C.toNat 0l (C.lower 0l (C.fromNat 1l 4)) --> 4 : ℕ
    Evaluate C.boolToNat 0l (C.isZero 0l (C.fromNat 1l 0)) --> 1 : ℕ
    Evaluate C.boolToNat 0l (C.isZero 0l (C.fromNat 1l 3)) --> 0 : ℕ
    Evaluate C.length 1l Type@0
               (C.cons 1l Type@0 ℕ (C.cons 1l Type@0 ⊤ (C.nil 1l Type@0))) --> 2
      : ℕ
    Evaluate C.sum 0l
               (C.append 0l ℕ (C.replicate 0l ℕ 3 4)
                 (C.cons 0l ℕ 5 (C.nil 0l ℕ))) --> 17 : ℕ
    Evaluate toNatPlus 0l 2 3 --> ⋆ : ⊤
    Evaluate toNatPow 0l 2 3 --> ⋆ : ⊤
    Evaluate toNatPow 3l 3 2 --> ⋆ : ⊤
    Evaluate toNatLower 2l 4 --> ⋆ : ⊤
    Evaluate C.toNat 0l (churchHalf 9) --> 4 : ℕ
    |}]
