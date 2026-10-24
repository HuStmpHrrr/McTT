(* Unit test cases for parsing *)

open Main
open McttExtracted.Entrypoint

(** Helper definitions *)

(* Every program sees the library, so that a unit can import the natural
   numbers, [Prelude›Builtin›Nat]. *)
let lib_root = [ "../lib" ]
let main_of_program_string ?search_root program =
  Main.main_of_program_string ?search_root ~extra_roots:lib_root program
let main_of_filename ?search_root filename =
  Main.main_of_filename ?search_root ~extra_roots:lib_root filename

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
   get a throwaway one, which imports the natural numbers with their
   constructors. *)
let nat_import = "import Prelude›Builtin›Nat use (Nat; zero; succ)\n"
let main_of_body body =
  main_of_program_string ~search_root:"../lib" (nat_import ^ "module Test where " ^ body ^ " end")

(* The same without the natural numbers. *)
let main_of_bare_body body = main_of_program_string ("module Test where " ^ body ^ " end")

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
     eval elim 2 at y -> Nat | zero => 0 | succ n, r => succ r end \
     eval t eval f" in
  [%expect {|
    Evaluate elim 2 at x1 → ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ x3 end --> 2 : ℕ
    Evaluate t --> ⋆ : ⊤
    Evaluate f --> λ (x1 : ⊥) → exfalso x1 return x2 . ℕ : ∀ (x1 : ⊥) → ℕ
    |}]

let%expect_test "each Unicode spelling parses" =
  let _ = main_of_body
    "def t : ⊤ ≔ ⋆ end \
     def f : ∀ (b : ⊥) → ℕ ≔ λ (b : ⊥) → exfalso b return y . ℕ end \
     def g : Π (x : ℕ) → ℕ ≔ λ (x : ℕ) → x end \
     def u : Type@ω ≔ Type@0 end \
     eval elim 2 at y -> ℕ | zero ⇒ 0 | succ n, r ⇒ succ r end \
     eval t eval f eval g" in
  [%expect {|
    Evaluate elim 2 at x1 → ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ x3 end --> 2 : ℕ
    Evaluate t --> ⋆ : ⊤
    Evaluate f --> λ (x1 : ⊥) → exfalso x1 return x2 . ℕ : ∀ (x1 : ⊥) → ℕ
    Evaluate g --> λ (x1 : ℕ) → x1 : ∀ (x1 : ℕ) → ℕ
    |}]

(* Identifiers are ASCII, so no Unicode symbol needs a space. *)
let%expect_test "Unicode symbols need no spaces" =
  let _ = main_of_body "def g:∀(x:ℕ)→ℕ≔λ(x:ℕ)→x end eval g" in
  [%expect {| Evaluate g --> λ (x1 : ℕ) → x1 : ∀ (x1 : ℕ) → ℕ |}]

let%expect_test "a unit path may be spelled with ›" =
  let _ = main_of_multi_string "import Prelude›Builtin›Nat import Lib›Num module Test where eval Lib::Num.double 2 eval Lib›Num.Ops.pred 2 end" in
  [%expect {|
    Evaluate Lib›Num.double 2 --> 4 : ℕ
    Evaluate Lib›Num.Ops.pred 2 --> 1 : ℕ
    |}]

(* [∷] is not a path separator: only [::] and [›] are. *)
let%expect_test "a unit path spelled with ∷ is rejected" =
  let _ = main_of_multi_string "import Prelude›Builtin›Nat import Lib∷Num module Test where eval 0 end" in
  [%expect {| Error: unexpected character "∷" at line 1, column 38 |}]

let%expect_test "a Unicode character that is not a token is rejected" =
  let _ = main_of_body "eval λ (x : ℕ) ↦ x" in
  [%expect {| Error: unexpected character "↦" at line 2, column 34 |}]

(* Columns count characters: [→] is one column, as it is displayed. *)
let%expect_test "a syntax error after Unicode is located by characters" =
  let _ = main_of_body "eval λ (x : ℕ) → → x" in
  [%expect {|
    Error: on "→" (at line 2, column 36 - line 2, column 37): An expression is
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
  let _ = main_of_program_string "import Prelude›Builtin›Nat use (Nat) def x : Nat := 0 end module Test where end" in
  [%expect {|
    Error: on "def" (at line 1, column 38 - line 1, column 41): This token is
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
    "eval elim 3 at y -> Nat | zero => 0 | succ n, r => 0 end : Nat" in
  [%expect {| Evaluate elim 3 at x1 → ℕ | zero ⇒ 0 | succ x2, x3 ⇒ 0 end --> 0 : ℕ |}]

let%expect_test "SimpleNat.mctt works" =
  let _ = main_of_example "SimpleNat.mctt" in
  [%expect {| Evaluate 4 --> 4 : ℕ |}]

let%expect_test "SimpleRec.mctt works" =
  let _ = main_of_example "SimpleRec.mctt" in
  [%expect {|
    Evaluate λ (x1 : ℕ)
               → elim x1 at x2 → ℕ | zero ⇒ 1 | succ x3, x4 ⇒ succ x4 end
      --> λ (x1 : ℕ) → elim x1 at x2 → ℕ | zero ⇒ 1 | succ x3, x4 ⇒ succ x4 end
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
    Error: on "end" (at line 2, column 34 - line 2, column 37): Either an
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
                           → elim x26
                             at x27 → Type@0
                             | zero ⇒ ℕ
                             | succ x28, A7 ⇒ A6
                             end)
                         0
                         (λ (x29 : ℕ)
                            (x30 : A6)
                            (x31 : elim x29
                                   at x32 → Type@0
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
    Error: on "in" (at line 2, column 33 - line 2, column 35): Expected the body
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
                     → elim x3
                       at x4 → Type@0
                       | zero ⇒ ℕ
                       | succ x5, A1 ⇒ ∀ (x6 : ℕ) → A1
                       end;
                 x7 : ∀ (x8 : x1 0) → ℕ ≔ λ (x9 : ℕ) → x9;
                 x10 : ∀ (x11 : ℕ)
                         (x12 : x1 (succ x11))
                         (x13 : ℕ)
                         → x1 x11 ≔
                   λ (x14 : ℕ)
                     (x15 : elim succ x14
                            at x16 → Type@0
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
                           → elim x25
                             at x27 → ℕ
                             | zero ⇒ x26
                             | succ x28, x29 ⇒ succ x29
                             end
                   in λ (x30 : ℕ)
                        (x31 : ℕ)
                        (x32 : ℕ)
                        → x22 x30 (x22 x31 x32)
                   end
             in (elim x20
                 at x33 → ∀ (x34 : x1 x33) → ℕ
                 | zero ⇒ x7
                 | succ x35, x36 ⇒
                   λ (x37 : x1 (succ x35)) → x36 (x10 x35 x37 (succ x35))
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
                           → elim x71
                             at x72 → Type@0
                             | zero ⇒ ℕ
                             | succ x73, A11 ⇒ A10
                             end)
                         0
                         (λ (x74 : ℕ)
                            (x75 : A10)
                            (x76 : elim x74
                                   at x77 → Type@0
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
      --> elim four at x1 → ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ (succ x3) end : ℕ
    Evaluate double four
      --> elim four at x1 → ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ (succ x3) end : ℕ
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
    Error: on "ω^2" (at line 2, column 24 - line 2, column 27): ω^2 is not a
      level: every level is below it. It is written only in a large universe,
      "Type@{ω^2}" or "Type@{ω^2+i}".
    |}]

let%expect_test "an unbraced large universe" =
  let _ = main_of_body "eval Type@omega^2" in
  [%expect {|
    Error: on "ω^2" (at line 2, column 29 - line 2, column 36): ω^2 is not a
      level: every level is below it. It is written only in a large universe,
      "Type@{ω^2}" or "Type@{ω^2+i}".
    |}]

let%expect_test "a large universe without its offset" =
  let _ = main_of_body "eval Type@{ω^2+}" in
  [%expect {|
    Error: on "}" (at line 2, column 34 - line 2, column 35): A numeral is
      expected after "Type@{ω^2+": the large universe "Type@{ω^2+i}".
    |}]

let%expect_test "a large universe not closed" =
  let _ = main_of_body "eval Type@{ω^2 Nat}" in
  [%expect {|
    Error: on "Nat" (at line 2, column 34 - line 2, column 37): A closing "}" or
      "+i" is expected after "Type@{ω^2": the large universe "Type@{ω^2}" or
      "Type@{ω^2+i}".
    |}]

(* An unbraced [+] is rejected. *)
let%expect_test "an unbraced omega offset is a syntax error" =
  let _ = main_of_body "eval Type@ω+1" in
  [%expect {|
    Error: on "+" (at line 2, column 30 - line 2, column 31): Expected ":"
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
    Error: on "u" (at line 2, column 31 - line 2, column 32): A numeral is
      expected after "Level@{": the sort of the type of levels.
    |}]

let%expect_test "the braced type of levels needs its closing brace" =
  let _ = main_of_body "eval Level@{1 Nat}" in
  [%expect {|
    Error: on "Nat" (at line 2, column 33 - line 2, column 36): A closing "}" is
      expected after the sort of "Level@{n".
    |}]

let%expect_test "Level@ needs a numeral" =
  let _ = main_of_body "eval Level@u" in
  [%expect {|
    Error: on "u" (at line 2, column 30 - line 2, column 31): A numeral is
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
  let _ = main_of_program_string "import Prelude›Builtin›Nat use (Nat) module Repro where def t : Nat Nat := 1 end end" in
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

(* The level of a small universe is an ordinary term, checked against the
   types of levels: a numeral there is a natural number, so [Type@{0}] is no
   type.  Wherever a type or a parameter is rejected for it, the error names
   the level, with a hint for a numeral. *)
let%expect_test "the level of a universe is a level: eval" =
  let _ = main_of_body "eval Level@{5} : Type@{0}" in
  [%expect {|
    Error: 0 is not of type Level@n for any n (the level of Type@{0});
      write 0l for the level 0
    |}];
  let _ = main_of_body "eval Nat : Type@{5}" in
  [%expect {|
    Error: 5 is not of type Level@n for any n (the level of Type@{5});
      write 5l for the level 5
    |}];
  let _ = main_of_body "eval Nat : Type@{true}" in
  [%expect {| Error: ⋆ is not of type Level@n for any n (the level of Type@{⋆}) |}];
  let _ = main_of_body "eval Nat : Type@{Nat}" in
  [%expect {| Error: ℕ is not of type Level@n for any n (the level of Type@{ℕ}) |}]

let%expect_test "the level of a universe is a level: declarations" =
  let _ = main_of_body "def t : Type@{0} := Nat end" in
  [%expect {|
    Error: 0 is not of type Level@n for any n (the level of Type@{0});
      write 0l for the level 0
    |}];
  let _ = main_of_body "theorem t : Type@{0} := Nat end" in
  [%expect {|
    Error: 0 is not of type Level@n for any n (the level of Type@{0});
      write 0l for the level 0
    |}];
  let _ = main_of_body "axiom x : Type@{0}" in
  [%expect {|
    Error: 0 is not of type Level@n for any n (the level of Type@{0});
      write 0l for the level 0
    |}]

let%expect_test "the level of a universe is a level: parameters" =
  let _ = main_of_body "def g (A : Type@{0}) : Nat := 0 end" in
  [%expect {|
    Error: 0 is not of type Level@n for any n (the level of Type@{0});
      write 0l for the level 0
    |}];
  let _ = main_of_body "module M (u : Level) (A : Type@{succ u}) where end" in
  [%expect {| Error: succ x1 is not of type Level@n for any n (the level of Type@{succ x1}) |}];
  let _ = main_of_body "module N where end module M (A : Type@{0}) := N" in
  [%expect {|
    Error: 0 is not of type Level@n for any n (the level of Type@{0});
      write 0l for the level 0
    |}];
  let _ = main_of_program_string "import Prelude›Builtin›Nat module T (A : Type@{0}) where end" in
  [%expect {|
    Error: 0 is not of type Level@n for any n (the level of Type@{0});
      write 0l for the level 0
    |}]

let%expect_test "the level of a universe is a level: nested" =
  let _ = main_of_body "eval Nat : Π (A : Type@{0}) → A" in
  [%expect {|
    Error: 0 is not of type Level@n for any n (the level of Type@{0});
      write 0l for the level 0
    |}];
  let _ = main_of_body "def f (u : Level) : Type@{succ u} := Nat end" in
  [%expect {| Error: succ x1 is not of type Level@n for any n (the level of Type@{succ x1}) |}];
  let _ = main_of_body "eval Nat : forall (u : Level) -> forall (B : Type@{u}) -> Type@{B}" in
  [%expect {| Error: A1 is not of type Level@n for any n (the level of Type@{A1}) |}];
  (* A type rejected for another reason keeps its message. *)
  let _ = main_of_body "eval Nat : Type@{0l} Nat" in
  [%expect {| Error: the ascribed type of ℕ, Type@0 ℕ, is not a type |}]

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
                   open Inner use (m)
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
                     → elim x4 at x5 → A1 | zero ⇒ x1 | succ x6, x7 ⇒ succ x7 end
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

let%expect_test "a unit name may be one segment" =
  let _ = main_of_multi "OneSegment.mctt" in
  [%expect {|
    Evaluate three --> 3 : ℕ
    Evaluate Single.next Single.three --> 4 : ℕ
    Evaluate S.next 4 --> 5 : ℕ
    Evaluate next 9 --> 10 : ℕ
    |}]

let%expect_test "a one-segment unit not imported is not in scope" =
  let _ = main_of_multi_string "module T where eval Single.three end" in
  [%expect {| Error: unbound name Single |}]

let%expect_test "an import is not transitive" =
  let _ = main_of_multi "Transitive.mctt" in
  [%expect {| Error: the unit Lib›Num is not imported |}]

let%expect_test "a cyclic import is rejected" =
  let _ = main_of_multi "Cycle.mctt" in
  [%expect {| Error: cyclic import: Cyc›A → Cyc›B → Cyc›A |}]

let%expect_test "a missing unit is reported" =
  let _ = main_of_multi "Missing.mctt" in
  [%expect {| Error: Lib›Nowhere: cannot find unit |}]

(** Search roots: the [--search-root] flags in order, then the entries of
    [MCTT_SEARCH_ROOT], then the current directory, run through
    [main_of_command_line] as the executable does. *)

(* A fresh, empty temporary directory (without [Filename.temp_dir], which is
   OCaml 5.1). *)
let fresh_dir () =
  let d = Filename.temp_file "mctt-roots" "" in
  Sys.remove d; Sys.mkdir d 0o755; d

let write_file path contents =
  let oc = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () -> output_string oc contents)

(* Two search roots under a temporary directory: [a] holds [A›U] and [D›U],
   [b] holds [B›U] and another [D›U], which differ in the type of [which].
   [both] imports [A›U] and [B›U]; [dup] imports [D›U] and shows [which]. *)
type roots_tree = { a : string; b : string; both : string; dup : string }
let roots_tree = lazy (
  let top = fresh_dir () in
  let root name units =
    let r = Filename.concat top name in
    Sys.mkdir r 0o755;
    List.iter (fun (dir, src) ->
        let d = Filename.concat r dir in
        Sys.mkdir d 0o755; write_file (Filename.concat d "U.mctt") src)
      units;
    r in
  let a = root "a" [ ("A", "module A›U where def t : Type@1 ≔ Type@0 end end");
                     ("D", "module D›U where def which : Type@1 ≔ Type@0 end end") ] in
  let b = root "b" [ ("B", "module B›U where def t : Type@2 ≔ Type@1 end end");
                     ("D", "module D›U where def which : Type@2 ≔ Type@1 end end") ] in
  let both = Filename.concat top "Both.mctt" in
  write_file both "import A›U\nimport B›U\nmodule Both where eval A›U.t eval B›U.t end";
  let dup = Filename.concat top "Dup.mctt" in
  write_file dup "import D›U\nmodule Dup where eval D›U.which end";
  { a; b; both; dup })

let%expect_test "--search-root given twice adds both roots" =
  let t = Lazy.force roots_tree in
  let _ = main_of_command_line [ t.a; t.b ] None t.both in
  [%expect {|
    Evaluate A›U.t --> Type@0 : Type@1
    Evaluate B›U.t --> Type@1 : Type@2
    |}]

let%expect_test "a unit under no --search-root is not found" =
  let t = Lazy.force roots_tree in
  let _ = main_of_command_line [ t.a ] None t.both in
  [%expect {| Error: B›U: cannot find unit |}]

let%expect_test "MCTT_SEARCH_ROOT alone adds its entries, ignoring empty ones" =
  let t = Lazy.force roots_tree in
  let _ = main_of_command_line [] (Some (":" ^ t.a ^ "::" ^ t.b ^ ":")) t.both in
  [%expect {|
    Evaluate A›U.t --> Type@0 : Type@1
    Evaluate B›U.t --> Type@1 : Type@2
    |}]

let%expect_test "a unit under no entry of MCTT_SEARCH_ROOT is not found" =
  let t = Lazy.force roots_tree in
  let _ = main_of_command_line [] (Some t.b) t.both in
  [%expect {| Error: A›U: cannot find unit |}]

let%expect_test "--search-root and MCTT_SEARCH_ROOT together add all their roots" =
  let t = Lazy.force roots_tree in
  let _ = main_of_command_line [ t.b ] (Some t.a) t.both in
  [%expect {|
    Evaluate A›U.t --> Type@0 : Type@1
    Evaluate B›U.t --> Type@1 : Type@2
    |}]

let%expect_test "a unit under several roots is read from the first: flags before the variable" =
  let t = Lazy.force roots_tree in
  let _ = main_of_command_line [ t.a ] (Some t.b) t.dup in
  let _ = main_of_command_line [ t.b ] (Some t.a) t.dup in
  [%expect {|
    Evaluate D›U.which --> Type@0 : Type@1
    Evaluate D›U.which --> Type@1 : Type@2
    |}]

let%expect_test "a unit under several roots is read from the first: flags and entries in order" =
  let t = Lazy.force roots_tree in
  let _ = main_of_command_line [ t.b; t.a ] None t.dup in
  let _ = main_of_command_line [] (Some (t.a ^ ":" ^ t.b)) t.dup in
  [%expect {|
    Evaluate D›U.which --> Type@1 : Type@2
    Evaluate D›U.which --> Type@0 : Type@1
    |}]

let%expect_test "the search roots are the flags, then the variable's entries, then ." =
  List.iter print_endline (search_roots [ "f1"; "f2" ] (Some "e1::e2:"));
  [%expect {|
    f1
    f2
    e1
    e2
    .
    |}]

let%expect_test "an ill-typed imported unit is reported" =
  let _ = main_of_multi "BadDep.mctt" in
  [%expect {| Error: the body of wrong, Type@0, is not of type ℕ |}]

let%expect_test "a file declaring another unit is reported" =
  let _ = main_of_multi "Misnamed.mctt" in
  [%expect {| Error: Lib›Wrong: the file of the unit declares another unit |}]

let%expect_test "lib/Lists.mctt" =
  let _ = main_of_lib "Lists.mctt" in
  [%expect {|
    Evaluate NL.length oneTwoThree --> 3 : ℕ
    Evaluate NL.append oneTwoThree (NatList.cons 4 NatList.nil)
      --> Prelude›Data›List.List.cons 0l ℕ 1
            (Prelude›Data›List.List.cons 0l ℕ 2
              (Prelude›Data›List.List.cons 0l ℕ 3
                (Prelude›Data›List.List.cons 0l ℕ 4
                  (Prelude›Data›List.List.nil 0l ℕ))))
      : Prelude›Data›List.List 0l ℕ
    Evaluate NL.reverse oneTwoThree
      --> Prelude›Data›List.List.cons 0l ℕ 3
            (Prelude›Data›List.List.cons 0l ℕ 2
              (Prelude›Data›List.List.cons 0l ℕ 1
                (Prelude›Data›List.List.nil 0l ℕ))) : Prelude›Data›List.List 0l ℕ
    Evaluate NL.map ℕ (λ (x1 : ℕ) → plus x1 x1) oneTwoThree
      --> Prelude›Data›List.List.cons 0l ℕ 2
            (Prelude›Data›List.List.cons 0l ℕ 4
              (Prelude›Data›List.List.cons 0l ℕ 6
                (Prelude›Data›List.List.nil 0l ℕ))) : Prelude›Data›List.List 0l ℕ
    Evaluate sum oneTwoThree --> 6 : ℕ
    Evaluate NL.foldr ℕ plus 0 (NL.reverse oneTwoThree) --> 6 : ℕ
    Evaluate evens oneTwoThree --> 2 : ℕ
    Evaluate Ops.length 1l Type@0
               (List.cons 1l Type@0 ℕ
                 (List.cons 1l Type@0 Bool (List.nil 1l Type@0))) --> 2 : ℕ
    Evaluate and tt (or ff tt) --> Prelude›Data›Bool.Bool.tt
      : Prelude›Data›Bool.Bool
    Evaluate eqb (not tt) ff --> Prelude›Data›Bool.Bool.tt
      : Prelude›Data›Bool.Bool
    Evaluate Cond.if 1l Type@0 (eqb tt ff) ℕ Bool --> Prelude›Data›Bool.Bool
      : Type@0
    Evaluate all
               (List.cons 0l Bool tt
                 (List.cons 0l Bool (not ff) (List.nil 0l Bool)))
      --> Prelude›Data›Bool.Bool.tt : Prelude›Data›Bool.Bool
    Evaluate head oneTwoThree --> Prelude›Data›Option.Option.some 0l ℕ 1
      : Prelude›Data›Option.Option 0l ℕ
    Evaluate Opt.getOr 0l ℕ 0 (Opt.map 0l ℕ ℕ succ (head NatList.nil)) --> 0 : ℕ
    Evaluate Opt.bind 0l ℕ ℕ (λ (x1 : ℕ) → head (NL.reverse oneTwoThree))
               (head oneTwoThree) --> Prelude›Data›Option.Option.some 0l ℕ 3
      : Prelude›Data›Option.Option 0l ℕ
    Evaluate P.swap 0l ℕ Bool (Prod.pair 0l ℕ Bool 1 tt)
      --> Prelude›Data›Prod.Prod.pair 0l Prelude›Data›Bool.Bool ℕ
            Prelude›Data›Bool.Bool.tt
            1 : Prelude›Data›Prod.Prod 0l Prelude›Data›Bool.Bool ℕ
    Evaluate S.case 0l ℕ Bool ℕ succ (λ (x1 : Bool) → if ℕ x1 1 0)
               (S.swap 0l Bool ℕ (Sum.inl 0l Bool ℕ ff)) --> 0 : ℕ
    Evaluate Tagged.snd (Tagged.Sigma.pair tt 3) --> 3 : ℕ
    Evaluate Tagged.snd (Tagged.Sigma.pair ff ff) --> Prelude›Data›Bool.Bool.ff
      : Prelude›Data›Bool.Bool
    Evaluate lengthAppend oneTwoThree oneTwoThree --> ⋆ : ⊤
    Evaluate sumReverse oneTwoThree --> ⋆ : ⊤
    Evaluate reverseReverse oneTwoThree
      --> λ (x1 : ∀ (x2 : Prelude›Data›List.List 0l ℕ) → Type@0)
            (x3 : x1
                    (Prelude›Data›List.List.cons 0l ℕ 1
                      (Prelude›Data›List.List.cons 0l ℕ 2
                        (Prelude›Data›List.List.cons 0l ℕ 3
                          (Prelude›Data›List.List.nil 0l ℕ)))))
            → Prelude›Data›List›Properties.Reverse.reverseReverse 0l ℕ
                (Prelude›Data›List.List.cons 0l ℕ 1
                  (Prelude›Data›List.List.cons 0l ℕ 2
                    (Prelude›Data›List.List.cons 0l ℕ 3
                      (Prelude›Data›List.List.nil 0l ℕ))))
                (λ (x4 : Prelude›Data›List.List 0l ℕ) → x1 x4)
                x3
      : ∀ (x1 : ∀ (x2 : Prelude›Data›List.List 0l ℕ) → Type@0)
          (x3 : x1
                  (Prelude›Data›List.List.cons 0l ℕ 1
                    (Prelude›Data›List.List.cons 0l ℕ 2
                      (Prelude›Data›List.List.cons 0l ℕ 3
                        (Prelude›Data›List.List.nil 0l ℕ)))))
          → x1
              (Prelude›Data›List.List.cons 0l ℕ 1
                (Prelude›Data›List.List.cons 0l ℕ 2
                  (Prelude›Data›List.List.cons 0l ℕ 3
                    (Prelude›Data›List.List.nil 0l ℕ))))
    Evaluate notAnd tt ff
      --> λ (x1 : ∀ (x2 : Prelude›Data›Bool.Bool) → Type@0)
            (x3 : x1 Prelude›Data›Bool.Bool.tt)
            → Prelude›Data›Bool›Properties.DeMorgan.notAnd
                Prelude›Data›Bool.Bool.tt
                Prelude›Data›Bool.Bool.ff
                (λ (x4 : Prelude›Data›Bool.Bool) → x1 x4)
                x3
      : ∀ (x1 : ∀ (x2 : Prelude›Data›Bool.Bool) → Type@0)
          (x3 : x1 Prelude›Data›Bool.Bool.tt)
          → x1 Prelude›Data›Bool.Bool.tt
    |}]

let%expect_test "lib/DataTypes.mctt" =
  let _ = main_of_lib "DataTypes.mctt" in
  [%expect {|
    Evaluate compare 3 5 --> Prelude›Data›Ordering.Ordering.less
      : Prelude›Data›Ordering.Ordering
    Evaluate thenCmp (compare 2 2) (flip (compare 1 4))
      --> Prelude›Data›Ordering.Ordering.greater : Prelude›Data›Ordering.Ordering
    Evaluate compareSpec 3 5 --> ⋆ : ⊤
    Evaluate total (Th.swap 0l ℕ ℕ (These.these 0l ℕ ℕ 2 3)) --> 5 : ℕ
    Evaluate total (These.that 0l ℕ ℕ 4) --> 4 : ℕ
    Evaluate N.last oneToFour --> 4 : ℕ
    Evaluate N.head (N.reverse oneToFour) --> 4 : ℕ
    Evaluate N.foldr ℕ plus (λ (x1 : ℕ) → x1) oneToFour --> 10 : ℕ
    Evaluate N.length (N.append oneToFour oneToFour) --> 8 : ℕ
    Evaluate T.nodes sample --> 2 : ℕ
    Evaluate T.leaves sample --> 3 : ℕ
    Evaluate T.toListInfix (T.mirror sample)
      --> Prelude›Data›List.List.cons 0l ℕ 2
            (Prelude›Data›List.List.cons 0l ℕ 1
              (Prelude›Data›List.List.nil 0l ℕ)) : Prelude›Data›List.List 0l ℕ
    Evaluate TP.Counts.leavesNodes sample --> ⋆ : ⊤
    Evaluate parity 7 --> Prelude›Data›Parity.Parity.odd
      : Prelude›Data›Parity.Parity
    Evaluate toSign (parity 4) --> Prelude›Data›Sign.Sign.positive
      : Prelude›Data›Sign.Sign
    Evaluate add (neg (pos 3)) (pos 5) --> Prelude›Data›Integer.Int.pos 2
      : Prelude›Data›Integer.Int
    Evaluate sub (pos 2) (pos 7) --> Prelude›Data›Integer.Int.negsuc 4
      : Prelude›Data›Integer.Int
    Evaluate mul (negsuc 1) (negsuc 2) --> Prelude›Data›Integer.Int.pos 6
      : Prelude›Data›Integer.Int
    Evaluate abs (mul (pos 3) (negsuc 3)) --> 12 : ℕ
    Evaluate absMul (pos 2) (negsuc 2) --> ⋆ : ⊤
    Evaluate fromNat 6
      --> Prelude›Data›Binary.Bin.doubleSucc
            (Prelude›Data›Binary.Bin.doubleSucc Prelude›Data›Binary.Bin.zero)
      : Prelude›Data›Binary.Bin
    Evaluate toNat (Bn.add (fromNat 13) (fromNat 22)) --> 35 : ℕ
    Evaluate toNatAdd (fromNat 6) (fromNat 7) --> ⋆ : ⊤
    Evaluate wToNat (wsucc (wsucc (wsucc wzero))) --> 3 : ℕ
    Evaluate WO.head 0l Bool Arity (wsucc wzero) --> Prelude›Data›Bool.Bool.tt
      : Prelude›Data›Bool.Bool
    |}]

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
    Evaluate leb 2 5 --> Prelude›Data›Bool.Bool.tt : Prelude›Data›Bool.Bool
    Evaluate leb 5 2 --> Prelude›Data›Bool.Bool.ff : Prelude›Data›Bool.Bool
    Evaluate lebComplete 2 5 ⋆ --> ⋆ : ⊤
    Evaluate lebFalse 5 2 ⋆ --> ⋆ : ⊤
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
  [%expect {| Error: unexpected character '$' at line 2, column 26 |}]

let%expect_test "an unterminated comment is reported" =
  let _ = main_of_body "eval 0 (* open" in
  [%expect {| Error: unterminated comment |}]

let%expect_test "a multi-line comment counts its lines" =
  let _ = main_of_program_string "import Prelude›Builtin›Nat module Test where\n(* one\n   two *)\n\neval 0 $ 1 end" in
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
    Evaluate orElim (Eq 3 3) (Not (Eq 3 3)) Bool (decEq 3 3)
               (λ (x1 : Eq 3 3) → tt)
               (λ (x2 : Not (Eq 3 3)) → ff) --> Prelude›Data›Bool.Bool.tt
      : Prelude›Data›Bool.Bool
    Evaluate orElim (Eq 3 4) (Not (Eq 3 4)) Bool (decEq 3 4)
               (λ (x1 : Eq 3 4) → tt)
               (λ (x2 : Not (Eq 3 4)) → ff) --> Prelude›Data›Bool.Bool.ff
      : Prelude›Data›Bool.Bool
    Evaluate orElim (Le 2 5) (Not (Le 2 5)) Bool (decLe 2 5)
               (λ (x1 : Le 2 5) → tt)
               (λ (x2 : Not (Le 2 5)) → ff) --> Prelude›Data›Bool.Bool.tt
      : Prelude›Data›Bool.Bool
    Evaluate orElim (Lt 5 5) (Not (Lt 5 5)) Bool (decLt 5 5)
               (λ (x1 : Lt 5 5) → tt)
               (λ (x2 : Not (Lt 5 5)) → ff) --> Prelude›Data›Bool.Bool.ff
      : Prelude›Data›Bool.Bool
    Evaluate decStable (Eq 4 4) (decEq 4 4) (λ (x1 : Not (Eq 4 4)) → x1 ⋆) --> ⋆
      : ⊤
    Evaluate eqb 6 6 --> Prelude›Data›Bool.Bool.tt : Prelude›Data›Bool.Bool
    Evaluate eqb 6 2 --> Prelude›Data›Bool.Bool.ff : Prelude›Data›Bool.Bool
    Evaluate iffFwd (IsTrue (eqb 5 5)) (Eq 5 5) (eqbSpec 5 5) ⋆ --> ⋆ : ⊤
    Evaluate iffBwd (IsTrue (eqb 5 5)) (Eq 5 5) (eqbSpec 5 5) ⋆ --> ⋆ : ⊤
    Evaluate eqbFalse 2 3 ⋆
      --> λ (x1 : ⊥) → Prelude›Arith›Decide.EqbLaws.eqbFalse 2 3 ⋆ x1
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
    Evaluate NV.allb positive 5 oneToFive --> Prelude›Data›Bool.Bool.tt
      : Prelude›Data›Bool.Bool
    Evaluate NV.allb positive 4 (NV.cons 3 0 oneTwoThree)
      --> Prelude›Data›Bool.Bool.ff : Prelude›Data›Bool.Bool
    Evaluate NV.anyb positive 3 (NV.snoc 2 (NV.replicate 2 0) 9)
      --> Prelude›Data›Bool.Bool.tt : Prelude›Data›Bool.Bool
    Evaluate NV.anyb positive 3 (NV.replicate 3 0) --> Prelude›Data›Bool.Bool.ff
      : Prelude›Data›Bool.Bool
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
    Evaluate allbSound 0l ℕ positive 5 oneToFive ⋆ 2 ⋆ --> ⋆ : ⊤
    Evaluate allbComplete 0l ℕ positive 4 (NV.replicate 4 3)
               (λ (x1 : ℕ)
                  (x2 : Lt x1 4)
                 → ⋆) --> ⋆ : ⊤
    Evaluate anybSound 0l ℕ positive 3 (NV.snoc 2 (NV.replicate 2 0) 9) ⋆ ℕ
               (λ (x1 : ℕ)
                  (x2 : Lt x1 3)
                  (x3 : IsTrue (positive (NV.snoc 2 (NV.replicate 2 0) 9 x1 x2)))
                 → x1) --> 2 : ℕ
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
    Evaluate sumTo (λ (x1 : ℕ) → if ℕ (isPrime x1) 1 0) 30 --> 10 : ℕ
    Evaluate sumTo (λ (x1 : ℕ) → if ℕ (isPrime x1) x1 0) 30 --> 129 : ℕ
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
                   open N use (y)
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
                   open N use (y; w)
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
  let _ = main_of_multi_string "import Prelude›Builtin›Nat import Lib::Num use (double) module X where eval double 3 end" in
  [%expect {| Evaluate double 3 --> 6 : ℕ |}]

let%expect_test "use as renames the definition" =
  let _ = main_of_multi_string "import Prelude›Builtin›Nat import Lib::Num use (double as dbl) module X where eval dbl 3 end" in
  [%expect {| Evaluate dbl 3 --> 6 : ℕ |}]

let%expect_test "export declares a public definition" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat import Lib::Num module X where module M where import Lib::Num export (double) end \
       eval M.double 3 end"
  in
  [%expect {| Evaluate M.double 3 --> 6 : ℕ |}]

let%expect_test "export as renames the public definition" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat import Lib::Num module X where module M where import Lib::Num export (double as dbl) end \
       eval M.dbl 3 end"
  in
  [%expect {| Evaluate M.dbl 3 --> 6 : ℕ |}]

let%expect_test "a used definition is private to its module" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat import Lib::Num module X where module M where import Lib::Num use (double) end \
       eval M.double 3 end"
  in
  [%expect {| Error: X.M.double is private |}]

let%expect_test "use of a submodule declares a private alias" =
  let _ = main_of_multi_string "import Prelude›Builtin›Nat import Lib::Num use (Ops) module X where eval Ops.pred 3 end" in
  [%expect {| Evaluate Ops.pred 3 --> 2 : ℕ |}]

let%expect_test "export of a submodule declares a public alias" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat import Lib::Num module X where module M where import Lib::Num export (Ops as P) end \
       eval M.P.pred 3 end"
  in
  [%expect {| Evaluate M.P.pred 3 --> 2 : ℕ |}]

let%expect_test "import as declares a private alias" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat use (Nat) import Lib::Num module X where module M where import Lib::Num.Ops as O \
       def z : Nat := O.pred 3 end end eval M.z end"
  in
  [%expect {| Evaluate M.z --> 2 : ℕ |}]

let%expect_test "an alias declared by import as is private" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat import Lib::Num module X where module M where import Lib::Num.Ops as O end \
       eval M.O.pred 3 end"
  in
  [%expect {| Error: X.M.O is private |}]

let%expect_test "an import with arguments and use" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat use (Nat; succ) import Lib::Priv module X where module M where import Lib::Priv.F 4 use (g) \
       def z : Nat := succ g end end eval M.z end"
  in
  [%expect {| Evaluate M.z --> 5 : ℕ |}]

let%expect_test "an import with arguments and export as" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat import Lib::Priv module X where module M where import Lib::Priv.F 4 export (g as h) end \
       eval M.h end"
  in
  [%expect {| Evaluate M.h --> 4 : ℕ |}]

let%expect_test "a member used and exported under two names is rejected" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat import Lib::Priv module X where import Lib::Priv.F 4 use (g) export (g as h) end"
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
    main_of_multi_string "import Prelude›Builtin›Nat use (Nat) import Lib::Num use (double) module X where def double : Nat := 0 end end"
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
      "import Prelude›Builtin›Nat use (Nat) import Lib::Num module X where eval let module L where open Lib::Num use (double as dbl) \
       export (Ops) def t : Nat := dbl 2 end end in L.Ops.pred L.t end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   open Lib›Num use (double as dbl) export (Ops)
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
      "import Prelude›Builtin›Nat import Lib::Num module X where eval let module L where open Lib::Num export (double as dbl) \
       end in L.dbl 2 end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   open Lib›Num export (double as dbl)
                 end
             in M1.dbl 2
             end --> 4 : ℕ
    |}]

let%expect_test "a local submodule use" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat use (Nat) import Lib::Num module X where eval let module L where open Lib::Num use (Ops) \
       def t : Nat := Ops.pred 5 end end in L.t end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   open Lib›Num use (Ops)
                   def t : ℕ ≔
                     Ops.pred 5
                   end
                 end
             in M1.t
             end --> 4 : ℕ
    |}]

let%expect_test "a local open of an inductive type is rejected" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat module X where eval let module L where open Prelude›Builtin›Nat use (Nat) end \
       in 0 end end"
  in
  [%expect {| Error: an inductive type cannot be opened in a local module: Nat |}]

let%expect_test "a local open of an inductive type through a local slot is rejected" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat module X where eval let module W := Prelude›Builtin›Nat in \
       let module L where open W use (Nat) end in 0 end end end"
  in
  [%expect {| Error: an inductive type cannot be opened in a local module: Nat |}]

let%expect_test "a local open of an inductive type through a local alias is rejected" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat module X where eval let module L where module W := Prelude›Builtin›Nat \
       open W use (Nat) end in 0 end end"
  in
  [%expect {| Error: an inductive type cannot be opened in a local module: Nat |}]

let%expect_test "a local open of a constructor and of rec is accepted" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat use (Nat) module X where eval let module L where open Nat use (succ; rec) \
       def two : Nat := succ (succ Nat.zero) end end in L.two end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   open Nat use (succ; rec)
                   def two : ℕ ≔
                     succ (succ Nat.zero)
                   end
                 end
             in M1.two
             end --> 2 : ℕ
    |}]

let%expect_test "a local module alias of an inductive type is a module" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat use (Nat) module X where eval let module L where module N := Nat \
       open N use (succ) def one : Nat := succ N.zero end end in L.one end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   module N ≔ Nat
                   open N use (succ)
                   def one : ℕ ≔
                     succ N.zero
                   end
                 end
             in M1.one
             end --> 1 : ℕ
    |}]

let%expect_test "a local import as" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat use (Nat) import Lib::Num module X where eval let module L where open Lib::Num as W \
       def t : Nat := W.double 1 end end in L.t end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   open Lib›Num as W
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
      "import Prelude›Builtin›Nat import Lib::Num module X where eval let module L where open Lib::Num use (double) end \
       in L.double 2 end end"
  in
  [%expect {| Error: double is private in a local module, but it is used outside it |}]

let%expect_test "a local submodule use is private" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat import Lib::Num module X where eval let module L where open Lib::Num use (Ops) end \
       in L.Ops.pred 2 end end"
  in
  [%expect {| Error: Ops is private in a local module, but it is used outside it |}]

let%expect_test "a local import as is private" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat import Lib::Num module X where eval let module L where open Lib::Num as W end \
       in L.W.double 2 end end"
  in
  [%expect {| Error: W is private in a local module, but it is used outside it |}]

let%expect_test "a local use of a missing member is rejected" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat import Lib::Num module X where eval let module L where open Lib::Num use (q) end in 0 end end"
  in
  [%expect {| Error: Lib›Num.q is not a member |}]

let%expect_test "a local member both used and exported is rejected" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat import Lib::Num module X where eval let module L where open Lib::Num use (double) \
       export (double) end in 0 end end"
  in
  [%expect {| Error: double is used and exported |}]

let%expect_test "a local import of a definition is rejected" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat import Lib::Num module X where eval let module L where open Lib::Num.double use (x) end \
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
  let _ = main_of_multi_string "import Prelude›Builtin›Nat use (Nat) import Lib::Priv as P module X where def x : Nat := P.s end end" in
  [%expect {| Error: Lib›Priv.s is private |}]

let%expect_test "a private member of another unit is not evaluated" =
  let _ = main_of_multi_string "import Lib::Priv as P module X where eval P.s end" in
  [%expect {| Error: Lib›Priv.s is private |}]

let%expect_test "a private member of another unit is not named by its path" =
  let _ = main_of_multi_string "import Lib::Priv module X where eval Lib::Priv.s end" in
  [%expect {| Error: Lib›Priv.s is private |}]

let%expect_test "a private member of another unit is not used in a module body" =
  let _ = main_of_multi_string "import Prelude›Builtin›Nat use (Nat) import Lib::Priv as P module X where module M where def y : Nat := P.s end end end" in
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
  let _ = main_of_body "module P := ℕ" in
  [%expect {| Error: not a module |}]

let%expect_test "an alias of a module is not a term" =
  let _ = main_of_body "module M where end open M as N eval N" in
  [%expect {| Error: Test.N is a module, not a term |}]

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
      "import Prelude›Builtin›Nat use (Nat) module LocalImp where eval let module L where open Prelude::Arith::MinMax use (max) \
       def m : Nat := max 2 3 end end in L.m end end"
  in
  [%expect {| Error: the unit Prelude›Arith›MinMax is not imported |}]

let%expect_test "a local import of a unit imported at the top level" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude›Builtin›Nat use (Nat) import Prelude::Arith::MinMax module LocalImp where eval let module L where \
       open Prelude::Arith::MinMax use (max) def m : Nat := max 2 3 end end in L.m end end"
  in
  [%expect {|
    Evaluate let module M1 where
                   open Prelude›Arith›MinMax use (max)
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
    Error: on "where" (at line 2, column 31 - line 2, column 36): Expected a
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
                   open Prelude›Arith›MinMax use (max)
                   def value : ∀ (x2 : ℕ) → ℕ ≔
                     λ (x3 : ℕ) → At.horner x3 x1 4
                   end
                   def total : ∀ (x4 : ℕ) → ℕ ≔
                     λ (x5 : ℕ) → sumTo value x5
                   end
                   def peak : ∀ (x6 : ℕ) → ℕ ≔
                     λ (x7 : ℕ)
                       → elim x7
                         at x8 → ℕ
                         | zero ⇒ 0
                         | succ x9, x10 ⇒ max (value x9) x10
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
    Evaluate negative minusThree --> Prelude›Data›Bool.Bool.tt
      : Prelude›Data›Bool.Bool
    Evaluate magnitude minusThree --> 3 : ℕ
    Evaluate negative (Additive.Base.pow minusThree 4)
      --> Prelude›Data›Bool.Bool.tt : Prelude›Data›Bool.Bool
    Evaluate magnitude (Additive.Base.pow minusThree 4) --> 12 : ℕ
    Evaluate negative (minus (ofNat 4) (ofNat 9)) --> Prelude›Data›Bool.Bool.tt
      : Prelude›Data›Bool.Bool
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
    Error: on "≔" (at line 2, column 25 - line 2, column 27): Expected a
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
  let _ = main_of_multi_string "import Prelude›Builtin›Nat import Lib::Num module X where open Lib::Num use (double) open Lib::Num.Ops as O eval O.pred (double 2) end" in
  [%expect {| Evaluate O.pred (double 2) --> 3 : ℕ |}]

let%expect_test "an open needs a target" =
  let _ = main_of_body "open use (a)" in
  [%expect {|
    Error: on "use" (at line 2, column 24 - line 2, column 27): Expected the
      module to open: a module in scope, a unit, or a module of a unit.
    |}]

let%expect_test "import names a unit, not a module in scope" =
  let _ = main_of_body "module M where end import M" in
  [%expect {| Error: M: cannot find unit |}]

(** Import only loads *)

let%expect_test "an import declares nothing" =
  let _ = main_of_multi_string "import Prelude›Builtin›Nat import Lib::Num module X where eval double 1 end" in
  [%expect {| Error: unbound name double |}];
  let _ = main_of_multi_string "import Prelude›Builtin›Nat import Lib::Num module X where eval Lib::Num.double 1 end" in
  [%expect {| Evaluate Lib›Num.double 1 --> 2 : ℕ |}]

let%expect_test "a repeated import does nothing" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat import Lib::Num import Lib::Num module X where import Lib::Num module M where import Lib::Num end \
       eval Lib::Num.double 2 end"
  in
  [%expect {| Evaluate Lib›Num.double 2 --> 4 : ℕ |}]

let%expect_test "the long form of import is an import and an open" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat module X where import Lib::Num as N use (double) export (Ops) eval N.double 3 eval double 3 eval Ops.pred 3 end"
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
      "import Prelude›Builtin›Nat import Lib::Num module X where eval let module L where import Lib::Num end in 0 end end"
  in
  [%expect {| Error: import is not allowed in a local module; use open |}]

(** Leading imports and opens *)

let%expect_test "a name imported into a unit with parameters prints as written" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "module Prelude›X (A : Type@0) where import Prelude›Arith›Equality use (Eq) \
       def bad : Eq 1 1 ≔ 0 end end"
  in
  [%expect {| Error: the body of bad, 0, is not of type Eq 1 1 |}];
  let _ =
    main_of_program_string ~search_root:"../lib"
      "module Prelude›Y (A : Type@0) where def foo : ⊤ ≔ ⋆ end \
       module N (B : Type@0) where def bar : ⊤ ≔ foo end def bad : ⊥ ≔ bar end end end"
  in
  [%expect {| Error: the body of bad, bar, is not of type ⊥ |}];
  let _ =
    main_of_program_string ~search_root:"../lib"
      "module Prelude›Z (A : Type@0) where module S where def y : ⊤ ≔ ⋆ end end \
       def bad : ⊥ ≔ S.y end end"
  in
  [%expect {| Error: the body of bad, S.y, is not of type ⊥ |}]

let%expect_test "a leading open in a parameter type" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude›Builtin›Nat import Prelude::Arith::Equality open Prelude::Arith::Equality use (Eq) \
       module ScratchP (p : Eq 1 1) where def q : Eq 1 1 := p end eval q end"
  in
  [%expect {| Evaluate q --> ⋆ : ⊤ |}];
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude›Builtin›Nat import Prelude::Arith::Equality as E use (Eq) \
       module ScratchP (p : Eq 1 1) (q : E.Eq 2 2) where def r : Eq 2 2 := q end eval r end"
  in
  [%expect {| Evaluate r --> ⋆ : ⊤ |}]

let%expect_test "an error names the parameters of the modules around it" =
  let _ =
    main_of_program_string
      "module T (n : Type@0) where module L (m : n) where \
         def x : n := fun (y : n) -> m end end end"
  in
  [%expect {| Error: the body of x, λ (x1 : n) → m, is not of type n |}];
  let _ =
    main_of_program_string
      "module T (x1 : Type@0) where def x : x1 := fun (y : x1) -> y end end"
  in
  [%expect {| Error: the body of x, λ (x1 : $0) → x1, is not of type $0 |}]

let%expect_test "a leading open sees no parameter" =
  let _ = main_of_multi_string "import Prelude›Builtin›Nat use (Nat) import Lib::Priv open Lib::Priv.F n as G module X (n : Nat) where end" in
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
      "module Scratch where open Prelude::Arith::Plus.Basic use (plusIdentityRight) end"
  in
  [%expect {| Error: the unit Prelude›Arith›Plus is not imported |}];
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude›Builtin›Nat import Prelude::Arith::Plus module Scratch where open Prelude::Arith::Plus.Basic use (plusIdentityRight) \
       eval plusIdentityRight 0 end"
  in
  [%expect {| Evaluate plusIdentityRight 0 --> ⋆ : ⊤ |}]

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
    Evaluate succ k --> succ k : ℕ
    |}]

let%expect_test "an axiom of another unit" =
  let _ =
    main_of_multi_string
      "import Prelude›Builtin›Nat use (Nat; succ) import Lib::Axioms module X where def d : Nat := succ Lib::Axioms.c end eval d \
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
  let _ = main_of_program_string "import Prelude›Builtin›Nat use (Nat) axiom x : Nat module T where end" in
  [%expect {|
    Error: on "axiom" (at line 1, column 38 - line 1, column 43): This token is
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
    Evaluate elim 3 at x1 → ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ (succ x3) end --> 6
      : ℕ
    Evaluate elim 2 at x1 → Type@0 | zero ⇒ ℕ | succ x2, A1 ⇒ ∀ (x3 : ℕ) → A1 end
      --> ∀ (x1 : ℕ)
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
      --> elim four at x1 → ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ (succ x3) end : ℕ
    Evaluate succ helper --> 2 : ℕ
    Evaluate double two --> 4 : ℕ
    Evaluate double (succ k)
      --> succ
            (succ
              (elim k at x1 → ℕ | zero ⇒ 0 | succ x2, x3 ⇒ succ (succ x3) end))
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
                   open Twice ℕ double use (twice)
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
                   open Adder 5 use (add) export (addIter)
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
    Evaluate ω+1 --> ω+1 : Level@1
    Evaluate ω·2+1 --> ω·2+1 : Level@2
    Evaluate Level@1 --> Level@1 : Type@0
    Evaluate lift 3l --> 3l : Level@1
    Evaluate ∀ (x1 : Level@1) → Type@{x1} --> ∀ (x1 : Level@1) → Type@{x1}
      : Type@{ω·2}
    Evaluate size (Shape.stack (Shape.line 3)) --> 4 : ℕ
    Evaluate L.List.cons 0l ℕ 1 (L.List.nil 0l ℕ)
      --> Prelude›Data›List.List.cons 0l ℕ 1 (Prelude›Data›List.List.nil 0l ℕ)
      : Prelude›Data›List.List 0l ℕ
    Evaluate L.Ops.length 0l ℕ oneTwo --> 2 : ℕ
    Evaluate cons 3 nil
      --> Prelude›Data›List.List.cons 0l ℕ 3 (Prelude›Data›List.List.nil 0l ℕ)
      : Prelude›Data›List.List 0l ℕ
    Evaluate Pairs.snd twoThree --> 3 : ℕ
    |}]

(** The documentation generator ([Doc]) *)

let doc_lib = lazy (Doc.load "../lib")

let%expect_test "mctt-doc: every name of lib lines up, and every use resolves" =
  List.iter print_endline (Doc.problems (Lazy.force doc_lib));
  [%expect {| |}]

let%expect_test "mctt-doc: a mutual group's recursor module and its functions have anchors" =
  let lib = Lazy.force doc_lib in
  List.iter (fun (u, x, n) -> Printf.printf "%s %d: %s\n" x n (Doc.link_of lib u x n))
    [ ([ "Forests" ], "Rec", 1); ([ "Forests" ], "rec_Tree", 1);
      ([ "Prelude"; "Data"; "Tree"; "Forest" ], "rec_Forest", 1) ];
  (* A view's function of [Rec] is at the group's name too. *)
  (* A fresh directory, made from a fresh file name: [Filename.temp_dir] is
     OCaml 5.1, and CI builds with 4.14. *)
  let dir = Filename.temp_file "mctt-doc" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  Out_channel.with_open_bin (Filename.concat dir "T.mctt") (fun oc -> output_string oc
    "module T where\n\
     inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end\n\
     mutual R where inductive Rose : Type@0 where | node (ts : List Rose) end end\n\
     def f : ⊤ ≔ R.Rec.rec_List_Rose 0l (fun (z : R.Rose) -> ⊤) (fun (z : List R.Rose) -> ⊤)\n\
     \  (fun (ts : List R.Rose) (h : ⊤) -> h) ⋆\n\
     \  (fun (t : R.Rose) (ts : List R.Rose) (ht : ⊤) (hts : ⊤) -> hts) (List.nil R.Rose) end\n\
     end\n");
  let t = Doc.load dir in
  List.iter print_endline (Doc.problems t);
  print_endline (Doc.link_of t [ "T" ] "rec_List_Rose" 1);
  [%expect {|
    Rec 1: line 69: Prelude›Data›Tree›Forest#TreeForest.Rec
    rec_Tree 1: line 69: Prelude›Data›Tree›Forest#TreeForest.Rec.rec_Tree
    rec_Forest 1: line 105: Prelude›Data›Tree›Forest#TreeForest.Rec.rec_Forest
    line 4: T#R.Rec.rec_List_Rose
    |}]

let%expect_test "mctt-doc: a unit comes before the units it is a prefix of" =
  (* [X/] and [X.mctt]: the directory's units come after [X], and [Xa]
     after all of them, segment by segment. *)
  let dir = fresh_dir () in
  Sys.mkdir (Filename.concat dir "X") 0o755;
  Sys.mkdir (Filename.concat dir "X/Nat") 0o755;
  List.iter (fun f -> write_file (Filename.concat dir (f ^ ".mctt"))
                (Printf.sprintf "module %s where\nend\n"
                   (Doc.unit_name (String.split_on_char '/' f))))
    [ "X"; "X/Properties"; "X/Nat"; "X/Nat/Properties"; "Xa"; "A" ];
  let lib = Doc.load ~check:false dir in
  List.iter (fun u -> print_endline (Doc.unit_name u.Doc.u_path)) lib.Doc.units;
  List.iter print_endline (Doc.problems ~resolve:false lib);
  (* The index lists them in the same order. *)
  let out = Filename.concat dir "site" in
  Doc.write_site lib out;
  let index = Doc.read_file (Filename.concat out "index.html") in
  let key = "class=\"unit\" href=\"" in
  let rec find i = if i + String.length key > String.length index then None
    else if String.sub index i (String.length key) = key then Some i else find (i + 1) in
  let rec units i acc = match find i with
    | None -> List.rev acc
    | Some j -> let k = String.index_from index j '>' in
        let e = String.index_from index k '<' in
        units e (String.sub index (k + 1) (e - k - 1) :: acc) in
  print_endline (String.concat " " (units 0 []));
  [%expect {|
    A
    X
    X›Nat
    X›Nat›Properties
    X›Properties
    Xa
    A X X›Nat X›Nat›Properties X›Properties Xa
    |}]

(* The unit [U] of [src], with the [units] it imports, each a name and its
   source, documented and checked: the problems [--check] reports, then
   each use in [U] of one of the names [xs], by line, with what it links
   to. *)
let doc_links ?(units = []) src xs =
  let dir = fresh_dir () in
  List.iter (fun (x, s) -> write_file (Filename.concat dir (x ^ ".mctt")) s) (("U", src) :: units);
  let lib = Doc.load dir in
  List.iter print_endline (Doc.problems lib);
  let u = List.find (fun u -> u.Doc.u_path = [ "U" ]) lib.Doc.units in
  Array.iteri (fun i o ->
      match u.Doc.u_toks.(u.Doc.u_vars.(i)).Doc.t with
      | McttExtracted.Parser.VAR ((p, _), y) when List.mem y xs && o.Doc.anchor = None && not o.Doc.bare ->
          Printf.printf "line %d %s: %s\n" p.Lexing.pos_lnum y
            (match Option.bind o.Doc.link (Doc.resolve lib 0) with
             | Some s -> Doc.unit_name s.Doc.s_unit ^ "#" ^ s.Doc.s_anchor
             | None -> "not linked")
      | _ -> ()) u.Doc.u_occ

let%expect_test "mctt-doc: a field selected from a term links to its record's field" =
  (* Two records with a field [a], both selected from in one command. *)
  doc_links
    "module U where\n\
     record P : Type@0 where a : ⊤; b : ⊤ end\n\
     record Q : Type@0 where a : ⊤ end\n\
     def f (p : P) (q : Q) (h : ∀ (z : ⊤) (w : ⊤) → ⊤) : ⊤ := h p.a q.a end\n\
     def g (q : Q) (p : P) (h : ∀ (z : ⊤) (w : ⊤) → ⊤) : ⊤ := h q.a p.a end\n\
     end\n" [ "a" ];
  [%expect {|
    line 4 a: U#P.a
    line 4 a: U#Q.a
    line 5 a: U#Q.a
    line 5 a: U#P.a
    |}]

let%expect_test "mctt-doc: a with-member selected from a term links to its definition" =
  doc_links
    "module U where\n\
     record P : Type@0 where a : ⊤; b : ⊤ with def sw : ⊤ := b end end end\n\
     def g (p : P) : ⊤ := p.sw end\n\
     def h (p : P) : ⊤ := (P p).sw end\n\
     end\n" [ "sw" ];
  [%expect {|
    line 3 sw: U#P.sw
    line 4 sw: U#P.sw
    |}]

let%expect_test "mctt-doc: a chain of selections from a record value links member by member" =
  doc_links
    "module U where\n\
     record Pair (A : Type@0) (B : Type@0) : Type@0 where fst : A; snd : B\n\
     \  with def swap : Pair B A := record Pair B A where fst := snd; snd := fst end end end end\n\
     def c : ⊤ := (record Pair ⊤ ⊤ where fst := ⋆; snd := ⋆ end).swap.fst end\n\
     eval (record Pair ⊤ ⊤ where fst := ⋆; snd := ⋆ end).swap.snd\n\
     end\n" [ "swap"; "fst"; "snd" ];
  [%expect {|
    line 3 snd: U#Pair.snd
    line 3 fst: U#Pair.fst
    line 4 swap: U#Pair.swap
    line 4 fst: U#Pair.fst
    line 5 swap: U#Pair.swap
    line 5 snd: U#Pair.snd
    |}]

let%expect_test "mctt-doc: a member selected from a function's result or a module's term links" =
  doc_links
    "module U where\n\
     record P : Type@0 where a : ⊤; b : ⊤ with def sw : ⊤ := b end end end\n\
     module M where def k : P := record P where a := ⋆; b := ⋆ end end end\n\
     def l (x : ⊤) : P := M.k end\n\
     def m (y : ⊤) : ⊤ := (l y).sw end\n\
     def j : ⊤ := M.k.a end\n\
     end\n" [ "sw"; "a"; "k" ];
  [%expect {|
    line 4 k: U#M.k
    line 5 sw: U#P.sw
    line 6 k: U#M.k
    line 6 a: U#P.a
    |}]

let%expect_test "mctt-doc: selections from terms link in every kind of declaration" =
  (* Two records with a field [ty]: in a module's parameters and its
     definitions, filed over them; in a record's parameters and fields,
     and its with-area, filed over the record's value; in a group's
     constructors; in a mutual definition's common parameters, result
     and clauses; in local definitions and modules; in an eval and its
     type. *)
  doc_links
    "module U where\n\
     record T : Type@1 where ty : Type@0 end\n\
     record S : Type@1 where ty : Type@0 end\n\
     module K (r : T) (q : S) (x : r.ty) where\n\
     \  def e (y : q.ty) : r.ty := x end\n\
     \  record R (v : q.ty) : Type@0 where f : r.ty with def g (w : q.ty) : r.ty := f end end end\n\
     \  inductive I (v : q.ty) : Type@0 where | i (z : r.ty) end\n\
     end\n\
     inductive W (r : T) : Type@1 where | w (x : r.ty) (s : S) (y : s.ty) end\n\
     inductive N : Type@0 where | z | s (k : N) end\n\
     mutual def (r : T) (q : S) (x : r.ty) (y : q.ty) fn (n : N) : r.ty := | z => x | s k, hk => hk end\n\
     def lt (r : T) (q : S) (x : r.ty) (y : q.ty) : r.ty :=\n\
     \  let v : r.ty := x; w : q.ty := y; module X (u : r.ty) where def o : q.ty := y end end in v end end\n\
     eval ⋆ : (record T where ty := ⊤ end).ty\n\
     end\n" [ "ty" ];
  [%expect {|
    line 4 ty: U#T.ty
    line 5 ty: U#S.ty
    line 5 ty: U#T.ty
    line 6 ty: U#S.ty
    line 6 ty: U#T.ty
    line 6 ty: U#S.ty
    line 6 ty: U#T.ty
    line 7 ty: U#S.ty
    line 7 ty: U#T.ty
    line 9 ty: U#T.ty
    line 9 ty: U#S.ty
    line 11 ty: U#T.ty
    line 11 ty: U#S.ty
    line 11 ty: U#T.ty
    line 12 ty: U#T.ty
    line 12 ty: U#S.ty
    line 12 ty: U#T.ty
    line 13 ty: U#T.ty
    line 13 ty: U#S.ty
    line 13 ty: U#T.ty
    line 13 ty: U#S.ty
    line 14 ty: U#T.ty
    |}]

let%expect_test "mctt-doc: a record value's module, its parameters written out" =
  (* [Pair r.ty ⊤ v] is the module of the value [v]: the [ty] in its
     parameters links as the others do. *)
  doc_links
    "module U where\n\
     record T : Type@1 where ty : Type@0 end\n\
     record Pair (A : Type@0) (B : Type@0) : Type@0 where fst : A; snd : B end\n\
     def f (r : T) (v : Pair r.ty ⊤) : r.ty := (Pair r.ty ⊤ v).fst end\n\
     end\n" [ "ty"; "fst" ];
  [%expect {|
    line 4 ty: U#T.ty
    line 4 ty: U#T.ty
    line 4 ty: U#T.ty
    line 4 fst: U#Pair.fst
    |}]


let%expect_test "mctt-doc: a selection the members of two records could be does not link" =
  (* The pairing alone: [f] as walked has the one selection [p.a], and is
     paired with an [f] filed with two, [a] of [P] and [a] of [Q], either
     of which it could be.  It has a note and no link. *)
  let decls = "module U where\n\
               record P : Type@0 where a : ⊤ end\n\
               record Q : Type@0 where a : ⊤ end\n" in
  let filed = decls ^ "def f (p : P) (q : Q) (h : ∀ (z : ⊤) (w : ⊤) → ⊤) : ⊤ := h p.a q.a end\nend\n" in
  let walked = decls ^ "def f (p : P) (q : Q) (h : ∀ (z : ⊤) (w : ⊤) → ⊤) : ⊤ := h ⋆ p.a end\nend\n" in
  let dir = fresh_dir () in
  write_file (Filename.concat dir "U.mctt") filed;
  (match McttExtracted.Entrypoint.main (Main.load_path_in [ dir ]) Main.read_unit Main.parser_log_fuel
           (Doc.buf_of (Doc.lex filed) 0) with
   | McttExtracted.Entrypoint.AllGood (_, _, th, gu, log) ->
       let u = Doc.walk [ "U" ] walked (Hashtbl.create 1) in
       Doc.record_selections u (([ "U" ], gu) :: th) gu log;
       List.iter print_endline u.Doc.u_notes;
       Array.iteri (fun i o -> match u.Doc.u_toks.(u.Doc.u_vars.(i)).Doc.t with
           | McttExtracted.Parser.VAR ((p, _), "a") when o.Doc.anchor = None ->
               Printf.printf "line %d a: %s\n" p.Lexing.pos_lnum (if o.Doc.link = None then "not linked" else "linked")
           | _ -> ()) u.Doc.u_occ
   | _ -> print_endline "not checked");
  [%expect {|
    a, line 4, a member of one of several records
    line 4 a: not linked
    |}]

let%expect_test "mctt-doc: selections from terms link in aliases and in the arguments of opens" =
  (* In an inductive and a record alias, a module alias, an import's and
     an open's arguments, in a module with a parameter of its own. *)
  doc_links ~units:[ ("A", "module A (X : Type@1) (x : X) where def y : X := x end end\n") ]
    "module U where\n\
     record T : Type@1 where ty : Type@0 end\n\
     record Pair (A : Type@0) (B : Type@0) : Type@0 where fst : A; snd : B end\n\
     inductive Id (A : Type@0) : Type@0 where | refl end\n\
     module F (r : T) where\n\
     \  record PT (s : T) := Pair r.ty s.ty\n\
     \  inductive IT := Id (record T where ty := ⊤ end).ty\n\
     \  import A Type@0 r.ty as B\n\
     \  open A Type@0 r.ty use (y)\n\
     \  module C := A Type@0 r.ty\n\
     end\n\
     end\n" [ "ty" ];
  [%expect {|
    line 6 ty: U#T.ty
    line 6 ty: U#T.ty
    line 7 ty: U#T.ty
    line 8 ty: U#T.ty
    line 9 ty: U#T.ty
    line 10 ty: U#T.ty
    |}]

let%expect_test "mctt-doc: a selection from a term the checker does not file does not link" =
  (* An import that declares nothing is not filed: the [ty] in its
     arguments is matched with nothing the checker found, so it has a note
     and no link. *)
  doc_links ~units:[ ("A", "module A (X : Type@1) (x : X) where def y : X := x end end\n") ]
    "module U where\n\
     record T : Type@1 where ty : Type@0 end\n\
     import A Type@0 (record T where ty := ⊤ end).ty\n\
     end\n" [ "ty" ];
  [%expect {|
    U: ty, line 3, a member of no record the checker found
    U: ty, line 3, not resolved
    line 3 ty: not linked
    |}]

let%expect_test "mctt-doc: every name of examples lines up" =
  List.iter print_endline (Doc.problems ~resolve:false (Doc.load ~check:false "../examples"));
  List.iter print_endline (Doc.problems ~resolve:false (Doc.load ~check:false "../examples/multi"));
  [%expect {| |}]

let%expect_test "mctt-doc: the units the checker rejects are reported" =
  List.iter print_endline (Doc.problems (Doc.load ~extra_roots:lib_root "../examples/multi"));
  [%expect {|
    BadDep: not checked
    Cyc›A: not checked
    Cyc›B: not checked
    Cycle: not checked
    Lib›Bad: not checked
    Lib›Bare: not checked
    Misnamed: not checked
    Missing: not checked
    Transitive: not checked
    |}]

let%expect_test "mctt-doc: a generated member links to its inductive declaration" =
  let lib = Doc.load ~extra_roots:lib_root "../examples/multi" in
  List.iter (fun (x, n) -> Printf.printf "%s %d: %s\n" x n (Doc.link_of lib [ "Generated" ] x n))
    [ ("rec", 1); ("s", 1); ("z", 1); ("rec", 2); ("t", 2); ("rec", 3); ("rec", 4) ];
  [%expect {|
    rec 1: line 15: Lib›Unary#U
    s 1: line 12: Lib›Unary#U.s
    z 1: line 12: Lib›Unary#U.z
    rec 2: line 18: Generated#B
    t 2: line 15: Generated#B.t
    rec 3: line 20: Lib›Unary#U
    rec 4: line 22: Lib›Unary#U
    |}]

let%expect_test "mctt-doc: the contents nest a unit's modules, inductives and exports" =
  let lib = Lazy.force doc_lib in
  let u = List.find (fun u -> u.Doc.u_path = [ "Prelude"; "Data"; "List" ]) lib.Doc.units in
  List.iter (fun e -> Printf.printf "%s%s %s #%s\n" (String.make (2 * e.Doc.te_depth) ' ')
                e.Doc.te_kw e.Doc.te_name e.Doc.te_anchor) u.Doc.u_toc;
  [%expect {|
    inductive List #List
      | nil #List.nil
      | cons #List.cons
    module Ops #Ops
      def length #Ops.length
      def append #Ops.append
      def map #Ops.map
      def foldr #Ops.foldr
      def reverse #Ops.reverse
    |}]

let%expect_test "mctt-doc: a contents entry with no anchor, and an anchor declared twice, are reported" =
  let items = Hashtbl.create 4 in
  (* The parameter [x], the third name, has the local anchor [l2], which is
     also the anchor of the definition [l2]. *)
  let u = Doc.walk [ "Twice" ] "module Twice where\ndef l2 (x : Type@0) : Type@0 := x end\nend\n" items in
  let ghost = { Doc.te_depth = 0; te_name = "ghost"; te_anchor = "ghost"; te_kw = "def"; te_kind = Doc.Def } in
  List.iter print_endline (Doc.toc_problems { u with Doc.u_toc = u.Doc.u_toc @ [ ghost ] });
  [%expect {|
    Twice: the contents entry ghost links to a missing anchor #ghost
    Twice: the anchor #l2 is declared 2 times
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
    524 evals, 524 boxes, 524 equal to mctt's output
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
    Tutorial: 45 evals, 1 outputs
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
    pow line 39: Prelude›Algebra›Monoid#pow
    pow line 39: Prelude›Arith›Pow#pow
    Additive line 22: Prelude›Algebra›Instances#Additive
    pow line 22: Prelude›Algebra›Monoid#pow
    powPlus line 76: Prelude›Algebra›Monoid#Power.powPlus
    plus line 211: Prelude›Arith›Plus#plus
    plus line 212: Prelude›Arith›Plus#plus
    add line 211: declares #Adding.add
    add line 212: Prelude›Arith›Plus#plus
    P line 211: declares #Adding.P
    P line 212: Tutorial#Adding.P
    addIter line 287: Tutorial#Adder.addIter
    x line 47: declares #l20
    x line 47: Tutorial#l20
    |}]

let%expect_test "mctt-doc: ℕ links to the type bound as the natural numbers" =
  let lib = Lazy.force doc_lib in
  let kinds = Doc.anchor_kinds lib in
  (* Every [ℕ] token of lib: each links to [Nat], the type
     Prelude::Builtin::Nat binds, through the imports of its unit. *)
  let link = "<a class=\"ty\" href=\"Prelude.Builtin.Nat.html#Nat\">ℕ</a>" in
  let span = "<span class=\"ty\">ℕ</span>" in
  let links = ref 0 and spans = ref 0 and others = ref 0 in
  List.iter (fun u ->
      let page = Doc.render_unit lib kinds u in
      links := !links + doc_count link page;
      spans := !spans + doc_count span page;
      others := !others + doc_count "ℕ</a>" page - doc_count link page) lib.Doc.units;
  Printf.printf "%d links to Nat, %d other links, %d without a link\n" !links !others !spans;
  (* A unit that binds none: the checker rejects it, and [ℕ] has no link. *)
  let items = Hashtbl.create 4 in
  let u = Doc.walk [ "NoNat" ] "module NoNat where\ndef f (n : ℕ) : ℕ ≔ n end\nend\n" items in
  let thetas = Hashtbl.create 4 and outputs = Hashtbl.create 4 and nats = Hashtbl.create 4 in
  Doc.check_units "../examples" [ u ] thetas outputs nats;
  let lib' = { Doc.root = "../examples"; units = [ u ]; failed = []; thetas; outputs; nats; items } in
  List.iter print_endline (Doc.problems lib');
  let page = Doc.render_unit lib' (Doc.anchor_kinds lib') u in
  Printf.printf "%d links, %d without a link\n" (doc_count "ℕ</a>" page) (doc_count span page);
  [%expect {|
    2717 links to Nat, 0 other links, 0 without a link
    NoNat: not checked
    0 links, 2 without a link
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
  let thetas = Hashtbl.create 4 and outputs = Hashtbl.create 4 and nats = Hashtbl.create 4 in
  Doc.check_units ~extra_roots:lib_root "../examples" us thetas outputs nats;
  { Doc.root = "../examples"; units = us; failed = []; thetas; outputs; nats; items })

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
    118 names: 62 linked, 54 binders
    u line 59: declares #l65
    u line 59: Universes#l65
    u line 60: Universes#l65
    v line 59: declares #l66
    v line 59: Universes#l66
    v line 60: Universes#l66
    depth line 52: Universes#depth
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
    Evaluate C.toNat 0l (CL.cpow 0l (C.fromNat 0l 2) (C.fromNat 1l 5)) --> 32 : ℕ
    Evaluate C.toNat 0l (CL.lower 0l (C.fromNat 1l 4)) --> 4 : ℕ
    Evaluate C.boolToNat 0l (CL.isZero 0l (C.fromNat 1l 0)) --> 1 : ℕ
    Evaluate C.boolToNat 0l (CL.isZero 0l (C.fromNat 1l 3)) --> 0 : ℕ
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
    Evaluate ω+1 --> ω+1 : Level@1
    Evaluate maxl 3l ω·2+1 --> ω·2+1 : Level@2
    Evaluate Level@2 --> Level@2 : Type@0
    Evaluate liftLevel (ofNat 3) --> 3l : Level@1
    Evaluate ∀ (x1 : Level@1) → Type@{x1} --> ∀ (x1 : Level@1) → Type@{x1}
      : Type@{ω·2}
    |}]

(* Inductive types *)

let%expect_test "Inductives.mctt works" =
  let _ = main_of_example "Inductives.mctt" in
  [%expect {|
    Evaluate length ℕ
               (append ℕ (List.cons ℕ 1 (List.cons ℕ 2 (List.nil ℕ)))
                 (List.cons ℕ 3 (List.nil ℕ))) --> 3 : ℕ
    Evaluate append ℕ (List.cons ℕ 1 (List.nil ℕ)) (List.cons ℕ 2 (List.nil ℕ))
      --> List.cons ℕ 1 (List.cons ℕ 2 (List.nil ℕ)) : List ℕ
    Evaluate count ℕ (List.cons ℕ 1 (List.cons ℕ 2 (List.nil ℕ))) --> 2 : ℕ
    Evaluate λ (x1 : List ℕ) → length ℕ (List.cons ℕ 0 x1)
      --> λ (x1 : List ℕ)
            → succ (elim x1 at x2 → ℕ | nil ⇒ 0 | cons x3 x4, x5 ⇒ succ x5 end)
      : ∀ (x1 : List ℕ) → ℕ
    Evaluate (List ℕ).cons 0 (List ℕ).nil --> List.cons ℕ 0 (List.nil ℕ) : List ℕ
    Evaluate cons ℕ 1 (nil ℕ) --> List.cons ℕ 1 (List.nil ℕ) : List ℕ
    Evaluate getOr ℕ 0 (Option.some ℕ 5) --> 5 : ℕ
    Evaluate getOr ℕ 0 (Option.none ℕ) --> 0 : ℕ
    Evaluate size ℕ
               (Tree.node ℕ (Tree.node ℕ (Tree.leaf ℕ) 1 (Tree.leaf ℕ)) 2
                 (Tree.leaf ℕ)) --> 2 : ℕ
    Evaluate snd ℕ (λ (x1 : ℕ) → ℕ) (Sigma.pair ℕ (λ (x2 : ℕ) → ℕ) 1 2) --> 2 : ℕ
    Evaluate steps 0 (Climb.step 0 (Climb.step 1 (Climb.stop 2))) --> 2 : ℕ
    Evaluate climbs 0 (Climb.step 0 (Climb.stop 1)) --> 1 : ℕ
    Evaluate approx omg 3 --> 3 : ℕ
    Evaluate approx (Ord.next omg) 2 --> 3 : ℕ
    Evaluate λ (x1 : ∀ (x2 : ℕ) → Ord) → approx (Ord.lim x1) 1
      --> λ (x1 : ∀ (x2 : ℕ) → Ord)
            → elim x1 1
              at x3 → ℕ
              | base ⇒ 0
              | next x4, x5 ⇒ succ x5
              | lim x6, x7 ⇒ x7 1
              end : ∀ (x1 : ∀ (x2 : ℕ) → Ord) → ℕ
    Evaluate approxRec (Ord.lim (λ (x1 : ℕ) → Ord.next (fin x1))) --> 3 : ℕ
    Evaluate approxA (OrdA.lim (λ (x1 : ℕ) → OrdA.next (OrdA.next OrdA.base))) 0
      --> 2 : ℕ
    Evaluate toNat (wsucc (wsucc (wsucc wzero))) --> 3 : ℕ
    Evaluate wsize (wsucc (wsucc wzero)) --> 3 : ℕ
    Evaluate sample sums --> 6 : ℕ
    Evaluate sample (Grid.node (λ (x1 : ℕ)
                                  (x2 : ℕ)
                                 → sums)) --> 12 : ℕ
    |}]

let%expect_test "a recursive argument names the type at all its parameters" =
  let _ = main_of_body "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List) end" in
  [%expect {| Error: List is not applied to its uniform parameters as declared in the argument xs of cons |}]

let%expect_test "a constructor's argument must live in the type's sort" =
  let _ = main_of_body "inductive Big : Type@0 where | mk (A : Type@0) end" in
  [%expect {| Error: ill-formed inductive declaration Big |}]

let%expect_test "a negative occurrence is rejected by the core" =
  let _ = main_of_body "inductive Bad : Type@0 where | mk (f : forall (x : Bad) -> Nat) end" in
  [%expect {| Error: Bad occurs in the domain of a function in the argument f of mk, which is not strictly positive |}]

let%expect_test "a recursive argument at another uniform parameter is rejected" =
  let _ = main_of_body "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List Nat) end" in
  [%expect {| Error: List is not applied to its uniform parameters as declared in the argument xs of cons |}]

let%expect_test "a recursive argument at too many parameters is rejected" =
  let _ = main_of_body "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A A) end" in
  [%expect {| Error: a recursive argument is List applied to all its parameters |}]

let%expect_test "a negative occurrence beside a positive one is rejected" =
  let _ = main_of_body "inductive Bad : Type@0 where | mk (f : forall (x : Bad) -> Bad) end" in
  [%expect {| Error: Bad occurs in the domain of a function in the argument f of mk, which is not strictly positive |}]

let%expect_test "a function into the type is a recursive argument" =
  let _ = main_of_body "inductive Ord : Type@0 where | lim (f : forall (n : Nat) -> Ord) end" in
  [%expect {| |}]

let%expect_test "a function into the type behind a definition is a recursive argument" =
  let _ = main_of_body "def Arr (X : Type@0) : Type@0 := forall (n : Nat) -> X end \
                        inductive Ord : Type@0 where | lim (f : Arr Ord) end" in
  [%expect {| |}]

let%expect_test "a function into the type of two arguments is a recursive argument" =
  let _ = main_of_body "inductive Grid : Type@0 where | cell | node (f : forall (n : Nat) (m : Nat) -> Grid) end" in
  [%expect {| |}]

let%expect_test "a function into the type at a non-uniform parameter is a recursive argument" =
  let _ = main_of_body "inductive D : forall (k : Nat) -> Type@0 where | leaf | node (f : forall (n : Nat) -> D (succ k)) end" in
  [%expect {| |}]

let%expect_test "the type in the domain of a domain of a function is rejected" =
  let _ = main_of_body "inductive Bad : Type@0 where | mk (f : forall (n : Nat) (x : Bad) -> Bad) end" in
  [%expect {| Error: Bad occurs in the domain of a function in the argument f of mk, which is not strictly positive |}]

let%expect_test "the type in a domain under a function into the type is rejected" =
  let _ = main_of_body "inductive Bad : Type@0 where | mk (f : forall (n : Nat) (g : forall (b : Bad) -> Nat) -> Bad) end" in
  [%expect {| Error: Bad occurs in the domain of a function in the argument f of mk, which is not strictly positive |}]

let%expect_test "a function into the type at another uniform parameter is rejected" =
  let _ = main_of_body "inductive L (A : Type@0) : Type@0 where | mk (f : forall (n : Nat) -> L Nat) end" in
  [%expect {| Error: L is not applied to its uniform parameters as declared in the argument f of mk |}]

let%expect_test "a function into an opaque definition of the type is rejected" =
  let _ = main_of_body "abstract def F (X : Type@0) : Type@0 := X end \
                        inductive Bad : Type@0 where | mk (f : forall (n : Nat) -> F Bad) end" in
  [%expect {| Error: Bad occurs in the argument f of mk under a head that does not compute (an opaque definition, an axiom or a parameter) |}]

let%expect_test "the type in the domain of a function beside a recursive argument is rejected" =
  let _ = main_of_body "inductive V : Type@0 where | leaf | node (l : V) (f : forall (x : V) -> V) end" in
  [%expect {| Error: V occurs in the domain of a function in the argument f of node, which is not strictly positive |}]

let%expect_test "a non-uniform parameter outside the sort is named" =
  let _ = main_of_body "inductive L (A : Type@0) : forall (B : Type@1) -> Type@0 where | mk end" in
  [%expect {|
    Error: the type of the non-uniform parameter 1 of L, Type@1,
      is not in the sort of L, Type@0
    |}]

let%expect_test "a nested occurrence is a view of the container" =
  let _ = main_of_body "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
                        inductive R : Type@0 where | mk (xs : List R) end" in
  [%expect {| |}]

let%expect_test "a nested occurrence under a function is a view of the container" =
  let _ = main_of_body "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
                        inductive R : Type@0 where | mk (f : forall (n : Nat) -> List R) end" in
  [%expect {| |}]

(* An eliminator at an application prints its scrutinee in parentheses, and
   an eliminator applied is parenthesised: both print back as they were
   read. *)
let%expect_test "an eliminator at an application, and applied, round-trip" =
  let _ = main_of_body "inductive Ord : Type@0 where | base | next (o : Ord) | lim (f : forall (n : Nat) -> Ord) end \
                        eval fun (g : forall (n : Nat) -> Ord) -> \
                          elim (g 1) at z -> Nat | base => 0 | next p, r => succ r | lim f, h => h 1 end \
                        eval fun (o : Ord) -> \
                          (elim o at z -> forall (n : Nat) -> Nat \
                           | base => fun (n : Nat) -> n | next p, r => r | lim f, h => fun (n : Nat) -> h n n end) 1" in
  [%expect {|
    Evaluate λ (x1 : ∀ (x2 : ℕ) → Ord)
               → elim x1 1
                 at x3 → ℕ
                 | base ⇒ 0
                 | next x4, x5 ⇒ succ x5
                 | lim x6, x7 ⇒ x7 1
                 end
      --> λ (x1 : ∀ (x2 : ℕ) → Ord)
            → elim x1 1
              at x3 → ℕ
              | base ⇒ 0
              | next x4, x5 ⇒ succ x5
              | lim x6, x7 ⇒ x7 1
              end : ∀ (x1 : ∀ (x2 : ℕ) → Ord) → ℕ
    Evaluate λ (x1 : Ord)
               → (elim x1
                  at x2 → ∀ (x3 : ℕ) → ℕ
                  | base ⇒ λ (x4 : ℕ) → x4
                  | next x5, x6 ⇒ x6
                  | lim x7, x8 ⇒ λ (x9 : ℕ) → x8 x9 x9
                  end)
                   1
      --> λ (x1 : Ord)
            → (elim x1
               at x2 → ∀ (x3 : ℕ) → ℕ
               | base ⇒ λ (x4 : ℕ) → x4
               | next x5, x6 ⇒ λ (x7 : ℕ) → x6 x7
               | lim x8, x9 ⇒ λ (x10 : ℕ) → x9 x10 x10
               end)
                1 : ∀ (x1 : Ord) → ℕ
    |}]

let%expect_test "an argument may not depend on a recursive one" =
  let _ = main_of_body "inductive V : Type@0 where | leaf \
                        | node (v : V) (w : (fun (x : Nat) -> Nat) v) end" in
  [%expect {| Error: the argument w of node depends on a recursive argument |}]

let%expect_test "a function argument in which the type does not occur is not recursive" =
  let _ = main_of_body "inductive F : Type@0 where | mk (f : forall (n : Nat) -> Nat) end \
                        eval F.mk (fun (n : Nat) -> succ n)" in
  [%expect {| Evaluate F.mk (λ (x1 : ℕ) → succ x1) --> F.mk (λ (x1 : ℕ) → succ x1) : F |}]

let%expect_test "a branch with the wrong number of names is rejected" =
  let _ = main_of_body "inductive N : Type@0 where | z | s (n : N) end \
                        def f (n : N) : N := elim n at k -> N | z => N.z | s m => m end end" in
  [%expect {| Error: the branch s binds 1 name but needs 2 (1 argument, 1 induction hypothesis) |}]

let%expect_test "a branch missing the induction hypothesis names what it needs" =
  let _ = main_of_body "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
                        def len (l : List Nat) : Nat := \
                          elim l at k -> Nat | nil => 0 | cons x xs => 0 end end" in
  [%expect {| Error: the branch cons binds 2 names but needs 3 (2 arguments, 1 induction hypothesis) |}]

let%expect_test "a branch for a name that is not a constructor is rejected" =
  let _ = main_of_body "inductive N : Type@0 where | z | s (n : N) end \
                        def f (n : N) : N := elim n at k -> N | z => N.z | t m, h => m end end" in
  [%expect {| Error: t is not a constructor of the eliminated type |}]

let%expect_test "an eliminator missing a branch is rejected" =
  let _ = main_of_body "inductive N : Type@0 where | z | s (n : N) end \
                        def f (n : N) : N := elim n at k -> N | z => N.z end end" in
  [%expect {| Error: the eliminator has no branch for s |}]

let%expect_test "an eliminator with two branches for a constructor is rejected" =
  let _ = main_of_body "inductive N : Type@0 where | z | s (n : N) end \
                        def f (n : N) : N := elim n at k -> N | z => N.z | z => N.z | s m, h => m end end" in
  [%expect {| Error: the eliminator has two branches for z |}]

let%expect_test "a term variable shadowing a module is a term, of no record type" =
  let _ = main_of_body "module B where def Id : Nat := 0 end end \
                        def f (B : Nat) : Nat := B.Id end" in
  [%expect {| Error: Id is selected from B, of type ℕ, which is not a record type |}]

let%expect_test "the branches must follow the constructors' order" =
  let _ = main_of_body "inductive N : Type@0 where | z | s (n : N) end \
                        def f (n : N) : N := elim n at k -> N | s m, h => m | z => N.z end end" in
  [%expect {| Error: the branches must follow the order of the constructors: z, s |}]

let%expect_test "an inductive type's name is a member of its frame" =
  let _ = main_of_body "def N : Nat := 0 end inductive N : Type@0 where | z end" in
  [%expect {| Error: N is already declared |}]

let%expect_test "an inductive type is declared under the parameters of its module" =
  let _ = main_of_body "module L (A : Type@0) where \
                          inductive List : Type@0 where | nil | cons (x : A) (xs : List) end \
                          def len (l : List) : Nat := elim l at (z : List) -> Nat | nil => 0 | cons x xs, r => succ r end end \
                        end \
                        eval L.len Nat (L.List.cons Nat 1 (L.List.nil Nat))" in
  [%expect {| Evaluate L.len ℕ (L.List.cons ℕ 1 (L.List.nil ℕ)) --> 1 : ℕ |}]

let%expect_test "an inductive type is a module over its uniform parameters" =
  let _ = main_of_body "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
                        eval (List Nat).cons 1 (List.nil Nat) : List Nat" in
  [%expect {| Evaluate (List ℕ).cons 1 (List.nil ℕ) --> List.cons ℕ 1 (List.nil ℕ) : List ℕ |}]

let%expect_test "a constructor is not a member of the type's frame" =
  let _ = main_of_body "inductive N : Type@0 where | z end eval z" in
  [%expect {| Error: unbound name z |}]

let%expect_test "constructors of two types may share a name" =
  let _ = main_of_body "inductive N : Type@0 where | z end inductive M : Type@0 where | z end \
                        eval M.z" in
  [%expect {| Evaluate M.z --> M.z : M |}]

(* Only the direct path of an inductive type is its type former; an alias
   of it, or a name an open declares for it, is a module (option B). *)
let%expect_test "an alias of an inductive type is a module, not the type" =
  let _ = main_of_body "inductive N : Type@0 where | z end module M := N eval M.z : M" in
  [%expect {| Error: Test.M is a module, not a term |}]

let%expect_test "an alias of an inductive type has its constructors" =
  let _ = main_of_body "inductive N : Type@0 where | z end module M := N eval M.z : N" in
  [%expect {| Evaluate M.z --> N.z : N |}]

let%expect_test "an alias of a parameterised inductive type is not applied as the type" =
  let _ = main_of_body "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
                        module L := List eval L Nat" in
  [%expect {| Error: Test.L is a module, not a term |}]

let%expect_test "an inductive type opened from a module is the type and its module" =
  let _ = main_of_body "module A where inductive N : Type@0 where | z end end \
                        open A use (N) eval N.z : N" in
  [%expect {| Evaluate N.z --> A.N.z : N |}]

let%expect_test "an inductive type opened under another name has its constructors and eliminator" =
  let _ = main_of_body "module A where inductive N : Type@0 where | z | s (n : N) end end \
                        open A use (N as K) eval K.s K.z : A.N \
                        eval elim (K.s K.z) at k -> Nat | z => 0 | s m, h => succ h end" in
  [%expect {|
    Evaluate K.s K.z --> A.N.s A.N.z : A.N
    Evaluate elim K.s K.z at x1 → ℕ | z ⇒ 0 | s x2, x3 ⇒ succ x3 end --> 1 : ℕ
    |}]

let%expect_test "an inductive type imported into a unit with parameters" =
  let _ = main_of_multi_string "import Lib›Unary module Test (A : Type@0) where \
                                def two : Lib›Unary.U := Lib›Unary.U.s (Lib›Unary.U.s Lib›Unary.U.z) end \
                                eval Lib›Unary.plus two two \
                                eval fun (n : Lib›Unary.U) -> elim n at x -> Lib›Unary.U \
                                  | z => two | s p, r => r end end" in
  [%expect {|
    Evaluate Lib›Unary.plus two two --> 4 : ℕ
    Evaluate λ (x1 : ℕ) → elim x1 at x2 → ℕ | z ⇒ two | s x3, x4 ⇒ x4 end
      --> λ (x1 : ℕ) → elim x1 at x2 → ℕ | z ⇒ 2 | s x3, x4 ⇒ x4 end
      : ∀ (x1 : ℕ) → ℕ
    |}]

let%expect_test "a private inductive type is a private module of public constructors" =
  let _ = main_of_body "module M where private inductive N : Type@0 where | z end eval N.z end" in
  [%expect {| Evaluate M.N.z --> M.N.z : M.N |}]

let%expect_test "a private inductive type is out of reach outside its module" =
  let _ = main_of_body "module M where private inductive N : Type@0 where | z end end eval M.N.z" in
  [%expect {| Error: Test.M.N is private |}]

let%expect_test "an inductive alias is the type at its arguments, as a term and as a module" =
  let _ = main_of_body "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
                        inductive LN := List Nat \
                        inductive L (B : Type@0) := List B \
                        inductive LN2 := L Nat \
                        eval LN \
                        eval L Nat \
                        eval LN.cons 1 LN.nil : LN2 \
                        eval L.cons Nat 1 (L.nil Nat) : List Nat \
                        eval fun (l : LN2) -> elim l at (z : LN2) -> Nat | nil => 0 | cons x xs, r => succ r end \
                        eval L.rec Nat 0l (fun (l : List Nat) -> Nat) 0 \
                          (fun (x : Nat) (xs : List Nat) (r : Nat) -> succ r) (LN.cons 1 LN.nil)" in
  [%expect {|
    Evaluate LN --> List ℕ : Type@0
    Evaluate L ℕ --> List ℕ : Type@0
    Evaluate LN.cons 1 LN.nil --> List.cons ℕ 1 (List.nil ℕ) : LN2
    Evaluate L.cons ℕ 1 (L.nil ℕ) --> List.cons ℕ 1 (List.nil ℕ) : List ℕ
    Evaluate λ (x1 : LN2)
               → elim x1
                 at (x2 : LN2) → ℕ
                 | nil ⇒ 0
                 | cons x3 x4, x5 ⇒ succ x5
                 end
      --> λ (x1 : List ℕ)
            → elim x1 at x2 → ℕ | nil ⇒ 0 | cons x3 x4, x5 ⇒ succ x5 end
      : ∀ (x1 : List ℕ) → ℕ
    Evaluate L.rec ℕ 0l (λ (x1 : List ℕ) → ℕ) 0
               (λ (x2 : ℕ)
                  (x3 : List ℕ)
                  (x4 : ℕ)
                 → succ x4)
               (LN.cons 1 LN.nil) --> 1 : ℕ
    |}]

let%expect_test "an inductive alias names an inductive type" =
  let _ = main_of_body "module M where end inductive X := M" in
  [%expect {| Error: Test.M is not an inductive type |}]

let%expect_test "an inductive alias takes no more arguments than the uniform parameters" =
  let _ = main_of_body "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
                        inductive Y := List Nat Nat" in
  [%expect {| Error: inductive alias Y: more arguments than uniform parameters of List |}]

let%expect_test "an inductive alias's arguments are typed" =
  let _ = main_of_body "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
                        inductive Z := List zero" in
  [%expect {| Error: ill-formed inductive alias Z |}]

let%expect_test "a private inductive alias is out of reach outside its module" =
  let _ = main_of_body "module M where inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
                          private inductive LN := List Nat eval LN.nil end \
                        eval M.LN.nil" in
  [%expect {| Error: Test.M.LN is private |}]

let%expect_test "an eliminator takes its type from its scrutinee" =
  let _ = main_of_body "inductive N : Type@0 where | z | s (n : N) end \
                        eval elim (N.s N.z) at k -> Nat | z => 0 | s m, h => succ h end" in
  [%expect {| Evaluate elim N.s N.z at x1 → ℕ | z ⇒ 0 | s x2, x3 ⇒ succ x3 end --> 1 : ℕ |}]

let%expect_test "an eliminator with no branches is rejected" =
  let _ = main_of_body "eval fun (n : Nat) -> elim n at k -> Nat end" in
  [%expect {| Error: the eliminator has no branch for zero |}]

let%expect_test "an eliminator is no member of its type" =
  let _ = main_of_body "inductive N : Type@0 where | z end \
                        eval fun (n : N) -> N.elim n at k -> Nat | z => 0 end" in
  [%expect {|
    Error: on "elim" (at line 2, column 76 - line 2, column 80): Expected a
      member name or "rec" after ".".
    |}]

let%expect_test "the recursor of a type under module parameters takes them first" =
  let _ = main_of_body "module L (A : Type@0) where \
                          inductive List : Type@0 where | nil | cons (x : A) (xs : List) end \
                        end \
                        eval L.List.rec Nat 0l (fun (l : L.List Nat) -> Nat) 0 \
                          (fun (x : Nat) (xs : L.List Nat) (r : Nat) -> succ r) (L.List.cons Nat 1 (L.List.nil Nat))" in
  [%expect {|
    Evaluate L.List.rec ℕ 0l (λ (x1 : L.List ℕ) → ℕ) 0
               (λ (x2 : ℕ)
                  (x3 : L.List ℕ)
                  (x4 : ℕ)
                 → succ x4)
               (L.List.cons ℕ 1 (L.List.nil ℕ)) --> 1 : ℕ
    |}]

let%expect_test "the recursor of the empty type" =
  let _ = main_of_body "inductive E : Type@0 where end \
                        eval fun (e : E) -> E.rec 0l (fun (z : E) -> False) e" in
  [%expect {|
    Evaluate λ (x1 : E) → E.rec 0l (λ (x2 : E) → ⊥) x1
      --> λ (x1 : E) → elim x1 at x2 → ⊥ end : ∀ (x1 : E) → ⊥
    |}]

let%expect_test "an argument is classified as its normal form" =
  let _ = main_of_body "def Id (X : Type@0) : Type@0 := X end \
                        inductive N : Type@0 where | z | s (n : Id N) end \
                        eval N.s (N.s N.z)" in
  [%expect {| Evaluate N.s (N.s N.z) --> N.s (N.s N.z) : N |}]

let%expect_test "an argument whose normal form is free of the type is not recursive" =
  let _ = main_of_body "inductive N : Type@0 where | mk (f : (fun (X : Type@0) -> Nat) (forall (a : N) -> Nat)) end \
                        eval N.mk 3" in
  [%expect {| Evaluate N.mk 3 --> N.mk 3 : N |}]

let%expect_test "a let or a transparent member in an argument is unfolded" =
  let _ = main_of_body "module M where def F (X : Type@0) : Type@0 := X end end \
                        inductive N : Type@0 where | z | s (n : M.F N) | t (n : let Y : Type@0 := N in Y end) end \
                        eval N.t (N.s N.z)" in
  [%expect {| Evaluate N.t (N.s N.z) --> N.t (N.s N.z) : N |}]

let%expect_test "a negative occurrence behind a definition is rejected" =
  let _ = main_of_body "def Neg (X : Type@0) : Type@0 := forall (x : X) -> False end \
                        inductive Bad : Type@0 where | mk (f : Neg Bad) end" in
  [%expect {| Error: Bad occurs in the domain of a function in the argument f of mk, which is not strictly positive |}]

let%expect_test "a non-strictly positive occurrence is rejected" =
  let _ = main_of_body "inductive Bad : Type@0 where | mk (f : forall (g : forall (b : Bad) -> Type@0) -> Type@0) end" in
  [%expect {| Error: Bad occurs in the domain of a function in the argument f of mk, which is not strictly positive |}]

let%expect_test "the type under an opaque definition is rejected" =
  let _ = main_of_body "abstract def F (X : Type@0) : Type@0 := X end \
                        inductive Bad : Type@0 where | mk (f : F Bad) end" in
  [%expect {| Error: Bad occurs in the argument f of mk under a head that does not compute (an opaque definition, an axiom or a parameter) |}]

let%expect_test "the type under an axiom is rejected" =
  let _ = main_of_body "axiom G : forall (X : Type@0) -> Type@0 \
                        inductive Bad : Type@0 where | mk (f : G Bad) end" in
  [%expect {| Error: Bad occurs in the argument f of mk under a head that does not compute (an opaque definition, an axiom or a parameter) |}]

let%expect_test "the type under a module parameter is rejected" =
  let _ = main_of_body "module M (F : forall (X : Type@0) -> Type@0) where \
                          inductive Bad : Type@0 where | mk (f : F Bad) end \
                        end" in
  [%expect {| Error: Bad occurs in the argument f of mk under a head that does not compute (an opaque definition, an axiom or a parameter) |}]

let%expect_test "an inductive type is not allowed in a local module" =
  let _ = main_of_body "eval let module M where inductive E : Type@0 where end end in zero end" in
  [%expect {| Error: an inductive type is not allowed in a local module |}]

let%expect_test "an eliminator needs a motive" =
  let _ = main_of_body "eval fun (x : Nat) -> elim x | zero => zero end" in
  [%expect {|
    Error: on "|" (at line 2, column 48 - line 2, column 49): An eliminator "elim
      M" is expected to be followed by its blocks, one per member of the group in
      member order, the scrutinee's marked "at", the others "with":
      "elim M at (z : T) -> ?motive | c xs ⇒ ?body … end".
    |}]

let%expect_test "an inductive type needs its type" =
  let _ = main_of_body "inductive E where end" in
  [%expect {|
    Error: on "where" (at line 2, column 31 - line 2, column 36): The uniform
      parameters of an inductive type are expected to be followed by ":" and its
      type, or, for an inductive alias, by ":=" and the type it names.
    |}]

(* [builtin natural ≔ X]: the numerals where the binding is visible. *)
let%expect_test "the bound natural numbers: numerals and their printing" =
  let _ = main_of_example "Builtin.mctt" in
  [%expect {|
    Evaluate plus 2 3 --> 5 : ℕ
    Evaluate mult 6 7 --> 42 : ℕ
    Evaluate 2 --> 2 : ℕ
    Evaluate λ (x1 : ℕ) → plus 2 x1 --> λ (x1 : ℕ) → S (S x1) : ∀ (x1 : ℕ) → ℕ
    |}]

let%expect_test "a numeral is the bound type's where the binding is imported" =
  let _ = main_of_multi_string "module Main where import Lib›Unary use (U; plus) eval plus 2 3 eval 0 : U end" in
  [%expect {|
    Evaluate plus 2 3 --> 5 : ℕ
    Evaluate 0 --> 0 : ℕ
    |}]

let%expect_test "a numeral needs a bound natural-number type" =
  let _ = main_of_bare_body "eval 3" in
  [%expect {| Error: unknown numeral 3: no natural-number type is bound |}]

let%expect_test "the token ℕ needs a bound natural-number type" =
  let _ = main_of_bare_body "eval λ (n : ℕ) → n" in
  [%expect {| Error: unknown type ℕ: no natural-number type is bound |}]

let%expect_test "two imports binding different types conflict" =
  let _ = main_of_multi_string "module Main where import Lib›Unary import Lib›Peano eval 1 end" in
  [%expect {| Error: the natural numbers are bound already, to U |}]

(* A unit sees the bindings it makes and those of what it imports, never
   those of the unit importing it. *)
let%expect_test "an imported unit does not see the binding of its importer" =
  let _ = main_of_multi_string "module Main where import Prelude›Builtin›Nat import Lib›Bare end" in
  [%expect {| Error: unknown numeral 2: no natural-number type is bound |}]

let%expect_test "a binding reached along two import paths is the same binding" =
  let _ = main_of_multi_string "module Main where import Lib›Num import Lib›Arith eval Lib›Arith.quadruple 1 end" in
  [%expect {| Evaluate Lib›Arith.quadruple 1 --> 4 : ℕ |}]

let%expect_test "a binding made in the body does not reach a unit it imports" =
  let _ = main_of_multi_string "module Main where inductive N : Type@0 where | z | s (n : N) end \
                                builtin natural := N module M where import Lib›Bare end end" in
  [%expect {| Error: unknown numeral 2: no natural-number type is bound |}]

let%expect_test "a binding made in the body meets that of a unit it imports later" =
  let _ = main_of_multi_string "module Main where inductive N : Type@0 where | z | s (n : N) end \
                                builtin natural := N module M where import Lib›Num end end" in
  [%expect {| Error: the natural numbers are bound already, to N |}]

let%expect_test "a binding made after an import meets that of the import" =
  let _ = main_of_multi_string "module Main where import Lib›Num inductive N : Type@0 where | z | s (n : N) end \
                                builtin natural := N end" in
  [%expect {| Error: the natural numbers are bound already, to Nat |}]

let%expect_test "the natural numbers are bound once" =
  let _ = main_of_multi_string "module Main where import Lib›Unary \
                                 inductive N : Type@0 where | z | s (n : N) end \
                                 builtin natural := N end" in
  [%expect {| Error: the natural numbers are bound already, to U |}]

let%expect_test "binding the same type again is allowed" =
  let _ = main_of_bare_body "inductive N : Type@0 where | z | s (n : N) end \
                             builtin natural := N builtin natural := N eval 2" in
  [%expect {| Evaluate 2 --> 2 : ℕ |}]

let%expect_test "a binding needs the shape of the natural numbers" =
  let _ = main_of_bare_body "inductive L : Type@0 where | nil | cons (l : L) (m : L) end \
                             builtin natural := L" in
  [%expect {| Error: L is not shaped as the natural numbers: it must have no parameter, one constructor without arguments and one with a single recursive argument |}]

let%expect_test "a binding needs the type in Type@0" =
  let _ = main_of_bare_body "inductive N : Type@1 where | z | s (n : N) end builtin natural := N" in
  [%expect {| Error: the natural numbers must be declared in Type@0, not N |}]

let%expect_test "a binding through an inductive alias without arguments" =
  let _ = main_of_bare_body "inductive N : Type@0 where | z | s (n : N) end inductive M := N \
                             builtin natural := M eval 2" in
  [%expect {| Evaluate 2 --> 2 : ℕ |}]

let%expect_test "a binding with the constructors in the other order" =
  let _ = main_of_bare_body "inductive N : Type@0 where | s (n : N) | z end \
                             builtin natural := N eval 2" in
  [%expect {| Evaluate 2 --> 2 : ℕ |}]

let%expect_test "a binding is of an inductive type" =
  let _ = main_of_bare_body "def D : Type@1 := Type@0 end builtin natural := D" in
  [%expect {| Error: Test.D is not an inductive type |}]

let%expect_test "natural is the only builtin" =
  let _ = main_of_bare_body "inductive N : Type@0 where | z | s (n : N) end builtin integer := N" in
  [%expect {| Error: there is no builtin integer |}]

let%expect_test "a binding may be made in a module, and holds after it" =
  let _ = main_of_bare_body "module M where inductive N : Type@0 where | z | s (n : N) end \
                             builtin natural := N end eval 2" in
  [%expect {| Evaluate 2 --> 2 : ℕ |}]

(* A bound type with constructors named otherwise than [zero] and [succ]:
   numerals, an eliminator over the constructors' own names, and the
   printing of both. *)
let%expect_test "a bound type with its own constructor names" =
  let _ = main_of_bare_body "inductive Num : Type@0 where | Z | S (n : Num) end builtin natural := Num \
                             open Num use (Z; S) \
                             eval elim 3 at x -> Num | Z => Z | S k, r => S (S r) end \
                             eval fun (n : Num) -> S (S n) eval S Z : Num" in
  [%expect {|
    Evaluate elim 3 at x1 → ℕ | Z ⇒ 0 | S x2, x3 ⇒ S (S x3) end --> 6 : ℕ
    Evaluate λ (x1 : ℕ) → S (S x1) --> λ (x1 : ℕ) → S (S x1) : ∀ (x1 : ℕ) → ℕ
    Evaluate 1 --> 1 : ℕ
    |}]

let%expect_test "a constructor chain of the bound type in an error prints as a numeral" =
  let _ = main_of_bare_body "inductive Num : Type@0 where | Z | S (n : Num) end builtin natural := Num \
                             open Num use (Z; S) eval S Z : Type@0" in
  [%expect {| Error: 1 is not of type Type@0 |}]

let%expect_test "a binding is not allowed in a local module" =
  let _ = main_of_body "eval let module M where builtin natural := N end in zero end" in
  [%expect {| Error: builtin is not allowed in a local module |}]

let%expect_test "a binding needs its type" =
  let _ = main_of_body "builtin natural N" in
  [%expect {|
    Error: on "N" (at line 2, column 35 - line 2, column 36): The kind of a
      builtin is expected to be followed by ":=" and the type bound, as in
      "builtin natural := Nat".
    |}]

(* An identifier may contain digits and underscores after its first
   character, and start with an underscore. *)
let%expect_test "names with digits and underscores" =
  let _ = main_of_body "def x_1 : Nat := 1 end def Num2 : Nat := succ x_1 end \
                        def _y : Nat := Num2 end def zero1 : Nat := zero end \
                        module M_2 where def List_2 : Nat := _y end end \
                        eval M_2.List_2 eval zero1 eval fun (x1 : Nat) -> x1" in
  [%expect {|
    Evaluate M_2.List_2 --> 2 : ℕ
    Evaluate zero1 --> 0 : ℕ
    Evaluate λ (x1 : ℕ) → x1 --> λ (x1 : ℕ) → x1 : ∀ (x1 : ℕ) → ℕ
    |}]

let%expect_test "a unit name may contain digits" =
  let _ = main_of_program_string "import Prelude›Builtin›Nat use (Nat) module T_2 where def a1 : Nat := 3 end eval a1 end" in
  [%expect {| Evaluate a1 --> 3 : ℕ |}]

let%expect_test "a numeral and a level literal stay one token" =
  let _ = main_of_body "def l2 : Level := 2l end eval Type@{l2} eval Type@{3L} eval 12" in
  [%expect {|
    Evaluate Type@{l2} --> Type@2 : Type@3
    Evaluate Type@3L --> Type@3L : Type@4L
    Evaluate 12 --> 12 : ℕ
    |}]

let%expect_test "a bare underscore is reserved" =
  let _ = main_of_body "def _ : Nat := 0 end" in
  [%expect {| Error: "_" is reserved, and not a name, at line 2, column 23 |}]

(* A branch of a printed eliminator writes its induction hypotheses after a
   comma, so that the printed term reads back as itself. *)
let%expect_test "a printed eliminator separates the induction hypotheses by a comma" =
  let _ = main_of_body "inductive N : Type@0 where | Z | S (n : N) end \
                        eval fun (n : N) -> elim n at k -> N | Z => N.Z | S m, h => N.S h end" in
  [%expect {|
    Evaluate λ (x1 : N) → elim x1 at x2 → N | Z ⇒ N.Z | S x3, x4 ⇒ N.S x4 end
      --> λ (x1 : N) → elim x1 at x2 → N | Z ⇒ N.Z | S x3, x4 ⇒ N.S x4 end
      : ∀ (x1 : N) → N
    |}]

let%expect_test "a printed eliminator reads back as itself" =
  let _ = main_of_body "inductive N : Type@0 where | Z | S (n : N) end \
                        eval λ (x1 : N) → elim x1 at x2 -> N | Z ⇒ N.Z | S x3, x4 ⇒ N.S x4 end" in
  [%expect {|
    Evaluate λ (x1 : N) → elim x1 at x2 → N | Z ⇒ N.Z | S x3, x4 ⇒ N.S x4 end
      --> λ (x1 : N) → elim x1 at x2 → N | Z ⇒ N.Z | S x3, x4 ⇒ N.S x4 end
      : ∀ (x1 : N) → N
    |}]

(** Members through what module expressions denote *)

let%expect_test "a member of a module alias is the member of its target" =
  let _ = main_of_body "module P where axiom c : Nat end module A := P \
                        axiom F (n : Nat) : Type@0 axiom f : F P.c eval f : F A.c" in
  [%expect {| Evaluate f --> f : F A.c |}]

let%expect_test "a member of a local alias with a parameter is the target's member under it" =
  let _ = main_of_body "module Q where axiom c : Nat end axiom F (n : Nat) : Type@0 \
                        axiom g : forall (n : Nat) -> F Q.c \
                        eval let module L (n : Nat) := Q in let h : forall (n : Nat) -> F (L.c n) := g in h end end" in
  [%expect {|
    Evaluate let module M1 (x1 : ℕ) ≔ Q; x2 : ∀ (x3 : ℕ) → F (M1.c x3) ≔ g
             in x2
             end --> λ (x1 : ℕ) → g x1 : ∀ (x1 : ℕ) → F Q.c
    |}]

let%expect_test "an abstract member of a local module is not of its type outside it" =
  let _ = main_of_body "eval let module X where abstract def f : Nat := 0 end end in X.f end : Nat" in
  [%expect {|
    Error: let module M1 where
                 abstract def f : ℕ ≔
                   0
                 end
               end in M1.f end is not of type ℕ
    |}]

let%expect_test "an inductive type through a unit alias" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude›Builtin›Nat use (Nat; zero; succ) import Prelude›Data›List as M \
       module X where eval M.List 0l Nat eval M.List.cons 0l Nat 1 (M.List.nil 0l Nat) end"
  in
  [%expect {|
    Evaluate M.List 0l ℕ --> Prelude›Data›List.List 0l ℕ : Type@0
    Evaluate M.List.cons 0l ℕ 1 (M.List.nil 0l ℕ)
      --> Prelude›Data›List.List.cons 0l ℕ 1 (Prelude›Data›List.List.nil 0l ℕ)
      : Prelude›Data›List.List 0l ℕ
    |}]

let%expect_test "an inductive type used from an applied unit" =
  let _ = main_of_multi_string "import Lib›Boxed ⊤ use (Box) module X where eval Box end" in
  [%expect {| Evaluate Box --> Lib›Boxed.Box ⊤ : Type@0 |}]

let%expect_test "an inductive alias of an inductive alias" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude›Builtin›Nat use (Nat; zero; succ) import Prelude›Data›Prod use (Prod) \
       module X where inductive A2 (B : Type@0) := Prod 0l B B inductive K := A2 \
       axiom F (X : Type@0) : Type@0 axiom f : F (Prod 0l Nat Nat) eval f : F (K Nat) eval (K Nat).pair 1 2 end"
  in
  [%expect {|
    Evaluate f --> f : F (K ℕ)
    Evaluate (K ℕ).pair 1 2 --> Prelude›Data›Prod.Prod.pair 0l ℕ ℕ 1 2
      : Prelude›Data›Prod.Prod 0l ℕ ℕ
    |}]

let%expect_test "the natural numbers bound through a module alias" =
  let _ = main_of_body "module M := Prelude›Builtin›Nat builtin natural := M.Nat eval 3" in
  [%expect {| Evaluate 3 --> 3 : ℕ |}]

let%expect_test "an alias of an inductive type's module is a module, not a term" =
  let _ =
    main_of_program_string ~search_root:"../lib"
      "import Prelude›Data›List use (List) module X where import Prelude›Builtin›Nat use (Nat) \
       module L := List eval L 0l Nat end"
  in
  [%expect {| Error: X.L is a module, not a term |}]

(** Groups: mutual declarations, nested occurrences, eliminator blocks,
    mutual definitions and the recursor module of a group *)

let group_tm_sp =
  "mutual S where inductive Tm : Type@0 where | var (n : Nat) | app (f : Tm) (s : Sp) \
   with Sp : Type@0 where | snil | scons (t : Tm) (s : Sp) end end "

let%expect_test "a mutual group is eliminated with one block per member" =
  let _ = main_of_body (group_tm_sp ^
    "eval elim (S.Tm.app (S.Tm.var 0) (S.Sp.scons (S.Tm.var 1) S.Sp.snil)) \
       at (z : S.Tm) -> Nat | var n => 1 | app f s, hf hs => succ hs \
       with (z : S.Sp) -> Nat | snil => 0 | scons t s, ht hs => succ hs end") in
  [%expect {|
    Evaluate elim S.Tm.app (S.Tm.var 0) (S.Sp.scons (S.Tm.var 1) S.Sp.snil)
             at (x1 : S.Tm) → ℕ
             | var x2 ⇒ 1
             | app x3 x4, x5 x6 ⇒ succ x6
             with (x7 : S.Sp) → ℕ
             | snil ⇒ 0
             | scons x8 x9, x10 x11 ⇒ succ x11
             end --> 2 : ℕ
    |}]

let%expect_test "an eliminator marks exactly one block at" =
  let _ = main_of_body (group_tm_sp ^
    "eval fun (t : S.Tm) -> elim t \
       at (z : S.Tm) -> Nat | var n => 1 | app f s, hf hs => hs \
       at (z : S.Sp) -> Nat | snil => 0 | scons t s, ht hs => hs end") in
  [%expect {| Error: exactly one block of an eliminator is marked at, the scrutinee's |}]

let%expect_test "an eliminator needs a block marked at" =
  let _ = main_of_body (group_tm_sp ^
    "eval fun (t : S.Tm) -> elim t \
       with (z : S.Tm) -> Nat | var n => 1 | app f s, hf hs => hs \
       with (z : S.Sp) -> Nat | snil => 0 | scons t s, ht hs => hs end") in
  [%expect {| Error: exactly one block of an eliminator is marked at, the scrutinee's |}]

let%expect_test "only the scrutinee's binder of a block may carry a type" =
  let _ = main_of_body
    "inductive V : forall (n : Nat) -> Type@0 where | vnil end \
     eval fun (v : V 0) -> elim v at (n : Nat) (z : V n) -> Nat | vnil => 0 end" in
  [%expect {| Error: only the last binder of a block (the scrutinee) may carry a type |}]

let%expect_test "a block for a member the group does not have is rejected" =
  let _ = main_of_body (group_tm_sp ^
    "eval fun (t : S.Tm) -> elim t at (z : S.Tm) -> Nat | var n => 1 | app f s, hf hs => hs end") in
  [%expect {|
    Error: an eliminator has one block per member of its group, in member order:
      Tm, Sp; the block for Sp is missing.
      The eliminator should read:
      elim x1 at (z : S.Tm) → …
      | var n ⇒ …
      | app f s, hf hs ⇒ …
      with (z : S.Sp) → …
      | snil ⇒ …
      | scons t s, ht hs ⇒ …
      end
    |}]

let group_tree_forest =
  "mutual G (A : Type@0) where inductive Tree : Type@0 where | node (x : A) (ts : Forest A) \
   with Forest : Type@0 where | nil | cons (t : Tree A) (ts : Forest A) end end "

let%expect_test "an eliminator missing a block gets the eliminator it needs" =
  let _ = main_of_bare_body (group_tree_forest ^
    "def f (z : G.Forest ⊤) : ⊤ := elim z at (z : G.Forest ⊤) -> ⊤ \
       | nil => ⋆ | cons t us, ht hus => ⋆ end end") in
  [%expect {|
    Error: an eliminator has one block per member of its group, in member order:
      Tree, Forest; the block for Tree is missing.
      The eliminator should read:
      elim x1 with (z : G.Tree ⊤) → …
      | node x ts, h ⇒ …
      at (z : G.Forest ⊤) → …
      | nil ⇒ …
      | cons t ts, ht hts ⇒ …
      end
    |}]

let%expect_test "an eliminator with a block too many gets the eliminator it needs" =
  let _ = main_of_bare_body
    "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
     inductive Rose : Type@0 where | node (ts : List Rose) end \
     def f (t : Rose) : ⊤ := elim t at (z : Rose) -> ⊤ | node ts, h => ⋆ \
       with (z : List Rose) -> ⊤ | nil => ⋆ | cons t ts, ht hts => ⋆ \
       with (z : List Rose) -> ⊤ | nil => ⋆ | cons t ts, ht hts => ⋆ end end" in
  [%expect {|
    Error: an eliminator has one block per member of its group, in member order:
      Rose, List Rose; block 3 (branches nil, cons) is for no member left.
      The eliminator should read:
      elim x1 at (z : Rose) → …
      | node ts, h ⇒ …
      with (z : List Rose) → …
      | nil ⇒ …
      | cons x xs, hx hxs ⇒ …
      end
    |}]

let%expect_test "an eliminator's blocks follow the order of the members" =
  let _ = main_of_bare_body (group_tree_forest ^
    "def f (z : G.Forest ⊤) : ⊤ := elim z at (z : G.Forest ⊤) -> ⊤ \
       | nil => ⋆ | cons t us, ht hus => ⋆ \
       with (z : G.Tree ⊤) -> ⊤ | node x ts, h => ⋆ end end") in
  [%expect {|
    Error: an eliminator has one block per member of its group, in member order:
      Tree, Forest; the blocks are not in member order.
      The eliminator should read:
      elim x1 with (z : G.Tree ⊤) → …
      | node x ts, h ⇒ …
      at (z : G.Forest ⊤) → …
      | nil ⇒ …
      | cons t ts, ht hts ⇒ …
      end
    |}]

let%expect_test "an eliminator of an imported group missing a block" =
  let _ = main_of_body
    "import Prelude›Data›Tree›Forest use (Tree) \
     def f (t : Tree 0l Nat) : Nat := elim t at (z : Tree 0l Nat) -> Nat | node x ts, h => h end end" in
  [%expect {|
    Error: an eliminator has one block per member of its group, in member order:
      Tree, Forest; the block for Forest is missing.
      The eliminator should read:
      elim x1 at (z : Prelude›Data›Tree›Forest.TreeForest.Tree 0l ℕ) → …
      | node x ts, h ⇒ …
      with (z : Prelude›Data›Tree›Forest.TreeForest.Forest 0l ℕ) → …
      | nil ⇒ …
      | cons t ts, ht hts ⇒ …
      end
    |}]

let%expect_test "an eliminator with no binder type missing a block" =
  let _ = main_of_bare_body
    "mutual G where inductive Tree : Type@0 where | node (ts : Forest) \
     with Forest : Type@0 where | nil | cons (t : Tree) (ts : Forest) end end \
     def f (z : G.Forest) : ⊤ := elim z at z -> ⊤ | nil => ⋆ | cons t us, ht hus => ⋆ end end" in
  [%expect {|
    Error: an eliminator has one block per member of its group, in member order:
      Tree, Forest; the block for Tree is missing.
      The eliminator should read:
      elim x1 with (z : G.Tree) → …
      | node ts, h ⇒ …
      at (z : G.Forest) → …
      | nil ⇒ …
      | cons t ts, ht hts ⇒ …
      end
    |}]

let%expect_test "a block for no member at its place prints its induction hypotheses after a comma" =
  (* Two groups have the block's constructors: the group is not known, and
     the term is printed as it is. *)
  let _ = main_of_bare_body
    "mutual G where inductive Tree : Type@0 where | node (ts : Forest) \
     with Forest : Type@0 where | nil | cons (t : Tree) (ts : Forest) end end \
     mutual H where inductive Tree : Type@0 where | node (ts : Forest) \
     with Forest : Type@0 where | nil | cons (t : Tree) (ts : Forest) end end \
     def f (z : G.Forest) : ⊤ := elim z at z -> ⊤ | nil => ⋆ | cons t us, ht hus => ⋆ end end" in
  [%expect {|
    Error: an eliminator has one block per member of its group, in member order:
      Tree, Forest; the block for Tree is missing.
      The eliminator should read:
      elim x1 with (z : G.Tree) → …
      | node ts, h ⇒ …
      at (z : G.Forest) → …
      | nil ⇒ …
      | cons t ts, ht hts ⇒ …
      end
    |}]

let%expect_test "the member written unapplied is the one named" =
  let _ = main_of_bare_body
    "mutual G (A : Type@0) where inductive Tree : Type@0 where | node (x : A) (ts : Forest) \
     with Forest : Type@0 where | nil | cons (t : Tree A) (ts : Forest A) end end" in
  [%expect {| Error: Forest is not applied to its uniform parameters as declared in the argument ts of node |}];
  let _ = main_of_bare_body
    "mutual G (A : Type@0) where inductive Tree : Type@0 where | node (x : A) (ts : Forest A) \
     with Forest : Type@0 where | nil | cons (t : Tree) (ts : Forest A) end end" in
  [%expect {| Error: Tree is not applied to its uniform parameters as declared in the argument t of cons |}]

let%expect_test "two members of a group have two names" =
  let _ = main_of_body
    "mutual S where inductive A : Type@0 where | a with A : Type@0 where | b end end" in
  [%expect {| Error: A is declared twice in a group |}]

let%expect_test "a group of inductive types takes no abstract" =
  let _ = main_of_body "abstract mutual S where inductive A : Type@0 where | a end end" in
  [%expect {| Error: a group of inductive types takes no abstract |}]

let%expect_test "a mutual definition has one function per member, in any order" =
  let _ = main_of_body (group_tm_sp ^
    "mutual def spine (z : S.Sp) : Nat := | snil => 0 | scons t s, ht hs => succ hs \
     with heads (z : S.Tm) : Nat := | var n => 0 | app f s, hf hs => succ hf end \
     eval spine (S.Sp.scons (S.Tm.var 1) (S.Sp.scons (S.Tm.var 2) S.Sp.snil)) \
     eval heads (S.Tm.app (S.Tm.var 0) S.Sp.snil)") in
  [%expect {|
    Evaluate spine (S.Sp.scons (S.Tm.var 1) (S.Sp.scons (S.Tm.var 2) S.Sp.snil))
      --> 2 : ℕ
    Evaluate heads (S.Tm.app (S.Tm.var 0) S.Sp.snil) --> 1 : ℕ
    |}]

let%expect_test "a mutual definition misses a member" =
  let _ = main_of_body (group_tm_sp ^
    "mutual def spine (z : S.Sp) : Nat := | snil => 0 | scons t s, ht hs => succ hs end") in
  [%expect {|
    Error: a mutual definition has one function per member of its group:
      the group has 2 members, the definition 1 function
    |}]

let%expect_test "a nested occurrence is eliminated at its view's block" =
  let _ = main_of_body
    "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
     inductive Rose : Type@0 where | node (ts : List Rose) end \
     eval elim (Rose.node (List.cons Rose (Rose.node (List.nil Rose)) (List.nil Rose))) \
       at (z : Rose) -> Nat | node ts, h => succ h \
       with (z : List Rose) -> Nat | nil => 0 | cons t ts, ht hts => succ hts end" in
  [%expect {|
    Evaluate elim Rose.node
                    (List.cons Rose (Rose.node (List.nil Rose)) (List.nil Rose))
             at (x1 : Rose) → ℕ
             | node x2, x3 ⇒ succ x3
             with (x4 : List Rose) → ℕ
             | nil ⇒ 0
             | cons x5 x6, x7 x8 ⇒ succ x8
             end --> 2 : ℕ
    |}]

let%expect_test "a group nests only at the uniform parameters of a container" =
  let _ = main_of_body
    "inductive Pair (A : Type@0) : forall (B : Type@0) -> Type@1 where | pair (x : A) (y : B) end \
     inductive Rose : Type@0 where | node (p : Pair Nat Rose) end" in
  [%expect {|
    Error: Rose occurs in a non-uniform argument of Pair
      in the argument p of node;
      a group may nest only at the uniform parameters of a declared type of a filed group
    |}]

let%expect_test "a mutual group files its recursor module" =
  let _ = main_of_body (group_tm_sp ^
    "eval S.Rec.rec_Tm 0l (fun (z : S.Tm) -> Nat) (fun (z : S.Sp) -> Nat) \
       (fun (n : Nat) -> 1) (fun (f : S.Tm) (s : S.Sp) (hf : Nat) (hs : Nat) -> succ hs) \
       0 (fun (t : S.Tm) (s : S.Sp) (ht : Nat) (hs : Nat) -> succ hs) \
       (S.Tm.app (S.Tm.var 0) (S.Sp.scons (S.Tm.var 1) S.Sp.snil))") in
  [%expect {|
    Evaluate S.Rec.rec_Tm 0l (λ (x1 : S.Tm) → ℕ) (λ (x2 : S.Sp) → ℕ)
               (λ (x3 : ℕ) → 1)
               (λ (x4 : S.Tm)
                  (x5 : S.Sp)
                  (x6 : ℕ)
                  (x7 : ℕ)
                 → succ x7)
               0
               (λ (x8 : S.Tm)
                  (x9 : S.Sp)
                  (x10 : ℕ)
                  (x11 : ℕ)
                 → succ x11)
               (S.Tm.app (S.Tm.var 0) (S.Sp.scons (S.Tm.var 1) S.Sp.snil)) --> 2
      : ℕ
    |}]

let%expect_test "the recursor module names a view by its instance" =
  let _ = main_of_body
    "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
     mutual R where inductive Rose : Type@0 where | node (ts : List Rose) end end \
     eval R.Rec.rec_List_Rose 0l (fun (z : R.Rose) -> Nat) (fun (z : List R.Rose) -> Nat) \
       (fun (ts : List R.Rose) (h : Nat) -> succ h) 0 \
       (fun (t : R.Rose) (ts : List R.Rose) (ht : Nat) (hts : Nat) -> succ hts) \
       (List.cons R.Rose (R.Rose.node (List.nil R.Rose)) (List.nil R.Rose))" in
  [%expect {|
    Evaluate R.Rec.rec_List_Rose 0l (λ (x1 : R.Rose) → ℕ)
               (λ (x2 : List R.Rose) → ℕ)
               (λ (x3 : List R.Rose)
                  (x4 : ℕ)
                 → succ x4)
               0
               (λ (x5 : R.Rose)
                  (x6 : List R.Rose)
                  (x7 : ℕ)
                  (x8 : ℕ)
                 → succ x8)
               (List.cons R.Rose (R.Rose.node (List.nil R.Rose))
                 (List.nil R.Rose)) --> 1 : ℕ
    |}]

let%expect_test "a single inductive type files its recursor module in its own module" =
  let _ = main_of_body
    "inductive E : Type@0 where | e | f (x : E) end \
     eval E.Rec.rec_E 0l (fun (z : E) -> Nat) 0 (fun (x : E) (h : Nat) -> succ h) (E.f (E.f E.e))" in
  [%expect {|
    Evaluate E.Rec.rec_E 0l (λ (x1 : E) → ℕ) 0 (λ (x2 : E)
                                                  (x3 : ℕ)
                                                 → succ x3)
               (E.f (E.f E.e)) --> 2 : ℕ
    |}]

let%expect_test "the recursor module is a module" =
  let _ = main_of_body "inductive E : Type@0 where | e end eval E.Rec" in
  [%expect {| Error: Test.E.Rec is a module, not a term |}]

let%expect_test "a nested type of one member files its recursor module in its own module" =
  let _ = main_of_body
    "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
     inductive Rose : Type@0 where | node (ts : List Rose) end \
     eval Rose.Rec.rec_List_Rose 0l (fun (z : Rose) -> Nat) (fun (z : List Rose) -> Nat) \
       (fun (ts : List Rose) (h : Nat) -> succ h) 0 \
       (fun (t : Rose) (ts : List Rose) (ht : Nat) (hts : Nat) -> succ hts) \
       (List.cons Rose (Rose.node (List.nil Rose)) (List.nil Rose))" in
  [%expect {|
    Evaluate Rose.Rec.rec_List_Rose 0l (λ (x1 : Rose) → ℕ)
               (λ (x2 : List Rose) → ℕ)
               (λ (x3 : List Rose)
                  (x4 : ℕ)
                 → succ x4)
               0
               (λ (x5 : Rose)
                  (x6 : List Rose)
                  (x7 : ℕ)
                  (x8 : ℕ)
                 → succ x8)
               (List.cons Rose (Rose.node (List.nil Rose)) (List.nil Rose)) --> 1
      : ℕ
    |}]

(* [inductive A … with B … end]: the recursor module is in the first
   declared member's module, [A.Rec]; its function at [B] is typed through
   the group as [A]'s module's frame carries it. *)
let%expect_test "a group written with [with] files its recursor module in its first member's module" =
  let _ = main_of_body
    "inductive A : Type@0 where | a0 | a1 (b : B) with B : Type@0 where | b0 (a : A) end \
     eval A.Rec.rec_B 0l (fun (z : A) -> Nat) (fun (z : B) -> Nat) \
       0 (fun (b : B) (h : Nat) -> succ h) (fun (a : A) (h : Nat) -> succ h) \
       (B.b0 (A.a1 (B.b0 A.a0)))" in
  [%expect {|
    Evaluate A.Rec.rec_B 0l (λ (x1 : A) → ℕ) (λ (x2 : B) → ℕ) 0
               (λ (x3 : B)
                  (x4 : ℕ)
                 → succ x4)
               (λ (x5 : A)
                  (x6 : ℕ)
                 → succ x6)
               (B.b0 (A.a1 (B.b0 A.a0))) --> 3 : ℕ
    |}]

let%expect_test "a later member of a group written with [with] has no recursor module" =
  let _ = main_of_body
    "inductive A : Type@0 where | a0 | a1 (b : B) with B : Type@0 where | b0 (a : A) end eval B.Rec" in
  [%expect {| Error: B.Rec has no inferable type |}]

let%expect_test "a constructor named Rec is rejected" =
  let _ = main_of_body "inductive Tag : Type@0 where | Rec | Val end" in
  [%expect {| Error: Rec is the recursor module of Tag, not a constructor |}]

let%expect_test "a constructor named rec is rejected" =
  let _ = main_of_body "inductive Tag : Type@0 where | rec | val end" in
  [%expect {| Error: rec is the recursor of Tag, not a constructor |}]

let%expect_test "a member of a mutual group named Rec is rejected" =
  let _ = main_of_body "mutual M where inductive Rec : Type@0 where | a end end" in
  [%expect {| Error: Rec is the recursor module of M, not a member |}]

(* The constructor's type is generated from the argument's normal form,
   which names the private [M.Q]: privacy checks what is written, so the
   generated definitions are not checked. *)
let%expect_test "a constructor whose argument normalizes to a private name" =
  let _ = main_of_body
    "module M where axiom Q0 : Type@0 private abstract def Q : Type@0 := Q0 end \
       def F (X : Type@0) : Type@0 := forall (q : Q) -> X end end \
     inductive T : Type@0 where | leaf | mk (f : M.F T) end \
     eval T.leaf" in
  [%expect {| Evaluate T.leaf --> T.leaf : T |}]

let%expect_test "a type named Rec has its own recursor module" =
  let _ = main_of_body
    "inductive Rec : Type@0 where | a (r : Rec) | b end \
     eval Rec.Rec.rec_Rec 0l (fun (z : Rec) -> Nat) (fun (r : Rec) (h : Nat) -> succ h) 0 (Rec.a (Rec.a Rec.b))" in
  [%expect {|
    Evaluate Rec.Rec.rec_Rec 0l (λ (x1 : Rec) → ℕ)
               (λ (x2 : Rec)
                  (x3 : ℕ)
                 → succ x3)
               0
               (Rec.a (Rec.a Rec.b)) --> 2 : ℕ
    |}]

let%expect_test "a mutual group prints back as written" =
  let _ = main_of_body (group_tm_sp ^ "eval S.Tm.var 0") in
  [%expect {| Evaluate S.Tm.var 0 --> S.Tm.var 0 : S.Tm |}]

let%expect_test "a group nests only at the uniform parameters: a type of non-uniform parameters only" =
  let _ = main_of_body
    "inductive B : forall (T : Type@0) -> Type@1 where | mk (x : T) end \
     inductive Rose : Type@0 where | node (b : B Rose) end" in
  [%expect {|
    Error: Rose occurs in a non-uniform argument of B in the argument b of node;
      a group may nest only at the uniform parameters of a declared type of a filed group
    |}]

let%expect_test "lib/Forests.mctt" =
  let _ = main_of_lib "Forests.mctt" in
  [%expect {|
    Evaluate R.sizeTree example --> 4 : ℕ
    Evaluate R.depthTree example --> 3 : ℕ
    Evaluate R.flattenTree example
      --> Prelude›Data›List.List.cons 0l ℕ 1
            (Prelude›Data›List.List.cons 0l ℕ 2
              (Prelude›Data›List.List.cons 0l ℕ 3
                (Prelude›Data›List.List.cons 0l ℕ 4
                  (Prelude›Data›List.List.nil 0l ℕ))))
      : Prelude›Data›List.List 0l ℕ
    Evaluate R.flattenTree (R.mapTree ℕ succ example)
      --> Prelude›Data›List.List.cons 0l ℕ 2
            (Prelude›Data›List.List.cons 0l ℕ 3
              (Prelude›Data›List.List.cons 0l ℕ 4
                (Prelude›Data›List.List.cons 0l ℕ 5
                  (Prelude›Data›List.List.nil 0l ℕ))))
      : Prelude›Data›List.List 0l ℕ
    Evaluate R.foldTree ℕ ℕ plus 0 plus example --> 10 : ℕ
    Evaluate R.sizeForest pair --> 5 : ℕ
    Evaluate LO.length 0l T (R.toList pair) --> 2 : ℕ
    Evaluate R.flattenForest (R.fromList (R.toList pair))
      --> Prelude›Data›List.List.cons 0l ℕ 1
            (Prelude›Data›List.List.cons 0l ℕ 2
              (Prelude›Data›List.List.cons 0l ℕ 3
                (Prelude›Data›List.List.cons 0l ℕ 4
                  (Prelude›Data›List.List.cons 0l ℕ 5
                    (Prelude›Data›List.List.nil 0l ℕ)))))
      : Prelude›Data›List.List 0l ℕ
    Evaluate leaves example --> 2 : ℕ
    Evaluate largest example --> 4 : ℕ
    Evaluate P.Maps.sizeMapTree ℕ succ example --> ⋆ : ⊤
    Evaluate P.Flatten.lengthFlattenTree example --> ⋆ : ⊤
    Evaluate P.Flatten.lengthFlattenForest pair --> ⋆ : ⊤
    Evaluate P.Folds.sizeFold example --> ⋆ : ⊤
    |}]

let%expect_test "lib/Roses.mctt" =
  let _ = main_of_lib "Roses.mctt" in
  [%expect {|
    Evaluate R.size example --> 5 : ℕ
    Evaluate R.depth example --> 3 : ℕ
    Evaluate R.flatten example
      --> Prelude›Data›List.List.cons 0l ℕ 1
            (Prelude›Data›List.List.cons 0l ℕ 2
              (Prelude›Data›List.List.cons 0l ℕ 3
                (Prelude›Data›List.List.cons 0l ℕ 4
                  (Prelude›Data›List.List.cons 0l ℕ 5
                    (Prelude›Data›List.List.nil 0l ℕ)))))
      : Prelude›Data›List.List 0l ℕ
    Evaluate R.flatten (R.map ℕ succ example)
      --> Prelude›Data›List.List.cons 0l ℕ 2
            (Prelude›Data›List.List.cons 0l ℕ 3
              (Prelude›Data›List.List.cons 0l ℕ 4
                (Prelude›Data›List.List.cons 0l ℕ 5
                  (Prelude›Data›List.List.cons 0l ℕ 6
                    (Prelude›Data›List.List.nil 0l ℕ)))))
      : Prelude›Data›List.List 0l ℕ
    Evaluate R.fold ℕ ℕ plus 0 plus example --> 15 : ℕ
    Evaluate LO.length 0l T (children example) --> 3 : ℕ
    Evaluate R.sizeForest (children example) --> 4 : ℕ
    Evaluate R.flattenForest (LO.reverse 0l T (children example))
      --> Prelude›Data›List.List.cons 0l ℕ 5
            (Prelude›Data›List.List.cons 0l ℕ 3
              (Prelude›Data›List.List.cons 0l ℕ 4
                (Prelude›Data›List.List.cons 0l ℕ 2
                  (Prelude›Data›List.List.nil 0l ℕ))))
      : Prelude›Data›List.List 0l ℕ
    Evaluate leaves example --> 3 : ℕ
    Evaluate P.Maps.sizeMap ℕ succ example --> ⋆ : ⊤
    Evaluate P.Flatten.lengthFlatten example --> ⋆ : ⊤
    Evaluate P.Flatten.lengthFlattenForest (children example) --> ⋆ : ⊤
    |}]

(** Member access through a term: a term of a record type, in module
    position, stands for the record's module at the term. *)

let pair_decl =
  "record Pair (A : Type@0) (B : Type@0) : Type@0 where fst : A; snd : B \
   with def swap : Pair B A := record Pair B A where fst := snd; snd := fst end end end end "

let%expect_test "a field through a term binder" =
  let _ = main_of_body (pair_decl ^ "def first (p : Pair Nat Nat) : Nat := p.fst end \
                                     eval first (record Pair Nat Nat where fst := 1; snd := 2 end)") in
  [%expect {| Evaluate first (record Pair ℕ ℕ where fst ≔ 1; snd ≔ 2 end) --> 1 : ℕ |}]

let%expect_test "a with-area member through a term binder" =
  let _ = main_of_body (pair_decl ^ "def sw (p : Pair Nat Nat) : Pair Nat Nat := p.swap end \
                                     eval (sw (record Pair Nat Nat where fst := 1; snd := 2 end)).fst") in
  [%expect {| Evaluate (sw (record Pair ℕ ℕ where fst ≔ 1; snd ≔ 2 end)).fst --> 2 : ℕ |}]

let%expect_test "a field through a term applied, with no let" =
  let _ = main_of_body (pair_decl ^ "def mk (n : Nat) : Pair Nat Nat := record Pair Nat Nat where fst := n; snd := 0 end end \
                                     def g (n : Nat) : Nat := (mk n).fst end eval g 7") in
  [%expect {| Evaluate g 7 --> 7 : ℕ |}]

let%expect_test "a field through a head that is no path, let-bound" =
  let _ = main_of_body (pair_decl ^ "eval (record Pair Nat Nat where fst := 5; snd := 6 end).snd \
                                     eval ((λ (q : Pair Nat Nat) → q) (record Pair Nat Nat where fst := 3; snd := 4 end)).fst") in
  [%expect {|
    Evaluate let x1 ≔ record Pair ℕ ℕ where fst ≔ 5; snd ≔ 6 end in x1.snd end
      --> 6 : ℕ
    Evaluate let x1 ≔
                   (λ (x2 : Pair ℕ ℕ) → x2)
                     (record Pair ℕ ℕ where fst ≔ 3; snd ≔ 4 end)
             in x1.fst
             end --> 3 : ℕ
    |}]

let%expect_test "a field through a term in a clause of a mutual definition" =
  let _ = main_of_body (pair_decl ^ "inductive L : Type@0 where | nil | cons (p : Pair Nat Nat) (l : L) end \
                                     mutual def sumFst (l : L) : Nat := \
                                     | nil => 0 \
                                     | cons p l, h => (elim p.fst at k -> Nat | zero => h | succ m, r => succ r end) \
                                     end \
                                     eval sumFst (L.cons (record Pair Nat Nat where fst := 3; snd := 4 end) \
                                                   (L.cons (record Pair Nat Nat where fst := 5; snd := 0 end) L.nil))") in
  [%expect {|
    Evaluate sumFst
               (L.cons (record Pair ℕ ℕ where fst ≔ 3; snd ≔ 4 end)
                 (L.cons (record Pair ℕ ℕ where fst ≔ 5; snd ≔ 0 end) L.nil))
      --> 8 : ℕ
    |}]

let%expect_test "a field through a term in the clauses of a mutual group" =
  let _ = main_of_body (pair_decl ^ "mutual EO where inductive Ev : Type@0 where | ez | es (o : Od) \
                                     with Od : Type@0 where | os (e : Ev) end end \
                                     mutual def (q : Pair Nat Nat) \
                                       evf (e : EO.Ev) : Nat := | ez => q.fst | es o, h => succ h \
                                       with odf (o : EO.Od) : Nat := | os e, h => succ (succ h) \
                                     end \
                                     eval evf (record Pair Nat Nat where fst := 10; snd := 0 end) \
                                       (EO.Ev.es (EO.Od.os EO.Ev.ez))") in
  [%expect {|
    Evaluate evf (record Pair ℕ ℕ where fst ≔ 10; snd ≔ 0 end)
               (EO.Ev.es (EO.Od.os EO.Ev.ez)) --> 13 : ℕ
    |}]

let%expect_test "a field through a term in the clauses of a nested group, its view's too" =
  let _ = main_of_body (pair_decl ^ "inductive Lst (A : Type@0) : Type@0 where | lnil | lcons (x : A) (xs : Lst A) end \
                                     inductive Rose : Type@0 where | node (p : Pair Nat Nat) (ts : Lst Rose) end \
                                     mutual def (q : Pair Nat Nat) \
                                       fstR (r : Rose) : Nat := | node p ts, h => p.fst \
                                       with fstL (ts : Lst Rose) : Nat := | lnil => q.snd | lcons t ts, ht hts => ht \
                                     end \
                                     eval fstR (record Pair Nat Nat where fst := 0; snd := 9 end) \
                                       (Rose.node (record Pair Nat Nat where fst := 7; snd := 0 end) (Lst.lnil Rose)) \
                                     eval fstL (record Pair Nat Nat where fst := 0; snd := 9 end) (Lst.lnil Rose)") in
  [%expect {|
    Evaluate fstR (record Pair ℕ ℕ where fst ≔ 0; snd ≔ 9 end)
               (Rose.node (record Pair ℕ ℕ where fst ≔ 7; snd ≔ 0 end)
                 (Lst.lnil Rose)) --> 7 : ℕ
    Evaluate fstL (record Pair ℕ ℕ where fst ≔ 0; snd ≔ 9 end) (Lst.lnil Rose)
      --> 9 : ℕ
    |}]

let%expect_test "a field through a global definition" =
  let _ = main_of_body (pair_decl ^ "def p : Pair Nat Nat := record Pair Nat Nat where fst := 1; snd := 2 end end \
                                     module M where def q : Pair Nat Nat := record Pair Nat Nat where fst := 3; snd := 4 end end end \
                                     eval p.fst eval p.snd eval M.q.fst") in
  [%expect {|
    Evaluate p.fst --> 1 : ℕ
    Evaluate p.snd --> 2 : ℕ
    Evaluate M.q.fst --> 3 : ℕ
    |}]

let%expect_test "an eliminator's annotation with an access through a term at its head" =
  let _ = main_of_body "record R : Type@1 where carrier : Type@0 with inductive T : Type@0 where | t end end end \
                        def f (q : R) (z : q.T) : Nat := elim z at (w : q.T) -> Nat | t => 0 end end" in
  [%expect {| |}]

let%expect_test "an eliminator's annotation with an access through a term in its arguments" =
  let _ = main_of_body "inductive Vec (A : Type@0) : Type@0 where | vnil | vcons (x : A) (v : Vec A) end \
                        record Carrier : Type@1 where carrier : Type@0 end \
                        def len (q : Carrier) (v : Vec q.carrier) : Nat := \
                          elim v at (z : Vec q.carrier) -> Nat | vnil => 0 | vcons x w, h => succ h end end \
                        eval len (record Carrier where carrier := Nat end) (Vec.vcons Nat 1 (Vec.vnil Nat))" in
  [%expect {|
    Evaluate len (record Carrier where carrier ≔ ℕ end)
               (Vec.vcons ℕ 1 (Vec.vnil ℕ)) --> 1 : ℕ
    |}]

let%expect_test "a constructor argument's type through a term" =
  let _ = main_of_body "record Carrier : Type@1 where carrier : Type@0 end \
                        inductive Vec (M : Carrier) : Type@0 where | vnil | vcons (x : M.carrier) (v : Vec M) end \
                        def NatC : Carrier := record Carrier where carrier := Nat end end \
                        eval Vec.vcons NatC 3 (Vec.vnil NatC)" in
  [%expect {|
    Evaluate Vec.vcons NatC 3 (Vec.vnil NatC)
      --> Vec.vcons (record Carrier where carrier ≔ ℕ end) 3
            (Vec.vnil (record Carrier where carrier ≔ ℕ end))
      : Vec (record Carrier where carrier ≔ ℕ end)
    |}]

let%expect_test "a member a record's module does not have, through a term" =
  let _ = main_of_body (pair_decl ^ "def g (q : Pair Nat Nat) : Nat := q.third end") in
  [%expect {| Error: third is not a member of record Test.Pair: neither a field nor a member of its with-area |}]

let%expect_test "a private with-area member, through a term" =
  let _ = main_of_body "record P : Type@0 where a : Nat with private def h : Nat := 0 end end end \
                        def g (q : P) : Nat := q.h end" in
  [%expect {| Error: Test.P.h is private |}]

let%expect_test "a field through a term of no record type" =
  let _ = main_of_body "def g (n : Nat) (m : Nat) : Nat := m.fst end" in
  [%expect {| Error: fst is selected from m, of type ℕ, which is not a record type |}]

let%expect_test "a record type applied to a value, as a term" =
  let _ = main_of_body (pair_decl ^ "def g (q : Pair Nat Nat) : Nat := Pair Nat Nat q end") in
  [%expect {|
    Error: Pair ℕ ℕ q is the module of the record value q; write (Pair ℕ ℕ q).f
      for a field, or Pair ℕ ℕ for the type
    |}]

let%expect_test "a record value with its fields out of order" =
  let _ = main_of_body (pair_decl ^ "eval record Pair Nat Nat where snd := 1; fst := 2 end") in
  [%expect {|
    Error: fields of Test.Pair must be given in order: fst, snd;
      got snd before fst
    |}]

let%expect_test "a record value with a field its record does not have" =
  let _ = main_of_body (pair_decl ^ "eval record Pair Nat Nat where fst := 1; zz := 2 end") in
  [%expect {| Error: zz is not a field of record Test.Pair |}]

let%expect_test "a record value with a field missing" =
  let _ = main_of_body (pair_decl ^ "eval record Pair Nat Nat where fst := 1 end") in
  [%expect {| Error: field snd of record Test.Pair is missing |}]

(** The typed fill: an eliminator's group and uniform parameters are read
    off its scrutinee's type, the one reading of it that fits its blocks *)

let list_rose =
  "inductive List (A : Type@0) : Type@0 where | nil | cons (x : A) (xs : List A) end \
   inductive Rose (A : Type@0) : Type@0 where | node (x : A) (ts : List (Rose A)) end "

let%expect_test "a list of roses eliminated as a list and as roses" =
  let _ = main_of_body (list_rose ^
    "def ts : List (Rose Nat) := List.cons (Rose Nat) (Rose.node Nat 1 (List.nil (Rose Nat))) (List.nil (Rose Nat)) end \
     def len (ts : List (Rose Nat)) : Nat := elim ts at y -> Nat | nil => 0 | cons t ts, h => succ h end end \
     def size (ts : List (Rose Nat)) : Nat := elim ts with y -> Nat | node x ts, h => succ h \
       at y -> Nat | nil => 0 | cons t ts, ht hts => succ hts end end \
     eval len ts eval size ts") in
  [%expect {|
    Evaluate len ts --> 1 : ℕ
    Evaluate size ts --> 1 : ℕ
    |}]

(* Two groups nest through lists alike, and both occur in the scrutinee's
   type: their eliminators' blocks have the same shape. *)
let%expect_test "an eliminator two readings of which fit its blocks is rejected" =
  let _ = main_of_body (list_rose ^
    "inductive Q1 : Type@0 where | a (xs : List Q1) end \
     inductive Q2 : Type@0 where | a (xs : List Q2) end \
     inductive Two (X : Type@0) (Y : Type@0) : Type@0 where | two (x : X) (y : Y) end \
     def f (y : List (Two Q1 Q2)) : Nat := elim y with z -> Nat | a xs, h => 0 \
       at z -> Nat | nil => 0 | cons x xs, h1 h2 => 1 end end") in
  [%expect {|
    Error: the eliminator of x1 is ambiguous: its blocks fit the eliminators of
      Q1 and of Q2
    |}]

let%expect_test "an eliminator's annotation through an inductive alias" =
  let _ = main_of_body (list_rose ^
    "inductive RoseN := Rose Nat \
     def g (r : RoseN) : Nat := elim r at (z : RoseN) -> Nat | node x ts, h => x \
       with (z : List RoseN) -> Nat | nil => 0 | cons t ts, ht hts => ht end end \
     eval g (Rose.node Nat 7 (List.nil (Rose Nat)))") in
  [%expect {| Evaluate g (Rose.node ℕ 7 (List.nil (Rose ℕ))) --> 7 : ℕ |}]

let%expect_test "an eliminator of a field, with a numeral in a branch" =
  let _ = main_of_body
    "record P : Type@0 where fst : Nat end \
     def h (p : P) : Nat := elim p.fst at z -> Nat | zero => 3 | succ n, ih => ih end end \
     eval h (record P where fst := 2 end)" in
  [%expect {| Evaluate h (record P where fst ≔ 2 end) --> 3 : ℕ |}]

let%expect_test "an eliminator with uniform parameters in a unit parameter's type" =
  let _ = main_of_program_string ~search_root:"../lib"
    "import Prelude›Builtin›Nat use (Nat)\nimport Prelude›Data›List use (List)\n\
     module Test (p : elim (List.nil 0l Nat) at z -> Type@0 | nil => Nat | cons x xs, h => Nat end) where \
     def q : Nat := p end end" in
  [%expect {| |}]

let%expect_test "an eliminator's scrutinee of no inductive type" =
  let _ = main_of_body "def f (A : Type@0) (a : A) : Nat := elim a at z -> Nat end end" in
  [%expect {|
    Error: the scrutinee a of an eliminator is of type A,
      which is not an inductive type
    |}]

let%expect_test "an eliminator no group of which fits its blocks" =
  let _ = main_of_body (list_rose ^
    "def f (ts : List (Rose Nat)) : Nat := elim ts with y -> Nat | leaf => 0 \
       at y -> Nat | nil => 0 | cons t ts, ht hts => 0 end end") in
  [%expect {|
    Error: an eliminator has one block per member of its group, in member order:
      List; block 1 (branches leaf) is for no member left.
      The eliminator should read:
      elim x1 at (z : List (Rose ℕ)) → …
      | nil ⇒ …
      | cons x xs, h ⇒ …
      end
    |}]

(** Definitions with a module part: inductive and record aliases, the
    items of opens, and the binding of the natural numbers, read as terms
    through their normal forms and as modules through their aliases. *)
let dm_decls =
  "module D where \
     record Pair (A : Type@0) (B : Type@0) : Type@0 where fst : A; snd : B with def two : Nat := 2 end end end \
     inductive N : Type@0 where | z | s (n : N) end \
   end "

let%expect_test "an open's items of a record type and an inductive type" =
  let _ = main_of_body (dm_decls ^
    "open D use (Pair; N) \
     def y : Pair Nat Nat := record Pair Nat Nat where fst := 1; snd := 2 end end \
     eval Pair.two Nat Nat y \
     eval y.two \
     eval N.rec 0l (fun (n : N) -> Nat) 0 (fun (n : N) (r : Nat) -> succ r) (N.s N.z)") in
  [%expect {|
    Evaluate Pair.two ℕ ℕ y --> 2 : ℕ
    Evaluate y.two --> 2 : ℕ
    Evaluate N.rec 0l (λ (x1 : N) → ℕ) 0 (λ (x2 : N)
                                            (x3 : ℕ)
                                           → succ x3) (N.s N.z) --> 1 : ℕ
    |}]

let%expect_test "an open's renamed items of an inductive type, a type and a module" =
  let _ = main_of_body (dm_decls ^ "open D use (N as K) def x : K := K.z end eval K.s x") in
  [%expect {| Evaluate K.s x --> D.N.s D.N.z : D.N |}]

let%expect_test "a record alias at all the parameters" =
  let _ = main_of_body (dm_decls ^
    "record P := D.Pair Nat Nat \
     def y : P := record D.Pair Nat Nat where fst := 1; snd := 2 end end \
     eval P.two y \
     eval y.fst") in
  [%expect {|
    Evaluate P.two y --> 2 : ℕ
    Evaluate y.fst --> 1 : ℕ
    |}]

let%expect_test "record aliases at some of the parameters" =
  let _ = main_of_body (dm_decls ^
    "record R := D.Pair \
     record S (A : Type@0) := D.Pair A \
     def y : R Nat Nat := record D.Pair Nat Nat where fst := 1; snd := 2 end end \
     eval R.two Nat Nat y \
     eval y : S Nat Nat") in
  [%expect {|
    Evaluate R.two ℕ ℕ y --> 2 : ℕ
    Evaluate y --> record D.Pair ℕ ℕ where fst ≔ 1; snd ≔ 2 end : S ℕ ℕ
    |}]

let%expect_test "an inductive alias is the type, its constructors and its recursor" =
  let _ = main_of_body (dm_decls ^
    "inductive M := D.N \
     eval M.z \
     eval elim M.s M.z at (k : M) -> Nat | z => 0 | s m, r => succ r end \
     eval M.rec 0l (fun (n : M) -> Nat) 0 (fun (n : M) (r : Nat) -> succ r) (M.s M.z)") in
  [%expect {|
    Evaluate M.z --> D.N.z : D.N
    Evaluate elim M.s M.z at (x1 : M) → ℕ | z ⇒ 0 | s x2, x3 ⇒ succ x3 end --> 1
      : ℕ
    Evaluate M.rec 0l (λ (x1 : M) → ℕ) 0 (λ (x2 : M)
                                            (x3 : ℕ)
                                           → succ x3) (M.s M.z) --> 1 : ℕ
    |}]

let%expect_test "an inductive alias of a record type is rejected" =
  let _ = main_of_body (dm_decls ^ "inductive F := D.Pair") in
  [%expect {| Error: inductive alias F names a record type: use record |}]

let%expect_test "a record alias of an inductive type is rejected" =
  let _ = main_of_body (dm_decls ^ "record F := D.N") in
  [%expect {| Error: record alias F names an inductive type: use inductive |}]

let%expect_test "an open of an inductive type as a module, a plain module alias" =
  let _ = main_of_body (dm_decls ^ "open D.N as K def x : D.N := K.z end eval x eval K.s x") in
  [%expect {|
    Evaluate x --> D.N.z : D.N
    Evaluate K.s x --> D.N.s D.N.z : D.N
    |}]

let%expect_test "a binding through an inductive alias in another module" =
  let _ = main_of_bare_body "module A where inductive MyNatT : Type@0 where | z | s (n : MyNatT) end end \
                             inductive MyNat := A.MyNatT builtin natural := MyNat eval 2" in
  [%expect {| Evaluate 2 --> 2 : ℕ |}]

let%expect_test "a binding of a plain module is rejected" =
  let _ = main_of_bare_body "module X where end builtin natural := X" in
  [%expect {| Error: Test.X is not an inductive type |}]

let%expect_test "an open of a record value as a module" =
  let _ = main_of_body (dm_decls ^
    "def q : D.Pair Nat Nat := record D.Pair Nat Nat where fst := 1; snd := 2 end end \
     module M where open q as W eval W.fst end") in
  [%expect {| Evaluate M.W.fst --> 1 : ℕ |}]

let%expect_test "an open of a record value given at the parameters" =
  let _ = main_of_body (dm_decls ^
    "record R := D.Pair \
     def q : D.Pair Nat Nat := record D.Pair Nat Nat where fst := 1; snd := 2 end end \
     module M where open R Nat Nat q as W eval W.snd end") in
  [%expect {| Evaluate M.W.snd --> 2 : ℕ |}]

(** Inductive aliases of a library inductive type at a level, the type
    former given some of its uniform parameters, and an alias of an
    alias. *)
let list_import =
  "import Prelude›Builtin›Nat use (Nat) import Prelude›Data›List use (List) "

let%expect_test "inductive aliases of a list type at a level, and of an alias" =
  let _ = main_of_program_string ~search_root:"../lib" (list_import ^
    "module Test where \
       inductive F (u : Level) := List u \
       def xs : F 0l Nat := List.nil 0l Nat end \
       inductive G := F 0l \
       def ys : G Nat := xs end \
       eval ys \
       eval List.cons 0l Nat 1 ys : G Nat \
     end") in
  [%expect {|
    Evaluate ys --> Prelude›Data›List.List.nil 0l ℕ : Prelude›Data›List.List 0l ℕ
    Evaluate List.cons 0l ℕ 1 ys
      --> Prelude›Data›List.List.cons 0l ℕ 1 (Prelude›Data›List.List.nil 0l ℕ)
      : G ℕ
    |}]

let%expect_test "a private inductive alias at a parameterized module's parameters" =
  let _ = main_of_program_string ~search_root:"../lib" (list_import ^
    "module Test where \
       module M (u : Level) (A : Type@{u}) where \
         private inductive L := List u A \
         def e : L := L.nil end \
       end \
       eval M.e 0l Nat \
     end") in
  [%expect {|
    Evaluate M.e 0l ℕ --> Prelude›Data›List.List.nil 0l ℕ
      : Prelude›Data›List.List 0l ℕ
    |}]

let%expect_test "an inductive type of a parameterized module, from outside it" =
  let _ = main_of_body
    "module P (A : Type@0) where inductive N : Type@0 where | z end end \
     def a : P.N Nat := (P Nat).N.z end \
     eval a" in
  [%expect {| Evaluate a --> P.N.z ℕ : P.N ℕ |}]

let%expect_test "an inductive type of a parameterized module, by its bare name inside it" =
  let _ = main_of_bare_body
    "module P (A : Type@0) where \
       inductive N : Type@0 where | z end \
       def n : N := N.z end \
     end \
     eval P.n" in
  [%expect {| Evaluate P.n --> λ (A1 : Type@0) → P.N.z A1 : ∀ (A1 : Type@0) → P.N A1 |}]
