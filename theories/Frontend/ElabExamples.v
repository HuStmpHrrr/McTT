From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Command.
From Mctt.Frontend Require Import Elaborator ElabSpec ElabCorrect.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core.Syntactic.System Require Import Command.

Import Syntax_Notations.
Open Scope string_scope.
Open Scope list_scope.

Import Cst.

(** * The Specification on Concrete Programs

    Surface programs are written as [Cst.prog] values, since the parser runs
    only after extraction.  Positive examples give the core unit, checked by
    [vm_compute] and transferred to [elab_spec] by soundness; negative ones
    are related to nothing, by [elaborate_core_fails]. *)

Ltac elab_ok := apply elaborate_core_sound; vm_compute; reflexivity.
Ltac elab_fails := apply elaborate_core_fails; eexists; vm_compute; reflexivity.
Ltac elab_err := vm_compute; reflexivity.

(** Items as the parser writes them: [as W], and [use (us) export (es)]. *)
Definition i_as (W : string) : list Cst.iitem := (None, W, true) :: nil.
Definition i_items (us es : list (string * string)) : list Cst.iitem :=
  map (fun p => (Some (fst p), snd p, true)) us ++ map (fun p => (Some (fst p), snd p, false)) es.

(** A sibling [y], read from the self slot [k]. *)
Definition sib (k : Datatypes.nat) (y : string) : exp := a_mem (me_var k) y.
Definition sibm (k : Datatypes.nat) (y : string) : modexp := me_mem (me_var k) y.

(** ** Self-Style Bodies

    The example of the design: two nested parameterized modules, and a
    member of the inner one using a member of the outer one.

<<
module Main where
  module M (A : Type@0) where
    def id (x : A) : A := x end
    module N (B : Type@0) where
      def k (x : A) (y : B) : A := id x end
    end
  end
  def j : forall (x : Nat) -> Nat := M.id Nat end
  eval (M Nat).N Nat).k 1 2
end
>>

    Each entry is read under the self slot of its body, which holds the
    entries before it.  In [k]'s body, the scope is [y, x, self(N), B,
    self(M), A, self(Main)]: [id] is read from [M]'s self slot, [#4], and is
    applied to nothing, since the slot holds [M]'s body under [M]'s own
    parameter.  [j] reads [M] from [Main]'s self slot [#0]. *)
Definition mnk : Cst.prog :=
  (nil, ("Main" :: nil, nil,
    c_mod false "M" (("A", typ 0) :: nil)
      (md_where
        (c_def md_pub "id" (pi "x" (var "A") (var "A")) (fn "x" (var "A") (var "x")) ::
         c_mod false "N" (("B", typ 0) :: nil)
           (md_where
             (c_def md_pub "k" (pi "x" (var "A") (pi "y" (var "B") (var "A")))
                (fn "x" (var "A") (fn "y" (var "B") (app (var "id") (var "x")))) :: nil)) :: nil)) ::
    c_def md_pub "j" (pi "x" nat nat) (app (proj (var "M") "id") nat) ::
    c_eval (app (app (proj (app (proj (app (var "M") nat) "N") nat) "k") (Cst.succ Cst.zero))
              (Cst.succ (Cst.succ Cst.zero))) None :: nil)).

Example mnk_spec :
  elab_spec mnk
    (nil, ⋅,
     cc_mod "M" false (⋅ ▹ Type@0)
       (cc_def "id" true false (Π #1 #2) (Some (λ #1 #0)) ::
        cc_mod "N" false (⋅ ▹ Type@0)
          (cc_def "k" true false (Π #3 (Π #2 #5)) (Some (λ #3 (λ #2 (sib 4 "id" $ #1)))) :: nil) :: nil) ::
     cc_def "j" true false (Π ℕ ℕ) (Some (a_mem (sibm 0 "M") "id" $ ℕ)) ::
     cc_eval (a_mem (me_app (me_mem (me_app (sibm 0 "M") ℕ) "N") ℕ) "k" $ succ zero $ succ (succ zero)) None :: nil).
Proof. elab_ok. Qed.

(** The use of [id] in [k], derived from the rules: [id] is the innermost
    entry naming it, under four binders, and the nearest self slot outside
    it is the next entry. *)
Example id_from_self :
  sel (en_var "y" :: en_var "x" :: en_self :: en_var "B" :: en_mem "id" "id" :: en_self :: en_var "A" :: en_self :: nil)
    (var "id") (sib 4 "id").
Proof.
  apply (sel_var _ _ 4 (en_mem "id" "id") (en_self :: en_var "A" :: en_self :: nil));
    [| change (sib 4 "id") with (a_mem (me_var (4 + 0)) "id"); apply dt_mem; reflexivity ].
  exists (en_var "y" :: en_var "x" :: en_self :: en_var "B" :: nil); cbn; repeat split.
  intros [H | [H | [H | []]]]; discriminate.
Qed.

(** Inside [M], [B] is [#1] and the self slot of [M] is [#0]; [a] is read
    from the unit's self slot, [#2].  Under the [fun], everything shifts by
    one.  Outside [M], [M.b] selects [b] from the member [M]. *)
Definition nested : Cst.prog :=
  (nil, ("U" :: nil, ("A", typ 0) :: nil,
         c_def md_pub "a" (typ 0) (var "A") ::
         c_mod false "M" (("B", typ 0) :: nil)
           (md_where
             (c_def md_pub "b" (typ 0) (var "B") ::
              c_eval (var "a") None ::
              c_eval (var "b") None ::
              c_eval (fn "x" nat (var "b")) None :: nil)) ::
         c_eval (app (proj (var "M") "b") nat) None :: nil)).

Example nested_spec :
  elab_spec nested
    (nil, ⋅ ▹ Type@0,
     cc_def "a" true false Type@0 (Some #1) ::
     cc_mod "M" false (⋅ ▹ Type@0)
       (cc_def "b" true false Type@0 (Some #1) ::
        cc_eval (sib 2 "a") None ::
        cc_eval (sib 0 "b") None ::
        cc_eval (λ ℕ (sib 1 "b")) None :: nil) ::
     cc_eval (a_mem (sibm 0 "M") "b" $ ℕ) None :: nil).
Proof. elab_ok. Qed.

(** ** [examples/ModuleParam.mctt]: a parameterized module and [let module] *)
Definition church : Cst.prog :=
  (nil, ("ModuleParam" :: nil, nil,
         c_mod false "Church" (("A", typ 0) :: nil)
           (md_where
             (c_def md_pub "t" (typ 0)
                (pi "z" (var "A") (pi "s" (pi "x" (var "A") (var "A")) (var "A"))) ::
              c_def md_pub "two" (var "t")
                (fn "z" (var "A") (fn "s" (pi "x" (var "A") (var "A"))
                   (app (var "s") (app (var "s") (var "z"))))) :: nil)) ::
         c_eval (letb (d_mod "C" nil (md_alias (app (var "Church") nat)))
                   (app (app (proj (var "C") "two") Cst.zero) (fn "x" nat (Cst.succ (var "x")))))
           (Some nat) :: nil)).

(** Inside [Church], [t] is [self.t].  [let module C := Church Nat] binds a
    local module slot, so [C.two] selects [two] of [#0]. *)
Example church_spec :
  elab_spec church
    (nil, ⋅,
     cc_mod "Church" false (⋅ ▹ Type@0)
       (cc_def "t" true false Type@0 (Some (Π #1 (Π (Π #2 #3) #3))) ::
        cc_def "two" true false (sib 0 "t") (Some (λ #1 (λ (Π #2 #3) (#0 $ (#0 $ #1))))) :: nil) ::
     cc_eval (ℓₘ (gu_mk ⋅ (Syntax.md_alias (me_app (sibm 0 "Church") ℕ)))
              in (a_mem (me_var 0) "two" $ zero $ λ ℕ (succ #0))) (Some ℕ) :: nil).
Proof. elab_ok. Qed.

(** ** [examples/ImportUse.mctt]: privacy, [open … as … use] *)
Definition import_use : Cst.prog :=
  (nil, ("ImportUse" :: nil, nil,
         c_mod false "Impl" nil
           (md_where
             (c_def md_priv "secret" nat (Cst.succ (Cst.succ (Cst.succ Cst.zero))) ::
              c_def md_pub "exposed" nat (Cst.succ (var "secret")) :: nil)) ::
         open_cmds nil ("Impl" :: nil) nil (Some "I") (i_items (("exposed", "exposed") :: nil) nil) ++
         c_eval (app (proj (var "I") "exposed") (var "exposed")) None :: nil)).

(** [open Impl as I use (exposed)] is [open Impl as I] then [open I use
    (exposed)] ([Cst.open_cmds]): the core declares the alias [I] and the
    member [exposed] in the frame, read from its self slot like any
    member. *)
Example import_use_spec :
  elab_spec import_use
    (nil, ⋅,
     cc_mod "Impl" false ⋅
       (cc_def "secret" true true ℕ (Some (succ (succ (succ zero)))) ::
        cc_def "exposed" true false ℕ (Some (succ (sib 0 "secret"))) :: nil) ::
     cc_open (sibm 0 "Impl") (Some "I") nil ::
     cc_open (sibm 0 "I") None (("exposed", "exposed", true) :: nil) ::
     cc_eval (a_mem (sibm 0 "I") "exposed" $ (sib 0 "exposed")) None :: nil).
Proof. elab_ok. Qed.

(** ** Leading Imports and Opens

    They come before the unit's header.  An import loads its unit; an open
    declares a slot of the leading context holding an alias of its target,
    named [N] by [as N], or read from by the names it declares, as a body
    is read from its self slot.  The parameters are read in the leading
    context, and the body sees it: here, the leading context is [N, ·]
    (innermost first), so [quadruple] is read from [#3] in the body, under
    the self slot, [n] and [N].

<<
import Lib::Arith use (quadruple)
import Lib::Num as N
module Main (n : N.t) where
  eval quadruple 2 : Nat
  eval N.double n
end
>>
*)
Definition main_mctt : Cst.prog :=
  (import_cmds ("Lib" :: "Arith" :: nil) nil nil None (i_items (("quadruple", "quadruple") :: nil) nil) ++
   import_cmds ("Lib" :: "Num" :: nil) nil nil (Some "N") nil,
   ("Main" :: nil, (("n", proj (var "N") "t") :: nil),
    c_eval (app (var "quadruple") (Cst.succ (Cst.succ Cst.zero))) (Some nat) ::
    c_eval (app (proj (var "N") "double") (var "n")) None :: nil)).

Example main_spec :
  elab_spec main_mctt
    (cc_load ("Lib" :: "Arith" :: nil) ::
     cc_open (me_unit ("Lib" :: "Arith" :: nil)) None (("quadruple", "quadruple", true) :: nil) ::
     cc_load ("Lib" :: "Num" :: nil) ::
     cc_open (me_unit ("Lib" :: "Num" :: nil)) (Some "N") nil :: nil,
     ⋅ ▹ a_mem (me_var 0) "t",
     cc_eval (sib 3 "quadruple" $ succ (succ zero)) (Some ℕ) ::
     cc_eval (a_mem (me_var 2) "double" $ #1) None :: nil).
Proof. elab_ok. Qed.

(** ** [examples/TrueFalse.mctt]: the unit type and the empty type *)
Definition true_false : Cst.prog :=
  (nil, ("TrueFalse" :: nil, nil,
         c_eval true_tm None ::
         c_eval (fn "u" true_ty (var "u")) None ::
         c_eval (fn "f" false_ty (exfalso (var "f") "x" nat)) None :: nil)).

Example true_false_spec :
  elab_spec true_false
    (nil, ⋅,
     cc_eval ⋆ None ::
     cc_eval (λ ⊤ #0) None ::
     cc_eval (λ ⊥ (efq #0 return ℕ)) None :: nil).
Proof. elab_ok. Qed.

(** ** Scoping Rules, Positive and Negative *)

Definition unit_of (cs : list Cst.cmd) : Cst.prog := (nil, ("T" :: nil, nil, cs)).

(** Privacy is not the elaborator's concern: [I.s] selects the member [s] of
    [I], and the core rejects the selection of a private member. *)
Example private_sibling :
  elab_spec (unit_of
    (c_mod false "I" nil (md_where (c_def md_priv "s" nat Cst.zero :: nil)) ::
     c_eval (proj (var "I") "s") None :: nil))
    (nil, ⋅,
     cc_mod "I" false ⋅ (cc_def "s" true true ℕ (Some zero) :: nil) ::
     cc_eval (a_mem (sibm 0 "I") "s") None :: nil).
Proof. elab_ok. Qed.

(** A frame nested in a member's own frame reads it from the outer self
    slot. *)
Example private_nested :
  elab_spec (unit_of
    (c_def md_priv "s" nat Cst.zero ::
     c_mod false "I" nil (md_where (c_eval (var "s") None :: nil)) :: nil))
    (nil, ⋅,
     cc_def "s" true true ℕ (Some zero) ::
     cc_mod "I" false ⋅ (cc_eval (sib 1 "s") None :: nil) :: nil).
Proof. elab_ok. Qed.

(** Redeclaring in the same frame is an error … *)
Example redeclare_same : forall u, ~ elab_spec (unit_of
  (c_def md_pub "x" nat Cst.zero :: c_def md_pub "x" nat Cst.zero :: nil)) u.
Proof. elab_fails. Qed.

(** … also over an alias … *)
Example redeclare_alias : forall u, ~ elab_spec (unit_of
  (c_mod false "I" nil (md_where nil) :: c_open nil ("I" :: nil) nil (i_as "x") ::
   c_def md_pub "x" nat Cst.zero :: nil)) u.
Proof. elab_fails. Qed.

(** … but shadowing an enclosing frame's member is allowed. *)
Example shadow_parent :
  elab_spec (unit_of
    (c_def md_pub "x" nat Cst.zero ::
     c_mod false "I" nil
       (md_where (c_def md_pub "x" nat (Cst.succ Cst.zero) :: c_eval (var "x") None :: nil)) :: nil))
    (nil, ⋅,
     cc_def "x" true false ℕ (Some zero) ::
     cc_mod "I" false ⋅ (cc_def "x" true false ℕ (Some (succ zero)) :: cc_eval (sib 0 "x") None :: nil) :: nil).
Proof. elab_ok. Qed.

(** A definition does not see itself. *)
Example no_self : forall u, ~ elab_spec (unit_of (c_def md_pub "x" nat (var "x") :: nil)) u.
Proof. elab_fails. Qed.

(** [module A.B] is [A], without parameters, holding [B]. *)
Example dotted_module :
  elab_spec (unit_of
    (c_mod_dotted false "B" ("A" :: nil) (("X", typ 0) :: nil) (md_where (c_def md_abs "y" (typ 0) (var "X") :: nil)) ::
     c_eval (app (proj (proj (var "A") "B") "y") nat) None :: nil))
    (nil, ⋅,
     cc_mod "A" false ⋅ (cc_mod "B" false (⋅ ▹ Type@0) (cc_def "y" false false Type@0 (Some #1) :: nil) :: nil) ::
     cc_eval (a_mem (me_mem (sibm 0 "A") "B") "y" $ ℕ) None :: nil).
Proof. elab_ok. Qed.

(** A unit is named by its full path only once imported. *)
Example unit_not_imported : forall u, ~ elab_spec (unit_of
  (c_eval (proj (glob ("L" :: "M" :: nil)) "f") None :: nil)) u.
Proof. elab_fails. Qed.

Example unit_imported :
  elab_spec (unit_of (c_import ("L" :: "M" :: nil) :: c_eval (proj (glob ("L" :: "M" :: nil)) "f") None :: nil))
    (nil, ⋅, cc_load ("L" :: "M" :: nil) :: cc_eval (a_mem (me_unit ("L" :: "M" :: nil)) "f") None :: nil).
Proof. elab_ok. Qed.

(** ** Definition Keywords

    Each keyword is [def] with the modifiers it implies, and takes [def]'s
    parameters ([Cst.def_cmd]); a modifier it implies already is rejected,
    with the message shown. *)
Example kw_theorem :
  elab_spec (unit_of (def_cmd dk_theorem md_pub "foo" (pi "n" nat nat) (fn "n" nat (var "n")) :: nil))
    (nil, ⋅, cc_def "foo" false false (Π ℕ ℕ) (Some (λ ℕ #0)) :: nil).
Proof. elab_ok. Qed.

Example kw_others :
  elab_spec (unit_of
    (def_cmd dk_lemma md_priv "a" nat Cst.zero :: def_cmd dk_fact md_pub "b" nat Cst.zero ::
     def_cmd dk_remark md_pub "c" nat Cst.zero :: def_cmd dk_let md_pub "d" nat Cst.zero ::
     def_cmd dk_given md_abs "e" nat Cst.zero :: def_cmd dk_def md_priv_abs "f" nat Cst.zero :: nil))
    (nil, ⋅,
     cc_def "a" false true ℕ (Some zero) :: cc_def "b" false true ℕ (Some zero) :: cc_def "c" false true ℕ (Some zero) ::
     cc_def "d" true true ℕ (Some zero) :: cc_def "e" false true ℕ (Some zero) :: cc_def "f" false true ℕ (Some zero) :: nil).
Proof. elab_ok. Qed.

Example kw_theorem_abstract :
  elaborate_core (unit_of (def_cmd dk_theorem md_abs "a" nat Cst.zero :: nil)) = eerr "theorem is already abstract".
Proof. elab_err. Qed.
Example kw_lemma_abstract :
  elaborate_core (unit_of (def_cmd dk_lemma md_priv_abs "a" nat Cst.zero :: nil)) = eerr "lemma is already abstract".
Proof. elab_err. Qed.
Example kw_fact_private :
  elaborate_core (unit_of (def_cmd dk_fact md_priv "a" nat Cst.zero :: nil)) = eerr "fact takes no modifiers".
Proof. elab_err. Qed.
Example kw_remark_abstract :
  elaborate_core (unit_of (def_cmd dk_remark md_abs "a" nat Cst.zero :: nil)) = eerr "remark takes no modifiers".
Proof. elab_err. Qed.
Example kw_let_private :
  elaborate_core (unit_of (def_cmd dk_let md_priv "a" nat Cst.zero :: nil)) = eerr "let is already private".
Proof. elab_err. Qed.
Example kw_given_private :
  elaborate_core (unit_of (def_cmd dk_given md_priv_abs "a" nat Cst.zero :: nil)) = eerr "given is already private".
Proof. elab_err. Qed.

(** ** Axioms

    [axiom x (ps) : A] takes [def]'s parameters and type and has no body
    ([Cst.axiom_cmd]); it takes no modifiers.  [axiom f (n : Nat) : Nat]
    then [def g : Nat := f 0 end] is: *)
Example axiom_member :
  elab_spec (unit_of (axiom_cmd md_pub "f" (pi "n" nat nat) ::
                      def_cmd dk_def md_pub "g" nat (app (var "f") Cst.zero) :: nil))
    (nil, ⋅, cc_def "f" false false (Π ℕ ℕ) None ::
             cc_def "g" true false ℕ (Some (sib 0 "f" $ zero)) :: nil).
Proof. elab_ok. Qed.

(** [private axiom a : Nat] and [abstract axiom a : Nat] are rejected. *)
Example axiom_private :
  elaborate_core (unit_of (axiom_cmd md_priv "a" nat :: nil)) = eerr "axiom takes no modifiers".
Proof. elab_err. Qed.
Example axiom_private_spec : forall u, ~ elab_spec (unit_of (axiom_cmd md_priv "a" nat :: nil)) u.
Proof. elab_fails. Qed.
Example axiom_abstract :
  elaborate_core (unit_of (axiom_cmd md_abs "a" nat :: nil)) = eerr "axiom takes no modifiers".
Proof. elab_err. Qed.

(** A local body has no axioms. *)
Example axiom_local :
  elaborate_core (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (axiom_cmd md_pub "a" nat :: nil))) Cst.zero) None :: nil))
  = eerr "axioms are not allowed in a local module".
Proof. elab_err. Qed.

(** ** Local Bodies

    A local body is read like a frame: each entry under its self slot, a
    sibling from that slot.

<<
let module X where
  def f : Nat := 0 end
  def g : Nat := succ f end
in X.g end
>>
*)
Example local_body :
  elab_spec (unit_of
    (c_eval (letb (d_mod "X" nil (md_where (c_def md_pub "f" nat Cst.zero ::
                                            c_def md_pub "g" nat (Cst.succ (var "f")) :: nil)))
               (proj (var "X") "g")) None :: nil))
    (nil, ⋅,
     cc_eval (ℓₘ (gu_body ⋅ (gm_ext (gm_ext gm_nil "f" (ge_def false ℕ (Some zero)))
                                    "g" (ge_def false ℕ (Some (succ (sib 0 "f"))))))
              in a_mem (me_var 0) "g") None :: nil).
Proof. elab_ok. Qed.

(** Its parameters lie outside its self slot, and a nested module is read
    from it as well. *)
Example local_params :
  elab_spec (unit_of
    (c_eval
       (letb (d_mod "L" (("A", typ 0) :: nil)
                (md_where
                   (c_def md_pub "x" (pi "a" (var "A") (var "A")) (fn "a" (var "A") (var "a")) ::
                    c_mod false "N" nil (md_where (c_def md_pub "y" nat Cst.zero :: nil)) ::
                    c_def md_pub "z" nat (proj (var "N") "y") :: nil)))
          (proj (var "L") "x")) None :: nil))
    (nil, ⋅,
     cc_eval
       (ℓₘ (gu_body (⋅ ▹ Type@0)
              (gm_ext
                 (gm_ext
                    (gm_ext gm_nil "x" (ge_def false (Π #1 #2) (Some (λ #1 #0))))
                    "N" (ge_mod false (gu_body ⋅ (gm_ext gm_nil "y" (ge_def false ℕ (Some zero))))))
                 "z" (ge_def false ℕ (Some (a_mem (sibm 0 "N") "y")))))
        in a_mem (me_var 0) "x") None :: nil).
Proof. elab_ok. Qed.

(** An open in a local body is a pre-form the core expands; what it
    declares are members of the body. *)
Example local_open :
  elab_spec (unit_of
    (c_eval
       (letb (d_mod "L" nil
                (md_where
                   (c_mod false "N" nil (md_where (c_def md_pub "y" nat Cst.zero :: nil)) ::
                    c_open nil ("N" :: nil) nil (i_items (("y", "y") :: nil) nil) ::
                    c_open nil ("N" :: nil) nil (i_as "K") ::
                    c_def md_pub "z" nat (var "y") ::
                    c_def md_pub "w" nat (proj (var "K") "y") :: nil)))
          (proj (var "L") "w")) None :: nil))
    (nil, ⋅,
     cc_eval
       (ℓₘ (gu_body ⋅
              (gm_ext
                 (gm_ext
                    (gm_open
                       (gm_open
                          (gm_ext gm_nil "N" (ge_mod false (gu_body ⋅ (gm_ext gm_nil "y" (ge_def false ℕ (Some zero))))))
                          (sibm 0 "N") None (("y", "y", true) :: nil))
                       (sibm 0 "N") (Some "K") nil)
                    "z" (ge_def false ℕ (Some (sib 0 "y"))))
                 "w" (ge_def false ℕ (Some (a_mem (sibm 0 "K") "y")))))
        in a_mem (me_var 0) "w") None :: nil).
Proof. elab_ok. Qed.

(** An open of a unit loads nothing: the unit must be imported already,
    here by a leading import. *)
Definition local_unit_import (leading : list Cst.cmd) : Cst.prog :=
  (leading, ("T" :: nil, nil,
    c_eval (letb (d_mod "L" nil (md_where (c_open ("X" :: nil) nil nil (i_items (("f", "f") :: nil) nil) :: nil))) Cst.zero)
      None :: nil)).

Example local_unit_loaded :
  elab_spec (local_unit_import (c_import ("X" :: nil) :: nil))
    (cc_load ("X" :: nil) :: nil, ⋅,
     cc_eval (ℓₘ (gu_body ⋅ (gm_open gm_nil (me_unit ("X" :: nil)) None (("f", "f", true) :: nil)))
              in zero) None :: nil).
Proof. elab_ok. Qed.

Example local_unit_not_loaded :
  elaborate_core (local_unit_import nil) = eerr "the unit is not imported".
Proof. elab_err. Qed.

(** A local body has no [import]s, no [eval]s, and no abstract definitions:
    a term files no constant. *)
Example local_import_rejected :
  elaborate_core (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (c_import ("X" :: nil) :: nil))) Cst.zero) None :: nil))
  = eerr "import is not allowed in a local module; use open".
Proof. elab_err. Qed.

Example local_eval :
  elaborate_core (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (c_eval Cst.zero None :: nil))) Cst.zero) None :: nil))
  = eerr "eval is not allowed in a local module".
Proof. elab_err. Qed.

Example local_abstract :
  elaborate_core (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (def_cmd dk_def md_abs "a" nat Cst.zero :: nil))) Cst.zero) None :: nil))
  = eerr "abstract definitions are not allowed in a local module".
Proof. elab_err. Qed.

(** So are the keywords that mean [abstract]. *)
Example local_theorem :
  elaborate_core (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (def_cmd dk_theorem md_pub "a" nat Cst.zero :: nil))) Cst.zero) None :: nil))
  = eerr "abstract definitions are not allowed in a local module".
Proof. elab_err. Qed.

(** A rejected keyword is rejected in a local body too. *)
Example kw_local_rejected :
  elaborate_core (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (def_cmd dk_fact md_abs "a" nat Cst.zero :: nil))) Cst.zero) None :: nil))
  = eerr "fact takes no modifiers".
Proof. elab_err. Qed.

(** A local body may have [private] entries, which the core's privacy check
    hides from outside the body. *)
Example local_private :
  elab_spec (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (c_def md_priv "s" nat Cst.zero ::
                                            c_mod true "N" nil (md_where nil) ::
                                            c_def md_pub "t" nat (Cst.succ (var "s")) :: nil)))
               (proj (var "L") "t")) None :: nil))
    (nil, ⋅,
     cc_eval (ℓₘ (gu_body ⋅ (gm_ext (gm_ext (gm_ext gm_nil
                                  "s" (ge_def true ℕ (Some zero)))
                                  "N" (ge_mod true (gu_body ⋅ gm_nil)))
                                  "t" (ge_def false ℕ (Some (succ (sib 0 "s"))))))
              in a_mem (me_var 0) "t") None :: nil).
Proof. elab_ok. Qed.

(** ** One Binding per Name per Frame *)

(** [module M (x : Nat) where def x … end]: a member may not take a
    parameter's name … *)
Definition member_param : Cst.prog := unit_of
  (c_mod false "M" (("x", nat) :: nil) (md_where (c_def md_pub "x" nat Cst.zero :: nil)) :: nil).
Example member_param_err : elaborate_core member_param = eerr "x is already declared".
Proof. elab_err. Qed.
Example member_param_spec : forall u, ~ elab_spec member_param u.
Proof. elab_fails. Qed.

(** … nor may an open's alias, here of the unit's own frame. *)
Definition alias_param : Cst.prog :=
  (nil, ("T" :: nil, ("x", nat) :: nil,
         c_mod false "M" nil (md_where nil) :: c_open nil ("M" :: nil) nil (i_as "x") :: nil)).
Example alias_param_err : elaborate_core alias_param = eerr "x is already declared".
Proof. elab_err. Qed.

(** [module M (x : Nat) (x : Nat)]: a telescope may not repeat a name. *)
Definition dup_params : Cst.prog := unit_of
  (c_mod false "M" (("x", nat) :: ("x", nat) :: nil) (md_where nil) :: nil).
Example dup_params_err : elaborate_core dup_params = eerr "duplicate parameter x".
Proof. elab_err. Qed.

(** Leading opens declare each name once, *)
Definition dup_leading : Cst.prog :=
  (import_cmds ("L" :: "A" :: nil) nil nil (Some "N") nil ++ import_cmds ("L" :: "B" :: nil) nil nil (Some "N") nil,
   ("T" :: nil, nil, nil)).
Example dup_leading_err : elaborate_core dup_leading = eerr "N is already declared".
Proof. elab_err. Qed.

(** and the unit's parameters and members may not take their names. *)
Example leading_param :
  elaborate_core (import_cmds ("L" :: "X" :: nil) nil nil (Some "A") nil,
                  ("T" :: nil, ("A", typ 0) :: nil, nil))
  = eerr "A is already declared".
Proof. elab_err. Qed.

Example leading_member :
  elaborate_core (import_cmds ("L" :: "X" :: nil) nil nil None (i_items (("f", "f") :: nil) nil),
                  ("T" :: nil, nil, c_def md_pub "f" nat Cst.zero :: nil))
  = eerr "f is already declared".
Proof. elab_err. Qed.

(** Across frames, shadowing is allowed: a module's parameter may reuse a
    member name of the enclosing frame, and a nested member the enclosing
    frame's parameter name. *)
Example shadow_param :
  elab_spec (nil, ("T" :: nil, ("x", nat) :: nil,
                   c_def md_pub "y" nat Cst.zero ::
                   c_mod false "M" (("y", nat) :: nil)
                     (md_where (c_def md_pub "x" nat (var "y") :: c_eval (var "x") None :: nil)) :: nil))
    (nil, ⋅ ▹ ℕ,
     cc_def "y" true false ℕ (Some zero) ::
     cc_mod "M" false (⋅ ▹ ℕ) (cc_def "x" true false ℕ (Some #1) :: cc_eval (sib 0 "x") None :: nil) :: nil).
Proof. elab_ok. Qed.

(** ** Opens

    [use] items are private declarations of the frame, [export] items public
    ones; [c as d] declares [d].  The target may be applied to arguments,
    read as terms where the open stands. *)
Example open_items_args :
  elab_spec (nil, ("T" :: nil, ("A", typ 0) :: nil,
    c_mod false "M" (("B", typ 0) :: nil)
      (md_where (c_def md_pub "c" (typ 0) (var "B") :: c_def md_pub "e" (typ 0) (var "B") :: nil)) ::
    c_open nil ("M" :: nil) (var "A" :: nil) (i_items (("c", "d") :: nil) (("e", "e") :: nil)) ::
    c_eval (var "d") None :: c_eval (var "e") None :: nil))
    (nil, ⋅ ▹ Type@0,
     cc_mod "M" false (⋅ ▹ Type@0)
       (cc_def "c" true false Type@0 (Some #1) :: cc_def "e" true false Type@0 (Some #1) :: nil) ::
     cc_open (me_app (sibm 0 "M") #1) None (("c", "d", true) :: ("e", "e", false) :: nil) ::
     cc_eval (sib 0 "d") None :: cc_eval (sib 0 "e") None :: nil).
Proof. elab_ok. Qed.

(** An item's name must be fresh in the frame before the open. *)
Example open_item_fresh :
  elaborate_core (unit_of
    (c_mod false "M" nil (md_where (c_def md_pub "c" nat Cst.zero :: nil)) ::
     c_def md_pub "d" nat Cst.zero ::
     c_open nil ("M" :: nil) nil (i_items nil (("c", "d") :: nil)) :: nil))
  = eerr "d is already declared".
Proof. elab_err. Qed.

(** [open] needs a target. *)
Example open_nothing :
  elaborate_core (unit_of (c_open nil nil nil nil :: nil)) = eerr "nothing to open".
Proof. elab_err. Qed.

(** A leading open of a unit that is not imported is rejected, as anywhere. *)
Example leading_open_unloaded :
  elaborate_core (open_cmds ("P" :: "E" :: nil) nil nil None (i_items (("Eq", "Eq") :: nil) nil),
                  ("T" :: nil, nil, nil))
  = eerr "the unit is not imported".
Proof. elab_err. Qed.

(** Before the header, an open may [use] but not [export] ([Cst.lead_cmds]). *)
Example leading_export :
  elaborate_core (c_import ("P" :: "E" :: nil) ::
                  lead_cmds (open_cmds ("P" :: "E" :: nil) nil nil None
                               (i_items (("Eq", "Eq") :: nil) (("refl", "refl") :: nil))),
                  ("T" :: nil, nil, nil))
  = eerr "export is not allowed before the module header".
Proof. elab_err. Qed.

(** A term is not a module. *)
Example term_not_module :
  elaborate_core (unit_of (c_mod false "P" nil (md_alias nat) :: nil)) = eerr "not a module".
Proof. elab_err. Qed.

(** ** A Loaded Unit Sees Only What It Imports

    [Lib::SeeB] names [Lib::SeeC] without importing it.  The elaborator
    rejects it, and so does the core, whatever loaded [Lib::SeeC] before:
    a loaded unit is run from nothing ([rl_run]), whatever the chain, so its
    body is checked in a global context without [Lib::SeeC]. *)
Definition seeB_core : cunit :=
  (nil, nil, cc_def "b" true false ℕ (Some (a_mem (me_unit ("Lib" :: "SeeC" :: nil)) "c")) :: nil).

Example seeB_not_elaborated :
  elaborate_core (nil, ("Lib" :: "SeeB" :: nil, nil,
                        c_def md_pub "b" nat (proj (glob ("Lib" :: "SeeC" :: nil)) "c") :: nil))
  = eerr "the unit is not imported".
Proof. elab_err. Qed.

Example seeB_rejected : forall load_path read to_core ch Θ U,
    ~ run_unit load_path read to_core (("Lib" :: "SeeB" :: nil) :: ch) nil seeB_core Θ U.
Proof.
  intros * Hr; inversion Hr; subst.
  match goal with H : run_leads _ _ _ _ _ _ _ _ _ |- _ => inversion H; subst end.
  match goal with H : run_cmds _ _ _ _ _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H end.
  match goal with H : cmd_xp_ok _ _ _ _ |- _ => destruct H as (mt & _ & Ex); cbn in Ex; injection Ex as <- end.
  match goal with H : run_cmd _ _ _ _ _ _ _ _ _ _ _ |- _ => inversion H; subst end.
  match goal with HM : wf_exp _ _ _ (a_mem _ _) |- _ =>
    apply (@alg_type_check_complete (gc_mk nil)) in HM; [| apply user_exp_all ] end.
  match goal with HM : alg_type_check _ _ (a_mem _ _) |- _ => inversion HM; subst end.
  match goal with HM : alg_type_infer _ _ (a_mem _ _) |- _ => inversion HM; subst end.
  - match goal with H : alg_modexp _ (me_unit _) |- _ => inversion H; subst end; discriminate.
  - match goal with H : modexp_spine _ = _ |- _ => cbn in H; injection H as <- <- <- end; contradiction.
Qed.
