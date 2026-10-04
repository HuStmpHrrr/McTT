From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Command.
From Mctt.Frontend Require Import Elaborator ElabSpec ElabCorrect.

Import Syntax_Notations.
Open Scope string_scope.
Open Scope list_scope.

Import Cst.

(** * The Specification on Concrete Programs

    Surface programs are written as [Cst.prog] values, since the parser runs
    only after extraction.  Positive examples give the core unit, checked by
    [vm_compute] and transferred to [elab_spec] by soundness; negative ones
    are related to nothing, by [elaborate_core_fails].

    [⟨U.M⟩] below abbreviates the module expression
    [qname_mod (q_abs ["U"] ["M"])]. *)

Definition mpath (fq ch : list string) : modexp := qname_mod (q_abs fq ch).

Ltac elab_ok := apply elaborate_core_sound; vm_compute; reflexivity.
Ltac elab_fails := apply elaborate_core_fails; eexists; vm_compute; reflexivity.

(** ** Pre-application

<<
module U (A : Type@0) where
  def a : Type@0 := A end
  module M (B : Type@0) where
    def b : Type@0 := B end
    eval a
    eval b
    eval fun (x : Nat) -> b
  end
  eval M.b Nat
end
>>

    Inside [M], [B] is [#0] and [A] is [#1].  [a] is applied to [A], and [b]
    to [A] and [B]; under the [fun] both shift by one.  Outside [M], [M] is
    the module [⟨U.M⟩ $ A], and [M.b] selects its member [b]. *)
Definition nested : Cst.prog :=
  (nil, ("U" :: nil, ("A", typ 0) :: nil,
         c_def md_pub "a" (typ 0) (var "A") ::
         c_mod "M" (("B", typ 0) :: nil)
           (md_where
             (c_def md_pub "b" (typ 0) (var "B") ::
              c_eval (var "a") None ::
              c_eval (var "b") None ::
              c_eval (fn "x" nat (var "b")) None :: nil)) ::
         c_eval (app (proj (var "M") "b") nat) None :: nil)).

Definition U_a : exp := qname_term (q_abs ("U" :: nil) ("a" :: nil)).
Definition U_M_b : exp := qname_term (q_abs ("U" :: nil) ("M" :: "b" :: nil)).

Example nested_spec :
  elab_spec nested
    (nil, ⋅ ▹ Type@0,
     cc_def "a" true false Type@0 #0 ::
     cc_mod "M" (⋅ ▹ Type@0)
       (cc_def "b" true false Type@0 #0 ::
        cc_eval (U_a $ #1) None ::
        cc_eval (U_M_b $ #1 $ #0) None ::
        cc_eval (λ ℕ (U_M_b $ #2 $ #1)) None :: nil) ::
     cc_eval (a_mem (me_app (mpath ("U" :: nil) ("M" :: nil)) #0) "b" $ ℕ) None :: nil).
Proof. elab_ok. Qed.

(** The first [eval] of [M], derived from the rules.  It is read in the
    scope [B, a ↦ U.a, A]: [a] lies under one binder ([B]) and over one
    ([A]), so it is [U.a] applied to [#1]. *)
Example a_preapplied :
  sel (en_var "B" :: en_mem "a" (q_abs ("U" :: nil) ("a" :: nil)) :: en_var "A" :: nil) (var "a") (U_a $ #1).
Proof.
  apply (sel_var _ _ 1 (en_mem "a" (q_abs ("U" :: nil) ("a" :: nil))) 1); [| apply dt_mem ].
  exists (en_var "B" :: nil), (en_var "A" :: nil); cbn; repeat split.
  intros [H | []]; discriminate.
Qed.

(** ** [examples/ModuleParam.mctt]: a parameterized module and [let module] *)
Definition church : Cst.prog :=
  (nil, ("ModuleParam" :: nil, nil,
         c_mod "Church" (("A", typ 0) :: nil)
           (md_where
             (c_def md_pub "t" (typ 0)
                (pi "z" (var "A") (pi "s" (pi "x" (var "A") (var "A")) (var "A"))) ::
              c_def md_pub "two" (var "t")
                (fn "z" (var "A") (fn "s" (pi "x" (var "A") (var "A"))
                   (app (var "s") (app (var "s") (var "z"))))) :: nil)) ::
         c_eval (letb (d_mod "C" nil (md_alias (app (var "Church") nat)))
                   (app (app (proj (var "C") "two") Cst.zero) (fn "x" nat (Cst.succ (var "x")))))
           (Some nat) :: nil)).

Definition Church_t : exp := qname_term (q_abs ("ModuleParam" :: nil) ("Church" :: "t" :: nil)).
Definition Church_two : exp := qname_term (q_abs ("ModuleParam" :: nil) ("Church" :: "two" :: nil)).

(** Inside [Church], [t] is [Church.t A].  [let module C := Church Nat]
    binds a local module slot, so [C.two] selects [two] of [#0]. *)
Example church_spec :
  elab_spec church
    (nil, ⋅,
     cc_mod "Church" (⋅ ▹ Type@0)
       (cc_def "t" true false Type@0 (Π #0 (Π (Π #1 #2) #2)) ::
        cc_def "two" true false (Church_t $ #0) (λ #0 (λ (Π #1 #2) (#0 $ (#0 $ #1)))) :: nil) ::
     cc_eval (ℓₘ (gu_mk ⋅ (Syntax.md_alias (me_app (mpath ("ModuleParam" :: nil) ("Church" :: nil)) ℕ)))
              in (a_mem (me_var 0) "two" $ zero $ λ ℕ (succ #0))) (Some ℕ) :: nil).
Proof. elab_ok. Qed.

(** ** [examples/ImportUse.mctt]: privacy, [import … as], [import … use] *)
Definition import_use : Cst.prog :=
  (nil, ("ImportUse" :: nil, nil,
         c_mod "Impl" nil
           (md_where
             (c_def md_priv "secret" nat (Cst.succ (Cst.succ (Cst.succ Cst.zero))) ::
              c_def md_pub "exposed" nat (Cst.succ (var "secret")) :: nil)) ::
         c_import nil ("Impl" :: nil) (i_as "I") ::
         c_import nil ("Impl" :: nil) (i_use ("exposed" :: nil)) ::
         c_eval (app (proj (var "I") "exposed") (var "exposed")) None :: nil)).

Definition Impl_ : string -> exp := fun x => qname_term (q_abs ("ImportUse" :: nil) ("Impl" :: x :: nil)).

Definition Impl : modexp := mpath ("ImportUse" :: nil) ("Impl" :: nil).

(** A private member is visible in its own frame.  An import is a command
    the core checks; [I] and [exposed] name [Impl] and its member. *)
Example import_use_spec :
  elab_spec import_use
    (nil, ⋅,
     cc_mod "Impl" ⋅
       (cc_def "secret" true true ℕ (succ (succ (succ zero))) ::
        cc_def "exposed" true false ℕ (succ (Impl_ "secret")) :: nil) ::
     cc_import None Impl nil ::
     cc_import None Impl ("exposed" :: nil) ::
     cc_eval (a_mem Impl "exposed" $ (a_mem Impl "exposed")) None :: nil).
Proof. elab_ok. Qed.

(** ** [examples/multi/Main.mctt]: leading imports of other units *)
Definition main_mctt : Cst.prog :=
  (c_import ("Lib" :: "Arith" :: nil) nil (i_use ("quadruple" :: nil)) ::
   c_import ("Lib" :: "Num" :: nil) nil (i_as "N") ::
   c_import ("Lib" :: "Num" :: nil) ("Ops" :: nil) (i_use ("pred" :: nil)) :: nil,
   ("Main" :: nil, nil,
    c_eval (app (var "quadruple") (Cst.succ (Cst.succ Cst.zero))) (Some nat) ::
    c_eval (app (proj (var "N") "double") (Cst.succ (Cst.succ (Cst.succ Cst.zero)))) None ::
    c_eval (app (var "pred") (app (proj (var "N") "double") (Cst.succ (Cst.succ (Cst.succ (Cst.succ (Cst.succ Cst.zero)))))))
      (Some nat) :: nil)).

(** A leading import loads its unit and names the module at its member
    path; the aliases select members of it. *)
Definition Arith : modexp := mpath ("Lib" :: "Arith" :: nil) nil.
Definition Num : modexp := mpath ("Lib" :: "Num" :: nil) nil.
Definition Ops : modexp := mpath ("Lib" :: "Num" :: nil) ("Ops" :: nil).

Example main_spec :
  elab_spec main_mctt
    (cc_import (Some ("Lib" :: "Arith" :: nil)) Arith ("quadruple" :: nil) ::
     cc_import (Some ("Lib" :: "Num" :: nil)) Num nil ::
     cc_import (Some ("Lib" :: "Num" :: nil)) Ops ("pred" :: nil) :: nil,
     ⋅,
     cc_eval (a_mem Arith "quadruple" $ succ (succ zero)) (Some ℕ) ::
     cc_eval (a_mem Num "double" $ succ (succ (succ zero))) None ::
     cc_eval (a_mem Ops "pred" $ (a_mem Num "double" $ succ (succ (succ (succ (succ zero)))))) (Some ℕ) :: nil).
Proof. elab_ok. Qed.

(** ** [examples/TrueFalse.mctt]: the unit type and the empty type

    The motive of [exfalso] binds [x], so [Nat] is elaborated under one more
    binder. *)
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
    (c_mod "I" nil (md_where (c_def md_priv "s" nat Cst.zero :: nil)) ::
     c_eval (proj (var "I") "s") None :: nil))
    (nil, ⋅,
     cc_mod "I" ⋅ (cc_def "s" true true ℕ zero :: nil) ::
     cc_eval (a_mem (mpath ("T" :: nil) ("I" :: nil)) "s") None :: nil).
Proof. elab_ok. Qed.

(** A frame nested in a member's own frame names it directly. *)
Example private_nested : exists u, elab_spec (unit_of
  (c_def md_priv "s" nat Cst.zero ::
   c_mod "I" nil (md_where (c_eval (var "s") None :: nil)) :: nil)) u.
Proof. eexists; elab_ok. Qed.

(** Redeclaring in the same frame is an error … *)
Example redeclare_same : forall u, ~ elab_spec (unit_of
  (c_def md_pub "x" nat Cst.zero :: c_def md_pub "x" nat Cst.zero :: nil)) u.
Proof. elab_fails. Qed.

(** … also over an alias … *)
Example redeclare_alias : forall u, ~ elab_spec (unit_of
  (c_mod "I" nil (md_where nil) :: c_import nil ("I" :: nil) (i_as "x") ::
   c_def md_pub "x" nat Cst.zero :: nil)) u.
Proof. elab_fails. Qed.

(** … but shadowing an enclosing frame's member is allowed. *)
Example shadow_parent :
  elab_spec (unit_of
    (c_def md_pub "x" nat Cst.zero ::
     c_mod "I" nil
       (md_where (c_def md_pub "x" nat (Cst.succ Cst.zero) :: c_eval (var "x") None :: nil)) :: nil))
    (nil, ⋅,
     cc_def "x" true false ℕ zero ::
     cc_mod "I" ⋅ (cc_def "x" true false ℕ (succ zero) ::
                   cc_eval (qname_term (q_abs ("T" :: nil) ("I" :: "x" :: nil))) None :: nil) :: nil).
Proof. elab_ok. Qed.

(** A definition does not see itself. *)
Example no_self : forall u, ~ elab_spec (unit_of (c_def md_pub "x" nat (var "x") :: nil)) u.
Proof. elab_fails. Qed.

(** A projection out of a closed module selects a member of the module
    expression; whether [M] still expects its parameter is left to typing. *)
Example partial_args :
  elab_spec (unit_of
    (c_mod "M" (("A", typ 0) :: nil) (md_where (c_def md_pub "f" (typ 0) (var "A") :: nil)) ::
     c_eval (proj (var "M") "f") None :: nil))
    (nil, ⋅,
     cc_mod "M" (⋅ ▹ Type@0) (cc_def "f" true false Type@0 #0 :: nil) ::
     cc_eval (a_mem (mpath ("T" :: nil) ("M" :: nil)) "f") None :: nil).
Proof. elab_ok. Qed.

(** [module A.B] is [A], without parameters, holding [B]. *)
Example dotted_module :
  elab_spec (unit_of
    (c_mod_dotted "B" ("A" :: nil) (("X", typ 0) :: nil) (md_where (c_def md_abs "y" (typ 0) (var "X") :: nil)) ::
     c_eval (app (proj (proj (var "A") "B") "y") nat) None :: nil))
    (nil, ⋅,
     cc_mod "A" ⋅ (cc_mod "B" (⋅ ▹ Type@0) (cc_def "y" false false Type@0 #0 :: nil) :: nil) ::
     cc_eval (a_mem (me_mem (mpath ("T" :: nil) ("A" :: nil)) "B") "y" $ ℕ) None :: nil).
Proof. elab_ok. Qed.

(** A unit is named by its full path only once imported. *)
Example unit_not_imported : forall u, ~ elab_spec (unit_of
  (c_eval (proj (glob ("L" :: "M" :: nil)) "f") None :: nil)) u.
Proof. elab_fails. Qed.

(** ** One Binding per Name per Frame

    Each program below is rejected by the elaborator with the message shown,
    and so related to nothing by the specification. *)

Ltac elab_err := vm_compute; reflexivity.

(** [def x … ; import M as x]: an alias may not take a member's name. *)
Definition alias_after_member : Cst.prog := unit_of
  (c_mod "M" nil (md_where nil) :: c_def md_pub "x" nat Cst.zero ::
   c_import nil ("M" :: nil) (i_as "x") :: nil).
Example alias_after_member_err : elaborate_core alias_after_member = eerr "x is already declared".
Proof. elab_err. Qed.
Example alias_after_member_spec : forall u, ~ elab_spec alias_after_member u.
Proof. elab_fails. Qed.

(** [import M as x ; def x …]: a member may not take an alias's name. *)
Definition member_after_alias : Cst.prog := unit_of
  (c_mod "M" nil (md_where nil) :: c_import nil ("M" :: nil) (i_as "x") ::
   c_def md_pub "x" nat Cst.zero :: nil).
Example member_after_alias_err : elaborate_core member_after_alias = eerr "x is already declared".
Proof. elab_err. Qed.

(** [def exposed … ; import Impl use (exposed)]: nor may a [use]d name. *)
Definition use_after_member : Cst.prog := unit_of
  (c_mod "Impl" nil (md_where (c_def md_pub "exposed" nat Cst.zero :: nil)) ::
   c_def md_pub "exposed" nat Cst.zero ::
   c_import nil ("Impl" :: nil) (i_use ("exposed" :: nil)) :: nil).
Example use_after_member_err : elaborate_core use_after_member = eerr "exposed is already declared".
Proof. elab_err. Qed.

(** [module M (x : Nat) where def x … end]: a member may not take a
    parameter's name … *)
Definition member_param : Cst.prog := unit_of
  (c_mod "M" (("x", nat) :: nil) (md_where (c_def md_pub "x" nat Cst.zero :: nil)) :: nil).
Example member_param_err : elaborate_core member_param = eerr "x is already declared".
Proof. elab_err. Qed.
Example member_param_spec : forall u, ~ elab_spec member_param u.
Proof. elab_fails. Qed.

(** … nor may a module, here the first segment of [module x.y] in the
    unit's own frame. *)
Definition module_param : Cst.prog :=
  (nil, ("T" :: nil, ("x", nat) :: nil, c_mod_dotted "y" ("x" :: nil) nil (md_where nil) :: nil)).
Example module_param_err : elaborate_core module_param = eerr "x is already declared".
Proof. elab_err. Qed.

(** An alias may not take a parameter's name (here the unit's). *)
Definition alias_param : Cst.prog :=
  (nil, ("T" :: nil, ("x", nat) :: nil,
         c_mod "M" nil (md_where nil) :: c_import nil ("M" :: nil) (i_as "x") :: nil)).
Example alias_param_err : elaborate_core alias_param = eerr "x is already declared".
Proof. elab_err. Qed.
Example alias_param_spec : forall u, ~ elab_spec alias_param u.
Proof. elab_fails. Qed.

(** [module M (x : Nat) (x : Nat)]: a telescope may not repeat a name … *)
Definition dup_params : Cst.prog := unit_of
  (c_mod "M" (("x", nat) :: ("x", nat) :: nil) (md_where nil) :: nil).
Example dup_params_err : elaborate_core dup_params = eerr "duplicate parameter x".
Proof. elab_err. Qed.
Example dup_params_spec : forall u, ~ elab_spec dup_params u.
Proof. elab_fails. Qed.

(** … also the unit's. *)
Definition dup_unit_params : Cst.prog := (nil, ("T" :: nil, ("x", nat) :: ("x", nat) :: nil, nil)).
Example dup_unit_params_err : elaborate_core dup_unit_params = eerr "duplicate parameter x".
Proof. elab_err. Qed.

(** Leading imports: an alias is fresh against the earlier leading aliases. *)
Definition dup_leading : Cst.prog :=
  (c_import ("L" :: "A" :: nil) nil (i_as "N") :: c_import ("L" :: "B" :: nil) nil (i_as "N") :: nil,
   ("T" :: nil, nil, nil)).
Example dup_leading_err : elaborate_core dup_leading = eerr "N is already declared".
Proof. elab_err. Qed.

(** Across frames, shadowing is allowed: a module's parameter may reuse a
    member name of the enclosing frame, and a nested member may reuse the
    enclosing frame's parameter name. *)
Example shadow_param :
  elab_spec (nil, ("T" :: nil, ("x", nat) :: nil,
                   c_def md_pub "y" nat Cst.zero ::
                   c_mod "M" (("y", nat) :: nil)
                     (md_where (c_def md_pub "x" nat (var "y") :: c_eval (var "x") None :: nil)) :: nil))
    (nil, ⋅ ▹ ℕ,
     cc_def "y" true false ℕ zero ::
     cc_mod "M" (⋅ ▹ ℕ)
       (cc_def "x" true false ℕ #0 ::
        cc_eval (qname_term (q_abs ("T" :: nil) ("M" :: "x" :: nil)) $ #1 $ #0) None :: nil) :: nil).
Proof. elab_ok. Qed.

(** ** Local Definitions

    A [let] elaborates to a core [let], and its name is a core variable like
    a [fun] binder.  The core typing rules, not the elaborator, unfold it. *)

(** A [let] inside the definiens of another [let]:

<<
fun (a : Nat) -> let x : Nat := let y : Nat := a in succ y end in succ x end
>>
*)
Example let_nested :
  elab_spec (unit_of
    (c_eval (fn "a" nat
               (letb (d_def "x" nat (letb (d_def "y" nat (var "a")) (Cst.succ (var "y"))))
                  (Cst.succ (var "x")))) None :: nil))
    (nil, ⋅, cc_eval (λ ℕ (ℓ ℕ ≔ (ℓ ℕ ≔ #0 in succ #0) in succ #0)) None :: nil).
Proof. elab_ok. Qed.

(** Each binding sees the earlier ones, in its type and in its definiens:

<<
let A : Type@0 := Nat; z : A := 0; f : forall (n : A) -> A := fun (n : A) -> succ z in f z end
>>
*)
Example let_multi :
  elab_spec (unit_of
    (c_eval (letb (d_def "A" (typ 0) nat)
               (letb (d_def "z" (var "A") Cst.zero)
                  (letb (d_def "f" (pi "n" (var "A") (var "A")) (fn "n" (var "A") (Cst.succ (var "z"))))
                     (app (var "f") (var "z"))))) None :: nil))
    (nil, ⋅,
     cc_eval (ℓ Type@0 ≔ ℕ in ℓ #0 ≔ zero in ℓ (Π #1 #2) ≔ λ #1 (succ #1) in #0 $ #1) None :: nil).
Proof. elab_ok. Qed.

(** A [let] may shadow a member of the frame.  The definiens still sees the
    member, which is applied to the parameter [A]; in the body, [A] lies one
    binder further out.

<<
module M (A : Type@0) where
  def y : Nat := 0 end
  eval let y : Nat := succ y in fun (a : A) -> y end
end
>>
*)
Definition T_M_y : exp := qname_term (q_abs ("T" :: nil) ("M" :: "y" :: nil)).

Example let_shadow :
  elab_spec (unit_of
    (c_mod "M" (("A", typ 0) :: nil)
       (md_where
         (c_def md_pub "y" nat Cst.zero ::
          c_eval (letb (d_def "y" nat (Cst.succ (var "y"))) (fn "a" (var "A") (var "y"))) None :: nil)) :: nil))
    (nil, ⋅,
     cc_mod "M" (⋅ ▹ Type@0)
       (cc_def "y" true false ℕ zero ::
        cc_eval (ℓ ℕ ≔ succ (T_M_y $ #0) in λ #1 #1) None :: nil) :: nil).
Proof. elab_ok. Qed.

(** ** Module Forms *)

Definition T_ (ch : list string) : modexp := mpath ("T" :: nil) ch.

(** [module P (A : Type@0) := M A] is an alias, read under its
    parameters. *)
Example alias_module :
  elab_spec (unit_of
    (c_mod "M" (("A", typ 0) :: nil) (md_where (c_def md_pub "f" (typ 0) (var "A") :: nil)) ::
     c_mod "P" (("A", typ 0) :: nil) (md_alias (app (var "M") (var "A"))) ::
     c_eval (proj (app (var "P") nat) "f") None :: nil))
    (nil, ⋅,
     cc_mod "M" (⋅ ▹ Type@0) (cc_def "f" true false Type@0 #0 :: nil) ::
     cc_alias "P" (⋅ ▹ Type@0) (me_app (T_ ("M" :: nil)) #0) ::
     cc_eval (a_mem (me_app (T_ ("P" :: nil)) ℕ) "f") None :: nil).
Proof. elab_ok. Qed.

(** A local module with a body: each entry binds a core variable for the
    entries after it, a nested module included.

<<
let module L (A : Type@0) where
  def x : A -> A := fun (a : A) -> a end
  module N where def y : Nat := 0 end end
  def z : Nat := N.y end
in L.x end
>>
*)
Example local_body :
  elab_spec (unit_of
    (c_eval
       (letb (d_mod "L" (("A", typ 0) :: nil)
                (md_where
                   (c_def md_pub "x" (pi "a" (var "A") (var "A")) (fn "a" (var "A") (var "a")) ::
                    c_mod "N" nil (md_where (c_def md_pub "y" nat Cst.zero :: nil)) ::
                    c_def md_pub "z" nat (proj (var "N") "y") :: nil)))
          (proj (var "L") "x")) None :: nil))
    (nil, ⋅,
     cc_eval
       (ℓₘ (gu_mk (⋅ ▹ Type@0)
              (md_body
                 (gm_ext
                    (gm_ext
                       (gm_ext gm_nil "x" (ge_def true false (Π #0 #1) (Some (λ #0 #0))))
                       "N" (ge_mod (gu_mk ⋅ (md_body (gm_ext gm_nil "y" (ge_def true false ℕ (Some zero)))))))
                    "z" (ge_def true false ℕ (Some (a_mem (me_var 0) "y"))))))
        in a_mem (me_var 0) "x") None :: nil).
Proof. elab_ok. Qed.

(** An import in a local body is a check entry for the core, and binds its
    aliases for the entries after it; it takes no binder.

<<
let module L where
  module N where def y : Nat := 0 end end
  import N use (y)
  import N as K
  def z : Nat := y end
  def w : Nat := K.y end
in L.w end
>>

    [N] is [me_var 0] at both imports; under [z], [K] is [me_var 1]. *)
Example local_import :
  elab_spec (unit_of
    (c_eval
       (letb (d_mod "L" nil
                (md_where
                   (c_mod "N" nil (md_where (c_def md_pub "y" nat Cst.zero :: nil)) ::
                    c_import nil ("N" :: nil) (i_use ("y" :: nil)) ::
                    c_import nil ("N" :: nil) (i_as "K") ::
                    c_def md_pub "z" nat (var "y") ::
                    c_def md_pub "w" nat (proj (var "K") "y") :: nil)))
          (proj (var "L") "w")) None :: nil))
    (nil, ⋅,
     cc_eval
       (ℓₘ (gu_mk ⋅
              (md_body
                 (gm_ext
                    (gm_ext
                       (gm_check
                          (gm_check
                             (gm_ext gm_nil "N" (ge_mod (gu_mk ⋅ (md_body (gm_ext gm_nil "y" (ge_def true false ℕ (Some zero)))))))
                             (bc_import (me_var 0) ("y" :: nil)))
                          (bc_import (me_var 0) nil))
                       "z" (ge_def true false ℕ (Some (a_mem (me_var 0) "y"))))
                    "w" (ge_def true false ℕ (Some (a_mem (me_var 1) "y"))))))
        in a_mem (me_var 0) "w") None :: nil).
Proof. elab_ok. Qed.

(** An import of a unit in a local body loads nothing: the unit must be
    imported already, here by a leading import. *)
Definition local_unit_import (leading : list Cst.cmd) : Cst.prog :=
  (leading, ("T" :: nil, nil,
    c_eval (letb (d_mod "L" nil (md_where (c_import ("X" :: nil) nil (i_use ("f" :: nil)) :: nil))) Cst.zero)
      None :: nil)).

Example local_unit_loaded :
  elab_spec (local_unit_import (c_import ("X" :: nil) nil i_open :: nil))
    (cc_import (Some ("X" :: nil)) (mpath ("X" :: nil) nil) nil :: nil, ⋅,
     cc_eval (ℓₘ (gu_mk ⋅ (md_body (gm_check gm_nil (bc_import (mpath ("X" :: nil) nil) ("f" :: nil)))))
              in zero) None :: nil).
Proof. elab_ok. Qed.

Example local_unit_not_loaded :
  elaborate_core (local_unit_import nil) = eerr "the unit is not imported".
Proof. vm_compute; reflexivity. Qed.

(** A local body has no [eval]s. *)
Example local_eval :
  elaborate_core (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (c_eval Cst.zero None :: nil))) Cst.zero) None :: nil))
  = eerr "eval is not allowed in a local module".
Proof. vm_compute; reflexivity. Qed.

(** [module A.B] in a local body is [A], without parameters, holding [B]. *)
Example local_path :
  elab_spec (unit_of
    (c_eval
       (letb (d_mod "L" nil
                (md_where (c_mod_dotted "B" ("A" :: nil) nil (md_where (c_def md_pub "y" nat Cst.zero :: nil)) :: nil)))
          (proj (proj (proj (var "L") "A") "B") "y")) None :: nil))
    (nil, ⋅,
     cc_eval
       (ℓₘ (gu_mk ⋅ (md_body (gm_ext gm_nil "A"
               (ge_mod (gu_mk ⋅ (md_body (gm_ext gm_nil "B"
                  (ge_mod (gu_mk ⋅ (md_body (gm_ext gm_nil "y" (ge_def true false ℕ (Some zero)))))))))))))
        in a_mem (me_mem (me_mem (me_var 0) "A") "B") "y") None :: nil).
Proof. elab_ok. Qed.

(** An import [as] alias names a module, not a term. *)
Example alias_not_term :
  elaborate_core (unit_of
    (c_mod "M" nil (md_where nil) :: c_import nil ("M" :: nil) (i_as "N") ::
     c_eval (var "N") None :: nil)) = eerr "a module is not a term".
Proof. elab_err. Qed.

(** A term is not a module. *)
Example term_not_module :
  elaborate_core (unit_of (c_mod "P" nil (md_alias nat) :: nil)) = eerr "not a module".
Proof. elab_err. Qed.

(** An alias is a member: its name must be fresh. *)
Example alias_redeclared :
  elaborate_core (unit_of
    (c_mod "M" nil (md_where nil) :: c_mod "M" nil (md_alias (var "M")) :: nil))
  = eerr "M is already declared".
Proof. elab_err. Qed.

(** A local module's telescope may not repeat a name. *)
Example local_dup_params :
  elaborate_core (unit_of
    (c_eval (letb (d_mod "L" (("x", nat) :: ("x", nat) :: nil) (md_where nil)) Cst.zero) None :: nil))
  = eerr "duplicate parameter x".
Proof. elab_err. Qed.

(** [import] needs a target. *)
Example import_nothing :
  elaborate_core (unit_of (c_import nil nil i_open :: nil)) = eerr "nothing to import".
Proof. elab_err. Qed.

(** ** The Running Example of [ElabSpec]

<<
module Main where
  module M (A : Type@0) where
    def id (x : A) : A := x end
    module N (B : Type@0) where
      def k (x : A) (y : B) : A := id x end
    end
  end
  def j : forall (x : Nat) -> Nat := M.id Nat end
end
>>
*)
Definition running : Cst.prog := (nil, ("Main" :: nil, nil,
  c_mod "M" (("A", typ 0) :: nil)
    (md_where
      (c_def md_pub "id" (pi "x" (var "A") (var "A")) (fn "x" (var "A") (var "x")) ::
       c_mod "N" (("B", typ 0) :: nil)
         (md_where
           (c_def md_pub "k" (pi "x" (var "A") (pi "y" (var "B") (var "A")))
              (fn "x" (var "A") (fn "y" (var "B") (app (var "id") (var "x")))) :: nil)) :: nil)) ::
  c_def md_pub "j" (pi "x" nat nat) (app (proj (var "M") "id") nat) :: nil)).

Definition Main_M_id : exp := qname_term (q_abs ("Main" :: nil) ("M" :: "id" :: nil)).

Example running_spec :
  elab_spec running
    (nil, ⋅,
     cc_mod "M" (⋅ ▹ Type@0)
       (cc_def "id" true false (Π #0 #1) (λ #0 #0) ::
        cc_mod "N" (⋅ ▹ Type@0)
          (cc_def "k" true false (Π #1 (Π #1 #3)) (λ #1 (λ #1 (Main_M_id $ #3 $ #1)))
             :: nil) :: nil) ::
     cc_def "j" true false (Π ℕ ℕ) (a_mem (mpath ("Main" :: nil) ("M" :: nil)) "id" $ ℕ) :: nil).
Proof. elab_ok. Qed.
