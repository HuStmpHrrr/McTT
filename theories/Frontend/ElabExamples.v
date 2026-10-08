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

(** Items as the parser writes them: [as W], and [use (us) export (es)]. *)
Definition i_as (W : string) : list iitem := (None, W, true) :: nil.
Definition i_items (us es : list (string * string)) : list iitem :=
  map (fun p => (Some (fst p), snd p, true)) us ++ map (fun p => (Some (fst p), snd p, false)) es.
Ltac elab_fails := apply elaborate_core_fails; eexists; vm_compute; reflexivity.

(** ** Pre-application

<<
module U (A : Typeω@0) where
  def a : Typeω@0 := A end
  module M (B : Typeω@0) where
    def b : Typeω@0 := B end
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
         c_mod false "M" (("B", typ 0) :: nil)
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
    (nil, ⋅ ▹ Typeω@0,
     cc_def "a" true false Typeω@0 (Some #0) ::
     cc_mod "M" false (⋅ ▹ Typeω@0)
       (cc_def "b" true false Typeω@0 (Some #0) ::
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

Definition Church_t : exp := qname_term (q_abs ("ModuleParam" :: nil) ("Church" :: "t" :: nil)).
Definition Church_two : exp := qname_term (q_abs ("ModuleParam" :: nil) ("Church" :: "two" :: nil)).

(** Inside [Church], [t] is [Church.t A].  [let module C := Church Nat]
    binds a local module slot, so [C.two] selects [two] of [#0]. *)
Example church_spec :
  elab_spec church
    (nil, ⋅,
     cc_mod "Church" false (⋅ ▹ Typeω@0)
       (cc_def "t" true false Typeω@0 (Some (Π #0 (Π (Π #1 #2) #2))) ::
        cc_def "two" true false (Church_t $ #0) (Some (λ #0 (λ (Π #1 #2) (#0 $ (#0 $ #1))))) :: nil) ::
     cc_eval (ℓₘ (gu_mk ⋅ (Syntax.md_alias (me_app (mpath ("ModuleParam" :: nil) ("Church" :: nil)) ℕ)))
              in (a_mem (me_var 0) "two" $ zero $ λ ℕ (succ #0))) (Some ℕ) :: nil).
Proof. elab_ok. Qed.

(** ** [examples/ImportUse.mctt]: privacy, [open … as], [open … use] *)
Definition import_use : Cst.prog :=
  (nil, ("ImportUse" :: nil, nil,
         c_mod false "Impl" nil
           (md_where
             (c_def md_priv "secret" nat (Cst.succ (Cst.succ (Cst.succ Cst.zero))) ::
              c_def md_pub "exposed" nat (Cst.succ (var "secret")) :: nil)) ::
         c_open nil ("Impl" :: nil) nil (i_as "I") ::
         c_open nil ("Impl" :: nil) nil (i_items (("exposed", "exposed") :: nil) nil) ::
         c_eval (app (proj (var "I") "exposed") (var "exposed")) None :: nil)).

Definition Impl_ : string -> exp := fun x => qname_term (q_abs ("ImportUse" :: nil) ("Impl" :: x :: nil)).

Definition Impl : modexp := mpath ("ImportUse" :: nil) ("Impl" :: nil).

(** A private member is visible in its own frame.  An open is a command
    whose items the core declares as members of the frame: [I] and
    [exposed] are the members [ImportUse.I] and [ImportUse.exposed], which
    the core defines as [Impl] and its member. *)
Definition ImportUse_ (ch : list string) : qname := q_abs ("ImportUse" :: nil) ch.

Example import_use_spec :
  elab_spec import_use
    (nil, ⋅,
     cc_mod "Impl" false ⋅
       (cc_def "secret" true true ℕ (Some (succ (succ (succ zero)))) ::
        cc_def "exposed" true false ℕ (Some (succ (Impl_ "secret"))) :: nil) ::
     cc_open Impl ((None, "I", true) :: nil) ::
     cc_open Impl ((Some "exposed", "exposed", true) :: nil) ::
     cc_eval (a_mem (qname_mod (ImportUse_ ("I" :: nil))) "exposed" $ (qname_term (ImportUse_ ("exposed" :: nil))))
       None :: nil).
Proof. elab_ok. Qed.

(** ** [examples/multi/Main.mctt]: leading imports of other units

    Each is the long form, [import X::Y] then [open X::Y …]
    ([Cst.import_cmds]). *)
Definition main_mctt : Cst.prog :=
  (import_cmds ("Lib" :: "Arith" :: nil) nil nil None (i_items (("quadruple", "quadruple") :: nil) nil) ++
   import_cmds ("Lib" :: "Num" :: nil) nil nil (Some "N") nil ++
   import_cmds ("Lib" :: "Num" :: nil) ("Ops" :: nil) nil None (i_items (("pred", "pred") :: nil) nil),
   ("Main" :: nil, nil,
    c_eval (app (var "quadruple") (Cst.succ (Cst.succ Cst.zero))) (Some nat) ::
    c_eval (app (proj (var "N") "double") (Cst.succ (Cst.succ (Cst.succ Cst.zero)))) None ::
    c_eval (app (var "pred") (app (proj (var "N") "double") (Cst.succ (Cst.succ (Cst.succ (Cst.succ (Cst.succ Cst.zero)))))))
      (Some nat) :: nil)).

(** A leading import loads its unit before the unit runs, and is read again
    as the first commands of the unit's body, where loading an already
    loaded unit does nothing; a leading open declares its items there, as
    members of the unit. *)
Definition Arith : modexp := mpath ("Lib" :: "Arith" :: nil) nil.
Definition Num : modexp := mpath ("Lib" :: "Num" :: nil) nil.
Definition Ops : modexp := mpath ("Lib" :: "Num" :: nil) ("Ops" :: nil).
Definition Main_ (x : string) : exp := qname_term (q_abs ("Main" :: nil) (x :: nil)).

Example main_spec :
  elab_spec main_mctt
    (cc_load ("Lib" :: "Arith" :: nil) :: cc_load ("Lib" :: "Num" :: nil) :: cc_load ("Lib" :: "Num" :: nil) :: nil,
     ⋅,
     cc_load ("Lib" :: "Arith" :: nil) :: cc_open Arith ((Some "quadruple", "quadruple", true) :: nil) ::
     cc_load ("Lib" :: "Num" :: nil) :: cc_open Num ((None, "N", true) :: nil) ::
     cc_load ("Lib" :: "Num" :: nil) :: cc_open Ops ((Some "pred", "pred", true) :: nil) ::
     cc_eval (Main_ "quadruple" $ succ (succ zero)) (Some ℕ) ::
     cc_eval (a_mem (mpath ("Main" :: nil) ("N" :: nil)) "double" $ succ (succ (succ zero))) None ::
     cc_eval (Main_ "pred" $ (a_mem (mpath ("Main" :: nil) ("N" :: nil)) "double"
                               $ succ (succ (succ (succ (succ zero)))))) (Some ℕ) :: nil).
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
    (c_mod false "I" nil (md_where (c_def md_priv "s" nat Cst.zero :: nil)) ::
     c_eval (proj (var "I") "s") None :: nil))
    (nil, ⋅,
     cc_mod "I" false ⋅ (cc_def "s" true true ℕ (Some zero) :: nil) ::
     cc_eval (a_mem (mpath ("T" :: nil) ("I" :: nil)) "s") None :: nil).
Proof. elab_ok. Qed.

(** A frame nested in a member's own frame names it directly. *)
Example private_nested : exists u, elab_spec (unit_of
  (c_def md_priv "s" nat Cst.zero ::
   c_mod false "I" nil (md_where (c_eval (var "s") None :: nil)) :: nil)) u.
Proof. eexists; elab_ok. Qed.

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
     cc_mod "I" false ⋅ (cc_def "x" true false ℕ (Some (succ zero)) ::
                   cc_eval (qname_term (q_abs ("T" :: nil) ("I" :: "x" :: nil))) None :: nil) :: nil).
Proof. elab_ok. Qed.

(** A definition does not see itself. *)
Example no_self : forall u, ~ elab_spec (unit_of (c_def md_pub "x" nat (var "x") :: nil)) u.
Proof. elab_fails. Qed.

(** A projection out of a closed module selects a member of the module
    expression; whether [M] still expects its parameter is left to typing. *)
Example partial_args :
  elab_spec (unit_of
    (c_mod false "M" (("A", typ 0) :: nil) (md_where (c_def md_pub "f" (typ 0) (var "A") :: nil)) ::
     c_eval (proj (var "M") "f") None :: nil))
    (nil, ⋅,
     cc_mod "M" false (⋅ ▹ Typeω@0) (cc_def "f" true false Typeω@0 (Some #0) :: nil) ::
     cc_eval (a_mem (mpath ("T" :: nil) ("M" :: nil)) "f") None :: nil).
Proof. elab_ok. Qed.

(** [module A.B] is [A], without parameters, holding [B]. *)
Example dotted_module :
  elab_spec (unit_of
    (c_mod_dotted false "B" ("A" :: nil) (("X", typ 0) :: nil) (md_where (c_def md_abs "y" (typ 0) (var "X") :: nil)) ::
     c_eval (app (proj (proj (var "A") "B") "y") nat) None :: nil))
    (nil, ⋅,
     cc_mod "A" false ⋅ (cc_mod "B" false (⋅ ▹ Typeω@0) (cc_def "y" false false Typeω@0 (Some #0) :: nil) :: nil) ::
     cc_eval (a_mem (me_mem (mpath ("T" :: nil) ("A" :: nil)) "B") "y" $ ℕ) None :: nil).
Proof. elab_ok. Qed.

(** A unit is named by its full path only once imported. *)
Example unit_not_imported : forall u, ~ elab_spec (unit_of
  (c_eval (proj (glob ("L" :: "M" :: nil)) "f") None :: nil)) u.
Proof. elab_fails. Qed.

(** The error names the unit by its path. *)
Example unit_not_imported_msg :
  elaborate_core (unit_of (c_eval (proj (glob ("L" :: "M" :: nil)) "f") None :: nil))
  = eerr "the unit L›M is not imported".
Proof. vm_compute; reflexivity. Qed.

(** ** Definition Keywords

    Each keyword is [def] with the modifiers it implies, and takes [def]'s
    parameters ([Cst.def_cmd]); a modifier it implies already is rejected,
    with the message shown.  [theorem foo (n : Nat) : Nat := n end] is: *)
Example kw_theorem :
  elab_spec (unit_of (def_cmd dk_theorem md_pub "foo" (pi "n" nat nat) (fn "n" nat (var "n")) :: nil))
    (nil, ⋅, cc_def "foo" false false (Π ℕ ℕ) (Some (λ ℕ #0)) :: nil).
Proof. elab_ok. Qed.

(** [private lemma], [fact], [remark], [let], [abstract given]: *)
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
Proof. vm_compute; reflexivity. Qed.
Example kw_lemma_abstract :
  elaborate_core (unit_of (def_cmd dk_lemma md_priv_abs "a" nat Cst.zero :: nil)) = eerr "lemma is already abstract".
Proof. vm_compute; reflexivity. Qed.
Example kw_fact_private :
  elaborate_core (unit_of (def_cmd dk_fact md_priv "a" nat Cst.zero :: nil)) = eerr "fact takes no modifiers".
Proof. vm_compute; reflexivity. Qed.
Example kw_remark_abstract :
  elaborate_core (unit_of (def_cmd dk_remark md_abs "a" nat Cst.zero :: nil)) = eerr "remark takes no modifiers".
Proof. vm_compute; reflexivity. Qed.
Example kw_let_private :
  elaborate_core (unit_of (def_cmd dk_let md_priv "a" nat Cst.zero :: nil)) = eerr "let is already private".
Proof. vm_compute; reflexivity. Qed.
Example kw_given_private :
  elaborate_core (unit_of (def_cmd dk_given md_priv_abs "a" nat Cst.zero :: nil)) = eerr "given is already private".
Proof. vm_compute; reflexivity. Qed.

(** ** Axioms

    [axiom x (ps) : A] takes [def]'s parameters and type and has no body
    ([Cst.axiom_cmd]); it is opaque, and takes no modifiers.
    [axiom f (n : Nat) : Nat  def g : Nat := f 0 end] is: *)
Example axiom_member :
  elab_spec (unit_of (axiom_cmd md_pub "f" (pi "n" nat nat) ::
                      def_cmd dk_def md_pub "g" nat (app (var "f") Cst.zero) :: nil))
    (nil, ⋅, cc_def "f" false false (Π ℕ ℕ) None ::
             cc_def "g" true false ℕ (Some (a_mem (mpath ("T" :: nil) nil) "f" $ zero)) :: nil).
Proof. elab_ok. Qed.

Example axiom_private :
  elaborate_core (unit_of (axiom_cmd md_priv "a" nat :: nil)) = eerr "axiom takes no modifiers".
Proof. vm_compute; reflexivity. Qed.
Example axiom_abstract :
  elaborate_core (unit_of (axiom_cmd md_abs "a" nat :: nil)) = eerr "axiom takes no modifiers".
Proof. vm_compute; reflexivity. Qed.

(** A local body has no axioms. *)
Example axiom_local :
  elaborate_core (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (axiom_cmd md_pub "a" nat :: nil))) Cst.zero) None :: nil))
  = eerr "axioms are not allowed in a local module".
Proof. vm_compute; reflexivity. Qed.

(** A rejected keyword is rejected in a local body too. *)
Example kw_local_rejected :
  elaborate_core (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (def_cmd dk_fact md_abs "a" nat Cst.zero :: nil))) Cst.zero) None :: nil))
  = eerr "fact takes no modifiers".
Proof. vm_compute; reflexivity. Qed.

(** In a local body, a keyword that means [abstract] gives an opaque entry,
    which the core rejects, as it does [abstract def]. *)
Example kw_local_theorem :
  elab_spec (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (def_cmd dk_theorem md_pub "a" nat Cst.zero :: nil))) Cst.zero) None :: nil))
    (nil, ⋅,
     cc_eval (ℓₘ (gu_mk ⋅ (md_body (gm_ext gm_nil "a" (ge_def false false ℕ (Some zero))))) in zero) None :: nil).
Proof. elab_ok. Qed.

(** ** One Binding per Name per Frame

    Each program below is rejected by the elaborator with the message shown,
    and so related to nothing by the specification. *)

Ltac elab_err := vm_compute; reflexivity.

(** [def x … ; open M as x]: an alias may not take a member's name. *)
Definition alias_after_member : Cst.prog := unit_of
  (c_mod false "M" nil (md_where nil) :: c_def md_pub "x" nat Cst.zero ::
   c_open nil ("M" :: nil) nil (i_as "x") :: nil).
Example alias_after_member_err : elaborate_core alias_after_member = eerr "x is already declared".
Proof. elab_err. Qed.
Example alias_after_member_spec : forall u, ~ elab_spec alias_after_member u.
Proof. elab_fails. Qed.

(** [open M as x ; def x …]: a member may not take an alias's name. *)
Definition member_after_alias : Cst.prog := unit_of
  (c_mod false "M" nil (md_where nil) :: c_open nil ("M" :: nil) nil (i_as "x") ::
   c_def md_pub "x" nat Cst.zero :: nil).
Example member_after_alias_err : elaborate_core member_after_alias = eerr "x is already declared".
Proof. elab_err. Qed.

(** [def exposed … ; open Impl use (exposed)]: nor may a [use]d name. *)
Definition use_after_member : Cst.prog := unit_of
  (c_mod false "Impl" nil (md_where (c_def md_pub "exposed" nat Cst.zero :: nil)) ::
   c_def md_pub "exposed" nat Cst.zero ::
   c_open nil ("Impl" :: nil) nil (i_items (("exposed", "exposed") :: nil) nil) :: nil).
Example use_after_member_err : elaborate_core use_after_member = eerr "exposed is already declared".
Proof. elab_err. Qed.

(** [module M (x : Nat) where def x … end]: a member may not take a
    parameter's name … *)
Definition member_param : Cst.prog := unit_of
  (c_mod false "M" (("x", nat) :: nil) (md_where (c_def md_pub "x" nat Cst.zero :: nil)) :: nil).
Example member_param_err : elaborate_core member_param = eerr "x is already declared".
Proof. elab_err. Qed.
Example member_param_spec : forall u, ~ elab_spec member_param u.
Proof. elab_fails. Qed.

(** … nor may a module, here the first segment of [module x.y] in the
    unit's own frame. *)
Definition module_param : Cst.prog :=
  (nil, ("T" :: nil, ("x", nat) :: nil, c_mod_dotted false "y" ("x" :: nil) nil (md_where nil) :: nil)).
Example module_param_err : elaborate_core module_param = eerr "x is already declared".
Proof. elab_err. Qed.

(** An alias may not take a parameter's name (here the unit's). *)
Definition alias_param : Cst.prog :=
  (nil, ("T" :: nil, ("x", nat) :: nil,
         c_mod false "M" nil (md_where nil) :: c_open nil ("M" :: nil) nil (i_as "x") :: nil)).
Example alias_param_err : elaborate_core alias_param = eerr "x is already declared".
Proof. elab_err. Qed.
Example alias_param_spec : forall u, ~ elab_spec alias_param u.
Proof. elab_fails. Qed.

(** [module M (x : Nat) (x : Nat)]: a telescope may not repeat a name … *)
Definition dup_params : Cst.prog := unit_of
  (c_mod false "M" (("x", nat) :: ("x", nat) :: nil) (md_where nil) :: nil).
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
  (import_cmds ("L" :: "A" :: nil) nil nil (Some "N") nil ++ import_cmds ("L" :: "B" :: nil) nil nil (Some "N") nil,
   ("T" :: nil, nil, nil)).
Example dup_leading_err : elaborate_core dup_leading = eerr "N is already declared".
Proof. elab_err. Qed.

(** Across frames, shadowing is allowed: a module's parameter may reuse a
    member name of the enclosing frame, and a nested member may reuse the
    enclosing frame's parameter name. *)
Example shadow_param :
  elab_spec (nil, ("T" :: nil, ("x", nat) :: nil,
                   c_def md_pub "y" nat Cst.zero ::
                   c_mod false "M" (("y", nat) :: nil)
                     (md_where (c_def md_pub "x" nat (var "y") :: c_eval (var "x") None :: nil)) :: nil))
    (nil, ⋅ ▹ ℕ,
     cc_def "y" true false ℕ (Some zero) ::
     cc_mod "M" false (⋅ ▹ ℕ)
       (cc_def "x" true false ℕ (Some #0) ::
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
               (letb (d_def "x" (Some nat) (letb (d_def "y" (Some nat) (var "a")) (Cst.succ (var "y"))))
                  (Cst.succ (var "x")))) None :: nil))
    (nil, ⋅, cc_eval (λ ℕ (ℓ ℕ ≔ (ℓ ℕ ≔ #0 in succ #0) in succ #0)) None :: nil).
Proof. elab_ok. Qed.

(** Each binding sees the earlier ones, in its type and in its definiens:

<<
let A : Typeω@0 := Nat; z : A := 0; f : forall (n : A) -> A := fun (n : A) -> succ z in f z end
>>
*)
Example let_multi :
  elab_spec (unit_of
    (c_eval (letb (d_def "A" (Some (typ 0)) nat)
               (letb (d_def "z" (Some (var "A")) Cst.zero)
                  (letb (d_def "f" (Some (pi "n" (var "A") (var "A"))) (fn "n" (var "A") (Cst.succ (var "z"))))
                     (app (var "f") (var "z"))))) None :: nil))
    (nil, ⋅,
     cc_eval (ℓ Typeω@0 ≔ ℕ in ℓ #0 ≔ zero in ℓ (Π #1 #2) ≔ λ #1 (succ #1) in #0 $ #1) None :: nil).
Proof. elab_ok. Qed.

(** Without an annotation the elaborator emits none; the core infers the
    type of the definiens.  Annotated and unannotated bindings mix:

<<
let A : Typeω@0 := Nat; z := 0; f := fun (n : A) -> succ z in f z end
>>
*)
Example let_mixed :
  elab_spec (unit_of
    (c_eval (letb (d_def "A" (Some (typ 0)) nat)
               (letb (d_def "z" None Cst.zero)
                  (letb (d_def "f" None (fn "n" (var "A") (Cst.succ (var "z"))))
                     (app (var "f") (var "z"))))) None :: nil))
    (nil, ⋅,
     cc_eval (ℓ Typeω@0 ≔ ℕ in ℓ ≔ zero in ℓ ≔ λ #1 (succ #1) in #0 $ #1) None :: nil).
Proof. elab_ok. Qed.

(** A [let] may shadow a member of the frame.  The definiens still sees the
    member, which is applied to the parameter [A]; in the body, [A] lies one
    binder further out.

<<
module M (A : Typeω@0) where
  def y : Nat := 0 end
  eval let y : Nat := succ y in fun (a : A) -> y end
end
>>
*)
Definition T_M_y : exp := qname_term (q_abs ("T" :: nil) ("M" :: "y" :: nil)).

Example let_shadow :
  elab_spec (unit_of
    (c_mod false "M" (("A", typ 0) :: nil)
       (md_where
         (c_def md_pub "y" nat Cst.zero ::
          c_eval (letb (d_def "y" (Some nat) (Cst.succ (var "y"))) (fn "a" (var "A") (var "y"))) None :: nil)) :: nil))
    (nil, ⋅,
     cc_mod "M" false (⋅ ▹ Typeω@0)
       (cc_def "y" true false ℕ (Some zero) ::
        cc_eval (ℓ ℕ ≔ succ (T_M_y $ #0) in λ #1 #1) None :: nil) :: nil).
Proof. elab_ok. Qed.

(** ** Module Forms *)

Definition T_ (ch : list string) : modexp := mpath ("T" :: nil) ch.

(** [module P (A : Typeω@0) := M A] is an alias, read under its
    parameters. *)
Example alias_module :
  elab_spec (unit_of
    (c_mod false "M" (("A", typ 0) :: nil) (md_where (c_def md_pub "f" (typ 0) (var "A") :: nil)) ::
     c_mod false "P" (("A", typ 0) :: nil) (md_alias (app (var "M") (var "A"))) ::
     c_eval (proj (app (var "P") nat) "f") None :: nil))
    (nil, ⋅,
     cc_mod "M" false (⋅ ▹ Typeω@0) (cc_def "f" true false Typeω@0 (Some #0) :: nil) ::
     cc_alias "P" false (⋅ ▹ Typeω@0) (me_app (T_ ("M" :: nil)) #0) ::
     cc_eval (a_mem (me_app (T_ ("P" :: nil)) ℕ) "f") None :: nil).
Proof. elab_ok. Qed.

(** A local module with a body: each entry binds a core variable for the
    entries after it, a nested module included.

<<
let module L (A : Typeω@0) where
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
                    c_mod false "N" nil (md_where (c_def md_pub "y" nat Cst.zero :: nil)) ::
                    c_def md_pub "z" nat (proj (var "N") "y") :: nil)))
          (proj (var "L") "x")) None :: nil))
    (nil, ⋅,
     cc_eval
       (ℓₘ (gu_mk (⋅ ▹ Typeω@0)
              (md_body
                 (gm_ext
                    (gm_ext
                       (gm_ext gm_nil "x" (ge_def true false (Π #0 #1) (Some (λ #0 #0))))
                       "N" (ge_mod false (gu_mk ⋅ (md_body (gm_ext gm_nil "y" (ge_def true false ℕ (Some zero)))))))
                    "z" (ge_def true false ℕ (Some (a_mem (me_var 0) "y"))))))
        in a_mem (me_var 0) "x") None :: nil).
Proof. elab_ok. Qed.

(** An open in a local body is a pre-form the core expands; each of its
    items is a binder of the body.

<<
let module L where
  module N where def y : Nat := 0 end end
  open N use (y)
  open N as K
  def z : Nat := y end
  def w : Nat := K.y end
in L.w end
>>

    [N] is [me_var 0] at the first open and [me_var 1] at the second;
    under [z], [y] is [#1], and under [w], [K] is [me_var 1]. *)
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
       (ℓₘ (gu_mk ⋅
              (md_body
                 (gm_ext
                    (gm_ext
                       (gm_open
                          (gm_open
                             (gm_ext gm_nil "N" (ge_mod false (gu_mk ⋅ (md_body (gm_ext gm_nil "y" (ge_def true false ℕ (Some zero)))))))
                             (me_var 0) ((Some "y", "y", true) :: nil))
                          (me_var 1) ((None, "K", true) :: nil))
                       "z" (ge_def true false ℕ (Some #1)))
                    "w" (ge_def true false ℕ (Some (a_mem (me_var 1) "y"))))))
        in a_mem (me_var 0) "w") None :: nil).
Proof. elab_ok. Qed.

(** An open of a unit in a local body loads nothing: the unit must be
    imported already, here by a leading import. *)
Definition local_unit_import (leading : list Cst.cmd) : Cst.prog :=
  (leading, ("T" :: nil, nil,
    c_eval (letb (d_mod "L" nil (md_where (c_open ("X" :: nil) nil nil (i_items (("f", "f") :: nil) nil) :: nil))) Cst.zero)
      None :: nil)).

Example local_unit_loaded :
  elab_spec (local_unit_import (c_import ("X" :: nil) :: nil))
    (cc_load ("X" :: nil) :: nil, ⋅,
     cc_load ("X" :: nil) ::
     cc_eval (ℓₘ (gu_mk ⋅ (md_body (gm_open gm_nil (mpath ("X" :: nil) nil) ((Some "f", "f", true) :: nil))))
              in zero) None :: nil).
Proof. elab_ok. Qed.

Example local_unit_not_loaded :
  elaborate_core (local_unit_import nil) = eerr "the unit X is not imported".
Proof. vm_compute; reflexivity. Qed.

(** A local body has no [import]s: it opens what is loaded already. *)
Example local_import_rejected :
  elaborate_core (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (c_import ("X" :: nil) :: nil))) Cst.zero) None :: nil))
  = eerr "import is not allowed in a local module; use open".
Proof. vm_compute; reflexivity. Qed.

(** The long form [import X::Y use (f)] in a local body is an [import]
    first, so it is rejected the same way. *)
Example local_long_import_rejected :
  elaborate_core (c_import ("X" :: nil) :: nil, ("T" :: nil, nil,
    c_eval (letb (d_mod "L" nil (md_where (import_cmds ("X" :: nil) nil nil None (i_items (("f", "f") :: nil) nil))))
              Cst.zero) None :: nil))
  = eerr "import is not allowed in a local module; use open".
Proof. vm_compute; reflexivity. Qed.

(** A local body has no [eval]s. *)
Example local_eval :
  elaborate_core (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (c_eval Cst.zero None :: nil))) Cst.zero) None :: nil))
  = eerr "eval is not allowed in a local module".
Proof. vm_compute; reflexivity. Qed.

(** A local body may have [private] entries, a definition or a module: the
    core's privacy check rejects a selection of them from outside the
    body. *)
Example local_private :
  elab_spec (unit_of
    (c_eval (letb (d_mod "L" nil (md_where (c_def md_priv "s" nat Cst.zero ::
                                            c_mod true "N" nil (md_where nil) ::
                                            c_def md_pub "t" nat (Cst.succ (var "s")) :: nil)))
               (proj (var "L") "t")) None :: nil))
    (nil, ⋅,
     cc_eval (ℓₘ (gu_mk ⋅ (md_body (gm_ext (gm_ext (gm_ext gm_nil
                                      "s" (ge_def true true ℕ (Some zero)))
                                      "N" (ge_mod true (gu_mk ⋅ (md_body gm_nil))))
                                      "t" (ge_def true false ℕ (Some (succ #1))))))
              in a_mem (me_var 0) "t") None :: nil).
Proof. elab_ok. Qed.

(** A local open that [use]s a name twice is the core's to reject: the
    names of a local body are checked fresh by typing. *)
Example local_use_dup :
  elab_spec (unit_of
    (c_eval
       (letb (d_mod "L" nil
                (md_where (c_mod false "N" nil (md_where (c_def md_pub "y" nat Cst.zero :: nil)) ::
                           c_open nil ("N" :: nil) nil (i_items (("y", "y") :: ("y", "y") :: nil) nil) :: nil)))
          Cst.zero) None :: nil))
    (nil, ⋅,
     cc_eval
       (ℓₘ (gu_mk ⋅
              (md_body
                 (gm_open
                    (gm_ext gm_nil "N" (ge_mod false (gu_mk ⋅ (md_body (gm_ext gm_nil "y" (ge_def true false ℕ (Some zero)))))))
                    (me_var 0) ((Some "y", "y", true) :: (Some "y", "y", true) :: nil))))
        in zero) None :: nil).
Proof. elab_ok. Qed.

(** [module A.B] in a local body is [A], without parameters, holding [B]. *)
Example local_path :
  elab_spec (unit_of
    (c_eval
       (letb (d_mod "L" nil
                (md_where (c_mod_dotted false "B" ("A" :: nil) nil (md_where (c_def md_pub "y" nat Cst.zero :: nil)) :: nil)))
          (proj (proj (proj (var "L") "A") "B") "y")) None :: nil))
    (nil, ⋅,
     cc_eval
       (ℓₘ (gu_mk ⋅ (md_body (gm_ext gm_nil "A"
               (ge_mod false (gu_mk ⋅ (md_body (gm_ext gm_nil "B"
                  (ge_mod false (gu_mk ⋅ (md_body (gm_ext gm_nil "y" (ge_def true false ℕ (Some zero)))))))))))))
        in a_mem (me_mem (me_mem (me_var 0) "A") "B") "y") None :: nil).
Proof. elab_ok. Qed.

(** An open [as] alias is a member like any other: whether it is a term
    is for typing to decide. *)
Example alias_term :
  elab_spec (unit_of
    (c_mod false "M" nil (md_where nil) :: c_open nil ("M" :: nil) nil (i_as "N") ::
     c_eval (var "N") None :: nil))
    (nil, ⋅,
     cc_mod "M" false ⋅ nil :: cc_open (T_ ("M" :: nil)) ((None, "N", true) :: nil) ::
     cc_eval (qname_term (q_abs ("T" :: nil) ("N" :: nil))) None :: nil).
Proof. elab_ok. Qed.

(** A term is not a module. *)
Example term_not_module :
  elaborate_core (unit_of (c_mod false "P" nil (md_alias nat) :: nil)) = eerr "not a module".
Proof. elab_err. Qed.

(** An alias is a member: its name must be fresh. *)
Example alias_redeclared :
  elaborate_core (unit_of
    (c_mod false "M" nil (md_where nil) :: c_mod false "M" nil (md_alias (var "M")) :: nil))
  = eerr "M is already declared".
Proof. elab_err. Qed.

(** A local module's telescope may not repeat a name. *)
Example local_dup_params :
  elaborate_core (unit_of
    (c_eval (letb (d_mod "L" (("x", nat) :: ("x", nat) :: nil) (md_where nil)) Cst.zero) None :: nil))
  = eerr "duplicate parameter x".
Proof. elab_err. Qed.

(** [open] needs a target. *)
Example open_nothing :
  elaborate_core (unit_of (c_open nil nil nil nil :: nil)) = eerr "nothing to open".
Proof. elab_err. Qed.

(** ** Opens Declare Names

    [use] items are private declarations of the frame, [export] items public
    ones; [c as d] declares [d].  The target may be applied to arguments,
    read as terms where the open stands.

<<
module T (A : Typeω@0) where
  module M (B : Typeω@0) where def c : Typeω@0 := B end def e : Typeω@0 := B end end
  open M A use (c as d) export (e)
  eval d
  eval e
end
>>

    [d] and [e] are the members [T.d] and [T.e], applied to the unit's
    parameter like every member of its frame. *)
Example import_items :
  elab_spec (nil, ("T" :: nil, ("A", typ 0) :: nil,
    c_mod false "M" (("B", typ 0) :: nil)
      (md_where (c_def md_pub "c" (typ 0) (var "B") :: c_def md_pub "e" (typ 0) (var "B") :: nil)) ::
    c_open nil ("M" :: nil) (var "A" :: nil) (i_items (("c", "d") :: nil) (("e", "e") :: nil)) ::
    c_eval (var "d") None :: c_eval (var "e") None :: nil))
    (nil, ⋅ ▹ Typeω@0,
     cc_mod "M" false (⋅ ▹ Typeω@0) (cc_def "c" true false Typeω@0 (Some #0) :: cc_def "e" true false Typeω@0 (Some #0) :: nil) ::
     cc_open (me_app (me_app (T_ ("M" :: nil)) #0) #0)
       ((Some "c", "d", true) :: (Some "e", "e", false) :: nil) ::
     cc_eval (qname_term (q_abs ("T" :: nil) ("d" :: nil)) $ #0) None ::
     cc_eval (qname_term (q_abs ("T" :: nil) ("e" :: nil)) $ #0) None :: nil).
Proof. elab_ok. Qed.

(** An item's name must be fresh in the frame before the open, *)
Example import_item_fresh :
  elaborate_core (unit_of
    (c_mod false "M" nil (md_where (c_def md_pub "c" nat Cst.zero :: nil)) ::
     c_def md_pub "d" nat Cst.zero ::
     c_open nil ("M" :: nil) nil (i_items nil (("c", "d") :: nil)) :: nil))
  = eerr "d is already declared".
Proof. elab_err. Qed.

(** but whether an open declares a name twice, or uses and exports one
    member, is the core's to check ([xe_fresh], [xe_both]). *)
Example import_items_dup :
  elab_spec (unit_of
    (c_mod false "M" nil (md_where (c_def md_pub "c" nat Cst.zero :: nil)) ::
     c_open nil ("M" :: nil) nil (i_items (("c", "c") :: nil) (("c", "c") :: nil)) :: nil))
    (nil, ⋅,
     cc_mod "M" false ⋅ (cc_def "c" true false ℕ (Some zero) :: nil) ::
     cc_open (T_ ("M" :: nil)) ((Some "c", "c", true) :: (Some "c", "c", false) :: nil) :: nil).
Proof. elab_ok. Qed.

(** The arguments of an open are read where it stands. *)
Example import_arg_unbound :
  elaborate_core (unit_of
    (c_mod false "M" (("B", typ 0) :: nil) (md_where nil) ::
     c_open nil ("M" :: nil) (var "B" :: nil) (i_as "W") :: nil))
  = eerr "unbound name B".
Proof. elab_err. Qed.

(** Leading imports and opens are read before the unit's header, where no
    parameter is in scope: their arguments may not name the parameters.

<<
import L::X A as W
module T (A : Typeω@0) where end
>>
*)
Example leading_args :
  elaborate_core (import_cmds ("L" :: "X" :: nil) nil (var "A" :: nil) (Some "W") nil,
                  ("T" :: nil, ("A", typ 0) :: nil, nil))
  = eerr "unbound name A".
Proof. elab_err. Qed.

(** Read again in the unit's own frame, after its parameters, their names
    are members of the unit, applied to its parameters; they are fresh
    against the parameters, *)
Example leading_param :
  elaborate_core (import_cmds ("L" :: "X" :: nil) nil nil (Some "A") nil,
                  ("T" :: nil, ("A", typ 0) :: nil, nil))
  = eerr "A is already declared".
Proof. elab_err. Qed.

(** and the unit's members against them. *)
Example leading_member :
  elaborate_core (import_cmds ("L" :: "X" :: nil) nil nil None (i_items (("f", "f") :: nil) nil),
                  ("T" :: nil, nil, c_def md_pub "f" nat Cst.zero :: nil))
  = eerr "f is already declared".
Proof. elab_err. Qed.

(** In the parameter types, a name a leading open declares denotes what it
    names: [Eq] is the member [Eq] of the unit, and [W] the unit.  In the
    body, they are the members [T.Eq] and [T.W], applied to the unit's
    parameter [p].

<<
import P::E
open P::E as W use (Eq)
module T (p : Eq 1 1) where
  eval W.refl
end
>>

    The [open … as W use (Eq)] is [open P::E as W] then [open W use (Eq)]
    ([Cst.open_cmds]): the item refers to the alias. *)
Definition PE : modexp := mpath ("P" :: "E" :: nil) nil.

Example leading_scope :
  elab_spec (c_import ("P" :: "E" :: nil) ::
             open_cmds ("P" :: "E" :: nil) nil nil (Some "W") (i_items (("Eq", "Eq") :: nil) nil),
             ("T" :: nil, ("p", app (app (var "Eq") (Cst.succ Cst.zero)) (Cst.succ Cst.zero)) :: nil,
              c_eval (proj (var "W") "refl") None :: nil))
    (cc_load ("P" :: "E" :: nil) :: nil,
     ⋅ ▹ (a_mem PE "Eq" $ succ zero $ succ zero),
     cc_load ("P" :: "E" :: nil) ::
     cc_open PE ((None, "W", true) :: nil) ::
     cc_open (me_app (T_ ("W" :: nil)) #0) ((Some "Eq", "Eq", true) :: nil) ::
     cc_eval (a_mem (me_app (T_ ("W" :: nil)) #0) "refl") None :: nil).
Proof. elab_ok. Qed.

(** A name a leading open declares as a module is not a term. *)
Example leading_alias_term :
  elaborate_core (c_import ("P" :: "E" :: nil) :: open_cmds ("P" :: "E" :: nil) nil nil (Some "W") nil,
                  ("T" :: nil, ("p", var "W") :: nil, nil))
  = eerr "a module is not a term".
Proof. elab_err. Qed.

(** A leading open of a unit that is not imported is rejected, as anywhere. *)
Example leading_open_unloaded :
  elaborate_core (open_cmds ("P" :: "E" :: nil) nil nil None (i_items (("Eq", "Eq") :: nil) nil),
                  ("T" :: nil, nil, nil))
  = eerr "the unit P›E is not imported".
Proof. elab_err. Qed.

(** Before the header, an open may [use] but not [export] ([Cst.lead_cmds]),
    in either form:

<<
import P::E
open P::E use (Eq) export (refl)
module T where end
>>
*)
Example leading_export :
  elaborate_core (c_import ("P" :: "E" :: nil) ::
                  lead_cmds (open_cmds ("P" :: "E" :: nil) nil nil None
                               (i_items (("Eq", "Eq") :: nil) (("refl", "refl") :: nil))),
                  ("T" :: nil, nil, nil))
  = eerr "export is not allowed before the module header".
Proof. elab_err. Qed.

Example leading_long_export :
  elaborate_core (lead_cmds (import_cmds ("P" :: "E" :: nil) nil nil (Some "W") (i_items nil (("refl", "refl") :: nil))),
                  ("T" :: nil, nil, nil))
  = eerr "export is not allowed before the module header".
Proof. elab_err. Qed.

(** Elsewhere it may. *)
Example frame_export :
  elab_spec (c_import ("P" :: "E" :: nil) :: nil,
             ("T" :: nil, nil, c_open ("P" :: "E" :: nil) nil nil (i_items nil (("refl", "refl") :: nil)) :: nil))
    (cc_load ("P" :: "E" :: nil) :: nil, ⋅,
     cc_load ("P" :: "E" :: nil) :: cc_open PE ((Some "refl", "refl", false) :: nil) :: nil).
Proof. elab_ok. Qed.

(** A bare import only loads, and importing a unit twice is two loads, the
    second of which the core does nothing for. *)
Example import_twice :
  elab_spec (c_import ("P" :: "E" :: nil) :: nil,
             ("T" :: nil, nil, c_import ("P" :: "E" :: nil) :: nil))
    (cc_load ("P" :: "E" :: nil) :: nil, ⋅,
     cc_load ("P" :: "E" :: nil) :: cc_load ("P" :: "E" :: nil) :: nil).
Proof. elab_ok. Qed.

(** [use] and [export] lists come in any order and any number, as one list
    of items in the order written; the core checks them together.

<<
module M where def a : Nat := 0 end def b : Nat := 1 end def c : Nat := 2 end end
open M export (a) use (b) export (c as d)
>>
*)
Example open_lists :
  elab_spec (unit_of
    (c_mod false "M" nil (md_where (c_def md_pub "a" nat Cst.zero :: c_def md_pub "b" nat (Cst.succ Cst.zero) ::
                                    c_def md_pub "c" nat (Cst.succ (Cst.succ Cst.zero)) :: nil)) ::
     c_open nil ("M" :: nil) nil ((Some "a", "a", false) :: (Some "b", "b", true) :: (Some "c", "d", false) :: nil) ::
     nil))
    (nil, ⋅,
     cc_mod "M" false ⋅ (cc_def "a" true false ℕ (Some zero) :: cc_def "b" true false ℕ (Some (succ zero)) ::
                         cc_def "c" true false ℕ (Some (succ (succ zero))) :: nil) ::
     cc_open (T_ ("M" :: nil)) ((Some "a", "a", false) :: (Some "b", "b", true) :: (Some "c", "d", false) :: nil) :: nil).
Proof. elab_ok. Qed.

(** In a local body, an open's items are binders of the body, [use]d or
    [export]ed alike; privacy is the core's.

<<
let module L where
  module N (A : Typeω@0) where def y : Typeω@0 := A end end
  open N Nat use (y as u) export (y)
in L.y end
>>
*)
Example local_items :
  elab_spec (unit_of
    (c_eval
       (letb (d_mod "L" nil
                (md_where
                   (c_mod false "N" (("A", typ 0) :: nil) (md_where (c_def md_pub "y" (typ 0) (var "A") :: nil)) ::
                    c_open nil ("N" :: nil) (nat :: nil) (i_items (("y", "u") :: nil) (("y", "y") :: nil)) :: nil)))
          (proj (var "L") "y")) None :: nil))
    (nil, ⋅,
     cc_eval
       (ℓₘ (gu_mk ⋅
              (md_body
                 (gm_open
                    (gm_ext gm_nil "N" (ge_mod false (gu_mk (⋅ ▹ Typeω@0)
                                         (md_body (gm_ext gm_nil "y" (ge_def true false Typeω@0 (Some #0)))))))
                    (me_app (me_var 0) ℕ) ((Some "y", "u", true) :: (Some "y", "y", false) :: nil))))
        in a_mem (me_var 0) "y") None :: nil).
Proof. elab_ok. Qed.

(** ** The Running Example of [ElabSpec]

<<
module Main where
  module M (A : Typeω@0) where
    def id (x : A) : A := x end
    module N (B : Typeω@0) where
      def k (x : A) (y : B) : A := id x end
    end
  end
  def j : forall (x : Nat) -> Nat := M.id Nat end
end
>>
*)
Definition running : Cst.prog := (nil, ("Main" :: nil, nil,
  c_mod false "M" (("A", typ 0) :: nil)
    (md_where
      (c_def md_pub "id" (pi "x" (var "A") (var "A")) (fn "x" (var "A") (var "x")) ::
       c_mod false "N" (("B", typ 0) :: nil)
         (md_where
           (c_def md_pub "k" (pi "x" (var "A") (pi "y" (var "B") (var "A")))
              (fn "x" (var "A") (fn "y" (var "B") (app (var "id") (var "x")))) :: nil)) :: nil)) ::
  c_def md_pub "j" (pi "x" nat nat) (app (proj (var "M") "id") nat) :: nil)).

Definition Main_M_id : exp := qname_term (q_abs ("Main" :: nil) ("M" :: "id" :: nil)).

Example running_spec :
  elab_spec running
    (nil, ⋅,
     cc_mod "M" false (⋅ ▹ Typeω@0)
       (cc_def "id" true false (Π #0 #1) (Some (λ #0 #0)) ::
        cc_mod "N" false (⋅ ▹ Typeω@0)
          (cc_def "k" true false (Π #1 (Π #1 #3)) (Some (λ #1 (λ #1 (Main_M_id $ #3 $ #1))))
             :: nil) :: nil) ::
     cc_def "j" true false (Π ℕ ℕ) (Some (a_mem (mpath ("Main" :: nil) ("M" :: nil)) "id" $ ℕ)) :: nil).
Proof. elab_ok. Qed.
