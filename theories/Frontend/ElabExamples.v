From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Command.
From Mctt.Frontend Require Import Elaborator ElabSpec ElabCorrect.

Import Syntax_Notations.
Open Scope string_scope.
Open Scope list_scope.

Import Cst.

(** * The Specification on Concrete Programs

    Surface programs written as [Cst.prog] values by hand (the parser is
    extracted, so it does not run here).  Positive examples state the core
    unit, checked by [vm_compute] and transported to [elab_spec] by
    soundness; negative ones show that the specification relates the program
    to nothing, by [elaborate_core_fails]. *)

Ltac elab_ok := apply elaborate_core_sound; vm_compute; reflexivity.
Ltac elab_fails := apply elaborate_core_fails; eexists; vm_compute; reflexivity.

(** ** Pre-application

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

    Inside [M], [B] is [#0] and [A] is [#1].  [a] is a member of [U], so it is
    pre-applied to [A] only; [b] is a member of [M], so to [A] and [B]; under
    the [fun] both move one binder out.  Outside [M], [M] is closed: [M.b] is
    pre-applied to [A] (open) and gets [B] from the user. *)
Definition nested : Cst.prog :=
  (nil, ("U" :: nil, ("A", typ 0) :: nil,
         c_def md_pub "a" (typ 0) (var "A") ::
         c_mod ("M" :: nil) (("B", typ 0) :: nil)
           (c_def md_pub "b" (typ 0) (var "B") ::
            c_eval (var "a") None ::
            c_eval (var "b") None ::
            c_eval (fn "x" nat (var "b")) None :: nil) ::
         c_eval (app (proj (var "M") "b") nat) None :: nil)).

Definition U_a : exp := a_glob (p_abs ("U" :: nil) ("a" :: nil)).
Definition U_M_b : exp := a_glob (p_abs ("U" :: nil) ("M" :: "b" :: nil)).

Example nested_spec :
  elab_spec nested
    (nil, ⋅ ▹ Type@0,
     cc_def "a" true false Type@0 #0 ::
     cc_mod "M" (⋅ ▹ Type@0)
       (cc_def "b" true false Type@0 #0 ::
        cc_eval (U_a $ #1) None ::
        cc_eval (U_M_b $ #1 $ #0) None ::
        cc_eval (λ ℕ (U_M_b $ #2 $ #1)) None :: nil) ::
     cc_eval (U_M_b $ #0 $ ℕ) None :: nil).
Proof. elab_ok. Qed.

(** The first [eval] of [M], derived by hand from the rules: [a] is not bound
    in [M]'s frame ([fb_next]), so it is the definition of [U]'s frame,
    pre-applied to [U]'s telescope, which starts one binder in. *)
Definition U_frame : sframe :=
  sf_mk nil (("A", Type@0) :: nil) (cc_def "a" true false Type@0 #0 :: nil) ss_empty.
Definition M_frame : sframe := sf_mk ("M" :: nil) (("B", Type@0) :: nil) nil ss_empty.

Example a_preapplied :
  sel ("U" :: nil) ss_empty (M_frame :: U_frame :: nil) nil (var "a") (s_term (U_a $ #1)).
Proof.
  apply sel_frame; [ intros [] |].
  apply fb_next.
  - intros [Ha | [Hd | Hp]].
    + apply Ha; intros [].
    + destruct Hd as (c & [] & _).
    + destruct Hp as [Hp | []]; discriminate.
  - change (s_term (U_a $ #1)) with (s_term (apps (a_glob (p_abs ("U" :: nil) (sf_path U_frame ++ "a" :: nil))) (#1 :: nil))).
    apply (fb_def _ _ _ _ _ "a" true false Type@0 #0 (#1 :: nil)).
    + intros [].
    + exists nil, nil; repeat split. intros (c & [] & _).
    + match goal with |- preapp ?off _ _ => change (#1 :: nil) with (nil ++ vars_desc off (List.length (sf_params U_frame))) end.
      repeat constructor.
Qed.

(** ** [examples/module_param.mctt]: a parameterized module and [let module] *)
Definition church : Cst.prog :=
  (nil, ("ModuleParam" :: nil, nil,
         c_mod ("Church" :: nil) (("A", typ 0) :: nil)
           (c_def md_pub "t" (typ 0)
              (pi "z" (var "A") (pi "s" (pi "x" (var "A") (var "A")) (var "A"))) ::
            c_def md_pub "two" (var "t")
              (fn "z" (var "A") (fn "s" (pi "x" (var "A") (var "A"))
                 (app (var "s") (app (var "s") (var "z"))))) :: nil) ::
         c_eval (letb (d_mod "C" (app (var "Church") nat))
                   (app (app (proj (var "C") "two") Cst.zero) (fn "x" nat (Cst.succ (var "x")))))
           (Some nat) :: nil)).

Definition Church_t : exp := a_glob (p_abs ("ModuleParam" :: nil) ("Church" :: "t" :: nil)).
Definition Church_two : exp := a_glob (p_abs ("ModuleParam" :: nil) ("Church" :: "two" :: nil)).

(** Inside [Church], [t] is [Church.t A]; outside, [C.two] is [Church.two ℕ]. *)
Example church_spec :
  elab_spec church
    (nil, ⋅,
     cc_mod "Church" (⋅ ▹ Type@0)
       (cc_def "t" true false Type@0 (Π #0 (Π (Π #1 #2) #2)) ::
        cc_def "two" true false (Church_t $ #0) (λ #0 (λ (Π #1 #2) (#0 $ (#0 $ #1)))) :: nil) ::
     cc_eval (Church_two $ ℕ $ zero $ λ ℕ (succ #0)) (Some ℕ) :: nil).
Proof. elab_ok. Qed.

(** ** [examples/import_use.mctt]: privacy, [import … as], [import … use] *)
Definition import_use : Cst.prog :=
  (nil, ("ImportUse" :: nil, nil,
         c_mod ("Impl" :: nil) nil
           (c_def md_priv "secret" nat (Cst.succ (Cst.succ (Cst.succ Cst.zero))) ::
            c_def md_pub "exposed" nat (Cst.succ (var "secret")) :: nil) ::
         c_import nil ("Impl" :: nil) (i_as "I") ::
         c_import nil ("Impl" :: nil) (i_use ("exposed" :: nil)) ::
         c_eval (app (proj (var "I") "exposed") (var "exposed")) None :: nil)).

Definition Impl_ : string -> exp := fun x => a_glob (p_abs ("ImportUse" :: nil) ("Impl" :: x :: nil)).

(** A private member is visible in its own frame, and imports of this unit
    emit nothing. *)
Example import_use_spec :
  elab_spec import_use
    (nil, ⋅,
     cc_mod "Impl" ⋅
       (cc_def "secret" true true ℕ (succ (succ (succ zero))) ::
        cc_def "exposed" true false ℕ (succ (Impl_ "secret")) :: nil) ::
     cc_eval ((Impl_ "exposed") $ (Impl_ "exposed")) None :: nil).
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

(** Paths into other units are opaque and not pre-applied. *)
Example main_spec :
  elab_spec main_mctt
    (cc_import ("Lib" :: "Arith" :: nil) nil ::
     cc_import ("Lib" :: "Num" :: nil) nil ::
     cc_import ("Lib" :: "Num" :: nil) ("Ops" :: nil) :: nil,
     ⋅,
     cc_eval (a_glob (p_abs ("Lib" :: "Arith" :: nil) ("quadruple" :: nil)) $ succ (succ zero)) (Some ℕ) ::
     cc_eval (a_glob (p_abs ("Lib" :: "Num" :: nil) ("double" :: nil)) $ succ (succ (succ zero))) None ::
     cc_eval (a_glob (p_abs ("Lib" :: "Num" :: nil) ("Ops" :: "pred" :: nil)) $
                (a_glob (p_abs ("Lib" :: "Num" :: nil) ("double" :: nil)) $
                   succ (succ (succ (succ (succ zero)))))) (Some ℕ) :: nil).
Proof. elab_ok. Qed.

(** ** Scoping Rules, Positive and Negative *)

Definition unit_of (cs : list Cst.cmd) : Cst.prog := (nil, ("T" :: nil, nil, cs)).

(** A private member is not reachable through a sibling … *)
Example private_sibling : forall u, ~ elab_spec (unit_of
  (c_mod ("I" :: nil) nil (c_def md_priv "s" nat Cst.zero :: nil) ::
   c_eval (proj (var "I") "s") None :: nil)) u.
Proof. elab_fails. Qed.

(** … nor by [use] … *)
Example private_use : forall u, ~ elab_spec (unit_of
  (c_mod ("I" :: nil) nil (c_def md_priv "s" nat Cst.zero :: nil) ::
   c_import nil ("I" :: nil) (i_use ("s" :: nil)) :: nil)) u.
Proof. elab_fails. Qed.

(** … but it is from a frame nested in its own. *)
Example private_nested : exists u, elab_spec (unit_of
  (c_def md_priv "s" nat Cst.zero ::
   c_mod ("I" :: nil) nil (c_eval (var "s") None :: nil) :: nil)) u.
Proof. eexists; elab_ok. Qed.

(** Redeclaring in the same frame is an error … *)
Example redeclare_same : forall u, ~ elab_spec (unit_of
  (c_def md_pub "x" nat Cst.zero :: c_def md_pub "x" nat Cst.zero :: nil)) u.
Proof. elab_fails. Qed.

(** … also over an alias … *)
Example redeclare_alias : forall u, ~ elab_spec (unit_of
  (c_mod ("I" :: nil) nil nil :: c_import nil ("I" :: nil) (i_as "x") ::
   c_def md_pub "x" nat Cst.zero :: nil)) u.
Proof. elab_fails. Qed.

(** … but shadowing an enclosing frame's member is allowed, and the inner
    one wins inside. *)
Example shadow_parent :
  elab_spec (unit_of
    (c_def md_pub "x" nat Cst.zero ::
     c_mod ("I" :: nil) nil (c_def md_pub "x" nat (Cst.succ Cst.zero) :: c_eval (var "x") None :: nil) :: nil))
    (nil, ⋅,
     cc_def "x" true false ℕ zero ::
     cc_mod "I" ⋅ (cc_def "x" true false ℕ (succ zero) ::
                   cc_eval (a_glob (p_abs ("T" :: nil) ("I" :: "x" :: nil))) None :: nil) :: nil).
Proof. elab_ok. Qed.

(** A definition does not see itself. *)
Example no_self : forall u, ~ elab_spec (unit_of (c_def md_pub "x" nat (var "x") :: nil)) u.
Proof. elab_fails. Qed.

(** A member of a closed parameterized module needs its arguments. *)
Example missing_args : forall u, ~ elab_spec (unit_of
  (c_mod ("M" :: nil) (("A", typ 0) :: nil) (c_def md_pub "f" (typ 0) (var "A") :: nil) ::
   c_eval (proj (var "M") "f") None :: nil)) u.
Proof. elab_fails. Qed.

(** [module A.B] is [A] without parameters holding [B]; its members are named
    by the dotted chain and pre-applied to nothing but [B]'s parameters. *)
Example dotted_module :
  elab_spec (unit_of
    (c_mod ("A" :: "B" :: nil) (("X", typ 0) :: nil) (c_def md_abs "y" (typ 0) (var "X") :: nil) ::
     c_eval (app (proj (proj (var "A") "B") "y") nat) None :: nil))
    (nil, ⋅,
     cc_mod "A" ⋅ (cc_mod "B" (⋅ ▹ Type@0) (cc_def "y" false false Type@0 #0 :: nil) :: nil) ::
     cc_eval (a_glob (p_abs ("T" :: nil) ("A" :: "B" :: "y" :: nil)) $ ℕ) None :: nil).
Proof. elab_ok. Qed.

(** A unit is named by its full path only once imported. *)
Example unit_not_imported : forall u, ~ elab_spec (unit_of
  (c_eval (proj (glob ("L" :: "M" :: nil)) "f") None :: nil)) u.
Proof. elab_fails. Qed.
