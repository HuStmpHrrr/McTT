From Stdlib Require Import List PeanoNat String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives Group.
From Mctt.Core.Semantic Require Import Domain Evaluation.
#[local] Open Scope list_scope.

(** * The Values the Extracted Code Computes

    A copy of Core's values ([Core.Semantic.Domain]) in which a constructor,
    a type former and a stuck eliminator carry the declaration of their
    group of inductive types, as an [option ind_decl] next to the group's
    name: the evaluator and readback read it there instead of looking the
    declaration up.  [None] says that the value was made where the
    declaration was not at hand; a consumer then looks it up, as for a
    Core value.

    The relations of [Extraction.FastEval] stay over Core's values: a fast
    value stands for its erasure ([fdomain_erase]), which drops the
    declarations, and every declaration it carries is the one its group's
    name finds ([fdomain_ok]).  The erasures are for types and proofs only;
    the extracted code never runs them. *)

(** ** The Values *)

Inductive fdomain : Set :=
(** [fd_pi κd κc a ρ B]: a [Π] out of a domain [a] of the kind [κd] into a
    codomain of the kind [κc], its codomain [B] a closure in [ρ] *)
| fd_pi : abs_kind -> abs_kind -> fdomain -> list fdentry -> exp -> fdomain
(** A large universe *)
| fd_univ : nat -> fdomain
(** A small universe at a level value *)
| fd_suniv : fdomain -> fdomain
(** The type [Level@n] *)
| fd_level : nat -> fdomain
(** The sort of the types of levels, [LevelSort] *)
| fd_level_sort : fdomain
(** A flat level: its constant and its atoms, each with its offset and its
    sort *)
| fd_lvl : o2 -> list (nat * nat * fdomain_ne) -> fdomain
(** [Prop] *)
| fd_prop : fdomain
(** [⊤] *)
| fd_True : fdomain
(** [fd_proof M ρ]: a proof kept as the proof term [M] as written, with
    the environment [ρ] of its free variables, as [d_proof] *)
| fd_proof : exp -> list fdentry -> fdomain
(** [⊥] *)
| fd_False : fdomain
(** [fd_and p ρ Q]: a [Σₚ] with first component [p], its second [Q] a
    closure in [ρ] *)
| fd_and : fdomain -> list fdentry -> exp -> fdomain
(** [fd_fn a ρ M]: a function with domain [a], its body a closure in [ρ] *)
| fd_fn : fdomain -> list fdentry -> exp -> fdomain
(** [fd_neut a m]: a neutral [m] at the type [a] *)
| fd_neut : fdomain -> fdomain_ne -> fdomain
(** A term member of a module still lacking arguments *)
| fd_member : fdmod -> list string -> fdomain
(** [fd_ind p oD k as]: the type former of the member [k] of the group at
    [p], applied to [as].  [oD] is the group's declaration, [Some D] with
    [ind_lookup Θ Ξ p = Some D] when the value was made from an entry that
    holds it (the type former selected from a module); [None] when it was
    made from the term [a_ind p k], whose evaluation looks nothing up. *)
| fd_ind : qname -> option ind_decl -> nat -> list fdomain -> fdomain
(** [fd_con p oD k c vs]: the constructor [c] of the member [k] of the
    group at [p], applied to [vs].  [oD] is the group's declaration,
    [Some D] with [ind_lookup Θ Ξ p = Some D] when the constructor was
    evaluated from its term or applied to one more argument; [None] when a
    constructor of a view became the container's constructor, whose
    declaration evaluation did not look up. *)
| fd_con : qname -> option ind_decl -> nat -> string -> list fdomain -> fdomain
(** [fd_ihfn ρ Bks p ups t i f]: the [i]-th recursive result of an argument
    [f] of a function shape, as [d_ihfn] *)
| fd_ihfn : list fdentry -> list eblock -> qname -> list fdomain -> ptyp -> nat -> fdomain -> fdomain
(** [fd_shfam p ups ρ B t]: the codomain of the type of an argument of a
    function shape [pt_pi B t], as [d_shfam] *)
| fd_shfam : qname -> list fdomain -> list fdentry -> exp -> ptyp -> fdomain
(** [fd_ihfam ρm As p ups ρ B t i f]: the codomain of the type of a
    recursive result of an argument of a function shape [pt_pi B t], as
    [d_ihfam] *)
| fd_ihfam : list fdentry -> list exp -> qname -> list fdomain -> list fdentry -> exp -> ptyp -> nat -> fdomain -> fdomain
(** [fd_record p ns]: the type former of the record at [p] applied to [ns] *)
| fd_record : qname -> list fdomain -> fdomain
(** A record value: its fields' values, by name *)
| fd_tuple : list (string * fdomain) -> fdomain
with fdomain_ne : Set :=
(** A variable, by de Bruijn level *)
| fd_var : nat -> fdomain_ne
(** A neutral applied to a normal argument *)
| fd_app : fdomain_ne -> fdomain_nf -> fdomain_ne
(** [fd_absurd c p]: ex falso at the type [c], from the proof [p] of [⊥] *)
| fd_absurd : fdomain -> fdomain -> fdomain_ne
(** An opaque definition or an axiom *)
| fd_glob : qname -> fdomain_ne
(** [fd_elim ρ Bks p D ups m as m']: the eliminator of the group at [p],
    as [d_elim].  [D] is the declaration of the group at [p]
    ([ind_lookup Θ Ξ p = Some D]), which the evaluator has whenever an
    eliminator gets stuck. *)
| fd_elim : list fdentry -> list eblock -> qname -> ind_decl -> list fdomain -> nat -> list fdomain -> fdomain_ne -> fdomain_ne
(** The field [f] of a neutral of a record type *)
| fd_proj : string -> fdomain_ne -> fdomain_ne
with fdomain_nf : Set :=
(** [fd_dom a m]: the value [m] at the type [a], to be read back *)
| fd_dom : fdomain -> fdomain -> fdomain_nf
with fdmod : Set :=
(** A global module and the arguments it has *)
| fdm_global : qname -> list fdomain -> fdmod
(** The closure of a unit's definition, with the parameters it still lacks *)
| fdm_local : list centry -> moddef -> list fdentry -> fdmod
(** A submodule of a local module still lacking arguments *)
| fdm_member : fdmod -> list string -> fdmod
with fdentry : Set :=
(** A term variable's value and its type *)
| fde_term : fdomain -> fentry_type -> fdentry
(** A module slot's value, and the unit declared for the entry *)
| fde_mod : fdmod -> gunit -> fdentry
(** A definition with a module part: its term part's value and type, its
    module part's value, and the unit declared for the entry *)
| fde_dm : fdomain -> fentry_type -> fdmod -> gunit -> fdentry
(** The type of a term variable in an environment, as [entry_type] *)
with fentry_type : Set :=
(** A type value *)
| fentry_type_value : fdomain -> fentry_type
(** [fentry_type_closure A ρ]: the type [A] in [ρ], not yet evaluated *)
| fentry_type_closure : exp -> list fdentry -> fentry_type
(** [fentry_type_shape p ups ρ t]: the type of a recursive argument of
    shape [t] in [ρ], at the uniform parameters [ups] of the group at
    [p] *)
| fentry_type_shape : qname -> list fdomain -> list fdentry -> ptyp -> fentry_type
(** [fentry_type_induction_hypothesis ρm As p ups ρ t v i]: the type of
    the [i]-th recursive result of an argument [v] of shape [t] *)
| fentry_type_induction_hypothesis : list fdentry -> list exp -> qname -> list fdomain -> list fdentry -> ptyp -> fdomain -> nat -> fentry_type
(** No type *)
| fentry_type_none : fentry_type.

(** A fast environment *)
Abbreviation fenv := (list fdentry).

(** The declaration a value carries, once looked up: [Some D].  It is a
    definition of its own so that the implementations' obligations keep
    the equation of the lookup that found [D]. *)
Definition carry (D : ind_decl) : option ind_decl := Some D.

(** ** Environments, as [Core.Semantic.Domain]'s *)

(** The entry past the end of an environment, [absent_entry]'s twin *)
Definition fabsent_entry : fdentry := fde_term fd_prop fentry_type_none.

(** The entry of [#x], or [fabsent_entry] past the end *)
Fixpoint fenv_entry (ρ : fenv) (x : nat) : fdentry :=
  match x with
  | 0 => List.hd fabsent_entry ρ
  | S x' => fenv_entry (List.tl ρ) x'
  end.

(** The empty global module, the module value of a term entry *)
Definition fdm_empty : fdmod := fdm_global (q_abs nil nil) nil.

(** The value of [#x] as a term *)
Definition fenv_var (ρ : fenv) (x : nat) : fdomain :=
  match fenv_entry ρ x with
  | fde_term d _ => d
  | fde_mod _ _ => fd_prop
  | fde_dm d _ _ _ => d
  end.

(** The type the entry of [#x] is stored at *)
Definition fenv_type (ρ : fenv) (x : nat) : fentry_type :=
  match fenv_entry ρ x with
  | fde_term _ t => t
  | fde_mod _ _ => fentry_type_none
  | fde_dm _ t _ _ => t
  end.

(** The value of [#x] as a module *)
Definition fenv_mod (ρ : fenv) (x : nat) : fdmod :=
  match fenv_entry ρ x with
  | fde_mod m _ => m
  | fde_term _ _ => fdm_empty
  | fde_dm _ _ m _ => m
  end.

(** One more term entry, of the type [t] *)
Definition fextend_env (ρ : fenv) (d : fdomain) (t : fentry_type) : fenv := fde_term d t :: ρ.
(** One more module entry, of the declared unit [U] *)
Definition fextend_env_mod (ρ : fenv) (m : fdmod) (U : gunit) : fenv := fde_mod m U :: ρ.
(** One more entry of a definition with a module part *)
Definition fextend_env_dm (ρ : fenv) (d : fdomain) (t : fentry_type) (m : fdmod) (U : gunit) : fenv := fde_dm d t m U :: ρ.

(** The environment extended by values, each at its type, outermost first,
    [env_extend_typed]'s twin *)
Definition fenv_extend_typed (ρ : fenv) (vts : list (fdomain * fentry_type)) : fenv :=
  List.fold_left (fun ρ vt => fextend_env ρ (fst vt) (snd vt)) vts ρ.

Lemma fenv_extend_typed_app : forall ρ vs ws, fenv_extend_typed ρ (vs ++ ws) = fenv_extend_typed (fenv_extend_typed ρ vs) ws.
Proof. intros; unfold fenv_extend_typed; rewrite List.fold_left_app; reflexivity. Qed.

(** The type the head of a telescope gives a variable over [ρ], as
    [tele_head_type] *)
Definition ftele_head_type (ρ : fenv) (T : list centry) : fentry_type :=
  match T with
  | e :: _ => match centry_type e with Some A => fentry_type_closure A ρ | None => fentry_type_none end
  | nil => fentry_type_none
  end.

(** The values [vs] at the telescope [T] with their types, as
    [tele_entries] *)
Fixpoint ftele_entries (ρ : fenv) (T : list centry) (vs : list fdomain) : list (fdomain * fentry_type) :=
  match vs with
  | nil => nil
  | v :: vs' => (v, ftele_head_type ρ T) :: ftele_entries (fextend_env ρ v (ftele_head_type ρ T)) (List.tl T) vs'
  end.

(** The environment extended by values at a telescope, as [env_tele] *)
Definition fenv_tele (ρ : fenv) (T : list centry) (vs : list fdomain) : fenv := fenv_extend_typed ρ (ftele_entries ρ T vs).

(** ** The Types of the Variables an Eliminator Binds, as
    [Core.Semantic.Evaluation]'s *)

(** [decl_env]'s twin *)
Definition fdecl_env (D : ind_decl) (ups : list fdomain) : fenv := fenv_tele nil (List.rev (ind_uparams D)) ups.

(** [cargs_entries]'s twin *)
Fixpoint fcargs_entries (p : qname) (ups : list fdomain) (ρ : fenv) (gs : list carg) (vs : list fdomain) : list (fdomain * fentry_type) :=
  match vs with
  | nil => nil
  | v :: vs' =>
      match gs with
      | ca_arg _ A :: gs' => (v, fentry_type_closure A ρ) :: fcargs_entries p ups (fextend_env ρ v (fentry_type_closure A ρ)) gs' vs'
      | ca_rec t :: gs' => (v, fentry_type_shape p ups ρ t) :: fcargs_entries p ups ρ gs' vs'
      | nil => (v, fentry_type_none) :: fcargs_entries p ups ρ nil vs'
      end
  end.

(** [ihs_types]'s twin *)
Fixpoint fihs_types (D : ind_decl) (p : qname) (ups : list fdomain) (ρm : fenv) (As : list exp)
    (ρ : fenv) (gs : list carg) (vs : list fdomain) : list fentry_type :=
  match gs, vs with
  | ca_arg _ A :: gs', v :: vs' => fihs_types D p ups ρm As (fextend_env ρ v (fentry_type_closure A ρ)) gs' vs'
  | ca_rec t :: gs', v :: vs' =>
      List.map (fun i => fentry_type_induction_hypothesis ρm As p ups ρ t v i) (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t)))
        ++ fihs_types D p ups ρm As ρ gs' vs'
  | _, _ => nil
  end.

(** [pair_values_with_types]'s twin *)
Fixpoint fpair_values_with_types (vs : list fdomain) (ts : list fentry_type) : list (fdomain * fentry_type) :=
  match vs with
  | nil => nil
  | v :: vs' => (v, List.hd fentry_type_none ts) :: fpair_values_with_types vs' (List.tl ts)
  end.

(** [branch_entries]'s twin *)
Definition fbranch_entries (D : ind_decl) (Mj : imember) (p : qname) (ups : list fdomain) (As : list exp) (ρm : fenv)
    (gs : list carg) (ns vs ihs : list fdomain) : list (fdomain * fentry_type) :=
  let nts := ftele_entries (fdecl_env D ups) (List.rev (im_nparams Mj)) ns in
  let ρa := fenv_extend_typed (fdecl_env D ups) nts in
  nts ++ fcargs_entries p ups ρa gs vs ++ fpair_values_with_types ihs (fihs_types D p ups ρm As ρa gs vs).

(** [motive_entries]'s twin *)
Definition fmotive_entries (D : ind_decl) (Mk : imember) (ups ns : list fdomain) (a m : fdomain) : list (fdomain * fentry_type) :=
  ftele_entries (fdecl_env D ups) (List.rev (im_nparams Mk)) ns ++ (m, fentry_type_value a) :: nil.

(** [global_proof_env]'s twin *)
Definition fglobal_proof_env (p : qname) (T : list centry) (args : list fdomain) : fenv :=
  fextend_env_mod (fenv_tele nil (List.rev T) args) (fdm_global p args)
    (gu_mk nil (md_alias (me_apps (qname_mod p) (vars_from 0 (List.length args))))).

(** ** Levels, as [Core.Semantic.Domain]'s *)

(** The sort of a neutral level, read off its type *)
Definition fdomain_level_sort (a : fdomain) : nat :=
  match a with fd_level n => n | _ => 0 end.

(** The flat view of a level value *)
Definition fdomain_level_view (d : fdomain) : (o2 * list (nat * nat * fdomain_ne))%type :=
  match d with
  | fd_lvl c xs => (c, xs)
  | fd_neut a m => (ordinal_zero, (0, fdomain_level_sort a, m) :: nil)
  | _ => (ordinal_zero, nil)
  end.

(** The successor of a level: one more on the constant and every offset *)
Definition fdomain_level_suc (d : fdomain) : fdomain :=
  fd_lvl (ordinal_succ (fst (fdomain_level_view d))) (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) (snd (fdomain_level_view d))).

(** The join of two levels: the join of the constants, the atoms of both *)
Definition fdomain_level_max (d e : fdomain) : fdomain :=
  fd_lvl (ordinal_max (fst (fdomain_level_view d)) (fst (fdomain_level_view e))) (snd (fdomain_level_view d) ++ snd (fdomain_level_view e)).

(** A literal level *)
Definition fdomain_level_lit (o : o2) : fdomain := fd_lvl o nil.

(** ** The Kind of a Type Value, as [domain_kind] *)

Definition fdomain_kind (a : fdomain) : abs_kind :=
  match a with
  | fd_pi _ κc _ _ _ => κc
  | fd_True | fd_False | fd_and _ _ _ | fd_neut fd_prop _ => ak_propositional
  | fd_level _ | fd_neut fd_level_sort _ => ak_level
  | _ => ak_relevant
  end.

(** ** The Erasure

    The Core value a fast value stands for: the same value without the
    declarations.  For types and proofs only. *)

Fixpoint fdomain_erase (d : fdomain) : domain :=
  match d with
  | fd_pi κd κc a ρ B => d_pi κd κc (fdomain_erase a) (List.map fdentry_erase ρ) B
  | fd_univ i => d_univ i
  | fd_suniv l => d_suniv (fdomain_erase l)
  | fd_level n => d_level n
  | fd_level_sort => d_level_sort
  | fd_lvl c xs => d_lvl c (List.map (fun ka => (fst ka, fdomain_ne_erase (snd ka))) xs)
  | fd_prop => d_prop
  | fd_True => d_True
  | fd_proof M ρ => d_proof M (List.map fdentry_erase ρ)
  | fd_False => d_False
  | fd_and p ρ Q => d_and (fdomain_erase p) (List.map fdentry_erase ρ) Q
  | fd_fn a ρ M => d_fn (fdomain_erase a) (List.map fdentry_erase ρ) M
  | fd_neut a m => d_neut (fdomain_erase a) (fdomain_ne_erase m)
  | fd_member h ch => d_member (fdmod_erase h) ch
  | fd_ind p _ k vs => d_ind p k (List.map fdomain_erase vs)
  | fd_con p _ k c vs => d_con p k c (List.map fdomain_erase vs)
  | fd_ihfn ρ Bks p ups t i f => d_ihfn (List.map fdentry_erase ρ) Bks p (List.map fdomain_erase ups) t i (fdomain_erase f)
  | fd_shfam p ups ρ B t => d_shfam p (List.map fdomain_erase ups) (List.map fdentry_erase ρ) B t
  | fd_ihfam ρm As p ups ρ B t i f =>
      d_ihfam (List.map fdentry_erase ρm) As p (List.map fdomain_erase ups) (List.map fdentry_erase ρ) B t i (fdomain_erase f)
  | fd_record p ns => d_record p (List.map fdomain_erase ns)
  | fd_tuple vs => d_tuple (List.map (fun f => (fst f, fdomain_erase (snd f))) vs)
  end
with fdomain_ne_erase (m : fdomain_ne) : domain_ne :=
  match m with
  | fd_var x => d_var x
  | fd_app m n => d_app (fdomain_ne_erase m) (fdomain_nf_erase n)
  | fd_absurd c p => d_absurd (fdomain_erase c) (fdomain_erase p)
  | fd_glob p => d_glob p
  | fd_elim ρ Bks p _ ups j as' m =>
      d_elim (List.map fdentry_erase ρ) Bks p (List.map fdomain_erase ups) j (List.map fdomain_erase as') (fdomain_ne_erase m)
  | fd_proj f m => d_proj f (fdomain_ne_erase m)
  end
with fdomain_nf_erase (n : fdomain_nf) : domain_nf :=
  match n with
  | fd_dom a m => d_dom (fdomain_erase a) (fdomain_erase m)
  end
with fdmod_erase (h : fdmod) : dmod :=
  match h with
  | fdm_global p args => dm_global p (List.map fdomain_erase args)
  | fdm_local Δ D ρ => dm_local Δ D (List.map fdentry_erase ρ)
  | fdm_member h ch => dm_member (fdmod_erase h) ch
  end
with fdentry_erase (e : fdentry) : dentry :=
  match e with
  | fde_term d t => de_term (fdomain_erase d) (fentry_type_erase t)
  | fde_mod h U => de_mod (fdmod_erase h) U
  | fde_dm d t h U => de_dm (fdomain_erase d) (fentry_type_erase t) (fdmod_erase h) U
  end
with fentry_type_erase (t : fentry_type) : entry_type :=
  match t with
  | fentry_type_value a => entry_type_value (fdomain_erase a)
  | fentry_type_closure A ρ => entry_type_closure A (List.map fdentry_erase ρ)
  | fentry_type_shape p ups ρ s => entry_type_shape p (List.map fdomain_erase ups) (List.map fdentry_erase ρ) s
  | fentry_type_induction_hypothesis ρm As p ups ρ s v i =>
      entry_type_induction_hypothesis (List.map fdentry_erase ρm) As p (List.map fdomain_erase ups)
        (List.map fdentry_erase ρ) s (fdomain_erase v) i
  | fentry_type_none => entry_type_none
  end.

(** The Core environment a fast one stands for *)
Abbreviation fenv_erase ρ := (List.map fdentry_erase ρ).

(** The values of a list *)
Abbreviation fdomains_erase vs := (List.map fdomain_erase vs).

(** The member a member stands for, on fast values: Core's
    [(group, member, arguments)] of [fast_eval_mref], with the group's
    declaration when it is at hand *)
Record fast_member_reference : Type := mk_fast_member_reference
  { (** The name of the group of the member stood for *)
    fmr_group : qname
  ; (** The group's declaration, when the member is the group's own;
        [None] at a view, whose group is looked up where it is read *)
    fmr_declaration : option ind_decl
  ; (** The index of the member in its group *)
    fmr_member : nat
  ; (** The group's parameters *)
    fmr_arguments : list fdomain }.

(** The Core triple a fast member reference stands for *)
Definition fast_member_reference_erase (r : fast_member_reference) : (qname * nat * list domain)%type :=
  match r with mk_fast_member_reference q _ k vs => (q, k, fdomains_erase vs) end.

(** ** The Erasure Commutes with the Operations *)

Lemma fenv_entry_erase : forall ρ x, env_entry (fenv_erase ρ) x = fdentry_erase (fenv_entry ρ x).
Proof.
  intros ρ x; revert ρ; induction x as [| x IH]; intros [| e ρ]; cbn; try reflexivity.
  - apply (IH nil).
  - apply IH.
Qed.

Lemma fenv_var_erase : forall ρ x, env_var (fenv_erase ρ) x = fdomain_erase (fenv_var ρ x).
Proof. intros; unfold env_var, fenv_var; rewrite fenv_entry_erase; destruct (fenv_entry ρ x); reflexivity. Qed.

Lemma fenv_type_erase : forall ρ x, env_type (fenv_erase ρ) x = fentry_type_erase (fenv_type ρ x).
Proof. intros; unfold env_type, fenv_type; rewrite fenv_entry_erase; destruct (fenv_entry ρ x); reflexivity. Qed.

Lemma fenv_mod_erase : forall ρ x, env_mod (fenv_erase ρ) x = fdmod_erase (fenv_mod ρ x).
Proof. intros; unfold env_mod, fenv_mod; rewrite fenv_entry_erase; destruct (fenv_entry ρ x); reflexivity. Qed.

Lemma fextend_env_erase : forall ρ d t,
    fenv_erase (fextend_env ρ d t) = extend_env (fenv_erase ρ) (fdomain_erase d) (fentry_type_erase t).
Proof. reflexivity. Qed.

Lemma fextend_env_mod_erase : forall ρ h U, fenv_erase (fextend_env_mod ρ h U) = extend_env_mod (fenv_erase ρ) (fdmod_erase h) U.
Proof. reflexivity. Qed.

Lemma fextend_env_dm_erase : forall ρ d t h U,
    fenv_erase (fextend_env_dm ρ d t h U) = extend_env_dm (fenv_erase ρ) (fdomain_erase d) (fentry_type_erase t) (fdmod_erase h) U.
Proof. reflexivity. Qed.

(** Typed values, erased *)
Abbreviation fvalue_types_erase vts := (List.map (fun vt => (fdomain_erase (fst vt), fentry_type_erase (snd vt))) vts).

Lemma fenv_extend_typed_erase : forall vts ρ,
    fenv_erase (fenv_extend_typed ρ vts) = env_extend_typed (fenv_erase ρ) (fvalue_types_erase vts).
Proof. induction vts as [| vt vts IH]; intros ρ; [ reflexivity | apply IH ]. Qed.

Lemma ftele_head_type_erase : forall ρ T, fentry_type_erase (ftele_head_type ρ T) = tele_head_type (fenv_erase ρ) T.
Proof. intros ρ [| e T]; [ reflexivity |]; cbn; destruct (centry_type e); reflexivity. Qed.

Lemma ftele_entries_erase : forall vs ρ T,
    fvalue_types_erase (ftele_entries ρ T vs) = tele_entries (fenv_erase ρ) T (fdomains_erase vs).
Proof.
  induction vs as [| v vs IH]; intros ρ T; [ reflexivity |]; cbn [ftele_entries tele_entries List.map fst snd].
  rewrite ftele_head_type_erase; f_equal; rewrite IH; cbn; rewrite ftele_head_type_erase; reflexivity.
Qed.

Lemma fenv_tele_erase : forall ρ T vs, fenv_erase (fenv_tele ρ T vs) = env_tele (fenv_erase ρ) T (fdomains_erase vs).
Proof. intros; unfold fenv_tele, env_tele; rewrite fenv_extend_typed_erase, ftele_entries_erase; reflexivity. Qed.

Lemma fdecl_env_erase : forall D ups, fenv_erase (fdecl_env D ups) = decl_env D (fdomains_erase ups).
Proof. intros; unfold fdecl_env, decl_env; apply fenv_tele_erase. Qed.

Lemma fcargs_entries_erase : forall p ups vs ρ gs,
    fvalue_types_erase (fcargs_entries p ups ρ gs vs) = cargs_entries p (fdomains_erase ups) (fenv_erase ρ) gs (fdomains_erase vs).
Proof.
  intros p ups vs; induction vs as [| v vs IH]; intros ρ [| [r A | t] gs]; cbn [fcargs_entries cargs_entries List.map fst snd];
    [ reflexivity .. | | | ]; f_equal; rewrite IH; reflexivity.
Qed.

Lemma fihs_types_erase : forall D p ups ρm As gs vs ρ,
    List.map fentry_type_erase (fihs_types D p ups ρm As ρ gs vs) =
    ihs_types D p (fdomains_erase ups) (fenv_erase ρm) As (fenv_erase ρ) gs (fdomains_erase vs).
Proof.
  intros D p ups ρm As gs; induction gs as [| [r A | t] gs IH]; intros [| v vs] ρ; cbn [fihs_types ihs_types List.map]; try reflexivity.
  - rewrite IH; reflexivity.
  - rewrite List.map_app, IH, List.map_map; reflexivity.
Qed.

Lemma fpair_values_with_types_erase : forall vs ts,
    fvalue_types_erase (fpair_values_with_types vs ts) = pair_values_with_types (fdomains_erase vs) (List.map fentry_type_erase ts).
Proof.
  induction vs as [| v vs IH]; intros ts; cbn [fpair_values_with_types pair_values_with_types List.map fst snd]; [ reflexivity |].
  rewrite IH; destruct ts; reflexivity.
Qed.

Lemma fbranch_entries_erase : forall D Mj p ups As ρm gs ns vs ihs,
    fvalue_types_erase (fbranch_entries D Mj p ups As ρm gs ns vs ihs) =
    branch_entries D Mj p (fdomains_erase ups) As (fenv_erase ρm) gs (fdomains_erase ns) (fdomains_erase vs) (fdomains_erase ihs).
Proof.
  intros; unfold fbranch_entries, branch_entries.
  rewrite !List.map_app, ftele_entries_erase, fcargs_entries_erase, fpair_values_with_types_erase, fihs_types_erase,
    fenv_extend_typed_erase, ftele_entries_erase, fdecl_env_erase; reflexivity.
Qed.

Lemma fmotive_entries_erase : forall D Mk ups ns a m,
    fvalue_types_erase (fmotive_entries D Mk ups ns a m) =
    motive_entries D Mk (fdomains_erase ups) (fdomains_erase ns) (fdomain_erase a) (fdomain_erase m).
Proof. intros; unfold fmotive_entries, motive_entries; rewrite List.map_app, ftele_entries_erase, fdecl_env_erase; reflexivity. Qed.

Lemma fglobal_proof_env_erase : forall p T args, fenv_erase (fglobal_proof_env p T args) = global_proof_env p T (fdomains_erase args).
Proof. intros; unfold fglobal_proof_env, global_proof_env; cbn; rewrite fenv_tele_erase, List.length_map; reflexivity. Qed.

Lemma fdomain_level_sort_erase : forall a, domain_level_sort (fdomain_erase a) = fdomain_level_sort a.
Proof. intros [] ; reflexivity. Qed.

Lemma fdomain_level_suc_erase : forall d, fdomain_erase (fdomain_level_suc d) = domain_level_suc (fdomain_erase d).
Proof.
  intros d; unfold fdomain_level_suc, domain_level_suc, domain_level_const, domain_level_atoms.
  destruct d; cbn; rewrite ?List.map_map; try reflexivity.
  rewrite fdomain_level_sort_erase; reflexivity.
Qed.

Lemma fdomain_level_max_erase : forall d e, fdomain_erase (fdomain_level_max d e) = domain_level_max (fdomain_erase d) (fdomain_erase e).
Proof.
  intros d e; unfold fdomain_level_max, domain_level_max, domain_level_const, domain_level_atoms; cbn [fdomain_erase].
  rewrite List.map_app; f_equal; [ destruct d, e; reflexivity |].
  f_equal; [ destruct d; cbn; rewrite ?fdomain_level_sort_erase; reflexivity
           | destruct e; cbn; rewrite ?fdomain_level_sort_erase; reflexivity ].
Qed.

Lemma fdomain_level_lit_erase : forall o, fdomain_erase (fdomain_level_lit o) = domain_level_lit o.
Proof. reflexivity. Qed.

Lemma fdomain_kind_erase : forall a, domain_kind (fdomain_erase a) = fdomain_kind a.
Proof. intros []; try reflexivity; match goal with a : fdomain |- _ => destruct a; reflexivity end. Qed.

(** The kind of a fast type, read as its erasure's *)
Lemma fdomain_kind_erase_eq : forall a κ, fdomain_kind a = κ -> domain_kind (fdomain_erase a) = κ.
Proof. intros * H; rewrite fdomain_kind_erase; exact H. Qed.

(** A record value's fields, erased *)
Lemma fields_erase_combine : forall (fl : list string) vs,
    List.map (fun f => (fst f, fdomain_erase (snd f))) (List.combine fl vs) = List.combine fl (fdomains_erase vs).
Proof. induction fl as [| f fl IH]; intros [| v vs]; cbn; f_equal; auto. Qed.

(** An element found, erased *)
Lemma nth_error_map_some : forall {A B} (f : A -> B) l n x,
    List.nth_error l n = Some x -> List.nth_error (List.map f l) n = Some (f x).
Proof. intros; rewrite List.nth_error_map; match goal with H : _ = _ |- _ => rewrite H end; reflexivity. Qed.

#[export]
Hint Resolve nth_error_map_some : mctt.

(** A field looked up, erased *)
Lemma field_lookup_erase : forall (vs : list (string * fdomain)) f,
    field_lookup (List.map (fun g => (fst g, fdomain_erase (snd g))) vs) f = option_map fdomain_erase (field_lookup vs f).
Proof. induction vs as [| [g v] vs IH]; intros f; cbn; [ reflexivity |]; destruct (String.eqb f g); auto. Qed.

Lemma field_lookup_erase_some : forall (vs : list (string * fdomain)) f v, field_lookup vs f = Some v ->
    field_lookup (List.map (fun g => (fst g, fdomain_erase (snd g))) vs) f = Some (fdomain_erase v).
Proof. intros * E; rewrite field_lookup_erase, E; reflexivity. Qed.

(** ** The Core Helpers on Values, Fast

    Each of [Core.Semantic.Evaluation]'s functions on values that the
    implementations call, on fast values, with the equation of its
    erasure. *)

(** [dm_clo]'s twin *)
Definition fdm_clo (U : gunit) (ρ : fenv) : fdmod :=
  match U with gu_mk Δ D => fdm_local Δ D ρ end.

Lemma fdm_clo_erase : forall U ρ, fdmod_erase (fdm_clo U ρ) = dm_clo U (fenv_erase ρ).
Proof. intros [Δ D] ρ; reflexivity. Qed.

(** [kinds_pads]'s twin *)
Definition fkinds_pads (n : nat) (ρ : fenv) : fenv := List.repeat fabsent_entry n ++ ρ.

Lemma fkinds_pads_erase : forall n ρ, fenv_erase (fkinds_pads n ρ) = kinds_pads n (fenv_erase ρ).
Proof. intros; unfold fkinds_pads, kinds_pads; rewrite List.map_app, List.map_repeat; reflexivity. Qed.

(** [kinds_body_entry]'s twin *)
Definition fkinds_body_entry (ρ : fenv) (y : string) (E : gentry) : fdentry :=
  match E with
  | ge_mod _ U => fde_mod (fdm_clo U ρ) U
  | ge_ind _ pq _ _ _ =>
      let U := gu_mk nil (md_alias (qname_mod (qname_sibling pq y))) in fde_mod (fdm_clo U ρ) U
  | ge_record _ p _ _ => let U := gu_mk nil (md_alias (qname_mod p)) in fde_mod (fdm_clo U ρ) U
  | ge_def_mod _ _ _ U => fde_dm fd_prop fentry_type_none (fdm_clo U ρ) U
  | _ => fabsent_entry
  end.

Lemma fkinds_body_entry_erase : forall ρ y E, fdentry_erase (fkinds_body_entry ρ y E) = kinds_body_entry (fenv_erase ρ) y E.
Proof. intros ρ y []; try reflexivity; match goal with U : gunit |- _ => destruct U; reflexivity end. Qed.

(** ** The Declarations Carried Are Right

    [fdomain_ok Θ Ξ v]: every declaration [v] carries, [Some D] next to the
    name [p], is the one [p] finds in [Θ ⍮ Ξ]; mutually, for neutrals,
    normal values, module values and environment entries. *)

(** The induction scheme of a predicate nested through [Forall] *)
Scheme All for Forall.

Section Ok.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** A carried declaration is right: absent, or the one [p] finds *)
  Definition decl_carried_ok (p : qname) (oD : option ind_decl) : Prop :=
    forall D, oD = Some D -> ind_lookup Θ Ξ p = Some D.

  Inductive fdomain_ok : fdomain -> Prop :=
  (** A [Π]: its domain and its closure's environment *)
  | fdomain_ok_pi : forall κd κc a ρ B, fdomain_ok a -> Forall fdentry_ok ρ -> fdomain_ok (fd_pi κd κc a ρ B)
  (** A large universe *)
  | fdomain_ok_univ : forall i, fdomain_ok (fd_univ i)
  (** A small universe: its level *)
  | fdomain_ok_suniv : forall l, fdomain_ok l -> fdomain_ok (fd_suniv l)
  (** The type of levels *)
  | fdomain_ok_level : forall n, fdomain_ok (fd_level n)
  (** The sort of the types of levels *)
  | fdomain_ok_level_sort : fdomain_ok fd_level_sort
  (** A flat level: its atoms *)
  | fdomain_ok_lvl : forall c xs, Forall (fun ka => fdomain_ne_ok (snd ka)) xs -> fdomain_ok (fd_lvl c xs)
  (** [Prop] *)
  | fdomain_ok_prop : fdomain_ok fd_prop
  (** [⊤] *)
  | fdomain_ok_True : fdomain_ok fd_True
  (** A kept proof: its environment *)
  | fdomain_ok_proof : forall M ρ, Forall fdentry_ok ρ -> fdomain_ok (fd_proof M ρ)
  (** [⊥] *)
  | fdomain_ok_False : fdomain_ok fd_False
  (** A conjunction: its first component and its closure's environment *)
  | fdomain_ok_and : forall p ρ Q, fdomain_ok p -> Forall fdentry_ok ρ -> fdomain_ok (fd_and p ρ Q)
  (** A function: its domain and its closure's environment *)
  | fdomain_ok_fn : forall a ρ M, fdomain_ok a -> Forall fdentry_ok ρ -> fdomain_ok (fd_fn a ρ M)
  (** A neutral: its type and itself *)
  | fdomain_ok_neut : forall a m, fdomain_ok a -> fdomain_ne_ok m -> fdomain_ok (fd_neut a m)
  (** A member of a module value: the module value *)
  | fdomain_ok_member : forall h ch, fdmod_ok h -> fdomain_ok (fd_member h ch)
  (** A type former: its declaration is right, and its arguments *)
  | fdomain_ok_indty : forall p oD k vs, decl_carried_ok p oD -> Forall fdomain_ok vs -> fdomain_ok (fd_ind p oD k vs)
  (** A constructor: its declaration is right, and its arguments *)
  | fdomain_ok_con : forall p oD k c vs, decl_carried_ok p oD -> Forall fdomain_ok vs -> fdomain_ok (fd_con p oD k c vs)
  (** A recursive result of a function shape: its environment, parameters and argument *)
  | fdomain_ok_ihfn : forall ρ Bks p ups t i f,
      Forall fdentry_ok ρ -> Forall fdomain_ok ups -> fdomain_ok f -> fdomain_ok (fd_ihfn ρ Bks p ups t i f)
  (** The family of a shape's argument type: its parameters and environment *)
  | fdomain_ok_shfam : forall p ups ρ B t, Forall fdomain_ok ups -> Forall fdentry_ok ρ -> fdomain_ok (fd_shfam p ups ρ B t)
  (** The family of a recursive result's type: its environments, parameters and argument *)
  | fdomain_ok_ihfam : forall ρm As p ups ρ B t i f,
      Forall fdentry_ok ρm -> Forall fdomain_ok ups -> Forall fdentry_ok ρ -> fdomain_ok f -> fdomain_ok (fd_ihfam ρm As p ups ρ B t i f)
  (** A record's type former: its arguments *)
  | fdomain_ok_record : forall p ns, Forall fdomain_ok ns -> fdomain_ok (fd_record p ns)
  (** A tuple: its fields *)
  | fdomain_ok_tuple : forall vs, Forall (fun f => fdomain_ok (snd f)) vs -> fdomain_ok (fd_tuple vs)
  with fdomain_ne_ok : fdomain_ne -> Prop :=
  (** A variable *)
  | fdomain_ne_ok_var : forall x, fdomain_ne_ok (fd_var x)
  (** An application: the neutral and the argument *)
  | fdomain_ne_ok_app : forall m n, fdomain_ne_ok m -> fdomain_nf_ok n -> fdomain_ne_ok (fd_app m n)
  (** Ex falso: its type and its proof *)
  | fdomain_ne_ok_absurd : forall c p, fdomain_ok c -> fdomain_ok p -> fdomain_ne_ok (fd_absurd c p)
  (** A global *)
  | fdomain_ne_ok_glob : forall p, fdomain_ne_ok (fd_glob p)
  (** A stuck eliminator: its declaration is right, and its environment,
      parameters, arguments and neutral *)
  | fdomain_ne_ok_elim : forall ρ Bks p D ups j as' m,
      ind_lookup Θ Ξ p = Some D -> Forall fdentry_ok ρ -> Forall fdomain_ok ups -> Forall fdomain_ok as' -> fdomain_ne_ok m ->
      fdomain_ne_ok (fd_elim ρ Bks p D ups j as' m)
  (** A field of a neutral: the neutral *)
  | fdomain_ne_ok_proj : forall f m, fdomain_ne_ok m -> fdomain_ne_ok (fd_proj f m)
  with fdomain_nf_ok : fdomain_nf -> Prop :=
  (** A value at a type: both *)
  | fdomain_nf_ok_dom : forall a m, fdomain_ok a -> fdomain_ok m -> fdomain_nf_ok (fd_dom a m)
  with fdmod_ok : fdmod -> Prop :=
  (** A global module: its arguments *)
  | fdmod_ok_global : forall p args, Forall fdomain_ok args -> fdmod_ok (fdm_global p args)
  (** A closure: its environment *)
  | fdmod_ok_local : forall Δ D ρ, Forall fdentry_ok ρ -> fdmod_ok (fdm_local Δ D ρ)
  (** A member closure: the module value *)
  | fdmod_ok_member : forall h ch, fdmod_ok h -> fdmod_ok (fdm_member h ch)
  with fdentry_ok : fdentry -> Prop :=
  (** A term entry: its value and its type *)
  | fdentry_ok_term : forall d t, fdomain_ok d -> fentry_type_ok t -> fdentry_ok (fde_term d t)
  (** A module entry *)
  | fdentry_ok_mod : forall h U, fdmod_ok h -> fdentry_ok (fde_mod h U)
  (** An entry of a definition with a module part: both parts and the type *)
  | fdentry_ok_dm : forall d t h U, fdomain_ok d -> fentry_type_ok t -> fdmod_ok h -> fdentry_ok (fde_dm d t h U)
  with fentry_type_ok : fentry_type -> Prop :=
  (** A type value *)
  | fentry_type_ok_value : forall a, fdomain_ok a -> fentry_type_ok (fentry_type_value a)
  (** A closure: its environment *)
  | fentry_type_ok_closure : forall A ρ, Forall fdentry_ok ρ -> fentry_type_ok (fentry_type_closure A ρ)
  (** A shape type: its parameters and environment *)
  | fentry_type_ok_shape : forall p ups ρ t, Forall fdomain_ok ups -> Forall fdentry_ok ρ -> fentry_type_ok (fentry_type_shape p ups ρ t)
  (** An induction hypothesis's type: its environments, parameters and argument *)
  | fentry_type_ok_induction_hypothesis : forall ρm As p ups ρ t v i,
      Forall fdentry_ok ρm -> Forall fdomain_ok ups -> Forall fdentry_ok ρ -> fdomain_ok v ->
      fentry_type_ok (fentry_type_induction_hypothesis ρm As p ups ρ t v i)
  (** No type *)
  | fentry_type_ok_none : fentry_type_ok fentry_type_none.

  (** Every entry of an environment *)
  Definition fenv_ok (ρ : fenv) : Prop := Forall fdentry_ok ρ.

  (** A member reference: its carried declaration is its group's, and its
      parameters are right *)
  Definition fast_member_reference_ok (r : fast_member_reference) : Prop :=
    decl_carried_ok (fmr_group r) (fmr_declaration r) /\ Forall fdomain_ok (fmr_arguments r).

  Lemma fenv_entry_ok : forall ρ x, fenv_ok ρ -> fdentry_ok (fenv_entry ρ x).
  Proof.
    intros ρ x; revert ρ; induction x as [| x IH]; intros [| e ρ] H; cbn.
    - repeat constructor.
    - inversion H; assumption.
    - apply (IH nil); constructor.
    - inversion H; apply IH; assumption.
  Qed.

  Lemma fenv_var_ok : forall ρ x, fenv_ok ρ -> fdomain_ok (fenv_var ρ x).
  Proof.
    intros ρ x H; unfold fenv_var; pose proof (fenv_entry_ok ρ x H) as He.
    destruct (fenv_entry ρ x); inversion He; subst; [ assumption | constructor | assumption ].
  Qed.

  Lemma fenv_type_ok : forall ρ x, fenv_ok ρ -> fentry_type_ok (fenv_type ρ x).
  Proof.
    intros ρ x H; unfold fenv_type; pose proof (fenv_entry_ok ρ x H) as He.
    destruct (fenv_entry ρ x); inversion He; subst; [ assumption | constructor | assumption ].
  Qed.

  Lemma fenv_mod_ok : forall ρ x, fenv_ok ρ -> fdmod_ok (fenv_mod ρ x).
  Proof.
    intros ρ x H; unfold fenv_mod; pose proof (fenv_entry_ok ρ x H) as He.
    destruct (fenv_entry ρ x); inversion He; subst; [ repeat constructor | assumption | assumption ].
  Qed.

  Lemma fextend_env_ok : forall ρ d t, fenv_ok ρ -> fdomain_ok d -> fentry_type_ok t -> fenv_ok (fextend_env ρ d t).
  Proof. intros; constructor; [ constructor |]; assumption. Qed.

  Lemma fextend_env_mod_ok : forall ρ h U, fenv_ok ρ -> fdmod_ok h -> fenv_ok (fextend_env_mod ρ h U).
  Proof. intros; constructor; [ constructor |]; assumption. Qed.

  Lemma fextend_env_dm_ok : forall ρ d t h U, fenv_ok ρ -> fdomain_ok d -> fentry_type_ok t -> fdmod_ok h ->
      fenv_ok (fextend_env_dm ρ d t h U).
  Proof. intros; constructor; [ constructor |]; assumption. Qed.

  Lemma fenv_extend_typed_ok : forall vts ρ, fenv_ok ρ ->
      Forall (fun vt => fdomain_ok (fst vt) /\ fentry_type_ok (snd vt)) vts -> fenv_ok (fenv_extend_typed ρ vts).
  Proof.
    induction vts as [| vt vts IH]; intros ρ Hρ Hv; [ exact Hρ |]; inversion Hv as [| ? ? [Hd Ht] Hr]; subst.
    apply IH; [ apply fextend_env_ok |]; assumption.
  Qed.

  Lemma ftele_head_type_ok : forall ρ T, fenv_ok ρ -> fentry_type_ok (ftele_head_type ρ T).
  Proof. intros ρ [| e T] H; cbn; [ constructor |]; destruct (centry_type e); constructor; exact H. Qed.

  Lemma ftele_entries_ok : forall vs ρ T, fenv_ok ρ -> Forall fdomain_ok vs ->
      Forall (fun vt => fdomain_ok (fst vt) /\ fentry_type_ok (snd vt)) (ftele_entries ρ T vs).
  Proof.
    induction vs as [| v vs IH]; intros ρ T Hρ Hv; cbn; constructor; inversion Hv; subst;
      [ split; [ assumption | apply ftele_head_type_ok; exact Hρ ] |].
    apply IH; [ apply fextend_env_ok; [ exact Hρ | assumption | apply ftele_head_type_ok; exact Hρ ] | assumption ].
  Qed.

  Lemma fenv_tele_ok : forall ρ T vs, fenv_ok ρ -> Forall fdomain_ok vs -> fenv_ok (fenv_tele ρ T vs).
  Proof. intros; apply fenv_extend_typed_ok; [| apply ftele_entries_ok ]; assumption. Qed.

  Lemma fdomain_level_view_ok : forall d, fdomain_ok d -> Forall (fun ka => fdomain_ne_ok (snd ka)) (snd (fdomain_level_view d)).
  Proof. intros d H; destruct d; cbn; inversion H; subst; auto. Qed.

  Lemma fdomain_level_suc_ok : forall d, fdomain_ok d -> fdomain_ok (fdomain_level_suc d).
  Proof.
    intros d H; unfold fdomain_level_suc; constructor; apply Forall_map.
    eapply Forall_impl; [| exact (fdomain_level_view_ok d H) ]; intros; assumption.
  Qed.

  Lemma fdomain_level_max_ok : forall d e, fdomain_ok d -> fdomain_ok e -> fdomain_ok (fdomain_level_max d e).
  Proof. intros; unfold fdomain_level_max; constructor; apply Forall_app; split; apply fdomain_level_view_ok; assumption. Qed.

  Lemma fdomain_level_lit_ok : forall o, fdomain_ok (fdomain_level_lit o).
  Proof. intros; constructor; constructor. Qed.

  Lemma fdm_clo_ok : forall U ρ, fenv_ok ρ -> fdmod_ok (fdm_clo U ρ).
  Proof. intros [Δ D] ρ H; constructor; exact H. Qed.

  Lemma fkinds_pads_ok : forall n ρ, fenv_ok ρ -> fenv_ok (fkinds_pads n ρ).
  Proof.
    intros n ρ H; unfold fenv_ok, fkinds_pads; apply Forall_app; split; [| exact H ].
    apply Forall_forall; intros e He; apply repeat_spec in He as ->; repeat constructor.
  Qed.

  Lemma fkinds_body_entry_ok : forall ρ y E, fenv_ok ρ -> fdentry_ok (fkinds_body_entry ρ y E).
  Proof. intros ρ y [] H; cbn; repeat constructor; try apply fdm_clo_ok; exact H. Qed.

  (** Elements of lists of right values *)
  Lemma Forall_nth_error_ok : forall {A} (P : A -> Prop) l n x, Forall P l -> List.nth_error l n = Some x -> P x.
  Proof. intros * H E; eapply Forall_forall; [ exact H | eapply nth_error_In; exact E ]. Qed.

  (** The element found first, so that a proof search fixes the list
      before it asks that it be right *)
  Lemma fdomains_nth_error_ok : forall vs n v, List.nth_error vs n = Some v -> Forall fdomain_ok vs -> fdomain_ok v.
  Proof. intros; eapply Forall_nth_error_ok; eassumption. Qed.

  Lemma field_lookup_ok : forall vs f v, field_lookup vs f = Some v -> Forall (fun g => fdomain_ok (snd g)) vs -> fdomain_ok v.
  Proof.
    induction vs as [| [g w] vs IH]; intros f v E H; cbn in E; [ discriminate |]; inversion H; subst.
    destruct (String.eqb f g); [ injection E as <-; assumption | eauto ].
  Qed.

  Lemma combine_ok : forall (fl : list string) vs, Forall fdomain_ok vs -> Forall (fun g => fdomain_ok (snd g)) (List.combine fl vs).
  Proof. induction fl as [| f fl IH]; intros [| v vs] H; cbn; constructor; inversion H; subst; auto. Qed.

  (** The declarations carried, read off a right value *)
  Lemma fdomain_ok_con_carried : forall p oD k c vs, fdomain_ok (fd_con p oD k c vs) -> decl_carried_ok p oD.
  Proof. intros * H; inversion H; assumption. Qed.

  Lemma fdomain_ok_ind_carried : forall p oD k vs, fdomain_ok (fd_ind p oD k vs) -> decl_carried_ok p oD.
  Proof. intros * H; inversion H; assumption. Qed.

  Lemma fdomain_ok_neut_ind_carried : forall p oD k vs m, fdomain_ok (fd_neut (fd_ind p oD k vs) m) -> decl_carried_ok p oD.
  Proof. intros * H; inversion H; subst; eapply fdomain_ok_ind_carried; eassumption. Qed.

  Lemma fdomain_nf_ok_dom_ind_carried : forall p oD j as' v,
      fdomain_nf_ok (fd_dom (fd_ind p oD j as') v) -> decl_carried_ok p oD.
  Proof. intros * H; inversion H; subst; eapply fdomain_ok_ind_carried; eassumption. Qed.

  Lemma fdomain_ne_ok_elim_decl : forall ρ Bks p D ups j as' m,
      fdomain_ne_ok (fd_elim ρ Bks p D ups j as' m) -> ind_lookup Θ Ξ p = Some D.
  Proof. intros * H; inversion H; assumption. Qed.

  Lemma decl_carried_some : forall p D, ind_lookup Θ Ξ p = Some D -> decl_carried_ok p (Some D).
  Proof. intros * E D' [= <-]; exact E. Qed.

  Lemma decl_carried_none : forall p, decl_carried_ok p None.
  Proof. intros p D E; discriminate E. Qed.

  Lemma decl_carried_lookup : forall p, decl_carried_ok p (ind_lookup Θ Ξ p).
  Proof. intros p D E; exact E. Qed.

  Lemma decl_carried_carry : forall p D, ind_lookup Θ Ξ p = Some D -> decl_carried_ok p (carry D).
  Proof. intros * E D' [= <-]; exact E. Qed.

  (** Lists of right values *)
  Lemma Forall_app_intro : forall {A} (P : A -> Prop) l1 l2, Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
  Proof. intros; apply Forall_app; split; assumption. Qed.

  Lemma Forall_repeat_intro : forall {A} (P : A -> Prop) x n, P x -> Forall P (List.repeat x n).
  Proof. intros; apply Forall_forall; intros y Hy; apply repeat_spec in Hy as ->; assumption. Qed.

  Lemma Forall_skipn_intro : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (List.skipn n l).
  Proof. intros A P n; induction n as [| n IH]; intros [| x l] H; cbn; auto; inversion H; auto. Qed.

  Lemma Forall_firstn_intro : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (List.firstn n l).
  Proof. intros A P n; induction n as [| n IH]; intros [| x l] H; cbn; auto; inversion H; auto. Qed.

  Lemma Forall_map_intro : forall {A B} (P : B -> Prop) (f : A -> B) l, (forall x, P (f x)) -> Forall P (List.map f l).
  Proof. intros; apply Forall_map, Forall_forall; auto. Qed.
End Ok.

#[export]
Hint Resolve decl_carried_some decl_carried_none decl_carried_lookup decl_carried_carry Forall_app_intro Forall_repeat_intro Forall_skipn_intro
  Forall_firstn_intro : mctt.
#[export]
Hint Constructors Forall : mctt.
#[export]
Hint Unfold fenv_ok : mctt.
(** A closure's environment, read as an environment, for the lemmas on
    environments *)
#[export]
Hint Extern 3 (Forall (fdentry_ok ?T ?X) ?ρ) => change (fenv_ok T X ρ) : mctt.

#[export]
Hint Constructors fdomain_ok fdomain_ne_ok fdomain_nf_ok fdmod_ok fdentry_ok fentry_type_ok : mctt.
#[export]
Hint Resolve fenv_var_ok fenv_type_ok fenv_mod_ok fextend_env_ok fextend_env_mod_ok fextend_env_dm_ok fenv_extend_typed_ok
  ftele_head_type_ok ftele_entries_ok fenv_tele_ok
  fdomain_level_suc_ok fdomain_level_max_ok fdomain_level_lit_ok fdm_clo_ok fkinds_pads_ok fkinds_body_entry_ok
  combine_ok : mctt.

(** The operations on fast values are read through their erasure
    equations, never unfolded by a tactic: the obligations of the
    implementations state them as computed.  [Opaque] has no [export]
    form, so each file defining implementations on fast values makes
    [fenv_var], [fenv_type], [fenv_mod], [fextend_env], [fextend_env_mod],
    [fextend_env_dm], [fenv_extend_typed], [fenv_tele], [fdomain_level_suc],
    [fdomain_level_max], [fdomain_level_lit], [fdm_clo], [fkinds_pads],
    [fkinds_body_entry] and [carry] opaque locally. *)

(** ** Right Values, by Their Parts

    [ok_invert] reads the parts of a right value made by a constructor off
    the hypothesis that it is right; [ok_solve] proves a value, a list or an
    environment right from the rightness of its parts. *)
Ltac fd_head v :=
  lazymatch v with
  | fd_pi _ _ _ _ _ => idtac | fd_univ _ => idtac | fd_suniv _ => idtac | fd_level _ => idtac | fd_level_sort => idtac
  | fd_lvl _ _ => idtac | fd_prop => idtac | fd_True => idtac | fd_proof _ _ => idtac | fd_False => idtac
  | fd_and _ _ _ => idtac | fd_fn _ _ _ => idtac | fd_neut _ _ => idtac
  | fd_member _ _ => idtac | fd_ind _ _ _ _ => idtac | fd_con _ _ _ _ _ => idtac | fd_ihfn _ _ _ _ _ _ _ => idtac
  | fd_shfam _ _ _ _ _ => idtac | fd_ihfam _ _ _ _ _ _ _ _ _ => idtac | fd_record _ _ => idtac | fd_tuple _ => idtac
  | fd_var _ => idtac | fd_app _ _ => idtac | fd_absurd _ _ => idtac | fd_glob _ => idtac
  | fd_elim _ _ _ _ _ _ _ _ => idtac | fd_proj _ _ => idtac | fd_dom _ _ => idtac
  | fdm_global _ _ => idtac | fdm_local _ _ _ => idtac | fdm_member _ _ => idtac
  | fde_term _ _ => idtac | fde_mod _ _ => idtac | fde_dm _ _ _ _ => idtac
  | fentry_type_value _ => idtac | fentry_type_closure _ _ => idtac | fentry_type_shape _ _ _ _ => idtac
  | fentry_type_induction_hypothesis _ _ _ _ _ _ _ _ => idtac | fentry_type_none => idtac
  end.

Ltac ok_invert :=
  repeat match goal with H : fenv_ok _ _ _ |- _ => unfold fenv_ok in H end;
  repeat match goal with
    | H : fdomain_ok _ _ ?v |- _ => fd_head v; inversion H; clear H; subst
    | H : fdomain_ne_ok _ _ ?v |- _ => fd_head v; inversion H; clear H; subst
    | H : fdomain_nf_ok _ _ ?v |- _ => fd_head v; inversion H; clear H; subst
    | H : fdmod_ok _ _ ?v |- _ => fd_head v; inversion H; clear H; subst
    | H : fdentry_ok _ _ ?v |- _ => fd_head v; inversion H; clear H; subst
    | H : fentry_type_ok _ _ ?v |- _ => fd_head v; inversion H; clear H; subst
    | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
    | H : Forall _ (_ ++ _) |- _ => apply Forall_app in H as [? ?]
    end.

Ltac ok_solve :=
  ok_invert; repeat match goal with |- _ /\ _ => split end;
  solve [ eauto 8 using fenv_var_ok, fenv_type_ok, fenv_mod_ok, fenv_extend_typed_ok, fenv_tele_ok, ftele_head_type_ok,
                         fdomains_nth_error_ok, field_lookup_ok, combine_ok, Forall_map_intro,
                         fdomain_level_suc_ok, fdomain_level_max_ok, fdomain_level_lit_ok, fkinds_body_entry_ok,
                         fkinds_pads_ok, fdm_clo_ok with mctt ].

(** ** Reading Erasures as Core Values

    [ferase_norm] computes the erasure of fast values made by a
    constructor, and turns the erasure of a fast operation into the Core
    operation on the erasures: the form in which the relations and the
    orders state them.  The erasure of a variable stays. *)
(** [rewrite ?L in *] only where the head [c] of its left side occurs:
    a rewrite that finds no instance still searches every hypothesis, and
    an obligation has many. *)
Ltac ferase_rw_at c L :=
  try (match goal with
       | |- context [c] => idtac
       | H : context [c] |- _ => idtac
       end; rewrite ?L in *).

Ltac ferase_rw_back_at c L :=
  try (match goal with
       | |- context [c] => idtac
       | H : context [c] |- _ => idtac
       end; rewrite <- ?L in *).

Ltac ferase_ops :=
  ferase_rw_back_at fenv_var fenv_var_erase; ferase_rw_back_at fenv_type fenv_type_erase;
  ferase_rw_back_at fenv_mod fenv_mod_erase;
  ferase_rw_at fextend_env fextend_env_erase; ferase_rw_at fextend_env_mod fextend_env_mod_erase;
  ferase_rw_at fextend_env_dm fextend_env_dm_erase; ferase_rw_at fenv_extend_typed fenv_extend_typed_erase;
  ferase_rw_at fenv_tele fenv_tele_erase; ferase_rw_at ftele_head_type ftele_head_type_erase;
  ferase_rw_at fkinds_pads fkinds_pads_erase;
  ferase_rw_at fkinds_body_entry fkinds_body_entry_erase; ferase_rw_at fdm_clo fdm_clo_erase;
  ferase_rw_at fdomain_level_suc fdomain_level_suc_erase; ferase_rw_at fdomain_level_max fdomain_level_max_erase;
  ferase_rw_at fdomain_level_lit fdomain_level_lit_erase; ferase_rw_at (@List.combine) fields_erase_combine;
  ferase_rw_at field_lookup field_lookup_erase.

Ltac ferase_norm :=
  unfold fast_member_reference_ok in *;
  ferase_ops;
  cbn [fdomain_erase fdomain_ne_erase fdomain_nf_erase fdmod_erase fdentry_erase fentry_type_erase List.map
       fast_member_reference_erase fmr_group fmr_declaration fmr_member fmr_arguments] in *;
  ferase_ops;
  (** each rewrite moves an erasure inwards, past one list operation *)
  repeat progress (rewrite ?List.map_app, <- ?skipn_map, <- ?firstn_map, ?List.map_repeat, ?List.map_map in *);
  rewrite ?length_map, ?nth_error_map in *;
  cbn [fdomain_erase fdomain_ne_erase fdomain_nf_erase fdmod_erase fdentry_erase fentry_type_erase List.map option_map] in *.
