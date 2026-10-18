(** * The Semantic Judgments

    A semantic judgment is stated at a global context [Θ ⍮ Ξ], as the
    syntactic one is, and holds at every global context [Θ2 ⍮ Ξ2] that
    [Θ ⍮ Ξ] embeds into soundly ([sem_emb]): there it is the relation of
    [Core/Completeness/LogicalRelation/Definitions.v], read in the PER model
    of [Θ2 ⍮ Ξ2].  A context is moreover valid in its module slots: the unit
    of each slot is valid where it stands ([SemK.ctx_ok]), read at [Θ ⍮ Ξ]
    itself and evaluated at [Θ2 ⍮ Ξ2].  The units and module expressions of
    the module judgments are valid in what they denote in the same way
    ([semK], [smt]).

    The relations at one global context are the building blocks; a sound
    embedding is stated over them, so the definitions below are not
    circular. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import GlobalPresup IndTyping GlobalPaths.
From Mctt.Core.Completeness Require Import LogicalRelation SemK IndCases.
Import Domain_Notations Syntax_Notations.
#[local] Open Scope list_scope.

(** ** Sound embeddings *)

(** [Θ1 ⍮ Ξ1] embeds soundly into [Θ2 ⍮ Ξ2]: it grows into it, and what it
    files and has open is valid there, its declarations too. *)
Record sem_emb (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  { sme_emb : Emb Θ1 Ξ1 Θ2 Ξ2
  ; sme_wf : ⊢ᵍ Θ1 ⍮ Ξ1
  ; sme_filed : @gfiled_ok (gc_mk Θ2 Ξ2) Θ1 Ξ1
  ; sme_ind : forall p D, ind_lookup Θ1 Ξ1 p = Some D -> @sem_core (gc_mk Θ2 Ξ2) D
  }.

(** A declaration of a well-formed global context is typed and closed. *)
Lemma decl_of_glookup : forall Θ Ξ p D,
    ⊢ᵍ Θ ⍮ Ξ -> ind_lookup Θ Ξ p = Some D -> decl_typed Θ Ξ D /\ decl_closed D.
Proof.
  intros * Hg Hl; split.
  - exact (gv_decls _ _ _ _ _ _ (gctx_rwf _ _ Hg) _ _ Hl).
  - exact (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hl).
Qed.

(** ** The judgments at one target

    Each judgment of [Θ ⍮ Ξ], read at a target [Θ2 ⍮ Ξ2]. *)

(** A context: semantically well formed, its slots holding valid units. *)
Record kctx_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) : Prop := mk_kctx_at
  { kca_ctx : @sem_ctx (gc_mk Θ2 Ξ2) Γ
  ; kca_slots : @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ Γ }.

Record kexp_eq_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (A M M' : exp) : Prop :=
  mk_kexp_eq_at
  { kea_ctx : kctx_at Θ Ξ Θ2 Ξ2 Γ
  ; kea_rel : @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M' }.

Record ksubtyp_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (A A' : typ) : Prop :=
  mk_ksubtyp_at
  { ksa_ctx : kctx_at Θ Ξ Θ2 Ξ2 Γ
  ; ksa_rel : @subtyp_under_ctx (gc_mk Θ2 Ξ2) Γ A A' }.

(** A universe: large, or small at a valid level. *)
Record kuniv_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (U : typ) : Prop :=
  mk_kuniv_at
  { kua_ctx : kctx_at Θ Ξ Θ2 Ξ2 Γ
  ; kua_univ : (exists i : nat, U = Typeω@i) \/
               (exists L (n : nat), U = Type⟨L⟩ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (Level@n) L L) }.

(** An extension: the two extended contexts are related, and valid in
    their slots. *)
Record kext_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ Ψ Ψ' : ctx) : Prop := mk_kext_at
  { kxa_ctx : kctx_at Θ Ξ Θ2 Ξ2 Γ
  ; kxa_rel : @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ Ψ Ψ'
  ; kxa_slots : @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ (Ψ ++ Γ)
  ; kxa_slots' : @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ (Ψ' ++ Γ) }.

(** Units: related, and valid in what they denote. *)
Record kunit_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (U U' : gunit) : Prop :=
  mk_kunit_at
  { kna_ctx : kctx_at Θ Ξ Θ2 Ξ2 Γ
  ; kna_rel : @rel_unit_under_ctx (gc_mk Θ2 Ξ2) Γ U U'
  ; kna_valid : @SemK.semK (gc_mk Θ2 Ξ2) Θ Ξ Γ (me_lit U)
  ; kna_valid' : @SemK.semK (gc_mk Θ2 Ξ2) Θ Ξ Γ (me_lit U') }.

(** Module expressions: related, and valid in what they denote. *)
Record kmod_at (Θ : gdeps) (Ξ : gstack) (Θ2 : gdeps) (Ξ2 : gstack) (Γ : ctx) (H H' : modexp) : Prop :=
  mk_kmod_at
  { kma_ctx : kctx_at Θ Ξ Θ2 Ξ2 Γ
  ; kma_rel : @rel_modexp_under_ctx (gc_mk Θ2 Ξ2) Γ H H'
  ; kma_valid : @SemK.smt (gc_mk Θ2 Ξ2) Θ Ξ Γ H
  ; kma_valid' : @SemK.smt (gc_mk Θ2 Ξ2) Θ Ξ Γ H' }.

Arguments kca_ctx {Θ Ξ Θ2 Ξ2 Γ}.
Arguments kca_slots {Θ Ξ Θ2 Ξ2 Γ}.
Arguments kea_ctx {Θ Ξ Θ2 Ξ2 Γ A M M'}.
Arguments kea_rel {Θ Ξ Θ2 Ξ2 Γ A M M'}.
Arguments ksa_ctx {Θ Ξ Θ2 Ξ2 Γ A A'}.
Arguments ksa_rel {Θ Ξ Θ2 Ξ2 Γ A A'}.
Arguments kua_ctx {Θ Ξ Θ2 Ξ2 Γ U}.
Arguments kua_univ {Θ Ξ Θ2 Ξ2 Γ U}.
Arguments kxa_ctx {Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'}.
Arguments kxa_rel {Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'}.
Arguments kxa_slots {Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'}.
Arguments kxa_slots' {Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'}.
Arguments kna_ctx {Θ Ξ Θ2 Ξ2 Γ U U'}.
Arguments kna_rel {Θ Ξ Θ2 Ξ2 Γ U U'}.
Arguments kna_valid {Θ Ξ Θ2 Ξ2 Γ U U'}.
Arguments kna_valid' {Θ Ξ Θ2 Ξ2 Γ U U'}.
Arguments kma_ctx {Θ Ξ Θ2 Ξ2 Γ H H'}.
Arguments kma_rel {Θ Ξ Θ2 Ξ2 Γ H H'}.
Arguments kma_valid {Θ Ξ Θ2 Ξ2 Γ H H'}.
Arguments kma_valid' {Θ Ξ Θ2 Ξ2 Γ H H'}.

(** Each judgment at a target from its parts, in the order the case
    lemmas of [KripkeCases.v] produce them. *)
Lemma kctx_at_intro : forall Θ Ξ Θ2 Ξ2 Γ,
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ Γ -> kctx_at Θ Ξ Θ2 Ξ2 Γ.
Proof. intros * [? ?]; constructor; assumption. Qed.

Lemma kexp_eq_at_intro : forall Θ Ξ Θ2 Ξ2 Γ A M M',
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ Γ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M' ->
    kexp_eq_at Θ Ξ Θ2 Ξ2 Γ A M M'.
Proof. intros * (? & ? & ?); repeat constructor; assumption. Qed.

Lemma ksubtyp_at_intro : forall Θ Ξ Θ2 Ξ2 Γ A A',
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ Γ /\ @subtyp_under_ctx (gc_mk Θ2 Ξ2) Γ A A' ->
    ksubtyp_at Θ Ξ Θ2 Ξ2 Γ A A'.
Proof. intros * (? & ? & ?); repeat constructor; assumption. Qed.

Lemma kuniv_at_intro : forall Θ Ξ Θ2 Ξ2 Γ U,
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ Γ /\
    ((exists i : nat, U = Typeω@i) \/ (exists L (n : nat), U = Type⟨L⟩ /\ @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ (Level@n) L L)) ->
    kuniv_at Θ Ξ Θ2 Ξ2 Γ U.
Proof. intros * (? & ? & ?); constructor; [ constructor |]; assumption. Qed.

Lemma kext_at_intro : forall Θ Ξ Θ2 Ξ2 Γ Ψ Ψ',
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ Ψ Ψ' /\
    @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ (Ψ ++ Γ) /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ (Ψ' ++ Γ) /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ Γ ->
    kext_at Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'.
Proof. intros * (? & ? & ? & ? & ?); constructor; [ constructor | .. ]; assumption. Qed.

Lemma kunit_at_intro : forall Θ Ξ Θ2 Ξ2 Γ U U',
    @rel_unit_under_ctx (gc_mk Θ2 Ξ2) Γ U U' /\
    @SemK.semK (gc_mk Θ2 Ξ2) Θ Ξ Γ (me_lit U) /\ @SemK.semK (gc_mk Θ2 Ξ2) Θ Ξ Γ (me_lit U') /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ Γ ->
    kunit_at Θ Ξ Θ2 Ξ2 Γ U U'.
Proof. intros * (? & ? & ? & ? & ?); constructor; [ constructor | .. ]; assumption. Qed.

Lemma kmod_at_intro : forall Θ Ξ Θ2 Ξ2 Γ H H',
    @rel_modexp_under_ctx (gc_mk Θ2 Ξ2) Γ H H' /\
    @SemK.smt (gc_mk Θ2 Ξ2) Θ Ξ Γ H /\ @SemK.smt (gc_mk Θ2 Ξ2) Θ Ξ Γ H' /\
    @sem_ctx (gc_mk Θ2 Ξ2) Γ /\ @SemK.ctx_ok (gc_mk Θ2 Ξ2) Θ Ξ Γ ->
    kmod_at Θ Ξ Θ2 Ξ2 Γ H H'.
Proof. intros * (? & ? & ? & ? & ?); constructor; [ constructor | .. ]; assumption. Qed.

(** Take the judgments at a target apart. *)
Ltac kdestruct :=
  repeat match goal with
    | H : kctx_at _ _ _ _ _ |- _ => destruct H
    | H : kexp_eq_at _ _ _ _ _ _ _ _ |- _ => destruct H
    | H : ksubtyp_at _ _ _ _ _ _ _ |- _ => destruct H
    | H : kuniv_at _ _ _ _ _ _ |- _ => destruct H
    | H : kext_at _ _ _ _ _ _ _ |- _ => destruct H
    | H : kunit_at _ _ _ _ _ _ _ |- _ => destruct H
    | H : kmod_at _ _ _ _ _ _ _ |- _ => destruct H
    end.

(** State a judgment at a target by its parts. *)
Ltac kgoal :=
  lazymatch goal with
  | |- kctx_at _ _ _ _ _ => apply kctx_at_intro
  | |- kexp_eq_at _ _ _ _ _ _ _ _ => apply kexp_eq_at_intro
  | |- ksubtyp_at _ _ _ _ _ _ _ => apply ksubtyp_at_intro
  | |- kuniv_at _ _ _ _ _ _ => apply kuniv_at_intro
  | |- kext_at _ _ _ _ _ _ _ => apply kext_at_intro
  | |- kunit_at _ _ _ _ _ _ _ => apply kunit_at_intro
  | |- kmod_at _ _ _ _ _ _ _ => apply kmod_at_intro
  end.

(** ** The judgments *)

Definition kctx Θ Ξ Γ : Prop :=
  forall Θ2 Ξ2, sem_emb Θ Ξ Θ2 Ξ2 -> kctx_at Θ Ξ Θ2 Ξ2 Γ.

Definition kexp_eq Θ Ξ Γ A M M' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ Ξ Θ2 Ξ2 -> kexp_eq_at Θ Ξ Θ2 Ξ2 Γ A M M'.

Definition kexp Θ Ξ Γ A M : Prop := kexp_eq Θ Ξ Γ A M M.

Definition ksubtyp Θ Ξ Γ A A' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ Ξ Θ2 Ξ2 -> ksubtyp_at Θ Ξ Θ2 Ξ2 Γ A A'.

Definition kuniv Θ Ξ Γ U : Prop :=
  forall Θ2 Ξ2, sem_emb Θ Ξ Θ2 Ξ2 -> kuniv_at Θ Ξ Θ2 Ξ2 Γ U.

Definition kext Θ Ξ Γ Ψ Ψ' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ Ξ Θ2 Ξ2 -> kext_at Θ Ξ Θ2 Ξ2 Γ Ψ Ψ'.

Definition kunit Θ Ξ Γ U U' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ Ξ Θ2 Ξ2 -> kunit_at Θ Ξ Θ2 Ξ2 Γ U U'.

Definition kmod Θ Ξ Γ H H' : Prop :=
  forall Θ2 Ξ2, sem_emb Θ Ξ Θ2 Ξ2 -> kmod_at Θ Ξ Θ2 Ξ2 Γ H H'.

Notation "⊨ Θ ⍮ Ξ ⍮ Γ" := (kctx Θ Ξ Γ)
  (at level 70, Θ at next level, Ξ at level 69, Γ at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A" := (kexp_eq Θ Ξ Γ A M M')
  (at level 70, Ξ at level 69, Γ at level 69, M at level 69, M' at level 69, A at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ M : A" := (kexp Θ Ξ Γ A M)
  (at level 70, Ξ at level 69, Γ at level 69, M at level 69, A at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ A ⊆ A'" := (ksubtyp Θ Ξ Γ A A')
  (at level 70, Ξ at level 69, Γ at level 69, A at level 69, A' at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ᵤ U" := (kuniv Θ Ξ Γ U)
  (at level 70, Ξ at level 69, Γ at level 69, U at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ'" := (kext Θ Ξ Γ Ψ Ψ')
  (at level 70, Ξ at level 69, Γ at level 69, Ψ at level 69, Ψ' at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U'" := (kunit Θ Ξ Γ U U')
  (at level 70, Ξ at level 69, Γ at level 69, U at level 69, U' at level 69) : type_scope.
Notation "Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H'" := (kmod Θ Ξ Γ H H')
  (at level 70, Ξ at level 69, Γ at level 69, H at level 69, H' at level 69) : type_scope.

(** Open the case of a rule: fix a sound embedding, read every premise at
    its target, take the premises apart, and state the conclusion there by
    its parts. *)
Ltac kintro :=
  unfold kctx, kexp, kexp_eq, ksubtyp, kuniv, kext, kunit, kmod in *; intros;
  match goal with He : sem_emb ?T1 ?X1 ?T2 ?X2 |- _ =>
    let Hemb := fresh "Hemb" in let Hgm := fresh "Hgm" in let Hgf := fresh "Hgf" in
    let Hsub := fresh "Hsub" in let Hgw := fresh "Hgw" in
    pose proof (sme_emb _ _ _ _ He) as Hemb; pose proof (sme_wf _ _ _ _ He) as Hgm;
    pose proof (sme_filed _ _ _ _ He) as Hgf;
    pose proof (em_res _ _ _ _ Hemb) as Hsub; pose proof (em_wf _ _ _ _ Hemb) as Hgw;
    change (⊢ᵍ @gc_deps (gc_mk T2 X2) ⍮ @gc_stack (gc_mk T2 X2)) in Hgw;
    change (gc_sub T1 X1 (@gc_deps (gc_mk T2 X2)) (@gc_stack (gc_mk T2 X2))) in Hsub end;
  repeat match goal with IH : forall _ _, sem_emb _ _ _ _ -> _, He : sem_emb _ _ _ _ |- _ =>
    specialize (IH _ _ He) end;
  kdestruct; destruct_conjs; kgoal.
