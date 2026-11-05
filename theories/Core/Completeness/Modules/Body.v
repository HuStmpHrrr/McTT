(** * Related Closures of Units

    The closures of two related units are related ([rel_lit_body],
    [rel_lit_alias]), and the closure of a unit moved along a substitution is
    related to the closure of the unit over the substituted environment
    ([unit_sub_link_body], [unit_sub_link_alias]).  A closure of a body
    stores the body's expansion ([eval_close_body]), with each local open
    replaced by the definitions it stores, which is the expansion typing
    reads ([body_xp_expand]): so a body is walked entry by entry along its
    expansion, which has no open. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas DescTyping.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases FunctionCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import LetCases UnitCases PropCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Modules Require Import MemberTypes ModuleVal Values ValidUnit.
From Mctt.Core.Semantic Require Import Realizability RetagReadable Evaluation.Modules.
From Mctt.Core.Semantic.Kinds Require Import Kinds KindsTyping KindsEval KindsPER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.

(** ** Walking along a Substitution

    [sub_walk_inv Γ' Γ σ Ψ ρl ρr]: [ρl] is an environment of [Ψ] moved along [σ]
    ([tele_sub Ψ σ ++ Γ']), and [σ] lifted over [Ψ] evaluates there to an
    environment related to [ρr], one of [Ψ ++ Γ]. *)
#[warnings="-cannot-define-projection"]
Record sub_walk_inv (Γ' Γ : ctx) (σ : sub) (Ψ : ctx) (ρl ρr : env) : Prop := mk_sub_walk_inv
  { (** The PER of the left context *)
    sub_walk_inv_left_rel : relation env
    (** The PER of the right context *)
  ; sub_walk_inv_right_rel : relation env
    (** The left PER is the one of [Ψ] moved along [σ], before [Γ'] *)
  ; sub_walk_inv_left_per : EF tele_sub Ψ σ ++ Γ' ≈ tele_sub Ψ σ ++ Γ' ∈ per_ctx_env ↘ sub_walk_inv_left_rel
    (** The right PER is the one of [Ψ ++ Γ] *)
  ; sub_walk_inv_right_per : EF Ψ ++ Γ ≈ Ψ ++ Γ ∈ per_ctx_env ↘ sub_walk_inv_right_rel
    (** [σ] lifted over [Ψ] goes from the left context to the right one *)
  ; sub_walk_inv_sub : (tele_sub Ψ σ ++ Γ') ⊨ˢ sb_qn (List.length Ψ) σ ≈ sb_qn (List.length Ψ) σ : Ψ ++ Γ
    (** The left environment is one of the left context *)
  ; sub_walk_inv_left : sub_walk_inv_left_rel ρl ρl
    (** [σ] lifted evaluates at it to one related to the right environment *)
  ; sub_walk_inv_link : exists ρm, ⟦ sb_qn (List.length Ψ) σ : Ψ ++ Γ ⟧s ρl ↘ ρm /\ sub_walk_inv_right_rel ρm ρr }.

(** The walk starts at a substitution's value. *)
Lemma sub_walk_init : forall Γ' Γ σ σ' R' R ρ ρσ,
    Γ' ⊨ˢ σ ≈ σ' : Γ ->
    EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' ->
    EF Γ ≈ Γ ∈ per_ctx_env ↘ R ->
    R' ρ ρ -> ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
    sub_walk_inv Γ' Γ σ nil ρ ρσ.
Proof.
  intros * Hσ HΓ' HΓ Hρ Hev.
  pose proof (rel_sub_under_ctx_refl_left Hσ) as Hσσ.
  econstructor; [ exact HΓ' | exact HΓ | exact Hσσ | exact Hρ |].
  exists ρσ; split; [ exact Hev |].
  eapply (rel_sub_under_ctx_at' Hσσ HΓ' HΓ); eassumption.
Qed.

(** The right environment of the walk is one of the right context. *)
Lemma sub_walk_right : forall Γ' Γ σ Ψ ρl ρr, sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    exists Rr, EF Ψ ++ Γ ≈ Ψ ++ Γ ∈ per_ctx_env ↘ Rr /\ Rr ρr ρr.
Proof.
  intros * [Rl Rr _ HΓr _ _ [ρm [_ Hmr]]].
  assert (HPr : PER Rr) by (eapply per_env_PER; exact HΓr).
  exists Rr; split; [ exact HΓr | etransitivity; [ symmetry; exact Hmr | exact Hmr ] ].
Qed.

(** One step of the walk, at an entry [e]: an extension of the left
    environment of the left context extended, and one of the right
    environment that the lifted substitution's value there relates to
    ([rel_sub_q_entry]: its head is the left head, retagged at [e]). *)
Lemma sub_walk_extend : forall Γ' Γ σ Ψ ρl ρr e x y Rl' Rr',
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    EF tele_sub (e :: Ψ) σ ++ Γ' ≈ tele_sub (e :: Ψ) σ ++ Γ' ∈ per_ctx_env ↘ Rl' ->
    EF (e :: Ψ) ++ Γ ≈ (e :: Ψ) ++ Γ ∈ per_ctx_env ↘ Rr' ->
    (tele_sub (e :: Ψ) σ ++ Γ') ⊨ˢ sb_qn (List.length (e :: Ψ)) σ ≈ sb_qn (List.length (e :: Ψ)) σ : (e :: Ψ) ++ Γ ->
    Rl' x x -> x↯ = ρl ->
    (forall Rr t, EF Ψ ++ Γ ≈ Ψ ++ Γ ∈ per_ctx_env ↘ Rr -> Rr t ρr ->
       Rr' (retag_entry (centry_tag e (Ψ ++ Γ) t) (centry_slot_unit e) (env_entry x 0) :: t) y) ->
    sub_walk_inv Γ' Γ σ (e :: Ψ) x y.
Proof.
  intros * [Rl Rr HΓl HΓr Hsub Hl [ρm [Hm Hmr]]] HΓl' HΓr' Hsub' Hx Hxl Hy.
  subst ρl.
  assert (HPr : PER Rr) by (eapply per_env_PER; exact HΓr).
  destruct (rel_sub_q_entry HΓl' HΓr Hsub _ _ Hx Hm e) as [t [Hq Htm]].
  econstructor; [ exact HΓl' | exact HΓr' | exact Hsub' | exact Hx |].
  eexists; split; [ exact Hq |].
  apply (Hy Rr); [ exact HΓr | etransitivity; eassumption ].
Qed.

(** A type along the walk: its value moved along the substitution at the
    left environment, against its value at the right one; elements related
    there are related at its head PER over any environment of the right
    context related to the right one. *)
Lemma sub_walk_type : forall Γ' Γ σ Ψ A i ρl ρr,
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ᵗ A ≈ A at i ->
    exists a a' R, ⟦ A[sb_qn (List.length Ψ) σ] ⟧ ρl ↘ a /\ ⟦ A ⟧ ρr ↘ a' /\ per_univ_elem i R a a' /\
      forall Rr t, EF Ψ ++ Γ ≈ Ψ ++ Γ ∈ per_ctx_env ↘ Rr -> Rr t ρr ->
        forall c c', R c c' -> Dom c ≈ c' ∈ per_head A A t ρr.
Proof.
  intros * [Rl Rr0 HΓl HΓr Hsub Hl [ρm [Hm Hmr]]] HA.
  destruct (rel_type_inst _ _ _ _ _ _ HA Hsub HΓl _ _ Hl Hm) as (a1 & a2 & Ha1 & Ha2 & U12).
  destruct (rel_type_inversion_simple_at HΓr HA _ _ Hmr) as (b2 & b3 & Hb2 & Hb3 & U23).
  functional_eval_rewrite_clear.
  assert (U13 : per_univ i a1 b3) by (eapply per_univ_trans'; eassumption).
  destruct U13 as [R HR].
  exists a1, b3, R; split; [ exact Ha1 | split; [ exact Hb3 | split; [ exact HR |] ] ].
  intros Rr t HRr Ht c c' Hc k Q x x' Hx Hx' HQ.
  destruct (rel_type_inversion_simple_at HRr HA _ _ Ht) as (d1 & d3 & Hd1 & Hd3 & [R' HR']).
  functional_eval_rewrite_clear.
  assert (Ha1d : Dom a1 ≈ x ∈ per_univ i).
  { eapply per_univ_trans'; [ eexists; exact HR | apply per_univ_sym'; eexists; exact HR' ]. }
  apply (per_univ_irrel_rel _ _ _ _ _ _ _ _ _ HR Ha1d HQ); exact Hc.
Qed.

(** Along the walk, both values of a type of the kind [κ] are of [κ]. *)
Lemma sub_walk_kind : forall Γ' Γ σ Ψ A κ i ρl ρr a a' R,
    sub_walk_inv Γ' Γ σ Ψ ρl ρr -> rel_type_kind (Ψ ++ Γ) A κ ->
    ⟦ A[sb_qn (List.length Ψ) σ] ⟧ ρl ↘ a -> ⟦ A ⟧ ρr ↘ a' -> per_univ_elem i R a a' ->
    domain_kind a = κ /\ domain_kind a' = κ.
Proof.
  intros * Hinv HAk Ha Ha' HR.
  destruct (sub_walk_right _ _ _ _ _ _ Hinv) as (Rr & HRr & Hrr).
  destruct (HAk _ HRr _ _ Hrr) as (a0 & Ea0 & Hk).
  pose proof (functional_eval_exp _ _ _ _ Ea0 Ha') as ->.
  split; [ rewrite (per_univ_elem_kind _ _ _ _ HR); exact Hk | exact Hk ].
Qed.

(** An assumption along the walk: the environments extended by related
    values, each stored at its type over its environment. *)
Lemma sub_walk_assumption : forall Γ' Γ σ Ψ κ A i ρl ρr,
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ᵗ A ≈ A at i ->
    exists a a' R, ⟦ A[sb_qn (List.length Ψ) σ] ⟧ ρl ↘ a /\ ⟦ A ⟧ ρr ↘ a' /\ per_univ_elem i R a a' /\
      forall c c', R c c' ->
        sub_walk_inv Γ' Γ σ (Ψ ▹{κ} A) (ρl ↦ c ⦂ entry_type_closure A[sb_qn (List.length Ψ) σ] ρl)
          (ρr ↦ c' ⦂ entry_type_closure A ρr).
Proof.
  intros * Hinv HA.
  destruct (sub_walk_type _ _ _ _ _ _ _ _ Hinv HA) as (a & a' & R & Ha & Ha' & HR & Hhd).
  exists a, a', R; split; [ exact Ha | split; [ exact Ha' | split; [ exact HR |] ] ].
  intros c c' Hc.
  pose proof Hinv as [Rl Rr HΓl HΓr Hsub Hl _].
  assert (HPR : PER R) by (eapply per_elem_PER; exact HR).
  assert (Hcc : R c c) by (etransitivity; [ exact Hc | symmetry; exact Hc ]).
  assert (Hc'c' : R c' c') by (etransitivity; [ symmetry; exact Hc | exact Hc ]).
  assert (Haa : per_univ_elem i R a a) by (etransitivity; [ exact HR | symmetry; exact HR ]).
  assert (Ha'a' : per_univ_elem i R a' a') by (etransitivity; [ symmetry; exact HR | exact HR ]).
  pose proof (entry_readable_of_elem_closure Ha Ha Haa Hcc) as [Rc _].
  pose proof (entry_readable_of_elem_closure Ha' Ha' Ha'a' Hc'c') as [Rc' _].
  eapply sub_walk_extend with (e := ce_ass κ A);
    [ exact Hinv | exact (per_ctx_env_of_typ_sub HΓl Hsub HA) | exact (per_ctx_env_of_typ HΓr HA)
    | exact (rel_sub_under_ctx_q Hsub HA)
    | exact (per_env_extend_sub_intro HΓl Hsub HA _ _ _ _ _ _ _ _ _ _ Hl Ha Haa Hcc Rc Rc) | reflexivity |].
  intros Rr0 t HRr0 Ht.
  assert (E : Rr0 <~> Rr) by (eapply per_ctx_env_right_irrel; eassumption).
  pose proof (Hhd _ _ HRr0 Ht _ _ Hc) as Hh.
  destruct (per_head_closure_readable (per_ctx_env_of_typ (κ := κ) HRr0 HA) HRr0 Ht Hh) as [Rl0 _].
  unfold per_env_extend; cbn [env_entry retag_entry extend_env].
  apply (mk_per_ctx_env_cons_rel _ _ _ _ (de_term c (centry_tag (ce_ass κ A) (Ψ ++ Γ) t) :: t) (ρr ↦ c' ⦂ entry_type_closure A ρr) (proj1 (E _ _) Ht));
    [ exact Hh | intros _; eexists; reflexivity | intros _; eexists; reflexivity
    | split; [ exact Rl0 | cbn; lia ] | split; [ exact Rc' | cbn; lia ] ].
Qed.

(** The parameters, outermost first: [ts] is the rest of the telescope,
    reversed.  The closures still lacking parameters store their
    definitions expanded ([moddef_expand]). *)
Lemma sub_walk_params : forall Γ' Γ σ ts Ψ Dl D ρl ρr,
    tele_ass ts ->
    ⊨ rev ts ++ Ψ ++ Γ ->
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    (forall ρl' ρr', sub_walk_inv Γ' Γ σ (rev ts ++ Ψ) ρl' ρr' ->
       exists h h', ⟦ nil ⊢ Dl ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρl' ↘ h /\ ⟦ nil ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρr' ↘ h' /\ per_dmod h h') ->
    exists h h', ⟦ tele_sub (rev ts) (sb_qn (List.length Ψ) σ) ⊢ Dl ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρl ↘ h /\
      ⟦ rev ts ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρr ↘ h' /\ per_dmod h h'.
Proof.
  induction ts as [| e ts IH]; intros * Hts HΨ Hinv HD; cbn [rev tele_sub app] in *.
  - apply HD; exact Hinv.
  - inversion Hts as [| ? ? (κ & A & ->) Hts0]; subst.
    rewrite tele_sub_app; cbn [tele_sub length sb_qn centry_sub].
    rewrite <- !app_assoc in HΨ; cbn [app] in HΨ.
    pose proof (rel_ctx_wf_app_r _ _ HΨ) as HΨA.
    destruct (rel_ctx_wf_ass_inv HΨA) as [Srt [HS HA]].
    destruct (rel_type_of_sort (sort_kind_type_sort _ _ HS) HA) as [i HAt].
    destruct (sub_walk_assumption _ _ _ _ κ _ _ _ _ Hinv HAt) as (a & a' & R & Ha & Ha' & HRa & Hc).
    destruct (sub_walk_kind _ _ _ _ _ _ _ _ _ _ _ _ Hinv (rel_type_kind_of_sort_kind HS HA) Ha Ha' HRa) as [Ka Ka'].
    exists (dm_local (tele_sub (rev ts) (sb_qn (S (List.length Ψ)) σ) ++ ce_ass κ A[sb_qn (List.length Ψ) σ] :: nil) (moddef_expand Dl) ρl),
           (dm_local (rev ts ++ ce_ass κ A :: nil) (moddef_expand D) ρr).
    split; [ apply close_unsat; rewrite length_app; cbn; lia |].
    split; [ apply close_unsat; rewrite length_app; cbn; lia |].
    eapply per_dmod_closure_step; [ exact Ha | exact Ha' | exact HRa | exact Ka | exact Ka' |].
    intros c c' Hcc.
    pose proof (IH (Ψ ▹{κ} A) Dl D _ _ Hts0 HΨ (Hc _ _ Hcc)) as HI.
    cbn [length] in HI.
    destruct HI as (h & h' & Hh & Hh' & Hhh); [| exists h, h'; rewrite !eval_close_expand_iff; split; [ exact Hh | split; [ exact Hh' | exact Hhh ] ] ].
    intros ρl' ρr' Hi; apply HD; rewrite <- app_assoc; exact Hi.
Qed.

(** A definition of a type of an evaluated kind [r] along the walk: its
    types and values, and the extended walk at the values of its two
    sides. *)
Lemma sub_walk_def : forall Γ' Γ σ Ψ A r i0 M ρl ρr,
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    evaluated_kind r -> Ψ ++ Γ ⊨ A : abs_kind_sort r Typeω@i0 -> Ψ ++ Γ ⊨ M : A ->
    exists i R m m', PER.Definitions.rel_typ i A[sb_qn (List.length Ψ) σ] ρl A ρr R /\
      rel_typ_kind A[sb_qn (List.length Ψ) σ] ρl r /\ rel_typ_kind A ρr r /\
      ⟦ M[sb_qn (List.length Ψ) σ] ⟧ ρl ↘ m /\ ⟦ M ⟧ ρr ↘ m' /\ R m m' /\
      sub_walk_inv Γ' Γ σ (Ψ ▸ A ≔ M) (ρl ↦ m ⦂ entry_type_closure A[sb_qn (List.length Ψ) σ] ρl)
        (ρr ↦ m' ⦂ entry_type_closure A ρr).
Proof.
  intros * Hinv Hr HA HM.
  assert (HSrt : relevant_sort (abs_kind_sort r Typeω@i0)) by (destruct Hr; constructor).
  destruct (rel_type_of_relevant_sort HSrt HA) as [[k HAt] HArel].
  destruct (sub_walk_type _ _ _ _ _ _ _ _ Hinv HAt) as (a & a' & R & Ha & Ha' & HR & Hhd).
  pose proof Hinv as [Rl Rr HΓl HΓr Hsub Hl [ρm [Hm Hmr]]].
  set (τ := sb_qn (List.length Ψ) σ) in *.
  assert (HPl : PER Rl) by (eapply per_env_PER; exact HΓl).
  assert (HPr : PER Rr) by (eapply per_env_PER; exact HΓr).
  assert (HPR : PER R) by (eapply per_elem_PER; exact HR).
  assert (Hrr : Rr ρr ρr) by (etransitivity; [ symmetry; exact Hmr | exact Hmr ]).
  destruct (valid_inst _ _ _ _ _ _ HM HArel Hsub HΓl _ _ Hl Hm) as (m1 & m2 & a2 & j & E & Hm1 & Hm2 & Ha2 & HE & Hm12).
  destruct (valid_at _ _ _ _ _ HM HAt HArel HΓr _ _ Hmr) as (m2' & m3 & a2' & j' & E' & Hm2' & Hm3 & Ha2' & HE' & Hm23).
  destruct (rel_type_inst _ _ _ _ _ _ HAt Hsub HΓl _ _ Hl Hm) as (b1 & b2 & Hb1 & Hb2 & U12).
  functional_eval_rewrite_clear.
  assert (E1 : R <~> E) by (eapply per_univ_irrel_rel; [ exact HR | exact U12 | exact HE ]).
  assert (E2 : R <~> E') by (eapply per_univ_irrel_rel; [ exact HR | exact U12 | exact HE' ]).
  apply E1 in Hm12; apply E2 in Hm23.
  assert (Hm13 : R m1 m3) by (etransitivity; eassumption).
  assert (Hm11 : R m1 m1) by (etransitivity; [ exact Hm13 | symmetry; exact Hm13 ]).
  assert (Hm33 : R m3 m3) by (etransitivity; [ symmetry; exact Hm13 | exact Hm13 ]).
  assert (Haa : per_univ_elem k R a a) by (etransitivity; [ exact HR | symmetry; exact HR ]).
  assert (Ha'a' : per_univ_elem k R a' a') by (etransitivity; [ symmetry; exact HR | exact HR ]).
  pose proof (per_univ_elem_kind _ _ _ _ HR) as Erel.
  destruct (rel_exp_of_abs_kind_sort_at HΓr HA _ _ Hrr) as (a0 & Ea0 & Hra0).
  functional_eval_rewrite_clear.
  exists k, R, m1, m3.
  split; [ econstructor; eassumption |].
  split; [ exists a; split; [ exact Ha | congruence ] |].
  split; [ exists a'; split; [ assumption | reflexivity ] |].
  split; [ exact Hm1 | split; [ exact Hm3 | split; [ exact Hm13 |] ] ].
  pose proof (entry_readable_of_elem_closure Ha Ha Haa Hm11) as [Rm1 _].
  pose proof (entry_readable_of_elem_closure Ha' Ha' Ha'a' Hm33) as [Rm3 _].
  pose proof (rel_type_inversion_simple_at HΓr HAt) as HSr.
  pose proof (rel_exp_under_ctx_simple_at_of_evaluated HΓr (rel_typ_evaluated_at HArel HΓr) HM) as HMr.
  eapply sub_walk_extend with (e := ce_def A M);
    [ exact Hinv | exact (per_ctx_env_of_def_sub_evaluated HΓl Hsub HAt HArel HM)
    | exact (per_ctx_env_of_def_evaluated Hr HΓr HAt (rel_exp_of_abs_kind_sort_at HΓr HA) HM)
    | exact (rel_sub_under_ctx_q_def_evaluated Hsub HAt HArel HM) | | reflexivity |].
  - eapply per_env_extend_def_intro;
      [ exact HPl | exact (rel_type_sub_simple HΓl Hsub HAt) | exact (rel_exp_under_ctx_sub_simple_evaluated HΓl Hsub HArel HM)
      | exact Hl | eapply per_head_of; [ exact Ha | exact Ha | exact Haa | exact Hm11 ] | exact Rm1 | exact Rm1 | exact Hm1
      | eapply per_head_of; [ exact Ha | exact Ha | exact Haa | exact Hm11 ] ].
  - intros Rr0 t HRr0 Ht.
    assert (Er : Rr0 <~> Rr) by (eapply per_ctx_env_right_irrel; eassumption).
    pose proof (proj1 (Er _ _) Ht) as Ht'.
    pose proof (Hhd _ _ HRr0 Ht _ _ Hm13) as Hh.
    destruct (per_head_closure_readable (per_ctx_env_of_typ (κ := ak_relevant) HRr0 HAt) HRr0 Ht Hh) as [Rl0 _].
    cbn [env_entry retag_entry extend_env].
    assert (Hext : per_env_extend A A Rr (de_term m1 (centry_tag (ce_def A M) (Ψ ++ Γ) t) :: t) (ρr ↦ m3 ⦂ entry_type_closure A ρr)).
    { apply (mk_per_ctx_env_cons_rel _ _ _ _ (de_term m1 (centry_tag (ce_def A M) (Ψ ++ Γ) t) :: t) (ρr ↦ m3 ⦂ entry_type_closure A ρr) Ht');
        [ exact Hh | intros _; eexists; reflexivity | intros _; eexists; reflexivity
        | split; [ exact Rl0 | cbn; lia ] | split; [ exact Rm3 | cbn; lia ] ]. }
    assert (Tr : def_tie A M (ρr ↦ m3 ⦂ entry_type_closure A ρr))
      by (exists m3; split; [ exact Hm3 | eapply per_head_of; [ exact Ha' | exact Ha' | exact Ha'a' | exact Hm33 ] ]).
    assert (HPe : PER (per_env_extend A A Rr)) by (eapply per_env_PER; exact (per_ctx_env_of_typ (κ := ak_relevant) HΓr HAt)).
    constructor; [ exact Hext | eapply (def_tie_resp HPr HSr HMr); [ symmetry; exact Hext | exact Tr ] | exact Tr ].
Qed.

(** A definition of a proposition along the walk: its types are related
    propositions, and the walk extends by the proofs kept, [⋆ᵈ⟨M[σ], ρl⟩]
    and [⋆ᵈ⟨M, ρr⟩], neither evaluated.  They read back: [M] is scoped by
    its context, [M] moved along [σ] by the left one. *)
Lemma sub_walk_def_proof : forall Γ' Γ σ Ψ A M ρl ρr,
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ A : Propₘ -> exp_scoped (List.length (Ψ ++ Γ)) M ->
    exists R, PER.Definitions.rel_typ 0 A[sb_qn (List.length Ψ) σ] ρl A ρr R /\
      rel_typ_kind A[sb_qn (List.length Ψ) σ] ρl ak_propositional /\ rel_typ_kind A ρr ak_propositional /\
      sub_walk_inv Γ' Γ σ (Ψ ▸ A ≔ M)
        (ρl ↦ ⋆ᵈ⟨M[sb_qn (List.length Ψ) σ], ρl⟩ ⦂ entry_type_closure A[sb_qn (List.length Ψ) σ] ρl)
        (ρr ↦ ⋆ᵈ⟨M, ρr⟩ ⦂ entry_type_closure A ρr).
Proof.
  intros * Hinv HA HMs.
  pose proof (rel_type_of_prop 0 HA) as HAt.
  destruct (sub_walk_type _ _ _ _ _ _ _ _ Hinv HAt) as (a & a' & R & Ha & Ha' & HR & _).
  pose proof Hinv as [Rl Rr HΓl HΓr Hsub Hl [ρm [Hm Hmr]]].
  set (τ := sb_qn (List.length Ψ) σ) in *.
  assert (HPr : PER Rr) by (eapply per_env_PER; exact HΓr).
  assert (Hrr : Rr ρr ρr) by (etransitivity; [ symmetry; exact Hmr | exact Hmr ]).
  pose proof Hsub as [_ _ _ _ _ Hτs].
  assert (HMτ : exp_scoped (List.length (tele_sub Ψ σ ++ Γ')) M[τ])
    by (eapply exp_scoped_sub; [ exact HMs | intros x Hx; exact (proj1 (Hτs x Hx)) ]).
  destruct (per_ctx_env_kept_proof_readable _ _ _ M[τ] HΓl (exp_scoped_free_bound _ _ HMτ) _ _ Hl) as [Rp1 _].
  destruct (per_ctx_env_kept_proof_readable _ _ _ M HΓr (exp_scoped_free_bound _ _ HMs) _ _ Hrr) as [Rp2 _].
  destruct (rel_exp_of_prop_sub_simple HΓl Hsub HA _ _ Hl) as (b & b2 & Eb & Eb2 & Hpb).
  destruct (rel_exp_of_prop_inversion_simple_at HΓr HA _ _ Hrr) as (b' & b2' & Eb' & Eb2' & Hpb').
  functional_eval_rewrite_clear.
  pose proof Hpb as [Hrb _ _]; pose proof Hpb' as [Hrb' _ _].
  pose proof (entry_readable_of_elem_closure Ha Ha (per_univ_elem_of_prop 0 _ _ Hpb) (conj Rp1 Rp1)) as [Rc1 _].
  pose proof (entry_readable_of_elem_closure Ha' Ha' (per_univ_elem_of_prop 0 _ _ Hpb') (conj Rp2 Rp2)) as [Rc2 _].
  exists R; split; [ econstructor; eassumption |].
  split; [ exists a; split; assumption |]; split; [ exists a'; split; assumption |].
  eapply sub_walk_extend with (e := ce_def A M);
    [ exact Hinv | exact (per_ctx_env_of_def_prop_at (M := M[τ]) HΓl (rel_exp_of_prop_sub_simple HΓl Hsub HA))
    | exact (per_ctx_env_of_def_prop (M := M) HΓr HA)
    | exact (rel_sub_under_ctx_q_def_prop Hsub HA) | | reflexivity |].
  - apply (mk_per_ctx_env_cons_rel _ _ _ _ (ρl ↦ ⋆ᵈ⟨M[τ], ρl⟩ ⦂ entry_type_closure A[τ] ρl) (ρl ↦ ⋆ᵈ⟨M[τ], ρl⟩ ⦂ entry_type_closure A[τ] ρl) Hl);
      [ exact (per_head_proof Ha Hrb Rp1 Rp1) | intros _; eexists; reflexivity | intros _; eexists; reflexivity
      | split; [ exact Rc1 | cbn; lia ] | split; [ exact Rc1 | cbn; lia ] ].
  - intros Rr0 t HRr0 Ht.
    assert (Er : Rr0 <~> Rr) by (eapply per_ctx_env_right_irrel; eassumption).
    pose proof (proj1 (Er _ _) Ht) as Ht'.
    destruct (rel_exp_of_prop_inversion_simple_at HRr0 HA _ _ Ht) as (d & d2 & Ed & Ed2 & Hpd).
    pose proof Hpd as [Hrd _ _].
    pose proof (per_head_proof (S' := A) (ρ' := ρr) Ed Hrd Rp1 Rp2) as Hh.
    destruct (per_head_closure_readable (per_ctx_env_of_typ (κ := ak_propositional) HRr0 HAt) HRr0 Ht Hh) as [Rl0 _].
    cbn [env_entry retag_entry extend_env].
    apply (mk_per_ctx_env_cons_rel _ _ _ _ (de_term ⋆ᵈ⟨M[τ], ρl⟩ (centry_tag (ce_def A M) (Ψ ++ Γ) t) :: t)
             (ρr ↦ ⋆ᵈ⟨M, ρr⟩ ⦂ entry_type_closure A ρr) Ht');
      [ exact Hh | intros _; eexists; reflexivity | intros _; eexists; reflexivity
      | split; [ exact Rl0 | cbn; lia ] | split; [ exact Rc2 | cbn; lia ] ].
Qed.

(** A nested unit along the walk: its two closures are related, and so are
    the environments they extend, each storing the unit written. *)
Lemma sub_walk_mod : forall Γ' Γ σ Ψ U ρl ρr,
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ᵐ me_lit U ≈ me_lit U -> gunit_scoped (List.length (Ψ ++ Γ)) U ->
    exists hl hr, ⟦ me_lit U[sb_qn (List.length Ψ) σ]ᵘ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρl ↘ hl /\
      ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρr ↘ hr /\ per_dmod hl hr /\
      sub_walk_inv Γ' Γ σ (Ψ ▹ₘ U) (ρl ↦ᵐ hl ⦂ U[sb_qn (List.length Ψ) σ]ᵘ) (ρr ↦ᵐ hr ⦂ U).
Proof.
  intros * Hinv HU HUs.
  pose proof Hinv as [Rl Rr HΓl HΓr Hsub Hl [ρm [Hm Hmr]]].
  set (τ := sb_qn (List.length Ψ) σ) in *.
  assert (HPr : PER Rr) by (eapply per_env_PER; exact HΓr).
  assert (HPd : PER per_dmod) by typeclasses eauto.
  destruct (unit_sub_chain HΓl Hsub HU _ _ _ _ Hl Hm Hm) as ([hl hm Hhl Hhm Hlm] & _).
  destruct (unit_chain_at HU HΓr _ _ Hmr) as [hm' hr Hhm' Hhr Hmr'].
  pose proof (functional_eval_modexp _ _ _ _ Hhm Hhm') as <-.
  assert (Hlr : per_dmod hl hr) by (etransitivity; eassumption).
  assert (Hll : per_dmod hl hl) by (etransitivity; [ exact Hlr | symmetry; exact Hlr ]).
  assert (Hrr : per_dmod hr hr) by (etransitivity; [ symmetry; exact Hlr | exact Hlr ]).
  pose proof Hsub as [_ _ _ _ _ Hτs].
  assert (HUτs : gunit_scoped (List.length (tele_sub Ψ σ ++ Γ')) U[τ]ᵘ)
    by (eapply gunit_scoped_sub; [ exact HUs | intros x Hx; exact (proj1 (Hτs x Hx)) ]).
  exists hl, hr; split; [ exact Hhl | split; [ exact Hhr | split; [ exact Hlr |] ] ].
  eapply sub_walk_extend with (e := ce_mod U);
    [ exact Hinv | exact (per_ctx_env_of_mod_sub HΓl Hsub HU HUs) | exact (per_ctx_env_of_mod HΓr HU HUs HUs)
    | exact (rel_sub_under_ctx_q_mod Hsub HU HUs) | | reflexivity |].
  - apply mk_per_ctx_env_mod_rel; cbn [drop_env tl env_mod env_entry hd extend_env_mod];
      first [ exact Hl | exists hl; split; [ exact Hhl | exact Hll ]
            | split; [ apply mod_entry_readable | exact (gunit_scoped_free_bound _ _ HUτs) ] | eexists; reflexivity ].
  - intros Rr0 t HRr0 Ht.
    assert (Er : Rr0 <~> Rr) by (eapply per_ctx_env_right_irrel; eassumption).
    pose proof (proj1 (Er _ _) Ht) as Ht'.
    destruct (unit_chain_at HU HΓr _ _ Ht') as [ht hr' Hht Hhr' Htr'].
    pose proof (functional_eval_modexp _ _ _ _ Hhr Hhr') as <-.
    cbn [env_entry retag_entry centry_slot_unit centry_unit].
    apply (mk_per_ctx_env_mod_rel _ _ _ _ (de_mod hl U :: t) (ρr ↦ᵐ hr ⦂ U));
      cbn [drop_env tl env_mod env_entry hd extend_env_mod];
      first [ exact Ht' | exists hr; split; [ exact Hhr | exact Hrr ]
            | exists ht; split; [ exact Hht | etransitivity; [ exact Hlr | symmetry; exact Htr' ] ]
            | split; [ apply mod_entry_readable | exact (gunit_scoped_free_bound _ _ HUs) ] | eexists; reflexivity ].
Qed.

(** A definition with a module part along the walk: its types and values
    as a definition's, its closures as a nested unit's, and the extended
    walk at them. *)
Lemma sub_walk_dm : forall Γ' Γ σ Ψ A i M U ρl ρr,
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ A : Typeω@i -> Ψ ++ Γ ⊨ M : A -> Ψ ++ Γ ⊨ᵐ me_lit U ≈ me_lit U ->
    exists j R m m' hl hr, PER.Definitions.rel_typ j A[sb_qn (List.length Ψ) σ] ρl A ρr R /\
      ⟦ M[sb_qn (List.length Ψ) σ] ⟧ ρl ↘ m /\ ⟦ M ⟧ ρr ↘ m' /\ R m m' /\
      ⟦ me_lit U[sb_qn (List.length Ψ) σ]ᵘ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρl ↘ hl /\
      ⟦ me_lit U ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρr ↘ hr /\ per_dmod hl hr /\
      sub_walk_inv Γ' Γ σ (Ψ ▸ₘ A ≔ M ‖ U)
        (ρl ↦ᵈ m ⦂ entry_type_closure A[sb_qn (List.length Ψ) σ] ρl ‖ hl ⦂ U[sb_qn (List.length Ψ) σ]ᵘ)
        (ρr ↦ᵈ m' ⦂ entry_type_closure A ρr ‖ hr ⦂ U).
Proof.
  intros * Hinv HA HM HU.
  pose proof (rel_type_of_typ HA) as HAt.
  destruct (sub_walk_def _ _ _ _ _ ak_relevant i _ _ _ Hinv evaluated_kind_relevant HA HM)
    as (k & R & m & m' & [a a' Ha Ha' HR] & _ & _ & Hm1 & Hm3 & Hmm & _).
  destruct (sub_walk_type _ _ _ _ _ _ _ _ Hinv HAt) as (b & b' & R0 & Hb & Hb' & HR0 & Hhd).
  functional_eval_rewrite_clear.
  assert (E : R <~> R0) by (eapply per_univ_elem_right_irrel; eassumption).
  pose proof Hinv as [Rl Rr HΓl HΓr Hsub Hl [ρm [Hm Hmr]]].
  set (τ := sb_qn (List.length Ψ) σ) in *.
  assert (HPl : PER Rl) by (eapply per_env_PER; exact HΓl).
  assert (HPr : PER Rr) by (eapply per_env_PER; exact HΓr).
  assert (HPR : PER R) by (eapply per_elem_PER; exact HR).
  assert (HPd : PER per_dmod) by typeclasses eauto.
  assert (Hm11 : R m m) by (etransitivity; [ exact Hmm | symmetry; exact Hmm ]).
  assert (Hm33 : R m' m') by (etransitivity; [ symmetry; exact Hmm | exact Hmm ]).
  assert (Haa : per_univ_elem k R a a) by (etransitivity; [ exact HR | symmetry; exact HR ]).
  assert (Ha'a' : per_univ_elem k R a' a') by (etransitivity; [ symmetry; exact HR | exact HR ]).
  (* the module part *)
  destruct (unit_sub_chain HΓl Hsub HU _ _ _ _ Hl Hm Hm) as ([hl hm Hhl Hhm Hlm] & _).
  destruct (unit_chain_at HU HΓr _ _ Hmr) as [hm' hr Hhm' Hhr Hmr'].
  pose proof (functional_eval_modexp _ _ _ _ Hhm Hhm') as <-.
  assert (Hlr : per_dmod hl hr) by (etransitivity; eassumption).
  assert (Hll : per_dmod hl hl) by (etransitivity; [ exact Hlr | symmetry; exact Hlr ]).
  assert (Hrr : per_dmod hr hr) by (etransitivity; [ symmetry; exact Hlr | exact Hlr ]).
  exists k, R, m, m', hl, hr.
  split; [ econstructor; eassumption |].
  split; [ exact Hm1 | split; [ exact Hm3 | split; [ exact Hmm |] ] ].
  split; [ exact Hhl | split; [ exact Hhr | split; [ exact Hlr |] ] ].
  pose proof (dm_entry_readable_of_elem_closure Ha Ha Haa Hm11 hl hl U[τ]ᵘ U[τ]ᵘ) as [Rd1 _].
  pose proof (dm_entry_readable_of_elem_closure Ha' Ha' Ha'a' Hm33 hr hr U U) as [Rd2 _].
  pose proof (rel_type_inversion_simple_at HΓr HAt) as HSr.
  pose proof (rel_exp_under_ctx_simple_at_rel HΓr HA HM) as HMr.
  eapply sub_walk_extend with (e := ce_dm A M U);
    [ exact Hinv | exact (per_ctx_env_of_dm_sub HΓl Hsub HA HM HU) | exact (per_ctx_env_of_dm HΓr HA HM HU)
    | exact (rel_sub_under_ctx_q_dm Hsub HA HM HU) | | reflexivity |].
  - assert (Hh1 : per_head A[τ] A[τ] ρl ρl m m) by (eapply per_head_of; [ exact Ha | exact Ha | exact Haa | exact Hm11 ]).
    apply mk_per_env_extend_dm; cbn [drop_env tl env_mod env_entry hd extend_env_dm];
      first [ exact Hl | exact Hh1 | exists m; split; [ exact Hm1 | exact Hh1 ]
            | exists hl; split; [ exact Hhl | exact Hll ] | split; [ exact Rd1 | cbn; lia ] | do 2 eexists; reflexivity ].
  - intros Rr0 t HRr0 Ht.
    assert (Er : Rr0 <~> Rr) by (eapply per_ctx_env_right_irrel; eassumption).
    pose proof (proj1 (Er _ _) Ht) as Ht'.
    pose proof (Hhd _ _ HRr0 Ht _ _ (proj1 (E _ _) Hmm)) as Hh.
    destruct (per_head_dm_readable (h := hl) (h' := hl) (U := U) (per_ctx_env_of_typ (κ := ak_relevant) HRr0 HAt) HRr0 Ht Hh) as [Rl0 _].
    destruct (unit_chain_at HU HΓr _ _ Ht') as [ht hr' Hht Hhr' Htr'].
    pose proof (functional_eval_modexp _ _ _ _ Hhr Hhr') as <-.
    cbn [env_entry retag_entry centry_slot_unit centry_unit].
    set (x := de_dm m (centry_tag (ce_dm A M U) (Ψ ++ Γ) t) hl U :: t).
    assert (Hext : per_env_extend A A Rr x (ρr ↦ᵈ m' ⦂ entry_type_closure A ρr ‖ hr ⦂ U)).
    { apply (mk_per_ctx_env_cons_rel _ _ _ _ x (ρr ↦ᵈ m' ⦂ entry_type_closure A ρr ‖ hr ⦂ U) Ht');
        [ exact Hh
        | intros Hp; exfalso; exact (not_rel_typ_propositional_of_typ HΓr HA _ _ Ht' Hp)
        | intros Hp; exfalso; exact (not_rel_typ_propositional_of_typ HΓr HA _ _ ltac:(etransitivity; [ symmetry; exact Ht' | exact Ht' ]) Hp)
        | exact Rl0 | split; [ exact Rd2 | cbn; lia ] ]. }
    assert (Tr : def_tie A M (ρr ↦ᵈ m' ⦂ entry_type_closure A ρr ‖ hr ⦂ U))
      by (exists m'; split; [ exact Hm3 | eapply per_head_of; [ exact Ha' | exact Ha' | exact Ha'a' | exact Hm33 ] ]).
    assert (HPe : PER (per_env_extend A A Rr)) by (eapply per_env_PER; exact (per_ctx_env_of_typ (κ := ak_relevant) HΓr HAt)).
    apply mk_per_env_extend_dm; subst x; cbn [drop_env tl env_mod env_entry hd extend_env_dm];
      first [ exact Ht' | exact Hh | exact Tr | exact Rl0
            | eapply (def_tie_resp HPr HSr HMr); [ symmetry; exact Hext | exact Tr ]
            | exists hr; split; [ exact Hhr | exact Hrr ]
            | exists ht; split; [ exact Hht | etransitivity; [ exact Hlr | symmetry; exact Htr' ] ]
            | split; [ exact Rd2 | cbn; lia ] | do 2 eexists; reflexivity ].
Qed.

(** An alias's targets along the walk are related. *)
Lemma sub_walk_alias : forall Γ' Γ σ Ψ E ρl ρr,
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    Ψ ++ Γ ⊨ᵐ E ≈ E ->
    exists h h', ⟦ E[sb_qn (List.length Ψ) σ]ᵐ ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρl ↘ h /\
      ⟦ E ⟧ᵐ gc_deps ⍮ gc_stack ⍮ ρr ↘ h' /\ per_dmod h h'.
Proof.
  intros * [Rl Rr HΓl HΓr Hsub Hl [ρm [Hm Hmr]]] HE.
  destruct (valid_mod_inst _ _ _ _ _ HE Hsub HΓl _ _ Hl Hm) as (h1 & h2 & Hh1 & Hh2 & D12).
  destruct (rel_modexp_at _ _ _ _ _ HE HΓr _ _ Hmr) as (g2 & g3 & Hg2 & Hg3 & D23).
  pose proof (functional_eval_modexp _ _ _ _ Hh2 Hg2) as <-.
  exists h1, g3; split; [ exact Hh1 | split; [ exact Hg3 | eapply per_dmod_trans; eassumption ] ].
Qed.

(** A body without opens, entry by entry, along the walk: the body moved
    along the substitution and the body itself make related environments,
    entry by entry related ([per_body]). *)
Lemma sub_walk_body : forall Γ' Γ σ Φ Ψ ρl ρr,
    gm_noopen Φ -> body_shape Φ Φ ->
    ⊨ body_ctx Φ ++ Ψ ++ Γ -> body_sorts_valid Φ (Ψ ++ Γ) -> gmod_scoped (List.length (Ψ ++ Γ)) Φ ->
    sub_walk_inv Γ' Γ σ Ψ ρl ρr ->
    per_body ρl (gmod_sub Φ (sb_qn (List.length Ψ) σ)) ρr Φ /\
    exists ρl1 ρr1, ⟦ gmod_sub Φ (sb_qn (List.length Ψ) σ) ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρl ↘ ρl1 /\
      ⟦ Φ ⟧ᵇ gc_deps ⍮ gc_stack ⍮ ρr ↘ ρr1 /\ sub_walk_inv Γ' Γ σ (body_ctx Φ ++ Ψ) ρl1 ρr1.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its Φg _]; intros * Hn Hs HΦ Hsv Hsc Hinv; cbn in Hn; [| | contradiction ].
  - split; [ constructor |]; exists ρl, ρr; split; [ constructor | split; [ constructor | exact Hinv ] ].
  - cbn [body_shape] in Hs; destruct Hs as (Hs & _ & HE).
    cbn [gmod_scoped] in Hsc; destruct Hsc as [Hsc HsE].
    pose proof (gm_noopen_nopens _ Hn) as Hn0.
    rewrite <- (length_body_ctx _ Hn0), <- List.length_app, app_assoc in HsE.
    assert (Hq : sb_eq (sb_qn (gm_binders Φ) (sb_qn (List.length Ψ) σ)) (sb_qn (List.length (body_ctx Φ ++ Ψ)) σ))
      by (rewrite sb_qn_add, length_app, (length_body_ctx _ Hn0); reflexivity).
    assert (HΦ0 : ⊨ body_ctx Φ ++ Ψ ++ Γ) by (destruct E as [? ? ? ? [] | | | |]; exact (rel_ctx_wf_tail HΦ)).
    destruct (IH _ _ _ Hn Hs HΦ0 (proj1 Hsv) Hsc Hinv) as (Hb & ρl1 & ρr1 & Hb1 & Hb1' & Hi1).
    destruct E as [b pv r A [M |] | pm [Δy Dy] | ? ? ? ? ? | pv A M [Δy Dy] | ? ? ? ?]; cbn in HE; try contradiction;
      cbn [gmod_sub gentry_sub body_ctx app body_sorts_valid entry_tm entry_kind gentry_scoped] in *;
      rewrite app_assoc in HΦ.
    + (* a definition, of the sort it is tagged with *)
      destruct (rel_ctx_wf_def_inv HΦ) as [_ HM].
      destruct (proj2 Hsv _ _ eq_refl) as [i0 HA]; rewrite app_assoc in HA.
      rewrite (exp_sub_sb_eq A _ _ Hq), (exp_sub_sb_eq M _ _ Hq).
      destruct (evaluated_kind_or_propositional r) as [Hr | ->]; [| cbn [abs_kind_sort] in HA ].
      * destruct (sub_walk_def _ _ _ _ _ _ _ _ _ _ Hi1 Hr HA HM) as (i & R & m & m' & HR & HSl & HSr & Hm & Hm' & Hmm & Hi).
        split; [ eapply per_body_def; [ exact Hb | exact Hb1 | exact Hb1' | exact HR | exact HSl | exact HSr
                                      | right; econstructor; eassumption ] |].
        exists (ρl1 ↦ m ⦂ entry_type_closure A[sb_qn (List.length (body_ctx Φ ++ Ψ)) σ] ρl1), (ρr1 ↦ m' ⦂ entry_type_closure A ρr1).
        split; [ apply eval_body_env_def; assumption | split; [ apply eval_body_env_def; assumption | exact Hi ] ].
      * destruct (sub_walk_def_proof _ _ _ _ _ _ _ _ Hi1 HA (proj2 HsE)) as (R & HR & HSl & HSr & Hi).
        split; [ eapply per_body_def; [ exact Hb | exact Hb1 | exact Hb1' | exact HR | exact HSl | exact HSr | left; reflexivity ] |].
        eexists _, _; split; [ apply eval_body_env_def_proof; exact Hb1 | split; [ apply eval_body_env_def_proof; exact Hb1' | exact Hi ] ].
    + (* a module *)
      pose proof (rel_unit_under_ctx_lit _ _ _ (rel_ctx_wf_mod_inv HΦ)) as HU.
      destruct (sub_walk_mod _ _ _ _ _ _ _ Hi1 HU HsE) as (hl & hr & Hhl & Hhr & Hlr & Hi).
      rewrite (gunit_sub_sb_eq (gu_mk Δy Dy) _ _ Hq) in *.
      rewrite gunit_sub_mk in Hhl, Hi |- *; apply eval_me_lit_iff in Hhl, Hhr.
      split; [ eapply per_body_mod; [ exact Hb | exact Hb1 | exact Hb1' | exact Hhl | exact Hhr | exact Hlr ] |].
      eexists _, _; split; [ apply eval_body_env_mod; [ exact Hb1 | exact Hhl ] | split; [ apply eval_body_env_mod; [ exact Hb1' | exact Hhr ] | exact Hi ] ].
    + (* a definition with a module part: as a definition and as a submodule *)
      destruct (rel_ctx_wf_dm_inv HΦ) as ([i HA] & HM & HUv).
      pose proof (rel_unit_under_ctx_lit _ _ _ HUv) as HU.
      destruct (sub_walk_dm _ _ _ _ _ _ _ _ _ _ Hi1 HA HM HU) as (j & R & m & m' & hl & hr & HR & Hm & Hm' & Hmm & Hhl & Hhr & Hlr & Hi).
      rewrite (exp_sub_sb_eq A _ _ Hq), (exp_sub_sb_eq M _ _ Hq), (gunit_sub_sb_eq (gu_mk Δy Dy) _ _ Hq).
      rewrite gunit_sub_mk in Hhl, Hi |- *; apply eval_me_lit_iff in Hhl, Hhr.
      split; [ eapply per_body_dm; [ exact Hb | exact Hb1 | exact Hb1' | exact HR | right; econstructor; eassumption
                                   | exact Hhl | exact Hhr | exact Hlr ] |].
      eexists _, _; split; [ apply eval_body_env_dm; [ exact Hb1 | exact Hm | exact Hhl ]
                           | split; [ apply eval_body_env_dm; [ exact Hb1' | exact Hm' | exact Hhr ] | exact Hi ] ].
Qed.

Variables (Θm : gdeps) (Ξm : gstack).

(** ** Closures Commute with Substitution

    The closure of [U[σ]] over [ρ] is related to that of [U] over [⟦σ⟧ρ],
    for a unit valid in its parts.  A closure of a body stores its
    expansion ([eval_close_body]), the expansion typing reads
    ([body_xp_expand]), and expansion commutes with substitution
    ([gm_expand_sub]): so the walk is along the expansion. *)

Lemma unit_sub_link_body : forall Γ' Γ σ σ' Δ Φ Φx R' ρ ρσ,
    tele_ass Δ -> body_xp Θm Ξm (Δ ++ Γ) Φ Φx -> body_shape Φx Φx ->
    ⊨ body_ctx Φx ++ Δ ++ Γ -> body_sorts_valid Φx (Δ ++ Γ) -> gmod_scoped (List.length (Δ ++ Γ)) Φx ->
    Γ' ⊨ˢ σ ≈ σ' : Γ -> EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' -> R' ρ ρ -> ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
    rel_modexp_evals (me_lit (gu_open Δ Φ)[σ]ᵘ) ρ (me_lit (gu_open Δ Φ)) ρσ.
Proof.
  intros * HΔ Hx Hsx HΦ Hsv Hsc Hσ HΓ' Hρ Hev.
  pose proof (body_xp_expand _ _ _ _ _ Hx) as HxE.
  pose proof (body_xp_result_noopen _ _ _ _ _ Hx) as Hn.
  pose proof (rel_ctx_wf_app_r _ _ HΦ) as HΔΓ.
  destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_app_r _ _ HΔΓ)) as [R HΓ].
  pose proof (sub_walk_init _ _ _ _ _ _ _ _ Hσ HΓ' HΓ Hρ Hev) as Hi.
  destruct (sub_walk_params Γ' Γ σ (rev Δ) nil (md_body sm_open (gmod_sub Φ (sb_qn (List.length Δ) σ))) (md_body sm_open Φ) ρ ρσ
              ltac:(apply Forall_rev; exact HΔ) ltac:(rewrite rev_involutive, app_nil_l; exact HΔΓ) Hi)
    as (h & h' & Hh & Hh' & Hhh).
  - intros ρl' ρr' Hi'; rewrite rev_involutive, app_nil_r in Hi'.
    destruct (sub_walk_body _ _ _ _ _ _ _ Hn Hsx HΦ Hsv Hsc Hi') as (Hb & _).
    eexists _, _; split; [ apply eval_close_body | split; [ apply eval_close_body |] ].
    apply per_dmod_body; rewrite gm_expand_sub, <- HxE; exact Hb.
  - rewrite rev_involutive in Hh, Hh'; cbn [List.length] in Hh.
    rewrite gunit_sub_mk; cbn [moddef_sub].
    exists h h'; [ apply eval_me_lit; exact Hh | apply eval_me_lit; exact Hh' | exact Hhh ].
Qed.

Lemma unit_sub_link_alias : forall Γ' Γ σ σ' Δ E R' ρ ρσ,
    tele_ass Δ -> ⊨ Δ ++ Γ -> Δ ++ Γ ⊨ᵐ E ≈ E ->
    Γ' ⊨ˢ σ ≈ σ' : Γ -> EF Γ' ≈ Γ' ∈ per_ctx_env ↘ R' -> R' ρ ρ -> ⟦ σ : Γ ⟧s ρ ↘ ρσ ->
    rel_modexp_evals (me_lit (gu_mk Δ (md_alias E))[σ]ᵘ) ρ (me_lit (gu_mk Δ (md_alias E))) ρσ.
Proof.
  intros * HΔ HΔΓ HE Hσ HΓ' Hρ Hev.
  destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_app_r _ _ HΔΓ)) as [R HΓ].
  pose proof (sub_walk_init _ _ _ _ _ _ _ _ Hσ HΓ' HΓ Hρ Hev) as Hi.
  destruct (sub_walk_params Γ' Γ σ (rev Δ) nil (md_alias E[sb_qn (List.length Δ) σ]ᵐ) (md_alias E) ρ ρσ
              ltac:(apply Forall_rev; exact HΔ) ltac:(rewrite rev_involutive, app_nil_l; exact HΔΓ) Hi)
    as (h & h' & Hh & Hh' & Hhh).
  - intros ρl' ρr' Hi'; rewrite rev_involutive, app_nil_r in Hi'.
    destruct (sub_walk_alias _ _ _ _ _ _ _ Hi' HE) as (g & g' & Hg & Hg' & Hgg).
    exists g, g'; split; [ apply eval_close_alias0; exact Hg | split; [ apply eval_close_alias0; exact Hg' | exact Hgg ] ].
  - rewrite rev_involutive in Hh, Hh'; cbn [List.length] in Hh.
    rewrite gunit_sub_mk; cbn [moddef_sub].
    exists h h'; [ apply eval_me_lit; exact Hh | apply eval_me_lit; exact Hh' | exact Hhh ].
Qed.

(** ** Entries of Two Related Bodies

    An entry of each of two bodies, read in the environments the bodies
    before it make, is related to the other through their filled-in forms,
    which are related at the parameters. *)

(** The types of two entries, of either sort, through their filled-in
    forms. *)
Lemma typ_bridge : forall C C1 C' C1' A A' σ σ' i i' j RC R1 RC' R1' ρa ρa' ρσ ρσ' ρ1 ρ1',
    C1 ⊨ᵗ A ≈ A at i -> C ⊨ˢ σ ≈ σ : C1 -> EF C ≈ C ∈ per_ctx_env ↘ RC -> RC ρa ρa' ->
    EF C1 ≈ C1 ∈ per_ctx_env ↘ R1 -> ⟦ σ : C1 ⟧s ρa ↘ ρσ -> R1 ρσ ρ1 ->
    C ⊨ᵗ A[σ] ≈ A'[σ'] at j ->
    C1' ⊨ᵗ A' ≈ A' at i' -> C' ⊨ˢ σ' ≈ σ' : C1' -> EF C' ≈ C' ∈ per_ctx_env ↘ RC' -> RC' ρa' ρa' ->
    EF C1' ≈ C1' ∈ per_ctx_env ↘ R1' -> ⟦ σ' : C1' ⟧s ρa' ↘ ρσ' -> R1' ρσ' ρ1' ->
    exists a a', ⟦ A ⟧ ρ1 ↘ a /\ ⟦ A' ⟧ ρ1' ↘ a' /\ Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * HA Hσ HRC Hρ HR1 Hev H1 HAA' HA' Hσ' HRC' Hρ' HR1' Hev' H1'.
  assert (HP : PER RC) by (eapply per_env_PER; exact HRC).
  assert (Hρρ : RC ρa ρa) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  pose proof (rel_type_inversion HA) as [R0 [HΔ0 HAgen]].
  destruct (HAgen _ _ HRC _ _ Hσ _ _ _ _ Hρρ Hev Hev) as [a1 a2 a3 a4 Ha1 Ha2 _ _ (U12 & _)].
  destruct (rel_type_inversion_simple_at HR1 HA _ _ H1) as (b2 & b3 & Hb2 & Hb3 & U23).
  destruct (rel_type_inversion_simple_at HRC HAA' _ _ Hρ) as (c1 & c4 & Hc1 & Hc4 & U14).
  pose proof (rel_type_inversion HA') as [R0' [HΔ0' HAgen']].
  destruct (HAgen' _ _ HRC' _ _ Hσ' _ _ _ _ Hρ' Hev' Hev') as [d4 d5 d6 d7 Hd4 Hd5 _ _ (U45 & _)].
  destruct (rel_type_inversion_simple_at HR1' HA' _ _ H1') as (e5 & e6 & He5 & He6 & U56).
  functional_eval_rewrite_clear.
  exists b3, e6; split; [ exact Hb3 | split; [ exact He6 |] ].
  eapply per_univ_trans'; [ apply per_univ_sym'; exact U23 |].
  eapply per_univ_trans'; [ apply per_univ_sym'; exact U12 |].
  eapply per_univ_trans'; [ exact U14 |].
  eapply per_univ_trans'; [ exact U45 | exact U56 ].
Qed.

(** The values of two definitions of types of an evaluated kind through
    their filled-in forms, related at an element PER of their types. *)
Lemma elem_bridge : forall C C1 C' C1' A A' M M' σ σ' i i' j RC R1 RC' R1' ρa ρa' ρσ ρσ' ρ1 ρ1' k R a a',
    C1 ⊨ᵗ A ≈ A at i -> rel_type_evaluated C1 A -> C1 ⊨ M : A ->
    C ⊨ˢ σ ≈ σ : C1 -> EF C ≈ C ∈ per_ctx_env ↘ RC -> RC ρa ρa' ->
    EF C1 ≈ C1 ∈ per_ctx_env ↘ R1 -> ⟦ σ : C1 ⟧s ρa ↘ ρσ -> R1 ρσ ρ1 ->
    C ⊨ᵗ A[σ] ≈ A'[σ'] at j -> rel_type_evaluated C A[σ] -> C ⊨ M[σ] ≈ M'[σ'] : A[σ] ->
    C1' ⊨ᵗ A' ≈ A' at i' -> rel_type_evaluated C1' A' -> C1' ⊨ M' : A' ->
    C' ⊨ˢ σ' ≈ σ' : C1' -> EF C' ≈ C' ∈ per_ctx_env ↘ RC' -> RC' ρa' ρa' ->
    EF C1' ≈ C1' ∈ per_ctx_env ↘ R1' -> ⟦ σ' : C1' ⟧s ρa' ↘ ρσ' -> R1' ρσ' ρ1' ->
    ⟦ A ⟧ ρ1 ↘ a -> ⟦ A' ⟧ ρ1' ↘ a' -> per_univ_elem k R a a' ->
    exists m m', ⟦ M ⟧ ρ1 ↘ m /\ ⟦ M' ⟧ ρ1' ↘ m' /\ R m m'.
Proof.
  intros * HA HArel HM Hσ HRC Hρ HR1 Hev H1 HAA' HAσrel HMM' HA' HArel' HM' Hσ' HRC' Hρ' HR1' Hev' H1' Ha Ha' HR.
  assert (HP : PER RC) by (eapply per_env_PER; exact HRC).
  assert (Hρρ : RC ρa ρa) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (HPR : PER R) by (eapply per_elem_PER; exact HR).
  (* the values along the chain ρ1, ρσ, ρa, ρa', ρσ', ρ1' *)
  destruct (valid_inst _ _ _ _ _ _ HM HArel Hσ HRC _ _ Hρρ Hev) as (m1 & m2 & x2 & j2 & X2 & Hm1 & Hm2 & Hx2 & HX2 & M12).
  destruct (rel_exp_under_ctx_simple_full_at_evaluated HR1 HArel HM) as [j3 HMs].
  destruct (HMs _ _ H1) as (y2 & y3 & Y & Hy2 & Hy3 & HY & m2' & m3 & Hm2' & Hm3 & M23).
  destruct (rel_exp_under_ctx_simple_full_at_evaluated HRC HAσrel HMM') as [j4 HMMs].
  destruct (HMMs _ _ Hρ) as (z1 & z4 & Z & Hz1 & Hz4 & HZ & m1' & m4 & Hm1' & Hm4 & M14).
  destruct (valid_inst _ _ _ _ _ _ HM' HArel' Hσ' HRC' _ _ Hρ' Hev') as (m4' & m5 & x5 & j5 & X5 & Hm4' & Hm5 & Hx5 & HX5 & M45).
  destruct (rel_exp_under_ctx_simple_full_at_evaluated HR1' HArel' HM') as [j6 HMs'].
  destruct (HMs' _ _ H1') as (w5 & w6 & W & Hw5 & Hw6 & HW & m5' & m6 & Hm5' & Hm6 & M56).
  (* the types along the chain *)
  destruct (rel_type_inst _ _ _ _ _ _ HA Hσ HRC _ _ Hρρ Hev) as (t1 & t2 & Ht1 & Ht2 & T12).
  destruct (rel_type_inversion_simple_at HRC HAA' _ _ Hρ) as (u1 & u4 & Hu1 & Hu4 & U14).
  destruct (rel_type_inst _ _ _ _ _ _ HA' Hσ' HRC' _ _ Hρ' Hev') as (v4 & v5 & Hv4 & Hv5 & V45).
  functional_eval_rewrite_clear.
  exists m3, m6; split; [ exact Hm3 | split; [ exact Hm6 |] ].
  assert (Ha_x2 : Dom a ≈ x2 ∈ per_univ j3) by (apply per_univ_sym'; eexists; exact HY).
  assert (Ha_t1 : Dom a ≈ z1 ∈ per_univ j3) by (eapply per_univ_trans'; [ exact Ha_x2 | apply per_univ_sym'; exact T12 ]).
  assert (Ha_u4 : Dom a ≈ u4 ∈ per_univ j3).
  { eapply per_univ_trans'; [ exact Ha_t1 | exact U14 ]. }
  assert (Ha_x5 : Dom a ≈ x5 ∈ per_univ j3) by (eapply per_univ_trans'; [ exact Ha_u4 | exact V45 ]).
  assert (EY : R <~> Y) by (eapply per_univ_irrel_rel; [ exact HR | exact Ha_x2 | exact HY ]).
  assert (EX2 : R <~> X2) by (eapply per_univ_irrel_rel; [ exact HR | exact Ha_x2 | exact HX2 ]).
  assert (EZ : R <~> Z) by (eapply per_univ_irrel_rel; [ exact HR | exact Ha_t1 | exact HZ ]).
  assert (EX5 : R <~> X5) by (eapply per_univ_irrel_rel; [ exact HR | exact Ha_x5 | exact HX5 ]).
  assert (EW : R <~> W) by (eapply per_univ_irrel_rel; [ exact HR | exact Ha_x5 | exact HW ]).
  apply EY in M23; apply EX2 in M12; apply EZ in M14; apply EX5 in M45; apply EW in M56.
  etransitivity; [ symmetry; exact M23 |].
  etransitivity; [ symmetry; exact M12 |].
  etransitivity; [ exact M14 |].
  etransitivity; [ exact M45 | exact M56 ].
Qed.

(** The closures of two module expressions through their filled-in
    forms. *)
Lemma mod_bridge : forall C C1 C' C1' H H' σ σ' RC R1 RC' R1' ρa ρa' ρσ ρσ' ρ1 ρ1',
    C1 ⊨ᵐ H ≈ H -> C ⊨ˢ σ ≈ σ : C1 -> EF C ≈ C ∈ per_ctx_env ↘ RC -> RC ρa ρa' ->
    EF C1 ≈ C1 ∈ per_ctx_env ↘ R1 -> ⟦ σ : C1 ⟧s ρa ↘ ρσ -> R1 ρσ ρ1 ->
    C ⊨ᵐ H[σ]ᵐ ≈ H'[σ']ᵐ ->
    C1' ⊨ᵐ H' ≈ H' -> C' ⊨ˢ σ' ≈ σ' : C1' -> EF C' ≈ C' ∈ per_ctx_env ↘ RC' -> RC' ρa' ρa' ->
    EF C1' ≈ C1' ∈ per_ctx_env ↘ R1' -> ⟦ σ' : C1' ⟧s ρa' ↘ ρσ' -> R1' ρσ' ρ1' ->
    rel_modexp_evals H ρ1 H' ρ1'.
Proof.
  intros * HH Hσ HRC Hρ HR1 Hev H1 HHH' HH' Hσ' HRC' Hρ' HR1' Hev' H1'.
  assert (HP : PER RC) by (eapply per_env_PER; exact HRC).
  assert (Hρρ : RC ρa ρa) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  destruct (valid_mod_inst _ _ _ _ _ HH Hσ HRC _ _ Hρρ Hev) as (h1 & h2 & Hh1 & Hh2 & D12).
  destruct (rel_modexp_at _ _ _ _ _ HH HR1 _ _ H1) as (g2 & g3 & Hg2 & Hg3 & D23).
  destruct (rel_modexp_at _ _ _ _ _ HHH' HRC _ _ Hρ) as (k1 & k4 & Hk1 & Hk4 & D14).
  destruct (valid_mod_inst _ _ _ _ _ HH' Hσ' HRC' _ _ Hρ' Hev') as (l4 & l5 & Hl4 & Hl5 & D45).
  destruct (rel_modexp_at _ _ _ _ _ HH' HR1' _ _ H1') as (n5 & n6 & Hn5 & Hn6 & D56).
  repeat match goal with
         | E1 : eval_modexp _ _ ?E ?r ?a, E2 : eval_modexp _ _ ?E ?r ?b |- _ =>
             assert_fails (constr_eq a b); pose proof (functional_eval_modexp _ _ _ _ E1 E2); subst b
         end.
  exists g3 n6; [ exact Hg3 | exact Hn6 |].
  eapply per_dmod_trans; [ apply per_dmod_sym; exact D23 |].
  eapply per_dmod_trans; [ apply per_dmod_sym; exact D12 |].
  eapply per_dmod_trans; [ exact D14 |].
  eapply per_dmod_trans; [ exact D45 | exact D56 ].
Qed.

(** ** Walking Two Related Bodies *)

(** The name of an entry a body has a prefix up to is one of its names. *)
Lemma prefix_in_names : forall Φ y P, gm_prefix_upto Φ y = Some P -> List.In y (gm_names Φ).
Proof.
  induction Φ as [| Φ IH z E | Φ IH H its Φg _]; intros * Hp; cbn in Hp |- *; try discriminate.
  - destruct (String.eqb_spec y z) as [-> | Hne]; [ left; reflexivity | right; eauto ].
  - destruct (existsb _ _); [ discriminate | apply in_or_app; right; eauto ].
Qed.

(** A prefix of a body is one of the body extended by an entry of another
    name. *)
Lemma prefix_ext_keep : forall Φ z E y P, List.NoDup (gm_names (gm_ext Φ z E)) ->
    gm_prefix_upto Φ y = Some P -> gm_prefix_upto (gm_ext Φ z E) y = Some P.
Proof.
  intros * Hn Hp; cbn [gm_names] in Hn; inversion Hn as [| ? ? Hz _]; subst.
  cbn [gm_prefix_upto]; destruct (String.eqb_spec y z) as [-> | _]; [| exact Hp ].
  exfalso; exact (Hz (prefix_in_names _ _ _ Hp)).
Qed.

(** A type of a sort, of a kind [r] at every environment of its context,
    is a type of [r]'s sort ([abs_kind_sort]).  A type of [LevelSort] is of
    the kind of levels only. *)
Lemma rel_exp_abs_kind_sort_of_kind : forall Γ A S r, ⊨ Γ -> type_sort S -> Γ ⊨ A : S ->
    (forall R, EF Γ ≈ Γ ∈ per_ctx_env ↘ R -> forall ρ, R ρ ρ -> rel_typ_kind A ρ r) ->
    exists i, Γ ⊨ A : abs_kind_sort r Typeω@i.
Proof.
  intros * HΓ HS HA Hr; destruct HS as [i | |].
  - exact (rel_exp_sort_of_kind _ _ _ r (type_sort_universe i) ltac:(discriminate) HA Hr).
  - exact (rel_exp_sort_of_kind _ _ _ r type_sort_prop ltac:(discriminate) HA Hr).
  - exists 0; destruct r; cbn [abs_kind_sort]; [| | exact HA ].
    all: first [ apply rel_exp_of_typ | apply rel_exp_of_prop ].
    all: destruct (rel_ctx_wf_per_ctx_env HΓ) as [R HR].
    all: exists R, HR; intros Γ' R' HR' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'; exfalso.
    all: assert (Hρσ : R ρσ ρ'σ') by (eapply rel_sub_under_ctx_at'; eassumption).
    all: assert (HP : PER R) by (eapply per_env_PER; exact HR).
    all: destruct (Hr _ HR ρσ ltac:(etransitivity; [ exact Hρσ | symmetry; exact Hρσ ])) as (a & Ea & Hra).
    all: destruct (rel_exp_of_level_sort_kind_at HR HA _ _ Hρσ) as (b & Eb & Hrb).
    all: pose proof (functional_eval_exp _ _ _ _ Ea Eb) as <-; congruence.
Qed.

(** The definitions of a body without opens are of their tagged sorts in
    the context the body before each makes, once each, filled in, is of its
    tagged sort over the body's context: at an environment of the body
    before it, the type is read as the type filled in is at the tail
    ([fill_rel_back]).  This turns the premises of the typing of a body
    unit, which type its definitions filled in, into [body_sorts_valid]. *)
Lemma body_sorts_valid_of_fill : forall Φ D, gm_nopens Φ = 0 -> body_shape Φ Φ -> List.NoDup (gm_names Φ) ->
    ⊨ body_ctx Φ ++ D -> gmod_scoped (List.length D) Φ ->
    (forall y Φ0 E A M σ, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) -> gm_fill Φ0 = Some σ ->
       exists i, D ⊨ A[σ] : abs_kind_sort (entry_kind E) Typeω@i) ->
    body_sorts_valid Φ D.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its Φg _]; intros * Hn Hs Hnd HC Hsc Hf; cbn [body_sorts_valid gm_nopens] in *; [ exact I | | discriminate ].
  cbn [body_shape] in Hs; destruct Hs as (Hs0 & _ & HsE).
  cbn [gmod_scoped] in Hsc; destruct Hsc as [Hsc0 _].
  assert (HC0 : ⊨ body_ctx Φ ++ D) by (destruct E as [? ? ? ? [] | | | |]; cbn in HsE; try contradiction; exact (rel_ctx_wf_tail HC)).
  split.
  - apply (IH _ Hn Hs0 ltac:(cbn [gm_names] in Hnd; inversion Hnd; assumption) HC0 Hsc0).
    intros y' Φ0 E' A M σ Hp HE' Hf0; exact (Hf y' Φ0 E' A M σ (prefix_ext_keep _ _ _ _ _ Hnd Hp) HE' Hf0).
  - intros A M HE.
    destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; [| exfalso; exact (proj1 (body_shape_fill _ _ Hn Hs0) Hf0) ].
    destruct (Hf y Φ E A M σ0 ltac:(cbn [gm_prefix_upto]; rewrite String.eqb_refl; reflexivity) HE Hf0) as [i' Hi].
    (* the type, of a sort over the body before it *)
    assert (HAS : exists Srt, type_sort Srt /\ body_ctx Φ ++ D ⊨ A : Srt).
    { destruct E as [b pv r A' [M' |] | | | pv A' M' U |]; cbn in HE; try discriminate; injection HE as <- <-;
        cbn [body_ctx app] in HC.
      - exact (proj1 (rel_ctx_wf_def_inv HC)).
      - destruct (rel_ctx_wf_dm_inv HC) as ([k Hk] & _ & _); exists Typeω@k; split; [ apply type_sort_universe | exact Hk ]. }
    destruct HAS as (Srt & HS & HA).
    pose proof (gsub_valid (fill_gsub _ _ _ Hn Hf0 HC0 Hsc0)) as Hτ.
    apply (rel_exp_abs_kind_sort_of_kind _ _ _ _ HC0 HS HA).
    intros R HR ρ Hρ.
    destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_app_r _ _ HC0)) as [RD HD].
    destruct (fill_rel_back _ _ _ Hn Hf0 HC0 Hsc0 _ _ HD HR _ Hρ) as (Htail & ρσ & Hσ & Hρσ).
    destruct (rel_exp_of_abs_kind_sort_at HD Hi _ _ Htail) as (a & Ea & Hra).
    destruct (rel_type_of_sort HS HA) as [k HAk].
    destruct (rel_type_inversion_simple_at HR HAk _ _ Hρσ) as (a1 & a2 & Ea1 & Ea2 & [R12 H12]).
    pose proof (rel_type_sub_kind HS HA Hτ HD Htail Hσ Ea Ea2) as Erel.
    exists a1; split; [ exact Ea1 |].
    rewrite (per_univ_elem_kind _ _ _ _ H12), <- Erel; exact Hra.
Qed.

(** The prefix of a valid body is valid. *)
Lemma body_prefix_rel_ctx_wf : forall Φx0 y E C, ⊨ body_ctx (gm_ext Φx0 y E) ++ C -> ⊨ body_ctx Φx0 ++ C.
Proof. intros * H; destruct E as [? ? ? ? [] | | | |]; exact (rel_ctx_wf_tail H). Qed.

(** Two expanded bodies of one shape, each read in its parameters'
    context, related entry by entry through their filled-in entries.  The
    definitions may be of any relevant sort, a universe or [LevelSort], or
    propositions. *)
Lemma rel_expanded_bodies : forall Φx Φx' C C' RC RC',
    gm_noopen Φx -> gm_noopen Φx' ->
    body_shape Φx Φx' -> body_shape Φx Φx -> body_shape Φx' Φx' ->
    List.NoDup (gm_names Φx) -> List.NoDup (gm_names Φx') ->
    ⊨ body_ctx Φx ++ C -> ⊨ body_ctx Φx' ++ C' ->
    body_sorts_valid Φx C -> body_sorts_valid Φx' C' ->
    gmod_scoped (List.length C) Φx -> gmod_scoped (List.length C') Φx' ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       (exists i, C ⊨ A[σ] ≈ A'[σ'] : abs_kind_sort (entry_kind E) Typeω@i) /\
       C ⊨ M[σ] ≈ M'[σ'] : A[σ]) ->
    (forall y Φ0 E U Φ0' E' U' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
       C ⊨ᵐ me_lit U[σ]ᵘ ≈ me_lit U'[σ']ᵘ) ->
    EF C ≈ C ∈ per_ctx_env ↘ RC -> EF C' ≈ C' ∈ per_ctx_env ↘ RC' ->
    forall ρa ρa', RC ρa ρa' -> RC' ρa' ρa' ->
    per_body ρa Φx ρa' Φx'.
Proof.
  induction Φx as [| Φx IH y E | Φx IH H its Φg _]; intros [| Φx' y' E' | Φx' H' its' Φg'] * Hn Hn' Hs Hsx Hsx' Hnd Hnd' HC HC'
    Hsv Hsv' Hsc Hsc' HD HU HRC HRC' ρa ρa' Hρ Hρ'; cbn [body_shape gm_noopen] in Hs, Hn, Hn'; try contradiction.
  - constructor.
  - destruct Hs as (Hs & <- & HE).
    cbn [body_shape] in Hsx, Hsx'; destruct Hsx as (Hsx & _ & HsE); destruct Hsx' as (Hsx' & _ & HsE').
    pose proof Hnd as Hnd0; cbn [gm_names] in Hnd0; inversion Hnd0 as [| ? ? _ Hnd00]; subst.
    pose proof Hnd' as Hnd0'; cbn [gm_names] in Hnd0'; inversion Hnd0' as [| ? ? _ Hnd00']; subst.
    pose proof (body_prefix_rel_ctx_wf _ _ _ _ HC) as HC0; pose proof (body_prefix_rel_ctx_wf _ _ _ _ HC') as HC0'.
    pose proof (proj1 Hsc) as Hsc0; pose proof (proj1 Hsc') as Hsc0'.
    pose proof (IH _ _ _ _ _ Hn Hn' Hs Hsx Hsx' Hnd00 Hnd00' HC0 HC0' (proj1 Hsv) (proj1 Hsv') Hsc0 Hsc0'
                ltac:(intros * H1 H2 H3 H4 H5 H6; eapply HD;
                        [ exact (prefix_ext_keep _ _ _ _ _ Hnd H1) | exact H2 | exact (prefix_ext_keep _ _ _ _ _ Hnd' H3)
                        | exact H4 | exact H5 | exact H6 ])
                ltac:(intros * H1 H2 H3 H4 H5 H6; eapply HU;
                        [ exact (prefix_ext_keep _ _ _ _ _ Hnd H1) | exact H2 | exact (prefix_ext_keep _ _ _ _ _ Hnd' H3)
                        | exact H4 | exact H5 | exact H6 ])
                HRC HRC' _ _ Hρ Hρ') as Hb.
    (* the entries before, filled in, against their environments *)
    pose proof (gm_noopen_nopens _ Hn) as Hn0; pose proof (gm_noopen_nopens _ Hn') as Hn0'.
    destruct (gm_fill Φx) as [σ0 |] eqn:Hf0; [| exfalso; exact (proj1 (body_shape_fill _ _ Hn0 Hsx) Hf0) ].
    destruct (gm_fill Φx') as [σ0' |] eqn:Hf0'; [| exfalso; exact (proj1 (body_shape_fill _ _ Hn0' Hsx') Hf0') ].
    destruct (rel_ctx_wf_per_ctx_env HC0) as [R0 HR0]; destruct (rel_ctx_wf_per_ctx_env HC0') as [R0' HR0'].
    assert (HP : PER RC) by (eapply per_env_PER; exact HRC).
    assert (Hρρ : RC ρa ρa) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
    destruct (fill_rel _ _ _ Hn0 Hf0 HC0 (proj1 Hsv) Hsc0 _ _ HRC HR0 _ Hρρ) as (ρσ & ρ1 & Hev & Hb1 & H1).
    destruct (fill_rel _ _ _ Hn0' Hf0' HC0' (proj1 Hsv') Hsc0' _ _ HRC' HR0' _ Hρ') as (ρσ' & ρ1' & Hev' & Hb1' & H1').
    pose proof (gsub_valid (fill_gsub _ _ _ Hn0 Hf0 HC0 Hsc0)) as Hσ.
    pose proof (gsub_valid (fill_gsub _ _ _ Hn0' Hf0' HC0' Hsc0')) as Hσ'.
    assert (H11 : R0 ρ1 ρ1) by (assert (PER R0) by (eapply per_env_PER; exact HR0); etransitivity; [ symmetry; exact H1 | exact H1 ]).
    assert (H11' : R0' ρ1' ρ1') by (assert (PER R0') by (eapply per_env_PER; exact HR0'); etransitivity; [ symmetry; exact H1' | exact H1' ]).
    assert (Hp : gm_prefix_upto (gm_ext Φx y E) y = Some (gm_ext Φx y E)) by (cbn; rewrite String.eqb_refl; reflexivity).
    assert (Hp' : gm_prefix_upto (gm_ext Φx' y E') y = Some (gm_ext Φx' y E')) by (cbn; rewrite String.eqb_refl; reflexivity).
    destruct E as [b pv r A [M |] | pm U | | pv A M U | ], E' as [b' pv' r' A' [M' |] | pm' U' | | pv' A' M' U' | ];
      cbn in HE, HsE, HsE'; try contradiction.
    3: { (* a definition with a module part each: as a definition each and
            as a submodule each *)
      destruct (HD _ _ _ _ _ _ _ _ _ _ _ Hp eq_refl Hp' eq_refl Hf0 Hf0') as [[iA HAA'] HMM'].
      cbn [entry_kind abs_kind_sort] in HAA'.
      destruct (rel_ctx_wf_dm_inv HC) as ([i HA] & HM & HUd); destruct (rel_ctx_wf_dm_inv HC') as ([i' HA'] & HM' & HUd').
      pose proof (rel_type_evaluated_of_typ (rel_exp_under_ctx_refl_left HAA')) as HAσrel.
      pose proof (rel_type_of_typ HAA') as HAAt.
      edestruct typ_bridge as (a & a' & Ha & Ha' & [R HR]);
        [ exact (rel_type_of_typ HA) | exact Hσ | exact HRC | exact Hρ | exact HR0 | exact Hev | exact H1
        | exact HAAt
        | exact (rel_type_of_typ HA') | exact Hσ' | exact HRC' | exact Hρ' | exact HR0' | exact Hev' | exact H1' |].
      edestruct elem_bridge as (m & m' & Hm & Hm' & Hmm');
        [ exact (rel_type_of_typ HA) | exact (rel_type_evaluated_of_typ HA) | exact HM | exact Hσ | exact HRC | exact Hρ
        | exact HR0 | exact Hev | exact H1 | exact HAAt | exact HAσrel | exact HMM'
        | exact (rel_type_of_typ HA') | exact (rel_type_evaluated_of_typ HA') | exact HM' | exact Hσ' | exact HRC' | exact Hρ'
        | exact HR0' | exact Hev' | exact H1' | exact Ha | exact Ha' | exact HR |].
      pose proof (HU _ _ _ _ _ _ _ _ _ Hp eq_refl Hp' eq_refl Hf0 Hf0') as HUU'.
      pose proof (rel_unit_under_ctx_lit _ _ _ HUd) as HUv; pose proof (rel_unit_under_ctx_lit _ _ _ HUd') as HUv'.
      destruct (mod_bridge _ _ _ _ (me_lit U) (me_lit U') _ _ _ _ _ _ _ _ _ _ _ _
                  HUv Hσ HRC Hρ HR0 Hev H1 HUU' HUv' Hσ' HRC' Hρ' HR0' Hev' H1')
        as [h h' Hh Hh' Hhh].
      destruct U as [Δy Dy], U' as [Δy' Dy']; apply eval_me_lit_iff in Hh, Hh'.
      eapply per_body_dm; [ exact Hb | exact Hb1 | exact Hb1' | econstructor; eassumption
                          | right; econstructor; eassumption | exact Hh | exact Hh' | exact Hhh ]. }
    + (* a definition each, of the sort both are tagged with *)
      destruct HE as (_ & _ & _ & <-).
      destruct (HD _ _ _ _ _ _ _ _ _ _ _ Hp eq_refl Hp' eq_refl Hf0 Hf0') as [[iA HAA'] HMM'].
      cbn [entry_kind] in HAA'.
      destruct (proj2 Hsv _ _ eq_refl) as [ia HA]; destruct (proj2 Hsv' _ _ eq_refl) as [ia' HA'].
      destruct (rel_ctx_wf_def_inv HC) as [_ HM]; destruct (rel_ctx_wf_def_inv HC') as [_ HM'].
      pose proof (rel_exp_of_abs_kind_sort_at HR0 HA _ _ H11) as HSl.
      pose proof (rel_exp_of_abs_kind_sort_at HR0' HA' _ _ H11') as HSr.
      destruct (evaluated_kind_or_propositional r) as [Hr | ->]; [| cbn [abs_kind_sort] in HA, HA', HAA' ].
      * assert (HSi : relevant_sort (abs_kind_sort r Typeω@ia)) by (destruct Hr; constructor).
        assert (HSi' : relevant_sort (abs_kind_sort r Typeω@ia')) by (destruct Hr; constructor).
        assert (HSrt : relevant_sort (abs_kind_sort r Typeω@iA)) by (destruct Hr; constructor).
        destruct (rel_type_of_relevant_sort HSi HA) as [[i HAt] HArel].
        destruct (rel_type_of_relevant_sort HSi' HA') as [[i' HAt'] HArel'].
        destruct (rel_type_of_relevant_sort HSrt (rel_exp_under_ctx_refl_left HAA')) as [_ HAσrel].
        destruct (rel_type_of_sort (relevant_sort_type_sort _ HSrt) HAA') as [j HAAt].
        edestruct typ_bridge as (a & a' & Ha & Ha' & [R HR]);
          [ exact HAt | exact Hσ | exact HRC | exact Hρ | exact HR0 | exact Hev | exact H1
          | exact HAAt
          | exact HAt' | exact Hσ' | exact HRC' | exact Hρ' | exact HR0' | exact Hev' | exact H1' |].
        edestruct elem_bridge as (m & m' & Hm & Hm' & Hmm');
          [ exact HAt | exact HArel | exact HM | exact Hσ | exact HRC | exact Hρ | exact HR0 | exact Hev | exact H1
          | exact HAAt | exact HAσrel | exact HMM'
          | exact HAt' | exact HArel' | exact HM' | exact Hσ' | exact HRC' | exact Hρ' | exact HR0' | exact Hev' | exact H1'
          | exact Ha | exact Ha' | exact HR |].
        eapply per_body_def; [ exact Hb | exact Hb1 | exact Hb1' | econstructor; eassumption
                             | exact HSl | exact HSr | right; econstructor; eassumption ].
      * (* proofs: their types related, nothing asked of the bodies *)
        edestruct typ_bridge as (a & a' & Ha & Ha' & [R HR]);
          [ exact (rel_type_of_prop 0 HA) | exact Hσ | exact HRC | exact Hρ | exact HR0 | exact Hev | exact H1
          | exact (rel_type_of_prop 0 HAA')
          | exact (rel_type_of_prop 0 HA') | exact Hσ' | exact HRC' | exact Hρ' | exact HR0' | exact Hev' | exact H1' |].
        eapply per_body_def; [ exact Hb | exact Hb1 | exact Hb1' | econstructor; eassumption
                             | exact HSl | exact HSr | left; reflexivity ].
    + (* a submodule each *)
      pose proof (HU _ _ _ _ _ _ _ _ _ Hp eq_refl Hp' eq_refl Hf0 Hf0') as HUU'.
      pose proof (rel_unit_under_ctx_lit _ _ _ (rel_ctx_wf_mod_inv HC)) as HUv; pose proof (rel_unit_under_ctx_lit _ _ _ (rel_ctx_wf_mod_inv HC')) as HUv'.
      destruct (mod_bridge _ _ _ _ (me_lit U) (me_lit U') _ _ _ _ _ _ _ _ _ _ _ _
                  HUv Hσ HRC Hρ HR0 Hev H1 HUU' HUv' Hσ' HRC' Hρ' HR0' Hev' H1')
        as [h h' Hh Hh' Hhh].
      destruct U as [Δy Dy], U' as [Δy' Dy']; apply eval_me_lit_iff in Hh, Hh'.
      eapply per_body_mod; [ exact Hb | exact Hb1 | exact Hb1' | exact Hh | exact Hh' | exact Hhh ].
Qed.

(** ** Related Closures *)

(** The heterogeneous relation of two extensions of one context, at the
    two sides. *)
Lemma ext_rel_sides : forall C C' R RC RC', EF C ≈ C' ∈ per_ctx_env ↘ R ->
    EF C ≈ C ∈ per_ctx_env ↘ RC -> EF C' ≈ C' ∈ per_ctx_env ↘ RC' ->
    forall ρ ρ', R ρ ρ' -> RC ρ ρ' /\ RC' ρ' ρ'.
Proof.
  intros * HR HRC HRC' ρ ρ' Hρ.
  assert (E1 : R <~> RC) by (eapply per_ctx_env_right_irrel; eassumption).
  assert (E2 : R <~> RC') by (eapply per_ctx_env_left_irrel; eassumption).
  split; [ apply E1, Hρ |].
  apply E2; eapply per_env_trans; [ exact HR | eapply per_env_sym; [ exact HR | exact Hρ ] | exact Hρ ].
Qed.

(** The parameters of two units, outermost first: [ts] and [ts'] are the
    telescopes reversed, each well formed, so that each parameter's type
    is of the kind its entry is tagged with.  The closures still lacking
    parameters store their definitions expanded ([moddef_expand]). *)
Lemma walk_params : forall ts ts' Γ Γ' RΓ R D D',
    tele_ass ts -> tele_ass ts' -> List.length ts = List.length ts' ->
    ⊨ rev ts ++ Γ -> ⊨ rev ts' ++ Γ' ->
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ RΓ ->
    EF rev ts ++ Γ ≈ rev ts' ++ Γ' ∈ per_ctx_env ↘ R ->
    (forall ρ ρ', R ρ ρ' -> exists h h', ⟦ nil ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ h /\
                                     ⟦ nil ⊢ D' ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h' /\ per_dmod h h') ->
    forall ρ ρ', RΓ ρ ρ' -> exists h h', ⟦ rev ts ⊢ D ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ ↘ h /\
                                     ⟦ rev ts' ⊢ D' ⟧ᶜ gc_deps ⍮ gc_stack ⍮ ρ' ↘ h' /\ per_dmod h h'.
Proof.
  induction ts as [| e ts IH]; intros [| e' ts'] * Hts Hts' Hl HW HW' HΓ HR HD ρ ρ' Hρ; cbn in Hl; try discriminate.
  - apply HD.
    assert (HRR : R <~> RΓ) by (eapply per_ctx_env_right_irrel; eassumption).
    apply HRR, Hρ.
  - inversion Hts as [| ? ? (κ & A & ->) Hts0]; inversion Hts' as [| ? ? (κ' & A' & ->) Hts0']; subst.
    cbn [rev] in HR, HW, HW' |- *.
    rewrite <- !app_assoc in HR; rewrite <- !app_assoc in HW; rewrite <- !app_assoc in HW'; cbn [app] in HR, HW, HW'.
    destruct (per_ctx_env_app_tail (rev ts) (rev ts') _ _ _ ltac:(rewrite !length_rev; congruence) HR)
      as [R1 HR1].
    assert (κ' = κ) as -> by (inversion HR1; reflexivity).
    destruct (per_ctx_env_cons_clean_inversion HΓ HR1) as (i & head_rel & Hhead & HE).
    destruct (Hhead _ _ Hρ) as [a a' Ha Ha' HRa].
    (** Each parameter's type is of its tagged kind. *)
    pose proof (rel_ctx_wf_app_r _ _ HW) as HWA; pose proof (rel_ctx_wf_app_r _ _ HW') as HWA'.
    destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_tail HWA)) as [R0 HR0].
    destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_tail HWA')) as [R0' HR0'].
    destruct (ext_rel_sides _ _ _ _ _ HΓ HR0 HR0' _ _ Hρ) as [H0 H0'].
    destruct (rel_ctx_wf_ass_kind HWA _ HR0 _ _ H0) as (a0 & Ea0 & Ka).
    destruct (rel_ctx_wf_ass_kind HWA' _ HR0' _ _ H0') as (a0' & Ea0' & Ka').
    pose proof (functional_eval_exp _ _ _ _ Ea0 Ha) as ->; pose proof (functional_eval_exp _ _ _ _ Ea0' Ha') as ->.
    eexists _, _; split; [ apply close_unsat; rewrite length_app; cbn; lia |].
    split; [ apply close_unsat; rewrite length_app; cbn; lia |].
    eapply per_dmod_closure_step; [ exact Ha | exact Ha' | exact HRa | exact Ka | exact Ka' |].
    intros c c' Hc.
    pose proof (entry_readable_of_elem_closure Ha Ha' HRa Hc) as [Rc Rc'].
    destruct (IH _ _ _ _ _ D D' Hts0 Hts0' ltac:(congruence) HW HW' HR1 HR HD (ρ ↦ c ⦂ entry_type_closure A ρ) (ρ' ↦ c' ⦂ entry_type_closure A' ρ'))
      as (h & h' & Hh & Hh' & Hhh).
    + apply HE; apply (mk_per_ctx_env_cons_rel _ _ _ _ (ρ ↦ c ⦂ entry_type_closure A ρ) (ρ' ↦ c' ⦂ entry_type_closure A' ρ') Hρ);
        [ exact Hc | intros _; eexists; reflexivity | intros _; eexists; reflexivity
        | split; [ exact Rc | cbn; lia ] | split; [ exact Rc' | cbn; lia ] ].
    + exists h, h'; rewrite !eval_close_expand_iff; split; [ exact Hh | split; [ exact Hh' | exact Hhh ] ].
Qed.

(** Two body units, related entry by entry along their expansions. *)
Section BodyRel.
  Variables (Γ Δ Δ' : ctx) (Φ Φ' Φx Φx' : gmod).
  Hypotheses (HΔ : Γ ⊨ˣ Δ ≈ Δ') (Ha : tele_ass Δ) (Ha' : tele_ass Δ') (Hl : List.length Δ = List.length Δ')
    (Hx : body_xp Θm Ξm (Δ ++ Γ) Φ Φx) (Hx' : body_xp Θm Ξm (Δ' ++ Γ) Φ' Φx')
    (Hsxx : body_shape Φx Φx') (Hsx : body_shape Φx Φx) (Hsx' : body_shape Φx' Φx')
    (Hnd : List.NoDup (gm_names Φx)) (Hnd' : List.NoDup (gm_names Φx'))
    (HC : ⊨ body_ctx Φx ++ Δ ++ Γ) (HC' : ⊨ body_ctx Φx' ++ Δ' ++ Γ)
    (Hsvb : body_sorts_valid Φx (Δ ++ Γ)) (Hsvb' : body_sorts_valid Φx' (Δ' ++ Γ))
    (Hscb : gmod_scoped (List.length (Δ ++ Γ)) Φx) (Hscb' : gmod_scoped (List.length (Δ' ++ Γ)) Φx').
  Hypothesis HD : forall y Φ0 E A M Φ0' E' A' M' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      (exists i, Δ ++ Γ ⊨ A[σ] ≈ A'[σ'] : abs_kind_sort (entry_kind E) Typeω@i) /\
      Δ ++ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ].
  Hypothesis HU : forall y Φ0 E U Φ0' E' U' σ σ',
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
      gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
      gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
      Δ ++ Γ ⊨ᵐ me_lit U[σ]ᵘ ≈ me_lit U'[σ']ᵘ.

  (** The closures of the two units over related environments are
      related. *)
  Lemma rel_closure_body : forall RΓ, EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
      forall ρ ρ', RΓ ρ ρ' -> rel_modexp_evals (me_lit (gu_open Δ Φ)) ρ (me_lit (gu_open Δ' Φ')) ρ'.
  Proof.
    intros RΓ HΓ ρ ρ' Hρ.
    pose proof (body_xp_expand _ _ _ _ _ Hx) as HxE; pose proof (body_xp_expand _ _ _ _ _ Hx') as HxE'.
    pose proof (body_xp_result_noopen _ _ _ _ _ Hx) as Hn; pose proof (body_xp_result_noopen _ _ _ _ _ Hx') as Hn'.
    destruct HΔ as [HΔΓ HΔ'Γ [Rh HRh]].
    destruct (rel_ctx_wf_per_ctx_env HΔΓ) as [RC HRC]; destruct (rel_ctx_wf_per_ctx_env HΔ'Γ) as [RC' HRC'].
    rewrite <- (rev_involutive Δ), <- (rev_involutive Δ') in HRh.
    destruct (walk_params (rev Δ) (rev Δ') Γ Γ RΓ Rh (md_body sm_open Φ) (md_body sm_open Φ')
                (Forall_rev Ha) (Forall_rev Ha') ltac:(rewrite !length_rev; exact Hl)
                ltac:(rewrite rev_involutive; exact HΔΓ) ltac:(rewrite rev_involutive; exact HΔ'Γ) HΓ HRh
                ltac:(intros ρa ρa' Hρa; rewrite !rev_involutive in HRh;
                      destruct (ext_rel_sides _ _ _ _ _ HRh HRC HRC' _ _ Hρa) as [H1 H2];
                      pose proof (rel_expanded_bodies _ _ _ _ _ _ Hn Hn' Hsxx Hsx Hsx' Hnd Hnd' HC HC' Hsvb Hsvb' Hscb Hscb' HD HU HRC HRC' _ _ H1 H2)
                        as Hb;
                      eexists _, _; split; [ apply eval_close_body | split; [ apply eval_close_body |] ];
                      apply per_dmod_body; rewrite <- HxE, <- HxE'; exact Hb)
                _ _ Hρ)
      as (h & h' & Hh & Hh' & Hhh).
    rewrite !rev_involutive in Hh, Hh'.
    exists h h'; [ apply eval_me_lit; exact Hh | apply eval_me_lit; exact Hh' | exact Hhh ].
  Qed.

  (** The two units are related, along substitutions too. *)
  Lemma rel_lit_body : Γ ⊨ᵐ me_lit (gu_open Δ Φ) ≈ me_lit (gu_open Δ' Φ').
  Proof.
    pose proof (rel_ctx_wf_app_r _ _ (rel_ctx_wf_app_r _ _ HC)) as HΓs.
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HΓ].
    refine (mk_rel_modexp_under_ctx _ _ _ RΓ HΓ _); intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
    assert (HP' : PER R') by (eapply per_env_PER; exact HΓ').
    assert (Hρρ : R' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
    assert (Hρ'ρ' : R' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
    pose proof (rel_sub_under_ctx_at' Hσ HΓ' HΓ _ _ _ _ Hρ Hev Hev') as Hρσ.
    destruct (unit_sub_link_body _ _ _ _ _ _ _ _ _ _ Ha Hx Hsx HC Hsvb Hscb Hσ HΓ' Hρρ Hev) as [v1 v2 Hv1 Hv2 V12].
    destruct (unit_sub_link_body _ _ _ _ _ _ _ _ _ _ Ha' Hx' Hsx' HC' Hsvb' Hscb' (rel_sub_under_ctx_refl_right Hσ) HΓ' Hρ'ρ' Hev')
      as [v4 v3 Hv4 Hv3 V43].
    destruct (rel_closure_body _ HΓ _ _ Hρσ) as [w2 w3 Hw2 Hw3 W23].
    pose proof (functional_eval_modexp _ _ _ _ Hw2 Hv2) as ->; pose proof (functional_eval_modexp _ _ _ _ Hw3 Hv3) as ->.
    apply (mk_rel_modexp v1 v2 v3 v4); try assumption.
    split; [ exact V12 | split; [ exact W23 | apply per_dmod_sym; exact V43 ] ].
  Qed.
End BodyRel.

(** The closures of two related aliases over related environments are
    related. *)
Lemma rel_closure_alias : forall Γ Δ Δ' E E' RΓ,
    Γ ⊨ˣ Δ ≈ Δ' -> tele_ass Δ -> tele_ass Δ' -> List.length Δ = List.length Δ' ->
    Δ ++ Γ ⊨ᵐ E ≈ E' -> EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ ->
    forall ρ ρ', RΓ ρ ρ' -> rel_modexp_evals (me_lit (gu_mk Δ (md_alias E))) ρ (me_lit (gu_mk Δ' (md_alias E'))) ρ'.
Proof.
  intros * HΔ Ha Ha' Hl HE HΓ ρ ρ' Hρ.
  destruct HΔ as [HΔΓ HΔ'Γ [Rh HRh]].
  destruct (rel_ctx_wf_per_ctx_env HΔΓ) as [RC HRC]; destruct (rel_ctx_wf_per_ctx_env HΔ'Γ) as [RC' HRC'].
  pose proof HRh as HRh0.
  rewrite <- (rev_involutive Δ), <- (rev_involutive Δ') in HRh.
  destruct (walk_params (rev Δ) (rev Δ') Γ Γ RΓ Rh (md_alias E) (md_alias E')
              (Forall_rev Ha) (Forall_rev Ha') ltac:(rewrite !length_rev; exact Hl)
                ltac:(rewrite rev_involutive; exact HΔΓ) ltac:(rewrite rev_involutive; exact HΔ'Γ) HΓ HRh
              ltac:(intros ρa ρa' Hρa;
                    destruct (ext_rel_sides _ _ _ _ _ HRh0 HRC HRC' _ _ Hρa) as [H1 _];
                    destruct (rel_modexp_at _ _ _ _ _ HE HRC _ _ H1) as (h & h' & Hh & Hh' & Hhh);
                    exists h, h'; split; [ apply eval_close_alias0; exact Hh | split; [ apply eval_close_alias0; exact Hh' | exact Hhh ] ])
              _ _ Hρ)
    as (h & h' & Hh & Hh' & Hhh).
  rewrite !rev_involutive in Hh, Hh'.
  exists h h'; [ apply eval_me_lit; exact Hh | apply eval_me_lit; exact Hh' | exact Hhh ].
Qed.

(** Two related aliases are related, along substitutions too. *)
Lemma rel_lit_alias : forall Γ Δ Δ' E E',
    Γ ⊨ˣ Δ ≈ Δ' -> tele_ass Δ -> tele_ass Δ' -> List.length Δ = List.length Δ' ->
    Δ ++ Γ ⊨ᵐ E ≈ E' -> Δ' ++ Γ ⊨ᵐ E' ≈ E' ->
    Γ ⊨ᵐ me_lit (gu_mk Δ (md_alias E)) ≈ me_lit (gu_mk Δ' (md_alias E')).
Proof.
  intros * HΔ Ha Ha' Hl HE HE'.
  pose proof HΔ as [HΔΓ HΔ'Γ _].
  destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_app_r _ _ HΔΓ)) as [RΓ HΓ].
  refine (mk_rel_modexp_under_ctx _ _ _ RΓ HΓ _); intros Γ' R' HΓ' σ σ' Hσ ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  assert (HP' : PER R') by (eapply per_env_PER; exact HΓ').
  assert (Hρρ : R' ρ ρ) by (etransitivity; [ exact Hρ | symmetry; exact Hρ ]).
  assert (Hρ'ρ' : R' ρ' ρ') by (etransitivity; [ symmetry; exact Hρ | exact Hρ ]).
  pose proof (rel_sub_under_ctx_at' Hσ HΓ' HΓ _ _ _ _ Hρ Hev Hev') as Hρσ.
  destruct (unit_sub_link_alias _ _ _ _ _ _ _ _ _ Ha HΔΓ (rel_modexp_refl_left HE) Hσ HΓ' Hρρ Hev) as [v1 v2 Hv1 Hv2 V12].
  destruct (unit_sub_link_alias _ _ _ _ _ _ _ _ _ Ha' HΔ'Γ HE' (rel_sub_under_ctx_refl_right Hσ) HΓ' Hρ'ρ' Hev')
    as [v4 v3 Hv4 Hv3 V43].
  destruct (rel_closure_alias _ _ _ _ _ _ HΔ Ha Ha' Hl HE HΓ _ _ Hρσ) as [w2 w3 Hw2 Hw3 W23].
  pose proof (functional_eval_modexp _ _ _ _ Hw2 Hv2) as ->; pose proof (functional_eval_modexp _ _ _ _ Hw3 Hv3) as ->.
  apply (mk_rel_modexp v1 v2 v3 v4); try assumption.
  split; [ exact V12 | split; [ exact W23 | apply per_dmod_sym; exact V43 ] ].
Qed.

End Fixed_GCtx.
