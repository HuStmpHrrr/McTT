(** * Member Types Are Types, and Reducts Inhabit Them

    The canonical type of a member of a well-formed module expression is a
    type, and its δ-reduct, when it has one, inhabits it ([member_wf]).  The
    rules of the core do not need this, since [wf_mem] carries both facts as
    premises; a checker does, since it cannot check either of them by
    recursion on the term.  The argument of a module application is checked
    against the domain of the module's arity, and the domain of a member's
    type agrees with it, which the PER model shows ([app_domain]). *)

From Stdlib Require Import Lia List.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export Consequences.
From Mctt.Core.Semantic Require Import Realizability Evaluation.Modules.
From Mctt.Core.Completeness Require Import UniverseCases MemberReps MemberSem PathCases GlobalSem ModuleCases.
From Mctt.Core.Syntactic.System Require Import MemberWf.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Types Below a Universe *)

Lemma pi_typ_absurd : forall Γ A B i k, Γ ⊢ Π A B ≈ Type@i : Type@k -> False.
Proof.
  intros * H.
  destruct (completeness_ty H) as [W [HW1 HW2]].
  inversion HW1; subst; inversion HW2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  congruence.
Qed.

Lemma subtyp_univ_inv : forall Γ X i, Γ ⊢ X ⊆ Type@i -> exists j k, j <= i /\ Γ ⊢ X ≈ Type@j : Type@k.
Proof.
  intros * H.
  destruct (subtyp_spec H) as [[k Hk] | [(j & j' & [k Hk] & [k' Hk'] & Hle) | (A1 & A2 & B1 & B2 & _ & [k Hk] & _)]].
  - exists i, k; split; [ lia | exact Hk ].
  - pose proof (exp_eq_typ_implies_eq_level Hk') as ->.
    exists j, k; split; [ exact Hle | exact Hk ].
  - exfalso; eapply pi_typ_absurd; exact Hk.
Qed.


(** ** A Binding's Value, Read Back Through the Binding *)

(** Under [Γ ▸ D ≔ N], a term is equal to its instance at [N], weakened: the
    variable is equal to [N[↑]ʷ] by δ. *)
Lemma def_ctx_inst : forall Γ D N k X Y,
    Γ ⊢ D : Type@k -> Γ ⊢ N : D -> Γ ▸ D ≔ N ⊢ X : Y ->
    Γ ▸ D ≔ N ⊢ X ≈ X[Id,,N][↑]ʷ : Y.
Proof.
  intros * HD HN HX.
  assert (HC : ⊢ Γ ▸ D ≔ N) by mauto 3.
  assert (Hw : Γ ▸ D ≔ N ⊢s Wk : Γ) by mauto 3.
  assert (HNw : Γ ▸ D ≔ N ⊢ N[Wk] : D[Wk]) by mauto 3.
  assert (Hσ : Γ ▸ D ≔ N ⊢s Wk ,, N[Wk] : Γ ▸ D ≔ N)
    by (eapply wf_sub_extend_def; [ exact Hw | exact HD | exact HN | exact HNw | eapply wf_exp_eq_refl; exact HNw ]).
  replace (X[Id,,N][↑]ʷ) with (X[Wk ,, N[Wk]]).
  2:{ rewrite exp_wk_sub; apply exp_sub_sb_eq; intros [| x]; cbn; [ rewrite exp_sub_of_shift | ]; reflexivity. }
  assert (Heq : Γ ▸ D ≔ N ⊢s Id ≈ Wk ,, N[Wk] : Γ ▸ D ≔ N).
  { constructor; [ mauto 3 | exact Hσ |].
    intros [| x] B Hx; inversion Hx; subst; cbn [sentry_exp sb_id sb_extend exp_sub]; rewrite ?exp_sub_id.
    - rewrite exp_sub_of_shift. eapply wf_exp_eq_var_delta; [ exact HC | constructor ].
    - apply wf_exp_eq_refl; mauto 3. }
  pose proof (sub_eq_preserves_exp _ _ _ _ _ HX _ _ _ Heq) as H'.
  rewrite !exp_sub_id in H'; exact H'.
Qed.



(** Under [Γ ▹ₘ U], a term is equal to its instance at the literal [⌜U⌝],
    weakened: equal substitutions agree on terms only, and the slot is not a
    term. *)
Lemma mod_ctx_inst : forall Γ U X Y,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> Γ ▹ₘ U ⊢ X : Y ->
    Γ ▹ₘ U ⊢ X ≈ X[Id ,,ₘ me_lit U][↑]ʷ : Y.
Proof.
  intros * HU HX.
  assert (HC : ⊢ Γ ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU).
  assert (Hw : Γ ▹ₘ U ⊢s Wk : Γ) by mauto 3.
  assert (Hσ : Γ ▹ₘ U ⊢s Wk ,,ₘ me_lit U[Wk]ᵘ : Γ ▹ₘ U)
    by (eapply wf_sub_extend_mod; [ exact Hw | exact HU | eapply sub_preserves_unit; eassumption ]).
  replace (X[Id ,,ₘ me_lit U][↑]ʷ) with (X[Wk ,,ₘ me_lit U[Wk]ᵘ]).
  2:{ rewrite exp_wk_sub; apply exp_sub_sb_eq; intros [| x]; cbn; [| reflexivity ].
      rewrite (gunit_sub_of_wk_ext _ _ _ (symmetry sb_of_wk_shift)); reflexivity. }
  assert (Heq : Γ ▹ₘ U ⊢s Id ≈ Wk ,,ₘ me_lit U[Wk]ᵘ : Γ ▹ₘ U).
  { constructor; [ mauto 3 | exact Hσ |].
    intros [| x] B Hx; inversion Hx; subst; cbn [sentry_exp sb_id sb_extend exp_sub]; rewrite ?exp_sub_id.
    apply wf_exp_eq_refl; mauto 3. }
  pose proof (sub_eq_preserves_exp _ _ _ _ _ HX _ _ _ Heq) as H'.
  rewrite !exp_sub_id in H'; exact H'.
Qed.

(** ** Local Bindings at the Level of Types *)

Lemma typ_let_inv : forall Γ D N T i, Γ ⊢ ℓ D ≔ N in T : Type@i ->
    (exists k, Γ ⊢ D : Type@k) /\ Γ ⊢ N : D /\ Γ ▸ D ≔ N ⊢ T : Type@i.
Proof.
  intros * H.
  destruct (wf_let_inversion H) as (k & C & HD & HN & HT & Hsub).
  destruct (subtyp_univ_inv _ _ _ Hsub) as (j & k' & Hle & HCj).
  split; [ eauto | split; [ exact HN |] ].
  assert (exists l, Γ ▸ D ≔ N ⊢ C : Type@l) as [l HCt] by (gen_presups; eauto).
  pose proof (def_ctx_inst _ _ _ _ _ _ HD HN HCt) as HCi.
  assert (⊢ Γ ▸ D ≔ N) by mauto 3.
  assert (HCw : Γ ▸ D ≔ N ⊢ C[Id,,N][↑]ʷ ≈ Type@j[↑]ʷ : Type@k'[↑]ʷ)
    by (eapply wk_preserves_exp_eq; [ exact HCj | mauto 3 ]).
  cbn in HCw.
  assert (Γ ▸ D ≔ N ⊢ C ≈ Type@j : Type@(max l k')) by mauto 4 using lift_exp_eq_max_left, lift_exp_eq_max_right.
  eapply lift_exp_ge; [ exact Hle |]; mauto 3.
Qed.


Lemma typ_let_mod_inv : forall Γ U T i, Γ ⊢ ℓₘ U in T : Type@i ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U /\ Γ ▹ₘ U ⊢ T : Type@i.
Proof.
  intros * H.
  destruct (wf_let_mod_inversion H) as (C & HU & HT & Hsub).
  destruct (subtyp_univ_inv _ _ _ Hsub) as (j & k' & Hle & HCj).
  split; [ exact HU |].
  assert (exists l, Γ ▹ₘ U ⊢ C : Type@l) as [l HCt] by (gen_presups; eauto).
  pose proof (mod_ctx_inst _ _ _ _ HU HCt) as HCi.
  assert (⊢ Γ ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU).
  assert (HCw : Γ ▹ₘ U ⊢ C[Id ,,ₘ me_lit U][↑]ʷ ≈ Type@j[↑]ʷ : Type@k'[↑]ʷ)
    by (eapply wk_preserves_exp_eq; [ exact HCj | mauto 3 ]).
  cbn in HCw.
  assert (Γ ▹ₘ U ⊢ C ≈ Type@j : Type@(max l k')) by mauto 4 using lift_exp_eq_max_left, lift_exp_eq_max_right.
  eapply lift_exp_ge; [ exact Hle |]; mauto 3.
Qed.

(** ** The [Π] a Type Is *)

Lemma pi_view_wf : forall A Γ i B C, Γ ⊢ A : Type@i -> pi_view A = Some (B, C) ->
    Γ ⊢ A ≈ Π B C : Type@i /\ Γ ⊢ B : Type@i /\ Γ ▹ B ⊢ C : Type@i.
Proof.
  induction A; intros * HA Hp; cbn in Hp; try discriminate.
  - injection Hp as <- <-.
    destruct (wf_pi_inversion' HA) as [HB HC].
    split; [ mauto 3 | split; assumption ].
  - destruct b as [D N | U];
      (destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ]; injection Hp as <- <-).
    + destruct (typ_let_inv _ _ _ _ _ HA) as ([k HD] & HN & HT).
      destruct (IHA _ _ _ _ HT eq_refl) as (HTe & HB' & HC').
      pose proof (wf_sub_single_def _ _ _ _ _ _ HD HN) as Hσ.
      pose proof (sub_preserves_typ_eq _ _ _ _ _ _ _ _ HTe Hσ) as HTs; cbn in HTs.
      split; [| split ].
      * eapply wf_exp_eq_trans; [ eapply wf_exp_eq_let_zeta_typ; eassumption | exact HTs ].
      * eapply sub_preserves_typ; eassumption.
      * eapply sub_preserves_typ; [ exact HC' | eapply wf_sub_q'; eassumption ].
    + destruct (typ_let_mod_inv _ _ _ _ HA) as (HU & HT).
      destruct (IHA _ _ _ _ HT eq_refl) as (HTe & HB' & HC').
      pose proof (wf_sub_single_mod _ _ _ _ HU) as Hσ.
      pose proof (sub_preserves_typ_eq _ _ _ _ _ _ _ _ HTe Hσ) as HTs; cbn in HTs.
      split; [| split ].
      * eapply wf_exp_eq_trans; [ eapply wf_exp_eq_let_mod_zeta_typ; eassumption | exact HTs ].
      * eapply sub_preserves_typ; eassumption.
      * eapply sub_preserves_typ; [ exact HC' | eapply wf_sub_q'; eassumption ].
Qed.

(** ** The Outermost Parameter of an Arity

    An arity is typed by its arity type: its outermost parameter is a type,
    and instantiating it with an argument of that type leaves an arity. *)

Lemma tele_view_wf : forall Γ T i B T1, Γ ⊢ ctx_pi T ⊤ : Type@i -> tele_view T = Some (B, T1) ->
    Γ ⊢ ctx_pi T ⊤ ≈ Π B (ctx_pi T1 ⊤) : Type@i /\ Γ ⊢ B : Type@i /\ Γ ▹ B ⊢ ctx_pi T1 ⊤ : Type@i.
Proof.
  intros * HT Hv; apply pi_view_wf; [ exact HT | rewrite tele_view_pi, Hv; reflexivity ].
Qed.

Lemma tele_inst_wf : forall Γ T i N T', Γ ⊢ ctx_pi T ⊤ : Type@i -> tele_inst T N = Some T' ->
    (forall B T1, tele_view T = Some (B, T1) -> Γ ⊢ N : B) -> Γ ⊢ ctx_pi T' ⊤ : Type@i.
Proof.
  intros * HT Hi HN; unfold tele_inst in Hi.
  destruct (tele_view T) as [[B T1] |] eqn:Hv; [| discriminate ]; injection Hi as <-.
  destruct (tele_view_wf _ _ _ _ _ HT Hv) as (_ & HB & HC).
  pose proof (wf_sub_single _ _ _ _ _ _ HB (HN _ _ eq_refl)) as Hσ.
  pose proof (sub_preserves_typ _ _ _ _ _ _ _ HC Hσ) as H; rewrite ctx_pi_sub in H; exact H.
Qed.

(** ** Semantic Equality of Types, Read Back *)

Lemma sem_typ_eq_syn : forall Γ A A' i,
    Γ ⊢ A : Type@i -> Γ ⊢ A' : Type@i -> Γ ⊨ A ≈ A' : Type@i -> Γ ⊢ A ≈ A' : Type@i.
Proof.
  intros * HA HA' H.
  destruct (rel_exp_under_ctx_at_initial_env H)
    as [ρ [j [elem_rel [a [m [m' [Hρ [Ha [Hm [Hm' [Htyp Hrel]]]]]]]]]]].
  destruct (per_elem_then_per_top Htyp Hrel (length Γ)) as [W [HW HW']].
  assert (H1 : nbe_f Γ A Type@i W) by (econstructor; eassumption).
  assert (H2 : nbe_f Γ A' Type@i W) by (econstructor; eassumption).
  pose proof (soundness' HA H1); pose proof (soundness' HA' H2).
  eapply wf_exp_eq_trans; [ eassumption | eapply wf_exp_eq_sym; eassumption ].
Qed.


(** ** Arities Through an Application

    A module expression applied to an argument has a [Π] for its arity, and
    then every member type it has is a [Π] as well, syntactically: an
    argument is still missing at each of its members.  This is read off the
    PER model ([sem_mt]). *)

Lemma wf_modexp_sem_mt : forall Γ H, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    sem_mt gc_deps gc_stack Γ H /\ Γ ⊨ᵐ H ≈ H.
Proof.
  intros * HH.
  destruct kripke_fundamental as (_ & _ & _ & _ & _ & _ & Km).
  pose proof (gctx_sem _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH))) as Hid.
  destruct (Km _ _ _ _ _ HH _ _ Hid) as (HR & HS & _).
  destruct GC; split; assumption.
Qed.

Lemma pi_view_lets_some : forall Ψ X, lets_only Ψ ->
    (forall σ, exists B C, pi_view X[σ] = Some (B, C)) ->
    forall σ, exists B C, pi_view (ctx_pi Ψ X)[σ] = Some (B, C).
Proof.
  induction Ψ as [| e Ψ IH]; intros X HL HX σ; cbn [ctx_pi]; [ apply HX |].
  inversion HL as [| ? ? He HL']; subst.
  destruct e as [B0 | B0 M0 | U0]; [ exfalso; exact (He _ eq_refl) | |];
    (apply IH; [ exact HL' |]; intros σ'; cbn;
     destruct (HX (q σ')) as (B & C & ->); eauto).
Qed.

Lemma rep_pos_pi : forall D A k b, rep D A k b -> forall n, k = S n ->
    forall σ, exists B C, pi_view A[σ] = Some (B, C).
Proof.
  induction 1 as [D X i b HD HX Hb | D τ D0 Ψ Δp X m b Hg0 HΔ HΨ HC Hr IH];
    intros n Hk σ; [ discriminate |].
  rewrite exp_sub_sub.
  destruct Δp as [| e0 Δ0] eqn:EΔ.
  - cbn [List.length plus] in Hk; subst m.
    rewrite app_nil_r.
    apply pi_view_lets_some; [ exact HΨ |]; intros; eapply IH; reflexivity.
  - assert (Hne : e0 :: Δ0 <> nil) by discriminate.
    destruct (exists_last Hne) as (l & e & El).
    rewrite <- EΔ in *; rewrite El in *; clear El EΔ e0 Δ0 Hne.
    apply Forall_app in HΔ as [_ He].
    inversion He as [| ? ? [B0 ->] _]; subst.
    rewrite app_assoc, ctx_pi_app; cbn; eauto.
Qed.

Lemma app_arity_pi : forall Γ H T0 B0 T1,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_deps gc_stack Γ H nil (mr_mod T0) -> tele_view T0 = Some (B0, T1) ->
    forall ch R, member_type gc_deps gc_stack Γ H ch R -> (mres_kind R = mk_term -> ch <> nil) ->
    exists B' C', pi_view (mres_ty R) = Some (B', C').
Proof.
  intros * HH Hm0 Hv * Hm Hch.
  destruct (wf_modexp_sem_mt _ _ HH) as [[_ S2] _].
  destruct (S2 nil _ ch R Hm0 eq_refl Hm Hch) as (m & n & Hr0 & Hr & Hmn); cbn [mres_ty] in Hr0.
  assert (Hp : pi_view (ctx_pi T0 ⊤) = Some (B0, ctx_pi T1 ⊤)) by (rewrite tele_view_pi, Hv; reflexivity).
  destruct (rep_pos_of_pi _ _ _ Hr0 _ _ Hp) as [m' ->].
  destruct n as [| n']; [ lia |].
  destruct (rep_pos_pi _ _ _ _ Hr n' eq_refl Id) as (B' & C' & Hp').
  rewrite exp_sub_id in Hp'; eauto.
Qed.


(** ** Prefixes of Member Chains

    Each prefix of a member chain of a well-formed module is a module.  A
    chain from a unit need not be a module, since its prefix may be an open
    frame; there the prefixes beyond a module of the chain are modules
    ([mod_base]). *)

Definition mod_base (Γ : ctx) (H : modexp) (ch1 : list String.string) : Prop :=
  gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H \/
  (⊢ Γ /\ exists mq pre suf r0, mod_qname H = Some mq /\ ch1 = pre ++ suf /\
     gc_module gc_deps gc_stack (qname_app mq pre) = Some r0).

(** A well-formed chain from a unit is a module at its own path. *)
Lemma wf_chain_mt : forall Γ H mq, mod_qname H = Some mq -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    exists T0, member_type gc_deps gc_stack Γ H nil (mr_mod T0).
Proof.
  intros * Hp HH; pose proof (modexp_parts_of_wf _ _ _ _ HH) as Hparts.
  destruct H as [fp | x | H0 y | H0 N | U]; cbn in Hp, Hparts; try discriminate; [ exact Hparts |].
  destruct Hparts as [(_ & A0 & Hm) | (_ & Hm)]; [ exists A0; eapply mt_mem; [ discriminate | exact Hm ] | exact Hm ].
Qed.

Lemma chain_module : forall Γ H mq T0, mod_qname H = Some mq -> member_type gc_deps gc_stack Γ H nil (mr_mod T0) ->
    exists r0, gc_module gc_deps gc_stack mq = Some r0.
Proof.
  intros * Hp Hm; rewrite (mod_qname_inv _ _ Hp) in Hm; exact (member_type_path_module _ _ _ _ _ Hm).
Qed.

Lemma mod_base_unit : forall Γ fp ch1, mod_base Γ (me_unit fp) ch1 ->
    ⊢ Γ /\ exists pre suf r0, ch1 = pre ++ suf /\ gc_module gc_deps gc_stack (q_abs fp pre) = Some r0.
Proof.
  intros * [HH | (HΓ & mq & pre & suf & r0 & Hp & -> & Hq)].
  - split; [ exact (presup_modexp_eq_ctx HH) |].
    destruct (wf_chain_mt _ (me_unit fp) (q_abs fp nil) eq_refl HH) as [A0 Hm].
    destruct (chain_module _ (me_unit fp) (q_abs fp nil) _ eq_refl Hm) as [r0 Hq].
    exists nil, ch1, r0; split; [ reflexivity | exact Hq ].
  - cbn in Hp; injection Hp as <-; split; [ exact HΓ |]; exists pre, suf, r0; split; [ reflexivity | exact Hq ].
Qed.

Lemma mod_base_nochain : forall Γ H ch1, mod_base Γ H ch1 -> mod_qname H = None -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros * [HH | (_ & mq & _ & _ & _ & Hp & _)] Hn; [ exact HH | congruence ]. Qed.

Lemma mod_base_mem : forall Γ H y ch1, mod_base Γ (me_mem H y) ch1 -> mod_base Γ H (y :: ch1).
Proof.
  intros * [HH | (HΓ & mq & pre & suf & r0 & Hp & -> & Hq)].
  - destruct (modexp_parts_of_wf _ _ _ _ HH) as [(HH0 & _) | (Hne & A0 & Hm)]; [ left; exact HH0 |].
    destruct (mod_qname H) as [mq0 |] eqn:Hp0; [| cbn in Hne; rewrite Hp0 in Hne; congruence ].
    assert (Hp : mod_qname (me_mem H y) = Some (qname_app mq0 (y :: nil))) by (cbn; rewrite Hp0; reflexivity).
    destruct (chain_module _ _ _ _ Hp Hm) as [r0 Hq].
    right; split; [ exact (presup_modexp_eq_ctx HH) |].
    exists mq0, (y :: nil), ch1, r0; split; [ exact Hp0 | split; [ reflexivity | exact Hq ] ].
  - cbn in Hp; destruct (mod_qname H) as [mq0 |] eqn:Hp0; [| discriminate ]; injection Hp as <-.
    right; split; [ exact HΓ |].
    exists mq0, (y :: pre), suf, r0; split; [ exact Hp0 | split; [ reflexivity |] ].
    unfold qname_app in *; cbn in *; rewrite <- app_assoc in Hq; exact Hq.
Qed.

Lemma umt_mod_mod : forall Θ Ξ Γ Δ Φ Φ' y Uy ch T,
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod Uy)) ->
    unit_member_type Θ Ξ (body_ctx Φ' ++ Δ ++ Γ) Uy ch (mr_mod T) ->
    unit_member_type Θ Ξ Γ (gu_body Δ Φ) (y :: ch) (mr_mod (T ++ body_ctx Φ' ++ Δ)).
Proof.
  intros * Hp Hu; change (mr_mod (T ++ body_ctx Φ' ++ Δ)) with (mres_gen (body_ctx Φ' ++ Δ) (mr_mod T)).
  eapply umt_mod; [ discriminate | exact Hp | exact Hu ].
Qed.

Lemma umt_alias_mod : forall Θ Ξ Γ Δ E ch T,
    member_type Θ Ξ (Δ ++ Γ) E ch (mr_mod T) ->
    unit_member_type Θ Ξ Γ (gu_mk Δ (md_alias E)) ch (mr_mod (T ++ Δ)).
Proof.
  intros * Hm; change (mr_mod (T ++ Δ)) with (mres_gen Δ (mr_mod T)); apply umt_alias; exact Hm.
Qed.

Theorem member_type_prefix_gen :
  (forall Γ H ch R, member_type gc_deps gc_stack Γ H ch R ->
     forall ch1 ch2, ch = ch1 ++ ch2 -> ch2 <> nil -> mod_base Γ H ch1 ->
     exists T', member_type gc_deps gc_stack Γ H ch1 (mr_mod T')) /\
  (forall Γ U ch R, unit_member_type gc_deps gc_stack Γ U ch R ->
     forall ch1 ch2, ch = ch1 ++ ch2 -> ch2 <> nil -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
     exists T', unit_member_type gc_deps gc_stack Γ U ch1 (mr_mod T')).
Proof.
  apply member_type_both_ind.
  - intros * Hne Hr ch1 ch2 -> Hne2 Hb.
    destruct (mod_base_unit _ _ _ Hb) as (HΓ & pre & suf & r0 & -> & Hq).
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
    rewrite <- app_assoc in Hr.
    destruct (path_prefix_resolve _ _ Hg _ _ _ _ _ Hq Hr Hne2) as [T1 HT1].
    eexists; eapply mt_unit_mod; exact HT1.
  - intros * Hm ch1 ch2 -> Hne2 Hb.
    destruct (mod_base_unit _ _ _ Hb) as (HΓ & pre & suf & r0 & -> & Hq).
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
    rewrite <- app_assoc in Hm.
    destruct (path_prefix_module _ _ Hg _ _ _ _ _ Hq Hm) as [[T1 HT1] | (U & r1 & _ & [=])].
    eexists; eapply mt_unit_mod; exact HT1.
  - intros * Hk Hm Hu IH ch1 ch2 -> Hne2 Hb.
    destruct (mod_base_unit _ _ _ Hb) as (HΓ & pre & suf & r0 & -> & Hq).
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
    pose proof Hm as Hm'; rewrite <- app_assoc in Hm'.
    destruct (path_prefix_module _ _ Hg _ _ _ _ _ Hq Hm') as [[T1 HT1] | (U' & r1 & HU' & [= <- ->])];
      [ eexists; eapply mt_unit_mod; exact HT1 |].
    destruct (IH r1 ch2 eq_refl Hne2 (gc_alias_unit_wf _ _ Hg _ _ _ Hm)) as [T' HT'].
    exists T'; eapply mt_unit_alias; [ cbn; discriminate | exact HU' | exact HT' ].
  - intros * Hx Hu IH ch1 ch2 -> Hne2 Hb.
    pose proof (mod_base_nochain _ _ _ Hb eq_refl) as HH.
    destruct (IH ch1 ch2 eq_refl Hne2 (ctx_lookup_mod_wf _ _ _ _ _ (presup_modexp_eq_ctx HH) Hx)) as [T' HT'].
    eexists; eapply mt_var; eassumption.
  - intros * Hu IH ch1 ch2 -> Hne2 Hb.
    pose proof (mod_base_nochain _ _ _ Hb eq_refl) as HH.
    destruct (IH ch1 ch2 eq_refl Hne2 (modexp_parts_of_wf _ _ _ _ HH)) as [T' HT'].
    eexists; eapply mt_lit; eassumption.
  - intros * Hk Hm IH ch1 ch2 -> Hne2 Hb.
    destruct (IH (y :: ch1) ch2 eq_refl Hne2 (mod_base_mem _ _ _ _ Hb)) as [T' HT'].
    exists T'; eapply mt_mem; [ cbn; discriminate | exact HT' ].
  - intros * Hm IH Ha ch1 ch2 -> Hne2 Hb.
    pose proof (mod_base_nochain _ _ _ Hb eq_refl) as HH.
    destruct (modexp_parts_of_wf _ _ _ _ HH) as [HH' (T0 & B0 & T1 & i & Hm0 & Hv0 & _)].
    destruct (IH ch1 ch2 eq_refl Hne2 (or_introl HH')) as [T' HT'].
    destruct (app_arity_pi _ _ _ _ _ HH' Hm0 Hv0 _ _ HT' ltac:(cbn; discriminate)) as (B' & C' & Hp').
    destruct (mres_app_of_pi _ N _ _ Hp') as (R'' & Ha'').
    destruct (mres_app_ty _ _ _ Ha'') as (_ & _ & _ & _ & Hk'').
    destruct R'' as [A'' | T'']; [ discriminate |].
    exists T''; eapply mt_app; eassumption.
  - intros * Hc Hne2 _.
    symmetry in Hc; apply app_eq_nil in Hc as [_ ->]; contradiction.
  - intros * Hp ch1 ch2 Hc Hne2 _.
    destruct ch1 as [| z ch1]; [ eexists; constructor |].
    injection Hc as -> Hc; symmetry in Hc; apply app_eq_nil in Hc as [_ ->]; contradiction.
  - intros * Hk Hp Hu IH ch1 ch2 Hc Hne2 HU.
    destruct ch1 as [| z ch1]; [ eexists; constructor |].
    injection Hc as -> ->.
    destruct (unit_parts_of_wf _ _ _ _ HU) as (HC & _ & _).
    destruct (IH ch1 ch2 eq_refl Hne2 (body_prefix_mod_wf _ _ _ _ _ _ _ _ HC Hp)) as [T' HT'].
    eexists; eapply umt_mod_mod; [ exact Hp | exact HT' ].
  - intros * Hm IH ch1 ch2 -> Hne2 HU.
    destruct (unit_parts_of_wf _ _ _ _ HU) as (_ & _ & HE).
    destruct (IH ch1 ch2 eq_refl Hne2 (or_introl HE)) as [T' HT'].
    eexists; eapply umt_alias_mod; eassumption.
Qed.

Corollary member_type_prefix :
  (forall Γ H ch R, member_type gc_deps gc_stack Γ H ch R ->
     forall ch1 ch2, ch = ch1 ++ ch2 -> ch2 <> nil -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
     exists T', member_type gc_deps gc_stack Γ H ch1 (mr_mod T')) /\
  (forall Γ U ch R, unit_member_type gc_deps gc_stack Γ U ch R ->
     forall ch1 ch2, ch = ch1 ++ ch2 -> ch2 <> nil -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
     exists T', unit_member_type gc_deps gc_stack Γ U ch1 (mr_mod T')).
Proof.
  split; [ intros * Hm * ? ? HH; eapply (proj1 member_type_prefix_gen); [ exact Hm | eassumption .. | left; exact HH ]
         | exact (proj2 member_type_prefix_gen) ].
Qed.

Lemma me_mems_wf : forall pre Γ H ch R,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> member_type gc_deps gc_stack Γ H (pre ++ ch) R -> ch <> nil ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_mems H pre ≈ me_mems H pre.
Proof.
  induction pre as [| y pre IH]; intros * HH Hm Hne; cbn [me_mems app] in *; [ exact HH |].
  destruct (proj1 member_type_prefix _ _ _ _ Hm (y :: nil) (pre ++ ch) eq_refl
              ltac:(destruct pre, ch; cbn; congruence) HH) as [T' HT'].
  eapply IH; [ eapply wf_me_mem; [ exact HH | exact HT' | exact HT' ] | | exact Hne ].
  eapply mt_mem; [ intros _; destruct pre, ch; cbn; congruence | exact Hm ].
Qed.

Lemma spine_nil_noargs : forall H R p0, modexp_spine H = (R, nil, p0) -> me_noargs H.
Proof.
  induction H; intros * Hs; cbn in Hs |- *; auto.
  - destruct (modexp_spine H) as [[R' args'] p0'] eqn:E; injection Hs as -> -> _; eauto.
  - destruct (modexp_spine H) as [[R' args'] p0'] eqn:E; injection Hs as _ Ha _.
    destruct args'; discriminate.
Qed.

(** ** Member References *)

Lemma member_ref_noargs_wf : forall Γ H ch A i M,
    me_noargs H -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_deps gc_stack Γ H ch (mr_term A) -> ch <> nil ->
    Γ ⊢ A : Type@i -> member_unfold_ch gc_deps gc_stack Γ H ch = Some M -> Γ ⊢ M : A ->
    Γ ⊢ member_ref H ch : A.
Proof.
  intros * Hn HH Hm Hne HA HMe HMt.
  destruct (exists_last Hne) as (pre & x & ->).
  rewrite member_ref_mems.
  eapply wf_mem;
    [ apply me_mems_noargs; exact Hn
    | eapply me_mems_wf; [ exact HH | exact Hm | discriminate ]
    | apply me_mems_member_type; [ exact Hm | discriminate ]
    | exact HA
    | unfold member_unfold; rewrite me_mems_unfold; exact HMe
    | exact HMt ].
Qed.

Lemma member_ref_wf : forall Γ H ch A i,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_deps gc_stack Γ H ch (mr_term A) -> ch <> nil -> Γ ⊢ A : Type@i ->
    (forall R args p0, modexp_spine H = (R, args, p0) -> Γ ⊢ apps (member_ref R (p0 ++ ch)) args : A) ->
    (exists M, member_unfold_ch gc_deps gc_stack Γ H ch = Some M /\ Γ ⊢ M : A) ->
    Γ ⊢ member_ref H ch : A.
Proof.
  intros * HH Hm Hne HA HR (M & HMe & HMt).
  destruct (modexp_spine H) as [[R args] p0] eqn:Es.
  destruct args as [| N args].
  - eapply member_ref_noargs_wf; [ exact (spine_nil_noargs _ _ _ Es) | eassumption .. ].
  - destruct (exists_last Hne) as (pre & x & ->).
    rewrite member_ref_mems.
    eapply wf_mem_app;
      [ eapply me_mems_wf; [ exact HH | exact Hm | discriminate ]
      | exact (me_mems_spine _ _ _ _ _ Es)
      | discriminate
      | exact HA
      | rewrite <- app_assoc; exact (HR _ _ _ eq_refl) ].
Qed.

(** ** The Domain of a Member's Type *)

Lemma dom_agree : forall Γ H T0 B0 T1 i ch R1 B1 C1 j,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H ->
    member_type gc_deps gc_stack Γ H nil (mr_mod T0) -> tele_view T0 = Some (B0, T1) -> Γ ⊢ B0 : Type@i ->
    member_type gc_deps gc_stack Γ H ch R1 -> (mres_kind R1 = mk_term -> ch <> nil) ->
    Γ ⊢ mres_ty R1 ≈ Π B1 C1 : Type@j -> Γ ⊢ B1 : Type@j ->
    exists k, Γ ⊢ B0 ≈ B1 : Type@k.
Proof.
  intros * HH Hm0 Hv HB0 Hm Hch HA1 HB1.
  destruct (wf_modexp_sem_mt _ _ HH) as [HS HHs].
  assert (Hok : gmod_ok gc_deps gc_stack).
  { pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
    clear - Hg; destruct GC as [Θ Ξ]; exact (gmod_ok_self _ _ Hg). }
  destruct (arity_pi _ _ _ _ _ HS Hm0 Hv) as (l & HBl & _ & HAl).
  pose proof (app_domain Hok _ _ _ _ _ _ HS HHs Hm0 HAl HBl _ _ _ _ _ Hm Hch
                (completeness_fundamental_exp_eq _ _ _ _ HA1) (completeness_fundamental_exp _ _ _ HB1)) as Hs.
  exists (max (max i l) j).
  apply sem_typ_eq_syn;
    [ eapply lift_exp_ge; [| exact HB0 ]; lia | eapply lift_exp_ge; [| exact HB1 ]; lia
    | eapply rel_exp_cumu_ge; [| exact Hs ]; lia ].
Qed.

(** ** Member Types Are Types *)

(** A chain from a unit need not be a module to have members: its prefix may
    be an open frame. *)
Definition mod_wf (Γ : ctx) (H : modexp) : Prop :=
  gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H \/ (⊢ Γ /\ mod_qname H <> None).

Lemma mod_wf_ctx : forall Γ H, mod_wf Γ H -> ⊢ Γ.
Proof. intros * [HH | [HΓ _]]; [ exact (presup_modexp_eq_ctx HH) | exact HΓ ]. Qed.

Lemma mod_wf_nochain : forall Γ H, mod_wf Γ H -> mod_qname H = None -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros * [HH | (_ & Hn)] Hp; [ exact HH | contradiction ]. Qed.

Lemma mod_wf_mem : forall Γ H y, mod_wf Γ (me_mem H y) -> mod_wf Γ H.
Proof.
  intros * [HH | (HΓ & Hn)].
  - destruct (modexp_parts_of_wf _ _ _ _ HH) as [(HH0 & _) | (Hn & _)]; [ left; exact HH0 |].
    right; split; [ exact (presup_modexp_eq_ctx HH) |]; cbn in Hn; destruct (mod_qname H); congruence.
  - right; split; [ exact HΓ |]; cbn in Hn; destruct (mod_qname H); congruence.
Qed.

(** A definition reached from a unit, as a term, is a global. *)
Lemma unit_ref_glob : forall Γ fp ch b pv A B, ⊢ Γ -> ch <> nil ->
    gc_resolve gc_deps gc_stack (q_abs fp ch) = Some (ge_def b pv A B) ->
    Γ ⊢ member_ref (me_unit fp) ch : A.
Proof.
  intros * HΓ Hne Hr.
  destruct (exists_last Hne) as (pre & x & ->); rewrite member_ref_mems.
  eapply wf_mem_glob; [ exact HΓ | exact (mod_qname_mems pre (me_unit fp) (q_abs fp nil) eq_refl) | exact Hr ].
Qed.

Theorem member_wf_gen :
  (forall Γ H ch R, member_type gc_deps gc_stack Γ H ch R ->
     mod_wf Γ H -> (mres_kind R = mk_term -> ch <> nil) ->
     (exists i, Γ ⊢ mres_ty R : Type@i) /\
     (mres_kind R = mk_term -> exists M, member_unfold_ch gc_deps gc_stack Γ H ch = Some M /\ Γ ⊢ M : mres_ty R) /\
     (mres_kind R = mk_term -> forall Q args p0, modexp_spine H = (Q, args, p0) ->
        Γ ⊢ apps (member_ref Q (p0 ++ ch)) args : mres_ty R)) /\
  (forall Γ U ch R, unit_member_type gc_deps gc_stack Γ U ch R ->
     gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> (mres_kind R = mk_term -> ch <> nil) ->
     (exists i, Γ ⊢ mres_ty R : Type@i) /\
     (mres_kind R = mk_term -> exists M, member_expansion U ch = Some M /\ Γ ⊢ M : mres_ty R)).
Proof.
  apply member_type_both_ind.
  - (* a definition reached from a unit *)
    intros Γ fp ch b pv A B Hne Hr HH Hch; cbn [mres_ty mres_kind].
    pose proof (mod_wf_ctx _ _ HH) as HΓ.
    destruct (wf_glob_typ _ _ _ _ _ _ _ _ HΓ Hr) as [i HA].
    assert (HM : member_unfold_ch gc_deps gc_stack Γ (me_unit fp) ch = Some (member_ref (me_unit fp) ch))
      by (cbn; rewrite Hr; reflexivity).
    pose proof (unit_ref_glob _ _ _ _ _ _ _ HΓ Hne Hr) as HMt.
    split; [ eauto | split; [ intros _; eauto |] ].
    intros _ Q args p0 Hs; cbn in Hs; injection Hs as <- <- <-; cbn [app apps]; exact HMt.
  - (* a body module *)
    intros Γ fp ch T Hm HH _; cbn [mres_ty mres_kind].
    split; [| split; discriminate ].
    pose proof (mod_wf_ctx _ _ HH) as HΓ.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
    pose proof (wf_gctx_closed _ _ _ HΓ) as Hc.
    destruct (gc_module_body _ _ _ _ Hm) as [Φ HΦ].
    destruct (gc_body_tele_wf _ _ Hg _ _ _ HΦ) as [HT _].
    assert (HTt : T ⊢ ⊤ : Type@0) by (econstructor; exact HT).
    destruct (ctx_pi_wf0 _ _ _ _ _ HTt) as [j Hj].
    assert (Hm0 : member_type gc_deps gc_stack nil (me_unit fp) ch (mr_mod T)) by (eapply mt_unit_mod; exact Hm).
    pose proof (mres_ty_scoped _ _ (proj1 (member_type_scoped _ _) _ _ _ _ Hm0 Hc I I)) as Hs; cbn in Hs.
    exists j; eapply closed_weaken_exp; [ exact HΓ | exact Hj | exact Hs | exact I ].
  - (* inside a global alias *)
    intros Γ fp ch U r R Hk Hm Hu IH HH Hch.
    pose proof (mod_wf_ctx _ _ HH) as HΓ.
    pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
    pose proof (wf_gctx_closed _ _ _ HΓ) as Hc.
    destruct (IH (gc_alias_unit_wf _ _ Hg _ _ _ Hm) Hk) as ([i HA] & HMu).
    pose proof (gctx_closed_module _ _ _ _ Hc Hm) as HUs; cbn in HUs.
    pose proof (mres_ty_scoped _ _ (proj2 (member_type_scoped _ _) _ _ _ _ Hu Hc I HUs)) as HAs; cbn in HAs.
    assert (HAΓ : Γ ⊢ mres_ty R : Type@i) by (eapply closed_weaken_exp; [ exact HΓ | exact HA | exact HAs | exact I ]).
    assert (HMΓ : mres_kind R = mk_term -> exists M, member_unfold_ch gc_deps gc_stack Γ (me_unit fp) ch = Some M /\ Γ ⊢ M : mres_ty R).
    { intros e; destruct (HMu e) as (M & HMe & HMt).
      exists M; split.
      - cbn; rewrite (gc_module_alias_resolve _ _ Hg _ _ _ Hm), Hm; exact HMe.
      - eapply closed_weaken_exp; [ exact HΓ | exact HMt | exact (member_expansion_scoped _ _ _ _ HMe HUs) | exact HAs ]. }
    split; [ eauto | split; [ exact HMΓ |] ].
    intros e Q args p0 Hs; cbn in Hs; injection Hs as <- <- <-; cbn [app apps].
    destruct (HMΓ e) as (M & HMe & HMt).
    (** The member lies in a closed module reached through the alias. *)
    pose proof (Hch e) as Hne.
    pose proof (Hk e) as Hrne.
    destruct R as [A | T]; [| discriminate e ]; cbn [mres_ty] in *.
    destruct (exists_last Hne) as (pre & x & ->).
    destruct (gc_module_alias_decomp _ _ Hg _ _ _ Hm) as (qp & y & Hqp & Hy).
    assert (Hb : mod_base Γ (me_unit fp) pre).
    { right; split; [ exact HΓ |].
      destruct (exists_last Hrne) as (r1 & z & Er); subst r.
      assert (Ep : pre = q_chain qp ++ y :: r1).
      { apply (f_equal q_chain) in Hqp; cbn in Hqp.
        replace (q_chain qp ++ y :: r1 ++ z :: nil) with ((q_chain qp ++ y :: r1) ++ z :: nil) in Hqp
          by (rewrite <- app_assoc; reflexivity).
        apply app_inj_tail in Hqp as [-> _]; reflexivity. }
      exists (q_abs fp nil), (q_chain qp ++ y :: nil), r1, (mr_alias U nil).
      split; [ reflexivity | split; [ rewrite Ep, <- app_assoc; reflexivity |] ].
      apply (f_equal q_unit) in Hqp; cbn in Hqp; subst fp.
      destruct qp; exact Hy. }
    assert (Hmt : member_type gc_deps gc_stack Γ (me_unit fp) (pre ++ x :: nil) (mr_term A))
      by (eapply mt_unit_alias; [ intros _; exact Hrne | exact Hm | exact Hu ]).
    destruct (proj1 member_type_prefix_gen _ _ _ _ Hmt pre (x :: nil) eq_refl ltac:(discriminate) Hb) as [T' HT'].
    assert (HH' : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_mems (me_unit fp) pre ≈ me_mems (me_unit fp) pre).
    { eapply wf_me_glob; [ exact HΓ | exact (mod_qname_mems pre (me_unit fp) (q_abs fp nil) eq_refl) |].
      apply me_mems_member_type; [ rewrite app_nil_r; exact HT' | cbn; discriminate ]. }
    rewrite member_ref_mems.
    change (a_mem (me_mems (me_unit fp) pre) x) with (member_ref (me_mems (me_unit fp) pre) (x :: nil)).
    eapply member_ref_noargs_wf;
      [ exact (mod_qname_noargs _ _ (mod_qname_mems pre (me_unit fp) (q_abs fp nil) eq_refl)) | exact HH'
      | apply me_mems_member_type; [ exact Hmt | discriminate ] | discriminate | exact HAΓ
      | rewrite me_mems_unfold; exact HMe | exact HMt ].
  - (* a module slot *)
    intros Γ x U ch R Hx Hu IH HH0 Hch.
    pose proof (mod_wf_nochain _ _ HH0 eq_refl) as HH.
    pose proof (presup_modexp_eq_ctx HH) as HΓ.
    destruct (IH (ctx_lookup_mod_wf _ _ _ _ _ HΓ Hx) Hch) as ([i HA] & HMu).
    assert (HMΓ : mres_kind R = mk_term -> exists M, member_unfold_ch gc_deps gc_stack Γ (me_var x) ch = Some M /\ Γ ⊢ M : mres_ty R).
    { intros e; destruct (HMu e) as (M & HMe & HMt).
      exists M; split; [ cbn; rewrite (ctx_find_mod_complete _ _ _ Hx); exact HMe | exact HMt ]. }
    split; [ eauto | split; [ exact HMΓ |] ].
    intros e Q args p0 Hs; cbn in Hs; injection Hs as <- <- <-; cbn [app apps].
    destruct (HMΓ e) as (M & HMe & HMt).
    pose proof (Hch e) as Hne.
    destruct R as [A | T]; [| discriminate e ]; cbn [mres_ty] in *.
    eapply member_ref_noargs_wf; [ exact I | exact HH | eapply mt_var; [ exact Hx | exact Hu ] | exact Hne | exact HA | exact HMe | exact HMt ].
  - (* a literal *)
    intros Γ U ch R Hu IH HH0 Hch.
    pose proof (mod_wf_nochain _ _ HH0 eq_refl) as HH.
    destruct (IH (modexp_parts_of_wf _ _ _ _ HH) Hch) as ([i HA] & HMu).
    split; [ eauto | split; [ exact HMu |] ].
    intros e Q args p0 Hs; cbn in Hs; injection Hs as <- <- <-; cbn [app apps].
    destruct (HMu e) as (M & HMe & HMt).
    pose proof (Hch e) as Hne.
    destruct R as [A | T]; [| discriminate e ]; cbn [mres_ty] in *.
    eapply member_ref_noargs_wf; [ exact I | exact HH | eapply mt_lit; exact Hu | exact Hne | exact HA | exact HMe | exact HMt ].
  - (* a selection *)
    intros Γ H y ch R Hk Hm IH HH Hch.
    destruct (IH (mod_wf_mem _ _ _ HH) ltac:(intros; discriminate)) as (HA & HMu & HR).
    split; [ exact HA | split; [ exact HMu |] ].
    intros e Q args p0 Hs; cbn in Hs.
    destruct (modexp_spine H) as [[R' args'] p0'] eqn:Es; injection Hs as <- <- <-.
    rewrite <- app_assoc; exact (HR e _ _ _ eq_refl).
  - (* an application *)
    intros Γ H N ch R R' Hm IH Ha HH0 Hch.
    pose proof (mod_wf_nochain _ _ HH0 eq_refl) as HH.
    destruct (modexp_parts_of_wf _ _ _ _ HH) as [HH' (T0 & B0 & T1 & i0 & Hm0 & Hv0 & HB0 & HN0)].
    destruct (mres_app_ty _ _ _ Ha) as (B & C & Hp & HR' & Hk').
    rewrite HR', Hk'; rewrite Hk' in Hch.
    destruct (IH (or_introl HH') Hch) as ([j HA] & HMu & HR).
    destruct (pi_view_wf _ _ _ _ _ HA Hp) as (HAe & HB & HC).
    destruct (dom_agree _ _ _ _ _ _ _ _ _ _ _ HH' Hm0 Hv0 HB0 Hm Hch HAe HB) as [k HBB].
    pose proof (wf_conv' _ _ _ _ _ _ _ HN0 HBB) as HN.
    pose proof (wf_sub_single _ _ _ _ _ _ HB HN) as Hσ.
    split; [ exists j; exact (sub_preserves_typ _ _ _ _ _ _ _ HC Hσ) | split ].
    + intros e; destruct (HMu e) as (M & HMe & HMt).
      exists (a_app M N); split; [ cbn; rewrite HMe; reflexivity |].
      eapply wf_app; [ exact HB | exact HC | eapply wf_conv'; [ exact HMt | exact HAe ] | exact HN ].
    + intros e Q args p0 Hs; cbn in Hs.
      destruct (modexp_spine H) as [[Q' args'] p0'] eqn:Es; injection Hs as <- <- <-.
      rewrite apps_snoc.
      eapply wf_app; [ exact HB | exact HC | eapply wf_conv'; [ exact (HR e _ _ _ eq_refl) | exact HAe ] | exact HN ].
  - (* the unit itself *)
    intros Γ Δ Φ HU _; cbn [mres_ty mres_kind].
    split; [| discriminate ].
    destruct (unit_parts_of_wf _ _ _ _ HU) as (HC & _ & _).
    pose proof (ctx_app_wf_right _ _ _ _ HC) as HΔ.
    assert (Δ ++ Γ ⊢ ⊤ : Type@0) by (econstructor; exact HΔ).
    eapply ctx_pi_wf; eassumption.
  - (* a definition of a body *)
    intros Γ Δ Φ Φ' x b pv A B Hp HU _; cbn [mres_ty mres_kind].
    destruct (unit_parts_of_wf _ _ _ _ HU) as (HC & _ & Hs).
    destruct (body_shape_prefix_def _ _ _ _ _ _ _ Hs Hp) as [M0 ->].
    pose proof (body_prefix_wf _ _ _ _ _ _ _ HC Hp) as Hx; cbn in Hx.
    destruct (ctx_decomp_def Hx) as (HC' & [i HA] & HM0).
    split; [ eapply ctx_pi_wf; rewrite <- app_assoc; eassumption |].
    intros _; eexists; split; [ exact (member_expansion_def _ _ _ _ _ _ _ _ Hp) |].
    cbn [body_ctx app ctx_fn].
    eapply ctx_fn_wf; [ rewrite <- app_assoc; exact HC' | rewrite <- app_assoc; exact HA |].
    assert (Hl : body_ctx Φ' ++ Δ ++ Γ ⊢ ℓ A ≔ M0 in #0 : A[↑]ʷ[Id,,M0])
      by (eapply wf_let; [ exact HA | exact HM0 | eapply wf_vlookup; [ exact Hx | constructor ] ]).
    rewrite exp_sub_shift_extend, exp_sub_id in Hl.
    rewrite <- app_assoc; exact Hl.
  - (* a member of a submodule of a body *)
    intros Γ Δ Φ Φ' y Uy ch R Hk Hp Hu IH HU Hch; rewrite mres_ty_gen, mres_kind_gen in *.
    destruct (unit_parts_of_wf _ _ _ _ HU) as (HC & _ & _).
    pose proof (body_prefix_mod_wf _ _ _ _ _ _ _ _ HC Hp) as HUy.
    destruct (IH HUy Hk) as ([i HA] & HMu).
    pose proof (body_prefix_wf _ _ _ _ _ _ _ HC Hp) as Hx; cbn in Hx.
    pose proof (proj1 (ctx_decomp_mod Hx)) as HC'.
    split; [ eapply ctx_pi_wf; rewrite <- app_assoc; eassumption |].
    intros e; destruct (HMu e) as (M1 & HM1e & HM1t).
    pose proof (Hk e) as Hne.
    destruct R as [A | T]; [| discriminate e ]; cbn [mres_ty] in *.
    eexists; split; [ exact (member_expansion_mod _ _ _ _ _ _ Hne Hp) |].
    cbn [body_ctx app ctx_fn].
    eapply ctx_fn_wf; [ rewrite <- app_assoc; exact HC' | rewrite <- app_assoc; exact HA |].
    rewrite <- app_assoc.
    pose proof (wf_wk_shift _ _ _ _ Hx) as Hw.
    assert (HR : ce_mod Uy :: body_ctx Φ' ++ Δ ++ Γ ⊢ member_ref (me_var 0) ch : A[↑]ʷ).
    { pose proof (wf_gctx_closed _ _ _ Hx) as Hc.
      pose proof (proj2 (member_type_wk _ _ Hc) _ _ _ _ Hu _ _ (wf_wk_mod_compat _ _ _ _ _ Hw)) as Hmt.
      eapply member_ref_noargs_wf with (i := i) (M := M1[↑]ʷ);
        [ exact I
        | eapply wf_me_var; [ exact Hx | apply mod_here ]
        | eapply mt_var; [ apply mod_here | exact Hmt ]
        | exact Hne
        | eapply wk_preserves_typ; eassumption
        | cbn; apply member_expansion_wk; exact HM1e
        | eapply wk_preserves_exp; eassumption ]. }
    assert (Hl : body_ctx Φ' ++ Δ ++ Γ ⊢ ℓₘ Uy in member_ref (me_var 0) ch : A[↑]ʷ[Id ,,ₘ me_lit Uy])
      by (eapply wf_let_mod; [ exact HUy | eapply wk_preserves_typ; eassumption | exact HR ]).
    rewrite exp_sub_shift_extend, exp_sub_id in Hl; exact Hl.
  - (* a member of an alias unit *)
    intros Γ Δ E ch R Hm IH HU Hch; rewrite mres_ty_gen, mres_kind_gen in *.
    destruct (unit_parts_of_wf _ _ _ _ HU) as (HC & _ & HE).
    destruct (IH (or_introl HE) Hch) as ([i HA] & HMu & HR).
    split; [ eapply ctx_pi_wf; eassumption |].
    intros e; pose proof (Hch e) as Hne.
    eexists; split; [ exact (member_expansion_alias _ _ _ Hne) |].
    eapply ctx_fn_wf; [ exact HC | exact HA |].
    destruct R as [A | T]; [| discriminate e ]; cbn [mres_ty] in *.
    eapply member_ref_wf; [ exact HE | exact Hm | exact Hne | exact HA | exact (HR e) | exact (HMu e) ].
Qed.

Corollary member_wf :
  (forall Γ H ch R, member_type gc_deps gc_stack Γ H ch R ->
     gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> (mres_kind R = mk_term -> ch <> nil) ->
     (exists i, Γ ⊢ mres_ty R : Type@i) /\
     (mres_kind R = mk_term -> exists M, member_unfold_ch gc_deps gc_stack Γ H ch = Some M /\ Γ ⊢ M : mres_ty R) /\
     (mres_kind R = mk_term -> forall Q args p0, modexp_spine H = (Q, args, p0) ->
        Γ ⊢ apps (member_ref Q (p0 ++ ch)) args : mres_ty R)) /\
  (forall Γ U ch R, unit_member_type gc_deps gc_stack Γ U ch R ->
     gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> (mres_kind R = mk_term -> ch <> nil) ->
     (exists i, Γ ⊢ mres_ty R : Type@i) /\
     (mres_kind R = mk_term -> exists M, member_expansion U ch = Some M /\ Γ ⊢ M : mres_ty R)).
Proof.
  split; [ intros * Hm HH; exact (proj1 member_wf_gen _ _ _ _ Hm (or_introl HH)) | exact (proj2 member_wf_gen) ].
Qed.

End Fixed_GCtx.
