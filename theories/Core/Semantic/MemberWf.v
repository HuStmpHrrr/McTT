(** * What Well-Formed Module Expressions Look Up

    A member a well-formed module expression looks up is typed, at the
    type the lookup reads, and so is its δ-reduct ([member_wf]): what the
    lookup reads is typed ([mem_desc_ok], [desc_ok_ty]), so the premises of
    [wf_mem] hold of it.  The outermost parameter a module still takes is a
    type ([mtele_head_wf]), and the entries a local open generates extend a
    well-formed context ([gens_ext_wf]).  The checker reads all three off
    the lookup, without checking anything again. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import MemberWf MemberLemmas DescTyping LookupSound GlobalPresup.
From Mctt.Core.Semantic Require Import Fixed.
Import Syntax_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Import Fixed_Notations.

(** A member a module expression looks up, at the type it is looked up at:
    a type, with its δ-reduct, if any, of it. *)
Corollary member_wf : forall Γ H x R A,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> mdenote gc_deps gc_stack Γ (me_mem H x) R ->
    ds_ty gc_deps gc_stack R = Some A ->
    (exists i, Γ ⊢ A : Typeω@i) /\ (forall M, ds_red R = Some M -> Γ ⊢ M : A) /\ Γ ⊢ a_mem H x : A.
Proof.
  intros * HH Hm Ht.
  pose proof (gctx_valid_syn _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH))) as Hv.
  destruct (desc_ok_ty _ _ Hv _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) Ht) as [Hi HM].
  split; [ exact Hi | split; [ exact HM | exact (wf_mem_desc _ _ _ _ _ _ _ HH Hm Ht) ] ].
Qed.

(** The next parameter of a closed telescope given typed arguments, at
    them, is a type. *)
Lemma args_ok_next : forall Γ T Ns C T1',
    args_ok gc_deps gc_stack Γ T Ns -> tele_ass T -> ctx_scoped 0 T -> ⊢ T ->
    tele_view (List.firstn (length T - length Ns) T) = Some (C, T1') ->
    exists i, Γ ⊢ C[sb_of_list Id Ns] : Typeω@i.
Proof.
  intros * (T1 & T2 & -> & Hl & Ha2 & Hs2 & HT2 & HN) Ha Hs HT Hv.
  replace (firstn (length (T1 ++ T2) - length Ns) (T1 ++ T2)) with T1 in Hv
    by (rewrite List.length_app, <- Hl, Nat.add_sub, List.firstn_app, Nat.sub_diag, List.firstn_O, List.app_nil_r, List.firstn_all; reflexivity).
  apply List.Forall_app in Ha as [Ha1 _].
  pose proof (tele_view_ass _ _ _ Ha1 Hv) as ->.
  rewrite <- List.app_assoc in HT; cbn [List.app] in HT.
  destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HT)) as [_ [i HC]].
  pose proof (closed_tele_weaken_exp _ _ _ _ _ _ Hs2 HC HT2) as HC'.
  pose proof (wf_sub_of_list_id _ _ _ _ _ Ha2 HT2 (eq_sym Hl) HN) as Hσ.
  exists i; pose proof (sub_preserves_typ _ _ _ _ _ _ _ HC' Hσ) as HB; cbn in HB; exact HB.
Qed.

(** The outermost parameter a typed module description still takes is a
    type. *)
Lemma desc_ok_tele_head : forall Γ Rm T B T1,
    desc_ok gc_deps gc_stack Γ Rm -> ds_tele Rm = Some T -> tele_view T = Some (B, T1) ->
    exists i, Γ ⊢ B : Typeω@i.
Proof.
  intros * HR Ht Hv.
  inversion HR as [Γ0 A om HA HM | Γ0 Θ' pq Ns D Hl Hau Hsu HTu HΘ' Hargs HaΘ | Γ0 Δ Φw Φ HΦ Hn Hent HaΔ Hsh Hnd HUw | Γ0 Θ' T0 Φ Ns Θ0 Ξ0 p Hg0 Hsub0 Hloc Ha0 Hs0 HT0 HΘ' Hargs HaΘ];
    subst; cbn in Ht; try discriminate.
  - (* an open module: its parameters *)
    injection Ht as <-.
    unfold tele_view in Hv; destruct (tele_open_split _ _ _ Hv) as (τ & Es).
    pose proof (tele_split_wf gc_deps gc_stack (rev Δ) Γ) as Hsw; rewrite rev_involutive, Es in Hsw.
    exact (proj1 (Hsw (ctx_app_wf_tail _ _ _ _ HΦ))).
  - (* a closed module: its outside parameters, then the rest of its telescope *)
    destruct (Nat.leb (length Ns) (length T0)); [| discriminate ]; injection Ht as <-.
    unfold tele_view in Hv; rewrite List.rev_app_distr in Hv.
    pose proof (tele_split_wf gc_deps gc_stack (rev Θ') Γ ltac:(rewrite rev_involutive; exact HΘ')) as Hsw.
    rewrite rev_involutive in Hsw.
    destruct (tele_split (rev Θ')) as [[[B' Θ''] τ] | τ] eqn:Es.
    + destruct (tele_open_app_inl _ (rev (tele_sub (List.firstn (length T0 - length Ns) T0) (sb_of_list Id Ns))) _ _ _ Es)
        as (T' & Ho).
      rewrite Ho in Hv; injection Hv as <- _; exact (proj1 Hsw).
    + destruct (tele_open_app_inr _ _ _ _ _ Es Hv) as (B0 & T0' & Ho & ->).
      fold (tele_view (tele_sub (List.firstn (length T0 - length Ns) T0) (sb_of_list Id Ns))) in Ho.
      rewrite tele_view_sub in Ho.
      destruct (tele_view (List.firstn (length T0 - length Ns) T0)) as [[C T1'] |] eqn:HvC; cbn in Ho; [| discriminate ].
      injection Ho as <- _.
      destruct (args_ok_next _ _ _ _ _ Hargs Ha0 Hs0 HT0 HvC) as [i HC].
      exists i; pose proof (sub_preserves_typ _ _ _ _ _ _ _ HC Hsw) as HB; cbn in HB; exact HB.
Qed.

(** The outermost parameter a well-formed module expression still takes is
    a type. *)
Corollary mtele_head_wf : forall Γ H R T B T1,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> mdenote gc_deps gc_stack Γ H R ->
    ds_mtele gc_deps gc_stack R = Some T -> tele_view T = Some (B, T1) ->
    exists i, Γ ⊢ B : Typeω@i.
Proof.
  intros * HH Hm Ht Hv.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  unfold ds_mtele in Ht; destruct (ds_mod gc_deps gc_stack R) as [Rm |] eqn:Hmd; [| discriminate ].
  exact (desc_ok_tele_head _ _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HH Hm) Hmd) Ht Hv).
Qed.

(** A well-formed module expression denotes a module with a telescope. *)
Lemma me_mtele : forall Γ H H',
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H' ->
    exists R T, mdenote gc_deps gc_stack Γ H R /\ ds_mtele gc_deps gc_stack R = Some T.
Proof.
  intros * HH.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
  destruct (me_denotes _ _ _ _ _ HH) as (R & Rm & Hm & Hmd).
  pose proof (desc_ok_mod _ _ Hg _ _ _ (me_desc_ok _ _ _ _ _ _ HH Hm) Hmd) as Hok.
  destruct (desc_ok_tele _ _ _ _ Hok (ds_mod_is_mod _ _ _ _ Hmd)) as [T HT].
  exists R, T; split; [ exact Hm | unfold ds_mtele; rewrite Hmd; exact HT ].
Qed.

(** ** What a Local Open Generates Is Well-Formed

    The entries an open of a well-formed module generates are well-formed:
    a definition is the member at its type, an alias the module or its
    submodule, each read past the entries generated before it. *)
Lemma gens_ext_wf_gen : forall g Γ1 H its gs, items_gen gc_deps gc_stack g Γ1 H its gs -> g = false ->
    forall Γ0 Ψ, Γ1 = Ψ ++ Γ0 -> gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵐ H ≈ H ->
    forall Φg, gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx Φg ++ Ψ ≈ body_ctx Φg ++ Ψ ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx (gens_append Φg (List.length (body_ctx Φg)) gs) ++ Ψ ≈
                                body_ctx (gens_append Φg (List.length (body_ctx Φg)) gs) ++ Ψ.
Proof.
  induction 1 as [| g Γ1 H d pv its gs _ IH | g Γ1 H n d pv A om its gs Hm _ IH | g Γ1 H n d pv R its gs Hm Hmod _ IH
                 | Γ1 H n d pv Θ' p Ns its gs Hm _ IH ];
    intros Eg Γ0 Ψ -> HH Φg HX; cbn [gens_append ig_entry]; try exact HX; [| | | discriminate ].
  all: pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- app_assoc in HC.
  all: pose proof (wf_wk_shiftn_app' _ _ _ _ HC) as Hw.
  - (* the module itself *)
    assert (HU0 : gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵘ gu_mk nil (md_alias H) ≈ gu_mk nil (md_alias H))
      by (apply wf_unit_eq_alias; [ apply wf_ext_eq_nil; gen_presups; assumption | constructor | constructor | exact HH | exact HH ]).
    pose proof (wk_preserves_unit _ _ _ _ _ _ _ HU0 Hw) as HU1.
    cbn [gentry_wk].
    change (S (length (body_ctx Φg)))
      with (length (body_ctx (gm_ext Φg d (ge_mod pv (gunit_wk (gu_mk nil (md_alias H)) (wk_shiftn (length (body_ctx Φg)))))))).
    apply (IH Eg Γ0 Ψ eq_refl HH).
    cbn [body_ctx app]; apply wf_ext_eq_mod; [ exact HX | rewrite <- app_assoc; exact HU1 | rewrite <- app_assoc; exact HU1 ].
  - (* a term member: a definition of it, at its type *)
    destruct (member_wf _ _ _ _ _ HH Hm eq_refl) as ([i HA] & _ & HM).
    pose proof (wk_preserves_typ _ _ _ _ _ _ _ HA Hw) as HA1.
    pose proof (wk_preserves_exp _ _ _ _ _ _ _ HM Hw) as HM1.
    cbn [gentry_wk option_map].
    change (S (length (body_ctx Φg)))
      with (length (body_ctx (gm_ext Φg d (ge_def true pv A[wk_shiftn (length (body_ctx Φg))]ʷ
                                               (Some (a_mem H n)[wk_shiftn (length (body_ctx Φg))]ʷ))))).
    apply (IH Eg Γ0 Ψ eq_refl HH).
    rewrite app_assoc in HA1, HM1; cbn [body_ctx app].
    eapply wf_ext_eq_def; [ exact HX | exact HA1 | apply wf_exp_eq_refl; exact HA1 | exact HM1 | apply wf_exp_eq_refl; exact HM1
                          | exact HA1 | exact HM1 ].
  - (* a module member: an alias of it *)
    pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg.
    pose proof (gctx_valid_syn _ _ Hg) as Hv.
    destruct (desc_ok_tele _ _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hv HH Hm) Hmod) as [T HT].
    assert (Hmt : ds_mtele gc_deps gc_stack R = Some T) by (unfold ds_mtele; rewrite (ds_is_mod_mod _ _ _ Hmod); exact HT).
    assert (HE : gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵐ me_mem H n ≈ me_mem H n)
      by (eapply wf_me_mem; [ exact HH | exact Hm | exact Hmt | exact Hm | exact Hmt ]).
    assert (HU0 : gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ0 ⊢ᵘ gu_mk nil (md_alias (me_mem H n)) ≈ gu_mk nil (md_alias (me_mem H n)))
      by (apply wf_unit_eq_alias; [ apply wf_ext_eq_nil; gen_presups; assumption | constructor | constructor | exact HE | exact HE ]).
    pose proof (wk_preserves_unit _ _ _ _ _ _ _ HU0 Hw) as HU1.
    cbn [gentry_wk].
    change (S (length (body_ctx Φg)))
      with (length (body_ctx (gm_ext Φg d (ge_mod pv (gunit_wk (gu_mk nil (md_alias (me_mem H n))) (wk_shiftn (length (body_ctx Φg)))))))).
    apply (IH Eg Γ0 Ψ eq_refl HH).
    cbn [body_ctx app]; apply wf_ext_eq_mod; [ exact HX | rewrite <- app_assoc; exact HU1 | rewrite <- app_assoc; exact HU1 ].
Qed.

(** An open's entries, after the body before it. *)
Corollary gens_ext_wf : forall Γ0 Ψ Φx H its gs,
    items_gen gc_deps gc_stack false (body_ctx Φx ++ Ψ ++ Γ0) H its gs ->
    gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Ψ ++ Γ0 ⊢ᵐ H ≈ H ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx Φx ++ Ψ ≈ body_ctx Φx ++ Ψ ->
    gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx (gens_append Φx 0 gs) ++ Ψ ≈ body_ctx (gens_append Φx 0 gs) ++ Ψ.
Proof.
  intros * Hg HH HX.
  rewrite gens_body_ctx_base, <- app_assoc.
  rewrite app_assoc in Hg, HH.
  exact (gens_ext_wf_gen _ _ _ _ _ Hg eq_refl Γ0 (body_ctx Φx ++ Ψ) eq_refl HH gm_nil HX).
Qed.

End Fixed_GCtx.
