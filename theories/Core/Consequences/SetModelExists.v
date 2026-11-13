(** * Existence of a Set Model of a Global Context

    Every well-formed transparent global context has a global valuation
    modelling it ([set_gctx_model_exists]).  Which members below each
    global module are proofs is fixed up front by the final context: a
    chain of selections from a global path is a proof exactly when it
    denotes a propositional member there.  This file first shows that the
    proofness table a module expression's syntax gives
    ([modexp_member_proofs]) agrees with what its selections denote
    ([modexp_proofs_coherent]), given that the global modules' tables do. *)

From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Consequences Require Import ModexpConversion.
From Mctt.Core.Syntactic Require Import Presup.
From Mctt.Core.Syntactic.System Require Import Structural SlotConversion.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas DescTyping Presup Paths LookupSound.
From Mctt.Core.SetModel.Interpretation Require Import Respects.
From Mctt.Core.Soundness Require Import MemberGluing Selection MemberApp.
Import Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** [chain_proof Θ Ξ Γ H ys x]: the chain [ys], then [x], selects a
    propositional member of [H] in [Γ]. *)
Definition chain_proof (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) (ys : list string) (x : string) : Prop :=
  exists R, mdenote Θ Ξ Γ (me_mem (me_mems H ys) x) R /\ mdesc_kind R = ak_propositional.

(** Selections commute with substitutions. *)
Lemma me_mems_sub_comm : forall ys H σ, (me_mems H ys)[σ]ᵐ = me_mems H[σ]ᵐ ys.
Proof. induction ys as [| y ys IH]; intros H σ; cbn; [ reflexivity | apply IH ]. Qed.

(** What a chain is selected from denotes, when the chain does. *)
Lemma mems_back : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ ys Q x X, mdenote Θ Ξ Γ (me_mem (me_mems Q ys) x) X -> exists R, mdenote Θ Ξ Γ Q R.
Proof.
  intros Θ Ξ Hg Γ ys; induction ys as [| y ys IH]; intros * HX; cbn [me_mems] in HX.
  - exact (step_left_back _ _ Hg _ _ (ps_mem x) _ HX).
  - destruct (IH _ _ _ HX) as [R HR]; exact (step_left_back _ _ Hg _ _ (ps_mem y) _ HR).
Qed.

(** A chain from what denotes a term denotes nothing. *)
Lemma chain_from_term : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ ys P R x X, obs_root Ξ P -> mdenote Θ Ξ Γ P R -> mdesc_mod R = None ->
    ~ mdenote Θ Ξ Γ (me_mem (me_mems P ys) x) X.
Proof.
  intros * Hg * Hq HP Hn HX.
  assert (Hy : exists y X1, mdenote Θ Ξ Γ (me_mem P y) X1).
  { destruct ys as [| y ys]; cbn [me_mems] in HX; [ eauto |].
    destruct (mems_back _ _ Hg _ _ _ _ _ HX) as [X1 HX1]; eauto. }
  destruct Hy as (y & X1 & HX1).
  destruct (mdenote_mem_obs_inv _ _ Hg _ _ _ _ Hq HX1) as (R0 & R0m & _ & _ & _ & _ & HR0 & Hmd & _).
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR0 _ HP), Hn in Hmd; discriminate.
Qed.

(** A chain from a frame-free well-formed module expression moved by a
    substitution is the chain from the expression, moved. *)
Lemma chain_sub_reflect : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall ys Γg H Ψ σ x X', Θ ⍮ Ξ ⍮ Γg ⊢ᵐ H ≈ H ->
    (forall R, mdenote Θ Ξ Γg H R -> ~ desc_reads_frame Ξ R) -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : Γg ->
    mdenote Θ Ξ Ψ (me_mem (me_mems H[σ]ᵐ ys) x) X' ->
    exists X, mdenote Θ Ξ Γg (me_mem (me_mems H ys) x) X /\ X' = mdesc_sub X σ.
Proof.
  intros Θ Ξ Hg ys; induction ys as [| y ys IH]; intros * HH Hff Hσ HX';
    (assert (Hq : obs_root Ξ H[σ]ᵐ);
     [ apply (obs_root_of_frame_free _ _ Hg _ _ _ (sub_preserves_modexp _ _ _ _ _ _ _ HH Hσ));
       intros R HR Hr; destruct (me_denotes _ _ _ _ _ HH) as (R0 & _ & HR0 & _);
       rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR _ (wf_sub_mdenote _ _ _ _ _ _ _ _ HH HR0 Hσ)) in Hr;
       exact (Hff _ HR0 (desc_reads_frame_sub _ _ _ Hr)) |]); cbn [me_mems] in HX' |- *.
  - destruct (generic_sel_reflect _ _ Hg _ _ _ _ _ _ HH Hσ Hq HX') as (Xg & HXg).
    exists Xg; split; [ exact HXg |].
    exact (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HX' _ (wf_sub_mdenote_mem _ _ _ _ _ _ _ _ _ HH HXg Hσ)).
  - destruct (mems_back _ _ Hg _ _ _ _ _ HX') as [R1' HR1'].
    destruct (generic_sel_reflect _ _ Hg _ _ _ _ _ _ HH Hσ Hq HR1') as (Xg & HXg).
    pose proof (wf_sub_mdenote_mem _ _ _ _ _ _ _ _ _ HH HXg Hσ) as HXgσ.
    pose proof (sel_desc_ok _ _ _ _ _ _ _ HH HXg) as HokX.
    destruct (mdesc_mod Xg) as [Xgm |] eqn:Em.
    + destruct (desc_ok_mod_tele _ _ Hg _ _ _ HokX Em) as [Ty HTy].
      assert (HHy : Θ ⍮ Ξ ⍮ Γg ⊢ᵐ me_mem H y ≈ me_mem H y) by (eapply wf_me_mem; eassumption).
      pose proof (obs_root_of_frame_free _ _ Hg _ _ _ HH Hff) as HqH.
      exact (IH _ _ _ _ _ _ HHy (fun R HR => sel_frame_free _ _ Hg _ _ _ _ _ HH HqH HR) Hσ HX').
    + exfalso; refine (chain_from_term _ _ Hg _ ys (me_mem H[σ]ᵐ y) (mdesc_sub Xg σ) _ _ (obs_root_step _ _ Hg _ (ps_mem y) Hq) HXgσ _ HX').
      destruct (mdesc_mod (mdesc_sub Xg σ)) eqn:E; [| reflexivity ].
      destruct (mdesc_mod_sub_inv _ _ _ E) as (? & HE' & _); congruence.
Qed.

(** A chain from a frame-free well-formed module expression, moved by a
    substitution. *)
Lemma chain_sub_forward : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall ys Γg H Ψ σ x X, Θ ⍮ Ξ ⍮ Γg ⊢ᵐ H ≈ H ->
    (forall R, mdenote Θ Ξ Γg H R -> ~ desc_reads_frame Ξ R) -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : Γg ->
    mdenote Θ Ξ Γg (me_mem (me_mems H ys) x) X -> mdenote Θ Ξ Ψ (me_mem (me_mems H[σ]ᵐ ys) x) (mdesc_sub X σ).
Proof.
  intros Θ Ξ Hg ys; induction ys as [| y ys IH]; intros * HH Hff Hσ HX; cbn [me_mems] in HX |- *.
  - exact (wf_sub_mdenote_mem _ _ _ _ _ _ _ _ _ HH HX Hσ).
  - pose proof (obs_root_of_frame_free _ _ Hg _ _ _ HH Hff) as HqH.
    destruct (mems_back _ _ Hg _ _ _ _ _ HX) as [Xg HXg].
    pose proof (sel_desc_ok _ _ _ _ _ _ _ HH HXg) as HokX.
    destruct (mdesc_mod Xg) as [Xgm |] eqn:Em.
    + destruct (desc_ok_mod_tele _ _ Hg _ _ _ HokX Em) as [Ty HTy].
      assert (HHy : Θ ⍮ Ξ ⍮ Γg ⊢ᵐ me_mem H y ≈ me_mem H y) by (eapply wf_me_mem; eassumption).
      exact (IH _ _ _ _ _ _ HHy (fun R HR => sel_frame_free _ _ Hg _ _ _ _ _ HH HqH HR) Hσ HX).
    + exfalso; exact (chain_from_term _ _ Hg _ ys (me_mem H y) Xg _ _ (obs_root_step _ _ Hg _ (ps_mem y) HqH) HXg Em HX).
Qed.

(** The chains of a frame-free well-formed module expression select
    proofs exactly where its moved chains do. *)
Lemma chain_proof_sub : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γg H Ψ σ ys x, Θ ⍮ Ξ ⍮ Γg ⊢ᵐ H ≈ H ->
    (forall R, mdenote Θ Ξ Γg H R -> ~ desc_reads_frame Ξ R) -> Θ ⍮ Ξ ⍮ Ψ ⊢ˢ σ : Γg ->
    chain_proof Θ Ξ Ψ H[σ]ᵐ ys x <-> chain_proof Θ Ξ Γg H ys x.
Proof.
  intros * Hg * HH Hff Hσ; unfold chain_proof; split.
  - intros (X' & HX' & Hk); destruct (chain_sub_reflect _ _ Hg _ _ _ _ _ _ _ HH Hff Hσ HX') as (X & HX & ->).
    exists X; split; [ exact HX | rewrite mdesc_kind_sub in Hk; exact Hk ].
  - intros (X & HX & Hk); exists (mdesc_sub X σ); split; [ exact (chain_sub_forward _ _ Hg _ _ _ _ _ _ _ HH Hff Hσ HX) | rewrite mdesc_kind_sub; exact Hk ].
Qed.

(** ** Chains of Descriptions *)

(** [desc_sel Θ Ξ Γ Rm y S]: the module description [Rm] has the entry [y],
    read as [S]. *)
Definition desc_sel (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (Rm : mdesc) (y : string) (S : mdesc) : Prop :=
  exists Γy E rd R1, mdesc_entry Rm y = Some (Γy, E, rd) /\ edenote Θ Ξ (Γy ++ Γ) (mdesc_entry_path Rm y) E R1 /\
    mdesc_read rd R1 = Some S.

(** [desc_chain Θ Ξ Γ R ys x X]: the selections [ys], then [x], from the
    module part of [R] read [X]. *)
Inductive desc_chain (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : mdesc -> list string -> string -> mdesc -> Prop :=
(** The last selection *)
| desc_chain_last : forall R Rm x X, mdesc_mod R = Some Rm -> desc_sel Θ Ξ Γ Rm x X -> desc_chain Θ Ξ Γ R nil x X
(** A selection, then the rest from what it reads *)
| desc_chain_step : forall R Rm y ys x S X, mdesc_mod R = Some Rm -> desc_sel Θ Ξ Γ Rm y S -> desc_chain Θ Ξ Γ S ys x X ->
    desc_chain Θ Ξ Γ R (y :: ys) x X.

(** A chain from an expression read through what it denotes is the chain
    from its description. *)
Lemma chain_desc_iff : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ ys P R x X, obs_root Ξ P -> mdenote Θ Ξ Γ P R ->
    mdenote Θ Ξ Γ (me_mem (me_mems P ys) x) X <-> desc_chain Θ Ξ Γ R ys x X.
Proof.
  intros Θ Ξ Hg Γ ys; induction ys as [| y ys IH]; intros * Hq HP; cbn [me_mems]; split.
  - intros HX; destruct (mdenote_mem_obs_inv _ _ Hg _ _ _ _ Hq HX) as (R0 & R0m & Γy & E & rd & R1 & HR0 & Hmd & He & Hed & Hr).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR0 _ HP) in Hmd.
    eapply desc_chain_last; [ exact Hmd | do 4 eexists; eauto ].
  - intros HX; inversion HX as [? Rm ? ? Hmd (Γy & E & rd & R1 & He & Hed & Hr) | ]; subst.
    eapply mdenote_mem; eassumption.
  - intros HX; destruct (mems_back _ _ Hg _ _ _ _ _ HX) as [S HS].
    destruct (mdenote_mem_obs_inv _ _ Hg _ _ _ _ Hq HS) as (R0 & R0m & Γy & E & rd & R1 & HR0 & Hmd & He & Hed & Hr).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR0 _ HP) in Hmd.
    eapply desc_chain_step; [ exact Hmd | do 4 eexists; eauto |].
    exact (proj1 (IH _ _ _ _ (obs_root_step _ _ Hg _ (ps_mem y) Hq) HS) HX).
  - intros HX; inversion HX as [| ? Rm ? ? ? S ? Hmd (Γy & E & rd & R1 & He & Hed & Hr) Hc]; subst.
    assert (HS : mdenote Θ Ξ Γ (me_mem P y) S) by (eapply mdenote_mem; eassumption).
    exact (proj2 (IH _ _ _ _ (obs_root_step _ _ Hg _ (ps_mem y) Hq) HS) Hc).
Qed.

(** Reading a member by its name keeps its kind and its module part. *)
Lemma reader_named_parts : forall L rd S, mdesc_kind (reader_named L rd S) = mdesc_kind S /\ mdesc_mod (reader_named L rd S) = mdesc_mod S.
Proof.
  intros L [Δ Φ | [|] [|] M] S; cbn [reader_named]; try (split; reflexivity).
  destruct L; [ rewrite mdesc_named_nil; split; reflexivity |].
  unfold mdesc_named; destruct S as [r A [] | | |]; split; reflexivity.
Qed.

(** An entry of a stored closed module denotes in every context. *)
Lemma closed_entry_ctx : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Θ' p T Φ Ns y Γy E rd Δ Γ o R, loc Θ Ξ p T Φ ->
    mdesc_entry (mdesc_closed Θ' p T Φ Ns) y = Some (Γy, E, rd) -> edenote Θ Ξ Δ o E R -> Γy = nil /\ edenote Θ Ξ Γ o E R.
Proof.
  intros * Hg * Hl He Hed.
  destruct (mdesc_entry_closed _ _ _ _ _ _ _ _ _ (loc_closed _ _ Hg _ _ _ Hl) He) as (-> & HsE & _).
  split; [ reflexivity | exact (edenote_closed_ctx _ _ (wf_gstack_closed _ _ Hg) _ _ _ _ _ HsE Hed) ].
Qed.

(** A selection from a canonical module abstracted over [L] is the
    selection under [L], abstracted: of one kind and module part. *)
Lemma desc_sel_up : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ L Dm y S, mdesc_canonical Θ Ξ Dm -> mdesc_is_mod Dm ->
    (desc_sel Θ Ξ Γ (mdesc_up L Dm) y S ->
     exists S0, desc_sel Θ Ξ (L ++ Γ) Dm y S0 /\ mdesc_kind S = mdesc_kind S0 /\ mdesc_mod S = option_map (mdesc_up L) (mdesc_mod S0)) /\
    (desc_sel Θ Ξ (L ++ Γ) Dm y S ->
     exists S1, desc_sel Θ Ξ Γ (mdesc_up L Dm) y S1 /\ mdesc_kind S1 = mdesc_kind S /\ mdesc_mod S1 = option_map (mdesc_up L) (mdesc_mod S)).
Proof.
  intros * Hg * Hc Him; unfold desc_sel; split.
  - intros (Γy & E & rd & R1 & He & Hed & Hr); rewrite mdesc_entry_up in He; rewrite mdesc_entry_path_up in Hed.
    destruct (mdesc_entry Dm y) as [[[Γy0 E0] rd0] |] eqn:He0; cbn in He; [ injection He as <- <- <- | discriminate ].
    rewrite mdesc_read_up in Hr; destruct (mdesc_read rd0 R1) as [S0 |] eqn:Hr0; cbn in Hr; [ injection Hr as <- | discriminate ].
    destruct (reader_named_parts L rd0 S0) as [Hk Hm].
    exists S0; split; [ exists Γy0, E0, rd0, R1; split; [ reflexivity | split; [| exact Hr0 ] ] |].
    + destruct Dm; cbn in Him; try contradiction.
      * rewrite List.app_assoc; exact Hed.
      * destruct (closed_entry_ctx _ _ Hg _ _ _ _ _ _ _ _ _ _ (L ++ Γ) _ _ Hc He0 Hed) as [-> Hed']; exact Hed'.
    + rewrite mdesc_kind_up, mdesc_mod_up, Hk, Hm; split; reflexivity.
  - intros (Γy0 & E & rd0 & R1 & He0 & Hed & Hr0).
    destruct (reader_named_parts L rd0 S) as [Hk Hm].
    exists (mdesc_up L (reader_named L rd0 S)); split; [| rewrite mdesc_kind_up, mdesc_mod_up, Hk, Hm; split; reflexivity ].
    exists (match Dm with mdesc_open _ _ _ => Γy0 ++ L | _ => Γy0 end), E, (reader_up L rd0), R1.
    rewrite mdesc_entry_up, He0, mdesc_entry_path_up, mdesc_read_up, Hr0; split; [ reflexivity | split; [| reflexivity ] ].
    destruct Dm; cbn in Him; try contradiction.
    + rewrite <- List.app_assoc; exact Hed.
    + destruct (closed_entry_ctx _ _ Hg _ _ _ _ _ _ _ _ _ _ Γ _ _ Hc He0 Hed) as [-> Hed']; exact Hed'.
Qed.

(** A selection from a canonical module description is canonical. *)
Lemma desc_sel_canonical : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ Rm y S, mdesc_canonical Θ Ξ Rm -> desc_sel Θ Ξ Γ Rm y S ->
    mdesc_canonical Θ Ξ S.
Proof.
  intros * Hg * Hc (Γy & E & rd & R1 & He & Hed & Hr).
  apply (mdesc_canonical_read _ _ rd R1 _); [| exact Hr ].
  apply (proj1 (proj2 (proj2 (mdenote_canon_all _ _ Hg))) _ _ _ _ Hed).
  intros qq pv Δ Φ' Ho HE.
  destruct Rm as [| Δ0 Φw Φx | Θ' p T Φ Ns |]; cbn in Ho; try discriminate.
  injection Ho as <-; cbn in He.
  destruct (gm_prefix_upto Φ y) as [[| Φ0 z E0 |] |] eqn:Hp; try discriminate; injection He as <- <- <-.
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & Hent).
  destruct E0 as [| pv0 [Δ1 [[|] Φ1 | ?]] | | |]; cbn [ge_read] in HE; try discriminate.
  injection HE as <- <- <-.
  right; exact (proj1 (loc_child_mod _ _ Hg _ _ _ Hc _ _ _ _ _ Hent)).
Qed.

(** Chains from a description whose module part is a canonical one
    abstracted over [L] are the chains under [L], of the same kinds. *)
Lemma desc_chain_up : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ L ys x R D, mdesc_canonical Θ Ξ D ->
    mdesc_mod R = option_map (mdesc_up L) (mdesc_mod D) ->
    (forall X, desc_chain Θ Ξ Γ R ys x X -> exists X0, desc_chain Θ Ξ (L ++ Γ) D ys x X0 /\ mdesc_kind X = mdesc_kind X0) /\
    (forall X0, desc_chain Θ Ξ (L ++ Γ) D ys x X0 -> exists X, desc_chain Θ Ξ Γ R ys x X /\ mdesc_kind X = mdesc_kind X0).
Proof.
  intros Θ Ξ Hg Γ L ys; induction ys as [| y ys IH]; intros x R D Hc HRD; split.
  - intros X HX; inversion HX as [? Rm ? ? Hm Hs |]; subst.
    rewrite Hm in HRD; destruct (mdesc_mod D) as [Dm |] eqn:HDm; cbn in HRD; [ injection HRD as -> | discriminate ].
    destruct (proj1 (desc_sel_up _ _ Hg _ _ _ _ _ (mdesc_canonical_mod _ _ _ _ Hc HDm) (mdesc_mod_is_mod _ _ HDm)) Hs)
      as (S0 & Hs0 & Hk & _).
    exists S0; split; [ eapply desc_chain_last; eassumption | exact Hk ].
  - intros X0 HX0; inversion HX0 as [? Dm ? ? HDm Hs0 |]; subst.
    destruct (proj2 (desc_sel_up _ _ Hg _ _ _ _ _ (mdesc_canonical_mod _ _ _ _ Hc HDm) (mdesc_mod_is_mod _ _ HDm)) Hs0)
      as (S1 & Hs1 & Hk & _).
    rewrite HDm in HRD; cbn in HRD.
    exists S1; split; [ eapply desc_chain_last; eassumption | exact Hk ].
  - intros X HX; inversion HX as [| ? Rm ? ? ? S ? Hm Hs Hc1]; subst.
    rewrite Hm in HRD; destruct (mdesc_mod D) as [Dm |] eqn:HDm; cbn in HRD; [ injection HRD as -> | discriminate ].
    pose proof (mdesc_canonical_mod _ _ _ _ Hc HDm) as HcDm.
    destruct (proj1 (desc_sel_up _ _ Hg _ _ _ _ _ HcDm (mdesc_mod_is_mod _ _ HDm)) Hs) as (S0 & Hs0 & _ & HmS).
    destruct (proj1 (IH x S S0 (desc_sel_canonical _ _ Hg _ _ _ _ HcDm Hs0) HmS) _ Hc1) as (X0 & HX0 & Hk).
    exists X0; split; [ eapply desc_chain_step; eassumption | exact Hk ].
  - intros X0 HX0; inversion HX0 as [| ? Dm ? ? ? S0 ? HDm Hs0 Hc1]; subst.
    pose proof (mdesc_canonical_mod _ _ _ _ Hc HDm) as HcDm.
    destruct (proj2 (desc_sel_up _ _ Hg _ _ _ _ _ HcDm (mdesc_mod_is_mod _ _ HDm)) Hs0) as (S1 & Hs1 & _ & HmS).
    destruct (proj2 (IH x S1 S0 (desc_sel_canonical _ _ Hg _ _ _ _ HcDm Hs0) HmS) _ Hc1) as (X & HX & Hk).
    rewrite HDm in HRD; cbn in HRD.
    exists X; split; [ eapply desc_chain_step; eassumption | exact Hk ].
Qed.

(** A module has one reading at each name. *)
Lemma desc_sel_functional : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ Rm y S S', desc_sel Θ Ξ Γ Rm y S -> desc_sel Θ Ξ Γ Rm y S' -> S = S'.
Proof.
  intros * Hg * (Γy & E & rd & R1 & He & Hed & Hr) (Γy' & E' & rd' & R1' & He' & Hed' & Hr').
  rewrite He in He'; injection He' as <- <- <-.
  rewrite (proj1 (proj2 (proj2 (mdenote_functional_all _ _ Hg))) _ _ _ _ Hed _ Hed') in Hr; congruence.
Qed.

(** A selection from a module abstracted over [L], moved by a substitution
    into [L ++ Γ], is there before the move, where the abstraction is
    well formed. *)
Lemma desc_sel_back : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ L Dm Ψ σ y X', mdesc_canonical Θ Ξ Dm -> mdesc_is_mod Dm ->
    desc_ok Θ Ξ Γ (mdesc_up L Dm) -> desc_sel Θ Ξ Ψ (mdesc_sub Dm σ) y X' -> exists X, desc_sel Θ Ξ (L ++ Γ) Dm y X.
Proof.
  intros * Hg * Hc Him Hok (Γy & E & rd & R1 & He & Hed & Hr).
  pose proof (gctx_valid_syn _ _ Hg) as Hv.
  enough (HS : exists S, desc_sel Θ Ξ Γ (mdesc_up L Dm) y S)
    by (destruct HS as [S HS]; destruct (proj1 (desc_sel_up _ _ Hg _ _ _ _ _ Hc Him) HS) as (S0 & HS0 & _); eauto).
  destruct Dm as [| Δ Φw Φx | Θ' p T Φ Ns |]; cbn in Him; try contradiction; cbn [mdesc_up] in Hok |- *.
  - (* an open body: the entry, denoted by typing *)
    cbn [mdesc_sub] in He.
    destruct (proj1 (open_entry_iff _ _ _ _ _ _ _) He) as (Φ0w & Hp & HE & _ & _).
    destruct (gm_prefix_sub_inv _ _ _ _ _ Hp) as (Φ0 & E0 & Hp0 & _ & ->).
    apply entry_readable_sub in HE.
    inversion Hok as [| Γ0 Δ0 Φw0 Φx0 l HΦ Hno _ _ Hsh _ _ _ _ _ | |]; subst.
    destruct (entry_denotes_exists _ _ _ _ _ _ _ HΦ Hp0 HE) as (R1g & HR1g).
    destruct (body_shape_fill _ _ (gm_noopen_nopens _ Hno) Hsh) as [Hf _].
    destruct (fill_prefix _ _ _ _ Hf Hp0) as [τ Hτ].
    eexists; exists (body_ctx Φ0 ++ Δ ++ L), E0, (reader_open (Δ ++ L) Φ0), R1g; split; [| split ].
    + apply (proj2 (open_entry_iff _ _ _ _ _ _ _)); exists Φ0; repeat split; assumption.
    + rewrite <- !List.app_assoc; rewrite <- List.app_assoc in HR1g; exact HR1g.
    + cbn; rewrite Hτ; reflexivity.
  - (* a closed body: the same entry, read at the arguments recorded *)
    cbn in He; destruct (gm_prefix_upto Φ y) as [[| Φ0 z E0 |] |] eqn:Hp; try discriminate; injection He as <- <- <-.
    assert (Heg : mdesc_entry (mdesc_closed (Θ' ++ L) p T Φ Ns) y =
                  Some (nil, ge_read T E0, reader_closed (Θ' ++ L) Ns (apps (a_mem (qname_mod p) y) Ns)))
      by (cbn; rewrite Hp; reflexivity).
    cbn [mdesc_sub mdesc_entry_path] in Hed.
    destruct (closed_entry_ctx _ _ Hg _ _ _ _ _ _ _ _ _ _ Γ _ _ Hc Heg Hed) as [_ Hedg].
    destruct (closed_entry_read_exists _ _ Hg Hv Γ _ p T Φ Ns y nil _ _ R1 Hok Heg Hedg) as (R' & Hr').
    exists R', nil, (ge_read T E0), (reader_closed (Θ' ++ L) Ns (apps (a_mem (qname_mod p) y) Ns)), R1.
    split; [ exact Heg | split; [ exact Hedg | exact Hr' ] ].
Qed.

(** A well-formed selection from what abstracts a module is well formed. *)
Lemma desc_sel_ok : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ Rm y S, desc_ok Θ Ξ Γ Rm -> desc_sel Θ Ξ Γ Rm y S -> desc_ok Θ Ξ Γ S.
Proof.
  intros * Hg * Hok (Γy & E & rd & R1 & He & Hed & Hr).
  exact (desc_ok_sel _ _ Hg (gctx_valid_syn _ _ Hg) _ _ _ _ _ _ _ _ Hok He Hed Hr).
Qed.

(** Chains from a scoped canonical description under [L], abstracted into
    a well-formed one, moved by a substitution: the chains, moved. *)
Lemma desc_chain_sub : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall ys Γ L x D Rt Ψ σ, ⊢ Θ ⍮ Ξ ⍮ L ++ Γ ->
    mdesc_canonical Θ Ξ D -> mdesc_scoped (List.length (L ++ Γ)) D -> mdesc_mod Rt = option_map (mdesc_up L) (mdesc_mod D) ->
    desc_ok Θ Ξ Γ Rt -> sub_mod_compat σ Ψ (L ++ Γ) ->
    (forall X, desc_chain Θ Ξ (L ++ Γ) D ys x X -> desc_chain Θ Ξ Ψ (mdesc_sub D σ) ys x (mdesc_sub X σ)) /\
    (forall X', desc_chain Θ Ξ Ψ (mdesc_sub D σ) ys x X' -> exists X, desc_chain Θ Ξ (L ++ Γ) D ys x X /\ X' = mdesc_sub X σ).
Proof.
  intros Θ Ξ Hg ys; induction ys as [| y ys IH]; intros * HΓ Hc Hsc HRt Hok Hmc;
    pose proof (wf_gstack_closed _ _ Hg) as Hcl;
    pose proof (slots_ok_ctx _ (wf_ctx_scoped _ _ _ HΓ)) as HSl;
    (assert (Hfw : forall Dm y S, mdesc_mod D = Some Dm -> desc_sel Θ Ξ (L ++ Γ) Dm y S ->
                   desc_sel Θ Ξ Ψ (mdesc_sub Dm σ) y (mdesc_sub S σ));
     [ intros * Hm (Γy & E & rd & R1 & He & Hed & Hr);
       destruct (desc_sel_sub _ _ Hcl _ _ _ _ _ _ _ _ _ _ _ _ HSl Hsc Hm He Hed Hr Hmc) as (Γy' & E' & rd' & R0' & He' & Hed' & Hr');
       exists Γy', E', rd', R0'; auto |]);
    (assert (Hbk : forall Dm y X', mdesc_mod D = Some Dm -> desc_sel Θ Ξ Ψ (mdesc_sub Dm σ) y X' ->
                   exists X, desc_sel Θ Ξ (L ++ Γ) Dm y X /\ X' = mdesc_sub X σ);
     [ intros * Hm HX'; rewrite Hm in HRt; cbn in HRt;
       destruct (desc_sel_back _ _ Hg _ _ _ _ _ _ _ (mdesc_canonical_mod _ _ _ _ Hc Hm) (mdesc_mod_is_mod _ _ Hm)
                   (desc_ok_mod _ _ Hg _ _ _ Hok HRt) HX') as [X HX];
       exists X; split; [ exact HX | exact (desc_sel_functional _ _ Hg _ _ _ _ _ HX' (Hfw _ _ _ Hm HX)) ] |]);
    (assert (Hinv : forall Dm y S, mdesc_mod D = Some Dm -> desc_sel Θ Ξ (L ++ Γ) Dm y S ->
                    mdesc_canonical Θ Ξ S /\ mdesc_scoped (List.length (L ++ Γ)) S /\
                    exists St, mdesc_mod St = option_map (mdesc_up L) (mdesc_mod S) /\ desc_ok Θ Ξ Γ St);
     [ intros * Hm HS; pose proof (mdesc_canonical_mod _ _ _ _ Hc Hm) as HcDm;
       split; [ exact (desc_sel_canonical _ _ Hg _ _ _ _ HcDm HS) | split ];
       [ destruct HS as (Γy & E & rd & R1 & He & Hed & Hr); exact (desc_sel_scoped _ _ Hcl _ _ _ _ _ _ _ _ _ _ HSl Hsc Hm He Hed Hr)
       | rewrite Hm in HRt; cbn in HRt;
         destruct (proj2 (desc_sel_up _ _ Hg _ _ _ _ _ HcDm (mdesc_mod_is_mod _ _ Hm)) HS) as (S1 & HS1 & _ & HmS1);
         exists S1; split; [ exact HmS1 | exact (desc_sel_ok _ _ Hg _ _ _ _ (desc_ok_mod _ _ Hg _ _ _ Hok HRt) HS1) ] ] |]);
    split.
  - intros X HX; inversion HX as [? Dm ? ? Hm Hs |]; subst.
    eapply desc_chain_last; [ exact (mdesc_mod_sub _ _ σ Hm) | exact (Hfw _ _ _ Hm Hs) ].
  - intros X' HX'; inversion HX' as [? Rm' ? ? Hm' Hs' |]; subst.
    destruct (mdesc_mod_sub_inv _ _ _ Hm') as (Dm & Hm & ->).
    destruct (Hbk _ _ _ Hm Hs') as (X & HX & ->); exists X; split; [ eapply desc_chain_last; eassumption | reflexivity ].
  - intros X HX; inversion HX as [| ? Dm ? ? ? S ? Hm Hs Hc1]; subst.
    destruct (Hinv _ _ _ Hm Hs) as (HcS & HsS & St & HSt & HokSt).
    eapply desc_chain_step; [ exact (mdesc_mod_sub _ _ σ Hm) | exact (Hfw _ _ _ Hm Hs) |].
    exact (proj1 (IH _ _ _ _ _ _ _ HΓ HcS HsS HSt HokSt Hmc) _ Hc1).
  - intros X' HX'; inversion HX' as [| ? Rm' ? ? ? S' ? Hm' Hs' Hc1]; subst.
    destruct (mdesc_mod_sub_inv _ _ _ Hm') as (Dm & Hm & ->).
    destruct (Hbk _ _ _ Hm Hs') as (S & HS & ->).
    destruct (Hinv _ _ _ Hm HS) as (HcS & HsS & St & HSt & HokSt).
    destruct (proj2 (IH _ _ _ _ _ _ _ HΓ HcS HsS HSt HokSt Hmc) _ Hc1) as (X & HX & ->).
    exists X; split; [ eapply desc_chain_step; eassumption | reflexivity ].
Qed.

(** A module abstracted over one more parameter is scoped under it. *)
Lemma up_last_scoped : forall n e D, mdesc_scoped n (mdesc_up (e :: nil) D) -> mdesc_is_mod D -> mdesc_scoped (S n) D.
Proof.
  intros n e [| Δ Φ Φx | Θ' p T Φ Ns |] HD Him; cbn in Him; try contradiction; cbn [mdesc_up mdesc_scoped] in HD |- *.
  - destruct HD as (H1 & H2 & H3); rewrite gunit_scoped_mk in H1, H2 |- *; rewrite gunit_scoped_mk.
    destruct H1 as [H1a H1b]; destruct H2 as [H2a H2b]; rewrite ctx_scoped_app in H1a, H2a; cbn in H1a, H2a.
    rewrite List.length_app in H1b, H2b; cbn in H1b, H2b; rewrite <- Nat.add_assoc in H1b, H2b; cbn in H1b, H2b.
    cbn; split; [ split; [ exact (proj1 H1a) | exact H1b ] | split; [ split; [ exact (proj1 H2a) | exact H2b ] | exact H3 ] ].
  - destruct HD as (H1 & H2 & H3); rewrite ctx_scoped_app in H1; cbn in H1.
    rewrite List.length_app in H3; cbn in H3; rewrite <- Nat.add_assoc in H3; cbn in H3.
    split; [ exact (proj1 H1) | split; [ exact H2 | exact H3 ] ].
Qed.

(** A module over one more parameter, and itself with the parameter given
    [N]: chains of the same kinds. *)
Lemma desc_chain_at_up : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ κ B D N ys x, ⊢ Θ ⍮ Ξ ⍮ Γ ▹{κ} B -> mdesc_canonical Θ Ξ D ->
    mdesc_scoped (S (List.length Γ)) D -> mdesc_is_mod D -> desc_ok Θ Ξ Γ (mdesc_up (ce_ass κ B :: nil) D) ->
    (forall X, desc_chain Θ Ξ Γ (mdesc_up (ce_ass κ B :: nil) D) ys x X ->
       exists X', desc_chain Θ Ξ Γ (mdesc_sub D (Id,,N)) ys x X' /\ mdesc_kind X = mdesc_kind X') /\
    (forall X', desc_chain Θ Ξ Γ (mdesc_sub D (Id,,N)) ys x X' ->
       exists X, desc_chain Θ Ξ Γ (mdesc_up (ce_ass κ B :: nil) D) ys x X /\ mdesc_kind X = mdesc_kind X').
Proof.
  intros * Hg * HΓ Hc Hsc Him Hok.
  assert (HR : mdesc_mod (mdesc_up (ce_ass κ B :: nil) D) = option_map (mdesc_up (ce_ass κ B :: nil)) (mdesc_mod D))
    by (rewrite mdesc_mod_up; reflexivity).
  pose proof (desc_chain_up _ _ Hg Γ (ce_ass κ B :: nil) ys x _ _ Hc HR) as [U1 U2].
  pose proof (desc_chain_sub _ _ Hg ys Γ (ce_ass κ B :: nil) x D _ Γ (Id,,N) HΓ Hc Hsc HR Hok (sub_mod_compat_single _ _ _ _))
    as [S1 S2].
  split.
  - intros X HX; destruct (U1 _ HX) as (X0 & HX0 & Hk).
    exists (mdesc_sub X0 (Id,,N)); split; [ exact (S1 _ HX0) | rewrite mdesc_kind_sub; exact Hk ].
  - intros X' HX'; destruct (S2 _ HX') as (X0 & HX0 & ->); destruct (U2 _ HX0) as (X & HX & Hk).
    exists X; split; [ exact HX | rewrite mdesc_kind_sub; exact Hk ].
Qed.

(** What has no module part, applied, has none. *)
Lemma at_mod_none : forall X N X', mdesc_mod X = None -> mdesc_at X N = Some X' -> mdesc_mod X' = None.
Proof.
  induction X as [r A om | Δ Φ Φx | Θ0 p T Φ Ns | Θd A M Rm IH]; intros N X' Hn Ha; cbn in Hn; try discriminate.
  - cbn in Ha; destruct (pi_view A) as [[? C] |]; [| discriminate ].
    destruct om as [M |]; [ destruct (fn_view M); [| discriminate ] |]; injection Ha as <-; reflexivity.
  - cbn in Ha; destruct (mdesc_at Rm N) as [Rm' |] eqn:E; [| discriminate ].
    pose proof (IH _ _ Hn E) as Hn'.
    destruct (tele_split (rev Θd)) as [[[? ?] ?] |]; injection Ha as <-; cbn; exact Hn'.
Qed.

(** Module parts of what is applied and of the application, applied. *)
Lemma at_mod_rel : forall X N X', mdesc_at X N = Some X' ->
    (forall Xm, mdesc_mod X = Some Xm -> exists Xm', mdesc_mod X' = Some Xm' /\ mdesc_at Xm N = Some Xm') /\
    (forall Xm', mdesc_mod X' = Some Xm' -> exists Xm, mdesc_mod X = Some Xm /\ mdesc_at Xm N = Some Xm').
Proof.
  intros * Ha; split.
  - intros Xm Hm; destruct (proj1 (mdesc_at_mod_part _ _ N Hm) _ Ha) as (Xm1 & Ha1 & Hm1); eauto.
  - intros Xm' Hm'; destruct (mdesc_mod X) as [Xm |] eqn:Hm.
    + destruct (proj1 (mdesc_at_mod_part _ _ N Hm) _ Ha) as (Xm1 & Ha1 & Hm1); rewrite Hm1 in Hm'; injection Hm' as <-; eauto.
    + rewrite (at_mod_none _ _ _ Hm Ha) in Hm'; discriminate.
Qed.

(** What an entry denotes is no definition with a module part over
    outside parameters. *)
Lemma edenote_dm_nil : forall Θ Ξ Γ o E R, edenote Θ Ξ Γ o E R -> forall Θd A M Rm, R = mdesc_dm Θd A M Rm -> Θd = nil.
Proof.
  intros * Hed * ->; inversion Hed as [| ? ? ? ? ? Hu | | ? ? ? ? ? ? ? ? Hu | ]; subst; try reflexivity.
  pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Him; cbn in Him; contradiction.
Qed.

(** Read at one more argument, a description's module part is its module
    part read there, applied to it. *)
Lemma ats_read_snoc_rel : forall R1 Ns N X X', (forall Θd A M Rm, R1 = mdesc_dm Θd A M Rm -> Θd = nil) ->
    mdesc_ats_read R1 Ns = Some X -> mdesc_ats_read R1 (Ns ++ N :: nil) = Some X' ->
    (forall Xm, mdesc_mod X = Some Xm -> exists Xm', mdesc_mod X' = Some Xm' /\ mdesc_at Xm N = Some Xm') /\
    (forall Xm', mdesc_mod X' = Some Xm' -> exists Xm, mdesc_mod X = Some Xm /\ mdesc_at Xm N = Some Xm').
Proof.
  intros * Hdm Ha Ha'.
  destruct R1 as [r A om | Δ Φ Φx | Θ0 p T Φ Ns0 | Θd A M Rm];
    try (rewrite mdesc_ats_read_other in Ha, Ha' by (intros; discriminate);
         rewrite mdesc_ats_snoc, Ha in Ha'; exact (at_mod_rel _ _ _ Ha')).
  pose proof (Hdm _ _ _ _ eq_refl) as ->.
  cbn [mdesc_ats_read] in Ha, Ha'.
  destruct (mdesc_term_part_ats (mdesc_term ak_relevant A (Some M)) Ns) as [[? ? [?|] | | |] |]; cbn in Ha; try discriminate.
  destruct (mdesc_ats Rm Ns) as [Rm1 |] eqn:E1; cbn in Ha; [ injection Ha as <- | discriminate ].
  destruct (mdesc_term_part_ats (mdesc_term ak_relevant A (Some M)) (Ns ++ N :: nil)) as [[? ? [?|] | | |] |]; cbn in Ha'; try discriminate.
  destruct (mdesc_ats Rm (Ns ++ N :: nil)) as [Rm2 |] eqn:E2; cbn in Ha'; [ injection Ha' as <- | discriminate ].
  rewrite mdesc_ats_snoc, E1 in E2; cbn [mdesc_mod]; exact (at_mod_rel _ _ _ E2).
Qed.

(** A typed module given an argument: one abstracted over the parameter
    the argument fills, substituted; or a closed module with no outside
    parameter, given one more argument. *)
Lemma mod_at_view : forall Θ Ξ Γ Rm N Rm', desc_ok Θ Ξ Γ Rm -> mdesc_is_mod Rm -> mdesc_at Rm N = Some Rm' ->
    (exists κ B D, Rm = mdesc_up (ce_ass κ B :: nil) D /\ Rm' = mdesc_sub D (Id,,N) /\ mdesc_is_mod D /\ ⊢ Θ ⍮ Ξ ⍮ Γ ▹{κ} B) \/
    (exists p T Φ Ns, Rm = mdesc_closed nil p T Φ Ns /\ Rm' = mdesc_closed nil p T Φ (Ns ++ N :: nil)).
Proof.
  intros * Hok Him Ha.
  destruct Rm as [| Δ Φw Φ | Θ' p T Φ Ns |]; cbn in Him; try contradiction.
  - inversion Hok as [| ? ? ? ? ? HΦ _ _ HaΔ | |]; subst.
    destruct Δ as [| e Δ0 _] using List.rev_ind; [ cbn in Ha; discriminate |].
    unfold all_assumptions in HaΔ; apply List.Forall_app in HaΔ as [_ He]; apply List.Forall_cons_iff in He as [(κ & B & ->) _].
    left; exists κ, B, (mdesc_open Δ0 Φw Φ); split; [ reflexivity | split; [| split; [ exact I |] ] ].
    + replace (mdesc_open (Δ0 ++ ce_ass κ B :: nil) Φw Φ) with (mdesc_up (nil ++ ce_ass κ B :: nil) (mdesc_open Δ0 Φw Φ)) in Ha
        by reflexivity.
      rewrite mdesc_at_up in Ha; cbn [tele_sub List.length sb_qn] in Ha; rewrite mdesc_up_nil in Ha; injection Ha as <-; reflexivity.
    + rewrite <- List.app_assoc in HΦ; cbn [List.app] in HΦ; rewrite List.app_assoc in HΦ; exact (ctx_app_wf_tail _ _ _ _ HΦ).
  - inversion Hok as [| | ? ? ? ? ? ? ? ? ? _ _ _ _ _ _ HΘ' _ HaΘ' |]; subst.
    destruct Θ' as [| e Θr _] using List.rev_ind.
    + right; exists p, T, Φ, Ns; split; [ reflexivity |].
      cbn in Ha; injection Ha as <-; rewrite map_exp_sub_id; reflexivity.
    + unfold all_assumptions in HaΘ'; apply List.Forall_app in HaΘ' as [_ He]; apply List.Forall_cons_iff in He as [(κ & B & ->) _].
      left; exists κ, B, (mdesc_closed Θr p T Φ Ns); split; [ reflexivity | split; [| split; [ exact I |] ] ].
      * replace (mdesc_closed (Θr ++ ce_ass κ B :: nil) p T Φ Ns) with (mdesc_up (nil ++ ce_ass κ B :: nil) (mdesc_closed Θr p T Φ Ns)) in Ha
          by reflexivity.
        rewrite mdesc_at_up in Ha; cbn [tele_sub List.length sb_qn] in Ha; rewrite mdesc_up_nil in Ha; injection Ha as <-; reflexivity.
      * rewrite <- List.app_assoc in HΘ'; cbn [List.app] in HΘ'; exact (ctx_app_wf_tail _ _ _ _ HΘ').
Qed.

(** [at_related N S S']: [S'] is [S] given [N] as far as members go: of
    one kind, the module part of each that of the other given [N]. *)
Record at_related (N : exp) (S S' : mdesc) : Prop :=
  { (** Of one kind *)
    at_related_kind : mdesc_kind S = mdesc_kind S';
    (** The module part of [S], given [N], is that of [S'] *)
    at_related_mod : forall Sm, mdesc_mod S = Some Sm -> exists Sm', mdesc_mod S' = Some Sm' /\ mdesc_at Sm N = Some Sm';
    (** The module part of [S'] is that of [S], given [N] *)
    at_related_mod_back : forall Sm', mdesc_mod S' = Some Sm' -> exists Sm, mdesc_mod S = Some Sm /\ mdesc_at Sm N = Some Sm' }.

(** An entry read at the arguments, and at one more: related. *)
Lemma closed_nil_read_rel : forall R1 Ns N M M' S S', (forall Θd A Md Rm, R1 = mdesc_dm Θd A Md Rm -> Θd = nil) ->
    mdesc_read (reader_closed nil Ns M) R1 = Some S -> mdesc_read (reader_closed nil (Ns ++ N :: nil) M') R1 = Some S' ->
    at_related N S S'.
Proof.
  intros * Hdm Hr Hr'; cbn [mdesc_read] in Hr, Hr'.
  destruct (mdesc_ats_read R1 Ns) as [X |] eqn:Ha; cbn in Hr; [ injection Hr as <- | discriminate ].
  destruct (mdesc_ats_read R1 (Ns ++ N :: nil)) as [X' |] eqn:Ha'; cbn in Hr'; [ injection Hr' as <- | discriminate ].
  rewrite !mdesc_up_nil; destruct (ats_read_snoc_rel _ _ _ _ _ Hdm Ha Ha') as [Hm Hm'].
  constructor; rewrite ?mdesc_kind_named, ?mdesc_mod_named.
  - rewrite (mdesc_kind_ats_read _ _ _ Hdm Ha), (mdesc_kind_ats_read _ _ _ Hdm Ha'); reflexivity.
  - exact Hm.
  - exact Hm'.
Qed.

(** A closed module with no outside parameter, and given one more
    argument, both typed: related selections. *)
Lemma closed_nil_sel_at : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ p T Φ Ns N y,
    desc_ok Θ Ξ Γ (mdesc_closed nil p T Φ Ns) -> desc_ok Θ Ξ Γ (mdesc_closed nil p T Φ (Ns ++ N :: nil)) ->
    (forall S, desc_sel Θ Ξ Γ (mdesc_closed nil p T Φ Ns) y S ->
       exists S', desc_sel Θ Ξ Γ (mdesc_closed nil p T Φ (Ns ++ N :: nil)) y S' /\ at_related N S S') /\
    (forall S', desc_sel Θ Ξ Γ (mdesc_closed nil p T Φ (Ns ++ N :: nil)) y S' ->
       exists S, desc_sel Θ Ξ Γ (mdesc_closed nil p T Φ Ns) y S /\ at_related N S S').
Proof.
  intros * Hg * Hok Hok'; pose proof (gctx_valid_syn _ _ Hg) as Hv; unfold desc_sel; split.
  - intros S (Γy & E & rd & R1 & He & Hed & Hr).
    cbn in He; destruct (gm_prefix_upto Φ y) as [[| Φ0 z E0 |] |] eqn:Hp; try discriminate; injection He as <- <- <-.
    assert (Heg : mdesc_entry (mdesc_closed nil p T Φ (Ns ++ N :: nil)) y =
                  Some (nil, ge_read T E0, reader_closed nil (Ns ++ N :: nil) (apps (a_mem (qname_mod p) y) (Ns ++ N :: nil))))
      by (cbn; rewrite Hp; reflexivity).
    cbn [mdesc_entry_path] in Hed.
    destruct (closed_entry_read_exists _ _ Hg Hv Γ nil p T Φ (Ns ++ N :: nil) y nil _ _ R1 Hok' Heg Hed) as (S' & Hr').
    exists S'; split; [ exists nil, (ge_read T E0), (reader_closed nil (Ns ++ N :: nil) (apps (a_mem (qname_mod p) y) (Ns ++ N :: nil))), R1;
                        split; [ exact Heg | split; [ exact Hed | exact Hr' ] ] |].
    exact (closed_nil_read_rel _ _ _ _ _ _ _ (edenote_dm_nil _ _ _ _ _ _ Hed) Hr Hr').
  - intros S' (Γy & E & rd & R1 & He & Hed & Hr').
    cbn in He; destruct (gm_prefix_upto Φ y) as [[| Φ0 z E0 |] |] eqn:Hp; try discriminate; injection He as <- <- <-.
    assert (Heg : mdesc_entry (mdesc_closed nil p T Φ Ns) y =
                  Some (nil, ge_read T E0, reader_closed nil Ns (apps (a_mem (qname_mod p) y) Ns)))
      by (cbn; rewrite Hp; reflexivity).
    cbn [mdesc_entry_path] in Hed.
    destruct (closed_entry_read_exists _ _ Hg Hv Γ nil p T Φ Ns y nil _ _ R1 Hok Heg Hed) as (S & Hr).
    exists S; split; [ exists nil, (ge_read T E0), (reader_closed nil Ns (apps (a_mem (qname_mod p) y) Ns)), R1;
                       split; [ exact Heg | split; [ exact Hed | exact Hr ] ] |].
    exact (closed_nil_read_rel _ _ _ _ _ _ _ (edenote_dm_nil _ _ _ _ _ _ Hed) Hr Hr').
Qed.

(** Chains from a description are those from its module part. *)
Lemma desc_chain_mod_eq : forall Θ Ξ Γ R R0 ys x X, mdesc_mod R = mdesc_mod R0 ->
    desc_chain Θ Ξ Γ R ys x X -> desc_chain Θ Ξ Γ R0 ys x X.
Proof.
  intros * Hm HX; inversion HX; subst; [ eapply desc_chain_last | eapply desc_chain_step ]; try eassumption; congruence.
Qed.

(** A selection from a scoped module is scoped. *)
Lemma desc_sel_scoped_mod : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ Rm y S, ⊢ Θ ⍮ Ξ ⍮ Γ -> mdesc_is_mod Rm ->
    mdesc_scoped (List.length Γ) Rm -> desc_sel Θ Ξ Γ Rm y S -> mdesc_scoped (List.length Γ) S.
Proof.
  intros * Hg * HΓ Him Hsc (Γy & E & rd & R1 & He & Hed & Hr).
  exact (desc_sel_scoped _ _ (wf_gstack_closed _ _ Hg) _ _ _ _ _ _ _ _ _ _ (slots_ok_ctx _ (wf_ctx_scoped _ _ _ HΓ)) Hsc
           (mdesc_is_mod_mod _ Him) He Hed Hr).
Qed.

(** Chains from a typed module, and from it given an argument, typed: of
    the same kinds. *)
Lemma mod_chain_at : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall ys Γ N x Rm Rm', ⊢ Θ ⍮ Ξ ⍮ Γ -> mdesc_canonical Θ Ξ Rm ->
    mdesc_scoped (List.length Γ) Rm -> mdesc_is_mod Rm -> desc_ok Θ Ξ Γ Rm -> desc_ok Θ Ξ Γ Rm' -> mdesc_at Rm N = Some Rm' ->
    (forall X, desc_chain Θ Ξ Γ Rm ys x X -> exists X', desc_chain Θ Ξ Γ Rm' ys x X' /\ mdesc_kind X = mdesc_kind X') /\
    (forall X', desc_chain Θ Ξ Γ Rm' ys x X' -> exists X, desc_chain Θ Ξ Γ Rm ys x X /\ mdesc_kind X = mdesc_kind X').
Proof.
  intros Θ Ξ Hg ys; induction ys as [| y ys IH]; intros * HΓ Hc Hsc Him Hok Hok' Ha;
    destruct (mod_at_view _ _ _ _ _ _ Hok Him Ha) as [(κ & B & D & -> & -> & HimD & HΓB) | (p & T & Φ & Ns & -> & ->)];
    try (assert (HcD : mdesc_canonical Θ Ξ D) by (destruct D; cbn in HimD |- *; try contradiction; exact Hc);
         exact (desc_chain_at_up _ _ Hg _ _ _ _ N _ x HΓB HcD (up_last_scoped _ _ _ Hsc HimD) HimD Hok)).
  - split.
    + intros X HX; inversion HX as [? Rm0 ? ? Hm Hs |]; subst; cbn in Hm; injection Hm as <-.
      destruct (proj1 (closed_nil_sel_at _ _ Hg _ _ _ _ _ _ x Hok Hok') _ Hs) as (S' & Hs' & Hr).
      exists S'; split; [ eapply desc_chain_last; [ reflexivity | exact Hs' ] | exact (at_related_kind _ _ _ Hr) ].
    + intros X' HX'; inversion HX' as [? Rm0 ? ? Hm Hs' |]; subst; cbn in Hm; injection Hm as <-.
      destruct (proj2 (closed_nil_sel_at _ _ Hg _ _ _ _ _ _ x Hok Hok') _ Hs') as (S & Hs & Hr).
      exists S; split; [ eapply desc_chain_last; [ reflexivity | exact Hs ] | exact (at_related_kind _ _ _ Hr) ].
  - assert (Hrec : forall S S', desc_sel Θ Ξ Γ (mdesc_closed nil p T Φ Ns) y S ->
                   desc_sel Θ Ξ Γ (mdesc_closed nil p T Φ (Ns ++ N :: nil)) y S' -> at_related N S S' ->
                   (forall X, desc_chain Θ Ξ Γ S ys x X -> exists X', desc_chain Θ Ξ Γ S' ys x X' /\ mdesc_kind X = mdesc_kind X') /\
                   (forall X', desc_chain Θ Ξ Γ S' ys x X' -> exists X, desc_chain Θ Ξ Γ S ys x X /\ mdesc_kind X = mdesc_kind X')).
    { intros S S' Hs Hs' Hr.
      pose proof (desc_sel_ok _ _ Hg _ _ _ _ Hok Hs) as HokS; pose proof (desc_sel_ok _ _ Hg _ _ _ _ Hok' Hs') as HokS'.
      pose proof (desc_sel_canonical _ _ Hg _ _ _ _ Hc Hs) as HcS.
      pose proof (desc_sel_scoped_mod _ _ Hg _ _ _ _ HΓ Him Hsc Hs) as HscS.
      assert (Hpart : forall Sm, mdesc_mod S = Some Sm ->
                exists Sm', mdesc_mod S' = Some Sm' /\
                  (forall X, desc_chain Θ Ξ Γ Sm ys x X -> exists X', desc_chain Θ Ξ Γ Sm' ys x X' /\ mdesc_kind X = mdesc_kind X') /\
                  (forall X', desc_chain Θ Ξ Γ Sm' ys x X' -> exists X, desc_chain Θ Ξ Γ Sm ys x X /\ mdesc_kind X = mdesc_kind X')).
      { intros Sm HSm; destruct (at_related_mod _ _ _ Hr _ HSm) as (Sm' & HSm' & HaS).
        exists Sm'; split; [ exact HSm' |].
        exact (IH _ _ _ _ _ HΓ (mdesc_canonical_mod _ _ _ _ HcS HSm) (mdesc_mod_scoped _ _ _ HscS HSm) (mdesc_mod_is_mod _ _ HSm)
                 (desc_ok_mod _ _ Hg _ _ _ HokS HSm) (desc_ok_mod _ _ Hg _ _ _ HokS' HSm') HaS). }
      split.
      - intros X HX; assert (HSm : exists Sm, mdesc_mod S = Some Sm) by (inversion HX; eauto).
        destruct HSm as (Sm & HSm); destruct (Hpart _ HSm) as (Sm' & HSm' & P1 & _).
        assert (HmS : mdesc_mod S = mdesc_mod Sm) by (rewrite HSm, (mdesc_is_mod_mod _ (mdesc_mod_is_mod _ _ HSm)); reflexivity).
        destruct (P1 _ (desc_chain_mod_eq _ _ _ _ _ _ _ _ HmS HX)) as (X' & HX' & Hk).
        assert (HmS' : mdesc_mod Sm' = mdesc_mod S') by (rewrite HSm', (mdesc_is_mod_mod _ (mdesc_mod_is_mod _ _ HSm')); reflexivity).
        exists X'; split; [ exact (desc_chain_mod_eq _ _ _ _ _ _ _ _ HmS' HX') | exact Hk ].
      - intros X' HX'; assert (HSm' : exists Sm', mdesc_mod S' = Some Sm') by (inversion HX'; eauto).
        destruct HSm' as (Sm' & HSm'); destruct (at_related_mod_back _ _ _ Hr _ HSm') as (Sm & HSm & _).
        destruct (Hpart _ HSm) as (Sm'' & HSm'' & _ & P2); rewrite HSm' in HSm''; injection HSm'' as <-.
        assert (HmS' : mdesc_mod S' = mdesc_mod Sm') by (rewrite HSm', (mdesc_is_mod_mod _ (mdesc_mod_is_mod _ _ HSm')); reflexivity).
        destruct (P2 _ (desc_chain_mod_eq _ _ _ _ _ _ _ _ HmS' HX')) as (X & HX & Hk).
        assert (HmS : mdesc_mod Sm = mdesc_mod S) by (rewrite HSm, (mdesc_is_mod_mod _ (mdesc_mod_is_mod _ _ HSm)); reflexivity).
        exists X; split; [ exact (desc_chain_mod_eq _ _ _ _ _ _ _ _ HmS HX) | exact Hk ]. }
    split.
    + intros X HX; inversion HX as [| ? Rm0 ? ? ? S ? Hm Hs Hc1]; subst; cbn in Hm; injection Hm as <-.
      destruct (proj1 (closed_nil_sel_at _ _ Hg _ _ _ _ _ _ y Hok Hok') _ Hs) as (S' & Hs' & Hr).
      destruct (proj1 (Hrec _ _ Hs Hs' Hr) _ Hc1) as (X' & HX' & Hk).
      exists X'; split; [ eapply desc_chain_step; [ reflexivity | exact Hs' | exact HX' ] | exact Hk ].
    + intros X' HX'; inversion HX' as [| ? Rm0 ? ? ? S' ? Hm Hs' Hc1]; subst; cbn in Hm; injection Hm as <-.
      destruct (proj2 (closed_nil_sel_at _ _ Hg _ _ _ _ _ _ y Hok Hok') _ Hs') as (S & Hs & Hr).
      destruct (proj2 (Hrec _ _ Hs Hs' Hr) _ Hc1) as (X & HX & Hk).
      exists X; split; [ eapply desc_chain_step; [ reflexivity | exact Hs | exact HX ] | exact Hk ].
Qed.

(** Chains from a typed description, and from it given an argument,
    typed: of the same kinds. *)
Lemma desc_chain_at : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall ys Γ N x R R', ⊢ Θ ⍮ Ξ ⍮ Γ -> mdesc_canonical Θ Ξ R ->
    mdesc_scoped (List.length Γ) R -> desc_ok Θ Ξ Γ R -> desc_ok Θ Ξ Γ R' -> mdesc_at R N = Some R' ->
    (forall X, desc_chain Θ Ξ Γ R ys x X -> exists X', desc_chain Θ Ξ Γ R' ys x X' /\ mdesc_kind X = mdesc_kind X') /\
    (forall X', desc_chain Θ Ξ Γ R' ys x X' -> exists X, desc_chain Θ Ξ Γ R ys x X /\ mdesc_kind X = mdesc_kind X').
Proof.
  intros * Hg * HΓ Hc Hsc Hok Hok' Ha; destruct (at_mod_rel _ _ _ Ha) as [Hf Hb].
  assert (Hpart : forall Rm Rm', mdesc_mod R = Some Rm -> mdesc_mod R' = Some Rm' -> mdesc_at Rm N = Some Rm' ->
            (forall X, desc_chain Θ Ξ Γ Rm ys x X -> exists X', desc_chain Θ Ξ Γ Rm' ys x X' /\ mdesc_kind X = mdesc_kind X') /\
            (forall X', desc_chain Θ Ξ Γ Rm' ys x X' -> exists X, desc_chain Θ Ξ Γ Rm ys x X /\ mdesc_kind X = mdesc_kind X'))
    by (intros * Hm Hm' Ham; exact (mod_chain_at _ _ Hg _ _ _ _ _ _ HΓ (mdesc_canonical_mod _ _ _ _ Hc Hm) (mdesc_mod_scoped _ _ _ Hsc Hm)
                                      (mdesc_mod_is_mod _ _ Hm) (desc_ok_mod _ _ Hg _ _ _ Hok Hm) (desc_ok_mod _ _ Hg _ _ _ Hok' Hm') Ham)).
  assert (Hself : forall Rm, mdesc_mod R = Some Rm -> mdesc_mod Rm = Some Rm) by (intros * Hm; exact (mdesc_is_mod_mod _ (mdesc_mod_is_mod _ _ Hm))).
  assert (Hself' : forall Rm', mdesc_mod R' = Some Rm' -> mdesc_mod Rm' = Some Rm') by (intros * Hm; exact (mdesc_is_mod_mod _ (mdesc_mod_is_mod _ _ Hm))).
  split.
  - intros X HX; assert (HRm : exists Rm, mdesc_mod R = Some Rm) by (inversion HX; eauto).
    destruct HRm as (Rm & HRm); destruct (Hf _ HRm) as (Rm' & HRm' & Ham).
    destruct (proj1 (Hpart _ _ HRm HRm' Ham) X (desc_chain_mod_eq _ _ _ _ _ _ _ _ ltac:(rewrite HRm, (Hself _ HRm); reflexivity) HX))
      as (X' & HX' & Hk).
    exists X'; split; [ eapply desc_chain_mod_eq; [| exact HX' ]; rewrite HRm', (Hself' _ HRm'); reflexivity | exact Hk ].
  - intros X' HX'; assert (HRm' : exists Rm', mdesc_mod R' = Some Rm') by (inversion HX'; eauto).
    destruct HRm' as (Rm' & HRm'); destruct (Hb _ HRm') as (Rm & HRm & Ham).
    destruct (proj2 (Hpart _ _ HRm HRm' Ham) X' (desc_chain_mod_eq _ _ _ _ _ _ _ _ ltac:(rewrite HRm', (Hself' _ HRm'); reflexivity) HX'))
      as (X & HX & Hk).
    exists X; split; [ eapply desc_chain_mod_eq; [| exact HX ]; rewrite HRm, (Hself _ HRm); reflexivity | exact Hk ].
Qed.

(** What reads an open frame, applied, still does. *)
Lemma reads_frame_at : forall Ξ R N R', mdesc_at R N = Some R' -> desc_reads_frame Ξ R -> desc_reads_frame Ξ R'.
Proof.
  intros * Ha (Θ' & p & T & Φ & Ns & Hm & Hf).
  destruct (proj1 (at_mod_rel _ _ _ Ha) _ Hm) as (Xm' & Hm' & Ha'); cbn in Ha'.
  destruct (tele_split (rev Θ')) as [[[? ?] ?] | ?]; injection Ha' as <-; unfold desc_reads_frame; do 5 eexists; (split; [ exact Hm' | exact Hf ]).
Qed.

(** The head of a well-formed chain of selections is well formed. *)
Lemma mems_typed_head : forall Θ Ξ Γ zs P, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_mems P zs ≈ me_mems P zs -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ P ≈ P.
Proof.
  intros Θ Ξ Γ zs; induction zs as [| z zs IH]; intros P HP; cbn [me_mems] in HP; [ exact HP |].
  exact (proj1 (modexp_gen _ _ _ _ _ (IH _ HP))).
Qed.

(** Chains through an entry of a well-formed module expression are read
    from what it denotes. *)
Lemma chain_proof_entry : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ P R w D rest x, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ P ≈ P -> mdenote Θ Ξ Γ P R ->
    (exists Rm, mdesc_mod R = Some Rm /\ desc_sel Θ Ξ Γ Rm w D) ->
    (chain_proof Θ Ξ Γ P (w :: rest) x <-> exists X, desc_chain Θ Ξ Γ R (w :: rest) x X /\ mdesc_kind X = ak_propositional).
Proof.
  intros * Hg * HP HR (Rm & HRm & Hs).
  pose proof Hs as (Γy & E & rd & R1 & He & Hed & Hr).
  assert (HD : mdenote Θ Ξ Γ (me_mem P w) D) by (eapply mdenote_mem; eassumption).
  pose proof (entry_read_frame_free _ _ Hg _ _ _ _ _ _ _ _ _ _ _ HP HR HRm He Hed Hr) as Hff.
  assert (Hobs : obs_root Ξ (me_mem P w)).
  { destruct (mod_qname (me_mem P w)) as [qn |] eqn:Hq; [ right; exists qn; split; [ exact Hq | exact (frame_free_of_desc _ _ Hg _ _ _ _ Hq HD Hff) ] | left; exact Hq ]. }
  assert (Hc : forall X, desc_chain Θ Ξ Γ D rest x X <-> desc_chain Θ Ξ Γ R (w :: rest) x X).
  { intros X; split; intros HX; [ eapply desc_chain_step; eassumption |].
    inversion HX as [| ? Rm0 ? ? ? S ? Hm0 Hs0 Hc0]; subst.
    rewrite HRm in Hm0; injection Hm0 as <-; rewrite (desc_sel_functional _ _ Hg _ _ _ _ _ Hs Hs0); exact Hc0. }
  unfold chain_proof; cbn [me_mems]; split.
  - intros (X & HX & Hk); exists X; split; [ apply Hc; exact (proj1 (chain_desc_iff _ _ Hg _ _ _ _ _ _ Hobs HD) HX) | exact Hk ].
  - intros (X & HX & Hk); exists X; split; [ apply (proj2 (chain_desc_iff _ _ Hg _ _ _ _ _ _ Hobs HD)); apply Hc; exact HX | exact Hk ].
Qed.

(** Chains from a well-formed module expression of a description, read
    from that description, when it names no open frame. *)
Lemma chain_proof_obs : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ P R ys x, obs_root Ξ P -> mdenote Θ Ξ Γ P R ->
    (chain_proof Θ Ξ Γ P ys x <-> exists X, desc_chain Θ Ξ Γ R ys x X /\ mdesc_kind X = ak_propositional).
Proof.
  intros * Hg * Hobs HR; unfold chain_proof; split; intros (X & HX & Hk); exists X; (split; [| exact Hk ]);
    [ exact (proj1 (chain_desc_iff _ _ Hg _ _ _ _ _ _ Hobs HR) HX) | exact (proj2 (chain_desc_iff _ _ Hg _ _ _ _ _ _ Hobs HR) HX) ].
Qed.

(** [spine_ok Θ Ξ Γ E zs]: the selections [zs] from [E] start well: with
    none, [E] is no open frame; with some, [E] has the first. *)
Definition spine_ok (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (E : modexp) (zs : list string) : Prop :=
  (zs = nil -> frame_free_target Θ Ξ Γ E) /\ (forall z zs', zs = z :: zs' -> exists S, mdenote Θ Ξ Γ (me_mem E z) S).

(** An entry selected from a well-formed application is an entry of its
    head's description. *)
Lemma app_head_entry : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ H N R z S', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H N ->
    mdenote Θ Ξ Γ H R -> mdenote Θ Ξ Γ (me_mem (me_app H N) z) S' -> exists Rm D, mdesc_mod R = Some Rm /\ desc_sel Θ Ξ Γ Rm z D.
Proof.
  intros * Hg * HA HR HS'.
  pose proof (presup_modexp_eq_ctx HA) as HΓ.
  destruct (modexp_gen _ _ _ _ _ HA) as [[HH _] _].
  destruct (me_denotes _ _ _ _ _ HA) as (R' & _ & HR' & _).
  destruct (mdenote_app_inv _ _ _ _ _ _ HR') as (R0 & HR0 & Ha).
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR0 _ HR) in Ha; clear R0 HR0.
  assert (Hobs' : obs_root Ξ (me_app H N)) by (left; reflexivity).
  pose proof (proj1 (chain_desc_iff _ _ Hg _ nil _ _ _ _ Hobs' HR') HS') as HcS'.
  destruct (proj2 (desc_chain_at _ _ Hg nil Γ N z R R' HΓ (mdenote_canon _ _ _ _ _ Hg HR) (wf_mdenote_scoped _ _ _ _ _ _ HH HR)
                     (me_desc_ok _ _ _ _ _ _ HH HR) (me_desc_ok _ _ _ _ _ _ HA HR') Ha) _ HcS') as (Sz & HcS & _).
  inversion HcS as [? Rm ? ? HRm Hs |]; subst; eauto.
Qed.

(** The selections from an application start well from its head. *)
Lemma spine_ok_app : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ H N zs, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H N ->
    spine_ok Θ Ξ Γ (me_app H N) zs -> spine_ok Θ Ξ Γ H zs.
Proof.
  intros * Hg * HA [Hn Hc].
  destruct (modexp_gen _ _ _ _ _ HA) as [[HH (R & _ & _ & _ & _ & HR & _)] _].
  split.
  - intros ->; destruct (Hn eq_refl) as (R' & HR' & HnE).
    destruct (mdenote_app_inv _ _ _ _ _ _ HR') as (R0 & HR0 & Ha).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR0 _ HR) in Ha.
    exists R; split; [ exact HR | intros Hr; exact (HnE (reads_frame_at _ _ _ _ Ha Hr)) ].
  - intros z zs' ->; destruct (Hc _ _ eq_refl) as (S' & HS').
    destruct (app_head_entry _ _ Hg _ _ _ _ _ _ HA HR HS') as (Rm & D & HRm & (Γy & E & rd & R1 & He & Hed & Hr)).
    exists D; eapply mdenote_mem; eassumption.
Qed.

(** Chains through a well-started selection spine from an application are
    those from its head: an application supplies an argument, which no
    member's kind depends on. *)
Lemma chain_proof_app : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ H N zs ys x,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H N -> spine_ok Θ Ξ Γ (me_app H N) zs ->
    (chain_proof Θ Ξ Γ (me_app H N) (zs ++ ys) x <-> chain_proof Θ Ξ Γ H (zs ++ ys) x).
Proof.
  intros * Hg * HA [Hff Hfst].
  pose proof (presup_modexp_eq_ctx HA) as HΓ.
  destruct (modexp_gen _ _ _ _ _ HA) as [[HH (R & _ & _ & _ & _ & HR & _)] _].
  destruct (me_denotes _ _ _ _ _ HA) as (R' & _ & HR' & _).
  destruct (mdenote_app_inv _ _ _ _ _ _ HR') as (R0 & HR0 & Ha).
  rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR0 _ HR) in Ha; clear R0 HR0.
  pose proof (desc_chain_at _ _ Hg (zs ++ ys) Γ N x R R' HΓ (mdenote_canon _ _ _ _ _ Hg HR) (wf_mdenote_scoped _ _ _ _ _ _ HH HR)
                (me_desc_ok _ _ _ _ _ _ HH HR) (me_desc_ok _ _ _ _ _ _ HA HR') Ha) as [Af Ab].
  assert (Hobs' : obs_root Ξ (me_app H N)) by (left; reflexivity).
  rewrite (chain_proof_obs _ _ Hg _ _ _ _ _ Hobs' HR').
  assert (HHside : chain_proof Θ Ξ Γ H (zs ++ ys) x <-> exists X, desc_chain Θ Ξ Γ R (zs ++ ys) x X /\ mdesc_kind X = ak_propositional).
  { destruct zs as [| z zs].
    - (* the application is the target: its head names no open frame *)
      apply (chain_proof_obs _ _ Hg); [| exact HR ].
      destruct (Hff eq_refl) as (RE & HRE & HnE).
      rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HRE _ HR') in HnE.
      destruct (mod_qname H) as [qn |] eqn:Hq; [| left; exact Hq ].
      right; exists qn; split; [ exact Hq |].
      exact (frame_free_of_desc _ _ Hg _ _ _ _ Hq HR (fun Hr => HnE (reads_frame_at _ _ _ _ Ha Hr))).
    - (* a selection from the application: the entry is in the head *)
      destruct (Hfst _ _ eq_refl) as (Sz' & HSz').
      destruct (app_head_entry _ _ Hg _ _ _ _ _ _ HA HR HSz') as (Rm & D & HRm & Hs).
      exact (chain_proof_entry _ _ Hg _ _ _ _ _ _ _ HH HR (ex_intro _ Rm (conj HRm Hs))). }
  rewrite HHside; split.
  - intros (X' & HX' & Hk); destruct (Ab _ HX') as (X & HX & Hk'); exists X; split; [ exact HX | congruence ].
  - intros (X & HX & Hk); destruct (Af _ HX) as (X' & HX' & Hk'); exists X'; split; [ exact HX' | congruence ].
Qed.

(** Selections from a path are a path. *)
Lemma mems_qname : forall ys P p, mod_qname P = Some p -> exists p', mod_qname (me_mems P ys) = Some p'.
Proof.
  induction ys as [| y ys IH]; intros * Hp; cbn [me_mems]; [ eauto |].
  apply (IH _ {| q_unit := q_unit p; q_chain := q_chain p ++ y :: nil |}); cbn; rewrite Hp; reflexivity.
Qed.

(** The chains of a path select proofs in one context as in another. *)
Lemma chain_proof_path_ctx : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Δ Γ P p ys x, mod_qname P = Some p ->
    chain_proof Θ Ξ Δ P ys x -> chain_proof Θ Ξ Γ P ys x.
Proof.
  intros * Hg * Hp (X & HX & Hk).
  destruct (mems_qname ys _ _ Hp) as (p' & Hp').
  assert (Hq : exists p'', mod_qname (me_mem (me_mems P ys) x) = Some p'') by (cbn; rewrite Hp'; eauto).
  destruct Hq as (p'' & Hq).
  pose proof (proj1 (mdenote_sub_lt_all _ _ (wf_gstack_closed _ _ Hg)) _ _ _ HX 0 ltac:(intros ? ? Hx; lia)
                (mod_qname_scoped _ _ 0 Hq) Γ Id ltac:(intros ? ? Hx; lia)) as HX'.
  rewrite (mod_qname_sub _ _ _ Hq) in HX'.
  exists (mdesc_sub X Id); split; [ exact HX' | rewrite mdesc_kind_sub; exact Hk ].
Qed.

(** Two expressions naming no open frame that denote alike have the same
    chains. *)
Lemma chain_proof_same_denote : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ P P' ys x, obs_root Ξ P -> obs_root Ξ P' ->
    (forall R, mdenote Θ Ξ Γ P R <-> mdenote Θ Ξ Γ P' R) -> (chain_proof Θ Ξ Γ P ys x <-> chain_proof Θ Ξ Γ P' ys x).
Proof.
  intros * Hg * Ho Ho' Hd; unfold chain_proof; split; intros (X & HX & Hk); exists X; (split; [| exact Hk ]).
  - destruct (mems_back _ _ Hg _ _ _ _ _ HX) as [R HR].
    exact (proj2 (chain_desc_iff _ _ Hg _ _ _ _ _ _ Ho' (proj1 (Hd R) HR)) (proj1 (chain_desc_iff _ _ Hg _ _ _ _ _ _ Ho HR) HX)).
  - destruct (mems_back _ _ Hg _ _ _ _ _ HX) as [R HR].
    exact (proj2 (chain_desc_iff _ _ Hg _ _ _ _ _ _ Ho (proj2 (Hd R) HR)) (proj1 (chain_desc_iff _ _ Hg _ _ _ _ _ _ Ho' HR) HX)).
Qed.

(** A slot has the chains of its unit. *)
Lemma chain_proof_slot_lit : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ k U ys x, Γ ∋ #k ≔ₘ U ->
    (chain_proof Θ Ξ Γ (me_var k) ys x <-> chain_proof Θ Ξ Γ (me_lit U) ys x).
Proof.
  intros * Hg * Hk; apply (chain_proof_same_denote _ _ Hg); [ left; reflexivity | left; reflexivity |].
  intros R; split; intros HR; inversion HR; subst; try (cbn in *; discriminate).
  - match goal with Hk' : ctx_lookup_mod k ?U' Γ, HU' : udenote _ _ _ _ ?U' _ |- _ =>
      pose proof (ctx_find_mod_complete _ _ _ Hk) as E1; pose proof (ctx_find_mod_complete _ _ _ Hk') as E2;
      rewrite E1 in E2; injection E2 as <-; apply mdenote_lit; exact HU' end.
  - eapply mdenote_slot; eassumption.
Qed.

(** What a well-formed unit denotes reads no open frame. *)
Lemma udenote_frame_free : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ U R, unit_full Θ Ξ Γ U -> udenote Θ Ξ Γ None U R -> ~ desc_reads_frame Ξ R.
Proof.
  intros * Hg * HU HR (Θ' & p & T & Φ & Ns & Hm & Hf).
  inversion HR as [? ? Δ sm Φb Φx R0 _ Hb | ? ? Δ E R0 R'' HE HR0]; subst.
  - destruct sm; cbn in Hb, HU; [ injection Hb as <-; cbn in Hm; discriminate | contradiction ].
  - destruct (unit_alias_frame_free _ _ _ _ _ HU) as (R1 & HR1 & Hn).
    rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HE _ HR1) in HR0.
    apply Hn; rewrite mdesc_mod_up in Hm; rewrite (mdesc_is_mod_mod _ (mdesc_mod_is_mod _ _ HR0)) in Hm; cbn in Hm.
    injection Hm as Hm.
    destruct R'' as [| | Θ0 p0 T0 Φ0 Ns0 |]; cbn in Hm; try discriminate; injection Hm as _ <- <- <- <-.
    unfold desc_reads_frame; do 5 eexists; (split; [ exact HR0 | exact Hf ]).
Qed.

(** A slot of a well-formed context reads no open frame. *)
Lemma slot_frame_free : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ k U, ⊢ Θ ⍮ Ξ ⍮ Γ -> Γ ∋ #k ≔ₘ U ->
    forall R, mdenote Θ Ξ Γ (me_var k) R -> ~ desc_reads_frame Ξ R.
Proof.
  intros * Hg * HΓ Hk R HR; inversion HR; subst; try (cbn in *; discriminate).
  match goal with Hk' : ctx_lookup_mod k ?U' Γ, HU' : udenote _ _ _ _ ?U' _ |- _ =>
    exact (udenote_frame_free _ _ Hg _ _ _ (proj1 (unit_full_of_eq _ _ _ _ _ (ctx_lookup_mod_wf _ _ _ _ _ HΓ Hk'))) HU') end.
Qed.

(** A slot under one more entry has the chains it had. *)
Lemma chain_proof_wk_var : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ e k U ys x, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> Γ ∋ #k ≔ₘ U ->
    (chain_proof Θ Ξ (e :: Γ) (me_var (S k)) ys x <-> chain_proof Θ Ξ Γ (me_var k) ys x).
Proof.
  intros * Hg * HeΓ Hk.
  pose proof (ctx_decomp_tail HeΓ) as HΓ.
  exact (chain_proof_sub _ _ Hg _ (me_var k) _ Wk ys x (wf_me_var _ _ _ _ _ HΓ Hk) (slot_frame_free _ _ Hg _ _ _ HΓ Hk)
           (wf_sub_shift _ _ _ _ HeΓ)).
Qed.

(** A literal unit, weakened under one more entry, has the chains it had. *)
Lemma chain_proof_wk_lit : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ e U ys x, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> unit_full Θ Ξ Γ U ->
    (chain_proof Θ Ξ (e :: Γ) (me_lit (gunit_wk U wk_shift)) ys x <-> chain_proof Θ Ξ Γ (me_lit U) ys x).
Proof.
  intros * Hg * HeΓ HU.
  assert (HL : Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_lit U ≈ me_lit U) by (apply wf_me_lit; exact (unit_eq_of_full _ _ _ _ HU)).
  assert (Hff : forall R, mdenote Θ Ξ Γ (me_lit U) R -> ~ desc_reads_frame Ξ R)
    by (intros R HR; inversion HR; subst; try (cbn in *; discriminate); eapply udenote_frame_free; eassumption).
  pose proof (chain_proof_sub _ _ Hg _ (me_lit U) _ Wk ys x HL Hff (wf_sub_shift _ _ _ _ HeΓ)) as Hs.
  cbn [modexp_sub] in Hs; rewrite (gunit_sub_of_wk_ext U wk_shift Wk) in Hs by (intros ?; reflexivity); exact Hs.
Qed.

(** The context of a grafted body: the fragment's entries over the
    body's. *)
Lemma body_ctx_graft : forall B A, body_ctx (gm_graft A B) = body_ctx B ++ body_ctx A.
Proof.
  induction B as [| B IH x E | B IH H its Bg _]; intros A; cbn [gm_graft]; [ reflexivity | | exact (IH A) ].
  destruct E as [? ? ? ? [] | | | |]; cbn [body_ctx]; rewrite IH; reflexivity.
Qed.

(** A grafted body has a body's shape where it and the fragment do. *)
Lemma body_shape_graft_base : forall B A, body_shape (gm_graft A B) (gm_graft A B) -> body_shape A A.
Proof.
  induction B as [| B IH x E | B IH H its Bg _]; intros A Hs; cbn [gm_graft body_shape] in Hs; [ exact Hs | |];
    destruct Hs as (Hs & _); exact (IH _ Hs).
Qed.

(** Chains through a module entry of a local body: those of the entry's
    unit, in the context of the entries before it. *)
Lemma open_entry_chain : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall Γ Δ Φ Φx Φ0 w E U σ ys x,
    ⊢ Θ ⍮ Ξ ⍮ body_ctx (gm_ext Φ0 w E) ++ Δ ++ Γ -> gm_prefix_upto Φx w = Some (gm_ext Φ0 w E) ->
    entry_unit E = Some U -> entry_readable E -> gm_fill Φ0 = Some σ ->
    (chain_proof Θ Ξ (body_ctx Φ0 ++ Δ ++ Γ) (me_lit U) ys x <->
     exists X, desc_chain Θ Ξ Γ (mdesc_open Δ Φ Φx) (w :: ys) x X /\ mdesc_kind X = ak_propositional).
Proof.
  intros * Hg * HC Hp HU Hrd Hσ.
  set (Ψ0 := body_ctx Φ0 ++ Δ ++ Γ).
  (* the entry's unit and what the entry denotes *)
  assert (HR1 : unit_full Θ Ξ Ψ0 U /\ forall RU, udenote Θ Ξ Ψ0 None U RU ->
            exists R1, edenote Θ Ξ Ψ0 None E R1 /\ mdesc_mod R1 = Some RU).
  { destruct E as [? ? ? ? ? | pv U0 | | pv A M U0 |]; cbn in HU; try discriminate; injection HU as <-; cbn [body_ctx List.app] in HC.
    - split; [ exact (proj1 (unit_full_of_eq _ _ _ _ _ (proj2 (ctx_decomp_mod HC)))) |].
      intros RU HRU; exists RU; split; [ apply edenote_mod; exact HRU | exact (mdesc_is_mod_mod _ (udenote_is_mod _ _ _ _ _ _ HRU)) ].
    - split; [ exact (proj1 (unit_full_of_eq _ _ _ _ _ (proj2 (proj2 (proj2 (ctx_decomp_dm HC)))))) |].
      destruct (ctx_decomp_dm_alias HC) as [E0 ->].
      intros RU HRU; exists (mdesc_dm nil A M RU); split; [ apply edenote_def_mod; exact HRU | cbn [mdesc_mod]; rewrite ?mdesc_up_nil; exact (mdesc_is_mod_mod _ (udenote_is_mod _ _ _ _ _ _ HRU)) ]. }
  destruct HR1 as [HUf HR1].
  assert (HΨ0 : ⊢ Θ ⍮ Ξ ⍮ Ψ0) by (destruct E; cbn [body_ctx List.app] in HC; try (destruct o); exact (ctx_decomp_tail HC)).
  assert (HL : Θ ⍮ Ξ ⍮ Ψ0 ⊢ᵐ me_lit U ≈ me_lit U) by (apply wf_me_lit; exact (unit_eq_of_full _ _ _ _ HUf)).
  destruct (me_denotes _ _ _ _ _ HL) as (RL & _ & HRL & _).
  assert (HRU : udenote Θ Ξ Ψ0 None U RL) by (inversion HRL; subst; try (cbn in *; discriminate); assumption).
  destruct (HR1 _ HRU) as (R1 & Hed & HmR1).
  pose proof (mdesc_is_mod_mod _ (udenote_is_mod _ _ _ _ _ _ HRU)) as Hself.
  set (S := mdesc_up Δ (mdesc_sub R1 σ)).
  assert (Hsel : desc_sel Θ Ξ Γ (mdesc_open Δ Φ Φx) w S).
  { exists (body_ctx Φ0 ++ Δ), E, (reader_open Δ Φ0), R1; split; [ apply (proj2 (open_entry_iff _ _ _ _ _ _ _)); exists Φ0; repeat split; assumption |].
    split; [ cbn [mdesc_entry_path]; rewrite <- List.app_assoc; exact Hed | cbn; rewrite Hσ; reflexivity ]. }
  (* moved by the filling into the body's context *)
  pose proof (wf_gm_fill _ _ _ _ _ HΨ0 Hσ) as Hσt.
  assert (Hff : forall R, mdenote Θ Ξ Ψ0 (me_lit U) R -> ~ desc_reads_frame Ξ R)
    by (intros R HR; inversion HR; subst; try (cbn in *; discriminate); eapply udenote_frame_free; eassumption).
  rewrite <- (chain_proof_sub _ _ Hg _ _ _ _ ys x HL Hff Hσt).
  pose proof (wf_sub_mdenote _ _ _ _ _ _ _ _ HL HRL Hσt) as HRσ.
  assert (Hobsσ : obs_root Ξ (me_lit U)[σ]ᵐ) by (left; reflexivity).
  rewrite (chain_proof_obs _ _ Hg _ _ _ _ _ Hobsσ HRσ).
  assert (HmS : mdesc_mod S = option_map (mdesc_up Δ) (mdesc_mod (mdesc_sub RL σ))).
  { unfold S; rewrite mdesc_mod_up, (mdesc_mod_sub _ _ σ HmR1), (mdesc_is_mod_mod _ (mdesc_is_mod_sub _ σ (udenote_is_mod _ _ _ _ _ _ HRU)));
      reflexivity. }
  destruct (desc_chain_up _ _ Hg Γ Δ ys x S (mdesc_sub RL σ)
              (mdesc_canonical_sub _ _ _ σ (mdenote_canon _ _ _ _ _ Hg HRL)) HmS) as [U1 U2].
  split.
  - intros (X0 & HX0 & Hk); destruct (U2 _ HX0) as (X & HX & Hk').
    exists X; split; [ eapply desc_chain_step; [ reflexivity | exact Hsel | exact HX ] | congruence ].
  - intros (X & HX & Hk); inversion HX as [| ? Rm ? ? ? S' ? Hm Hs Hc]; subst; cbn in Hm; injection Hm as <-.
    rewrite (desc_sel_functional _ _ Hg _ _ _ _ _ Hs Hsel) in Hc.
    destruct (U1 _ Hc) as (X0 & HX0 & Hk'); exists X0; split; [ exact HX0 | congruence ].
Qed.

Section Coherence.
  Context {GC : GCtx}.
  Variable γ : global_valuation.

  (** The global modules' tables are what their chains denote. *)
  Hypothesis Hglob : forall fp ys x,
      module_member_proofs γ (set_module_global (q_abs fp nil) nil) ys x = true <->
      chain_proof gc_deps gc_stack nil (me_unit fp) ys x.

  (** The table at a position holding no slot is empty. *)
  Hypothesis Hno : forall ys x, no_slot_proofs γ ys x = false.

  (** [slots_proof_coherent Γ κs]: the table [κs] gives each module slot of
      [Γ] is what the slot's chains denote. *)
  Definition slots_proof_coherent (Γ : ctx) (κs : nat -> member_proofness) : Prop :=
    forall k U, ctx_find_mod Γ k = Some U -> forall ys x, κs k ys x = true <-> chain_proof gc_deps gc_stack Γ (me_var k) ys x.

  (** The slots of a grafted body: the fragment's over the body's. *)
  Lemma body_slot_proofs_graft : forall B A κs, body_slot_proofs γ κs (gm_graft A B) = body_slot_proofs γ (body_slot_proofs γ κs A) B.
  Proof. induction B as [| B IH x E | B IH H its Bg _]; intros A κs; cbn [gm_graft body_slot_proofs]; rewrite ?IH; reflexivity. Qed.

  (** A member of a grafted body: the fragment's, else the body's. *)
  Lemma body_member_lookup_graft : forall B A κs ys x,
      body_member_lookup γ κs (gm_graft A B) ys x =
      match body_member_lookup γ (body_slot_proofs γ κs A) B ys x with Some b => Some b | None => body_member_lookup γ κs A ys x end.
  Proof.
    induction B as [| B IH z E | B IH H its Bg _]; intros A κs ys x; cbn [gm_graft body_member_lookup]; [ reflexivity | |].
    - rewrite body_slot_proofs_graft; destruct (String.eqb (chain_key ys x) z); [ reflexivity | apply IH ].
    - rewrite body_slot_proofs_graft, IH.
      destruct (body_member_lookup γ (body_slot_proofs γ (body_slot_proofs γ κs A) B) Bg ys x); [ reflexivity |].
      reflexivity.
  Qed.

  (** A body's tables are its expansion's: an open's are those of the
      entries it stores. *)
  Lemma body_tables_expand : forall Φ κs, body_slot_proofs γ κs (gm_expand Φ) = body_slot_proofs γ κs Φ /\
      forall ys x, body_member_lookup γ κs (gm_expand Φ) ys x = body_member_lookup γ κs Φ ys x.
  Proof.
    induction Φ as [| Φ IH z E | Φ IH H its Φg IHg]; intros κs; cbn [gm_expand body_slot_proofs body_member_lookup].
    - split; reflexivity.
    - destruct (IH κs) as [Hs Hl]; rewrite Hs; split; [ reflexivity | intros ys x; rewrite Hl; reflexivity ].
    - destruct (IH κs) as [Hs Hl]; rewrite body_slot_proofs_graft, Hs.
      destruct (IHg (body_slot_proofs γ κs Φ)) as [Hsg Hlg]; split; [ exact Hsg |].
      intros ys x; rewrite body_member_lookup_graft, Hs, Hlg, Hl; reflexivity.
  Qed.

  (** A member of a body with no open: at the last entry so named. *)
  Lemma body_member_lookup_noopen : forall Φ κs ys x, gm_noopen Φ ->
      body_member_lookup γ κs Φ ys x =
      match gm_prefix_upto Φ (chain_key ys x) with
      | Some (gm_ext Φ' _ E) =>
          Some (match ys with nil => gentry_is_proof E | _ :: ys' => gentry_slot_proofs γ (body_slot_proofs γ κs Φ') E ys' x end)
      | _ => None
      end.
  Proof.
    induction Φ as [| Φ IH z E | Φ IH H its Φg _]; intros κs ys x Hn; cbn [body_member_lookup gm_prefix_upto gm_noopen] in Hn |- *;
      [ reflexivity | | contradiction ].
    destruct (String.eqb (chain_key ys x) z); [ reflexivity | exact (IH _ _ _ Hn) ].
  Qed.

  (** One more entry: a module slot of the table of what its unit's chains
      denote, after slots coherent with the context, is coherent. *)
  Lemma slots_coherent_push : ⊢ᵍ gc_deps ⍮ gc_stack -> forall Γ e κs P, ⊢ gc_deps ⍮ gc_stack ⍮ e :: Γ ->
      slots_proof_coherent Γ κs ->
      (forall U0, match e with ce_mod U | ce_dm _ _ U => Some U | _ => None end = Some U0 ->
         forall ys x, P ys x = true <-> chain_proof gc_deps gc_stack Γ (me_lit U0) ys x) ->
      slots_proof_coherent (e :: Γ) (push_slot_proofs κs P).
  Proof.
    intros Hg * HeΓ Hκ HP [| k] U Hk ys x; cbn [push_slot_proofs].
    - assert (HU0 : exists U0, match e with ce_mod U | ce_dm _ _ U => Some U | _ => None end = Some U0 /\
                      U = gunit_wk U0 wk_shift /\ unit_full gc_deps gc_stack Γ U0).
      { cbn in Hk; destruct e as [| | U0 | A M U0]; try discriminate; injection Hk as <-; exists U0;
          (split; [ reflexivity | split; [ reflexivity |] ]).
        - exact (proj1 (unit_full_of_eq _ _ _ _ _ (proj2 (ctx_decomp_mod HeΓ)))).
        - exact (proj1 (unit_full_of_eq _ _ _ _ _ (proj2 (proj2 (proj2 (ctx_decomp_dm HeΓ)))))). }
      destruct HU0 as (U0 & HeU & -> & HU0).
      rewrite (HP _ HeU), (chain_proof_slot_lit _ _ Hg _ _ _ _ _ (ctx_find_mod_sound _ _ _ Hk)).
      symmetry; exact (chain_proof_wk_lit _ _ Hg _ _ _ _ _ HeΓ HU0).
    - cbn in Hk; destruct (ctx_find_mod Γ k) as [U' |] eqn:Ek; cbn in Hk; [| discriminate ].
      rewrite (Hκ _ _ Ek); symmetry; exact (chain_proof_wk_var _ _ Hg _ _ _ _ _ _ HeΓ (ctx_find_mod_sound _ _ _ Ek)).
  Qed.

  (** Under a telescope of assumptions, the tables past it are coherent. *)
  Lemma slots_coherent_tele : ⊢ᵍ gc_deps ⍮ gc_stack -> forall Δ Γ κs, all_assumptions Δ -> ⊢ gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ->
      slots_proof_coherent Γ κs -> slots_proof_coherent (Δ ++ Γ) (tele_out_proofs γ κs (List.rev Δ)).
  Proof.
    intros Hg Δ; induction Δ as [| e Δ IH]; intros Γ κs Ha HΔ Hκ; [ exact Hκ |].
    inversion Ha as [| ? ? (κ & A & ->) Ha']; subst.
    cbn [List.rev]; rewrite tele_out_proofs_app; cbn [tele_out_proofs List.app].
    apply (slots_coherent_push Hg); [ exact HΔ | exact (IH _ _ Ha' (ctx_decomp_tail HΔ) Hκ) | intros U0 HU0; discriminate ].
  Qed.

  (** [table_coherent Γ κs E zs]: past the selections [zs], the table [E]'s
      syntax gives, at the tables [κs], is what [E]'s chains denote. *)
  Definition table_coherent (Γ : ctx) (κs : nat -> member_proofness) (E : modexp) (zs : list string) : Prop :=
    forall ys x, modexp_member_proofs γ κs E (zs ++ ys) x = true <-> chain_proof gc_deps gc_stack Γ E (zs ++ ys) x.

  (** A loaded unit or an open frame: its global table. *)
  Lemma table_coherent_unit : ⊢ᵍ gc_deps ⍮ gc_stack -> forall Γ κs fp zs, table_coherent Γ κs (me_unit fp) zs.
  Proof.
    intros Hg * ys x; cbn [modexp_member_proofs]; rewrite Hglob; split;
      apply (chain_proof_path_ctx _ _ Hg _ _ _ (q_abs fp nil)); reflexivity.
  Qed.

  (** A module slot: its given table. *)
  Lemma table_coherent_var : forall Γ κs k U zs, slots_proof_coherent Γ κs -> ctx_find_mod Γ k = Some U ->
      table_coherent Γ κs (me_var k) zs.
  Proof. intros * Hκ Hk ys x; cbn [modexp_member_proofs]; exact (Hκ _ _ Hk _ _). Qed.

  (** A selection: its module's, past it. *)
  Lemma table_coherent_mem : forall Γ κs H y zs, table_coherent Γ κs H (y :: zs) -> table_coherent Γ κs (me_mem H y) zs.
  Proof. intros * HH ys x; cbn [modexp_member_proofs]; exact (HH ys x). Qed.

  (** An application: its head's. *)
  Lemma table_coherent_app : ⊢ᵍ gc_deps ⍮ gc_stack -> forall Γ κs H N zs,
      gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H N -> spine_ok gc_deps gc_stack Γ (me_app H N) zs ->
      table_coherent Γ κs H zs -> table_coherent Γ κs (me_app H N) zs.
  Proof.
    intros Hg * HA Hs HH ys x; cbn [modexp_member_proofs].
    rewrite (chain_proof_app _ _ Hg _ _ _ _ _ _ HA Hs); exact (HH ys x).
  Qed.

  (** A literal alias: its target's table under its parameters. *)
  Lemma unit_coherent_alias : ⊢ᵍ gc_deps ⍮ gc_stack -> forall Γ κs Δ E,
      unit_alias_full gc_deps gc_stack Γ Δ E -> slots_proof_coherent Γ κs ->
      (forall κs', slots_proof_coherent (Δ ++ Γ) κs' -> table_coherent (Δ ++ Γ) κs' E nil) ->
      forall ys x, unit_member_proofs γ κs (gu_mk Δ (md_alias E)) ys x = true <->
                   chain_proof gc_deps gc_stack Γ (me_lit (gu_mk Δ (md_alias E))) ys x.
  Proof.
    intros Hg * HU Hκ IH ys x.
    pose proof (unit_alias_target _ _ _ _ _ HU) as HE; pose proof (unit_alias_ctx _ _ _ _ _ HU) as HΔ.
    rewrite unit_member_proofs_tele_out; cbn [moddef_member_proofs].
    rewrite (IH _ (slots_coherent_tele Hg _ _ _ (unit_alias_ass _ _ _ _ _ HU) HΔ Hκ) ys x).
    destruct (unit_alias_frame_free _ _ _ _ _ HU) as (R1 & HR1 & Hn).
    assert (Hobs : obs_root gc_stack E).
    { apply (obs_root_of_frame_free _ _ Hg _ _ _ HE); intros R HR.
      rewrite (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR _ HR1); exact Hn. }
    destruct (me_denotes _ _ _ _ _ HE) as (R0 & R'' & HR0 & HR'').
    assert (Hlit : mdenote gc_deps gc_stack Γ (me_lit (gu_mk Δ (md_alias E))) (mdesc_up Δ R''))
      by (apply mdenote_lit; eapply udenote_alias; eassumption).
    assert (Hobs' : obs_root gc_stack (me_lit (gu_mk Δ (md_alias E)))) by (left; reflexivity).
    rewrite (chain_proof_obs _ _ Hg _ _ _ _ _ Hobs HR0), (chain_proof_obs _ _ Hg _ _ _ _ _ Hobs' Hlit).
    pose proof (mdesc_is_mod_mod _ (mdesc_mod_is_mod _ _ HR'')) as Hself.
    assert (Hm : mdesc_mod (mdesc_up Δ R'') = option_map (mdesc_up Δ) (mdesc_mod R'')) by (rewrite mdesc_mod_up; reflexivity).
    destruct (desc_chain_up _ _ Hg Γ Δ ys x _ _ (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg HR0) HR'') Hm) as [U1 U2].
    split.
    - intros (X & HX & Hk).
      destruct (U2 X (desc_chain_mod_eq _ _ _ _ _ _ _ _ ltac:(rewrite HR'', Hself; reflexivity) HX)) as (X1 & HX1 & Hk1).
      exists X1; split; [ exact HX1 | congruence ].
    - intros (X1 & HX1 & Hk1); destruct (U1 _ HX1) as (X & HX & Hk).
      exists X; split; [ eapply desc_chain_mod_eq; [| exact HX ]; rewrite HR'', Hself; reflexivity | congruence ].
  Qed.

  (** [body_coherent Ψ κs Φx]: the tables of the body [Φx] with no open,
      over the context [Ψ] and its tables [κs], are what chains denote: the
      slots of its entries, and each entry's module part at its prefix. *)
  Definition body_coherent (Ψ : ctx) (κs : nat -> member_proofness) (Φx : gmod) : Prop :=
    slots_proof_coherent (body_ctx Φx ++ Ψ) (body_slot_proofs γ κs Φx) /\
    forall y Φ0 E U0, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U0 ->
      forall ys x, gentry_slot_proofs γ (body_slot_proofs γ κs Φ0) E ys x = true <->
                   chain_proof gc_deps gc_stack (body_ctx Φ0 ++ Ψ) (me_lit U0) ys x.

  (** A literal body: the member its expansion has at the chain's first
      name, read as its entry's tag or module part's table. *)
  Lemma unit_coherent_body : ⊢ᵍ gc_deps ⍮ gc_stack -> forall Γ κs Δ Φ,
      unit_body_full gc_deps gc_stack Γ Δ Φ -> slots_proof_coherent Γ κs ->
      (forall Ψ κs', slots_proof_coherent Ψ κs' -> ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx (gm_expand Φ) ++ Ψ ->
         body_shape (gm_expand Φ) (gm_expand Φ) -> body_coherent Ψ κs' (gm_expand Φ)) ->
      forall ys x, unit_member_proofs γ κs (gu_mk Δ (md_body sm_open Φ)) ys x = true <->
                   chain_proof gc_deps gc_stack Γ (me_lit (gu_mk Δ (md_body sm_open Φ))) ys x.
  Proof.
    intros Hg * HU Hκ IH ys x.
    destruct HU as [Φx es l ps Hps Hx HC Hes Htg Hd Ho Hass Hs Hsh Hnd Hpar lv Rt HF Hff].
    pose proof (body_xp_expand _ _ _ _ _ Hx) as HxE.
    assert (HΔ : ⊢ gc_deps ⍮ gc_stack ⍮ Δ ++ Γ) by exact (ctx_app_wf_tail _ _ _ _ HC).
    pose proof (slots_coherent_tele Hg _ _ _ Hass HΔ Hκ) as HκΔ.
    set (κΔ := tele_out_proofs γ κs (List.rev Δ)) in HκΔ.
    pose proof (IH _ _ HκΔ ltac:(rewrite <- HxE; exact HC) ltac:(rewrite <- HxE; exact Hsh)) as [_ Hent].
    rewrite <- HxE in Hent.
    assert (Hno' : gm_noopen Φx) by (rewrite HxE; apply gm_noopen_expand).
    rewrite unit_member_proofs_tele_out; cbn [moddef_member_proofs]; fold κΔ.
    rewrite <- (proj2 (body_tables_expand Φ κΔ)), <- HxE, (body_member_lookup_noopen _ _ _ _ Hno').
    assert (Hlit : mdenote gc_deps gc_stack Γ (me_lit (gu_mk Δ (md_body sm_open Φ))) (mdesc_open Δ Φ Φx))
      by (apply mdenote_lit; eapply udenote_body; [ exact Hx | reflexivity ]).
    assert (Hobs : obs_root gc_stack (me_lit (gu_mk Δ (md_body sm_open Φ)))) by (left; reflexivity).
    pose proof (body_shape_fill _ _ (gm_noopen_nopens _ Hno') Hsh) as [Hfill _].
    rewrite (chain_proof_obs _ _ Hg _ _ _ _ _ Hobs Hlit).
    (* the entry at the chain's first name *)
    assert (Hfirst : forall X, desc_chain gc_deps gc_stack Γ (mdesc_open Δ Φ Φx) ys x X ->
              exists Φ0 E R1 S, gm_prefix_upto Φx (chain_key ys x) = Some (gm_ext Φ0 (chain_key ys x) E) /\ entry_readable E /\
                edenote gc_deps gc_stack (body_ctx Φ0 ++ Δ ++ Γ) None E R1 /\ mdesc_read (reader_open Δ Φ0) R1 = Some S /\
                match ys with nil => X = S | _ :: ys' => desc_chain gc_deps gc_stack Γ S ys' x X end).
    { intros X HX; inversion HX as [? Rm ? ? Hm (Γy & E & rd & R1 & He & Hed & Hr) | ? Rm ? ? ? S ? Hm (Γy & E & rd & R1 & He & Hed & Hr) Hc];
        subst; cbn in Hm; injection Hm as <-;
        destruct (proj1 (open_entry_iff _ _ _ _ _ _ _) He) as (Φ0 & Hp & Hrd & -> & ->);
        exists Φ0, E, R1; [ exists X | exists S ]; cbn [chain_key];
        (split; [ exact Hp | split; [ exact Hrd | split; [ rewrite <- List.app_assoc in Hed; exact Hed | split; [ exact Hr |] ] ] ]);
        first [ reflexivity | exact Hc ]. }
    destruct (gm_prefix_upto Φx (chain_key ys x)) as [Φ1 |] eqn:Hp.
    2: { (* none: no member, no chain *)
      split; [ destruct ys; discriminate |].
      intros (X & HX & _); destruct (Hfirst _ HX) as (? & ? & ? & ? & Hp' & _); discriminate. }
    destruct (gm_prefix_entry _ _ _ Hp) as (Φ0 & E & -> & _).
    destruct (shape_prefix _ _ _ _ _ Hsh Hp) as (Φ0' & E' & Hp' & _ & HsE); rewrite Hp in Hp'; injection Hp' as <- <-.
    destruct (fill_prefix _ _ _ _ Hfill Hp) as (σ & Hσ).
    pose proof (body_prefix_wf _ _ _ _ _ _ _ HC Hp) as HCE.
    destruct ys as [| w ys']; cbn [chain_key] in *.
    - (* the member itself: a proof exactly when its entry is a definition
         of a proposition *)
      destruct E as [b pv κ A [M |] | pv U | | pv A M U |]; cbn in HsE; try contradiction; cbn [gentry_is_proof].
      + destruct HsE as (-> & _ & _ & _); split.
        * intros Hk; exists (mdesc_up Δ (mdesc_sub (mdesc_term κ A (Some M)) σ)); split.
          -- eapply desc_chain_last; [ reflexivity |].
             exists (body_ctx Φ0 ++ Δ), (ge_def true pv κ A (Some M)), (reader_open Δ Φ0), (mdesc_term κ A (Some M)).
             split; [ apply (proj2 (open_entry_iff _ _ _ _ _ _ _)); exists Φ0; split; [ exact Hp | split; [ exact I | split; reflexivity ] ] |].
             split; [ exact (edenote_def _ _ _ _ _ _ _ _ _) | cbn; rewrite Hσ; reflexivity ].
          -- rewrite mdesc_kind_up, mdesc_kind_sub; cbn; destruct κ; cbn in Hk; congruence.
        * intros (X & HX & Hk); destruct (Hfirst _ HX) as (Φ0' & E' & R1 & S & Hp' & _ & Hed & Hr & ->); injection Hp' as <- <-.
          inversion Hed; subst; cbn in Hr; rewrite Hσ in Hr; injection Hr as <-; cbn in Hk; subst; reflexivity.
      + split; [ discriminate |]; intros (X & HX & Hk).
        destruct (Hfirst _ HX) as (Φ0' & E' & R1 & S & Hp' & _ & Hed & Hr & ->); injection Hp' as <- <-.
        inversion Hed as [| ? ? ? ? R1' HU1 | | | ]; subst; cbn in Hr; rewrite Hσ in Hr; injection Hr as <-;
          rewrite ?mdesc_kind_up, ?mdesc_kind_sub in Hk.
        rewrite (proj1 (mdesc_is_mod_parts _ (udenote_is_mod _ _ _ _ _ _ HU1))) in Hk; discriminate.
      + split; [ discriminate |]; intros (X & HX & Hk).
        destruct (Hfirst _ HX) as (Φ0' & E' & R1 & S & Hp' & _ & Hed & Hr & ->); injection Hp' as <- <-.
        inversion Hed; subst; cbn in Hr; rewrite Hσ in Hr; injection Hr as <-; rewrite ?mdesc_kind_up, ?mdesc_kind_sub in Hk;
          cbn in Hk; discriminate.
    - (* a member past the entry: none for a definition, else the entry's
         unit's *)
      destruct E as [b pv κ A [M |] | pv U | | pv A M U |]; cbn in HsE; try contradiction.
      + cbn [gentry_slot_proofs]; rewrite Hno; split; [ discriminate |]; intros (X & HX & _).
        destruct (Hfirst _ HX) as (Φ0' & E' & R1 & S & Hp' & _ & Hed & Hr & Hc); injection Hp' as <- <-.
        inversion Hed; subst; cbn in Hr; rewrite Hσ in Hr; injection Hr as <-; inversion Hc; subst; cbn in *; discriminate.
      + rewrite (Hent _ _ _ U Hp eq_refl); exact (open_entry_chain _ _ Hg _ _ _ _ _ _ _ _ _ _ _ HCE Hp eq_refl I Hσ).
      + rewrite (Hent _ _ _ U Hp eq_refl); exact (open_entry_chain _ _ Hg _ _ _ _ _ _ _ _ _ _ _ HCE Hp eq_refl I Hσ).
  Qed.

  (** The entries before a body's last are well formed. *)
  Lemma body_ctx_ext_wf : forall Ψ Φx z E, ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx (gm_ext Φx z E) ++ Ψ ->
      ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Ψ.
  Proof. intros * HC; destruct E as [? ? ? ? [] | | | |]; cbn [body_ctx List.app] in HC; exact (ctx_decomp_tail HC). Qed.

  (** The unit of a body's last entry is well formed before it. *)
  Lemma entry_unit_full : forall Ψ Φx z E U0, ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx (gm_ext Φx z E) ++ Ψ -> entry_unit E = Some U0 ->
      unit_full gc_deps gc_stack (body_ctx Φx ++ Ψ) U0.
  Proof.
    intros * HC HU0; destruct E as [? ? ? ? [] | pv U | | pv A M U |]; cbn in HU0; try discriminate; injection HU0 as <-;
      cbn [body_ctx List.app] in HC.
    - exact (proj1 (unit_full_of_eq _ _ _ _ _ (proj2 (ctx_decomp_mod HC)))).
    - exact (proj1 (unit_full_of_eq _ _ _ _ _ (proj2 (proj2 (proj2 (ctx_decomp_dm HC)))))).
  Qed.

  (** A body with one more entry, coherent with the body before it and the
      entry's unit's tables. *)
  Lemma body_coherent_ext : ⊢ᵍ gc_deps ⍮ gc_stack -> forall Ψ κs Φx z E, body_coherent Ψ κs Φx ->
      (forall Ψ0 κs0 U0, slots_proof_coherent Ψ0 κs0 -> entry_unit E = Some U0 -> unit_full gc_deps gc_stack Ψ0 U0 ->
         forall ys x, gentry_slot_proofs γ κs0 E ys x = true <-> chain_proof gc_deps gc_stack Ψ0 (me_lit U0) ys x) ->
      ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx (gm_ext Φx z E) ++ Ψ -> entry_shape E E -> body_coherent Ψ κs (gm_ext Φx z E).
  Proof.
    intros Hg * [Hs He] HE HC Hsh; split.
    - cbn [body_slot_proofs].
      destruct E as [b pv κ A [M |] | pv U | | pv A M U |]; cbn in Hsh; try contradiction; cbn [body_ctx List.app] in HC |- *;
        (apply (slots_coherent_push Hg); [ exact HC | exact Hs |]); intros U0 HU0; try discriminate; injection HU0 as <-.
      + apply HE; [ exact Hs | reflexivity | exact (proj1 (unit_full_of_eq _ _ _ _ _ (proj2 (ctx_decomp_mod HC)))) ].
      + apply HE; [ exact Hs | reflexivity | exact (proj1 (unit_full_of_eq _ _ _ _ _ (proj2 (proj2 (proj2 (ctx_decomp_dm HC)))))) ].
    - intros y Φ0 E0 U0 Hp HU0; cbn [gm_prefix_upto] in Hp.
      destruct (String.eqb y z); [ injection Hp as <- <- <- | exact (He _ _ _ _ Hp HU0) ].
      exact (HE _ _ _ Hs HU0 (entry_unit_full _ _ _ _ _ HC HU0)).
  Qed.

  (** A body grafted with a fragment, each coherent. *)
  Lemma body_coherent_graft : forall Ψ κs A B, gm_noopen B -> body_coherent Ψ κs A ->
      body_coherent (body_ctx A ++ Ψ) (body_slot_proofs γ κs A) B -> body_coherent Ψ κs (gm_graft A B).
  Proof.
    intros * HnB [HsA HeA] [HsB HeB]; split.
    - rewrite body_ctx_graft, body_slot_proofs_graft, <- List.app_assoc; exact HsB.
    - intros y Φ0 E U0 Hp HU0; rewrite (gm_prefix_upto_graft _ _ _ HnB) in Hp.
      destruct (gm_prefix_upto B y) as [P |] eqn:HpB; [| exact (HeA _ _ _ _ Hp HU0) ].
      destruct (gm_prefix_entry _ _ _ HpB) as (P0 & E' & -> & _); cbn [gm_graft] in Hp; injection Hp as <- <-.
      rewrite body_slot_proofs_graft, body_ctx_graft, <- List.app_assoc; exact (HeB _ _ _ _ HpB HU0).
  Qed.

  (** The tables the syntax gives are what chains denote: of a module
      expression past a well-started chain of selections, and of a unit. *)
  Theorem proofs_coherent_all : ⊢ᵍ gc_deps ⍮ gc_stack ->
    (forall H Γ κs zs, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> spine_ok gc_deps gc_stack Γ H zs -> slots_proof_coherent Γ κs ->
       table_coherent Γ κs H zs) /\
    (forall U Γ κs, unit_full gc_deps gc_stack Γ U -> slots_proof_coherent Γ κs ->
       forall ys x, unit_member_proofs γ κs U ys x = true <-> chain_proof gc_deps gc_stack Γ (me_lit U) ys x).
  Proof.
    intros Hg.
    set (Pm := fun H => forall Γ κs zs, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> spine_ok gc_deps gc_stack Γ H zs ->
                 slots_proof_coherent Γ κs -> table_coherent Γ κs H zs).
    set (Pu := fun U => forall Γ κs, unit_full gc_deps gc_stack Γ U -> slots_proof_coherent Γ κs ->
                 forall ys x, unit_member_proofs γ κs U ys x = true <-> chain_proof gc_deps gc_stack Γ (me_lit U) ys x).
    set (Pd := fun D => forall Γ Δ κs, unit_full gc_deps gc_stack Γ (gu_mk Δ D) -> slots_proof_coherent Γ κs ->
                 forall ys x, unit_member_proofs γ κs (gu_mk Δ D) ys x = true <->
                              chain_proof gc_deps gc_stack Γ (me_lit (gu_mk Δ D)) ys x).
    set (Pg := fun Φ => forall Ψ κs, slots_proof_coherent Ψ κs -> ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx (gm_expand Φ) ++ Ψ ->
                 body_shape (gm_expand Φ) (gm_expand Φ) -> body_coherent Ψ κs (gm_expand Φ)).
    set (Pn := fun E => forall Ψ κs U0, slots_proof_coherent Ψ κs -> entry_unit E = Some U0 -> unit_full gc_deps gc_stack Ψ U0 ->
                 forall ys x, gentry_slot_proofs γ κs E ys x = true <-> chain_proof gc_deps gc_stack Ψ (me_lit U0) ys x).
    assert (Hall : (forall M : exp, True) /\ (forall H, Pm H) /\ (forall b : binding, True) /\ (forall U, Pu U) /\
                   (forall D, Pd D) /\ (forall Φ, Pg Φ) /\ (forall E, Pn E) /\ (forall e : centry, True)).
    { apply (syn_mut_ind (fun _ => True) Pm (fun _ => True) Pu Pd Pg Pn (fun _ => True));
        unfold Pm, Pu, Pd, Pg, Pn; cbn beta; intros; try exact I.
      (* a loaded unit or an open frame *)
      1: { exact (table_coherent_unit Hg _ _ _ _). }
      (* a slot *)
      1: { destruct (me_denotes _ _ _ _ _ H) as (R & _ & HR & _); inversion HR; subst; try (cbn in *; discriminate).
           eapply table_coherent_var; [ exact H1 | apply ctx_find_mod_complete; eassumption ]. }
      (* a selection *)
      1: { apply table_coherent_mem; apply H0; [ exact (proj1 (modexp_gen _ _ _ _ _ H1)) | | exact H3 ].
           split; [ discriminate | intros z zs' [= <- _]; destruct (me_denotes _ _ _ _ _ H1) as (S & _ & HS & _); exists S; exact HS ]. }
      (* an application *)
      1: { apply (table_coherent_app Hg); [ exact H2 | exact H3 |].
           apply H0; [ exact (proj1 (proj1 (modexp_gen _ _ _ _ _ H2))) | exact (spine_ok_app _ _ Hg _ _ _ _ H2 H3) | exact H4 ]. }
      (* a literal *)
      1: { intros ys x; cbn [modexp_member_proofs]; apply H; [ exact (proj1 (modexp_gen _ _ _ _ _ H0)) | exact H2 ]. }
      (* a unit: its definition's *)
      1: { apply H0; assumption. }
      (* a body *)
      1: { destruct s; [| cbn in H0; contradiction ]. exact (unit_coherent_body Hg _ _ _ _ H0 H1 H ys x). }
      (* an alias *)
      1: { apply (unit_coherent_alias Hg _ _ _ _ H0 H1); intros κs' Hκ'.
           apply H; [ exact (unit_alias_target _ _ _ _ _ H0) | | exact Hκ' ].
           split; [ intros _; exact (unit_alias_frame_free _ _ _ _ _ H0) | intros z zs' Hz; discriminate ]. }
      (* the empty body *)
      1: { split; [ exact H | intros; cbn in *; discriminate ]. }
      (* an entry *)
      1: { cbn [gm_expand] in H2, H3 |- *; destruct H3 as (Hsh0 & _ & HsE).
           apply (body_coherent_ext Hg); [ apply H; [ exact H1 | exact (body_ctx_ext_wf _ _ _ _ H2) | exact Hsh0 ] | exact H0 | exact H2 | exact HsE ]. }
      (* an open: its stored entries grafted *)
      1: { cbn [gm_expand] in H4, H5 |- *.
           pose proof (gm_noopen_expand Φg) as HnB.
           rewrite body_ctx_graft, <- List.app_assoc in H4.
           pose proof (ctx_app_wf_tail _ _ _ _ H4) as HA.
           pose proof (H0 _ _ H3 HA (body_shape_graft_base _ _ H5)) as HcA.
           apply (body_coherent_graft _ _ _ _ HnB HcA).
           apply H2; [ exact (proj1 HcA) | exact H4 | exact (body_shape_graft_fragment _ _ H5) ]. }
      (* entries: a module or a definition with a module part, its unit's *)
      all: try (cbn in *; discriminate).
      all: cbn [entry_unit gentry_slot_proofs] in *; match goal with HE : Some ?U = Some ?U0 |- _ => injection HE as <- end;
        match goal with IH : forall _ _, unit_full _ _ _ ?U -> _ |- _ => apply IH; assumption end. }
    destruct Hall as (_ & HPm & _ & HPu & _); split; [ exact HPm | exact HPu ].
  Qed.

  (** The table a well-formed module expression that is no open frame
      gives, at tables coherent with its context, is what its chains
      denote. *)
  Corollary modexp_proofs_coherent : ⊢ᵍ gc_deps ⍮ gc_stack -> forall Γ E, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ E ≈ E ->
      frame_free_target gc_deps gc_stack Γ E -> forall κs, slots_proof_coherent Γ κs ->
      forall ys x, modexp_member_proofs γ κs E ys x = true <-> chain_proof gc_deps gc_stack Γ E ys x.
  Proof.
    intros Hg * HE Hff κs Hκ ys x.
    refine (proj1 (proofs_coherent_all Hg) E Γ κs nil HE _ Hκ ys x).
    split; [ intros _; exact Hff | intros z zs' Hz; discriminate ].
  Qed.

End Coherence.
