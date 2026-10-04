(** * Unsealing a Global Context

    [abstract] only hides a body from conversion: an opaque definition still
    has one.  Unsealing a global context makes every definition with a body
    transparent, and leaves axioms and everything else as they are.  Making a
    definition transparent only adds the δ-equation of [wf_exp_eq_mem_glob_unfold],
    and no rule asks a filed definition to be opaque, so every judgment, the
    global ones included, survives unsealing ([unseal_preserves_wf]).

    The rules that read the transparency flag at all are:
    - [wf_exp_eq_mem_glob_unfold], which asks for [true]; unsealing keeps it;
    - [entry_shape], which asks for [true] on both sides, but only ever of a
      local unit (a slot, a [let module] or a literal), which unsealing does
      not touch; the units it reaches, in [Θ] and [Ξ], are read through
      [gc_resolve] and [gc_module] only.
    [member_type] and [member_unfold] read the privacy flag, never the
    transparency one.

    A global context without axioms ([gc_no_axioms]) unseals to a transparent
    one ([gc_no_axioms_unseal_transparent]), which is what consistency and
    canonicity are proved at. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Import Definitions Command.
Import Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Unsealing *)

(** The flag of a definition once unsealed: transparent when it has a body. *)
Definition flag_unseal (b : bool) (B : option exp) : bool :=
  match B with
  | Some _ => true
  | None => b
  end.

Fixpoint ge_unseal (E : gentry) : gentry :=
  match E with
  | ge_def b pv A B => ge_def (flag_unseal b B) pv A B
  | ge_mod (gu_mk Δ (md_body Φ)) => ge_mod (gu_mk Δ (md_body (gm_unseal Φ)))
  | ge_mod U => ge_mod U
  end
with gm_unseal (Φ : gmod) : gmod :=
  match Φ with
  | gm_nil => gm_nil
  | gm_ext Φ x E => gm_ext (gm_unseal Φ) x (ge_unseal E)
  | gm_check Φ c => gm_check (gm_unseal Φ) c
  end.

(** An alias has no definition of its own, so it is unchanged. *)
Definition gu_unseal (U : gunit) : gunit :=
  match U with
  | gu_mk Δ (md_body Φ) => gu_mk Δ (md_body (gm_unseal Φ))
  | _ => U
  end.

Fixpoint gd_unseal (d : gdep) : gdep :=
  match d with
  | nil => nil
  | (fp, U) :: d => (fp, gu_unseal U) :: gd_unseal d
  end.

Fixpoint gds_unseal (Θ : gdeps) : gdeps :=
  match Θ with
  | nil => nil
  | d :: Θ => gd_unseal d :: gds_unseal Θ
  end.

Fixpoint gs_unseal (Ξ : gstack) : gstack :=
  match Ξ with
  | nil => nil
  | (mp, U) :: Ξ => (mp, gu_unseal U) :: gs_unseal Ξ
  end.

Lemma gd_unseal_app : forall d d', gd_unseal (d ++ d') = gd_unseal d ++ gd_unseal d'.
Proof. induction d as [| [fp U] d IH]; intros; cbn; congruence. Qed.

Lemma ge_unseal_mod : forall U, ge_unseal (ge_mod U) = ge_mod (gu_unseal U).
Proof. intros [Δ [Φ | E]]; reflexivity. Qed.

Lemma gu_params_unseal : forall U, gu_params (gu_unseal U) = gu_params U.
Proof. intros [Δ [Φ | E]]; reflexivity. Qed.

Lemma gu_mod_unseal : forall U, gu_mod (gu_unseal U) = gm_unseal (gu_mod U).
Proof. intros [Δ [Φ | E]]; reflexivity. Qed.

Lemma gs_tele_unseal : forall Ξ, gs_tele (gs_unseal Ξ) = gs_tele Ξ.
Proof. induction Ξ as [| [mp U] Ξ IH]; cbn; [ reflexivity | rewrite gu_params_unseal, IH; reflexivity ]. Qed.

Lemma gm_names_unseal : forall Φ, gm_names (gm_unseal Φ) = gm_names Φ.
Proof. induction Φ; cbn; congruence. Qed.

Lemma gm_fresh_unseal : forall x Φ, gm_fresh x Φ -> gm_fresh x (gm_unseal Φ).
Proof. unfold gm_fresh; intros; rewrite gm_names_unseal; assumption. Qed.

(** ** Resolution Commutes with Unsealing

    What a path resolves to is unsealed with the context; what a module path
    resolves to is not changed at all, since a body module is handed back as
    its telescope only, and an alias is unchanged. *)

Lemma gm_resolve_unseal : forall Φ ip,
    gm_resolve (gm_unseal Φ) ip = option_map ge_unseal (gm_resolve Φ ip).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] ip; cbn; [ reflexivity | | apply IH ].
  destruct ip as [| x ip']; [ reflexivity |].
  destruct (String.eqb x y); [| apply IH ].
  destruct ip' as [| z ip''], E as [b pv A B | [Δ' [Φ' | E']]]; cbn; try reflexivity.
  apply IH.
Qed.

Lemma gm_submodule_unseal : forall Φ T x ip,
    gm_submodule T (gm_unseal Φ) x ip = gm_submodule T Φ x ip.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] T x ip; cbn; [ reflexivity | | apply IH ].
  destruct (String.eqb x y); [| apply IH ].
  destruct E as [b pv A B | [Δ' [Φ' | E']]]; cbn; try reflexivity.
  destruct ip; [ reflexivity | apply IH ].
Qed.

Lemma gm_module_unseal : forall Φ T ip,
    gm_module T (gm_unseal Φ) ip = gm_module T Φ ip.
Proof. intros * ; destruct ip; cbn; [ reflexivity | apply gm_submodule_unseal ]. Qed.

Lemma gs_find_unseal : forall Ξ p,
    gs_find (gs_unseal Ξ) p = option_map (fun r => (gu_unseal (fst r), snd r)) (gs_find Ξ p).
Proof.
  induction Ξ as [| [mp U] Ξ IH]; intros; cbn; [ reflexivity |].
  destruct (qname_strip mp p); [ reflexivity | apply IH ].
Qed.

Lemma gs_find_tele_unseal : forall Ξ p,
    gs_find_tele (gs_unseal Ξ) p =
      option_map (fun r => let '(U, ip, T) := r in (gu_unseal U, ip, T)) (gs_find_tele Ξ p).
Proof.
  induction Ξ as [| [mp U] Ξ IH]; intros; cbn; [ reflexivity |].
  destruct (qname_strip mp p); [ rewrite gs_tele_unseal; reflexivity | apply IH ].
Qed.

Lemma gd_lookup_unseal : forall d fp,
    gd_lookup (gd_unseal d) fp = option_map gu_unseal (gd_lookup d fp).
Proof.
  unfold gd_lookup; induction d as [| [fq U] d IH]; intros; cbn; [ reflexivity |].
  destruct (path_beq fp fq); [ reflexivity | apply IH ].
Qed.

Lemma concat_unseal : forall Θ, List.concat (gds_unseal Θ) = gd_unseal (List.concat Θ).
Proof.
  induction Θ as [| d Θ IH]; cbn; [ reflexivity |].
  rewrite IH, gd_unseal_app; reflexivity.
Qed.

Lemma gds_lookup_unseal : forall Θ fp,
    gds_lookup (gds_unseal Θ) fp = option_map gu_unseal (gds_lookup Θ fp).
Proof. intros; unfold gds_lookup; rewrite concat_unseal; apply gd_lookup_unseal. Qed.

Lemma gc_resolve_unseal : forall Θ Ξ p,
    gc_resolve (gds_unseal Θ) (gs_unseal Ξ) p = option_map ge_unseal (gc_resolve Θ Ξ p).
Proof.
  intros; unfold gc_resolve; rewrite gs_find_unseal.
  destruct (gs_find Ξ p) as [[U ip] |]; cbn; [ rewrite gu_mod_unseal; apply gm_resolve_unseal |].
  rewrite gds_lookup_unseal.
  destruct (gds_lookup Θ (q_unit p)); cbn; [ rewrite gu_mod_unseal; apply gm_resolve_unseal | reflexivity ].
Qed.

Lemma gc_resolve_unseal_def : forall Θ Ξ p b pv A B,
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    gc_resolve (gds_unseal Θ) (gs_unseal Ξ) p = Some (ge_def (flag_unseal b B) pv A B).
Proof. intros * H; rewrite gc_resolve_unseal, H; reflexivity. Qed.

(** A transparent definition stays as it is. *)
Lemma gc_resolve_unseal_transparent : forall Θ Ξ p pv A M,
    gc_resolve Θ Ξ p = Some (ge_def true pv A (Some M)) ->
    gc_resolve (gds_unseal Θ) (gs_unseal Ξ) p = Some (ge_def true pv A (Some M)).
Proof. intros * H; exact (gc_resolve_unseal_def _ _ _ _ _ _ _ H). Qed.

Lemma gc_module_unseal : forall Θ Ξ p,
    gc_module (gds_unseal Θ) (gs_unseal Ξ) p = gc_module Θ Ξ p.
Proof.
  intros; unfold gc_module; rewrite gs_find_tele_unseal.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T] |]; cbn; [ reflexivity | |].
  - rewrite gu_params_unseal, gu_mod_unseal; apply gm_submodule_unseal.
  - rewrite gds_lookup_unseal.
    destruct (gds_lookup Θ (q_unit p)); cbn; [| reflexivity ].
    rewrite gu_params_unseal, gu_mod_unseal; apply gm_module_unseal.
Qed.

(** ** Freshness *)

Lemma gd_names_unseal : forall d, List.map fst (gd_unseal d) = List.map fst d.
Proof. induction d as [| [fp U] d IH]; cbn; congruence. Qed.

Lemma gd_fresh_unseal : forall fp d, gd_fresh fp d -> gd_fresh fp (gd_unseal d).
Proof. unfold gd_fresh; intros; rewrite gd_names_unseal; assumption. Qed.

Lemma gds_fresh_unseal : forall fp Θ, gds_fresh fp Θ -> gds_fresh fp (gds_unseal Θ).
Proof. unfold gds_fresh; intros; rewrite concat_unseal; apply gd_fresh_unseal; assumption. Qed.

Lemma frame_fresh_unseal : forall Θ Ξ mp,
    frame_fresh Θ Ξ mp -> frame_fresh (gds_unseal Θ) (gs_unseal Ξ) mp.
Proof.
  intros * H; destruct Ξ as [| [mq U] Ξ]; cbn in *.
  - destruct H; split; [ apply gds_fresh_unseal |]; assumption.
  - destruct H as (x & -> & Hx); exists x; split; [ reflexivity |].
    rewrite gu_mod_unseal; apply gm_fresh_unseal; assumption.
Qed.

(** ** Members *)

Lemma member_type_unseal : forall Θ Ξ,
    (forall Γ H ch R, member_type Θ Ξ Γ H ch R ->
       member_type (gds_unseal Θ) (gs_unseal Ξ) Γ H ch R) /\
    (forall Γ U ch R, unit_member_type Θ Ξ Γ U ch R ->
       unit_member_type (gds_unseal Θ) (gs_unseal Ξ) Γ U ch R).
Proof.
  intros; apply member_type_both_ind; intros; econstructor;
    eauto using gc_resolve_unseal_def; rewrite gc_module_unseal; eassumption.
Qed.

Corollary member_type_unseal' : forall Θ Ξ Γ H ch R,
    member_type Θ Ξ Γ H ch R -> member_type (gds_unseal Θ) (gs_unseal Ξ) Γ H ch R.
Proof. intros Θ Ξ; apply (member_type_unseal Θ Ξ). Qed.

Lemma member_unfold_ch_unseal : forall Θ Ξ Γ H ch,
    member_unfold_ch (gds_unseal Θ) (gs_unseal Ξ) Γ H ch = member_unfold_ch Θ Ξ Γ H ch.
Proof.
  intros; revert ch; induction H as [fp | x | H IH y | H IH N | U]; intros; cbn; auto.
  - rewrite gc_resolve_unseal, gc_module_unseal.
    destruct (gc_resolve Θ Ξ (q_abs fp ch)) as [[b pv A B | [Δ [Φ | E]]] |]; reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma member_unfold_unseal : forall Θ Ξ Γ H x,
    member_unfold (gds_unseal Θ) (gs_unseal Ξ) Γ H x = member_unfold Θ Ξ Γ H x.
Proof. intros; apply member_unfold_ch_unseal. Qed.

Lemma member_ok_unseal : forall Θ Ξ Γ H n,
    member_ok Θ Ξ Γ H n -> member_ok (gds_unseal Θ) (gs_unseal Ξ) Γ H n.
Proof.
  unfold member_ok; intros * [[A HA] | [A HA]]; [ left | right ];
    exists A; apply member_type_unseal'; assumption.
Qed.

(** ** Unsealing Preserves Every Judgment *)

Theorem unseal_preserves_wf :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ M : A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ M ≈ M' : A) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ A ⊆ A') /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ᵘ U ≈ U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ᵐ H ≈ H') /\
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢e E -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ mp ⊢e ge_unseal E) /\
  (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ mp ⍮ Δ ⊢m gm_unseal Φ) /\
  (forall Θ Ξ mp U, Θ ⍮ Ξ ⍮ mp ⊢u U -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ mp ⊢u gu_unseal U) /\
  (forall Θ d, wf_gdep Θ d -> wf_gdep (gds_unseal Θ) (gd_unseal d)) /\
  (forall Θ, wf_gdeps Θ -> wf_gdeps (gds_unseal Θ)) /\
  (forall Θ Ξ, wf_gstack Θ Ξ -> wf_gstack (gds_unseal Θ) (gs_unseal Ξ)) /\
  (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> ⊢g gds_unseal Θ ⍮ gs_unseal Ξ).
Proof.
  apply wf_mut_ind_all; intros; cbn.
  all: try rewrite <- (gs_tele_unseal Ξ).
  all: try solve [ econstructor; rewrite ?gs_tele_unseal;
                   eauto using gc_resolve_unseal_def, gc_resolve_unseal_transparent,
                     member_ok_unseal, gm_fresh_unseal, gds_fresh_unseal, gd_fresh_unseal,
                     frame_fresh_unseal, member_type_unseal';
                   rewrite ?member_unfold_unseal; eassumption ].
Qed.

Corollary unseal_exp : forall Θ Ξ Γ A M,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ M : A.
Proof. apply unseal_preserves_wf. Qed.

Corollary unseal_exp_eq : forall Θ Ξ Γ A M M',
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ M ≈ M' : A.
Proof. apply unseal_preserves_wf. Qed.

Corollary unseal_subtyp : forall Θ Ξ Γ A A',
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> gds_unseal Θ ⍮ gs_unseal Ξ ⍮ Γ ⊢ A ⊆ A'.
Proof. apply unseal_preserves_wf. Qed.

Corollary unseal_gctx : forall Θ Ξ, ⊢g Θ ⍮ Ξ -> ⊢g gds_unseal Θ ⍮ gs_unseal Ξ.
Proof. apply unseal_preserves_wf. Qed.

(** ** Global Contexts without Axioms

    Every definition has a body, at every depth of nesting; an alias declares
    no definition of its own.  Transparency is not asked for. *)

Fixpoint ge_no_axioms (E : gentry) : Prop :=
  match E with
  | ge_def _ _ _ B => B <> None
  | ge_mod (gu_mk _ (md_body Φ)) => gm_no_axioms Φ
  | ge_mod (gu_mk _ (md_alias _)) => True
  end
with gm_no_axioms (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ _ E => gm_no_axioms Φ /\ ge_no_axioms E
  | gm_check Φ _ => gm_no_axioms Φ
  end.

Definition gds_no_axioms (Θ : gdeps) : Prop :=
  forall fp U, List.In (fp, U) (List.concat Θ) -> gm_no_axioms (gu_mod U).

Definition gs_no_axioms (Ξ : gstack) : Prop :=
  forall mp U, List.In (mp, U) Ξ -> gm_no_axioms (gu_mod U).

Definition gc_no_axioms (Θ : gdeps) (Ξ : gstack) : Prop := gds_no_axioms Θ /\ gs_no_axioms Ξ.

Lemma gm_transparent_no_axioms : forall Φ, gm_transparent Φ -> gm_no_axioms Φ.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] HΦ; cbn in *; [ exact I | | exact (IH _ HΦ) ].
  destruct HΦ as [HΦ HE]; split; [ exact (IH _ HΦ) |].
  destruct E as [b pv A B | [Δ' [Φ' | E']]]; cbn in *; [ apply HE | exact (IH _ HE) | exact I ].
Qed.

(** A transparent global context has no axioms. *)
Lemma gc_transparent_no_axioms : forall Θ Ξ, gc_transparent Θ Ξ -> gc_no_axioms Θ Ξ.
Proof.
  intros * [HΘ HΞ]; split; intros ? ? Hin;
    apply gm_transparent_no_axioms; [ exact (HΘ _ _ Hin) | exact (HΞ _ _ Hin) ].
Qed.

Lemma gm_no_axioms_unseal_transparent : forall Φ, gm_no_axioms Φ -> gm_transparent (gm_unseal Φ).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] HΦ; cbn in *; [ exact I | | exact (IH _ HΦ) ].
  destruct HΦ as [HΦ HE]; split; [ exact (IH _ HΦ) |].
  destruct E as [b pv A [M |] | [Δ' [Φ' | E']]]; cbn in *;
    [ split; congruence | contradiction | exact (IH _ HE) | exact I ].
Qed.

Lemma gd_unseal_in : forall d fp U',
    List.In (fp, U') (gd_unseal d) -> exists U, U' = gu_unseal U /\ List.In (fp, U) d.
Proof.
  induction d as [| [fq U] d IH]; intros * Hin; cbn in Hin; [ contradiction |].
  destruct Hin as [[= <- <-] | Hin]; [ exists U; cbn; auto |].
  destruct (IH _ _ Hin) as (U0 & -> & ?); exists U0; cbn; auto.
Qed.

Lemma gs_unseal_in : forall Ξ mp U',
    List.In (mp, U') (gs_unseal Ξ) -> exists U, U' = gu_unseal U /\ List.In (mp, U) Ξ.
Proof.
  induction Ξ as [| [mq U] Ξ IH]; intros * Hin; cbn in Hin; [ contradiction |].
  destruct Hin as [[= <- <-] | Hin]; [ exists U; cbn; auto |].
  destruct (IH _ _ Hin) as (U0 & -> & ?); exists U0; cbn; auto.
Qed.

(** Without axioms, unsealing makes the global context transparent. *)
Theorem gc_no_axioms_unseal_transparent : forall Θ Ξ,
    gc_no_axioms Θ Ξ -> gc_transparent (gds_unseal Θ) (gs_unseal Ξ).
Proof.
  intros * [HΘ HΞ]; split; intros ? ? Hin.
  - rewrite concat_unseal in Hin; destruct (gd_unseal_in _ _ _ Hin) as (U0 & -> & Hin0).
    rewrite gu_mod_unseal; apply gm_no_axioms_unseal_transparent, (HΘ _ _ Hin0).
  - destruct (gs_unseal_in _ _ _ Hin) as (U0 & -> & Hin0).
    rewrite gu_mod_unseal; apply gm_no_axioms_unseal_transparent, (HΞ _ _ Hin0).
Qed.


(** A resolved definition without a body is an axiom. *)
Lemma gm_no_axioms_resolve : forall Φ ip b pv A B,
    gm_no_axioms Φ -> gm_resolve Φ ip = Some (ge_def b pv A B) -> B <> None.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] ip b pv A0 B0 HΦ H; cbn in H, HΦ; [ discriminate | | eapply IH; eassumption ].
  destruct HΦ as [HΦ HE].
  destruct ip as [| x ip']; [ discriminate |].
  destruct (String.eqb x y); [| eapply IH; eassumption ].
  destruct ip' as [| z ip''], E as [b' pv' A B | [Δ' [Φ' | E']]]; try discriminate.
  - injection H as <- <- <- <-; exact HE.
  - eapply IH; [ exact HE | exact H ].
Qed.

Lemma gc_no_axioms_resolve : forall Θ Ξ p b pv A B,
    gc_no_axioms Θ Ξ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    B <> None.
Proof.
  intros * [HΘ HΞ] Hr.
  destruct (gc_resolve_inv _ _ _ _ Hr) as [(mp & U & ip & Hin & Hm) | (fp & U & Hl & Hm)].
  - exact (gm_no_axioms_resolve _ _ _ _ _ _ (HΞ _ _ Hin) Hm).
  - exact (gm_no_axioms_resolve _ _ _ _ _ _ (HΘ _ _ (gd_lookup_in _ _ _ Hl)) Hm).
Qed.

(** ** Running Commands Files No Axiom

    A [def] always has a body ([cc_def]), so no command files an axiom, and
    every global context a run reaches has none: the consistency and
    canonicity theorems at [gc_no_axioms] hold of every program. *)

Lemma in_concat_gds_merge : forall Θ Θ' x,
    List.In x (List.concat (gds_merge Θ Θ')) -> List.In x (List.concat Θ) \/ List.In x (List.concat Θ').
Proof.
  apply (gds_merge_ind (fun Θ Θ' => forall x,
    List.In x (List.concat (gds_merge Θ Θ')) -> List.In x (List.concat Θ) \/ List.In x (List.concat Θ'))).
  - intros x Hx; left; exact Hx.
  - intros * Hl IH x; rewrite gds_merge_l by exact Hl; cbn.
    intros [Hx | Hx]%List.in_app_or; [ left; apply List.in_or_app; auto |].
    destruct (IH _ Hx); [ left; apply List.in_or_app |]; auto.
  - intros * Hl IH x; rewrite gds_merge_r by exact Hl; cbn.
    intros [Hx | Hx]%List.in_app_or; [ right; apply List.in_or_app; auto |].
    destruct (IH _ Hx); [| right; apply List.in_or_app ]; auto.
  - intros * Hl IH x; rewrite gds_merge_both by exact Hl; cbn.
    intros [Hx | Hx]%List.in_app_or.
    + unfold gd_union in Hx; apply List.in_app_or in Hx as [Hx | Hx%List.filter_In];
        [ left | right ]; apply List.in_or_app; left; [ exact Hx | exact (proj1 Hx) ].
    + destruct (IH _ Hx); [ left | right ]; apply List.in_or_app; auto.
Qed.

Lemma gds_no_axioms_merge : forall Θ Θ',
    gds_no_axioms Θ -> gds_no_axioms Θ' -> gds_no_axioms (gds_merge Θ Θ').
Proof. intros * H H' fp U [Hin | Hin]%in_concat_gds_merge; eauto. Qed.

Lemma gds_no_axioms_file : forall fp U Θ,
    gm_no_axioms (gu_mod U) -> gds_no_axioms Θ -> gds_no_axioms (file fp U Θ).
Proof. intros * HU HΘ fq V [[= <- <-] | Hin]; eauto. Qed.

Lemma gs_no_axioms_nil : gs_no_axioms nil.
Proof. intros ? ? []. Qed.

Lemma gds_no_axioms_nil : gds_no_axioms nil.
Proof. intros ? ? []. Qed.

Lemma gs_no_axioms_push : forall mp Δ Ξ, gs_no_axioms Ξ -> gs_no_axioms (gs_push mp Δ Ξ).
Proof. intros * H mq U [[= <- <-] | Hin]; [ exact I | eauto ]. Qed.

Lemma gs_no_axioms_add : forall x E Ξ,
    ge_no_axioms E -> gs_no_axioms Ξ -> gs_no_axioms (gs_add x E Ξ).
Proof.
  intros * HE HΞ mq U Hin; destruct Ξ as [| [mp V] Ξ]; [ destruct Hin |].
  destruct Hin as [[= <- <-] | Hin]; [| eauto using in_cons ].
  cbn; split; [ apply (HΞ mp V); left; reflexivity | exact HE ].
Qed.

Lemma gs_no_axioms_head : forall mp U Ξ, gs_no_axioms ((mp, U) :: Ξ) -> gm_no_axioms (gu_mod U).
Proof. intros * H; apply (H mp U); left; reflexivity. Qed.

Lemma gs_no_axioms_tail : forall f Ξ, gs_no_axioms (f :: Ξ) -> gs_no_axioms Ξ.
Proof. intros * H mp U Hin; apply (H mp U); right; exact Hin. Qed.

#[local] Hint Resolve gs_no_axioms_head gs_no_axioms_tail gds_no_axioms_merge gds_no_axioms_file gs_no_axioms_nil gds_no_axioms_nil
  gs_no_axioms_push gs_no_axioms_add : mctt.

Section Run.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).

  Theorem run_no_axioms :
    (forall ch Θ Ξ c Θ' Ξ', run_cmd load_path read to_core ch Θ Ξ c Θ' Ξ' ->
       gc_no_axioms Θ Ξ -> gc_no_axioms Θ' Ξ') /\
    (forall ch Θ Ξ cs Θ' Ξ', run_cmds load_path read to_core ch Θ Ξ cs Θ' Ξ' ->
       gc_no_axioms Θ Ξ -> gc_no_axioms Θ' Ξ') /\
    (forall ch u Θ U, run_unit load_path read to_core ch u Θ U ->
       gds_no_axioms Θ /\ gm_no_axioms (gu_mod U)).
  Proof.
    apply run_mut_ind; intros; unfold gc_no_axioms in *; destruct_all;
      (* the runs inside start where the hypotheses hold, the unit's frame empty *)
      repeat match goal with IH : _ /\ _ -> _ /\ _ |- _ =>
        specialize (IH ltac:(split; auto with mctt)); destruct IH end;
      split; eauto with mctt.
    (* a definition has a body, and a module's body is the frame its commands
       ended on *)
    all: apply gs_no_axioms_add; cbn; eauto with mctt; congruence.
  Qed.

  Corollary run_unit_no_axioms : forall ch u Θ U,
      run_unit load_path read to_core ch u Θ U -> gds_no_axioms Θ /\ gm_no_axioms (gu_mod U).
  Proof. apply run_no_axioms. Qed.

  (** Every state a unit runs through, from nothing, has no axioms. *)
  Corollary run_cmds_no_axioms : forall ch cs Θ Ξ,
      run_cmds load_path read to_core ch nil nil cs Θ Ξ -> gc_no_axioms Θ Ξ.
  Proof. intros * H; eapply run_no_axioms; [ exact H | split; auto with mctt ]. Qed.

  (** What a program files, filed with it. *)
  Corollary prog_sem_no_axioms : forall prg Θ U,
      prog_sem load_path read to_core prg Θ U -> gc_no_axioms (file (prog_path prg) U Θ) nil.
  Proof.
    intros * (u & _ & Hu); destruct (run_unit_no_axioms _ _ _ _ Hu).
    split; auto with mctt.
  Qed.
End Run.
