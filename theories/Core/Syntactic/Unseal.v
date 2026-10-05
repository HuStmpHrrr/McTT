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
  | ge_mod pv (gu_mk Δ (md_body Φ)) => ge_mod pv (gu_mk Δ (md_body (gm_unseal Φ)))
  | ge_mod pv U => ge_mod pv U
  end
with gm_unseal (Φ : gmod) : gmod :=
  match Φ with
  | gm_nil => gm_nil
  | gm_ext Φ x E => gm_ext (gm_unseal Φ) x (ge_unseal E)
  | gm_open Φ H its => gm_open (gm_unseal Φ) H its
  end.

(** An alias has no definition of its own, so it is unchanged. *)
Definition gu_unseal (U : gunit) : gunit :=
  match U with
  | gu_mk Δ (md_body Φ) => gu_mk Δ (md_body (gm_unseal Φ))
  | _ => U
  end.

Fixpoint gds_unseal (Θ : gdeps) : gdeps :=
  match Θ with
  | nil => nil
  | (fp, U) :: Θ => (fp, gu_unseal U) :: gds_unseal Θ
  end.

Fixpoint gs_unseal (Ξ : gstack) : gstack :=
  match Ξ with
  | nil => nil
  | (mp, U) :: Ξ => (mp, gu_unseal U) :: gs_unseal Ξ
  end.

Lemma ge_unseal_mod : forall pv U, ge_unseal (ge_mod pv U) = ge_mod pv (gu_unseal U).
Proof. intros pv [Δ [Φ | E]]; reflexivity. Qed.

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
  destruct ip' as [| z ip''], E as [b pv A B | ? [Δ' [Φ' | E']]]; cbn; try reflexivity.
  apply IH.
Qed.

Lemma gm_submodule_unseal : forall Φ T x ip,
    gm_submodule T (gm_unseal Φ) x ip = gm_submodule T Φ x ip.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] T x ip; cbn; [ reflexivity | | apply IH ].
  destruct (String.eqb x y); [| apply IH ].
  destruct E as [b pv A B | ? [Δ' [Φ' | E']]]; cbn; try reflexivity.
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

Lemma gds_lookup_unseal : forall Θ fp,
    gds_lookup (gds_unseal Θ) fp = option_map gu_unseal (gds_lookup Θ fp).
Proof.
  induction Θ as [| [fq U] Θ IH]; intros; cbn; [ reflexivity |].
  destruct (path_beq fp fq); [ reflexivity | apply IH ].
Qed.

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

Lemma frame_fresh_unseal : forall Θ Ξ mp,
    frame_fresh Θ Ξ mp -> frame_fresh (gds_unseal Θ) (gs_unseal Ξ) mp.
Proof.
  intros * H; destruct Ξ as [| [mq U] Ξ]; cbn in *.
  - destruct H as [Hn Hc]; split; [ rewrite gds_lookup_unseal, Hn; reflexivity | assumption ].
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
    destruct (gc_resolve Θ Ξ (q_abs fp ch)) as [[b pv A B | ? [Δ [Φ | E]]] |]; reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma member_unfold_unseal : forall Θ Ξ Γ H x,
    member_unfold (gds_unseal Θ) (gs_unseal Ξ) Γ H x = member_unfold Θ Ξ Γ H x.
Proof. intros; apply member_unfold_ch_unseal. Qed.

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
  (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> ⊢g gds_unseal Θ ⍮ gs_unseal Ξ).
Proof.
  apply wf_mut_ind_all; intros; cbn.
  all: try rewrite <- (gs_tele_unseal Ξ).
  all: try solve [ econstructor; rewrite ?gs_tele_unseal;
                   eauto using gc_resolve_unseal_def, gc_resolve_unseal_transparent,
                     gm_fresh_unseal,
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
  | ge_mod _ (gu_mk _ (md_body Φ)) => gm_no_axioms Φ
  | ge_mod _ (gu_mk _ (md_alias _)) => True
  end
with gm_no_axioms (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ _ E => gm_no_axioms Φ /\ ge_no_axioms E
  | gm_open Φ _ _ => gm_no_axioms Φ
  end.

Definition gds_no_axioms (Θ : gdeps) : Prop :=
  forall fp U, List.In (fp, U) Θ -> gm_no_axioms (gu_mod U).

Definition gs_no_axioms (Ξ : gstack) : Prop :=
  forall mp U, List.In (mp, U) Ξ -> gm_no_axioms (gu_mod U).

Definition gc_no_axioms (Θ : gdeps) (Ξ : gstack) : Prop := gds_no_axioms Θ /\ gs_no_axioms Ξ.

Lemma gm_transparent_no_axioms : forall Φ, gm_transparent Φ -> gm_no_axioms Φ.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] HΦ; cbn in *; [ exact I | | exact (IH _ HΦ) ].
  destruct HΦ as [HΦ HE]; split; [ exact (IH _ HΦ) |].
  destruct E as [b pv A B | ? [Δ' [Φ' | E']]]; cbn in *; [ apply HE | exact (IH _ HE) | exact I ].
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
  destruct E as [b pv A [M |] | ? [Δ' [Φ' | E']]]; cbn in *;
    [ split; congruence | contradiction | exact (IH _ HE) | exact I ].
Qed.

Lemma gds_unseal_in : forall Θ fp U',
    List.In (fp, U') (gds_unseal Θ) -> exists U, U' = gu_unseal U /\ List.In (fp, U) Θ.
Proof.
  induction Θ as [| [fq U] Θ IH]; intros * Hin; cbn in Hin; [ contradiction |].
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
  - destruct (gds_unseal_in _ _ _ Hin) as (U0 & -> & Hin0).
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
  destruct ip' as [| z ip''], E as [b' pv' A B | ? [Δ' [Φ' | E']]]; try discriminate.
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
  - exact (gm_no_axioms_resolve _ _ _ _ _ _ (HΘ _ _ (gds_lookup_in _ _ _ Hl)) Hm).
Qed.

(** ** Running Commands Without Axioms

    A command declares an axiom only as [cc_def] with no body.  A run of
    commands that declare none, loading units that declare none, files no
    axiom, so every global context it reaches has none: the consistency and
    canonicity theorems at [gc_no_axioms] hold of every such program. *)

(** No axiom, at any depth of nesting. *)
Fixpoint cmd_no_axioms (c : ccmd) : Prop :=
  match c with
  | cc_def _ _ _ _ oM => oM <> None
  | cc_mod _ _ _ cs => List.fold_right (fun c P => cmd_no_axioms c /\ P) True cs
  | _ => True
  end.

Definition cmds_no_axioms (cs : list ccmd) : Prop := List.Forall cmd_no_axioms cs.

Definition unit_no_axioms (u : cunit) : Prop :=
  let '(imps, _, cs) := u in cmds_no_axioms imps /\ cmds_no_axioms cs.

Lemma cmd_no_axioms_mod : forall x pv Δ cs, cmd_no_axioms (cc_mod x pv Δ cs) <-> cmds_no_axioms cs.
Proof.
  intros; cbn; unfold cmds_no_axioms; induction cs as [| c cs IH]; cbn;
    [ split; constructor | rewrite List.Forall_cons_iff, IH; reflexivity ].
Qed.

(** Expansion keeps a definition one, and a module's body as it is. *)
Lemma cmd_xp_no_axioms : forall mt S c c', cmd_xp mt S c = xok c' -> cmd_no_axioms c -> cmd_no_axioms c'.
Proof.
  intros * Ex Hc; pose proof (cmd_xp_head _ _ _ _ Ex) as Hh.
  destruct c as [x b pv A oM | x pv Δ cs | | | |];
    [| | destruct c'; cbn in Hh; try discriminate; exact I ..].
  - destruct (cmd_xp_def_inv _ _ _ _ _ _ _ _ Ex) as (A' & oM' & -> & Hiff); cbn in *; tauto.
  - destruct (cmd_xp_mod_inv _ _ _ _ _ _ _ Ex) as (Δ' & _ & ->); rewrite cmd_no_axioms_mod in *; exact Hc.
Qed.

Lemma in_gds_merge : forall Θ Θ' x,
    List.In x (gds_merge Θ Θ') -> List.In x Θ \/ List.In x Θ'.
Proof.
  unfold gds_merge; intros * [Hx | Hx]%List.in_app_or; [ right; exact (proj1 (proj1 (List.filter_In _ _ _) Hx)) | left; exact Hx ].
Qed.

Lemma gds_no_axioms_merge : forall Θ Θ',
    gds_no_axioms Θ -> gds_no_axioms Θ' -> gds_no_axioms (gds_merge Θ Θ').
Proof. intros * H H' fp U [Hin | Hin]%in_gds_merge; eauto. Qed.

Lemma gds_no_axioms_cons : forall fp U Θ,
    gm_no_axioms (gu_mod U) -> gds_no_axioms Θ -> gds_no_axioms ((fp, U) :: Θ).
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

#[local] Hint Resolve gs_no_axioms_head gs_no_axioms_tail gds_no_axioms_merge gds_no_axioms_cons gs_no_axioms_nil gds_no_axioms_nil
  gs_no_axioms_push gs_no_axioms_add : mctt.

Lemma gens_run_no_axioms : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> gs_no_axioms Ξ -> gs_no_axioms Ξ'.
Proof. induction 1; intros HΞ; auto; apply IHgens_run, gs_no_axioms_add; cbn; auto; congruence. Qed.

Section Run.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  (** Every unit the elaborator gives declares no axiom. *)
  Hypothesis Hload : forall prg u, to_core prg = Some u -> unit_no_axioms u.

  Theorem run_no_axioms :
    (forall ch Θ Ξ c Θ' Ξ', run_cmd load_path read to_core ch Θ Ξ c Θ' Ξ' ->
       cmd_no_axioms c -> gc_no_axioms Θ Ξ -> gc_no_axioms Θ' Ξ') /\
    (forall ch Θ Ξ cs Θ' Ξ', run_cmds load_path read to_core ch Θ Ξ cs Θ' Ξ' ->
       cmds_no_axioms cs -> gc_no_axioms Θ Ξ -> gc_no_axioms Θ' Ξ') /\
    (forall ch u Θ U, run_unit load_path read to_core ch u Θ U ->
       unit_no_axioms u -> gds_no_axioms Θ /\ gm_no_axioms (gu_mod U)).
  Proof.
    apply run_mut_ind; intros; unfold gc_no_axioms in *.
    (* a definition has a body *)
    - destruct_all; split; [ assumption | apply gs_no_axioms_add; cbn; auto; congruence ].
    (* an axiom is not among the commands *)
    - cbn in *; contradiction.
    (* a module's body is the frame its commands ended on *)
    - rewrite cmd_no_axioms_mod in *; destruct_all.
      match goal with IH : cmds_no_axioms _ -> _ |- _ =>
        destruct (IH ltac:(assumption) ltac:(split; auto with mctt)) as [HΘ HΞ] end.
      split; [ exact HΘ | apply gs_no_axioms_add; cbn; eauto with mctt ].
    - destruct_all; split; [ assumption | apply gs_no_axioms_add; cbn; auto ].
    - assumption.
    (* a load: the loaded unit is the elaborator's *)
    - destruct_all.
      match goal with IH : unit_no_axioms _ -> _ |- _ => destruct (IH ltac:(eapply Hload; eassumption)) end.
      split; eauto with mctt.
    (* an open declares what it generates *)
    - destruct_all; split; [ assumption | eapply gens_run_no_axioms; eassumption ].
    - assumption.
    - assumption.
    - assumption.
    (* a command runs as expanded, which keeps it free of axioms *)
    - match goal with
      | Hx : cmd_xp_ok _ _ _ _, Hc : cmds_no_axioms (_ :: _) |- _ =>
          destruct Hx as (mt & _ & Ex); inversion Hc; subst;
          pose proof (cmd_xp_no_axioms _ _ _ _ Ex ltac:(assumption))
      end; eauto.
    (* a unit: its loads from nothing, then its body in its own frame *)
    - cbn in *; destruct_all.
      match goal with IH1 : cmds_no_axioms ?is -> _ -> _ /\ gs_no_axioms nil, H1 : cmds_no_axioms ?is |- _ =>
        destruct (IH1 H1 ltac:(split; auto with mctt)) end.
      match goal with IH2 : cmds_no_axioms ?cs -> _ -> _ /\ gs_no_axioms (_ :: nil), H2 : cmds_no_axioms ?cs |- _ =>
        destruct (IH2 H2 ltac:(split; auto with mctt)) end.
      split; eauto with mctt.
  Qed.

  Corollary run_unit_no_axioms : forall ch u Θ U,
      run_unit load_path read to_core ch u Θ U -> unit_no_axioms u -> gds_no_axioms Θ /\ gm_no_axioms (gu_mod U).
  Proof. apply run_no_axioms. Qed.

  (** Every state a unit runs through, from nothing, has no axioms. *)
  Corollary run_cmds_no_axioms : forall ch cs Θ Ξ,
      run_cmds load_path read to_core ch nil nil cs Θ Ξ -> cmds_no_axioms cs -> gc_no_axioms Θ Ξ.
  Proof. intros * H Hc; eapply run_no_axioms; [ exact H | exact Hc | split; auto with mctt ]. Qed.

  (** What a program files, filed with it. *)
  Corollary prog_sem_no_axioms : forall prg Θ U,
      prog_sem load_path read to_core prg Θ U -> gc_no_axioms ((prog_path prg, U) :: Θ) nil.
  Proof.
    intros * (u & Ht & Hu); destruct (run_unit_no_axioms _ _ _ _ Hu (Hload _ _ Ht)).
    split; auto with mctt.
  Qed.
End Run.
