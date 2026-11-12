(** * The Set Interpretation under Weakening

    A term weakened by a renaming [φ] of the context, under the
    extension [Ψ] it is read in, has the value the term has, in an
    environment that reads each variable where the renaming sends it
    ([set_interp_wk]).  The typing premises of a λ and of an elimination
    move by the syntactic weakening lemma; an elimination's branches move
    under the binders their context adds, which the typing fixes
    ([elim_shape]). *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation Require Export Interp.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members CoreInversions.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Lemmas Scoping.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf MemberLemmas.
From Mctt.Core.Syntactic.System.Inductives Require Typing.
Require Import Mctt.Core.Syntactic.System.Inductives.Syntax.
Import ListNotations.

(** ** Environments Along a Renaming *)

(** [ρ] reads each variable where [ρ'] reads its image by [φ]. *)
Definition env_agrees (ρ ρ' : set_env) (φ : wk) : Prop := forall x, ρ x = ρ' (φ x).

Lemma env_agrees_extend : forall ρ ρ' φ e, env_agrees ρ ρ' φ -> env_agrees (set_env_extend ρ e) (set_env_extend ρ' e) (wk_q φ).
Proof. intros * H [| x]; cbn; [reflexivity | apply H]. Qed.

Lemma wk_qn_q : forall n φ, wk_qn n (wk_q φ) = wk_qn (S n) φ.
Proof. intros. rewrite <- Nat.add_1_r, wk_qn_plus. reflexivity. Qed.

Lemma env_agrees_extend_kinded : forall vs κs ρ ρ' φ, env_agrees ρ ρ' φ ->
    env_agrees (set_env_extend_kinded ρ κs vs) (set_env_extend_kinded ρ' κs vs) (wk_qn (List.length vs) φ).
Proof.
  induction vs as [| v vs IH]; intros κs ρ ρ' φ H; cbn [set_env_extend_kinded List.length]; [exact H |].
  rewrite <- wk_qn_q. apply IH. apply env_agrees_extend. exact H.
Qed.

Lemma centry_kind_wk : forall e φ, centry_kind (centry_wk e φ) = centry_kind e.
Proof. intros [] φ; reflexivity. Qed.

Lemma ctx_kinds_tele_wk : forall Δ φ, ctx_kinds (tele_wk Δ φ) = ctx_kinds Δ.
Proof.
  induction Δ as [| e Δ IH]; intros φ; [reflexivity |]. unfold ctx_kinds in *. cbn [tele_wk List.map List.rev].
  rewrite IH, centry_kind_wk. reflexivity.
Qed.

Section Weakening.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** A typing under an extension moves along a renaming of the context
    under it. *)
Lemma typing_wk : forall Ψ Γ Δ φ M A, gc_deps ⍮ gc_stack ⍮ Ψ ++ Γ ⊢ M : A -> gc_deps ⍮ gc_stack ⍮ Δ ⊢ʷ φ : Γ ->
    gc_deps ⍮ gc_stack ⍮ tele_wk Ψ φ ++ Δ ⊢ exp_wk M (wk_qn (List.length Ψ) φ) : exp_wk A (wk_qn (List.length Ψ) φ).
Proof.
  intros * HM Hφ. destruct (presup_exp HM) as [HΓ _].
  pose proof (wk_preserves_ext _ _ _ _ _ _ _ (ext_of_ctx _ _ _ _ HΓ) Hφ) as Hx.
  eapply wk_preserves_exp; [exact HM |]. apply wf_wk_ext; [exact Hφ | eapply ext_eq_ctx_left; exact Hx | exact HΓ].
Qed.

(** [elim_shape p Us Bks D]: what the typing of an elimination of the
    group [D] at [p], at the uniform parameters [Us] and the blocks [Bks],
    fixes of their shapes, whatever the context. *)
Record elim_shape (p : qname) (Us : list exp) (Bks : list eblock) (D : ind_decl) : Prop :=
  { (** The group *)
    elim_shape_lookup : ind_lookup gc_deps gc_stack p = Some D
    (** It is closed *)
  ; elim_shape_closed : decl_closed D
    (** One uniform parameter each *)
  ; elim_shape_uniform : List.length Us = ind_nu D
    (** Each motive binds its member's parameters and the scrutinee *)
  ; elim_shape_binders : blocks_binder_count_ok D Bks
    (** Each branch binds its constructor's parameters, arguments and
        recursive results *)
  ; elim_shape_counts : forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
      ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat }.

Lemma elim_shape_of_typing : forall Γ r p Us m Bks M C, gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_elim r p Us m Bks M : C ->
    exists D, elim_shape p Us Bks D.
Proof.
  intros * H. pose proof H as H'. apply wf_elim_inversion in H as [D Mm bm Ps i Hl Hm Hb HPl _ _ HUs HBt _].
  exists D. destruct (presup_exp H') as [HΓ _]. constructor.
  - exact Hl.
  - eapply gctx_closed_ind; [eapply wf_gctx_closed; exact HΓ | exact Hl].
  - subst Us. rewrite List.firstn_length_le; [reflexivity |]. rewrite HPl. unfold im_np. lia.
  - exact (Typing.blocks_typed_binder_count _ _ _ _ _ _ _ _ _ HBt).
  - exact (Typing.blocks_typed_counts _ _ _ _ _ _ _ _ _ HBt).
Qed.

End Weakening.
