(** * Instances of the Fundamental Theorem

    The fundamental theorem glues a typed term at each of its instances
    ([glu_rel_exp_under_sub]): at the substitutions whose term components
    are glued at every renaming ([glu_rel_sub_inst]).  This file builds the
    instances the rules need: weakened ones, lifted ones under a binder of
    each entry kind, extended ones by a glued term, and the renamings and
    the identity out of a context glued with its variables' types
    ([glu_rel_ctx_types]), which the context rules build.  A variable is
    glued at its type at every renaming once its type is
    ([glu_rel_exp_under_renaming_var]), so a component is never moved along
    a substitution: each instance of a term is glued at its own value. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Soundness Require Import LogicalRelation VariableCases ContextCases.
Import Domain_Notations Wk_Notations Fixed_Notations.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Renamings *)

(** A term glued at every renaming is glued at every renaming of a
    renaming of it. *)
Lemma glu_rel_exp_under_renaming_wk : forall {Γ Γ' M A ψ},
    glu_rel_exp_under_renaming Γ M A ->
    Γ' ⊢ʷ ψ : Γ ->
    glu_rel_exp_under_renaming Γ' M[ψ]ʷ A[ψ]ʷ.
Proof.
  intros * HM Hψ Γ'' φ Hφ HΓ''.
  rewrite !exp_wk_wk; apply HM; [ eapply wf_wk_compose; eassumption | exact HΓ'' ].
Qed.

(** The same past one more entry. *)
Lemma glu_rel_exp_under_renaming_shift : forall {e Γ M A},
    ⊢ (e :: Γ)%list ->
    glu_rel_exp_under_renaming Γ M A ->
    glu_rel_exp_under_renaming (e :: Γ)%list M[↑]ʷ A[↑]ʷ.
Proof.
  intros * He HM; eapply glu_rel_exp_under_renaming_wk; [ exact HM | apply wf_wk_shift; exact He ].
Qed.

(** A term glued at every renaming is glued, at the identity. *)
Lemma glu_rel_exp_of_under_renaming : forall {Γ M A},
    ⊩ Γ ->
    glu_rel_exp_under_renaming Γ M A ->
    Γ ⊩ M : A.
Proof.
  intros * HΓ HM.
  pose proof (HM Γ wk_id) as H; rewrite !exp_wk_id in H; apply H; [| exact HΓ ].
  apply wf_wk_id; destruct HΓ as [Sb HSb]; eapply glu_ctx_env_wf_ctx; exact HSb.
Qed.

(** A variable is glued at its type at every renaming, when its type is
    glued at every renaming as a term of a sort of types: a renamed
    variable is a variable of the renamed type ([wf_wk_lookup]). *)
Lemma glu_rel_exp_under_renaming_var : forall {Γ x A S},
    Γ ∋ #x : A ->
    type_sort S ->
    glu_rel_exp_under_renaming Γ A S ->
    glu_rel_exp_under_renaming Γ #x A.
Proof.
  intros * Hx HS HA Γ' φ Hφ HΓ'.
  change (#x[φ]ʷ) with (#(φ x)).
  eapply glu_rel_exp_var_witness; [ exact HΓ' | eapply wf_wk_lookup; eassumption | exact HS |].
  rewrite <- (type_sort_wk S φ HS); apply HA; assumption.
Qed.

(** A unit glued at every renaming is glued at every renaming of a
    renaming of it. *)
Lemma glu_unit_under_renaming_wk : forall {Γ Γ' U ψ},
    glu_unit_under_renaming Γ U ->
    Γ' ⊢ʷ ψ : Γ ->
    glu_unit_under_renaming Γ' (gunit_wk U ψ).
Proof.
  intros * HU Hψ Γ'' φ Hφ HΓ''.
  rewrite gunit_wk_wk; apply HU; [ eapply wf_wk_compose; eassumption | exact HΓ'' ].
Qed.

(** The same past one more entry. *)
Lemma glu_unit_under_renaming_shift : forall {e Γ U},
    ⊢ (e :: Γ)%list ->
    glu_unit_under_renaming Γ U ->
    glu_unit_under_renaming (e :: Γ)%list (gunit_wk U ↑).
Proof.
  intros * He HU; eapply glu_unit_under_renaming_wk; [ exact HU | apply wf_wk_shift; exact He ].
Qed.

(** ** Weakened Instances *)

(** An instance postcomposed with a renaming into a glued context is an
    instance: each component, renamed, is glued at every renaming. *)
Lemma glu_rel_sub_inst_wk : forall {Γ Γ' Δ τ ψ},
    glu_rel_sub_inst Γ τ Δ ->
    Γ' ⊢ʷ ψ : Γ ->
    ⊩ Γ' ->
    glu_rel_sub_inst Γ' (sb_wk τ ψ) Δ.
Proof.
  intros * [Hτ HΓ Hc Hm] Hψ HΓ'.
  econstructor; [ eapply wf_sub_wk; eassumption | exact HΓ' | |].
  - intros x A Hx; rewrite <- !exp_wk_sub.
    eapply glu_rel_exp_under_renaming_wk; [ apply Hc; exact Hx | exact Hψ ].
  - intros x U Hx; rewrite <- gunit_wk_sub.
    eapply glu_unit_under_renaming_wk; [ exact (Hm _ _ Hx) | exact Hψ ].
Qed.

(** A unit glued at its instances is glued at every renaming of each. *)
Lemma glu_rel_unit_under_sub_inst_renaming : forall {Γ Δ τ U},
    glu_rel_unit_under_sub Δ U ->
    glu_rel_sub_inst Γ τ Δ ->
    glu_unit_under_renaming Γ U[τ]ᵘ.
Proof.
  intros * HU Hτ Γ' φ Hφ HΓ'.
  rewrite gunit_wk_sub; apply HU; eapply glu_rel_sub_inst_wk; eassumption.
Qed.

(** A term glued at its instances is glued at every renaming of each. *)
Lemma glu_rel_exp_under_sub_inst_renaming : forall {Γ Δ τ M A},
    glu_rel_exp_under_sub Δ M A ->
    glu_rel_sub_inst Γ τ Δ ->
    glu_rel_exp_under_renaming Γ M[τ] A[τ].
Proof.
  intros * HM Hτ Γ' φ Hφ HΓ'.
  rewrite !exp_wk_sub; apply HM; eapply glu_rel_sub_inst_wk; eassumption.
Qed.

(** ** Renamings and the Identity as Instances *)

(** A renaming of a context glued with its variables' types into a glued
    context is an instance: its components are variables. *)
Lemma glu_rel_ctx_types_renaming : forall {Γ Γ' φ},
    glu_rel_ctx_types Γ ->
    Γ' ⊢ʷ φ : Γ ->
    ⊩ Γ' ->
    glu_rel_sub_inst Γ' (ι φ) Γ.
Proof.
  intros * [HΓ Ht Hs] Hφ HΓ'.
  econstructor; [ apply wf_sub_of_wk; exact Hφ | exact HΓ' | |].
  - intros x A Hx; rewrite !exp_sub_of_wk.
    destruct (Ht _ _ Hx) as (S & HS & HA).
    change (#x[φ]ʷ) with (#(φ x)).
    eapply glu_rel_exp_under_renaming_var; [ eapply wf_wk_lookup; eassumption | exact HS |].
    rewrite <- (type_sort_wk S φ HS); eapply glu_rel_exp_under_renaming_wk; eassumption.
  - intros x U Hx; rewrite gunit_sub_of_wk.
    eapply glu_unit_under_renaming_wk; [ exact (Hs _ _ Hx) | exact Hφ ].
Qed.

(** The identity is an instance. *)
Lemma glu_rel_ctx_types_id : forall {Γ},
    glu_rel_ctx_types Γ ->
    glu_rel_sub_inst Γ Id Γ.
Proof.
  intros * HΓ.
  assert (H : glu_rel_sub_inst Γ (ι wk_id) Γ).
  { apply glu_rel_ctx_types_renaming; [ exact HΓ | | apply HΓ ].
    apply wf_wk_id; destruct (glu_rel_ctx_types_ctx _ HΓ) as [Sb HSb]; eapply glu_ctx_env_wf_ctx; exact HSb. }
  destruct H as [_ HΓ' Hc Hm].
  econstructor; [ apply wf_sub_id; destruct HΓ' as [Sb HSb]; eapply glu_ctx_env_wf_ctx; exact HSb | exact HΓ' | |].
  - intros x A Hx; specialize (Hc _ _ Hx); rewrite !exp_sub_of_wk, !exp_wk_id in Hc; rewrite !exp_sub_id; exact Hc.
  - intros x U Hx; specialize (Hm _ _ Hx); rewrite gunit_sub_of_wk, gunit_wk_id in Hm; rewrite gunit_sub_id; exact Hm.
Qed.

(** A term glued at its instances is glued. *)
Lemma glu_rel_exp_of_under_sub : forall {Γ M A},
    glu_rel_exp_under_sub Γ M A ->
    Γ ⊩ M : A.
Proof.
  intros * HM.
  pose proof (glu_rel_exp_under_sub_inst _ _ _ HM _ _ (glu_rel_ctx_types_id (glu_rel_exp_under_sub_ctx _ _ _ HM))) as H.
  rewrite !exp_sub_id in H; exact H.
Qed.

(** A term glued at its instances is glued at every renaming. *)
Lemma glu_rel_exp_under_sub_renaming : forall {Γ M A},
    glu_rel_exp_under_sub Γ M A ->
    glu_rel_exp_under_renaming Γ M A.
Proof.
  intros * HM Γ' φ Hφ HΓ'.
  rewrite <- !exp_sub_of_wk; apply HM.
  apply glu_rel_ctx_types_renaming; [ apply HM | exact Hφ | exact HΓ' ].
Qed.

(** An instance precomposed with a renaming is an instance: its
    components are the instance's at the renamed variables and slots. *)
Lemma glu_rel_sub_inst_of_wk_comp : forall {Γ Σ Σ' τ φ},
    glu_rel_sub_inst Γ τ Σ' ->
    Σ' ⊢ʷ φ : Σ ->
    glu_rel_sub_inst Γ ((ι φ) ⨟ τ) Σ.
Proof.
  intros * [Hτ HΓ Hc Hm] Hφ.
  econstructor; [ eapply wf_sub_compose; [ apply wf_sub_of_wk; exact Hφ | exact Hτ ] | exact HΓ | |].
  - intros x A Hx.
    replace (A[(ι φ) ⨟ τ]) with (A[φ]ʷ[τ]) by (rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
    change (#x[(ι φ) ⨟ τ]) with (#(φ x)[τ]).
    apply Hc; eapply wf_wk_lookup; eassumption.
  - intros x U Hx.
    replace (U[(ι φ) ⨟ τ]ᵘ) with ((gunit_wk U φ)[τ]ᵘ) by (rewrite <- gunit_sub_of_wk, gunit_sub_sub; reflexivity).
    eapply Hm; eapply wf_wk_lookup_mod; eassumption.
Qed.

(** A term glued at its instances is glued at the instances of each of its
    renamings into a context glued with its types. *)
Lemma glu_rel_exp_under_sub_wk : forall {Σ Σ' M A φ},
    glu_rel_exp_under_sub Σ M A ->
    glu_rel_ctx_types Σ' ->
    Σ' ⊢ʷ φ : Σ ->
    glu_rel_exp_under_sub Σ' M[φ]ʷ A[φ]ʷ.
Proof.
  intros * HM HΣ' Hφ.
  econstructor; [ exact HΣ' |].
  intros Γ τ Hτ.
  rewrite <- !exp_sub_of_wk, !exp_sub_sub.
  apply HM; eapply glu_rel_sub_inst_of_wk_comp; eassumption.
Qed.

(** The same for a unit. *)
Lemma glu_rel_unit_under_sub_wk : forall {Σ Σ' U φ},
    glu_rel_unit_under_sub Σ U ->
    Σ' ⊢ʷ φ : Σ ->
    glu_rel_unit_under_sub Σ' (gunit_wk U φ).
Proof.
  intros * HU Hφ Γ τ Hτ.
  rewrite <- gunit_sub_of_wk, gunit_sub_sub.
  apply HU; eapply glu_rel_sub_inst_of_wk_comp; eassumption.
Qed.

(** A type of a sort of types glued at its instances is glued at each,
    at the sort. *)
Lemma glu_rel_exp_under_sub_inst_sort : forall {Γ Δ τ A S},
    glu_rel_exp_under_sub Δ A S ->
    type_sort S ->
    glu_rel_sub_inst Γ τ Δ ->
    Γ ⊩ A[τ] : S.
Proof.
  intros * HA HS Hτ.
  pose proof (glu_rel_exp_under_sub_inst _ _ _ HA _ _ Hτ) as H; rewrite (type_sort_sub S τ HS) in H; exact H.
Qed.

(** The same at a type equal to the instance's, as a closed type is. *)
Lemma glu_rel_exp_under_sub_inst_conv : forall {Γ Δ τ M A A'},
    glu_rel_exp_under_sub Δ M A ->
    glu_rel_sub_inst Γ τ Δ ->
    A[τ] = A' ->
    Γ ⊩ M[τ] : A'.
Proof. intros * HM Hτ <-; exact (glu_rel_exp_under_sub_inst _ _ _ HM _ _ Hτ). Qed.

(** A term glued at its instances at one type is glued at them at
    another, when each instance moves. *)
Lemma glu_rel_exp_under_sub_conv_typ : forall {Δ M A A'},
    (forall Γ τ, glu_rel_sub_inst Γ τ Δ -> Γ ⊩ M[τ] : A[τ] -> Γ ⊩ M[τ] : A'[τ]) ->
    glu_rel_exp_under_sub Δ M A ->
    glu_rel_exp_under_sub Δ M A'.
Proof.
  intros * Hmove [HΔ HM]; econstructor; [ exact HΔ |].
  intros Γ τ Hτ; apply Hmove; [ exact Hτ | apply HM; exact Hτ ].
Qed.

(** A term glued at its instances is typed. *)
Lemma glu_rel_exp_under_sub_wf : forall {Γ M A},
    glu_rel_exp_under_sub Γ M A ->
    Γ ⊢ M : A.
Proof. intros * HM; exact (glu_rel_exp_to_wf_exp (glu_rel_exp_of_under_sub HM)). Qed.

(** ** Contexts Glued with their Variables' Types *)

(** A unit glued at its instances is glued at every renaming of a context
    glued with its types. *)
Lemma glu_rel_unit_under_sub_renaming : forall {Γ U},
    glu_rel_ctx_types Γ ->
    glu_rel_unit_under_sub Γ U ->
    glu_unit_under_renaming Γ U.
Proof.
  intros * HΓ HU Γ' φ Hφ HΓ'.
  rewrite <- gunit_sub_of_wk; apply HU.
  apply glu_rel_ctx_types_renaming; [ exact HΓ | exact Hφ | exact HΓ' ].
Qed.

(** One more entry: the types of the variables and the units of the slots
    under it are weakened past it, and the head's are given. *)
Lemma glu_rel_ctx_types_cons : forall {e Γ},
    glu_rel_ctx_types Γ ->
    ⊩ (e :: Γ)%list ->
    (forall A, (e :: Γ)%list ∋ #0 : A -> exists S, type_sort S /\ glu_rel_exp_under_renaming (e :: Γ)%list A S) ->
    (forall U, (e :: Γ)%list ∋ #0 ≔ₘ U -> glu_unit_under_renaming (e :: Γ)%list U) ->
    glu_rel_ctx_types (e :: Γ)%list.
Proof.
  intros * [HΓ Ht Hs] HeΓ Hhead Hheadm.
  assert (He : ⊢ (e :: Γ)%list) by (destruct HeΓ as [Sb HSb]; eapply glu_ctx_env_wf_ctx; exact HSb).
  econstructor; [ exact HeΓ | |].
  - intros [| n] A Hx; [ exact (Hhead _ Hx) |].
    inversion Hx; subst.
    destruct (Ht _ _ ltac:(eassumption)) as (S & HS & HA).
    exists S; split; [ exact HS |].
    rewrite <- (type_sort_wk S ↑ HS); apply glu_rel_exp_under_renaming_shift; assumption.
  - intros [| n] U Hx; [ exact (Hheadm _ Hx) |].
    inversion Hx; subst.
    apply glu_unit_under_renaming_shift; [ exact He | eapply Hs; eassumption ].
Qed.

(** The head of an entry whose type is glued at its instances: its type,
    weakened past it, is glued at every renaming. *)
Lemma glu_rel_ctx_types_head : forall {e Γ A S},
    ⊢ (e :: Γ)%list ->
    type_sort S ->
    glu_rel_exp_under_sub Γ A S ->
    exists S', type_sort S' /\ glu_rel_exp_under_renaming (e :: Γ)%list A[↑]ʷ S'.
Proof.
  intros * He HS HA.
  exists S; split; [ exact HS |].
  rewrite <- (type_sort_wk S ↑ HS); apply glu_rel_exp_under_renaming_shift; [ exact He |].
  apply glu_rel_exp_under_sub_renaming; exact HA.
Qed.

(** As [wf_ctx_empty]. *)
Lemma glu_rel_ctx_types_empty : ⊢ᵍ gc_deps ⍮ gc_stack -> glu_rel_ctx_types ⋅.
Proof.
  intros Hg; econstructor; [ apply glu_rel_ctx_empty; exact Hg | intros x A Hx; inversion Hx | intros x U Hx; inversion Hx ].
Qed.

(** An assumption of a type of a sort of its kind. *)
Lemma glu_rel_ctx_types_extend : forall {Γ A S κ},
    glu_rel_exp_under_sub Γ A S ->
    sort_kind S κ ->
    glu_rel_ctx_types (Γ ▹{κ} A).
Proof.
  intros * HA HS.
  pose proof (glu_rel_exp_of_under_sub HA) as HAg.
  assert (HeΓ : ⊩ Γ ▹{κ} A) by (eapply glu_rel_ctx_extend; [ eapply presup_ctx_glu_rel_exp | |]; eassumption).
  apply glu_rel_ctx_types_cons; [ apply HA | exact HeΓ | | intros U Hx; inversion Hx ].
  intros A' Hx; inversion Hx; subst.
  eapply glu_rel_ctx_types_head; [ destruct HeΓ as [Sb HSb]; eapply glu_ctx_env_wf_ctx; exact HSb
                                 | eapply sort_kind_type_sort; exact HS | exact HA ].
Qed.

(** A definition, of a type of a sort. *)
Lemma glu_rel_ctx_types_extend_def : forall {Γ A S M},
    glu_rel_exp_under_sub Γ A S ->
    type_sort S ->
    glu_rel_exp_under_sub Γ M A ->
    glu_rel_ctx_types (Γ ▸ A ≔ M).
Proof.
  intros * HA HS HM.
  pose proof (glu_rel_exp_of_under_sub HA) as HAg.
  assert (HeΓ : ⊩ Γ ▸ A ≔ M)
    by (eapply glu_rel_ctx_extend_def; [ eapply presup_ctx_glu_rel_exp; exact HAg | exact HAg | exact HS | exact (glu_rel_exp_of_under_sub HM) ]).
  apply glu_rel_ctx_types_cons; [ apply HA | exact HeΓ | | intros U Hx; inversion Hx ].
  intros A' Hx; inversion Hx; subst.
  eapply glu_rel_ctx_types_head; [ destruct HeΓ as [Sb HSb]; eapply glu_ctx_env_wf_ctx; exact HSb | exact HS | exact HA ].
Qed.

(** A module slot of a well-formed unit glued at its instances: no
    variable of a type, and the slot's unit. *)
Lemma glu_rel_ctx_types_extend_mod : forall {Γ U},
    glu_rel_ctx_types Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U ->
    glu_rel_unit_under_sub Γ U ->
    glu_rel_ctx_types (Γ ▹ₘ U).
Proof.
  intros * HΓ HU HUg.
  assert (HeΓ : ⊩ Γ ▹ₘ U) by (apply glu_rel_ctx_extend_mod; [ apply HΓ | exact HU ]).
  assert (He : ⊢ Γ ▹ₘ U) by (destruct HeΓ as [Sb HSb]; eapply glu_ctx_env_wf_ctx; exact HSb).
  apply glu_rel_ctx_types_cons; [ exact HΓ | exact HeΓ | intros A' Hx; inversion Hx |].
  intros U' Hx; inversion Hx; subst.
  apply glu_unit_under_renaming_shift; [ exact He | exact (glu_rel_unit_under_sub_renaming HΓ HUg) ].
Qed.

(** A definition with a module part, its unit glued at its instances. *)
Lemma glu_rel_ctx_types_extend_dm : forall {Γ A M E} {i : nat},
    glu_rel_exp_under_sub Γ A Typeω@i ->
    glu_rel_exp_under_sub Γ M A ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
    glu_rel_unit_under_sub Γ (gu_mk nil (md_alias E)) ->
    glu_rel_ctx_types (Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E)).
Proof.
  intros * HA HM HU HUg.
  pose proof (glu_rel_exp_of_under_sub HA) as HAg.
  assert (HeΓ : ⊩ Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E))
    by (eapply glu_rel_ctx_extend_dm; [ eapply presup_ctx_glu_rel_exp; exact HAg | exact HAg | exact (glu_rel_exp_of_under_sub HM) | exact HU ]).
  assert (He : ⊢ Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E)) by (destruct HeΓ as [Sb HSb]; eapply glu_ctx_env_wf_ctx; exact HSb).
  apply glu_rel_ctx_types_cons; [ apply HA | exact HeΓ | |].
  - intros A' Hx; inversion Hx; subst.
    eapply glu_rel_ctx_types_head; [ exact He | constructor | exact HA ].
  - intros U' Hx; inversion Hx; subst.
    apply glu_unit_under_renaming_shift; [ exact He | exact (glu_rel_unit_under_sub_renaming (glu_rel_exp_under_sub_ctx _ _ _ HA) HUg) ].
Qed.

(** ** Lifted Instances *)

(** An instance lifted over an entry, into a glued context: the head is a
    variable, glued when its type is, and the other components are the
    instance's, weakened past the entry. *)
Lemma glu_rel_sub_inst_q_gen : forall {Γ Δ τ e},
    glu_rel_sub_inst Γ τ Δ ->
    ⊩ (centry_sub e τ :: Γ)%list ->
    (centry_sub e τ :: Γ)%list ⊢ˢ q τ : (e :: Δ)%list ->
    (forall A, (e :: Δ)%list ∋ #0 : A ->
          (centry_sub e τ :: Γ)%list ∋ #0 : A[q τ] /\
          exists S, type_sort S /\ glu_rel_exp_under_renaming (centry_sub e τ :: Γ)%list A[q τ] S) ->
    (forall U, (e :: Δ)%list ∋ #0 ≔ₘ U -> glu_unit_under_renaming (centry_sub e τ :: Γ)%list U[q τ]ᵘ) ->
    glu_rel_sub_inst (centry_sub e τ :: Γ)%list (q τ) (e :: Δ)%list.
Proof.
  intros * [Hτ HΓ Hc Hm] HeΓ Hq Hhead Hheadm.
  assert (He : ⊢ (centry_sub e τ :: Γ)%list) by (destruct HeΓ as [Sb HSb]; eapply glu_ctx_env_wf_ctx; exact HSb).
  econstructor; [ exact Hq | exact HeΓ | |].
  - intros [| n] A Hx.
    + destruct (Hhead _ Hx) as (Hx' & S & HS & HA).
      change (#0[q τ]) with (#0).
      eapply glu_rel_exp_under_renaming_var; eassumption.
    + inversion Hx; subst.
      change (#(S n)[q τ]) with (sentry_exp (sentry_wk (τ n) ↑)).
      rewrite <- sentry_exp_wk, exp_wk_shift_sub_q.
      apply glu_rel_exp_under_renaming_shift; [ exact He | apply Hc; eassumption ].
  - intros [| n] U Hx; [ exact (Hheadm _ Hx) |].
    inversion Hx; subst.
    rewrite gunit_wk_shift_sub_q.
    apply glu_unit_under_renaming_shift; [ exact He | eapply Hm; eassumption ].
Qed.

(** The slot of an entry lifted over an instance, its unit glued at the
    instances: the slot's unit, weakened past it. *)
Lemma glu_rel_sub_inst_q_head_mod : forall {Γ Δ τ e U},
    glu_rel_sub_inst Γ τ Δ ->
    ⊢ (centry_sub e τ :: Γ)%list ->
    glu_rel_unit_under_sub Δ U ->
    glu_unit_under_renaming (centry_sub e τ :: Γ)%list (gunit_wk U ↑)[q τ]ᵘ.
Proof.
  intros * Hτ He HU.
  rewrite gunit_wk_shift_sub_q; apply glu_unit_under_renaming_shift; [ exact He |].
  eapply glu_rel_unit_under_sub_inst_renaming; eassumption.
Qed.

(** The head of an entry lifted over an instance, its type glued at the
    instances: the variable is a variable of the substituted type. *)
Lemma glu_rel_sub_inst_q_head : forall {Γ Δ τ e A S},
    glu_rel_sub_inst Γ τ Δ ->
    ⊢ (centry_sub e τ :: Γ)%list ->
    (centry_sub e τ :: Γ)%list ∋ #0 : A[τ][↑]ʷ ->
    type_sort S ->
    glu_rel_exp_under_sub Δ A S ->
    (centry_sub e τ :: Γ)%list ∋ #0 : A[↑]ʷ[q τ] /\
      exists S', type_sort S' /\ glu_rel_exp_under_renaming (centry_sub e τ :: Γ)%list A[↑]ʷ[q τ] S'.
Proof.
  intros * Hτ He Hx HS HA.
  rewrite exp_wk_shift_sub_q; split; [ exact Hx |].
  exists S; split; [ exact HS |].
  rewrite <- (type_sort_wk S ↑ HS); apply glu_rel_exp_under_renaming_shift; [ exact He |].
  rewrite <- (type_sort_sub S τ HS); eapply glu_rel_exp_under_sub_inst_renaming; eassumption.
Qed.

(** An instance lifted over an assumption of a type glued at its
    instances. *)
Lemma glu_rel_sub_inst_q : forall {Γ Δ τ A S κ},
    glu_rel_sub_inst Γ τ Δ ->
    glu_rel_exp_under_sub Δ A S ->
    sort_kind S κ ->
    glu_rel_sub_inst (Γ ▹{κ} A[τ]) (q τ) (Δ ▹{κ} A).
Proof.
  intros * Hτ HA HS.
  pose proof (sort_kind_type_sort _ _ HS) as HSt.
  assert (HAτ : Γ ⊩ A[τ] : S)
    by (pose proof (glu_rel_exp_under_sub_inst _ _ _ HA _ _ Hτ) as H; rewrite (type_sort_sub S τ HSt) in H; exact H).
  assert (HeΓ : ⊩ Γ ▹{κ} A[τ]) by (eapply glu_rel_ctx_extend; [ apply Hτ | exact HAτ | exact HS ]).
  assert (He : ⊢ Γ ▹{κ} A[τ]) by (destruct HeΓ as [Sb HSb]; eapply glu_ctx_env_wf_ctx; exact HSb).
  apply (glu_rel_sub_inst_q_gen (e := ce_ass κ A)); [ exact Hτ | exact HeΓ | | | intros U Hx; inversion Hx ].
  - eapply wf_sub_q; [ apply Hτ | exact (glu_rel_exp_under_sub_wf HA) | exact HS | exact (glu_rel_exp_to_wf_exp HAτ) ].
  - intros A' Hx; inversion Hx; subst.
    eapply glu_rel_sub_inst_q_head; [ exact Hτ | exact He | constructor | exact HSt | exact HA ].
Qed.

(** An instance lifted over a definition of a type glued at its
    instances. *)
Lemma glu_rel_sub_inst_q_def : forall {Γ Δ τ A M S},
    glu_rel_sub_inst Γ τ Δ ->
    glu_rel_exp_under_sub Δ A S ->
    type_sort S ->
    glu_rel_exp_under_sub Δ M A ->
    glu_rel_sub_inst (Γ ▸ A[τ] ≔ M[τ]) (q τ) (Δ ▸ A ≔ M).
Proof.
  intros * Hτ HA HS HM.
  assert (HAτ : Γ ⊩ A[τ] : S)
    by (pose proof (glu_rel_exp_under_sub_inst _ _ _ HA _ _ Hτ) as H; rewrite (type_sort_sub S τ HS) in H; exact H).
  assert (HMτ : Γ ⊩ M[τ] : A[τ]) by (apply HM; exact Hτ).
  assert (HeΓ : ⊩ Γ ▸ A[τ] ≔ M[τ]) by (eapply glu_rel_ctx_extend_def; [ apply Hτ | exact HAτ | exact HS | exact HMτ ]).
  assert (He : ⊢ Γ ▸ A[τ] ≔ M[τ]) by (destruct HeΓ as [Sb HSb]; eapply glu_ctx_env_wf_ctx; exact HSb).
  apply (glu_rel_sub_inst_q_gen (e := ce_def A M)); [ exact Hτ | exact HeΓ | | | intros U Hx; inversion Hx ].
  - eapply wf_sub_q_def; [ apply Hτ | exact (glu_rel_exp_under_sub_wf HA) | exact HS | exact (glu_rel_exp_under_sub_wf HM)
                         | exact (glu_rel_exp_to_wf_exp HAτ) | exact (glu_rel_exp_to_wf_exp HMτ) ].
  - intros A' Hx; inversion Hx; subst.
    eapply glu_rel_sub_inst_q_head; [ exact Hτ | exact He | constructor | exact HS | exact HA ].
Qed.

(** An instance lifted over a module slot whose unit is well formed at
    the instance and glued at the instances. *)
Lemma glu_rel_sub_inst_q_mod : forall {Γ Δ τ U},
    glu_rel_sub_inst Γ τ Δ ->
    gc_deps ⍮ gc_stack ⍮ Δ ⊢ᵘ U ≈ U ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U[τ]ᵘ ≈ U[τ]ᵘ ->
    glu_rel_unit_under_sub Δ U ->
    glu_rel_sub_inst (Γ ▹ₘ U[τ]ᵘ) (q τ) (Δ ▹ₘ U).
Proof.
  intros * Hτ HU HUτ HUg.
  assert (HeΓ : ⊩ Γ ▹ₘ U[τ]ᵘ) by (apply glu_rel_ctx_extend_mod; [ apply Hτ | exact HUτ ]).
  assert (He : ⊢ Γ ▹ₘ U[τ]ᵘ) by (destruct HeΓ as [Sb HSb]; eapply glu_ctx_env_wf_ctx; exact HSb).
  apply (glu_rel_sub_inst_q_gen (e := ce_mod U)); [ exact Hτ | exact HeΓ | | intros A' Hx; inversion Hx |].
  - eapply wf_sub_q_mod; [ apply Hτ | exact HU | exact HUτ ].
  - intros U' Hx; inversion Hx; subst.
    exact (glu_rel_sub_inst_q_head_mod (e := ce_mod U) Hτ He HUg).
Qed.

(** An instance lifted over a definition with a module part. *)
Lemma glu_rel_sub_inst_q_dm : forall {Γ Δ τ A M E} {i : nat},
    glu_rel_sub_inst Γ τ Δ ->
    glu_rel_exp_under_sub Δ A Typeω@i ->
    glu_rel_exp_under_sub Δ M A ->
    gc_deps ⍮ gc_stack ⍮ Δ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E[τ]ᵐ) ≈ gu_mk nil (md_alias E[τ]ᵐ) ->
    glu_rel_unit_under_sub Δ (gu_mk nil (md_alias E)) ->
    glu_rel_sub_inst (Γ ▸ₘ A[τ] ≔ M[τ] ‖ gu_mk nil (md_alias E[τ]ᵐ)) (q τ) (Δ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E)).
Proof.
  intros * Hτ HA HM HU HUτ HUg.
  assert (HAτ : Γ ⊩ A[τ] : Typeω@i) by (apply HA; exact Hτ).
  assert (HMτ : Γ ⊩ M[τ] : A[τ]) by (apply HM; exact Hτ).
  assert (HeΓ : ⊩ Γ ▸ₘ A[τ] ≔ M[τ] ‖ gu_mk nil (md_alias E[τ]ᵐ))
    by (eapply glu_rel_ctx_extend_dm; [ apply Hτ | exact HAτ | exact HMτ | exact HUτ ]).
  assert (He : ⊢ Γ ▸ₘ A[τ] ≔ M[τ] ‖ gu_mk nil (md_alias E[τ]ᵐ)) by (destruct HeΓ as [Sb HSb]; eapply glu_ctx_env_wf_ctx; exact HSb).
  apply (glu_rel_sub_inst_q_gen (e := ce_dm A M (gu_mk nil (md_alias E)))); [ exact Hτ | exact HeΓ | | |].
  - eapply wf_sub_q_dm; [ apply Hτ | exact (glu_rel_exp_under_sub_wf HA) | exact (glu_rel_exp_under_sub_wf HM) | exact HU
                        | exact (glu_rel_exp_to_wf_exp HAτ) | exact (glu_rel_exp_to_wf_exp HMτ) | exact HUτ ].
  - intros A' Hx; inversion Hx; subst.
    eapply glu_rel_sub_inst_q_head; [ exact Hτ | exact He | constructor | constructor | exact HA ].
  - intros U' Hx; inversion Hx; subst.
    exact (glu_rel_sub_inst_q_head_mod (e := ce_dm A M (gu_mk nil (md_alias E))) Hτ He HUg).
Qed.

(** ** Extended Instances *)

(** An instance extended by an entry: the head is the entry's term part,
    glued at every renaming at its type, and the other components are the
    instance's. *)
Lemma glu_rel_sub_inst_extend_gen : forall {Γ Δ τ e en},
    glu_rel_sub_inst Γ τ Δ ->
    Γ ⊢ˢ sb_extend τ en : (e :: Δ)%list ->
    (forall A, (e :: Δ)%list ∋ #0 : A -> glu_rel_exp_under_renaming Γ (sentry_exp en) A[sb_extend τ en]) ->
    (forall U, (e :: Δ)%list ∋ #0 ≔ₘ U -> glu_unit_under_renaming Γ U[sb_extend τ en]ᵘ) ->
    glu_rel_sub_inst Γ (sb_extend τ en) (e :: Δ)%list.
Proof.
  intros * [Hτ HΓ Hc Hm] Hτe Hhead Hheadm.
  econstructor; [ exact Hτe | exact HΓ | |].
  - intros [| n] A Hx; [ exact (Hhead _ Hx) |].
    inversion Hx; subst.
    change (#(S n)[sb_extend τ en]) with (#n[τ]).
    rewrite exp_sub_shift_extend; apply Hc; eassumption.
  - intros [| n] U Hx; [ exact (Hheadm _ Hx) |].
    inversion Hx; subst.
    rewrite gunit_sub_shift_extend; eapply Hm; eassumption.
Qed.

(** An instance extended by a term glued at its type at every renaming,
    for an assumption. *)
Lemma glu_rel_sub_inst_extend : forall {Γ Δ τ A S κ N},
    glu_rel_sub_inst Γ τ Δ ->
    Δ ⊢ A : S ->
    sort_kind S κ ->
    glu_rel_exp_under_renaming Γ N A[τ] ->
    glu_rel_sub_inst Γ (τ,,N) (Δ ▹{κ} A).
Proof.
  intros * Hτ HA HS HN.
  apply (glu_rel_sub_inst_extend_gen (e := ce_ass κ A)); [ exact Hτ | | | intros U Hx; inversion Hx ].
  - eapply wf_sub_extend; [ apply Hτ | exact HA | exact HS |].
    apply glu_rel_exp_to_wf_exp, glu_rel_exp_of_under_renaming; [ apply Hτ | exact HN ].
  - intros A' Hx; inversion Hx; subst.
    rewrite exp_sub_shift_extend; exact HN.
Qed.

(** An instance extended by the instance of a definition's body, for the
    definition: the body glued at its instances is glued at every renaming
    of this one. *)
Lemma glu_rel_sub_inst_extend_def : forall {Γ Δ τ A S M},
    glu_rel_sub_inst Γ τ Δ ->
    Δ ⊢ A : S ->
    type_sort S ->
    glu_rel_exp_under_sub Δ M A ->
    glu_rel_sub_inst Γ (τ,,M[τ]) (Δ ▸ A ≔ M).
Proof.
  intros * Hτ HA HS HM.
  pose proof (glu_rel_exp_to_wf_exp (glu_rel_exp_under_sub_inst _ _ _ HM _ _ Hτ)) as HMτ.
  apply (glu_rel_sub_inst_extend_gen (e := ce_def A M)); [ exact Hτ | | | intros U Hx; inversion Hx ].
  - eapply wf_sub_extend_def; [ apply Hτ | exact HA | exact HS | exact (glu_rel_exp_under_sub_wf HM) | exact HMτ
                              | apply wf_exp_eq_refl; exact HMτ ].
  - intros A' Hx; inversion Hx; subst.
    rewrite exp_sub_shift_extend; eapply glu_rel_exp_under_sub_inst_renaming; eassumption.
Qed.

(** An instance extended by a unit's literal, for a module slot of the
    unit glued at its instances: no component is a term, and the slot's
    unit is the unit's instance. *)
Lemma glu_rel_sub_inst_extend_mod : forall {Γ Δ τ U},
    glu_rel_sub_inst Γ τ Δ ->
    gc_deps ⍮ gc_stack ⍮ Δ ⊢ᵘ U ≈ U ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U[τ]ᵘ ≈ U[τ]ᵘ ->
    glu_rel_unit_under_sub Δ U ->
    glu_rel_sub_inst Γ (τ ,,ₘ me_lit U[τ]ᵘ) (Δ ▹ₘ U).
Proof.
  intros * Hτ HU HUτ HUg.
  apply (glu_rel_sub_inst_extend_gen (e := ce_mod U));
    [ exact Hτ | eapply wf_sub_extend_mod; [ apply Hτ | exact HU | exact HUτ ] | intros A' Hx; inversion Hx |].
  intros U' Hx; inversion Hx; subst.
  rewrite gunit_sub_shift_extend; eapply glu_rel_unit_under_sub_inst_renaming; eassumption.
Qed.

(** An instance extended by the instance of a definition's body and a
    unit's literal, for a definition with a module part. *)
Lemma glu_rel_sub_inst_extend_dm : forall {Γ Δ τ A M E} {i : nat},
    glu_rel_sub_inst Γ τ Δ ->
    Δ ⊢ A : Typeω@i ->
    glu_rel_exp_under_sub Δ M A ->
    gc_deps ⍮ gc_stack ⍮ Δ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ (gu_mk nil (md_alias E))[τ]ᵘ ≈ (gu_mk nil (md_alias E))[τ]ᵘ ->
    glu_rel_unit_under_sub Δ (gu_mk nil (md_alias E)) ->
    glu_rel_sub_inst Γ (τ ,,ᵈ M[τ] ‖ me_lit (gu_mk nil (md_alias E))[τ]ᵘ) (Δ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E)).
Proof.
  intros * Hτ HA HM HU HUτ HUg.
  pose proof (glu_rel_exp_to_wf_exp (glu_rel_exp_under_sub_inst _ _ _ HM _ _ Hτ)) as HMτ.
  apply (glu_rel_sub_inst_extend_gen (e := ce_dm A M (gu_mk nil (md_alias E)))); [ exact Hτ | | |].
  - eapply wf_sub_extend_dm; [ apply Hτ | exact HA | exact (glu_rel_exp_under_sub_wf HM) | exact HU | exact HMτ
                             | apply wf_exp_eq_refl; exact HMτ | exact HUτ ].
  - intros A' Hx; inversion Hx; subst.
    rewrite exp_sub_shift_extend; eapply glu_rel_exp_under_sub_inst_renaming; eassumption.
  - intros U' Hx; inversion Hx; subst.
    rewrite gunit_sub_shift_extend; eapply glu_rel_unit_under_sub_inst_renaming; eassumption.
Qed.

End Fixed_GCtx.

(** ** The Rules

    A context rule glues the context with its variables' types; a variable
    is glued at an instance as the instance's component. *)

#[local] Generalizable All Variables.

(** The case of a rule whose conclusion only glues its context: a premise
    glues the context. *)
Ltac glu_ctx_case :=
  glu_intro; first [ assumption | eapply glu_rel_exp_under_sub_ctx; eassumption ].

(** The case of a rule whose conclusion glues a term: at each target, the
    context from a premise, then an instance [τ] into a context [Γ'], with
    the syntactic premises moved to the target. *)
Ltac glu_inst_intro :=
  glu_intro; glu_gctx_embedding_wf;
  econstructor; [ first [ assumption | eapply glu_rel_exp_under_sub_ctx; eassumption ] | intros ?Γ' ?τ ?Hτ ].

(** A premise at an instance: a term at its type, or a type at its sort
    of types. *)
Ltac glu_inst :=
  match goal with
  | Hτ : glu_rel_sub_inst ?Γ' ?τ ?Δ, H : glu_rel_exp_under_sub ?Δ ?M ?A |- ?Γ' ⊩ ?M' : _ =>
      unify M' (exp_sub M τ);
      eapply (glu_rel_exp_under_sub_inst_conv H Hτ);
      first [ apply type_sort_sub;
              first [ assumption | eapply sort_kind_type_sort; eassumption | constructor | apply type_sort_abs_kind; constructor ]
            | reflexivity
            | rewrite ?exp_wk_shift_sub_q, ?abs_kind_sort_sub, ?abs_kind_sort_wk; reflexivity
            | rewrite ?exp_sub_extend_sub, ?exp_sub_q_extend; reflexivity ]
  end.

(** A premise of a local rule at an instance: a term glued at the
    instance, the instance's glued domain, or a side condition. *)
Ltac glu_inst_premise :=
  first [ glu_inst | eapply glu_rel_sub_inst_ctx; eassumption | eassumption ].

Lemma glu_ctx_empty :
  `( ⊢ᵍ Θ ⍮ Ξ ->
     ⊩ Θ ⍮ Ξ ⍮ ⋅ ).
Proof. glu_intro; eapply glu_rel_ctx_types_empty; eapply gctx_embedding_wf, glu_gctx_embedding_embedding; eassumption. Qed.

Lemma glu_ctx_extend :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     sort_kind Srt κ ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹{κ} A ).
Proof. glu_intro; eapply glu_rel_ctx_types_extend; eassumption. Qed.

Lemma glu_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ).
Proof. glu_intro; eapply glu_rel_ctx_types_extend_def; eassumption. Qed.

(** A slot glues when the context does and its unit is well formed and
    glues. *)
Lemma glu_ctx_extend_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ->
     glu_unit_eq Θ Ξ Γ U U ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▹ₘ U ).
Proof.
  glu_intro; glu_gctx_embedding_wf.
  eapply (@glu_rel_ctx_types_extend_mod (gc_mk _ _)); [ eassumption | apply Hwu; eassumption | eassumption ].
Qed.

(** A definition with a module part glues when its term part does and its
    unit is well formed and glues. *)
Lemma glu_ctx_extend_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk nil (md_alias E) ≈ gu_mk nil (md_alias E) ->
     glu_unit_eq Θ Ξ Γ (gu_mk nil (md_alias E)) (gu_mk nil (md_alias E)) ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ gu_mk nil (md_alias E) ).
Proof.
  glu_intro; glu_gctx_embedding_wf.
  eapply (@glu_rel_ctx_types_extend_dm (gc_mk _ _)); [ eassumption | eassumption | apply Hwu; eassumption | eassumption ].
Qed.

(** A variable at an instance is the instance's component, glued at its
    type at every renaming, so at the identity. *)
Lemma glu_vlookup :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊩ #x : A ).
Proof.
  glu_intro; econstructor; [ eassumption |].
  intros Γ' τ Hτ.
  apply glu_rel_exp_of_under_renaming; [ apply Hτ | apply Hτ; eassumption ].
Qed.

Lemma glu_exp_eq_var :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.

Lemma glu_exp_eq_var_delta :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ M : A ->
     ⊩ Θ ⍮ Ξ ⍮ Γ ).
Proof. glu_ctx_case. Qed.
