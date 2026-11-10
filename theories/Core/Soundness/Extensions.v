(** * Extensions at the Instances

    An extension [Ψ] of a context [Γ] is glued at the instances
    ([glu_rel_ext_under_sub]) when each of its entries is glued at the
    instances of the context before it.  An instance of [Γ] then lifts
    through [Ψ]: each entry lifts it by the lifting of its kind
    ([Instances.v]), so the instance lifted through [Ψ] is an instance of
    [Ψ ++ Γ] ([glu_rel_ext_under_sub_inst]).  A term glued at the instances
    of [Ψ ++ Γ] is then glued at the instances of [Γ] lifted through [Ψ],
    as the motives and the branches of an eliminator are.  The extension
    rules glue an extension entry by entry, as the rules type it. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Soundness Require Import LogicalRelation Instances.
Import Domain_Notations Wk_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** The context of a glued extension is glued with its variables'
    types. *)
Lemma glu_rel_ext_under_sub_ctx : forall {Γ Ψ},
    glu_rel_ext_under_sub Γ Ψ ->
    glu_rel_ctx_types Γ.
Proof. induction Ψ as [| e Ψ IH]; cbn; [ intros; assumption | intros [HΨ _]; exact (IH HΨ) ]. Qed.

(** An instance lifted through a glued extension is an instance of the
    extended context: entry by entry, by the lifting of each entry's kind,
    the unit of a module part well formed at the instance by the
    substitution lemma. *)
Lemma glu_rel_ext_under_sub_inst : forall {Γ Ψ},
    glu_rel_ext_under_sub Γ Ψ ->
    forall Γ' τ, glu_rel_sub_inst Γ' τ Γ ->
    glu_rel_sub_inst (tele_sub Ψ τ ++ Γ') (sb_qn (List.length Ψ) τ) (Ψ ++ Γ).
Proof.
  induction Ψ as [| e Ψ IH]; intros HΨ Γ' τ Hτ; cbn in HΨ |- *; [ exact Hτ |].
  destruct HΨ as [HΨ He].
  pose proof (IH HΨ _ _ Hτ) as Hτ'.
  destruct e as [κ A | A M | U | A M U]; cbn in He |- *.
  - destruct He as (S & HS & HA); exact (glu_rel_sub_inst_q Hτ' HA HS).
  - destruct He as [S HS HA HM]; exact (glu_rel_sub_inst_q_def Hτ' HA HS HM).
  - destruct He as [HU HUg].
    exact (glu_rel_sub_inst_q_mod Hτ' HU (sub_preserves_unit _ _ _ _ _ _ _ HU (glu_rel_sub_inst_typed _ _ _ Hτ')) HUg).
  - destruct He as [i E -> HA HM HU HUg].
    pose proof (sub_preserves_unit _ _ _ _ _ _ _ HU (glu_rel_sub_inst_typed _ _ _ Hτ')) as HUτ.
    exact (glu_rel_sub_inst_q_dm Hτ' HA HM HU HUτ HUg).
Qed.

(** A term glued at the instances of an extended context is glued at each
    instance of the context lifted through the extension. *)
Lemma glu_rel_exp_under_sub_ext_inst : forall {Γ Ψ Γ' τ M A},
    glu_rel_ext_under_sub Γ Ψ ->
    glu_rel_exp_under_sub (Ψ ++ Γ) M A ->
    glu_rel_sub_inst Γ' τ Γ ->
    tele_sub Ψ τ ++ Γ' ⊩ M[sb_qn (List.length Ψ) τ] : A[sb_qn (List.length Ψ) τ].
Proof. intros * HΨ HM Hτ; exact (glu_rel_exp_under_sub_inst _ _ _ HM _ _ (glu_rel_ext_under_sub_inst HΨ _ _ Hτ)). Qed.

End Fixed_GCtx.

(** ** The Rules

    An extension glues entry by entry: each entry's parts are the
    fundamental theorem's gluings of the rule's premises, at the context
    before the entry.  The module slot and the definition with a module
    part are in [ModuleCases.v], with the units. *)

#[local] Generalizable All Variables.

Lemma glu_ext_eq_nil :
  `( ⊩ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ ⋅ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ ⋅ ).
Proof. intros * HΓ; split; intros Θ2 Ξ2 Hμ; exact (HΓ _ _ Hμ). Qed.

(** An assumption: its type at a sort of its kind, on each side. *)
Lemma glu_ext_eq_ass :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ A : Srt ->
     sort_kind Srt κ ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ A' : Srt' ->
     sort_kind Srt' κ ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ ▹{κ} A) /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ' ▹{κ} A') ).
Proof.
  intros * [HΨ HΨ'] HA HS HA' HS'; split; intros Θ2 Ξ2 Hμ; (split; [ eauto |]); cbn; eexists; eauto.
Qed.

(** A definition: its type at a sort of types and its body at the type, on
    each side. *)
Lemma glu_ext_eq_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ A : Srt ->
     type_sort Srt ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ A' : Srt' ->
     type_sort Srt' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊩ M : A ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊩ M' : A' ->
     Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ ▸ A ≔ M) /\ Θ ⍮ Ξ ⍮ Γ ⊩ˣ (Ψ' ▸ A' ≔ M') ).
Proof.
  intros * [HΨ HΨ'] HA HS HA' HS' HM HM'; split; intros Θ2 Ξ2 Hμ; (split; [ eauto |]); cbn.
  - econstructor; [ exact HS | exact (HA _ _ Hμ) | exact (HM _ _ Hμ) ].
  - econstructor; [ exact HS' | exact (HA' _ _ Hμ) | exact (HM' _ _ Hμ) ].
Qed.
