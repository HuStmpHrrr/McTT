(** * Values of Members of Global Modules

    A member of a global module lacking parameters is a member closure
    ([eval_sel_global_unsat]), not its stored value: applied to the
    module's remaining arguments it is the stored value applied to all of
    them.  Its gluing is the stored value's, read along the arguments: a
    value that applies as a glued one does, at a type of nested [Π]s, is
    glued ([app_sim_glu]), with no move of a gluing between values.  The
    type of the member is a [Π] over the module's telescope
    ([eval_ctx_pi_kinds]), and a member closure applies as the stored value
    does ([glob_member_sim]). *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic.PER.Lemmas Require Import UniverseSubtyping.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Soundness Require Import LogicalRelation.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Completeness.Consequences Require Import Types.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** [v] applies as [g] does to arguments of the kinds [ks], outermost
    first: it takes an argument of the next kind, and applied to one it
    gives a value that applies as [g]'s result does to the rest; after all
    of them the two are the same. *)
Fixpoint app_sim (ks : list abs_kind) (v g : domain) : Prop :=
  match ks with
  | nil => v = g
  | κ :: ks => arg_kind gc_deps gc_stack v = κ /\
            forall n g', $| g & n |↘ g' -> exists v', $| v & n |↘ v' /\ app_sim ks v' g'
  end.

(** A type value of nested [Π]s into evaluated kinds, their domains of the
    kinds [ks], outermost first, at every argument. *)
Fixpoint pi_kinds_depth (ks : list abs_kind) (a : domain) : Prop :=
  match ks with
  | nil => True
  | κ :: ks => exists κc a1 ρ B, a = d_pi κ κc a1 ρ B /\ evaluated_kind κc /\
            forall c b, ⟦ B ⟧ ρ ↦ c ⦂ entry_type_value a1 ↘ b -> pi_kinds_depth ks b
  end.

(** Values that apply as related ones do are related. *)
Lemma app_sim_per : forall ks i a a' R,
    pi_kinds_depth ks a -> pi_kinds_depth ks a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    forall v v' g g', app_sim ks v g -> app_sim ks v' g' -> R g g' -> R v v'.
Proof.
  induction ks as [| κ ks IH]; intros * Hd Hd' HR * Hv Hv' Hg; cbn in Hv, Hv'.
  - subst; exact Hg.
  - destruct Hd as (κc & a1 & ρ & B & -> & Hκ & HB).
    destruct Hd' as (κc' & a1' & ρ' & B' & -> & Hκ' & HB').
    basic_invert_per_univ_elem HR.
    destruct Hv as [Hkv Hv]; destruct Hv' as [Hkv' Hv'].
    match goal with H : _ <~> pi_elements _ _ _ _ |- _ => rename H into Hpe end.
    match goal with Hm : forall c c' (equiv_c_c' : _), rel_mod_eval _ _ _ _ _ _ |- _ => rename Hm into HBB end.
    apply Hpe; constructor; [ rewrite Hkv; reflexivity | rewrite Hkv'; congruence |].
    apply Hpe in Hg; destruct Hg as [_ _ Hgapp].
    intros c c' Hcc'.
    destruct (Hgapp c c' Hcc') as [gc g'c' Hgc Hg'c' Hrel].
    destruct (Hv _ _ Hgc) as (vc & Hvc & Hsc).
    destruct (Hv' _ _ Hg'c') as (v'c & Hv'c & Hsc').
    destruct (HBB c c' Hcc') as [b b' Eb Eb' Hbb'].
    econstructor; [ exact Hvc | exact Hv'c |].
    eapply IH; [ exact (HB _ _ Eb) | exact (HB' _ _ Eb') | exact Hbb' | exact Hsc | exact Hsc' | exact Hrel ].
Qed.

(** A value that applies as a glued one does, at a type of nested [Π]s, is
    glued: at each argument, its result applies as the glued one's, which
    is glued at the codomain. *)
Lemma app_sim_glu : forall ks i a P El,
    pi_kinds_depth ks a ->
    DG a ∈ glu_univ_elem i ↘ P ↘ El ->
    forall Γ A M v g, Γ ⊢ M : A ® g ∈ El -> app_sim ks v g -> Γ ⊢ M : A ® v ∈ El.
Proof.
  induction ks as [| κ ks IH]; intros * Hd Hga * Hg Hv.
  - cbn in Hv; subst; exact Hg.
  - pose proof Hd as Hd0.
    destruct Hd as (κc & a1 & ρ & B & -> & Hκ & HB).
    destruct (glu_univ_elem_per_univ _ _ _ _ Hga) as [R HR].
    pose proof HR as HR0.
    basic_invert_per_univ_elem HR0.
    match goal with Hm : forall c c' (equiv_c_c' : _), rel_mod_eval _ _ _ _ _ _ |- _ => rename Hm into HBB end.
    match goal with Ha : per_univ_elem _ ?ir a1 a1 |- _ => rename Ha into Ha1 end.
    destruct (glu_univ_elem_pi_clean_inversion1 Ha1 Hκ Hga) as (IP & IEl & OP & OEl & elr & HIg & HOg & Hel & _ & HEl).
    apply HEl in Hg; apply HEl.
    destruct Hg as [? ? ? ? ? ? HMt Hgg HA HIT HOT HIP Happ].
    econstructor; [ exact HMt | | exact HA | exact HIT | exact HOT | exact HIP |].
    + exact (app_sim_per (_ :: ks) _ _ _ _ Hd0 Hd0 Hel _ _ _ _ Hv Hv Hgg).
    + intros Δ φ N n Hφ HN equiv_n.
      destruct (Happ _ _ _ _ Hφ HN equiv_n) as (gn & Hgn & HgnEl).
      destruct Hv as [_ Hv].
      destruct (Hv _ _ Hgn) as (vn & Hvn & Hsn).
      destruct (HBB n n equiv_n) as [b b' Eb _ _].
      exists vn; split; [ exact Hvn |].
      exact (IH _ _ _ _ (HB _ _ Eb) (HOg _ equiv_n _ Eb) _ _ _ _ _ HgnEl Hsn).
Qed.

(** The kinds of a telescope's parameters, outermost first, as a module's
    parameters take arguments ([tele_param_kind]). *)
Definition tele_kinds (T : ctx) : list abs_kind :=
  List.map (fun e => match e with ce_ass ak_level _ => ak_level | _ => ak_relevant end) (List.rev T).

Lemma tele_kinds_app : forall T1 T2, tele_kinds (T1 ++ T2) = tele_kinds T2 ++ tele_kinds T1.
Proof. intros; unfold tele_kinds; rewrite List.rev_app_distr, List.map_app; reflexivity. Qed.

(** The type of functions over a telescope of assumptions of evaluated
    kinds: nested [Π]s, their domains of the telescope's kinds. *)
Lemma eval_ctx_pi_kinds : forall r T A ks0,
    evaluated_kind r ->
    (forall Δ1 κ B Δ2, T = Δ1 ++ ce_ass κ B :: Δ2 -> evaluated_kind κ) ->
    all_assumptions T ->
    (forall ρ a, ⟦ A ⟧ ρ ↘ a -> pi_kinds_depth ks0 a) ->
    forall ρ a, ⟦ ctx_pi_at r T A ⟧ ρ ↘ a -> pi_kinds_depth (tele_kinds T ++ ks0) a.
Proof.
  intros r; induction T as [| e T IH]; intros A ks0 Hr Hk Ha HA ρ a Ea; cbn [ctx_pi_at] in Ea; [ exact (HA _ _ Ea) |].
  apply List.Forall_cons_iff in Ha as [(κ & B & ->) Ha].
  assert (Hκ : evaluated_kind κ) by (apply (Hk nil κ B T); reflexivity).
  change (ce_ass κ B :: T) with ((ce_ass κ B :: nil) ++ T); rewrite tele_kinds_app, <- List.app_assoc.
  eapply (IH (a_pi κ r B A) (tele_kinds (ce_ass κ B :: nil) ++ ks0) Hr); [| exact Ha | | exact Ea ].
  - intros Δ1 κ' B' Δ2 ->; apply (Hk (ce_ass κ B :: Δ1) κ' B' Δ2); reflexivity.
  - intros ρ' a' Ea'; inversion Ea'; subst.
    unfold tele_kinds; cbn [List.rev List.app List.map].
    assert (E : match ce_ass κ B with ce_ass ak_level _ => ak_level | _ => ak_relevant end = κ)
      by (destruct Hκ; reflexivity).
    rewrite E; cbn [pi_kinds_depth].
    do 4 eexists; split; [ reflexivity | split; [ exact Hr |] ].
    intros c b Eb; exact (HA _ _ Eb).
Qed.

(** A member of a global module lacking parameters applies as its stored
    value does: given an argument it is the member of the module given one
    more, a member closure while the module still lacks a parameter
    ([eval_sel_global_unsat]), and the stored value applied to all the
    arguments once it lacks none. *)
Lemma glob_member_sim : forall p T Φ x g,
    gc_loc gc_deps gc_stack p = Some (T, Φ) ->
    (forall args r, List.length args = List.length T -> $*| g & args | gc_deps ⍮ gc_stack ↘ r ->
       dm_global p args ·ₜ x gc_deps ⍮ gc_stack ↘ r) ->
    forall Tin Tout args, T = Tin ++ Tout -> List.length args = List.length Tout ->
    forall gargs, $*| g & args | gc_deps ⍮ gc_stack ↘ gargs ->
    forall v, (Tin = nil -> v = gargs) -> (Tin <> nil -> v = d_member (dm_global p args) (x :: nil)) ->
    app_sim (tele_kinds Tin) v gargs.
Proof.
  intros p T Φ x g Hloc Hsat Tin.
  induction Tin as [| e Tin IH] using List.rev_ind; intros Tout args ET Hl gargs Hg v Hv0 Hv1.
  - cbn; exact (Hv0 eq_refl).
  - assert (Hne : Tin ++ e :: nil <> nil) by (destruct Tin; discriminate).
    rewrite (Hv1 Hne); clear Hv0 Hv1.
    rewrite tele_kinds_app; cbn [tele_kinds List.rev List.app List.map app_sim].
    split.
    + cbn [arg_kind dmod_param_kind]; rewrite Hloc; unfold tele_param_kind.
      rewrite ET, <- List.app_assoc, List.rev_app_distr; cbn [List.app List.rev].
      rewrite <- List.app_assoc, List.nth_error_app2, List.length_rev, Hl by (rewrite List.length_rev; lia).
      replace (length Tout - length Tout) with 0 by lia; cbn.
      destruct e as [[] ? | | | ]; reflexivity.
    + intros n g' Hg'.
      assert (Hg2 : $*| g & args ++ n :: nil | gc_deps ⍮ gc_stack ↘ g')
        by (apply eval_apps_app; exists gargs; split; [ exact Hg | econstructor; [ exact Hg' | constructor ] ]).
      assert (ET' : T = Tin ++ (e :: Tout)) by (rewrite ET, <- List.app_assoc; reflexivity).
      assert (Hl' : List.length (args ++ n :: nil) = List.length (e :: Tout)) by (rewrite List.length_app; cbn; lia).
      destruct Tin as [| e' Tin'] eqn:ETin.
      * (** The module given all its parameters: the stored value applied *)
        exists g'; split; [| apply (IH (e :: Tout) (args ++ n :: nil)); auto; congruence ].
        econstructor; [ constructor | constructor ].
        apply Hsat; [ rewrite ET'; exact Hl' | exact Hg2 ].
      * (** Still lacking one: a member closure *)
        rewrite <- ETin in *.
        exists (d_member (dm_global p (args ++ n :: nil)) (x :: nil)); split.
        -- econstructor; [ constructor | constructor ].
           eapply eval_sel_global_unsat; [ exact Hloc |].
           rewrite Hl', ET', List.length_app, ETin; cbn; lia.
        -- apply (IH (e :: Tout) (args ++ n :: nil) ET' Hl' g' Hg2); [ intros E; rewrite ETin in E; discriminate | intros _; reflexivity ].
Qed.

End Fixed_GCtx.

(** The parameters of a stored module are of evaluated kinds: each is a
    type of a universe or of levels ([params_evaluated]), so not a
    proposition, whose sort would be [Prop] ([subtyp_same_kind]). *)
Lemma glob_tele_kinds : forall Θ Ξ p T Φ, ⊢ᵍ Θ ⍮ Ξ -> loc Θ Ξ p T Φ ->
    forall Δ1 κ A Δ2, T = Δ1 ++ ce_ass κ A :: Δ2 -> evaluated_kind κ.
Proof.
  intros * Hg Hl * ET.
  destruct (loc_valid _ _ _ _ _ (gctx_valid_syn _ _ Hg) Hl) as [[_ HwT l HR] _].
  pose proof (HR _ _ _ _ ET) as HP; rewrite List.app_nil_r in HP.
  rewrite ET in HwT.
  destruct (ctx_decomp_sort_kind (ctx_app_wf_tail _ _ _ _ HwT)) as [_ (Srt & HS & HA)].
  destruct HS; [ constructor | exfalso | constructor ].
  assert (HAp : Θ ⍮ Ξ ⍮ Δ2 ⊢ A : abs_kind_sort ak_propositional Typeω@0) by exact HA.
  assert (Hs : Θ ⍮ Ξ ⍮ Δ2 ⊢ A ⊆ A) by (eapply wf_subtyp_refl; [ exact HA | constructor | eapply wf_exp_eq_refl; exact HA ]).
  destruct HP as [HP | HP].
  - assert (HAr : Θ ⍮ Ξ ⍮ Δ2 ⊢ A : abs_kind_sort ak_relevant Typeω@l) by exact HP.
    pose proof (@subtyp_same_kind (gc_mk Θ Ξ) _ _ _ _ _ _ _ Hs HAp HAr); discriminate.
  - assert (HAr : Θ ⍮ Ξ ⍮ Δ2 ⊢ A : abs_kind_sort ak_level Typeω@0) by exact HP.
    pose proof (@subtyp_same_kind (gc_mk Θ Ξ) _ _ _ _ _ _ _ Hs HAp HAr); discriminate.
Qed.
