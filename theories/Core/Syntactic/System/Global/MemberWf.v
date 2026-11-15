(** * Well-Formed Parts of Modules

    The parts a well-formed module expression, unit or context is made of are
    well-formed: the unit of a slot, the parts of an equivalence of module
    expressions, an extension read off a context, and the telescopes and alias
    units of a valid global context. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System.Global Require Export Presup.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Unit of a Slot *)

Lemma ctx_lookup_mod_wf : forall Θ Ξ Γ x U,
    ⊢ Θ ⍮ Ξ ⍮ Γ -> Γ ∋ #x ≔ₘ U -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U.
Proof.
  intros * HΓ Hx; induction Hx.
  - destruct (ctx_decomp_mod HΓ) as [HΓ' HU].
    eapply wk_preserves_unit; [ exact HU | apply wf_wk_shift; exact HΓ ].
  - eapply wk_preserves_unit; [ exact (ctx_decomp_dm_unit HΓ) | apply wf_wk_shift; exact HΓ ].
  - match goal with HΓ : ⊢ _ ⍮ _ ⍮ ?e :: ?G |- _ =>
      assert (⊢ Θ ⍮ Ξ ⍮ G) as HΓ' by (eapply (ctx_app_wf_tail _ _ (e :: nil)); exact HΓ) end.
    eapply wk_preserves_unit; [ eauto | apply wf_wk_shift; exact HΓ ].
Qed.

(** ** An Extension Read off a Context *)

Lemma ext_of_ctx : forall Θ Ξ X Γ, ⊢ Θ ⍮ Ξ ⍮ X ++ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ X ≈ X.
Proof.
  induction X as [| [κ A | A M | U | A M U] X IH]; intros * H; cbn in H.
  - constructor; exact H.
  - inversion H; subst.
    match goal with HA : _ ⍮ _ ⍮ X ++ Γ ⊢ A : ?S, HS : sort_kind ?S _ |- _ =>
      eapply wf_ext_eq_ass_same;
        [ apply IH; eauto using presup_exp_ctx | exact HA | exact HS | exact HA ] end.
  - inversion H; subst.
    match goal with HA : _ ⍮ _ ⍮ X ++ Γ ⊢ A : ?S, HS : type_sort ?S, HM : _ ⍮ _ ⍮ X ++ Γ ⊢ M : A |- _ =>
      eapply wf_ext_eq_def_same;
        [ apply IH; eauto using presup_exp_ctx | exact HA | exact HS | exact HA | exact HM | exact HM ] end.
  - inversion H; subst.
    match goal with HU : _ ⍮ _ ⍮ X ++ Γ ⊢ᵘ U ≈ U |- _ =>
      eapply wf_ext_eq_mod; [ apply IH; eauto using presup_unit_eq_ctx | exact HU | exact HU ] end.
  - inversion H; subst.
    match goal with HA : _ ⍮ _ ⍮ X ++ Γ ⊢ A : Typeω@_, HM : _ ⍮ _ ⍮ X ++ Γ ⊢ M : A,
                    HU : _ ⍮ _ ⍮ X ++ Γ ⊢ᵘ ?U ≈ ?U |- _ =>
      eapply wf_ext_eq_dm;
        [ apply IH; eauto using presup_exp_ctx | exact HA | eapply wf_exp_eq_refl; exact HA | exact HM
        | eapply wf_exp_eq_refl; exact HM | exact HA | exact HM | exact HU | exact HU ] end.
Qed.

(** ** The Parts of a Well-Formed Unit *)



Lemma member_ref_cons : forall H y ch, ch <> nil -> member_ref H (y :: ch) = member_ref (me_mem H y) ch.
Proof. intros * Hne; destruct ch; [ contradiction | reflexivity ]. Qed.

Lemma member_ref_mems : forall pre H x, member_ref H (pre ++ x :: nil) = a_mem (me_mems H pre) x.
Proof.
  induction pre as [| y pre IH]; intros; [ reflexivity |].
  cbn [app me_mems]; rewrite member_ref_cons by (destruct pre; discriminate); apply IH.
Qed.

Lemma qname_term_snoc : forall mp x, qname_term (qname_app mp (x :: nil)) = a_mem (qname_mod mp) x.
Proof. intros [fp ms] x; unfold qname_term, qname_mod; cbn; apply member_ref_mems. Qed.

(** ** Applied Modules

    A module applied to arguments splits one way into a module that is no
    application and the arguments. *)

Definition me_noapp (H : modexp) : Prop := match H with me_app _ _ => False | _ => True end.

Lemma me_apps_snoc : forall Ns H N, me_apps H (Ns ++ N :: nil) = me_app (me_apps H Ns) N.
Proof. induction Ns as [| N' Ns IH]; intros; cbn; [ reflexivity | apply IH ]. Qed.

Lemma app_split_length : forall (Ms Ks Ms' Ks' : list exp),
    Ms ++ Ks = Ms' ++ Ks' -> List.length Ms = List.length Ms' -> Ms = Ms' /\ Ks = Ks'.
Proof.
  induction Ms as [| M Ms IH]; intros * HL Hl; destruct Ms' as [| M' Ms']; cbn in *; try discriminate; [ auto |].
  injection HL as -> HL; injection Hl as Hl; destruct (IH _ _ _ HL Hl) as [-> ->]; auto.
Qed.

(** A module split into the module it applies and the arguments. *)
Fixpoint me_unapps (H : modexp) : (modexp * list exp)%type :=
  match H with
  | me_app H' N => let (H0, Ns) := me_unapps H' in (H0, Ns ++ N :: nil)
  | _ => (H, nil)
  end.

Lemma me_unapps_spec : forall H, H = me_apps (fst (me_unapps H)) (snd (me_unapps H)) /\ me_noapp (fst (me_unapps H)).
Proof.
  induction H as [| | | H IH N |]; cbn; try (split; [ reflexivity | exact I ]).
  destruct (me_unapps H) as [H0 Ns]; cbn in *; destruct IH as [-> Hn].
  rewrite me_apps_snoc; split; [ reflexivity | exact Hn ].
Qed.

Lemma apps_snoc : forall args M N, apps M (args ++ N :: nil) = a_app (apps M args) N.
Proof. induction args; intros; cbn; auto. Qed.

(** ** Telescopes of a Valid Global Context *)
