(** * Changing the Parameters of an Eliminator

    A checker infers the parameters of the scrutinee's type, which are equal
    to, not the same as, those of a derivation, so it is what moves the
    premises of the eliminator to them: the blocks are typed at the equal
    uniform parameters ([blocks_typed_us_conv], in
    [System/Inductives/UniformParams.v]), the scrutinee at the equal
    parameters, and the motive's instance at the non-uniform ones and the
    scrutinee is equal at equal ones. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export SystemOpt.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing Views UniformParams.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {Θ : gdeps} {Ξ : gstack}.

  (** ** The Eliminator's Premises at Equal Parameters *)

  Lemma wf_elim_params_conv : forall Γ p D m Mm bm Ps Ps' M Bks i,
      ind_lookup Θ Ξ p = Some D -> ind_member D m = Some Mm -> nth_error Bks m = Some bm ->
      List.length Ps = im_np D Mm ->
      (forall j P T, nth_error Ps j = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
      List.length Ps' = im_np D Mm ->
      (forall j P T, nth_error Ps' j = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps') j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
      (forall j P P' T, nth_error Ps j = Some P -> nth_error Ps' j = Some P' ->
         nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P ≈ P' : T) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
      blocks_typed Θ Ξ Γ p D (List.firstn (ind_nu D) Ps) Bks i ->
      Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps') (List.skipn (ind_nu D) Ps') /\
      blocks_typed Θ Ξ Γ p D (List.firstn (ind_nu D) Ps') Bks i /\
      Θ ⍮ Ξ ⍮ Γ ⊢ (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)]
                ≈ (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps' ++ M :: nil)] : Typeω@i.
  Proof.
    intros * Hl Hm Hb HPl HPt HPl' HPt' HPP HM HBt.
    assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
    destruct (params_typed_split _ _ D Hc _ _ Γ Ps Hm HPl HPt) as [HUt HNt].
    destruct (params_typed_split _ _ D Hc _ _ Γ Ps' Hm HPl' HPt') as [HUt' HNt'].
    destruct (params_eq_split Γ D m Mm Ps Ps' Hc Hm HPl HPl' HPP) as [HUe HNe].
    set (Us := List.firstn (ind_nu D) Ps) in *; set (Us' := List.firstn (ind_nu D) Ps') in *.
    set (Ns := List.skipn (ind_nu D) Ps) in *; set (Ns' := List.skipn (ind_nu D) Ps') in *.
    assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
    assert (HUl' : List.length Us' = ind_nu D) by (unfold Us'; rewrite List.length_firstn; unfold im_np in HPl'; lia).
    assert (HNl : List.length Ns = im_nn Mm) by (unfold Ns; rewrite List.length_skipn; unfold im_np in HPl; lia).
    assert (HNl' : List.length Ns' = im_nn Mm) by (unfold Ns'; rewrite List.length_skipn; unfold im_np in HPl'; lia).
    pose proof (blocks_typed_us_conv _ _ _ _ _ _ _ Hl HΓ HUl HUt HUl' HUt' HUe HBt) as HBt'.
    pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUt) as Hσ.
    assert (Hσσ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ).
    { eapply wf_sub_eq_of_list; [ exact (decl_closed_ass _ Hc) | exact (wf_uparams_app _ _ _ HD Hc _ HΓ)
                                | apply wf_sub_eq_refl, wf_sub_id, HΓ | exact HUl | exact HUl' | exact HUe ]. }
    (* the non-uniform parameters, as a substitution *)
    assert (Hδδ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Ns ≈ sb_of_list Id Ns' : tele_sub (im_nparams Mm) (sb_of_list Id Us) ++ Γ).
    { eapply wf_sub_eq_of_list; [ apply tele_ass_sub; exact (decl_typed_nparams_ass _ _ _ HD _ _ Hm) | exact (wf_nparams_sub _ _ _ HD Hc _ _ _ _ Hm HΓ Hσ)
                                | apply wf_sub_eq_refl, wf_sub_id, HΓ | rewrite length_tele_sub; exact HNl
                                | rewrite length_tele_sub; exact HNl' |].
      intros j N N' T HN HN' HT; rewrite tele_insts_tele_sub in HT.
      rewrite (tele_insts_sb_eq _ _ (sb_of_list Id Us)) in HT by apply sb_compose_id_right.
      exact (HNe _ _ _ _ HN HN' HT). }
    assert (Hδ' : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Ns' : tele_sub (im_nparams Mm) (sb_of_list Id Us) ++ Γ) by (gen_presups; assumption).
    (* the member's type: at the other non-uniform, then uniform, parameters *)
    pose proof (HMc_eq := elim_mctx_us_eq _ _ _ _ _ _ _ Hl Hm HΓ HUl HUl' Hσσ).
    unfold elim_mctx in HMc_eq.
    destruct (ext_eq_ass_inv _ _ _ _ _ _ _ HMc_eq) as (j & _ & Hhd & Hhh & _).
    assert (Ehd : forall Vs Xs, List.length Vs = ind_nu D -> List.length Xs = im_nn Mm ->
               (ind_mty p D m (List.map (fun U => U[wk_shiftn (im_nn Mm)]ʷ) Vs) (vars_from 0 (im_nn Mm)))[sb_of_list Id Xs]
               = ind_mty p D m Vs Xs).
    { intros Vs Xs HVl HXl; rewrite ind_head_inst by assumption.
      rewrite (List.map_ext _ (fun U => U) exp_sub_id), List.map_id; reflexivity. }
    pose proof (sub_eq_preserves_typ _ _ _ _ _ _ _ _ Hhd Hδδ) as HT1.
    pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ Hhh Hδ') as HT2.
    rewrite !Ehd in HT1, HT2 by assumption.
    assert (HM1 : Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m Us Ns') by (eapply wf_conv'; [ exact HM | exact HT1 ]).
    split; [ eapply wf_conv'; [ exact HM1 | exact HT2 ] | split; [ exact HBt' |] ].
    (* the motive's instance *)
    eapply sub_eq_preserves_typ; [ exact (blocks_typed_motive _ _ _ _ _ _ _ _ HBt _ _ _ Hm Hb) |].
    rewrite !sb_of_list_app; cbn [sb_of_list].
    unfold elim_mctx; cbn [List.app].
    eapply wf_sub_eq_extend; [ exact Hδδ | exact Hhd | rewrite Ehd by assumption; exact HM | rewrite Ehd by assumption; exact HM1
                             | rewrite Ehd by assumption; apply wf_exp_eq_refl; exact HM ].
  Qed.
End Fixed_GCtx.
