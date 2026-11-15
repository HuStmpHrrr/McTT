(** * The Set Rule of [ι]

    The computation rule of the eliminators in the set model.  The lemmas
    it rests on are in [Inductives/Elim.v]. *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Import Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Weakening Substitution.
From Mctt.Core.SetModel.Judgments Require Import Substitution Universes Props Functions.
From Mctt.Core.SetModel Require Import Modules.ValidUnit Modules.MemberTypes Modules.Sel Inductives.Model
  Records.Model Inductives.Elim.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members Presup CoreInversions.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths DescTyping MemberLemmas.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing UniformParams.
Import ListNotations.

Section Eliminator.
  (** The context the rules' premises are read at ([Ξ] names contexts below) *)
  Variable Θr : gdeps.
  Variable Ξr : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** The [ι] rule: the eliminator at a constructor is the constructor's
    branch, at the non-uniform parameters, the arguments and the recursive
    results. *)
Lemma set_rule_elim_iota : forall Γ r p Us m Bks D Mm bm c gs Ps As n B i,
    set_ctx_slots Θr Ξr T γ Γ ->
    ⊢ Θr ⍮ Ξr ⍮ Γ ->
    ind_lookup Θr Ξr p = Some D ->
    ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm ->
    ind_con Mm c = Some gs ->
    List.length Bks = ind_nblk D ->
    List.length Ps = im_np D Mm ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       Θr ⍮ Ξr ⍮ Γ ⊢ P : A) ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       set_exp_eq Θr Ξr T γ Γ A P P) ->
    List.length As = List.length gs ->
    (forall k N A, List.nth_error As k = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list sb_id Ps) As) k = Some A -> Θr ⍮ Ξr ⍮ Γ ⊢ N : A) ->
    (forall k N A, List.nth_error As k = Some N ->
       List.nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list sb_id Ps) As) k = Some A -> set_exp_eq Θr Ξr T γ Γ A N N) ->
    Us = List.firstn (ind_nu D) Ps ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       Θr ⍮ Ξr ⍮ Γ ⊢ˣ ce_ass ak_relevant (eb_scrutinee_type b) :: tele_sub (im_nparams Mk) (sb_of_list sb_id (List.firstn (ind_nu D) Ps))
                    ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       Θr ⍮ Ξr ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : abs_kind_sort r (a_typ i)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       set_exp_eq Θr Ξr T γ (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b)) ->
    (forall k Mk, ind_member D k = Some Mk ->
       Θr ⍮ Ξr ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk, ind_member D k = Some Mk ->
       set_ext_eq_suffixes Θr Ξr T γ Γ (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps))) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       Θr ⍮ Ξr ⍮ Γ ⊢ˣ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                    ≈ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       set_ext_eq_suffixes Θr Ξr T γ Γ (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps))
         (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps))) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       Θr ⍮ Ξr ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
         : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       set_exp_eq Θr Ξr T γ (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ)
         (elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) B B) ->
    brs_lookup (eb_brs bm) c = Some (n, B) ->
    motive_kind r ->
    set_exp_eq Θr Ξr T γ Γ
      (exp_sub (eb_motive bm) (sb_of_list sb_id (List.skipn (ind_nu D) Ps ++
         apps_exp (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
           (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As) :: nil)))
      (a_elim r p Us m Bks (apps_exp (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                              (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As)))
      (exp_sub B (sb_of_list sb_id (List.skipn (ind_nu D) Ps ++ As ++
         elim_ihs r p D (List.firstn (ind_nu D) Ps) Bks (sb_of_list sb_id Ps) (im_nn Mm) gs As))).
Proof.
  intros Γ r p Us m Bks D Mm bm c gs Ps As n B i HΓ HcΓ HDsrc Hm Hbm Hgs HlB HPl HPs0 HPsem0 HAl HAs0 HAsem0 HUs Hcnt Hsc0
    HMty0 HMotsem0 HMx0 HMxsem0 Hbrs HBx0 HBxsem0 Hn HBty0 HBsem0 Hlook Hmk.
  set_open. destruct HΓ as [HΓ _]. subst Us.
  destruct (gctx_embedding_preserves_wf _ _ _ _ Hμe) as (_ & Mx & _ & _ & Me & _).
  pose proof (fun k P A H1 H2 => Mx _ _ _ (HPs0 k P A H1 H2)) as HPs.
  pose proof (fun k P A H1 H2 => HPsem0 k P A H1 H2 _ _ Hμ) as HPsem.
  pose proof (fun k N A H1 H2 => Mx _ _ _ (HAs0 k N A H1 H2)) as HAs.
  pose proof (fun k N A H1 H2 => HAsem0 k N A H1 H2 _ _ Hμ) as HAsem.
  pose proof (fun k Mk b H1 H2 => Me _ _ _ (Hsc0 k Mk b H1 H2)) as Hsc.
  pose proof (fun k Mk b H1 H2 => Mx _ _ _ (HMty0 k Mk b H1 H2)) as HMty.
  pose proof (fun k Mk b H1 H2 => HMotsem0 k Mk b H1 H2 _ _ Hμ) as HMotsem.
  pose proof (fun k Mk H1 => Me _ _ _ (HMx0 k Mk H1)) as HMx.
  pose proof (fun k Mk H1 => set_ext_eq_left T γ _ _ _
                (set_ext_eq_suffixes_eq T γ _ _ _ (HMxsem0 k Mk H1 _ _ Hμ) nil _ nil _ eq_refl eq_refl eq_refl)) as HMxsem.
  pose proof (fun k Mk c gs H1 H2 => Me _ _ _ (HBx0 k Mk c gs H1 H2)) as HBx.
  pose proof (fun k Mk c gs H1 H2 => set_ext_eq_left T γ _ _ _
                (set_ext_eq_suffixes_eq T γ _ _ _ (HBxsem0 k Mk c gs H1 H2 _ _ Hμ) nil _ nil _ eq_refl eq_refl eq_refl)) as HBxsem.
  pose proof (fun k Mk b c gs n B H1 H2 H3 H4 => Mx _ _ _ (HBty0 k Mk b c gs n B H1 H2 H3 H4)) as HBty.
  pose proof (fun k Mk b c gs n B H1 H2 H3 H4 => HBsem0 k Mk b c gs n B H1 H2 H3 H4 _ _ Hμ) as HBsem.
  cbv beta in HPs, HPsem, HAs, HAsem, Hsc, HMty, HMotsem, HMx, HMxsem, HBx, HBxsem, HBty, HBsem.
  assert (Hex : exists ρb FS FB, set_elim_iota_setting T γ Γ r p m Bks D Mm bm c gs Ps As n B i ρb FS FB)
    by (eapply set_elim_iota_setting_of_premises; first [eassumption | reflexivity]).
  destruct Hex as (ρb & FS & FB & Hset).
  exists (fun ρ => FS (ρb ρ)), (iota_value r FB ρb), (fun ρ => FB (ρb ρ)).
  constructor; [exact (set_elim_iota_setting_type T γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hset)
               | eapply set_elim_iota_lhs_denotes; eassumption
               | exact (set_elim_iota_setting_rhs T γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hset)
               | eapply set_elim_iota_values; eassumption | eapply set_elim_iota_value_mem; eassumption].
Qed.

End Eliminator.
