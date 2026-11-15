(** * The Set Rules of Eliminators

    The rules of the eliminators in the set model: [elim], its congruence
    and its views.  The lemmas they rest on are in [Inductives/Elim.v] and
    [Inductives/ElimView.v]. *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Import Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Weakening Substitution.
From Mctt.Core.SetModel.Judgments Require Import Substitution Universes Props Functions.
From Mctt.Core.SetModel Require Import Modules.ValidUnit Modules.MemberTypes Modules.Sel Inductives.Model
  Records.Model Inductives.Elim Inductives.ElimView.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members Presup CoreInversions.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths DescTyping MemberLemmas.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing UniformParams Views ViewLeaves.
Import ListNotations.

Section Eliminator.
  (** The context the rules' premises are read at ([Ξ] names contexts below) *)
  Variable Θr : gdeps.
  Variable Ξr : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** An elimination, typed by its premises, of which the parameters, the
    scrutinee, the motives and the branches hold in the model, holds in
    the model: the motive at the scrutinee, of the eliminator's results. *)
Lemma set_rule_elim : forall Γ r p Us m Bks M D Mm bm Ps i,
    set_ctx_slots Θr Ξr T γ Γ ->
    ind_lookup Θr Ξr p = Some D ->
    ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm ->
    List.length Bks = ind_nblk D ->
    List.length Ps = im_np D Mm ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       Θr ⍮ Ξr ⍮ Γ ⊢ P : A) ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       set_exp_eq Θr Ξr T γ Γ A P P) ->
    Θr ⍮ Ξr ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    set_exp_eq Θr Ξr T γ Γ (ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps)) M M ->
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
    motive_kind r ->
    set_exp_eq Θr Ξr T γ Γ (exp_sub (eb_motive bm) (sb_of_list sb_id (List.skipn (ind_nu D) Ps ++ M :: nil)))
      (a_elim r p Us m Bks M) (a_elim r p Us m Bks M).
Proof.
  intros Γ r p Us m Bks M D Mm bm Ps i HΓ HDsrc Hm Hbm HlB HPl HPs0 HPsem0 HMt HMsem HUs Hcnt Hsc0 HMty0 HMotsem0 HMx0 HMxsem0
    Hbrs HBx0 HBxsem0 Hn HBty0 HBsem0 Hmk.
  set_open. destruct HΓ as [HΓ _]. subst Us.
  destruct (gctx_embedding_preserves_wf _ _ _ _ Hμe) as (_ & Mx & _ & _ & Me & _).
  pose proof (fun k P A H1 H2 => Mx _ _ _ (HPs0 k P A H1 H2)) as HPs.
  pose proof (fun k P A H1 H2 => HPsem0 k P A H1 H2 _ _ Hμ) as HPsem.
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
  cbv beta in HPs, HPsem, Hsc, HMty, HMotsem, HMx, HMxsem, HBx, HBxsem, HBty, HBsem.
  assert (Hex : exists FM Fns FMot, set_elim_setting T γ Γ r p m Bks M D Mm bm Ps i FM Fns FMot)
    by (eapply set_elim_setting_of_premises; first [eassumption | reflexivity]).
  destruct Hex as (FM & Fns & FMot & Hset).
  exists (fun ρ => FMot (elim_motive_env p D m Mm (List.firstn (ind_nu D) Ps) Fns FM ρ)),
    (fun ρ => end_value T γ Γ ρ r p (List.firstn (ind_nu D) Ps) Bks (large_results T i) m (FM ρ)),
    (fun ρ => end_value T γ Γ ρ r p (List.firstn (ind_nu D) Ps) Bks (large_results T i) m (FM ρ)).
  constructor; [eapply set_elim_motive_denotes; eassumption | eapply set_elim_denotes; eassumption
               | eapply set_elim_denotes; eassumption | intros; apply set_eq_refl
               | exact (set_elim_setting_value T γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hset)].
Qed.

(** The congruence of the eliminator: equal parameters, scrutinees and
    branches, at motives equal at each member, give equal eliminations. *)
Lemma set_rule_elim_cong : forall Γ r p Us Us' m Bks Bks' M M' D Mm bm Ps Ps' i,
    set_ctx_slots Θr Ξr T γ Γ ->
    ind_lookup Θr Ξr p = Some D ->
    ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm ->
    List.length Bks = ind_nblk D ->
    List.length Bks' = ind_nblk D ->
    List.length Ps = im_np D Mm ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       Θr ⍮ Ξr ⍮ Γ ⊢ P : A) ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       set_exp_eq Θr Ξr T γ Γ A P P) ->
    List.length Ps' = im_np D Mm ->
    (forall k P P' A, List.nth_error Ps k = Some P -> List.nth_error Ps' k = Some P' ->
       List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A -> Θr ⍮ Ξr ⍮ Γ ⊢ P ≈ P' : A) ->
    Θr ⍮ Ξr ⍮ Γ ⊢ M ≈ M' : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    set_exp_eq Θr Ξr T γ Γ (ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps)) M M' ->
    Us = List.firstn (ind_nu D) Ps ->
    Us' = List.firstn (ind_nu D) Ps' ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_binder_count b = S (im_nn Mk)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       Θr ⍮ Ξr ⍮ Γ ⊢ˣ ce_ass ak_relevant (eb_scrutinee_type b) :: tele_sub (im_nparams Mk) (sb_of_list sb_id (List.firstn (ind_nu D) Ps))
                    ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b ->
       Θr ⍮ Ξr ⍮ Γ ⊢ˣ ce_ass ak_relevant (eb_scrutinee_type b) :: tele_sub (im_nparams Mk) (sb_of_list sb_id (List.firstn (ind_nu D) Ps))
                    ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       Θr ⍮ Ξr ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : abs_kind_sort r (a_typ i)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       set_exp_eq Θr Ξr T γ (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b)) ->
    (forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
       Θr ⍮ Ξr ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b ≈ eb_motive b' : abs_kind_sort r (a_typ i)) ->
    (forall k Mk, ind_member D k = Some Mk ->
       Θr ⍮ Ξr ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk, ind_member D k = Some Mk ->
       set_ext_eq_suffixes Θr Ξr T γ Γ (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) (elim_mctx p D k Mk (List.firstn (ind_nu D) Ps))) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k b b', List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
       List.map fst (eb_brs b) = List.map fst (eb_brs b')) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       Θr ⍮ Ξr ⍮ Γ ⊢ˣ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                    ≈ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
       set_ext_eq_suffixes Θr Ξr T γ Γ (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps))
         (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps))) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
    (forall k Mk b b' j c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       List.nth_error Bks' k = Some b' ->
       List.nth_error (eb_brs b) j = Some (c, n, B) -> List.nth_error (eb_brs b') j = Some (c, n, B') ->
       ind_con Mk c = Some gs ->
       Θr ⍮ Ξr ⍮ elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B ≈ B'
         : elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    (forall k Mk b b' j c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       List.nth_error Bks' k = Some b' ->
       List.nth_error (eb_brs b) j = Some (c, n, B) -> List.nth_error (eb_brs b') j = Some (c, n, B') ->
       ind_con Mk c = Some gs ->
       set_exp_eq Θr Ξr T γ (elim_bctx r p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ)
         (elim_branch_type p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) B B') ->
    motive_kind r ->
    set_exp_eq Θr Ξr T γ Γ (exp_sub (eb_motive bm) (sb_of_list sb_id (List.skipn (ind_nu D) Ps ++ M :: nil)))
      (a_elim r p Us m Bks M) (a_elim r p Us' m Bks' M').
Proof.
  intros Γ r p Us Us' m Bks Bks' M M' D Mm bm Ps Ps' i HΓ HDsrc Hm Hbm HlB HlB' HPl HPs0 HPsem0 HPl' HPP0 HMM HMMsem HUs HUs'
    Hcnt Hcnt' Hsc0 Hsc0' HMty0 HMotsem0 HAA0 HMx0 HMxsem0 Hbrs Hnames HBx0 HBxsem0 Hn HBB0 HBBsem0 Hmk.
  set_open. destruct HΓ as [HΓ _]. subst Us Us'.
  destruct (gctx_embedding_preserves_wf _ _ _ _ Hμe) as (_ & Mx & Mq & _ & Me & _).
  pose proof (fun k P A H1 H2 => Mx _ _ _ (HPs0 k P A H1 H2)) as HPs.
  pose proof (fun k P A H1 H2 => HPsem0 k P A H1 H2 _ _ Hμ) as HPsem.
  pose proof (fun k P P' A H1 H2 H3 => Mq _ _ _ _ (HPP0 k P P' A H1 H2 H3)) as HPP.
  pose proof (fun k Mk b H1 H2 => Me _ _ _ (Hsc0 k Mk b H1 H2)) as Hsc.
  pose proof (fun k Mk b H1 H2 => Me _ _ _ (Hsc0' k Mk b H1 H2)) as Hsc'.
  pose proof (fun k Mk b H1 H2 => Mx _ _ _ (HMty0 k Mk b H1 H2)) as HMty.
  pose proof (fun k Mk b H1 H2 => HMotsem0 k Mk b H1 H2 _ _ Hμ) as HMotsem.
  pose proof (fun k Mk b b' H1 H2 H3 => Mq _ _ _ _ (HAA0 k Mk b b' H1 H2 H3)) as HAA.
  pose proof (fun k Mk H1 => Me _ _ _ (HMx0 k Mk H1)) as HMx.
  pose proof (fun k Mk H1 => set_ext_eq_left T γ _ _ _
                (set_ext_eq_suffixes_eq T γ _ _ _ (HMxsem0 k Mk H1 _ _ Hμ) nil _ nil _ eq_refl eq_refl eq_refl)) as HMxsem.
  pose proof (fun k Mk c gs H1 H2 => Me _ _ _ (HBx0 k Mk c gs H1 H2)) as HBx.
  pose proof (fun k Mk c gs H1 H2 => set_ext_eq_left T γ _ _ _
                (set_ext_eq_suffixes_eq T γ _ _ _ (HBxsem0 k Mk c gs H1 H2 _ _ Hμ) nil _ nil _ eq_refl eq_refl eq_refl)) as HBxsem.
  pose proof (fun k Mk b b' j c gs n B B' H1 H2 H3 H4 H5 H6 => Mq _ _ _ _ (HBB0 k Mk b b' j c gs n B B' H1 H2 H3 H4 H5 H6)) as HBB.
  pose proof (fun k Mk b b' j c gs n B B' H1 H2 H3 H4 H5 H6 => HBBsem0 k Mk b b' j c gs n B B' H1 H2 H3 H4 H5 H6 _ _ Hμ) as HBBsem.
  cbv beta in HPs, HPsem, HPP, Hsc, Hsc', HMty, HMotsem, HAA, HMx, HMxsem, HBx, HBxsem, HBB, HBBsem.
  assert (Hex : exists FM Fns FMot, set_elim_cong_setting T γ Γ r p m Bks Bks' M M' D Mm bm Ps Ps' i FM Fns FMot)
    by (eapply set_elim_cong_setting_of_premises; first [eassumption | reflexivity]).
  destruct Hex as (FM & Fns & FMot & [Hset HFR]).
  exists (fun ρ => FMot (elim_motive_env p D m Mm (List.firstn (ind_nu D) Ps) Fns FM ρ)),
    (fun ρ => end_value T γ Γ ρ r p (List.firstn (ind_nu D) Ps) Bks (large_results T i) m (FM ρ)),
    (fun ρ => end_value T γ Γ ρ r p (List.firstn (ind_nu D) Ps) Bks (large_results T i) m (FM ρ)).
  constructor; [eapply set_elim_motive_denotes; eassumption | eapply set_elim_denotes; eassumption | exact HFR
               | intros; apply set_eq_refl | exact (set_elim_setting_value T γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hset)].
Qed.

End Eliminator.
Section ElimView.
  (** The context the rule's premises are read at *)
  Variable Θr : gdeps.
  Variable Ξr : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** The eliminator at a view, of which the parameters, the scrutinee, the
    motives and the branches hold in the model, is in the model the
    container's eliminator at the view's blocks wrapped. *)
Lemma set_rule_elim_view : forall Γ r p Us m Bks M D Mm bm Ps i qc k' Is vm D' C,
    set_ctx_slots Θr Ξr T γ Γ ->
    ind_lookup Θr Ξr p = Some D ->
    ind_member D m = Some Mm ->
    im_head Mm = mh_view qc k' Is vm ->
    ind_lookup Θr Ξr qc = Some D' ->
    List.nth_error Bks m = Some bm ->
    List.length Bks = ind_nblk D ->
    List.length Ps = im_np D Mm ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       Θr ⍮ Ξr ⍮ Γ ⊢ P : A) ->
    (forall k P A, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mm) sb_id Ps) k = Some A ->
       set_exp_eq Θr Ξr T γ Γ A P P) ->
    Θr ⍮ Ξr ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    set_exp_eq Θr Ξr T γ Γ (ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps)) M M ->
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
    motive_kind r ->
    Θr ⍮ Ξr ⍮ Γ ⊢ a_elim r qc (im_pre Mm (List.firstn (ind_nu D) Ps)) k'
        (view_wrap r p qc D D' vm (List.firstn (ind_nu D) Ps) (im_pre Mm (List.firstn (ind_nu D) Ps)) Bks) M : C ->
    set_exp_eq Θr Ξr T γ Γ (exp_sub (eb_motive bm) (sb_of_list sb_id (List.skipn (ind_nu D) Ps ++ M :: nil)))
      (a_elim r p Us m Bks M)
      (a_elim r qc (im_pre Mm (List.firstn (ind_nu D) Ps)) k'
         (view_wrap r p qc D D' vm (List.firstn (ind_nu D) Ps) (im_pre Mm (List.firstn (ind_nu D) Ps)) Bks) M).
Proof.
  intros Γ r p Us m Bks M D Mm bm Ps i qc k' Is vm D' C HΓ HDsrc Hm Hh HD'src Hbm HlB HPl HPs0 HPsem0 HMt HMsem HUs Hcnt Hsc0
    HMty0 HMotsem0 HMx0 HMxsem0 Hbrs HBx0 HBxsem0 Hn HBty0 HBsem0 Hmk HR.
  set_open. destruct HΓ as [HΓ _]. subst Us.
  destruct (gctx_embedding_preserves_wf _ _ _ _ Hμe) as (_ & Mx & _ & _ & Me & _).
  pose proof (fun k P A H1 H2 => Mx _ _ _ (HPs0 k P A H1 H2)) as HPs.
  pose proof (fun k P A H1 H2 => HPsem0 k P A H1 H2 _ _ Hμ) as HPsem.
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
  cbv beta in HPs, HPsem, Hsc, HMty, HMotsem, HMx, HMxsem, HBx, HBxsem, HBty, HBsem.
  assert (Hex : exists FM Fns FMot, set_elim_view_setting T γ Γ r p m Bks M D Mm bm Ps i qc k' vm D' FM Fns FMot)
    by (eapply set_elim_view_setting_of_premises; first [eassumption | reflexivity]).
  destruct Hex as (FM & Fns & FMot & [Hset HFR]).
  exists (fun ρ => FMot (elim_motive_env p D m Mm (List.firstn (ind_nu D) Ps) Fns FM ρ)),
    (fun ρ => end_value T γ Γ ρ r p (List.firstn (ind_nu D) Ps) Bks (large_results T i) m (FM ρ)),
    (fun ρ => end_value T γ Γ ρ r p (List.firstn (ind_nu D) Ps) Bks (large_results T i) m (FM ρ)).
  constructor; [eapply set_elim_motive_denotes; eassumption | eapply set_elim_denotes; eassumption | exact HFR
               | intros; apply set_eq_refl | exact (set_elim_setting_value T γ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hset)].
Qed.

End ElimView.
