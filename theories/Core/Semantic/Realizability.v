From Stdlib Require Import Lia Morphisms_Relations PeanoNat Relation_Definitions.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export NbE PER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.


Section Fixed_GCtx.
  Context {GC : GCtx}.


(** ** Reading Back at Telescopes *)

Lemma read_ps_app : forall s ρ T1 vs1 Ms1, read_ps gc_deps gc_stack s ρ T1 vs1 Ms1 ->
    forall T2 vs2 Ms2, read_ps gc_deps gc_stack s (env_args ρ vs1) T2 vs2 Ms2 ->
    read_ps gc_deps gc_stack s ρ (T1 ++ T2) (vs1 ++ vs2) (nfs_app Ms1 Ms2).
Proof.
  induction 1; intros * H2; cbn [List.app nfs_app]; [ exact H2 |].
  econstructor; [ eassumption | eassumption | apply IHread_ps; exact H2 ].
Qed.

Lemma skipn_nth_cons' : forall {X : Type} (l : list X) n a,
    List.nth_error l n = Some a -> List.skipn n l = a :: List.skipn (S n) l.
Proof.
  induction l as [| b l IH]; intros [| n] a H; cbn in *; try discriminate; [ injection H as ->; reflexivity | apply IH; exact H ].
Qed.

(** Two lists related at a telescope whose types read back related elements
    equally read back equally. *)
Lemma read_ps_tele : forall (T : list centry) (tr : nat -> list domain -> relation domain) ρ ρ',
    tele_ass T ->
    (forall k A pre pre', List.nth_error T k = Some (ce_ass A) -> tele_pre tr k pre pre' ->
       exists a a', ⟦ A ⟧ env_args ρ pre ↘ a /\ ⟦ A ⟧ env_args ρ' pre' ↘ a' /\
         (forall b b', tr k pre b b' -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top)) ->
    forall vs vs', tele_full tr T vs vs' ->
    forall s, exists Ms, read_ps gc_deps gc_stack s ρ T vs Ms /\ read_ps gc_deps gc_stack s ρ' T vs' Ms.
Proof.
  intros * Hass Hev vs vs' Hf s.
  pose proof Hf as Hf'; rewrite tele_full_iff in Hf'; destruct Hf' as (Hl & Hl' & Hr).
  assert (Hall : forall m j, m + j = List.length T ->
             exists Ms, read_ps gc_deps gc_stack s (env_args ρ (List.firstn j vs)) (List.skipn j T) (List.skipn j vs) Ms /\
                        read_ps gc_deps gc_stack s (env_args ρ' (List.firstn j vs')) (List.skipn j T) (List.skipn j vs') Ms).
  { induction m as [| m IH]; intros j Hj.
    - rewrite !List.skipn_all2 by lia; exists nfs_nil; split; constructor.
    - destruct (nth_error_lt_some' T j ltac:(lia)) as [e He].
      destruct (nth_error_lt_some' vs j ltac:(lia)) as [v Hv].
      destruct (nth_error_lt_some' vs' j ltac:(lia)) as [v' Hv'].
      assert (He' : exists A, e = ce_ass A)
        by (unfold tele_ass in Hass; rewrite List.Forall_forall in Hass; apply Hass; eapply List.nth_error_In; exact He).
      destruct He' as [A ->].
      destruct (Hev _ _ _ _ He (tele_pre_of_full _ _ _ _ j Hf ltac:(lia))) as (a & a' & Ea & Ea' & Hrb).
      destruct (Hrb _ _ (Hr _ _ _ Hv Hv') s) as (V & HV & HV').
      destruct (IH (S j) ltac:(lia)) as (Ms & HM & HM').
      rewrite (firstn_S_snoc _ _ _ Hv), env_args_snoc in HM.
      rewrite (firstn_S_snoc _ _ _ Hv'), env_args_snoc in HM'.
      exists (nfs_cons V Ms).
      rewrite (skipn_nth_cons' _ _ _ He), (skipn_nth_cons' _ _ _ Hv), (skipn_nth_cons' _ _ _ Hv').
      split; econstructor; eassumption. }
  destruct (Hall (List.length T) 0 ltac:(lia)) as (Ms & HM & HM'); exists Ms; split; assumption.
Qed.

Lemma rev_params_split : forall D, List.rev (ind_params D) = List.rev (ind_uparams D) ++ List.rev (ind_nparams D).
Proof.
  intros; unfold ind_uparams, ind_nparams.
  rewrite <- List.rev_app_distr, List.firstn_skipn; reflexivity.
Qed.

Lemma read_ps_length : forall s ρ T vs Ms, read_ps gc_deps gc_stack s ρ T vs Ms -> List.length vs = List.length T.
Proof. induction 1; cbn; congruence. Qed.

(** The codomain of the type of an argument of a function shape, at an
    argument. *)
Lemma eval_fam_cod_shfam : forall p ups ρ t x a,
    eval_shty gc_deps gc_stack p ups (ρ ↦ x) t a ->
    ⟦ fam_cod ⟧ nil ↦ d_shfam p ups ρ t ↦ x ↘ a.
Proof. intros; unfold fam_cod; econstructor; [ apply eval_exp_var | apply eval_exp_var | econstructor; eassumption ]. Qed.

Lemma eval_fam_cod_ihfam : forall ρm A ρ t f x fx a,
    $| f & x | gc_deps ⍮ gc_stack ↘ fx ->
    eval_ihty gc_deps gc_stack ρm A (ρ ↦ x) t fx a ->
    ⟦ fam_cod ⟧ nil ↦ d_ihfam ρm A ρ t f ↦ x ↘ a.
Proof. intros; unfold fam_cod; econstructor; [ apply eval_exp_var | apply eval_exp_var | econstructor; eassumption ]. Qed.

Lemma env_args_snoc3 : forall (u a b c : list domain) x,
    env_args nil (u ++ a ++ b ++ c ++ x :: nil) = env_args nil (u ++ a ++ b ++ c) ↦ x.
Proof. intros; rewrite !List.app_assoc, env_args_snoc; reflexivity. Qed.

(** The realisability of an inductive type, from that of the types of its
    telescopes. *)
Lemma realize_ind : forall p D ups ups' ns ns'
    (nr : nat -> list domain -> relation domain)
    (ar : list domain -> String.string -> nat -> list domain -> relation domain)
    (dr : list domain -> exp -> relation domain),
    ind_lookup gc_deps gc_stack p = Some D ->
    tele_ass (ind_params D) ->
    List.length ups = ind_nu D ->
    per_top_ps (List.rev (ind_uparams D)) ups ups' ->
    (forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) -> tele_pre nr k vs vs' ->
       exists a a', ⟦ A ⟧ env_args nil (ups ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups' ++ vs') ↘ a' /\
         (forall b b', nr k vs b b' -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top)) ->
    (forall ms ms' c gs k A vs vs',
       tele_full nr (List.rev (ind_nparams D)) ms ms' -> ind_con D c = Some gs ->
       List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' ->
       exists a a', ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups' ++ ms' ++ vs') ↘ a' /\
         (forall b b', ar ms c k vs b b' -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top)) ->
    (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys',
       tele_full nr (List.rev (ind_nparams D)) ms ms' ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
       List.nth_error (ptyp_doms t) k = Some B ->
       tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
       exists a a', ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ a /\ ⟦ B ⟧ env_args nil (ups' ++ ms' ++ ws' ++ ys') ↘ a' /\
         Dom a ≈ a' ∈ per_top_typ /\
         (forall c c', Dom c ≈ c' ∈ per_bot -> dr (ms ++ ws ++ ys) B (⇑ a c) (⇑ a' c'))) ->
    (forall ms ms' c gs gs1 t gs2 ws ws' ys ys',
       tele_full nr (List.rev (ind_nparams D)) ms ms' ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
       tele_full (shape_tr dr ms ws (ptyp_doms t)) (ptyp_doms t) ys ys' ->
       exists bs bs', eval_exps gc_deps gc_stack (ptyp_ps t) (env_args nil (ups ++ ms ++ ws ++ ys)) bs /\
         eval_exps gc_deps gc_stack (ptyp_ps t) (env_args nil (ups' ++ ms' ++ ws' ++ ys')) bs' /\
         tele_full nr (List.rev (ind_nparams D)) bs bs') ->
    tele_full nr (List.rev (ind_nparams D)) ns ns' ->
    Dom d_ind p (ups ++ ns) ≈ d_ind p (ups' ++ ns') ∈ per_top_typ /\
    (forall b b', ind_rel p D ups nr ar dr ns b b' -> Dom ⇓ (d_ind p (ups ++ ns)) b ≈ ⇓ (d_ind p (ups' ++ ns')) b' ∈ per_top).
Proof.
  intros * Hl Hass Hu Hps Hn Ha Hdr Hcl Hns.
  assert (Hle : ind_nu D <= ind_np D).
  { destruct (Hps 0) as (Ms & HM & _); apply read_ps_length in HM.
    rewrite List.length_rev in HM; unfold ind_uparams in HM; rewrite List.length_skipn in HM.
    unfold ind_nn in HM; unfold ind_np; lia. }
  assert (Hu' : List.length ups' = ind_nu D).
  { destruct (Hps 0) as (Ms & _ & HM); apply read_ps_length in HM.
    rewrite List.length_rev in HM; unfold ind_uparams in HM; rewrite List.length_skipn in HM.
    unfold ind_nn in HM; unfold ind_np in *; lia. }
  assert (Hpar : forall xs xs', tele_full nr (List.rev (ind_nparams D)) xs xs' ->
             per_top_ps (List.rev (ind_params D)) (ups ++ xs) (ups' ++ xs')).
  { intros xs xs' Hx s.
    destruct (Hps s) as (Ms1 & HM1 & HM1').
    assert (Hassn : tele_ass (List.rev (ind_nparams D)))
      by (apply List.Forall_rev; unfold ind_nparams; apply Forall_firstn'; exact Hass).
    destruct (read_ps_tele (List.rev (ind_nparams D)) nr (env_args nil ups) (env_args nil ups') Hassn
                ltac:(intros k A pre pre' Hk Hp; rewrite <- !env_args_app; exact (Hn _ _ _ _ Hk Hp))
                _ _ Hx s) as (Ms2 & HM2 & HM2').
    exists (nfs_app Ms1 Ms2); rewrite rev_params_split; split; apply read_ps_app; assumption. }
  assert (Hlen : forall xs xs', tele_full nr (List.rev (ind_nparams D)) xs xs' ->
             List.length (ups ++ xs) = ind_np D /\ List.length (ups' ++ xs') = ind_np D).
  { intros xs xs' Hx; rewrite tele_full_iff in Hx; destruct Hx as (Hl1 & Hl2 & _).
    rewrite List.length_rev, length_nparams in Hl1, Hl2; rewrite !List.length_app; unfold ind_nn in *; lia. }
  split.
  { intros s; destruct (Hpar _ _ Hns s) as (Ms & HM & HM').
    destruct (Hlen _ _ Hns) as [Hl1 Hl2].
    exists (nf_indty p Ms); split; econstructor; eassumption. }
  assert (Hmain :
    (forall xs x y, ind_rel p D ups nr ar dr xs x y -> forall xs', tele_full nr (List.rev (ind_nparams D)) xs xs' ->
       Dom ⇓ (d_ind p (ups ++ xs)) x ≈ ⇓ (d_ind p (ups' ++ xs')) y ∈ per_top) /\
    (forall pre gs vs vs', ind_args_rel p D ups nr ar dr pre gs vs vs' ->
       forall xs xs' c gsf gs1 vp vp', pre = xs ++ nonrec_vals gs1 vp ->
         List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
         tele_full nr (List.rev (ind_nparams D)) xs xs' -> ind_con D c = Some gsf -> gsf = gs1 ++ gs ->
         tele_full (ar xs c) (cargs_nonrec gsf) (nonrec_vals gsf (vp ++ vs)) (nonrec_vals gsf (vp' ++ vs')) ->
         forall s, exists Vs, read_cargs gc_deps gc_stack s p ups (env_args nil (ups ++ pre)) gs vs Vs /\
           read_cargs gc_deps gc_stack s p ups' (env_args nil (ups' ++ xs' ++ nonrec_vals gs1 vp')) gs vs' Vs) /\
    (forall pre t v v', ind_shape_rel p D ups nr ar dr pre t v v' ->
       forall xs xs' c gs1 t0 gs2 ws ws' k ys ys', pre = xs ++ ws ++ ys ->
         tele_full nr (List.rev (ind_nparams D)) xs xs' -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
         tele_pre (ar xs c) (List.length (cargs_nonrec gs1)) ws ws' ->
         ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
         tele_pre (shape_tr dr xs ws (ptyp_doms t0)) k ys ys' ->
         forall s, exists a a' V, eval_shty gc_deps gc_stack p ups (env_args nil (ups ++ pre)) t a /\
           eval_shty gc_deps gc_stack p ups' (env_args nil (ups' ++ xs' ++ ws' ++ ys')) t a' /\
           Rnf ⇓ a v in gc_deps ⍮ gc_stack ⍮ s ↘ V /\ Rnf ⇓ a' v' in gc_deps ⍮ gc_stack ⍮ s ↘ V) /\
    (forall pre t f x f' x', ind_app_rel p D ups nr ar dr pre t f x f' x' ->
       forall xs xs' c gs1 t0 gs2 ws ws' k ys ys', pre = xs ++ ws ++ ys ->
         tele_full nr (List.rev (ind_nparams D)) xs xs' -> ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
         tele_pre (ar xs c) (List.length (cargs_nonrec gs1)) ws ws' ->
         ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
         tele_pre (shape_tr dr xs ws (ptyp_doms t0)) k ys ys' ->
         forall s, exists r r' a a' V, $| f & x | gc_deps ⍮ gc_stack ↘ r /\ $| f' & x' | gc_deps ⍮ gc_stack ↘ r' /\
           eval_shty gc_deps gc_stack p ups (env_args nil (ups ++ pre)) t a /\
           eval_shty gc_deps gc_stack p ups' (env_args nil (ups' ++ xs' ++ ws' ++ ys')) t a' /\
           Rnf ⇓ a r in gc_deps ⍮ gc_stack ⍮ s ↘ V /\ Rnf ⇓ a' r' in gc_deps ⍮ gc_stack ⍮ s ↘ V)).
  { apply ind_rel_mut_ind_all.
    - intros * _ Hc Hb Hb' _ _ Ha0 Hia IH xs' Hx s.
      destruct (Hpar _ _ Hx s) as (Ms & HM & HM').
      destruct (Hlen _ _ Hx) as [Hl1 Hl2].
      assert (Hvl : List.length vs = List.length gs /\ List.length vs' = List.length gs).
      { clear - Hia; induction Hia; cbn; [ split; reflexivity | | ]; destruct IHHia; split; congruence. }
      destruct (IH _ xs' c gs nil nil nil ltac:(cbn; rewrite List.app_nil_r; reflexivity)
                   eq_refl eq_refl Hx Hc eq_refl Ha0 s) as (Vs & HV & HV').
      cbn [nonrec_vals List.app] in HV'; rewrite List.app_nil_r in HV'.
      exists (nf_con p c (nfs_app Ms Vs)); split; (eapply read_nf_con; [ exact Hl | exact Hc | eassumption | | eassumption |]).
      + rewrite List.length_app; lia.
      + rewrite firstn_app_exact by exact Hu; rewrite skipn_app_exact by exact Hb; exact HV.
      + rewrite List.length_app; lia.
      + rewrite firstn_app_exact by exact Hu'; rewrite skipn_app_exact by exact Hb'; exact HV'.
    - intros * _ _ _ _ _ _ Hm xs' _ s; destruct (Hm s) as (L & HL & HL').
      exists (⇑ⁿ L); split; constructor; assumption.
    - intros * _ _ _ _ _ _ _ s; exists nfs_nil; split; constructor.
    - intros * Hia IH xs xs' c gsf gs1 vp vp' Hρ Hl1 Hl2 Hx Hc Heq Ha0 s.
      subst pre gsf.
      set (k := List.length (cargs_nonrec gs1)).
      assert (Hk : List.nth_error (cargs_nonrec (gs1 ++ ca_arg A :: gs)) k = Some A)
        by (unfold k; rewrite cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
      assert (HL : forall w ws wp, List.length wp = List.length gs1 ->
                 nonrec_vals (gs1 ++ ca_arg A :: gs) (wp ++ w :: ws) = nonrec_vals gs1 wp ++ w :: nonrec_vals gs ws)
        by (intros; rewrite nonrec_vals_app by assumption; reflexivity).
      assert (Hpre : tele_pre (ar xs c) k (nonrec_vals gs1 vp) (nonrec_vals gs1 vp'))
        by (exact (nonrec_prefix_gen _ _ _ _ _ _ _ _ eq_refl Hl1 Hl2 Ha0)).
      assert (Hrel : ar xs c k (nonrec_vals gs1 vp) v v').
      { rewrite tele_full_iff in Ha0; destruct Ha0 as (_ & _ & Hr).
        rewrite !HL in Hr by assumption.
        specialize (Hr k v v').
        rewrite !List.nth_error_app2, !length_nonrec_vals, Nat.sub_diag in Hr by (try rewrite length_nonrec_vals; unfold k; lia || assumption).
        specialize (Hr eq_refl eq_refl).
        rewrite (firstn_app_exact (nonrec_vals gs1 vp)) in Hr by (unfold k; apply length_nonrec_vals; assumption).
        exact Hr. }
      destruct (Ha _ _ _ _ _ _ _ _ Hx Hc Hk Hpre) as (a & a' & Ea & Ea' & Hrb).
      destruct (Hrb _ _ Hrel s) as (V & HV & HV').
      assert (Henv : forall us ys wp w, List.length wp = List.length gs1 ->
                 env_args nil (us ++ ys ++ nonrec_vals gs1 wp) ↦ w
                 = env_args nil (us ++ ys ++ nonrec_vals (gs1 ++ ca_arg A :: nil) (wp ++ w :: nil))).
      { intros; rewrite nonrec_vals_app by assumption; cbn; rewrite !List.app_assoc, env_args_snoc; reflexivity. }
      destruct (IH xs xs' c (gs1 ++ ca_arg A :: gs) (gs1 ++ ca_arg A :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil)
                  ltac:(rewrite nonrec_vals_app by assumption; cbn; rewrite List.app_assoc; reflexivity)
                  ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                  Hx Hc ltac:(rewrite <- List.app_assoc; reflexivity) ltac:(rewrite <- !List.app_assoc; exact Ha0) s)
        as (Vs & HVs & HVs').
      exists (nfs_cons V Vs); split; econstructor; try eassumption.
      + rewrite !List.app_assoc, env_args_snoc in HVs; rewrite !List.app_assoc; exact HVs.
      + rewrite Henv by assumption; exact HVs'.
    - intros * Hsh IHs Hia IH xs xs' c gsf gs1 vp vp' Hρ Hl1 Hl2 Hx Hc Heq Ha0 s.
      subst pre gsf.
      pose proof (nonrec_prefix_gen _ _ _ _ _ _ _ _ eq_refl Hl1 Hl2 Ha0) as Hpre.
      destruct (IHs xs xs' c gs1 t gs (nonrec_vals gs1 vp) (nonrec_vals gs1 vp') 0 nil nil
                  ltac:(rewrite List.app_nil_r; reflexivity) Hx Hc Hpre eq_refl ltac:(lia) (tele_pre_nil _) s)
        as (a & a' & V & Ea & Ea' & HV & HV').
      rewrite List.app_nil_r in Ea'.
      destruct (IH xs xs' c (gs1 ++ ca_rec t :: gs) (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil)
                  ltac:(rewrite nonrec_vals_app by assumption; cbn; rewrite List.app_nil_r; reflexivity)
                  ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                  Hx Hc ltac:(rewrite <- List.app_assoc; reflexivity) ltac:(rewrite <- !List.app_assoc; exact Ha0) s)
        as (Vs & HVs & HVs').
      rewrite nonrec_vals_app in HVs' by assumption; cbn in HVs'; rewrite List.app_nil_r in HVs'.
      exists (nfs_cons V Vs); split; econstructor; eassumption.
    - intros * Hb Hr IHr xs xs' c gs1 t0 gs2 ws ws' k0 ys ys' Hρ Hx Hc Hw Hs Hk Hy s.
      destruct (ptyp_skip_self _ _ _ _ Hs) as [Hkd HPs].
      assert (Hyf : tele_full (shape_tr dr xs ws (ptyp_doms t0)) (ptyp_doms t0) ys ys')
        by (destruct Hy as [Hyl Hya]; split; [ lia | exact Hya ]).
      destruct (Hcl xs xs' c _ gs1 t0 gs2 ws ws' ys ys' Hx Hc eq_refl Hw Hyf) as (bs0 & bs1 & E0 & E1 & Hbs).
      rewrite HPs in E0, E1; subst pre.
      pose proof (functional_eval_exps' _ _ _ _ Hb E0) as <-.
      destruct (IHr _ Hbs s) as (V & HV & HV').
      exists (d_ind p (ups ++ bs)), (d_ind p (ups' ++ bs1)), V.
      split; [ constructor; exact Hb | split; [ constructor; exact E1 | split; assumption ] ].
    - intros * Hf IH xs xs' c gs1 t0 gs2 ws ws' k0 ys ys' Hρ Hx Hc Hw Hs Hk Hy s.
      destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB Hs'].
      assert (Hkl : k0 < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence).
      destruct (Hdr xs xs' c _ gs1 t0 gs2 ws ws' k0 B ys ys' Hx Hc eq_refl Hw HB Hy) as (b & b' & Eb & Eb' & Htt & Hbot).
      pose proof (Hbot _ _ (var_per_bot (n := s))) as Hxx.
      subst pre.
      destruct (IH _ _ Hxx xs xs' c gs1 t0 gs2 ws ws' (S k0) (ys ++ ⇑! b s :: nil) (ys' ++ ⇑! b' s :: nil)
                  ltac:(rewrite <- !List.app_assoc; reflexivity) Hx Hc Hw Hs' ltac:(lia)
                  ltac:(apply tele_pre_snoc; [ exact Hy | unfold shape_tr; rewrite (List.nth_error_nth _ _ _ HB); exact Hxx ])
                  (S s))
        as (r & r' & a & a' & V & Er & Er' & Ea & Ea' & HV & HV').
      destruct (Htt s) as (A & HA & HA').
      rewrite !List.app_assoc, env_args_snoc in Ea, Ea'; rewrite <- !List.app_assoc in Ea, Ea'.
      eexists _, _, (λⁿ A V); split; [ econstructor; exact Eb | split; [ econstructor; exact Eb' |] ].
      split; (eapply read_nf_fn; [ eassumption | eassumption | apply eval_fam_cod_shfam; eassumption | eassumption ]).
    - intros * Ef Ef' Hsh IH xs xs' c gs1 t0 gs2 ws ws' k0 ys ys' Hρ Hx Hc Hw Hs Hk Hy s.
      destruct (IH xs xs' c gs1 t0 gs2 ws ws' k0 ys ys' Hρ Hx Hc Hw Hs Hk Hy s) as (a & a' & V & Ea & Ea' & HV & HV').
      exists r, r', a, a', V; repeat split; assumption. }
  intros b b' Hb; exact (proj1 Hmain _ _ _ Hb _ Hns).
Qed.

(** The neutrals of an inductive type at its own parameters are elements. *)
Lemma ind_rel_neut_canon : forall p D ups ups' ns ns'
    (nr : nat -> list domain -> relation domain)
    (ar : list domain -> String.string -> nat -> list domain -> relation domain)
    (dr : list domain -> exp -> relation domain) c c',
    tele_ass (ind_params D) ->
    (forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) -> tele_pre nr k vs vs' -> PER (nr k vs)) ->
    (forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) -> tele_pre nr k vs vs' ->
       (nr k vs <~> nr k vs')) ->
    (forall ms ms' c gs k A vs vs', tele_full nr (List.rev (ind_nparams D)) ms ms' -> ind_con D c = Some gs ->
       List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' -> PER (ar ms c k vs)) ->
    (forall ms ms' c gs k A vs vs', tele_full nr (List.rev (ind_nparams D)) ms ms' -> ind_con D c = Some gs ->
       List.nth_error (cargs_nonrec gs) k = Some A -> tele_pre (ar ms c) k vs vs' -> (ar ms c k vs <~> ar ms' c k vs')) ->
    (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full nr (List.rev (ind_nparams D)) ms ms' ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
       PER (dr (ms ++ ws ++ ys) B)) ->
    (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_full nr (List.rev (ind_nparams D)) ms ms' ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_pre (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_pre (shape_tr dr ms ws (ptyp_doms t)) k ys ys' ->
       (dr (ms ++ ws ++ ys) B <~> dr (ms' ++ ws' ++ ys') B)) ->
    List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
    per_top_ps (List.rev (ind_uparams D)) ups ups' ->
    ind_adm D ups nr ar dr ups' -> ind_adm D ups nr ar dr ups ->
    tele_full nr (List.rev (ind_nparams D)) ns ns' ->
    Dom c ≈ c' ∈ per_bot ->
    ind_rel p D ups nr ar dr ns (⇑ (d_ind p (ups ++ ns)) c) (⇑ (d_ind p (ups' ++ ns')) c').
Proof.
  intros * Hass HnP HnI HaP HaI HdP HdI Hu Hu' Hps Had' Had Hns Hc.
  assert (Hle : ind_nu D <= ind_np D).
  { destruct (Hps 0) as (Ms & HM & _); apply read_ps_length in HM.
    rewrite List.length_rev in HM; unfold ind_uparams in HM; rewrite List.length_skipn in HM.
    unfold ind_nn in HM; unfold ind_np; lia. }
  pose proof Hns as Hl; rewrite tele_full_iff in Hl; destruct Hl as (Hl1 & Hl2 & _).
  rewrite List.length_rev, length_nparams in Hl1, Hl2.
  constructor.
  - rewrite List.length_app; unfold ind_nn in *; lia.
  - rewrite List.length_app; unfold ind_nn in *; lia.
  - rewrite firstn_app_exact by exact Hu; exact Had.
  - rewrite firstn_app_exact by exact Hu'; exact Had'.
  - rewrite skipn_app_exact by exact Hu; exact (tnr_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ Hns).
  - rewrite skipn_app_exact by exact Hu'; exact Hns.
  - exact Hc.
Qed.

Lemma realize_per_univ_elem_gen : forall {i a a' R},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom a ≈ a' ∈ per_top_typ
    /\ (forall {c c'}, Dom c ≈ c' ∈ per_bot -> Dom ⇑ a c ≈ ⇑ a' c' ∈ R)
    /\ (forall {b b'}, Dom b ≈ b' ∈ R -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top).
Proof.
  intros * Hunivelem. simpl in Hunivelem.
  per_univ_elem_induction Hunivelem; repeat split; intros;
    apply_relation_equivalence; mauto.
  - subst; repeat econstructor.
  - subst.
    eexists.
    per_univ_elem_econstructor; (solve [try (try (eexists; split); econstructor); mauto]).
  - subst.
    destruct_by_head per_univ.
    specialize (H2 _ _ _ H0).
    destruct_conjs.
    intro s.
    specialize (H1 s) as [? []]; (solve [try (try (eexists; split); econstructor); mauto]).
  (** The small universes.  They read back as the universe at the canonical
      form their level reads back as, which the two related levels share; the
      other two components are as in the large tier, with the elements at the
      index of the realiser. *)
  - intro s.
    destruct (H0 s) as [W [HW HW']].
    destruct (read_nf_level_real _ _ _ _ HW) as [L [-> _]].
    exists (nf_univ_of L); split; apply read_typ_suniv; assumption.
  - eexists.
    per_univ_elem_econstructor; (solve [try (try (eexists; split); econstructor); mauto]).
  - destruct_by_head per_univ.
    match goal with H : per_univ_elem _ _ _ _ |- _ => specialize (H2 _ _ _ H) end.
    destruct_conjs.
    intro s.
    match goal with H : per_top_typ _ _ |- _ => specialize (H s) as [? []] end;
      (solve [try (try (eexists; split); econstructor); mauto]).
  (** The elements of a type of levels read back at every sort. *)
  - intro s.
    match goal with H : per_lvl_at _ _ _ |- _ => apply per_lvl_at_lvl in H; destruct (H s) as [L [HL HL']] end.
    exists L; split; eapply read_nf_level_sort; eassumption.
  - intro s.
    inversion_clear_by_head per_ne.
    (on_all_hyp: fun H => specialize (H s) as [? []]); (solve [try (try (eexists; split); econstructor); mauto]).
  - destruct IHHunivelem as [? []].
    intro s.
    assert (Dom ⇑! a s ≈ ⇑! a' s ∈ in_rel) by eauto using var_per_bot.
    destruct_rel_mod_eval.
    specialize (H9 (S s)) as [? []].
    specialize (H2 s) as [? []]; (solve [try (try (eexists; split); econstructor); mauto]).
  - intros c0 c0' equiv_c0_c0'.
    destruct_conjs.
    destruct_rel_mod_eval.
    econstructor; try solve [econstructor; eauto].
    enough (Dom c $ᵈ ⇓ a c0 ≈ c' $ᵈ ⇓ a' c0' ∈ per_bot) by eauto.
    intro s.
    specialize (H3 s) as [? []].
    specialize (H5 _ _ equiv_c0_c0' s) as [? []]; (solve [try (try (eexists; split); econstructor); mauto]).
  - destruct_conjs.
    intro s.
    assert (Dom ⇑! a s ≈ ⇑! a' s ∈ in_rel) by eauto using var_per_bot.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    match goal with
    | _: ($| ?f0 & ⇑! a s |↘ _),
        _: ($| ?f0' & ⇑! a' s |↘ _),
          _: (⟦ B ⟧ ρ ↦ ⇑! a s ↘ ?b0),
            _: ⟦ B' ⟧ ρ' ↦ ⇑! a' s ↘ ?b0' |- _ =>
        rename f0 into f;
        rename f0' into f';
        rename b0 into b;
        rename b0' into b'
    end.
    assert (Dom ⇓ b fa ≈ ⇓ b' f'a' ∈ per_top) by eauto.
    specialize (H2 s) as [? []].
    specialize (H16 (S s)) as [? []]; (solve [try (try (eexists; split); econstructor); mauto]).
  - intro s.
    (on_all_hyp: fun H => destruct (H s) as [? []]); (solve [try (try (eexists; split); econstructor); mauto]).
  - intro s.
    inversion_clear_by_head per_ne.
    (on_all_hyp: fun H => specialize (H s) as [? []]); (solve [try (try (eexists; split); econstructor); mauto]).
  (** An inductive type: [realize_ind], from the realisability of the
      types of its telescopes. *)
  - unshelve epose proof (realize_ind p D ups ups' ns ns' nr ar dr H H0 H1 H3 _ _ _ (proj1 (proj2 (proj2 H13))) H15) as [Hrt _];
    [ intros k A vs vs' Hk Hp; destruct (H5 _ _ _ _ Hk Hp) as [a a' Ea Ea' (_ & _ & _ & Hrb)]; eauto
    | intros ms ms' c0 gs k A vs vs' Hm Hc Hk Hp; destruct (H8 _ _ _ _ _ _ _ _ Hm Hc Hk Hp) as [a a' Ea Ea' (_ & _ & _ & Hrb)]; eauto
    | intros ms ms' c0 gs gs1 t gs2 ws ws' k B ys ys' Hm Hc Heq Hw HB Hy;
      destruct (H11 _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy) as [a a' Ea Ea' (_ & Htt & Hbot & _)];
      exists a, a'; repeat split; eauto
    | exact Hrt ].
  - eapply ind_rel_neut_canon; eassumption.
  - unshelve epose proof (realize_ind p D ups ups' ns ns' nr ar dr H H0 H1 H3 _ _ _ (proj1 (proj2 (proj2 H13))) H15) as [_ Hre];
    [ intros k A vs vs' Hk Hp; destruct (H5 _ _ _ _ Hk Hp) as [a a' Ea Ea' (_ & _ & _ & Hrb)]; eauto
    | intros ms ms' c0 gs k A vs vs' Hm Hc Hk Hp; destruct (H8 _ _ _ _ _ _ _ _ Hm Hc Hk Hp) as [a a' Ea Ea' (_ & _ & _ & Hrb)]; eauto
    | intros ms ms' c0 gs gs1 t gs2 ws ws' k B ys ys' Hm Hc Heq Hw HB Hy;
      destruct (H11 _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy) as [a a' Ea Ea' (_ & Htt & Hbot & _)];
      exists a, a'; repeat split; eauto
    | eapply Hre; eassumption ].
Qed.

Corollary per_univ_then_per_top_typ : forall {i a a' R},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom a ≈ a' ∈ per_top_typ.
Proof.
  intros * ?%realize_per_univ_elem_gen; firstorder.
Qed.

Hint Resolve per_univ_then_per_top_typ : mctt.

Corollary per_bot_then_per_elem : forall {i a a' R c c'},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom c ≈ c' ∈ per_bot -> Dom ⇑ a c ≈ ⇑ a' c' ∈ R.
Proof.
  intros * ?%realize_per_univ_elem_gen; firstorder.
Qed.

(** [per_bot_then_per_elem] is not a hint: its conclusion has the relation [R]
    in head position, so the pattern would be higher-order, and Rocq rejects
    it. *)

Corollary per_elem_then_per_top : forall {i a a' R b b'},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom b ≈ b' ∈ R -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top.
Proof.
  intros * ?%realize_per_univ_elem_gen; firstorder.
Qed.

Hint Resolve per_elem_then_per_top : mctt.

Lemma per_ctx_then_per_env_initial_env : forall {Γ Γ' env_rel},
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ env_rel ->
    exists ρ ρ', initial_env_f Γ ρ /\ initial_env_f Γ' ρ' /\ Dom ρ ≈ ρ' ∈ env_rel.
Proof.
  induction 1.
  - do 2 eexists; intuition.
  - destruct_conjs.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    do 2 eexists; repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    eexists.
    eapply per_bot_then_per_elem; eauto.
    erewrite per_ctx_respects_length; mauto.
    eexists; eauto.
  - (** A definition slot holds the value of the body. *)
    destruct IHper_ctx_env as [ρ [ρ' [? [? Hρ]]]].
    assert (Dom ρ ≈ ρ ∈ tail_rel) by solve_per.
    assert (Dom ρ' ≈ ρ' ∈ tail_rel) by solve_per.
    match goal with
    | Hbody : forall ρ ρ' (_ : Dom ρ ≈ ρ' ∈ tail_rel), rel_elem _ _ _ _ _ |- _ =>
        destruct (Hbody _ _ Hρ)
    end.
    do 2 eexists; repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    exists Hρ.
    solve_def_heads.
  - (** A slot holds the closure of its unit, which the premise relates to
        the other unit's. *)
    destruct IHper_ctx_env as [ρ [ρ' [? [? Hρ]]]].
    assert (Dom ρ ≈ ρ ∈ tail_rel) by solve_per.
    assert (Dom ρ' ≈ ρ' ∈ tail_rel) by solve_per.
    match goal with HU : forall ρ ρ', tail_rel ρ ρ' -> rel_mexp _ _ _ _ |- _ =>
      destruct (HU _ _ Hρ) as (h & h' & Hh & Hh' & Hr) end.
    assert (T1 : tie_mod h (me_lit U) ρ)
      by (exists h; split; [ exact Hh | eapply per_dmod_trans; [ exact Hr | apply per_dmod_sym, Hr ] ]).
    assert (T2 : tie_mod h' (me_lit U') ρ')
      by (exists h'; split; [ exact Hh' | eapply per_dmod_trans; [ apply per_dmod_sym, Hr | exact Hr ] ]).
    exists (ρ ↦ᵐ h), (ρ' ↦ᵐ h'); repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    simpl; repeat split; try assumption; unfold env_mod; cbn [env_entry List.hd]; solve_tie.
Qed.

Lemma var_per_elem : forall {a b i R} n,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    Dom ⇑! a n ≈ ⇑! b n ∈ R.
Proof.
  intros.
  eapply per_bot_then_per_elem; mauto.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_then_per_top_typ : mctt.
#[export]
Hint Resolve per_elem_then_per_top : mctt.
