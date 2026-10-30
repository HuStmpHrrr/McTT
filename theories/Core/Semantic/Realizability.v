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

Lemma read_ps_app : forall s ρ T1 vs1 Ms1, Rps vs1 at T1 in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Ms1 ->
    forall T2 vs2 Ms2, Rps vs2 at T2 in gc_deps ⍮ gc_stack ⍮ env_args ρ vs1 ⍮ s ↘ Ms2 ->
    Rps vs1 ++ vs2 at T1 ++ T2 in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ (Ms1 ++ Ms2).
Proof.
  induction 1; intros * H2; cbn [List.app]; [ exact H2 |].
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
    (forall k A pre pre', List.nth_error T k = Some (ce_ass A) -> tele_prefix_rel tr k pre pre' ->
       exists a a', ⟦ A ⟧ env_args ρ pre ↘ a /\ ⟦ A ⟧ env_args ρ' pre' ↘ a' /\
         (forall b b', tr k pre b b' -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top)) ->
    forall vs vs', tele_rel tr T vs vs' ->
    forall s, exists Ms, Rps vs at T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Ms /\ Rps vs' at T in gc_deps ⍮ gc_stack ⍮ ρ' ⍮ s ↘ Ms.
Proof.
  intros * Hass Hev vs vs' Hf s.
  pose proof Hf as Hf'; rewrite tele_rel_iff in Hf'; destruct Hf' as (Hl & Hl' & Hr).
  assert (Hall : forall m j, m + j = List.length T ->
             exists Ms, Rps List.skipn j vs at List.skipn j T in gc_deps ⍮ gc_stack ⍮ env_args ρ (List.firstn j vs) ⍮ s ↘ Ms /\
                        Rps List.skipn j vs' at List.skipn j T in gc_deps ⍮ gc_stack ⍮ env_args ρ' (List.firstn j vs') ⍮ s ↘ Ms).
  { induction m as [| m IH]; intros j Hj.
    - rewrite !List.skipn_all2 by lia; exists nil; split; constructor.
    - destruct (nth_error_lt_some' T j ltac:(lia)) as [e He].
      destruct (nth_error_lt_some' vs j ltac:(lia)) as [v Hv].
      destruct (nth_error_lt_some' vs' j ltac:(lia)) as [v' Hv'].
      assert (He' : exists A, e = ce_ass A)
        by (unfold tele_ass in Hass; rewrite List.Forall_forall in Hass; apply Hass; eapply List.nth_error_In; exact He).
      destruct He' as [A ->].
      destruct (Hev _ _ _ _ He (tele_prefix_rel_of_full _ _ _ _ j Hf ltac:(lia))) as (a & a' & Ea & Ea' & Hrb).
      destruct (Hrb _ _ (Hr _ _ _ Hv Hv') s) as (V & HV & HV').
      destruct (IH (S j) ltac:(lia)) as (Ms & HM & HM').
      rewrite (firstn_S_snoc _ _ _ Hv), env_args_snoc in HM.
      rewrite (firstn_S_snoc _ _ _ Hv'), env_args_snoc in HM'.
      exists (cons V Ms).
      rewrite (skipn_nth_cons' _ _ _ He), (skipn_nth_cons' _ _ _ Hv), (skipn_nth_cons' _ _ _ Hv').
      split; econstructor; eassumption. }
  destruct (Hall (List.length T) 0 ltac:(lia)) as (Ms & HM & HM'); exists Ms; split; assumption.
Qed.

Lemma rev_im_params_split : forall D M, List.rev (im_params D M) = List.rev (ind_uparams D) ++ List.rev (im_nparams M).
Proof. intros; unfold im_params; rewrite List.rev_app_distr; reflexivity. Qed.

Lemma read_ps_length : forall s ρ T vs Ms, Rps vs at T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Ms -> List.length vs = List.length T.
Proof. induction 1; cbn; congruence. Qed.

(** The codomain of the type of an argument of a function shape, at an
    argument. *)
Lemma eval_fam_cod_shfam : forall p ups ρ t x a,
    ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↦ x ↘ a ->
    ⟦ fam_cod ⟧ nil ↦ d_shfam p ups ρ t ↦ x ↘ a.
Proof.
  intros; unfold fam_cod; eapply eval_exp_app; [ apply eval_exp_var | reflexivity | apply eval_exp_var | econstructor; eassumption ].
Qed.

(** The type of a shape is relevant: a member, a record or a [Π]. *)
Lemma eval_shape_type_relevant : forall p ups ρ t a,
    ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ a -> domain_relevance a = relevant.
Proof. intros * H; inversion H; reflexivity. Qed.

Lemma eval_fam_cod_ihfam : forall ρm A p ups ρ t i f x fx as' a,
    $| f & x | gc_deps ⍮ gc_stack ↘ fx ->
    ⟦ihty fx of t at p ups under ρm A ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↦ x ↘ as' ->
    List.nth_error as' i = Some a ->
    ⟦ fam_cod ⟧ nil ↦ d_ihfam ρm A p ups ρ t i f ↦ x ↘ a.
Proof.
  intros; unfold fam_cod; eapply eval_exp_app; [ apply eval_exp_var | reflexivity | apply eval_exp_var | econstructor; eassumption ].
Qed.

Lemma env_args_snoc3 : forall (u a b c : list domain) x,
    env_args nil (u ++ a ++ b ++ c ++ x :: nil) = env_args nil (u ++ a ++ b ++ c) ↦ x.
Proof. intros; rewrite !List.app_assoc, env_args_snoc; reflexivity. Qed.

(** The realisability of a member of a group of inductive types, from that
    of the types of the group's telescopes.  An element is read back at the
    type's parameters, while it is related at its own.  A constructor of a
    view is read at the view's own telescopes ([read_nf_con_view]), as one
    of a declared member is at its own, so the two cases are one.  A
    recursive argument's index at the type's prefix is related to the
    element's own through the index at the element's own prefix ([admissible_index_at]),
    the two prefixes related by the admissibility of the type's uniform
    parameters beside themselves ([Hcd]) and beside the other side's
    ([Hcl]). *)
Lemma realize_indty : forall p D ups ups'
    (nr : nat -> nat -> list domain -> relation domain)
    (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (dr : nat -> list domain -> exp -> relation domain),
    ind_lookup gc_deps gc_stack p = Some D ->
    grp_tele_ass D ->
    List.length ups = ind_nu D ->
    per_top_ps (List.rev (ind_uparams D)) ups ups' ->
    nparams_per D nr -> nparams_inv D nr -> args_per D nr ar -> args_inv D nr ar ->
    doms_per D nr ar dr -> doms_inv D nr ar dr ->
    (forall m Mm k A vs vs', ind_member D m = Some Mm ->
       List.nth_error (List.rev (im_nparams Mm)) k = Some (ce_ass A) -> tele_prefix_rel (nr m) k vs vs' ->
       exists a a', ⟦ A ⟧ env_args nil (ups ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups' ++ vs') ↘ a' /\
         (forall b b', nr m k vs b b' -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top)) ->
    (forall m Mm ms ms' c gs k A vs vs', ind_member D m = Some Mm ->
       tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' -> ind_con Mm c = Some gs ->
       List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar m ms c) k vs vs' ->
       exists a a', ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups' ++ ms' ++ vs') ↘ a' /\
         (forall b b', ar m ms c k vs b b' -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top)) ->
    (forall m Mm ms ms' c gs gs1 t gs2 ws ws' k B ys ys', ind_member D m = Some Mm ->
       tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' ->
       ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
       List.nth_error (ptyp_doms t) k = Some B ->
       tele_prefix_rel (shape_doms_rel (dr m) ms ws (ptyp_doms t)) k ys ys' ->
       exists a a', ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ a /\ ⟦ B ⟧ env_args nil (ups' ++ ms' ++ ws' ++ ys') ↘ a' /\
         Dom a ≈ a' ∈ per_top_typ /\
         (forall c c', Dom c ≈ c' ∈ per_bot -> dr m (ms ++ ws ++ ys) B (relevant_value a (⇑ a c)) (relevant_value a' (⇑ a' c')))) ->
    adm_uparams D ups nr ar dr ups' ->
    adm_uparams D ups nr ar dr ups ->
    forall k Mk ns ns', ind_member D k = Some Mk ->
    tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns' ->
    Dom d_ind p k (ups ++ ns) ≈ d_ind p k (ups' ++ ns') ∈ per_top_typ /\
    (forall u u' b b', ind_rel p D (admissible_index_at D ups nr) nr ar dr k u u' ns ns' b b' ->
       Dom ⇓ (d_ind p k (ups ++ ns)) b ≈ ⇓ (d_ind p k (ups' ++ ns')) b' ∈ per_top).
Proof.
  intros * Hl Hass Hu Hps HnP HnI HaP HaI HdP HdI Hn Ha Hdr Hcl Hcd.
  assert (Hu' : List.length ups' = ind_nu D).
  { destruct (Hps 0) as (Ms & _ & HM); apply read_ps_length in HM.
    rewrite List.length_rev in HM; unfold ind_nu; lia. }
  assert (Hpar : forall m Mm xs xs', ind_member D m = Some Mm -> tele_rel (nr m) (List.rev (im_nparams Mm)) xs xs' ->
             per_top_ps (List.rev (im_params D Mm)) (ups ++ xs) (ups' ++ xs')).
  { intros m Mm xs xs' HM Hx s.
    destruct (Hps s) as (Ms1 & HM1 & HM1').
    assert (Hassn : tele_ass (List.rev (im_nparams Mm)))
      by (apply List.Forall_rev; exact (grp_tele_ass_nparams _ Hass _ _ HM)).
    destruct (read_ps_tele (List.rev (im_nparams Mm)) (nr m) (env_args nil ups) (env_args nil ups') Hassn
                ltac:(intros k A pre pre' Hk Hp; rewrite <- !env_args_app; exact (Hn _ _ _ _ _ _ HM Hk Hp))
                _ _ Hx s) as (Ms2 & HM2 & HM2').
    exists (Ms1 ++ Ms2)%list; rewrite rev_im_params_split; split; apply read_ps_app; assumption. }
  assert (Hlen : forall m Mm xs xs', ind_member D m = Some Mm -> tele_rel (nr m) (List.rev (im_nparams Mm)) xs xs' ->
             List.length (ups ++ xs) = im_np D Mm /\ List.length (ups' ++ xs') = im_np D Mm).
  { intros m Mm xs xs' HM Hx; rewrite tele_rel_iff in Hx; destruct Hx as (Hl1 & Hl2 & _).
    rewrite List.length_rev in Hl1, Hl2; rewrite !List.length_app; unfold im_np, im_nn; lia. }
  pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
  pose proof (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as ttrans.
  pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl.
  pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl_r.
  pose proof (args_prefix_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tarpi.
  pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tarpl.
  pose proof (args_prefix_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tarpr.
  pose proof (doms_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tshi.
  pose proof (doms_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tshl.
  pose proof (doms_rel_refl_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tshri.
  pose proof (nparams_tele_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as ntsym.
  pose proof (nparams_tele_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as nttrans.
  (** The elements are read back at indices [xs] and [xs'] related to their
      own, the arguments and shapes after values of the type's parameters
      [xs] and [xs'] related to their own [ms] and [ms']. *)
  assert (Hmain :
    (forall k u u' ns0 ns0' x y, ind_rel p D (admissible_index_at D ups nr) nr ar dr k u u' ns0 ns0' x y ->
       forall Mk xs xs', ind_member D k = Some Mk ->
         tele_rel (nr k) (List.rev (im_nparams Mk)) xs ns0 -> tele_rel (nr k) (List.rev (im_nparams Mk)) xs' ns0' ->
         Dom ⇓ (d_ind p k (ups ++ xs)) x ≈ ⇓ (d_ind p k (ups' ++ xs')) y ∈ per_top) /\
    (forall k u u' pre pre' gs vs vs', con_args_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' gs vs vs' ->
       forall Mk ms ms' xs xs' c gsf gs1 vp vp', ind_member D k = Some Mk ->
         pre = ms ++ nonrec_arg_vals gs1 vp -> pre' = ms' ++ nonrec_arg_vals gs1 vp' ->
         List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
         tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms' ->
         tele_rel (nr k) (List.rev (im_nparams Mk)) xs ms -> tele_rel (nr k) (List.rev (im_nparams Mk)) xs' ms' ->
         ind_con Mk c = Some gsf -> gsf = gs1 ++ gs ->
         tele_rel (ar k ms c) (cargs_nonrec gsf) (nonrec_arg_vals gsf (vp ++ vs)) (nonrec_arg_vals gsf (vp' ++ vs')) ->
         forall s, exists Vs,
           Rcargs vs at gs of p ups in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ xs ++ nonrec_arg_vals gs1 vp) ⍮ s ↘ Vs /\
           Rcargs vs' at gs of p ups' in gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ xs' ++ nonrec_arg_vals gs1 vp') ⍮ s ↘ Vs) /\
    (forall k u u' pre pre' t v v', rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' t v v' ->
       forall Mk ms ms' xs xs' c gs1 t0 gs2 ws ws' kk ys ys', ind_member D k = Some Mk ->
         pre = ms ++ ws ++ ys -> pre' = ms' ++ ws' ++ ys' ->
         tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms' ->
         tele_rel (nr k) (List.rev (im_nparams Mk)) xs ms -> tele_rel (nr k) (List.rev (im_nparams Mk)) xs' ms' ->
         ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
         tele_prefix_rel (ar k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
         ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
         tele_prefix_rel (shape_doms_rel (dr k) ms ws (ptyp_doms t0)) kk ys ys' ->
         forall s, exists V, Rsh v at t of p ups in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ xs ++ ws ++ ys) ⍮ s ↘ V /\
           Rsh v' at t of p ups' in gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ xs' ++ ws' ++ ys') ⍮ s ↘ V) /\
    (forall k u u' pre pre' t f x f' x', rec_arg_app_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' t f x f' x' ->
       forall Mk ms ms' xs xs' c gs1 t0 gs2 ws ws' kk ys ys', ind_member D k = Some Mk ->
         pre = ms ++ ws ++ ys -> pre' = ms' ++ ws' ++ ys' ->
         tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms' ->
         tele_rel (nr k) (List.rev (im_nparams Mk)) xs ms -> tele_rel (nr k) (List.rev (im_nparams Mk)) xs' ms' ->
         ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
         tele_prefix_rel (ar k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
         ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
         tele_prefix_rel (shape_doms_rel (dr k) ms ws (ptyp_doms t0)) kk ys ys' ->
         forall s, exists r r' V, $| f & x | gc_deps ⍮ gc_stack ↘ r /\ $| f' & x' | gc_deps ⍮ gc_stack ↘ r' /\
           Rsh r at t of p ups in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ xs ++ ws ++ ys) ⍮ s ↘ V /\
           Rsh r' at t of p ups' in gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ xs' ++ ws' ++ ys') ⍮ s ↘ V)).
  { apply ind_rel_mut_ind_all.
    - (** A constructor: its parameters off the type, its arguments at the
          member's telescopes, at a declared member or a view alike. *)
      intros k0 Mk0 hd k' ns0 ns0' c gs bs bs' vs vs' u u' HM Hrv Hr Hn0 Hc Hb Hb' Hs Hs' Ha0 Hia IH Mk1 xs xs' HM1 Hx Hx' s.
      rewrite HM in HM1; injection HM1 as <-.
      assert (Hxx : tele_rel (nr k0) (List.rev (im_nparams Mk0)) xs xs')
        by exact (ttrans _ _ HM _ _ _ Hx (ttrans _ _ HM _ _ _ Hn0 (tsym _ _ HM _ _ Hx'))).
      destruct (Hpar _ _ _ _ HM Hxx s) as (Ms & HMs & HMs').
      destruct (Hlen _ _ _ _ HM Hxx) as [Hl1 Hl2].
      assert (Hvl : List.length vs = List.length gs /\ List.length vs' = List.length gs).
      { clear - Hia; induction Hia; cbn; [ split; reflexivity | | ]; destruct IHHia; split; congruence. }
      destruct (IH Mk0 (List.skipn (im_unu D Mk0) bs) (List.skipn (im_unu D Mk0) bs') xs xs' c gs nil nil nil HM
                   ltac:(cbn; rewrite List.app_nil_r; reflexivity) ltac:(cbn; rewrite List.app_nil_r; reflexivity)
                   eq_refl eq_refl
                   (ttrans _ _ HM _ _ _ (ttrans _ _ HM _ _ _ (tsym _ _ HM _ _ Hs) Hn0) Hs')
                   (ttrans _ _ HM _ _ _ Hx Hs) (ttrans _ _ HM _ _ _ Hx' Hs') Hc eq_refl Ha0 s) as (Vs & HV & HV').
      cbn [nonrec_arg_vals List.app] in HV, HV'; rewrite List.app_nil_r in HV, HV'.
      unfold im_ref in Hr; destruct (im_head Mk0) as [pm | qc kc Is vm | qr Is fl] eqn:Hh; injection Hr as <- <-;
        [| | exfalso; exact (not_rview_record _ _ _ _ Hrv Hh) ].
      + assert (Hu0 : im_unu D Mk0 = ind_nu D) by (unfold im_unu; rewrite Hh; reflexivity).
        exists (nf_con p k0 c (Ms ++ Vs)%list); split;
          (eapply read_nf_con; [ exact Hl | exact HM | exact Hh | exact Hc | eassumption | | eassumption |]).
        * rewrite List.length_app; unfold im_np, im_nn in *; lia.
        * rewrite firstn_app_exact by exact Hu; rewrite skipn_app_exact by (unfold im_np, im_nn in *; lia); exact HV.
        * rewrite List.length_app; unfold im_np, im_nn in *; lia.
        * rewrite firstn_app_exact by exact Hu'; rewrite skipn_app_exact by (unfold im_np, im_nn in *; lia); exact HV'.
      + exists (nf_con p k0 c (Ms ++ Vs)%list); split.
        * eapply read_nf_con_view with (n := List.length bs);
            [ exact Hl | exact HM | exact Hh | exact Hc | exact Hl1 | rewrite List.length_app; lia | exact HMs |].
          rewrite firstn_app_exact by exact Hu; rewrite skipn_app_exact by reflexivity; exact HV.
        * eapply read_nf_con_view with (n := List.length bs');
            [ exact Hl | exact HM | exact Hh | exact Hc | exact Hl2 | rewrite List.length_app; lia | exact HMs' |].
          rewrite firstn_app_exact by exact Hu'; rewrite skipn_app_exact by reflexivity; exact HV'.
    - intros k0 Mk0 hd k' ns0 ns0' as1 as2 m m' _ _ HM Hrv _ _ _ _ _ _ Hm Mk1 xs xs' _ _ _ s; destruct (Hm s) as (L & HL & HL').
      exists (⇑ⁿ L); split; (eapply read_nf_ind_neut; [ exact Hl | exact HM | exact Hrv | exact HL || exact HL' ]).
    - (** A record view: its projections at the pseudo-constructor's
          arguments, at the group's uniform parameters only. *)
      intros k0 Mk0 qr Is fl c gs v vs v' vs' u u' HM Hh Hnp Hcs Hp Hp' Ha0 Hia IH Mk1 xs xs' HM1 Hx Hx' s.
      rewrite HM in HM1; injection HM1 as <-.
      pose proof (ind_con_single _ _ _ Hcs) as Hc.
      assert (Hn0 : tele_rel (nr k0) (List.rev (im_nparams Mk0)) nil nil) by (rewrite Hnp; split; reflexivity + exact I).
      assert (Hxs : forall zs, tele_rel (nr k0) (List.rev (im_nparams Mk0)) zs nil -> zs = nil)
        by (intros zs [Hz _]; rewrite Hnp in Hz; destruct zs; [ reflexivity | discriminate Hz ]).
      rewrite (Hxs _ Hx), (Hxs _ Hx') in *; rewrite !List.app_nil_r.
      destruct (IH Mk0 nil nil nil nil c gs nil nil nil HM eq_refl eq_refl eq_refl eq_refl Hn0 Hn0 Hn0 Hc eq_refl Ha0 s)
        as (Vs & HV & HV').
      cbn [nonrec_arg_vals List.app] in HV, HV'; rewrite List.app_nil_r in HV, HV'.
      destruct (Hps s) as (Ms & HMs & HMs').
      exists (nf_con p k0 c (Ms ++ Vs)%list); split;
        (eapply read_nf_rview; [ exact Hl | exact HM | exact Hh | exact Hcs | | eassumption | eassumption | eassumption ]);
        assumption.
    - intros; exists nil; split; constructor.
    - intros k0 u u' pre v pre' v' gs vs vs' rA A Hia IH Mk0 ms ms' xs xs' c gsf gs1 vp vp' HM Hρ Hρ' Hl1 Hl2 Hm Hx Hx'
        Hc Heq Ha0 s.
      subst pre pre' gsf.
      set (k := List.length (cargs_nonrec gs1)).
      assert (Hk : List.nth_error (cargs_nonrec (gs1 ++ ca_arg rA A :: gs)) k = Some A)
        by (unfold k; rewrite cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
      assert (Hkle : k <= List.length (cargs_nonrec (gs1 ++ ca_arg rA A :: gs)))
        by (unfold k; rewrite cargs_nonrec_app, List.length_app; lia).
      assert (HL : forall w ws wp, List.length wp = List.length gs1 ->
                 nonrec_arg_vals (gs1 ++ ca_arg rA A :: gs) (wp ++ w :: ws) = nonrec_arg_vals gs1 wp ++ w :: nonrec_arg_vals gs ws)
        by (intros; rewrite nonrec_arg_vals_app by assumption; reflexivity).
      assert (Hpre : tele_prefix_rel (ar k0 ms c) k (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp'))
        by (exact (nonrec_prefix_gen _ _ _ _ _ _ _ _ eq_refl Hl1 Hl2 Ha0)).
      assert (Hrel : ar k0 ms c k (nonrec_arg_vals gs1 vp) v v').
      { rewrite tele_rel_iff in Ha0; destruct Ha0 as (_ & _ & Hr).
        rewrite !HL in Hr by assumption.
        specialize (Hr k v v').
        rewrite !List.nth_error_app2, !length_nonrec_arg_vals, Nat.sub_diag in Hr by (try rewrite length_nonrec_arg_vals; unfold k; lia || assumption).
        specialize (Hr eq_refl eq_refl).
        rewrite (firstn_app_exact (nonrec_arg_vals gs1 vp)) in Hr by (unfold k; apply length_nonrec_arg_vals; assumption).
        exact Hr. }
      pose proof (trefl _ _ HM _ _ Hm) as Hmm.
      pose proof (tsym _ _ HM _ _ Hx) as Hmx.
      pose proof (tarpl _ _ HM ms c _ Hmm Hc k _ _ Hkle Hpre) as Hpp.
      assert (Hrel' : ar k0 xs c k (nonrec_arg_vals gs1 vp) v v')
        by exact (proj1 (HaI _ _ _ _ _ _ _ _ _ _ HM Hmx Hc Hk Hpp _ _) Hrel).
      assert (Hxx : tele_rel (nr k0) (List.rev (im_nparams Mk0)) xs xs')
        by exact (ttrans _ _ HM _ _ _ Hx (ttrans _ _ HM _ _ _ Hm (tsym _ _ HM _ _ Hx'))).
      pose proof (tarpi _ _ HM _ _ _ _ _ _ _ Hmx Hc Hkle Hpre) as Hprex.
      destruct (Ha _ _ _ _ _ _ _ _ _ _ HM Hxx Hc Hk Hprex) as (a & a' & Ea & Ea' & Hrb).
      destruct (Hrb _ _ Hrel' s) as (V & HV & HV').
      assert (Henv : forall us ys wp w, List.length wp = List.length gs1 ->
                 env_args nil (us ++ ys ++ nonrec_arg_vals gs1 wp) ↦ w
                 = env_args nil (us ++ ys ++ nonrec_arg_vals (gs1 ++ ca_arg rA A :: nil) (wp ++ w :: nil))).
      { intros; rewrite nonrec_arg_vals_app by assumption; cbn; rewrite !List.app_assoc, env_args_snoc; reflexivity. }
      destruct (IH Mk0 ms ms' xs xs' c (gs1 ++ ca_arg rA A :: gs) (gs1 ++ ca_arg rA A :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil) HM
                  ltac:(rewrite nonrec_arg_vals_app by assumption; cbn; rewrite List.app_assoc; reflexivity)
                  ltac:(rewrite nonrec_arg_vals_app by assumption; cbn; rewrite List.app_assoc; reflexivity)
                  ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                  Hm Hx Hx' Hc ltac:(rewrite <- List.app_assoc; reflexivity) ltac:(rewrite <- !List.app_assoc; exact Ha0) s)
        as (Vs & HVs & HVs').
      exists (cons V Vs); split; econstructor; try eassumption.
      + rewrite Henv by assumption; exact HVs.
      + rewrite Henv by assumption; exact HVs'.
    - intros k0 u u' pre pre' t v v' gs vs vs' Hsh IHs Hia IH Mk0 ms ms' xs xs' c gsf gs1 vp vp' HM Hρ Hρ' Hl1 Hl2 Hm Hx Hx'
        Hc Heq Ha0 s.
      subst pre pre' gsf.
      pose proof (nonrec_prefix_gen _ _ _ _ _ _ _ _ eq_refl Hl1 Hl2 Ha0) as Hpre.
      destruct (IHs Mk0 ms ms' xs xs' c gs1 t gs (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp') 0 nil nil HM
                  ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity)
                  Hm Hx Hx' Hc Hpre eq_refl ltac:(lia) (tele_prefix_rel_nil _) s)
        as (V & HV & HV').
      rewrite List.app_nil_r in HV, HV'.
      destruct (IH Mk0 ms ms' xs xs' c (gs1 ++ ca_rec t :: gs) (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil) HM
                  ltac:(rewrite nonrec_arg_vals_app by assumption; cbn; rewrite List.app_nil_r; reflexivity)
                  ltac:(rewrite nonrec_arg_vals_app by assumption; cbn; rewrite List.app_nil_r; reflexivity)
                  ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                  Hm Hx Hx' Hc ltac:(rewrite <- List.app_assoc; reflexivity) ltac:(rewrite <- !List.app_assoc; exact Ha0) s)
        as (Vs & HVs & HVs').
      rewrite nonrec_arg_vals_app in HVs, HVs' by assumption; cbn in HVs, HVs'; rewrite List.app_nil_r in HVs, HVs'.
      exists (cons V Vs); split; econstructor; eassumption.
    - (** The end of a shape: the index at the type's prefix is related to
          the element's own through the index at the element's own prefix
          ([admissible_index_at]), the two prefixes related by [Hcd] on the left and by
          [Hcl] on the right. *)
      intros Ps u pre bs u' pre' bs' j v v' k0 _ _ O O' Hr IHr Mk0 ms ms' xs xs' c gs1 t0 gs2 ws ws' k1 ys ys'
        HM Hρ Hρ' Hm Hx Hx' Hc Hw Hs Hk Hy s.
      destruct (ptyp_skip_self _ _ _ _ Hs) as (Hkd & Hj & HPs).
      subst pre pre'.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (trefl _ _ HM _ _ Hm) as Hmm.
      pose proof (tsym _ _ HM _ _ Hx) as Hmx.
      pose proof (tsym _ _ HM _ _ Hx') as Hmx'.
      pose proof (tarpl _ _ HM ms c _ Hmm Hc _ ws ws' HK Hw) as Hww.
      pose proof (tarpi _ _ HM _ _ _ _ _ _ _ Hmx Hc HK Hww) as Hwx.
      pose proof (tarpr _ _ HM _ _ _ _ _ _ _ Hm Hc HK Hw) as Hw'.
      pose proof (tshl _ _ HM ms c _ gs1 t0 gs2 ws Hmm Hc eq_refl Hww k1 ys ys' Hk Hy) as Hyy.
      pose proof (tshi _ _ HM _ _ _ _ _ _ _ _ _ _ _ _ Hmx Hc eq_refl Hww Hk Hyy) as Hyx.
      pose proof (tshri _ _ HM _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc eq_refl Hw Hk Hy) as Hy'.
      assert (Hyxf : tele_rel (shape_doms_rel (dr k0) xs ws (ptyp_doms t0)) (ptyp_doms t0) ys ys)
        by (destruct Hyx as [Hyl Hya]; split; [ lia | exact Hya ]).
      assert (Hyf' : tele_rel (shape_doms_rel (dr k0) ms' ws' (ptyp_doms t0)) (ptyp_doms t0) ys' ys')
        by (destruct Hy' as [Hyl Hya]; split; [ lia | exact Hya ]).
      destruct O as [idx Ei Ri]; destruct O' as [idx' Ei' Ri'].
      destruct (adm_rec_params _ _ _ _ _ _ Hcd k0 Mk0 xs ms c _ gs1 t0 gs2 ws ws ys ys HM Hx Hc eq_refl Hwx Hyxf)
        as [bT b0 ET E0 RT].
      destruct (adm_rec_params _ _ _ _ _ _ Hcl k0 Mk0 ms' xs' c _ gs1 t0 gs2 ws' ws' ys' ys' HM Hmx' Hc eq_refl Hw' Hyf')
        as [b1 bT' E1 ET' RT'].
      rewrite HPs in ET, E0, E1, ET'; rewrite Hj in RT, RT'.
      pose proof (functional_eval_exps' _ _ _ _ E0 Ei) as <-.
      pose proof (functional_eval_exps' _ _ _ _ E1 Ei') as <-.
      pose proof (nttrans _ _ _ _ RT Ri) as Rb.
      pose proof (nttrans _ _ _ _ (ntsym _ _ _ RT') Ri') as Rb'.
      destruct (nparams_tele_rel_member p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ Rb) as (Mj & HMj & Hb1).
      destruct (nparams_tele_rel_member p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ Rb') as (Mj' & HMj' & Hb2).
      rewrite HMj in HMj'; injection HMj' as <-.
      destruct (IHr Mj bT bT' HMj Hb1 Hb2 s) as (V & HV & HV').
      exists V; split; econstructor; eassumption.
    - (** A domain of a shape: its variables are related at the type's
          parameters, hence at the element's own ([HdI]). *)
      intros k0 pre B u u' pre' t f f' Hf IH Mk0 ms ms' xs xs' c gs1 t0 gs2 ws ws' k1 ys ys' HM Hρ Hρ' Hm Hx Hx' Hc Hw Hs Hk
        Hy s.
      destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB Hs'].
      assert (Hkl : k1 < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence).
      subst pre pre'.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (trefl _ _ HM _ _ Hm) as Hmm.
      pose proof (tsym _ _ HM _ _ Hx) as Hmx.
      pose proof (tarpl _ _ HM ms c _ Hmm Hc _ ws ws' HK Hw) as Hww.
      pose proof (tarpi _ _ HM _ _ _ _ _ _ _ Hmx Hc HK Hw) as Hwx.
      pose proof (tshi _ _ HM _ _ _ _ _ _ _ _ _ _ _ _ Hmx Hc eq_refl Hww Hk Hy) as Hyx.
      pose proof (ttrans _ _ HM _ _ _ Hx (ttrans _ _ HM _ _ _ Hm (tsym _ _ HM _ _ Hx'))) as Hxx.
      destruct (Hdr k0 Mk0 xs xs' c _ gs1 t0 gs2 ws ws' k1 B ys ys' HM Hxx Hc eq_refl Hwx HB Hyx)
        as (b & b' & Eb & Eb' & Htt & Hbot).
      pose proof (Hbot _ _ (var_per_bot (n := s))) as Hxv.
      pose proof (tshl _ _ HM ms c _ gs1 t0 gs2 ws Hmm Hc eq_refl Hww k1 ys ys' Hk Hy) as Hyy.
      pose proof (proj2 (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hmx Hc eq_refl Hww HB Hyy _ _) Hxv) as Hxv'.
      destruct (IH _ _ Hxv' Mk0 ms ms' xs xs' c gs1 t0 gs2 ws ws' (S k1) (ys ++ relevant_value b (⇑! b s) :: nil)
                  (ys' ++ relevant_value b' (⇑! b' s) :: nil) HM
                  ltac:(rewrite <- !List.app_assoc; reflexivity) ltac:(rewrite <- !List.app_assoc; reflexivity)
                  Hm Hx Hx' Hc Hw Hs' ltac:(lia)
                  ltac:(apply tele_prefix_rel_snoc; [ exact Hy | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hxv' ])
                  (S s))
        as (r & r' & V & Er & Er' & HV & HV').
      destruct (Htt s) as (A & HA & HA').
      rewrite !List.app_assoc, env_args_snoc in HV, HV'; rewrite <- !List.app_assoc in HV, HV'.
      exists (λⁿ A V); split; econstructor; eassumption.
    - intros f x r f' x' r' k0 u u' pre pre' t Ef Ef' Hsh IH Mk0 ms ms' xs xs' c gs1 t0 gs2 ws ws' k1 ys ys'
        HM Hρ Hρ' Hm Hx Hx' Hc Hw Hs Hk Hy s.
      destruct (IH Mk0 ms ms' xs xs' c gs1 t0 gs2 ws ws' k1 ys ys' HM Hρ Hρ' Hm Hx Hx' Hc Hw Hs Hk Hy s)
        as (V & HV & HV').
      exists r, r', V; repeat split; assumption. }
  intros k Mk ns ns' HMk Hns; split.
  { intros s; destruct (Hpar _ _ _ _ HMk Hns s) as (Ms & HM & HM').
    destruct (Hlen _ _ _ _ HMk Hns) as [Hl1 Hl2].
    exists (nf_indty p k Ms); split; econstructor; eassumption. }
  intros u u' b b' Hb; exact (proj1 Hmain _ _ _ _ _ _ _ Hb _ _ _ HMk (trefl _ _ HMk _ _ Hns) (trefl_r _ _ HMk _ _ Hns)).
Qed.

(** The neutrals of a declared member at the type's own parameters are
    elements, when its uniform parameters are admissible. *)
Lemma ind_rel_neut_canon : forall p D ups ups'
    (nr : nat -> nat -> list domain -> relation domain)
    (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (dr : nat -> list domain -> exp -> relation domain)
    (okr : nat -> list domain -> list exp -> list domain -> Prop)
    k Mk pm ns ns' c c',
    grp_tele_ass D ->
    nparams_per D nr -> nparams_inv D nr -> args_per D nr ar -> args_inv D nr ar ->
    doms_per D nr ar dr -> doms_inv D nr ar dr ->
    ind_member D k = Some Mk -> im_head Mk = mh_decl pm ->
    List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
    tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns' ->
    Dom c ≈ c' ∈ per_bot ->
    ind_rel p D okr nr ar dr k ups ups' ns ns' (⇑ (d_ind p k (ups ++ ns)) c) (⇑ (d_ind p k (ups' ++ ns')) c').
Proof.
  intros * Hass HnP HnI HaP HaI HdP HdI HM Hh Hu Hu' Hns Hc.
  pose proof Hns as Hl; rewrite tele_rel_iff in Hl; destruct Hl as (Hl1 & Hl2 & _).
  rewrite List.length_rev in Hl1, Hl2.
  assert (Hu0 : im_unu D Mk = ind_nu D) by (unfold im_unu; rewrite Hh; reflexivity).
  eapply ind_rel_neut; [ exact HM | unfold im_is_rview; rewrite Hh; reflexivity | unfold im_ref; rewrite Hh; reflexivity | exact Hns | | | | | exact Hc ];
    rewrite Hu0.
  - rewrite List.length_app; unfold im_np, im_nn; lia.
  - rewrite List.length_app; unfold im_np, im_nn; lia.
  - rewrite skipn_app_exact by exact Hu;
      exact (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns).
  - rewrite skipn_app_exact by exact Hu';
      exact (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ Hns).
Qed.

(** ** Record Types *)

(** The neutral projections of a prefix of the fields are the prefix of
    the neutral projections. *)
Lemma eval_neutral_fields_firstn : forall ns m fl pre rs, eval_neutral_fields gc_deps gc_stack ns m fl pre rs ->
    forall n, eval_neutral_fields gc_deps gc_stack ns m (List.firstn n fl) pre (List.firstn n rs).
Proof.
  induction 1; intros [| n]; cbn [List.firstn]; econstructor; eauto.
Qed.

Lemma eval_neutral_fields_length : forall ns m fl pre rs, eval_neutral_fields gc_deps gc_stack ns m fl pre rs ->
    List.length rs = List.length fl.
Proof. induction 1; cbn; congruence. Qed.

Lemma Forall2_of_nth : forall {X Y} (P : X -> Y -> Prop) l1 l2, List.length l1 = List.length l2 ->
    (forall k x y, List.nth_error l1 k = Some x -> List.nth_error l2 k = Some y -> P x y) -> List.Forall2 P l1 l2.
Proof.
  induction l1 as [| x l1 IH]; intros [| y l2] Hl H; cbn in Hl; try discriminate; constructor.
  - exact (H 0 _ _ eq_refl eq_refl).
  - apply IH; [ congruence | intros k; exact (H (S k)) ].
Qed.

Lemma Forall2_nth_both : forall {X Y} (P : X -> Y -> Prop) l1 l2 k x y,
    List.Forall2 P l1 l2 -> List.nth_error l1 k = Some x -> List.nth_error l2 k = Some y -> P x y.
Proof.
  intros * H; revert k; induction H; intros [| k] H1 H2; cbn in *; try discriminate.
  - congruence.
  - eauto.
Qed.

(** A record type at related parameters is realisable when its fields'
    types are: it reads back, its neutrals are related (their neutral
    projections, at each field's type, are), and related elements read back
    equally, as the η-long tuple of their projections. *)
Lemma realize_record : forall p R ns ns' (fr : nat -> list domain -> relation domain),
    record_lookup gc_deps gc_stack p = Some R ->
    List.NoDup (List.map fst (record_fields R)) ->
    List.length ns = List.length (record_params R) ->
    List.length ns' = List.length (record_params R) ->
    per_top_ps (List.rev (record_params R)) ns ns' ->
    (forall k f T vs vs', List.nth_error (record_fields R) k = Some (f, T) -> tele_prefix_rel fr k vs vs' ->
       exists a a', ⟦ T ⟧ env_args nil (ns ++ vs) ↘ a /\ ⟦ T ⟧ env_args nil (ns' ++ vs') ↘ a' /\
         (forall c c', Dom c ≈ c' ∈ per_bot -> fr k vs (relevant_value a (⇑ a c)) (relevant_value a' (⇑ a' c'))) /\
         (forall b b', fr k vs b b' -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top)) ->
    Dom d_record p ns ≈ d_record p ns' ∈ per_top_typ /\
    (forall c c', Dom c ≈ c' ∈ per_bot -> record_rel R fr (⇑ (d_record p ns) c) (⇑ (d_record p ns') c')) /\
    (forall b b', record_rel R fr b b' -> Dom ⇓ (d_record p ns) b ≈ ⇓ (d_record p ns') b' ∈ per_top).
Proof.
  intros * Hl Hnd Hn Hn' Hps Hev.
  set (fl := record_fields R) in *.
  repeat split.
  - intros s; destruct (Hps s) as (Ps & H1 & H2); exists (nf_record p Ps); split; econstructor; eassumption.
  - (** The neutral projections, built field by field, related at each
        field's type, and the projections they are. *)
    intros c c' Hc.
    assert (Hall : forall m j pre pre', m + j = List.length fl -> tele_prefix_rel fr j pre pre' ->
               exists rs rs', eval_neutral_fields gc_deps gc_stack ns c (List.skipn j fl) pre rs /\
                 eval_neutral_fields gc_deps gc_stack ns' c' (List.skipn j fl) pre' rs' /\
                 tele_prefix_rel fr (List.length fl) (pre ++ rs) (pre' ++ rs')).
    { induction m as [| m IH]; intros j pre pre' Hj Hp.
      - rewrite List.skipn_all2 by lia; exists nil, nil; rewrite !List.app_nil_r.
        split; [ constructor | split; [ constructor |] ]; replace (List.length fl) with j by lia; exact Hp.
      - destruct (nth_error_lt_some' fl j ltac:(lia)) as [[g T] Hg].
        destruct (Hev _ _ _ _ _ Hg Hp) as (a & a' & Ea & Ea' & Hbot & _).
        assert (Hpc : Dom d_proj g c ≈ d_proj g c' ∈ per_bot)
          by (intros s; destruct (Hc s) as (M & HM & HM'); exists (ne_proj g M); split; constructor; assumption).
        destruct (IH (S j) (pre ++ relevant_value a (⇑ a (d_proj g c)) :: nil) (pre' ++ relevant_value a' (⇑ a' (d_proj g c')) :: nil)
                    ltac:(lia) (tele_prefix_rel_snoc _ _ _ _ _ _ Hp (Hbot _ _ Hpc))) as (rs & rs' & Er & Er' & Hrs).
        exists (relevant_value a (⇑ a (d_proj g c)) :: rs), (relevant_value a' (⇑ a' (d_proj g c')) :: rs').
        rewrite (skipn_nth_cons' _ _ _ Hg).
        rewrite <- !List.app_assoc in Hrs; cbn [List.app] in Hrs.
        split; [ econstructor; eassumption | split; [ econstructor; eassumption | exact Hrs ] ]. }
    destruct (Hall (List.length fl) 0 nil nil ltac:(lia) (tele_prefix_rel_nil _)) as (rs & rs' & Er & Er' & Hrs).
    cbn [List.skipn List.app] in *.
    assert (Hproj : forall ms m0 rs0, eval_neutral_fields gc_deps gc_stack ms m0 fl nil rs0 ->
               record_projs R (⇑ (d_record p ms) m0) rs0).
    { intros ms m0 rs0 E.
      apply Forall2_of_nth; [ symmetry; exact (eval_neutral_fields_length _ _ _ _ _ E) |].
      intros k [g T] r Hk Hr; cbn [fst].
      econstructor; [ exact Hl | exact (field_index_nth_nodup _ _ _ _ Hnd Hk) | apply eval_neutral_fields_firstn; exact E |].
      rewrite List.nth_error_firstn; destruct (Nat.ltb_spec k (S k)); [ exact Hr | lia ]. }
    destruct Hrs as [Hlr Hfrom].
    econstructor; [ exact (Hproj _ _ _ Er) | exact (Hproj _ _ _ Er') | split; [ exact Hlr | exact Hfrom ] ].
  - (** The elements: the projections, read back field by field at each
        field's type in the parameters and the projections before it. *)
    intros b b' [vs vs' Hvl Hvr Hrel] s.
    destruct (Hps s) as (Ps & H1 & H2).
    pose proof Hrel as Hrel'; rewrite tele_rel_iff in Hrel'; destruct Hrel' as (Hlv & Hlv' & Hr).
    fold fl in Hrel, Hlv, Hlv'.
    assert (Hall : forall m j, m + j = List.length fl ->
               exists Fs, Rflds b at List.skipn j fl in gc_deps ⍮ gc_stack ⍮ env_args nil (ns ++ List.firstn j vs) ⍮ s ↘ Fs /\
                 Rflds b' at List.skipn j fl in gc_deps ⍮ gc_stack ⍮ env_args nil (ns' ++ List.firstn j vs') ⍮ s ↘ Fs).
    { induction m as [| m IH]; intros j Hj.
      - rewrite List.skipn_all2 by lia; exists nil; split; constructor.
      - destruct (nth_error_lt_some' fl j ltac:(lia)) as [[g T] Hg].
        destruct (nth_error_lt_some' vs j ltac:(lia)) as [v Hv].
        destruct (nth_error_lt_some' vs' j ltac:(lia)) as [v' Hv'].
        destruct (Hev _ _ _ _ _ Hg (tele_prefix_rel_of_full _ _ _ _ j Hrel ltac:(lia))) as (a & a' & Ea & Ea' & _ & Htop).
        destruct (Htop _ _ (Hr _ _ _ Hv Hv') s) as (F & HF & HF').
        destruct (IH (S j) ltac:(lia)) as (Fs & HFs & HFs').
        rewrite (firstn_S_snoc _ _ _ Hv), List.app_assoc, env_args_snoc in HFs.
        rewrite (firstn_S_snoc _ _ _ Hv'), List.app_assoc, env_args_snoc in HFs'.
        exists (cons F Fs); rewrite (skipn_nth_cons' _ _ _ Hg).
        split; econstructor;
          [ exact (Forall2_nth_both _ _ _ _ _ _ Hvl Hg Hv) | exact Ea | exact HF | exact HFs
          | exact (Forall2_nth_both _ _ _ _ _ _ Hvr Hg Hv') | exact Ea' | exact HF' | exact HFs' ]. }
    destruct (Hall (List.length fl) 0 ltac:(lia)) as (Fs & HFs & HFs').
    cbn [List.skipn List.firstn] in HFs, HFs'; rewrite List.app_nil_r in HFs, HFs'.
    exists (nf_tuple p Ps (List.map fst fl) Fs); split; econstructor; eassumption.
Qed.

(** [realize_record] at the record clause's premises, the realisability of
    the fields' types read off the induction hypotheses. *)
#[local] Ltac realize_record_from_ih :=
  match goal with
  | Hl : record_lookup _ _ ?p = Some ?R, Hnd : List.NoDup _, Hn : List.length ?ns = _, Hn' : List.length ?ns' = _,
    Hps : per_top_ps _ ?ns ?ns', HfE : fields_evals _ ?R ?ns ?ns' ?fr |- _ =>
      unshelve epose proof (realize_record p R ns ns' fr Hl Hnd Hn Hn' Hps _) as (Hrt & Hrn & Hre);
      [ intros k f T vs vs' Hk Hp; destruct (HfE _ _ _ _ _ Hk Hp) as [a a' Ea Ea' (_ & _ & Hbot & Htop)];
        exists a, a'; repeat split; eauto |]
  end.

(** Realisability: related types read back equally, neutrals of them are
    related (as the proof [⋆ᵈ] at a proposition, as relevance-directed
    evaluation has them), and related elements read back equally. *)
Lemma realize_per_univ_elem_gen : forall {i a a' R},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom a ≈ a' ∈ per_top_typ
    /\ (forall {c c'}, Dom c ≈ c' ∈ per_bot -> Dom relevant_value a (⇑ a c) ≈ relevant_value a' (⇑ a' c') ∈ R)
    /\ (forall {b b'}, Dom b ≈ b' ∈ R -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top).
Proof.
  intros * Hunivelem. simpl in Hunivelem.
  per_univ_elem_induction Hunivelem.
  - (** A large universe: its neutrals are neutral types, relevant; its
        elements read back as types. *)
    subst; repeat split.
    + intro s; eexists; split; econstructor.
    + intros c c' Hc; cbn [relevant_value domain_relevance]; apply_relation_equivalence.
      constructor; [| reflexivity | reflexivity ].
      eexists; basic_per_univ_elem_econstructor; [ reflexivity | reflexivity | exact Hc | reflexivity ].
    + intros b b' Hb; apply_relation_equivalence; destruct Hb as [[R' HR'] _ _].
      match goal with IH : forall A B R, per_univ_elem _ R A B -> _ |- _ => destruct (IH _ _ _ HR') as (Htt & _ & _) end.
      intro s; destruct (Htt s) as (C & HC & HC'); exists C; split; constructor; assumption.
  - (** A small universe.  It reads back as the universe at the canonical
        form its level reads back as, which the two related levels share; the
        other two components are as in the large tier, with the elements at
        the index of the realiser. *)
    repeat split.
    + intro s.
      match goal with H : per_lvl _ _ |- _ => destruct (H s) as [W [HW HW']] end.
      destruct (read_nf_level_real _ _ _ _ HW) as [L [-> _]].
      exists (nf_univ_of L); split; apply read_typ_suniv; assumption.
    + intros c c' Hc; cbn [relevant_value domain_relevance]; apply_relation_equivalence.
      constructor; [| reflexivity | reflexivity ].
      eexists; basic_per_univ_elem_econstructor; [ reflexivity | reflexivity | exact Hc | reflexivity ].
    + intros b b' Hb; apply_relation_equivalence; destruct Hb as [[R' HR'] _ _].
      match goal with IH : forall A B R, per_univ_elem _ R A B -> _ |- _ => destruct (IH _ _ _ HR') as (Htt & _ & _) end.
      intro s; destruct (Htt s) as (C & HC & HC'); exists C; split; constructor; assumption.
  - (** A type of levels: its elements read back at every sort. *)
    repeat split.
    + intro s; eexists; split; econstructor.
    + intros c c' Hc; cbn [relevant_value domain_relevance]; apply_relation_equivalence.
      apply per_bot_then_per_lvl_at; exact Hc.
    + intros b b' Hb; apply_relation_equivalence; intro s.
      apply per_lvl_at_lvl in Hb; destruct (Hb s) as [L [HL HL']].
      exists L; split; eapply read_nf_level_sort; eassumption.
  - (** [Prop]: its neutrals are neutral propositions; its elements read
        back as types. *)
    repeat split.
    + intro s; eexists; split; econstructor.
    + intros c c' Hc; cbn [relevant_value domain_relevance]; apply_relation_equivalence.
      constructor; [ reflexivity | reflexivity |].
      intro s; destruct (Hc s) as (C & HC & HC'); exists (⇑ⁿ C); split; constructor; assumption.
    + intros b b' Hb; apply_relation_equivalence; destruct Hb as [_ _ Ht].
      intro s; destruct (Ht s) as (C & HC & HC'); exists C; split; apply read_nf_prop; assumption.
  - (** A proposition: its only element is the proof, read back as [⋆ⁿ]. *)
    match goal with Hp : per_prop _ _ |- _ => destruct Hp as [Hl Hr Ht] end.
    repeat split.
    + exact Ht.
    + intros c c' Hc; unfold relevant_value; rewrite Hl, Hr; apply_relation_equivalence; split; reflexivity.
    + intros b b' _ s; exists ⋆ⁿ; split; apply read_nf_proof; assumption.
  - (** The placeholder type, by η. *)
    repeat split.
    + intro s; eexists; split; econstructor.
    + intros c c' Hc; cbn [relevant_value domain_relevance]; apply_relation_equivalence; exact I.
    + intros b b' _ s; exists nf_placeholder; split; constructor.
  - (** A [Π]: read back under a fresh variable of the domain, the proof
        [⋆ᵈ] at a proposition; its neutrals applied are neutrals of the
        relevant codomain. *)
    destruct IHHunivelem as (Hatt & Habot & Hatop).
    repeat split.
    + intro s.
      assert (Hv : Dom relevant_value a (⇑! a s) ≈ relevant_value a' (⇑! a' s) ∈ in_rel) by (apply Habot; apply var_per_bot).
      match goal with HT : forall c c' (e : in_rel c c'), rel_mod_eval _ B _ B' _ _ |- _ =>
        destruct (HT _ _ Hv) as [b b' Eb Eb' [HRb (Hbtt & _ & _)]] end.
      destruct (Hatt s) as (A0 & HA0 & HA0').
      destruct (Hbtt (S s)) as (B0 & HB0 & HB0').
      exists (Πⁿ A0 B0); split; econstructor; eassumption.
    + intros c c' Hc; cbn [relevant_value domain_relevance]; apply_relation_equivalence.
      constructor; [ reflexivity | reflexivity |].
      intros c0 c0' Hc0.
      match goal with HT : forall c c' (e : in_rel c c'), rel_mod_eval _ B _ B' _ _ |- _ =>
        destruct (HT _ _ Hc0) as [b b' Eb Eb' [HRb (_ & Hbbot & _)]] end.
      assert (Hap : Dom c $ᵈ ⇓ a c0 ≈ c' $ᵈ ⇓ a' c0' ∈ per_bot) by (apply domain_app_per; [ exact Hc | exact (Hatop _ _ Hc0) ]).
      econstructor; [ eapply eval_app_neut; exact Eb | eapply eval_app_neut; exact Eb' | exact (Hbbot _ _ Hap) ].
    + intros f f' Hf; apply_relation_equivalence; destruct Hf as [_ _ Happ].
      intro s.
      assert (Hv : Dom relevant_value a (⇑! a s) ≈ relevant_value a' (⇑! a' s) ∈ in_rel) by (apply Habot; apply var_per_bot).
      destruct (Happ _ _ Hv) as [fa f'a' Hfa Hf'a' Hrel].
      match goal with HT : forall c c' (e : in_rel c c'), rel_mod_eval _ B _ B' _ _ |- _ =>
        destruct (HT _ _ Hv) as [b b' Eb Eb' [HRb (_ & _ & Hbtop)]] end.
      destruct (Hbtop _ _ Hrel (S s)) as (M0 & HM0 & HM0').
      destruct (Hatt s) as (A0 & HA0 & HA0').
      exists (λⁿ A0 M0); split; econstructor; eassumption.
  - (** A neutral relevant type: its elements are neutrals. *)
    match goal with Hr : domain_relevance (⇑ a b) = relevant, Hr' : domain_relevance (⇑ a' b') = relevant |- _ =>
      rename Hr into Hra; rename Hr' into Hra' end.
    repeat split.
    + intro s; match goal with Hb : per_bot b b' |- _ => destruct (Hb s) as (M & HM & HM') end.
      exists (⇑ⁿ M); split; constructor; assumption.
    + intros c c' Hc; unfold relevant_value; rewrite Hra, Hra'; apply_relation_equivalence; constructor; exact Hc.
    + intros m m' Hm; apply_relation_equivalence; destruct Hm as [? ? ? ? Hm]; intro s.
      destruct (Hm s) as (M & HM & HM'); exists (⇑ⁿ M); split; apply read_nf_neut; assumption.
  (** A member of a group of inductive types: [realize_indty], from the
      realisability of the types of its telescopes; its neutrals by
      [ind_rel_neut_canon], the fresh-variable admissibility of the type's
      own uniform parameters following from the type-level one. *)
  - repeat split; [| intros c c' Hc; cbn [relevant_value domain_relevance] | intros b b' Hb ];
      apply_relation_equivalence.
    + unshelve epose proof (realize_indty p D ups ups' nr ar dr H H0 H3 H5 H6 H8 H9 H11 H12 H14
                              _ _ _ H15 H16 k M ns ns' H1 H17) as [Hrt _];
      [ intros m Mm k0 A vs vs' Hm Hk Hp; destruct (H7 _ _ _ _ _ _ Hm Hk Hp) as [a a' Ea Ea' (_ & _ & _ & Hrb)]; eauto
      | intros m Mm ms ms' c0 gs k0 A vs vs' Hm0 Hm Hc Hk Hp;
        destruct (H10 _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Hk Hp) as [a a' Ea Ea' (_ & _ & _ & Hrb)]; eauto
      | intros m Mm ms ms' c0 gs gs1 t gs2 ws ws' k0 B ys ys' Hm0 Hm Hc Heq Hw HB Hy;
        destruct (H13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Heq Hw HB Hy) as [a a' Ea Ea' (_ & Htt & Hbot & _)];
        exists a, a'; repeat split; eauto
      | exact Hrt ].
    + unfold grp_rel.
      eapply ind_rel_neut_canon; eassumption.
    + unshelve epose proof (realize_indty p D ups ups' nr ar dr H H0 H3 H5 H6 H8 H9 H11 H12 H14
                              _ _ _ H15 H16 k M ns ns' H1 H17) as [_ Hre];
      [ intros m Mm k0 A vs vs' Hm Hk Hp; destruct (H7 _ _ _ _ _ _ Hm Hk Hp) as [a a' Ea Ea' (_ & _ & _ & Hrb)]; eauto
      | intros m Mm ms ms' c0 gs k0 A vs vs' Hm0 Hm Hc Hk Hp;
        destruct (H10 _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Hk Hp) as [a a' Ea Ea' (_ & _ & _ & Hrb)]; eauto
      | intros m Mm ms ms' c0 gs gs1 t gs2 ws ws' k0 B ys ys' Hm0 Hm Hc Heq Hw HB Hy;
        destruct (H13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Heq Hw HB Hy) as [a a' Ea Ea' (_ & Htt & Hbot & _)];
        exists a, a'; repeat split; eauto
      | unfold grp_rel in *; eapply Hre; eassumption ].
  (** A record type: [realize_record], from the realisability of the types
      of its fields. *)
  - repeat split; [| intros c c' Hc; cbn [relevant_value domain_relevance] | intros b b' Hb ];
      apply_relation_equivalence.
    + realize_record_from_ih; exact Hrt.
    + realize_record_from_ih; apply Hrn; assumption.
    + realize_record_from_ih; apply Hre; assumption.
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
    Dom c ≈ c' ∈ per_bot -> Dom relevant_value a (⇑ a c) ≈ relevant_value a' (⇑ a' c') ∈ R.
Proof.
  intros * ?%realize_per_univ_elem_gen; firstorder.
Qed.

(** At a relevant type, the neutrals themselves are related. *)
Corollary per_bot_then_per_elem_relevant : forall {i a a' R c c'},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    domain_relevance a = relevant ->
    Dom c ≈ c' ∈ per_bot -> Dom ⇑ a c ≈ ⇑ a' c' ∈ R.
Proof.
  intros * HR Hr Hc.
  pose proof (per_univ_elem_relevance _ _ _ _ HR) as Hr'; rewrite Hr in Hr'.
  pose proof (per_bot_then_per_elem HR Hc) as H; unfold relevant_value in H; rewrite Hr, <- Hr' in H; exact H.
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

(** The elements of a proposition include the proof. *)
Lemma per_elem_proof : forall {i R a a'},
    DF a ≈ a' ∈ per_univ_elem i ↘ R -> domain_relevance a = propositional -> Dom ⋆ᵈ ≈ ⋆ᵈ ∈ R.
Proof.
  intros * HR Hr.
  pose proof (per_univ_elem_relevance _ _ _ _ HR) as Hr'; rewrite Hr in Hr'.
  pose proof (per_bot_then_per_elem HR (var_per_bot (n := 0))) as H.
  unfold relevant_value in H; rewrite Hr, <- Hr' in H; exact H.
Qed.

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
    unshelve eapply mk_per_ctx_env_cons_rel; [ eassumption | | intros _; reflexivity | intros _; reflexivity ].
    eapply per_bot_then_per_elem; eauto.
    erewrite per_ctx_respects_length; mauto.
    eexists; eauto.
  - (** A definition slot holds the value of the body at a relevant type,
        the proof at a proposition. *)
    destruct IHper_ctx_env as [ρ [ρ' [? [? Hρ]]]].
    assert (Dom ρ ≈ ρ ∈ tail_rel) by solve_per.
    assert (Dom ρ' ≈ ρ' ∈ tail_rel) by solve_per.
    match goal with HS : forall ρ ρ' (_ : Dom ρ ≈ ρ' ∈ tail_rel), rel_typ_sort _ _ _ |- _ => rename HS into HS0 end.
    match goal with HT : forall ρ ρ' (_ : Dom ρ ≈ ρ' ∈ tail_rel), rel_typ _ _ _ _ _ _ |- _ =>
      destruct (HT _ _ Hρ) as [a a' Ha Ha' HR] end.
    destruct (HS0 _ _ Hρ) as (a0 & Ha0 & Hr0).
    assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (per_univ_elem_relevance _ _ _ _ HR) as Hr0'.
    destruct r; cbn [def_bodies_rel def_heads_at] in *.
    + match goal with
      | Hbody : forall ρ ρ' (_ : Dom ρ ≈ ρ' ∈ tail_rel), rel_elem _ _ _ _ _ |- _ =>
          destruct (Hbody _ _ Hρ)
      end.
      do 2 eexists; repeat split;
        only 1-2: (eapply initial_env_cons_def; [ eassumption | eassumption | congruence | eassumption ]).
      apply_relation_equivalence.
      unshelve eapply mk_per_ctx_env_def_rel'; [ exact Hρ | solve_def_heads | intros _; reflexivity | intros _; reflexivity ].
    + do 2 eexists; repeat split;
        only 1-2: (eapply initial_env_cons_def_proof; [ eassumption | eassumption | congruence ]).
      apply_relation_equivalence.
      unshelve eapply mk_per_ctx_env_def_rel';
        [ exact Hρ | split; [ eapply per_elem_proof; eassumption | exact I ] | intros _; reflexivity | intros _; reflexivity ].
  - (** A slot holds the closure of its unit, which the premise relates to
        the other unit's. *)
    destruct IHper_ctx_env as [ρ [ρ' [? [? Hρ]]]].
    assert (Dom ρ ≈ ρ ∈ tail_rel) by solve_per.
    assert (Dom ρ' ≈ ρ' ∈ tail_rel) by solve_per.
    match goal with HU : forall ρ ρ', tail_rel ρ ρ' -> rel_modexp_evals _ _ _ _ |- _ =>
      destruct (HU _ _ Hρ) as [h h' Hh Hh' Hr] end.
    assert (T1 : tie_mod h (me_lit U) ρ)
      by (exists h; split; [ exact Hh | eapply per_dmod_trans; [ exact Hr | apply per_dmod_sym, Hr ] ]).
    assert (T2 : tie_mod h' (me_lit U') ρ')
      by (exists h'; split; [ exact Hh' | eapply per_dmod_trans; [ apply per_dmod_sym, Hr | exact Hr ] ]).
    exists (ρ ↦ᵐ h), (ρ' ↦ᵐ h'); repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    simpl; repeat split; try assumption; unfold env_mod; cbn [env_entry List.hd]; solve_tie.
  - (** A definition with a module part holds the value of its term and the
        closure of its unit. *)
    destruct IHper_ctx_env as [ρ [ρ' [? [? Hρ]]]].
    assert (Dom ρ ≈ ρ ∈ tail_rel) by solve_per.
    assert (Dom ρ' ≈ ρ' ∈ tail_rel) by solve_per.
    (** A definition with a module part is of a relevant type. *)
    subst r; cbn [def_bodies_rel def_heads_at] in *.
    match goal with
    | Hbody : forall ρ ρ' (_ : Dom ρ ≈ ρ' ∈ tail_rel), rel_elem _ _ _ _ _ |- _ =>
        destruct (Hbody _ _ Hρ) as [m m' Hm Hm' Hmm]
    end.
    match goal with HU : forall ρ ρ', tail_rel ρ ρ' -> rel_modexp_evals _ _ _ _ |- _ =>
      destruct (HU _ _ Hρ) as [h h' Hh Hh' Hr] end.
    assert (T1 : tie_mod h (me_lit U) ρ)
      by (exists h; split; [ exact Hh | eapply per_dmod_trans; [ exact Hr | apply per_dmod_sym, Hr ] ]).
    assert (T2 : tie_mod h' (me_lit U') ρ')
      by (exists h'; split; [ exact Hh' | eapply per_dmod_trans; [ apply per_dmod_sym, Hr | exact Hr ] ]).
    exists (ρ ↦ᵈ m ‖ h), (ρ' ↦ᵈ m' ‖ h'); repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    solve_def_heads_pre.
    apply (mk_per_ctx_env_dm_rel _ _ _ _ _ _ _ (ρ ↦ᵈ m ‖ h) (ρ' ↦ᵈ m' ‖ h') Hρ);
      unfold env_mod; cbn [env_entry List.hd extend_env_dm]; cbn;
      try solve [ solve_tie ]; solve_def_heads_post.
Qed.

Lemma var_per_elem : forall {a b i R} n,
    DF a ≈ b ∈ per_univ_elem i ↘ R ->
    Dom relevant_value a (⇑! a n) ≈ relevant_value b (⇑! b n) ∈ R.
Proof.
  intros.
  eapply per_bot_then_per_elem; mauto.
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve per_univ_then_per_top_typ : mctt.
#[export]
Hint Resolve per_elem_then_per_top : mctt.
