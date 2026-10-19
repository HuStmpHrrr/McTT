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
    Rps vs1 ++ vs2 at T1 ++ T2 in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ nfs_app Ms1 Ms2.
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
    - rewrite !List.skipn_all2 by lia; exists nfs_nil; split; constructor.
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

Lemma read_ps_length : forall s ρ T vs Ms, Rps vs at T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Ms -> List.length vs = List.length T.
Proof. induction 1; cbn; congruence. Qed.

(** The codomain of the type of an argument of a function shape, at an
    argument. *)
Lemma eval_fam_cod_shfam : forall p ups ρ t x a,
    ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↦ x ↘ a ->
    ⟦ fam_cod ⟧ nil ↦ d_shfam p ups ρ t ↦ x ↘ a.
Proof. intros; unfold fam_cod; econstructor; [ apply eval_exp_var | apply eval_exp_var | econstructor; eassumption ]. Qed.

Lemma eval_fam_cod_ihfam : forall ρm A ρ t f x fx a,
    $| f & x | gc_deps ⍮ gc_stack ↘ fx ->
    ⟦ihty fx of t under ρm A ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↦ x ↘ a ->
    ⟦ fam_cod ⟧ nil ↦ d_ihfam ρm A ρ t f ↦ x ↘ a.
Proof. intros; unfold fam_cod; econstructor; [ apply eval_exp_var | apply eval_exp_var | econstructor; eassumption ]. Qed.

Lemma env_args_snoc3 : forall (u a b c : list domain) x,
    env_args nil (u ++ a ++ b ++ c ++ x :: nil) = env_args nil (u ++ a ++ b ++ c) ↦ x.
Proof. intros; rewrite !List.app_assoc, env_args_snoc; reflexivity. Qed.

(** The realisability of an inductive type, from that of the types of its
    telescopes.  An element is read back at the type's parameters, while it
    is related at its own: its own uniform parameters are admissible beside
    the type's on each side ([HOk], [HOk']), which relates the parameters
    of its recursive arguments at the two. *)
Lemma realize_indty : forall p D ups ups' ns ns'
    (nr : nat -> list domain -> relation domain)
    (ar : list domain -> String.string -> nat -> list domain -> relation domain)
    (dr : list domain -> exp -> relation domain)
    (Ok : list domain -> Prop),
    ind_lookup gc_deps gc_stack p = Some D ->
    tele_ass (ind_params D) ->
    List.length ups = ind_nu D ->
    per_top_ps (List.rev (ind_uparams D)) ups ups' ->
    (forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) -> tele_prefix_rel nr k vs vs' -> PER (nr k vs)) ->
    (forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) -> tele_prefix_rel nr k vs vs' ->
       (nr k vs <~> nr k vs')) ->
    (forall ms ms' c gs k A vs vs', tele_rel nr (List.rev (ind_nparams D)) ms ms' -> ind_con D c = Some gs ->
       List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar ms c) k vs vs' -> PER (ar ms c k vs)) ->
    (forall ms ms' c gs k A vs vs', tele_rel nr (List.rev (ind_nparams D)) ms ms' -> ind_con D c = Some gs ->
       List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar ms c) k vs vs' -> (ar ms c k vs <~> ar ms' c k vs')) ->
    (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nr (List.rev (ind_nparams D)) ms ms' ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t)) k ys ys' ->
       PER (dr (ms ++ ws ++ ys) B)) ->
    (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nr (List.rev (ind_nparams D)) ms ms' ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t)) k ys ys' ->
       (dr (ms ++ ws ++ ys) B <~> dr (ms' ++ ws' ++ ys') B)) ->
    (forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) -> tele_prefix_rel nr k vs vs' ->
       exists a a', ⟦ A ⟧ env_args nil (ups ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups' ++ vs') ↘ a' /\
         (forall b b', nr k vs b b' -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top)) ->
    (forall ms ms' c gs k A vs vs',
       tele_rel nr (List.rev (ind_nparams D)) ms ms' -> ind_con D c = Some gs ->
       List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar ms c) k vs vs' ->
       exists a a', ⟦ A ⟧ env_args nil (ups ++ ms ++ vs) ↘ a /\ ⟦ A ⟧ env_args nil (ups' ++ ms' ++ vs') ↘ a' /\
         (forall b b', ar ms c k vs b b' -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top)) ->
    (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys',
       tele_rel nr (List.rev (ind_nparams D)) ms ms' ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
       List.nth_error (ptyp_doms t) k = Some B ->
       tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t)) k ys ys' ->
       exists a a', ⟦ B ⟧ env_args nil (ups ++ ms ++ ws ++ ys) ↘ a /\ ⟦ B ⟧ env_args nil (ups' ++ ms' ++ ws' ++ ys') ↘ a' /\
         Dom a ≈ a' ∈ per_top_typ /\
         (forall c c', Dom c ≈ c' ∈ per_bot -> dr (ms ++ ws ++ ys) B (⇑ a c) (⇑ a' c'))) ->
    (forall u, Ok u -> adm_uparams D ups nr ar dr u) ->
    (forall u, Ok u -> adm_uparams D ups' nr ar dr u) ->
    tele_rel nr (List.rev (ind_nparams D)) ns ns' ->
    Dom d_ind p (ups ++ ns) ≈ d_ind p (ups' ++ ns') ∈ per_top_typ /\
    (forall b b', ind_rel p D Ok nr ar dr ns ns' b b' -> Dom ⇓ (d_ind p (ups ++ ns)) b ≈ ⇓ (d_ind p (ups' ++ ns')) b' ∈ per_top).
Proof.
  intros * Hl Hass Hu Hps HnP HnI HaP HaI HdP HdI Hn Ha Hdr HOk HOk' Hns.
  assert (Hle : ind_nu D <= ind_np D).
  { destruct (Hps 0) as (Ms & HM & _); apply read_ps_length in HM.
    rewrite List.length_rev in HM; unfold ind_uparams in HM; rewrite List.length_skipn in HM.
    unfold ind_nn in HM; unfold ind_np; lia. }
  assert (Hu' : List.length ups' = ind_nu D).
  { destruct (Hps 0) as (Ms & _ & HM); apply read_ps_length in HM.
    rewrite List.length_rev in HM; unfold ind_uparams in HM; rewrite List.length_skipn in HM.
    unfold ind_nn in HM; unfold ind_np in *; lia. }
  assert (Hpar : forall xs xs', tele_rel nr (List.rev (ind_nparams D)) xs xs' ->
             per_top_ps (List.rev (ind_params D)) (ups ++ xs) (ups' ++ xs')).
  { intros xs xs' Hx s.
    destruct (Hps s) as (Ms1 & HM1 & HM1').
    assert (Hassn : tele_ass (List.rev (ind_nparams D)))
      by (apply List.Forall_rev; unfold ind_nparams; apply Forall_firstn'; exact Hass).
    destruct (read_ps_tele (List.rev (ind_nparams D)) nr (env_args nil ups) (env_args nil ups') Hassn
                ltac:(intros k A pre pre' Hk Hp; rewrite <- !env_args_app; exact (Hn _ _ _ _ Hk Hp))
                _ _ Hx s) as (Ms2 & HM2 & HM2').
    exists (nfs_app Ms1 Ms2); rewrite rev_params_split; split; apply read_ps_app; assumption. }
  assert (Hlen : forall xs xs', tele_rel nr (List.rev (ind_nparams D)) xs xs' ->
             List.length (ups ++ xs) = ind_np D /\ List.length (ups' ++ xs') = ind_np D).
  { intros xs xs' Hx; rewrite tele_rel_iff in Hx; destruct Hx as (Hl1 & Hl2 & _).
    rewrite List.length_rev, length_nparams in Hl1, Hl2; rewrite !List.length_app; unfold ind_nn in *; lia. }
  split.
  { intros s; destruct (Hpar _ _ Hns s) as (Ms & HM & HM').
    destruct (Hlen _ _ Hns) as [Hl1 Hl2].
    exists (nf_indty p Ms); split; econstructor; eassumption. }
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
  (** The elements are read back at indices [xs] and [xs'] related to their
      own, the arguments and shapes after values of the type's parameters
      [xs] and [xs'] related to their own [ms] and [ms']. *)
  assert (Hmain :
    (forall ns0 ns0' x y, ind_rel p D Ok nr ar dr ns0 ns0' x y ->
       forall xs xs', tele_rel nr (List.rev (ind_nparams D)) xs ns0 -> tele_rel nr (List.rev (ind_nparams D)) xs' ns0' ->
       Dom ⇓ (d_ind p (ups ++ xs)) x ≈ ⇓ (d_ind p (ups' ++ xs')) y ∈ per_top) /\
    (forall u u' pre pre' gs vs vs', con_args_rel p D Ok nr ar dr u u' pre pre' gs vs vs' ->
       forall ms ms' xs xs' c gsf gs1 vp vp', pre = ms ++ nonrec_arg_vals gs1 vp -> pre' = ms' ++ nonrec_arg_vals gs1 vp' ->
         List.length vp = List.length gs1 -> List.length vp' = List.length gs1 -> Ok u -> Ok u' ->
         tele_rel nr (List.rev (ind_nparams D)) ms ms' ->
         tele_rel nr (List.rev (ind_nparams D)) xs ms -> tele_rel nr (List.rev (ind_nparams D)) xs' ms' ->
         ind_con D c = Some gsf -> gsf = gs1 ++ gs ->
         tele_rel (ar ms c) (cargs_nonrec gsf) (nonrec_arg_vals gsf (vp ++ vs)) (nonrec_arg_vals gsf (vp' ++ vs')) ->
         forall s, exists Vs,
           Rcargs vs at gs of p ups in gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ xs ++ nonrec_arg_vals gs1 vp) ⍮ s ↘ Vs /\
           Rcargs vs' at gs of p ups' in gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ xs' ++ nonrec_arg_vals gs1 vp') ⍮ s ↘ Vs) /\
    (forall u u' pre pre' t v v', rec_arg_rel p D Ok nr ar dr u u' pre pre' t v v' ->
       forall ms ms' xs xs' c gs1 t0 gs2 ws ws' k ys ys', pre = ms ++ ws ++ ys -> pre' = ms' ++ ws' ++ ys' ->
         Ok u -> Ok u' -> tele_rel nr (List.rev (ind_nparams D)) ms ms' ->
         tele_rel nr (List.rev (ind_nparams D)) xs ms -> tele_rel nr (List.rev (ind_nparams D)) xs' ms' ->
         ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
         tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
         ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
         tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t0)) k ys ys' ->
         forall s, exists a a' V, ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ xs ++ ws ++ ys) ↘ a /\
           ⟦shty t of p ups' ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ xs' ++ ws' ++ ys') ↘ a' /\
           Rnf ⇓ a v in gc_deps ⍮ gc_stack ⍮ s ↘ V /\ Rnf ⇓ a' v' in gc_deps ⍮ gc_stack ⍮ s ↘ V) /\
    (forall u u' pre pre' t f x f' x', rec_arg_app_rel p D Ok nr ar dr u u' pre pre' t f x f' x' ->
       forall ms ms' xs xs' c gs1 t0 gs2 ws ws' k ys ys', pre = ms ++ ws ++ ys -> pre' = ms' ++ ws' ++ ys' ->
         Ok u -> Ok u' -> tele_rel nr (List.rev (ind_nparams D)) ms ms' ->
         tele_rel nr (List.rev (ind_nparams D)) xs ms -> tele_rel nr (List.rev (ind_nparams D)) xs' ms' ->
         ind_con D c = Some (gs1 ++ ca_rec t0 :: gs2) ->
         tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
         ptyp_skip k t0 = t -> k <= List.length (ptyp_doms t0) ->
         tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t0)) k ys ys' ->
         forall s, exists r r' a a' V, $| f & x | gc_deps ⍮ gc_stack ↘ r /\ $| f' & x' | gc_deps ⍮ gc_stack ↘ r' /\
           ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups ++ xs ++ ws ++ ys) ↘ a /\
           ⟦shty t of p ups' ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ups' ++ xs' ++ ws' ++ ys') ↘ a' /\
           Rnf ⇓ a r in gc_deps ⍮ gc_stack ⍮ s ↘ V /\ Rnf ⇓ a' r' in gc_deps ⍮ gc_stack ⍮ s ↘ V)).
  { apply ind_rel_mut_ind_all.
    - intros ns0 ns0' c gs bs bs' vs vs' Hn0 Hc Hb Hb' Ho Ho' Hs Hs' Ha0 Hia IH xs xs' Hx Hx' s.
      assert (Hxx : tele_rel nr (List.rev (ind_nparams D)) xs xs')
        by exact (ttrans _ _ _ Hx (ttrans _ _ _ Hn0 (tsym _ _ Hx'))).
      destruct (Hpar _ _ Hxx s) as (Ms & HM & HM').
      destruct (Hlen _ _ Hxx) as [Hl1 Hl2].
      assert (Hvl : List.length vs = List.length gs /\ List.length vs' = List.length gs).
      { clear - Hia; induction Hia; cbn; [ split; reflexivity | | ]; destruct IHHia; split; congruence. }
      destruct (IH (List.skipn (ind_nu D) bs) (List.skipn (ind_nu D) bs') xs xs' c gs nil nil nil
                   ltac:(cbn; rewrite List.app_nil_r; reflexivity) ltac:(cbn; rewrite List.app_nil_r; reflexivity)
                   eq_refl eq_refl Ho Ho' (ttrans _ _ _ (ttrans _ _ _ (tsym _ _ Hs) Hn0) Hs')
                   (ttrans _ _ _ Hx Hs) (ttrans _ _ _ Hx' Hs') Hc eq_refl Ha0 s) as (Vs & HV & HV').
      cbn [nonrec_arg_vals List.app] in HV, HV'; rewrite List.app_nil_r in HV, HV'.
      exists (nf_con p c (nfs_app Ms Vs)); split; (eapply read_nf_con; [ exact Hl | exact Hc | eassumption | | eassumption |]).
      + rewrite List.length_app; lia.
      + rewrite firstn_app_exact by exact Hu; rewrite skipn_app_exact by exact Hb; exact HV.
      + rewrite List.length_app; lia.
      + rewrite firstn_app_exact by exact Hu'; rewrite skipn_app_exact by exact Hb'; exact HV'.
    - intros * _ _ _ _ _ _ _ Hm xs xs' _ _ s; destruct (Hm s) as (L & HL & HL').
      exists (⇑ⁿ L); split; constructor; assumption.
    - intros; exists nfs_nil; split; constructor.
    - intros u u' pre v pre' v' gs vs vs' A Hia IH ms ms' xs xs' c gsf gs1 vp vp' Hρ Hρ' Hl1 Hl2 Ou Ou' Hm Hx Hx' Hc Heq Ha0 s.
      subst pre pre' gsf.
      set (k := List.length (cargs_nonrec gs1)).
      assert (Hk : List.nth_error (cargs_nonrec (gs1 ++ ca_arg A :: gs)) k = Some A)
        by (unfold k; rewrite cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
      assert (Hkle : k <= List.length (cargs_nonrec (gs1 ++ ca_arg A :: gs)))
        by (unfold k; rewrite cargs_nonrec_app, List.length_app; lia).
      assert (HL : forall w ws wp, List.length wp = List.length gs1 ->
                 nonrec_arg_vals (gs1 ++ ca_arg A :: gs) (wp ++ w :: ws) = nonrec_arg_vals gs1 wp ++ w :: nonrec_arg_vals gs ws)
        by (intros; rewrite nonrec_arg_vals_app by assumption; reflexivity).
      assert (Hpre : tele_prefix_rel (ar ms c) k (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp'))
        by (exact (nonrec_prefix_gen _ _ _ _ _ _ _ _ eq_refl Hl1 Hl2 Ha0)).
      assert (Hrel : ar ms c k (nonrec_arg_vals gs1 vp) v v').
      { rewrite tele_rel_iff in Ha0; destruct Ha0 as (_ & _ & Hr).
        rewrite !HL in Hr by assumption.
        specialize (Hr k v v').
        rewrite !List.nth_error_app2, !length_nonrec_arg_vals, Nat.sub_diag in Hr by (try rewrite length_nonrec_arg_vals; unfold k; lia || assumption).
        specialize (Hr eq_refl eq_refl).
        rewrite (firstn_app_exact (nonrec_arg_vals gs1 vp)) in Hr by (unfold k; apply length_nonrec_arg_vals; assumption).
        exact Hr. }
      pose proof (trefl _ _ Hm) as Hmm.
      pose proof (tsym _ _ Hx) as Hmx.
      pose proof (tarpl ms c _ Hmm Hc k _ _ Hkle Hpre) as Hpp.
      assert (Hrel' : ar xs c k (nonrec_arg_vals gs1 vp) v v')
        by exact (proj1 (HaI _ _ _ _ _ _ _ _ Hmx Hc Hk Hpp _ _) Hrel).
      assert (Hxx : tele_rel nr (List.rev (ind_nparams D)) xs xs')
        by exact (ttrans _ _ _ Hx (ttrans _ _ _ Hm (tsym _ _ Hx'))).
      pose proof (tarpi _ _ _ _ _ _ _ Hmx Hc Hkle Hpre) as Hprex.
      destruct (Ha _ _ _ _ _ _ _ _ Hxx Hc Hk Hprex) as (a & a' & Ea & Ea' & Hrb).
      destruct (Hrb _ _ Hrel' s) as (V & HV & HV').
      assert (Henv : forall us ys wp w, List.length wp = List.length gs1 ->
                 env_args nil (us ++ ys ++ nonrec_arg_vals gs1 wp) ↦ w
                 = env_args nil (us ++ ys ++ nonrec_arg_vals (gs1 ++ ca_arg A :: nil) (wp ++ w :: nil))).
      { intros; rewrite nonrec_arg_vals_app by assumption; cbn; rewrite !List.app_assoc, env_args_snoc; reflexivity. }
      destruct (IH ms ms' xs xs' c (gs1 ++ ca_arg A :: gs) (gs1 ++ ca_arg A :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil)
                  ltac:(rewrite nonrec_arg_vals_app by assumption; cbn; rewrite List.app_assoc; reflexivity)
                  ltac:(rewrite nonrec_arg_vals_app by assumption; cbn; rewrite List.app_assoc; reflexivity)
                  ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                  Ou Ou' Hm Hx Hx' Hc ltac:(rewrite <- List.app_assoc; reflexivity) ltac:(rewrite <- !List.app_assoc; exact Ha0) s)
        as (Vs & HVs & HVs').
      exists (nfs_cons V Vs); split; econstructor; try eassumption.
      + rewrite Henv by assumption; exact HVs.
      + rewrite Henv by assumption; exact HVs'.
    - intros u u' pre pre' t v v' gs vs vs' Hsh IHs Hia IH ms ms' xs xs' c gsf gs1 vp vp' Hρ Hρ' Hl1 Hl2 Ou Ou' Hm Hx Hx' Hc Heq Ha0 s.
      subst pre pre' gsf.
      pose proof (nonrec_prefix_gen _ _ _ _ _ _ _ _ eq_refl Hl1 Hl2 Ha0) as Hpre.
      destruct (IHs ms ms' xs xs' c gs1 t gs (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp') 0 nil nil
                  ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity)
                  Ou Ou' Hm Hx Hx' Hc Hpre eq_refl ltac:(lia) (tele_prefix_rel_nil _) s)
        as (a & a' & V & Ea & Ea' & HV & HV').
      rewrite List.app_nil_r in Ea, Ea'.
      destruct (IH ms ms' xs xs' c (gs1 ++ ca_rec t :: gs) (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil)
                  ltac:(rewrite nonrec_arg_vals_app by assumption; cbn; rewrite List.app_nil_r; reflexivity)
                  ltac:(rewrite nonrec_arg_vals_app by assumption; cbn; rewrite List.app_nil_r; reflexivity)
                  ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                  Ou Ou' Hm Hx Hx' Hc ltac:(rewrite <- List.app_assoc; reflexivity) ltac:(rewrite <- !List.app_assoc; exact Ha0) s)
        as (Vs & HVs & HVs').
      rewrite nonrec_arg_vals_app in HVs, HVs' by assumption; cbn in HVs, HVs'; rewrite List.app_nil_r in HVs, HVs'.
      exists (nfs_cons V Vs); split; econstructor; eassumption.
    - (** The end of a shape: the parameters it evaluates to at the type's
          base are related to those at the element's own ([adm_rec_params] of
          [Ok], on each side). *)
      intros Ps u pre bs u' pre' bs' v v' k E E' Hr IHr ms ms' xs xs' c gs1 t0 gs2 ws ws' k0 ys ys' Hρ Hρ' Ou Ou' Hm Hx Hx' Hc Hw Hs Hk Hy s.
      destruct (ptyp_skip_self _ _ _ _ Hs) as [Hkd HPs].
      subst pre pre'.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (trefl _ _ Hm) as Hmm.
      pose proof (tsym _ _ Hx) as Hmx.
      pose proof (ttrans _ _ _ Hm (tsym _ _ Hx')) as Hmx'.
      pose proof (tarpl ms c _ Hmm Hc _ ws ws' HK Hw) as Hww.
      pose proof (tarpi _ _ _ _ _ _ _ Hmx Hc HK Hww) as Hwx.
      pose proof (tarpr _ _ _ _ _ _ _ Hmx' Hc HK Hw) as Hwx'.
      pose proof (tshl ms c _ gs1 t0 gs2 ws Hmm Hc eq_refl Hww k0 ys ys' Hk Hy) as Hyy.
      pose proof (tshi _ _ _ _ _ _ _ _ _ _ _ _ Hmx Hc eq_refl Hww Hk Hyy) as Hyx.
      pose proof (tshri _ _ _ _ _ _ _ _ _ _ _ _ Hmx' Hc eq_refl Hw Hk Hy) as Hyx'.
      assert (Hyxf : tele_rel (shape_doms_rel dr xs ws (ptyp_doms t0)) (ptyp_doms t0) ys ys)
        by (destruct Hyx as [Hyl Hya]; split; [ lia | exact Hya ]).
      assert (Hyxf' : tele_rel (shape_doms_rel dr xs' ws' (ptyp_doms t0)) (ptyp_doms t0) ys' ys')
        by (destruct Hyx' as [Hyl Hya]; split; [ lia | exact Hya ]).
      destruct (adm_rec_params _ _ _ _ _ _ (HOk _ Ou) xs ms c _ gs1 t0 gs2 ws ws ys ys Hx Hc eq_refl Hwx Hyxf)
        as [bs0 bs1 E0 E1 Hbs].
      destruct (adm_rec_params _ _ _ _ _ _ (HOk' _ Ou') xs' ms' c _ gs1 t0 gs2 ws' ws' ys' ys' Hx' Hc eq_refl Hwx' Hyxf')
        as [bs0' bs1' E0' E1' Hbs'].
      rewrite HPs in E0, E1, E0', E1'.
      pose proof (functional_eval_exps' _ _ _ _ E1 E) as ->.
      pose proof (functional_eval_exps' _ _ _ _ E1' E') as ->.
      destruct (IHr _ _ Hbs Hbs' s) as (V & HV & HV').
      exists (d_ind p (ups ++ bs0)), (d_ind p (ups' ++ bs0')), V.
      split; [ constructor; exact E0 | split; [ constructor; exact E0' | split; assumption ] ].
    - (** A domain of a shape: its variables are related at the type's
          parameters, hence at the element's own ([HdI]). *)
      intros pre B u u' pre' t f f' Hf IH ms ms' xs xs' c gs1 t0 gs2 ws ws' k0 ys ys' Hρ Hρ' Ou Ou' Hm Hx Hx' Hc Hw Hs Hk Hy s.
      destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB Hs'].
      assert (Hkl : k0 < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence).
      subst pre pre'.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (trefl _ _ Hm) as Hmm.
      pose proof (tsym _ _ Hx) as Hmx.
      pose proof (tarpl ms c _ Hmm Hc _ ws ws' HK Hw) as Hww.
      pose proof (tarpi _ _ _ _ _ _ _ Hmx Hc HK Hw) as Hwx.
      pose proof (tshi _ _ _ _ _ _ _ _ _ _ _ _ Hmx Hc eq_refl Hww Hk Hy) as Hyx.
      pose proof (ttrans _ _ _ Hx (ttrans _ _ _ Hm (tsym _ _ Hx'))) as Hxx.
      destruct (Hdr xs xs' c _ gs1 t0 gs2 ws ws' k0 B ys ys' Hxx Hc eq_refl Hwx HB Hyx) as (b & b' & Eb & Eb' & Htt & Hbot).
      pose proof (Hbot _ _ (var_per_bot (n := s))) as Hxv.
      pose proof (tshl ms c _ gs1 t0 gs2 ws Hmm Hc eq_refl Hww k0 ys ys' Hk Hy) as Hyy.
      pose proof (proj2 (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ Hmx Hc eq_refl Hww HB Hyy _ _) Hxv) as Hxv'.
      destruct (IH _ _ Hxv' ms ms' xs xs' c gs1 t0 gs2 ws ws' (S k0) (ys ++ ⇑! b s :: nil) (ys' ++ ⇑! b' s :: nil)
                  ltac:(rewrite <- !List.app_assoc; reflexivity) ltac:(rewrite <- !List.app_assoc; reflexivity)
                  Ou Ou' Hm Hx Hx' Hc Hw Hs' ltac:(lia)
                  ltac:(apply tele_prefix_rel_snoc; [ exact Hy | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hxv' ])
                  (S s))
        as (r & r' & a & a' & V & Er & Er' & Ea & Ea' & HV & HV').
      destruct (Htt s) as (A & HA & HA').
      rewrite !List.app_assoc, env_args_snoc in Ea, Ea'; rewrite <- !List.app_assoc in Ea, Ea'.
      eexists _, _, (λⁿ A V); split; [ econstructor; exact Eb | split; [ econstructor; exact Eb' |] ].
      split; (eapply read_nf_fn; [ eassumption | eassumption | apply eval_fam_cod_shfam; eassumption | eassumption ]).
    - intros f x r f' x' r' u u' pre pre' t Ef Ef' Hsh IH ms ms' xs xs' c gs1 t0 gs2 ws ws' k0 ys ys'
        Hρ Hρ' Ou Ou' Hm Hx Hx' Hc Hw Hs Hk Hy s.
      destruct (IH ms ms' xs xs' c gs1 t0 gs2 ws ws' k0 ys ys' Hρ Hρ' Ou Ou' Hm Hx Hx' Hc Hw Hs Hk Hy s)
        as (a & a' & V & Ea & Ea' & HV & HV').
      exists r, r', a, a', V; repeat split; assumption. }
  intros b b' Hb; exact (proj1 Hmain _ _ _ _ Hb _ _ (trefl _ _ Hns) (trefl_r _ _ Hns)).
Qed.

(** The neutrals of an inductive type at its own parameters are elements,
    when its uniform parameters are admissible. *)
Lemma ind_rel_neut_canon : forall p D ups ups' ns ns'
    (nr : nat -> list domain -> relation domain)
    (ar : list domain -> String.string -> nat -> list domain -> relation domain)
    (dr : list domain -> exp -> relation domain) (Ok : list domain -> Prop) c c',
    tele_ass (ind_params D) ->
    (forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) -> tele_prefix_rel nr k vs vs' -> PER (nr k vs)) ->
    (forall k A vs vs', List.nth_error (List.rev (ind_nparams D)) k = Some (ce_ass A) -> tele_prefix_rel nr k vs vs' ->
       (nr k vs <~> nr k vs')) ->
    (forall ms ms' c gs k A vs vs', tele_rel nr (List.rev (ind_nparams D)) ms ms' -> ind_con D c = Some gs ->
       List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar ms c) k vs vs' -> PER (ar ms c k vs)) ->
    (forall ms ms' c gs k A vs vs', tele_rel nr (List.rev (ind_nparams D)) ms ms' -> ind_con D c = Some gs ->
       List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar ms c) k vs vs' -> (ar ms c k vs <~> ar ms' c k vs')) ->
    (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nr (List.rev (ind_nparams D)) ms ms' ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t)) k ys ys' ->
       PER (dr (ms ++ ws ++ ys) B)) ->
    (forall ms ms' c gs gs1 t gs2 ws ws' k B ys ys', tele_rel nr (List.rev (ind_nparams D)) ms ms' ->
       ind_con D c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (ar ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
       List.nth_error (ptyp_doms t) k = Some B -> tele_prefix_rel (shape_doms_rel dr ms ws (ptyp_doms t)) k ys ys' ->
       (dr (ms ++ ws ++ ys) B <~> dr (ms' ++ ws' ++ ys') B)) ->
    List.length ups = ind_nu D -> List.length ups' = ind_nu D ->
    per_top_ps (List.rev (ind_uparams D)) ups ups' ->
    Ok ups' -> Ok ups ->
    tele_rel nr (List.rev (ind_nparams D)) ns ns' ->
    Dom c ≈ c' ∈ per_bot ->
    ind_rel p D Ok nr ar dr ns ns' (⇑ (d_ind p (ups ++ ns)) c) (⇑ (d_ind p (ups' ++ ns')) c').
Proof.
  intros * Hass HnP HnI HaP HaI HdP HdI Hu Hu' Hps Had' Had Hns Hc.
  assert (Hle : ind_nu D <= ind_np D).
  { destruct (Hps 0) as (Ms & HM & _); apply read_ps_length in HM.
    rewrite List.length_rev in HM; unfold ind_uparams in HM; rewrite List.length_skipn in HM.
    unfold ind_nn in HM; unfold ind_np; lia. }
  pose proof Hns as Hl; rewrite tele_rel_iff in Hl; destruct Hl as (Hl1 & Hl2 & _).
  rewrite List.length_rev, length_nparams in Hl1, Hl2.
  constructor.
  - exact Hns.
  - rewrite List.length_app; unfold ind_nn in *; lia.
  - rewrite List.length_app; unfold ind_nn in *; lia.
  - rewrite firstn_app_exact by exact Hu; exact Had.
  - rewrite firstn_app_exact by exact Hu'; exact Had'.
  - rewrite skipn_app_exact by exact Hu; exact (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ Hns).
  - rewrite skipn_app_exact by exact Hu'; exact (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ Hns).
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
  (** An inductive type: [realize_indty], from the realisability of the
      types of its telescopes. *)
  - unshelve epose proof (realize_indty p D ups ups' ns ns' nr ar dr (adm_uparams D ups nr ar dr) H H0 H1 H3 H4 H6 H7 H9 H10 H12 _ _ _
                            (fun u Hu => Hu) (fun u Hu => adm_base p D ups nr ar dr H0 H4 H6 H7 H9 H10 H12 _ _ H13 Hu) H15) as [Hrt _];
    [ intros k A vs vs' Hk Hp; destruct (H5 _ _ _ _ Hk Hp) as [a a' Ea Ea' (_ & _ & _ & Hrb)]; eauto
    | intros ms ms' c0 gs k A vs vs' Hm Hc Hk Hp; destruct (H8 _ _ _ _ _ _ _ _ Hm Hc Hk Hp) as [a a' Ea Ea' (_ & _ & _ & Hrb)]; eauto
    | intros ms ms' c0 gs gs1 t gs2 ws ws' k B ys ys' Hm Hc Heq Hw HB Hy;
      destruct (H11 _ _ _ _ _ _ _ _ _ _ _ _ _ Hm Hc Heq Hw HB Hy) as [a a' Ea Ea' (_ & Htt & Hbot & _)];
      exists a, a'; repeat split; eauto
    | exact Hrt ].
  - eapply ind_rel_neut_canon; eassumption.
  - unshelve epose proof (realize_indty p D ups ups' ns ns' nr ar dr (adm_uparams D ups nr ar dr) H H0 H1 H3 H4 H6 H7 H9 H10 H12 _ _ _
                            (fun u Hu => Hu) (fun u Hu => adm_base p D ups nr ar dr H0 H4 H6 H7 H9 H10 H12 _ _ H13 Hu) H15) as [_ Hre];
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
      destruct (HU _ _ Hρ) as [h h' Hh Hh' Hr] end.
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
