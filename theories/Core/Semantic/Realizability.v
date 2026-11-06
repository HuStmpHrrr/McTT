From Stdlib Require Import Lia Morphisms_Relations PeanoNat Relation_Definitions.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export NbE PER.
From Mctt.Core.Syntactic.System Require Import Scoping.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.


Section Fixed_GCtx.
  Context {GC : GCtx}.


(** ** Reading Back at Telescopes *)

(** The environment of the values of a telescope, one value more, at the
    type of the telescope's next entry. *)
Lemma env_tele_snoc_nth : forall ρ T pre κ A v,
    List.nth_error T (List.length pre) = Some (ce_ass κ A) ->
    env_tele ρ T (pre ++ v :: nil) = env_tele ρ T pre ↦ v ⦂ entry_type_closure A (env_tele ρ T pre).
Proof.
  intros * HA.
  assert (Hlt : List.length pre < List.length T) by (apply List.nth_error_Some; congruence).
  rewrite (env_tele_firstn _ _ (pre ++ v :: nil)), (env_tele_firstn _ _ pre), List.length_app; cbn [List.length].
  rewrite Nat.add_1_r, (firstn_S_snoc _ _ _ HA).
  apply env_tele_snoc; rewrite List.length_firstn; lia.
Qed.

(** The same for the environment of a group's components. *)
Lemma components_env_snoc_nth : forall D u Ts pre κ A v,
    List.nth_error Ts (List.length pre) = Some (ce_ass κ A) ->
    components_env D u Ts (pre ++ v :: nil) = components_env D u Ts pre ↦ v ⦂ entry_type_closure A (components_env D u Ts pre).
Proof. intros * H; unfold components_env; exact (env_tele_snoc_nth _ _ _ _ _ _ H). Qed.

Lemma read_ps_app : forall s ρ T1 vs1 Ms1, Rps vs1 at T1 in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Ms1 ->
    forall T2 vs2 Ms2, Rps vs2 at T2 in gc_deps ⍮ gc_stack ⍮ env_tele ρ T1 vs1 ⍮ s ↘ Ms2 ->
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
    alike read back alike. *)
Lemma read_ps_tele : forall (T : list centry) (tr : nat -> list domain -> relation domain) ρ ρ',
    all_assumptions T ->
    (forall k κ A pre pre', List.nth_error T k = Some (ce_ass κ A) -> tele_prefix_rel tr k pre pre' ->
       exists a a', ⟦ A ⟧ env_tele ρ T pre ↘ a /\ ⟦ A ⟧ env_tele ρ' T pre' ↘ a' /\
         (forall b b', tr k pre b b' -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top)) ->
    forall vs vs', tele_rel tr T vs vs' ->
    forall s, exists Ms Ms', Rps vs at T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Ms /\ Rps vs' at T in gc_deps ⍮ gc_stack ⍮ ρ' ⍮ s ↘ Ms' /\
      nfs_eq_upto_proofs Ms Ms'.
Proof.
  intros * Hass Hev vs vs' Hf s.
  pose proof Hf as Hf'; rewrite tele_rel_iff in Hf'; destruct Hf' as (Hl & Hl' & Hr).
  assert (Hall : forall m j, m + j = List.length T ->
             exists Ms Ms', Rps List.skipn j vs at List.skipn j T in gc_deps ⍮ gc_stack ⍮ env_tele ρ T (List.firstn j vs) ⍮ s ↘ Ms /\
                        Rps List.skipn j vs' at List.skipn j T in gc_deps ⍮ gc_stack ⍮ env_tele ρ' T (List.firstn j vs') ⍮ s ↘ Ms' /\
                        nfs_eq_upto_proofs Ms Ms').
  { induction m as [| m IH]; intros j Hj.
    - rewrite !List.skipn_all2 by lia; exists nil, nil; split; [ constructor | split; [ constructor | reflexivity ] ].
    - destruct (nth_error_lt_some' T j ltac:(lia)) as [e He].
      destruct (nth_error_lt_some' vs j ltac:(lia)) as [v Hv].
      destruct (nth_error_lt_some' vs' j ltac:(lia)) as [v' Hv'].
      assert (He' : exists κ A, e = ce_ass κ A)
        by (unfold all_assumptions in Hass; rewrite List.Forall_forall in Hass; apply Hass; eapply List.nth_error_In; exact He).
      destruct He' as (κ & A & ->).
      destruct (Hev _ _ _ _ _ He (tele_prefix_rel_of_full _ _ _ _ j Hf ltac:(lia))) as (a & a' & Ea & Ea' & Hrb).
      destruct (Hrb _ _ (Hr _ _ _ Hv Hv') s) as [V V' HV HV' HE].
      destruct (IH (S j) ltac:(lia)) as (Ms & Ms' & HM & HM' & HEs).
      assert (Hj1 : List.length (List.firstn j vs) = j) by (rewrite List.length_firstn; lia).
      assert (Hj2 : List.length (List.firstn j vs') = j) by (rewrite List.length_firstn; lia).
      rewrite (firstn_S_snoc _ _ _ Hv), (env_tele_snoc_nth _ _ _ κ A) in HM by (rewrite Hj1; exact He).
      rewrite (firstn_S_snoc _ _ _ Hv'), (env_tele_snoc_nth _ _ _ κ A) in HM' by (rewrite Hj2; exact He).
      exists (cons V Ms), (cons V' Ms').
      rewrite (skipn_nth_cons' _ _ _ He), (skipn_nth_cons' _ _ _ Hv), (skipn_nth_cons' _ _ _ Hv').
      split; [ econstructor; eassumption | split; [ econstructor; eassumption | apply nfs_eq_upto_proofs_cons; split; assumption ] ]. }
  destruct (Hall (List.length T) 0 ltac:(lia)) as (Ms & Ms' & HM & HM' & HE); exists Ms, Ms'; repeat split; assumption.
Qed.

Lemma rev_im_params_split : forall D M, List.rev (im_params D M) = List.rev (ind_uparams D) ++ List.rev (im_nparams M).
Proof. intros; unfold im_params; rewrite List.rev_app_distr; reflexivity. Qed.

Lemma read_ps_length : forall s ρ T vs Ms, Rps vs at T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Ms -> List.length vs = List.length T.
Proof. induction 1; cbn; congruence. Qed.

(** As many normal forms as values. *)
Lemma read_ps_length_nf : forall s ρ T vs Ms, Rps vs at T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Ms -> List.length Ms = List.length vs.
Proof. induction 1; cbn; congruence. Qed.

(** Value [j] of a telescope reads back at its type, evaluated in the
    environment of the values before it: for [Rps (v0 :: v1 :: nil) at
    (A0 :: A1 :: nil) in ρ ↘ (R0 :: R1 :: nil)], [R1] is [v1] read at
    [⟦A1⟧ (ρ ↦ v0 ⦂ entry_type_closure A0 ρ)]. *)
Lemma read_ps_nth_type : forall s ρ T vs Rs, Rps vs at T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Rs ->
    forall j κ A v R, List.nth_error T j = Some (ce_ass κ A) -> List.nth_error vs j = Some v -> List.nth_error Rs j = Some R ->
      exists a, ⟦ A ⟧ env_tele ρ T (List.firstn j vs) ↘ a /\ Rnf ⇓ a v in gc_deps ⍮ gc_stack ⍮ s ↘ R.
Proof.
  induction 1 as [| ? ? ? ? ? ? ? ? ? ? Ha0 HV0 _ IH]; intros [| j] κ1 A1 v1 R1 HA Hv HR; cbn in HA, Hv, HR; try discriminate.
  - injection HA as <- <-; injection Hv as <-; injection HR as <-; eexists; split; [ exact Ha0 | exact HV0 ].
  - exact (IH _ _ _ _ _ HA Hv HR).
Qed.

(** At a propositional type every value reads back as a proof term
    ([read_nf_proof] is the only rule there). *)
Lemma read_nf_propositional : forall s a v W, domain_kind a = ak_propositional ->
    Rnf ⇓ a v in gc_deps ⍮ gc_stack ⍮ s ↘ W -> exists P, W = nf_proof P.
Proof.
  intros * Ha H; inversion H; subst; cbn in *; try congruence; eauto;
    exfalso; eapply evaluated_kind_not_propositional; eassumption.
Qed.

(** The codomain of the type of an argument of a function shape, at an
    argument. *)
Lemma eval_fam_cod_shfam : forall p ups ρ B t x a tf tx,
    ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↦ x ⦂ entry_type_closure B ρ ↘ a ->
    ⟦ fam_cod ⟧ nil ↦ d_shfam p ups ρ B t ⦂ tf ↦ x ⦂ tx ↘ a.
Proof.
  intros; unfold fam_cod; eapply eval_exp_app; [ apply eval_exp_var | cbn; constructor | apply eval_exp_var | econstructor; eassumption ].
Qed.

(** The type of a shape is relevant: a member, a record or a [Π]. *)
Lemma eval_shape_type_relevant : forall p ups ρ t a,
    ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ a -> domain_kind a = ak_relevant.
Proof. intros * H; inversion H; reflexivity. Qed.

Lemma eval_fam_cod_ihfam : forall ρm A p ups ρ B t i f x fx as' a tf tx,
    $| f & x | gc_deps ⍮ gc_stack ↘ fx ->
    ⟦ihty fx of t at p ups under ρm A ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↦ x ⦂ entry_type_closure B ρ ↘ as' ->
    List.nth_error as' i = Some a ->
    ⟦ fam_cod ⟧ nil ↦ d_ihfam ρm A p ups ρ B t i f ⦂ tf ↦ x ⦂ tx ↘ a.
Proof.
  intros; unfold fam_cod; eapply eval_exp_app; [ apply eval_exp_var | cbn; constructor | apply eval_exp_var | econstructor; eassumption ].
Qed.

(** The environment of the uniform parameters [ups] of a group and the
    non-uniform ones [xs] of a member, as a member's parameter telescope
    has it, is that of the member's components. *)
Lemma env_params_components : forall D Mk ups xs, List.length ups = ind_nu D ->
    env_tele nil (List.rev (im_params D Mk)) (ups ++ xs) = components_env D ups (List.rev (im_nparams Mk)) xs.
Proof.
  intros * Hu; rewrite rev_im_params_split, env_tele_app; [ reflexivity |].
  rewrite List.length_rev; exact Hu.
Qed.

(** The environment of the components of a constructor's member and of
    the non-recursive arguments [vp] of [gs1], read by the declared type of
    a later non-recursive argument: only the telescope of [gs1] is read. *)
Lemma components_env_args_prefix : forall D u (Mk : imember) gs1 gs xs vp,
    List.length xs = List.length (im_nparams Mk) -> List.length vp = List.length gs1 ->
    components_env D u (List.rev (im_nparams Mk) ++ cargs_nonrec_tele (gs1 ++ gs)) (xs ++ nonrec_arg_vals gs1 vp)
    = components_env D u (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) (xs ++ nonrec_arg_vals gs1 vp).
Proof.
  intros * Hx Hv.
  rewrite cargs_nonrec_tele_app, List.app_assoc.
  apply components_env_prefix.
  rewrite !List.length_app, List.length_rev, length_nonrec_arg_vals by exact Hv.
  rewrite length_cargs_nonrec_tele; lia.
Qed.

(** One non-recursive argument more. *)
Lemma components_env_args_snoc : forall D u (Mk : imember) gs1 rA A xs vp v,
    List.length xs = List.length (im_nparams Mk) -> List.length vp = List.length gs1 ->
    components_env D u (List.rev (im_nparams Mk) ++ cargs_nonrec_tele (gs1 ++ ca_arg rA A :: nil))
      (xs ++ nonrec_arg_vals (gs1 ++ ca_arg rA A :: nil) (vp ++ v :: nil))
    = components_env D u (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) (xs ++ nonrec_arg_vals gs1 vp)
        ↦ v ⦂ entry_type_closure A (components_env D u (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) (xs ++ nonrec_arg_vals gs1 vp)).
Proof.
  intros * Hx Hv.
  rewrite cargs_nonrec_tele_snoc_arg, nonrec_arg_vals_app by exact Hv; cbn [nonrec_arg_vals].
  rewrite !List.app_assoc; apply components_env_snoc.
  rewrite !List.length_app, List.length_rev, length_nonrec_arg_vals by exact Hv.
  rewrite length_cargs_nonrec_tele; lia.
Qed.

(** One recursive argument more: nothing joins the environment. *)
Lemma components_env_args_snoc_rec : forall D u (Mk : imember) gs1 t xs vp v,
    List.length vp = List.length gs1 ->
    components_env D u (List.rev (im_nparams Mk) ++ cargs_nonrec_tele (gs1 ++ ca_rec t :: nil))
      (xs ++ nonrec_arg_vals (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil))
    = components_env D u (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) (xs ++ nonrec_arg_vals gs1 vp).
Proof.
  intros * Hv.
  rewrite cargs_nonrec_tele_snoc_rec, nonrec_arg_vals_app by exact Hv; cbn [nonrec_arg_vals].
  rewrite List.app_nil_r; reflexivity.
Qed.

(** The environment of a recursive argument's components, at its shape's
    first [List.length ys] domains: only those domains are read. *)
Lemma components_env_shape_prefix : forall D u (Mk : imember) gs1 t xs ws ys,
    List.length xs = List.length (im_nparams Mk) -> List.length ws = List.length (cargs_nonrec gs1) ->
    List.length ys <= List.length (ptyp_doms t) ->
    components_env D u (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (xs ++ ws ++ ys)
    = components_env D u (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn (List.length ys) (shape_doms_tele t))
        (xs ++ ws ++ ys).
Proof.
  intros * Hx Hw Hy.
  rewrite <- (List.firstn_skipn (List.length ys) (shape_doms_tele t)) at 1.
  rewrite !List.app_assoc; apply components_env_prefix.
  rewrite !List.length_app, List.length_rev, List.length_firstn, length_cargs_nonrec_tele; unfold shape_doms_tele;
    rewrite !List.length_map; lia.
Qed.

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
    (dr : nat -> list domain -> list centry -> exp -> relation domain),
    ind_lookup gc_deps gc_stack p = Some D ->
    group_structure D ->
    List.length ups = ind_nu D ->
    per_top_ps (List.rev (ind_uparams D)) ups ups' ->
    nparams_per D nr -> nparams_inv D nr -> args_per D nr ar -> args_inv D nr ar ->
    doms_per D nr ar dr -> doms_inv D nr ar dr ->
    (forall m Mm k κ A vs vs', ind_member D m = Some Mm ->
       List.nth_error (List.rev (im_nparams Mm)) k = Some (ce_ass κ A) -> tele_prefix_rel (nr m) k vs vs' ->
       exists a a', ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm)) vs ↘ a /\
         ⟦ A ⟧ components_env D ups' (List.rev (im_nparams Mm)) vs' ↘ a' /\
         (forall b b', nr m k vs b b' -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top)) ->
    (forall m Mm ms ms' c gs k A vs vs', ind_member D m = Some Mm ->
       tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' -> ind_con Mm c = Some gs ->
       List.nth_error (cargs_nonrec gs) k = Some A -> tele_prefix_rel (ar m ms c) k vs vs' ->
       exists a a', ⟦ A ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms ++ vs) ↘ a /\
         ⟦ A ⟧ components_env D ups' (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs) (ms' ++ vs') ↘ a' /\
         (forall b b', ar m ms c k vs b b' -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top)) ->
    (forall m Mm ms ms' c gs gs1 t gs2 ws ws' k B ys ys', ind_member D m = Some Mm ->
       tele_rel (nr m) (List.rev (im_nparams Mm)) ms ms' ->
       ind_con Mm c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
       tele_prefix_rel (ar m ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
       List.nth_error (ptyp_doms t) k = Some B ->
       tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) ms ws t) k ys ys' ->
       exists a a', ⟦ B ⟧ components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ms ++ ws ++ ys) ↘ a /\
         ⟦ B ⟧ components_env D ups' (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t) (ms' ++ ws' ++ ys') ↘ a' /\
         Dom a ≈ a' ∈ per_top_typ /\
         (forall c c', Dom c ≈ c' ∈ per_bot -> dr m (ms ++ ws ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t)) B
           (⇑ a c) (⇑ a' c'))) ->
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
  { destruct (Hps 0) as [? ? _ HM _]; apply read_ps_length in HM.
    rewrite List.length_rev in HM; unfold ind_nu; lia. }
  assert (Hpar : forall m Mm xs xs', ind_member D m = Some Mm -> tele_rel (nr m) (List.rev (im_nparams Mm)) xs xs' ->
             per_top_ps (List.rev (im_params D Mm)) (ups ++ xs) (ups' ++ xs')).
  { intros m Mm xs xs' HM Hx s.
    destruct (Hps s) as [Ms1 Ms1' HM1 HM1' HE1].
    assert (Hassn : all_assumptions (List.rev (im_nparams Mm)))
      by (apply List.Forall_rev; exact (group_structure_nparams _ Hass _ _ HM)).
    destruct (read_ps_tele (List.rev (im_nparams Mm)) (nr m) (decl_env D ups) (decl_env D ups') Hassn
                (fun k κ A pre pre' Hk Hp => Hn _ _ _ _ _ _ _ HM Hk Hp) _ _ Hx s) as (Ms2 & Ms2' & HM2 & HM2' & HE2).
    rewrite rev_im_params_split.
    apply (mk_params_read_alike _ _ _ _ (Ms1 ++ Ms2) (Ms1' ++ Ms2'));
      [ apply read_ps_app; assumption | apply read_ps_app; assumption | apply nfs_eq_upto_proofs_app; assumption ]. }
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
    (forall k u u' pre pre' Ts gs vs vs', con_args_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts gs vs vs' ->
       forall Mk ms ms' xs xs' c gsf gs1 vp vp', ind_member D k = Some Mk ->
         pre = ms ++ nonrec_arg_vals gs1 vp -> pre' = ms' ++ nonrec_arg_vals gs1 vp' ->
         Ts = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ->
         List.length vp = List.length gs1 -> List.length vp' = List.length gs1 ->
         tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms' ->
         tele_rel (nr k) (List.rev (im_nparams Mk)) xs ms -> tele_rel (nr k) (List.rev (im_nparams Mk)) xs' ms' ->
         ind_con Mk c = Some gsf -> gsf = gs1 ++ gs ->
         tele_rel (ar k ms c) (cargs_nonrec gsf) (nonrec_arg_vals gsf (vp ++ vs)) (nonrec_arg_vals gsf (vp' ++ vs')) ->
         forall s, exists Vs Vs',
           Rcargs vs at gs of p ups in gc_deps ⍮ gc_stack ⍮ components_env D ups Ts (xs ++ nonrec_arg_vals gs1 vp) ⍮ s ↘ Vs /\
           Rcargs vs' at gs of p ups' in gc_deps ⍮ gc_stack ⍮ components_env D ups' Ts (xs' ++ nonrec_arg_vals gs1 vp') ⍮ s ↘ Vs' /\
           nfs_eq_upto_proofs Vs Vs') /\
    (forall k u u' pre pre' Ts t v v', rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts t v v' ->
       forall Mk ms ms' xs xs' c gs1 t0 gs2 ws ws' kk ys ys', ind_member D k = Some Mk ->
         pre = ms ++ ws ++ ys -> pre' = ms' ++ ws' ++ ys' ->
         Ts = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kk (shape_doms_tele t0) ->
         tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms' ->
         tele_rel (nr k) (List.rev (im_nparams Mk)) xs ms -> tele_rel (nr k) (List.rev (im_nparams Mk)) xs' ms' ->
         ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
         tele_prefix_rel (ar k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
         ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
         tele_prefix_rel (shape_doms_rel (dr k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ms ws t0) kk ys ys' ->
         forall s, exists V V', Rsh v at t of p ups in gc_deps ⍮ gc_stack ⍮ components_env D ups Ts (xs ++ ws ++ ys) ⍮ s ↘ V /\
           Rsh v' at t of p ups' in gc_deps ⍮ gc_stack ⍮ components_env D ups' Ts (xs' ++ ws' ++ ys') ⍮ s ↘ V' /\
           nf_eq_upto_proofs V V') /\
    (forall k u u' pre pre' Ts t f x f' x', rec_arg_app_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts t f x f' x' ->
       forall Mk ms ms' xs xs' c gs1 t0 gs2 ws ws' kk ys ys', ind_member D k = Some Mk ->
         pre = ms ++ ws ++ ys -> pre' = ms' ++ ws' ++ ys' ->
         Ts = List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1 ++ List.firstn kk (shape_doms_tele t0) ->
         tele_rel (nr k) (List.rev (im_nparams Mk)) ms ms' ->
         tele_rel (nr k) (List.rev (im_nparams Mk)) xs ms -> tele_rel (nr k) (List.rev (im_nparams Mk)) xs' ms' ->
         ind_con Mk c = Some (gs1 ++ ca_rec t0 :: gs2) ->
         tele_prefix_rel (ar k ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
         ptyp_skip kk t0 = t -> kk <= List.length (ptyp_doms t0) ->
         tele_prefix_rel (shape_doms_rel (dr k) (List.rev (im_nparams Mk)) (cargs_nonrec_tele gs1) ms ws t0) kk ys ys' ->
         forall s, exists r r' V V', $| f & x | gc_deps ⍮ gc_stack ↘ r /\ $| f' & x' | gc_deps ⍮ gc_stack ↘ r' /\
           Rsh r at t of p ups in gc_deps ⍮ gc_stack ⍮ components_env D ups Ts (xs ++ ws ++ ys) ⍮ s ↘ V /\
           Rsh r' at t of p ups' in gc_deps ⍮ gc_stack ⍮ components_env D ups' Ts (xs' ++ ws' ++ ys') ⍮ s ↘ V' /\
           nf_eq_upto_proofs V V')).
  { apply ind_rel_mut_ind_all.
    - (** A constructor: its parameters off the type, its arguments at the
          member's telescopes, at a declared member or a view alike. *)
      intros k0 Mk0 hd k' ns0 ns0' c gs bs bs' vs vs' u u' HM Hrv Hr Hn0 Hc Hb Hb' Hs Hs' Ha0 Hia IH Mk1 xs xs' HM1 Hx Hx' s.
      rewrite HM in HM1; injection HM1 as <-.
      assert (Hxx : tele_rel (nr k0) (List.rev (im_nparams Mk0)) xs xs')
        by exact (ttrans _ _ HM _ _ _ Hx (ttrans _ _ HM _ _ _ Hn0 (tsym _ _ HM _ _ Hx'))).
      destruct (Hpar _ _ _ _ HM Hxx s) as [Ms Ms' HMs HMs' HEs].
      destruct (Hlen _ _ _ _ HM Hxx) as [Hl1 Hl2].
      assert (Hvl : List.length vs = List.length gs /\ List.length vs' = List.length gs).
      { clear - Hia; induction Hia; cbn; [ split; reflexivity | | ]; destruct IHHia; split; congruence. }
      destruct (IH Mk0 (List.skipn (im_unu D Mk0) bs) (List.skipn (im_unu D Mk0) bs') xs xs' c gs nil nil nil HM
                   ltac:(cbn; rewrite List.app_nil_r; reflexivity) ltac:(cbn; rewrite List.app_nil_r; reflexivity)
                   ltac:(cbn; rewrite List.app_nil_r; reflexivity)
                   eq_refl eq_refl
                   (ttrans _ _ HM _ _ _ (ttrans _ _ HM _ _ _ (tsym _ _ HM _ _ Hs) Hn0) Hs')
                   (ttrans _ _ HM _ _ _ Hx Hs) (ttrans _ _ HM _ _ _ Hx' Hs') Hc eq_refl Ha0 s) as (Vs & Vs' & HV & HV' & HEv).
      cbn [nonrec_arg_vals List.app] in HV, HV'; rewrite List.app_nil_r in HV, HV'.
      (** The two constructors agree up to proofs part by part. *)
      assert (HE : nf_eq_upto_proofs (nf_con p k0 c (Ms ++ Vs)) (nf_con p k0 c (Ms' ++ Vs')))
        by (apply nf_con_upto_proofs, nfs_eq_upto_proofs_app; assumption).
      unfold im_ref in Hr; destruct (im_head Mk0) as [pm | qc kc Is vm | qr Is fl] eqn:Hh; injection Hr as <- <-;
        [| | exfalso; exact (not_rview_record _ _ _ _ Hrv Hh) ].
      + assert (Hu0 : im_unu D Mk0 = ind_nu D) by (unfold im_unu; rewrite Hh; reflexivity).
        apply (mk_normal_reads_alike _ _ _ (nf_con p k0 c (Ms ++ Vs)%list) (nf_con p k0 c (Ms' ++ Vs')%list)); [ | | exact HE ];
          (eapply read_nf_con; [ exact Hl | exact HM | exact Hh | exact Hc | eassumption | | eassumption |]).
        * rewrite List.length_app; unfold im_np, im_nn in *; lia.
        * rewrite env_params_components, firstn_app_exact by exact Hu;
            rewrite skipn_app_exact by (unfold im_np, im_nn in *; lia); exact HV.
        * rewrite List.length_app; unfold im_np, im_nn in *; lia.
        * rewrite env_params_components, firstn_app_exact by exact Hu';
            rewrite skipn_app_exact by (unfold im_np, im_nn in *; lia); exact HV'.
      + apply (mk_normal_reads_alike _ _ _ (nf_con p k0 c (Ms ++ Vs)%list) (nf_con p k0 c (Ms' ++ Vs')%list)); [ | | exact HE ].
        * eapply read_nf_con_view with (n := List.length bs);
            [ exact Hl | exact HM | exact Hh | exact Hc | exact Hl1 | rewrite List.length_app; lia | exact HMs |].
          rewrite env_params_components, firstn_app_exact by exact Hu; rewrite skipn_app_exact by reflexivity; exact HV.
        * eapply read_nf_con_view with (n := List.length bs');
            [ exact Hl | exact HM | exact Hh | exact Hc | exact Hl2 | rewrite List.length_app; lia | exact HMs' |].
          rewrite env_params_components, firstn_app_exact by exact Hu'; rewrite skipn_app_exact by reflexivity; exact HV'.
    - intros k0 Mk0 hd k' ns0 ns0' as1 as2 m m' _ _ HM Hrv _ _ _ _ _ _ Hm Mk1 xs xs' _ _ _ s;
        destruct (Hm s) as [L L' HL HL' HE].
      apply (mk_normal_reads_alike _ _ _ (⇑ⁿ{ak_relevant} L) (⇑ⁿ{ak_relevant} L'));
        [ eapply read_nf_ind_neut; [ exact Hl | exact HM | exact Hrv | exact HL ]
        | eapply read_nf_ind_neut; [ exact Hl | exact HM | exact Hrv | exact HL' ]
        | unfold nf_eq_upto_proofs; cbn [nf_eqb_upto_proofs]; rewrite dec_eqb_refl; exact HE ].
    - (** A record view: its projections at the pseudo-constructor's
          arguments, at the group's uniform parameters only. *)
      intros k0 Mk0 qr Is fl c gs v vs v' vs' u u' HM Hh Hnp Hcs Hp Hp' Ha0 Hia IH Mk1 xs xs' HM1 Hx Hx' s.
      rewrite HM in HM1; injection HM1 as <-.
      pose proof (ind_con_single _ _ _ Hcs) as Hc.
      assert (Hn0 : tele_rel (nr k0) (List.rev (im_nparams Mk0)) nil nil) by (rewrite Hnp; split; reflexivity + exact I).
      assert (Hxs : forall zs, tele_rel (nr k0) (List.rev (im_nparams Mk0)) zs nil -> zs = nil)
        by (intros zs [Hz _]; rewrite Hnp in Hz; destruct zs; [ reflexivity | discriminate Hz ]).
      rewrite (Hxs _ Hx), (Hxs _ Hx') in *; rewrite !List.app_nil_r.
      destruct (IH Mk0 nil nil nil nil c gs nil nil nil HM eq_refl eq_refl ltac:(rewrite Hnp; reflexivity)
                  eq_refl eq_refl Hn0 Hn0 Hn0 Hc eq_refl Ha0 s)
        as (Vs & Vs' & HV & HV' & HEv).
      destruct (Hps s) as [Ms Ms' HMs HMs' HEs].
      apply (mk_normal_reads_alike _ _ _ (nf_con p k0 c (Ms ++ Vs)%list) (nf_con p k0 c (Ms' ++ Vs')%list));
        [ eapply read_nf_rview; [ exact Hl | exact HM | exact Hh | exact Hcs | assumption | eassumption | exact HMs | exact HV ]
        | eapply read_nf_rview; [ exact Hl | exact HM | exact Hh | exact Hcs | assumption | eassumption | exact HMs' | exact HV' ]
        | apply nf_con_upto_proofs, nfs_eq_upto_proofs_app; assumption ].
    - intros; exists nil, nil; split; [ constructor | split; [ constructor | reflexivity ] ].
    - intros k0 u u' pre v pre' v' Ts rA A gs vs vs' Hia IH Mk0 ms ms' xs xs' c gsf gs1 vp vp' HM Hρ Hρ' HTs Hl1 Hl2 Hm Hx Hx'
        Hc Heq Ha0 s.
      subst pre pre' gsf Ts.
      assert (Hxl : List.length xs = List.length (im_nparams Mk0) /\ List.length xs' = List.length (im_nparams Mk0)).
      { pose proof Hx as Hxl; pose proof Hx' as Hxl'; rewrite tele_rel_iff in Hxl, Hxl';
          destruct Hxl as (Hxl & _ & _), Hxl' as (Hxl' & _ & _); rewrite List.length_rev in Hxl, Hxl'; split; assumption. }
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
      (** The argument's type reads only the telescope before it. *)
      rewrite components_env_args_prefix in Ea, Ea' by (apply Hxl || assumption).
      destruct (Hrb _ _ Hrel' s) as [V V' HV HV' HEV].
      destruct (IH Mk0 ms ms' xs xs' c (gs1 ++ ca_arg rA A :: gs) (gs1 ++ ca_arg rA A :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil) HM
                  ltac:(rewrite nonrec_arg_vals_app by assumption; cbn; rewrite List.app_assoc; reflexivity)
                  ltac:(rewrite nonrec_arg_vals_app by assumption; cbn; rewrite List.app_assoc; reflexivity)
                  ltac:(rewrite cargs_nonrec_tele_snoc_arg, List.app_assoc; reflexivity)
                  ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                  Hm Hx Hx' Hc ltac:(rewrite <- List.app_assoc; reflexivity) ltac:(rewrite <- !List.app_assoc; exact Ha0) s)
        as (Vs & Vs' & HVs & HVs' & HEs).
      rewrite <- List.app_assoc, <- (cargs_nonrec_tele_snoc_arg gs1 rA A) in HVs, HVs'.
      rewrite components_env_args_snoc in HVs, HVs' by (apply Hxl || assumption).
      exists (cons V Vs), (cons V' Vs');
        split; [ econstructor; eassumption | split; [ econstructor; eassumption | apply nfs_eq_upto_proofs_cons; split; assumption ] ].
    - intros k0 u u' pre pre' Ts t v v' gs vs vs' Hsh IHs Hia IH Mk0 ms ms' xs xs' c gsf gs1 vp vp' HM Hρ Hρ' HTs Hl1 Hl2 Hm Hx Hx'
        Hc Heq Ha0 s.
      subst pre pre' gsf Ts.
      pose proof (nonrec_prefix_gen _ _ _ _ _ _ _ _ eq_refl Hl1 Hl2 Ha0) as Hpre.
      destruct (IHs Mk0 ms ms' xs xs' c gs1 t gs (nonrec_arg_vals gs1 vp) (nonrec_arg_vals gs1 vp') 0 nil nil HM
                  ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity)
                  ltac:(cbn [List.firstn]; rewrite List.app_nil_r; reflexivity)
                  Hm Hx Hx' Hc Hpre eq_refl ltac:(lia) (tele_prefix_rel_nil _) s)
        as (V & V' & HV & HV' & HEV).
      rewrite List.app_nil_r in HV, HV'.
      destruct (IH Mk0 ms ms' xs xs' c (gs1 ++ ca_rec t :: gs) (gs1 ++ ca_rec t :: nil) (vp ++ v :: nil) (vp' ++ v' :: nil) HM
                  ltac:(rewrite nonrec_arg_vals_app by assumption; cbn; rewrite List.app_nil_r; reflexivity)
                  ltac:(rewrite nonrec_arg_vals_app by assumption; cbn; rewrite List.app_nil_r; reflexivity)
                  ltac:(rewrite cargs_nonrec_tele_snoc_rec; reflexivity)
                  ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                  Hm Hx Hx' Hc ltac:(rewrite <- List.app_assoc; reflexivity) ltac:(rewrite <- !List.app_assoc; exact Ha0) s)
        as (Vs & Vs' & HVs & HVs' & HEs).
      rewrite nonrec_arg_vals_app in HVs, HVs' by assumption; cbn [nonrec_arg_vals] in HVs, HVs';
        rewrite List.app_nil_r in HVs, HVs'.
      exists (cons V Vs), (cons V' Vs');
        split; [ econstructor; eassumption | split; [ econstructor; eassumption | apply nfs_eq_upto_proofs_cons; split; assumption ] ].
    - (** The end of a shape: the index at the type's prefix is related to
          the element's own through the index at the element's own prefix
          ([admissible_index_at]), the two prefixes related by [Hcd] on the left and by
          [Hcl] on the right. *)
      intros Ps u Ts pre bs u' pre' bs' j v v' k0 _ _ O O' Hr IHr Mk0 ms ms' xs xs' c gs1 t0 gs2 ws ws' k1 ys ys'
        HM Hρ Hρ' HTs Hm Hx Hx' Hc Hw Hs Hk Hy s.
      destruct (ptyp_skip_self _ _ _ _ Hs) as (Hkd & Hj & HPs).
      subst pre pre' Ts.
      (** At the end of the shape, the telescope is all of its domains. *)
      rewrite shape_doms_tele_firstn_all in O, O' |- * by lia.
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
      assert (Hyxf : tele_rel (shape_doms_rel (dr k0) (List.rev (im_nparams Mk0)) (cargs_nonrec_tele gs1) xs ws t0) (ptyp_doms t0) ys ys)
        by (destruct Hyx as [Hyl Hya]; split; [ lia | exact Hya ]).
      assert (Hyf' : tele_rel (shape_doms_rel (dr k0) (List.rev (im_nparams Mk0)) (cargs_nonrec_tele gs1) ms' ws' t0) (ptyp_doms t0) ys' ys')
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
      destruct (IHr Mj bT bT' HMj Hb1 Hb2 s) as [V V' HV HV' HE].
      exists V, V'; split; [ econstructor; eassumption | split; [ econstructor; eassumption | exact HE ] ].
    - (** A domain of a shape: its variables are related at the type's
          parameters, hence at the element's own ([HdI]). *)
      intros k0 pre Ts B u u' pre' t f f' Hf IH _ _ Mk0 ms ms' xs xs' c gs1 t0 gs2 ws ws' k1 ys ys' HM Hρ Hρ' HTs Hm Hx Hx' Hc Hw Hs Hk
        Hy s.
      destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB Hs'].
      assert (Hkl : k1 < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence).
      subst pre pre' Ts.
      (** The lengths of the components before the domain. *)
      assert (Hxl : List.length xs = List.length (im_nparams Mk0)).
      { pose proof Hx as Hxl; rewrite tele_rel_iff in Hxl; destruct Hxl as (Hxl & _ & _); rewrite List.length_rev in Hxl; exact Hxl. }
      assert (Hxl' : List.length xs' = List.length (im_nparams Mk0)).
      { pose proof Hx' as Hl0; rewrite tele_rel_iff in Hl0; destruct Hl0 as (Hl0 & _ & _); rewrite List.length_rev in Hl0; exact Hl0. }
      assert (Hwl : List.length ws = List.length (cargs_nonrec gs1) /\ List.length ws' = List.length (cargs_nonrec gs1)).
      { pose proof Hw as Hwl; rewrite tele_prefix_rel_iff in Hwl; destruct Hwl as (? & ? & _); split; assumption. }
      assert (Hyl : List.length ys = k1 /\ List.length ys' = k1).
      { pose proof Hy as Hyl; rewrite tele_prefix_rel_iff in Hyl; destruct Hyl as (? & ? & _); split; assumption. }
      destruct Hwl as [Hwl Hwl'], Hyl as [Hyl Hyl'].
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
      destruct (IH _ _ Hxv' Mk0 ms ms' xs xs' c gs1 t0 gs2 ws ws' (S k1) (ys ++ ⇑! b s :: nil)
                  (ys' ++ ⇑! b' s :: nil) HM
                  ltac:(rewrite <- !List.app_assoc; reflexivity) ltac:(rewrite <- !List.app_assoc; reflexivity)
                  ltac:(apply prefix_tele_snoc_dom; exact HB)
                  Hm Hx Hx' Hc Hw Hs' ltac:(lia)
                  ltac:(apply tele_prefix_rel_snoc; [ exact Hy | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hxv' ])
                  (S s))
        as (r & r' & V & V' & Er & Er' & HV & HV' & HEV).
      destruct (Htt s) as [A A' HA HA' HEA].
      (** The domain's type reads only the domains before it, and the rest
          of the shape is read with its variable joined at that type. *)
      rewrite components_env_shape_prefix in Eb, Eb' by (assumption || lia).
      rewrite Hyl in Eb; rewrite Hyl' in Eb'.
      rewrite (List.app_assoc ws ys), (List.app_assoc xs (ws ++ ys)), components_env_snoc in HV
        by (rewrite !List.length_app, List.length_rev, List.length_firstn, length_cargs_nonrec_tele; unfold shape_doms_tele;
            rewrite !List.length_map; lia).
      rewrite (List.app_assoc ws' ys'), (List.app_assoc xs' (ws' ++ ys')), components_env_snoc in HV'
        by (rewrite !List.length_app, List.length_rev, List.length_firstn, length_cargs_nonrec_tele; unfold shape_doms_tele;
            rewrite !List.length_map; lia).
      exists (λⁿ A V), (λⁿ A' V');
        split; [ econstructor; eassumption | split; [ econstructor; eassumption | apply nf_fn_upto_proofs; assumption ] ].
    - intros f x r f' x' r' k0 u u' pre pre' Ts t Ef Ef' Hsh IH Mk0 ms ms' xs xs' c gs1 t0 gs2 ws ws' k1 ys ys'
        HM Hρ Hρ' HTs Hm Hx Hx' Hc Hw Hs Hk Hy s.
      destruct (IH Mk0 ms ms' xs xs' c gs1 t0 gs2 ws ws' k1 ys ys' HM Hρ Hρ' HTs Hm Hx Hx' Hc Hw Hs Hk Hy s)
        as (V & V' & HV & HV' & HE).
      exists r, r', V, V'; repeat split; assumption. }
  intros k Mk ns ns' HMk Hns; split.
  { intros s; destruct (Hpar _ _ _ _ HMk Hns s) as [Ms Ms' HM HM' HE].
    destruct (Hlen _ _ _ _ HMk Hns) as [Hl1 Hl2].
    apply (mk_type_reads_alike _ _ _ (nf_indty p k Ms) (nf_indty p k Ms'));
      [ econstructor; eassumption | econstructor; eassumption | apply nf_indty_upto_proofs; assumption ]. }
  intros u u' b b' Hb; exact (proj1 Hmain _ _ _ _ _ _ _ Hb _ _ _ HMk (trefl _ _ HMk _ _ Hns) (trefl_r _ _ HMk _ _ Hns)).
Qed.

(** The neutrals of a declared member at the type's own parameters are
    elements, when its uniform parameters are admissible. *)
Lemma ind_rel_neut_canon : forall p D ups ups'
    (nr : nat -> nat -> list domain -> relation domain)
    (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain)
    (dr : nat -> list domain -> list centry -> exp -> relation domain)
    (okr : nat -> list domain -> list centry -> list exp -> list domain -> Prop)
    k Mk pm ns ns' c c',
    group_structure D ->
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
Lemma eval_neutral_fields_firstn : forall m ρ fl rs, eval_neutral_fields gc_deps gc_stack m ρ fl rs ->
    forall n, eval_neutral_fields gc_deps gc_stack m ρ (List.firstn n fl) (List.firstn n rs).
Proof.
  induction 1; intros [| n]; cbn [List.firstn]; econstructor; eauto.
Qed.

Lemma eval_neutral_fields_length : forall m ρ fl rs, eval_neutral_fields gc_deps gc_stack m ρ fl rs ->
    List.length rs = List.length fl.
Proof. induction 1; cbn; congruence. Qed.

(** The environment of a record type's parameters and of the projections
    of its first fields, one projection more, at its field's type. *)
(** The fields' telescope, outermost first, has each field's type at its
    kind. *)
Lemma nth_error_rev_fields_tele : forall fs κs k f T, List.nth_error fs k = Some (f, T) ->
    List.nth_error (List.rev (fields_tele fs κs)) k = Some (ce_ass (List.nth k κs ak_relevant) T).
Proof.
  induction fs as [| fT fs IH]; intros κs [| k] f T H; cbn [List.nth_error] in H; try discriminate;
    cbn [fields_tele]; rewrite List.rev_app_distr; cbn [List.rev List.app List.nth_error].
  - injection H as ->; destruct κs; reflexivity.
  - destruct κs as [| κ κs]; cbn [List.tl List.nth];
      [ rewrite (IH nil k f T H); destruct k; reflexivity | exact (IH κs k f T H) ].
Qed.

Lemma record_fields_env_snoc : forall R ns pre f T v,
    List.nth_error (record_fields R) (List.length pre) = Some (f, T) ->
    record_fields_env R ns (pre ++ v :: nil) = record_fields_env R ns pre ↦ v ⦂ entry_type_closure T (record_fields_env R ns pre).
Proof.
  intros * H; unfold record_fields_env; apply (env_tele_snoc_nth _ _ _ (record_field_kind R (List.length pre))).
  unfold record_fields_tele, record_field_kind; exact (nth_error_rev_fields_tele _ _ _ _ _ H).
Qed.

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
       exists a a', ⟦ T ⟧ record_fields_env R ns vs ↘ a /\ ⟦ T ⟧ record_fields_env R ns' vs' ↘ a' /\
         (forall c c', Dom c ≈ c' ∈ per_bot -> fr k vs (⇑ a c) (⇑ a' c')) /\
         (forall b b', fr k vs b b' -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top)) ->
    Dom d_record p ns ≈ d_record p ns' ∈ per_top_typ /\
    (forall c c', Dom c ≈ c' ∈ per_bot -> record_rel R fr (⇑ (d_record p ns) c) (⇑ (d_record p ns') c')) /\
    (forall b b', record_rel R fr b b' -> Dom ⇓ (d_record p ns) b ≈ ⇓ (d_record p ns') b' ∈ per_top).
Proof.
  intros * Hl Hnd Hn Hn' Hps Hev.
  set (fl := record_fields R) in *.
  repeat split.
  - intros s; destruct (Hps s) as [Ps Ps' H1 H2 HE].
    apply (mk_type_reads_alike _ _ _ (nf_record p Ps) (nf_record p Ps'));
      [ econstructor; eassumption | econstructor; eassumption | apply nf_record_upto_proofs; exact HE ].
  - (** The neutral projections, built field by field, related at each
        field's type, and the projections they are. *)
    intros c c' Hc.
    assert (Hall : forall m j pre pre', m + j = List.length fl -> tele_prefix_rel fr j pre pre' ->
               exists rs rs', eval_neutral_fields gc_deps gc_stack c (record_fields_env R ns pre) (List.skipn j fl) rs /\
                 eval_neutral_fields gc_deps gc_stack c' (record_fields_env R ns' pre') (List.skipn j fl) rs' /\
                 tele_prefix_rel fr (List.length fl) (pre ++ rs) (pre' ++ rs')).
    { induction m as [| m IH]; intros j pre pre' Hj Hp.
      - rewrite List.skipn_all2 by lia; exists nil, nil; rewrite !List.app_nil_r.
        split; [ constructor | split; [ constructor |] ]; replace (List.length fl) with j by lia; exact Hp.
      - destruct (nth_error_lt_some' fl j ltac:(lia)) as [[g T] Hg].
        destruct (Hev _ _ _ _ _ Hg Hp) as (a & a' & Ea & Ea' & Hbot & _).
        pose proof Hp as Hpl; rewrite tele_prefix_rel_iff in Hpl; destruct Hpl as (Hpl & Hpl' & _).
        assert (Hpc : Dom d_proj g c ≈ d_proj g c' ∈ per_bot)
          by (intros s; destruct (Hc s) as [M M' HM HM' HE];
              apply (mk_neutral_reads_alike _ _ _ (ne_proj g M) (ne_proj g M')); [ constructor; assumption .. |];
              unfold ne_eq_upto_proofs in *; cbn; rewrite dec_eqb_refl; exact HE).
        destruct (IH (S j) (pre ++ ⇑ a (d_proj g c) :: nil) (pre' ++ ⇑ a' (d_proj g c') :: nil)
                    ltac:(lia) (tele_prefix_rel_snoc _ _ _ _ _ _ Hp (Hbot _ _ Hpc))) as (rs & rs' & Er & Er' & Hrs).
        rewrite (record_fields_env_snoc _ _ _ g T) in Er by (rewrite Hpl; exact Hg).
        rewrite (record_fields_env_snoc _ _ _ g T) in Er' by (rewrite Hpl'; exact Hg).
        exists (⇑ a (d_proj g c) :: rs), (⇑ a' (d_proj g c') :: rs').
        rewrite (skipn_nth_cons' _ _ _ Hg).
        rewrite <- !List.app_assoc in Hrs; cbn [List.app] in Hrs.
        split; [ econstructor; eassumption | split; [ econstructor; eassumption | exact Hrs ] ]. }
    destruct (Hall (List.length fl) 0 nil nil ltac:(lia) (tele_prefix_rel_nil _)) as (rs & rs' & Er & Er' & Hrs).
    cbn [List.skipn List.app] in *.
    assert (Hproj : forall ms m0 rs0, eval_neutral_fields gc_deps gc_stack m0 (env_tele nil (List.rev (record_params R)) ms) fl rs0 ->
               record_projs R (⇑ (d_record p ms) m0) rs0).
    { intros ms m0 rs0 E.
      apply Forall2_of_nth; [ symmetry; exact (eval_neutral_fields_length _ _ _ _ E) |].
      intros k [g T] r Hk Hr; cbn [fst].
      econstructor; [ exact Hl | exact (field_index_nth_nodup _ _ _ _ Hnd Hk) | apply eval_neutral_fields_firstn; exact E |].
      rewrite List.nth_error_firstn; destruct (Nat.ltb_spec k (S k)); [ exact Hr | lia ]. }
    destruct Hrs as [Hlr Hfrom].
    econstructor; [ exact (Hproj _ _ _ Er) | exact (Hproj _ _ _ Er') | split; [ exact Hlr | exact Hfrom ] ].
  - (** The elements: the projections, read back field by field at each
        field's type in the parameters and the projections before it. *)
    intros b b' [vs vs' Hvl Hvr Hrel] s.
    destruct (Hps s) as [Ps Ps' H1 H2 HEP].
    pose proof Hrel as Hrel'; rewrite tele_rel_iff in Hrel'; destruct Hrel' as (Hlv & Hlv' & Hr).
    fold fl in Hrel, Hlv, Hlv'.
    assert (Hall : forall m j, m + j = List.length fl ->
               exists Fs Fs', Rflds b at List.skipn j fl in gc_deps ⍮ gc_stack ⍮ record_fields_env R ns (List.firstn j vs) ⍮ s ↘ Fs /\
                 Rflds b' at List.skipn j fl in gc_deps ⍮ gc_stack ⍮ record_fields_env R ns' (List.firstn j vs') ⍮ s ↘ Fs' /\
                 nfs_eq_upto_proofs Fs Fs').
    { induction m as [| m IH]; intros j Hj.
      - rewrite List.skipn_all2 by lia; exists nil, nil; split; [ constructor | split; [ constructor | reflexivity ] ].
      - destruct (nth_error_lt_some' fl j ltac:(lia)) as [[g T] Hg].
        destruct (nth_error_lt_some' vs j ltac:(lia)) as [v Hv].
        destruct (nth_error_lt_some' vs' j ltac:(lia)) as [v' Hv'].
        destruct (Hev _ _ _ _ _ Hg (tele_prefix_rel_of_full _ _ _ _ j Hrel ltac:(lia))) as (a & a' & Ea & Ea' & _ & Htop).
        destruct (Htop _ _ (Hr _ _ _ Hv Hv') s) as [F F' HF HF' HEF].
        destruct (IH (S j) ltac:(lia)) as (Fs & Fs' & HFs & HFs' & HEs).
        assert (Hj1 : List.length (List.firstn j vs) = j) by (rewrite List.length_firstn; lia).
        assert (Hj2 : List.length (List.firstn j vs') = j) by (rewrite List.length_firstn; lia).
        rewrite (firstn_S_snoc _ _ _ Hv), (record_fields_env_snoc _ _ _ g T) in HFs by (rewrite Hj1; exact Hg).
        rewrite (firstn_S_snoc _ _ _ Hv'), (record_fields_env_snoc _ _ _ g T) in HFs' by (rewrite Hj2; exact Hg).
        exists (cons F Fs), (cons F' Fs'); rewrite (skipn_nth_cons' _ _ _ Hg).
        split; [| split; [| apply nfs_eq_upto_proofs_cons; split; assumption ] ]; econstructor;
          [ exact (Forall2_nth_both _ _ _ _ _ _ Hvl Hg Hv) | exact Ea | exact HF | exact HFs
          | exact (Forall2_nth_both _ _ _ _ _ _ Hvr Hg Hv') | exact Ea' | exact HF' | exact HFs' ]. }
    destruct (Hall (List.length fl) 0 ltac:(lia)) as (Fs & Fs' & HFs & HFs' & HEs).
    cbn [List.skipn List.firstn] in HFs, HFs'.
    apply (mk_normal_reads_alike _ _ _ (nf_tuple p Ps (List.map fst fl) Fs) (nf_tuple p Ps' (List.map fst fl) Fs'));
      [ econstructor; [ eassumption | eassumption | eassumption | exact HFs ]
      | econstructor; [ eassumption | eassumption | eassumption | exact HFs' ]
      | apply nf_tuple_upto_proofs; assumption ].
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

(** Realisability: related types read back alike, neutrals of them are
    related (a neutral at a proposition is a neutral proof, which reads
    back as itself), and related elements read back alike. *)
Lemma realize_per_univ_elem_gen : forall {i a a' R},
    DF a ≈ a' ∈ per_univ_elem i ↘ R ->
    Dom a ≈ a' ∈ per_top_typ
    /\ (forall {c c'}, Dom c ≈ c' ∈ per_bot -> Dom ⇑ a c ≈ ⇑ a' c' ∈ R)
    /\ (forall {b b'}, Dom b ≈ b' ∈ R -> Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top).
Proof.
  intros * Hunivelem. simpl in Hunivelem.
  per_univ_elem_induction Hunivelem.
  - (** A large universe: its neutrals are neutral types, relevant; its
        elements read back as types. *)
    subst; repeat split.
    + apply per_top_typ_of_reads; intro s; eexists; split; econstructor.
    + intros c c' Hc; apply_relation_equivalence.
      constructor; [| reflexivity | reflexivity ].
      eexists; basic_per_univ_elem_econstructor; [ cbn; constructor | reflexivity | exact Hc | reflexivity ].
    + intros b b' Hb; apply_relation_equivalence; destruct Hb as [[R' HR'] _ _].
      match goal with IH : forall A B R, per_univ_elem _ R A B -> _ |- _ => destruct (IH _ _ _ HR') as (Htt & _ & _) end.
      intro s; destruct (Htt s) as [C C' HC HC' HE].
      apply (mk_normal_reads_alike _ _ _ C C'); [ constructor; exact HC | constructor; exact HC' | exact HE ].
  - (** A small universe.  It reads back as the universe at the canonical
        form its level reads back as, which the two related levels share; the
        other two components are as in the large tier, with the elements at
        the index of the realiser. *)
    repeat split.
    + intro s.
      match goal with H : per_lvl _ _ |- _ => destruct (per_lvl_reads _ _ H s) as (L & L' & HW & HW' & HE) end.
      apply (mk_type_reads_alike _ _ _ (nf_univ_of L) (nf_univ_of L'));
        [ apply read_typ_suniv; assumption | apply read_typ_suniv; assumption | apply nf_univ_of_upto_proofs; exact HE ].
    + intros c c' Hc; apply_relation_equivalence.
      constructor; [| reflexivity | reflexivity ].
      eexists; basic_per_univ_elem_econstructor; [ cbn; constructor | reflexivity | exact Hc | reflexivity ].
    + intros b b' Hb; apply_relation_equivalence; destruct Hb as [[R' HR'] _ _].
      match goal with IH : forall A B R, per_univ_elem _ R A B -> _ |- _ => destruct (IH _ _ _ HR') as (Htt & _ & _) end.
      intro s; destruct (Htt s) as [C C' HC HC' HE].
      apply (mk_normal_reads_alike _ _ _ C C'); [ constructor; exact HC | constructor; exact HC' | exact HE ].
  - (** A type of levels: its elements read back at every sort. *)
    repeat split.
    + apply per_top_typ_of_reads; intro s; eexists; split; econstructor.
    + intros c c' Hc; apply_relation_equivalence.
      apply per_bot_then_per_lvl_at; exact Hc.
    + intros b b' Hb; apply_relation_equivalence; intro s.
      destruct (Hb s) as [L L' HL HL' HE _].
      apply (mk_normal_reads_alike _ _ _ (nf_lvl_of L) (nf_lvl_of L'));
        [ eapply read_nf_level_sort; eassumption | eapply read_nf_level_sort; eassumption | apply nf_lvl_of_upto_proofs; exact HE ].
  - (** [Prop]: its neutrals are neutral propositions; its elements read
        back as types. *)
    repeat split.
    + apply per_top_typ_of_reads; intro s; eexists; split; econstructor.
    + intros c c' Hc; apply_relation_equivalence.
      constructor; [ reflexivity | reflexivity |].
      intro s; destruct (Hc s) as [C C' HC HC' HE].
      apply (mk_type_reads_alike _ _ _ (⇑ⁿ{ak_propositional} C) (⇑ⁿ{ak_propositional} C'));
        [ constructor; assumption | constructor; assumption
        | unfold nf_eq_upto_proofs; cbn [nf_eqb_upto_proofs]; rewrite dec_eqb_refl; exact HE ].
    + intros b b' Hb; apply_relation_equivalence; destruct Hb as [_ _ Ht].
      intro s; destruct (Ht s) as [C C' HC HC' HE].
      apply (mk_normal_reads_alike _ _ _ C C'); [ apply read_nf_prop; assumption | apply read_nf_prop; assumption | exact HE ].
  - (** [LevelSort]: its neutrals are neutral types of levels; its
        elements read back as types, as types of the least small index. *)
    repeat split.
    + apply per_top_typ_of_reads; intro s; eexists; split; econstructor.
    + intros c c' Hc; apply_relation_equivalence.
      assert (Hcode : per_level_code per_ne (⇑ LevelSortᵈ c) (⇑ LevelSortᵈ c')) by (econstructor; [ exact Hc | reflexivity ]).
      split; [ do 2 eexists; left; exact Hcode
             | split; [ do 2 eexists; right; exact Hcode | eexists; exact (per_level_code_univ_elem _ _ _ Hcode _) ] ].
    + intros b b' Hb; apply_relation_equivalence; destruct Hb as [_ [_ [R' HR']]].
      match goal with IH : forall A B R, per_univ_elem _ R A B -> _ |- _ => destruct (IH _ _ _ HR') as (Htt & _ & _) end.
      intro s; destruct (Htt s) as [C C' HC HC' HE].
      apply (mk_normal_reads_alike _ _ _ C C');
        [ apply read_nf_at_level_sort; exact HC | apply read_nf_at_level_sort; exact HC' | exact HE ].
  - (** A proposition: its elements are the proofs that read back, each as
        a proof term, which erasure ignores; its neutrals are neutral
        proofs. *)
    match goal with Hp : per_prop _ _ |- _ => destruct Hp as [Hl Hr Ht] end.
    repeat split.
    + exact Ht.
    + intros c c' Hc; apply_relation_equivalence; split; intro s; destruct (Hc s) as [M M' HM HM' _];
        eexists; constructor; eassumption.
    + intros b b' Hb; apply_relation_equivalence; destruct Hb as [Hb Hb']; intro s.
      destruct (Hb s) as [M HM], (Hb' s) as [M' HM'].
      apply (mk_normal_reads_alike _ _ _ (nf_proof M) (nf_proof M'));
        [ apply read_nf_proof; assumption | apply read_nf_proof; assumption | reflexivity ].
  - (** A [Π]: read back under a fresh variable of the domain, a neutral
        proof at a proposition; its neutrals applied are neutrals of the
        relevant codomain. *)
    destruct IHHunivelem as (Hatt & Habot & Hatop).
    repeat split.
    + intro s.
      assert (Hv : Dom ⇑! a s ≈ ⇑! a' s ∈ in_rel) by (apply Habot; apply var_per_bot).
      match goal with HT : forall c c' (e : in_rel c c'), rel_mod_eval _ B _ B' _ _ |- _ =>
        destruct (HT _ _ Hv) as [b b' Eb Eb' [HRb (Hbtt & _ & _)]] end.
      destruct (Hatt s) as [A0 A0' HA0 HA0' HEA].
      destruct (Hbtt (S s)) as [B0 B0' HB0 HB0' HEB].
      apply (mk_type_reads_alike _ _ _ (nf_pi κd κc A0 B0) (nf_pi κd κc A0' B0'));
        [ econstructor; eassumption | econstructor; eassumption | apply nf_pi_upto_proofs; assumption ].
    + intros c c' Hc; apply_relation_equivalence.
      constructor; [ reflexivity | reflexivity |].
      intros c0 c0' Hc0.
      match goal with HT : forall c c' (e : in_rel c c'), rel_mod_eval _ B _ B' _ _ |- _ =>
        destruct (HT _ _ Hc0) as [b b' Eb Eb' [HRb (_ & Hbbot & _)]] end.
      assert (Hap : Dom c $ᵈ ⇓ a c0 ≈ c' $ᵈ ⇓ a' c0' ∈ per_bot) by (apply domain_app_per; [ exact Hc | exact (Hatop _ _ Hc0) ]).
      econstructor; [ eapply eval_app_neut; [ eassumption | exact Eb ] | eapply eval_app_neut; [ eassumption | exact Eb' ]
                    | exact (Hbbot _ _ Hap) ].
    + intros f f' Hf; apply_relation_equivalence; destruct Hf as [_ _ Happ].
      intro s.
      assert (Hv : Dom ⇑! a s ≈ ⇑! a' s ∈ in_rel) by (apply Habot; apply var_per_bot).
      destruct (Happ _ _ Hv) as [fa f'a' Hfa Hf'a' Hrel].
      match goal with HT : forall c c' (e : in_rel c c'), rel_mod_eval _ B _ B' _ _ |- _ =>
        destruct (HT _ _ Hv) as [b b' Eb Eb' [HRb (_ & _ & Hbtop)]] end.
      destruct (Hbtop _ _ Hrel (S s)) as [M0 M0' HM0 HM0' HEM].
      destruct (Hatt s) as [A0 A0' HA0 HA0' HEA].
      apply (mk_normal_reads_alike _ _ _ (λⁿ A0 M0) (λⁿ A0' M0'));
        [ econstructor; eassumption | econstructor; eassumption | apply nf_fn_upto_proofs; assumption ].
  - (** A neutral type of an evaluated kind: its elements are neutrals. *)
    repeat split.
    + intro s; match goal with Hb : per_bot b b' |- _ => destruct (Hb s) as [M M' HM HM' HE] end.
      (** The two neutral types are at sorts of one kind. *)
      apply (mk_type_reads_alike _ _ _ (⇑ⁿ{domain_kind (⇑ a b)} M) (⇑ⁿ{domain_kind (⇑ a' b')} M'));
        [ constructor; assumption | constructor; assumption
        | unfold nf_eq_upto_proofs; cbn [nf_eqb_upto_proofs];
          match goal with Hk : domain_kind _ = domain_kind _ |- _ => rewrite Hk, dec_eqb_refl end; exact HE ].
    + intros c c' Hc; apply_relation_equivalence; constructor; exact Hc.
    + intros m m' Hm; apply_relation_equivalence; destruct Hm as [? ? ? ? Hm]; intro s.
      destruct (Hm s) as [M M' HM HM' HE].
      apply (mk_normal_reads_alike _ _ _ (⇑ⁿ{domain_kind (⇑ a b)} M) (⇑ⁿ{domain_kind (⇑ a' b')} M'));
        [ apply read_nf_neut; [ eauto with mctt | assumption ] | apply read_nf_neut; [ eauto with mctt | assumption ]
        | unfold nf_eq_upto_proofs; cbn [nf_eqb_upto_proofs];
          match goal with Hk : domain_kind _ = domain_kind _ |- _ => rewrite Hk, dec_eqb_refl end; exact HE ].
  (** A member of a group of inductive types: [realize_indty], from the
      realisability of the types of its telescopes; its neutrals by
      [ind_rel_neut_canon], the fresh-variable admissibility of the type's
      own uniform parameters following from the type-level one. *)
  - repeat split; [| intros c c' Hc | intros b b' Hb ];
      apply_relation_equivalence.
    + unshelve epose proof (realize_indty p D ups ups' nr ar dr H H0 H3 H5 H6 H8 H9 H11 H12 H14
                              _ _ _ H15 H16 k M ns ns' H1 H17) as [Hrt _];
      [ intros m Mm k0 κ A vs vs' Hm Hk Hp; destruct (H7 _ _ _ _ _ _ _ Hm Hk Hp) as [a a' Ea Ea' (_ & _ & _ & Hrb)]; eauto
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
      [ intros m Mm k0 κ A vs vs' Hm Hk Hp; destruct (H7 _ _ _ _ _ _ _ Hm Hk Hp) as [a a' Ea Ea' (_ & _ & _ & Hrb)]; eauto
      | intros m Mm ms ms' c0 gs k0 A vs vs' Hm0 Hm Hc Hk Hp;
        destruct (H10 _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Hk Hp) as [a a' Ea Ea' (_ & _ & _ & Hrb)]; eauto
      | intros m Mm ms ms' c0 gs gs1 t gs2 ws ws' k0 B ys ys' Hm0 Hm Hc Heq Hw HB Hy;
        destruct (H13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm0 Hm Hc Heq Hw HB Hy) as [a a' Ea Ea' (_ & Htt & Hbot & _)];
        exists a, a'; repeat split; eauto
      | unfold grp_rel in *; eapply Hre; eassumption ].
  (** A record type: [realize_record], from the realisability of the types
      of its fields. *)
  - repeat split; [| intros c c' Hc | intros b b' Hb ];
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

(** Related elements of a type read back at it, as term entries stored at
    the types' values. *)
Lemma entry_readable_of_elem : forall {i a a' R v v'},
    DF a ≈ a' ∈ per_univ_elem i ↘ R -> Dom v ≈ v' ∈ R ->
    entry_readable (de_term v (entry_type_value a)) /\ entry_readable (de_term v' (entry_type_value a')).
Proof.
  intros * HR Hv; split; intros s;
    destruct (per_univ_then_per_top_typ HR s) as [A A' HA HA' _];
    destruct (per_elem_then_per_top HR Hv s) as [W W' HW HW' _];
    eexists; econstructor; solve [ constructor | eassumption ].
Qed.

(** And as term entries stored at the types as closures, in the
    environments they evaluate in: the arguments of a telescope. *)
Lemma entry_readable_of_elem_closure : forall {i A A' ρ ρ' a a' R v v'},
    ⟦ A ⟧ ρ ↘ a -> ⟦ A' ⟧ ρ' ↘ a' ->
    DF a ≈ a' ∈ per_univ_elem i ↘ R -> Dom v ≈ v' ∈ R ->
    entry_readable (de_term v (entry_type_closure A ρ)) /\ entry_readable (de_term v' (entry_type_closure A' ρ')).
Proof.
  intros * Ea Ea' HR Hv; split; intros s;
    destruct (per_univ_then_per_top_typ HR s) as [T T' HT HT' _];
    destruct (per_elem_then_per_top HR Hv s) as [W W' HW HW' _];
    eexists; eapply read_entry_term; solve [ eapply eval_entry_type_closure; eassumption | eassumption ].
Qed.

(** ** Readability of Environments

    A kept proof reads back once every entry of its environment its scope
    reaches does: the lets bind entries only ([read_lets]).  Past its end
    an environment has no entry ([absent_entry]), which never reads back,
    so the scope must stay within the environment. *)

(** The entries of an environment past its end are [absent_entry]. *)
Lemma env_entry_past_end : forall ρ x, List.length ρ <= x -> env_entry ρ x = absent_entry.
Proof. intros * H; rewrite env_entry_nth; apply List.nth_overflow; exact H. Qed.

(** The entry past the end of an environment does not read back: it has
    no type. *)
Lemma absent_entry_unreadable : forall s b, ~ Rent absent_entry in gc_deps ⍮ gc_stack ⍮ s ↘ b.
Proof. intros * H; inversion H; subst; match goal with He : eval_entry_type _ _ entry_type_none _ |- _ => inversion He end. Qed.

(** An entry that reads back is inside its environment. *)
Lemma entry_readable_inside : forall ρ x, entry_readable (env_entry ρ x) -> x < List.length ρ.
Proof.
  intros * H; destruct (Nat.lt_ge_cases x (List.length ρ)) as [Hx | Hx]; [ exact Hx | exfalso ].
  rewrite env_entry_past_end in H by exact Hx; destruct (H 0) as [b Hb]; exact (absent_entry_unreadable _ _ Hb).
Qed.

(** The lets of an environment whose entries read back, at any number of
    positions within its length. *)
Lemma read_lets_of_env_readable : forall ρ, env_readable ρ ->
    forall k s, k <= List.length ρ -> exists bs, Rlets ρ at k in gc_deps ⍮ gc_stack ⍮ s ↘ bs.
Proof.
  intros ρ H k; induction k as [| k IH]; intros s Hk; [ eexists; constructor |].
  destruct (H k ltac:(lia) s) as [b Hb]; destruct (IH (S s) ltac:(lia)) as [bs Hbs]; eexists; econstructor; eassumption.
Qed.

(** A proof kept over an environment whose entries read back reads back,
    when its scope stays within the environment. *)
Lemma kept_proof_readable : forall M ρ, env_readable ρ -> proof_scope M ρ <= List.length ρ -> proof_readable ⋆ᵈ⟨M, ρ⟩.
Proof.
  intros * H Hk s; destruct (read_lets_of_env_readable _ H (proof_scope M ρ) s Hk) as [bs Hbs].
  eexists; constructor; exact Hbs.
Qed.

(** An initial environment has an entry for each entry of its context. *)
Lemma initial_env_length : forall Γ ρ, initial_env_f Γ ρ -> List.length ρ = List.length Γ.
Proof. induction 1; cbn; congruence. Qed.

(** Related initial environments read back at every entry. *)
Lemma initial_env_readable : forall Γ Γ' R ρ ρ', EF Γ ≈ Γ' ∈ per_ctx_env ↘ R ->
    initial_env_f Γ ρ -> initial_env_f Γ' ρ' -> Dom ρ ≈ ρ' ∈ R -> env_readable ρ /\ env_readable ρ'.
Proof.
  intros * HΓ Hi Hi' Hρ.
  pose proof (per_ctx_env_length HΓ) as Hl.
  pose proof (initial_env_length _ _ Hi) as Hl1; pose proof (initial_env_length _ _ Hi') as Hl2.
  split; intros x Hx'; [ rewrite Hl1 in Hx' | rewrite Hl2 in Hx'; rewrite <- Hl in Hx' ];
    first [ exact (proj1 (per_ctx_env_entries_readable _ _ _ HΓ _ _ Hρ x Hx'))
          | exact (proj2 (per_ctx_env_entries_readable _ _ _ HΓ _ _ Hρ x Hx')) ].
Qed.

(** A module entry reads back, by its stored unit. *)
Lemma mod_entry_readable : forall h U, entry_readable (de_mod h U).
Proof. intros * s; eexists; constructor. Qed.

(** The initial environments of two related contexts are related.  The
    contexts are scoped: the initial environment of a module slot stores
    the slot's unit, which the context PER asks to be scoped by the slot's
    tail ([head_readable]). *)
Lemma per_ctx_then_per_env_initial_env : forall {Γ Γ' env_rel},
    EF Γ ≈ Γ' ∈ per_ctx_env ↘ env_rel ->
    ctx_scoped 0 Γ -> ctx_scoped 0 Γ' ->
    exists ρ ρ', initial_env_f Γ ρ /\ initial_env_f Γ' ρ' /\ Dom ρ ≈ ρ' ∈ env_rel.
Proof.
  induction 1; intros HsΓ HsΓ'.
  2-5: cbn [ctx_scoped] in HsΓ, HsΓ'; destruct HsΓ as [HeΓ HsΓ]; destruct HsΓ' as [HeΓ' HsΓ'];
         specialize (IHper_ctx_env HsΓ HsΓ').
  - do 2 eexists; intuition.
  - destruct_conjs.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    do 2 eexists; repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    (** A fresh variable of the type on each side, at the same level: a
        term entry that reads back. *)
    match goal with
    | Ht : tail_rel ?ρ ?ρ', HR : per_univ_elem _ (head_rel _ _ ?Ht) _ _ |- _ =>
        pose proof (per_ctx_env_length equiv_Γ_Γ') as Hlen; rewrite <- Hlen;
        pose proof (per_bot_then_per_elem HR (var_per_bot (n := List.length Γ))) as Hv;
        unshelve eapply mk_per_ctx_env_cons_rel;
          [ exact Ht | exact Hv | intros _; eexists; reflexivity | intros _; eexists; reflexivity
          | exact (conj (proj1 (entry_readable_of_elem HR Hv)) (le_n 0))
          | exact (conj (proj2 (entry_readable_of_elem HR Hv)) (le_n 0)) ]
    end.
  - (** A definition slot holds the value of the body at a relevant type,
        the proof at a proposition. *)
    destruct IHper_ctx_env as [ρ [ρ' [Hi [Hi' Hρ]]]].
    assert (Dom ρ ≈ ρ ∈ tail_rel) by solve_per.
    assert (Dom ρ' ≈ ρ' ∈ tail_rel) by solve_per.
    match goal with HS : forall ρ ρ' (_ : Dom ρ ≈ ρ' ∈ tail_rel), rel_typ_kind _ _ _ |- _ => rename HS into HS0 end.
    match goal with HT : forall ρ ρ' (_ : Dom ρ ≈ ρ' ∈ tail_rel), rel_typ _ _ _ _ _ _ |- _ =>
      destruct (HT _ _ Hρ) as [a a' Ha Ha' HR] end.
    destruct (HS0 _ _ Hρ) as (a0 & Ha0 & Hr0).
    assert (a0 = a) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (per_univ_elem_kind _ _ _ _ HR) as Hr0'.
    (** At an evaluated kind, relevant or of levels, the heads hold the
        bodies' values. *)
    destruct r; cbn [def_heads_at def_bodies_at] in *; [ | | rename Hr0 into Hr0l ].
    1,3: match goal with
         | Hbody : forall ρ ρ' (_ : Dom ρ ≈ ρ' ∈ ?TR), rel_elem _ _ _ _ _ |- _ =>
             destruct (Hbody _ _ Hρ) as [m m' Hm Hm' Hmm]
         end;
      do 2 eexists; repeat split;
        only 1-2: (eapply initial_env_cons_def;
                   [ eassumption | eassumption | rewrite ?Hr0, ?Hr0l, <- ?Hr0'; first [ rewrite ?Hr0, ?Hr0l; constructor | constructor ]
                   | eassumption ]);
      apply_relation_equivalence;
      unshelve eapply mk_per_ctx_env_def_rel';
        [ exact Hρ | solve_def_heads | intros _; eexists; reflexivity | intros _; eexists; reflexivity
        | exact (conj (proj1 (entry_readable_of_elem HR Hmm)) (le_n 0))
        | exact (conj (proj2 (entry_readable_of_elem HR Hmm)) (le_n 0)) ].
    + (** The kept bodies read back over the initial environments: they
          are scoped by the contexts. *)
      assert (Hp' : domain_kind a' = ak_propositional) by congruence.
      assert (HMb : exp_free_bound M <= List.length Γ)
        by (destruct HeΓ as [_ HMs]; rewrite Nat.add_0_r in HMs; exact (exp_scoped_free_bound _ _ HMs)).
      assert (HM'b : exp_free_bound M' <= List.length Γ)
        by (destruct HeΓ' as [_ HMs]; rewrite Nat.add_0_r, <- (per_ctx_env_length equiv_Γ_Γ') in HMs;
            exact (exp_scoped_free_bound _ _ HMs)).
      destruct (per_ctx_env_kept_proof_readable _ _ _ M equiv_Γ_Γ' HMb _ _ Hρ) as [Hρr _].
      destruct (per_ctx_env_kept_proof_readable _ _ _ M' equiv_Γ_Γ' HM'b _ _ Hρ) as [_ Hρr'].
      assert (Hkept : forall b M0 ρ0, proof_readable ⋆ᵈ⟨M0, ρ0⟩ -> domain_kind b = ak_propositional ->
                (forall s, exists B, Rtyp b in gc_deps ⍮ gc_stack ⍮ s ↘ B) ->
                entry_readable (de_term ⋆ᵈ⟨M0, ρ0⟩ (entry_type_value b))).
      { intros * Hr Hb Hty s; destruct (Hty s) as [B HB]; destruct (Hr s) as [P HP].
        eexists; econstructor; [ constructor | exact HB | apply read_nf_proof; [ exact Hb | exact HP ] ]. }
      do 2 eexists; repeat split;
        only 1-2: (eapply initial_env_cons_def_proof; [ eassumption | eassumption | congruence ]).
      apply_relation_equivalence.
      unshelve eapply mk_per_ctx_env_def_rel';
        [ exact Hρ | split; [ apply (per_univ_elem_propositional _ _ _ _ HR ltac:(congruence));
                              split; assumption | exact I ]
        | intros _; eexists; reflexivity | intros _; eexists; reflexivity
        | split; [| cbn; lia ];
          apply Hkept; [ exact Hρr | congruence | intros s; destruct (per_univ_then_per_top_typ HR s) as [? ? ? ? _]; eexists; eassumption ]
        | split; [| cbn; lia ];
          apply Hkept; [ exact Hρr' | exact Hp' | intros s; destruct (per_univ_then_per_top_typ HR s) as [? ? ? ? _]; eexists; eassumption ] ].
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
    exists (ρ ↦ᵐ h ⦂ U), (ρ' ↦ᵐ h' ⦂ U'); repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    (** The stored units are the slots' own, scoped by their tails. *)
    pose proof (per_ctx_env_length equiv_Γ_Γ') as Hlen.
    pose proof (gunit_scoped_free_bound _ _ HeΓ) as HbU; pose proof (gunit_scoped_free_bound _ _ HeΓ') as HbU'.
    rewrite Nat.add_0_r in HbU, HbU'.
    constructor; cbn [drop_env List.tl]; [ exact Hρ | .. ]; unfold env_mod; cbn [env_entry List.hd];
      try solve [ solve_tie ]; try solve [ solve_entry_kind ];
      try (split; [ apply mod_entry_readable | cbn; lia ]).
    (** The ties across: each side's head against the other unit over its
        own tail, by the premise at the diagonal tails. *)
    all: cbn [List.tl List.hd].
    all: try solve [ solve_entry_kind ].
    + match goal with HU : forall ρ ρ', tail_rel ρ ρ' -> rel_modexp_evals _ _ _ _, Hd : tail_rel ρ ρ |- _ =>
        destruct (HU _ _ Hd) as [k k' Ek Ek' Rk] end.
      pose proof (functional_eval_modexp _ _ _ _ Hh Ek) as <-.
      exists k'; split; assumption.
    + match goal with HU : forall ρ ρ', tail_rel ρ ρ' -> rel_modexp_evals _ _ _ _, Hd : tail_rel ρ' ρ' |- _ =>
        destruct (HU _ _ Hd) as [k k' Ek Ek' Rk] end.
      pose proof (functional_eval_modexp _ _ _ _ Hh' Ek') as <-.
      exists k; split; [ assumption | apply per_dmod_sym; assumption ].
  - (** A definition with a module part holds the value of its term and the
        closure of its unit. *)
    destruct IHper_ctx_env as [ρ [ρ' [? [? Hρ]]]].
    assert (Dom ρ ≈ ρ ∈ tail_rel) by solve_per.
    assert (Dom ρ' ≈ ρ' ∈ tail_rel) by solve_per.
    (** A definition with a module part is of a relevant type. *)
    subst r; cbn [def_heads_at] in *.
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
    match goal with HT : forall ρ ρ' (_ : Dom ρ ≈ ρ' ∈ tail_rel), rel_typ _ _ _ _ _ _ |- _ =>
      destruct (HT _ _ Hρ) as [a a' Ha Ha' HR] end.
    exists (ρ ↦ᵈ m ⦂ entry_type_value a ‖ h ⦂ U), (ρ' ↦ᵈ m' ⦂ entry_type_value a' ‖ h' ⦂ U');
      repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    (** The term parts read back at their types, as elements of them. *)
    destruct (entry_readable_of_elem HR Hmm) as [Hrl Hrr].
    solve_def_heads_pre.
    apply (mk_per_ctx_env_dm_rel _ _ _ _ _ _ _ (ρ ↦ᵈ m ⦂ entry_type_value a ‖ h ⦂ U) (ρ' ↦ᵈ m' ⦂ entry_type_value a' ‖ h' ⦂ U') Hρ);
      unfold env_mod; cbn [env_entry List.hd extend_env_dm]; cbn;
      try solve [ solve_tie ]; try solve_def_heads_post.
    all: try match goal with |- head_readable _ _ => split end.
    all: try (cbn; lia).
    all: try solve [ solve_entry_kind ].
    all: intros s; first [ solve [ destruct (Hrl s) as [b Hb]; inversion Hb; subst; eexists; eapply read_entry_dm; eassumption ]
                         | solve [ destruct (Hrr s) as [b Hb]; inversion Hb; subst; eexists; eapply read_entry_dm; eassumption ] ].
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
