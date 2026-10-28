(** * The Stuck Eliminator at a View, Read as the Container's

    A view's stuck eliminator reads back as its container's ([read_ne_elim]
    at [im_sel], E1′).  The container's stuck eliminator at the wrapped
    blocks and the group's at the view's member read back alike: block by
    block over the members of the group read, the blocks they read are
    the group's own by the agreement of the views' maps
    ([view_maps_coherent]), under fresh variables of the container's
    telescopes on one side and of the group's on the other.  Those fresh
    variables are related at the group's relations: a container's type at
    its uniform parameters [ub] is related to the container's at the
    view's instance [cups] at the group's uniform parameters, which is
    related to the group's by the view's equations
    ([ViewEquations.tele_link_types]).  The recursive results at the
    positions a view nests through are the eliminators' at members of
    lower rank. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing Views.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas MemberWf.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness Require Import VariableCases FunctionCases LevelCases SubtypingCases.
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations ViewArgs Con Elim Iota ViewBranch ElimView.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence ViewCount IndElim ReadPairs.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Fresh Variables of a View's Container and of the Group

    The view [m] of the container's member [k'] at the instance [Is], its
    map [vm]; the group's uniform parameters [u0], the instance's value
    [cups] there, and uniform parameters [ub] of the container related to
    [cups].  The container's member [i'] and the group's member [v] the
    view takes it to. *)
(** The relations of types linked by a related pair agree. *)
Lemma rel_link : forall (i j k : universe_index) R T S a b c d, DF a ≈ b ∈ per_univ_elem i ↘ R -> DF b ≈ c ∈ per_univ_elem j ↘ T ->
    DF c ≈ d ∈ per_univ_elem k ↘ S -> (R <~> S).
Proof.
  intros * H1 H2 H3.
  etransitivity; [ exact (per_univ_elem_chain_iff _ _ _ _ _ _ _ H1 H2) | exact (per_univ_elem_chain_iff _ _ _ _ _ _ _ H2 H3) ].
Qed.

(** A fresh variable of a type is related to one of a related type. *)
Lemma fresh_var_rel : forall (i : universe_index) R a b s, DF a ≈ b ∈ per_univ_elem i ↘ R -> R (⇑! a s) (⇑! b s).
Proof. intros * H; exact (per_bot_then_per_elem H var_per_bot). Qed.

Lemma fresh_tele_cons_inv : forall A T ρ s vs, Ftele ce_ass A :: T in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ vs ->
    exists a vs', vs = ⇑! a s :: vs' /\ ⟦ A ⟧ ρ ↘ a /\ Ftele T in gc_deps ⍮ gc_stack ⍮ ρ ↦ ⇑! a s ⍮ S s ↘ vs'.
Proof. intros * H; inversion H; subst; eauto. Qed.

(** The type of a view [j] of a group at uniform parameters [ups]: the
    container's member's at the view's instance [cups], against it at
    uniform parameters [cs] related to [cups], at non-uniform parameters
    related at the view: related types (the view's relation is the
    container's, [nr_from]).  The premise [Hend] of [shty_link]. *)
Lemma view_end_type : forall VP, valid_groups VP -> forall pq G, VP pq G ->
    forall ups, per_gargs (List.rev (ind_uparams G)) nil nil ups ups -> List.length ups = ind_nu G ->
    forall j Mj qc kc Is vm Dq cups cs bs bs', ind_member G j = Some Mj -> im_head Mj = mh_view qc kc Is vm ->
      ind_lookup gc_deps gc_stack qc = Some Dq -> ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups ->
      per_gargs (List.rev (ind_uparams Dq)) nil nil cups cs ->
      ntele_rel G (canon_nparams_rel G ups) j bs bs' ->
      exists (i : universe_index) R, DF d_ind qc kc (cups ++ bs) ≈ d_ind qc kc (cs ++ bs') ∈ per_univ_elem i ↘ R.
Proof.
  intros VP HP pq G HPG ups Hgu Hu j Mj qc kc Is vm Dq cups cs bs bs' HMj Hh Hq Ecups Hcs Hbs.
  pose proof (valid_groups_valid VP HP pq G HPG) as Hg.
  pose proof (containers_valid_of_groups VP HP pq G HPG) as Hcv.
  pose proof (Hcv _ _ _ _ _ _ _ HMj Hh Hq) as HgQ.
  destruct (decl_typed_view _ _ _ (valid_group_typed _ _ Hg) _ _ _ _ _ _ HMj Hh) as (D2 & Mk' & Hl2 & HMk' & Hkd & HIl & _ & Hvm & _ & _).
  rewrite Hq in Hl2; injection Hl2 as <-.
  assert (Hhd : exists pm, im_head Mk' = mh_decl pm).
  { pose proof (proj2 (decl_typed_order _ _ _ (valid_group_typed _ _ HgQ) _ _ HMk') Hkd) as Hd.
    unfold im_is_decl in Hd; destruct (im_head Mk'); [ eauto | discriminate | discriminate ]. }
  destruct Hhd as [pm Hhd].
  destruct (vg_view_args_values pq G Hg Hcv _ _ _ _ _ _ _ HMj Hh Hq _ _ Hgu Hu) as (c0 & c0' & E0 & E0' & Hcu).
  pose proof (functional_eval_exps' _ _ _ _ E0 Ecups) as ->.
  pose proof (functional_eval_exps' _ _ _ _ E0' Ecups) as ->.
  assert (Hlc : List.length cups = ind_nu Dq) by (rewrite (eval_exps_length _ _ _ Ecups); exact HIl).
  pose proof (view_agreement_canonical_all VP pq G HP HPG ups ups Hgu Hu j _ _ _ _ _ _ _ _ HMj Hh Hq Ecups Ecups) as Hvc.
  destruct (agree_members _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvc _ _ HMk') as (v & Mv & Hvmb).
  assert (v = j) as -> by (pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvmb) as Hv; rewrite Hvm in Hv; congruence).
  assert (Mv = Mj) as -> by (pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMv; rewrite HMj in HMv; congruence).
  unfold ntele_rel in Hbs; rewrite HMj in Hbs.
  pose proof (nr_from pq G ups ups _ _ _ qc Dq cups cups _ _ _ vm Hvc kc Mk' j Mj bs bs' HMk' Hvmb Hbs) as Hbs'.
  destruct (vg_relate qc Dq HgQ kc Mk' pm cups cs bs bs' HMk' Hhd Hcs Hlc Hbs') as [i W].
  exists i; eexists; exact W.
Qed.

Lemma fresh_cargs_arg_inv : forall pq U A gs ρ s vs, Fcargs ca_arg A :: gs of pq U in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ vs ->
    exists a vs', vs = ⇑! a s :: vs' /\ ⟦ A ⟧ ρ ↘ a /\ Fcargs gs of pq U in gc_deps ⍮ gc_stack ⍮ ρ ↦ ⇑! a s ⍮ S s ↘ vs'.
Proof. intros * H; inversion H; subst; eauto. Qed.

Lemma fresh_cargs_rec_inv : forall pq U t gs ρ s vs, Fcargs ca_rec t :: gs of pq U in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ vs ->
    exists a vs', vs = ⇑! a s :: vs' /\ ⟦shty t of pq U ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ a /\
      Fcargs gs of pq U in gc_deps ⍮ gc_stack ⍮ ρ ⍮ S s ↘ vs'.
Proof. intros * H; inversion H; subst; eauto. Qed.

(** ** The Domains of Two Shapes, Read Alike

    The domains of the container's shape [t'] after its own prefix [preQ]
    at its uniform parameters [ub], and of the group's [t] in [ρB], after
    the group's prefix [pre] of the member [k]: each defined, at arguments
    related at the group's relation of the domain read back alike, related
    to themselves at the container's, and so on for the rests after
    them. *)

(** At the domains' values [bA] (the container's, of [B'] after [preQ])
    and [bB], at related arguments [c] and [c']: what [cross_doms] has of
    them, [R] of the rests [t'] and [t] after them. *)
#[warnings="-cannot-define-projection"]
Record cross_doms_step (R : list domain -> list domain -> env -> ptyp -> ptyp -> Prop) (ub : list domain)
    (pre preQ : list domain) (ρB : env) (B' : exp) (bA bB : domain) (t' t : ptyp) (c c' : domain) : Prop :=
  mk_cross_doms_step
  { (** The arguments read back alike at the domains *)
    cross_doms_top : Dom ⇓ bA c ≈ ⇓ bB c' ∈ per_top
    (** The container's related to itself at its own domain *)
  ; cross_doms_canon : canon_doms_rel ub 0 preQ B' c c
    (** The rests after them *)
  ; cross_doms_rest : R (pre ++ c :: nil) (preQ ++ c :: nil) (ρB ↦ c') t' t }.
Scheme All for cross_doms_step.

(** [cross_doms ub dr k pre preQ ρB t' t]: the domains of the container's
    shape [t'] and the group's [t], domain by domain, as the section
    describes ([cross_doms_step] at each). *)
Inductive cross_doms (ub : list domain) (dr : nat -> list domain -> exp -> relation domain) (k : nat) :
    list domain -> list domain -> env -> ptyp -> ptyp -> Prop :=
(** At the ends, nothing *)
| cross_doms_self : forall pre preQ ρB j' Ps' j Ps, cross_doms ub dr k pre preQ ρB (pt_self j' Ps') (pt_self j Ps)
(** At a domain on each side: related arguments read back alike, are
    related to themselves at the container's domain, and the rests after
    them *)
| cross_doms_pi : forall pre preQ ρB B' t' B t bA bB,
    ⟦ B' ⟧ env_args nil (ub ++ preQ) ↘ bA -> ⟦ B ⟧ ρB ↘ bB ->
    (forall c c', dr k pre B c c' -> cross_doms_step (cross_doms ub dr k) ub pre preQ ρB B' bA bB t' t c c') ->
    cross_doms ub dr k pre preQ ρB (pt_pi B' t') (pt_pi B t).

Lemma shty_pi_inv : forall pq U ρ B t a, ⟦shty pt_pi B t of pq U ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ a ->
    exists b, ⟦ B ⟧ ρ ↘ b /\ a = Πᵈ b (nil ↦ d_shfam pq U ρ t) fam_cod.
Proof. intros * H; inversion H; subst; eauto. Qed.

(** The types of a container's recursive argument and of the group's,
    related: their domains read alike.  The group's at its uniform
    parameters [u0], after the prefix [ms'], [ws'], [ys']; the
    container's at [ub] after [preQ]. *)
Lemma cross_doms_fresh : forall p D, valid_group p D -> forall u0, per_gargs (List.rev (ind_uparams D)) nil nil u0 u0 ->
    List.length u0 = ind_nu D ->
    forall v Mv c gs gs1 t gs2 ms ms' ws ws', ind_member D v = Some Mv -> ind_con Mv c = Some gs -> gs = gs1 ++ ca_rec t :: gs2 ->
      tele_rel (canon_nparams_rel D u0 v) (List.rev (im_nparams Mv)) ms ms' ->
      tele_prefix_rel (canon_args_rel D u0 v ms c) (List.length (cargs_nonrec gs1)) ws ws' ->
      forall qc ub n kk t' preQ ys ys' a1 a2 (i : universe_index) R, kk + n = List.length (ptyp_doms t) -> ptyp_depth t' = n ->
        tele_prefix_rel (shape_doms_rel (canon_doms_rel u0 v) ms ws (ptyp_doms t)) kk ys ys' ->
        ⟦shty t' of qc ub ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ub ++ preQ) ↘ a1 ->
        ⟦shty ptyp_skip kk t of p u0 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ ms' ++ ws' ++ ys') ↘ a2 ->
        DF a1 ≈ a2 ∈ per_univ_elem i ↘ R ->
        cross_doms ub (canon_doms_rel u0) v (ms ++ ws ++ ys) preQ (env_args nil (u0 ++ ms' ++ ws' ++ ys')) t' (ptyp_skip kk t).
Proof.
  intros p D Hg u0 Hgu Hu v Mv c gs gs1 t gs2 ms ms' ws ws' HM Hc Heq Hm Hw qc ub.
  destruct (vg_doms_related p D Hg u0 u0 Hgu Hu Hgu) as [ud Hdr].
  induction n as [| n IH]; intros kk t' preQ ys ys' a1 a2 i R Hkn Hdp Hy E1 E2 HR.
  - rewrite Nat.add_0_r in Hkn; subst kk; rewrite ptyp_skip_end.
    destruct t' as [j' Ps' | B' t1']; cbn in Hdp; [ constructor | lia ].
  - destruct (ptyp_skip_lt kk t ltac:(lia)) as (B & HB & Hs); rewrite Hs in E2 |- *.
    destruct t' as [j' Ps' | B' t1']; cbn in Hdp; [ lia |].
    destruct (shty_pi_inv _ _ _ _ _ _ E1) as (b1 & Eb1' & ->); destruct (shty_pi_inv _ _ _ _ _ _ E2) as (b2 & Eb2' & ->).
    basic_invert_per_univ_elem HR.
    rename equiv_a_a' into Hab.
    destruct (Hdr v Mv ms ms' c gs gs1 t gs2 ws ws' kk B ys ys' HM Hm Hc Heq Hw HB Hy) as (d & d' & Ed & Ed' & [Rd Hdd]).
    assert (d' = b2) as -> by (eapply functional_eval_exp; eassumption).
    pose proof (per_univ_trans _ _ _ _ _ _ Hdd (per_univ_sym _ _ _ _ Hdd)) as Hd0.
    destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ Hdd (per_univ_sym _ _ _ _ Hab)) as (Rx & Hx & _).
    assert (Hin : forall c0 c0', canon_doms_rel u0 v (ms ++ ws ++ ys) B c0 c0' -> in_rel c0 c0').
    { intros c0 c0' Hcc; apply (rel_link _ _ _ _ _ _ _ _ _ _ Hd0 Hx Hab); exact (Hcc _ _ _ _ Ed Ed Hd0). }
    apply (cross_doms_pi _ _ _ _ _ _ _ _ _ _ b1 b2 Eb1' Eb2'); intros c0 c0' Hcc; constructor; revert c0 c0' Hcc.
    + intros c0 c0' Hcc; exact (per_elem_then_per_top Hab (Hin _ _ Hcc)).
    + intros c0 c0' Hcc i0 R0 a a' Ea Ea' HR0.
      pose proof (functional_eval_exp _ _ _ _ Ea Eb1') as ->; pose proof (functional_eval_exp _ _ _ _ Ea' Eb1') as ->.
      apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ HR0 Hab).
      pose proof (Hin _ _ Hcc) as Hc1.
      assert (HP : PER in_rel) by (eapply per_elem_PER; exact Hab).
      etransitivity; [ exact Hc1 | symmetry; exact Hc1 ].
    + intros c0 c0' Hcc.
      pose proof (Hin _ _ Hcc) as Hcc'.
      match goal with
      | Hcod : forall c c' (equiv_c_c' : in_rel c c'), rel_mod_eval _ _ _ _ _ _ |- _ =>
          destruct (Hcod _ _ Hcc') as [x0 x0' Ex0 Ex0' HRx]
      end.
      apply fam_cod_shfam_inv in Ex0; apply fam_cod_shfam_inv in Ex0'; rewrite <- env_args_snoc3 in Ex0'.
      rewrite <- env_args_snoc in Ex0; rewrite <- List.app_assoc in Ex0.
      rewrite <- env_args_snoc3.
      replace ((ms ++ ws ++ ys) ++ c0 :: nil) with (ms ++ ws ++ (ys ++ c0 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
      apply (IH (S kk) t1' (preQ ++ c0 :: nil) (ys ++ c0 :: nil) (ys' ++ c0' :: nil) x0 x0' i (out_rel c0 c0' Hcc') ltac:(lia)
               ltac:(unfold ptyp_depth in *; cbn in *; lia)); [| exact Ex0 | exact Ex0' | exact HRx ].
      apply tele_prefix_rel_snoc; [ exact Hy | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc ].
Qed.

(** The arguments [vsA] of a container's constructor (kinds [gsA]) and
    [vsB] of the group's at the view (kinds [gsB]), after the container's
    side's prefix [pre] in the group's relation, its own [preQ] in the
    container's (at the uniform parameters [ub]), and the group's side's
    [pre']: at each argument recursive in both, neutrals on each side, the
    container's related to itself at its own relation, and the domains of
    their shapes read alike. *)
Inductive cross_tops (qc : qname) (D' : ind_decl) (ub u0 : list domain) (dr : nat -> list domain -> exp -> relation domain)
    (kQ k : nat) : list domain -> list domain -> list domain -> list carg -> list carg -> list domain -> list domain -> Prop :=
(** No argument *)
| cross_tops_nil : forall pre preQ pre', cross_tops qc D' ub u0 dr kQ k pre preQ pre' nil nil nil nil
(** Non-recursive in both: the arguments join the prefixes *)
| cross_tops_arg : forall pre preQ pre' A' A gsA gsB vA vB vsA vsB,
    cross_tops qc D' ub u0 dr kQ k (pre ++ vA :: nil) (preQ ++ vA :: nil) (pre' ++ vB :: nil) gsA gsB vsA vsB ->
    cross_tops qc D' ub u0 dr kQ k pre preQ pre' (ca_arg A' :: gsA) (ca_arg A :: gsB) (vA :: vsA) (vB :: vsB)
(** Nested through: the container's argument joins its own prefix *)
| cross_tops_nest : forall pre preQ pre' A' t gsA gsB vA vB vsA vsB,
    cross_tops qc D' ub u0 dr kQ k pre (preQ ++ vA :: nil) pre' gsA gsB vsA vsB ->
    cross_tops qc D' ub u0 dr kQ k pre preQ pre' (ca_arg A' :: gsA) (ca_rec t :: gsB) (vA :: vsA) (vB :: vsB)
(** Recursive in both: neutrals, the container's at its own relation, the
    domains read alike *)
| cross_tops_rec : forall pre preQ pre' t' t gsA gsB vA vB vsA vsB,
    is_neut vA -> is_neut vB ->
    rec_arg_rel qc D' (okr_at D' ub (canon_nparams_rel D' ub)) (canon_nparams_rel D' ub) (canon_args_rel D' ub)
      (canon_doms_rel ub) kQ ub ub preQ preQ t' vA vA ->
    cross_doms ub dr k pre preQ (env_args nil (u0 ++ pre')) t' t ->
    cross_tops qc D' ub u0 dr kQ k pre preQ pre' gsA gsB vsA vsB ->
    cross_tops qc D' ub u0 dr kQ k pre preQ pre' (ca_rec t' :: gsA) (ca_rec t :: gsB) (vA :: vsA) (vB :: vsB).

Lemma cross_tops_arg_inv : forall qc D' ub u0 dr kQ k pre preQ pre' A' A gsA gsB vA vB vsA vsB,
    cross_tops qc D' ub u0 dr kQ k pre preQ pre' (ca_arg A' :: gsA) (ca_arg A :: gsB) (vA :: vsA) (vB :: vsB) ->
    cross_tops qc D' ub u0 dr kQ k (pre ++ vA :: nil) (preQ ++ vA :: nil) (pre' ++ vB :: nil) gsA gsB vsA vsB.
Proof. intros * H; inversion H; subst; assumption. Qed.

Lemma cross_tops_nest_inv : forall qc D' ub u0 dr kQ k pre preQ pre' A' t gsA gsB vA vB vsA vsB,
    cross_tops qc D' ub u0 dr kQ k pre preQ pre' (ca_arg A' :: gsA) (ca_rec t :: gsB) (vA :: vsA) (vB :: vsB) ->
    cross_tops qc D' ub u0 dr kQ k pre (preQ ++ vA :: nil) pre' gsA gsB vsA vsB.
Proof. intros * H; inversion H; subst; assumption. Qed.



Lemma con_args_arg_inv : forall p D okr nr ar dr k u u' pre pre' A gs v v' vs vs',
    con_args_rel p D okr nr ar dr k u u' pre pre' (ca_arg A :: gs) (v :: vs) (v' :: vs') ->
    con_args_rel p D okr nr ar dr k u u' (pre ++ v :: nil) (pre' ++ v' :: nil) gs vs vs'.
Proof. intros * H; inversion H; subst; assumption. Qed.

Lemma con_args_rec_inv : forall p D okr nr ar dr k u u' pre pre' t gs v v' vs vs',
    con_args_rel p D okr nr ar dr k u u' pre pre' (ca_rec t :: gs) (v :: vs) (v' :: vs') ->
    rec_arg_rel p D okr nr ar dr k u u' pre pre' t v v' /\ con_args_rel p D okr nr ar dr k u u' pre pre' gs vs vs'.
Proof. intros * H; inversion H; subst; split; assumption. Qed.

Lemma cargs_plen_tail : forall D g gs, cargs_plen D (g :: gs) -> cargs_plen D gs.
Proof. intros D g gs H gs1 t gs2 E; apply (H (g :: gs1) t gs2); rewrite E; reflexivity. Qed.

(** A member's type at uniform parameters [X]: at the reference the
    member has, after as many values as its own uniform parameters. *)
Lemma mref_ref_len : forall pq G j Mj X hd k pre, ind_lookup gc_deps gc_stack pq = Some G -> ind_member G j = Some Mj ->
    List.length X = ind_nu G -> ⟦mref j of pq X ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pre) ->
    im_ref pq j Mj = (hd, k) /\ List.length pre = im_unu G Mj.
Proof.
  intros * Hl HM HX E; unfold im_ref, im_unu.
  destruct (im_head Mj) as [pm | qv kv Iv vmv | qr Ir fl] eqn:Hh.
  - pose proof (mref_decl_inv _ _ _ _ _ _ _ Hl HM Hh E) as Heq; injection Heq as -> -> ->; split; [ reflexivity | exact HX ].
  - destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hl HM Hh E) as (py & Heq & Ep); injection Heq as -> -> ->.
    split; [ reflexivity | exact (eval_exps_length _ _ _ Ep) ].
  - exfalso; inversion E; subst; congruence.
Qed.

(** The fresh variables of a member's non-uniform parameters at uniform
    parameters related to themselves: related to themselves. *)
Lemma fresh_nparams_exist : forall pq G, valid_group pq G -> forall ups, per_gargs (List.rev (ind_uparams G)) nil nil ups ups ->
    List.length ups = ind_nu G -> forall j Mj s, ind_member G j = Some Mj ->
    exists ns, Ftele List.rev (im_nparams Mj) in gc_deps ⍮ gc_stack ⍮ env_args nil ups ⍮ s ↘ ns /\
      tele_rel (canon_nparams_rel G ups j) (List.rev (im_nparams Mj)) ns ns.
Proof.
  intros pq G Hg ups Hgu Hu j Mj s HM.
  destruct (vg_canon pq G Hg ups Hgu Hu) as [CnP CnI CaP CaI CdP CdI].
  pose proof (adm_fresh_of_uparams pq G ups _ _ _ (valid_group_ass _ _ Hg) CnP CnI CaP CaI CdP CdI ups (vg_adm pq G Hg ups ups Hgu Hu Hgu))
    as Ha.
  destruct (fresh_tele_rel_ftele _ _ _ _ _ _ _ _ (adm_fresh_nparams _ _ _ _ _ _ _ Ha _ Mj s HM)) as (nsu & ns & Fu & Fa & Lu & Hua).
  rewrite List.app_nil_r in Fu, Fa.
  pose proof (functional_fresh_tele' _ _ _ _ _ Fu Fa) as <-.
  exists nsu; split; [ exact Fu | split; assumption ].
Qed.

(** A member's type at uniform parameters related to themselves is
    defined, at a member not a record view. *)
Lemma mref_exists : forall VP, valid_groups VP -> forall pq G, VP pq G ->
    forall X, per_gargs (List.rev (ind_uparams G)) nil nil X X -> List.length X = ind_nu G ->
    forall j Mj, ind_member G j = Some Mj -> im_is_rview Mj = false -> exists r, ⟦mref j of pq X ⟧ gc_deps ⍮ gc_stack ↘ r.
Proof.
  intros VP HP pq G HPG X Hgx Hx j Mj HM Hrv.
  pose proof (valid_groups_valid VP HP pq G HPG) as Hg.
  pose proof (containers_valid_of_groups VP HP pq G HPG) as Hcv.
  unfold im_is_rview in Hrv; destruct (im_head Mj) as [pm | qc kc Is vm | qr Ir fl] eqn:Hh; [| | discriminate Hrv ].
  - eexists; eapply eval_mref_decl; [ exact (valid_group_lookup _ _ Hg) | exact HM | exact Hh ].
  - destruct (grp_tele_ass_views _ (valid_group_ass _ _ Hg) _ _ _ _ _ _ HM Hh) as (Dq & Mc & Hq & _).
    destruct (vg_view_args_values pq G Hg Hcv _ _ _ _ _ _ _ HM Hh Hq X X Hgx Hx) as (cs & _ & Ecs & _).
    eexists; eapply eval_mref_view; [ exact (valid_group_lookup _ _ Hg) | exact HM | exact Hh | exact Ecs ].
Qed.

(** ** Values of Instances of a Closed Telescope *)

(** Terms [Vs] of a closed telescope [C] over [Γ0], as an instance that
    commutes with substitutions: their values moved by [σ] at [ρ], against
    their values at the value of [σ]. *)
Lemma closed_vals_sub_link : forall C Γ0 Vs RC, tele_ass C -> ⊨ C -> ⊨ Γ0 -> EF C ≈ C ∈ per_ctx_env ↘ RC ->
    List.length Vs = List.length C ->
    (forall j V, List.nth_error Vs j = Some V -> exists T, Γ0 ⊨ V : T) ->
    sub_link Γ0 (C ++ Γ0) (sb_of_list Id Vs) ->
    forall Γ' RΓ' σ ρ E u, EF Γ' ≈ Γ' ∈ per_ctx_env ↘ RΓ' -> Γ' ⊨ˢ σ ≈ σ : Γ0 -> RΓ' ρ ρ -> ⟦ σ ⟧s ρ ↘ E ->
      ⟦ Vs ⟧* gc_deps ⍮ gc_stack ⍮ E ↘ u ->
      exists w, ⟦ List.map (fun V => V[σ]) Vs ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ w /\ RC (env_args nil w) (env_args nil u).
Proof.
  intros * HCa HC HΓ0 HRC HVl HVt Hlk * HRΓ' Hσ Hρ Hev Hu.
  assert (Hev' : forall j N, List.nth_error (List.map (fun V => V[σ]) Vs) j = Some N -> exists v, ⟦ N ⟧ ρ ↘ v).
  { intros j N HN; apply nth_error_map_inv in HN as (V & HV & ->).
    destruct (HVt _ _ HV) as [T [R0 HR0 i0 Hgen]].
    destruct (Hgen _ _ HRΓ' _ _ Hσ _ _ _ _ Hρ Hev Hev) as (Re & _ & [v1 _ _ _ Ev1 _ _ _ _]); eauto. }
  destruct (eval_exps_each _ _ Hev') as [w Hw].
  exists w; split; [ exact Hw |].
  destruct (closed_app_sem _ _ HCa HC HΓ0) as [HCΓ Hres].
  destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ].
  destruct (Hlk _ _ HRΓ' _ _ Hσ _ HRCΓ _ _ Hρ Hev) as (e1 & Ee1 & He1).
  pose proof (He1 _ (eval_sb_of_list _ _ _ _ _ (eval_sub_id E) Hu)) as H12.
  assert (Ee1' : ⟦ sb_of_list Id Vs ⨟ σ ⟧s ρ ↘ env_args E w).
  { eapply eval_sub_sb_eq; [| exact (eval_sb_of_list _ _ _ _ _ Hev Hw) ].
    etransitivity; [ apply sb_of_list_cong; intros x; reflexivity | symmetry; apply sb_of_list_compose_gen ]. }
  pose proof (functional_eval_sub _ _ _ _ Ee1 Ee1') as E1.
  pose proof (per_ctx_env_resp_env_eq HRCΓ _ _ _ _ E1 ltac:(reflexivity) H12) as H12'.
  apply (Hres _ _ HRC HRCΓ) in H12'.
  pose proof (eval_exps_length _ _ _ Hw) as L1; pose proof (eval_exps_length _ _ _ Hu) as L2.
  rewrite List.length_map in L1.
  eapply closed_env_base; [ exact HCa | exact HC | exact HRC | rewrite L1; exact HVl | rewrite L2; exact HVl | exact H12' ].
Qed.

(** Two instances of a closed telescope [C] over [Γ0] equal as
    substitutions: their values at related environments related at [C]. *)
Lemma sb_of_list_vals_rel : forall C Γ0 Ms Ms' RC RΓ0, tele_ass C -> ⊨ C -> ⊨ Γ0 ->
    EF C ≈ C ∈ per_ctx_env ↘ RC -> EF Γ0 ≈ Γ0 ∈ per_ctx_env ↘ RΓ0 ->
    Γ0 ⊨ˢ sb_of_list Id Ms ≈ sb_of_list Id Ms' : C ++ Γ0 -> List.length Ms = List.length C -> List.length Ms' = List.length C ->
    forall ρ ρ', RΓ0 ρ ρ' -> exists ms ms', ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms /\ ⟦ Ms' ⟧* gc_deps ⍮ gc_stack ⍮ ρ' ↘ ms' /\
      RC (env_args nil ms) (env_args nil ms').
Proof.
  intros * HCa HC HΓ0 HRC HRΓ0 Hsub Hl Hl' ρ ρ' Hρ.
  destruct (rel_sub_under_ctx_simple Hsub) as (RΓ1 & HRΓ1 & RΔ & HRΔ & Hs).
  assert (E : RΓ0 <~> RΓ1) by (eapply per_ctx_env_right_irrel; eassumption).
  destruct (Hs _ _ (proj1 (E _ _) Hρ)) as (y1 & y2 & Ey1 & Ey2 & Hy).
  destruct (eval_sb_of_list_inv _ _ _ _ _ Ey1 (eval_sub_id ρ)) as (ms & Ems & Eq1).
  destruct (eval_sb_of_list_inv _ _ _ _ _ Ey2 (eval_sub_id ρ')) as (ms' & Ems' & Eq2).
  pose proof (per_ctx_env_resp_env_eq HRΔ _ _ _ _ Eq1 Eq2 Hy) as Hy'.
  destruct (closed_app_sem _ _ HCa HC HΓ0) as [_ Hres].
  pose proof (Hres _ _ HRC HRΔ _ _ Hy') as H.
  exists ms, ms'; split; [ exact Ems | split; [ exact Ems' |] ].
  pose proof (eval_exps_length _ _ _ Ems) as L1; pose proof (eval_exps_length _ _ _ Ems') as L2.
  eapply closed_env_base; [ exact HCa | exact HC | exact HRC | rewrite L1; exact Hl | rewrite L2; exact Hl' | exact H ].
Qed.

(** A view [v] of a group of a view [k]'s container's view [i'], of the
    container [D''] of [i']: its instance at the group's uniform parameters
    [ups] related to [i']'s instance at uniform parameters [ub] of [k]'s
    container related to [k]'s instance [cups] at [ups] (the view
    equations of [v], [vg_view_view_is]). *)
Lemma view_view_values : forall VP, valid_groups VP -> forall pq G, VP pq G ->
    forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm',
      ind_member G k = Some Mk -> im_head Mk = mh_view qc k' Is vm -> ind_lookup gc_deps gc_stack qc = Some D' ->
      ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' -> ind_lookup gc_deps gc_stack q'' = Some D'' ->
      List.nth_error vm i' = Some v -> ind_member G v = Some Mv -> im_head Mv = mh_view q'' k'' X vm' ->
      forall ups cups ub, per_gargs (List.rev (ind_uparams G)) nil nil ups ups -> List.length ups = ind_nu G ->
        ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ cups -> per_gargs (List.rev (ind_uparams D')) nil nil ub cups ->
        exists prea preb, ⟦ Is'' ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ub ↘ prea /\
          ⟦ X ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil ups ↘ preb /\
          per_gargs (List.rev (ind_uparams D'')) nil nil prea preb.
Proof.
  intros VP HP pq G HPG k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm' HMk Hh Hq HMi' Hh' Hq'' Hv HMv HhMv
    ups cups ub Hgu Hu Ecups Hub.
  pose proof (valid_groups_valid VP HP pq G HPG) as Hg.
  pose proof (containers_valid_of_groups VP HP pq G HPG) as Hcv.
  pose proof (valid_groups_containers VP HP pq G k Mk qc k' Is vm D' HPG HMk Hh Hq) as HVQ.
  pose proof (valid_groups_valid VP HP qc D' HVQ) as HgQ.
  pose proof (containers_valid_of_groups VP HP qc D' HVQ) as HcvQ.
  pose proof (valid_groups_containers VP HP qc D' i' Mi' q'' k'' Is'' vm'' D'' HVQ HMi' Hh' Hq'') as HVQ2.
  pose proof (valid_groups_valid VP HP q'' D'' HVQ2) as HgQ2.
  pose proof (valid_group_closed _ _ HgQ2) as Hc2.
  pose proof (decl_closed_ass _ Hc2) as HaC; pose proof (valid_ind_decl_uparams _ (valid_group_valid _ _ HgQ2)) as HWC.
  pose proof (decl_closed_ass _ (valid_group_closed _ _ HgQ)) as HaQ; pose proof (valid_ind_decl_uparams _ (valid_group_valid _ _ HgQ)) as HWQ.
  pose proof (valid_ind_decl_uparams _ (valid_group_valid _ _ Hg)) as HWG.
  destruct (rel_ctx_wf_per_ctx_env HWC) as [RC HRC].
  assert (HPC : PER RC) by (eapply per_env_PER; exact HRC).
  destruct (rel_ctx_wf_per_ctx_env HWQ) as [RQ HRQ].
  destruct (rel_ctx_wf_per_ctx_env HWG) as [RG HRG].
  (** The lengths of the instances. *)
  destruct (grp_tele_ass_views _ (valid_group_ass _ _ HgQ) _ _ _ _ _ _ HMi' Hh') as (D3 & Mc3 & Hq3 & _ & _ & HlI2).
  rewrite Hq'' in Hq3; injection Hq3 as <-.
  destruct (grp_tele_ass_views _ (valid_group_ass _ _ Hg) _ _ _ _ _ _ HMv HhMv) as (D4 & Mc4 & Hq4 & _ & _ & HlX).
  rewrite Hq'' in Hq4; injection Hq4 as <-.
  destruct (grp_tele_ass_views _ (valid_group_ass _ _ Hg) _ _ _ _ _ _ HMk Hh) as (D5 & Mc5 & Hq5 & _ & _ & HlIs).
  rewrite Hq in Hq5; injection Hq5 as <-.
  assert (Hlc : List.length cups = ind_nu D') by (rewrite (eval_exps_length _ _ _ Ecups); exact HlIs).
  assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
  unfold ind_nu in HlI2, HlX, Hlc, Hlb.
  set (σ := sb_of_list Id Is).
  set (E0 := env_args nil ups).
  assert (HE0 : RG E0 E0) by exact (uparams_rel_env G (valid_group_valid _ _ Hg) ups ups Hgu Hu RG HRG).
  assert (Eσ : ⟦ σ ⟧s E0 ↘ env_args E0 cups) by exact (eval_sb_of_list _ _ _ _ _ (eval_sub_id E0) Ecups).
  pose proof (gsub_valid (vg_view_args_gsub pq G Hg Hcv _ _ _ _ _ _ _ HMk Hh Hq)) as Hσ.
  assert (HI2 : forall j I T, List.nth_error Is'' j = Some I -> List.nth_error (tele_insts (ind_uparams D'') Id Is'') j = Some T ->
             ind_uparams D' ⊨ I : T)
    by (intros j I T HI HT; exact (vg_view_is qc D' HgQ HcvQ _ _ _ _ _ _ _ _ _ _ HMi' Hh' Hq'' HI HT)).
  assert (HTex : forall j I, List.nth_error Is'' j = Some I ->
             exists T, List.nth_error (tele_insts (ind_uparams D'') Id Is'') j = Some T).
  { intros j I HI; apply nth_error_lt_some'.
    rewrite length_tele_insts by exact HaC.
    assert (j < List.length Is'') by (apply List.nth_error_Some; congruence); lia. }
  (** [i']'s instance at [ub] and at [cups]. *)
  destruct (vg_view_args_values qc D' HgQ HcvQ _ _ _ _ _ _ _ HMi' Hh' Hq'' ub cups Hub ltac:(unfold ind_nu; exact Hlb))
    as (pa & ns & Epa & Ens & Hg4).
  assert (H4 : RC (env_args nil pa) (env_args nil ns))
    by (apply (gargs_env_rel _ _ _ _ _ _ HRC HWC); [ rewrite (eval_exps_length _ _ _ Epa); exact HlI2 | exact Hg4 ]).
  (** At [cups], against at the value of [k]'s instance. *)
  destruct (closed_inst_cross _ _ Is'' Is'' HaC HWC HWQ HlI2 HlI2) as [Hsub3 _].
  { intros k0 N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-; exact (HI2 _ _ _ HN HT). }
  pose proof (uparams_refl_r D' (valid_group_valid _ _ HgQ) (valid_group_closed _ _ HgQ) _ _ Hub ltac:(unfold ind_nu; exact Hlb)) as Hcc.
  assert (HQ3 : RQ (env_args E0 cups) (env_args nil cups)).
  { pose proof (gargs_env_rel _ _ _ _ _ _ HRQ HWQ Hlc Hcc) as H0.
    eapply closed_env_base; [ exact HaQ | exact HWQ | exact HRQ | exact Hlc | exact Hlc | exact H0 ]. }
  destruct (sb_of_list_vals_rel _ _ _ _ RC RQ HaC HWC HWQ HRC HRQ Hsub3 HlI2 HlI2 _ _ HQ3) as (n' & ns' & En' & Ens' & H3).
  pose proof (functional_eval_exps' _ _ _ _ Ens' Ens) as ->.
  (** At the value of [k]'s instance, against [i']'s instance moved by it. *)
  destruct (closed_app_sem _ _ HaQ HWQ HWG) as [HWQG _].
  destruct (closed_inst_cross _ (ind_uparams D' ++ ind_uparams G) Is'' Is'' HaC HWC HWQG HlI2 HlI2) as [_ Hlk1].
  { intros k0 N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-.
    exact (closed_app_valid _ _ _ _ _ HaQ HWQ HWG (HI2 _ _ _ HN HT)). }
  assert (HTy : forall j I, List.nth_error Is'' j = Some I -> exists T, ind_uparams D' ++ ind_uparams G ⊨ I : T).
  { intros j I HI; destruct (HTex _ _ HI) as [T HT]; exists T.
    exact (closed_app_valid _ _ _ _ _ HaQ HWQ HWG (HI2 _ _ _ HI HT)). }
  destruct (closed_vals_sub_link _ _ Is'' RC HaC HWC HWQG HRC HlI2 HTy Hlk1 _ _ σ E0 (env_args E0 cups) n' HRG Hσ HE0 Eσ En')
    as (w & Ew & H1).
  (** [i']'s instance moved by [k]'s, against [v]'s: the view equations. *)
  assert (Hpt : forall k0 N N' T, List.nth_error (List.map (fun I => I[σ]) Is'') k0 = Some N -> List.nth_error X k0 = Some N' ->
             List.nth_error (tele_insts (ind_uparams D'') Id (List.map (fun I => I[σ]) Is'')) k0 = Some T ->
             ind_uparams G ⊨ N ≈ N' : T).
  { intros k0 N N' T HN HN' HT.
    apply nth_error_map_inv in HN as (I & HI & ->).
    destruct (HTex _ _ HI) as [T0 HT0].
    pose proof (tele_insts_closed_sub _ _ σ _ _ HaC (decl_closed_uparams _ Hc2) HT0) as HT0'.
    rewrite HT in HT0'; injection HT0' as ->.
    apply rel_exp_under_ctx_sym.
    exact (vg_view_view_is pq G Hg Hcv k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm' k0 N' (I[σ]) T0
             HMk Hh Hq HMi' Hh' Hq'' Hc2 Hv HMv HhMv HN' ltac:(rewrite List.nth_error_map, HI; reflexivity) HT0). }
  destruct (closed_inst_cross _ _ _ _ HaC HWC HWG ltac:(rewrite List.length_map; exact HlI2) HlX Hpt) as [Hsub2 _].
  destruct (sb_of_list_vals_rel _ _ _ _ RC RG HaC HWC HWG HRC HRG Hsub2 ltac:(rewrite List.length_map; exact HlI2) HlX _ _ HE0)
    as (w' & xs & Ew' & Exs & H2).
  pose proof (functional_eval_exps' _ _ _ _ Ew' Ew) as ->.
  assert (Hall : RC (env_args nil pa) (env_args nil xs))
    by (etransitivity; [ exact H4 | etransitivity; [ symmetry; exact H3 | etransitivity; [ symmetry; exact H1 | exact H2 ] ] ]).
  assert (HWC' : ⊨ List.rev (List.rev (ind_uparams D'')) ++ ⋅) by (rewrite List.rev_involutive, List.app_nil_r; exact HWC).
  assert (HRC' : EF List.rev (List.rev (ind_uparams D'')) ++ ⋅ ≈ List.rev (List.rev (ind_uparams D'')) ++ ⋅ ∈ per_ctx_env ↘ RC)
    by (rewrite List.rev_involutive, List.app_nil_r; exact HRC).
  destruct (rel_gargs _ _ _ _ per_ctx_env_nil_true HWC' (List.Forall_rev HaC) HRC' nil nil pa xs
              ltac:(rewrite List.length_rev, (eval_exps_length _ _ _ Epa); exact HlI2)
              ltac:(rewrite List.length_rev, (eval_exps_length _ _ _ Exs); exact HlX) Hall) as [_ Hgall].
  exists pa, xs; split; [ exact Epa | split; [ exact Exs | exact Hgall ] ].
Qed.

Section CrossFresh.
  #[local] Set Default Proof Using "All".
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hg := valid_groups_valid VP HP p D HPD.
  Let Hcv := containers_valid_of_groups VP HP p D HPD.
  Variables (m : nat) (Mm : imember) (qc : qname) (k' : nat) (Is : list exp) (vm : list nat) (D' : ind_decl).
  Hypotheses (HMm : ind_member D m = Some Mm) (Hh : im_head Mm = mh_view qc k' Is vm)
    (Hq : ind_lookup gc_deps gc_stack qc = Some D').
  Let HVQ := valid_groups_containers VP HP p D m Mm qc k' Is vm D' HPD HMm Hh Hq.
  Let HgQ := valid_groups_valid VP HP qc D' HVQ.
  Let HcvQ := containers_valid_of_groups VP HP qc D' HVQ.
  Variables (u0 cups ub : list domain).
  Hypotheses (Hgu : per_gargs (List.rev (ind_uparams D)) nil nil u0 u0) (Hu : List.length u0 = ind_nu D)
    (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil u0 ↘ cups)
    (Hub : per_gargs (List.rev (ind_uparams D')) nil nil ub cups).
  Let nr := canon_nparams_rel D u0.
  Variables (i' : nat) (Mi' : imember) (v : nat) (Mv : imember).
  Hypotheses (HMi' : ind_member D' i' = Some Mi') (Hv : List.nth_error vm i' = Some v) (HMv : ind_member D v = Some Mv).

  (** The fresh non-uniform parameters of the container's member at [ub]
      and of the group's at [u0] are related at the group's relation. *)
  Record cross_params (nsA nsB : list domain) : Prop := mk_cross_params
    { (** Related at the group's member *)
      cross_params_rel : tele_rel (nr v) (List.rev (im_nparams Mv)) nsA nsB
      (** Related across at the container's member's telescope *)
    ; cross_params_container : per_gargs (List.rev (im_params D' Mi')) nil nil (ub ++ nsA) (cups ++ nsB)
      (** The group's side related to itself at the container's *)
    ; cross_params_container_right : per_gargs (List.rev (im_params D' Mi')) nil nil (cups ++ nsB) (cups ++ nsB)
      (** The group's side related to itself at the group's *)
    ; cross_params_group_right : per_gargs (List.rev (im_params D Mv)) nil nil (u0 ++ nsB) (u0 ++ nsB) }.

  Lemma cross_fresh_nparams : forall s nsA nsB,
      Ftele List.rev (im_nparams Mi') in gc_deps ⍮ gc_stack ⍮ env_args nil ub ⍮ s ↘ nsA ->
      Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ env_args nil u0 ⍮ s ↘ nsB ->
      cross_params nsA nsB.
  Proof.
    pose proof (view_nn p D Hg m Mm qc k' Is vm D' HMm Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
    pose proof (valid_group_valid _ _ Hg) as HD; pose proof (valid_group_closed _ _ Hg) as Hc.
    pose proof (valid_group_valid _ _ HgQ) as HDQ; pose proof (valid_group_closed _ _ HgQ) as HcQ.
    pose proof (view_cups_rel p D Hg Hcv m Mm qc k' Is vm D' HMm Hh Hq u0 cups Hgu Hu Ecups) as Hcc.
    pose proof (length_cups p D Hg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups) as Hlc.
    assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
    set (tc := List.rev (im_nparams Mi')); set (tg := List.rev (im_nparams Mv)).
    (** The container's base: [ub] and [cups] over no base, and [cups]
        over [u0] as the instance gives it. *)
    pose proof (valid_ind_decl_uparams _ HDQ) as HUQ.
    destruct (rel_ctx_wf_per_ctx_env HUQ) as [RQ HRQ].
    assert (HPQ : PER RQ) by (eapply per_env_PER; exact HRQ).
    assert (HQb : RQ (env_args nil ub) (env_args nil cups))
      by (apply (gargs_env_rel _ _ _ _ _ _ HRQ HUQ); [ unfold ind_nu in Hlb; exact Hlb | exact Hub ]).
    assert (HQ0 : RQ (env_args nil cups) (env_args nil cups))
      by (apply (gargs_env_rel _ _ _ _ _ _ HRQ HUQ); [ exact Hlc | exact Hcc ]).
    set (Ec := env_args (env_args nil u0) cups); set (Eg := env_args nil u0).
    assert (HQc : RQ (env_args nil cups) Ec) by exact (closed_env_base _ _ _ _ _ _ _ _ (decl_closed_ass _ HcQ) HUQ HRQ Hlc Hlc HQ0).
    assert (HQbE : RQ (env_args nil ub) Ec) by (etransitivity; [ exact HQb | exact HQc ]).
    assert (HQEE : RQ Ec Ec) by (etransitivity; [ symmetry; exact HQc | exact HQc ]).
    (** The two telescopes, equal under the view's instance. *)
    assert (Hac : tele_ass tc) by exact (List.Forall_rev (member_nparams_ass D' HcQ _ _ HMi')).
    assert (Hag : tele_ass tg) by exact (List.Forall_rev (member_nparams_ass D Hc _ _ HMv)).
    assert (HWc0 : ⊨ List.rev tc ++ ind_uparams D') by (unfold tc; rewrite List.rev_involutive; exact (valid_ind_decl_params _ HDQ _ _ HMi')).
    assert (HTc0 : forall j0 A, List.nth_error tc j0 = Some (ce_ass A) ->
                     exists i : nat, List.rev (List.firstn j0 tc) ++ ind_uparams D' ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (valid_ind_decl_npar _ HDQ _ _ _ _ HMi' HA))).
    pose proof (valid_ind_decl_uparams _ HD) as HUD.
    destruct (rel_ctx_wf_per_ctx_env HUD) as [RU HRU].
    pose proof (uparams_rel_env D HD _ _ Hgu Hu _ HRU) as HρU.
    assert (HaC0 : tele_ass (List.rev tc ++ ind_uparams D'))
      by (apply List.Forall_app; split; [ apply List.Forall_rev; exact Hac | exact (decl_closed_ass _ HcQ) ]).
    assert (HWc : ⊨ List.rev tc ++ ind_uparams D' ++ ind_uparams D)
      by (rewrite List.app_assoc; exact (proj1 (closed_app_sem _ _ HaC0 HWc0 HUD))).
    assert (HTc : forall j0 A, List.nth_error tc j0 = Some (ce_ass A) ->
                    exists i : nat, List.rev (List.firstn j0 tc) ++ ind_uparams D' ++ ind_uparams D ⊨ A : Typeω@i).
    { intros j0 A HA; destruct (HTc0 _ _ HA) as [i HAv].
      assert (Ha0 : tele_ass (List.rev (List.firstn j0 tc) ++ ind_uparams D'))
        by (apply List.Forall_app; split; [ exact (tele_ass_firstn _ _ Hac) | exact (decl_closed_ass _ HcQ) ]).
      exists i; rewrite List.app_assoc; exact (closed_app_valid _ _ _ _ _ Ha0 (rel_ctx_wf_firstn _ _ j0 HWc0) HUD HAv). }
    assert (HWg : ⊨ List.rev tg ++ ind_uparams D) by (unfold tg; rewrite List.rev_involutive; exact (valid_ind_decl_params _ HD _ _ HMv)).
    assert (HTg : forall j0 A, List.nth_error tg j0 = Some (ce_ass A) ->
                    exists i : nat, List.rev (List.firstn j0 tg) ++ ind_uparams D ⊨ A : Typeω@i)
      by (intros j0 A HA; exact (proj2 (valid_ind_decl_npar _ HD _ _ _ _ HMv HA))).
    assert (Heq : ind_uparams D ⊨ˣ tele_sub (List.rev tg) Id ≈ tele_sub (List.rev tc) (sb_of_list Id Is)).
    { unfold tg, tc; rewrite !List.rev_involutive, tele_sub_id.
      exact (vg_view_nparams p D Hg Hcv _ _ _ _ _ _ _ _ _ _ _ HMm Hh Hq HMi' Hv HMv). }
    assert (Hlen : List.length tg = List.length tc) by (unfold tg, tc; rewrite !List.length_rev, !length_im_nparams; exact Hnn).
    destruct (gsub_props (vg_view_args_gsub p D Hg Hcv _ _ _ _ _ _ _ HMm Hh Hq)) as [Hτ _].
    pose proof (eval_sb_of_list _ _ _ _ _ (eval_sub_id (env_args nil u0)) Ecups) as Eτ.
    pose proof (tele_link_types (ind_uparams D) RU (env_args nil u0) HRU HρU (ind_uparams D) (ind_uparams D' ++ ind_uparams D)
                  Id (sb_of_list Id Is) Eg Ec (rel_sub_id (ex_intro _ _ HRU)) Hτ (eval_sub_id _) Eτ tg tc Hag Hac Hlen HWg HWc
                  HTg HTc Heq) as Hlink.
    (** Step by step along the two telescopes. *)
    assert (Main : forall n j preA preB, j + n = List.length tg -> List.length preA = j -> List.length preB = j ->
               per_gargs (List.firstn j tc) (env_args nil ub) Ec preA preB ->
               per_gargs (List.firstn j tc) Ec Ec preB preB ->
               per_gargs (List.firstn j tg) Eg Eg preA preB ->
               per_gargs (List.firstn j tg) Eg Eg preB preB ->
               tele_prefix_rel (nr v) j preA preB ->
               forall s rA rB, Ftele List.skipn j tc in gc_deps ⍮ gc_stack ⍮ env_args nil (ub ++ preA) ⍮ s ↘ rA ->
                 Ftele List.skipn j tg in gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ preB) ⍮ s ↘ rB ->
                 tele_prefix_rel (nr v) (List.length tg) (preA ++ rA) (preB ++ rB) /\
                 per_gargs tc (env_args nil ub) Ec (preA ++ rA) (preB ++ rB) /\
                 per_gargs tc Ec Ec (preB ++ rB) (preB ++ rB) /\
                 per_gargs tg Eg Eg (preB ++ rB) (preB ++ rB)).
    { induction n as [| n IH]; intros j preA preB Hjn LA LB G1 G2 G3 G4 Hpre s rA rB FA FB.
      - rewrite List.skipn_all2 in FA by (rewrite <- Hlen; lia).
        rewrite List.skipn_all2 in FB by lia.
        rewrite Nat.add_0_r in Hjn.
        rewrite List.firstn_all2 in G1, G2 by (rewrite <- Hlen; lia).
        rewrite List.firstn_all2 in G4 by lia.
        inversion FA; inversion FB; subst; rewrite !List.app_nil_r.
        split; [ exact Hpre | split; [ exact G1 | split; [ exact G2 | exact G4 ] ] ].
      - destruct (List.nth_error tc j) as [ec |] eqn:HC; [| apply List.nth_error_None in HC; lia ].
        destruct (List.nth_error tg j) as [eg |] eqn:HG; [| apply List.nth_error_None in HG; lia ].
        destruct (proj1 (List.Forall_forall _ _) Hac ec (List.nth_error_In _ _ HC)) as [C ->].
        destruct (proj1 (List.Forall_forall _ _) Hag eg (List.nth_error_In _ _ HG)) as [G ->].
        rewrite (skipn_nth_cons _ _ _ HC) in FA; rewrite (skipn_nth_cons _ _ _ HG) in FB.
        destruct (fresh_tele_cons_inv _ _ _ _ _ FA) as (aA & rA0 & -> & EaA & FA'); clear FA.
        destruct (fresh_tele_cons_inv _ _ _ _ _ FB) as (aB & rB0 & -> & EaB & FB'); clear FB.
        assert (HlA : List.length preA = List.length (List.rev (List.firstn j tc))) by (rewrite List.length_rev, List.length_firstn; lia).
        assert (HlB : List.length preA = List.length (List.rev (List.firstn j tg))) by (rewrite List.length_rev, List.length_firstn; lia).
        (** The container's type at [ub] against it at the instance. *)
        destruct (HTc0 _ _ HC) as [iC HCv].
        destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_firstn _ _ j HWc0)) as [RC HRC].
        pose proof G1 as G1'; rewrite <- (List.rev_involutive (List.firstn j tc)) in G1'.
        pose proof (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRQ HRC (rel_ctx_wf_firstn _ _ j HWc0) HQbE HlA G1') as E1.
        destruct (rel_exp_of_typ_inversion_simple_at HRC HCv _ _ E1) as (a1 & a2 & Ea1 & Ea2 & [R12 H12]).
        rewrite <- env_args_app in Ea1.
        assert (a1 = aA) as -> by (eapply functional_eval_exp; eassumption).
        (** The container's at the instance against the group's. *)
        destruct (Hlink j preB G C LB HG HC G4 G2) as (iL & RL & b & a & Eb & Ea & Hba).
        unfold Eg in Eb; rewrite <- env_args_app in Eb.
        assert (b = aB) as -> by (eapply functional_eval_exp; eassumption).
        assert (a2 = a) as -> by (eapply functional_eval_exp; eassumption).
        destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ H12 (per_univ_sym _ _ _ _ Hba)) as (Rx & Hx & _).
        (** The group's type at the two prefixes. *)
        destruct (HTg _ _ HG) as [iG HGv].
        destruct (rel_ctx_wf_per_ctx_env (rel_ctx_wf_firstn _ _ j HWg)) as [RG HRG].
        pose proof G3 as G3'; rewrite <- (List.rev_involutive (List.firstn j tg)) in G3'.
        pose proof (gargs_env_rel_gen _ _ _ _ _ _ _ _ HRU HRG (rel_ctx_wf_firstn _ _ j HWg) HρU HlB G3') as E3.
        destruct (rel_exp_of_typ_inversion_simple_at HRG HGv _ _ E3) as (g1 & g2 & Eg1 & Eg2 & [Rg Hg12]).
        unfold Eg in Eg1, Eg2; rewrite <- env_args_app in Eg1, Eg2.
        assert (g2 = aB) as -> by (eapply functional_eval_exp; eassumption).
        (** The fresh variables. *)
        assert (Hxx : Rx (⇑! aA s) (⇑! aB s)) by exact (per_bot_then_per_elem Hx var_per_bot).
        assert (HRg : Rg (⇑! aA s) (⇑! aB s)) by (apply (per_univ_elem_left_irrel _ _ _ _ _ _ _ Hg12 Hx); exact Hxx).
        assert (H12x : R12 (⇑! aA s) (⇑! aB s)) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ H12 Hx); exact Hxx).
        pose proof (per_univ_trans _ _ _ _ _ _ Hba (per_univ_sym _ _ _ _ Hba)) as Hbb.
        pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hba) Hba) as Haa.
        assert (Hbbx : RL (⇑! aB s) (⇑! aB s)) by exact (per_bot_then_per_elem Hbb var_per_bot).
        assert (Hnrx : nr v j preA (⇑! aA s) (⇑! aB s)).
        { unfold nr, canon_nparams_rel; rewrite (nth_ctyp_eq _ _ _ _ _ HMv HG).
          apply (per_head_left Eg1 Eg2 Hg12); exact HRg. }
        assert (HfC : List.firstn (S j) tc = List.firstn j tc ++ ce_ass C :: nil) by exact (firstn_S_nth _ _ _ HC).
        assert (HfG : List.firstn (S j) tg = List.firstn j tg ++ ce_ass G :: nil) by exact (firstn_S_nth _ _ _ HG).
        assert (LfC : List.length preA = List.length (List.firstn j tc)) by (rewrite List.length_firstn; lia).
        assert (LfC' : List.length preB = List.length (List.firstn j tc)) by (rewrite List.length_firstn; lia).
        assert (LfG : List.length preA = List.length (List.firstn j tg)) by (rewrite List.length_firstn; lia).
        assert (LfG' : List.length preB = List.length (List.firstn j tg)) by (rewrite List.length_firstn; lia).
        pose proof (IH (S j) (preA ++ ⇑! aA s :: nil) (preB ++ ⇑! aB s :: nil) ltac:(lia)
                      ltac:(rewrite List.length_app; cbn; lia) ltac:(rewrite List.length_app; cbn; lia)) as IH'.
        rewrite HfC, HfG in IH'.
        replace (preA ++ ⇑! aA s :: rA0) with ((preA ++ ⇑! aA s :: nil) ++ rA0) by (rewrite <- List.app_assoc; reflexivity).
        replace (preB ++ ⇑! aB s :: rB0) with ((preB ++ ⇑! aB s :: nil) ++ rB0) by (rewrite <- List.app_assoc; reflexivity).
        refine (IH' _ _ _ _ _ (S s) _ _ _ _).
        + apply (per_gargs_snoc _ C _ _ _ _ _ _ iC R12 LfC G1); [ econstructor; [ rewrite <- env_args_app; exact EaA | exact Ea | exact H12 ] | exact H12x ].
        + apply (per_gargs_snoc _ C _ _ _ _ _ _ iL RL LfC' G2); [ econstructor; [ exact Ea | exact Ea | exact Haa ] | exact Hbbx ].
        + assert (Eg1' : ⟦ G ⟧ env_args Eg preA ↘ g1) by (unfold Eg; rewrite <- env_args_app; exact Eg1).
          assert (EaB' : ⟦ G ⟧ env_args Eg preB ↘ aB) by (unfold Eg; rewrite <- env_args_app; exact EaB).
          apply (per_gargs_snoc _ G _ _ _ _ _ _ iG Rg LfG G3); [ econstructor; [ exact Eg1' | exact EaB' | exact Hg12 ] | exact HRg ].
        + assert (EaB' : ⟦ G ⟧ env_args Eg preB ↘ aB) by (unfold Eg; rewrite <- env_args_app; exact EaB).
          apply (per_gargs_snoc _ G _ _ _ _ _ _ iL RL LfG' G4); [ econstructor; [ exact EaB' | exact EaB' | exact Hbb ] | exact Hbbx ].
        + apply tele_prefix_rel_snoc; [ exact Hpre | exact Hnrx ].
        + rewrite List.app_assoc, env_args_snoc; exact FA'.
        + rewrite List.app_assoc, env_args_snoc; exact FB'.
    }
    intros s nsA nsB FA FB.
    pose proof (Main (List.length tg) 0 nil nil eq_refl eq_refl eq_refl ltac:(constructor) ltac:(constructor) ltac:(constructor)
                  ltac:(constructor) (tele_prefix_rel_nil _) s nsA nsB) as H.
    cbn [List.skipn List.app] in H; rewrite !List.app_nil_r in H.
    destruct (H FA FB) as (Hpre & G1 & G2 & G4).
    assert (HWt : ⊨ List.rev tc ++ ind_uparams D') by exact HWc0.
    assert (HQcb : RQ Ec (env_args nil cups)) by (symmetry; exact HQc).
    assert (HQbb : RQ (env_args nil ub) (env_args nil ub)) by (etransitivity; [ exact HQb | symmetry; exact HQb ]).
    pose proof (per_gargs_base _ _ _ HRQ HWt Hac _ _ _ _ _ _ HQbE HQbb HQcb G1) as G1'.
    pose proof (per_gargs_base _ _ _ HRQ HWt Hac _ _ _ _ _ _ HQEE HQcb HQcb G2) as G2'.
    assert (Hub' : per_gargs (List.rev (ind_uparams D')) nil nil ub cups) by exact Hub.
    constructor; unfold im_params; rewrite ?List.rev_app_distr.
    - apply tele_rel_of_pre; exact Hpre.
    - apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hlb | exact Hub' | exact G1' ].
    - apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hlc | exact Hcc | exact G2' ].
    - apply per_gargs_app_intro; [ rewrite List.length_rev; exact Hu | exact Hgu | exact G4 ].
  Qed.

  (** *** The Fresh Arguments of a Constructor

      Of the constructor [c] of the container's member (kinds [gsA]) and of
      the group's (kinds [gsB]), after the fresh non-uniform parameters
      [nsA] and [nsB]: related at the group's relations ([con_args_rel] and
      its non-recursive ones), position by position.  The invariant is the
      container's telescope between the two sides and at the group's side,
      and the group's telescope at its side; each type the container's
      variable has is related to the group's through them. *)
  Section CrossArgs.
    Variables (c : String.string) (gsA gsB : list carg).
    Hypotheses (HconA : ind_con Mi' c = Some gsA) (HconB : ind_con Mv c = Some gsB) (Hcorr : cargs_corr vm gsA gsB).
    Variables (nsA nsB : list domain).
    Hypothesis (Hcp : cross_params nsA nsB).
    Hypothesis (HnsA : tele_rel (canon_nparams_rel D' ub i') (List.rev (im_nparams Mi')) nsA nsA).
    Let ar := canon_args_rel D u0.
    Let dr := canon_doms_rel u0.

    (** The invariant past one position, the container's variable [aA] and
        the group's [aB] there, at the group's type [CG]: the container's
        prefixes related across and at the group's side, the group's at its
        side, the two variables related at [CG], and their types related. *)
    Record cross_position_step (gA1 : list carg) (gA : carg) (gB1 : list carg) (gB : carg) (vA1 vB1 : list domain)
        (CG : exp) (aA aB : domain) (s : nat) : Prop := mk_cross_position_step
      { (** The container's prefixes related across *)
        container_prefix_rel : per_gargs (List.rev (cargs_ctx qc D' Mi' (gA1 ++ gA :: nil) ++ im_params D' Mi')) nil nil
          (ub ++ nsA ++ vA1 ++ ⇑! aA s :: nil) (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil)
        (** The group's side related to itself at the container's
            telescope *)
      ; container_right_prefix : per_gargs (List.rev (cargs_ctx qc D' Mi' (gA1 ++ gA :: nil) ++ im_params D' Mi')) nil nil
          (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil) (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil)
        (** The group's side related to itself at the group's telescope *)
      ; group_right_prefix : per_gargs (List.rev (cargs_ctx p D Mv (gB1 ++ gB :: nil) ++ im_params D Mv)) nil nil
          (u0 ++ nsB ++ vB1 ++ ⇑! aB s :: nil) (u0 ++ nsB ++ vB1 ++ ⇑! aB s :: nil)
        (** The two variables related at [CG] *)
      ; fresh_heads_agree : per_head CG CG (env_args nil (u0 ++ nsB ++ vB1)) (env_args nil (u0 ++ nsB ++ vB1)) (⇑! aA s) (⇑! aB s)
        (** Their types related *)
      ; fresh_types_related : exists (i : universe_index) R, DF aA ≈ aB ∈ per_univ_elem i ↘ R }.

    (** One position:the container's type there [CA], the group's [CG],
        the container's variable's type [aA] related to [CA] at its side,
        the group's [aB] to [CG] at its: the invariant extends, and the
        variables are related at the group's type. *)
    Lemma cross_position : forall gA1 gA gA2 gB1 gB gB2 vA1 vB1 CA CG aA aB s,
        gsA = gA1 ++ gA :: gA2 -> gsB = gB1 ++ gB :: gB2 -> cargs_corr vm gA1 gB1 ->
        List.length vA1 = List.length gA1 -> List.length vB1 = List.length gB1 ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (ub ++ nsA ++ vA1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (cups ++ nsB ++ vB1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx p D Mv gB1 ++ im_params D Mv)) nil nil (u0 ++ nsB ++ vB1) (u0 ++ nsB ++ vB1) ->
        cargs_ctx qc D' Mi' (gA1 ++ gA :: nil) = ce_ass CA :: cargs_ctx qc D' Mi' gA1 ->
        cargs_ctx p D Mv (gB1 ++ gB :: nil) = ce_ass CG :: cargs_ctx p D Mv gB1 ->
        (exists (i : nat) R cA, ⟦ CA ⟧ env_args nil (ub ++ nsA ++ vA1) ↘ cA /\ DF cA ≈ aA ∈ per_univ_elem i ↘ R) ->
        (exists (i : nat) R gB0, ⟦ CG ⟧ env_args nil (u0 ++ nsB ++ vB1) ↘ gB0 /\ DF gB0 ≈ aB ∈ per_univ_elem i ↘ R) ->
        cross_position_step gA1 gA gB1 gB vA1 vB1 CG aA aB s.
    Proof.
      intros * HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg [iA [RA [cA' [EcA' HcaA]]]] [iB [RB [gB' [EgB' HgaB]]]].
      destruct Hcp as [Hns HpA HpC HpG].
      pose proof (view_nn p D Hg m Mm qc k' Is vm D' HMm Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
      pose proof (length_cups p D Hg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups) as Hlc.
      assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
      pose proof Hns as Hns0; rewrite tele_rel_iff in Hns0; destruct Hns0 as (LnA & LnB & _).
      rewrite List.length_rev, length_im_nparams in LnA, LnB.
      assert (Hl1 : List.length gA1 = List.length gB1) by exact (cargs_corr_len _ _ _ Hc1).
      (** The container's type, at the two sides. *)
      destruct (vg_cargs_sem_all qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA (gA1 ++ gA :: nil) gA2
                  ltac:(rewrite <- List.app_assoc; exact HeA)) as [HWc1 _].
      rewrite ECc in HWc1.
      destruct (rel_ctx_wf_ass_inv HWc1) as [ic HCv].
      pose proof (rel_ctx_wf_tail HWc1) as HWc.
      destruct (rel_ctx_wf_per_ctx_env HWc) as [RW HRW].
      assert (LW : List.length (ub ++ nsA ++ vA1) = List.length (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi'))
        by (rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      pose proof (gargs_env_rel _ _ _ _ _ _ HRW HWc LW K1) as E1.
      destruct (rel_exp_of_typ_inversion_simple_at HRW HCv _ _ E1) as (cA & cB & EcA & EcB & [RC HRC]).
      assert (cA' = cA) as -> by (eapply functional_eval_exp; eassumption).
      (** The container's type at the group's side against the group's. *)
      pose proof (view_arg_link p D Hg Hcv m Mm qc k' Is vm D' HMm Hh Hq HcvQ u0 cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
                    c gsA gsB HconA HconB Hcorr nsB LnB gA1 gA gA2 gB1 gB gB2 CA CG vB1 HeA HeB (eq_sym Hl1) LB ECc ECg K3 K2) as HL.
      destruct (group_container_types_related _ _ _ _ HL) as (iL & RL & gB0 & cB0 & EgB & EcB0 & HgcL).
      assert (cB0 = cB) as -> by (eapply functional_eval_exp; eassumption).
      assert (gB' = gB0) as -> by (eapply functional_eval_exp; eassumption).
      (** The chain from the container's variable to the group's. *)
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ HcaA) HRC) as (R1 & H1 & _).
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ H1 (per_univ_sym _ _ _ _ HgcL)) as (R2 & H2 & _).
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ H2 HgaB) as (Rx & Hx & _).
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ HgcL) HgaB) as (R3 & H3 & _).
      pose proof (fresh_var_rel _ _ _ _ s Hx) as Hxx.
      pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hx) Hx) as Hbb.
      pose proof (fresh_var_rel _ _ _ _ s Hbb) as Hxb.
      pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRC) HRC) as HCC.
      pose proof (per_univ_trans _ _ _ _ _ _ HgcL (per_univ_sym _ _ _ _ HgcL)) as HGG.
      assert (HRCx : RC (⇑! aA s) (⇑! aB s))
        by (apply (rel_link _ _ _ _ _ _ _ _ _ _ HRC (per_univ_sym _ _ _ _ H1) Hx); exact Hxx).
      assert (HCCx : RC (⇑! aB s) (⇑! aB s)) by (apply (rel_link _ _ _ _ _ _ _ _ _ _ HCC H3 Hbb); exact Hxb).
      assert (HGGx : RL (⇑! aB s) (⇑! aB s)) by (apply (rel_link _ _ _ _ _ _ _ _ _ _ HGG HgaB Hbb); exact Hxb).
      assert (HGAx : RL (⇑! aA s) (⇑! aB s))
        by (apply (rel_link _ _ _ _ _ _ _ _ _ _ HGG (per_univ_sym _ _ _ _ H2) Hx); exact Hxx).
      assert (LW' : List.length (ub ++ nsA ++ vA1) = List.length (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')))
        by (rewrite List.length_rev; exact LW).
      assert (LW2 : List.length (cups ++ nsB ++ vB1) = List.length (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')))
        by (rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      assert (LW3 : List.length (u0 ++ nsB ++ vB1) = List.length (List.rev (cargs_ctx p D Mv gB1 ++ im_params D Mv)))
        by (rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      constructor; [ rewrite ECc | rewrite ECc | rewrite ECg | idtac | idtac ];
        cbn [List.app List.rev];
        [ replace (ub ++ nsA ++ vA1 ++ ⇑! aA s :: nil) with ((ub ++ nsA ++ vA1) ++ ⇑! aA s :: nil)
            by (rewrite <- !List.app_assoc; reflexivity);
          replace (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil) with ((cups ++ nsB ++ vB1) ++ ⇑! aB s :: nil)
            by (rewrite <- !List.app_assoc; reflexivity)
        | replace (cups ++ nsB ++ vB1 ++ ⇑! aB s :: nil) with ((cups ++ nsB ++ vB1) ++ ⇑! aB s :: nil)
            by (rewrite <- !List.app_assoc; reflexivity)
        | replace (u0 ++ nsB ++ vB1 ++ ⇑! aB s :: nil) with ((u0 ++ nsB ++ vB1) ++ ⇑! aB s :: nil)
            by (rewrite <- !List.app_assoc; reflexivity)
        | idtac | idtac ].
      - apply (per_gargs_snoc _ CA _ _ _ _ _ _ ic RC LW' K1); [ econstructor; [ exact EcA | exact EcB | exact HRC ] | exact HRCx ].
      - apply (per_gargs_snoc _ CA _ _ _ _ _ _ ic RC LW2 K2); [ econstructor; [ exact EcB | exact EcB | exact HCC ] | exact HCCx ].
      - apply (per_gargs_snoc _ CG _ _ _ _ _ _ iL RL LW3 K3); [ econstructor; [ exact EgB | exact EgB | exact HGG ] | exact HGGx ].
      - apply (per_head_left EgB EgB HGG); exact HGAx.
      - exists iA, Rx; exact Hx.
    Qed.

    (** The invariant past one position at given values: the container's
        [x] and the group's [x'] there, related at the group's type at its
        side; and the two sides' types there related. *)
    #[warnings="-cannot-define-projection"]
    Record cross_vals_step (gA1 : list carg) (gA : carg) (gB1 : list carg) (gB : carg) (vA1 vB1 : list domain)
        (CA CG : exp) (x x' : domain) : Prop := mk_cross_vals_step
      { (** The container's prefixes related across *)
        vals_container_prefix : per_gargs (List.rev (cargs_ctx qc D' Mi' (gA1 ++ gA :: nil) ++ im_params D' Mi')) nil nil
          (ub ++ nsA ++ vA1 ++ x :: nil) (cups ++ nsB ++ vB1 ++ x' :: nil)
        (** The group's side related to itself at the container's
            telescope *)
      ; vals_container_right : per_gargs (List.rev (cargs_ctx qc D' Mi' (gA1 ++ gA :: nil) ++ im_params D' Mi')) nil nil
          (cups ++ nsB ++ vB1 ++ x' :: nil) (cups ++ nsB ++ vB1 ++ x' :: nil)
        (** The group's side related to itself at the group's telescope *)
      ; vals_group_right : per_gargs (List.rev (cargs_ctx p D Mv (gB1 ++ gB :: nil) ++ im_params D Mv)) nil nil
          (u0 ++ nsB ++ vB1 ++ x' :: nil) (u0 ++ nsB ++ vB1 ++ x' :: nil)
        (** The container's type at its side and the group's at its,
            related *)
      ; vals_types_related : exists (i : nat) R cA gB0, ⟦ CA ⟧ env_args nil (ub ++ nsA ++ vA1) ↘ cA /\
          ⟦ CG ⟧ env_args nil (u0 ++ nsB ++ vB1) ↘ gB0 /\ DF cA ≈ gB0 ∈ per_univ_elem i ↘ R }.

    Lemma cross_position_vals : forall gA1 gA gA2 gB1 gB gB2 vA1 vB1 CA CG x x',
        gsA = gA1 ++ gA :: gA2 -> gsB = gB1 ++ gB :: gB2 -> cargs_corr vm gA1 gB1 ->
        List.length vA1 = List.length gA1 -> List.length vB1 = List.length gB1 ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (ub ++ nsA ++ vA1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (cups ++ nsB ++ vB1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx p D Mv gB1 ++ im_params D Mv)) nil nil (u0 ++ nsB ++ vB1) (u0 ++ nsB ++ vB1) ->
        cargs_ctx qc D' Mi' (gA1 ++ gA :: nil) = ce_ass CA :: cargs_ctx qc D' Mi' gA1 ->
        cargs_ctx p D Mv (gB1 ++ gB :: nil) = ce_ass CG :: cargs_ctx p D Mv gB1 ->
        (exists (i : nat) R gB0, ⟦ CG ⟧ env_args nil (u0 ++ nsB ++ vB1) ↘ gB0 /\ DF gB0 ≈ gB0 ∈ per_univ_elem i ↘ R /\ R x x') ->
        cross_vals_step gA1 gA gB1 gB vA1 vB1 CA CG x x'.
    Proof.
      intros * HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg [iB [RB [gB' [EgB' [HgB Hxx]]]]].
      destruct Hcp as [Hns HpA HpC HpG].
      pose proof (view_nn p D Hg m Mm qc k' Is vm D' HMm Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
      pose proof (length_cups p D Hg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups) as Hlc.
      assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
      pose proof Hns as Hns0; rewrite tele_rel_iff in Hns0; destruct Hns0 as (LnA & LnB & _).
      rewrite List.length_rev, length_im_nparams in LnA, LnB.
      assert (Hl1 : List.length gA1 = List.length gB1) by exact (cargs_corr_len _ _ _ Hc1).
      (** The container's type, at the two sides. *)
      destruct (vg_cargs_sem_all qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA (gA1 ++ gA :: nil) gA2
                  ltac:(rewrite <- List.app_assoc; exact HeA)) as [HWc1 _].
      rewrite ECc in HWc1.
      destruct (rel_ctx_wf_ass_inv HWc1) as [ic HCv].
      pose proof (rel_ctx_wf_tail HWc1) as HWc.
      destruct (rel_ctx_wf_per_ctx_env HWc) as [RW HRW].
      assert (LW : List.length (ub ++ nsA ++ vA1) = List.length (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi'))
        by (rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      pose proof (gargs_env_rel _ _ _ _ _ _ HRW HWc LW K1) as E1.
      destruct (rel_exp_of_typ_inversion_simple_at HRW HCv _ _ E1) as (cA & cB & EcA & EcB & [RC HRC]).
      (** The container's type at the group's side against the group's. *)
      pose proof (view_arg_link p D Hg Hcv m Mm qc k' Is vm D' HMm Hh Hq HcvQ u0 cups Hgu Hu Ecups i' Mi' v Mv HMi' Hv HMv
                    c gsA gsB HconA HconB Hcorr nsB LnB gA1 gA gA2 gB1 gB gB2 CA CG vB1 HeA HeB (eq_sym Hl1) LB ECc ECg K3 K2) as HL.
      destruct (group_container_types_related _ _ _ _ HL) as (iL & RL & gB0 & cB0 & EgB & EcB0 & HgcL).
      assert (cB0 = cB) as -> by (eapply functional_eval_exp; eassumption).
      assert (gB' = gB0) as -> by (eapply functional_eval_exp; eassumption).
      (** The values, at each of the types. *)
      assert (HPB : PER RB) by (eapply per_elem_PER; exact HgB).
      assert (Hx'x' : RB x' x') by (etransitivity; [ symmetry; exact Hxx | exact Hxx ]).
      pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HRC) HRC) as HCC.
      pose proof (per_univ_trans _ _ _ _ _ _ HgcL (per_univ_sym _ _ _ _ HgcL)) as HGG.
      assert (HRCx : RC x x') by (apply (rel_link _ _ _ _ _ _ _ _ _ _ HRC (per_univ_sym _ _ _ _ HgcL) HgB); exact Hxx).
      assert (HCCx : RC x' x') by (apply (rel_link _ _ _ _ _ _ _ _ _ _ HCC (per_univ_sym _ _ _ _ HgcL) HgB); exact Hx'x').
      assert (HGGx : RL x' x') by (apply (rel_link _ _ _ _ _ _ _ _ _ _ HGG HgB HgB); exact Hx'x').
      destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ HRC (per_univ_sym _ _ _ _ HgcL)) as (Rx & Hx & _).
      assert (LW' : List.length (ub ++ nsA ++ vA1) = List.length (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')))
        by (rewrite List.length_rev; exact LW).
      assert (LW2 : List.length (cups ++ nsB ++ vB1) = List.length (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')))
        by (rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      assert (LW3 : List.length (u0 ++ nsB ++ vB1) = List.length (List.rev (cargs_ctx p D Mv gB1 ++ im_params D Mv)))
        by (rewrite List.length_rev, !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
      constructor; [ rewrite ECc | rewrite ECc | rewrite ECg | idtac ];
        cbn [List.app List.rev];
        [ replace (ub ++ nsA ++ vA1 ++ x :: nil) with ((ub ++ nsA ++ vA1) ++ x :: nil)
            by (rewrite <- !List.app_assoc; reflexivity);
          replace (cups ++ nsB ++ vB1 ++ x' :: nil) with ((cups ++ nsB ++ vB1) ++ x' :: nil)
            by (rewrite <- !List.app_assoc; reflexivity)
        | replace (cups ++ nsB ++ vB1 ++ x' :: nil) with ((cups ++ nsB ++ vB1) ++ x' :: nil)
            by (rewrite <- !List.app_assoc; reflexivity)
        | replace (u0 ++ nsB ++ vB1 ++ x' :: nil) with ((u0 ++ nsB ++ vB1) ++ x' :: nil)
            by (rewrite <- !List.app_assoc; reflexivity)
        | idtac ].
      - apply (per_gargs_snoc _ CA _ _ _ _ _ _ ic RC LW' K1); [ econstructor; [ exact EcA | exact EcB | exact HRC ] | exact HRCx ].
      - apply (per_gargs_snoc _ CA _ _ _ _ _ _ ic RC LW2 K2); [ econstructor; [ exact EcB | exact EcB | exact HCC ] | exact HCCx ].
      - apply (per_gargs_snoc _ CG _ _ _ _ _ _ iL RL LW3 K3); [ econstructor; [ exact EgB | exact EgB | exact HGG ] | exact HGGx ].
      - exists ic, Rx, cA, gB0; split; [ exact EcA | split; [ exact EgB | exact Hx ] ].
    Qed.

    (** A recursive argument related at the group's side's prefix on both
        sides is related at the two prefixes. *)
    Lemma cross_rec_move : forall gB1 t gB2 vA1 vB1 x y, gsB = gB1 ++ ca_rec t :: gB2 ->
        tele_prefix_rel (ar v nsA c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vA1) (nonrec_arg_vals gB1 vB1) ->
        tele_prefix_rel (ar v nsB c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vB1) (nonrec_arg_vals gB1 vB1) ->
        rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsB ++ nonrec_arg_vals gB1 vB1) (nsB ++ nonrec_arg_vals gB1 vB1) t x y ->
        rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsA ++ nonrec_arg_vals gB1 vA1) (nsB ++ nonrec_arg_vals gB1 vB1) t x y.
    Proof.
      intros * HeB K4 K6 H.
      destruct Hcp as [Hns _ _ _].
      destruct (vg_canon p D Hg u0 Hgu Hu) as [CnP CnI CaP CaI CdP CdI].
      pose proof (valid_group_ass _ _ Hg) as Hass.
      pose proof (nparams_rel_sym p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv _ _ Hns) as Hsn.
      pose proof (nparams_rel_refl_r p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv _ _ Hns) as HBB.
      pose proof (nparams_rel_refl_l p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv _ _ Hns) as HAA.
      assert (HconB' : ind_con Mv c = Some (gB1 ++ ca_rec t :: gB2)) by (rewrite <- HeB; exact HconB).
      assert (HK : List.length (cargs_nonrec gB1) <= List.length (cargs_nonrec gsB))
        by (rewrite HeB, cargs_nonrec_app, List.length_app; lia).
      pose proof (args_prefix_rel_sym p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv nsA c gsB _ _ _ HAA HconB HK K4) as K4A.
      pose proof (args_prefix_rel_inst p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv nsA nsB c gsB _ _ _ Hns HconB HK K4A) as K4s.
      destruct (ind_rel_sym_all p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI (okr_at D u0 nr)) as (_ & _ & Hsym & _).
      pose proof (Hsym _ _ _ _ _ _ _ _ H Mv nsB nsB c gB1 t gB2 _ _ 0 nil nil HMv
                    ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity) HBB HconB' K6
                    eq_refl ltac:(lia) (tele_prefix_rel_nil _)) as H1.
      pose proof (proj1 (vg_rec_arg_move_right p D Hg v Mv c gB1 t gB2 u0 u0 nsB nsA _ _ _ _ HMv HconB' Hgu Hu Hsn K4s) H1) as H2.
      exact (Hsym _ _ _ _ _ _ _ _ H2 Mv nsB nsA c gB1 t gB2 _ _ 0 nil nil HMv
               ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity) Hsn HconB' K4s
               eq_refl ltac:(lia) (tele_prefix_rel_nil _)).
    Qed.

    (** And back: related at the two prefixes, related at the group's
        side's on both sides. *)
    Lemma cross_rec_move_back : forall gB1 t gB2 vA1 vB1 x y, gsB = gB1 ++ ca_rec t :: gB2 ->
        tele_prefix_rel (ar v nsA c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vA1) (nonrec_arg_vals gB1 vB1) ->
        tele_prefix_rel (ar v nsB c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vB1) (nonrec_arg_vals gB1 vB1) ->
        rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsA ++ nonrec_arg_vals gB1 vA1) (nsB ++ nonrec_arg_vals gB1 vB1) t x y ->
        rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsB ++ nonrec_arg_vals gB1 vB1) (nsB ++ nonrec_arg_vals gB1 vB1) t x y.
    Proof.
      intros * HeB K4 K6 H.
      destruct Hcp as [Hns _ _ _].
      destruct (vg_canon p D Hg u0 Hgu Hu) as [CnP CnI CaP CaI CdP CdI].
      pose proof (valid_group_ass _ _ Hg) as Hass.
      pose proof (nparams_rel_sym p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv _ _ Hns) as Hsn.
      pose proof (nparams_rel_refl_r p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv _ _ Hns) as HBB.
      pose proof (nparams_rel_refl_l p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv _ _ Hns) as HAA.
      assert (HconB' : ind_con Mv c = Some (gB1 ++ ca_rec t :: gB2)) by (rewrite <- HeB; exact HconB).
      assert (HK : List.length (cargs_nonrec gB1) <= List.length (cargs_nonrec gsB))
        by (rewrite HeB, cargs_nonrec_app, List.length_app; lia).
      pose proof (args_prefix_rel_sym p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv nsA c gsB _ _ _ HAA HconB HK K4) as K4A.
      pose proof (args_prefix_rel_inst p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv nsA nsB c gsB _ _ _ Hns HconB HK K4A) as K4s.
      destruct (ind_rel_sym_all p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI (okr_at D u0 nr)) as (_ & _ & Hsym & _).
      pose proof (Hsym _ _ _ _ _ _ _ _ H Mv nsA nsB c gB1 t gB2 _ _ 0 nil nil HMv
                    ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity) Hns HconB' K4
                    eq_refl ltac:(lia) (tele_prefix_rel_nil _)) as H1.
      pose proof (proj2 (vg_rec_arg_move_right p D Hg v Mv c gB1 t gB2 u0 u0 nsB nsA _ _ _ _ HMv HconB' Hgu Hu Hsn K4s) H1) as H2.
      exact (Hsym _ _ _ _ _ _ _ _ H2 Mv nsB nsB c gB1 t gB2 _ _ 0 nil nil HMv
               ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity) HBB HconB' K6
               eq_refl ltac:(lia) (tele_prefix_rel_nil _)).
    Qed.

    (** The rest of the arguments after the positions [gA1] and [gB1], at
        the prefixes [vA1] and [vB1]: the fresh variables on each side, the
        arguments related at the group's relation, the non-recursive ones
        at their types, and the types of the ones recursive in both read
        alike at their domains. *)
    #[warnings="-cannot-define-projection"]
    Record cross_fresh_tail (gA1 gB1 gA2 gB2 : list carg) (vA1 vB1 : list domain) (s : nat) : Prop := mk_cross_fresh_tail
      { (** The container's fresh arguments *)
        cross_fresh_tail_vsA : list domain
        (** The group's fresh arguments *)
      ; cross_fresh_tail_vsB : list domain
        (** The container's are fresh at [ub] *)
      ; cross_fresh_tail_args_a : Fcargs gA2 of qc ub in gc_deps ⍮ gc_stack ⍮ env_args nil (ub ++ nsA ++ nonrec_arg_vals gA1 vA1) ⍮ s ↘ cross_fresh_tail_vsA
        (** The group's are fresh at [u0] *)
      ; cross_fresh_tail_args_b : Fcargs gB2 of p u0 in gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ nsB ++ nonrec_arg_vals gB1 vB1) ⍮ s ↘ cross_fresh_tail_vsB
        (** They are related at the group's relation *)
      ; cross_fresh_tail_related : con_args_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsA ++ nonrec_arg_vals gB1 vA1)
          (nsB ++ nonrec_arg_vals gB1 vB1) gB2 cross_fresh_tail_vsA cross_fresh_tail_vsB
        (** The non-recursive ones are related at their types *)
      ; cross_fresh_tail_nonrec : tele_rel_from (ar v nsA c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vA1)
          (nonrec_arg_vals gB2 cross_fresh_tail_vsA) (nonrec_arg_vals gB2 cross_fresh_tail_vsB)
        (** The types of the ones recursive in both read alike at their
            domains *)
      ; cross_fresh_tail_tops : cross_tops qc D' ub u0 dr i' v (nsA ++ nonrec_arg_vals gB1 vA1) (nsA ++ nonrec_arg_vals gA1 vA1)
          (nsB ++ nonrec_arg_vals gB1 vB1) gA2 gB2 cross_fresh_tail_vsA cross_fresh_tail_vsB }.

    Lemma cross_fresh_cargs : forall gA2 gB2 gA1 gB1 vA1 vB1, gsA = gA1 ++ gA2 -> gsB = gB1 ++ gB2 -> cargs_corr vm gA1 gB1 ->
        List.length vA1 = List.length gA1 -> List.length vB1 = List.length gB1 ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (ub ++ nsA ++ vA1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (cups ++ nsB ++ vB1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx p D Mv gB1 ++ im_params D Mv)) nil nil (u0 ++ nsB ++ vB1) (u0 ++ nsB ++ vB1) ->
        tele_prefix_rel (ar v nsA c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vA1) (nonrec_arg_vals gB1 vB1) ->
        tele_prefix_rel (canon_args_rel D' ub i' nsA c) (List.length (cargs_nonrec gA1))
          (nonrec_arg_vals gA1 vA1) (nonrec_arg_vals gA1 vA1) ->
        tele_prefix_rel (ar v nsB c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vB1) (nonrec_arg_vals gB1 vB1) ->
        forall s, cross_fresh_tail gA1 gB1 gA2 gB2 vA1 vB1 s.
    Proof.
      induction gA2 as [| gA gA2 IH]; intros [| gB gB2] gA1 gB1 vA1 vB1 HeA HeB Hc1 LA LB K1 K2 K3 K4 K5 K6 s.
      - apply (mk_cross_fresh_tail _ _ _ _ _ _ _ nil nil); first [ constructor | exact I ].
      - exfalso; pose proof (cargs_corr_len _ _ _ Hcorr) as H; rewrite HeA, HeB, !List.length_app in H.
        pose proof (cargs_corr_len _ _ _ Hc1); cbn in H; lia.
      - exfalso; pose proof (cargs_corr_len _ _ _ Hcorr) as H; rewrite HeA, HeB, !List.length_app in H.
        pose proof (cargs_corr_len _ _ _ Hc1); cbn in H; lia.
      - assert (Hl1 : List.length gA1 = List.length gB1) by exact (cargs_corr_len _ _ _ Hc1).
        assert (Hco : cargs_corr vm (gA :: gA2) (gB :: gB2))
          by (rewrite HeA, HeB in Hcorr; exact (proj2 (cargs_corr_split _ _ _ _ _ Hcorr Hl1))).
        pose proof Hcp as [Hns HpA HpC HpG].
        pose proof Hns as Hns0; rewrite tele_rel_iff in Hns0; destruct Hns0 as (LnA & LnB & _).
        rewrite List.length_rev, length_im_nparams in LnA, LnB.
        pose proof (view_nn p D Hg m Mm qc k' Is vm D' HMm Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
        pose proof (length_cups p D Hg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups) as Hlc.
        assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
        pose proof (uparams_refl_l D' (valid_group_valid _ _ HgQ) (valid_group_closed _ _ HgQ) _ _ Hub) as Hubub.
        destruct (vg_canon p D Hg u0 Hgu Hu) as [CnP CnI CaP CaI CdP CdI].
        pose proof (valid_group_ass _ _ Hg) as Hass.
        pose proof (nparams_rel_refl_r p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv _ _ Hns) as HnsB.
        assert (HeA'' : gsA = (gA1 ++ gA :: nil) ++ gA2) by (rewrite <- List.app_assoc; exact HeA).
        assert (HeB'' : gsB = (gB1 ++ gB :: nil) ++ gB2) by (rewrite <- List.app_assoc; exact HeB).
        assert (Hc1' : cargs_corr vm (gA1 ++ gA :: nil) (gB1 ++ gB :: nil)).
        { apply cargs_corr_app; [ exact Hc1 |].
          destruct gA, gB; cbn in Hco |- *; try contradiction; try exact I; tauto. }
        (** The container's telescope at its side, and the group's at its. *)
        destruct (vg_cargs_sem_all qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA gA1 (gA :: gA2) HeA) as [HWA0 _].
        destruct (vg_cargs_sem_all p D Hg Hcv v Mv c gsB HMv HconB gB1 (gB :: gB2) HeB) as [HWB0 _].
        destruct (vg_cargs_sem_all qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA gsA nil ltac:(rewrite List.app_nil_r; reflexivity))
          as [HΨA _].
        destruct (vg_cargs_sem_all p D Hg Hcv v Mv c gsB HMv HconB gsB nil ltac:(rewrite List.app_nil_r; reflexivity))
          as [HΨB _].
        assert (LWA : List.length (ub ++ nsA ++ vA1) = List.length (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi'))
          by (rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
        assert (LWB : List.length (u0 ++ nsB ++ vB1) = List.length (cargs_ctx p D Mv gB1 ++ im_params D Mv))
          by (rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
        assert (K1A : per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (ub ++ nsA ++ vA1) (ub ++ nsA ++ vA1)).
        { assert (HW' : ⊨ List.rev (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) ++ ⋅)
            by (rewrite List.rev_involutive, List.app_nil_r; exact HWA0).
          assert (Hta : tele_ass (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')))
            by (apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D' (valid_group_closed _ _ HgQ) i' Mi' HMi') ]).
          exact (per_gargs_refl_l _ _ _ per_ctx_env_nil_true HW' Hta _ _ _ _ I K1). }
        assert (RenvA : forall R, EF cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi' ≈ cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi' ∈ per_ctx_env ↘ R ->
                          R (env_args nil (ub ++ nsA ++ vA1)) (env_args nil (ub ++ nsA ++ vA1)))
          by (intros R HR; exact (gargs_env_rel _ _ _ _ _ _ HR HWA0 LWA K1A)).
        assert (RenvB : forall R, EF cargs_ctx p D Mv gB1 ++ im_params D Mv ≈ cargs_ctx p D Mv gB1 ++ im_params D Mv ∈ per_ctx_env ↘ R ->
                          R (env_args nil (u0 ++ nsB ++ vB1)) (env_args nil (u0 ++ nsB ++ vB1)))
          by (intros R HR; exact (gargs_env_rel _ _ _ _ _ _ HR HWB0 LWB K3)).
        pose proof (cargs_ctx_snoc qc D' Mi' gA1 gA) as ECc; pose proof (cargs_ctx_snoc p D Mv gB1 gB) as ECg.
        cbn [cargs_ctx_aux List.app] in ECc, ECg.
        assert (LAB : List.length vA1 = List.length gB1) by lia.
        assert (LBA : List.length vB1 = List.length gA1) by lia.
        (** The group's type at a recursive position, at its side. *)
        assert (Hgrec : forall t, gB = ca_rec t -> exists (iG : nat) RGG gB0,
                   ⟦ ptyp_ty p D (im_nn Mv) (cargs_pat gB1) t ⟧ env_args nil (u0 ++ nsB ++ vB1) ↘ gB0 /\
                   DF gB0 ≈ gB0 ∈ per_univ_elem iG ↘ RGG).
        { intros t ->.
          destruct (vg_cargs_sem_all p D Hg Hcv v Mv c gsB HMv HconB (gB1 ++ ca_rec t :: nil) gB2 HeB'') as [HWB1 _].
          rewrite ECg in HWB1; destruct (rel_ctx_wf_ass_inv HWB1) as [iG HGv].
          pose proof (rel_ctx_wf_tail HWB1) as HWB.
          destruct (rel_ctx_wf_per_ctx_env HWB) as [RWB HRWB].
          destruct (rel_exp_of_typ_inversion_simple_at HRWB HGv _ _ (gargs_env_rel _ _ _ _ _ _ HRWB HWB LWB K3))
            as (gB0 & gB0' & EgB & EgB' & [RGG HGG]).
          assert (gB0' = gB0) as -> by (eapply functional_eval_exp; eassumption).
          exists iG, RGG, gB0; split; [ exact EgB | exact HGG ]. }
        (** At a recursive position of the group: its variable and the
            relation of its type, the recursive argument's. *)
        assert (Hglink : forall t, gB = ca_rec t ->
                   exists aB (iG : nat) RGG gB0,
                     ⟦shty t of p u0 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ nsB ++ nonrec_arg_vals gB1 vB1) ↘ aB /\
                     ⟦ ptyp_ty p D (im_nn Mv) (cargs_pat gB1) t ⟧ env_args nil (u0 ++ nsB ++ vB1) ↘ gB0 /\
                     DF gB0 ≈ gB0 ∈ per_univ_elem iG ↘ RGG /\
                     (exists (i : nat) R, DF gB0 ≈ aB ∈ per_univ_elem i ↘ R) /\
                     (RGG <~> rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsB ++ nonrec_arg_vals gB1 vB1)
                                (nsB ++ nonrec_arg_vals gB1 vB1) t)).
        { intros t ->.
          destruct (Hgrec t eq_refl) as (iG & RGG & gB0 & EgB & HGG).
          destruct (shty_link p D Hg Hcv v Mv c gsB HMv HconB HΨB gB1 t gB2 HeB u0 nsB vB1 Hu LnB LB Hgu HnsB K6 RenvB
                      (view_end_type VP HP p D HPD u0 Hgu Hu (ptyp_mem t)) (List.length (ptyp_doms t)) 0 nil gB0 iG RGG
                      eq_refl (tele_prefix_rel_nil _) ltac:(constructor) ltac:(rewrite List.app_nil_r; exact EgB) HGG)
            as (aB & EaB & [RB HgaB]).
          rewrite List.app_nil_r in EaB; cbn [ptyp_skip] in EaB.
          pose proof (view_end_rel_of_agreement p D Hg Hcv u0 u0 Hgu Hu (ptyp_mem t)
                        (view_agreement_canonical_all VP p D HP HPD u0 u0 Hgu Hu (ptyp_mem t))) as Hendr.
          pose proof (shape_char p D Hg Hcv v Mv c gsB HMv HconB HΨB gB1 t gB2 HeB u0 nsB vB1 Hu LnB LB Hgu HnsB K6 RenvB Hendr
                        (rview_end_rel_all VP p D HP HPD u0 u0 Hgu Hu (ptyp_mem t)) (List.length (ptyp_doms t)) 0 nil gB0 iG RGG eq_refl (tele_prefix_rel_nil _) ltac:(constructor)
                        ltac:(rewrite List.app_nil_r; exact EgB) HGG) as ERG.
          rewrite List.app_nil_r in ERG; cbn [ptyp_skip] in ERG.
          exists aB, iG, RGG, gB0; split; [ exact EaB | split; [ exact EgB | split; [ exact HGG | split; [ exists iG, RB; exact HgaB | exact ERG ] ] ] ]. }
        destruct gA as [A' | t'], gB as [A | t]; cbn [cargs_corr] in Hco; try contradiction.
        + (** Non-recursive in both. *)
          destruct (vg_arg_types qc D' HgQ HcvQ i' Mi' c gsA gA1 A' gA2 ub nsA vA1 HMi' HconA HeA Hlb ltac:(lia) LA K1A)
            as (iA & RA & cA & aA & EcA & EaA & HcaA).
          destruct (vg_arg_types p D Hg Hcv v Mv c gsB gB1 A gB2 u0 nsB vB1 HMv HconB HeB Hu LnB LB K3)
            as (iB & RB & gB0 & aB & EgB & EaB & HgaB).
          destruct (cross_position gA1 (ca_arg A') gA2 gB1 (ca_arg A) gB2 vA1 vB1 _ _ aA aB s HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg
                      ltac:(exists iA, RA, cA; split; [ exact EcA | exact HcaA ])
                      ltac:(exists iB, RB, gB0; split; [ exact EgB | exact HgaB ]))
            as [K1' K2' K3' Hrel [ix [Rx Hx]]].
          (** The non-recursive relations at the position. *)
          assert (HnthB : List.nth_error (cargs_nonrec gsB) (List.length (cargs_nonrec gB1)) = Some A)
            by (rewrite HeB, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
          assert (HnthA : List.nth_error (cargs_nonrec gsA) (List.length (cargs_nonrec gA1)) = Some A')
            by (rewrite HeA, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
          destruct (vg_arg_head p D Hg Hcv v Mv c gsB gB1 A gB2 u0 nsB vB1 HMv HconB HeB Hu LnB LB K3)
            as (i2 & R2 & a2 & Ea2 & HR2 & E2).
          assert (a2 = gB0) as -> by (eapply functional_eval_exp; eassumption).
          pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ Hx) Hx) as Hbb.
          pose proof (per_univ_trans _ _ _ _ _ _ Hx (per_univ_sym _ _ _ _ Hx)) as Haa.
          assert (HarB : ar v nsB c (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vB1) (⇑! aA s) (⇑! aB s))
            by (apply E2, (per_head_left Ea2 Ea2 HR2); exact Hrel).
          assert (HarA : ar v nsA c (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vA1) (⇑! aA s) (⇑! aB s))
            by (apply (CaI v Mv nsA nsB c gsB _ A _ _ HMv Hns HconB HnthB K4); exact HarB).
          assert (HbbB : ar v nsB c (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vB1) (⇑! aB s) (⇑! aB s)).
          { apply E2, (rel_link _ _ _ _ _ _ _ _ _ _ HR2 HgaB Hbb); exact (fresh_var_rel _ _ _ _ s Hbb). }
          assert (HaaA : canon_args_rel D' ub i' nsA c (List.length (cargs_nonrec gA1)) (nonrec_arg_vals gA1 vA1) (⇑! aA s) (⇑! aA s)).
          { unfold canon_args_rel; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HMi' HconA HnthA).
            apply (per_head_left EaA EaA Haa); exact (fresh_var_rel _ _ _ _ s Haa). }
          destruct (IH gB2 (gA1 ++ ca_arg A' :: nil) (gB1 ++ ca_arg A :: nil) (vA1 ++ ⇑! aA s :: nil) (vB1 ++ ⇑! aB s :: nil)
                      HeA'' HeB'' Hc1' ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                      K1' K2' K3') with (s := S s) as [vA2' vB2' FA' FB' IHc IHf IHt].
          * rewrite cargs_nonrec_app, !nonrec_arg_vals_app by lia; cbn [cargs_nonrec nonrec_arg_vals List.app].
            rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r.
            apply tele_prefix_rel_snoc; [ exact K4 | exact HarA ].
          * rewrite cargs_nonrec_app, !nonrec_arg_vals_app by lia; cbn [cargs_nonrec nonrec_arg_vals List.app].
            rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r.
            apply tele_prefix_rel_snoc; [ exact K5 | exact HaaA ].
          * rewrite cargs_nonrec_app, !nonrec_arg_vals_app by lia; cbn [cargs_nonrec nonrec_arg_vals List.app].
            rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r.
            apply tele_prefix_rel_snoc; [ exact K6 | exact HbbB ].
          * rewrite (nonrec_arg_vals_app gA1 _ vA1 _ LA) in FA'; cbn [nonrec_arg_vals] in FA'.
            replace (ub ++ nsA ++ nonrec_arg_vals gA1 vA1 ++ ⇑! aA s :: nil)
              with ((ub ++ nsA ++ nonrec_arg_vals gA1 vA1) ++ ⇑! aA s :: nil) in FA' by (rewrite <- !List.app_assoc; reflexivity).
            rewrite env_args_snoc in FA'.
            rewrite (nonrec_arg_vals_app gB1 _ vB1 _ LB) in FB'; cbn [nonrec_arg_vals] in FB'.
            replace (u0 ++ nsB ++ nonrec_arg_vals gB1 vB1 ++ ⇑! aB s :: nil)
              with ((u0 ++ nsB ++ nonrec_arg_vals gB1 vB1) ++ ⇑! aB s :: nil) in FB' by (rewrite <- !List.app_assoc; reflexivity).
            rewrite env_args_snoc in FB'.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB) in IHc;
              cbn [nonrec_arg_vals] in IHc.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB) in IHf, IHt; cbn [nonrec_arg_vals] in IHf, IHt.
            rewrite cargs_nonrec_app, List.length_app in IHf; cbn [cargs_nonrec List.length] in IHf; rewrite Nat.add_1_r in IHf.
            apply (mk_cross_fresh_tail _ _ _ _ _ _ _ (⇑! aA s :: vA2') (⇑! aB s :: vB2')).
            -- econstructor; [ exact EaA | exact FA' ].
            -- econstructor; [ exact EaB | exact FB' ].
            -- apply con_args_arg; rewrite <- !List.app_assoc; exact IHc.
            -- cbn [nonrec_arg_vals tele_rel_from]; split; [ exact HarA | exact IHf ].
            -- apply cross_tops_arg.
               rewrite (nonrec_arg_vals_app gA1 _ vA1 _ LA), (nonrec_arg_vals_app gB1 _ vB1 _ LB) in IHt;
                 cbn [nonrec_arg_vals] in IHt; rewrite <- !List.app_assoc; exact IHt.
        + (** Non-recursive in the container, recursive in the group. *)
          destruct (vg_arg_types qc D' HgQ HcvQ i' Mi' c gsA gA1 A' gA2 ub nsA vA1 HMi' HconA HeA Hlb ltac:(lia) LA K1A)
            as (iA & RA & cA & aA & EcA & EaA & HcaA).
          destruct (Hglink t eq_refl) as (aB & iG & RGG & gB0 & EaB & EgB & HGG & (iB & RB & HgaB) & ERG).
          destruct (cross_position gA1 (ca_arg A') gA2 gB1 (ca_rec t) gB2 vA1 vB1 _ _ aA aB s HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg
                      ltac:(exists iA, RA, cA; split; [ exact EcA | exact HcaA ])
                      ltac:(exists iB, RB, gB0; split; [ exact EgB | exact HgaB ]))
            as [K1' K2' K3' Hrel [ix [Rx Hx]]].
          assert (Hrr : rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsB ++ nonrec_arg_vals gB1 vB1)
                          (nsB ++ nonrec_arg_vals gB1 vB1) t (⇑! aA s) (⇑! aB s))
            by (apply ERG, (per_head_left EgB EgB HGG); exact Hrel).
          pose proof (cross_rec_move gB1 t gB2 vA1 vB1 _ _ HeB K4 K6 Hrr) as HrrA.
          assert (HnthA : List.nth_error (cargs_nonrec gsA) (List.length (cargs_nonrec gA1)) = Some A')
            by (rewrite HeA, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
          pose proof (per_univ_trans _ _ _ _ _ _ Hx (per_univ_sym _ _ _ _ Hx)) as Haa.
          assert (HaaA : canon_args_rel D' ub i' nsA c (List.length (cargs_nonrec gA1)) (nonrec_arg_vals gA1 vA1) (⇑! aA s) (⇑! aA s)).
          { unfold canon_args_rel; rewrite (nth_atyp_eq _ _ _ _ _ _ _ HMi' HconA HnthA).
            apply (per_head_left EaA EaA Haa); exact (fresh_var_rel _ _ _ _ s Haa). }
          destruct (IH gB2 (gA1 ++ ca_arg A' :: nil) (gB1 ++ ca_rec t :: nil) (vA1 ++ ⇑! aA s :: nil) (vB1 ++ ⇑! aB s :: nil)
                      HeA'' HeB'' Hc1' ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                      K1' K2' K3') with (s := S s) as [vA2' vB2' FA' FB' IHc IHf IHt].
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB).
            cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K4.
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gA1 _ vA1 _ LA); cbn [cargs_nonrec nonrec_arg_vals List.app].
            rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r.
            apply tele_prefix_rel_snoc; [ exact K5 | exact HaaA ].
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gB1 _ vB1 _ LB); cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K6.
          * rewrite (nonrec_arg_vals_app gA1 _ vA1 _ LA) in FA'; cbn [nonrec_arg_vals] in FA'.
            replace (ub ++ nsA ++ nonrec_arg_vals gA1 vA1 ++ ⇑! aA s :: nil)
              with ((ub ++ nsA ++ nonrec_arg_vals gA1 vA1) ++ ⇑! aA s :: nil) in FA' by (rewrite <- !List.app_assoc; reflexivity).
            rewrite env_args_snoc in FA'.
            rewrite (nonrec_arg_vals_app gB1 _ vB1 _ LB) in FB'; cbn [nonrec_arg_vals] in FB'; rewrite List.app_nil_r in FB'.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB) in IHc;
              cbn [nonrec_arg_vals] in IHc; rewrite !List.app_nil_r in IHc.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB) in IHf, IHt; cbn [nonrec_arg_vals] in IHf, IHt;
              rewrite List.app_nil_r in IHf, IHt.
            rewrite cargs_nonrec_app in IHf; cbn [cargs_nonrec] in IHf; rewrite List.app_nil_r in IHf.
            apply (mk_cross_fresh_tail _ _ _ _ _ _ _ (⇑! aA s :: vA2') (⇑! aB s :: vB2')).
            -- econstructor; [ exact EaA | exact FA' ].
            -- econstructor; [ exact EaB | exact FB' ].
            -- eapply con_args_rec; [ exact HrrA | exact IHc ].
            -- cbn [nonrec_arg_vals]; exact IHf.
            -- apply cross_tops_nest.
               rewrite ?(nonrec_arg_vals_app gA1 _ vA1 _ LA), ?(nonrec_arg_vals_app gB1 _ vB1 _ LB) in IHt;
                 cbn [nonrec_arg_vals] in IHt; rewrite ?List.app_nil_r in IHt; rewrite <- ?List.app_assoc; exact IHt.
        + (** Recursive in both. *)
          destruct Hco as (Hmt & Hdp & Hco).
          (** The container's type at its side, against its variable's. *)
          destruct (vg_cargs_sem_all qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA (gA1 ++ ca_rec t' :: nil) gA2 HeA'') as [HWA1 _].
          rewrite ECc in HWA1; destruct (rel_ctx_wf_ass_inv HWA1) as [iC HCv].
          pose proof (rel_ctx_wf_tail HWA1) as HWA.
          destruct (rel_ctx_wf_per_ctx_env HWA) as [RWA HRWA].
          destruct (rel_exp_of_typ_inversion_simple_at HRWA HCv _ _ (gargs_env_rel _ _ _ _ _ _ HRWA HWA LWA K1A))
            as (cA & cA' & EcA & EcA' & [RCC HCC]).
          assert (cA' = cA) as -> by (eapply functional_eval_exp; eassumption).
          destruct (shty_link qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA HΨA gA1 t' gA2 HeA ub nsA vA1 Hlb ltac:(lia) LA Hubub HnsA K5 RenvA
                      (view_end_type VP HP qc D' HVQ ub Hubub Hlb (ptyp_mem t')) (List.length (ptyp_doms t')) 0 nil cA iC RCC
                      eq_refl (tele_prefix_rel_nil _) ltac:(constructor) ltac:(rewrite List.app_nil_r; exact EcA) HCC)
            as (aA & EaA & [RA HcaA]).
          rewrite List.app_nil_r in EaA; cbn [ptyp_skip] in EaA.
          destruct (Hglink t eq_refl) as (aB & iG & RGG & gB0 & EaB & EgB & HGG & (iB & RB & HgaB) & ERG).
          destruct (cross_position gA1 (ca_rec t') gA2 gB1 (ca_rec t) gB2 vA1 vB1 _ _ aA aB s HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg
                      ltac:(exists iC, RA, cA; split; [ exact EcA | exact HcaA ])
                      ltac:(exists iB, RB, gB0; split; [ exact EgB | exact HgaB ]))
            as [K1' K2' K3' Hrel [ix [Rx Hx]]].
          assert (Hrr : rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsB ++ nonrec_arg_vals gB1 vB1)
                          (nsB ++ nonrec_arg_vals gB1 vB1) t (⇑! aA s) (⇑! aB s))
            by (apply ERG, (per_head_left EgB EgB HGG); exact Hrel).
          pose proof (cross_rec_move gB1 t gB2 vA1 vB1 _ _ HeB K4 K6 Hrr) as HrrA.
          (** The domains of the two types read alike. *)
          pose proof (cross_doms_fresh p D Hg u0 Hgu Hu v Mv c gsB gB1 t gB2 nsA nsB (nonrec_arg_vals gB1 vA1)
                        (nonrec_arg_vals gB1 vB1) HMv HconB HeB Hns K4 qc ub (List.length (ptyp_doms t)) 0 t'
                        (nsA ++ nonrec_arg_vals gA1 vA1) nil nil aA aB ix Rx
                        eq_refl ltac:(unfold ptyp_depth in *; lia) (tele_prefix_rel_nil _) EaA
                        ltac:(rewrite List.app_nil_r; exact EaB) Hx) as Hts.
          cbn [ptyp_skip] in Hts; rewrite !List.app_nil_r in Hts.
          (** The container's variable at its own relation. *)
          pose proof (shape_char qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA HΨA gA1 t' gA2 HeA ub nsA vA1 Hlb ltac:(lia) LA Hubub HnsA K5
                        RenvA (view_end_rel_all VP qc D' HP HVQ ub ub Hubub Hlb (ptyp_mem t'))
                        (rview_end_rel_all VP qc D' HP HVQ ub ub Hubub Hlb (ptyp_mem t')) (List.length (ptyp_doms t')) 0 nil
                        cA iC RCC eq_refl (tele_prefix_rel_nil _) ltac:(constructor) ltac:(rewrite List.app_nil_r; exact EcA) HCC)
            as ERC.
          rewrite !List.app_nil_r in ERC; cbn [ptyp_skip] in ERC.
          assert (HrrQ : rec_arg_rel qc D' (okr_at D' ub (canon_nparams_rel D' ub)) (canon_nparams_rel D' ub) (canon_args_rel D' ub)
                           (canon_doms_rel ub) i' ub ub (nsA ++ nonrec_arg_vals gA1 vA1) (nsA ++ nonrec_arg_vals gA1 vA1) t'
                           (⇑! aA s) (⇑! aA s)).
          { apply ERC.
            pose proof (per_univ_trans _ _ _ _ _ _ (per_univ_sym _ _ _ _ HcaA) HcaA) as Haa.
            apply (rel_link _ _ _ _ _ _ _ _ _ _ HCC HcaA Haa); exact (fresh_var_rel _ _ _ _ s Haa). }
          destruct (IH gB2 (gA1 ++ ca_rec t' :: nil) (gB1 ++ ca_rec t :: nil) (vA1 ++ ⇑! aA s :: nil) (vB1 ++ ⇑! aB s :: nil)
                      HeA'' HeB'' Hc1' ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                      K1' K2' K3') with (s := S s) as [vA2' vB2' FA' FB' IHc IHf IHt].
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB).
            cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K4.
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gA1 _ vA1 _ LA); cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K5.
          * rewrite cargs_nonrec_app, (nonrec_arg_vals_app gB1 _ vB1 _ LB); cbn [cargs_nonrec nonrec_arg_vals]; rewrite !List.app_nil_r; exact K6.
          * rewrite (nonrec_arg_vals_app gA1 _ vA1 _ LA) in FA'; cbn [nonrec_arg_vals] in FA'; rewrite List.app_nil_r in FA'.
            rewrite (nonrec_arg_vals_app gB1 _ vB1 _ LB) in FB'; cbn [nonrec_arg_vals] in FB'; rewrite List.app_nil_r in FB'.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB), (nonrec_arg_vals_app gB1 _ vB1 _ LB) in IHc;
              cbn [nonrec_arg_vals] in IHc; rewrite !List.app_nil_r in IHc.
            rewrite (nonrec_arg_vals_app gB1 _ vA1 _ LAB) in IHf, IHt; cbn [nonrec_arg_vals] in IHf, IHt;
              rewrite List.app_nil_r in IHf, IHt.
            rewrite cargs_nonrec_app in IHf; cbn [cargs_nonrec] in IHf; rewrite List.app_nil_r in IHf.
            apply (mk_cross_fresh_tail _ _ _ _ _ _ _ (⇑! aA s :: vA2') (⇑! aB s :: vB2')).
            -- econstructor; [ exact EaA | exact FA' ].
            -- econstructor; [ exact EaB | exact FB' ].
            -- eapply con_args_rec; [ exact HrrA | exact IHc ].
            -- cbn [nonrec_arg_vals]; exact IHf.
            -- apply cross_tops_rec; [ eexists _, _; reflexivity | eexists _, _; reflexivity | exact HrrQ | exact Hts |].
               rewrite (nonrec_arg_vals_app gA1 _ vA1 _ LA), (nonrec_arg_vals_app gB1 _ vB1 _ LB) in IHt;
                 cbn [nonrec_arg_vals] in IHt; rewrite !List.app_nil_r in IHt; exact IHt.
    Qed.

    (** The rest of the arguments after the positions [gA1] and [gB1], at
        given values: [xsA] the container's (and the group read's left
        side's), [xsB] the group's right side's, related at the group's
        relations and the container's at its own; at each argument
        recursive in both, neutrals whose shapes' domains read alike. *)
    Lemma cross_vals_cargs : forall gA2 gB2 gA1 gB1 vA1 vB1 xsA xsB, gsA = gA1 ++ gA2 -> gsB = gB1 ++ gB2 ->
        cargs_corr vm gA1 gB1 -> List.length vA1 = List.length gA1 -> List.length vB1 = List.length gB1 ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (ub ++ nsA ++ vA1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (cups ++ nsB ++ vB1) (cups ++ nsB ++ vB1) ->
        per_gargs (List.rev (cargs_ctx p D Mv gB1 ++ im_params D Mv)) nil nil (u0 ++ nsB ++ vB1) (u0 ++ nsB ++ vB1) ->
        tele_prefix_rel (ar v nsA c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vA1) (nonrec_arg_vals gB1 vB1) ->
        tele_prefix_rel (canon_args_rel D' ub i' nsA c) (List.length (cargs_nonrec gA1))
          (nonrec_arg_vals gA1 vA1) (nonrec_arg_vals gA1 vA1) ->
        tele_prefix_rel (ar v nsB c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vB1) (nonrec_arg_vals gB1 vB1) ->
        con_args_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsA ++ nonrec_arg_vals gB1 vA1) (nsB ++ nonrec_arg_vals gB1 vB1)
          gB2 xsA xsB ->
        tele_rel_from (ar v nsA c) (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vA1)
          (nonrec_arg_vals gB2 xsA) (nonrec_arg_vals gB2 xsB) ->
        con_args_rel qc D' (okr_at D' ub (canon_nparams_rel D' ub)) (canon_nparams_rel D' ub) (canon_args_rel D' ub)
          (canon_doms_rel ub) i' ub ub (nsA ++ nonrec_arg_vals gA1 vA1) (nsA ++ nonrec_arg_vals gA1 vA1) gA2 xsA xsA ->
        tele_rel_from (canon_args_rel D' ub i' nsA c) (List.length (cargs_nonrec gA1)) (nonrec_arg_vals gA1 vA1)
          (nonrec_arg_vals gA2 xsA) (nonrec_arg_vals gA2 xsA) ->
        List.Forall is_neut xsA -> List.Forall is_neut xsB ->
        cross_tops qc D' ub u0 dr i' v (nsA ++ nonrec_arg_vals gB1 vA1) (nsA ++ nonrec_arg_vals gA1 vA1)
          (nsB ++ nonrec_arg_vals gB1 vB1) gA2 gB2 xsA xsB.
    Proof.
      induction gA2 as [| gA gA2 IH];
        intros [| gB gB2] gA1 gB1 vA1 vB1 xsA xsB HeA HeB Hc1 LA LB K1 K2 K3 K4 K5 K6 Hga Hnf Hca Hnq HnA HnB.
      - inversion Hga; subst; constructor.
      - exfalso; pose proof (cargs_corr_len _ _ _ Hcorr) as H; rewrite HeA, HeB, !List.length_app in H.
        pose proof (cargs_corr_len _ _ _ Hc1); cbn in H; lia.
      - exfalso; pose proof (cargs_corr_len _ _ _ Hcorr) as H; rewrite HeA, HeB, !List.length_app in H.
        pose proof (cargs_corr_len _ _ _ Hc1); cbn in H; lia.
      - assert (Hl1 : List.length gA1 = List.length gB1) by exact (cargs_corr_len _ _ _ Hc1).
        assert (Hco : cargs_corr vm (gA :: gA2) (gB :: gB2))
          by (rewrite HeA, HeB in Hcorr; exact (proj2 (cargs_corr_split _ _ _ _ _ Hcorr Hl1))).
        pose proof Hcp as [Hns HpA HpC HpG].
        pose proof Hns as Hns0; rewrite tele_rel_iff in Hns0; destruct Hns0 as (LnA & LnB & _).
        rewrite List.length_rev, length_im_nparams in LnA, LnB.
        pose proof (view_nn p D Hg m Mm qc k' Is vm D' HMm Hh Hq i' Mi' v Mv HMi' Hv HMv) as Hnn.
        pose proof (length_cups p D Hg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups) as Hlc.
        assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
        pose proof (uparams_refl_l D' (valid_group_valid _ _ HgQ) (valid_group_closed _ _ HgQ) _ _ Hub) as Hubub.
        destruct (vg_canon p D Hg u0 Hgu Hu) as [CnP CnI CaP CaI CdP CdI].
        pose proof (valid_group_ass _ _ Hg) as Hass.
        pose proof (nparams_rel_refl_r p D u0 _ _ _ Hass CnP CnI CaP CaI CdP CdI _ _ HMv _ _ Hns) as HnsB.
        assert (HeA'' : gsA = (gA1 ++ gA :: nil) ++ gA2) by (rewrite <- List.app_assoc; exact HeA).
        assert (HeB'' : gsB = (gB1 ++ gB :: nil) ++ gB2) by (rewrite <- List.app_assoc; exact HeB).
        assert (Hc1' : cargs_corr vm (gA1 ++ gA :: nil) (gB1 ++ gB :: nil)).
        { apply cargs_corr_app; [ exact Hc1 |].
          destruct gA, gB; cbn in Hco |- *; try contradiction; try exact I; tauto. }
        (** The container's telescope at its side, and the group's at its. *)
        destruct (vg_cargs_sem_all qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA gA1 (gA :: gA2) HeA) as [HWA0 _].
        destruct (vg_cargs_sem_all p D Hg Hcv v Mv c gsB HMv HconB gB1 (gB :: gB2) HeB) as [HWB0 _].
        destruct (vg_cargs_sem_all qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA gsA nil ltac:(rewrite List.app_nil_r; reflexivity))
          as [HΨA _].
        destruct (vg_cargs_sem_all p D Hg Hcv v Mv c gsB HMv HconB gsB nil ltac:(rewrite List.app_nil_r; reflexivity))
          as [HΨB _].
        assert (LWA : List.length (ub ++ nsA ++ vA1) = List.length (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi'))
          by (rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
        assert (LWB : List.length (u0 ++ nsB ++ vB1) = List.length (cargs_ctx p D Mv gB1 ++ im_params D Mv))
          by (rewrite !List.length_app, length_cargs_ctx, length_im_params; unfold im_np, ind_nu in *; lia).
        assert (K1A : per_gargs (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) nil nil (ub ++ nsA ++ vA1) (ub ++ nsA ++ vA1)).
        { assert (HW' : ⊨ List.rev (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')) ++ ⋅)
            by (rewrite List.rev_involutive, List.app_nil_r; exact HWA0).
          assert (Hta : tele_ass (List.rev (cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi')))
            by (apply List.Forall_rev, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (member_params_ass D' (valid_group_closed _ _ HgQ) i' Mi' HMi') ]).
          exact (per_gargs_refl_l _ _ _ per_ctx_env_nil_true HW' Hta _ _ _ _ I K1). }
        assert (RenvA : forall R, EF cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi' ≈ cargs_ctx qc D' Mi' gA1 ++ im_params D' Mi' ∈ per_ctx_env ↘ R ->
                          R (env_args nil (ub ++ nsA ++ vA1)) (env_args nil (ub ++ nsA ++ vA1)))
          by (intros R HR; exact (gargs_env_rel _ _ _ _ _ _ HR HWA0 LWA K1A)).
        assert (RenvB : forall R, EF cargs_ctx p D Mv gB1 ++ im_params D Mv ≈ cargs_ctx p D Mv gB1 ++ im_params D Mv ∈ per_ctx_env ↘ R ->
                          R (env_args nil (u0 ++ nsB ++ vB1)) (env_args nil (u0 ++ nsB ++ vB1)))
          by (intros R HR; exact (gargs_env_rel _ _ _ _ _ _ HR HWB0 LWB K3)).
        pose proof (cargs_ctx_snoc qc D' Mi' gA1 gA) as ECc; pose proof (cargs_ctx_snoc p D Mv gB1 gB) as ECg.
        cbn [cargs_ctx_aux List.app] in ECc, ECg.
        assert (LAB : List.length vA1 = List.length gB1) by lia.
        assert (LBA : List.length vB1 = List.length gA1) by lia.
        (** The group's type at a recursive position, at its side. *)
        assert (Hgrec : forall t, gB = ca_rec t -> exists (iG : nat) RGG gB0,
                   ⟦ ptyp_ty p D (im_nn Mv) (cargs_pat gB1) t ⟧ env_args nil (u0 ++ nsB ++ vB1) ↘ gB0 /\
                   DF gB0 ≈ gB0 ∈ per_univ_elem iG ↘ RGG).
        { intros t ->.
          destruct (vg_cargs_sem_all p D Hg Hcv v Mv c gsB HMv HconB (gB1 ++ ca_rec t :: nil) gB2 HeB'') as [HWB1 _].
          rewrite ECg in HWB1; destruct (rel_ctx_wf_ass_inv HWB1) as [iG HGv].
          pose proof (rel_ctx_wf_tail HWB1) as HWB.
          destruct (rel_ctx_wf_per_ctx_env HWB) as [RWB HRWB].
          destruct (rel_exp_of_typ_inversion_simple_at HRWB HGv _ _ (gargs_env_rel _ _ _ _ _ _ HRWB HWB LWB K3))
            as (gB0 & gB0' & EgB & EgB' & [RGG HGG]).
          assert (gB0' = gB0) as -> by (eapply functional_eval_exp; eassumption).
          exists iG, RGG, gB0; split; [ exact EgB | exact HGG ]. }
        (** At a recursive position of the group: its variable and the
            relation of its type, the recursive argument's. *)
        assert (Hglink : forall t, gB = ca_rec t ->
                   exists aB (iG : nat) RGG gB0,
                     ⟦shty t of p u0 ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ nsB ++ nonrec_arg_vals gB1 vB1) ↘ aB /\
                     ⟦ ptyp_ty p D (im_nn Mv) (cargs_pat gB1) t ⟧ env_args nil (u0 ++ nsB ++ vB1) ↘ gB0 /\
                     DF gB0 ≈ gB0 ∈ per_univ_elem iG ↘ RGG /\
                     (exists (i : nat) R, DF gB0 ≈ aB ∈ per_univ_elem i ↘ R) /\
                     (RGG <~> rec_arg_rel p D (okr_at D u0 nr) nr ar dr v u0 u0 (nsB ++ nonrec_arg_vals gB1 vB1)
                                (nsB ++ nonrec_arg_vals gB1 vB1) t)).
        { intros t ->.
          destruct (Hgrec t eq_refl) as (iG & RGG & gB0 & EgB & HGG).
          destruct (shty_link p D Hg Hcv v Mv c gsB HMv HconB HΨB gB1 t gB2 HeB u0 nsB vB1 Hu LnB LB Hgu HnsB K6 RenvB
                      (view_end_type VP HP p D HPD u0 Hgu Hu (ptyp_mem t)) (List.length (ptyp_doms t)) 0 nil gB0 iG RGG
                      eq_refl (tele_prefix_rel_nil _) ltac:(constructor) ltac:(rewrite List.app_nil_r; exact EgB) HGG)
            as (aB & EaB & [RB HgaB]).
          rewrite List.app_nil_r in EaB; cbn [ptyp_skip] in EaB.
          pose proof (view_end_rel_of_agreement p D Hg Hcv u0 u0 Hgu Hu (ptyp_mem t)
                        (view_agreement_canonical_all VP p D HP HPD u0 u0 Hgu Hu (ptyp_mem t))) as Hendr.
          pose proof (shape_char p D Hg Hcv v Mv c gsB HMv HconB HΨB gB1 t gB2 HeB u0 nsB vB1 Hu LnB LB Hgu HnsB K6 RenvB Hendr
                        (rview_end_rel_all VP p D HP HPD u0 u0 Hgu Hu (ptyp_mem t)) (List.length (ptyp_doms t)) 0 nil gB0 iG RGG eq_refl (tele_prefix_rel_nil _) ltac:(constructor)
                        ltac:(rewrite List.app_nil_r; exact EgB) HGG) as ERG.
          rewrite List.app_nil_r in ERG; cbn [ptyp_skip] in ERG.
          exists aB, iG, RGG, gB0; split; [ exact EaB | split; [ exact EgB | split; [ exact HGG | split; [ exists iG, RB; exact HgaB | exact ERG ] ] ] ]. }
        destruct gA as [A' | t'], gB as [A | t]; cbn [cargs_corr] in Hco; try contradiction.
        + (** Non-recursive in both. *)
          destruct xsA as [| x xsA], xsB as [| x' xsB]; try (inversion Hga; fail).
          pose proof (con_args_arg_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hga) as Hga0.
          pose proof (con_args_arg_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca) as Hca0.
          cbn [nonrec_arg_vals tele_rel_from] in Hnf, Hnq.
          destruct Hnf as [HarA Hnf0]; destruct Hnq as [HaaA Hnq0].
          apply List.Forall_cons_iff in HnA as [HnA0 HnA1]; apply List.Forall_cons_iff in HnB as [HnB0 HnB1].
          assert (HnthB : List.nth_error (cargs_nonrec gsB) (List.length (cargs_nonrec gB1)) = Some A)
            by (rewrite HeB, cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
          destruct (vg_arg_head p D Hg Hcv v Mv c gsB gB1 A gB2 u0 nsB vB1 HMv HconB HeB Hu LnB LB K3)
            as (i2 & R2 & a2 & Ea2 & HR2 & E2).
          assert (HarB : ar v nsB c (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vB1) x x')
            by (apply (CaI v Mv nsA nsB c gsB _ A _ _ HMv Hns HconB HnthB K4); exact HarA).
          assert (Hxx : R2 x x') by (apply E2; exact HarB).
          assert (HP2 : PER R2) by (eapply per_elem_PER; exact HR2).
          assert (Hx'x' : R2 x' x') by (etransitivity; [ symmetry; exact Hxx | exact Hxx ]).
          assert (HbbB : ar v nsB c (List.length (cargs_nonrec gB1)) (nonrec_arg_vals gB1 vB1) x' x') by (apply E2; exact Hx'x').
          destruct (cross_position_vals gA1 (ca_arg A') gA2 gB1 (ca_arg A) gB2 vA1 vB1 _ _ x x' HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg
                      ltac:(exists i2, R2, a2; split; [ exact Ea2 | split; [ exact HR2 | exact Hxx ] ]))
            as [K1' K2' K3' _].
          apply cross_tops_arg.
          pose proof (IH gB2 (gA1 ++ ca_arg A' :: nil) (gB1 ++ ca_arg A :: nil) (vA1 ++ x :: nil) (vB1 ++ x' :: nil) xsA xsB
                        HeA'' HeB'' Hc1' ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)) as IH'.
          rewrite !cargs_nonrec_app, !nonrec_arg_vals_app in IH' by lia.
          cbn [cargs_nonrec nonrec_arg_vals List.app List.length] in IH'.
          rewrite !List.length_app in IH'; cbn [List.length] in IH'; rewrite !Nat.add_1_r in IH'.
          rewrite <- !List.app_assoc; rewrite <- !List.app_assoc in Hga0; rewrite <- !List.app_assoc in Hca0.
          apply IH'; try assumption.
          all: try (apply tele_prefix_rel_snoc; assumption).
          all: rewrite List.app_assoc; assumption.
        + (** Non-recursive in the container, recursive in the group. *)
          destruct xsA as [| x xsA], xsB as [| x' xsB]; try (inversion Hga; fail).
          destruct (con_args_rec_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hga) as [Hrr Hga0].
          pose proof (con_args_arg_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca) as Hca0.
          cbn [nonrec_arg_vals tele_rel_from] in Hnf, Hnq.
          destruct Hnq as [HaaA Hnq0].
          apply List.Forall_cons_iff in HnA as [HnA0 HnA1]; apply List.Forall_cons_iff in HnB as [HnB0 HnB1].
          destruct (Hglink t eq_refl) as (aB & iG & RGG & gB0 & EaB & EgB & HGG & _ & ERG).
          pose proof (cross_rec_move_back gB1 t gB2 vA1 vB1 x x' HeB K4 K6 Hrr) as Hrr'.
          assert (Hxx : RGG x x') by (apply ERG; exact Hrr').
          destruct (cross_position_vals gA1 (ca_arg A') gA2 gB1 (ca_rec t) gB2 vA1 vB1 _ _ x x' HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg
                      ltac:(exists iG, RGG, gB0; split; [ exact EgB | split; [ exact HGG | exact Hxx ] ]))
            as [K1' K2' K3' _].
          apply cross_tops_nest.
          pose proof (IH gB2 (gA1 ++ ca_arg A' :: nil) (gB1 ++ ca_rec t :: nil) (vA1 ++ x :: nil) (vB1 ++ x' :: nil) xsA xsB
                        HeA'' HeB'' Hc1' ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)) as IH'.
          rewrite !cargs_nonrec_app, !nonrec_arg_vals_app in IH' by lia.
          cbn [cargs_nonrec nonrec_arg_vals List.app List.length] in IH'.
          rewrite !List.length_app in IH'; cbn [List.length] in IH'; rewrite !Nat.add_1_r, !Nat.add_0_r, !List.app_nil_r in IH'.
          rewrite <- !List.app_assoc; rewrite <- !List.app_assoc in Hca0.
          apply IH'; try assumption.
          all: try (apply tele_prefix_rel_snoc; assumption).
          all: rewrite List.app_assoc; assumption.
        + (** Recursive in both. *)
          destruct xsA as [| x xsA], xsB as [| x' xsB]; try (inversion Hga; fail).
          destruct (con_args_rec_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hga) as [Hrr Hga0].
          destruct (con_args_rec_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca) as [HrrQ Hca0].
          cbn [nonrec_arg_vals] in Hnf, Hnq.
          apply List.Forall_cons_iff in HnA as [HnA0 HnA1]; apply List.Forall_cons_iff in HnB as [HnB0 HnB1].
          destruct Hco as (Hmt & Hdp & Hco).
          (** The container's type at its side, against its shape's. *)
          destruct (vg_cargs_sem_all qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA (gA1 ++ ca_rec t' :: nil) gA2 HeA'') as [HWA1 _].
          rewrite ECc in HWA1; destruct (rel_ctx_wf_ass_inv HWA1) as [iC HCv].
          pose proof (rel_ctx_wf_tail HWA1) as HWA.
          destruct (rel_ctx_wf_per_ctx_env HWA) as [RWA HRWA].
          destruct (rel_exp_of_typ_inversion_simple_at HRWA HCv _ _ (gargs_env_rel _ _ _ _ _ _ HRWA HWA LWA K1A))
            as (cA & cA' & EcA & EcA' & [RCC HCC]).
          assert (cA' = cA) as -> by (eapply functional_eval_exp; eassumption).
          destruct (shty_link qc D' HgQ HcvQ i' Mi' c gsA HMi' HconA HΨA gA1 t' gA2 HeA ub nsA vA1 Hlb ltac:(lia) LA Hubub HnsA K5 RenvA
                      (view_end_type VP HP qc D' HVQ ub Hubub Hlb (ptyp_mem t')) (List.length (ptyp_doms t')) 0 nil cA iC RCC
                      eq_refl (tele_prefix_rel_nil _) ltac:(constructor) ltac:(rewrite List.app_nil_r; exact EcA) HCC)
            as (aA & EaA & [RA HcaA]).
          rewrite List.app_nil_r in EaA; cbn [ptyp_skip] in EaA.
          (** The group's, and the values at it. *)
          destruct (Hglink t eq_refl) as (aB & iG & RGG & gB0 & EaB & EgB & HGG & (iB & RB & HgaB) & ERG).
          pose proof (cross_rec_move_back gB1 t gB2 vA1 vB1 x x' HeB K4 K6 Hrr) as Hrr'.
          assert (Hxx : RGG x x') by (apply ERG; exact Hrr').
          destruct (cross_position_vals gA1 (ca_rec t') gA2 gB1 (ca_rec t) gB2 vA1 vB1 _ _ x x' HeA HeB Hc1 LA LB K1 K2 K3 ECc ECg
                      ltac:(exists iG, RGG, gB0; split; [ exact EgB | split; [ exact HGG | exact Hxx ] ]))
            as [K1' K2' K3' (ic & Rc & cA0 & gB00 & EcA0 & EgB0 & Hcg)].
          assert (cA0 = cA) as -> by (eapply functional_eval_exp; eassumption).
          assert (gB00 = gB0) as -> by (eapply functional_eval_exp; eassumption).
          (** The two shapes' types related, and so their domains. *)
          destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ (per_univ_sym _ _ _ _ HcaA) Hcg) as (R1 & H1 & _).
          destruct (per_univ_elem_trans_any _ _ _ _ _ _ _ H1 HgaB) as (Rx & Hx & _).
          pose proof (cross_doms_fresh p D Hg u0 Hgu Hu v Mv c gsB gB1 t gB2 nsA nsB (nonrec_arg_vals gB1 vA1)
                        (nonrec_arg_vals gB1 vB1) HMv HconB HeB Hns K4 qc ub (List.length (ptyp_doms t)) 0 t'
                        (nsA ++ nonrec_arg_vals gA1 vA1) nil nil aA aB iC Rx
                        eq_refl ltac:(unfold ptyp_depth in *; lia) (tele_prefix_rel_nil _) EaA
                        ltac:(rewrite List.app_nil_r; exact EaB) Hx) as Hts.
          cbn [ptyp_skip] in Hts; rewrite !List.app_nil_r in Hts.
          apply cross_tops_rec; [ exact HnA0 | exact HnB0 | exact HrrQ | exact Hts |].
          pose proof (IH gB2 (gA1 ++ ca_rec t' :: nil) (gB1 ++ ca_rec t :: nil) (vA1 ++ x :: nil) (vB1 ++ x' :: nil) xsA xsB
                        HeA'' HeB'' Hc1' ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)) as IH'.
          rewrite !cargs_nonrec_app, !nonrec_arg_vals_app in IH' by lia.
          cbn [cargs_nonrec nonrec_arg_vals List.app List.length] in IH'.
          rewrite !List.app_nil_r in IH'.
          apply IH'; assumption.
    Qed.
  End CrossArgs.
End CrossFresh.

(** ** Results Taken from Either Side, Path by Path

    Along the group's leaf paths of an argument recursive in both: the
    marks [cs] of those the container has ([leaf_in]) and the flags [fs]
    of those the group read has a fresh variable at.  A fresh variable's
    path is the container's, and an eliminator's path of the container's
    is at a member [P] holds of. *)
Inductive cross_flags_ok (P : nat -> Prop) : list bool -> list bool -> list nat -> Prop :=
(** No path *)
| cross_flags_ok_nil : cross_flags_ok P nil nil nil
(** A fresh variable's path, the container's *)
| cross_flags_ok_fresh : forall cs fs j ms, cross_flags_ok P cs fs ms -> cross_flags_ok P (true :: cs) (true :: fs) (j :: ms)
(** An eliminator's path of the container's, at a member [P] holds of *)
| cross_flags_ok_nest : forall cs fs j ms, P j -> cross_flags_ok P cs fs ms -> cross_flags_ok P (true :: cs) (false :: fs) (j :: ms)
(** A path the group nests through alone *)
| cross_flags_ok_group : forall cs fs j ms, cross_flags_ok P cs fs ms -> cross_flags_ok P (false :: cs) (false :: fs) (j :: ms).

Lemma cross_flags_ok_length : forall P cs fs ms, cross_flags_ok P cs fs ms ->
    List.length fs = List.length cs /\ List.length ms = List.length cs.
Proof. induction 1; cbn; lia. Qed.

(** The flags of the paths [ls] by two tests. *)
Lemma cross_flags_ok_of : forall (P : nat -> Prop) (g f : leaf_path -> bool) ls,
    (forall l, In l ls -> f l = true -> g l = true) -> (forall l, In l ls -> g l = true -> f l = false -> P (leaf_mem l)) ->
    cross_flags_ok P (List.map g ls) (List.map f ls) (List.map leaf_mem ls).
Proof.
  intros P g f; induction ls as [| l ls IH]; intros H1 H2; cbn; [ constructor |].
  assert (IH' : cross_flags_ok P (List.map g ls) (List.map f ls) (List.map leaf_mem ls))
    by (apply IH; intros l0 Hl0; [ apply H1 | apply H2 ]; right; exact Hl0).
  destruct (g l) eqn:Hg, (f l) eqn:Hf.
  - apply cross_flags_ok_fresh; exact IH'.
  - apply cross_flags_ok_nest; [ apply H2; [ left; reflexivity | exact Hg | exact Hf ] | exact IH' ].
  - exfalso; pose proof (H1 l ltac:(left; reflexivity) Hf); congruence.
  - apply cross_flags_ok_group; exact IH'.
Qed.

Lemma cross_flags_ok_app : forall P cs1 cs2 ms1 ms2 fs, List.length cs1 = List.length ms1 ->
    cross_flags_ok P (cs1 ++ cs2) fs (ms1 ++ ms2) ->
    exists fs1 fs2, fs = fs1 ++ fs2 /\ cross_flags_ok P cs1 fs1 ms1 /\ cross_flags_ok P cs2 fs2 ms2.
Proof.
  intros P; induction cs1 as [| c cs1 IH]; intros cs2 [| m ms1] ms2 fs L H; cbn in L; try discriminate; cbn in H.
  - exists nil, fs; split; [ reflexivity | split; [ constructor | exact H ] ].
  - inversion H as [| ? ? ? ? H0 | ? ? ? ? Hm H0 | ? ? ? ? H0]; subst;
      destruct (IH cs2 ms1 ms2 _ ltac:(lia) H0) as (fs1 & fs2 & -> & H1 & H2);
      [ exists (true :: fs1), fs2 | exists (false :: fs1), fs2 | exists (false :: fs1), fs2 ];
      split; auto; split; auto; constructor; auto.
Qed.

(** Results taken from either side along the group's paths: at a fresh
    variable's, neutrals of the types on each side; at an eliminator's of
    the container's, each side's eliminator's result; at a path the group
    nests through alone, the group's eliminator's.  The container's lists
    are along its own paths, those [cs] marks. *)
Inductive cross_leaf_results : list bool -> list bool -> list domain -> list domain -> list domain -> list domain ->
    list domain -> list domain -> Prop :=
(** No path *)
| cross_leaf_results_nil : cross_leaf_results nil nil nil nil nil nil nil nil
(** A fresh neutral on each side *)
| cross_leaf_results_fresh : forall cs fs a a' as1 as2 r r' rs1 rs2 e e' o1 o2, Dom e ≈ e' ∈ per_bot ->
    cross_leaf_results cs fs as1 as2 rs1 rs2 o1 o2 ->
    cross_leaf_results (true :: cs) (true :: fs) (a :: as1) (a' :: as2) (r :: rs1) (r' :: rs2) (⇑ a e :: o1) (⇑ a' e' :: o2)
(** The eliminator's result on each side *)
| cross_leaf_results_nest : forall cs fs a a' as1 as2 r r' rs1 rs2 o1 o2,
    cross_leaf_results cs fs as1 as2 rs1 rs2 o1 o2 ->
    cross_leaf_results (true :: cs) (false :: fs) (a :: as1) (a' :: as2) (r :: rs1) (r' :: rs2) (r :: o1) (r' :: o2)
(** The group's eliminator's result alone *)
| cross_leaf_results_group : forall cs fs as1 a' as2 rs1 r' rs2 o1 o2,
    cross_leaf_results cs fs as1 as2 rs1 rs2 o1 o2 ->
    cross_leaf_results (false :: cs) (false :: fs) as1 (a' :: as2) rs1 (r' :: rs2) o1 (r' :: o2).

(** The number of the paths [cs] marks. *)
Definition marked (cs : list bool) : nat := List.length (List.filter (fun b => b) cs).

(** Paths none of which is marked: none counted. *)
Lemma marked_none : forall {X : Type} (l : list X), marked (List.map (fun _ => false) l) = 0.
Proof. intros X l; unfold marked; induction l; cbn; auto. Qed.

(** At paths none of which is the container's: the group's results. *)
Lemma cross_leaf_results_none : forall {X : Type} (l : list X) fs B S o1 o2,
    cross_leaf_results (List.map (fun _ => false) l) fs nil B nil S o1 o2 -> o1 = nil /\ o2 = S.
Proof.
  intros X; induction l as [| x l IH]; intros * H; cbn in H; inversion H; subst; [ split; reflexivity |].
  match goal with H0 : cross_leaf_results _ _ nil _ nil _ _ _ |- _ => destruct (IH _ _ _ _ _ H0) as [-> ->] end.
  split; reflexivity.
Qed.

Lemma marked_app : forall cs1 cs2, marked (cs1 ++ cs2) = marked cs1 + marked cs2.
Proof. intros; unfold marked; rewrite List.filter_app, List.length_app; reflexivity. Qed.

Lemma cross_leaf_results_length : forall cs fs as1 as2 rs1 rs2 o1 o2, cross_leaf_results cs fs as1 as2 rs1 rs2 o1 o2 ->
    List.length o1 = marked cs /\ List.length o2 = List.length cs.
Proof. induction 1; unfold marked in *; cbn; lia. Qed.

Lemma cross_leaf_results_app_inv : forall cs1 cs2 fs1 fs2 A1 A2 B1 B2 R1 R2 S1 S2 o1 o2,
    cross_leaf_results (cs1 ++ cs2) (fs1 ++ fs2) (A1 ++ A2) (B1 ++ B2) (R1 ++ R2) (S1 ++ S2) o1 o2 ->
    List.length fs1 = List.length cs1 -> List.length A1 = marked cs1 -> List.length R1 = marked cs1 ->
    List.length B1 = List.length cs1 -> List.length S1 = List.length cs1 ->
    exists o11 o12 o21 o22, o1 = o11 ++ o12 /\ o2 = o21 ++ o22 /\
      cross_leaf_results cs1 fs1 A1 B1 R1 S1 o11 o21 /\ cross_leaf_results cs2 fs2 A2 B2 R2 S2 o12 o22.
Proof.
  induction cs1 as [| c cs1 IH]; intros cs2 fs1 fs2 A1 A2 B1 B2 R1 R2 S1 S2 o1 o2 H Lf LA LR LB LS.
  - destruct fs1, A1, B1, R1, S1; cbn in Lf, LA, LR, LB, LS; try discriminate; unfold marked in *; cbn in *; try discriminate.
    exists nil, o1, nil, o2; split; [ reflexivity | split; [ reflexivity | split; [ constructor | exact H ] ] ].
  - destruct fs1 as [| f fs1]; cbn in Lf; [ discriminate |].
    destruct B1 as [| b B1], S1 as [| x S1]; cbn in LB, LS; try discriminate.
    unfold marked in LA, LR; cbn [List.filter] in LA, LR.
    destruct c.
    + destruct A1 as [| a A1], R1 as [| r R1]; cbn in LA, LR; try discriminate.
      cbn [List.app] in H.
      inversion H as [| ? ? ? ? ? ? ? ? ? ? e e' ? ? He H0 | ? ? ? ? ? ? ? ? ? ? ? ? H0 |]; subst;
        destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ H0 ltac:(lia) ltac:(unfold marked; lia) ltac:(unfold marked; lia) ltac:(lia) ltac:(lia))
          as (o11 & o12 & o21 & o22 & -> & -> & H1 & H2).
      * exists (⇑ a e :: o11), o12, (⇑ b e' :: o21), o22; split; [ reflexivity | split; [ reflexivity | split; [ constructor; assumption | exact H2 ] ] ].
      * exists (r :: o11), o12, (x :: o21), o22; split; [ reflexivity | split; [ reflexivity | split; [ constructor; assumption | exact H2 ] ] ].
    + cbn [List.app] in H.
      inversion H as [| | | ? ? ? ? ? ? ? ? ? ? H0]; subst;
        destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ H0 ltac:(lia) ltac:(unfold marked; lia) ltac:(unfold marked; lia) ltac:(lia) ltac:(lia))
          as (o11 & o12 & o21 & o22 & -> & -> & H1 & H2).
      exists o11, o12, (x :: o21), o22; split; [ reflexivity | split; [ reflexivity | split; [ constructor; assumption | exact H2 ] ] ].
Qed.

(** The results taken from either side of a function shape, along its
    paths [l1] (the container's) and [l2] (the group's), applied to
    arguments [c1] and [c2] read back alike: those of the rest at the
    functions' values there. *)
Lemma cross_leaf_results_apply : forall cs fs (l1 l2 : list nat) o1 o2 b1 b2 ρm1 ρm2 As1 As2 p1 p2 u1 u2 ρ1 ρ2 t1 t2
    f1 f2 Bk1 Bk2 c1 c2 fc1 fc2 tc1 tc2 rc1 rc2,
    cross_leaf_results cs fs
      (List.map (fun i => Πᵈ b1 (nil ↦ d_ihfam ρm1 As1 p1 u1 ρ1 t1 i f1) fam_cod) l1)
      (List.map (fun i => Πᵈ b2 (nil ↦ d_ihfam ρm2 As2 p2 u2 ρ2 t2 i f2) fam_cod) l2)
      (List.map (fun i => d_ihfn ρm1 Bk1 p1 u1 t1 i f1) l1) (List.map (fun i => d_ihfn ρm2 Bk2 p2 u2 t2 i f2) l2) o1 o2 ->
    $| f1 & c1 | gc_deps ⍮ gc_stack ↘ fc1 -> $| f2 & c2 | gc_deps ⍮ gc_stack ↘ fc2 ->
    ⟦ihty fc1 of t1 at p1 u1 under ρm1 As1 ⟧ gc_deps ⍮ gc_stack ⍮ ρ1 ↦ c1 ↘ tc1 ->
    ⟦ihty fc2 of t2 at p2 u2 under ρm2 As2 ⟧ gc_deps ⍮ gc_stack ⍮ ρ2 ↦ c2 ↘ tc2 ->
    ⟦ih fc1 of t1 under p1 u1 Bk1 ⟧ gc_deps ⍮ gc_stack ⍮ ρm1 ↘ rc1 -> ⟦ih fc2 of t2 under p2 u2 Bk2 ⟧ gc_deps ⍮ gc_stack ⍮ ρm2 ↘ rc2 ->
    (forall i, In i l1 -> i < List.length tc1 /\ i < List.length rc1) ->
    (forall i, In i l2 -> i < List.length tc2 /\ i < List.length rc2) ->
    Dom ⇓ b1 c1 ≈ ⇓ b2 c2 ∈ per_top ->
    exists oc1 oc2, List.Forall2 (fun g x => $| g & c1 | gc_deps ⍮ gc_stack ↘ x) o1 oc1 /\
      List.Forall2 (fun g x => $| g & c2 | gc_deps ⍮ gc_stack ↘ x) o2 oc2 /\
      cross_leaf_results cs fs (List.map (fun i => List.nth i tc1 d_True) l1) (List.map (fun i => List.nth i tc2 d_True) l2)
        (List.map (fun i => List.nth i rc1 d_True) l1) (List.map (fun i => List.nth i rc2 d_True) l2) oc1 oc2.
Proof.
  induction cs as [| cb cs IH]; intros * H Ef1 Ef2 T1 T2 R1 R2 Hi1 Hi2 Htop.
  - destruct l1, l2; cbn [List.map] in H; inversion H; subst; exists nil, nil; split; [ constructor | split; constructor ].
  - destruct cb.
    + destruct l1 as [| x1 l1], l2 as [| x2 l2]; cbn [List.map] in H; inversion H; subst; clear H.
      all: destruct (Hi1 x1 ltac:(left; reflexivity)) as [L1 L3]; destruct (Hi2 x2 ltac:(left; reflexivity)) as [L2 L4].
      all: match goal with H0 : cross_leaf_results _ _ _ _ _ _ _ _ |- _ =>
             destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 Ef1 Ef2 T1 T2 R1 R2
                         ltac:(intros i0 Hi0; apply Hi1; right; exact Hi0) ltac:(intros i0 Hi0; apply Hi2; right; exact Hi0) Htop)
               as (oc1 & oc2 & F1 & F2 & Hr) end.
      * match goal with He : per_bot ?e ?e' |- _ =>
          exists (⇑ (List.nth x1 tc1 d_True) (e $ᵈ ⇓ b1 c1) :: oc1), (⇑ (List.nth x2 tc2 d_True) (e' $ᵈ ⇓ b2 c2) :: oc2);
          split; [| split ]; [ constructor; [| exact F1 ] | constructor; [| exact F2 ] | cbn [List.map]; constructor; [| exact Hr ] ];
          [ apply eval_app_neut; eapply eval_fam_cod_ihfam; [ exact Ef1 | exact T1 | apply List.nth_error_nth'; exact L1 ]
          | apply eval_app_neut; eapply eval_fam_cod_ihfam; [ exact Ef2 | exact T2 | apply List.nth_error_nth'; exact L2 ]
          | exact (per_bot_app _ _ _ _ He Htop) ] end.
      * exists (List.nth x1 rc1 d_True :: oc1), (List.nth x2 rc2 d_True :: oc2).
        split; [| split ]; [ constructor; [| exact F1 ] | constructor; [| exact F2 ] | cbn [List.map]; constructor; exact Hr ].
        -- eapply eval_app_ihfn; [ exact Ef1 | exact R1 | apply List.nth_error_nth'; exact L3 ].
        -- eapply eval_app_ihfn; [ exact Ef2 | exact R2 | apply List.nth_error_nth'; exact L4 ].
    + destruct l2 as [| x2 l2]; cbn [List.map] in H; inversion H; subst; clear H.
      destruct (Hi2 x2 ltac:(left; reflexivity)) as [L2 L4].
      match goal with H0 : cross_leaf_results _ _ _ _ _ _ _ _ |- _ =>
        destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 Ef1 Ef2 T1 T2 R1 R2
                    Hi1 ltac:(intros i0 Hi0; apply Hi2; right; exact Hi0) Htop)
          as (oc1 & oc2 & F1 & F2 & Hr) end.
      exists oc1, (List.nth x2 rc2 d_True :: oc2).
      split; [ exact F1 | split; [ constructor; [| exact F2 ] | cbn [List.map]; constructor; exact Hr ] ].
      eapply eval_app_ihfn; [ exact Ef2 | exact R2 | apply List.nth_error_nth'; exact L4 ].
Qed.

(** Fresh variables along the paths flagged [fs], from [s] on, on each
    side, and the results along the paths from them and the eliminators'. *)
#[warnings="-cannot-define-projection"]
Record fresh_cross_out (cs fs : list bool) (as1 as2 rs1 rs2 : list domain) (s : nat) : Prop := mk_fresh_cross_out
  { (** The container's fresh variables *)
    fresh_cross_ihs1 : list domain
    (** The group's fresh variables *)
  ; fresh_cross_ihs2 : list domain
    (** The container's results along its paths *)
  ; fresh_cross_out1 : list domain
    (** The group's results along its paths *)
  ; fresh_cross_out2 : list domain
    (** The container's are fresh along the paths it has flagged *)
  ; fresh_cross_fresh1 : fresh_leaf_vars (sel_flags cs fs) as1 s fresh_cross_ihs1
    (** The group's along its paths flagged *)
  ; fresh_cross_fresh2 : fresh_leaf_vars fs as2 s fresh_cross_ihs2
    (** As many on each side *)
  ; fresh_cross_len : List.length fresh_cross_ihs1 = List.length fresh_cross_ihs2
    (** The container's results, its variables and its eliminator's *)
  ; fresh_cross_wrap1 : forall X, wrap_leaf_vals (sel_flags cs fs) rs1 (fresh_cross_ihs1 ++ X) X fresh_cross_out1
    (** The group's results, its variables and its eliminator's *)
  ; fresh_cross_wrap2 : forall Y, wrap_leaf_vals fs rs2 (fresh_cross_ihs2 ++ Y) Y fresh_cross_out2
    (** Taken from either side *)
  ; fresh_cross_rel : cross_leaf_results cs fs as1 as2 rs1 rs2 fresh_cross_out1 fresh_cross_out2 }.

Lemma fresh_cross_results : forall P cs fs ms, cross_flags_ok P cs fs ms ->
    forall as1 as2 rs1 rs2 s, List.length as1 = marked cs -> List.length rs1 = marked cs ->
    List.length as2 = List.length cs -> List.length rs2 = List.length cs ->
    fresh_cross_out cs fs as1 as2 rs1 rs2 s.
Proof.
  intros P cs fs ms H; induction H as [| cs fs j ms H IH | cs fs j ms Hj H IH | cs fs j ms H IH];
    intros as1 as2 rs1 rs2 s L1 L2 L3 L4; unfold marked in L1, L2; cbn [List.filter List.length] in L1, L2, L3, L4.
  - destruct as1, as2, rs1, rs2; cbn in *; try discriminate.
    apply (mk_fresh_cross_out nil nil nil nil nil nil s nil nil nil nil); try constructor; reflexivity.
  - destruct as1 as [| a as1], as2 as [| a' as2], rs1 as [| r rs1], rs2 as [| r' rs2]; cbn in L1, L2, L3, L4; try discriminate.
    destruct (IH as1 as2 rs1 rs2 (S s) ltac:(unfold marked; lia) ltac:(unfold marked; lia) ltac:(lia) ltac:(lia))
      as [i1 i2 o1 o2 F1 F2 Li W1 W2 Hr].
    apply (mk_fresh_cross_out _ _ _ _ _ _ _ (⇑! a s :: i1) (⇑! a' s :: i2) (⇑! a s :: o1) (⇑! a' s :: o2)).
    + constructor; exact F1.
    + constructor; exact F2.
    + cbn; lia.
    + intros X; cbn; constructor; apply W1.
    + intros Y; cbn; constructor; apply W2.
    + constructor; [ exact var_per_bot | exact Hr ].
  - destruct as1 as [| a as1], as2 as [| a' as2], rs1 as [| r rs1], rs2 as [| r' rs2]; cbn in L1, L2, L3, L4; try discriminate.
    destruct (IH as1 as2 rs1 rs2 s ltac:(unfold marked; lia) ltac:(unfold marked; lia) ltac:(lia) ltac:(lia))
      as [i1 i2 o1 o2 F1 F2 Li W1 W2 Hr].
    apply (mk_fresh_cross_out _ _ _ _ _ _ _ i1 i2 (r :: o1) (r' :: o2)).
    + constructor; exact F1.
    + constructor; exact F2.
    + exact Li.
    + intros X; constructor; apply W1.
    + intros Y; constructor; apply W2.
    + constructor; exact Hr.
  - destruct as2 as [| a' as2], rs2 as [| r' rs2]; cbn in L3, L4; try discriminate.
    destruct (IH as1 as2 rs1 rs2 s ltac:(unfold marked; lia) ltac:(unfold marked; lia) ltac:(lia) ltac:(lia))
      as [i1 i2 o1 o2 F1 F2 Li W1 W2 Hr].
    apply (mk_fresh_cross_out _ _ _ _ _ _ _ i1 i2 o1 (r' :: o2)).
    + exact F1.
    + constructor; exact F2.
    + exact Li.
    + exact W1.
    + intros Y; constructor; apply W2.
    + constructor; exact Hr.
Qed.

(** ** The Stuck Eliminators, Read Alike

    The setting of [ElimView.cross_elim_all], without its premise on the
    stuck eliminators, and the container's uniform parameters [ub] related
    to the view's instance [cups] at the group's [u0]. *)
(** The paths of the arguments [gq] (of the group read [Dc]) recursive in
    [gA] too (the container's): each [Dc] has, the container has. *)
Fixpoint cargs_leaf_mono (Dc D' : ind_decl) (gq gA : list carg) : Prop :=
  match gq, gA with
  | ca_rec t'' :: gq', ca_rec t' :: gA' => (forall l, leaf_in Dc t'' l = true -> leaf_in D' t' l = true) /\ cargs_leaf_mono Dc D' gq' gA'
  | _ :: gq', _ :: gA' => cargs_leaf_mono Dc D' gq' gA'
  | _, _ => True
  end.

(** The canonical relation of a member's non-uniform parameters at related
    uniform parameters [ups] and [ups2]: the same. *)
Lemma canon_nparams_base : forall pq G, valid_group pq G -> forall ups ups2,
    per_gargs (List.rev (ind_uparams G)) nil nil ups ups -> List.length ups = ind_nu G ->
    per_gargs (List.rev (ind_uparams G)) nil nil ups ups2 ->
    forall j Mj, ind_member G j = Some Mj -> forall a b,
      tele_rel (canon_nparams_rel G ups j) (List.rev (im_nparams Mj)) a b ->
      tele_rel (canon_nparams_rel G ups2 j) (List.rev (im_nparams Mj)) a b.
Proof.
  intros pq G Hg ups ups2 Hgu Hu Hg2 j Mj HM a b Hab.
  pose proof (valid_group_valid _ _ Hg) as HD.
  destruct (sort_value G HD ups Hgu Hu) as [s0 Hs0].
  pose proof (canon_hn G HD (valid_group_closed _ _ Hg) (valid_group_sort _ _ Hg) ups s0 Hu Hs0 ups2 Hg2) as Hn.
  destruct (vg_canon pq G Hg ups Hgu Hu) as [CnP CnI CaP CaI CdP CdI].
  pose proof (List.Forall_rev (member_nparams_ass G (valid_group_closed _ _ Hg) _ _ HM)) as Hta.
  apply (tele_rel_map _ (canon_nparams_rel G ups j)); [| exact Hab ].
  intros k pa pb x y Hk Hp1 _ Hxy.
  destruct (nth_error_lt_some' _ _ Hk) as [e He].
  destruct (proj1 (List.Forall_forall _ _) Hta e (List.nth_error_In _ _ He)) as [A ->].
  pose proof (nparams_prefix_rel_refl_l pq G ups _ _ _ (valid_group_ass _ _ Hg) CnP CnI CaP CaI CdP CdI j Mj HM k pa pb
                ltac:(lia) Hp1) as Hpa.
  destruct (Hn j Mj k A pa pa HM He Hpa) as (a1 & a2 & E1 & E2 & [R HR]).
  unfold canon_nparams_rel in *; rewrite (nth_ctyp_eq _ _ _ _ _ HM He) in Hxy |- *.
  intros i R' b1 b1' Eb Eb' HR'.
  pose proof (functional_eval_exp _ _ _ _ Eb E2) as ->; pose proof (functional_eval_exp _ _ _ _ Eb' E2) as ->.
  pose proof (per_univ_trans _ _ _ _ _ _ HR (per_univ_sym _ _ _ _ HR)) as H11.
  pose proof (Hxy _ _ _ _ E1 E1 H11) as Hx1.
  apply (per_univ_elem_left_irrel _ _ _ _ _ _ _ HR HR').
  apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ H11 HR); exact Hx1.
Qed.

(** ** The Container's Marks at a Record View's Fields

    The marks of the leaf paths of the arguments [gs] of a group's record
    view (kinds [gs'] at the container's [D']), those the container has
    ([leaf_in]): none of an argument the group nests through, those of the
    shape's of one recursive in both. *)
Fixpoint cargs_leaf_in (D D' : ind_decl) (gs' gs : list carg) : list bool :=
  match gs', gs with
  | ca_arg _ :: gs1', ca_arg _ :: gs1 => cargs_leaf_in D D' gs1' gs1
  | ca_arg _ :: gs1', ca_rec t :: gs1 => List.map (fun _ => false) (shape_leaves (rv_leaves D) 0 t) ++ cargs_leaf_in D D' gs1' gs1
  | ca_rec t' :: gs1', ca_rec t :: gs1 => List.map (leaf_in D' t') (shape_leaves (rv_leaves D) 0 t) ++ cargs_leaf_in D D' gs1' gs1
  | _, _ => nil
  end.

(** At a record view of the group and the container's the view takes to
    it, of one record and fields: the marks of its leaf paths are its
    fields'. *)
Lemma rview_leaf_in : forall D D' vm j' Mj' qr Is' fl gs' j Mj Is gs Ps' Ps, leaves_coherent D ->
    ind_member D' j' = Some Mj' -> im_head Mj' = mh_record qr Is' fl -> im_cons Mj' = (rview_con, gs') :: nil ->
    List.length gs' = List.length fl -> List.NoDup fl ->
    ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (rview_con, gs) :: nil ->
    List.length gs = List.length fl -> cargs_corr vm gs' gs ->
    List.map (leaf_in D' (pt_self j' Ps')) (shape_leaves (rv_leaves D) 0 (pt_self j Ps)) = cargs_leaf_in D D' gs' gs.
Proof.
  intros * HlcD HMj' Hh' Hcs' Hlen' Hnd HMj Hh Hcs Hlen Hcorr.
  cbn [shape_leaves]; rewrite (HlcD _ _ _ _ _ _ _ HMj Hh Hcs), List.map_map.
  erewrite List.map_ext by (intros; apply leaf_in_wk).
  assert (Hfs : forall fs2 fs2' fs1 fs1' ns, List.combine fl gs = fs1 ++ fs2 -> List.combine fl gs' = fs1' ++ fs2' ->
             List.length fs1 = List.length fs1' -> cargs_corr vm (List.map snd fs2') (List.map snd fs2) ->
             List.map (leaf_in D' (pt_self j' Ps')) (fields_leaves (rv_leaves D) ns fs2)
             = cargs_leaf_in D D' (List.map snd fs2') (List.map snd fs2)).
  { induction fs2 as [| [f g] fs2 IHf]; intros [| [f' g'] fs2'] fs1 fs1' ns E E' Lf Hco; cbn [List.map cargs_corr] in Hco;
      try (destruct g'; contradiction); try (destruct g; contradiction); [ reflexivity |].
    destruct (combine_app_split _ _ _ _ (eq_sym Hlen) E) as [Efl Egs].
    destruct (combine_app_split _ _ _ _ (eq_sym Hlen') E') as [Efl' Egs'].
    cbn [List.map] in Efl, Efl'.
    assert (Ef : f' = f).
    { assert (Hn1 : List.nth_error fl (List.length fs1) = Some f)
        by (rewrite Efl, List.nth_error_app2 by (rewrite List.length_map; lia); rewrite List.length_map, Nat.sub_diag; reflexivity).
      assert (Hn2 : List.nth_error fl (List.length fs1) = Some f')
        by (rewrite Efl', List.nth_error_app2 by (rewrite List.length_map; lia); rewrite List.length_map, Lf, Nat.sub_diag;
            reflexivity).
      congruence. }
    subst f'.
    assert (E1 : List.combine fl gs = (fs1 ++ (f, g) :: nil) ++ fs2) by (rewrite E, <- List.app_assoc; reflexivity).
    assert (E1' : List.combine fl gs' = (fs1' ++ (f, g') :: nil) ++ fs2') by (rewrite E', <- List.app_assoc; reflexivity).
    assert (L1 : List.length (fs1 ++ (f, g) :: nil) = List.length (fs1' ++ (f, g') :: nil)) by (rewrite !List.length_app; cbn; lia).
    assert (Hfind : List.find (fun fg => String.eqb (fst fg) f) (List.combine fl gs') = Some (f, g')).
    { rewrite E'; apply find_name_split; rewrite <- E', combine_fst_eq by exact (eq_sym Hlen'); exact Hnd. }
    destruct g as [A | t], g' as [A' | t']; cbn [cargs_corr] in Hco; try contradiction.
    - cbn [fields_leaves cargs_leaf_in List.map snd]; exact (IHf _ _ _ _ E1 E1' L1 Hco).
    - (** Nested through by the group: none of its paths is the
          container's. *)
      cbn [fields_leaves cargs_leaf_in List.map snd]; rewrite List.map_app, List.map_map.
      f_equal; [| exact (IHf _ _ _ _ E1 E1' L1 Hco) ].
      transitivity (List.map (fun _ => false) (shape_leaves (rv_leaves D) (List.length ns) t)).
      + apply List.map_ext; intros l; cbn [leaf_in]; rewrite HMj', Hh', Hcs', Hfind; reflexivity.
      + rewrite !List.map_const; f_equal; apply length_shape_leaves.
    - destruct Hco as (Hmt & Hdp & Hco).
      cbn [fields_leaves cargs_leaf_in List.map snd]; rewrite List.map_app, List.map_map.
      f_equal; [| exact (IHf _ _ _ _ E1 E1' L1 Hco) ].
      transitivity (List.map (leaf_in D' t') (shape_leaves (rv_leaves D) (List.length ns) t)).
      + apply List.map_ext; intros l; cbn [leaf_in]; rewrite HMj', Hh', Hcs', Hfind; reflexivity.
      + apply leaf_in_shape_leaves. }
  pose proof (Hfs (List.combine fl gs) (List.combine fl gs') nil nil nil eq_refl eq_refl eq_refl) as H.
  rewrite !combine_snd_eq in H by lia; exact (H Hcorr).
Qed.

Section CrossBot.
  #[local] Set Default Proof Using "All".
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hvg := valid_groups_valid VP HP p D HPD.
  Let Hcv := containers_valid_of_groups VP HP p D HPD.
  Let HD := valid_group_valid _ _ Hvg.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hl := valid_group_lookup _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
  Let Hass := valid_group_ass _ _ Hvg.
  Let Hrs : rview_struct_ok gc_deps gc_stack D := grp_tele_ass_rstruct _ Hass.
  Let Hlc : leaves_coherent D := leaves_coherent_of_order D (rview_struct_order _ _ _ Hrs).
  Variable (Γ : ctx) (RΓ : relation env).
  Hypotheses (HRΓ : EF Γ ≈ Γ ∈ per_ctx_env ↘ RΓ) (HΓ : ⊨ Γ).
  Variable (RU : relation env).
  Hypothesis (HRU : EF ind_uparams D ≈ ind_uparams D ∈ per_ctx_env ↘ RU).
  Variable (Us : list exp).
  Hypotheses (HUl : List.length Us = ind_nu D)
    (HUs : forall k N T, List.nth_error Us k = Some N -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T ->
             Γ ⊨ N : T).
  Variable (C1 : env) (u0 : list domain).
  Hypotheses (HC11 : RΓ C1 C1) (HUC : ⟦ Us ⟧* gc_deps ⍮ gc_stack ⍮ C1 ↘ u0).
  Variable (Bks : list eblock) (iA : nat).
  Hypothesis (HBk : valid_blocks p D Γ Us Bks iA).
  Let HBks := valid_blocks_has p D Γ Us Bks iA Hdt HBk.
  Let HMall := valid_blocks_mctx _ _ _ _ _ _ HBk.
  Let HAv := valid_blocks_motive _ _ _ _ _ _ HBk.
  Let nr := canon_nparams_rel D u0.
  Let ar := canon_args_rel D u0.
  Let dr := canon_doms_rel u0.
  Let G := grp_rel p D u0 nr ar dr.
  Let Rel := fun j ns m ns' m' =>
    per_head (List.nth j (blocks_motives Bks) a_True) (List.nth j (blocks_motives Bks) a_True)
      (env_args C1 (ns ++ m :: nil)) (env_args C1 (ns' ++ m' :: nil)).
  #[local] Abbreviation EB f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC).
  #[local] Abbreviation u0_len' := (u0_len D Us HUl C1 u0 HUC).
  #[local] Abbreviation u0_gargs' := (EB u0_gargs).
  #[local] Abbreviation Hcp := (vg_canon p D Hvg u0 u0_gargs' u0_len').
  #[local] Abbreviation HnP := (ind_canon_props_np_per _ _ Hcp).
  #[local] Abbreviation HnI := (ind_canon_props_np_iff _ _ Hcp).
  #[local] Abbreviation HaP := (ind_canon_props_arg_per _ _ Hcp).
  #[local] Abbreviation HaI := (ind_canon_props_arg_iff _ _ Hcp).
  #[local] Abbreviation HdP := (ind_canon_props_dom_per _ _ Hcp).
  #[local] Abbreviation HdI := (ind_canon_props_dom_iff _ _ Hcp).
  #[local] Abbreviation tsym := (nparams_rel_sym p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI).
  #[local] Abbreviation ttrans := (nparams_rel_trans p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI).
  (** The group's eliminator against itself at [C1] ([ElimView.SelfElim]). *)
  #[local] Abbreviation SE f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC Bks iA HBk).

  (** The view [m] of the container's member [k'], its map [vm]. *)
  Variable (qc : qname) (D' : ind_decl) (m : nat) (Mm : imember) (k' : nat) (Is : list exp) (vm : list nat).
  Hypotheses (Hq : ind_lookup gc_deps gc_stack qc = Some D') (HMm : ind_member D m = Some Mm)
    (Hh : im_head Mm = mh_view qc k' Is vm).
  Let HVQ := valid_groups_containers VP HP p D m Mm qc k' Is vm D' HPD HMm Hh Hq.
  Let HgQ := valid_groups_valid VP HP qc D' HVQ.
  Let HcvQ := containers_valid_of_groups VP HP qc D' HVQ.
  Let HdtQ := valid_group_typed _ _ HgQ.
  Let HassQ := valid_group_ass _ _ HgQ.
  Let HrsQ : rview_struct_ok gc_deps gc_stack D' := grp_tele_ass_rstruct _ HassQ.
  Let HlcQ : leaves_coherent D' := leaves_coherent_of_order D' (rview_struct_order _ _ _ HrsQ).

  (** The container's eliminator: a block for each member with one. *)
  Variable (ρb : env) (VBb : list eblock) (ub : list domain).
  Hypotheses (HbB : forall i' Mi', ind_member D' i' = Some Mi' -> im_is_rview Mi' = false -> exists b, List.nth_error VBb i' = Some b)
    (HnmB : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b -> eb_nm b = S (im_nn Mi'))
    (HnaB : forall i' Mi' b, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b -> brs_names (im_cons Mi') (eb_brs b))
    (HarB : forall i' Mi' b c gs' n B, ind_member D' i' = Some Mi' -> List.nth_error VBb i' = Some b ->
              ind_con Mi' c = Some gs' -> In (c, n, B) (eb_brs b) -> n = (im_nn Mi' + List.length gs' + cargs_nrec D' gs')%nat).
  Hypothesis (Hmot_x : forall i' Mi' v bb ba u u' ns ns' x x', ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
                List.nth_error vm i' = Some v -> List.nth_error VBb i' = Some bb -> List.nth_error Bks v = Some ba ->
                G v u u' ns ns' x x' ->
                exists a a', ⟦ eb_motive bb ⟧ env_args ρb (ns ++ x :: nil) ↘ a /\
                  ⟦ eb_motive ba ⟧ env_args C1 (ns' ++ x' :: nil) ↘ a' /\
                  DF a ≈ a' ∈ per_univ_elem iA ↘ Rel v ns x ns' x').
  Hypothesis (Hbr_x : forall i' Mi' v Mv bb ba c gs' gs nb na Bb Ba u u' bs bs' vs vs' w ihs hd k,
                ind_member D' i' = Some Mi' -> im_is_rview Mi' = false ->
                List.nth_error vm i' = Some v -> ind_member D v = Some Mv ->
                List.nth_error VBb i' = Some bb -> List.nth_error Bks v = Some ba ->
                ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
                brs_lookup (eb_brs bb) c = Some (nb, Bb) -> brs_lookup (eb_brs ba) c = Some (na, Ba) ->
                G v u u' (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs')
                  (d_con hd k c (bs ++ vs)) (d_con hd k c (bs' ++ vs')) ->
                cross_fields_rel D D' dr Rel C1 p u0 Bks v u u'
                  (List.skipn (im_unu D Mv) bs) (List.skipn (im_unu D Mv) bs') gs' gs vs vs' w ihs ->
                exists r r', ⟦ Bb ⟧ env_args ρb (List.skipn (im_unu D Mv) bs ++ vs ++ w) ↘ r /\
                  ⟦ Ba ⟧ env_args C1 (List.skipn (im_unu D Mv) bs' ++ vs' ++ ihs) ↘ r' /\
                  Rel v (List.skipn (im_unu D Mv) bs) (d_con hd k c (bs ++ vs))
                    (List.skipn (im_unu D Mv) bs') (d_con hd k c (bs' ++ vs')) r r').
  Variable (cups : list domain).
  Hypotheses (Ecups : ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ env_args nil u0 ↘ cups)
    (Hub : per_gargs (List.rev (ind_uparams D')) nil nil ub cups).
  #[local] Abbreviation XE f := (f VP p D HP HPD Γ RΓ HRΓ HΓ RU HRU Us HUl HUs C1 u0 HC11 HUC Bks iA HBk qc D' m Mm k' Is vm
     Hq HMm Hh ρb VBb ub HbB HnmB HnaB HarB Hmot_x Hbr_x).
  #[local] Abbreviation CF f := (f VP p D HP HPD m Mm qc k' Is vm D' HMm Hh Hq u0 cups ub u0_gargs' u0_len' Ecups Hub).
  (** The container's canonical relations at [ub]. *)
  Let nrQ := canon_nparams_rel D' ub.
  Let arQ := canon_args_rel D' ub.
  Let drQ := canon_doms_rel ub.
  Let AsA := blocks_motives VBb.
  Let AsB := blocks_motives Bks.

  (** The stuck eliminators at the member [j] of the group, with a block,
      and the container's members the view takes to [j]. *)
  Definition cross_bot (j : nat) : Prop :=
    forall i' Mj hd k as1 as2 e e' w w' ns ns', List.nth_error vm i' = Some j -> ind_member D j = Some Mj ->
      im_is_rview Mj = false -> G j w w' ns ns' (⇑ (d_ind hd k as1) e) (⇑ (d_ind hd k as2) e') ->
      Dom d_elim ρb VBb qc ub i' as1 e ≈ d_elim C1 Bks p u0 j as2 e' ∈ per_bot.

  Lemma cross_view_members : forall j' j, List.nth_error vm j' = Some j ->
      exists Mj' Mj, ind_member D' j' = Some Mj' /\ view_member p D qc D' vm j' Mj' j Mj.
  Proof. exact (XE cross_member). Qed.

  (** The two eliminators at related neutrals of a member with a block:
      stuck, on each side. *)
  Lemma cross_neut_evals : forall i' j Mj hd k as1 as2 e e' w w' ns ns', List.nth_error vm i' = Some j ->
      ind_member D j = Some Mj -> im_is_rview Mj = false ->
      G j w w' ns ns' (⇑ (d_ind hd k as1) e) (⇑ (d_ind hd k as2) e') ->
      exists r r', ⟦elim ⇑ (d_ind hd k as1) e at i' of qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ r /\
        ⟦elim ⇑ (d_ind hd k as2) e' at j of p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ r'.
  Proof.
    intros * Hvi HM Hrv Hcur.
    pose proof Hcur as Hcur0.
    inversion Hcur0 as [| j0 Mj0 hd0 k0 ns0 ns0' as1' as2' e0 e0' w0 w0' HM0 Hrv0 Href Hn L1 L2 Hs1 Hs2 He |]; subst;
      [| rewrite HM in *; match goal with H : Some _ = Some _ |- _ => injection H as <- end;
         exfalso; eapply not_rview_record; eassumption ].
    rewrite HM in HM0; injection HM0 as <-.
    destruct (cross_view_members i' j Hvi) as (Mi' & Mk0 & HMi' & Hvmb).
    pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMk0; rewrite HM in HMk0; injection HMk0 as <-.
    pose proof (view_member_nn _ _ _ _ _ _ _ _ _ Hvmb) as Hnn'.
    assert (HrvI : im_is_rview Mi' = false) by (rewrite <- (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb); exact Hrv).
    pose proof (ind_rel_idx p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HM Hcur Hs1 Hs2) as Hm.
    destruct (SE self_ref_target _ _ _ _ HM Href) as (Dq & Mq & Hq' & HMq & Hnnq & Hnuq).
    destruct (HbB _ _ HMi' HrvI) as [bb Hbb]; destruct (HBks _ _ HM Hrv) as [ba Hba].
    destruct (Hmot_x i' Mi' j bb ba w w' _ _ _ _ HMi' HrvI Hvi Hbb Hba Hm) as (a & a' & Ea & Ea' & HR).
    exists (⇑ a (d_elim ρb VBb qc ub i' as1 e)), (⇑ a' (d_elim C1 Bks p u0 j as2 e')); split.
    - eapply eval_elim_neut; [ exact Hq | exact HMi' | rewrite <- (view_member_ref _ _ _ _ _ _ _ _ _ Hvmb HrvI); exact Href | exact Hq'
                             | exact HMq | unfold im_np; lia | exact Hbb | rewrite (HnmB _ _ _ HMi' Hbb), Hnnq, Hnn'; reflexivity
                             | rewrite Hnuq; exact Ea ].
    - eapply eval_elim_neut; [ exact Hl | exact HM | exact Href | exact Hq' | exact HMq | unfold im_np; lia | exact Hba
                             | rewrite (valid_blocks_nm _ _ _ _ _ _ HBk _ _ _ HM Hba), Hnnq; reflexivity | rewrite Hnuq; exact Ea' ].
  Qed.

  (** The container's canonical relation of a member's non-uniform
      parameters at [ub] is the group's at [u0] of the member the view
      takes it to: at [cups] by the view, and [ub] and [cups] are
      related. *)
  Lemma cross_nparams_transfer : forall j' Mj' j Mj, List.nth_error vm j' = Some j -> ind_member D' j' = Some Mj' ->
      ind_member D j = Some Mj -> forall a b, tele_rel (nrQ j') (List.rev (im_nparams Mj')) a b ->
      tele_rel (nr j) (List.rev (im_nparams Mj)) a b.
  Proof.
    intros * Hv HMj' HMj a b Hab.
    pose proof (length_cups p D Hvg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups) as Hlcu.
    assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
    pose proof (uparams_refl_l D' (valid_group_valid _ _ HgQ) (valid_group_closed _ _ HgQ) _ _ Hub) as Hubub.
    apply (view_nparams_transfer p D Hvg Hcv m Mm qc k' Is vm D' HMm Hh Hq u0 cups u0_gargs' u0_len' Ecups j' Mj' j Mj HMj' Hv HMj).
    exact (canon_nparams_base qc D' HgQ ub cups Hubub Hlb Hub j' Mj' HMj' a b Hab).
  Qed.

  (** The container's paths are as many as the group's it has. *)
  Lemma cross_marked : forall t' t, shape_corr vm t' t ->
      marked (List.map (leaf_in D' t') (shape_leaves (rv_leaves D) 0 t)) = List.length (shape_leaves (rv_leaves D') 0 t').
  Proof.
    intros t' t Hsc.
    rewrite <- (leaves_in_count_view p qc D D' vm Hlc HlcQ Hrs HrsQ cross_view_members (S (ptyp_mem t)) t' t 0
                  ltac:(intros; lia) Hsc).
    unfold marked, leaves_in_count; induction (shape_leaves (rv_leaves D) 0 t) as [| l ls IH]; cbn; [ reflexivity |].
    destruct (leaf_in D' t' l); cbn; rewrite IH; reflexivity.
  Qed.

  (** *** The Recursive Results at Neutrals, Path by Path

      The recursive results of neutral arguments [vA] (the container's,
      of its shape [t'], after its own prefix [preQ]) and [vB] (the
      group's, of [t], after [pre']), along the group's leaf paths: the
      types and the eliminators' results on each side, and results taken
      from either ([cross_leaf_results]) related as the cross relation
      has them. *)
  #[warnings="-cannot-define-projection"]
  Record cross_ih_out (k : nat) (pre pre' preQ : list domain) (t' t : ptyp) (vA vB : domain) (fs : list bool) : Prop :=
    mk_cross_ih_out
    { (** The container's recursive results' types *)
      cross_ih_tyA : list domain
      (** The group's recursive results' types *)
    ; cross_ih_tyB : list domain
      (** The container's eliminator's results *)
    ; cross_ih_resA : list domain
      (** The group's eliminator's results *)
    ; cross_ih_resB : list domain
      (** The container's types, its components after [preQ] at [ub] *)
    ; cross_ih_Ta : ⟦ihty vA of t' at qc ub under ρb AsA ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ub ++ preQ) ↘ cross_ih_tyA
      (** The group's types, its components after [pre'] at [u0] *)
    ; cross_ih_Tb : ⟦ihty vB of t at p u0 under C1 AsB ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ pre') ↘ cross_ih_tyB
      (** The container's eliminator's results *)
    ; cross_ih_Ra : ⟦ih vA of t' under qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ cross_ih_resA
      (** The group's eliminator's results *)
    ; cross_ih_Rb : ⟦ih vB of t under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ cross_ih_resB
      (** One container type per container path *)
    ; cross_ih_lta : List.length cross_ih_tyA = List.length (shape_leaves (rv_leaves D') 0 t')
      (** One group type per group path *)
    ; cross_ih_ltb : List.length cross_ih_tyB = List.length (shape_leaves (rv_leaves D) 0 t)
      (** One container result per container path *)
    ; cross_ih_lra : List.length cross_ih_resA = List.length (shape_leaves (rv_leaves D') 0 t')
      (** One group result per group path *)
    ; cross_ih_lrb : List.length cross_ih_resB = List.length (shape_leaves (rv_leaves D) 0 t)
      (** Results taken from either are related *)
    ; cross_ih_rel : forall oA oB,
        cross_leaf_results (List.map (leaf_in D' t') (shape_leaves (rv_leaves D) 0 t)) fs
          cross_ih_tyA cross_ih_tyB cross_ih_resA cross_ih_resB oA oB ->
        cross_result_rel D D' dr Rel C1 p u0 Bks k u0 u0 pre pre' t' t vA vB oA oB }.

  (** Of the fields [xsA] of a container's record view (kinds [gA], after
      its own prefix [preQ]) against [xsB] of the group's (kinds [gB]),
      the group's types [tyB] and results [resB] given: the container's
      types and results, and results taken from either related as
      [cross_fields_rel] has them. *)
  #[warnings="-cannot-define-projection"]
  Record cross_ihs_out (k : nat) (pre pre' preQ : list domain) (gA gB : list carg) (xsA xsB : list domain) (fs : list bool)
      (tyB resB : list domain) : Prop := mk_cross_ihs_out
    { (** The container's recursive results' types *)
      cross_ihs_tyA : list domain
      (** The container's eliminator's results *)
    ; cross_ihs_resA : list domain
      (** The container's types, its fields' after [preQ] at [ub] *)
    ; cross_ihs_Ta : ⟦ihtys xsA of gA at qc ub under ρb AsA ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (ub ++ preQ) ↘ cross_ihs_tyA
      (** The container's eliminator's results *)
    ; cross_ihs_Ra : ⟦ihs xsA of gA under qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ cross_ihs_resA
      (** One container type per container path *)
    ; cross_ihs_lta : List.length cross_ihs_tyA = cargs_nrec D' gA
      (** One container result per container path *)
    ; cross_ihs_lra : List.length cross_ihs_resA = cargs_nrec D' gA
      (** Results taken from either are related *)
    ; cross_ihs_rel : forall oA oB,
        cross_leaf_results (cargs_leaf_in D D' gA gB) fs cross_ihs_tyA tyB cross_ihs_resA resB oA oB ->
        cross_fields_rel D D' dr Rel C1 p u0 Bks k u0 u0 pre pre' gA gB xsA xsB oA oB }.

  (** The fields one by one, the shapes recursive in both by [HQ]. *)
  Lemma cross_fields_walk : forall (Q : ptyp -> Prop),
      (forall t' t, Q t -> forall k kQ pre pre' preQ vA vB fs, shape_corr vm t' t ->
         rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u0 u0 pre pre' t vA vB ->
         rec_arg_rel qc D' (okr_at D' ub nrQ) nrQ arQ drQ kQ ub ub preQ preQ t' vA vA ->
         cross_doms ub dr k pre preQ (env_args nil (u0 ++ pre')) t' t -> is_neut vA -> is_neut vB ->
         cross_flags_ok cross_bot (List.map (leaf_in D' t') (shape_leaves (rv_leaves D) 0 t)) fs
           (List.map leaf_mem (shape_leaves (rv_leaves D) 0 t)) ->
         cross_ih_out k pre pre' preQ t' t vA vB fs) ->
      forall gA gB xsA xsB k kQ pre pre' preQ fs tyB resB, (forall t, In (ca_rec t) gB -> Q t) -> cargs_corr vm gA gB ->
        con_args_rel p D (okr_at D u0 nr) nr ar dr k u0 u0 pre pre' gB xsA xsB ->
        cross_tops qc D' ub u0 dr kQ k pre preQ pre' gA gB xsA xsB ->
        cross_flags_ok cross_bot (cargs_leaf_in D D' gA gB) fs (cargs_mems D gB) ->
        ⟦ihtys xsB of gB at p u0 under C1 AsB ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ pre') ↘ tyB ->
        ⟦ihs xsB of gB under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1 ↘ resB ->
        cross_ihs_out k pre pre' preQ gA gB xsA xsB fs tyB resB.
  Proof.
    intros Q HQ.
    induction gA as [| g' gA IH]; intros [| gB0 gB] xsA xsB k kQ pre pre' preQ fs tyB resB HinQ Hco Hca Ht Hfl Tb Rb;
      cbn in Hco; try contradiction; try (destruct g'; contradiction).
    - inversion Ht; subst; inversion Tb; subst; inversion Rb; subst; cbn in Hfl; inversion Hfl; subst.
      apply (mk_cross_ihs_out _ _ _ _ _ _ _ _ _ _ _ nil nil); try constructor; try reflexivity.
      intros oA oB Hclr; inversion Hclr; subst; constructor.
    - assert (HinQ' : forall t0, In (ca_rec t0) gB -> Q t0) by (intros t0 Hin; apply HinQ; right; exact Hin).
      destruct g' as [A' | t'], gB0 as [A | t]; cbn in Hco; try contradiction.
      + (** Non-recursive in both. *)
        inversion Ht; subst.
        match goal with Ht' : cross_tops _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Ht' into Ht0 end.
        pose proof (con_args_arg_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca) as Hca0.
        inversion Tb; subst.
        match goal with T0 : eval_ihtys _ _ _ _ _ _ _ _ _ _ |- _ => rename T0 into Tb0 end.
        inversion Rb; subst.
        match goal with R0 : eval_ihs _ _ _ _ _ _ _ _ _ |- _ => rename R0 into Rb0 end.
        rewrite <- env_args_snoc, <- List.app_assoc in Tb0.
        cbn [cargs_leaf_in cargs_mems] in Hfl.
        destruct (IH gB _ _ k kQ _ _ _ fs tyB resB HinQ' Hco Hca0 Ht0 Hfl Tb0 Rb0) as [tyA resA Ta Ra Lta Lra Hrel].
        apply (mk_cross_ihs_out _ _ _ _ _ _ _ _ _ _ _ tyA resA).
        * apply eval_ihtys_arg; rewrite <- env_args_snoc, <- List.app_assoc; exact Ta.
        * apply eval_ihs_arg; exact Ra.
        * exact Lta.
        * exact Lra.
        * intros oA oB Hclr; apply cross_fields_arg; exact (Hrel _ _ Hclr).
      + (** Nested through by the group only: its eliminator's results. *)
        inversion Ht; subst.
        match goal with Ht' : cross_tops _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Ht' into Ht0 end.
        destruct (con_args_rec_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca) as [Hrr Hca0].
        inversion Tb; subst.
        match goal with T1 : eval_ihty _ _ _ _ _ _ _ _ _ _, T2 : eval_ihtys _ _ _ _ _ _ _ _ _ _ |- _ =>
          rename T1 into Tb1; rename T2 into Tb2 end.
        inversion Rb; subst.
        match goal with R1 : eval_ih _ _ _ _ _ _ _ _ _, R2 : eval_ihs _ _ _ _ _ _ _ _ _ |- _ =>
          rename R1 into Rb1; rename R2 into Rb2 end.
        cbn [cargs_leaf_in cargs_mems] in Hfl.
        assert (Lfm : List.length (List.map (fun _ => false) (shape_leaves (rv_leaves D) 0 t)) = List.length (shape_mems D t))
          by (unfold shape_mems; rewrite !List.length_map; reflexivity).
        destruct (cross_flags_ok_app _ _ _ _ _ _ Lfm Hfl) as (fs1 & fs2 & -> & Hf1 & Hf2).
        destruct (IH gB _ _ k kQ _ _ _ fs2 _ _ HinQ' Hco Hca0 Ht0 Hf2 Tb2 Rb2) as [tyA resA Ta Ra Lta Lra Hrel].
        apply (mk_cross_ihs_out _ _ _ _ _ _ _ _ _ _ _ tyA resA).
        * apply eval_ihtys_arg; rewrite <- env_args_snoc, <- List.app_assoc; exact Ta.
        * apply eval_ihs_arg; exact Ra.
        * exact Lta.
        * exact Lra.
        * intros oA oB Hclr.
          rewrite <- (List.app_nil_l tyA), <- (List.app_nil_l resA) in Hclr.
          pose proof (proj1 (cross_flags_ok_length _ _ _ _ Hf1)) as Lf1.
          pose proof (proj1 eval_ihty_length_all _ _ _ _ _ _ _ _ Tb1 D Hl Hlc) as LB1.
          pose proof (proj1 (proj2 eval_ih_length_all) _ _ _ _ _ _ _ Rb1 D Hl Hlc) as LS1.
          destruct (cross_leaf_results_app_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hclr Lf1
                      ltac:(rewrite marked_none; reflexivity) ltac:(rewrite marked_none; reflexivity)
                      ltac:(rewrite LB1, List.length_map; reflexivity) ltac:(rewrite LS1, List.length_map; reflexivity))
            as (o11 & o12 & o21 & o22 & -> & -> & H1 & H2).
          destruct (cross_leaf_results_none _ _ _ _ _ _ H1) as [-> ->].
          cbn [List.app]; eapply cross_fields_nest; [ exact Rb1 | exact (Hrel _ _ H2) ].
      + (** Recursive in both. *)
        destruct Hco as (Hmt & Hdp & Hco).
        pose proof (shape_corr_of _ _ _ Hmt Hdp) as Hsc.
        inversion Ht; subst.
        match goal with Ht' : cross_tops _ _ _ _ _ _ _ _ _ _ _ _ _ _, HrQ' : rec_arg_rel qc _ _ _ _ _ _ _ _ _ _ _ _ _,
                        Hd' : cross_doms _ _ _ _ _ _ _ _ |- _ =>
          rename Ht' into Ht0; rename HrQ' into HrQ; rename Hd' into Hdoms end.
        match goal with Hn1 : is_neut ?a1, Hn2 : is_neut ?a2 |- _ => rename Hn1 into HnA; rename Hn2 into HnB end.
        destruct (con_args_rec_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca) as [Hrr Hca0].
        inversion Tb; subst.
        match goal with T1 : eval_ihty _ _ _ _ _ _ _ _ _ _, T2 : eval_ihtys _ _ _ _ _ _ _ _ _ _ |- _ =>
          rename T1 into Tb1; rename T2 into Tb2 end.
        inversion Rb; subst.
        match goal with R1 : eval_ih _ _ _ _ _ _ _ _ _, R2 : eval_ihs _ _ _ _ _ _ _ _ _ |- _ =>
          rename R1 into Rb1; rename R2 into Rb2 end.
        cbn [cargs_leaf_in cargs_mems] in Hfl.
        assert (Lfm : List.length (List.map (leaf_in D' t') (shape_leaves (rv_leaves D) 0 t)) = List.length (shape_mems D t))
          by (unfold shape_mems; rewrite !List.length_map; reflexivity).
        destruct (cross_flags_ok_app _ _ _ _ _ _ Lfm Hfl) as (fs1 & fs2 & -> & Hf1 & Hf2).
        destruct (HQ t' t (HinQ t (or_introl eq_refl)) k kQ pre pre' preQ _ _ fs1 Hsc Hrr HrQ Hdoms HnA HnB Hf1)
          as [tyA1 tyB1 resA1 resB1 Ta1 Tb1' Ra1 Rb1' Lta1 Ltb1 Lra1 Lrb1 Hrel1].
        pose proof (functional_eval_ihty _ _ _ _ _ _ _ _ _ Tb1' Tb1) as <-.
        pose proof (functional_eval_ih _ _ _ _ _ _ _ _ Rb1' Rb1) as <-.
        destruct (IH gB _ _ k kQ _ _ _ fs2 _ _ HinQ' Hco Hca0 Ht0 Hf2 Tb2 Rb2) as [tyA2 resA2 Ta2 Ra2 Lta2 Lra2 Hrel2].
        apply (mk_cross_ihs_out _ _ _ _ _ _ _ _ _ _ _ (tyA1 ++ tyA2) (resA1 ++ resA2)).
        * econstructor; [ exact Ta1 | exact Ta2 ].
        * econstructor; [ exact Ra1 | exact Ra2 ].
        * cbn [cargs_nrec]; rewrite List.length_app, Lta1, Lta2; reflexivity.
        * cbn [cargs_nrec]; rewrite List.length_app, Lra1, Lra2; reflexivity.
        * intros oA oB Hclr.
          pose proof (proj1 (cross_flags_ok_length _ _ _ _ Hf1)) as Lf1.
          destruct (cross_leaf_results_app_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hclr Lf1
                      ltac:(rewrite Lta1, (cross_marked _ _ Hsc); reflexivity) ltac:(rewrite Lra1, (cross_marked _ _ Hsc); reflexivity)
                      ltac:(rewrite Ltb1, List.length_map; reflexivity) ltac:(rewrite Lrb1, List.length_map; reflexivity))
            as (o11 & o12 & o21 & o22 & -> & -> & H1 & H2).
          destruct (cross_leaf_results_length _ _ _ _ _ _ _ _ H1) as [Lo1 Lo2].
          eapply cross_fields_rec; [ | | exact (Hrel1 _ _ H1) | exact (Hrel2 _ _ H2) ].
          -- rewrite Lo1; unfold marked, leaves_in_count.
             clear; induction (shape_leaves (rv_leaves D) 0 t) as [| l ls IH]; cbn; [ reflexivity |].
             destruct (leaf_in D' t' l); cbn; rewrite IH; reflexivity.
          -- rewrite Lo2, List.length_map; reflexivity.
  Qed.


  Lemma cross_leaves : forall n t' t, (forall Mj, ind_member D (ptyp_mem t) = Some Mj -> im_is_rview Mj = true -> ptyp_mem t < n) ->
      forall k kQ pre pre' preQ vA vB fs, shape_corr vm t' t ->
      rec_arg_rel p D (okr_at D u0 nr) nr ar dr k u0 u0 pre pre' t vA vB ->
      rec_arg_rel qc D' (okr_at D' ub nrQ) nrQ arQ drQ kQ ub ub preQ preQ t' vA vA ->
      cross_doms ub dr k pre preQ (env_args nil (u0 ++ pre')) t' t ->
      is_neut vA -> is_neut vB ->
      cross_flags_ok cross_bot (List.map (leaf_in D' t') (shape_leaves (rv_leaves D) 0 t)) fs
        (List.map leaf_mem (shape_leaves (rv_leaves D) 0 t)) ->
      cross_ih_out k pre pre' preQ t' t vA vB fs.
  Proof.
    induction n as [n IHn] using Wf_nat.lt_wf_ind.
    intros t'; induction t' as [j' Ps' | B' t1' IHt]; intros [j Ps | B t1] Hrk k kQ pre pre' preQ vA vB fs Hsc Hrg HrQ Hd HnA HnB Hfl;
      cbn in Hsc; try contradiction.
    - destruct (cross_view_members _ _ Hsc) as (Mj' & Mj & HMj' & Hvmb).
      pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMj.
      pose proof (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb) as Ervs.
      destruct (im_is_rview Mj) eqn:Hrv.
      + (** Record views: their fields, at the projections. *)
        specialize (Hrk Mj HMj Hrv); cbn [ptyp_mem] in Hrk.
        assert (Hrv' : im_is_rview Mj' = true) by congruence.
        unfold im_is_rview in Hrv'; destruct (im_head Mj') as [| | qr Is' fl] eqn:Hh'; try discriminate Hrv'.
        destruct (view_member_rview _ _ _ _ _ _ _ _ _ Hvmb _ _ _ Hh') as (Is0 & Hh0).
        destruct (rview_struct_con _ _ _ Hrs _ _ _ _ _ HMj Hh0) as (gsr & Hcs & Hlen).
        destruct (rview_struct_con _ _ _ HrsQ _ _ _ _ _ HMj' Hh') as (gsr' & Hcs' & Hlen').
        destruct (rview_struct_record _ _ _ HrsQ _ _ _ _ _ HMj' Hh') as [Rr HR].
        pose proof (rview_record_nodup _ _ _ _ _ _ HR) as Hnd.
        assert (HcB : ind_con Mj rview_con = Some gsr)
          by (unfold ind_con; rewrite Hcs; cbn; rewrite ?String.eqb_refl; reflexivity).
        destruct (view_member_cons' _ _ _ _ _ _ _ _ _ Hvmb rview_con gsr HcB) as (g0 & HcA & Hcorr).
        assert (g0 = gsr') as ->
          by (unfold ind_con in HcA; rewrite Hcs' in HcA; cbn in HcA; rewrite ?String.eqb_refl in HcA; injection HcA as <-;
              reflexivity).
        (** The fields on each side, at the projections. *)
        destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrg) as (bs & bs' & Eb & Eb' & _ & _ & Hi).
        destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HrQ) as (bsQ & bsQ' & EbQ & EbQ' & _ & _ & HiQ).
        pose proof Hi as Hi0.
        inversion Hi0 as [? Mx ? ? ? ? cx gsx ? ? vsx vsx' ? ? HMx Hrvx | ? Mx ? ? ? ? ? ? ? ? ? ? HMx Hrvx
                         | ? Mx qrx Isx flx cx gsx ? ws ? ws' ? ? HMx Hhx Hnpx Hcsx Ew Ew' Hnr Hca]; subst;
          [ exfalso; destruct HnA as (? & ? & HnA); discriminate HnA
          | exfalso; rewrite HMj in HMx; injection HMx as <-; congruence |].
        rewrite HMj in HMx; injection HMx as <-.
        rewrite Hh0 in Hhx; injection Hhx as <- <- <-; rewrite Hcs in Hcsx; injection Hcsx as <- <-.
        pose proof HiQ as HiQ0.
        inversion HiQ0 as [? My ? ? ? ? cy gsy ? ? vsy vsy' ? ? HMy Hrvy | ? My ? ? ? ? ? ? ? ? ? ? HMy Hrvy
                          | ? My qry Isy fly cy gsy ? wsQ ? wsQ' ? ? HMy Hhy Hnpy Hcsy EwQ EwQ' HnrQ HcaQ]; subst;
          [ exfalso; destruct HnA as (? & ? & HnA); discriminate HnA
          | exfalso; rewrite HMj' in HMy; injection HMy as <-; unfold im_is_rview in Hrvy; rewrite Hh' in Hrvy; discriminate Hrvy |].
        rewrite HMj' in HMy; injection HMy as <-.
        rewrite Hh' in Hhy; injection Hhy as <- <- <-; rewrite Hcs' in Hcsy; injection Hcsy as <- <-.
        pose proof (functional_eval_projs _ _ _ _ EwQ Ew) as ->; pose proof (functional_eval_projs _ _ _ _ EwQ' Ew) as ->.
        pose proof (is_neut_projs _ _ _ Ew HnA) as HnwA; pose proof (is_neut_projs _ _ _ Ew' HnB) as HnwB.
        (** The group's results at its side. *)
        destruct (SE self_rview_ihs j nil nil vA vB Mj qr Is0 fl rview_con gsr ws ws' Hi HnA HnB HMj Hh0 Hcs Ew Ew')
          as [tys tys' rs rs' _ Tb0 _ Rb0].
        (** The fields read alike at their domains. *)
        assert (HcpR : cross_params D D' u0 cups ub Mj' j Mj nil nil).
        { apply mk_cross_params; unfold im_params; rewrite ?Hnpx, ?Hnpy; cbn [List.rev List.app]; rewrite ?List.app_nil_r.
          - split; [ reflexivity | exact I ].
          - exact Hub.
          - exact (view_cups_rel p D Hvg Hcv m Mm qc k' Is vm D' HMm Hh Hq u0 cups u0_gargs' u0_len' Ecups).
          - exact u0_gargs'. }
        assert (HnsQ : tele_rel (canon_nparams_rel D' ub j') (List.rev (im_nparams Mj')) nil nil)
          by (rewrite Hnpy; split; [ reflexivity | exact I ]).
        assert (K1 : per_gargs (List.rev (cargs_ctx qc D' Mj' nil ++ im_params D' Mj')) nil nil (ub ++ nil ++ nil) (cups ++ nil ++ nil))
          by (cbn [cargs_ctx cargs_ctx_aux List.app]; pose proof (cross_params_container _ _ _ _ _ _ _ _ _ _ HcpR) as Hx;
              rewrite !List.app_nil_r in Hx |- *; exact Hx).
        assert (K2 : per_gargs (List.rev (cargs_ctx qc D' Mj' nil ++ im_params D' Mj')) nil nil (cups ++ nil ++ nil) (cups ++ nil ++ nil))
          by (cbn [cargs_ctx cargs_ctx_aux List.app]; pose proof (cross_params_container_right _ _ _ _ _ _ _ _ _ _ HcpR) as Hx;
              rewrite !List.app_nil_r in Hx |- *; exact Hx).
        assert (K3 : per_gargs (List.rev (cargs_ctx p D Mj nil ++ im_params D Mj)) nil nil (u0 ++ nil ++ nil) (u0 ++ nil ++ nil))
          by (cbn [cargs_ctx cargs_ctx_aux List.app]; pose proof (cross_params_group_right _ _ _ _ _ _ _ _ _ _ HcpR) as Hx;
              rewrite !List.app_nil_r in Hx |- *; exact Hx).
        assert (HcA' : ind_con Mj' rview_con = Some gsr')
          by (unfold ind_con; rewrite Hcs'; cbn; rewrite ?String.eqb_refl; reflexivity).
        pose proof (CF cross_vals_cargs j' Mj' j Mj HMj' Hsc HMj rview_con gsr' gsr HcA' HcB Hcorr nil nil HcpR HnsQ
                      gsr' gsr nil nil nil nil ws ws' eq_refl eq_refl I eq_refl eq_refl K1 K2 K3
                      (tele_prefix_rel_nil _) (tele_prefix_rel_nil _) (tele_prefix_rel_nil _)
                      Hca (proj2 Hnr) HcaQ (proj2 HnrQ) HnwA HnwB) as Htops.
        cbn [nonrec_arg_vals List.app] in Htops.
        (** The fields one by one. *)
        assert (HinQ : forall t0, In (ca_rec t0) gsr ->
                   forall Mt, ind_member D (ptyp_mem t0) = Some Mt -> im_is_rview Mt = true -> ptyp_mem t0 < j).
        { intros t0 Hin Mt HMt HrT.
          destruct (List.in_split _ _ Hin) as (gs1 & gs2 & Egs1).
          exact (rview_struct_order _ _ _ Hrs _ _ _ _ _ _ _ _ _ _ _ HMj Hh0 Hcs Egs1 HMt HrT). }
        assert (Efl : List.map (leaf_in D' (pt_self j' Ps')) (shape_leaves (rv_leaves D) 0 (pt_self j Ps)) = cargs_leaf_in D D' gsr' gsr)
          by exact (rview_leaf_in D D' vm j' Mj' qr Is' fl gsr' j Mj Is0 gsr Ps' Ps Hlc HMj' Hh' Hcs' Hlen' Hnd HMj Hh0 Hcs Hlen Hcorr).
        change (List.map leaf_mem (shape_leaves (rv_leaves D) 0 (pt_self j Ps))) with (shape_mems D (pt_self j Ps)) in Hfl.
        rewrite Efl, (shape_mems_rview _ _ _ _ _ _ _ _ _ Hlc HMj Hh0 Hcs ltac:(lia)) in Hfl.
        assert (Tb0' : ⟦ihtys ws' of gsr at p u0 under C1 AsB ⟧ gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ nil) ↘ tys')
          by (rewrite List.app_nil_r; exact Tb0).
        destruct (cross_fields_walk _ (fun t' t HQt => IHn j Hrk t' t HQt) gsr' gsr ws ws' j j' nil nil nil fs tys' rs' HinQ Hcorr
                    Hca Htops Hfl Tb0' Rb0)
          as [tyA resA Ta Ra Lta Lra Hrel].
        rewrite List.app_nil_r in Ta.
        apply (mk_cross_ih_out _ _ _ _ _ _ _ _ _ tyA tys' resA rs').
        * eapply eval_ihty_rview; [ exact Hq | exact HMj' | exact Hh' | exact Hcs' | exact Ew | exact Ta ].
        * eapply eval_ihty_rview; [ exact Hl | exact HMj | exact Hh0 | exact Hcs | exact Ew' | exact Tb0 ].
        * eapply eval_ih_rview; [ exact Hq | exact HMj' | exact Hh' | exact Hcs' | exact Ew | exact Ra ].
        * eapply eval_ih_rview; [ exact Hl | exact HMj | exact Hh0 | exact Hcs | exact Ew' | exact Rb0 ].
        * rewrite Lta; symmetry; exact (length_shape_leaves_rview _ _ _ _ _ _ _ _ _ _ HlcQ HMj' Hh' Hcs' ltac:(lia)).
        * rewrite (length_shape_leaves_rview _ _ _ _ _ _ _ _ _ _ Hlc HMj Hh0 Hcs ltac:(lia)).
          exact (proj2 (proj2 eval_ihty_length_all _ _ _ _ _ _ _ _ Tb0 D Hl Hlc)).
        * rewrite Lra; symmetry; exact (length_shape_leaves_rview _ _ _ _ _ _ _ _ _ _ HlcQ HMj' Hh' Hcs' ltac:(lia)).
        * rewrite (length_shape_leaves_rview _ _ _ _ _ _ _ _ _ _ Hlc HMj Hh0 Hcs ltac:(lia)).
          exact (proj2 (proj1 eval_ih_length_all _ _ _ _ _ _ _ Rb0 D Hl Hlc)).
        * intros oA oB Hclr; rewrite Efl in Hclr.
          eapply cross_result_rview; [ exact HMj' | exact Hh' | exact Hcs' | exact HMj | exact Hh0 | exact Hcs
                                    | exact Ew | exact Ew' | exact (Hrel _ _ Hclr) ].
      + (** Members with a block: one path. *)
        assert (Hrv' : im_is_rview Mj' = false) by congruence.
        destruct HnA as (aA & eA & ->); destruct HnB as (aB & eB & ->).
        destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrg) as (bs & bs' & Eb & Eb' & _ & _ & Hi).
        destruct (rec_arg_self_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HrQ) as (bsQ & bsQ' & EbQ & EbQ' & _ & _ & HiQ).
        pose proof (functional_eval_exps' _ _ _ _ EbQ EbQ') as <-.
        inversion Hi as [| jx Mx hd k0 nsx nsx' as1 as2 ex ex' ux ux' HMx Hrvx Hr Hn L1 L2 Hs1 Hs2 He |]; subst;
          [| exfalso; match goal with H1 : ind_member D j = Some ?M1, H2 : im_head ?M1 = mh_record _ _ _ |- _ =>
                rewrite HMj in H1; injection H1 as <-; exact (not_rview_record _ _ _ _ Hrv H2) end ].
        rewrite HMj in HMx; injection HMx as <-.
        inversion HiQ as [| jy My hdy ky nsy nsy' as1' as2' ey ey' uy uy' HMy Hrvy Hry Hny L1' L2' HsQ HsQ' HeQ |]; subst;
          [| exfalso; match goal with H1 : ind_member D' j' = Some ?M1, H2 : im_head ?M1 = mh_record _ _ _ |- _ =>
                rewrite HMj' in H1; injection H1 as <-; exact (not_rview_record _ _ _ _ Hrv' H2) end ].
        rewrite HMj' in HMy; injection HMy as <-.
        pose proof (view_member_unu _ _ _ _ _ _ _ _ _ Hvmb Hrv') as Hunu.
        pose proof (cross_nparams_transfer j' Mj' j Mj Hsc HMj' HMj _ _ HsQ) as HsQt.
        rewrite <- Hunu in HsQt.
        pose proof (ttrans _ _ HMj _ _ _ Hs1 (tsym _ _ HMj _ _ HsQt)) as Hpa.
        pose proof (nparams_rel_refl_r p D u0 _ _ _ Hass HnP HnI HaP HaI HdP HdI _ _ HMj _ _ Hn) as Hbb'.
        pose proof (ind_rel_idx p D u0 nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HMj Hi Hpa Hbb') as Hm.
        destruct (HbB _ _ HMj' Hrv') as [bb Hbb]; destruct (HBks _ _ HMj Hrv) as [ba Hba].
        destruct (Hmot_x j' Mj' j bb ba u0 u0 bsQ bs' _ _ HMj' Hrv' Hsc Hbb Hba Hm) as (a1 & a2 & Ea1 & Ea2 & HR).
        destruct (cross_neut_evals j' j Mj hd k0 as1 as2 eA eB u0 u0 bs bs' Hsc HMj Hrv Hi) as (r1 & r2 & Er1 & Er2).
        assert (Lg : List.length (shape_leaves (rv_leaves D) 0 (pt_self j Ps)) = 1)
          by (cbn [shape_leaves]; rewrite (rv_leaves_not_rview _ _ _ HMj Hrv); reflexivity).
        assert (Lc : List.length (shape_leaves (rv_leaves D') 0 (pt_self j' Ps')) = 1)
          by (cbn [shape_leaves]; rewrite (rv_leaves_not_rview _ _ _ HMj' Hrv'); reflexivity).
        apply (mk_cross_ih_out _ _ _ _ _ _ _ _ _ (a1 :: nil) (a2 :: nil) (r1 :: nil) (r2 :: nil)).
        * eapply eval_ihty_self; [ exact Hq | exact HMj' | exact Hrv' | exact EbQ | unfold AsA; rewrite (nth_blocks_motives _ _ _ Hbb); exact Ea1 ].
        * eapply eval_ihty_self; [ exact Hl | exact HMj | exact Hrv | exact Eb' | unfold AsB; rewrite (nth_blocks_motives _ _ _ Hba); exact Ea2 ].
        * eapply eval_ih_self; [ exact Hq | exact HMj' | exact Hrv' | exact Er1 ].
        * eapply eval_ih_self; [ exact Hl | exact HMj | exact Hrv | exact Er2 ].
        * rewrite Lc; reflexivity.
        * rewrite Lg; reflexivity.
        * rewrite Lc; reflexivity.
        * rewrite Lg; reflexivity.
        * intros oA oB Hclr.
          cbn [shape_leaves] in Hclr, Hfl; rewrite (rv_leaves_not_rview _ _ _ HMj Hrv) in Hclr, Hfl.
          cbn [List.map leaf_in leaf_mem] in Hclr, Hfl; rewrite HMj', Hrv' in Hclr, Hfl; cbn [negb] in Hclr, Hfl.
          inversion Hclr; subst;
            match goal with H0 : cross_leaf_results nil _ nil nil nil nil ?o1 ?o2 |- _ => inversion H0; subst end.
          -- (** A fresh variable: at the motive's relation. *)
             eapply cross_result_self; [ exact HMj' | exact Hrv' | exact HMj | exact Hrv | exact Eb | exact Eb' |].
             apply (proj1 (SE self_motive_move j Mj u0 u0 bsQ bs' _ _ bs bs' HMj Hrv Hm (tsym _ _ HMj _ _ Hpa) Hbb' _ _)).
             lazymatch goal with |- _ (⇑ _ ?x) (⇑ _ ?y) =>
               match goal with Hb0 : per_bot x y |- _ => exact (per_bot_then_per_elem HR Hb0) end end.
          -- (** The eliminators, at a member of lower rank. *)
             inversion Hfl as [| | ? ? ? ? Hbot _ |]; subst.
             pose proof (XE cross_neut_elim j' j Mj hd k0 as1 as2 eA eB u0 u0 bs bs' Hsc HMj Hrv Hi
                           (Hbot j' Mj hd k0 as1 as2 eA eB u0 u0 bs bs' Hsc HMj Hrv Hi)) as Hcm.
             inversion Hcm; subst;
               [| exfalso; match goal with H1 : ind_member D' j' = Some ?M1, H2 : im_head ?M1 = mh_record _ _ _ |- _ =>
                    rewrite HMj' in H1; injection H1 as <-; exact (not_rview_record _ _ _ _ Hrv' H2) end ].
             repeat match goal with
                    | E1 : eval_elim _ _ ρb qc ub VBb j' _ ?x1 |- _ =>
                        tryif constr_eq x1 r1 then fail
                        else (assert (x1 = r1) by (eapply functional_eval_elim; eassumption); subst x1)
                    | E2 : eval_elim _ _ C1 p u0 Bks j _ ?x2 |- _ =>
                        tryif constr_eq x2 r2 then fail
                        else (assert (x2 = r2) by (eapply functional_eval_elim; eassumption); subst x2)
                    end.
             eapply cross_result_self; [ exact HMj' | exact Hrv' | exact HMj | exact Hrv | exact Eb | exact Eb' | eassumption ].
    - (** Through a domain. *)
      inversion Hd as [| ? ? ? ? ? ? ? bA bB EbA EbB Hstep]; subst.
      assert (Ecs : List.map (leaf_in D' (pt_pi B' t1')) (shape_leaves (rv_leaves D) 0 (pt_pi B t1))
                    = List.map (leaf_in D' t1') (shape_leaves (rv_leaves D) 0 t1))
        by (cbn [shape_leaves]; rewrite List.map_map; exact (leaf_in_shape_leaves D' (rv_leaves D) t1 t1' 1 0)).
      change (List.map leaf_mem (shape_leaves (rv_leaves D) 0 (pt_pi B t1))) with (shape_mems D (pt_pi B t1)) in Hfl.
      rewrite shape_mems_pi, Ecs in Hfl; unfold shape_mems in Hfl.
      set (N' := List.length (shape_leaves (rv_leaves D') 0 t1')).
      set (N := List.length (shape_leaves (rv_leaves D) 0 t1)).
      assert (LN' : List.length (shape_leaves (rv_leaves D') 0 (pt_pi B' t1')) = N')
        by (cbn [shape_leaves]; rewrite List.length_map; apply length_shape_leaves).
      assert (LN : List.length (shape_leaves (rv_leaves D) 0 (pt_pi B t1)) = N)
        by (cbn [shape_leaves]; rewrite List.length_map; apply length_shape_leaves).
      apply (mk_cross_ih_out _ _ _ _ _ _ _ _ _
        (List.map (fun i => Πᵈ bA (nil ↦ d_ihfam ρb AsA qc ub (env_args nil (ub ++ preQ)) t1' i vA) fam_cod) (List.seq 0 N'))
        (List.map (fun i => Πᵈ bB (nil ↦ d_ihfam C1 AsB p u0 (env_args nil (u0 ++ pre')) t1 i vB) fam_cod) (List.seq 0 N))
        (List.map (fun i => d_ihfn ρb VBb qc ub t1' i vA) (List.seq 0 N'))
        (List.map (fun i => d_ihfn C1 Bks p u0 t1 i vB) (List.seq 0 N))).
      + eapply eval_ihty_pi; [ exact Hq | exact EbA ].
      + eapply eval_ihty_pi; [ exact Hl | exact EbB ].
      + eapply eval_ih_pi; exact Hq.
      + eapply eval_ih_pi; exact Hl.
      + rewrite LN', List.length_map, List.length_seq; reflexivity.
      + rewrite LN, List.length_map, List.length_seq; reflexivity.
      + rewrite LN', List.length_map, List.length_seq; reflexivity.
      + rewrite LN, List.length_map, List.length_seq; reflexivity.
      + (** At related arguments: the rest's results, at the functions'
            values there. *)
        intros oA oB Hclr; rewrite Ecs in Hclr.
        apply cross_result_pi; intros c c' Hcc.
        destruct (Hstep c c' Hcc) as [Htop Hcan Hd1].
        destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrg c c' Hcc) as (fc & fc' & Ef & Ef' & Hrg1).
        destruct (rec_arg_pi_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HrQ c c Hcan) as (fq & fq' & Eq & Eq' & HrQ1).
        pose proof (functional_eval_app _ _ _ _ Ef Eq) as <-; pose proof (functional_eval_app _ _ _ _ Ef Eq') as <-.
        rewrite <- env_args_snoc, <- List.app_assoc in Hd1.
        destruct (IHt t1 Hrk k kQ (pre ++ c :: nil) (pre' ++ c' :: nil) (preQ ++ c :: nil) fc fc' fs Hsc Hrg1 HrQ1 Hd1
                    (is_neut_app _ _ _ Ef HnA) (is_neut_app _ _ _ Ef' HnB) Hfl)
          as [tyc tyc' rc rc' Tc Tc' Rc Rc' Lc1 Lc2 Lc3 Lc4 Hrc].
        rewrite List.app_assoc, env_args_snoc in Tc, Tc'.
        destruct (cross_leaf_results_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c c' fc fc' tyc tyc' rc rc'
                    Hclr Ef Ef' Tc Tc' Rc Rc'
                    ltac:(intros x Hx; apply List.in_seq in Hx; unfold N' in Hx; lia)
                    ltac:(intros x Hx; apply List.in_seq in Hx; unfold N in Hx; lia) Htop)
          as (oc & oc' & F1 & F2 & Hoc).
        replace N' with (List.length tyc) in Hoc at 1 by lia.
        rewrite map_nth_seq_all in Hoc.
        replace N with (List.length tyc') in Hoc at 1 by lia.
        rewrite map_nth_seq_all in Hoc.
        replace N' with (List.length rc) in Hoc at 1 by lia.
        rewrite map_nth_seq_all in Hoc.
        replace N with (List.length rc') in Hoc at 1 by lia.
        rewrite map_nth_seq_all in Hoc.
        econstructor; [ exact Ef | exact Ef' | exact F1 | exact F2 | exact (Hrc _ _ Hoc) ].
  Qed.

  (** The container's flags along its own paths: those along the group's
      paths the container has. *)
  Lemma cross_container_flags : forall X t'' t' t, shape_corr vm t' t ->
      List.map (leaf_in X t'') (shape_leaves (rv_leaves D') 0 t')
      = sel_flags (List.map (leaf_in D' t') (shape_leaves (rv_leaves D) 0 t)) (List.map (leaf_in X t'') (shape_leaves (rv_leaves D) 0 t)).
  Proof.
    intros X t'' t' t Hsc.
    rewrite sel_flags_map.
    assert (Hsk : forall ls, List.map (leaf_in X t'') ls = List.map (leaf_in X t'') (List.map leaf_skel ls))
      by (intros ls; rewrite List.map_map; apply List.map_ext; intros l; rewrite leaf_in_skel; reflexivity).
    rewrite (Hsk (shape_leaves (rv_leaves D') 0 t')), (Hsk (List.filter _ _)).
    rewrite (leaves_view_skel p qc D D' vm Hlc HlcQ Hrs HrsQ cross_view_members (S (ptyp_mem t)) t' t 0 0
               ltac:(intros; lia) Hsc); reflexivity.
  Qed.

  (** The eliminators' results at every path. *)
  Lemma cross_leaf_results_all_nest : forall cs A B R S, List.length A = marked cs -> List.length R = marked cs ->
      List.length B = List.length cs -> List.length S = List.length cs ->
      cross_leaf_results cs (List.map (fun _ => false) cs) A B R S R S.
  Proof.
    induction cs as [| [|] cs IH]; intros A B R S LA LR LB LS; unfold marked in *; cbn in LA, LR, LB, LS |- *.
    - destruct A, B, R, S; cbn in *; try discriminate; constructor.
    - destruct A, B, R, S; cbn in *; try discriminate; constructor; apply IH; unfold marked; lia.
    - destruct B, S; cbn in *; try discriminate; constructor; apply IH; unfold marked; lia.
  Qed.

  (** *** The Recursive Results of a Branch

      The arguments [vA] of a container's constructor (kinds [gA]) and
      [vB] of the group's (kinds [gB]), of kinds [gq] in the group read
      [Dc]: the fresh recursive results on each side along the paths [Dc]
      has, the wrapped results the branches are read under, and those
      related as [cross_fields_rel] has them. *)
  #[warnings="-cannot-define-projection"]
  Record cross_wrapped (Dc : ind_decl) (k : nat) (pre pre' preQ : list domain) (gq gA gB : list carg) (vA vB : list domain)
      (s2 : nat) : Prop := mk_cross_wrapped
    { (** The container's fresh recursive results *)
      cross_wrapped_ihsA : list domain
      (** The group's fresh recursive results *)
    ; cross_wrapped_ihsB : list domain
      (** The container's wrapped results *)
    ; cross_wrapped_wA : list domain
      (** The group's wrapped results *)
    ; cross_wrapped_wB : list domain
      (** The container's fresh results *)
    ; cross_wrapped_fresh_a : Fihs vA at gq gA of Dc under ρb AsA at qc ub in gc_deps ⍮ gc_stack ⍮ env_args nil (ub ++ preQ)
        ⍮ s2 ↘ cross_wrapped_ihsA
      (** The group's fresh results *)
    ; cross_wrapped_fresh_b : Fihs vB at gq gB of Dc under C1 AsB at p u0 in gc_deps ⍮ gc_stack ⍮ env_args nil (u0 ++ pre')
        ⍮ s2 ↘ cross_wrapped_ihsB
      (** As many on each side *)
    ; cross_wrapped_len : List.length cross_wrapped_ihsA = List.length cross_wrapped_ihsB
      (** The container's wrapped results, from them *)
    ; cross_wrapped_wrap_a : ⟦wihs vA of gq gA of Dc with cross_wrapped_ihsA under qc ub VBb ⟧ gc_deps ⍮ gc_stack ⍮ ρb
        ↘ cross_wrapped_wA
      (** The group's wrapped results, from them *)
    ; cross_wrapped_wrap_b : ⟦wihs vB of gq gB of Dc with cross_wrapped_ihsB under p u0 Bks ⟧ gc_deps ⍮ gc_stack ⍮ C1
        ↘ cross_wrapped_wB
      (** The wrapped results are related *)
    ; cross_wrapped_related : cross_fields_rel D D' dr Rel C1 p u0 Bks k u0 u0 pre pre' gA gB vA vB
        cross_wrapped_wA cross_wrapped_wB }.

  Lemma cross_wrapped_results : forall (rk : nat -> nat) r, view_rank_ok gc_deps gc_stack D rk ->
      (forall j', rk j' < r -> cross_bot j') ->
      forall Dc k kQ gq gA gB vA vB pre pre' preQ s2,
        cargs_kinds gq gA -> cargs_corr vm gA gB -> cargs_nest_ok D Dc rk r gq gB -> cargs_leaf_mono Dc D' gq gA ->
        con_args_rel p D (okr_at D u0 nr) nr ar dr k u0 u0 pre pre' gB vA vB ->
        cross_tops qc D' ub u0 dr kQ k pre preQ pre' gA gB vA vB ->
        cross_wrapped Dc k pre pre' preQ gq gA gB vA vB s2.
  Proof.
    intros rk r Hrk HIH Dc k kQ.
    induction gq as [| g' gq IH]; intros [| gA0 gA] [| gB0 gB] vA vB pre pre' preQ s2 Hk Hco Hno Hmo Hca Ht;
      cbn in Hk, Hco; try contradiction;
      try (destruct g'; cbn in Hk; contradiction); try (destruct gA0; cbn in Hk, Hco; contradiction).
    - inversion Ht; subst.
      apply (mk_cross_wrapped _ _ _ _ _ _ _ _ _ _ _ nil nil nil nil); first [ reflexivity | constructor ].
    - destruct g' as [T' | t''], gA0 as [A' | t'], gB0 as [A | t]; cbn in Hk, Hco, Hno, Hmo; try contradiction.
      + (** Non-recursive throughout. *)
        inversion Ht; subst.
        match goal with Ht' : cross_tops _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Ht' into Ht0 end.
        inversion Hca; subst.
        match goal with Hc' : con_args_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hc' into Hca0 end.
        destruct (IH gA gB _ _ _ _ _ s2 Hk Hco Hno Hmo Hca0 Ht0) as [ihsA ihsB wA wB IA IB Li WA WB HR].
        apply (mk_cross_wrapped _ _ _ _ _ _ _ _ _ _ _ ihsA ihsB wA wB).
        * apply fresh_ihs_arg; rewrite <- env_args_snoc, <- List.app_assoc; exact IA.
        * apply fresh_ihs_arg; rewrite <- env_args_snoc, <- List.app_assoc; exact IB.
        * exact Li.
        * apply wrap_ihs_eval_arg; exact WA.
        * apply wrap_ihs_eval_arg; exact WB.
        * apply cross_fields_arg; exact HR.
      + (** Nested through by the group only: the group's eliminator at
            its argument. *)
        inversion Ht; subst.
        match goal with Ht' : cross_tops _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Ht' into Ht0 end.
        inversion Hca; subst.
        match goal with Hr' : rec_arg_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _, Hc' : con_args_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          rename Hr' into Hrr; rename Hc' into Hca0 end.
        destruct (proj1 (proj2 (proj2 (SE self_elim_all))) _ _ _ _ _ _ _ _ Hrr) as (ih0 & ih & _ & Ih & _).
        destruct Hno as [_ Hno].
        destruct (IH gA gB _ _ _ _ _ s2 Hk Hco Hno Hmo Hca0 Ht0) as [ihsA ihsB wA wB IA IB Li WA WB HR].
        apply (mk_cross_wrapped _ _ _ _ _ _ _ _ _ _ _ ihsA ihsB wA (ih ++ wB)).
        * apply fresh_ihs_arg; rewrite <- env_args_snoc, <- List.app_assoc; exact IA.
        * apply fresh_ihs_nest; exact IB.
        * exact Li.
        * apply wrap_ihs_eval_arg; exact WA.
        * eapply wrap_ihs_eval_nest; [ exact Ih | exact WB ].
        * eapply cross_fields_nest; [ exact Ih | exact HR ].
      + (** Nested through by both: the eliminators, at members of lower
            rank. *)
        inversion Ht; subst.
        match goal with Ht' : cross_tops _ _ _ _ _ _ _ _ _ _ _ _ _ _, HrQ' : rec_arg_rel qc _ _ _ _ _ _ _ _ _ _ _ _ _,
                        Hd' : cross_doms _ _ _ _ _ _ _ _ |- _ =>
          rename Ht' into Ht0; rename HrQ' into HrQ; rename Hd' into Hdoms end.
        match goal with Hn1 : is_neut ?a1, Hn2 : is_neut ?a2 |- _ => rename Hn1 into HnA; rename Hn2 into HnB end.
        inversion Hca; subst.
        match goal with Hr' : rec_arg_rel p _ _ _ _ _ _ _ _ _ _ _ _ _, Hc' : con_args_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          rename Hr' into Hrr; rename Hc' into Hca0 end.
        destruct Hco as (Hmt & Hdp & Hco); destruct Hno as [Hlt Hno].
        pose proof (shape_corr_of _ _ _ Hmt Hdp) as Hsc.
        set (ls := shape_leaves (rv_leaves D) 0 t) in *.
        assert (Hfl : cross_flags_ok cross_bot (List.map (leaf_in D' t') ls) (List.map (fun _ => false) (List.map (leaf_in D' t') ls))
                        (List.map leaf_mem ls)).
        { rewrite List.map_map.
          apply (cross_flags_ok_of cross_bot (leaf_in D' t') (fun _ => false) ls); [ intros; discriminate |].
          intros l Hin _ _; apply HIH.
          pose proof (leaf_mem_rank p D u0 nr ar dr Hl Hass HnP HnI HaP HaI HdP HdI
                        (vg_adm p D Hvg u0 u0 u0_gargs' u0_len' u0_gargs') rk Hrk t 0 l Hin) as Hle; lia. }
        destruct (cross_leaves (S (ptyp_mem t)) t' t ltac:(intros; lia) k kQ pre pre' preQ _ _ _ Hsc Hrr HrQ Hdoms HnA HnB Hfl)
          as [tyA tyB resA resB Ta Tb Ra Rb Lta Ltb Lra Lrb Hrel].
        destruct (IH gA gB _ _ _ _ _ s2 Hk Hco Hno Hmo Hca0 Ht0) as [ihsA ihsB wA wB IA IB Li WA WB HR].
        apply (mk_cross_wrapped _ _ _ _ _ _ _ _ _ _ _ ihsA ihsB (resA ++ wA) (resB ++ wB)).
        * apply fresh_ihs_nest; exact IA.
        * apply fresh_ihs_nest; exact IB.
        * exact Li.
        * eapply wrap_ihs_eval_nest; [ exact Ra | exact WA ].
        * eapply wrap_ihs_eval_nest; [ exact Rb | exact WB ].
        * eapply cross_fields_rec; [ | exact Lrb | | exact HR ].
          -- rewrite Lra, <- (cross_marked _ _ Hsc); unfold marked, leaves_in_count, ls.
             clear; induction (shape_leaves (rv_leaves D) 0 t) as [| l ls IH]; cbn; [ reflexivity |].
             destruct (leaf_in D' t' l); cbn; rewrite IH; reflexivity.
          -- apply Hrel, cross_leaf_results_all_nest;
               [ rewrite Lta; symmetry; exact (cross_marked _ _ Hsc) | rewrite Lra; symmetry; exact (cross_marked _ _ Hsc)
               | rewrite Ltb, List.length_map; reflexivity | rewrite Lrb, List.length_map; reflexivity ].
      + (** Recursive throughout: the fresh recursive results along the
            paths the group read has. *)
        inversion Ht; subst.
        match goal with Ht' : cross_tops _ _ _ _ _ _ _ _ _ _ _ _ _ _, HrQ' : rec_arg_rel qc _ _ _ _ _ _ _ _ _ _ _ _ _,
                        Hd' : cross_doms _ _ _ _ _ _ _ _ |- _ =>
          rename Ht' into Ht0; rename HrQ' into HrQ; rename Hd' into Hdoms end.
        match goal with Hn1 : is_neut ?a1, Hn2 : is_neut ?a2 |- _ => rename Hn1 into HnA; rename Hn2 into HnB end.
        inversion Hca; subst.
        match goal with Hr' : rec_arg_rel p _ _ _ _ _ _ _ _ _ _ _ _ _, Hc' : con_args_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          rename Hr' into Hrr; rename Hc' into Hca0 end.
        destruct Hco as (Hmt & Hdp & Hco); destruct Hno as [Hnl Hno]; destruct Hmo as [Hmono Hmo].
        pose proof (shape_corr_of _ _ _ Hmt Hdp) as Hsc.
        set (ls := shape_leaves (rv_leaves D) 0 t) in *.
        set (fs := List.map (leaf_in Dc t'') ls).
        assert (Hfl : cross_flags_ok cross_bot (List.map (leaf_in D' t') ls) fs (List.map leaf_mem ls)).
        { apply (cross_flags_ok_of cross_bot (leaf_in D' t') (leaf_in Dc t'') ls).
          - intros l _ Hf; exact (Hmono l Hf).
          - intros l Hin _ Hf; apply HIH; exact (Hnl l Hin Hf). }
        destruct (cross_leaves (S (ptyp_mem t)) t' t ltac:(intros; lia) k kQ pre pre' preQ _ _ _ Hsc Hrr HrQ Hdoms HnA HnB Hfl)
          as [tyA tyB resA resB Ta Tb Ra Rb Lta Ltb Lra Lrb Hrel].
        destruct (fresh_cross_results _ _ _ _ Hfl tyA tyB resA resB s2
                    ltac:(rewrite Lta; symmetry; exact (cross_marked _ _ Hsc)) ltac:(rewrite Lra; symmetry; exact (cross_marked _ _ Hsc))
                    ltac:(rewrite Ltb, List.length_map; reflexivity) ltac:(rewrite Lrb, List.length_map; reflexivity))
          as [i1 i2 o1 o2 F1 F2 Li12 W1 W2 Ho].
        destruct (IH gA gB _ _ _ _ _ (List.length i1 + s2) Hk Hco Hno Hmo Hca0 Ht0) as [ihsA ihsB wA wB IA IB Li WA WB HR].
        assert (Hfeq : sel_flags (List.map (leaf_in D' t') ls) fs = List.map (leaf_in Dc t'') (shape_leaves (rv_leaves D') 0 t'))
          by (unfold fs, ls; symmetry; exact (cross_container_flags Dc t'' t' t Hsc)).
        rewrite Hfeq in F1, W1.
        apply (mk_cross_wrapped _ _ _ _ _ _ _ _ _ _ _ (i1 ++ ihsA) (i2 ++ ihsB) (o1 ++ wA) (o2 ++ wB)).
        * eapply fresh_ihs_rec; [ exact Hq | exact Ta | exact F1 | exact IA ].
        * eapply fresh_ihs_rec; [ exact Hl | exact Tb | exact F2 | rewrite <- Li12; exact IB ].
        * rewrite !List.length_app; lia.
        * eapply wrap_ihs_eval_rec; [ exact Hq | exact Ra | exact (W1 ihsA) | exact WA ].
        * eapply wrap_ihs_eval_rec; [ exact Hl | exact Rb | exact (W2 ihsB) | exact WB ].
        * destruct (cross_leaf_results_length _ _ _ _ _ _ _ _ Ho) as [Lo1 Lo2].
          eapply cross_fields_rec; [ | | exact (Hrel _ _ Ho) | exact HR ].
          -- rewrite Lo1; unfold ls; rewrite (cross_marked _ _ Hsc).
             rewrite <- (leaves_in_count_view p qc D D' vm Hlc HlcQ Hrs HrsQ cross_view_members (S (ptyp_mem t)) t' t 0
                           ltac:(intros; lia) Hsc); reflexivity.
          -- rewrite Lo2, List.length_map; reflexivity.
  Qed.

  (** *** A Block

      A block of the two stuck eliminators, the one of the member [Mn] of
      the group read [Dc]: the container's member [a] its selection [sela]
      gives, the group's member [b] [selb] gives, [b] the member the view
      takes [a] to, both with a block; [Mn]'s constructors are [a]'s, their
      arguments of kinds compatible with [a]'s, the paths [Dc] has the
      container's, and nested through by [b] only at members of rank below
      [r]; the two members' types at a common reference. *)
  #[warnings="-cannot-define-projection"]
  Record cross_block_site (rk : nat -> nat) (r : nat) (Dc : ind_decl) (sela selb : option (list nat)) (n : nat) (Mn : imember)
      : Prop := mk_cross_block_site
    { (** The container's member index *)
      cross_block_site_a : nat
      (** The container's member *)
    ; cross_block_site_Ma : imember
      (** The group's member index *)
    ; cross_block_site_b : nat
      (** The group's member *)
    ; cross_block_site_Mb : imember
      (** The common reference's group *)
    ; cross_block_site_hd : qname
      (** The common reference's member *)
    ; cross_block_site_k : nat
      (** The container side's uniform parameters at the reference *)
    ; cross_block_site_prea : list domain
      (** The group side's uniform parameters at the reference *)
    ; cross_block_site_preb : list domain
      (** [sela] gives [a] *)
    ; cross_block_site_src_a : elim_src sela n = cross_block_site_a
      (** [selb] gives [b] *)
    ; cross_block_site_src_b : elim_src selb n = cross_block_site_b
      (** The view takes [a] to [b] *)
    ; cross_block_site_in_view_map : List.nth_error vm cross_block_site_a = Some cross_block_site_b
      (** [a] is a member of the container *)
    ; cross_block_site_member_a : ind_member D' cross_block_site_a = Some cross_block_site_Ma
      (** [a] has a block *)
    ; cross_block_site_rv_a : im_is_rview cross_block_site_Ma = false
      (** [b] is a member of the group *)
    ; cross_block_site_member_b : ind_member D cross_block_site_b = Some cross_block_site_Mb
      (** [b] has a block *)
    ; cross_block_site_rv_b : im_is_rview cross_block_site_Mb = false
      (** [Mn] has [a]'s non-uniform parameter count *)
    ; cross_block_site_nn : im_nn Mn = im_nn cross_block_site_Ma
      (** [Mn]'s constructors are [a]'s *)
    ; cross_block_site_names : List.map fst (im_cons Mn) = List.map fst (im_cons cross_block_site_Ma)
      (** Their argument kinds are compatible with [a]'s *)
    ; cross_block_site_kinds : forall c gq gA, In (c, gq) (im_cons Mn) -> ind_con cross_block_site_Ma c = Some gA -> cargs_kinds gq gA
      (** The paths [Dc] has are [a]'s *)
    ; cross_block_site_mono : forall c gq gA, In (c, gq) (im_cons Mn) -> ind_con cross_block_site_Ma c = Some gA ->
        cargs_leaf_mono Dc D' gq gA
      (** [b] nests through only at members of rank below [r] *)
    ; cross_block_site_nest : forall c gq gB, In (c, gq) (im_cons Mn) -> ind_con cross_block_site_Mb c = Some gB ->
        cargs_nest_ok D Dc rk r gq gB
      (** The container's paths [Dc] has are as many as [Dc]'s branch binds *)
    ; cross_block_site_count_a : forall c gq gA, In (c, gq) (im_cons Mn) -> ind_con cross_block_site_Ma c = Some gA ->
        cargs_nin D' Dc gq gA = cargs_nrec Dc gq
      (** So are the group's *)
    ; cross_block_site_count_b : forall c gq gB, In (c, gq) (im_cons Mn) -> ind_con cross_block_site_Mb c = Some gB ->
        cargs_nin D Dc gq gB = cargs_nrec Dc gq
      (** [a]'s type at [ub] is at the reference *)
    ; cross_block_site_ref_a : ⟦mref cross_block_site_a of qc ub ⟧ gc_deps ⍮ gc_stack ↘ (cross_block_site_hd, cross_block_site_k, cross_block_site_prea)
      (** [b]'s type at [u0] is at the reference *)
    ; cross_block_site_ref_b : ⟦mref cross_block_site_b of p u0 ⟧ gc_deps ⍮ gc_stack ↘ (cross_block_site_hd, cross_block_site_k, cross_block_site_preb) }.

  Lemma cross_block_read : forall (rk : nat -> nat) r, view_rank_ok gc_deps gc_stack D rk -> (forall j', rk j' < r -> cross_bot j') ->
      forall s Dc sela selb n Mn, cross_block_site rk r Dc sela selb n Mn ->
        block_read_pair qc D' ub VBb ρb p D u0 Bks C1 s Dc sela selb n Mn.
  Proof.
    intros rk r Hrk HIH s Dc sela selb n Mn
      [a Ma b Mb hd k prea preb Hsa Hsb Hvab HMa HrvA HMb HrvB Hnn Hnames Hkinds Hmono Hnest Hcnta Hcntb Ra Rb].
    pose proof (length_cups p D Hvg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups) as Hlcu.
    assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
    pose proof (uparams_refl_l D' (valid_group_valid _ _ HgQ) (valid_group_closed _ _ HgQ) _ _ Hub) as Hubub.
    destruct (cross_view_members a b Hvab) as (Ma0 & Mb0 & HMa0 & Hvmb).
    rewrite HMa in HMa0; injection HMa0 as <-.
    pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMb0; rewrite HMb in HMb0; injection HMb0 as <-.
    destruct (mref_ref_len qc D' a Ma ub hd k prea Hq HMa Hlb Ra) as [Hra Hla].
    destruct (mref_ref_len p D b Mb u0 hd k preb Hl HMb u0_len' Rb) as [Hrb Hlb'].
    pose proof (view_member_unu _ _ _ _ _ _ _ _ _ Hvmb HrvA) as Hunu.
    pose proof (view_member_nn _ _ _ _ _ _ _ _ _ Hvmb) as Hnn'.
    pose proof (view_member_names _ _ _ _ _ _ _ _ _ Hvmb) as HnamesAB.
    destruct (HbB _ _ HMa HrvA) as [blA HblA]; destruct (HBks _ _ HMb HrvB) as [blB HblB].
    destruct (fresh_nparams_exist qc D' HgQ ub Hubub Hlb a Ma s HMa) as (nsA & FnsA & HnsA).
    destruct (fresh_nparams_exist p D Hvg u0 u0_gargs' u0_len' b Mb s HMb) as (nsB & FnsB & _).
    pose proof (CF cross_fresh_nparams a Ma b Mb HMa Hvab HMb s nsA nsB FnsA FnsB) as Hcp.
    pose proof Hcp as [Hns HpA HpC HpG].
    pose proof (nparams_rel_refl_l p D u0 _ _ _ Hass HnP HnI HaP HaI HdP HdI _ _ HMb _ _ Hns) as HAA.
    pose proof (nparams_rel_refl_r p D u0 _ _ _ Hass HnP HnI HaP HaI HdP HdI _ _ HMb _ _ Hns) as HBB.
    pose proof Hns as Hns0; rewrite tele_rel_iff in Hns0; destruct Hns0 as (LnA & LnB & _).
    rewrite List.length_rev, length_im_nparams in LnA, LnB.
    assert (Lpa : List.length prea = im_unu D Mb) by lia.
    (** The motives at the fresh neutral. *)
    assert (Hneu : G b u0 u0 nsA nsB (⇑! (d_ind hd k (prea ++ nsA)) (s + im_nn Mn)) (⇑! (d_ind hd k (preb ++ nsB)) (s + im_nn Mn))).
    { eapply ind_rel_neut; [ exact HMb | exact HrvB | exact Hrb | exact Hns | | | | | exact var_per_bot ].
      - rewrite List.length_app; lia.
      - rewrite List.length_app; lia.
      - rewrite skipn_app_exact by exact Lpa; exact HAA.
      - rewrite skipn_app_exact by exact Hlb'; exact HBB. }
    destruct (Hmot_x a Ma b blA blB u0 u0 nsA nsB _ _ HMa HrvA Hvab HblA HblB Hneu) as (aa & ab & Ea & Eb & HR).
    apply (mk_block_read_pair qc D' ub VBb ρb p D u0 Bks C1 s Dc sela selb n Mn Ma Mb blA blB hd k prea preb nsA nsB aa ab).
    - rewrite Hsa; exact HMa.
    - rewrite Hsb; exact HMb.
    - rewrite Hsa; exact HblA.
    - rewrite Hsb; exact HblB.
    - rewrite (HnmB _ _ _ HMa HblA), Hnn; reflexivity.
    - rewrite (valid_blocks_nm _ _ _ _ _ _ HBk _ _ _ HMb HblB), Hnn', Hnn; reflexivity.
    - rewrite Hsa; exact Ra.
    - rewrite Hsb; exact Rb.
    - exact FnsA.
    - exact FnsB.
    - exact Ea.
    - exact Eb.
    - exact (per_univ_then_per_top_typ HR).
    - pose proof (HnaB _ _ _ HMa HblA) as Hn0; unfold brs_names in *; rewrite Hnames; exact Hn0.
    - pose proof (valid_blocks_names _ _ _ _ _ _ HBk _ _ _ HMb HblB) as Hn0; unfold brs_names in *; rewrite Hnames, <- HnamesAB; exact Hn0.
    - (** A branch. *)
      intros c gq na Ba nb Bb Hin InA InB.
      assert (HinA : In c (List.map fst (im_cons Ma)))
        by (rewrite <- Hnames; apply List.in_map_iff; exists (c, gq); split; [ reflexivity | exact Hin ]).
      destruct (cons_lookup_names _ _ HinA) as [gsA HcA].
      destruct (view_member_cons _ _ _ _ _ _ _ _ _ Hvmb c gsA HcA) as (gsB & HcB & Hcorr).
      pose proof (Hkinds c gq gsA Hin HcA) as Hkd.
      pose proof (Hmono c gq gsA Hin HcA) as Hmo.
      pose proof (Hnest c gq gsB Hin HcB) as Hno.
      pose proof (grp_tele_ass_plen _ (valid_group_ass _ _ HgQ) _ _ _ _ HMa (cons_lookup_in _ _ _ HcA)) as PA.
      pose proof (grp_tele_ass_plen _ Hass _ _ _ _ HMb (cons_lookup_in _ _ _ HcB)) as PB.
      assert (K1 : per_gargs (List.rev (cargs_ctx qc D' Ma nil ++ im_params D' Ma)) nil nil (ub ++ nsA ++ nil) (cups ++ nsB ++ nil))
        by (cbn [cargs_ctx cargs_ctx_aux List.app]; rewrite !List.app_nil_r; exact HpA).
      assert (K2 : per_gargs (List.rev (cargs_ctx qc D' Ma nil ++ im_params D' Ma)) nil nil (cups ++ nsB ++ nil) (cups ++ nsB ++ nil))
        by (cbn [cargs_ctx cargs_ctx_aux List.app]; rewrite !List.app_nil_r; exact HpC).
      assert (K3 : per_gargs (List.rev (cargs_ctx p D Mb nil ++ im_params D Mb)) nil nil (u0 ++ nsB ++ nil) (u0 ++ nsB ++ nil))
        by (cbn [cargs_ctx cargs_ctx_aux List.app]; rewrite !List.app_nil_r; exact HpG).
      destruct (CF cross_fresh_cargs a Ma b Mb HMa Hvab HMb c gsA gsB HcA HcB Hcorr nsA nsB Hcp HnsA gsA gsB nil nil nil nil
                  eq_refl eq_refl I eq_refl eq_refl K1 K2 K3 (tele_prefix_rel_nil _) (tele_prefix_rel_nil _)
                  (tele_prefix_rel_nil _) (s + im_nn Mn))
        as [vsA vsB FA FB Hca Hnr Ht].
      cbn [nonrec_arg_vals List.length cargs_nonrec] in FA, FB, Hca, Hnr, Ht.
      rewrite !List.app_nil_r in FA; rewrite !List.app_nil_r in FB; rewrite !List.app_nil_r in Hca;
        rewrite !List.app_nil_r in Ht.
      destruct (cross_wrapped_results rk r Hrk HIH Dc b a gq gsA gsB vsA vsB nsA nsB nsA (s + im_nn Mn + List.length gq)
                  Hkd Hcorr Hno Hmo Hca Ht)
        as [ihsA ihsB wA wB IA IB Lw WA WB HCR].
      pose proof (con_args_rel_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hca) as [LvA LvB].
      (** The constructors on each side, related. *)
      assert (HG : G b u0 u0 nsA nsB (d_con hd k c ((prea ++ nsA) ++ vsA)) (d_con hd k c ((preb ++ nsB) ++ vsB))).
      { eapply ind_rel_con; [ exact HMb | exact HrvB | exact Hrb | exact Hns | exact HcB | | | | | | ].
        - rewrite List.length_app; lia.
        - rewrite List.length_app; lia.
        - rewrite skipn_app_exact by exact Lpa; exact HAA.
        - rewrite skipn_app_exact by exact Hlb'; exact HBB.
        - rewrite skipn_app_exact by exact Lpa; split; [ apply length_nonrec_arg_vals; exact LvA | exact Hnr ].
        - rewrite !skipn_app_exact by assumption; exact Hca. }
      assert (HnA : List.NoDup (List.map (fun b0 => fst (fst b0)) (eb_brs blA))).
      { pose proof (HnaB _ _ _ HMa HblA) as Hn0; unfold brs_names in Hn0; rewrite <- Hn0.
        exact (decl_typed_nodup _ _ _ (valid_group_typed _ _ HgQ) _ _ HMa). }
      assert (HnB : List.NoDup (List.map (fun b0 => fst (fst b0)) (eb_brs blB))).
      { pose proof (valid_blocks_names _ _ _ _ _ _ HBk _ _ _ HMb HblB) as Hn0; unfold brs_names in Hn0; rewrite <- Hn0.
        exact (decl_typed_nodup _ _ _ Hdt _ _ HMb). }
      destruct (Hbr_x a Ma b Mb blA blB c gsA gsB na nb Ba Bb u0 u0 (prea ++ nsA) (preb ++ nsB) vsA vsB wA wB hd k
                  HMa HrvA Hvab HMb HblA HblB HcA HcB (brs_lookup_nodup_in _ _ _ _ HnA InA) (brs_lookup_nodup_in _ _ _ _ HnB InB))
        as (ra & rb & Era & Erb & Hrr).
      { rewrite !skipn_app_exact by assumption; exact HG. }
      { rewrite !skipn_app_exact by assumption; exact HCR. }
      rewrite skipn_app_exact in Era by exact Lpa; rewrite skipn_app_exact in Erb by exact Hlb'.
      rewrite skipn_app_exact in Hrr by exact Lpa; rewrite skipn_app_exact in Hrr by exact Hlb'.
      destruct (Hmot_x a Ma b blA blB u0 u0 nsA nsB _ _ HMa HrvA Hvab HblA HblB HG) as (ta & tb & Ta & Tb & HT).
      rewrite <- !List.app_assoc in Ta, Tb.
      apply (mk_branch_read_pair qc D' ub VBb ρb p D u0 Bks C1 s Dc Mn hd k prea preb Ma Mb (eb_motive blA) (eb_motive blB)
               nsA nsB c gq na nb Ba Bb gsA gsB vsA vsB ihsA ihsB wA wB ra rb ta tb).
      + exact HcA.
      + exact HcB.
      + rewrite (HarB _ _ _ _ _ _ _ HMa HblA HcA InA), (cargs_kinds_length _ _ Hkd), Hnn; reflexivity.
      + rewrite (valid_blocks_arity _ _ _ _ _ _ HBk _ _ _ _ _ _ _ HMb HblB HcB InB), (cargs_kinds_length _ _ Hkd),
          (cargs_corr_len _ _ _ Hcorr), Hnn', Hnn; reflexivity.
      + exact PA.
      + exact PB.
      + exact (Hcnta c gq gsA Hin HcA).
      + exact (Hcntb c gq gsB Hin HcB).
      + exact FA.
      + exact FB.
      + exact IA.
      + exact IB.
      + exact WA.
      + exact WB.
      + exact Era.
      + exact Erb.
      + exact Ta.
      + exact Tb.
      + rewrite <- !List.app_assoc in Hrr, HT; exact (per_elem_then_per_top HT Hrr).
  Qed.

  (** *** The References of the Two Sides

      A container's member [a] with a block and the group's member [b] the
      view takes it to: their types at [ub] and at [u0] are at a common
      reference. *)
  #[warnings="-cannot-define-projection"]
  Record cross_ref_pair (a b : nat) : Prop := mk_cross_ref_pair
    { (** The common reference's group *)
      cross_ref_pair_hd : qname
      (** The common reference's member *)
    ; cross_ref_pair_k : nat
      (** [a]'s uniform parameters at the reference *)
    ; cross_ref_pair_prea : list domain
      (** [b]'s uniform parameters at the reference *)
    ; cross_ref_pair_preb : list domain
      (** [a]'s type at [ub] is at the reference *)
    ; cross_ref_pair_ref_a : ⟦mref a of qc ub ⟧ gc_deps ⍮ gc_stack ↘ (cross_ref_pair_hd, cross_ref_pair_k, cross_ref_pair_prea)
      (** [b]'s type at [u0] is at the reference *)
    ; cross_ref_pair_ref_b : ⟦mref b of p u0 ⟧ gc_deps ⍮ gc_stack ↘ (cross_ref_pair_hd, cross_ref_pair_k, cross_ref_pair_preb) }.

  Lemma cross_refs : forall a Ma b Mb, List.nth_error vm a = Some b -> ind_member D' a = Some Ma -> ind_member D b = Some Mb ->
      im_is_rview Ma = false -> cross_ref_pair a b.
  Proof.
    intros a Ma b Mb Hvab HMa HMb HrvA.
    pose proof (length_cups p D Hvg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups) as Hlcu.
    assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
    pose proof (uparams_refl_l D' (valid_group_valid _ _ HgQ) (valid_group_closed _ _ HgQ) _ _ Hub) as Hubub.
    destruct (cross_view_members a b Hvab) as (Ma0 & Mb0 & HMa0 & Hvmb).
    rewrite HMa in HMa0; injection HMa0 as <-.
    pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMb0; rewrite HMb in HMb0; injection HMb0 as <-.
    assert (HrvB : im_is_rview Mb = false) by (rewrite (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb); exact HrvA).
    destruct (mref_exists VP HP qc D' HVQ ub Hubub Hlb a Ma HMa HrvA) as [[[hda ka] prea] Ra].
    destruct (mref_exists VP HP p D HPD u0 u0_gargs' u0_len' b Mb HMb HrvB) as [[[hdb kb] preb] Rb].
    destruct (mref_ref_len qc D' a Ma ub hda ka prea Hq HMa Hlb Ra) as [Hra _].
    destruct (mref_ref_len p D b Mb u0 hdb kb preb Hl HMb u0_len' Rb) as [Hrb _].
    pose proof (view_member_ref _ _ _ _ _ _ _ _ _ Hvmb HrvA) as Href.
    rewrite Hra, Hrb in Href; injection Href as <- <-.
    exact (mk_cross_ref_pair a b hdb kb prea preb Ra Rb).
  Qed.

  (** *** The Uniform Parameters the Two Sides Read

      At a declared member of the container, its own [ub] and [k]'s
      instance [cups]; at a view of the container's, its instance at [ub]
      and the group's view's at [u0], which the view equations relate. *)
  Lemma cross_uparams_read : forall i' Mi' j Mj hd k prea preb Dq, List.nth_error vm i' = Some j ->
      ind_member D' i' = Some Mi' -> ind_member D j = Some Mj -> im_is_rview Mi' = false ->
      ⟦mref i' of qc ub ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, prea) -> ⟦mref j of p u0 ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, preb) ->
      ind_lookup gc_deps gc_stack hd = Some Dq ->
      per_top_ps (List.rev (ind_uparams Dq)) prea preb.
  Proof.
    intros i' Mi' j Mj hd k prea preb Dq Hvi HMi' HMj HrvI Ra Rb HDq.
    pose proof (length_cups p D Hvg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups) as Hlcu.
    assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
    destruct (grp_tele_ass_vm _ Hass _ _ _ _ _ _ _ _ _ HMm Hh Hq HMi') as [jj Mjj Hvj HMjj _ Hhm].
    rewrite Hvi in Hvj; injection Hvj as <-; rewrite HMj in HMjj; injection HMjj as <-.
    unfold im_is_rview in HrvI; destruct (im_head Mi') as [pm | qv kv Iv vmv | qr Ir fl] eqn:Hh'; [| | discriminate HrvI ].
    - destruct Hhm as [vm' Hhj].
      pose proof (mref_decl_inv _ _ _ _ _ _ _ Hq HMi' Hh' Ra) as Heq; injection Heq as -> -> ->.
      destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hl HMj Hhj Rb) as (py & Heq & Epy); injection Heq as ->.
      pose proof (functional_eval_exps' _ _ _ _ Epy Ecups) as ->.
      rewrite Hq in HDq; injection HDq as <-.
      intros s; exact (per_gargs_top _ _ _ _ _ Hub ltac:(rewrite List.length_rev; unfold ind_nu in Hlb; exact Hlb) s).
    - destruct Hhm as (Is' & vm' & Hhj & _).
      destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hq HMi' Hh' Ra) as (pa & Heq & Epa); injection Heq as -> -> ->.
      destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hl HMj Hhj Rb) as (pb & Heq & Epb); injection Heq as ->.
      destruct (view_view_values VP HP p D HPD m Mm qc k' Is vm D' i' Mi' j qv kv Iv vmv Dq Mj Is' vm'
                  HMm Hh Hq HMi' Hh' HDq Hvi HMj Hhj u0 cups ub u0_gargs' u0_len' Ecups Hub) as (pa' & pb' & Epa' & Epb' & Hgp).
      pose proof (functional_eval_exps' _ _ _ _ Epa' Epa) as ->; pose proof (functional_eval_exps' _ _ _ _ Epb' Epb) as ->.
      destruct (grp_tele_ass_views _ (valid_group_ass _ _ HgQ) _ _ _ _ _ _ HMi' Hh') as (D3 & Mc3 & Hq3 & _ & _ & HlIv).
      rewrite HDq in Hq3; injection Hq3 as <-.
      assert (Lp : List.length pa = List.length (List.rev (ind_uparams Dq)))
        by (rewrite List.length_rev, (eval_exps_length _ _ _ Epa); exact HlIv).
      intros s; exact (per_gargs_top _ _ _ _ _ Hgp Lp s).
  Qed.

  (** The paths of a container's member's arguments the group read has,
      at a declared member: all of its own. *)
  Lemma cargs_leaf_mono_refl : forall X gs, cargs_leaf_mono X X gs gs.
  Proof. intros X; induction gs as [| [A | t] gs IH]; cbn; auto. Qed.

  (** At a view of a group [Dc] of the container's: those [Dc] has, by the
      view's map. *)
  Lemma cargs_leaf_mono_view : forall qv Dc vmv, rview_struct_ok gc_deps gc_stack Dc ->
      (forall j' j, List.nth_error vmv j' = Some j -> exists Mj' Mj, ind_member Dc j' = Some Mj' /\ view_member qc D' qv Dc vmv j' Mj' j Mj) ->
      forall gq gA, cargs_corr vmv gq gA -> cargs_leaf_mono Dc D' gq gA.
  Proof.
    intros qv Dc vmv HrsC Hvmv.
    induction gq as [| [A'' | t''] gq IH]; intros [| [A' | t'] gA] Hco; cbn in Hco |- *; try contradiction; auto.
    all: first [ exact (IH _ Hco)
               | destruct Hco as (Hmt & Hdp & Hco); split; [| exact (IH _ Hco) ];
                 intros l Hin; exact (leaf_in_view_mono qc qv D' Dc vmv HrsQ HrsC Hvmv l t'' t' (shape_corr_of _ _ _ Hmt Hdp) Hin) ].
  Qed.

  (** *** The Stuck Eliminators at a Member

      The group's member [j] the view takes the container's [i'] to is a
      view, of [i']'s container, at the map the agreement of the views'
      maps gives ([view_maps_coherent]): the blocks the two read for each
      member of the group read are the container's at its member and the
      group's at the member the view takes it to.  Its recursive results
      at the paths it nests through are at members of lower rank. *)
  Lemma cross_bot_rank : forall rk, view_rank_ok gc_deps gc_stack D rk ->
      forall j, (forall j', rk j' < rk j -> cross_bot j') -> cross_bot j.
  Proof.
    intros rk Hrk j HIH i' Mj hd k as1 as2 e e' w w' ns ns' Hvi HM Hrv Hg0.
    pose proof (length_cups p D Hvg m Mm qc k' Is vm D' HMm Hh Hq u0 cups Ecups) as Hlcu.
    assert (Hlb : List.length ub = ind_nu D') by (destruct (per_gargs_length _ _ _ _ _ Hub) as [H1 _]; lia).
    pose proof Hg0 as Hg1.
    inversion Hg1 as [| j0 Mj0 hd0 k0 ns0 ns0' as1' as2' e0 e0' w0 w0' HM0 Hrv0 Hr Hn L1 L2 Hs1 Hs2 He |]; subst;
      [| rewrite HM in *; match goal with H : Some _ = Some _ |- _ => injection H as <- end;
         exfalso; eapply not_rview_record; eassumption ].
    rewrite HM in HM0; injection HM0 as <-.
    destruct (cross_view_members i' j Hvi) as (Mi' & Mj1 & HMi' & Hvmb).
    pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb) as HMj1; rewrite HM in HMj1; injection HMj1 as <-.
    assert (HrvI : im_is_rview Mi' = false) by (rewrite <- (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb); exact Hrv).
    pose proof (view_member_ref _ _ _ _ _ _ _ _ _ Hvmb HrvI) as Href; rewrite Hr in Href; symmetry in Href.
    destruct (SE self_ref_target j Mj hd k HM Hr) as (Dq & Mk & HDq & HMk & Hnnq & Hnuq).
    destruct (cross_refs i' Mi' j Mj Hvi HMi' HM HrvI) as [hd1 k1 prea preb Ra Rb].
    destruct (mref_ref_len qc D' i' Mi' ub hd1 k1 prea Hq HMi' Hlb Ra) as [Hra _].
    rewrite Href in Hra; injection Hra as <- <-.
    apply (per_bot_elim_pair qc D' ub VBb ρb p D u0 Bks C1 Hq Hl i' Mi' j Mj hd k Dq Mk as1 as2 e e' prea preb
             HMi' HM Href Hr HDq HMk).
    - unfold im_np; lia.
    - unfold im_np; lia.
    - intros i0 Mi0 b HMi0 Hb; exact (HnmB _ _ _ HMi0 Hb).
    - intros i0 Mi0 b HMi0 Hb; exact (valid_blocks_nm _ _ _ _ _ _ HBk _ _ _ HMi0 Hb).
    - exact (grp_tele_ass_leaf_arity _ HassQ).
    - exact (grp_tele_ass_leaf_arity _ Hass).
    - exact Ra.
    - exact Rb.
    - exact (cross_uparams_read i' Mi' j Mj hd k prea preb Dq Hvi HMi' HM HrvI Ra Rb HDq).
    - exact He.
    - (** The blocks. *)
      intros s n Mn HMnb.
      destruct (ind_bmembers_member _ _ _ HMnb) as [HMn Hnb].
      apply (cross_block_read rk (rk j) Hrk HIH s).
      destruct (grp_tele_ass_vm _ Hass _ _ _ _ _ _ _ _ _ HMm Hh Hq HMi') as [jj Mjj Hvj HMjj _ Hhm].
      rewrite Hvi in Hvj; injection Hvj as <-; rewrite HM in HMjj; injection HMjj as <-.
      pose proof (grp_tele_ass_view_maps_coherent _ Hass) as Hcoh.
      unfold im_is_rview in HrvI; destruct (im_head Mi') as [pm | qv kv Iv vmv | qr Ir fl] eqn:Hh'; [| | discriminate HrvI ].
      + (** A declared member of the container: the view's own map. *)
        destruct Hhm as [vm' Hhj].
        pose proof (Hcoh m Mm qc k' Is vm D' i' Mi' j Mj qc i' Is vm' HMm Hh Hq HMi' Hvi HM Hhj) as Hvma.
        unfold view_map_at in Hvma; rewrite Hh' in Hvma; subst vm'.
        assert (Hsa : im_sel Mi' = None) by (unfold im_sel; rewrite Hh'; reflexivity).
        assert (Hsb : im_sel Mj = Some vm) by (unfold im_sel; rewrite Hhj; reflexivity).
        rewrite Hsa, Hsb.
        unfold im_ref in Href; rewrite Hh' in Href; injection Href as <- <-.
        rewrite Hq in HDq; injection HDq as <-.
        assert (HrvN : im_is_rview Mn = false).
        { destruct (im_is_rview Mn) eqn:E; [| reflexivity ].
          apply (proj1 (rview_struct_suffix _ _ _ HrsQ _ _ HMn)) in E; lia. }
        destruct (grp_tele_ass_view_wrap _ Hass _ _ _ _ _ _ HMm Hh) as (D2 & Hq2 & Hvw); rewrite Hq in Hq2; injection Hq2 as <-.
        assert (Hnl : n < List.length vm)
          by (rewrite (view_wrap_ok_length _ _ _ Hvw); apply List.nth_error_Some; unfold ind_member in HMn; congruence).
        destruct (nth_error_lt_some' _ _ Hnl) as [b Hvb].
        destruct (cross_view_members n b Hvb) as (Mn0 & Mb & HMn0 & Hvmb2).
        rewrite HMn in HMn0; injection HMn0 as <-.
        pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb2) as HMb.
        assert (HrvB : im_is_rview Mb = false) by (rewrite (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb2); exact HrvN).
        destruct (cross_refs n Mn b Mb Hvb HMn HMb HrvN) as [hdn kn pran prbn Ran Rbn].
        pose proof (decl_typed_nodup _ _ _ HdtQ _ _ HMn) as Hnd.
        apply (mk_cross_block_site rk (rk j) D' None (Some vm) n Mn n Mn b Mb hdn kn pran prbn).
        * reflexivity.
        * cbn; exact (List.nth_error_nth _ _ _ Hvb).
        * exact Hvb.
        * exact HMn.
        * exact HrvN.
        * exact HMb.
        * exact HrvB.
        * reflexivity.
        * reflexivity.
        * intros c gq gA Hin HcA.
          pose proof (cons_lookup_nodup_in _ _ _ Hnd Hin) as Hc0; unfold ind_con in HcA; rewrite Hc0 in HcA; injection HcA as <-.
          apply cargs_kinds_refl.
        * intros c gq gA Hin HcA.
          pose proof (cons_lookup_nodup_in _ _ _ Hnd Hin) as Hc0; unfold ind_con in HcA; rewrite Hc0 in HcA; injection HcA as <-.
          apply cargs_leaf_mono_refl.
        * intros c gq gB Hin HcB.
          exact (view_rank_ok_nest _ _ _ _ Hrk j Mj qc i' Is vm D' n Mn b Mb c gq gB HM Hhj Hq HMn Hvb HMb
                   (cons_lookup_nodup_in _ _ _ Hnd Hin) HcB).
        * (** read as its own: every path is the container's *)
          intros c gq gA Hin HcA.
          pose proof (cons_lookup_nodup_in _ _ _ Hnd Hin) as Hc0; unfold ind_con in HcA; rewrite Hc0 in HcA; injection HcA as <-.
          exact (cargs_nin_own_of_ass D' HassQ gq (grp_tele_ass_plen _ HassQ _ _ _ _ HMn Hin)).
        * (** the group's paths the container has *)
          intros c gq gB Hin HcB.
          destruct (view_member_cons _ _ _ _ _ _ _ _ _ Hvmb2 c gq (cons_lookup_nodup_in _ _ _ Hnd Hin)) as (gB0 & HcB0 & Hco).
          rewrite HcB in HcB0; injection HcB0 as <-.
          exact (cargs_nin_view p qc D D' vm Hlc HlcQ Hrs HrsQ cross_view_members gq gB Hco).
        * exact Ran.
        * exact Rbn.
      + (** A view of the container's: its map, then the view's. *)
        destruct Hhm as (Is' & vm' & Hhj & _).
        pose proof (Hcoh m Mm qc k' Is vm D' i' Mi' j Mj qv kv Is' vm' HMm Hh Hq HMi' Hvi HM Hhj) as Hvma.
        unfold view_map_at in Hvma; rewrite Hh' in Hvma.
        assert (Hsa : im_sel Mi' = Some vmv) by (unfold im_sel; rewrite Hh'; reflexivity).
        assert (Hsb : im_sel Mj = Some vm') by (unfold im_sel; rewrite Hhj; reflexivity).
        rewrite Hsa, Hsb.
        unfold im_ref in Href; rewrite Hh' in Href; injection Href as <- <-.
        pose proof (HcvQ _ _ _ _ _ _ _ HMi' Hh' HDq) as HgD.
        pose proof (grp_tele_ass_rstruct _ (valid_group_ass _ _ HgD)) as HrsC.
        assert (HrvN : im_is_rview Mn = false).
        { destruct (im_is_rview Mn) eqn:E; [| reflexivity ].
          apply (proj1 (rview_struct_suffix _ _ _ HrsC _ _ HMn)) in E; lia. }
        assert (Hvmv : forall a' a, List.nth_error vmv a' = Some a ->
                  exists Ma' Ma, ind_member Dq a' = Some Ma' /\ view_member qc D' qv Dq vmv a' Ma' a Ma).
        { intros a' a Hva'.
          destruct (grp_tele_ass_view_wrap _ HassQ _ _ _ _ _ _ HMi' Hh') as (D3 & Hq3 & Hvw3).
          rewrite HDq in Hq3; injection Hq3 as <-.
          assert (Hi : a' < List.length (ind_members Dq))
            by (rewrite <- (view_wrap_ok_length _ _ _ Hvw3); apply List.nth_error_Some; congruence).
          destruct (nth_error_lt_some' _ _ Hi) as [Ma' HMa'].
          destruct (view_agree_members qc D' i' Mi' qv kv Iv vmv Dq HassQ HMi' Hh' HDq a' Ma' HMa') as (a0 & Ma & Hvm0).
          pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvm0) as Hv0; rewrite Hva' in Hv0; injection Hv0 as <-.
          exists Ma', Ma; split; [ exact HMa' | exact Hvm0 ]. }
        destruct (view_agree_members qc D' i' Mi' qv kv Iv vmv Dq HassQ HMi' Hh' HDq n Mn HMn) as (a & Ma & Hvmn).
        pose proof (view_member_v _ _ _ _ _ _ _ _ _ Hvmn) as Hva.
        pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmn) as HMa.
        assert (HrvA : im_is_rview Ma = false) by (rewrite (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmn); exact HrvN).
        assert (Hb : exists b, List.nth_error vm' n = Some b /\ List.nth_error vm a = Some b).
        { pose proof (f_equal (fun l => List.nth_error l n) Hvma) as E; cbn beta in E.
          rewrite !List.nth_error_map, Hva in E; cbn in E.
          destruct (List.nth_error vm' n) as [b |] eqn:Hb0; cbn in E; [| discriminate ].
          injection E as E; exists b; split; [ reflexivity | exact E ]. }
        destruct Hb as (b & Hvb' & Hvab).
        destruct (cross_view_members a b Hvab) as (Ma0 & Mb & HMa0 & Hvmb2).
        rewrite HMa in HMa0; injection HMa0 as <-.
        pose proof (view_member_mem _ _ _ _ _ _ _ _ _ Hvmb2) as HMb.
        assert (HrvB : im_is_rview Mb = false) by (rewrite (view_member_is_rview _ _ _ _ _ _ _ _ _ Hvmb2); exact HrvA).
        destruct (cross_refs a Ma b Mb Hvab HMa HMb HrvA) as [hdn kn pran prbn Ran Rbn].
        pose proof (decl_typed_nodup _ _ _ (valid_group_typed _ _ HgD) _ _ HMn) as Hnd.
        apply (mk_cross_block_site rk (rk j) Dq (Some vmv) (Some vm') n Mn a Ma b Mb hdn kn pran prbn).
        * cbn; exact (List.nth_error_nth _ _ _ Hva).
        * cbn; exact (List.nth_error_nth _ _ _ Hvb').
        * exact Hvab.
        * exact HMa.
        * exact HrvA.
        * exact HMb.
        * exact HrvB.
        * symmetry; exact (view_member_nn _ _ _ _ _ _ _ _ _ Hvmn).
        * symmetry; exact (view_member_names _ _ _ _ _ _ _ _ _ Hvmn).
        * intros c gq gA Hin HcA.
          destruct (view_member_cons _ _ _ _ _ _ _ _ _ Hvmn c gq (cons_lookup_nodup_in _ _ _ Hnd Hin)) as (gA0 & HcA0 & Hco).
          rewrite HcA in HcA0; injection HcA0 as <-; exact (cargs_kinds_of_corr _ _ _ Hco).
        * intros c gq gA Hin HcA.
          destruct (view_member_cons _ _ _ _ _ _ _ _ _ Hvmn c gq (cons_lookup_nodup_in _ _ _ Hnd Hin)) as (gA0 & HcA0 & Hco).
          rewrite HcA in HcA0; injection HcA0 as <-.
          exact (cargs_leaf_mono_view qv Dq vmv HrsC Hvmv gq gA Hco).
        * intros c gq gB Hin HcB.
          exact (view_rank_ok_nest _ _ _ _ Hrk j Mj qv kv Is' vm' Dq n Mn b Mb c gq gB HM Hhj HDq HMn Hvb' HMb
                   (cons_lookup_nodup_in _ _ _ Hnd Hin) HcB).
        * (** the container's paths the view's container has *)
          intros c gq gA Hin HcA.
          destruct (view_member_cons _ _ _ _ _ _ _ _ _ Hvmn c gq (cons_lookup_nodup_in _ _ _ Hnd Hin)) as (gA0 & HcA0 & Hco).
          rewrite HcA in HcA0; injection HcA0 as <-.
          exact (cargs_nin_view qc qv D' Dq vmv HlcQ (leaves_coherent_of_order Dq (rview_struct_order _ _ _ HrsC)) HrsQ HrsC Hvmv
                   gq gA Hco).
        * (** the group's: its own view of that container *)
          intros c gq gB Hin HcB.
          pose proof (view_members_of_ass p D j Mj qv kv Is' vm' Dq Hass HM Hhj HDq) as HvmD.
          destruct (HvmD n b Hvb') as (Mn1 & Mb1 & HMn1 & Hvm1).
          rewrite HMn in HMn1; injection HMn1 as <-.
          rewrite (view_member_mem _ _ _ _ _ _ _ _ _ Hvm1) in HMb; injection HMb as <-.
          destruct (view_member_cons _ _ _ _ _ _ _ _ _ Hvm1 c gq (cons_lookup_nodup_in _ _ _ Hnd Hin)) as (gB0 & HcB0 & Hco).
          rewrite HcB in HcB0; injection HcB0 as <-.
          exact (cargs_nin_view p qv D Dq vm' Hlc (leaves_coherent_of_order Dq (rview_struct_order _ _ _ HrsC)) Hrs HrsC HvmD
                   gq gB Hco).
        * exact Ran.
        * exact Rbn.
  Qed.

  (** ** The Stuck Eliminators

      By strong induction on the rank. *)
  Theorem cross_bot_all : forall j, cross_bot j.
  Proof.
    destruct (grp_tele_ass_rank _ Hass) as [rk Hrk].
    assert (H : forall r j, rk j < r -> cross_bot j).
    { induction r as [| r IH]; intros j Hj; [ lia |].
      apply (cross_bot_rank rk Hrk j); intros j' Hj'; apply IH; lia. }
    intros j; exact (H (S (rk j)) j ltac:(lia)).
  Qed.
End CrossBot.

End Fixed_GCtx.
