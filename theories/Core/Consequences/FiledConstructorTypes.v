(** * The Filed Constructor Types of a Declaration

    A run of a group's declaration files, for each declared member, the
    constructor types the user wrote, up to conversion, with each [Self_i]
    the type former of the member [i] at the frames' parameters
    ([run_cmd_ind_con_types]).  An argument classified as written is filed as
    its own image under that instantiation; one classified as its normal
    form is equal to it by soundness, and the equality moves through the
    instantiation of the [Self]s and the [Π]s over the arguments before it.
    A nested occurrence, found on a normal form only, is filed as the view
    of its instance, whose type is the container's member at the instance
    with the [Self]s instantiated. *)

From Stdlib Require Import Lia List String PeanoNat Bool Wf_nat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base Soundness.
From Mctt.Core.Consequences Require Import Consistency.
From Mctt.Core.Syntactic Require Import SystemOpt CtxSub.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing Syntax Runs Views.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Core Require Import Completeness.
From Mctt.Algorithmic Require Import Strengthening.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Instances Normalized Equal up to Proofs

    Two lists of terms at the instances of a closed telescope, whose
    normal forms are equal up to their proofs, are equal, and each term is
    equal to the other's normal form: position by position, the types are
    equal by the equal terms before, and the terms are equal by soundness
    up to proofs, each read back at the first one's type. *)

(** The [j]-th terms normalized pointwise are typed and normalized. *)
Lemma nbes_nth : forall Θ Ξ Γ Ms As Ws, nbes Θ Ξ Γ Ms As Ws ->
    forall j M A W, List.nth_error Ms j = Some M -> List.nth_error As j = Some A -> List.nth_error Ws j = Some W ->
      Θ ⍮ Ξ ⍮ Γ ⊢ M : A /\ nbe Θ Ξ Γ M A W.
Proof.
  induction 1 as [| M0 Ms A0 As W0 Ws HM HW _ IH]; intros [| j] M A W HMj HAj HWj; cbn in *; try discriminate.
  - injection HMj as <-; injection HAj as <-; injection HWj as <-; split; assumption.
  - exact (IH _ _ _ _ HMj HAj HWj).
Qed.

Lemma nbes_length : forall Θ Ξ Γ Ms As Ws, nbes Θ Ξ Γ Ms As Ws -> List.length Ws = List.length Ms /\ List.length As = List.length Ms.
Proof. induction 1; cbn; [ split; reflexivity | destruct IHnbes; split; f_equal; assumption ]. Qed.

(** Lists equal up to proofs are so position by position. *)
Lemma nfs_eq_upto_proofs_nth : forall Ws Rs, nfs_eq_upto_proofs Ws Rs ->
    List.length Ws = List.length Rs /\
    forall j W R, List.nth_error Ws j = Some W -> List.nth_error Rs j = Some R -> nf_eq_upto_proofs W R.
Proof.
  unfold nfs_eq_upto_proofs; induction Ws as [| W Ws IH]; intros [| R Rs] H; cbn in H; try discriminate.
  - split; [ reflexivity | intros [] ? ? ? [=] ].
  - apply andb_prop in H as [H1 H2]; destruct (IH _ H2) as [Hl Hn]; split; [ cbn; f_equal; exact Hl |].
    intros [| j] W0 R0 HW HR; cbn in HW, HR; [ injection HW as <-; injection HR as <-; exact H1 | exact (Hn _ _ _ HW HR) ].
Qed.

Lemma nbes_upto_proofs_eq : forall Θ Ξ Γ U Cs Ms Ws Rs,
    all_assumptions U -> ⊢ Θ ⍮ Ξ ⍮ U ++ Γ ->
    nbes Θ Ξ Γ Cs (tele_insts U Id Cs) Ws -> nbes Θ Ξ Γ Ms (tele_insts U Id Ms) Rs -> nfs_eq_upto_proofs Ws Rs ->
    forall j C M T, List.nth_error Cs j = Some C -> List.nth_error Ms j = Some M -> List.nth_error (tele_insts U Id Cs) j = Some T ->
      Θ ⍮ Ξ ⍮ Γ ⊢ C ≈ M : T.
Proof.
  intros * HUa HU HC HM HWR j; induction j as [j IH] using lt_wf_ind; intros C M T HCj HMj HTj.
  destruct (nbes_length _ _ _ _ _ _ HC) as [HlW HlA]; destruct (nbes_length _ _ _ _ _ _ HM) as [HlR HlA'].
  destruct (nfs_eq_upto_proofs_nth _ _ HWR) as [HlWR HWRn].
  assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by exact (ctx_app_wf_tail _ _ _ _ HU).
  destruct (nth_error_lt_some Ws j ltac:(rewrite HlW; apply List.nth_error_Some; congruence)) as [W HWj].
  destruct (nth_error_lt_some Rs j ltac:(rewrite HlR; apply List.nth_error_Some; congruence)) as [R HRj].
  destruct (nth_error_lt_some (tele_insts U Id Ms) j ltac:(rewrite HlA'; apply List.nth_error_Some; congruence)) as [T' HT'j].
  destruct (nbes_nth _ _ _ _ _ _ HC _ _ _ _ HCj HTj HWj) as [HCt HCn].
  destruct (nbes_nth _ _ _ _ _ _ HM _ _ _ _ HMj HT'j HRj) as [HMt HMn].
  (** The types are equal, by the equal terms before. *)
  destruct (@tele_insts_cong_upto (gc_mk Θ Ξ) U Γ Γ Id Id Cs Ms HUa HU (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ HΓ))
              j T T' HTj HT'j ltac:(intros j' N N' T0 Hj' HN HN' HT0; exact (IH j' Hj' _ _ _ HN HN' HT0))) as (S & HS & HTT).
  assert (HMt' : Θ ⍮ Ξ ⍮ Γ ⊢ M : T) by (eapply wf_conv_sort; [ exact HMt | exact (presup_exp_eq_left HTT) | exact HS | exact (wf_exp_eq_sym _ _ _ _ _ _ HTT) ]).
  destruct (soundness HMt') as (R' & HR' & _).
  pose proof (completeness_at_equal_types HS (wf_exp_eq_refl HMt) (wf_exp_eq_sym _ _ _ _ _ _ HTT) HMn HR') as HRR.
  pose proof (HWRn _ _ _ HWj HRj) as HWR0.
  exact (soundness_upto_proofs HCt HMt' HCn HR' ltac:(etransitivity; eassumption)).
Qed.

(** A record type at equal instances of its parameters, in a large
    universe. *)
Lemma record_apps_args_conv : forall Θ Ξ Γ qr Rr Ls Ls',
    ⊢ Θ ⍮ Ξ ⍮ Γ -> record_lookup Θ Ξ qr = Some Rr ->
    List.length Ls = List.length (record_params Rr) -> List.length Ls' = List.length (record_params Rr) ->
    (forall j N A, List.nth_error Ls j = Some N -> List.nth_error (tele_insts (record_params Rr) Id Ls) j = Some A ->
       Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
    (forall j N N' T, List.nth_error Ls j = Some N -> List.nth_error Ls' j = Some N' ->
       List.nth_error (tele_insts (record_params Rr) Id Ls) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : T) ->
    exists i, Θ ⍮ Ξ ⍮ Γ ⊢ apps (a_record qr) Ls ≈ apps (a_record qr) Ls' : Typeω@i.
Proof.
  intros * HΓ Hl HL HL' HLs HLL.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  destruct (@record_former_typed (gc_mk Θ Ξ) ⋅ qr Rr (wf_ctx_empty _ _ Hg) Hl) as (j & Hf0 & _).
  destruct (@record_former_typed (gc_mk Θ Ξ) Γ qr Rr HΓ Hl) as (j' & HfΓ & _).
  destruct (wf_record_inversion Hf0) as [R0 Hl0 Hnd Hass i0 Hty HF HS HFs _].
  cbn in Hl0; rewrite Hl in Hl0; injection Hl0 as <-.
  pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
  destruct (wf_is_univ_typ HS) as [k Hk].
  assert (HP : ⊢ Θ ⍮ Ξ ⍮ record_params Rr ++ ⋅) by (rewrite List.app_nil_r; exact (presup_is_univ_ctx HS)).
  pose proof (wf_apps_vars Θ Ξ (record_params Rr) ⋅ (record_sort Rr) (a_record qr) k Hass HP
                ltac:(rewrite List.app_nil_r; exact Hk) Hf0) as HT0.
  cbn [exp_wk] in HT0; rewrite List.app_nil_r in HT0.
  assert (Hsc : exp_scoped (List.length (record_params Rr)) (apps (a_record qr) (vars_from 0 (List.length (record_params Rr))))).
  { apply exp_scoped_apps; split; [ cbn; exact I | apply vars_from_scoped; lia ]. }
  pose proof (closed_tele_exp_cong Θ Ξ Γ (record_params Rr) _ _ Ls Ls' Hass (closed_params _ Hc) Hsc (closed_sort _ Hc)
                HT0 HΓ HL HL' HLL) as Heq.
  assert (E : forall L, List.length L = List.length (record_params Rr) ->
             (apps (a_record qr) (vars_from 0 (List.length (record_params Rr))))[sb_of_list Id L] = apps (a_record qr) L)
    by (intros L HL0; rewrite <- HL0; apply apps_vars_sb_of_list; exact I).
  rewrite (E Ls HL), (E Ls' HL') in Heq.
  destruct (record_sort_large Θ Ξ Γ qr Rr Ls HfΓ Hl HL HLs) as [n Hn].
  exists n; exact (wf_exp_eq_subtyp' _ _ _ _ _ _ _ Heq Hn).
Qed.

(** A member's type former at instances equal at the uniform parameters and
    the same non-uniform ones, in a large universe. *)
Lemma ind_nest_eq : forall Θ Ξ Ψ qc k D' Cs Rs Ns i,
    ind_lookup Θ Ξ qc = Some D' -> List.length Cs = ind_nu D' -> List.length Rs = List.length Cs ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ apps (a_ind qc k) (Cs ++ Ns) : Typeω@i ->
    (forall j N N' T, List.nth_error Cs j = Some N -> List.nth_error Rs j = Some N' ->
       List.nth_error (tele_insts (ind_uparams D') Id Cs) j = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T) ->
    exists i', Θ ⍮ Ξ ⍮ Ψ ⊢ apps (a_ind qc k) (Cs ++ Ns) ≈ apps (a_ind qc k) (Rs ++ Ns) : Typeω@i'.
Proof.
  intros * Hl HCl HRl HT HCR.
  assert (HΨ : ⊢ Θ ⍮ Ξ ⍮ Ψ) by (gen_presups; assumption).
  pose proof (ctx_wf_gctx _ _ _ HΨ) as Hg; pose proof (decls_of_ctx _ _ _ HΨ) as HDs.
  destruct (wf_apps_exp_head _ _ _ _ _ _ HT) as [T0 HT0].
  destruct (wf_ind_inversion HT0) as [D0 Mk Hl0 Hk Hlt _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  destruct (decl_of_lookup _ _ _ _ _ HΨ Hl) as [HD Hc].
  pose proof (@wf_ind_apps_len (gc_mk Θ Ξ) Ψ qc D' k Mk (Cs ++ Ns) i Hl Hk HT) as HLc.
  pose proof (@wf_ind_apps_inv (gc_mk Θ Ξ) Ψ qc D' k Mk (Cs ++ Ns) _ Hl Hk HT HLc) as HTc.
  assert (HLv : List.length (Rs ++ Ns) = im_np D' Mk) by (rewrite List.length_app, HRl, <- List.length_app; exact HLc).
  assert (Hass : all_assumptions (ind_uparams D')) by exact (decl_typed_ass _ _ _ HD).
  assert (HTT : forall j N N' T, List.nth_error (Cs ++ Ns) j = Some N -> List.nth_error (Rs ++ Ns) j = Some N' ->
             List.nth_error (tele_insts (im_params D' Mk) Id (Cs ++ Ns)) j = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T).
  { intros j N N' T HN HN' HTj.
    pose proof HTj as HTj0.
    unfold im_params in HTj; rewrite tele_insts_app in HTj by (try exact Hass; rewrite HCl; reflexivity).
    assert (Hl1 : List.length (tele_insts (ind_uparams D') Id Cs) = List.length Cs)
      by (rewrite length_tele_insts by exact Hass; unfold ind_nu in HCl; lia).
    destruct (Nat.lt_ge_cases j (List.length Cs)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HN, HTj by lia; rewrite List.nth_error_app1 in HN' by lia.
      exact (HCR _ _ _ _ HN HN' HTj).
    - rewrite List.nth_error_app2 in HN by lia; rewrite List.nth_error_app2 in HN' by lia; rewrite HRl, HN in HN'.
      injection HN' as <-; apply wf_exp_eq_refl.
      apply (HTc j); [ rewrite List.nth_error_app2 by lia; exact HN | exact HTj0 ]. }
  assert (HTv : forall j N T, List.nth_error (Rs ++ Ns) j = Some N ->
             List.nth_error (tele_insts (im_params D' Mk) Id (Rs ++ Ns)) j = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N : T).
  { intros j N' T' HN' HT'.
    assert (HPΨ : ⊢ Θ ⍮ Ξ ⍮ im_params D' Mk ++ Ψ)
      by (apply wf_ctx_closed_app; [ exact (decl_closed_params_ass _ _ _ Hc Hk) | exact (decl_closed_params _ _ _ Hc Hk)
                                   | exact (member_params_wf _ _ _ _ _ HD Hk) | exact HΨ ]).
    assert (Hj : j < List.length (Cs ++ Ns)) by (rewrite List.length_app, <- HRl, <- List.length_app; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some (Cs ++ Ns) j Hj) as [N HN].
    destruct (nth_error_lt_some (tele_insts (im_params D' Mk) Id (Cs ++ Ns)) j
                ltac:(rewrite length_tele_insts by exact (decl_closed_params_ass _ _ _ Hc Hk); rewrite length_im_params, <- HLc; lia))
      as [T HTj].
    destruct (@tele_insts_cong Θ Ξ (im_params D' Mk) Ψ Ψ Id Id (Cs ++ Ns) (Rs ++ Ns)
                (decl_closed_params_ass _ _ _ Hc Hk) HPΨ (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ HΨ))
                ltac:(rewrite length_im_params; exact HLc) ltac:(rewrite length_im_params; exact HLv) HTT _ _ _ HTj HT')
      as (S & HS & HTT').
    pose proof (HTT _ _ _ _ HN HN' HTj) as HNN.
    eapply wf_conv_sort; [ exact (presup_exp_eq_right HNN) | exact (presup_exp_eq_right HTT') | exact HS | exact HTT' ]. }
  destruct (ind_apps_conv_large _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk Hlt HΨ HLc HLv HTc HTv HTT) as (i' & _ & _ & Heq).
  exists i'; exact Heq.
Qed.

(** Each term is equal to the other list's normal form at its place. *)
Lemma nbes_upto_proofs_eq_nf : forall Θ Ξ Γ U Cs Ms Ws Rs,
    all_assumptions U -> ⊢ Θ ⍮ Ξ ⍮ U ++ Γ ->
    nbes Θ Ξ Γ Cs (tele_insts U Id Cs) Ws -> nbes Θ Ξ Γ Ms (tele_insts U Id Ms) Rs -> nfs_eq_upto_proofs Ws Rs ->
    forall j C R T, List.nth_error Cs j = Some C -> List.nth_error Rs j = Some R -> List.nth_error (tele_insts U Id Cs) j = Some T ->
      Θ ⍮ Ξ ⍮ Γ ⊢ C ≈ R : T.
Proof.
  intros * HUa HU HC HM HWR j C R T HCj HRj HTj.
  destruct (nbes_length _ _ _ _ _ _ HM) as [HlR HlA'].
  destruct (nth_error_lt_some Ms j ltac:(rewrite <- HlR; apply List.nth_error_Some; congruence)) as [M HMj].
  destruct (nth_error_lt_some (tele_insts U Id Ms) j ltac:(rewrite HlA'; apply List.nth_error_Some; congruence)) as [T' HT'j].
  destruct (nbes_nth _ _ _ _ _ _ HM _ _ _ _ HMj HT'j HRj) as [HMt HMn].
  pose proof (nbes_upto_proofs_eq _ _ _ _ _ _ _ _ HUa HU HC HM HWR _ _ _ _ HCj HMj HTj) as HCM.
  pose proof (soundness' HMt HMn) as HMR.
  assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by exact (ctx_app_wf_tail _ _ _ _ HU).
  destruct (@tele_insts_cong_upto (gc_mk Θ Ξ) U Γ Γ Id Id Cs Ms HUa HU (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ HΓ))
              j T T' HTj HT'j) as (S & HS & HTT).
  { intros j' N N' T0 _ HN HN' HT0; exact (nbes_upto_proofs_eq _ _ _ _ _ _ _ _ HUa HU HC HM HWR _ _ _ _ HN HN' HT0). }
  eapply wf_exp_eq_trans; [ exact HCM |].
  eapply wf_exp_eq_conv_sort; [ exact HMR | exact (presup_exp_eq_left HTT) | exact HS | exact (wf_exp_eq_sym _ _ _ _ _ _ HTT) ].
Qed.

(** The arguments of an instance and the normal forms of another of its
    view, both keyed, moved under more binders, are equal at the
    parameters' types at the first. *)
Lemma inst_args_eq : forall Θ Ξ Γu U Cs Ws Ms Rs Ψ φ,
    all_assumptions U -> ctx_scoped 0 U -> ⊢ Θ ⍮ Ξ ⍮ U ++ Γu ->
    nbes Θ Ξ Γu Cs (tele_insts U Id Cs) Ws -> nbes Θ Ξ Γu Ms (tele_insts U Id Ms) Rs -> nfs_eq_upto_proofs Ws Rs ->
    Θ ⍮ Ξ ⍮ Ψ ⊢ʷ φ : Γu ->
    forall j N N' T, List.nth_error (List.map (fun C => C[φ]ʷ) Cs) j = Some N ->
      List.nth_error (List.map (fun R => (nf_to_exp R)[φ]ʷ) Rs) j = Some N' ->
      List.nth_error (tele_insts U Id (List.map (fun C => C[φ]ʷ) Cs)) j = Some T -> Θ ⍮ Ξ ⍮ Ψ ⊢ N ≈ N' : T.
Proof.
  intros * Ha Hs HU HC HM HWR Hφ j N N' T HN HN' HT.
  rewrite List.nth_error_map in HN, HN'.
  destruct (List.nth_error Cs j) as [C |] eqn:HCj; [| discriminate ]; injection HN as <-.
  destruct (List.nth_error Rs j) as [R |] eqn:HRj; [| discriminate ]; injection HN' as <-.
  assert (Em : List.map (fun C => C[φ]ʷ) Cs = List.map (fun C => C[ι φ]) Cs)
    by (apply List.map_ext; intros; symmetry; apply exp_sub_of_wk).
  rewrite Em, <- (tele_insts_sub U 0 Id Id (ι φ) Cs Ha Hs ltac:(intros x Hx; lia)), List.nth_error_map in HT.
  destruct (List.nth_error (tele_insts U Id Cs) j) as [T0 |] eqn:HT0; [| discriminate ]; injection HT as <-.
  pose proof (nbes_upto_proofs_eq_nf _ _ _ _ _ _ _ _ Ha HU HC HM HWR _ _ _ _ HCj HRj HT0) as H.
  rewrite exp_sub_of_wk; exact (wk_preserves_exp_eq _ _ _ _ _ _ _ _ H Hφ).
Qed.

(** ** Syntax *)

Lemma wk_pat_app_lt : forall pre rest x, x < pat_nargs pre -> wk_pat (pre ++ rest) x = wk_pat pre x.
Proof.
  induction pre as [| [] pre IH]; intros rest x Hx; cbn in Hx |- *; [ lia | |].
  - unfold wk_compose; rewrite IH by exact Hx; reflexivity.
  - destruct x as [| x]; cbn; [ reflexivity |]; rewrite IH by lia; reflexivity.
Qed.

Lemma wk_pat_app_ge : forall pre rest y, wk_pat (pre ++ rest) (pat_nargs pre + y) = List.length pre + wk_pat rest y.
Proof.
  induction pre as [| [] pre IH]; intros rest y; cbn [List.app pat_nargs wk_pat List.length]; [ reflexivity | |].
  - unfold wk_compose, wk_shift; rewrite IH; lia.
  - cbn; rewrite IH; reflexivity.
Qed.

Lemma wk_pat_falses_trues : forall np n y,
    wk_pat (List.repeat false np ++ List.repeat true n) y = if y <? np then y else y + n.
Proof.
  induction np as [| np IH]; intros n y; cbn [List.repeat List.app wk_pat].
  - induction n as [| n IHn]; cbn [List.repeat wk_pat]; [ destruct (y <? 0) eqn:E; [ apply Nat.ltb_lt in E; lia | lia ] |].
    unfold wk_compose, wk_shift; rewrite IHn; destruct (y <? 0) eqn:E; [ apply Nat.ltb_lt in E; lia | lia ].
  - destruct y as [| y]; cbn; [ reflexivity |]; rewrite IH.
    change (S (if y <? np then y else y + n) = (if S y <? S np then S y else S y + n)).
    destruct (y <? np) eqn:E; destruct (S y <? S np) eqn:E'; apply Nat.ltb_lt in E || apply Nat.ltb_ge in E;
      apply Nat.ltb_lt in E' || apply Nat.ltb_ge in E'; lia.
Qed.

Lemma wk_pat_trues : forall m x, wk_pat (List.repeat true m) x = x + m.
Proof. induction m as [| m IH]; intros x; cbn; [ lia | unfold wk_compose, wk_shift; rewrite IH; lia ]. Qed.

(** A term over the pattern [pre], weakened past [np] more binders and [n]
    [Self]s, with the [Self]s instantiated by [Xs], is the term over
    [pre]. *)
Lemma wk_classify_sub : forall pre np n A Xs, List.length Xs = n ->
    A[wk_pat (pre ++ List.repeat false np ++ List.repeat true n)]ʷ[sb_qn (List.length pre + np) (sb_of_list Id Xs)] = A[wk_pat pre]ʷ.
Proof.
  intros * HXs; rewrite <- exp_sub_of_wk, exp_sub_sub, <- (exp_sub_of_wk A (wk_pat _)).
  apply exp_sub_sb_eq; intros x; rewrite sb_compose_var, !sb_of_wk_var; cbn [sentry_sub].
  destruct (Nat.lt_ge_cases x (pat_nargs pre)) as [Hx | Hx].
  - rewrite wk_pat_app_lt by exact Hx.
    pose proof (wk_pat_bound pre 0 x ltac:(lia)) as Hb.
    rewrite sb_qn_lt by lia; reflexivity.
  - replace x with (pat_nargs pre + (x - pat_nargs pre)) by lia.
    rewrite wk_pat_app_ge, wk_pat_ge, wk_pat_falses_trues.
    set (y := x - pat_nargs pre).
    destruct (y <? np) eqn:E; [ apply Nat.ltb_lt in E | apply Nat.ltb_ge in E ].
    + rewrite sb_qn_lt by lia; reflexivity.
    + rewrite sb_qn_ge by lia.
      replace (List.length pre + (y + n) - (List.length pre + np)) with (List.length Xs + (y - np)) by lia.
      rewrite sb_of_list_ge; cbn; f_equal; lia.
Qed.

Lemma image_pat_some : forall pat T A, image_pat pat T = Some A -> T = A[wk_pat pat]ʷ.
Proof.
  intros * H; unfold image_pat in H.
  destruct (exp_eq_dec T T[unwk_pat pat]ʷ[wk_pat pat]ʷ) as [E |]; [| discriminate ].
  injection H as <-; exact E.
Qed.

Lemma image_pats_some : forall pat Ts As, image_pats pat Ts = Some As -> Ts = List.map (fun A => A[wk_pat pat]ʷ) As.
Proof.
  induction Ts as [| T Ts IH]; intros As H; cbn in H; [ injection H as <-; reflexivity |].
  destruct (image_pat pat T) as [A |] eqn:E1; [| discriminate ].
  destruct (image_pats pat Ts) as [As' |] eqn:E2; [| discriminate ].
  injection H as <-; cbn; rewrite <- (image_pat_some _ _ _ E1), <- (IH _ eq_refl); reflexivity.
Qed.

Lemma apps_app_head_args : forall M, M = apps (app_head M) (app_args M).
Proof.
  induction M; cbn; try reflexivity.
  rewrite apps_exp_app; cbn; rewrite <- IHM1; reflexivity.
Qed.

(** ** The [Self]s Instantiated

    [sb_selfs p b n t] sends the [n] [Self]s, [b] binders up, to the type
    formers of the members of the group at [p] at the [t] frames'
    parameters. *)

Lemma length_self_insts : forall p n t,
    List.length (List.map (fun j => apps (a_ind p j) (vars_from 0 t)) (List.seq 0 n)) = n.
Proof. intros; rewrite List.length_map, List.length_seq; reflexivity. Qed.

Lemma self_var_sub : forall p b n t x, b <= x -> x < b + n ->
    (a_var x)[sb_selfs p b n t] = apps (a_ind p (n - 1 - (x - b))) (vars_from b t).
Proof.
  intros * H1 H2; unfold sb_selfs; cbn [exp_sub].
  rewrite sb_qn_ge by lia.
  rewrite (sb_of_list_nth _ _ _ a_prop) by (rewrite length_self_insts; lia).
  rewrite length_self_insts.
  rewrite (List.nth_indep _ a_prop (apps (a_ind p 0) (vars_from 0 t))) by (rewrite length_self_insts; lia).
  rewrite (List.map_nth (fun j => apps (a_ind p j) (vars_from 0 t))), List.seq_nth by lia.
  cbn [sentry_wk sentry_exp]; rewrite apps_exp_wk, vars_from_wk_shiftn; cbn; reflexivity.
Qed.

(** ** A Classified Argument Is Its Filed Entry

    An argument classified ([classify_arg]) and numbered ([classified_carg_num]) is filed
    as an entry whose type is the argument with the [Self]s instantiated,
    when the filed group [D] has the declared members as type formers
    ([Hdecl]) and the views at their instances ([Hview]): its [n]-th member
    on is the [v]-th view, the container's member at the view's uniform
    arguments with the [Self]s instantiated. *)

(** The type of the entry a filed argument adds to the arguments' context
    ([cargs_ctx_aux]), the arguments before it recursive as [pat] says. *)
Definition carg_entry (pq : qname) (D : ind_decl) (nn : nat) (pat : list bool) (g : carg) : typ :=
  match g with ca_arg _ A => A[wk_pat pat]ʷ | ca_rec t => ptyp_ty pq D nn pat t end.

(** The tag of that entry: a non-recursive argument's own, a recursive
    one's relevant. *)
Definition carg_entry_kind (g : carg) : abs_kind :=
  match g with ca_arg κ _ => κ | ca_rec _ => ak_relevant end.

Lemma cargs_ctx_aux_single : forall pq D nn pat g,
    cargs_ctx_aux pq D nn pat (g :: nil) = ce_ass (carg_entry_kind g) (carg_entry pq D nn pat g) :: nil.
Proof. intros; destruct g; reflexivity. Qed.

Lemma classified_carg_num_bit : forall n Vs g g', classified_carg_num n Vs g = Some g' ->
    classified_carg_bit g = match g' with ca_rec _ => true | ca_arg _ _ => false end.
Proof.
  intros * H; destruct g as [A | r]; cbn in H; [ injection H as <-; reflexivity |].
  destruct (classified_ptyp_num n Vs r); [ injection H as <-; reflexivity | discriminate ].
Qed.

(** ** A Shape as Written

    A shape the classification reads is the term it was read off
    ([classify_shape_exp]): a [Self] at the uniform parameters, a type
    former or a record at its instance, under [Π]s over [Self]-free
    domains, each part weakened back as the classification strengthened
    it. *)

Section Shapes.
  Variables (nu np n : nat) (pat : list bool).

  (** An instance's argument, over the uniform parameters, the [Self]s and
      the frames', under [d] domains: weakened past the domains, the
      arguments before and the non-uniform parameters. *)
  Definition inst_wk (d : nat) (C : exp) : exp := C[wk_pat (List.repeat true (d + List.length pat + (np - nu)))]ʷ.

  (** A [Self]-free part under [d] domains, weakened back. *)
  Definition rest_wk (d : nat) (N : exp) : exp := N[wk_pat (classify_pat d np n pat)]ʷ.

  (** The term a shape as written stands for, under [d] domains. *)
  Fixpoint written_ptyp_exp (d : nat) (t : written_ptyp) : exp :=
    match t with
    | classified_ptyp_self j Ps =>
        apps (a_var (d + List.length pat + np + (n - 1 - j))) (vars_from (d + List.length pat + (np - nu)) nu ++ List.map (rest_wk d) Ps)
    | classified_ptyp_nest (vi_ind qc k Cs) Ns => apps (a_ind qc k) (List.map (inst_wk d) Cs ++ List.map (rest_wk d) Ns)
    | classified_ptyp_nest (vi_record qr Is) Ns => apps (a_record qr) (List.map (inst_wk d) Is ++ List.map (rest_wk d) Ns)
    | classified_ptyp_pi B t' => a_pi ak_relevant ak_relevant (rest_wk d B) (written_ptyp_exp (S d) t')
    end.

  (** The term an argument as written stands for. *)
  Definition written_carg_exp (g : written_carg) : exp :=
    match g with
    | classified_carg_arg _ A => A[wk_pat (classify_pat 0 np n pat)]ʷ
    | classified_carg_rec_case t => written_ptyp_exp 0 t
    end.

  (** The declared members a shape ends in are among the [n]. *)
  Fixpoint ptyp_selfs_lt {K : Set} (t : classified_ptyp_of K) : Prop :=
    match t with
    | classified_ptyp_self j _ => j < n
    | classified_ptyp_nest _ _ => True
    | classified_ptyp_pi _ t' => ptyp_selfs_lt t'
    end.

  Variable (grp_nu : qname -> nat -> option nat) (rec_np : qname -> option nat).

  (** The instances a shape nests at are of filed groups and records, at
      all their uniform parameters, a record at no non-uniform one. *)
  Fixpoint ptyp_nests_ok (t : written_ptyp) : Prop :=
    match t with
    | classified_ptyp_self _ _ => True
    | classified_ptyp_nest (vi_ind qc k Cs) _ => grp_nu qc k = Some (List.length Cs)
    | classified_ptyp_nest (vi_record qr Is) Ns => rec_np qr = Some (List.length Is) /\ Ns = nil
    | classified_ptyp_pi _ t' => ptyp_nests_ok t'
    end.

  Lemma image_pats_length : forall pat' Ts As, image_pats pat' Ts = Some As -> List.length As = List.length Ts.
  Proof. intros * H; rewrite (image_pats_some _ _ _ H), List.length_map; reflexivity. Qed.

  (** A shape headed by a [Self], a type former or a record. *)
  Lemma classify_head_exp : forall d T t,
      match app_head T with
      | a_var x => classify_self nu np n pat d x (app_args T)
      | a_ind qc k => classify_nest grp_nu nu np n pat d qc k (app_args T)
      | a_record qr => classify_record_view rec_np nu np n pat d qr (app_args T)
      | _ => None
      end = Some t ->
      T = written_ptyp_exp d t /\ ptyp_selfs_lt t /\ ptyp_nests_ok t.
  Proof.
    intros * H; rewrite (apps_app_head_args T); set (args := app_args T) in *.
    destruct (app_head T) eqn:Eh; try discriminate.
    - (** A type former at an instance *)
      match goal with Eh : app_head T = a_ind ?a ?c |- _ => rename a into qc; rename c into k end.
      unfold classify_nest in H.
      destruct (grp_nu qc k) as [m |] eqn:Em; [| discriminate ].
      destruct (m <=? List.length args) eqn:Eml; [| discriminate ]; apply Nat.leb_le in Eml.
      destruct (image_pats (List.repeat true (d + List.length pat + (np - nu))) (List.firstn m args)) as [Cs |] eqn:ECs;
        [| discriminate ].
      destruct (image_pats (classify_pat d np n pat) (List.skipn m args)) as [Ns |] eqn:ENs; [| discriminate ].
      destruct (selfs_occur nu n Cs); [| discriminate ].
      injection H as <-; cbn [written_ptyp_exp ptyp_selfs_lt ptyp_nests_ok]; split; [| split; [ exact I |] ].
      + rewrite <- (List.firstn_skipn m args) at 1; rewrite (image_pats_some _ _ _ ECs), (image_pats_some _ _ _ ENs); reflexivity.
      + rewrite Em, (image_pats_length _ _ _ ECs), List.length_firstn; f_equal; lia.
    - (** A [Self] *)
      match goal with Eh : app_head T = a_var ?a |- _ => rename a into x end.
      unfold classify_self in H.
      set (b := d + List.length pat + np) in *.
      destruct ((b <=? x) && (x <? b + n))%bool eqn:Eb; [| discriminate ].
      apply andb_prop in Eb as [Eb1 Eb2]; apply Nat.leb_le in Eb1; apply Nat.ltb_lt in Eb2.
      destruct (list_eq_dec exp_eq_dec (List.firstn nu args) (vars_from (d + List.length pat + (np - nu)) nu))
        as [Ef |]; [| discriminate ].
      destruct (image_pats (classify_pat d np n pat) (List.skipn nu args)) as [Ps |] eqn:EPs; [| discriminate ].
      cbn in H; injection H as <-; cbn [written_ptyp_exp ptyp_selfs_lt ptyp_nests_ok]; split; [| split; [ lia | exact I ] ].
      rewrite <- (List.firstn_skipn nu args) at 1; rewrite Ef, (image_pats_some _ _ _ EPs).
      fold b; replace (b + (n - 1 - (n - 1 - (x - b)))) with x by lia; reflexivity.
    - (** A record at an instance *)
      match goal with Eh : app_head T = a_record ?a |- _ => rename a into qr end.
      unfold classify_record_view in H.
      destruct (rec_np qr) as [m |] eqn:Em; [| discriminate ].
      destruct (Nat.eqb m (List.length args)) eqn:Eml; [| discriminate ]; apply Nat.eqb_eq in Eml.
      destruct (image_pats (List.repeat true (d + List.length pat + (np - nu))) args) as [Is |] eqn:EIs; [| discriminate ].
      destruct (selfs_occur nu n Is && selfs_guarded nu n Is)%bool; [| discriminate ].
      injection H as <-; cbn [written_ptyp_exp ptyp_selfs_lt ptyp_nests_ok List.map]; split; [| split; [ exact I |] ].
      + rewrite List.app_nil_r; unfold inst_wk; rewrite <- (image_pats_some _ _ _ EIs); reflexivity.
      + rewrite Em, (image_pats_length _ _ _ EIs), Eml; split; reflexivity.
  Qed.

  Lemma classify_shape_exp : forall T d t, classify_shape grp_nu rec_np nu np n pat d T = Some t ->
      T = written_ptyp_exp d t /\ ptyp_selfs_lt t /\ ptyp_nests_ok t.
  Proof.
    induction T; intros d0 t0 Hc.
    all: try solve [ eapply classify_head_exp; exact Hc ].
    match type of Hc with classify_shape _ _ _ _ _ _ _ (a_pi ?k1 ?k2 _ _) = _ =>
      destruct k1; destruct k2; try solve [ eapply classify_head_exp; exact Hc ] end.
    cbn [classify_shape] in Hc.
    destruct (image_pat (classify_pat d0 np n pat) T1) as [B0 |] eqn:EB; [| discriminate ].
    destruct (classify_shape grp_nu rec_np nu np n pat (S d0) T2) as [r' |] eqn:Er; [| discriminate ].
    cbn in Hc; injection Hc as <-.
    destruct (IHT2 _ _ Er) as (E2 & Hl2 & Hn2); cbn [written_ptyp_exp ptyp_selfs_lt ptyp_nests_ok]; split; [| split; assumption ].
    rewrite (image_pat_some _ _ _ EB), <- E2; reflexivity.
  Qed.

  Lemma classify_arg_exp : forall T g, classify_arg grp_nu rec_np nu np n pat T = Some g ->
      T = written_carg_exp g /\ match g with classified_carg_rec_case t => ptyp_selfs_lt t /\ ptyp_nests_ok t | _ => True end.
  Proof.
    intros * Hc; unfold classify_arg in Hc.
    destruct (image_pat (classify_pat 0 np n pat) T) as [A |] eqn:EA.
    - injection Hc as <-; split; [ exact (image_pat_some _ _ _ EA) | exact I ].
    - destruct (classify_shape grp_nu rec_np nu np n pat 0 T) as [r |] eqn:Er; [| discriminate ].
      injection Hc as <-; exact (classify_shape_exp _ _ _ Er).
  Qed.

End Shapes.

(** The instance a key stands for: its arguments read back. *)
Definition key_inst (x : view_key) : view_inst :=
  match x with
  | vk_ind qc k Ws => vi_ind qc k (List.map nf_to_exp Ws)
  | vk_record qr Ws => vi_record qr (List.map nf_to_exp Ws)
  end.

(** The view a key is filed as among the keys [Ks]: the first of its view. *)
Definition key_rep (Ks : list view_key) (x : view_key) : view_key :=
  match view_key_index x Ks with Some v => List.nth v Ks x | None => x end.

(** A classified shape with each instance the one its filed view stands
    for. *)
Fixpoint ptyp_rep (Ks : list view_key) (t : classified_ptyp) : written_ptyp :=
  match t with
  | classified_ptyp_self j Ps => classified_ptyp_self j Ps
  | classified_ptyp_nest x Ns => classified_ptyp_nest (key_inst (key_rep Ks x)) Ns
  | classified_ptyp_pi B t' => classified_ptyp_pi B (ptyp_rep Ks t')
  end.

(** A classified argument with its instance the one its filed view stands
    for. *)
Definition carg_rep (Ks : list view_key) (g : classified_carg) : written_carg :=
  match g with
  | classified_carg_arg κ A => classified_carg_arg κ A
  | classified_carg_rec_case t => classified_carg_rec_case (ptyp_rep Ks t)
  end.

(** A shape as classified is equal to the one with each instance that of
    its filed view: an instance and its filed view's are of one view, so
    their arguments are equal ([inst_args_eq]), and so are the type
    formers at them ([ind_nest_eq], [record_apps_args_conv]), under the
    same [Π]s. *)
Lemma ptyp_rep_eq : forall Θ Ξ Γu Ks nu np n pat tw tc,
    written_ptyp_key Θ Ξ Γu tw tc ->
    ptyp_nests_ok (grp_info Θ Ξ) (rec_info Θ Ξ) tw ->
    (forall x, In x (classified_ptyp_view tc) -> view_key_eq x (key_rep Ks x) /\ exists y, view_inst_key Θ Ξ Γu y (key_rep Ks x)) ->
    ⊢ Θ ⍮ Ξ ⍮ Γu ->
    forall d Ψ i, Θ ⍮ Ξ ⍮ Ψ ⊢ʷ wk_pat (List.repeat true (d + List.length pat + (np - nu))) : Γu ->
      Θ ⍮ Ξ ⍮ Ψ ⊢ written_ptyp_exp nu np n pat d tw : Typeω@i ->
      exists i', Θ ⍮ Ξ ⍮ Ψ ⊢ written_ptyp_exp nu np n pat d tw ≈ written_ptyp_exp nu np n pat d (ptyp_rep Ks tc) : Typeω@i'.
Proof.
  intros * Hkey; induction Hkey as [j Ps | x y Ns Hxy | B tw tc Hk IH]; intros Hok Hreps HΓu d Ψ i Hφ HT.
  - (** A declared member: as written *)
    exists i; cbn [ptyp_rep]; apply wf_exp_eq_refl; exact HT.
  - (** A nested occurrence: the instance, and its filed view's *)
    cbn [classified_ptyp_view] in Hreps; destruct (Hreps y (or_introl eq_refl)) as [Hyr (y' & Hy')].
    cbn [ptyp_rep].
    remember (key_rep Ks y) as r eqn:Er; clear Er Hreps.
    destruct Hxy as [qc k Cs D' Ws Hl HCs | qr Is Rr Ws Hl HIs].
    + destruct Hy' as [qc' k' Ms D'' Rs Hl' HMs | qr' Is' Rr' Rs Hl' HIs'];
        [| exfalso; destruct (view_key_eq_parts _ _ Hyr) as (_ & Hrec & _); discriminate Hrec ].
      destruct (view_key_eq_parts _ _ Hyr) as (Eh & _ & HWR); cbn in Eh, HWR; injection Eh as <- <-.
      rewrite Hl in Hl'; injection Hl' as <-.
      cbn [key_inst written_ptyp_exp] in HT |- *.
      cbn [ptyp_nests_ok] in Hok; unfold grp_info in Hok; rewrite Hl in Hok.
      destruct (k <? ind_ndecl D') eqn:Elt; [| discriminate ]; injection Hok as Hnu.
      destruct (decl_of_lookup _ _ _ _ _ HΓu Hl) as [HD Hc].
      assert (HU : ⊢ Θ ⍮ Ξ ⍮ ind_uparams D' ++ Γu)
        by (apply wf_ctx_closed_app; [ exact (decl_typed_ass _ _ _ HD) | exact (decl_closed_uparams _ Hc)
                                     | exact (decl_typed_uparams_field _ _ _ HD) | exact HΓu ]).
      destruct (nbes_length _ _ _ _ _ _ HCs) as [HlW _]; destruct (nfs_eq_upto_proofs_nth _ _ HWR) as [HlWR _].
      rewrite List.map_map.
      eapply ind_nest_eq; [ exact Hl | rewrite List.length_map; symmetry; exact Hnu | rewrite !List.length_map; lia
                          | exact HT |].
      intros j N N' T HN HN' HTj.
      exact (inst_args_eq _ _ _ _ _ _ _ _ _ _ (decl_typed_ass _ _ _ HD) (decl_closed_uparams _ Hc) HU HCs HMs HWR Hφ
               j N N' T HN HN' HTj).
    + destruct Hy' as [qc' k' Ms D'' Rs Hl' HMs | qr' Is' Rr' Rs Hl' HIs'];
        [ exfalso; destruct (view_key_eq_parts _ _ Hyr) as (_ & Hrec & _); discriminate Hrec |].
      destruct (view_key_eq_parts _ _ Hyr) as (Eh & _ & HWR); cbn in Eh, HWR; injection Eh as <-.
      rewrite Hl in Hl'; injection Hl' as <-.
      cbn [ptyp_nests_ok] in Hok; destruct Hok as [Hok ->]; unfold rec_info in Hok; rewrite Hl in Hok; injection Hok as Hnp.
      cbn [key_inst written_ptyp_exp List.map] in HT |- *; rewrite !List.app_nil_r in HT |- *.
      destruct (@record_params_facts (gc_mk Θ Ξ) Γu qr Rr HΓu Hl) as (Ht & Hc & HU).
      destruct (nbes_length _ _ _ _ _ _ HIs) as [HlW _]; destruct (nfs_eq_upto_proofs_nth _ _ HWR) as [HlWR _].
      assert (HΨ : ⊢ Θ ⍮ Ξ ⍮ Ψ) by (gen_presups; assumption).
      assert (HL : List.length (List.map (inst_wk nu np pat d) Is) = List.length (record_params Rr))
        by (rewrite List.length_map; symmetry; exact Hnp).
      rewrite List.map_map, ?List.app_nil_r.
      eapply record_apps_args_conv; [ exact HΨ | exact Hl | exact HL | rewrite List.length_map; lia | |].
      * exact (@wf_record_apps_inv (gc_mk Θ Ξ) Ψ qr Rr _ _ Hl HT HL).
      * intros j N N' T HN HN' HTj.
        exact (inst_args_eq _ _ _ _ _ _ _ _ _ _ (typed_params_ass _ _ _ Ht) (closed_params _ Hc) HU HIs HIs' HWR Hφ
                 j N N' T HN HN' HTj).
  - (** A [Π] over a [Self]-free domain: the shapes under it *)
    cbn [written_ptyp_exp ptyp_rep] in HT |- *.
    cbn [ptyp_nests_ok] in Hok.
    cbn [classified_ptyp_view] in Hreps.
    destruct (wf_pi_inversion_at HT) as [U HU HB Hbody _ _].
    assert (HB1 : exists i1, Θ ⍮ Ξ ⍮ Ψ ⊢ rest_wk np n pat d B : Typeω@i1) by exact (wf_exp_is_univ_large HU HB).
    destruct HB1 as [i1 HB1].
    assert (Hbody1 : exists i2, Θ ⍮ Ξ ⍮ Ψ ▹{ak_relevant} rest_wk np n pat d B ⊢ written_ptyp_exp nu np n pat (S d) tw : Typeω@i2).
    { destruct (is_univ_cases _ _ _ _ HU) as [[i0 ->] | (L & m & -> & HL)]; cbn in Hbody; [ eexists; exact Hbody |].
      exists 0; eapply wf_exp_suniv_large; [| exact Hbody ].
      eapply wk_preserves_exp in HL; [ exact HL |].
      apply wf_wk_shift; gen_presups; assumption. }
    destruct Hbody1 as [i2 Hbody1].
    assert (Hext : ⊢ Θ ⍮ Ξ ⍮ Ψ ▹{ak_relevant} rest_wk np n pat d B) by (gen_presups; assumption).
    assert (Hφ' : Θ ⍮ Ξ ⍮ Ψ ▹{ak_relevant} rest_wk np n pat d B ⊢ʷ wk_pat (List.repeat true (S d + List.length pat + (np - nu))) : Γu)
      by (cbn [Nat.add List.repeat wk_pat]; eapply wf_wk_compose; [ exact (wf_wk_shift _ _ _ _ Hext) | exact Hφ ]).
    destruct (IH Hok Hreps HΓu (S d) _ i2 Hφ' Hbody1) as [i' Hi'].
    destruct (wf_exp_eq_pi_sort_at _ _ _ ak_relevant ak_relevant _ _ _ _ Typeω@i1 i' HB1 ltac:(constructor)
                (wf_exp_eq_refl HB1) Hi' ltac:(discriminate)) as [j Hj].
    exists j; exact Hj.
Qed.

Section Filed.
  Variables (p : qname) (D : ind_decl) (Ks : list view_key) (nu n t nn : nat).
  Hypothesis HDnu : ind_nu D = nu + t.
  Hypothesis Hdecl : forall i Us Ns, i < n -> ind_mty p D i Us Ns = apps (a_ind p i) (Us ++ Ns).
  Hypothesis Hview : forall v x, List.nth_error Ks v = Some x ->
    (forall C, In C (view_key_args x) -> exp_scoped (nu + t) (nf_to_exp C)[sb_selfs p nu n t] /\ exp_mvc 0 (nf_to_exp C)[sb_selfs p nu n t]) /\
    forall Us Ns, ind_mty p D (n + v) Us Ns
                  = apps (view_key_head x) (List.map (fun C => (nf_to_exp C)[sb_selfs p nu n t][sb_of_list Id Us]) (view_key_args x) ++ Ns).
  (** A classified shape, its instances those of their filed views, with
      the [Self]s instantiated is the filed shape's type. *)
  Lemma ptyp_rep_filed : forall pat tc d s, ptyp_selfs_lt n tc -> classified_ptyp_num n Ks tc = Some s ->
      (written_ptyp_exp nu (nn + nu) n pat d (ptyp_rep Ks tc))[sb_selfs p (d + List.length pat + (nn + nu)) n t]
      = ptyp_ty p D nn (List.repeat false d ++ pat) s.
  Proof.
    intros pat tc; induction tc as [j Ps | x Ns | B tc IH]; intros d s Hlt Hs.
    2:{ (** A nested occurrence: the view of its instance. *)
      cbn [classified_ptyp_num] in Hs.
      destruct (view_key_index x Ks) as [v |] eqn:Ev; [| discriminate ]; cbn in Hs; injection Hs as <-.
      cbn [ptyp_rep]; unfold key_rep; rewrite Ev.
      destruct (view_key_index_in _ _ _ Ev) as (y & Hy & _).
      rewrite (List.nth_error_nth _ _ x Hy).
      destruct (Hview _ _ Hy) as [HsC Hty].
      destruct y as [qc k Ws | qr Ws]; cbn [key_inst written_ptyp_exp view_key_head view_key_args] in HsC, Hty |- *;
      cbn [ptyp_ty]; rewrite Hty;
      rewrite apps_exp_sub; cbn [exp_sub];
      rewrite List.map_app, !List.map_map;
      f_equal; f_equal;
      [ apply List.map_ext_in; intros C HC; unfold inst_wk;
        destruct (HsC _ HC) as [HCs HCm];
        unfold ind_uvars; rewrite HDnu, List.length_app, List.repeat_length;
        rewrite exp_at_vars by assumption;
        rewrite <- exp_sub_of_wk with (φ := wk_pat _),
          exp_sub_sb_eq with (σ := ι (wk_pat _)) (τ := ι (wk_shiftn (d + List.length pat + nn)));
        [ rewrite exp_sub_of_wk;
          unfold sb_selfs; replace (d + List.length pat + (nn + nu)) with ((d + List.length pat + nn) + nu) by lia;
          rewrite exp_shiftn_sub_qn; reflexivity
        | intros x0; cbn; rewrite wk_pat_trues; f_equal; lia ]
      | apply List.map_ext; intros P; unfold rest_wk;
        unfold classify_pat; rewrite List.app_assoc;
        replace (d + List.length pat + (nn + nu)) with (List.length (List.repeat false d ++ pat) + (nn + nu))
          by (rewrite List.length_app, List.repeat_length; lia);
        unfold sb_selfs; apply wk_classify_sub; apply length_self_insts
      | apply List.map_ext_in; intros C HC; unfold inst_wk;
        destruct (HsC _ HC) as [HCs HCm];
        unfold ind_uvars; rewrite HDnu, List.length_app, List.repeat_length;
        rewrite exp_at_vars by assumption;
        rewrite <- exp_sub_of_wk with (φ := wk_pat _),
          exp_sub_sb_eq with (σ := ι (wk_pat _)) (τ := ι (wk_shiftn (d + List.length pat + nn)));
        [ rewrite exp_sub_of_wk;
          unfold sb_selfs; replace (d + List.length pat + (nn + nu)) with ((d + List.length pat + nn) + nu) by lia;
          rewrite exp_shiftn_sub_qn; reflexivity
        | intros x0; cbn; rewrite wk_pat_trues; f_equal; lia ]
      | apply List.map_ext; intros P; unfold rest_wk;
        unfold classify_pat; rewrite List.app_assoc;
        replace (d + List.length pat + (nn + nu)) with (List.length (List.repeat false d ++ pat) + (nn + nu))
          by (rewrite List.length_app, List.repeat_length; lia);
        unfold sb_selfs; apply wk_classify_sub; apply length_self_insts ]. }
    2:{ (** A [Π] over a [Self]-free domain. *)
      cbn [classified_ptyp_num] in Hs.
      destruct (classified_ptyp_num n Ks tc) as [s' |] eqn:Es; [| discriminate ]; cbn in Hs; injection Hs as <-.
      cbn [ptyp_rep written_ptyp_exp exp_sub ptyp_ty ptyp_selfs_lt] in Hlt |- *; f_equal.
      - unfold rest_wk, classify_pat; rewrite List.app_assoc.
        replace (d + List.length pat + (nn + nu)) with (List.length (List.repeat false d ++ pat) + (nn + nu))
          by (rewrite List.length_app, List.repeat_length; lia).
        unfold sb_selfs; apply wk_classify_sub; apply length_self_insts.
      - exact (IH (S d) s' Hlt eq_refl). }
    (** A [Self]: the type former of its declared member. *)
    cbn in Hs; injection Hs as <-; cbn [ptyp_rep written_ptyp_exp ptyp_selfs_lt] in Hlt |- *.
    set (b := d + List.length pat + (nn + nu)) in *.
    cbn [ptyp_ty]; rewrite Hdecl by lia.
    rewrite apps_exp_sub, self_var_sub by lia.
    replace (n - 1 - (b + (n - 1 - j) - b)) with j by lia.
    rewrite List.map_app, List.map_map; unfold rest_wk.
    unfold sb_selfs at 1; rewrite vars_from_sub by (unfold b; lia); fold (sb_selfs p b n t).
    rewrite <- !apps_exp_app; f_equal.
    unfold ind_uvars; rewrite HDnu, List.length_app, List.repeat_length.
    rewrite List.app_assoc; f_equal.
    * replace (d + List.length pat + (nn + nu - nu)) with (d + List.length pat + nn) by lia.
      replace (nu + t) with (t + nu) by lia; rewrite <- vars_from_app; f_equal; f_equal; unfold b; lia.
    * apply List.map_ext; intros P.
      unfold classify_pat; rewrite List.app_assoc.
      replace b with (List.length (List.repeat false d ++ pat) + (nn + nu))
        by (unfold b; rewrite List.length_app, List.repeat_length; lia).
      unfold sb_selfs; apply wk_classify_sub; apply length_self_insts.
  Qed.

  Lemma carg_rep_filed : forall pat g g',
      match g with classified_carg_rec_case tc => ptyp_selfs_lt n tc | _ => True end ->
      classified_carg_num n Ks g = Some g' ->
      (written_carg_exp nu (nn + nu) n pat (carg_rep Ks g))[sb_selfs p (List.length pat + (nn + nu)) n t] = carg_entry p D nn pat g'.
  Proof.
    intros pat [κ A | tc] g' Hlt Hn; cbn in Hn.
    - injection Hn as <-; cbn [carg_rep written_carg_exp carg_entry].
      unfold classify_pat; cbn [List.repeat List.app].
      unfold sb_selfs; apply wk_classify_sub; apply length_self_insts.
    - destruct (classified_ptyp_num n Ks tc) as [s |] eqn:Es; [| discriminate ]; injection Hn as <-.
      cbn [carg_rep written_carg_exp carg_entry].
      exact (ptyp_rep_filed _ _ 0 _ Hlt Es).
  Qed.

End Filed.

(** ** The Filed Group

    [raw_decl_filed] files the declared members in order, then the views, each
    the container's member at its instance. *)

Lemma Forall2_nth_error_l : forall {X Y} (Rl : X -> Y -> Prop) l1 l2 i a,
    Forall2 Rl l1 l2 -> List.nth_error l1 i = Some a -> exists b, List.nth_error l2 i = Some b /\ Rl a b.
Proof.
  intros X Y Rl l1 l2 i a H; revert i; induction H as [| a1 b1 l1 l2 Hab H IH]; intros [| i] Hi; cbn in Hi; try discriminate.
  - injection Hi as <-; exists b1; split; [ reflexivity | exact Hab ].
  - exact (IH _ Hi).
Qed.

Lemma raw_members_filed_length : forall Ξ n Vs ms css Ms, raw_members_filed Ξ n Vs ms css = Some Ms -> List.length Ms = List.length ms.
Proof.
  induction ms as [| Mr ms IH]; intros [| cs css] Ms H; cbn in H; try discriminate; [ injection H as <-; reflexivity |].
  destruct (classified_cons_num n Vs cs); [| discriminate ].
  destruct (raw_members_filed Ξ n Vs ms css) as [Ms' |] eqn:E; [| discriminate ]; injection H as <-; cbn; f_equal; eapply IH; exact E.
Qed.

Lemma raw_members_filed_nth : forall Ξ n Vs ms css Ms, raw_members_filed Ξ n Vs ms css = Some Ms ->
    forall j Mr cs, List.nth_error ms j = Some Mr -> List.nth_error css j = Some cs ->
      List.nth_error Ms j
      = option_map (fun cs' => mk_imember (mh_decl (ind_qname Ξ (raw_member_name Mr))) (raw_member_nparams Mr) cs') (classified_cons_num n Vs cs).
Proof.
  induction ms as [| Mr0 ms IH]; intros [| cs0 css] Ms H j Mr cs Hj Hc; cbn in H; try discriminate; [ destruct j; discriminate |].
  destruct (classified_cons_num n Vs cs0) as [cs0' |] eqn:E0; [| discriminate ].
  destruct (raw_members_filed Ξ n Vs ms css) as [Ms' |] eqn:E; [| discriminate ]; injection H as <-.
  destruct j as [| j]; cbn in Hj, Hc |- *.
  - injection Hj as <-; injection Hc as <-; rewrite E0; reflexivity.
  - exact (IH _ _ E _ _ _ Hj Hc).
Qed.

Lemma raw_members_filed_decl : forall Ξ n Vs ms css Ms, raw_members_filed Ξ n Vs ms css = Some Ms -> Forall (fun M => im_is_decl M = true) Ms.
Proof.
  induction ms as [| Mr ms IH]; intros [| cs css] Ms H; cbn in H; try discriminate; [ injection H as <-; constructor |].
  destruct (classified_cons_num n Vs cs); [| discriminate ].
  destruct (raw_members_filed Ξ n Vs ms css) as [Ms' |] eqn:E; [| discriminate ]; injection H as <-.
  constructor; [ reflexivity | eapply IH; exact E ].
Qed.

Lemma raw_view_filed_view : forall Θ Ξ σ n Ks x ss cs Nv M, raw_view_filed Θ Ξ σ n Ks x ss cs Nv = Some M -> im_is_decl M = false.
Proof.
  intros * H; destruct x as [qc k Cs | qr Is]; unfold raw_view_filed in H.
  - destruct (ind_lookup Θ Ξ qc); [| discriminate ].
    destruct (ind_member _ k); [| discriminate ].
    destruct (classified_cons_num n Ks cs); [| discriminate ].
    injection H as <-; reflexivity.
  - destruct (record_lookup Θ Ξ qr); [| discriminate ].
    destruct (classified_cons_num n Ks cs); [| discriminate ].
    injection H as <-; reflexivity.
Qed.

Lemma raw_views_filed_views : forall Θ Ξ σ n Ks xs Vs Ss css Nvs Mvs, raw_views_filed Θ Ξ σ n Ks xs Vs Ss css Nvs = Some Mvs ->
    Forall (fun M => im_is_decl M = false) Mvs.
Proof.
  induction xs as [| x xs IH]; intros * H; cbn in H; [ injection H as <-; constructor |].
  destruct (view_key_pos x Vs) as [w |]; [| discriminate ].
  destruct (raw_view_filed _ _ _ _ _ _ _ _ _) as [M |] eqn:E1; [| discriminate ].
  destruct (raw_views_filed Θ Ξ σ n Ks xs Vs Ss css Nvs) as [Ms' |] eqn:E2; [| discriminate ]; injection H as <-.
  constructor; [ exact (raw_view_filed_view _ _ _ _ _ _ _ _ _ _ E1) | eapply IH; exact E2 ].
Qed.

(** The [v]-th view filed is the [v]-th key's, its data read off the
    tables at the key's position among the views found. *)
Lemma raw_views_filed_nth : forall Θ Ξ σ n Ks xs Vs Ss css Nvs Mvs, raw_views_filed Θ Ξ σ n Ks xs Vs Ss css Nvs = Some Mvs ->
    forall v x, List.nth_error xs v = Some x ->
      exists w, view_key_pos x Vs = Some w /\
        List.nth_error Mvs v = raw_view_filed Θ Ξ σ n Ks x (List.nth w Ss nil) (List.nth w css nil) (List.nth w Nvs nil).
Proof.
  induction xs as [| x0 xs IH]; intros * H v x Hx; cbn in H; [ destruct v; discriminate |].
  destruct (view_key_pos x0 Vs) as [w0 |] eqn:Ew; [| discriminate ].
  destruct (raw_view_filed _ _ _ _ _ _ _ _ _) as [M |] eqn:E1; [| discriminate ].
  destruct (raw_views_filed Θ Ξ σ n Ks xs Vs Ss css Nvs) as [Ms' |] eqn:E2; [| discriminate ]; injection H as <-.
  destruct v as [| v]; cbn in Hx |- *.
  - injection Hx as <-; exists w0; split; [ exact Ew | symmetry; exact E1 ].
  - exact (IH _ _ _ _ _ E2 _ _ Hx).
Qed.

Lemma raw_views_filed_length : forall Θ Ξ σ n Ks xs Vs Ss css Nvs Mvs, raw_views_filed Θ Ξ σ n Ks xs Vs Ss css Nvs = Some Mvs ->
    List.length Mvs = List.length xs.
Proof.
  induction xs as [| x xs IH]; intros * H; cbn in H; [ injection H as <-; reflexivity |].
  destruct (view_key_pos x Vs) as [w |]; [| discriminate ].
  destruct (raw_view_filed _ _ _ _ _ _ _ _ _) as [M |] eqn:E1; [| discriminate ].
  destruct (raw_views_filed Θ Ξ σ n Ks xs Vs Ss css Nvs) as [Ms' |] eqn:E2; [| discriminate ]; injection H as <-.
  cbn; f_equal; eapply IH; exact E2.
Qed.

Lemma raw_args_tele_cons : forall y κ T args, raw_args_tele ((y, κ, T) :: args) = raw_args_tele args ++ ce_ass κ T :: nil.
Proof. reflexivity. Qed.

Lemma length_raw_args_tele : forall args, List.length (raw_args_tele args) = List.length args.
Proof. intros; unfold raw_args_tele; rewrite List.length_rev, List.length_map; reflexivity. Qed.

Lemma raw_args_tele_app : forall args1 args2, raw_args_tele (args1 ++ args2) = raw_args_tele args2 ++ raw_args_tele args1.
Proof. intros; unfold raw_args_tele; rewrite List.map_app, List.rev_app_distr; reflexivity. Qed.

(** A [Π] over assumptions of equal bodies. *)
Lemma ctx_pi_ass_eq : forall Θ Ξ Δ Γ A A' i,
    all_assumptions Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A ≈ A' : Typeω@i ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ A ≈ ctx_pi Δ A' : Typeω@j.
Proof.
  induction Δ as [| e Δ IH]; intros * Hass HΔ HA; cbn in *; [ eauto |].
  inversion Hass as [| ? ? (κ & B & ->) Hass']; subst.
  pose proof (ctx_decomp_tail HΔ) as HΔ'.
  (** The assumption is of a sort at its tag *)
  destruct (ctx_decomp_kind HΔ) as (S & HS & HB).
  destruct (wf_exp_eq_pi_sort_at _ _ _ κ ak_relevant B B A A' S i HB HS (wf_exp_eq_refl HB) HA ltac:(discriminate)) as [j Hj].
  exact (IH _ _ _ j Hass' HΔ' Hj).
Qed.

Lemma raw_decl_selfs_from_snoc : forall R j l Mr,
    raw_decl_selfs_from R j (l ++ Mr :: nil) = ce_ass ak_relevant (raw_decl_self_ty R Mr)[wk_shiftn (j + List.length l)]ʷ :: raw_decl_selfs_from R j l.
Proof.
  intros R j l; revert j; induction l as [| M0 l IH]; intros; cbn [List.app raw_decl_selfs_from List.length].
  - rewrite Nat.add_0_r; reflexivity.
  - rewrite IH; cbn [List.app]; do 4 f_equal; lia.
Qed.

Lemma tele_wk_shiftn_sb_of_list : forall Δ Xs σ,
    tele_sub (tele_wk Δ (wk_shiftn (List.length Xs))) (sb_of_list σ Xs) = tele_sub Δ σ.
Proof.
  intros; rewrite <- tele_sub_of_wk, tele_sub_sub; apply tele_sub_sb_eq.
  intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn]; rewrite Nat.add_comm; apply sb_of_list_ge.
Qed.

Lemma classified_cons_num_in : forall n Vs cs cs' c gsr, classified_cons_num n Vs cs = Some cs' -> In (c, gsr) cs ->
    exists gs, classified_cargs_num n Vs gsr = Some gs /\ In (c, gs) cs'.
Proof.
  induction cs as [| [c0 gs0] cs IH]; intros * H Hin; [ destruct Hin |]; cbn in H.
  destruct (classified_cargs_num n Vs gs0) as [gs0' |] eqn:E1; [| discriminate ].
  destruct (classified_cons_num n Vs cs) as [cs0 |] eqn:E2; [| discriminate ].
  injection H as <-.
  destruct Hin as [[= <- <-] | Hin].
  - exists gs0'; split; [ exact E1 | left; reflexivity ].
  - destruct (IH _ _ _ eq_refl Hin) as (gs & Hgs & Hin'); exists gs; split; [ exact Hgs | right; exact Hin' ].
Qed.

Lemma classify_args_in_length : forall Θ Ξ Γp nu np n pat args1 args gs,
    classify_args_in Θ Ξ Γp nu np n pat args1 args gs -> List.length gs = List.length args.
Proof. induction 1; cbn; auto. Qed.

(** The type of a constructor of the declared member [j], [Mr], with the
    arguments [args] as written, over the filed parameters: the member's
    own, the group's uniform ones and the frames' [T]; the [Self]s are
    instantiated as the type formers at the frames' parameters
    ([sb_selfs]), and the result is [Self_j] at all the member's
    parameters. *)
Definition user_con_ty (p : qname) (R : raw_decl) (Mr : raw_member) (j : nat) (T : ctx) (args : list (string * abs_kind * exp)) : typ :=
  let np := (List.length (raw_member_nparams Mr) + raw_decl_nu R)%nat in
  ctx_pi (raw_member_nparams Mr ++ raw_decl_uparams R ++ T)
    (ctx_pi (raw_args_tele args) (apps (a_var (List.length args + np + (raw_decl_nmembers R - 1 - j))) (vars_from (List.length args) np)))
      [sb_selfs p np (raw_decl_nmembers R) (List.length T)].

(** The constructor [c] of the member [j] of the group at [p] is filed, of
    a type equal to [U]. *)
#[warnings="-cannot-define-projection"]
Record filed_con_ty (Θ : gdeps) (Ξ : gstack) (p : qname) (j : nat) (c : string) (U : typ) : Prop := mk_filed_con_ty
  { (** The filed group *)
    filed_con_ty_decl : ind_decl
    (** The member [j] *)
  ; filed_con_ty_member : imember
    (** The constructor's filed argument kinds *)
  ; filed_con_ty_args : list carg
    (** The group is found at [p] *)
  ; filed_con_ty_lookup : ind_lookup Θ Ξ p = Some filed_con_ty_decl
    (** The member is the group's [j]-th *)
  ; filed_con_ty_member_at : ind_member filed_con_ty_decl j = Some filed_con_ty_member
    (** [c] is one of its constructors *)
  ; filed_con_ty_con : ind_con filed_con_ty_member c = Some filed_con_ty_args
    (** The constructor's type is equal to [U] *)
  ; filed_con_ty_ty : exists i, Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p filed_con_ty_decl j filed_con_ty_member filed_con_ty_args ≈ U : Typeω@i }.

(** A filed constructor stays filed, at its type, along an embedding. *)
Lemma gctx_embedding_preserves_filed_con_ty : forall Θ Ξ Θ2 Ξ2 p j c U,
    gctx_embedding Θ Ξ Θ2 Ξ2 -> filed_con_ty Θ Ξ p j c U -> filed_con_ty Θ2 Ξ2 p j c U.
Proof.
  intros * He [D M gs Hl Hm Hc (i & Hty)].
  apply (mk_filed_con_ty _ _ _ _ _ _ D M gs);
    [ exact (ind_lookup_gc_sub _ _ _ _ _ _ (gctx_embedding_resolution _ _ _ _ He) Hl) | exact Hm | exact Hc
    | exists i; exact (proj1 (proj2 (proj2 (gctx_embedding_preserves_wf _ _ _ _ He))) _ _ _ _ Hty) ].
Qed.

(** A classification as written meets no instance: keyed, it is itself,
    and so is its filed form. *)
Lemma ptyp_rep_none : forall Θ Ξ Γu Ks tw tc, written_ptyp_key Θ Ξ Γu tw tc -> ptyp_nests_ok grp_none rec_none tw ->
    ptyp_rep Ks tc = tw.
Proof.
  induction 1 as [j Ps | x y Ns Hxy | B tw tc _ IH]; intros Hok; cbn [ptyp_rep]; [ reflexivity | | f_equal; exact (IH Hok) ].
  destruct Hxy; cbn in Hok; [ discriminate | destruct Hok; discriminate ].
Qed.

(** Keying keeps the declared members a shape ends in. *)
Lemma ptyp_selfs_lt_key : forall Θ Ξ Γu n tw tc, written_ptyp_key Θ Ξ Γu tw tc -> ptyp_selfs_lt n tw -> ptyp_selfs_lt n tc.
Proof. induction 1; cbn; auto. Qed.

(** A numbered shape's instances have filed views. *)
Lemma ptyp_num_index : forall n Ks tc s, classified_ptyp_num n Ks tc = Some s ->
    forall x, In x (classified_ptyp_view tc) -> exists v, view_key_index x Ks = Some v.
Proof.
  intros n Ks tc; induction tc as [j Ps | y Ns | B tc IH]; intros s Hs x Hx; cbn in Hs, Hx; [ destruct Hx | |].
  - destruct Hx as [-> | []]; destruct (view_key_index x Ks) as [v |]; [ exists v; reflexivity | discriminate ].
  - destruct (classified_ptyp_num n Ks tc) as [s' |] eqn:Es; [| discriminate ]; exact (IH _ eq_refl _ Hx).
Qed.

(** The filed keys are among the views found. *)
Lemma filed_keys_in : forall meets Vs y, In y (filed_keys meets Vs) -> In y Vs.
Proof.
  unfold filed_keys, ind_keys, record_keys; intros * Hy; apply List.in_app_or in Hy as [Hy | Hy];
    [ apply List.filter_In in Hy as [Hy _]; exact Hy |].
  apply sort_by_height_in, List.filter_In in Hy as [Hy _]; exact Hy.
Qed.

(** A context weakened past its first [m] entries. *)
Lemma wf_wk_pat_trues_skipn : forall Θ Ξ Γ m, m <= List.length Γ -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ʷ wk_pat (List.repeat true m) : List.skipn m Γ.
Proof.
  intros * Hm HΓ.
  rewrite <- (List.firstn_skipn m Γ) in HΓ |- * at 1.
  assert (E : wk_eq (wk_pat (List.repeat true m)) (wk_shiftn (List.length (List.firstn m Γ))))
    by (intros x; rewrite wk_pat_trues, List.length_firstn; unfold wk_shiftn; lia).
  rewrite E; exact (wf_wk_shiftn_app' _ _ _ _ HΓ).
Qed.

(** ** Each View Is a Keyed Instance

    Every view found is the key of an instance over the group's uniform
    context: a classification keys what it meets ([view_inst_key]), and a
    sibling of a keyed view is keyed by the instance its own arguments
    instantiate. *)

(** A key is the key of an instance over [Γ]. *)
Definition key_sourced (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (y : view_key) : Prop := exists z, view_inst_key Θ Ξ Γ z y.

(** The new views are among those offered. *)
Lemma views_new_sub : forall acc ss y, In y (views_new acc ss) -> In y ss.
Proof.
  intros acc ss; revert acc; induction ss as [| s ss IH]; intros acc y Hy; cbn in Hy; [ destruct Hy |].
  destruct (view_key_mem s acc); [ right; exact (IH _ _ Hy) |].
  destruct Hy as [<- | Hy]; [ left; reflexivity | right; exact (IH _ _ Hy) ].
Qed.

(** A property of the views found so far and of the instances to meet,
    kept by the siblings and the instances met of a view, holds of all the
    views found. *)
Lemma views_dfs_forall : forall (P : view_key -> Prop) sibs meets acc tr Vs, views_dfs sibs meets acc tr Vs ->
    (forall x, In x acc -> P x) -> (forall x, In x tr -> P x) ->
    (forall x, P x -> forall y, In y (sibs x) -> P y) -> (forall x, P x -> forall y, In y (meets x) -> P y) ->
    forall x, In x Vs -> P x.
Proof.
  intros P sibs meets; induction 1 as [acc | acc x tr Vs H IH]; intros Hacc Htr Hs Hm; [ exact Hacc |].
  assert (Hx : P x) by (apply Htr; left; reflexivity).
  assert (Hnew : forall y, In y (views_met sibs acc x) -> P y).
  { intros y Hy; unfold views_met in Hy; destruct (view_key_mem x acc); [ destruct Hy |].
    apply views_new_sub, List.in_app_or in Hy as [Hy | [<- | []]]; [ exact (Hs _ Hx _ Hy) | exact Hx ]. }
  apply IH; [ | | exact Hs | exact Hm ].
  - intros y Hy; apply List.in_app_or in Hy as [Hy | Hy]; [ exact (Hacc _ Hy) | exact (Hnew _ Hy) ].
  - intros y Hy; apply List.in_app_or in Hy as [Hy | Hy]; [| exact (Htr _ (or_intror Hy)) ].
    apply List.in_concat in Hy as (l & Hl & Hy); apply List.in_map_iff in Hl as (z & <- & Hz).
    exact (Hm _ (Hnew _ Hz) _ Hy).
Qed.

(** The instance a keyed shape or argument meets is keyed. *)
Lemma written_ptyp_key_sourced : forall Θ Ξ Γ tw tc, written_ptyp_key Θ Ξ Γ tw tc ->
    forall y, In y (classified_ptyp_view tc) -> key_sourced Θ Ξ Γ y.
Proof.
  induction 1 as [j Ps | x y0 Ns Hxy | B tw tc _ IH]; cbn; intros y Hy; [ destruct Hy | | exact (IH _ Hy) ].
  destruct Hy as [<- | []]; exists x; exact Hxy.
Qed.

Lemma written_carg_key_sourced : forall Θ Ξ Γ gw g, written_carg_key Θ Ξ Γ gw g ->
    forall y, In y (classified_carg_view g) -> key_sourced Θ Ξ Γ y.
Proof. intros * [κ A | tw tc H] y Hy; cbn in Hy; [ destruct Hy | exact (written_ptyp_key_sourced _ _ _ _ _ H _ Hy) ]. Qed.

(** The instances the arguments meet are keyed over the context without
    the non-uniform parameters. *)
Lemma classify_args_in_sourced : forall Θ Ξ Γp nu np n pat args1 args gs,
    classify_args_in Θ Ξ Γp nu np n pat args1 args gs -> List.length pat = List.length args1 ->
    forall g y, In g gs -> In y (classified_carg_view g) -> key_sourced Θ Ξ (List.skipn (np - nu) Γp) y.
Proof.
  induction 1 as [pat args1 | pat args1 y0 κ T args g gs Hg _ _ IH]; intros Hl g' y Hg' Hy; [ destruct Hg' |].
  destruct Hg' as [<- | Hg']; [| apply (IH ltac:(rewrite List.length_app; cbn; lia) _ _ Hg' Hy) ].
  assert (Ev : classified_carg_view (classified_carg_tag κ g) = classified_carg_view g) by (destruct g; reflexivity).
  rewrite Ev in Hy.
  assert (E : List.skipn (List.length pat + (np - nu)) (raw_args_tele args1 ++ Γp) = List.skipn (np - nu) Γp).
  { rewrite List.skipn_app, List.skipn_all2 by (rewrite length_raw_args_tele; lia).
    rewrite length_raw_args_tele; cbn [List.app]; f_equal; lia. }
  destruct Hg as [gw g0 _ Hk | i W gw g0 _ _ _ _ _ Hk]; rewrite E in Hk; exact (written_carg_key_sourced _ _ _ _ _ Hk _ Hy).
Qed.

Lemma classify_cons_in_sourced : forall Θ Ξ Γp nu np n rcs cs, classify_cons_in Θ Ξ Γp nu np n rcs cs ->
    forall y, In y (classified_cons_views cs) -> key_sourced Θ Ξ (List.skipn (np - nu) Γp) y.
Proof.
  unfold classify_cons_in, classified_cons_views; induction 1 as [| rc c rcs cs [_ Hc] _ IH]; intros y Hy; [ destruct Hy |].
  cbn in Hy; apply List.in_app_or in Hy as [Hy | Hy]; [| exact (IH _ Hy) ].
  apply List.in_concat in Hy as (l & Hl & Hy); apply List.in_map_iff in Hl as (g & <- & Hg).
  exact (classify_args_in_sourced _ _ _ _ _ _ _ _ _ _ Hc eq_refl _ _ Hg Hy).
Qed.

(** A declared member's arguments' context without the arguments before
    one and the member's parameters is the group's uniform one. *)
Lemma member_ctx_skipn : forall Ξ R Mr args1,
    List.skipn (List.length args1 + List.length (raw_member_nparams Mr)) (raw_args_tele args1 ++ raw_member_args_ctx Ξ R Mr)
    = raw_decl_uniform_ctx Ξ R.
Proof.
  intros; rewrite List.skipn_app, (List.skipn_all2 (raw_args_tele args1)) by (rewrite length_raw_args_tele; lia).
  rewrite length_raw_args_tele; cbn [List.app].
  replace (List.length args1 + List.length (raw_member_nparams Mr) - List.length args1)
    with (List.length (raw_member_nparams Mr)) by lia.
  unfold raw_member_args_ctx, raw_decl_uniform_ctx; rewrite tele_wk_app, <- List.app_assoc.
  rewrite List.skipn_app, List.skipn_all2 by (rewrite length_tele_wk; lia).
  rewrite length_tele_wk, Nat.sub_diag; reflexivity.
Qed.

(** The siblings of a keyed view are keyed. *)
Lemma siblings_from_sourced : forall Θ Ξ Γ qc Cs i ms ss Ms D',
    ⊢ᵍ Θ ⍮ Ξ -> ind_lookup Θ Ξ qc = Some D' -> nbes Θ Ξ Γ Ms (tele_insts (ind_uparams D') Id Ms) Cs ->
    siblings_from Θ Ξ Γ qc Cs i ms ss -> forall y, In y ss -> key_sourced Θ Ξ Γ y.
Proof.
  intros * Hg Hl HMs.
  induction 1 as [i | i M ms ss pm _ _ IH | i M ms ss qv kv Iv vmv Dv Ws _ Hlv HWs _ IH | i M ms ss qr Ir fl Rr Ws _ Hlr HWs _ IH];
    intros y Hy; [ destruct Hy | | |]; (destruct Hy as [<- | Hy]; [| exact (IH _ Hy) ]).
  - exists (vi_ind qc i Ms); econstructor; [ exact Hl | exact HMs ].
  - pose proof (gctx_closed_ind _ _ _ _ (wf_gstack_closed _ _ Hg) Hlv) as Hc.
    exists (vi_ind qv kv (List.map (fun I => I[sb_of_list sb_id (List.map nf_to_exp Cs)]) Iv)); econstructor; [ exact Hlv |].
    rewrite <- (tele_insts_sub (ind_uparams Dv) 0 Id Id _ Iv (decl_closed_ass _ Hc) (decl_closed_uparams _ Hc)
                  ltac:(intros x Hx; lia)).
    exact HWs.
  - pose proof (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) Hlr) as Hc.
    pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hlr) as Ht.
    exists (vi_record qr (List.map (fun I => I[sb_of_list sb_id (List.map nf_to_exp Cs)]) Ir)); econstructor; [ exact Hlr |].
    rewrite <- (tele_insts_sub (record_params Rr) 0 Id Id _ Ir (typed_params_ass _ _ _ Ht) (closed_params _ Hc)
                  ltac:(intros x Hx; lia)).
    exact HWs.
Qed.

Lemma view_siblings_sourced : forall Θ Ξ R x ss, ⊢ᵍ Θ ⍮ Ξ -> view_siblings Θ Ξ R x ss ->
    key_sourced Θ Ξ (raw_decl_uniform_ctx Ξ R) x -> forall y, In y ss -> key_sourced Θ Ξ (raw_decl_uniform_ctx Ξ R) y.
Proof.
  intros * Hg [qc k Cs D' ss' Hl Hs | qr Is] (z & Hz) y Hy; [| destruct Hy as [<- | []]; exists z; exact Hz ].
  inversion Hz as [qc0 k0 Ms D'' Cs0 Hl' HMs | ]; subst.
  rewrite Hl in Hl'; injection Hl' as <-.
  exact (siblings_from_sourced _ _ _ _ _ _ _ _ _ _ Hg Hl HMs Hs _ Hy).
Qed.

(** The instances a view's constructors meet are keyed. *)
Lemma view_classify_sourced : forall Θ Ξ R x cs, view_classify Θ Ξ R x cs ->
    forall y, In y (classified_cons_views cs) -> key_sourced Θ Ξ (raw_decl_uniform_ctx Ξ R) y.
Proof.
  intros * [qc k Cs D' Mk' cs' _ _ Hc | qr Is Rr cs' _ Hc] y Hy;
    pose proof (classify_cons_in_sourced _ _ _ _ _ _ _ _ Hc _ Hy) as H.
  - replace (im_nn Mk' + raw_decl_nu R - raw_decl_nu R) with (List.length (tele_sub (im_nparams Mk') (sb_of_list sb_id (List.map nf_to_exp Cs))))
      in H by (rewrite length_tele_sub; unfold im_nn; lia).
    rewrite List.skipn_app, List.skipn_all, Nat.sub_diag in H; exact H.
  - rewrite Nat.sub_diag in H; exact H.
Qed.

(** One member of a list related to another is related to one of it. *)
Lemma Forall2_in_r : forall {X Y} (Rl : X -> Y -> Prop) l1 l2 b, Forall2 Rl l1 l2 -> In b l2 -> exists a, In a l1 /\ Rl a b.
Proof.
  intros X Y Rl l1 l2 b H; induction H as [| a1 b1 l1 l2 Hab _ IH]; intros Hb; [ destruct Hb |].
  destruct Hb as [<- | Hb]; [ exists a1; split; [ left; reflexivity | exact Hab ] |].
  destruct (IH Hb) as (a & Ha & Hr); exists a; split; [ right; exact Ha | exact Hr ].
Qed.

(** Every view found is keyed over the group's uniform context. *)
Lemma views_sourced : forall Θ Ξ R csD Vs Ss csV, ⊢ᵍ Θ ⍮ Ξ ->
    Forall2 (raw_member_classify Θ Ξ R) (raw_decl_members R) csD ->
    Forall2 (view_siblings Θ Ξ R) Vs Ss -> Forall2 (view_classify Θ Ξ R) Vs csV ->
    views_dfs (siblings_table Vs Ss) (meets_table Vs csV) nil (List.concat (List.map classified_cons_views csD)) Vs ->
    forall y, In y Vs -> exists z, view_inst_key Θ Ξ (raw_decl_uniform_ctx Ξ R) z y.
Proof.
  intros * Hg Hcls Hs Hv Hb.
  apply (views_dfs_forall (key_sourced Θ Ξ (raw_decl_uniform_ctx Ξ R)) _ _ _ _ _ Hb).
  - intros x [].
  - intros x Hx; apply List.in_concat in Hx as (l & Hl & Hx); apply List.in_map_iff in Hl as (cs & <- & Hcs).
    destruct (Forall2_in_r _ _ _ _ Hcls Hcs) as (Mr & _ & HMr).
    pose proof (classify_cons_in_sourced _ _ _ _ _ _ _ _ HMr _ Hx) as H.
    replace (List.length (raw_member_nparams Mr) + raw_decl_nu R - raw_decl_nu R) with (0 + List.length (raw_member_nparams Mr))
      in H by lia.
    rewrite <- (member_ctx_skipn Ξ R Mr nil); exact H.
  - intros x Hx y Hy; unfold siblings_table in Hy.
    destruct (view_key_pos x Vs) as [v |] eqn:Ev; [| destruct Hy as [<- | []]; exact Hx ].
    exact (view_siblings_sourced _ _ _ _ _ Hg (Forall2_index _ _ _ _ _ _ Hs Ev) Hx _ Hy).
  - intros x _ y Hy; unfold meets_table in Hy.
    destruct (view_key_pos x Vs) as [v |] eqn:Ev; [| destruct Hy ].
    exact (view_classify_sourced _ _ _ _ _ (Forall2_index _ _ _ _ _ _ Hv Ev) _ Hy).
Qed.

(** ** The Constructor Types of a Run

    The premises of [run_cmd_ind_case], the group filed as [D] at [p] in the stack
    [Ξf] the entries make. *)

Section ConTypes.
  Variables (Θ : gdeps) (Ξ : gstack) (pv : bool) (R : raw_decl) (Mr0 : raw_member) (Mrs : list raw_member)
    (csD : list (list (string * list classified_carg))) (Vs : list view_key) (Ss : list (list view_key))
    (csV : list (list (string * list classified_carg))) (Nvs : list ctx) (Ms Mvs : list imember) (Ξf : gstack).

  #[local] Abbreviation p := (ind_qname Ξ (raw_member_name Mr0)).
  #[local] Abbreviation n := (raw_decl_nmembers R).
  #[local] Abbreviation nu := (raw_decl_nu R).
  #[local] Abbreviation t := (List.length (gs_tele Ξ)).
  #[local] Abbreviation D := (mk_ind (raw_decl_uparams R ++ gs_tele Ξ) (raw_member_sort Mr0) (Ms ++ Mvs)).
  (** The views in filing order *)
  #[local] Abbreviation Ks := (filed_keys (meets_table Vs csV) Vs).

  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.
  Hypothesis HMr : raw_decl_members R = Mr0 :: Mrs.
  Hypothesis Hsort : Forall (fun Mr => raw_member_sort Mr = raw_member_sort Mr0) Mrs.
  Hypothesis Hcls : Forall2 (raw_member_classify Θ Ξ R) (raw_decl_members R) csD.
  Hypothesis Hsibs : Forall2 (view_siblings Θ Ξ R) Vs Ss.
  Hypothesis Hvcls : Forall2 (view_classify Θ Ξ R) Vs csV.
  Hypothesis Hnps : Forall2 (view_nparams Θ Ξ R) Vs Nvs.
  Hypothesis Hms : raw_members_filed Ξ n Ks (raw_decl_members R) csD = Some Ms.
  Hypothesis Hmvs : raw_views_filed Θ Ξ (sb_selfs p nu n t) n Ks Ks Vs Ss csV Nvs = Some Mvs.
  (** The stack the declared members end on: well formed, the stack before
      embedded in it, the group found at its first member's path *)
  Hypothesis Hfwf : ⊢ᵍ Θ ⍮ Ξf.
  Hypothesis Hfemb : gctx_embedding Θ Ξ Θ Ξf.
  Hypothesis Hflk : ind_lookup Θ Ξf p = Some D.
  (** Each view found is the key of an instance over the group's uniform
      context ([views_sourced]) *)
  Hypothesis Hsrc : forall y, In y Vs -> exists z, view_inst_key Θ Ξ (raw_decl_uniform_ctx Ξ R) z y.


  Lemma filed_wf : ⊢ᵍ Θ ⍮ Ξf.
  Proof. exact Hfwf. Qed.

  Lemma filed_gctx_embedding : gctx_embedding Θ Ξ Θ Ξf.
  Proof. exact Hfemb. Qed.

  Lemma filed_lookup : ind_lookup Θ Ξf p = Some D.
  Proof. exact Hflk. Qed.

  Lemma filed_decl_typed : decl_typed Θ Ξf D.
  Proof. exact (proj1 (decl_of_lookup _ _ ⋅ _ _ (wf_ctx_empty _ _ filed_wf) filed_lookup)). Qed.

  Lemma filed_decl_closed : decl_closed D.
  Proof. exact (proj2 (decl_of_lookup _ _ ⋅ _ _ (wf_ctx_empty _ _ filed_wf) filed_lookup)). Qed.

  Lemma length_filed_decls : List.length Ms = n.
  Proof. exact (raw_members_filed_length _ _ _ _ _ _ Hms). Qed.

  Lemma filed_nu : ind_nu D = nu + t.
  Proof. unfold ind_nu, raw_decl_nu; cbn; apply List.length_app. Qed.

  Lemma filed_ndecl : ind_ndecl D = n.
  Proof.
    unfold ind_ndecl; cbn [ind_members]; rewrite List.filter_app.
    assert (H1 : forall l, Forall (fun M => im_is_decl M = true) l -> List.filter im_is_decl l = l)
      by (induction 1 as [| M l HM _ IH]; cbn; [ reflexivity | rewrite HM, IH; reflexivity ]).
    assert (H2 : forall l, Forall (fun M => im_is_decl M = false) l -> List.filter im_is_decl l = nil)
      by (induction 1 as [| M l HM _ IH]; cbn; [ reflexivity | rewrite HM, IH; reflexivity ]).
    rewrite (H1 _ (raw_members_filed_decl _ _ _ _ _ _ Hms)), (H2 _ (raw_views_filed_views _ _ _ _ _ _ _ _ _ _ _ Hmvs)), List.app_nil_r.
    exact length_filed_decls.
  Qed.

  (** The declared members are the type formers, the views the containers'
      members at their instances. *)
  Lemma filed_mty_decl : forall i Us Ns, i < n -> ind_mty p D i Us Ns = apps (a_ind p i) (Us ++ Ns).
  Proof.
    intros * Hi; unfold ind_mty, ind_member; cbn [ind_members].
    rewrite List.nth_error_app1 by (rewrite length_filed_decls; exact Hi).
    destruct (nth_error_lt_some Ms i ltac:(rewrite length_filed_decls; exact Hi)) as [M HM]; rewrite HM.
    pose proof (proj1 (List.Forall_forall _ _) (raw_members_filed_decl _ _ _ _ _ _ Hms) M (List.nth_error_In _ _ HM)) as Hd.
    unfold im_ty_at, im_ref, im_pre, im_is_decl in *; destruct (im_head M); [ reflexivity | discriminate | discriminate ].
  Qed.

  Lemma filed_view : forall v x, List.nth_error Ks v = Some x ->
      (forall C, In C (view_key_args x) -> exp_scoped (nu + t) (nf_to_exp C)[sb_selfs p nu n t] /\ exp_mvc 0 (nf_to_exp C)[sb_selfs p nu n t]) /\
      forall Us Ns, ind_mty p D (n + v) Us Ns
                    = apps (view_key_head x) (List.map (fun C => (nf_to_exp C)[sb_selfs p nu n t][sb_of_list Id Us]) (view_key_args x) ++ Ns).
  Proof.
    intros * Hv.
    destruct (raw_views_filed_nth _ _ _ _ _ _ _ _ _ _ _ Hmvs _ _ Hv) as (w & _ & Hnth).
    assert (Hlt : v < List.length Mvs)
      by (rewrite (raw_views_filed_length _ _ _ _ _ _ _ _ _ _ _ Hmvs); apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some Mvs v Hlt) as [M HM].
    assert (Hk : ind_member D (n + v) = Some M).
    { unfold ind_member; cbn [ind_members]; rewrite List.nth_error_app2 by (rewrite length_filed_decls; lia).
      rewrite length_filed_decls; replace (n + v - n) with v by lia; exact HM. }
    rewrite HM in Hnth; symmetry in Hnth; unfold raw_view_filed in Hnth.
    destruct (decl_mvc_members _ (decl_typed_mvc _ _ _ filed_decl_typed) _ _ Hk) as (_ & Hmv & _).
    destruct x as [qc k Cs | qr Is]; cbn [view_key_head view_key_args].
    - destruct (ind_lookup Θ Ξ qc); [| discriminate ].
      destruct (ind_member _ k); [| discriminate ].
      destruct (classified_cons_num n Ks _); [| discriminate ].
      injection Hnth as <-.
      split.
      + intros C HC.
        pose proof (decl_closed_head_scoped _ filed_decl_closed _ _ _ _ _ _ Hk eq_refl) as Hsc.
        cbn in Hmv; rewrite List.Forall_forall in Hsc, Hmv.
        pose proof (List.in_map (fun C0 => (nf_to_exp C0)[sb_selfs p nu n t]) _ _ HC) as HC'.
        rewrite filed_nu in Hsc; split; [ apply Hsc | apply Hmv ]; exact HC'.
      + intros Us Ns; unfold ind_mty; rewrite Hk; unfold im_ty_at, im_ref, im_pre; cbn [im_head fst snd].
        rewrite List.map_map; reflexivity.
    - destruct (record_lookup Θ Ξ qr); [| discriminate ].
      destruct (classified_cons_num n Ks _); [| discriminate ].
      injection Hnth as <-.
      split.
      + intros C HC.
        pose proof (decl_closed_rhead_scoped _ filed_decl_closed _ _ _ _ _ Hk eq_refl) as Hsc.
        cbn in Hmv; rewrite List.Forall_forall in Hsc, Hmv.
        pose proof (List.in_map (fun C0 => (nf_to_exp C0)[sb_selfs p nu n t]) _ _ HC) as HC'.
        rewrite filed_nu in Hsc; split; [ apply Hsc | apply Hmv ]; exact HC'.
      + intros Us Ns; unfold ind_mty; rewrite Hk; unfold im_ty_at, im_pre; cbn [im_head].
        rewrite List.map_map; reflexivity.
  Qed.

  Lemma filed_member : forall j Mr cs, List.nth_error (raw_decl_members R) j = Some Mr -> List.nth_error csD j = Some cs ->
      exists cs', classified_cons_num n Ks cs = Some cs' /\
        ind_member D j = Some (mk_imember (mh_decl (ind_qname Ξ (raw_member_name Mr))) (raw_member_nparams Mr) cs').
  Proof.
    intros * Hj Hc.
    pose proof (raw_members_filed_nth _ _ _ _ _ _ Hms _ _ _ Hj Hc) as H.
    assert (Hlt : j < List.length Ms)
      by (rewrite length_filed_decls; unfold raw_decl_nmembers; apply List.nth_error_Some; congruence).
    unfold ind_member; cbn [ind_members]; rewrite List.nth_error_app1 by exact Hlt.
    destruct (classified_cons_num n Ks cs) as [cs' |]; cbn in H.
    - exists cs'; split; [ reflexivity | exact H ].
    - exfalso; apply List.nth_error_None in H; lia.
  Qed.

  Lemma member_sort : forall Mr, In Mr (raw_decl_members R) -> raw_member_sort Mr = raw_member_sort Mr0.
  Proof.
    intros Mr Hin; rewrite HMr in Hin; destruct Hin as [<- | Hin]; [ reflexivity |].
    exact (proj1 (List.Forall_forall _ _) Hsort _ Hin).
  Qed.

  Lemma filed_ind_ty : forall j Mr cs', List.nth_error (raw_decl_members R) j = Some Mr ->
      ind_ty D (mk_imember (mh_decl (ind_qname Ξ (raw_member_name Mr))) (raw_member_nparams Mr) cs') = ctx_pi (gs_tele Ξ) (raw_decl_self_ty R Mr).
  Proof.
    intros * Hj; unfold ind_ty, raw_decl_self_ty, im_params, im_nn; cbn [im_nparams ind_uparams ind_sort].
    rewrite (member_sort _ (List.nth_error_In _ _ Hj)), List.app_assoc, ctx_pi_app; reflexivity.
  Qed.

  (** The frames' parameters, the outer part of the filed group's uniform
      ones. *)
  Lemma frames_ass : all_assumptions (gs_tele Ξ).
  Proof.
    pose proof (decl_typed_ass _ _ _ filed_decl_typed) as H; cbn [ind_uparams] in H.
    unfold all_assumptions in *; apply List.Forall_app in H as [_ H]; exact H.
  Qed.

  Lemma frames_scoped : ctx_scoped 0 (gs_tele Ξ).
  Proof.
    pose proof (decl_closed_uparams _ filed_decl_closed) as H; cbn [ind_uparams] in H.
    apply ctx_scoped_app in H as [_ H]; exact H.
  Qed.

  Lemma frames_mvc : ctx_mvc (gs_tele Ξ).
  Proof.
    pose proof (decl_mvc_uparams _ (decl_typed_mvc _ _ _ filed_decl_typed)) as H; cbn [ind_uparams] in H.
    unfold ctx_mvc in *; apply List.Forall_app in H as [_ H]; exact H.
  Qed.

  Lemma frames_wf : ⊢ Θ ⍮ Ξf ⍮ gs_tele Ξ.
  Proof. pose proof (decl_typed_uparams_field _ _ _ filed_decl_typed) as H; cbn [ind_uparams] in H; exact (ctx_app_wf_tail _ _ _ _ H). Qed.

  (** The type former of a declared member at the frames' parameters is of
      its [Self]'s type. *)
  Lemma self_frames_typed : forall i Mr, List.nth_error (raw_decl_members R) i = Some Mr ->
      Θ ⍮ Ξf ⍮ gs_tele Ξ ⊢ apps (a_ind p i) (vars_from 0 t) : raw_decl_self_ty R Mr.
  Proof.
    intros * Hi.
    destruct (Forall2_nth_error_l _ _ _ _ _ Hcls Hi) as (cs & Hcs & _).
    destruct (filed_member _ _ _ Hi Hcs) as (cs' & _ & Hk).
    set (Mi := mk_imember (mh_decl (ind_qname Ξ (raw_member_name Mr))) (raw_member_nparams Mr) cs') in *.
    pose proof filed_decl_typed as HD; pose proof filed_decl_closed as Hc.
    pose proof (filed_ind_ty _ _ cs' Hi) as Hty; fold Mi in Hty.
    assert (Hlt : i < ind_ndecl D) by (rewrite filed_ndecl; unfold raw_decl_nmembers; apply List.nth_error_Some; congruence).
    pose proof (wf_ind _ _ _ _ _ _ _ frames_wf filed_lookup Hk Hlt) as Hind; rewrite Hty in Hind.
    (** The [Self]'s type over the frames' parameters: typed, scoped and
        free of module variables. *)
    pose proof (member_params_wf _ _ _ _ _ HD Hk) as HP.
    destruct (member_sort_typed _ _ _ _ _ HD Hk) as ([j Hj] & _).
    unfold im_params in HP, Hj; cbn [im_nparams ind_uparams] in HP, Hj; rewrite List.app_assoc in HP, Hj.
    destruct (ctx_pi_wf _ _ _ _ _ _ HP Hj) as [j' Hj'].
    assert (EB : ctx_pi (raw_member_nparams Mr ++ raw_decl_uparams R) (ind_sort D)[wk_shiftn (im_nn Mi)]ʷ = raw_decl_self_ty R Mr)
      by (unfold raw_decl_self_ty, im_nn; cbn [ind_sort im_nparams]; rewrite (member_sort _ (List.nth_error_In _ _ Hi)); reflexivity).
    change (im_nparams Mi) with (raw_member_nparams Mr) in Hj'; rewrite EB in Hj'.
    assert (HsB : exp_scoped t (raw_decl_self_ty R Mr)).
    { rewrite <- EB; pose proof (decl_closed_params _ _ _ Hc Hk) as Hs; unfold im_params in Hs; cbn [im_nparams ind_uparams Mi] in Hs.
      rewrite List.app_assoc in Hs; apply ctx_scoped_app in Hs as [Hs _]; rewrite Nat.add_0_r in Hs.
      apply ctx_pi_scoped; [ exact Hs |].
      eapply exp_scoped_wk; [ exact (decl_closed_sort _ Hc) |]; intros x Hx; cbn [ind_nu ind_uparams] in Hx.
      rewrite filed_nu in Hx; unfold wk_shiftn, im_nn, raw_decl_nu in *; cbn [im_nparams Mi]; rewrite !List.length_app in *; lia. }
    assert (HmB : exp_mvc 0 (raw_decl_self_ty R Mr)).
    { rewrite <- EB; pose proof (decl_typed_mvc _ _ _ HD) as Hm.
      destruct (decl_mvc_members _ Hm _ _ Hk) as (HnM & _ & _); pose proof (decl_mvc_uparams _ Hm) as HuM.
      cbn [ind_uparams im_nparams Mi] in HnM, HuM.
      apply ctx_pi_mvc.
      - pose proof (decl_closed_params_ass _ _ _ Hc Hk) as Ha; unfold im_params in Ha; cbn [im_nparams ind_uparams Mi] in Ha.
        rewrite List.app_assoc in Ha; unfold all_assumptions in *; apply List.Forall_app in Ha as [Ha _]; exact Ha.
      - unfold ctx_mvc in HuM; apply List.Forall_app in HuM as [HuM _]; apply List.Forall_app; split; assumption.
      - eapply exp_mvc_mono; [| apply exp_mvc_wk; exact (decl_mvc_sort _ Hm) ]; lia. }
    replace (raw_decl_self_ty R Mr) with ((raw_decl_self_ty R Mr)[sb_of_list Id (vars_from 0 t)]).
    - eapply wf_apps_closed_pi; [ exact frames_ass | exact frames_scoped | exact HsB | exact Hj' | exact frames_wf | exact Hind
                                | rewrite length_vars_from; reflexivity |].
      pose proof (wf_vars_tele Θ Ξf nil (gs_tele Ξ) frames_ass frames_scoped frames_mvc) as H.
      cbn [List.app List.length] in H; exact (H frames_wf).
    - rewrite (exp_at_vars _ _ _ HsB HmB).
      apply (exp_scoped_wk_id _ _ _ HsB); intros; unfold wk_shiftn; lia.
  Qed.

  (** The [Self]s instantiated, a substitution from the frames'
      parameters. *)
  Lemma selfs_sub_typed : ⊢ Θ ⍮ Ξf ⍮ raw_decl_selfs R ++ gs_tele Ξ ->
      Θ ⍮ Ξf ⍮ gs_tele Ξ ⊢ˢ sb_of_list Id (List.map (fun j => apps (a_ind p j) (vars_from 0 t)) (List.seq 0 n))
        : raw_decl_selfs R ++ gs_tele Ξ.
  Proof.
    intros HS.
    assert (H : forall m, m <= n ->
      ⊢ Θ ⍮ Ξf ⍮ raw_decl_selfs_from R 0 (List.firstn m (raw_decl_members R)) ++ gs_tele Ξ ->
      Θ ⍮ Ξf ⍮ gs_tele Ξ ⊢ˢ sb_of_list Id (List.map (fun j => apps (a_ind p j) (vars_from 0 t)) (List.seq 0 m))
        : raw_decl_selfs_from R 0 (List.firstn m (raw_decl_members R)) ++ gs_tele Ξ).
    { induction m as [| m IH]; intros Hm Hctx.
      - cbn; apply wf_sub_id; exact frames_wf.
      - destruct (List.nth_error (raw_decl_members R) m) as [Mm |] eqn:HMm;
          [| apply List.nth_error_None in HMm; unfold raw_decl_nmembers in Hm; lia ].
        rewrite (firstn_S_nth_error _ _ _ HMm) in Hctx |- * .
        rewrite raw_decl_selfs_from_snoc in Hctx |- *; cbn [Nat.add] in Hctx |- *.
        rewrite List.length_firstn in Hctx |- *;
          replace (Nat.min m (List.length (raw_decl_members R))) with m in * by (unfold raw_decl_nmembers in Hm; lia).
        rewrite List.seq_S, List.map_app, sb_of_list_app; cbn [List.map sb_of_list Nat.add].
        destruct (ctx_decomp Hctx) as [Hctx' _].
        destruct (ctx_decomp_kind Hctx) as (Si & HSi & Hi).
        eapply wf_sub_extend; [ apply IH; [ lia | exact Hctx' ] | exact Hi | exact HSi |].
        rewrite exp_sub_wk.
        rewrite (exp_sub_sb_eq _ _ Id).
        + rewrite exp_sub_id; exact (self_frames_typed _ _ HMm).
        + intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
          replace (x + m) with (List.length (List.map (fun j => apps (a_ind p j) (vars_from 0 t)) (List.seq 0 m)) + x)
            by (rewrite List.length_map, List.length_seq; lia).
          apply sb_of_list_ge. }
    pose proof (H n (le_n _)) as H'; unfold raw_decl_selfs; rewrite List.firstn_all2 in H' by (unfold raw_decl_nmembers; lia).
    exact (H' HS).
  Qed.

  (** The [Self]s instantiated, from the filed parameters of a declared
      member into the context its arguments are written in. *)
  Lemma base_sub : forall Mr, ⊢ Θ ⍮ Ξf ⍮ raw_member_args_ctx Ξ R Mr -> ⊢ Θ ⍮ Ξf ⍮ raw_member_nparams Mr ++ raw_decl_uparams R ++ gs_tele Ξ ->
      Θ ⍮ Ξf ⍮ raw_member_nparams Mr ++ raw_decl_uparams R ++ gs_tele Ξ ⊢ˢ sb_selfs p (List.length (raw_member_nparams Mr) + nu) n t : raw_member_args_ctx Ξ R Mr.
  Proof.
    intros Mr Hb HP; unfold raw_member_args_ctx in *.
    pose proof (selfs_sub_typed (ctx_app_wf_tail _ _ _ _ Hb)) as Hσ.
    pose proof (wf_sub_ext _ _ (tele_wk (raw_member_nparams Mr ++ raw_decl_uparams R) (wk_shiftn n)) _ _ _ Hσ) as H.
    assert (E : tele_sub (tele_wk (raw_member_nparams Mr ++ raw_decl_uparams R) (wk_shiftn n))
                (sb_of_list Id (List.map (fun j => apps (a_ind p j) (vars_from 0 t)) (List.seq 0 n)))
              = raw_member_nparams Mr ++ raw_decl_uparams R)
      by (pose proof (tele_wk_shiftn_sb_of_list (raw_member_nparams Mr ++ raw_decl_uparams R)
                        (List.map (fun j => apps (a_ind p j) (vars_from 0 t)) (List.seq 0 n)) Id) as E;
          rewrite length_self_insts, tele_sub_id in E; exact E).
    rewrite E, length_tele_wk, List.length_app, <- List.app_assoc in H.
    unfold sb_selfs, raw_decl_nu; apply H; [ exact HP | exact Hb ].
  Qed.

  (** The arguments after [args1], as written with the [Self]s instantiated
      and as filed, give equal [Π]s into the member, when the arguments
      before give contexts the one below the other. *)
  Lemma conv_tail : forall j Mr Mj c gsall,
      List.nth_error (raw_decl_members R) j = Some Mr -> ind_member D j = Some Mj -> im_nparams Mj = raw_member_nparams Mr ->
      In (c, gsall) (im_cons Mj) ->
      forall pat args1 args gsr2, classify_args_in Θ Ξ (raw_member_args_ctx Ξ R Mr) nu (List.length (raw_member_nparams Mr) + nu) n pat args1 args gsr2 ->
      forall gs1 gs2, classified_cargs_num n Ks gsr2 = Some gs2 -> gsall = gs1 ++ gs2 -> pat = cargs_pat gs1 ->
      List.length args1 = List.length gs1 ->
      Θ ⍮ Ξf ⊢ tele_sub (raw_args_tele args1) (sb_selfs p (List.length (raw_member_nparams Mr) + nu) n t) ++ im_params D Mj
        ⊆ cargs_ctx p D Mj gs1 ++ im_params D Mj ->
      exists i, Θ ⍮ Ξf ⍮ tele_sub (raw_args_tele args1) (sb_selfs p (List.length (raw_member_nparams Mr) + nu) n t) ++ im_params D Mj
        ⊢ ctx_pi (tele_sub (raw_args_tele args) (sb_selfs p (List.length args1 + (List.length (raw_member_nparams Mr) + nu)) n t))
            (ind_mty p D j (ind_uvars D (im_nn Mj) (List.length gsall)) (vars_from (List.length gsall) (im_nn Mj)))
        ≈ ctx_pi (cargs_ctx_aux p D (im_nn Mj) pat gs2)
            (ind_mty p D j (ind_uvars D (im_nn Mj) (List.length gsall)) (vars_from (List.length gsall) (im_nn Mj)))
        : Typeω@i.
  Proof.
    intros j Mr Mj c gsall Hj Hk Hnp Hin.
    set (np := List.length (raw_member_nparams Mr) + nu).
    induction 1 as [pat args1 | pat args1 y κ T args g gsr Hg Hκ Hgs IH]; intros gs1 gs2 Hn Hall Hpat Hlen Hsub.
    - (** No argument left: the result type. *)
      cbn in Hn; injection Hn as <-; rewrite List.app_nil_r in Hall; subst gsall.
      pose proof (cons_lookup_nodup _ _ _ (decl_typed_nodup _ _ _ filed_decl_typed _ _ Hk) Hin) as Hcon.
      destruct (con_cod_typed _ _ _ _ _ _ _ _ filed_wf (decls_of_ctx _ _ _ (wf_ctx_empty _ _ filed_wf)) filed_lookup Hk Hcon)
        as [i Hi].
      exists i; cbn [raw_args_tele tele_sub ctx_pi List.rev List.map cargs_ctx_aux].
      apply wf_exp_eq_refl.
      pose proof (ctx_sub_escape _ _ _ _ Hsub) as Hid.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hi Hid) as H; rewrite !exp_sub_id in H; exact H.
    - (** An argument: equal at its type as written and as filed, then the
          rest. *)
      cbn [classified_cargs_num] in Hn.
      destruct (classified_carg_num n Ks (classified_carg_tag κ g)) as [g' |] eqn:Eg; [| discriminate ].
      destruct (classified_cargs_num n Ks gsr) as [gs2' |] eqn:Egs; [| discriminate ].
      injection Hn as <-.
      set (τ := sb_selfs p (List.length args1 + np) n t).
      (** The filed entry is tagged as written: a non-recursive argument at
          its own tag, a recursive one relevant ([Hκ]). *)
      assert (Hkind : carg_entry_kind g' = κ).
      { destruct g as [κ0 A0 | r0]; cbn in Eg.
        - injection Eg as <-; reflexivity.
        - destruct (classified_ptyp_num n Ks r0); cbn in Eg; [ injection Eg as <- | discriminate ].
          cbn; symmetry; exact (Hκ eq_refl). }
      (** The classification untagged is filed at the same type. *)
      assert (Eg0 : exists g0', classified_carg_num n Ks g = Some g0' /\
                  carg_entry p D (im_nn Mj) pat g0' = carg_entry p D (im_nn Mj) pat g').
      { destruct g as [κ0 A0 | r0]; cbn in Eg |- *.
        - injection Eg as <-; eexists; split; reflexivity.
        - destruct (classified_ptyp_num n Ks r0); cbn in Eg; [ injection Eg as <- | discriminate ].
          eexists; split; reflexivity. }
      destruct Eg0 as (g0' & Eg0 & Ee0).
      (** The argument as classified, as written or as its normal form, and
          its filed entry. *)
      assert (Hlp : List.length pat = List.length args1) by (rewrite Hpat, length_cargs_pat; lia).
      set (Γraw := raw_args_tele args1 ++ raw_member_args_ctx Ξ R Mr) in *.
      assert (EΓu : List.skipn (List.length pat + (np - nu)) Γraw = raw_decl_uniform_ctx Ξ R)
        by (unfold Γraw, np; rewrite Hlp; replace (List.length (raw_member_nparams Mr) + nu - nu)
              with (List.length (raw_member_nparams Mr)) by lia; apply member_ctx_skipn).
      (** The argument with its instance that of its filed view: as written,
          or equal to its normal form, and filed as [g'] *)
      assert (Hrep : forall gw, written_carg_key Θ Ξ (List.skipn (List.length pat + (np - nu)) Γraw) gw g ->
                     match gw with classified_carg_rec_case tw => ptyp_selfs_lt n tw | _ => True end ->
                     (written_carg_exp nu np n pat (carg_rep Ks g))[τ] = carg_entry p D (im_nn Mj) pat g').
      { intros gw Hk' Hlt; rewrite <- Ee0.
        unfold τ; rewrite <- Hlp.
        unfold im_nn; rewrite Hnp.
        apply (carg_rep_filed p D Ks nu n t (List.length (raw_member_nparams Mr)) filed_nu filed_mty_decl filed_view); [| exact Eg0 ].
        destruct Hk' as [κ0 A0 | tw tc Hkt]; [ exact I | exact (ptyp_selfs_lt_key _ _ _ _ _ _ Hkt Hlt) ]. }
      assert (HT' : exists T', (T' = T \/ exists i, Θ ⍮ Ξ ⍮ Γraw ⊢ T ≈ T' : Typeω@i) /\ T'[τ] = carg_entry p D (im_nn Mj) pat g').
      { destruct Hg as [gw g0 Hc Hk' | i W gw g0 _ HTt HW _ Hc Hk'].
        - (** As written: no instance *)
          destruct (classify_arg_exp _ _ _ _ _ _ _ _ Hc) as [ET Hok].
          exists T; split; [ left; reflexivity |].
          rewrite <- (Hrep gw Hk' ltac:(destruct gw; [ exact I | exact (proj1 Hok) ])).
          f_equal; rewrite ET.
          destruct Hk' as [κ0 A0 | tw tc Hkt]; [ reflexivity |].
          cbn [carg_rep written_carg_exp]; rewrite (ptyp_rep_none _ _ _ Ks _ _ Hkt (proj2 Hok)); reflexivity.
        - (** As its normal form: each instance equal to its filed view's *)
          destruct (classify_arg_exp _ _ _ _ _ _ _ _ Hc) as [EW Hok].
          exists (written_carg_exp nu np n pat (carg_rep Ks g0)); split;
            [ right | exact (Hrep gw Hk' ltac:(destruct gw; [ exact I | exact (proj1 Hok) ])) ].
          pose proof (@soundness_ty' (gc_mk Θ Ξ) _ _ _ _ HTt HW) as HTW.
          destruct Hk' as [κ0 A0 | tw tc Hkt]; [ exists i; rewrite EW in HTW; exact HTW |].
          cbn [carg_rep written_carg_exp] in EW |- *.
          assert (HΓraw : ⊢ Θ ⍮ Ξ ⍮ Γraw) by (gen_presups; assumption).
          assert (Hm : List.length pat + (np - nu) <= List.length Γraw)
            by (unfold Γraw, np; rewrite List.length_app, length_raw_args_tele; unfold raw_member_args_ctx;
                rewrite List.length_app, length_tele_wk, List.length_app; lia).
          assert (HΓu : ⊢ Θ ⍮ Ξ ⍮ List.skipn (List.length pat + (np - nu)) Γraw)
            by (rewrite <- (List.firstn_skipn (List.length pat + (np - nu)) Γraw) in HΓraw; exact (ctx_app_wf_tail _ _ _ _ HΓraw)).
          assert (HWt : Θ ⍮ Ξ ⍮ Γraw ⊢ written_ptyp_exp nu np n pat 0 tw : Typeω@i)
            by (rewrite <- EW; exact (presup_exp_eq_right HTW)).
          destruct (ptyp_rep_eq Θ Ξ _ Ks nu np n pat tw tc Hkt (proj2 Hok)) with (d := 0) (Ψ := Γraw) (i := i) as [i' Hi'];
            [ | exact HΓu | exact (wf_wk_pat_trues_skipn _ _ _ _ Hm HΓraw) | exact HWt |].
          + intros x Hx; rewrite EΓu.
            cbn [classified_carg_num] in Eg0.
            destruct (classified_ptyp_num n Ks tc) as [s |] eqn:Es; [| discriminate ].
            destruct (ptyp_num_index _ _ _ _ Es _ Hx) as [v Hv].
            destruct (view_key_index_in _ _ _ Hv) as (y0 & Hy0 & Hxy0).
            unfold key_rep; rewrite Hv, (List.nth_error_nth _ _ x Hy0).
            split; [ exact Hxy0 | exact (Hsrc _ (filed_keys_in _ _ _ (List.nth_error_In _ _ Hy0))) ].
          + exists (max i i'); eapply wf_exp_eq_trans; [ apply lift_exp_eq_max_left; rewrite EW in HTW; exact HTW
                                                   | apply lift_exp_eq_max_right; exact Hi' ]. }
      destruct HT' as (T' & HTT & Hentry).
      assert (EP : im_params D Mj = raw_member_nparams Mr ++ raw_decl_uparams R ++ gs_tele Ξ) by (unfold im_params; rewrite Hnp; reflexivity).
      (** The filed entry is a type after the filed arguments before it. *)
      assert (Hin' : In (c, (gs1 ++ g' :: nil) ++ gs2') (im_cons Mj))
        by (rewrite <- List.app_assoc; cbn; rewrite <- Hall; exact Hin).
      destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ filed_wf (decls_of_ctx _ _ _ (wf_ctx_empty _ _ filed_wf)) filed_lookup Hk Hin'
                  (gs1 ++ g' :: nil) gs2' eq_refl) as (HRk & _ & _).
      rewrite cargs_ctx_snoc, cargs_ctx_aux_single, <- Hpat, Hkind in HRk; cbn [List.app] in HRk.
      destruct (ctx_decomp_kind HRk) as (S1 & HS1 & HT'i).
      pose proof (ctx_sub_escape _ _ _ _ Hsub) as Hid.
      assert (HT'L : Θ ⍮ Ξf ⍮ tele_sub (raw_args_tele args1) (sb_selfs p np n t) ++ im_params D Mj ⊢ T'[τ] : S1)
        by (rewrite Hentry; pose proof (sub_preserves_exp _ _ _ _ _ _ _ HT'i Hid) as H; rewrite !exp_sub_id in H; exact H).
      (** The argument as written and as classified are equal, the [Self]s
          instantiated. *)
      assert (HTe : exists S2, type_sort S2 /\ Θ ⍮ Ξf ⍮ tele_sub (raw_args_tele args1) (sb_selfs p np n t) ++ im_params D Mj
                                 ⊢ T[τ] ≈ T'[τ] : S2).
      { destruct HTT as [-> | [i2 HTe]]; [ exists S1; split; [ exact (sort_kind_type_sort _ _ HS1) | apply wf_exp_eq_refl; exact HT'L ] |].
        exists Typeω@i2; split; [ constructor |].
        pose proof (proj1 (proj2 (proj2 (gctx_embedding_preserves_wf _ _ _ _ filed_gctx_embedding))) _ _ _ _ HTe) as HTe'.
        pose proof (presup_exp_eq_ctx HTe') as Hraw.
        assert (Hb : ⊢ Θ ⍮ Ξf ⍮ raw_member_args_ctx Ξ R Mr) by exact (ctx_app_wf_tail _ _ _ _ Hraw).
        assert (HP : ⊢ Θ ⍮ Ξf ⍮ raw_member_nparams Mr ++ raw_decl_uparams R ++ gs_tele Ξ)
          by (rewrite <- EP; exact (member_params_wf _ _ _ _ _ filed_decl_typed Hk)).
        pose proof (wf_sub_ext _ _ (raw_args_tele args1) _ _ _ (base_sub Mr Hb HP)) as Hτ.
        rewrite <- EP in Hτ; specialize (Hτ (ctx_sub_dom _ _ _ _ Hsub) Hraw).
        rewrite length_raw_args_tele in Hτ; unfold sb_selfs in Hτ; rewrite <- sb_qn_plus in Hτ;
          fold (sb_selfs p (List.length args1 + np) n t) in Hτ.
        exact (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HTe' Hτ). }
      destruct HTe as (S2 & HS2 & HTe).
      (** The argument's type and its entry's are of one sort at the tag,
          up to the level: a type of a universe is no proposition. *)
      assert (Hsd : exists Sd, sort_kind Sd κ /\
                 Θ ⍮ Ξf ⍮ tele_sub (raw_args_tele args1) (sb_selfs p np n t) ++ im_params D Mj ⊢ T'[τ] : Sd /\
                 Θ ⍮ Ξf ⍮ cargs_ctx p D Mj gs1 ++ im_params D Mj ⊢ carg_entry p D (im_nn Mj) pat g' : Sd /\
                 Θ ⍮ Ξf ⍮ tele_sub (raw_args_tele args1) (sb_selfs p np n t) ++ im_params D Mj ⊢ T[τ] ≈ T'[τ] : Sd).
      { assert (HT'2 : Θ ⍮ Ξf ⍮ tele_sub (raw_args_tele args1) (sb_selfs p np n t) ++ im_params D Mj ⊢ T'[τ] : S2)
          by (gen_presups; assumption).
        inversion HS1 as [k1 | |]; subst; destruct HS2 as [k2 | |].
        - exists Typeω@(max k1 k2); repeat split; [ constructor | eapply lift_exp_max_left; exact HT'L
                                                 | eapply lift_exp_max_left; exact HT'i | eapply lift_exp_eq_max_right; exact HTe ].
        - exfalso; exact (@typ_prop_absurd (gc_mk Θ Ξf) _ _ _ HT'L HT'2).
        - exfalso; exact (@level_type_not_large (gc_mk Θ Ξf) _ _ _ HT'2 HT'L).
        - exfalso; exact (@typ_prop_absurd (gc_mk Θ Ξf) _ _ _ HT'2 HT'L).
        - exists Propₘ; repeat split; [ constructor | exact HT'L | exact HT'i | exact HTe ].
        - exfalso; exact (@level_type_not_prop (gc_mk Θ Ξf) _ _ HT'2 HT'L).
        - exfalso; exact (@level_type_not_large (gc_mk Θ Ξf) _ _ _ HT'L HT'2).
        - exfalso; exact (@level_type_not_prop (gc_mk Θ Ξf) _ _ HT'L HT'2).
        - exists LevelSort; repeat split; [ constructor | exact HT'L | exact HT'i | exact HTe ]. }
      destruct Hsd as (Sd & HSd & HT'd & HEd & HTed).
      assert (HTL : Θ ⍮ Ξf ⍮ tele_sub (raw_args_tele args1) (sb_selfs p np n t) ++ im_params D Mj ⊢ T[τ] : Sd)
        by (gen_presups; assumption).
      (** The context after it. *)
      assert (Hsub' : Θ ⍮ Ξf ⊢ tele_sub (raw_args_tele (args1 ++ (y, κ, T) :: nil)) (sb_selfs p np n t) ++ im_params D Mj
                        ⊆ cargs_ctx p D Mj (gs1 ++ g' :: nil) ++ im_params D Mj).
      { rewrite raw_args_tele_app, tele_sub_app; cbn [raw_args_tele List.map List.rev List.app tele_sub centry_sub List.length snd fst].
        rewrite length_raw_args_tele.
        rewrite cargs_ctx_snoc, cargs_ctx_aux_single, <- Hpat, <- Hentry, Hkind; cbn [List.app].
        change (sb_qn 0 ?x) with x.
        replace (sb_qn (List.length args1) (sb_selfs p np n t)) with τ
          by (unfold τ, sb_selfs; rewrite sb_qn_plus; reflexivity).
        eapply ctx_sub_extend;
          [ exact Hsub | rewrite Hentry; exact HEd | exact HSd | exact HTL | exact HSd
          | eapply proj1, wf_subtyp_of_exp_eq; [ exact HTL | exact HT'd | exact (sort_kind_type_sort _ _ HSd) | exact HTed ] ]. }
      assert (Hpat' : classified_carg_bit g :: pat = cargs_pat (gs1 ++ g' :: nil))
        by (rewrite cargs_pat_snoc, <- (classified_carg_bit_tag κ g), <- (classified_carg_num_bit _ _ _ _ Eg), Hpat; reflexivity).
      destruct (IH (gs1 ++ g' :: nil) gs2' eq_refl ltac:(rewrite <- List.app_assoc; exact Hall) Hpat'
                  ltac:(rewrite !List.length_app, Hlen; reflexivity) Hsub') as [j0 Hj0].
      (** The two sides as [Π]s. *)
      rewrite raw_args_tele_cons, tele_sub_app; cbn [tele_sub centry_sub List.length]; rewrite ctx_pi_snoc.
      assert (Ecg : cargs_ctx_aux p D (im_nn Mj) pat (g' :: gs2')
                    = cargs_ctx_aux p D (im_nn Mj) (classified_carg_bit g :: pat) gs2'
                        ++ ce_ass (carg_entry_kind g') (carg_entry p D (im_nn Mj) pat g') :: nil)
        by (rewrite <- (classified_carg_bit_tag κ g), (classified_carg_num_bit _ _ _ _ Eg); destruct g'; reflexivity).
      rewrite Ecg, ctx_pi_snoc, Hkind.
      rewrite raw_args_tele_app, tele_sub_app in Hj0; cbn [raw_args_tele List.map List.rev List.app tele_sub centry_sub List.length snd] in Hj0.
      rewrite length_raw_args_tele, List.length_app in Hj0; cbn [List.length] in Hj0.
      replace (List.length args1 + 1 + np) with (1 + (List.length args1 + np)) in Hj0 by lia.
      assert (E1 : sb_qn (List.length args1) (sb_selfs p np n t) = τ) by (unfold τ, sb_selfs; rewrite sb_qn_plus; reflexivity).
      assert (E2 : sb_selfs p (1 + (List.length args1 + np)) n t = sb_qn 1 τ)
        by (unfold τ, sb_selfs; rewrite sb_qn_plus; reflexivity).
      change (sb_qn 0 ?x) with x in Hj0 |- *.
      rewrite E1, E2 in Hj0.
      rewrite <- Hentry.
      exact (pi_cong_sort HSd HTL HTed Hj0).
  Qed.

  (** A constructor of a declared member is filed at a type equal to the
      user's. *)
  Lemma member_con_ty : forall j Mr c args, List.nth_error (raw_decl_members R) j = Some Mr -> In (c, args) (raw_member_cons Mr) ->
      filed_con_ty Θ Ξf p j c (user_con_ty p R Mr j (gs_tele Ξ) args).
  Proof.
    intros * Hj Hin.
    destruct (Forall2_nth_error_l _ _ _ _ _ Hcls Hj) as (cs & Hcs & Hcl).
    destruct (Forall2_in_left _ _ _ _ Hcl Hin) as ([c' gsr] & Hin' & Heq & Hc); cbn [fst snd] in Heq, Hc; subst c'.
    destruct (filed_member _ _ _ Hj Hcs) as (cs' & Hcs' & Hk).
    set (Mj := mk_imember (mh_decl (ind_qname Ξ (raw_member_name Mr))) (raw_member_nparams Mr) cs') in *.
    destruct (classified_cons_num_in _ _ _ _ _ _ Hcs' Hin') as (gs & Hgs & Hing).
    assert (HinM : In (c, gs) (im_cons Mj)) by exact Hing.
    pose proof (cons_lookup_nodup _ _ _ (decl_typed_nodup _ _ _ filed_decl_typed _ _ Hk) HinM) as Hcon.
    apply (mk_filed_con_ty _ _ _ _ _ _ D Mj gs filed_lookup Hk Hcon).
    pose proof (classify_args_in_length _ _ _ _ _ _ _ _ _ _ Hc) as Hlen.
    assert (Hjn : j < n) by (unfold raw_decl_nmembers; apply List.nth_error_Some; congruence).
    unfold con_ty, user_con_ty, cargs_ctx; rewrite ctx_pi_sub.
    set (np := List.length (raw_member_nparams Mr) + nu) in *.
    rewrite length_raw_args_tele.
    assert (Lgs : List.length gs = List.length args).
    { rewrite <- Hlen; clear -Hgs; revert gs Hgs; induction gsr as [| g gsr IH]; intros gs H; cbn in H;
        [ injection H as <-; reflexivity |].
      destruct (classified_carg_num n Ks g); [| discriminate ]; destruct (classified_cargs_num n Ks gsr) eqn:E; [| discriminate ].
      injection H as <-; cbn; f_equal; apply IH; reflexivity. }
    (** The result type: [Self_j] at the member's parameters is the type
        former at the frames' and the member's parameters. *)
    assert (Eres : (apps (a_var (List.length args + np + (n - 1 - j))) (vars_from (List.length args) np))
                     [sb_qn (List.length args) (sb_selfs p np n t)]
                   = ind_mty p D j (ind_uvars D (im_nn Mj) (List.length gs)) (vars_from (List.length gs) (im_nn Mj))).
    { replace (sb_qn (List.length args) (sb_selfs p np n t)) with (sb_selfs p (List.length args + np) n t)
        by (unfold sb_selfs; rewrite sb_qn_plus; reflexivity).
      rewrite apps_exp_sub, self_var_sub by lia.
      replace (n - 1 - (List.length args + np + (n - 1 - j) - (List.length args + np))) with j by lia.
      unfold sb_selfs at 1; rewrite vars_from_sub by lia.
      rewrite (filed_mty_decl _ _ _ Hjn), <- apps_exp_app; f_equal.
      unfold ind_uvars; rewrite filed_nu, Lgs; cbn [im_nn im_nparams Mj]; unfold np.
      change (im_nn Mj) with (List.length (raw_member_nparams Mr)).
      set (a := List.length args); set (k := List.length (raw_member_nparams Mr)).
      replace (k + nu) with (nu + k) by lia; rewrite <- (vars_from_app a nu k).
      replace (nu + t) with (t + nu) by lia; rewrite <- (vars_from_app (a + k) t nu).
      rewrite List.app_assoc; do 3 f_equal; lia. }
    rewrite Eres.
    (** The arguments, from none before. *)
    assert (HP : ⊢ Θ ⍮ Ξf ⍮ im_params D Mj) by exact (member_params_wf _ _ _ _ _ filed_decl_typed Hk).
    assert (Hsub0 : Θ ⍮ Ξf ⊢ tele_sub (raw_args_tele nil) (sb_selfs p np n t) ++ im_params D Mj ⊆ cargs_ctx p D Mj nil ++ im_params D Mj)
      by (cbn; apply ctx_sub_refl; exact HP).
    destruct (conv_tail j Mr Mj c gs Hj Hk eq_refl HinM nil nil args gsr Hc nil gs Hgs eq_refl eq_refl eq_refl Hsub0) as [i Hi].
    cbn [raw_args_tele tele_sub List.app List.length List.rev List.map] in Hi; rewrite Nat.add_0_l in Hi.
    assert (HP0 : ⊢ Θ ⍮ Ξf ⍮ im_params D Mj ++ ⋅) by (rewrite List.app_nil_r; exact HP).
    destruct (ctx_pi_ass_eq _ _ _ ⋅ _ _ _ (decl_closed_params_ass _ _ _ filed_decl_closed Hk) HP0
                ltac:(rewrite List.app_nil_r; exact Hi)) as [i' Hi'].
    exists i'; apply wf_exp_eq_sym; exact Hi'.
  Qed.

End ConTypes.

(** A run of a group's declaration files, for each declared member, the
    constructors the user wrote, at types equal to the user's with the
    [Self]s the members' type formers at the frames' parameters, in the
    global context the run makes. *)
Theorem run_cmd_ind_con_types : forall load_path read to_core ch B Rb Θ Ξ pv R B' Rb' Θ' Ξ' Mr0 Mrs,
    Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ core_cmd_inductive pv R ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> ⊢ᵍ Θ ⍮ Ξ ->
    raw_decl_members R = Mr0 :: Mrs ->
    forall j Mr c args, List.nth_error (raw_decl_members R) j = Some Mr -> In (c, args) (raw_member_cons Mr) ->
      filed_con_ty Θ' Ξ' (ind_qname Ξ (raw_member_name Mr0)) j c
        (user_con_ty (ind_qname Ξ (raw_member_name Mr0)) R Mr j (gs_tele Ξ) args).
Proof.
  intros * Hr HΞ HMr * Hj Hin.
  inversion Hr; subst.
  (** The group as filed: its declared members, then its views. *)
  match goal with
  | Hfiled : raw_decl_filed _ _ R _ _ _ _ _ = Some _ |- _ => pose proof (raw_decl_filed_uparams _ _ _ _ _ _ _ _ _ Hfiled) as Hu
  end.
  match goal with
  | HM : raw_decl_members R = _ :: _, Hfiled : raw_decl_filed _ _ R _ _ _ _ _ = Some _ |- _ =>
      rewrite HMr in HM; injection HM as <- <-;
      unfold raw_decl_filed in Hfiled; rewrite HMr in Hfiled;
      destruct (raw_members_filed _ _ _ _ _) as [Ms |] eqn:Hms; [| discriminate ];
      destruct (raw_views_filed _ _ _ _ _ _ _ _ _ _) as [Mvs |] eqn:Hmvs; [| discriminate ];
      injection Hfiled as <-; rewrite <- HMr in Hms
  end.
  (** The declared members, each with its module, file no unit and embed the
      stack; the group is found at its first member's path. *)
  match goal with
  | Hm : run_ind_members _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?Ξf |- _ =>
      pose proof Hm as Hm'; rewrite HMr in Hm'; cbn [List.map] in Hm';
      pose proof (ind_members_run_lookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm' HΞ Hu) as Hlk;
      destruct (ind_members_run_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HΞ Hu) as [-> -> -> Hwf1 Hsub1]
  end.
  (** The recursor module, if any, is filed after the members. *)
  match goal with
  | Hrec : run_cmds _ _ _ _ _ _ _ _ (List.map ci_core (rec_cmds _ _ _ _ _)) _ _ _ _, Hwf1 : ⊢ᵍ Θ ⍮ ?Ξf |- _ =>
      destruct (rec_cmds_run_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrec Hwf1) as [-> -> -> Hwf Hsub];
      apply (gctx_embedding_preserves_filed_con_ty Θ Ξf); [ constructor; assumption |]
  end.
  eapply member_con_ty; try eassumption; try (constructor; assumption).
  eapply views_sourced; eassumption.
Qed.
