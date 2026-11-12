(** * The Set Rules of the Eliminator

    At an environment of its context, the eliminator of a group at an
    element of a member's carrier has a result in the motive there: by
    induction on the group's least fixed point ([member_carrier_ind]), the
    element is built by a constructor from arguments whose recursive ones
    have results, which the branch takes, in its context, to a result in
    the motive at the constructor.

    The recursive results are functions of the arguments: along a leaf
    path, the eliminator's result at the end ([elim_result], described
    among the elements of the universe of the motives, without choice),
    under a domain the graph of the results at the argument's values, at a
    projection the results at the field ([leaf_result]). *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Weakening Substitution JudgmentSubstitution.
From Mctt.Core.SetModel.Interpretation.Global Require Import Model.
From Mctt.Core.SetModel.Cases Require Import UniverseCases ValidUnit MemberTypes Sel IndCases RecordCases.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths DescTyping MemberLemmas.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing.
Import ListNotations.

Section Eliminator.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).
  (** The global context is well formed *)
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  (** The valuation models the global context *)
  Hypothesis Hok : set_gctx_ok T γ.

(** ** Closed Contexts Read Only Their Own Entries *)

Lemma set_env_above_lt' : forall n ρ ρb x, x < n -> set_env_above n ρ ρb x = ρ x.
Proof.
  induction n as [| n IH]; intros ρ ρb x Hx; [lia |]. destruct x as [| x]; [reflexivity |]. cbn [set_env_above].
  change (set_env_extend (set_env_above n (set_env_tail ρ) ρb) (ρ 0) (S x)) with (set_env_above n (set_env_tail ρ) ρb x).
  rewrite IH by lia. reflexivity.
Qed.

Lemma set_env_above_ge' : forall n ρ ρb y, set_env_above n ρ ρb (n + y) = ρb y.
Proof. induction n as [| n IH]; intros ρ ρb y; [reflexivity |]. cbn [set_env_above Nat.add]. apply IH. Qed.

(** The values of a telescope read only its own entries. *)
Lemma set_env_values_agree : forall Δ ρ ρ', (forall x, x < List.length Δ -> ρ x = ρ' x) -> set_env_values Δ ρ = set_env_values Δ ρ'.
Proof.
  induction Δ as [| e Δ IH]; intros ρ ρ' E; [reflexivity |]. cbn [set_env_values List.length] in *.
  rewrite (IH (set_env_tail ρ) (set_env_tail ρ')); [| intros x Hx; unfold set_env_tail; apply E; lia].
  rewrite (E 0) by lia. reflexivity.
Qed.

(** A term of a closed context has one value at two environments whose
    entries in the context are equal, whatever they hold below it: both
    are read at environments holding both below the context. *)
Lemma set_interp_closed_ctx_functional : forall Δ ρ1 ρ2 M v1 v2, ctx_scoped 0 Δ -> exp_scoped (List.length Δ) M ->
    (forall x, x < List.length Δ -> set_entry_eq γ (ρ1 x) (ρ2 x)) ->
    set_env_eq γ (set_env_drop (List.length Δ) ρ1) (set_env_drop (List.length Δ) ρ1) ->
    set_env_eq γ (set_env_drop (List.length Δ) ρ2) (set_env_drop (List.length Δ) ρ2) ->
    set_interp T γ Δ ρ1 M v1 -> set_interp T γ Δ ρ2 M v2 -> set_eq v1 v2.
Proof.
  intros * HΔ HM E Ed1 Ed2 H1 H2. set (n := List.length Δ) in *.
  pose proof (wf_ctx_empty _ _ Hgw) as Hc.
  assert (Hwk : forall φ, gc_deps ⍮ gc_stack ⍮ nil ⊢ʷ φ : nil)
    by (intros φ; constructor; [exact Hc | exact Hc | intros ? ? Hl; inversion Hl | intros ? ? ? Hl; inversion Hl
                               | intros ? ? Hl; inversion Hl]).
  set (ρb := set_env_merge (set_env_drop n ρ1) (set_env_drop n ρ2)).
  assert (Hmv : forall ρ ρ' φ v, set_interp T γ Δ ρ M v -> (forall x, x < n -> ρ x = ρ' x) ->
            (forall y, ρ (n + y) = ρ' (n + φ y)) -> set_interp T γ Δ ρ' M v).
  { intros ρ ρ' φ v H Hlt Hge. rewrite <- (List.app_nil_r Δ) in H.
    pose proof (set_interp_wk T γ _ _ _ _ H Δ nil nil φ ρ' eq_refl (Hwk φ)) as H'.
    rewrite tele_closed_wk, List.app_nil_r in H' by exact HΔ. fold n in H'.
    rewrite (proj1 syn_scoped_wk_id M n (wk_qn n φ) HM (fun x Hx => wk_qn_lt n φ x Hx)) in H'.
    apply H'. intros x. destruct (Nat.lt_ge_cases x n) as [Hx | Hx].
    - rewrite wk_qn_lt by exact Hx. apply Hlt. exact Hx.
    - rewrite wk_qn_ge by exact Hx. replace x with (n + (x - n)) at 1 by lia. rewrite Hge. f_equal. lia. }
  set (ρ3 := set_env_above n ρ1 ρb). set (ρ3' := set_env_above n ρ2 ρb).
  assert (H1' : set_interp T γ Δ ρ3 M v1).
  { apply (Hmv ρ1 ρ3 (fun y => y + y) v1 H1); intros; unfold ρ3;
      [rewrite set_env_above_lt' by assumption; reflexivity | rewrite set_env_above_ge'; unfold ρb; rewrite set_env_merge_even; reflexivity]. }
  assert (H2' : set_interp T γ Δ ρ3' M v2).
  { apply (Hmv ρ2 ρ3' (fun y => S (y + y)) v2 H2); intros; unfold ρ3';
      [rewrite set_env_above_lt' by assumption; reflexivity | rewrite set_env_above_ge'; unfold ρb; rewrite set_env_merge_odd; reflexivity]. }
  apply (set_interp_functional T γ Hfn Hmods _ _ _ _ H1' ρ3' v2); [| exact H2'].
  intros x. unfold ρ3, ρ3'. destruct (Nat.lt_ge_cases x n) as [Hx | Hx].
  - rewrite !set_env_above_lt' by exact Hx. apply E. exact Hx.
  - replace x with (n + (x - n)) by lia. rewrite !set_env_above_ge'. unfold ρb, set_env_merge.
    destruct (Nat.even (x - n)); [apply Ed1 | apply Ed2].
Qed.

(** ** Pointwise Equal Environments *)

Lemma set_interp_env_ext : forall Ξ ρ ρ' M v, ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> (forall x, ρ x = ρ' x) ->
    set_interp T γ Ξ ρ M v -> set_interp T γ Ξ ρ' M v.
Proof.
  intros * Hc E H. pose proof (set_interp_wk T γ _ _ _ _ H nil Ξ Ξ wk_id ρ' eq_refl (wf_wk_id _ _ _ Hc) ltac:(intros; apply E)) as H'.
  cbn [tele_wk List.app wk_qn List.length] in H'. rewrite exp_wk_id in H'. exact H'.
Qed.

Lemma set_interp_gunit_env_ext : forall Ξ ρ ρ' U m, ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> (forall x, ρ x = ρ' x) ->
    set_interp_gunit T γ Ξ ρ U m -> set_interp_gunit T γ Ξ ρ' U m.
Proof.
  intros * Hc E H.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (set_interp_wk_all T γ))))) _ _ _ _ H nil Ξ Ξ wk_id ρ'
                (Build_wk_setting Ξ ρ nil Ξ Ξ wk_id ρ' eq_refl (wf_wk_id _ _ _ Hc) (fun x => E x))) as H'.
  cbn [tele_wk List.app wk_qn List.length] in H'. rewrite gunit_wk_id in H'. exact H'.
Qed.

Lemma set_entry_rel_ext : forall Ξ ρ ρ' ce e e', ⊢ gc_deps ⍮ gc_stack ⍮ ce :: Ξ -> (forall x, ρ x = ρ' x) ->
    set_entry_rel T γ Ξ ρ ce e e' -> set_entry_rel T γ Ξ ρ' ce e e'.
Proof.
  intros * Hc E He. pose proof (ctx_decomp_tail Hc) as Hc'.
  destruct ce as [κ A | A M | U | A M U]; cbn [set_entry_rel] in He |- *.
  - destruct He as (x & x' & a & [E1 E2 Ha Hx Ex]). exists x, x', a. constructor; try assumption.
    exact (set_interp_env_ext _ _ _ _ _ Hc' E Ha).
  - destruct He as (r0 & v & v' & w & [E1 E2 Hw Ev Ev']). exists r0, v, v', w. constructor; try assumption.
    exact (set_interp_env_ext _ _ _ _ _ Hc' E Hw).
  - destruct He as (m & m' & n & [E1 E2 Hn Em Em']). exists m, m', n. constructor; try assumption.
    exact (set_interp_gunit_env_ext _ _ _ _ _ Hc' E Hn).
  - destruct He as (v & v' & w & m & m' & n & [E1 E2 Hw Hn Ev Ev' Em Em']). exists v, v', w, m, m', n.
    constructor; try assumption; [exact (set_interp_env_ext _ _ _ _ _ Hc' E Hw) | exact (set_interp_gunit_env_ext _ _ _ _ _ Hc' E Hn)].
Qed.

(** Related environments of a well-formed context stay related at
    environments equal to them at every variable. *)
Lemma set_env_rel_ext : forall Ξ ρ1 ρ2 ρ1' ρ2', ⊢ gc_deps ⍮ gc_stack ⍮ Ξ -> (forall x, ρ1 x = ρ1' x) -> (forall x, ρ2 x = ρ2' x) ->
    set_env_rel T γ Ξ ρ1 ρ2 -> set_env_rel T γ Ξ ρ1' ρ2'.
Proof.
  induction Ξ as [| ce Ξ IH]; intros * Hc E1 E2 H.
  - intros x. rewrite <- E1, <- E2. apply H.
  - destruct H as [Ht He]. split.
    + apply (IH (set_env_tail ρ1) (set_env_tail ρ2)); [exact (ctx_decomp_tail Hc) | intros; apply E1 | intros; apply E2 | exact Ht].
    + rewrite <- E1, <- E2. eapply set_entry_rel_ext; [exact Hc | | exact He]. intros x. apply E1.
Qed.

Lemma set_env_values_resp : forall Δ ρ ρ', set_env_eq γ ρ ρ' -> list_set_eq (set_env_values Δ ρ) (set_env_values Δ ρ').
Proof.
  induction Δ as [| e Δ IH]; intros ρ ρ' E; cbn [set_env_values]; [constructor |].
  apply list_set_eq_app; [apply IH; intros x; apply E | constructor; [apply (set_entry_value_resp (γ := γ)); apply E | constructor]].
Qed.

(** ** Instances of Closed Telescopes

    A closed telescope [Ψ] over a closed base [B], instantiated in [Γ] by
    a substitution [σ] of the base: an environment of the instance reads
    one of [Ψ ++ B] ([inst_closed_env]), and grows by an element of the
    next type's reading there. *)

Section ClosedInstances.
  Variables (Γ B : ctx) (σ : sub) (Fσ : set_env -> set_env).
  Hypotheses (Hσ : set_gsub_with T γ Γ σ (B ++ Γ) Fσ) (HΓ : set_ctx T γ Γ) (HcΓ : ⊢ gc_deps ⍮ gc_stack ⍮ Γ).

(** The environment of [Ψ ++ B] an environment of [tele_sub Ψ σ ++ Γ]
    reads. *)
Definition inst_closed_env (Ψ : ctx) (ρo : set_env) : set_env :=
  set_env_moved (List.length (Ψ ++ B)) (set_env_drop (List.length Γ)) (set_env_moved (List.length Ψ) Fσ ρo).

Lemma inst_closed_env_in : forall Ψ ρo, ctx_scoped 0 (Ψ ++ B) -> set_ctx T γ (Ψ ++ B) -> set_ctx T γ ((Ψ ++ B) ++ Γ) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ B -> ⊢ gc_deps ⍮ gc_stack ⍮ (Ψ ++ B) ++ Γ ->
    set_env_in T γ (tele_sub Ψ σ ++ Γ) ρo ->
    set_env_in T γ (Ψ ++ B ++ Γ) (set_env_moved (List.length Ψ) Fσ ρo) /\ set_env_in T γ (Ψ ++ B) (inst_closed_env Ψ ρo).
Proof.
  intros * Hs HC HCΓ Hc HcΓ' Hρo. rewrite <- List.app_assoc in HCΓ, HcΓ'.
  pose proof (set_env_in_moved T γ Hfn Hmods _ _ _ _ _ _ Hσ HΓ HCΓ HcΓ' Hρo) as H1. split; [exact H1 |].
  pose proof (set_gsub_drop T γ _ HcΓ) as Hd.
  rewrite List.app_assoc in H1. rewrite <- (tele_sub_closed _ (sb_of_wk (wk_shiftn (List.length Γ))) Hs) in H1.
  pose proof (set_env_in_moved T γ Hfn Hmods _ _ _ _ _ _ Hd HΓ ltac:(rewrite List.app_nil_r; exact HC)
                ltac:(rewrite List.app_nil_r; exact Hc) H1) as H2.
  rewrite List.app_nil_r in H2. exact H2.
Qed.

(** Its values: the base's at [Fσ], then the telescope's. *)
Lemma inst_closed_env_values : forall Ψ ρo,
    set_env_values (Ψ ++ B) (inst_closed_env Ψ ρo) = set_env_values B (Fσ (set_env_drop (List.length Ψ) ρo)) ++ set_env_values Ψ ρo.
Proof.
  intros Ψ ρo. rewrite set_env_values_app. f_equal.
  - apply set_env_values_agree. intros x Hx. unfold inst_closed_env, set_env_drop, set_env_moved.
    rewrite set_env_above_lt' by (rewrite List.length_app; lia). replace (List.length Ψ + x) with (List.length Ψ + x) by reflexivity.
    rewrite set_env_above_ge'. reflexivity.
  - apply set_env_values_agree. intros x Hx. unfold inst_closed_env, set_env_moved.
    rewrite set_env_above_lt' by (rewrite List.length_app; lia). rewrite set_env_above_lt' by exact Hx. reflexivity.
Qed.

(** One more assumption of the telescope, at an element of its type's
    reading at the closed environment. *)
Lemma set_env_in_inst_extend : forall Ψ κ A F ρo x,
    ctx_scoped 0 (Ψ ++ B) -> exp_scoped (List.length (Ψ ++ B)) A -> set_ctx T γ (Ψ ++ B) -> set_ctx T γ ((Ψ ++ B) ++ Γ) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ B -> ⊢ gc_deps ⍮ gc_stack ⍮ (Ψ ++ B) ++ Γ ->
    set_reads T γ (Ψ ++ B) A F -> set_env_in T γ (tele_sub Ψ σ ++ Γ) ρo ->
    set_mem x (code_carrier (F (set_env_values (Ψ ++ B) (inst_closed_env Ψ ρo)))) ->
    set_env_in T γ (tele_sub (ce_ass κ A :: Ψ) σ ++ Γ) (set_env_extend ρo (set_entry_term κ x)).
Proof.
  intros * Hs HA HC HCΓ Hc HcΓ' HF Hρo Hx.
  destruct (inst_closed_env_in _ _ Hs HC HCΓ Hc HcΓ' Hρo) as [H1 H2].
  set (a := F (set_env_values (Ψ ++ B) (inst_closed_env Ψ ρo))) in *.
  pose proof (HF _ H2) as Ha. fold a in Ha.
  pose proof (set_gsub_drop T γ _ HcΓ) as Hd.
  assert (Hb1 : set_env_in T γ Γ (set_env_drop (List.length (Ψ ++ B)) (set_env_moved (List.length Ψ) Fσ ρo))).
  { rewrite List.app_assoc in H1. exact (set_env_rel_drop T γ _ _ _ _ H1). }
  pose proof (set_interp_moved T γ _ _ _ _ _ _ _ _ Hd ltac:(rewrite List.app_nil_r; exact Hc) Hb1 ltac:(rewrite List.app_nil_r; exact Ha))
    as Ha1.
  rewrite (tele_sub_closed _ _ Hs), (exp_scoped_sub_id _ _ _ HA (fun x Hx => sb_qn_lt _ _ _ Hx)), <- List.app_assoc in Ha1.
  assert (Hb2 : set_env_in T γ Γ (set_env_drop (List.length Ψ) ρo)) by exact (set_env_in_drop T γ _ _ _ _ Hρo).
  pose proof (set_interp_moved T γ _ _ _ _ _ _ _ _ Hσ ltac:(rewrite <- List.app_assoc in HcΓ'; exact HcΓ') Hb2 Ha1) as Ha2.
  split; [exact Hρo |]. cbn [set_entry_rel centry_sub tele_sub]. exists x, x, a.
  constructor; [reflexivity | reflexivity | exact Ha2 | exact Hx | apply set_eq_refl].
Qed.

End ClosedInstances.

(** ** Erasing Recursive Arguments

    The carriers read each argument after the arguments before it with the
    recursive ones erased ([arguments_fit]); the environments hold them.
    The types ignore each erasure ([set_constructor_ok_ignores]), at any
    values, so they ignore all of them. *)

(** [l] with the positions [P] erased. *)
Fixpoint erase_all (P : list nat) (l : list aczel_set) : list aczel_set :=
  match P with
  | nil => l
  | n :: P' => erase_at n (erase_all P' l)
  end.

Lemma length_erase_at : forall n l, n < List.length l -> List.length (erase_at n l) = List.length l.
Proof.
  intros n l Hn. unfold erase_at. rewrite List.length_app, List.length_firstn. cbn [List.length]. rewrite List.length_skipn. lia.
Qed.

Lemma length_erase_all : forall P l, (forall n, In n P -> n < List.length l) -> List.length (erase_all P l) = List.length l.
Proof.
  induction P as [| n P IH]; intros l HP; [reflexivity |]. cbn [erase_all].
  rewrite length_erase_at; [apply IH; intros; apply HP; right; assumption |].
  rewrite IH by (intros; apply HP; right; assumption). apply HP. left. reflexivity.
Qed.

(** A function that ignores each erasure at every list of a length
    ignores all of them. *)
Lemma erase_all_ignored : forall (F : list aczel_set -> aczel_set) N P l,
    (forall n l', In n P -> List.length l' = N -> set_eq (F l') (F (erase_at n l'))) ->
    (forall n, In n P -> n < N) -> List.length l = N -> set_eq (F l) (F (erase_all P l)).
Proof.
  intros F N P. induction P as [| n P IH]; intros l HF HP Hl; cbn [erase_all]; [apply set_eq_refl |].
  eapply set_eq_trans; [apply IH; [intros; apply HF; [right |]; assumption | intros; apply HP; right; assumption | exact Hl] |].
  apply HF; [left; reflexivity |]. rewrite length_erase_all; [exact Hl |]. intros m Hm. rewrite Hl. apply HP. right. exact Hm.
Qed.

Lemma erase_all_ignored_list : forall (F : list aczel_set -> list aczel_set) N P l,
    (forall n l', In n P -> List.length l' = N -> list_set_eq (F l') (F (erase_at n l'))) ->
    (forall n, In n P -> n < N) -> List.length l = N -> list_set_eq (F l) (F (erase_all P l)).
Proof.
  intros F N P. induction P as [| n P IH]; intros l HF HP Hl; cbn [erase_all]; [apply list_set_eq_refl |].
  eapply list_set_eq_trans; [apply IH; [intros; apply HF; [right |]; assumption | intros; apply HP; right; assumption | exact Hl] |].
  apply HF; [left; reflexivity |]. rewrite length_erase_all; [exact Hl |]. intros m Hm. rewrite Hl. apply HP. right. exact Hm.
Qed.

Lemma nth_error_erase_at : forall n l i, n < List.length l ->
    List.nth_error (erase_at n l) i = if Nat.eqb i n then Some empty_set else List.nth_error l i.
Proof.
  intros n l i Hn. unfold erase_at. destruct (Nat.lt_trichotomy i n) as [Hi | [-> | Hi]].
  - rewrite List.nth_error_app1 by (rewrite List.length_firstn; lia). rewrite List.nth_error_firstn.
    destruct (Nat.ltb_spec i n); [| lia]. destruct (Nat.eqb_spec i n); [lia | reflexivity].
  - rewrite List.nth_error_app2 by (rewrite List.length_firstn; lia). rewrite List.length_firstn, Nat.min_l by lia.
    rewrite Nat.sub_diag, Nat.eqb_refl. reflexivity.
  - rewrite List.nth_error_app2 by (rewrite List.length_firstn; lia). rewrite List.length_firstn, Nat.min_l by lia.
    destruct (i - n) as [| k] eqn:E; [lia |]. cbn [List.nth_error]. rewrite List.nth_error_skipn.
    destruct (Nat.eqb_spec i n); [lia |]. f_equal. lia.
Qed.

(** The values of arguments as the carriers read them: the recursive
    ones erased. *)
Fixpoint erase_args (sgs : list set_argument) (vals : list aczel_set) : list aczel_set :=
  match sgs, vals with
  | set_argument_plain _ _ :: sgs', v :: vals' => v :: erase_args sgs' vals'
  | set_argument_recursive _ _ _ _ :: sgs', _ :: vals' => empty_set :: erase_args sgs' vals'
  | _, _ => nil
  end.

Lemma length_erase_args : forall sgs vals, List.length sgs = List.length vals -> List.length (erase_args sgs vals) = List.length vals.
Proof. induction sgs as [| [] sgs IH]; intros [| v vals] Hl; cbn in *; try lia; rewrite IH by lia; reflexivity. Qed.

(** The [k]-th argument erased, if recursive, after the first [k]. *)
Lemma erase_args_firstn_S : forall k sgs vals g v, List.nth_error sgs k = Some g -> List.nth_error vals k = Some v ->
    erase_args (List.firstn (S k) sgs) (List.firstn (S k) vals) =
    erase_args (List.firstn k sgs) (List.firstn k vals) ++
      [match g with set_argument_plain _ _ => v | set_argument_recursive _ _ _ _ => empty_set end].
Proof.
  induction k as [| k IH]; intros [| g0 sgs] [| v0 vals] g v Hg Hv; cbn in Hg, Hv; try discriminate.
  - injection Hg as <-. injection Hv as <-. destruct g0; reflexivity.
  - change (List.firstn (S (S k)) (g0 :: sgs)) with (g0 :: List.firstn (S k) sgs).
    change (List.firstn (S (S k)) (v0 :: vals)) with (v0 :: List.firstn (S k) vals).
    change (List.firstn (S k) (g0 :: sgs)) with (g0 :: List.firstn k sgs).
    change (List.firstn (S k) (v0 :: vals)) with (v0 :: List.firstn k vals).
    destruct g0; cbn [erase_args List.app]; rewrite (IH sgs vals g v Hg Hv); reflexivity.
Qed.

Lemma erase_at_app : forall A x B, erase_at (List.length A) (A ++ x :: B) = A ++ empty_set :: B.
Proof.
  intros. unfold erase_at. rewrite List.firstn_app, Nat.sub_diag, List.firstn_all; cbn [List.firstn]. rewrite List.app_nil_r.
  rewrite List.skipn_app, List.skipn_all2 by lia. replace (S (List.length A) - List.length A) with 1 by lia. reflexivity.
Qed.

(** A reading that ignores each recursive argument before the [j]-th, at
    every list of its length, reads the values with them erased alike. *)
Lemma erase_args_ignored_gen : forall {X : Type} (R : X -> X -> Prop), (forall x, R x x) -> (forall x y z, R x y -> R y z -> R x z) ->
    forall (F : list aczel_set -> X) L0 sgs vals j,
    (forall n L' ty ds tg tp, n < j -> List.nth_error sgs n = Some (set_argument_recursive ty ds tg tp) ->
       List.length L' = List.length L0 + j -> R (F L') (F (erase_at (List.length L0 + n) L'))) ->
    j <= List.length sgs -> j <= List.length vals ->
    R (F (L0 ++ List.firstn j vals)) (F (L0 ++ erase_args (List.firstn j sgs) (List.firstn j vals))).
Proof.
  intros X R Rrefl Rtrans F L0 sgs vals j HF Hjs Hjv.
  assert (C : forall k, k <= j ->
            R (F (L0 ++ List.firstn j vals))
                   (F (L0 ++ erase_args (List.firstn k sgs) (List.firstn k vals) ++ List.skipn k (List.firstn j vals)))).
  { induction k as [| k IH]; intros Hk; [cbn; apply Rrefl |].
    eapply Rtrans; [apply IH; lia |].
    destruct (List.nth_error sgs k) as [g |] eqn:Hg; [| apply List.nth_error_None in Hg; lia].
    destruct (List.nth_error vals k) as [v |] eqn:Hv; [| apply List.nth_error_None in Hv; lia].
    assert (Hs : List.skipn k (List.firstn j vals) = v :: List.skipn (S k) (List.firstn j vals)).
    { apply skipn_nth_cons. rewrite List.nth_error_firstn. destruct (Nat.ltb_spec k j); [exact Hv | lia]. }
    rewrite Hs, (erase_args_firstn_S k sgs vals g v Hg Hv), <- List.app_assoc. cbn [List.app].
    assert (Hlk : List.length (erase_args (List.firstn k sgs) (List.firstn k vals)) = k)
      by (rewrite length_erase_args; rewrite !List.length_firstn; lia).
    destruct g as [κ ty | ty ds tg tp]; [apply Rrefl |].
    rewrite !List.app_assoc.
    set (A := L0 ++ erase_args (List.firstn k sgs) (List.firstn k vals)).
    set (Bl := List.skipn (S k) (List.firstn j vals)).
    assert (HA : List.length A = List.length L0 + k) by (unfold A; rewrite List.length_app, Hlk; reflexivity).
    rewrite <- (erase_at_app A v Bl), HA. apply (HF k _ ty ds tg tp); [lia | exact Hg |].
    rewrite List.length_app, HA. cbn [List.length]. unfold Bl. rewrite List.length_skipn, List.length_firstn. lia. }
  eapply Rtrans; [apply (C j (le_n _)) |]. rewrite List.skipn_all2 by (rewrite List.length_firstn; lia).
  rewrite List.app_nil_r. apply Rrefl.
Qed.

Lemma erase_args_ignored : forall (F : list aczel_set -> aczel_set) L0 sgs vals j,
    (forall n L' ty ds tg tp, n < j -> List.nth_error sgs n = Some (set_argument_recursive ty ds tg tp) ->
       List.length L' = List.length L0 + j -> set_eq (F L') (F (erase_at (List.length L0 + n) L'))) ->
    j <= List.length sgs -> j <= List.length vals ->
    set_eq (F (L0 ++ List.firstn j vals)) (F (L0 ++ erase_args (List.firstn j sgs) (List.firstn j vals))).
Proof. intros. apply (erase_args_ignored_gen set_eq set_eq_refl set_eq_trans); assumption. Qed.

Lemma erase_args_ignored_list : forall (F : list aczel_set -> list aczel_set) L0 sgs vals j,
    (forall n L' ty ds tg tp, n < j -> List.nth_error sgs n = Some (set_argument_recursive ty ds tg tp) ->
       List.length L' = List.length L0 + j -> list_set_eq (F L') (F (erase_at (List.length L0 + n) L'))) ->
    j <= List.length sgs -> j <= List.length vals ->
    list_set_eq (F (L0 ++ List.firstn j vals)) (F (L0 ++ erase_args (List.firstn j sgs) (List.firstn j vals))).
Proof. intros. apply (erase_args_ignored_gen list_set_eq list_set_eq_refl list_set_eq_trans); assumption. Qed.

(** [arguments_fit]'s reading of each argument. *)
Lemma arguments_fit_nth : forall G bound S pre sgs vals, arguments_fit G bound S pre sgs vals ->
    forall j g v, List.nth_error sgs j = Some g -> List.nth_error vals j = Some v ->
    match g with
    | set_argument_plain _ type => set_mem v (code_carrier (type (pre ++ erase_args (List.firstn j sgs) (List.firstn j vals))))
    | set_argument_recursive _ ds target tparams =>
        set_mem v (shape_set G bound S (pre ++ erase_args (List.firstn j sgs) (List.firstn j vals)) ds target tparams nil)
    end.
Proof.
  induction 1 as [pre | pre κ type gs a vals Ha H IH | pre type ds target tparams gs a vals Ha H IH];
    intros [| j] g v Hg Hv; cbn in Hg, Hv; try discriminate.
  - injection Hg as <-. injection Hv as <-. rewrite List.app_nil_r. exact Ha.
  - specialize (IH j g v Hg Hv). cbn [List.firstn erase_args]. rewrite <- List.app_assoc in IH. exact IH.
  - injection Hg as <-. injection Hv as <-. rewrite List.app_nil_r. exact Ha.
  - specialize (IH j g v Hg Hv). cbn [List.firstn erase_args]. rewrite <- List.app_assoc in IH. exact IH.
Qed.

(** ** The Codes of Recursive Arguments *)

Lemma list_set_eq_firstn : forall n xs ys, list_set_eq xs ys -> list_set_eq (List.firstn n xs) (List.firstn n ys).
Proof.
  induction n as [| n IH]; intros xs ys E; [constructor |]. destruct E as [| x y xs ys Exy E]; cbn; constructor; [exact Exy | apply IH; exact E].
Qed.

Lemma pi_codomain_resp : forall C C' x x', set_eq C C' -> set_eq x x' -> set_eq (pi_codomain C x) (pi_codomain C' x').
Proof.
  intros * E Ex. unfold pi_codomain, code_datum. apply set_apply_resp; [| exact Ex].
  apply pair_second_resp. apply pair_first_resp. apply pair_second_resp. exact E.
Qed.

Lemma pi_codomain_pi_code_on : forall dom F x, respects_on (code_carrier dom) F -> set_mem x (code_carrier dom) ->
    set_eq (pi_codomain (pi_code dom F) x) (F x).
Proof.
  intros dom F x HF Hx. unfold pi_codomain, pi_code.
  eapply set_eq_trans; [apply set_apply_resp; [| apply set_eq_refl] |].
  - eapply set_eq_trans; [apply pair_second_resp; apply code_datum_type_code | apply pair_second_ordered_pair].
  - apply set_apply_graph_on; assumption.
Qed.

(** Equal [Π] codes have equal domains and codomains. *)
Lemma pi_code_inj : forall a F a' F', set_eq (pi_code a F) (pi_code a' F') -> respects_on (code_carrier a) F ->
    respects_on (code_carrier a') F' -> set_eq a a' /\ forall x, set_mem x (code_carrier a) -> set_eq (F x) (F' x).
Proof.
  intros * E HF HF'. assert (Ea : set_eq a a').
  { eapply set_eq_trans; [apply set_eq_sym; apply pi_domain_pi_code |]. eapply set_eq_trans; [| apply pi_domain_pi_code].
    unfold pi_domain, code_datum. apply pair_first_resp. apply pair_first_resp. apply pair_second_resp. exact E. }
  split; [exact Ea |]. intros x Hx.
  apply (set_eq_trans _ (pi_codomain (pi_code a F) x)); [apply set_eq_sym; apply pi_codomain_pi_code_on; assumption |].
  apply (set_eq_trans _ (pi_codomain (pi_code a' F') x)); [apply pi_codomain_resp; [exact E | apply set_eq_refl] |].
  apply pi_codomain_pi_code_on; [exact HF' |]. eapply set_mem_eq_r; [apply code_carrier_resp; exact Ea | exact Hx].
Qed.

Section ShapeCodes.
  Variable G : set_group.
  (** The carriers respect equal parameters *)
  Hypothesis HGresp : forall k ps ps', list_set_eq ps ps' -> set_eq (set_group_carrier G k ps) (set_group_carrier G k ps').

Lemma shape_code_resp : forall ds target tparams, Forall list_function_respects ds -> list_list_function_respects tparams ->
    forall pre pre' pts pts', list_set_eq pre pre' -> list_set_eq pts pts' ->
    set_eq (shape_code G ds target tparams pre pts) (shape_code G ds target tparams pre' pts').
Proof.
  intros ds target tparams Hds Htp. induction Hds as [| d ds Hd Hds IH]; intros pre pre' pts pts' Epre Epts; cbn [shape_code].
  - apply type_code_resp; [apply set_eq_refl |]. apply HGresp. apply list_set_eq_app;
      [apply list_set_eq_firstn; exact Epre | apply list_set_eq_skipn; apply Htp; apply list_set_eq_app; assumption].
  - apply pi_code_resp_on; [apply Hd; apply list_set_eq_app; assumption |].
    intros x x' _ Ex. apply IH; [exact Epre | apply list_set_eq_app; [exact Epts | constructor; [exact Ex | constructor]]].
Qed.

(** The elements of a recursive argument's set of shapes, at the
    candidate carriers [S], are of its code, when [S]'s elements at the
    shape's ends are the carriers'. *)
Lemma shape_set_sub_code : forall bound S pre target tparams ds pts1,
    Forall list_function_respects ds -> list_list_function_respects tparams ->
    (forall pts, points_fit ds pre pts1 pts ->
       let ps := tparams (pre ++ pts1 ++ pts) in
       set_sub (candidate_carrier bound S target (List.skipn (List.length (set_group_uniform_types G)) ps))
               (set_group_carrier G target (List.firstn (List.length (set_group_uniform_types G)) pre ++
                                            List.skipn (List.length (set_group_uniform_types G)) ps))) ->
    set_sub (shape_set G bound S pre ds target tparams pts1) (code_carrier (shape_code G ds target tparams pre pts1)).
Proof.
  intros bound S pre target tparams ds. induction ds as [| d ds IH]; intros pts1 Hds Htp Hl; cbn [shape_set shape_code].
  - intros z Hz. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
    specialize (Hl nil (points_fit_nil _ _)). cbv zeta in Hl. rewrite List.app_nil_r in Hl. exact (Hl z Hz).
  - inversion Hds as [| ? ? Hd Hds']; subst.
    intros z Hz. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |]. revert z Hz.
    apply function_set_mono_on.
    + intros x y _ E. apply shape_set_resp; [exact Hds' | exact Htp | apply list_set_eq_refl |
        apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact E | constructor]]].
    + intros x y _ E. apply code_carrier_resp. apply shape_code_resp; [exact Hds' | exact Htp | apply list_set_eq_refl |
        apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact E | constructor]]].
    + intros x Hx. apply IH; [exact Hds' | exact Htp |]. intros pts Hpts. cbv zeta.
      pose proof (Hl (x :: pts) (points_fit_cons _ _ _ _ _ _ Hx Hpts)) as H. cbv zeta in H.
      rewrite <- !List.app_assoc. cbn [List.app]. exact H.
Qed.

Lemma firstn_erase_at_ge : forall m n l, m <= n -> n < List.length l -> List.firstn m (erase_at n l) = List.firstn m l.
Proof.
  intros m n l Hmn Hl. unfold erase_at. rewrite List.firstn_app, List.firstn_firstn, Nat.min_l by exact Hmn.
  rewrite List.length_firstn, Nat.min_l by lia. replace (m - n) with 0 by lia. cbn. rewrite List.app_nil_r. reflexivity.
Qed.

(** A recursive argument's code ignores an erasure that its domains and
    target parameters ignore. *)
Lemma shape_code_erase : forall ds target tparams pre n, Forall list_function_respects ds -> list_list_function_respects tparams ->
    List.length (set_group_uniform_types G) <= n -> n < List.length pre ->
    forall pts1,
    (forall k d pts, List.nth_error ds k = Some d -> List.length pts = k ->
       set_eq (d (pre ++ pts1 ++ pts)) (d (erase_at n pre ++ pts1 ++ pts))) ->
    (forall pts, List.length pts = List.length ds ->
       list_set_eq (tparams (pre ++ pts1 ++ pts)) (tparams (erase_at n pre ++ pts1 ++ pts))) ->
    set_eq (shape_code G ds target tparams pre pts1) (shape_code G ds target tparams (erase_at n pre) pts1).
Proof.
  intros ds target tparams pre n Hds Htp Hn Hnl. induction Hds as [| d ds Hd Hds IH]; intros pts1 H1 H2; cbn [shape_code].
  - apply type_code_resp; [apply set_eq_refl |]. apply HGresp. rewrite firstn_erase_at_ge by assumption.
    apply list_set_eq_app; [apply list_set_eq_refl |]. apply list_set_eq_skipn.
    specialize (H2 nil eq_refl). rewrite !List.app_nil_r in H2. exact H2.
  - apply pi_code_resp_on.
    + specialize (H1 0 d nil eq_refl eq_refl). rewrite !List.app_nil_r in H1. exact H1.
    + intros x x' _ Ex. eapply set_eq_trans; [apply (IH (pts1 ++ [x])) |].
      * intros k d' pts Hk Hl. rewrite <- !List.app_assoc. cbn [List.app]. apply (H1 (S k) d' (x :: pts) Hk). cbn. lia.
      * intros pts Hl. rewrite <- !List.app_assoc. cbn [List.app]. apply (H2 (x :: pts)). cbn. lia.
      * apply shape_code_resp; [exact Hds | exact Htp | apply list_set_eq_refl |].
        apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact Ex | constructor]].
Qed.

Lemma repeat_false_snoc : forall n (pat : list bool), List.repeat false (S n) ++ pat = List.repeat false n ++ false :: pat.
Proof. induction n as [| n IH]; intros pat; [reflexivity |]. cbn [List.repeat List.app] in *. rewrite <- IH. reflexivity. Qed.

(** A recursive argument's type, read as its code: along points of the
    code's domains, an environment of the shape's domains, where the
    type's end reads the code's end. *)
Lemma shape_env_of_points : forall p D nn ds target tparams pre0 t pat Ψ θ C pts1,
    Forall list_function_respects ds -> list_list_function_respects tparams ->
    set_env_in T γ Ψ θ -> set_interp T γ Ψ θ (ptyp_ty p D nn pat t) C ->
    set_eq C (shape_code G ds target tparams pre0 pts1) -> List.length ds = ptyp_depth t ->
    forall pts, points_fit ds pre0 pts1 pts ->
    set_env_in T γ (shape_domains_ctx pat (ptyp_doms t) ++ Ψ) (set_env_extend_kinded θ (List.repeat ak_relevant (List.length pts)) pts) /\
    exists C', set_interp T γ (shape_domains_ctx pat (ptyp_doms t) ++ Ψ)
                 (set_env_extend_kinded θ (List.repeat ak_relevant (List.length pts)) pts)
                 (ptyp_ty p D nn (List.repeat false (ptyp_depth t) ++ pat) (pt_self (ptyp_mem t) (ptyp_ps t))) C' /\
               set_eq C' (shape_code G nil target tparams pre0 (pts1 ++ pts)).
Proof.
  intros p D nn ds target tparams pre0 t. revert ds.
  induction t as [j Ps | A t IH]; intros ds pat Ψ θ C pts1 Hds Htp Hθ HC EC Hl pts Hpts.
  - destruct ds; [| discriminate]. inversion Hpts; subst. cbn [List.length List.repeat set_env_extend_kinded shape_domains_ctx ptyp_doms
      List.app ptyp_depth ptyp_mem ptyp_ps] in *. rewrite List.app_nil_r. split; [exact Hθ |]. exists C. split; [exact HC | exact EC].
  - destruct ds as [| d ds]; [discriminate |]. cbn [List.length ptyp_depth ptyp_doms] in Hl. injection Hl as Hl.
    inversion Hds as [| ? ? Hd Hds']; subst.
    inversion Hpts as [| ? ? ? ? b pts' Hb Hpts']; subst.
    cbn [ptyp_ty] in HC. destruct (set_interp_pi_inv T γ _ _ _ _ _ _ _ HC) as (a1 & F & HA & HB & [[Hk _] | [_ ->]]);
      [discriminate |].
    cbn [shape_code] in EC.
    assert (Eθ : set_env_eq γ θ θ) by exact (set_env_rel_eq T γ _ _ _ Hθ).
    destruct (pi_code_inj _ _ _ _ EC (set_interp_family_respects T γ Hfn Hmods _ _ _ _ _ _ _ Eθ HB)) as [Ea EF].
    { intros x y _ E. apply shape_code_resp; [exact Hds' | exact Htp | apply list_set_eq_refl |].
      apply list_set_eq_app; [apply list_set_eq_refl | constructor; [exact E | constructor]]. }
    assert (Hb1 : set_mem b (code_carrier a1)) by (eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact Ea | exact Hb]).
    set (θ1 := set_env_extend θ (set_entry_term ak_relevant b)).
    assert (Hθ1 : set_env_in T γ (ce_ass ak_relevant (exp_wk A (wk_pat pat)) :: Ψ) θ1).
    { split; [exact Hθ |]. cbn [set_entry_rel]. exists b, b, a1. constructor; [reflexivity | reflexivity | exact HA | exact Hb1 | apply set_eq_refl]. }
    destruct (IH ds (false :: pat) _ θ1 (F b) (pts1 ++ [b]) Hds' Htp Hθ1 (HB b Hb1) (EF b Hb1) Hl pts' Hpts') as [Henv (C' & HC' & EC')].
    cbn [List.length List.repeat set_env_extend_kinded List.hd List.tl shape_domains_ctx ptyp_doms ptyp_depth ptyp_mem ptyp_ps].
    rewrite <- List.app_assoc. cbn [List.app].
    change (false :: List.repeat false (List.length (ptyp_doms t)) ++ pat) with (List.repeat false (S (List.length (ptyp_doms t))) ++ pat).
    rewrite repeat_false_snoc. unfold ptyp_depth in HC'. rewrite <- List.app_assoc in EC'. cbn [List.app] in EC'.
    split; [exact Henv |]. exists C'. split; [exact HC' | exact EC'].
Qed.

End ShapeCodes.

(** ** Arguments as Environments *)

Lemma set_tele_types_suffix : forall Γ0 X Δ Fs, set_tele_types T γ Γ0 (X ++ Δ) Fs ->
    set_tele_types T γ Γ0 Δ (List.firstn (List.length Δ) Fs).
Proof.
  induction X as [| e X IH]; intros Δ Fs H; cbn [List.app] in H.
  - rewrite <- (length_set_tele_types T γ _ _ _ H), List.firstn_all. exact H.
  - inversion H as [| κ A Δ0 Fs0 F H0 HA]; subst. pose proof (IH _ _ H0) as H1.
    rewrite List.firstn_app. rewrite (length_set_tele_types T γ _ _ _ H0), List.length_app.
    replace (List.length Δ - (List.length X + List.length Δ)) with 0 by lia. cbn. rewrite List.app_nil_r. exact H1.
Qed.

(** The kinds and the shapes of the semantic arguments, position by
    position. *)
Lemma set_arguments_shape_nth : forall gs sgs, set_arguments_shape gs sgs -> forall i g, List.nth_error gs i = Some g ->
    exists sg, List.nth_error sgs i = Some sg /\
      match g with
      | ca_arg κ _ => exists F, sg = set_argument_plain κ F
      | ca_rec t => exists F ds tparams, sg = set_argument_recursive F ds (ptyp_mem t) tparams /\ List.length ds = ptyp_depth t
      end.
Proof.
  induction 1 as [| κ A F gs sgs H IH | t F ds tparams gs sgs Hl H IH]; intros [| i] g Hg; cbn in Hg; try discriminate.
  - injection Hg as <-. eexists; split; [reflexivity | eauto].
  - exact (IH _ _ Hg).
  - injection Hg as <-. eexists; split; [reflexivity | eauto].
  - exact (IH _ _ Hg).
Qed.

Lemma set_arguments_shape_length : forall gs sgs, set_arguments_shape gs sgs -> List.length sgs = List.length gs.
Proof. induction 1; cbn; congruence. Qed.

(** The arguments' prefix of a constructor's telescope. *)
Lemma cargs_ctx_prefix : forall p D Mk gs1 rest,
    List.skipn (List.length (gs1 ++ rest) - List.length gs1) (cargs_ctx p D Mk (gs1 ++ rest)) = cargs_ctx p D Mk gs1.
Proof.
  intros. rewrite cargs_ctx_app, List.length_app.
  replace (List.length gs1 + List.length rest - List.length gs1) with (List.length rest) by lia.
  rewrite List.skipn_app, List.skipn_all2 by (rewrite length_cargs_ctx_aux; lia).
  rewrite length_cargs_ctx_aux, Nat.sub_diag. reflexivity.
Qed.

Lemma points_fit_length : forall ds pre pts1 pts, points_fit ds pre pts1 pts -> List.length pts = List.length ds.
Proof. induction 1; cbn; congruence. Qed.

Lemma length_shape_domains_ctx : forall Bs pat, List.length (shape_domains_ctx pat Bs) = List.length Bs.
Proof. induction Bs as [| B Bs IH]; intros pat; cbn [shape_domains_ctx]; [reflexivity |]. rewrite List.length_app, IH. cbn. lia. Qed.

Lemma set_env_extend_kinded_snoc_any : forall vs ρ κs x,
    set_env_extend_kinded ρ κs (vs ++ [x]) =
    set_env_extend (set_env_extend_kinded ρ κs vs) (set_entry_term (List.nth (List.length vs) κs ak_relevant) x).
Proof.
  induction vs as [| v vs IH]; intros ρ κs x; cbn [List.app set_env_extend_kinded List.length].
  - destruct κs; reflexivity.
  - rewrite IH. destruct κs; cbn [List.tl List.nth]; [destruct (List.length vs); reflexivity | reflexivity].
Qed.

(** The values of an environment extended by values, of any kinds. *)
Lemma set_env_values_extend_kinded_any : forall Δ ρ κs vs, List.length Δ = List.length vs ->
    set_env_values Δ (set_env_extend_kinded ρ κs vs) = vs.
Proof.
  induction Δ as [| e Δ IH]; intros ρ κs vs Hl.
  - destruct vs; [reflexivity | discriminate].
  - destruct (List.exists_last (l := vs) ltac:(intros ->; discriminate)) as (vs1 & x & ->).
    rewrite List.length_app in Hl; cbn in Hl. rewrite set_env_extend_kinded_snoc_any. cbn [set_env_values].
    change (set_env_tail (set_env_extend ?r ?e)) with r. rewrite IH by lia. reflexivity.
Qed.

(** Points of domains equal at every list are points of both. *)
Lemma points_fit_transfer : forall ds pre pre' pts1 pts, points_fit ds pre pts1 pts ->
    (forall k d pts0, List.nth_error ds k = Some d -> List.length pts0 = List.length pts1 + k ->
       set_eq (d (pre ++ pts0)) (d (pre' ++ pts0))) ->
    points_fit ds pre' pts1 pts.
Proof.
  induction 1 as [pre0 points | d ds pre0 points b pts Hb H IH]; intros Hd; constructor.
  - eapply set_mem_eq_r; [apply code_carrier_resp; apply (Hd 0 d points eq_refl); lia | exact Hb].
  - apply IH. intros k d' pts0 Hk Hl. apply (Hd (S k) d' pts0 Hk). rewrite List.length_app in Hl. cbn in Hl. lia.
Qed.

Section Arguments.
  (** The eliminator's context, an environment of it, the group, and the
      uniform parameters' instance *)
  Variables (Γ : ctx) (ρ : set_env) (p : qname) (D : ind_decl) (Us : list exp) (Fσ : set_env -> set_env).
  Hypotheses (HΓ : set_ctx T γ Γ) (HcΓ : ⊢ gc_deps ⍮ gc_stack ⍮ Γ) (Hρ : set_env_in T γ Γ ρ)
    (HD : ind_lookup gc_deps gc_stack p = Some D)
    (Hσ : set_gsub_with T γ Γ (sb_of_list sb_id Us) (ind_uparams D ++ Γ) Fσ).

  (** The uniform parameters' values *)
  Definition elim_uniform_values : list aczel_set := set_env_values (ind_uparams D) (Fσ ρ).

(** An environment of an instance whose part below it is [ρ] at every
    variable has the uniform parameters' values. *)
Lemma inst_uniform_values : forall ρ', (forall x, ρ' x = ρ x) ->
    list_set_eq (set_env_values (ind_uparams D) (Fσ ρ')) elim_uniform_values.
Proof.
  intros ρ' E. unfold elim_uniform_values. apply set_env_values_resp.
  assert (Hr : set_env_rel T γ Γ ρ' ρ) by (eapply set_env_rel_ext; [exact HcΓ | intros x; symmetry; apply E | intros x; reflexivity | exact Hρ]).
  pose proof (set_env_rel_eq T γ _ _ _ (set_gsub_rel _ _ _ _ _ _ Hσ _ _ Hr)) as E'. intros x. apply E'.
Qed.

  (** The group's carriers: the least fixed point in [U], at instances of
      the members' parameters over the uniform values *)
  Variable U : aczel_set.
  Hypothesis Hcar : forall k Mk ρk, ind_member D k = Some Mk -> set_env_in T γ (im_params D Mk) ρk ->
    list_set_eq (uniform_values D Mk ρk) elim_uniform_values ->
    set_eq (set_group_carrier (global_group γ p) k (set_env_values (im_params D Mk) ρk))
           (member_carrier (global_group γ p) elim_uniform_values U U k (set_env_values (im_nparams Mk) ρk)).
  (** The candidate carriers at hand, among the fixed point's points *)
  Variable S : aczel_set.
  Hypothesis HS : set_sub S (carrier_fixed_point (global_group γ p) elim_uniform_values U U).

Lemma group_uniform_count : List.length (set_group_uniform_types (global_group γ p)) = ind_nu D.
Proof.
  pose proof (set_group_ok_uniform _ _ _ _ _ (set_gctx_ok_groups _ _ Hok _ _ HD)) as H.
  rewrite (length_set_tele_types T γ _ _ _ H). reflexivity.
Qed.

(** At the end of a recursive argument's shape, the candidate carriers'
    elements are the carriers': the argument's points are an instance of
    its target's parameters ([set_constructor_ok_target_instance]). *)
Lemma recursive_leaf_sub : forall k Mk gs sgs gs1 t gs2 F ds target tparams θo C pre_e,
    ind_member D k = Some Mk -> set_constructor_ok T γ p D (global_group γ p) Mk gs sgs ->
    gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error sgs (List.length gs1) = Some (set_argument_recursive F ds target tparams) ->
    Forall list_function_respects ds -> list_list_function_respects tparams ->
    List.length ds = ptyp_depth t ->
    set_env_in T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo ->
    set_interp T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo (ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t) C ->
    set_eq C (shape_code (global_group γ p) ds target tparams (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo) nil) ->
    list_set_eq (List.firstn (ind_nu D) (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo)) elim_uniform_values ->
    list_set_eq (List.firstn (ind_nu D) pre_e) elim_uniform_values ->
    (forall k' d pts0, List.nth_error ds k' = Some d -> List.length pts0 = k' ->
       set_eq (d (pre_e ++ pts0)) (d (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo ++ pts0))) ->
    (forall pts, List.length pts = List.length ds ->
       list_set_eq (tparams (pre_e ++ pts)) (tparams (set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo ++ pts))) ->
    forall pts, points_fit ds pre_e nil pts ->
    let ps := tparams (pre_e ++ nil ++ pts) in
    set_sub (candidate_carrier U S target (List.skipn (List.length (set_group_uniform_types (global_group γ p))) ps))
            (set_group_carrier (global_group γ p) target
               (List.firstn (List.length (set_group_uniform_types (global_group γ p))) pre_e ++
                List.skipn (List.length (set_group_uniform_types (global_group γ p))) ps)).
Proof.
  intros * Hk Hcok Egs Hsg Hds Htp Hlds Hθo HC EC Hus Hpre Hdom Htps pts Hpts ps.
  unfold ps. rewrite group_uniform_count. cbn [List.app].
  set (G := global_group γ p) in *. set (Lv := set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θo) in *.
  (* the points are points of the code read at the environment's values *)
  assert (Hpts' : points_fit ds Lv nil pts)
    by (apply (points_fit_transfer _ _ _ _ _ Hpts); intros k' d pts0 Hk' Hl; cbn in Hl; exact (Hdom k' d pts0 Hk' Hl)).
  (* the environment of the shape's end *)
  destruct (shape_env_of_points (global_group γ p) (set_group_ok_carrier_resp _ _ _ _ _ (set_gctx_ok_groups _ _ Hok _ _ HD))
              p D (im_nn Mk) ds target tparams Lv t (cargs_pat gs1) _ θo C nil Hds Htp Hθo HC EC Hlds pts Hpts') as [Hθ' _].
  set (θ' := set_env_extend_kinded θo (List.repeat ak_relevant (List.length pts)) pts) in *.
  pose proof (points_fit_length _ _ _ _ Hpts) as Hlpts.
  assert (Hlds' : List.length (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t)) = List.length pts)
    by (rewrite length_shape_domains_ctx, Hlpts, Hlds; reflexivity).
  assert (Hθ'v : set_env_values (recursive_end_ctx p D Mk gs1 t) θ' = Lv ++ pts).
  { unfold recursive_end_ctx, θ'. rewrite set_env_values_app. f_equal.
    - unfold Lv. apply set_env_values_agree. intros x _. unfold set_env_drop. rewrite Hlds', set_env_extend_kinded_ge. reflexivity.
    - apply set_env_values_extend_kinded_any. exact Hlds'. }
  destruct (set_constructor_ok_target_instance _ _ _ _ _ _ _ _ Hcok gs1 t gs2 F ds target tparams Egs Hsg θ' Hθ')
    as (Mt & ρt & [HMt Hρt Evals]).
  rewrite Hθ'v in Evals.
  assert (HlLv : ind_nu D <= List.length Lv)
    by (unfold Lv; rewrite length_set_env_values, List.length_app, length_im_params; unfold im_np; lia).
  rewrite List.firstn_app, (proj2 (Nat.sub_0_le (ind_nu D) (List.length Lv)) HlLv), List.app_nil_r in Evals.
  unfold im_params in Evals. rewrite set_env_values_app in Evals.
  assert (Hlen : List.length (List.firstn (ind_nu D) Lv) =
                 List.length (set_env_values (ind_uparams D) (set_env_drop (List.length (im_nparams Mt)) ρt)))
    by (rewrite List.length_firstn, length_set_env_values, Nat.min_l by exact HlLv; reflexivity).
  destruct (list_set_eq_app_inv _ _ _ _ Hlen Evals) as [Eu En].
  assert (Hun : list_set_eq (uniform_values D Mt ρt) elim_uniform_values).
  { unfold uniform_values. rewrite <- (length_im_nparams Mt). eapply list_set_eq_trans; [apply list_set_eq_sym; exact Eu | exact Hus]. }
  pose proof (Hcar _ _ _ HMt Hρt Hun) as Ecar.
  intros z Hz.
  assert (Hz1 : set_mem z (member_carrier G elim_uniform_values U U target (set_env_values (im_nparams Mt) ρt))).
  { unfold member_carrier. eapply set_mem_eq_r; [apply candidate_carrier_resp |].
    - eapply list_set_eq_trans; [| exact En]. apply list_set_eq_skipn. apply Htps. rewrite Hlpts. reflexivity.
    - exact (candidate_carrier_mono _ _ _ _ _ HS _ Hz). }
  eapply set_mem_eq_r; [| eapply set_mem_eq_r; [apply set_eq_sym; exact Ecar | exact Hz1]].
  apply (set_group_ok_carrier_resp _ _ _ _ _ (set_gctx_ok_groups _ _ Hok _ _ HD)).
  unfold im_params. rewrite set_env_values_app. apply list_set_eq_app.
  - rewrite (length_im_nparams Mt). eapply list_set_eq_trans; [apply list_set_eq_sym; exact Eu |].
    eapply list_set_eq_trans; [exact Hus | apply list_set_eq_sym; exact Hpre].
  - eapply list_set_eq_trans; [apply list_set_eq_sym; exact En |]. apply list_set_eq_skipn. apply list_set_eq_sym. apply Htps.
    rewrite Hlpts. reflexivity.
Qed.

(** A member's parameters, and its constructors' arguments over them,
    denote, closed. *)
Lemma member_params_ctx : forall k Mk SMk, ind_member D k = Some Mk -> List.nth_error (set_group_members (global_group γ p)) k = Some SMk ->
    set_ctx T γ (im_params D Mk).
Proof.
  intros * Hk HSk. pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG.
  pose proof (set_ctx_of_tele_types T γ Hfn Hmods _ _ _ (set_group_ok_uniform _ _ _ _ _ HG) I) as HU. rewrite List.app_nil_r in HU.
  exact (set_ctx_of_tele_types T γ Hfn Hmods _ _ _ (set_member_ok_nparams _ _ _ _ _ _ _ (set_group_ok_members _ _ _ _ _ HG _ _ _ Hk HSk)) HU).
Qed.

Lemma cargs_prefix_ctx : forall k Mk SMk gs sgs gs1 rest, ind_member D k = Some Mk ->
    List.nth_error (set_group_members (global_group γ p)) k = Some SMk ->
    set_constructor_ok T γ p D (global_group γ p) Mk gs sgs -> gs = gs1 ++ rest ->
    set_ctx T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk).
Proof.
  intros * Hk HSk Hcok ->. pose proof (set_constructor_ok_types _ _ _ _ _ _ _ _ Hcok) as Ht.
  rewrite cargs_ctx_app in Ht. pose proof (set_tele_types_suffix _ _ _ _ Ht) as Ht'.
  exact (set_ctx_of_tele_types T γ Hfn Hmods _ _ _ Ht' (member_params_ctx _ _ _ Hk HSk)).
Qed.

(** The arguments of a constructor, built from arguments fitting the
    candidate carriers at the parameters of an environment of the member's
    non-uniform parameters, are an environment of the instance of their
    telescope. *)
Lemma args_env : forall k Mk SMk cs gs ρn vals,
    ind_member D k = Some Mk -> List.nth_error (set_group_members (global_group γ p)) k = Some SMk ->
    In cs (set_member_constructors SMk) -> ind_con Mk (set_constructor_name cs) = Some gs ->
    set_constructor_ok T γ p D (global_group γ p) Mk gs (set_constructor_arguments cs) ->
    set_env_in T γ (tele_sub (im_nparams Mk) (sb_of_list sb_id Us) ++ Γ) ρn -> (forall x, set_env_drop (im_nn Mk) ρn x = ρ x) ->
    arguments_fit (global_group γ p) U S (elim_uniform_values ++ set_env_values (im_nparams Mk) ρn) (set_constructor_arguments cs) vals ->
    forall gs1 rest, gs = gs1 ++ rest ->
    set_env_in T γ (tele_sub (cargs_ctx p D Mk gs1 ++ im_nparams Mk) (sb_of_list sb_id Us) ++ Γ)
      (set_env_extend_kinded ρn (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn (List.length gs1) vals)).
Proof.
  intros k Mk SMk cs gs ρn vals Hk HSk Hcs Hgs Hcok Hρn Hdrop Hfit.
  set (G := global_group γ p) in *. set (sgs := set_constructor_arguments cs) in *.
  pose proof (set_gctx_ok_groups _ _ Hok _ _ HD) as HG. fold G in HG.
  pose proof (set_constructor_ok_shape _ _ _ _ _ _ _ _ Hcok) as Hsh.
  pose proof (set_arguments_shape_length _ _ Hsh) as Hlsh.
  pose proof (arguments_fit_length _ _ _ _ _ _ Hfit) as Hlv.
  pose proof (set_group_ok_respects _ _ _ _ _ HG _ _ _ HSk Hcs) as Hrs. fold sgs in Hrs.
  pose proof (gctx_closed_ind _ _ _ _ (wf_gctx_closed _ _ _ HcΓ) HD) as Hcl.
  pose proof (decls_of_ctx _ _ _ HcΓ) as HDs.
  pose proof (cons_lookup_in _ _ _ Hgs) as Hin.
  induction gs1 as [| g gs1 IH] using List.rev_ind; intros rest Egs.
  - cbn [cargs_ctx cargs_ctx_aux List.app List.length List.firstn ctx_kinds List.map List.rev set_env_extend_kinded]. exact Hρn.
  - specialize (IH (g :: rest) ltac:(rewrite Egs, <- List.app_assoc; reflexivity)).
    set (i := List.length gs1) in *.
    assert (Hgi : List.nth_error gs i = Some g) by (rewrite Egs, <- List.app_assoc, List.nth_error_app2, Nat.sub_diag by lia; reflexivity).
    destruct (set_arguments_shape_nth _ _ Hsh _ _ Hgi) as (sg & Hsg & Hsgk).
    assert (Hi : i < List.length vals) by (rewrite Hlv; apply List.nth_error_Some; congruence).
    destruct (List.nth_error vals i) as [v |] eqn:Hv; [| apply List.nth_error_None in Hv; lia].
    assert (Hfirst : List.firstn (List.length (gs1 ++ [g])) vals = List.firstn i vals ++ [v])
      by (rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r; apply firstn_S_nth; exact Hv).
    rewrite Hfirst, cargs_ctx_snoc.
    assert (Hlk : List.length (ctx_kinds (cargs_ctx p D Mk gs1)) = List.length (List.firstn i vals))
      by (rewrite length_ctx_kinds, length_cargs_ctx, List.length_firstn; lia).
    (* the closed context of the arguments before, and its instance *)
    assert (EΨ : (cargs_ctx p D Mk gs1 ++ im_nparams Mk) ++ ind_uparams D = cargs_ctx p D Mk gs1 ++ im_params D Mk)
      by (rewrite <- List.app_assoc; reflexivity).
    assert (Egs1 : gs = gs1 ++ (g :: rest)) by (rewrite Egs, <- List.app_assoc; reflexivity).
    pose proof (cargs_ctx_closed p D k Mk _ gs gs1 (g :: rest) Hcl Hk Hin Egs1) as Hs0.
    pose proof (cargs_ctx_closed p D k Mk _ gs (gs1 ++ [g]) rest Hcl Hk Hin Egs) as Hs1.
    destruct (cargs_ctx_wf _ _ _ _ _ _ _ _ Hgw HDs HD Hk Hin gs1 (g :: rest) Egs1) as (Hw0 & _ & _).
    pose proof (cargs_prefix_ctx _ _ _ _ _ gs1 (g :: rest) Hk HSk Hcok Egs1) as Hc0.
    assert (Hass0 : all_assumptions (cargs_ctx p D Mk gs1 ++ im_params D Mk))
      by (apply List.Forall_app; split; [apply cargs_ctx_aux_ass | exact (decl_closed_params_ass _ _ _ Hcl Hk)]).
    pose proof (wf_ctx_closed_app _ _ _ _ Hass0 Hs0 Hw0 HcΓ) as HwΓ0.
    assert (HcΓ0 : set_ctx T γ ((cargs_ctx p D Mk gs1 ++ im_params D Mk) ++ Γ)).
    { pose proof (set_ctx_moved T γ Hfn Hmods _ nil Γ _ _ (set_gsub_drop T γ _ HcΓ) HΓ ltac:(rewrite List.app_nil_r; exact Hc0)
                    ltac:(rewrite List.app_nil_r; exact Hw0)) as H.
      rewrite tele_sub_closed in H by exact Hs0. exact H. }
    pose proof (set_constructor_ok_types _ _ _ _ _ _ _ _ Hcok) as Htys.
    set (ρo := set_env_extend_kinded ρn (ctx_kinds (cargs_ctx p D Mk gs1)) (List.firstn i vals)) in *.
    set (Ψ := cargs_ctx p D Mk gs1 ++ im_nparams Mk) in *.
    (* one more entry, of a type read off the closed context *)
    assert (Gen : forall κ A F, cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] = [ce_ass κ A] ->
              ctx_scoped 0 (ce_ass κ A :: cargs_ctx p D Mk gs1 ++ im_params D Mk) ->
              set_reads T γ (cargs_ctx p D Mk gs1 ++ im_params D Mk) A F ->
              set_mem v (code_carrier (F (set_env_values (Ψ ++ ind_uparams D) (inst_closed_env Γ (ind_uparams D) Fσ Ψ ρo)))) ->
              set_env_in T γ (tele_sub ((cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] ++ cargs_ctx p D Mk gs1) ++ im_nparams Mk)
                                       (sb_of_list sb_id Us) ++ Γ)
                (set_env_extend_kinded ρn (ctx_kinds (cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] ++ cargs_ctx p D Mk gs1))
                   (List.firstn i vals ++ [v]))).
    { intros κ A F E Hsc HF Hx. rewrite E. cbn [List.app]. rewrite ctx_kinds_cons, set_env_extend_kinded_snoc by exact Hlk.
      fold ρo. cbn [centry_kind].
      change (ce_ass κ A :: cargs_ctx p D Mk gs1 ++ im_nparams Mk) with (ce_ass κ A :: Ψ).
      destruct Hsc as [HsA _]. cbn [ce_scoped] in HsA.
      rewrite Nat.add_0_r, <- EΨ in HsA.
      rewrite <- EΨ in HF, Hs0, Hc0, Hw0, HwΓ0, HcΓ0.
      exact (set_env_in_inst_extend Γ (ind_uparams D) _ Fσ Hσ HΓ HcΓ Ψ κ A F ρo v Hs0 HsA Hc0 HcΓ0 Hw0 HwΓ0 HF IH Hx). }
    assert (Hlc : List.length (cargs_ctx p D Mk gs1) = List.length (List.firstn i vals))
      by (rewrite length_cargs_ctx, List.length_firstn; lia).
    (* the closed environment's values *)
    assert (Hvals : list_set_eq (set_env_values (Ψ ++ ind_uparams D) (inst_closed_env Γ (ind_uparams D) Fσ Ψ ρo))
                                (elim_uniform_values ++ set_env_values (im_nparams Mk) ρn ++ List.firstn i vals)).
    { rewrite inst_closed_env_values. apply list_set_eq_app.
      - apply inst_uniform_values. intros x. unfold Ψ, set_env_drop, ρo.
        rewrite List.length_app, <- Nat.add_assoc, Hlc, set_env_extend_kinded_ge. apply Hdrop.
      - unfold Ψ. rewrite set_env_values_app. replace (set_env_values (cargs_ctx p D Mk gs1) ρo) with (List.firstn i vals)
          by (unfold ρo; symmetry; apply set_env_values_extend_kinded_any; exact Hlc).
        apply list_set_eq_app; [| apply list_set_eq_refl].
        rewrite (set_env_values_agree (im_nparams Mk) (set_env_drop (List.length (cargs_ctx p D Mk gs1)) ρo) ρn);
          [apply list_set_eq_refl |].
        intros x _. unfold set_env_drop, ρo. rewrite Hlc, set_env_extend_kinded_ge. reflexivity. }
    assert (HL0 : List.length (elim_uniform_values ++ set_env_values (im_nparams Mk) ρn) = im_np D Mk)
      by (unfold elim_uniform_values; rewrite List.length_app, !length_set_env_values; unfold im_np, im_nn, ind_nu; lia).
    assert (Hrec : forall n ty ds tg tp, List.nth_error sgs n = Some (set_argument_recursive ty ds tg tp) ->
              exists t, List.nth_error gs n = Some (ca_rec t)).
    { intros n ty ds tg tp Hn. assert (Hn' : n < List.length gs) by (rewrite <- Hlsh; apply List.nth_error_Some; congruence).
      destruct (List.nth_error gs n) as [g' |] eqn:Hg'; [| apply List.nth_error_None in Hg'; lia].
      destruct (set_arguments_shape_nth _ _ Hsh _ _ Hg') as (sg' & Hsg' & Hk'). rewrite Hn in Hsg'. injection Hsg' as <-.
      destruct g' as [κ' A' | t']; [destruct Hk' as [F' Hk']; discriminate | eauto]. }
    assert (Hgs_eq : cargs_ctx p D Mk gs =
              cargs_ctx_aux p D (im_nn Mk) (cargs_pat (gs1 ++ [g])) rest ++ (cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] ++ cargs_ctx p D Mk gs1))
      by (rewrite Egs, cargs_ctx_app, cargs_ctx_snoc; reflexivity).
    assert (Hs1' : ctx_scoped 0 ((cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [g] ++ cargs_ctx p D Mk gs1) ++ im_params D Mk))
      by (rewrite <- cargs_ctx_snoc; exact Hs1).
    destruct g as [κ A0 | t].
    + (* a non-recursive argument: of its type at the values, which ignores the recursive ones before it *)
      destruct Hsgk as [Fp ->].
      set (A := exp_wk A0 (wk_pat (cargs_pat gs1))).
      assert (E : cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [ca_arg κ A0] = [ce_ass κ A]) by reflexivity.
      rewrite E in Hgs_eq, Hs1'. cbn [List.app] in Hgs_eq, Hs1'.
      destruct (set_tele_types_entry T γ _ _ _ Htys _ κ A _ Hgs_eq) as (F & HF & HnF).
      rewrite List.nth_error_map, length_cargs_ctx in HnF. fold i in HnF. rewrite Hsg in HnF. cbn in HnF. injection HnF as <-.
      apply (Gen κ A Fp E Hs1' HF).
      pose proof (arguments_fit_nth _ _ _ _ _ _ Hfit i _ v Hsg Hv) as Hm. cbn beta iota in Hm.
      assert (Hrp : list_function_respects Fp) by (rewrite List.Forall_forall in Hrs; exact (Hrs _ (List.nth_error_In _ _ Hsg))).
      eapply set_mem_eq_r; [| exact Hm]. apply code_carrier_resp.
      eapply set_eq_trans; [| apply Hrp; apply list_set_eq_sym; exact Hvals]. rewrite List.app_assoc. apply set_eq_sym.
      apply erase_args_ignored; [| lia | lia].
      intros n L' ty ds tg tp Hn Hsn HL'. destruct (Hrec _ _ _ _ _ Hsn) as (tn & Htn).
      rewrite HL0 in HL' |- *.
      exact (set_constructor_ok_ignores _ _ _ _ _ _ _ _ Hcok n tn i _ L' Htn Hn Hsg HL').
    + (* a recursive argument: in its set of shapes, within its code *)
      destruct Hsgk as (Fr & ds & tparams & -> & Hlds).
      set (A := ptyp_ty p D (im_nn Mk) (cargs_pat gs1) t).
      assert (E : cargs_ctx_aux p D (im_nn Mk) (cargs_pat gs1) [ca_rec t] = [ce_ass ak_relevant A]) by reflexivity.
      rewrite E in Hgs_eq, Hs1'. cbn [List.app] in Hgs_eq, Hs1'.
      destruct (set_tele_types_entry T γ _ _ _ Htys _ ak_relevant A _ Hgs_eq) as (F & HF & HnF).
      rewrite List.nth_error_map, length_cargs_ctx in HnF. fold i in HnF. rewrite Hsg in HnF. cbn in HnF. injection HnF as <-.
      apply (Gen ak_relevant A Fr E Hs1' HF).
      set (θ := inst_closed_env Γ (ind_uparams D) Fσ Ψ ρo).
      destruct (inst_closed_env_in Γ (ind_uparams D) _ Fσ Hσ HΓ HcΓ Ψ ρo ltac:(rewrite EΨ; exact Hs0) ltac:(rewrite EΨ; exact Hc0)
                  ltac:(rewrite EΨ; exact HcΓ0) ltac:(rewrite EΨ; exact Hw0) ltac:(rewrite EΨ; exact HwΓ0) IH) as [_ Hθ].
      fold θ in Hθ. rewrite EΨ in Hθ, Hvals |- *.
      pose proof (set_constructor_ok_recursive _ _ _ _ _ _ _ _ Hcok i t Fr ds (ptyp_mem t) tparams θ Hgi Hsg) as Hrc.
      rewrite Egs1 in Hrc. unfold i in Hrc. rewrite cargs_ctx_prefix in Hrc. specialize (Hrc Hθ). cbn [set_argument_type] in HF.
      fold θ in Hvals. set (Lθ := set_env_values (cargs_ctx p D Mk gs1 ++ im_params D Mk) θ) in *.
      set (L0 := elim_uniform_values ++ set_env_values (im_nparams Mk) ρn) in *.
      set (pre_e := L0 ++ erase_args (List.firstn i sgs) (List.firstn i vals)).
      assert (Hrsg : argument_respects (set_argument_recursive Fr ds (ptyp_mem t) tparams))
        by (rewrite List.Forall_forall in Hrs; exact (Hrs _ (List.nth_error_In _ _ Hsg))).
      destruct Hrsg as [Hds Htp].
      pose proof (arguments_fit_nth _ _ _ _ _ _ Hfit i _ v Hsg Hv) as Hm. cbn beta iota in Hm. fold L0 pre_e in Hm.
      assert (Hign : forall n L', n < i -> (exists ty ds' tg tp, List.nth_error sgs n = Some (set_argument_recursive ty ds' tg tp)) ->
                 List.length L' = List.length L0 + i ->
                 argument_ignores (List.length L0 + n) (set_argument_recursive Fr ds (ptyp_mem t) tparams) L').
      { intros n L' Hn (ty & ds' & tg & tp & Hsn) HL'. destruct (Hrec _ _ _ _ _ Hsn) as (tn & Htn). rewrite HL0 in HL' |- *.
        exact (set_constructor_ok_ignores _ _ _ _ _ _ _ _ Hcok n tn i _ L' Htn Hn Hsg HL'). }
      assert (Hiv : i <= List.length sgs) by lia. assert (Hiv' : i <= List.length vals) by lia.
      assert (HLθ : list_set_eq Lθ (L0 ++ List.firstn i vals)) by (unfold L0; rewrite <- List.app_assoc; exact Hvals).
      assert (Hnu : List.length elim_uniform_values = ind_nu D)
        by (unfold elim_uniform_values; rewrite length_set_env_values; reflexivity).
      assert (Hdom : forall k' d pts0, List.nth_error ds k' = Some d -> List.length pts0 = k' ->
                set_eq (d (pre_e ++ pts0)) (d (Lθ ++ pts0))).
      { intros k' d pts0 Hk' Hl'.
        assert (Hd : list_function_respects d) by (rewrite List.Forall_forall in Hds; exact (Hds _ (List.nth_error_In _ _ Hk'))).
        eapply set_eq_trans; [| apply Hd; apply list_set_eq_app; [apply list_set_eq_sym; exact HLθ | apply list_set_eq_refl]].
        apply set_eq_sym. unfold pre_e.
        apply (erase_args_ignored (fun L => d (L ++ pts0)) L0 sgs vals i); [| exact Hiv | exact Hiv'].
        intros n L' ty ds' tg tp Hn Hsn HL'. exact (proj1 (Hign n L' Hn ltac:(eauto) HL') k' d pts0 Hk' Hl'). }
      assert (Htps : forall pts, List.length pts = List.length ds -> list_set_eq (tparams (pre_e ++ pts)) (tparams (Lθ ++ pts))).
      { intros pts Hl'.
        eapply list_set_eq_trans; [| apply Htp; apply list_set_eq_app; [apply list_set_eq_sym; exact HLθ | apply list_set_eq_refl]].
        apply list_set_eq_sym. unfold pre_e.
        apply (erase_args_ignored_list (fun L => tparams (L ++ pts)) L0 sgs vals i); [| exact Hiv | exact Hiv'].
        intros n L' ty ds' tg tp Hn Hsn HL'. exact (proj2 (Hign n L' Hn ltac:(eauto) HL') pts Hl'). }
      assert (Hus : list_set_eq (List.firstn (ind_nu D) Lθ) elim_uniform_values).
      { eapply list_set_eq_trans; [apply list_set_eq_firstn; exact HLθ |]. unfold L0.
        rewrite <- List.app_assoc, List.firstn_app, Hnu, Nat.sub_diag, List.firstn_all2 by lia.
        cbn [List.firstn]. rewrite List.app_nil_r. apply list_set_eq_refl. }
      assert (Hpre : list_set_eq (List.firstn (ind_nu D) pre_e) elim_uniform_values).
      { unfold pre_e, L0. rewrite <- List.app_assoc, List.firstn_app, Hnu, Nat.sub_diag, List.firstn_all2 by lia.
        cbn [List.firstn]. rewrite List.app_nil_r. apply list_set_eq_refl. }
      pose proof (set_group_ok_carrier_resp _ _ _ _ _ HG) as HGresp.
      pose proof (shape_set_sub_code G HGresp U S pre_e (ptyp_mem t) tparams ds nil Hds Htp
                    (fun pts Hpts => recursive_leaf_sub k Mk gs sgs gs1 t rest Fr ds (ptyp_mem t) tparams θ (Fr Lθ) pre_e Hk Hcok Egs1 Hsg
                                       Hds Htp Hlds Hθ (HF θ Hθ) Hrc Hus Hpre Hdom Htps pts Hpts) v Hm) as Hv1.
      eapply set_mem_eq_r; [| exact Hv1]. apply code_carrier_resp.
      eapply set_eq_trans; [| apply set_eq_sym; exact Hrc].
      eapply set_eq_trans;
        [| apply shape_code_resp; [exact HGresp | exact Hds | exact Htp | apply list_set_eq_sym; exact HLθ | apply list_set_eq_refl]].
      apply set_eq_sym. unfold pre_e.
      apply (erase_args_ignored (fun L => shape_code G ds (ptyp_mem t) tparams L nil) L0 sgs vals i); [| exact Hiv | exact Hiv'].
      intros n L' ty ds' tg tp Hn Hsn HL'. destruct (Hign n L' Hn ltac:(eauto) HL') as [H1 H2].
      apply (shape_code_erase G HGresp); [exact Hds | exact Htp | unfold G; rewrite group_uniform_count, HL0; unfold im_np; lia | lia
                                         | exact H1 | exact H2].
Qed.

End Arguments.

(** ** The Eliminator's Results at One Environment *)

Section Results.
  (** The eliminator's context and environment *)
  Variables (Γ : ctx) (ρ : set_env).
  (** Its sort, group, uniform parameters and blocks *)
  Variables (r : abs_kind) (p : qname) (Us : list exp) (Bks : list eblock).
  (** A set holding every result *)
  Variable V : aczel_set.
  (** The environment is one of the context *)
  Hypothesis Hρ : set_env_in T γ Γ ρ.

Lemma set_elim_functional : forall j v res res', set_elim T γ Γ ρ r p Us Bks j v res -> set_elim T γ Γ ρ r p Us Bks j v res' ->
    set_eq res res'.
Proof.
  intros * H H'. destruct (set_interp_functional_all T γ Hfn Hmods) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hel & _).
  exact (Hel _ _ _ _ _ _ _ _ _ H _ _ _ (set_env_rel_eq T γ _ _ _ Hρ) (set_eq_refl _) H').
Qed.

Lemma set_ih_functional : forall t v ihs ihs', set_ih T γ Γ ρ r p Us Bks t v ihs -> set_ih T γ Γ ρ r p Us Bks t v ihs' ->
    list_set_eq ihs ihs'.
Proof.
  intros * H H'. destruct (set_interp_functional_all T γ Hfn Hmods) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hih).
  exact (Hih _ _ _ _ _ _ _ _ _ H _ _ _ (set_env_rel_eq T γ _ _ _ Hρ) (set_eq_refl _) H').
Qed.

(** A result is one at a value equal to the element. *)
Lemma set_elim_resp_value : forall j v v' res, set_eq v v' -> set_elim T γ Γ ρ r p Us Bks j v res ->
    set_elim T γ Γ ρ r p Us Bks j v' res.
Proof.
  intros * E H. destruct (set_elim_strip T γ _ _ _ _ _ _ _ _ _ H) as (res0 & E0 & H0).
  apply (set_elim_resp T γ _ _ _ _ _ _ _ _ res0); [| apply set_eq_sym; exact E0].
  destruct H0. eapply set_elim_con; try eassumption. eapply set_eq_trans; [apply set_eq_sym; exact E | eassumption].
Qed.

Lemma elim_result_pred_resp : forall j v, respects_set_eq (fun z => exists res, set_elim T γ Γ ρ r p Us Bks j v res /\ set_eq res z).
Proof. intros j v x y E (res & H & Ex). exists res. split; [exact H | eapply set_eq_trans; eassumption]. Qed.

(** The eliminator's result at the member [j] and the element [v]. *)
Definition elim_result (j : nat) (v : aczel_set) : aczel_set :=
  set_describe V (fun z => exists res, set_elim T γ Γ ρ r p Us Bks j v res /\ set_eq res z).

(** A result in [V] is the described one. *)
Lemma elim_result_eq : forall j v res, set_elim T γ Γ ρ r p Us Bks j v res -> set_mem res V ->
    set_eq (elim_result j v) res.
Proof.
  intros * H HV. apply set_describe_eq; [apply elim_result_pred_resp | exact HV | exists res; split; [exact H | apply set_eq_refl] |].
  intros w _ (res' & H' & E'). eapply set_eq_trans; [apply set_eq_sym; exact E' |]. exact (set_elim_functional _ _ _ _ H' H).
Qed.

(** The described result is a result. *)
Lemma elim_result_spec : forall j v res, set_elim T γ Γ ρ r p Us Bks j v res -> set_mem res V ->
    set_elim T γ Γ ρ r p Us Bks j v (elim_result j v).
Proof. intros * H HV. apply (set_elim_resp T γ _ _ _ _ _ _ _ _ res); [exact H | apply set_eq_sym; exact (elim_result_eq _ _ _ H HV)]. Qed.

(** The recursive result of an element [v] along a leaf path. *)
Fixpoint leaf_result (l : leaf_path) (v : aczel_set) : aczel_set :=
  match l with
  | leaf_self j _ => elim_result j v
  | leaf_pi _ l' => graph_set (relation_domain v) (fun b => leaf_result l' (set_apply v b))
  | leaf_proj f _ l' => leaf_result l' (tuple_field v f)
  end.

Lemma elim_result_resp : forall j v v', set_eq v v' -> set_eq (elim_result j v) (elim_result j v').
Proof.
  intros j v v' E. unfold elim_result, set_describe. apply union_set_resp.
  apply separation_set_resp; [apply elim_result_pred_resp | apply elim_result_pred_resp | apply set_eq_refl |].
  intros z; split; intros (res0 & Hr & Ez); exists res0; (split; [| exact Ez]); eapply set_elim_resp_value; try exact Hr;
    [exact E | apply set_eq_sym; exact E].
Qed.

Lemma leaf_result_resp : forall l v v', set_eq v v' -> set_eq (leaf_result l v) (leaf_result l v').
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros v v' E; cbn [leaf_result].
  - apply elim_result_resp; exact E.
  - apply graph_set_resp; [intros b b' Eb; apply IH; apply set_apply_resp; [apply set_eq_refl | exact Eb]
                          | intros b b' Eb; apply IH; apply set_apply_resp; [apply set_eq_refl | exact Eb]
                          | apply relation_domain_resp; exact E |].
    intros b _. apply IH. apply set_apply_resp; [exact E | apply set_eq_refl].
  - apply IH. apply tuple_field_resp. exact E.
Qed.

(** A list of values indexed by positions, pointwise equal to a map. *)
Lemma map_seq_set_eq : forall {X : Type} (L : list X) (f : nat -> aczel_set) (g : X -> aczel_set) k,
    (forall i x, List.nth_error L i = Some x -> set_eq (f (k + i)) (g x)) ->
    list_set_eq (List.map f (List.seq k (List.length L))) (List.map g L).
Proof.
  intros X L f g. induction L as [| x L IH]; intros k H; cbn [List.length List.seq List.map]; constructor.
  - specialize (H 0 x eq_refl). rewrite Nat.add_0_r in H. exact H.
  - apply IH. intros i y Hy. replace (S k + i) with (k + S i) by lia. exact (H (S i) y Hy).
Qed.

Lemma map_set_eq : forall {X : Type} (L : list X) (f g : X -> aczel_set), (forall x, In x L -> set_eq (f x) (g x)) ->
    list_set_eq (List.map f L) (List.map g L).
Proof. intros X L f g H. induction L as [| x L IH]; cbn; constructor; [apply H; left; reflexivity | apply IH; intros; apply H; right; assumption]. Qed.

(** A moved path has the same results. *)
Lemma leaf_result_wk : forall l φ v, set_eq (leaf_result (leaf_wk φ l) v) (leaf_result l v).
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros φ v; cbn [leaf_wk leaf_result].
  - apply set_eq_refl.
  - apply graph_set_resp; [intros b b' Eb; apply leaf_result_resp; apply set_apply_resp; [apply set_eq_refl | exact Eb]
                          | intros b b' Eb; apply leaf_result_resp; apply set_apply_resp; [apply set_eq_refl | exact Eb]
                          | apply set_eq_refl |].
    intros b _. apply IH.
  - apply IH.
Qed.

(** ** The Recursive Results Along a Shape *)

Section Shapes.
  (** The group *)
  Variable D : ind_decl.
  Hypothesis HD : ind_lookup gc_deps gc_stack p = Some D.
  (** Its record views' paths are read off their fields *)
  Hypothesis Hco : leaves_coherent D.
  (** It is typed *)
  Hypothesis HDt : decl_typed gc_deps gc_stack D.

(** [end_results j w]: at the end of a shape, the element [w] of the member
    [j] has a result, at a member with a block, and its fields have the
    recursive results along the record view's paths, at a record view. *)
Record end_results (j : nat) (w : aczel_set) (Mj : imember) : Prop :=
  { (** [Mj] is the member *)
    end_results_member : ind_member D j = Some Mj
    (** A member with a block: a result in [V] *)
  ; end_results_block : im_is_rview Mj = false -> exists res, set_elim T γ Γ ρ r p Us Bks j w res /\ set_mem res V
    (** A record view: its fields' results along its paths *)
  ; end_results_rview : forall qr Is fl c gs, im_head Mj = mh_record qr Is fl -> im_cons Mj = [(c, gs)] ->
      set_ihs T γ Γ ρ r p Us Bks gs (List.map (tuple_field w) fl)
        (List.map (fun l => leaf_result l w) (fields_leaves (rview_leaves D) nil (List.combine fl gs))) }.

(** [shape_results t a]: every value of [a] at the domains of [t] has its
    results at the shape's end. *)
Fixpoint shape_results (t : ptyp) (a : aczel_set) : Prop :=
  match t with
  | pt_self j _ => exists Mj, end_results j a Mj
  | pt_pi _ t' => forall b, set_mem b (relation_domain a) -> shape_results t' (set_apply a b)
  end.

(** An argument whose values have their results has its recursive results
    along the shape's paths. *)
Lemma set_ih_of_shape_results : forall t m a, shape_results t a ->
    set_ih T γ Γ ρ r p Us Bks t a (List.map (fun l => leaf_result l a) (shape_leaves (rview_leaves D) m t)).
Proof.
  induction t as [j Ps | B t IH]; intros m a Ha; cbn [shape_results shape_leaves] in *.
  - destruct Ha as (Mj & [HMj Hblk Hrv]).
    destruct (im_is_rview Mj) eqn:Hr.
    + destruct (im_head Mj) as [pm | qc k' Is0 vm | qr Is fl] eqn:Hh; unfold im_is_rview in Hr; rewrite Hh in Hr; try discriminate.
      destruct (rview_struct_con _ _ _ (decl_typed_record_struct _ _ _ HDt) _ _ _ _ _ HMj Hh) as (gs & Hcs & _).
      pose proof (Hco _ _ _ _ _ _ _ HMj Hh Hcs) as E. rewrite E.
      eapply (set_ih_resp T γ); [eapply set_ih_rview; [exact HD | exact HMj | exact Hh | exact Hcs | exact (Hrv _ _ _ _ _ eq_refl Hcs)] |].
      rewrite List.map_map. apply map_set_eq. intros l _. apply set_eq_sym. apply leaf_result_wk.
    + rewrite (rview_leaves_not_rview _ _ _ HMj Hr). cbn [List.map].
      destruct (Hblk eq_refl) as (res & Hres & HV).
      eapply set_ih_self; [exact HD | exact HMj | exact Hr |]. exact (elim_result_spec _ _ _ Hres HV).
  - rewrite List.map_map.
    set (Ls := shape_leaves (rview_leaves D) (S m) t).
    eapply (set_ih_resp T γ);
      [eapply (set_ih_pi T γ _ _ _ _ _ _ D B t a (fun b => List.map (fun l => leaf_result l (set_apply a b)) Ls));
         [exact HD |]; intros b Hb; exact (IH (S m) (set_apply a b) (Ha b Hb)) |].
    rewrite (length_shape_leaves (rview_leaves D) t 0 (S m)). fold Ls.
    apply map_seq_set_eq. intros i l Hi. cbn [leaf_result Nat.add].
    apply graph_set_resp; [| | apply set_eq_refl |].
    + intros b b' Eb. apply list_set_eq_nth. apply map_set_eq. intros l0 _. apply leaf_result_resp.
      apply set_apply_resp; [apply set_eq_refl | exact Eb].
    + intros b b' Eb. apply leaf_result_resp. apply set_apply_resp; [apply set_eq_refl | exact Eb].
    + intros b _.
      assert (Hn : List.nth i (List.map (fun l0 => leaf_result l0 (set_apply a b)) Ls) empty_set = leaf_result l (set_apply a b))
        by (apply List.nth_error_nth; rewrite List.nth_error_map, Hi; reflexivity).
      rewrite Hn. apply set_eq_refl.
Qed.

End Shapes.

(** ** The Recursive Results' Types Along Leaf Paths *)

(** A substitution of terms over [β] agrees with the environment extended
    by their values. *)
Lemma sub_agrees_of_list : forall Ψ ρe L vals, set_interp_list T γ Ψ ρe L vals ->
    forall β ρ0 κs, (forall y, sub_entry_agrees T γ Ψ ρe (β y) (ρ0 y)) ->
    forall y, sub_entry_agrees T γ Ψ ρe (sb_of_list β L y) (set_env_extend_kinded ρ0 κs vals y).
Proof.
  intros Ψ ρe L vals H. induction H as [Ξ ρ1 | Ξ ρ1 M Ms v vs HM HMs IH]; intros β ρ0 κs Hβ y; [exact (Hβ y) |].
  cbn [sb_of_list set_env_extend_kinded]. apply IH. intros [| z]; cbn [sb_extend set_env_extend].
  - split; cbn; [exact HM | constructor].
  - exact (Hβ z).
Qed.

(** An entry's agreement survives one more binder, the entry weakened. *)
Lemma sub_agrees_shift : forall Ψ ρe e d s v, ⊢ gc_deps ⍮ gc_stack ⍮ e :: Ψ -> sub_entry_agrees T γ Ψ ρe s v ->
    sub_entry_agrees T γ (e :: Ψ) (set_env_extend ρe d) (sentry_sub s (sb_of_wk wk_shift)) v.
Proof.
  intros * Hc [He Hm]. rewrite sentry_sub_of_wk. unfold sub_entry_agrees. rewrite <- sentry_exp_wk, sentry_modexp_wk.
  assert (Hw : gc_deps ⍮ gc_stack ⍮ e :: Ψ ⊢ʷ wk_shift : Ψ) by (apply wf_wk_shift; exact Hc).
  assert (Hag : env_agrees ρe (set_env_extend ρe d) (wk_qn (List.length (@nil centry)) wk_shift)) by (intros y; reflexivity).
  split.
  - exact (proj1 (set_interp_wk_all T γ) _ _ _ _ He nil Ψ _ _ _ (Build_wk_setting _ _ _ _ _ _ _ eq_refl Hw Hag)).
  - exact (proj1 (proj2 (proj2 (proj2 (set_interp_wk_all T γ)))) _ _ _ _ Hm nil Ψ _ _ _ (Build_wk_setting _ _ _ _ _ _ _ eq_refl Hw Hag)).
Qed.

(** A term read at an environment a substitution realizes keeps its value
    substituted. *)
Lemma interp_realized : forall Tc θ Ψ ρe σ M v, ⊢ gc_deps ⍮ gc_stack ⍮ Tc -> gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ σ : Tc ->
    (forall y, sub_entry_agrees T γ Ψ ρe (σ y) (θ y)) -> set_interp T γ Tc θ M v -> set_interp T γ Ψ ρe (exp_sub M σ) v.
Proof.
  intros * Hc Hσ Hag HM.
  assert (Hs : sub_setting T γ Tc θ nil Tc Ψ σ ρe ρe)
    by (constructor; [reflexivity | exact Hσ | intros y Hy; cbn in Hy; lia | intros y; reflexivity | exact Hag]).
  pose proof (set_interp_sub T γ _ _ _ _ HM Hc _ _ _ _ _ _ Hs) as H. cbn [tele_sub List.app List.length] in H. exact H.
Qed.

Lemma interp_list_realized : forall Tc θ Ψ ρe σ Ms vs, ⊢ gc_deps ⍮ gc_stack ⍮ Tc -> gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ σ : Tc ->
    (forall y, sub_entry_agrees T γ Ψ ρe (σ y) (θ y)) -> set_interp_list T γ Tc θ Ms vs ->
    set_interp_list T γ Ψ ρe (List.map (fun M => exp_sub M σ) Ms) vs.
Proof.
  intros * Hc Hσ Hag HM.
  assert (Hs : sub_setting T γ Tc θ nil Tc Ψ σ ρe ρe)
    by (constructor; [reflexivity | exact Hσ | intros y Hy; cbn in Hy; lia | intros y; reflexivity | exact Hag]).
  pose proof (proj1 (proj2 (set_interp_sub_all T γ)) _ _ _ _ HM _ _ _ _ _ _ Hc Hs) as H.
  cbn [tele_sub List.app List.length] in H. exact H.
Qed.

(** A substitution lifted past one more binder realizes the environment
    extended by the binder's entry. *)
Lemma sub_agrees_q : forall Ψ ρe e d σ θ, ⊢ gc_deps ⍮ gc_stack ⍮ e :: Ψ ->
    (forall y, sub_entry_agrees T γ Ψ ρe (σ y) (θ y)) ->
    forall y, sub_entry_agrees T γ (e :: Ψ) (set_env_extend ρe d) (sb_q σ y) (set_env_extend θ d y).
Proof.
  intros * Hc Hσ [| y].
  - split; cbn; [exact (set_interp_var T γ _ _ 0) | exact (set_interp_me_var T γ _ _ 0)].
  - unfold sb_q. cbn [sb_extend set_env_extend]. unfold sb_wk. rewrite <- sentry_sub_of_wk.
    exact (sub_agrees_shift _ _ _ _ _ _ Hc (Hσ y)).
Qed.

Section LeafFits.
  (** The group, and the level of the motives *)
  Variables (D : ind_decl) (i : nat).
  (** The motives' contexts are well formed *)
  Hypothesis HMwf : forall j Mj, ind_member D j = Some Mj -> ⊢ gc_deps ⍮ gc_stack ⍮ elim_mctx p D j Mj Us ++ Γ.
  (** The blocks' motives denote *)
  Hypothesis HMot : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
    exists FS FM FM', set_exp_eq_with T γ (elim_mctx p D j Mj Us ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b) FS FM FM'.

(** The recursive result at the end of a path: the eliminator's result,
    or the empty set, a proof, into propositions. *)
Definition end_value (j : nat) (w : aczel_set) : aczel_set :=
  match r with ak_propositional => empty_set | _ => elim_result j w end.

(** The recursive result of [v] along the path [l]: the empty set, a
    proof, into propositions, otherwise [leaf_result]. *)
Definition leaf_value (l : leaf_path) (v : aczel_set) : aczel_set :=
  match r with ak_propositional => empty_set | _ => leaf_result l v end.

(** [end_fact j Mj ns w]: the element [w] of the member [j] at the
    non-uniform parameters [ns] is an environment of the motive's context
    with [ρ], and the result there is of every reading of the motive. *)
Definition end_fact (j : nat) (Mj : imember) (ns : list aczel_set) (w : aczel_set) : Prop :=
  forall b FS FM FM', List.nth_error Bks j = Some b ->
    set_exp_eq_with T γ (elim_mctx p D j Mj Us ++ Γ) (abs_kind_sort r (a_typ i)) (eb_motive b) (eb_motive b) FS FM FM' ->
    set_env_in T γ (elim_mctx p D j Mj Us ++ Γ) (set_env_extend_kinded ρ (ctx_kinds (elim_mctx p D j Mj Us)) (ns ++ [w])) /\
    set_mem (end_value j w) (code_carrier (FM (set_env_extend_kinded ρ (ctx_kinds (elim_mctx p D j Mj Us)) (ns ++ [w])))).

(** [leaf_fits Ψ ρe β σ x xv l]: the recursive result of [xv] along [l] is
    of every reading of its type. *)
Definition leaf_fits (Ψ : ctx) (ρe : set_env) (β σ : sub) (x : exp) (xv : aczel_set) (l : leaf_path) : Prop :=
  forall A, set_interp T γ Ψ ρe (leaf_ihty r (blocks_motives Bks) β σ x l) A -> set_mem (leaf_value l xv) (code_carrier A).

(** [leaf_self_with Ψ ρe β σ x xv j Ps Mj b ns]: at the end of a path, at
    the member [j], [Mj], of the block [b], the parameters [Ps] moved by
    [σ] have the values [ns], and the end's facts hold there. *)
Record leaf_self_with (Ψ : ctx) (ρe : set_env) (β σ : sub) (x : exp) (xv : aczel_set) (j : nat) (Ps : list exp)
    (Mj : imember) (b : eblock) (ns : list aczel_set) : Prop :=
  { (** [Mj] is the member [j] *)
    leaf_self_member : ind_member D j = Some Mj
    (** [b] is its block *)
  ; leaf_self_block : List.nth_error Bks j = Some b
    (** The parameters' values *)
  ; leaf_self_params : set_interp_list T γ Ψ ρe (List.map (fun P => exp_sub P σ) Ps) ns
    (** The instance of the motive's context is a substitution *)
  ; leaf_self_typed : gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ sb_of_list β (List.map (fun P => exp_sub P σ) Ps ++ x :: nil)
      : elim_mctx p D j Mj Us ++ Γ
    (** The end's facts *)
  ; leaf_self_fact : end_fact j Mj ns xv }.

(** [leaf_pi_with Ψ ρe σ B xv a rest]: under a domain [B] moved by [σ], of
    the value [a], [xv] is a function on [a]'s elements, and [rest] holds
    at each. *)
Record leaf_pi_with (Ψ : ctx) (ρe : set_env) (σ : sub) (B : exp) (xv a : aczel_set) (rest : aczel_set -> Prop) : Prop :=
  { (** [a] is the domain's value *)
    leaf_pi_interp : set_interp T γ Ψ ρe (exp_sub B σ) a
    (** [xv]'s domain is its carrier *)
  ; leaf_pi_domain_eq : set_eq (relation_domain xv) (code_carrier a)
    (** The rest of the path, at each point *)
  ; leaf_pi_rest : forall b, set_mem b (code_carrier a) -> rest b }.

(** [leaf_sem Ψ ρe β σ x xv l]: the result fits along [l], or, along the
    path [l], the value [xv] of [x]
    has its domains' values and its end's facts, its components moved by
    [σ] and the motives' context by [β], read in [Ψ] at [ρe]. *)
Fixpoint leaf_sem (Ψ : ctx) (ρe : set_env) (β σ : sub) (x : exp) (xv : aczel_set) (l : leaf_path) {struct l} : Prop :=
  leaf_fits Ψ ρe β σ x xv l \/
  match l with
  | leaf_self j Ps => exists Mj b ns, leaf_self_with Ψ ρe β σ x xv j Ps Mj b ns
  | leaf_pi B l' =>
      exists a, leaf_pi_with Ψ ρe σ B xv a (fun b =>
        leaf_sem (ce_ass ak_relevant (exp_sub B σ) :: Ψ) (set_env_extend ρe (set_entry_term ak_relevant b)) (sb_compose β (sb_of_wk wk_shift))
          (sb_q σ) (a_app (exp_wk x wk_shift) (a_var 0)) (set_apply xv b) l')
  | leaf_proj f ns l' => leaf_sem Ψ ρe β (sb_of_list σ (projections_of ns x)) (a_proj f x) (tuple_field xv f) l'
  end.

Lemma leaf_sem_of_fits : forall Ψ ρe β σ x xv l, leaf_fits Ψ ρe β σ x xv l -> leaf_sem Ψ ρe β σ x xv l.
Proof. intros * H. destruct l; cbn [leaf_sem]; left; exact H. Qed.

(** The recursive result along a path is of the type the branch's context
    gives it there. *)
Lemma leaf_fit : forall l Ψ ρe β σ x xv A, ⊢ gc_deps ⍮ gc_stack ⍮ Ψ -> set_env_in T γ Ψ ρe ->
    (forall y, sub_entry_agrees T γ Ψ ρe (β y) (ρ y)) -> set_interp T γ Ψ ρe x xv -> leaf_sem Ψ ρe β σ x xv l ->
    set_interp T γ Ψ ρe (leaf_ihty r (blocks_motives Bks) β σ x l) A -> set_mem (leaf_value l xv) (code_carrier A).
Proof.
  induction l as [j Ps | B l IH | f ns l IH]; intros Ψ ρe β σ x xv A HcΨ Hρe Hβ Hx Hl HA;
    (destruct Hl as [Hfit | Hl]; [exact (Hfit A HA) |]); cbn [leaf_sem leaf_ihty] in Hl, HA.
  - (* the end: the motive at the moved environment *)
    destruct Hl as (Mj & b & ns & [HMj Hb Hns Hτ Hfact]).
    rewrite (blocks_motives_nth _ _ _ Hb) in HA.
    destruct (HMot j Mj b HMj Hb) as (FS & FM & FM' & Hw).
    destruct (Hfact b FS FM FM' Hb Hw) as [Henv Hmem].
    destruct Hw as [_ HL _ _ _].
    pose proof (set_denotes_exists _ _ _ _ _ HL _ Henv) as HM0.
    assert (Hset : sub_setting T γ (elim_mctx p D j Mj Us ++ Γ)
                     (set_env_extend_kinded ρ (ctx_kinds (elim_mctx p D j Mj Us)) (ns ++ [xv])) nil (elim_mctx p D j Mj Us ++ Γ) Ψ
                     (sb_of_list β (List.map (fun P => exp_sub P σ) Ps ++ x :: nil)) ρe ρe).
    { constructor; [reflexivity | exact Hτ | intros y Hy; cbn in Hy; lia | intros y; reflexivity |].
      intros y. cbn [List.length Nat.add]. apply (sub_agrees_of_list _ _ _ _ (set_interp_list_app T γ _ _ _ _ _ _ Hns
                    (set_interp_list_cons T γ _ _ _ _ _ _ Hx (set_interp_list_nil T γ _ _))) β ρ _ Hβ). }
    pose proof (set_interp_sub T γ _ _ _ _ HM0 (HMwf _ _ HMj) _ _ _ _ _ _ Hset) as H1.
    cbn [tele_sub List.app List.length] in H1. change (sb_qn 0 ?s) with s in H1.
    pose proof (set_interp_functional T γ Hfn Hmods _ _ _ _ HA ρe _ (set_env_rel_eq T γ _ _ _ Hρe) H1) as E.
    eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact E |]. exact Hmem.
  - (* a domain: a function of the results there, or their truth *)
    destruct Hl as (a & [Ha Edom Hrest]).
    set (B' := exp_sub B σ) in *.
    assert (Hpi : exists a1 F, ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass ak_relevant B' :: Ψ /\ set_interp T γ Ψ ρe B' a1 /\
                    (forall b, set_mem b (code_carrier a1) ->
                       set_interp T γ (ce_ass ak_relevant B' :: Ψ) (set_env_extend ρe (set_entry_term ak_relevant b))
                         (leaf_ihty r (blocks_motives Bks) (sb_compose β (sb_of_wk wk_shift)) (sb_q σ) (a_app (exp_wk x wk_shift) (a_var 0)) l)
                         (F b)) /\
                    ((r = ak_propositional /\ A = forall_code a1 F) \/ (r <> ak_propositional /\ A = pi_code a1 F)))
      by (inversion HA; subst; do 2 eexists; repeat split; eauto).
    destruct Hpi as (a1 & F & Hc' & Ha1 & HF & Hk).
    pose proof (set_interp_functional T γ Hfn Hmods _ _ _ _ Ha1 ρe _ (set_env_rel_eq T γ _ _ _ Hρe) Ha) as Ea.
    assert (Hb1 : forall b, set_mem b (code_carrier a1) -> set_mem b (code_carrier a))
      by (intros b Hb; eapply set_mem_eq_r; [apply code_carrier_resp; exact Ea | exact Hb]).
    assert (Hin : forall b, set_mem b (code_carrier a1) -> set_mem (leaf_value l (set_apply xv b)) (code_carrier (F b))).
    { intros b Hb. apply (IH (ce_ass ak_relevant B' :: Ψ) (set_env_extend ρe (set_entry_term ak_relevant b))
                              (sb_compose β (sb_of_wk wk_shift)) (sb_q σ) (a_app (exp_wk x wk_shift) (a_var 0)) (set_apply xv b) (F b) Hc').
      - split; [exact Hρe |]. cbn [set_entry_rel]. exists b, b, a1. constructor; [reflexivity | reflexivity | exact Ha1 | exact Hb | apply set_eq_refl].
      - intros y. unfold sb_compose. exact (sub_agrees_shift _ _ _ _ _ _ Hc' (Hβ y)).
      - apply set_interp_app; [| exact (set_interp_var T γ _ _ 0)].
        assert (Hw : gc_deps ⍮ gc_stack ⍮ ce_ass ak_relevant B' :: Ψ ⊢ʷ wk_shift : Ψ) by (apply wf_wk_shift; exact Hc').
        exact (proj1 (set_interp_wk_all T γ) _ _ _ _ Hx nil Ψ _ _ _
                 (Build_wk_setting Ψ ρe nil Ψ _ wk_shift (set_env_extend ρe (set_entry_term ak_relevant b)) eq_refl Hw (fun y => eq_refl))).
      - exact (Hrest b (Hb1 b Hb)).
      - exact (HF b Hb). }
    destruct Hk as [[Hr ->] | [Hr ->]].
    + unfold leaf_value in Hin |- *. rewrite Hr in Hin |- *. unfold forall_code.
      eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |]. apply set_mem_truth. split; [| apply set_eq_refl].
      intros b Hb. exact (Hin b Hb).
    + assert (Hlv : forall v, leaf_value (leaf_pi B l) v = graph_set (relation_domain v) (fun b => leaf_result l (set_apply v b)))
        by (intros v; unfold leaf_value; destruct r; [reflexivity | contradiction | reflexivity]).
      assert (Hlv' : forall v, leaf_value l v = leaf_result l v)
        by (intros v; unfold leaf_value; destruct r; [reflexivity | contradiction | reflexivity]).
      rewrite Hlv. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
      assert (HFr : respects_on (code_carrier a1) F)
        by exact (set_interp_family_respects T γ Hfn Hmods _ _ _ _ _ _ _ (set_env_rel_eq T γ _ _ _ Hρe) HF).
      assert (Hres : respects_set_eq_fun (fun b => leaf_result l (set_apply xv b)))
        by (intros b b' Eb; apply leaf_result_resp; apply set_apply_resp; [apply set_eq_refl | exact Eb]).
      eapply set_mem_eq_l; [apply graph_set_resp_on; [apply set_eq_sym; eapply set_eq_trans; [exact Edom | apply code_carrier_resp; apply set_eq_sym; exact Ea] |] |].
      * intros b b' _ Eb. apply Hres. exact Eb.
      * apply graph_set_function_on.
        -- intros b b' Hb Eb. apply code_carrier_resp. exact (HFr b b' Hb Eb).
        -- intros b b' _ Eb. apply Hres. exact Eb.
        -- intros b Hb. rewrite <- Hlv'. exact (Hin b Hb).
  - exact (IH Ψ ρe β _ (a_proj f x) (tuple_field xv f) A HcΨ Hρe Hβ (set_interp_proj T γ _ _ _ _ _ Hx) Hl HA).
Qed.

(** ** Along a Shape *)

Section Walk.
  (** The group is typed and closed, at its uniform parameters *)
  Hypotheses (HDt : decl_typed gc_deps gc_stack D) (Hcl : decl_closed D) (HUl : List.length Us = ind_nu D).
  Hypothesis HMh : forall j Mj, ind_member D j = Some Mj -> elim_mctx_head_large gc_deps gc_stack Γ p D j Mj Us.
  (** A member that is no record view has a block *)
  Hypothesis HBk : forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false -> exists b, List.nth_error Bks j = Some b.
  (** What the end of a shape at a record view gives *)
  Variable RV : nat -> list aczel_set -> aczel_set -> Prop.

(** [shape_end_with Mk Bs1 Tb j Ps θ xv Mj ns]: at the end of a shape, at
    the member [j], [Mj], its parameters [Ps] have the values [ns] at [θ],
    and [xv] has the end's facts there. *)
Record shape_end_with (Mk : imember) (Bs1 : list exp) (Tb : ctx) (j : nat) (Ps : list exp) (θ : set_env) (xv : aczel_set)
    (Mj : imember) (ns : list aczel_set) : Prop :=
  { (** [Mj] is the member [j] *)
    shape_end_member : ind_member D j = Some Mj
    (** The parameters' values *)
  ; shape_end_params : set_interp_list T γ (doms_ctx Bs1 ++ Tb ++ im_params D Mk) θ Ps ns
    (** At a member with a block, the end's facts *)
  ; shape_end_block : im_is_rview Mj = false -> end_fact j Mj ns xv
    (** At a record view, what it gives *)
  ; shape_end_rview : im_is_rview Mj = true -> RV j ns xv }.

(** [shape_pi_with Mk Bs1 Tb B θ xv a rest]: the shape's next domain [B]
    has the value [a] at [θ], [xv] is a function on its elements, and
    [rest] holds at each. *)
Record shape_pi_with (Mk : imember) (Bs1 : list exp) (Tb : ctx) (B : exp) (θ : set_env) (xv a : aczel_set)
    (rest : aczel_set -> Prop) : Prop :=
  { (** [a] is the domain's value *)
    shape_pi_interp : set_interp T γ (doms_ctx Bs1 ++ Tb ++ im_params D Mk) θ B a
    (** [xv]'s domain is its carrier *)
  ; shape_pi_domain_eq : set_eq (relation_domain xv) (code_carrier a)
    (** The rest of the shape, at each point *)
  ; shape_pi_rest : forall b, set_mem b (code_carrier a) -> rest b }.

(** [shape_closed_ok Mk Bs1 Tb t θ xv]: at the environment [θ] of the
    shape's components, [xv] is a function on each domain's value, and at
    the end its parameters' values give the end's facts. *)
Fixpoint shape_closed_ok (Mk : imember) (Bs1 : list exp) (Tb : ctx) (t : ptyp) (θ : set_env) (xv : aczel_set) {struct t} : Prop :=
  match t with
  | pt_pi B t' =>
      exists a, shape_pi_with Mk Bs1 Tb B θ xv a (fun b =>
        shape_closed_ok Mk (Bs1 ++ B :: nil) Tb t' (set_env_extend θ (set_entry_term ak_relevant b)) (set_apply xv b))
  | pt_self j Ps => exists Mj ns, shape_end_with Mk Bs1 Tb j Ps θ xv Mj ns
  end.

  (** A record view's end fits along its paths, wherever it is read *)
  Hypothesis HRV : forall Mk Bs1 Tb Ψ ρe β σ x xv θ j Ps Mj ns, ⊢ gc_deps ⍮ gc_stack ⍮ Ψ -> set_env_in T γ Ψ ρe ->
    (forall y, sub_entry_agrees T γ Ψ ρe (β y) (ρ y)) -> gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ β : Γ ->
    gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ im_params D Mk -> (forall y, sub_entry_agrees T γ Ψ ρe (σ y) (θ y)) ->
    shape_uc D Us (doms_ctx Bs1 ++ Tb ++ im_params D Mk) σ β -> set_interp T γ Ψ ρe x xv ->
    gc_deps ⍮ gc_stack ⍮ Ψ ⊢ x : ptyp_ty_at p D (List.map (fun U => exp_sub U β) Us) σ (pt_self j Ps) ->
    ind_member D j = Some Mj -> im_is_rview Mj = true -> List.length Ps = im_nn Mj ->
    set_interp_list T γ (doms_ctx Bs1 ++ Tb ++ im_params D Mk) θ Ps ns -> RV j ns xv ->
    forall l, In l (shape_leaves (rview_leaves D) (List.length Bs1 + List.length Tb + im_nn Mk) (pt_self j Ps)) ->
    leaf_fits Ψ ρe β σ x xv l.

Lemma shape_leaf_sem : forall t Mk Bs1 Tb Ψ ρe β σ x xv θ Mj,
    ⊢ gc_deps ⍮ gc_stack ⍮ Ψ -> set_env_in T γ Ψ ρe -> (forall y, sub_entry_agrees T γ Ψ ρe (β y) (ρ y)) ->
    gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ β : Γ -> gc_deps ⍮ gc_stack ⍮ Ψ ⊢ˢ σ : doms_ctx Bs1 ++ Tb ++ im_params D Mk ->
    (forall y, sub_entry_agrees T γ Ψ ρe (σ y) (θ y)) -> ⊢ gc_deps ⍮ gc_stack ⍮ doms_ctx Bs1 ++ Tb ++ im_params D Mk ->
    shape_uc D Us (doms_ctx Bs1 ++ Tb ++ im_params D Mk) σ β -> set_interp T γ Ψ ρe x xv ->
    gc_deps ⍮ gc_stack ⍮ Ψ ⊢ x : ptyp_ty_at p D (List.map (fun U => exp_sub U β) Us) σ t ->
    ind_member D (ptyp_mem t) = Some Mj -> List.length (ptyp_ps t) = im_nn Mj ->
    shape_doms_typed gc_deps gc_stack D Mk Bs1 Tb t -> shape_leaf_typed gc_deps gc_stack D Mk Mj Bs1 Tb t ->
    shape_closed_ok Mk Bs1 Tb t θ xv ->
    forall l, In l (shape_leaves (rview_leaves D) (List.length Bs1 + List.length Tb + im_nn Mk) t) -> leaf_sem Ψ ρe β σ x xv l.
Proof.
  induction t as [j0 Ps | B t IH]; intros Mk Bs1 Tb Ψ ρe β σ x xv θ Mj HcΨ Hρe Hβ Hβt Hσt Hσ HcT Huc Hx Hxt Hj HPl HB HP Hcok l Hin;
    cbn [ptyp_mem ptyp_ps shape_closed_ok shape_leaves] in Hj, HPl, Hcok, Hin.
  - (* the end: a record view's fits, or the end's facts *)
    destruct Hcok as (Mj0 & ns & [HMj0 Hns Hblk Hrv]). rewrite Hj in HMj0. injection HMj0 as <-.
    destruct (im_is_rview Mj) eqn:Hr.
    + apply leaf_sem_of_fits.
      eapply HRV; [exact HcΨ | exact Hρe | exact Hβ | exact Hβt | exact Hσt | exact Hσ | exact Huc | exact Hx | exact Hxt
                  | exact Hj | exact Hr | exact HPl | exact Hns | exact (Hrv eq_refl) | exact Hin].
    + rewrite (rview_leaves_not_rview _ _ _ Hj Hr) in Hin. destruct Hin as [<- | []].
      cbn [leaf_sem]. right. destruct (HBk _ _ Hj Hr) as [b Hb]. exists Mj, b, ns.
      constructor; [exact Hj | exact Hb | exact (interp_list_realized _ _ _ _ _ _ _ HcT Hσt Hσ Hns) | | exact (Hblk eq_refl)].
      exact (ih_leaf_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDt Hcl Hj HUl (HMwf _ _ Hj) Hβt Hσt Huc HPl
               (shape_leaf_at _ _ _ _ _ _ _ _ HP eq_refl) Hxt).
  - (* a domain: the walk goes on under it *)
    apply List.in_map_iff in Hin as (l' & <- & Hin').
    destruct Hcok as (a & [Ha Edom Hrest]).
    cbn [leaf_sem]. right. exists a.
    constructor; [exact (interp_realized _ _ _ _ _ _ _ HcT Hσt Hσ Ha) | exact Edom |].
    intros b Hb.
    destruct (HB nil B (ptyp_doms t) eq_refl) as [j1 Hj1]. rewrite List.app_nil_r in Hj1.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hj1 Hσt) as Hj1'. cbn [exp_sub] in Hj1'.
    assert (HΨ' : ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass ak_relevant (exp_sub B σ) :: Ψ)
      by (eapply wf_ctx_extend; [exact Hj1' | constructor]).
    pose proof (wf_sub_q _ _ _ _ _ _ _ _ Hσt Hj1 (sort_kind_universe _) Hj1') as Hσt'.
    assert (Hβt' : gc_deps ⍮ gc_stack ⍮ ce_ass ak_relevant (exp_sub B σ) :: Ψ ⊢ˢ sb_compose β (sb_of_wk wk_shift) : Γ)
      by (eapply wf_sub_compose; [exact Hβt | apply wf_sub_of_wk, wf_wk_shift; exact HΨ']).
    assert (HcT' : ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass ak_relevant B :: doms_ctx Bs1 ++ Tb ++ im_params D Mk)
      by (eapply wf_ctx_extend; [exact Hj1 | constructor]).
    assert (EC : ce_ass ak_relevant B :: doms_ctx Bs1 ++ Tb ++ im_params D Mk = doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ im_params D Mk)
      by (rewrite doms_ctx_app_one; reflexivity).
    rewrite EC in Hσt', HcT'.
    assert (Huc' : shape_uc D Us (doms_ctx (Bs1 ++ B :: nil) ++ Tb ++ im_params D Mk) (sb_q σ) (sb_compose β (sb_of_wk wk_shift)))
      by (rewrite doms_ctx_app_one; apply shape_uc_pi; [exact (proj2 (length_shape_ctx D Mk Bs1 Tb)) | exact Huc]).
    pose proof (shape_doms_typed_pi _ _ _ _ _ _ _ _ HB) as HB''.
    pose proof (shape_leaf_typed_pi _ _ _ _ _ _ _ _ _ HP) as HP''.
    destruct (ty_at_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDt Hcl HUl HMwf HMh Hβt' Hσt' Huc' Hj HPl HB'' HP'') as [j2 Hj2].
    assert (Hus : List.map (fun U => exp_wk U wk_shift) (List.map (fun U => exp_sub U β) Us)
                  = List.map (fun U => exp_sub U (sb_compose β (sb_of_wk wk_shift))) Us)
      by (rewrite List.map_map; apply List.map_ext; intros; rewrite <- exp_sub_of_wk, exp_sub_sub; reflexivity).
    cbn [ptyp_ty_at] in Hxt. rewrite Hus in Hxt.
    pose proof (shape_arg_app _ _ _ _ _ _ _ _ Hj1' Hj2 Hxt) as Hxt'.
    assert (Hb1 : set_mem b (code_carrier a)) by exact Hb.
    apply (IH Mk (Bs1 ++ B :: nil) Tb _ _ _ _ _ _ (set_env_extend θ (set_entry_term ak_relevant b)) Mj HΨ').
    + split; [exact Hρe |]. cbn [set_entry_rel]. exists b, b, a.
      constructor; [reflexivity | reflexivity | exact (interp_realized _ _ _ _ _ _ _ HcT Hσt Hσ Ha) | exact Hb | apply set_eq_refl].
    + intros y. unfold sb_compose. exact (sub_agrees_shift _ _ _ _ _ _ HΨ' (Hβ y)).
    + exact Hβt'.
    + exact Hσt'.
    + exact (sub_agrees_q _ _ _ _ _ _ HΨ' Hσ).
    + exact HcT'.
    + exact Huc'.
    + apply set_interp_app; [| exact (set_interp_var T γ _ _ 0)].
      assert (Hw : gc_deps ⍮ gc_stack ⍮ ce_ass ak_relevant (exp_sub B σ) :: Ψ ⊢ʷ wk_shift : Ψ) by (apply wf_wk_shift; exact HΨ').
      exact (proj1 (set_interp_wk_all T γ) _ _ _ _ Hx nil Ψ _ _ _
               (Build_wk_setting Ψ ρe nil Ψ _ wk_shift (set_env_extend ρe (set_entry_term ak_relevant b)) eq_refl Hw (fun y => eq_refl))).
    + exact Hxt'.
    + exact Hj.
    + exact HPl.
    + exact HB''.
    + exact HP''.
    + exact (Hrest b Hb).
    + rewrite List.length_app. cbn [List.length]. replace (List.length Bs1 + 1 + List.length Tb + im_nn Mk)
        with (S (List.length Bs1 + List.length Tb + im_nn Mk)) by lia. exact Hin'.
Qed.

End Walk.

End LeafFits.

End Results.

End Eliminator.
