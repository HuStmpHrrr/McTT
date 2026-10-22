From Stdlib Require Import Arith List ListDec String PeanoNat Bool Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Core Require Import Soundness.
From Mctt.Core.Semantic Require Import GlobalExt.
From Mctt.Extraction Require Import Lookup PseudoMonadic NbE TypeCheckBase IndCheck GlobalCheck.
Import Syntax_Notations GlobalCtx_Notations.

(** * Deciding a Declaration

    The well-formedness of a group of inductive declarations as entries of
    a frame ([wf_gentry_ind_nil], [wf_gentry_ind_mem_nil],
    [wf_gentry_ind_ext]), decided premise by premise: the syntactic ones
    by computation, the judgments by [Extraction.GlobalCheck].  The
    premises quantifying over the members, the arguments of the
    constructors and the non-uniform parameters are decided along the
    lists, at each way of splitting them ([forall_split_dec]).  The checks
    of the views' rank, maps and members ([rank_check], [vwrap_check],
    [view_maps_check]) are complete as well as sound. *)

(** ** Module Variables

    [exp_mvc], computed. *)

Fixpoint exp_mvcb (n : nat) (M : exp) {struct M} : bool :=
  match M with
  | a_typ _ | a_level _ | a_llit _ | a_True | a_true | a_False => true
  | a_succl M | a_univ M => exp_mvcb n M
  | a_maxl M N => exp_mvcb n M && exp_mvcb n N
  | a_exfalso A M => exp_mvcb (S n) A && exp_mvcb n M
  | a_ind _ _ | a_con _ _ _ | a_nlit _ | a_ntok => true
  | a_elim _ Us _ Bks M =>
      (fix us_mvcb (Us : list exp) : bool :=
         match Us with
         | nil => true
         | U :: Us' => exp_mvcb n U && us_mvcb Us'
         end) Us &&
      (fix blocks_mvcb (Bks : list eblock) : bool :=
         match Bks with
         | nil => true
         | eb_mk nm oZ A Bs :: Bks' =>
             match oZ with Some Z => exp_mvcb (nm - 1 + n) Z | None => true end &&
             exp_mvcb (nm + n) A &&
             (fix brs_mvcb (Bs : list (string * nat * exp)) : bool :=
                match Bs with
                | nil => true
                | b :: Bs' => exp_mvcb (snd (fst b) + n) (snd b) && brs_mvcb Bs'
                end) Bs &&
             blocks_mvcb Bks'
         end) Bks &&
      exp_mvcb n M
  | a_pi A B | a_fn A B => exp_mvcb n A && exp_mvcb (S n) B
  | a_app M N => exp_mvcb n M && exp_mvcb n N
  | a_var _ => true
  | a_let b B => bnd_mvcb n b && exp_mvcb (S n) B
  | a_mem H _ => modexp_mvcb n H
  end
with modexp_mvcb (n : nat) (H : modexp) {struct H} : bool :=
  match H with
  | me_unit _ => true
  | me_var x => Nat.ltb x n
  | me_mem H _ => modexp_mvcb n H
  | me_app H N => modexp_mvcb n H && exp_mvcb n N
  | me_lit U => gunit_mvcb n U
  end
with bnd_mvcb (n : nat) (b : bnd) {struct b} : bool :=
  match b with
  | b_def oA M => match oA with Some A => exp_mvcb n A | None => true end && exp_mvcb n M
  | b_mod U => gunit_mvcb n U
  end
with gunit_mvcb (n : nat) (U : gunit) {struct U} : bool :=
  match U with
  | gu_mk Δ D =>
      (fix tele_mvcb (Δ : list centry) : bool :=
         match Δ with
         | nil => true
         | e :: Δ' => centry_mvcb (List.length Δ' + n) e && tele_mvcb Δ'
         end) Δ &&
      moddef_mvcb (List.length Δ + n) D
  end
with moddef_mvcb (n : nat) (D : moddef) {struct D} : bool :=
  match D with
  | md_body sm Φ => gmod_mvcb n Φ
  | md_alias E => modexp_mvcb n E
  end
with gmod_mvcb (n : nat) (Φ : gmod) {struct Φ} : bool :=
  match Φ with
  | gm_nil => true
  | gm_ext Φ _ E => gmod_mvcb n Φ && gentry_mvcb (gm_binders Φ + n) E
  | gm_open Φ H _ => gmod_mvcb n Φ && modexp_mvcb (gm_binders Φ + n) H
  end
with gentry_mvcb (n : nat) (E : gentry) {struct E} : bool :=
  match E with
  | ge_def _ _ A B => exp_mvcb n A && match B with Some M => exp_mvcb n M | None => true end
  | ge_mod _ U => gunit_mvcb n U
  | ge_ind _ _ _ D Φ => gmod_mvcb (ind_nu D + n) Φ
  | ge_ind_alias _ _ _ _ _ _ => true
  end
with centry_mvcb (n : nat) (e : centry) {struct e} : bool :=
  match e with
  | ce_ass A => exp_mvcb n A
  | ce_def A M => exp_mvcb n A && exp_mvcb n M
  | ce_mod U => gunit_mvcb n U
  end.

(** The uniform parameters of an eliminator, decided by the inner
    fixpoint of [exp_mvcb]. *)
Lemma us_mvcb_spec : forall n (Us : list exp),
    List.Forall (fun U => forall n, exp_mvcb n U = true <-> exp_mvc n U) Us ->
    (fix us_mvcb (Us : list exp) : bool :=
       match Us with
       | nil => true
       | U :: Us' => exp_mvcb n U && us_mvcb Us'
       end) Us = true <-> all_list (exp_mvc n) Us.
Proof.
  intros n Us HU; induction HU as [| U Us HU _ IH]; cbn; [ split; auto |].
  rewrite andb_true_iff, HU, IH; reflexivity.
Qed.

(** The branches of a block, decided by the inner fixpoint of [exp_mvcb]. *)
Lemma brs_mvcb_spec : forall n (Bs : list (string * nat * exp)),
    List.Forall (fun br => forall n, exp_mvcb n (snd br) = true <-> exp_mvc n (snd br)) Bs ->
    (fix brs_mvcb (Bs : list (string * nat * exp)) : bool :=
       match Bs with
       | nil => true
       | b :: Bs' => exp_mvcb (snd (fst b) + n) (snd b) && brs_mvcb Bs'
       end) Bs = true <-> all_brs (fun k B => exp_mvc (k + n) B) Bs.
Proof.
  intros n Bs HB; induction HB as [| b Bs Hb _ IH]; cbn; [ split; auto |].
  rewrite andb_true_iff, Hb, IH; reflexivity.
Qed.

(** The blocks of an eliminator, decided by the inner fixpoint of
    [exp_mvcb]. *)
Lemma blocks_mvcb_spec : forall n (Bks : list eblock),
    List.Forall (fun b => (forall Z, eb_ann b = Some Z -> forall n, exp_mvcb n Z = true <-> exp_mvc n Z) /\
                          (forall n, exp_mvcb n (eb_motive b) = true <-> exp_mvc n (eb_motive b)) /\
                          List.Forall (fun br => forall n, exp_mvcb n (snd br) = true <-> exp_mvc n (snd br)) (eb_brs b)) Bks ->
    (fix blocks_mvcb (Bks : list eblock) : bool :=
       match Bks with
       | nil => true
       | eb_mk nm oZ A Bs :: Bks' =>
           match oZ with Some Z => exp_mvcb (nm - 1 + n) Z | None => true end &&
           exp_mvcb (nm + n) A &&
           (fix brs_mvcb (Bs : list (string * nat * exp)) : bool :=
              match Bs with
              | nil => true
              | b :: Bs' => exp_mvcb (snd (fst b) + n) (snd b) && brs_mvcb Bs'
              end) Bs &&
           blocks_mvcb Bks'
       end) Bks = true <->
    all_blocks (fun nm oZ A Bs => opt_all (exp_mvc (nm - 1 + n)) oZ /\ exp_mvc (nm + n) A /\
                                  all_brs (fun k B => exp_mvc (k + n) B) Bs) Bks.
Proof.
  intros n Bks HB; induction HB as [| [nm oZ A Bs] Bks (HZ & HA & HBs) _ IH]; cbn in *; [ split; auto |].
  rewrite !andb_true_iff, HA, IH, (brs_mvcb_spec n Bs HBs).
  destruct oZ as [Z |]; cbn; [ rewrite (HZ Z eq_refl) | ]; tauto.
Qed.

Lemma mvcb_spec :
  (forall M n, exp_mvcb n M = true <-> exp_mvc n M) /\
  (forall H n, modexp_mvcb n H = true <-> modexp_mvc n H) /\
  (forall b n, bnd_mvcb n b = true <-> bnd_mvc n b) /\
  (forall U n, gunit_mvcb n U = true <-> gunit_mvc n U) /\
  (forall D n, moddef_mvcb n D = true <-> moddef_mvc n D) /\
  (forall Φ n, gmod_mvcb n Φ = true <-> gmod_mvc n Φ) /\
  (forall E n, gentry_mvcb n E = true <-> gentry_mvc n E) /\
  (forall e n, centry_mvcb n e = true <-> centry_mvc n e).
Proof.
  apply syn_mut_ind; intros;
    cbn [exp_mvcb modexp_mvcb bnd_mvcb gunit_mvcb moddef_mvcb gmod_mvcb gentry_mvcb centry_mvcb
         exp_mvc modexp_mvc bnd_mvc gunit_mvc moddef_mvc gmod_mvc gentry_mvc centry_mvc].
  (** An eliminator: its uniform parameters and blocks, by the inner
      fixpoints. *)
  all: try lazymatch goal with
    | HU : List.Forall _ ?Us, HB : List.Forall _ ?Bks, HM : forall n, exp_mvcb n ?M = true <-> _
      |- _ <-> all_list _ ?Us /\ all_blocks _ ?Bks /\ exp_mvc _ ?M =>
        rewrite !andb_true_iff, (us_mvcb_spec _ _ HU), (blocks_mvcb_spec _ _ HB), HM; tauto
    end.
  all: rewrite ?andb_true_iff.
  all: repeat match goal with IH : forall n : nat, _ <-> _ |- _ => setoid_rewrite IH; clear IH end.
  all: try (split; auto; fail).
  - apply Nat.ltb_lt.
  - destruct oA as [A |]; [ rewrite (H A eq_refl) | split; intros [_ ?]; split; auto ]; reflexivity.
  - (* a unit: its telescope *)
    match goal with |- ?l = true /\ _ <-> ?r /\ _ => enough (Ht : l = true <-> r) by (rewrite Ht; reflexivity) end.
    clear - H; induction H as [| e Δ He _ IH]; cbn; [ split; auto |].
    rewrite andb_true_iff, He, IH; reflexivity.
  - destruct B as [M |]; [ rewrite (H0 M eq_refl) | split; intros [? _]; split; auto ]; reflexivity.
Qed.

(** A constructor argument without free module variables, computed. *)
Definition carg_mvcb (g : carg) : bool :=
  match g with
  | ca_arg A => exp_mvcb 0 A
  | ca_rec t => forallb (exp_mvcb 0) (ptyp_doms t) && forallb (exp_mvcb 0) (ptyp_ps t)
  end.

(** A member's head without free module variables, computed. *)
Definition mhead_mvcb (h : mhead) : bool :=
  match h with
  | mh_decl _ => true
  | mh_view _ _ Is _ => forallb (exp_mvcb 0) Is
  end.

(** A member without free module variables, computed. *)
Definition member_mvcb (M : imember) : bool :=
  forallb (centry_mvcb 0) (im_nparams M) && mhead_mvcb (im_head M) &&
  forallb (fun cg => forallb carg_mvcb (snd cg)) (im_cons M).

(** A group without free module variables, computed. *)
Definition decl_mvcb (D : ind_decl) : bool :=
  forallb (centry_mvcb 0) (ind_uparams D) && exp_mvcb 0 (ind_sort D) && forallb member_mvcb (ind_members D).

Lemma forallb_Forall : forall {X} (f : X -> bool) (P : X -> Prop) l,
    (forall x, f x = true <-> P x) -> forallb f l = true <-> List.Forall P l.
Proof.
  intros * Hf; rewrite forallb_forall, List.Forall_forall; split; intros H x Hx; apply Hf; auto.
Qed.

Lemma carg_mvcb_spec : forall g, carg_mvcb g = true <-> carg_mvc g.
Proof.
  destruct mvcb_spec as (He & _).
  intros [A | t]; cbn; [ apply He |].
  rewrite andb_true_iff, !(forallb_Forall _ _ _ (fun M => He M 0)); reflexivity.
Qed.

Lemma mhead_mvcb_spec : forall h, mhead_mvcb h = true <-> mhead_mvc h.
Proof.
  destruct mvcb_spec as (He & _).
  intros [pm | qc k Is vm]; cbn; [ split; auto | apply (forallb_Forall _ _ _ (fun M => He M 0)) ].
Qed.

Lemma member_mvcb_spec : forall M, member_mvcb M = true <->
    ctx_mvc (im_nparams M) /\ mhead_mvc (im_head M) /\ (forall c gs, In (c, gs) (im_cons M) -> List.Forall carg_mvc gs).
Proof.
  destruct mvcb_spec as (_ & _ & _ & _ & _ & _ & _ & Hc).
  intros M; unfold member_mvcb, ctx_mvc; rewrite !andb_true_iff.
  rewrite (forallb_Forall _ _ _ (fun e => Hc e 0)), mhead_mvcb_spec.
  rewrite (forallb_Forall _ (fun cg => List.Forall carg_mvc (snd cg))) by (intros; apply forallb_Forall, carg_mvcb_spec).
  split.
  - intros [[H1 H2] H3]; split; [ exact H1 | split; [ exact H2 |] ].
    intros c gs Hin; exact (proj1 (List.Forall_forall _ _) H3 (c, gs) Hin).
  - intros (H1 & H2 & H3); split; [ split; assumption |].
    apply List.Forall_forall; intros [c gs] Hin; exact (H3 c gs Hin).
Qed.

Lemma decl_mvcb_spec : forall D, decl_mvcb D = true <-> decl_mvc D.
Proof.
  destruct mvcb_spec as (He & _ & _ & _ & _ & _ & _ & Hc).
  intros D; unfold decl_mvcb; rewrite !andb_true_iff.
  rewrite (forallb_Forall _ _ _ (fun e => Hc e 0)), He, (forallb_Forall _ _ _ member_mvcb_spec).
  split.
  - intros [[H1 H2] H3]; constructor; [ exact H1 | exact H2 |].
    intros k M Hk; exact (proj1 (List.Forall_forall _ _) H3 M (List.nth_error_In _ _ Hk)).
  - intros [H1 H2 H3]; split; [ split; assumption |].
    apply List.Forall_forall; intros M HM; apply List.In_nth_error in HM as [k Hk]; exact (H3 k M Hk).
Qed.

Definition decl_mvc_dec (D : ind_decl) : {decl_mvc D} + {~ decl_mvc D} :=
  match decl_mvcb D as b return decl_mvcb D = b -> _ with
  | true => fun E => left (proj1 (decl_mvcb_spec D) E)
  | false => fun E => right (fun H => diff_false_true (eq_trans (eq_sym E) (proj2 (decl_mvcb_spec D) H)))
  end eq_refl.

Definition ind_sort_univ_dec (S : typ) : {ind_sort_univ S} + {~ ind_sort_univ S}.
Proof.
  destruct S; try (right; intros [[? [=]] | [? [=]]]; fail).
  - left; left; eexists; reflexivity.
  - left; right; eexists; reflexivity.
Defined.

(** Distinct names, decided by a computation rather than by the opaque
    [ListDec.NoDup_dec]. *)
Fixpoint nodupb (l : list string) : bool :=
  match l with
  | nil => true
  | x :: l' => negb (existsb (String.eqb x) l') && nodupb l'
  end.

Lemma nodupb_spec : forall l, nodupb l = true <-> List.NoDup l.
Proof.
  induction l as [| x l IH]; cbn; [ split; [ constructor | reflexivity ] |].
  rewrite andb_true_iff, negb_true_iff, IH, <- not_true_iff_false, existsb_exists; split.
  - intros [Hn Hl]; constructor; [ intros Hin; apply Hn; exists x; split; [ exact Hin | apply String.eqb_refl ] | exact Hl ].
  - intros Hnd; inversion Hnd; subst; split; [| assumption ].
    intros (y & Hy & E); apply String.eqb_eq in E; subst; contradiction.
Qed.

Definition nodup_dec (l : list string) : {List.NoDup l} + {~ List.NoDup l} :=
  match nodupb l as b return nodupb l = b -> _ with
  | true => fun E => left (proj1 (nodupb_spec l) E)
  | false => fun E => right (fun H => diff_false_true (eq_trans (eq_sym E) (proj2 (nodupb_spec l) H)))
  end eq_refl.

(** ** Quantifying over Lists *)

(** A property at each way of splitting a list around one element. *)
Definition forall_split_dec {X : Type} :
  forall (L : list X) (P : list X -> X -> list X -> Prop),
    (forall l1 x l2, L = l1 ++ x :: l2 -> {P l1 x l2} + {~ P l1 x l2}) ->
    {forall l1 x l2, L = l1 ++ x :: l2 -> P l1 x l2} + {~ forall l1 x l2, L = l1 ++ x :: l2 -> P l1 x l2}.
Proof.
  fix go 1; intros [| a L] P f.
  - left; intros [] ? ? [=].
  - destruct (f nil a L eq_refl) as [Ha | Ha]; [| right; intros H; apply Ha, H; reflexivity ].
    destruct (go L (fun l1 x l2 => P (a :: l1) x l2) (fun l1 x l2 E => f (a :: l1) x l2 (f_equal (cons a) E)))
      as [HL | HL].
    + left; intros [| b l1] x l2 E; [ injection E as -> ->; exact Ha |].
      injection E as -> E; exact (HL _ _ _ E).
    + right; intros H; apply HL; intros l1 x l2 E; apply H; rewrite E; reflexivity.
Defined.

(** Two lists entry by entry, at the indices both have. *)
Definition forall_nth2_dec {X Y : Type} (R : X -> Y -> Prop) (f : forall x y, {R x y} + {~ R x y}) :
  forall (L1 : list X) (L2 : list Y),
    {forall k x y, List.nth_error L1 k = Some x -> List.nth_error L2 k = Some y -> R x y}
    + {~ forall k x y, List.nth_error L1 k = Some x -> List.nth_error L2 k = Some y -> R x y}.
Proof.
  fix go 1; intros [| x L1] [| y L2].
  - left; intros [] ? ? [=].
  - left; intros [] ? ? [=].
  - left; intros [] ? ? ? [=].
  - destruct (f x y) as [Hxy | Hxy]; [| right; intros H; apply Hxy, (H 0); reflexivity ].
    destruct (go L1 L2) as [HL | HL]; [ left | right ].
    + intros [| k] x' y' E1 E2; cbn in E1, E2; [ injection E1 as <-; injection E2 as <-; exact Hxy | exact (HL _ _ _ E1 E2) ].
    + intros H; apply HL; intros k; apply (H (S k)).
Defined.

(** A property of every member of a group, decided at each. *)
Definition members_dec (D : ind_decl) (Q : nat -> imember -> Prop)
    (f : forall k M, ind_member D k = Some M -> {Q k M} + {~ Q k M}) :
  { forall k M, ind_member D k = Some M -> Q k M } + { ~ forall k M, ind_member D k = Some M -> Q k M }.
Proof.
  pose (Q' := fun k => forall M, ind_member D k = Some M -> Q k M).
  assert (f' : forall k, k < List.length (ind_members D) -> (forall k', k' < k -> Q' k') -> {Q' k} + {~ Q' k}).
  { intros k _ _; unfold Q'.
    destruct (ind_member D k) as [M |] eqn:Hk; [| left; intros; discriminate ].
    destruct (f k M Hk) as [HQ | HQ]; [ left; intros M' [= <-]; exact HQ | right; intros H; exact (HQ (H M eq_refl)) ]. }
  destruct (forall_lt_dec Q' (List.length (ind_members D)) f') as [HQ | HQ]; [ left | right ].
  - intros k M Hk; apply (HQ k); [ apply List.nth_error_Some; unfold ind_member in Hk; congruence | exact Hk ].
  - intros H; apply HQ; intros k _; exact (H k).
Defined.

(** ** The Checks of a Group's Views Are Complete

    [rank_check], [vwrap_check] and [view_maps_check] accept every group
    that has a rank, whose views' members are the container's, and whose
    views agree on their maps: the checker rejects no group the
    declarative rule accepts. *)

Lemma in_combine_seq_nth : forall {X} (l : list X) s k M, In (k, M) (List.combine (List.seq s (List.length l)) l) ->
    s <= k /\ List.nth_error l (k - s) = Some M.
Proof.
  intros X l; induction l as [| x l IH]; intros s k M H; cbn in H; [ contradiction |].
  destruct H as [[= <- <-] | H]; [ split; [ lia | rewrite Nat.sub_diag; reflexivity ] |].
  destruct (IH (S s) k M H) as [Hle Hk]; split; [ lia |].
  replace (k - s) with (S (k - S s)) by lia; exact Hk.
Qed.

(** A pair of [combine (seq 0 _)] is an index and its element. *)
Corollary in_combine_seq0 : forall {X} (l : list X) k M,
    In (k, M) (List.combine (List.seq 0 (List.length l)) l) -> List.nth_error l k = Some M.
Proof. intros * H; destruct (in_combine_seq_nth l 0 k M H) as [_ Hk]; rewrite Nat.sub_0_r in Hk; exact Hk. Qed.

Lemma cargs_corrb_complete : forall vm gs' gs, cargs_corr vm gs' gs -> cargs_corrb vm gs' gs = true.
Proof.
  induction gs' as [| [A' | t'] gs' IH]; intros [| [A | t] gs] H; cbn in H |- *; try contradiction; auto.
  destruct H as (Hj & Hd & H); rewrite Hj, Nat.eqb_refl, Hd, Nat.eqb_refl; cbn; auto.
Qed.

(** A view's members that are the container's members pass the check. *)
Theorem vwrap_check_complete : forall D D' vm, vwrap_ok D D' vm -> vwrap_check D D' vm = true.
Proof.
  intros * [Hl Hm]; unfold vwrap_check; apply andb_true_iff; split; [ apply Nat.eqb_eq; exact Hl |].
  apply List.forallb_forall; intros [i' Mi'] Hin; cbn [fst snd].
  pose proof (in_combine_seq0 _ _ _ Hin) as HMi'.
  destruct (List.nth_error vm i') as [v |] eqn:Hv; [| reflexivity ].
  destruct (Hm _ _ _ HMi' Hv) as (Mv & HMv & Hnn & Hnames & Hcorr).
  rewrite HMv, Hnn, Nat.eqb_refl; cbn.
  destruct (list_eq_dec string_dec _ _) as [_ | Hne]; [| contradiction ]; cbn.
  apply List.forallb_forall; intros [c gs'] Hcg; cbn [fst snd].
  destruct (ind_con Mv c) as [gs |] eqn:Hc; [| reflexivity ].
  exact (cargs_corrb_complete _ _ _ (Hcorr _ _ _ Hcg Hc)).
Qed.

Lemma view_map_at_check_complete : forall vm M vmv, view_map_at vm M vmv -> view_map_at_check vm M vmv = true.
Proof.
  intros * H; unfold view_map_at in H; unfold view_map_at_check.
  destruct (im_head M); destruct (list_eq_dec _ _ _) as [_ | Hne]; first [ reflexivity | contradiction ].
Qed.

(** Views that agree on their maps pass the check. *)
Theorem view_maps_check_complete : forall Θ Ξ D, view_maps_coherent Θ Ξ D -> view_maps_check Θ Ξ D = true.
Proof.
  intros * H; unfold view_maps_check; apply List.forallb_forall; intros Mk HMk.
  apply List.In_nth_error in HMk as [k HMk].
  destruct (im_head Mk) as [pm | qc k' Is vm] eqn:Hh; [ reflexivity |].
  destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| reflexivity ].
  apply List.forallb_forall; intros [i' Mi'] Hin; cbn [fst snd].
  pose proof (in_combine_seq0 _ _ _ Hin) as HMi'.
  destruct (List.nth_error vm i') as [v |] eqn:Hv; [| reflexivity ].
  destruct (ind_member D v) as [Mv |] eqn:HMv; [| reflexivity ].
  destruct (im_head Mv) as [pm' | qv kv Iv vmv] eqn:HhMv; [ reflexivity |].
  exact (view_map_at_check_complete _ _ _ (H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hl HMi' Hv HMv HhMv)).
Qed.

(** The largest of a list is at least each of its elements. *)
Lemma fold_max_ge : forall l x, In x l -> x <= List.fold_right Nat.max 0 l.
Proof. induction l as [| y l IH]; intros x Hx; cbn in *; [ contradiction | destruct Hx as [<- | Hx]; [ lia | specialize (IH _ Hx); lia ] ]. Qed.

(** Filtering by a weaker test keeps no fewer elements, and one more when
    some element passes only the weaker. *)
Lemma filter_length_le : forall {X} (p pw : X -> bool) l, (forall y, p y = true -> pw y = true) ->
    List.length (List.filter p l) <= List.length (List.filter pw l).
Proof.
  intros X p pw l Hpw; induction l as [| y l IH]; cbn; [ lia |].
  destruct (p y) eqn:Ep; [ rewrite (Hpw _ Ep); cbn; lia |]; destruct (pw y); cbn; lia.
Qed.

Lemma filter_length_lt : forall {X} (p pw : X -> bool) l x, (forall y, p y = true -> pw y = true) ->
    In x l -> p x = false -> pw x = true -> List.length (List.filter p l) < List.length (List.filter pw l).
Proof.
  intros X p pw l x Hpw; induction l as [| y l IH]; intros Hin Hp Hw; cbn in Hin; [ contradiction |].
  cbn; destruct Hin as [-> | Hin].
  - rewrite Hp, Hw; cbn; pose proof (filter_length_le p pw l Hpw); lia.
  - specialize (IH Hin Hp Hw); destruct (p y) eqn:Ep; [ rewrite (Hpw _ Ep); cbn; lia |]; destruct (pw y); cbn; lia.
Qed.

Section RankComplete.
  Variables (Θ : gdeps) (Ξ : gstack) (D : ind_decl) (rk : nat -> nat).
  Hypothesis HDs : decls_typed Θ Ξ.
  Hypothesis Hrk : view_rank_ok Θ Ξ D rk.

  Lemma cargs_nest_targets_lt : forall r gs' gs j, cargs_nest_ok rk r gs' gs -> In j (cargs_nest_targets gs' gs) -> rk j < r.
  Proof.
    intros r; induction gs' as [| [A' | t'] gs' IH]; intros [| [A | t] gs] j Hok Hj; cbn in Hok, Hj; try contradiction;
      first [ destruct Hok as [Hlt Hok]; destruct Hj as [<- | Hj]; [ exact Hlt | exact (IH _ _ Hok Hj) ]
            | exact (IH _ _ Hok Hj) ].
  Qed.

  (** A view's rank is above that of every member it nests through. *)
  Lemma member_nest_targets_lt : forall k Mk j, ind_member D k = Some Mk -> In j (member_nest_targets Θ Ξ D Mk) -> rk j < rk k.
  Proof.
    intros * HMk Hj; unfold member_nest_targets in Hj.
    destruct (im_head Mk) as [pm | qc k' Is vm] eqn:Hh; [ contradiction |].
    destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| contradiction ].
    apply List.in_concat in Hj as (l1 & Hl1 & Hj); apply List.in_map_iff in Hl1 as ([i' Mi'] & <- & Hin); cbn [fst snd] in Hj.
    pose proof (in_combine_seq0 _ _ _ Hin) as HMi'.
    destruct (List.nth_error vm i') as [v |] eqn:Hv; [| contradiction ].
    destruct (ind_member D v) as [Mv |] eqn:HMv; [| contradiction ].
    apply List.in_concat in Hj as (l2 & Hl2 & Hj); apply List.in_map_iff in Hl2 as ([c gs'] & <- & Hcg); cbn [fst snd] in Hj.
    destruct (ind_con Mv c) as [gs |] eqn:Hc; [| contradiction ].
    assert (Hc' : ind_con Mi' c = Some gs').
    { unfold ind_con; apply cons_lookup_nodup; [| exact Hcg ].
      exact (dt_nodup _ _ _ (HDs _ _ Hl) _ _ HMi'). }
    exact (cargs_nest_targets_lt _ _ _ _ (vro_nest _ _ _ _ Hrk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hl HMi' Hv HMv Hc' Hc) Hj).
  Qed.

  (** The members of rank below [k]'s. *)
  Definition rank_below (k : nat) : nat :=
    List.length (List.filter (fun j => rk j <? rk k) (List.seq 0 (List.length (ind_members D)))).

  Lemma rank_below_lt : forall k j, j < List.length (ind_members D) -> rk j < rk k -> rank_below j < rank_below k.
  Proof.
    intros * Hj Hlt; unfold rank_below; apply filter_length_lt with (x := j).
    - intros y Hy; apply Nat.ltb_lt in Hy; apply Nat.ltb_lt; lia.
    - apply List.in_seq; lia.
    - apply Nat.ltb_ge; lia.
    - apply Nat.ltb_lt; exact Hlt.
  Qed.

  Lemma rank_below_bound : forall k, k < List.length (ind_members D) -> rank_below k < List.length (ind_members D).
  Proof.
    intros * Hk; unfold rank_below.
    assert (Hall : forall l : list nat, List.filter (fun _ => true) l = l) by (induction l; cbn; congruence).
    pose proof (filter_length_lt (fun j => rk j <? rk k) (fun _ => true) (List.seq 0 (List.length (ind_members D))) k
                  (fun _ _ => eq_refl) ltac:(apply List.in_seq; lia) (Nat.ltb_irrefl _) eq_refl) as H.
    rewrite Hall, List.length_seq in H; exact H.
  Qed.

  Lemma iter_nonmember : forall m j, ind_member D j = None -> grp_rank_iter Θ Ξ D m j = 0.
  Proof. intros [| m] j Hj; cbn; [ reflexivity | rewrite Hj; reflexivity ]. Qed.

  Lemma iter_view : forall m k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
      grp_rank_iter Θ Ξ D (S m) k =
        S (List.fold_right Nat.max 0 (List.map (grp_rank_iter Θ Ξ D m) (member_nest_targets Θ Ξ D Mk))).
  Proof. intros * Hk Hh; cbn [grp_rank_iter]; rewrite Hk, Hh; reflexivity. Qed.

  (** The candidate rank of a member is stable after as many rounds as
      there are members below it. *)
  Lemma iter_stable : forall r k m, rk k = r -> rank_below k < m ->
      grp_rank_iter Θ Ξ D m k = grp_rank_iter Θ Ξ D (S m) k.
  Proof.
    induction r as [r IH] using lt_wf_ind; intros k m Hr Hm.
    destruct m as [| m]; [ lia |].
    destruct (ind_member D k) as [Mk |] eqn:Hk; [| rewrite !iter_nonmember by exact Hk; reflexivity ].
    destruct (im_head Mk) as [pm | qc k' Is vm] eqn:Hh; [ cbn [grp_rank_iter]; rewrite Hk, Hh; reflexivity |].
    rewrite (iter_view m _ _ _ _ _ _ Hk Hh), (iter_view (S m) _ _ _ _ _ _ Hk Hh).
    f_equal; f_equal; apply List.map_ext_in; intros j Hj.
    pose proof (member_nest_targets_lt _ _ _ Hk Hj) as Hlt.
    assert (Hcase : (exists Mj, ind_member D j = Some Mj) \/ ind_member D j = None)
      by (destruct (ind_member D j); eauto).
    destruct Hcase as [[Mj Hjm] | Hjm].
    - assert (Hjn : j < List.length (ind_members D)) by (apply List.nth_error_Some; unfold ind_member in Hjm; congruence).
      pose proof (rank_below_lt k j Hjn Hlt).
      apply (IH (rk j)); [ lia | reflexivity | lia ].
    - rewrite !iter_nonmember by exact Hjm; reflexivity.
  Qed.

  (** A group with a rank passes the check. *)
  Theorem rank_check_complete_at : rank_check Θ Ξ D = true.
  Proof.
    unfold rank_check, grp_rank; apply List.forallb_forall; intros [k Mk] Hin; cbn [fst snd].
    pose proof (in_combine_seq0 _ _ _ Hin) as HMk.
    assert (Hkn : k < List.length (ind_members D)) by (apply List.nth_error_Some; congruence).
    pose proof (rank_below_bound k Hkn) as Hb.
    destruct (List.length (ind_members D)) as [| n'] eqn:En; [ lia |].
    destruct (im_head Mk) as [pm | qc k' Is vm] eqn:Hh.
    - cbn [grp_rank_iter]; unfold ind_member; rewrite HMk, Hh; reflexivity.
    - apply List.forallb_forall; intros j Hj; apply Nat.ltb_lt.
      assert (Hjk : rk j < rk k) by exact (member_nest_targets_lt _ _ _ HMk Hj).
      assert (Hj' : grp_rank_iter Θ Ξ D n' j = grp_rank_iter Θ Ξ D (S n') j).
      { assert (Hcase : (exists Mj, ind_member D j = Some Mj) \/ ind_member D j = None)
          by (destruct (ind_member D j); eauto).
        destruct Hcase as [[Mj Hjm] | Hjm].
        - assert (Hjn : j < S n') by (rewrite <- En; apply List.nth_error_Some; unfold ind_member in Hjm; congruence).
          pose proof (rank_below_lt k j ltac:(rewrite En; exact Hjn) Hjk).
          apply (iter_stable (rk j)); [ reflexivity | lia ].
        - rewrite !iter_nonmember by exact Hjm; reflexivity. }
      rewrite <- Hj', (iter_view n' _ _ _ _ _ _ HMk Hh).
      pose proof (fold_max_ge _ _ (List.in_map (grp_rank_iter Θ Ξ D n') _ _ Hj)); lia.
  Qed.
End RankComplete.

(** A group with some rank passes the check. *)
Theorem rank_check_complete : forall Θ Ξ D, decls_typed Θ Ξ -> (exists rk, view_rank_ok Θ Ξ D rk) -> rank_check Θ Ξ D = true.
Proof. intros * HDs [rk Hrk]; exact (rank_check_complete_at Θ Ξ D rk HDs Hrk). Qed.
