From Stdlib Require Import Arith List ListDec String PeanoNat Bool Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Core Require Import Soundness Completeness.
From Mctt.Core.Semantic Require Import GlobalExt.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Extraction Require Import Lookup PseudoMonadic NbE Subtyping TypeCheckBase IndCheck TypeCheck GlobalCheck.
Import Syntax_Notations GlobalCtx_Notations.

(** * Deciding a Declaration

    The well-formedness of a group of inductive declarations as entries of
    a frame, each with an empty module ([wf_gentry_ind_nil],
    [wf_gentry_ind_mem_nil]), decided premise by premise: the syntactic ones
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
  | a_record _ => true
  | a_tuple T fs =>
      exp_mvcb n T &&
      (fix fields_mvcb (fs : list (string * exp)) : bool :=
         match fs with
         | nil => true
         | f :: fs' => exp_mvcb n (snd f) && fields_mvcb fs'
         end) fs
  | a_proj _ M => exp_mvcb n M
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
  | ge_def_mod _ A M U => exp_mvcb n A && exp_mvcb n M && gunit_mvcb n U
  | ge_record _ _ R Φ => gmod_mvcb (S (List.length (record_params R)) + n) Φ
  end
with centry_mvcb (n : nat) (e : centry) {struct e} : bool :=
  match e with
  | ce_ass A => exp_mvcb n A
  | ce_def A M => exp_mvcb n A && exp_mvcb n M
  | ce_mod U => gunit_mvcb n U
  | ce_dm A M U => exp_mvcb n A && exp_mvcb n M && gunit_mvcb n U
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

(** The fields of a tuple, computed. *)
Lemma fields_mvcb_spec : forall n (fs : list (string * exp)),
    List.Forall (fun f => forall n, exp_mvcb n (snd f) = true <-> exp_mvc n (snd f)) fs ->
    (fix fields_mvcb (fs : list (string * exp)) : bool :=
       match fs with
       | nil => true
       | f :: fs' => exp_mvcb n (snd f) && fields_mvcb fs'
       end) fs = true <->
    all_list (fun f => exp_mvc n (snd f)) fs.
Proof.
  intros n fs HF; induction HF as [| f fs Hf _ IH]; cbn in *; [ split; auto |].
  rewrite andb_true_iff, Hf, IH; reflexivity.
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
  (** A tuple: its annotation and its fields, by the inner fixpoint. *)
  all: try lazymatch goal with
    | HF : List.Forall _ ?fs, HT : forall n, exp_mvcb n ?T = true <-> _ |- _ <-> exp_mvc _ ?T /\ all_list _ ?fs =>
        rewrite andb_true_iff, (fields_mvcb_spec _ _ HF), HT; reflexivity
    end.
  all: rewrite ?andb_true_iff.
  all: repeat match goal with IH : forall n : nat, _ <-> _ |- _ => setoid_rewrite IH; clear IH end.
  all: try (split; auto; fail).
  (** A definition with a module part: its three parts, reassociated. *)
  all: try (tauto; fail).
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
      exact (decl_typed_nodup _ _ _ (HDs _ _ Hl) _ _ HMi'). }
    exact (cargs_nest_targets_lt _ _ _ _ (view_rank_ok_nest _ _ _ _ Hrk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hl HMi' Hv HMv Hc' Hc) Hj).
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

(** ** Quantifying over the Parts of a Group

    The premises of a group's rule quantify over its members, its views,
    the members of a view's container, the constructors two members share,
    the positions of a recursive argument in two argument lists, and the
    positions of lists; each is decided along a list, and, for the
    premises at one universe, with a bound ([bound_in_dec]). *)

(** A property monotone in a bound at every element of a list, with one
    bound for them all. *)
Definition bound_in_dec {X : Type} (Q : X -> nat -> Prop) (Hmono : forall x l l', l <= l' -> Q x l -> Q x l') :
  forall (L : list X), (forall x, In x L -> {l | Q x l} + {forall l, ~ Q x l}) ->
    {l | forall x, In x L -> Q x l} + {forall l, ~ forall x, In x L -> Q x l}.
Proof.
  fix go 1; intros [| x L] f.
  - left; exists 0; intros ? [].
  - destruct (f x (or_introl eq_refl)) as [[lx Hx] | Hx]; [| right; intros l H; exact (Hx l (H x (or_introl eq_refl))) ].
    destruct (go L (fun y Hy => f y (or_intror Hy))) as [[lL HL] | HL];
      [| right; intros l H; apply (HL l); intros y Hy; exact (H y (or_intror Hy)) ].
    left; exists (Nat.max lx lL); intros y [<- | Hy]; [ eapply Hmono; [| exact Hx ]; lia | eapply Hmono; [| exact (HL y Hy) ]; lia ].
Defined.

(** A property at every member of a group, with one bound. *)
Definition members_bound_dec (D : ind_decl) (Q : nat -> imember -> nat -> Prop)
    (Hmono : forall k M l l', l <= l' -> Q k M l -> Q k M l')
    (f : forall k M, ind_member D k = Some M -> {l | Q k M l} + {forall l, ~ Q k M l}) :
  {l | forall k M, ind_member D k = Some M -> Q k M l} + {forall l, ~ forall k M, ind_member D k = Some M -> Q k M l}.
Proof.
  destruct (bound_in_dec (fun kM l => Q (fst kM) (snd kM) l) (fun kM l l' Hle => Hmono _ _ _ _ Hle)
              (List.combine (List.seq 0 (List.length (ind_members D))) (ind_members D))) as [[l Hl] | Hl].
  - intros [k M] Hin; exact (f k M (in_combine_seq0 _ _ _ Hin)).
  - left; exists l; intros k M Hk; exact (Hl (k, M) (in_combine_seq _ _ _ Hk)).
  - right; intros l H; apply (Hl l); intros [k M] Hin; exact (H k M (in_combine_seq0 _ _ _ Hin)).
Defined.

(** A property of every view of a group, decided at each. *)
Definition views_dec (D : ind_decl) (Q : nat -> imember -> qname -> nat -> list exp -> list nat -> Prop)
    (f : forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       {Q k Mk qc k' Is vm} + {~ Q k Mk qc k' Is vm}) :
  {forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm -> Q k Mk qc k' Is vm}
  + {~ forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm -> Q k Mk qc k' Is vm}.
Proof.
  destruct (members_dec D (fun k Mk => forall qc k' Is vm, im_head Mk = mh_view qc k' Is vm -> Q k Mk qc k' Is vm))
    as [H | H].
  - intros k Mk Hk; destruct (im_head Mk) as [pm | qc k' Is vm] eqn:Hh; [ left; intros; discriminate |].
    destruct (f _ _ _ _ _ _ Hk Hh) as [HQ | HQ];
      [ left; intros ? ? ? ? [= <- <- <- <-]; exact HQ | right; intros H'; exact (HQ (H' _ _ _ _ eq_refl)) ].
  - left; intros * Hk Hh; exact (H _ _ Hk _ _ _ _ Hh).
  - right; intros H'; apply H; intros * Hk * Hh; exact (H' _ _ _ _ _ _ Hk Hh).
Defined.

(** The same with one bound. *)
Definition views_bound_dec (D : ind_decl) (Q : nat -> imember -> qname -> nat -> list exp -> list nat -> nat -> Prop)
    (Hmono : forall k Mk qc k' Is vm l l', l <= l' -> Q k Mk qc k' Is vm l -> Q k Mk qc k' Is vm l')
    (f : forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       {l | Q k Mk qc k' Is vm l} + {forall l, ~ Q k Mk qc k' Is vm l}) :
  {l | forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm -> Q k Mk qc k' Is vm l}
  + {forall l, ~ forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm -> Q k Mk qc k' Is vm l}.
Proof.
  destruct (members_bound_dec D (fun k Mk l => forall qc k' Is vm, im_head Mk = mh_view qc k' Is vm -> Q k Mk qc k' Is vm l))
    as [[l H] | H].
  - intros * Hle HQ * Hh; exact (Hmono _ _ _ _ _ _ _ _ Hle (HQ _ _ _ _ Hh)).
  - intros k Mk Hk; destruct (im_head Mk) as [pm | qc k' Is vm] eqn:Hh; [ left; exists 0; intros; discriminate |].
    destruct (f _ _ _ _ _ _ Hk Hh) as [[l HQ] | HQ];
      [ left; exists l; intros ? ? ? ? [= <- <- <- <-]; exact HQ | right; intros l H'; exact (HQ l (H' _ _ _ _ eq_refl)) ].
  - left; exists l; intros * Hk Hh; exact (H _ _ Hk _ _ _ _ Hh).
  - right; intros l H'; apply (H l); intros * Hk * Hh; exact (H' _ _ _ _ _ _ Hk Hh).
Defined.

(** The same with one bound, at every member of a group. *)
Definition members_bound_dec' := members_bound_dec.

(** A property of the constructors two members share, decided at each. *)
Definition con_pairs_dec (M1 M2 : imember) (Q : string -> list carg -> list carg -> Prop)
    (f : forall c gs1 gs2, ind_con M1 c = Some gs1 -> ind_con M2 c = Some gs2 -> {Q c gs1 gs2} + {~ Q c gs1 gs2}) :
  {forall c gs1 gs2, ind_con M1 c = Some gs1 -> ind_con M2 c = Some gs2 -> Q c gs1 gs2}
  + {~ forall c gs1 gs2, ind_con M1 c = Some gs1 -> ind_con M2 c = Some gs2 -> Q c gs1 gs2}.
Proof.
  destruct (forall_in_dec (fun cg => forall gs1 gs2, ind_con M1 (fst cg) = Some gs1 -> ind_con M2 (fst cg) = Some gs2 ->
                                     Q (fst cg) gs1 gs2) (im_cons M1)) as [H | H].
  - intros [c gs] _; cbn [fst].
    destruct (ind_con M1 c) as [gs1 |] eqn:H1; [| left; intros ? ? [=] ].
    destruct (ind_con M2 c) as [gs2 |] eqn:H2; [| left; intros ? ? _ [=] ].
    destruct (f c gs1 gs2 H1 H2) as [HQ | HQ];
      [ left; intros ? ? [= <-] [= <-]; exact HQ | right; intros H'; exact (HQ (H' _ _ eq_refl eq_refl)) ].
  - left; intros c gs1 gs2 H1 H2; exact (H (c, gs1) (cons_lookup_in _ _ _ H1) gs1 gs2 H1 H2).
  - right; intros H'; apply H; intros [c gs] _ gs1 gs2 H1 H2; exact (H' _ _ _ H1 H2).
Defined.

(** The same with one bound. *)
Definition con_pairs_bound_dec (M1 M2 : imember) (Q : string -> list carg -> list carg -> nat -> Prop)
    (Hmono : forall c gs1 gs2 l l', l <= l' -> Q c gs1 gs2 l -> Q c gs1 gs2 l')
    (f : forall c gs1 gs2, ind_con M1 c = Some gs1 -> ind_con M2 c = Some gs2 -> {l | Q c gs1 gs2 l} + {forall l, ~ Q c gs1 gs2 l}) :
  {l | forall c gs1 gs2, ind_con M1 c = Some gs1 -> ind_con M2 c = Some gs2 -> Q c gs1 gs2 l}
  + {forall l, ~ forall c gs1 gs2, ind_con M1 c = Some gs1 -> ind_con M2 c = Some gs2 -> Q c gs1 gs2 l}.
Proof.
  destruct (bound_in_dec (fun cg l => forall gs1 gs2, ind_con M1 (fst cg) = Some gs1 -> ind_con M2 (fst cg) = Some gs2 ->
                                      Q (fst cg) gs1 gs2 l)
              (fun cg l l' Hle H gs1 gs2 H1 H2 => Hmono _ _ _ _ _ Hle (H gs1 gs2 H1 H2)) (im_cons M1)) as [[l H] | H].
  - intros [c gs] _; cbn [fst].
    destruct (ind_con M1 c) as [gs1 |] eqn:H1; [| left; exists 0; intros ? ? [=] ].
    destruct (ind_con M2 c) as [gs2 |] eqn:H2; [| left; exists 0; intros ? ? _ [=] ].
    destruct (f c gs1 gs2 H1 H2) as [[l HQ] | HQ];
      [ left; exists l; intros ? ? [= <-] [= <-]; exact HQ | right; intros l H'; exact (HQ l (H' _ _ eq_refl eq_refl)) ].
  - left; exists l; intros c gs1 gs2 H1 H2; exact (H (c, gs1) (cons_lookup_in _ _ _ H1) gs1 gs2 H1 H2).
  - right; intros l H'; apply (H l); intros [c gs] _ gs1 gs2 H1 H2; exact (H' _ _ _ H1 H2).
Defined.

(** A split of a list around its element at a position. *)
Lemma split_at_pos : forall {X} (l l1 l2 : list X) x, l = l1 ++ x :: l2 ->
    l1 = List.firstn (List.length l1) l /\ List.nth_error l (List.length l1) = Some x /\ l2 = List.skipn (S (List.length l1)) l.
Proof.
  intros * ->; split; [| split ].
  - rewrite List.firstn_app, Nat.sub_diag, List.firstn_all; cbn [List.firstn]; rewrite List.app_nil_r; reflexivity.
  - rewrite List.nth_error_app2, Nat.sub_diag by lia; reflexivity.
  - rewrite List.skipn_app, List.skipn_all2 by lia; replace (S (List.length l1) - List.length l1) with 1 by lia; reflexivity.
Qed.

Lemma split_of_pos : forall {X} (l : list X) n x, List.nth_error l n = Some x ->
    l = List.firstn n l ++ x :: List.skipn (S n) l /\ List.length (List.firstn n l) = n.
Proof.
  intros * Hn; pose proof (List.nth_error_split l n Hn) as (l1 & l2 & -> & <-).
  rewrite List.firstn_app, Nat.sub_diag, List.firstn_all; cbn [List.firstn]; rewrite List.app_nil_r.
  rewrite List.skipn_app, List.skipn_all2 by lia; replace (S (List.length l1) - List.length l1) with 1 by lia.
  split; reflexivity.
Qed.

(** A property at the positions where two argument lists both have a
    recursive argument, decided at each. *)
Definition rec_pairs_dec (gs' gs : list carg) (Q : list carg -> ptyp -> list carg -> list carg -> ptyp -> list carg -> Prop)
    (f : forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
       List.length gs1' = List.length gs1 -> {Q gs1' t' gs2' gs1 t gs2} + {~ Q gs1' t' gs2' gs1 t gs2}) :
  {forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
     List.length gs1' = List.length gs1 -> Q gs1' t' gs2' gs1 t gs2}
  + {~ forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
     List.length gs1' = List.length gs1 -> Q gs1' t' gs2' gs1 t gs2}.
Proof.
  destruct (forall_split_dec gs' (fun gs1' g' gs2' => forall t' gs1 t gs2, g' = ca_rec t' -> gs = gs1 ++ ca_rec t :: gs2 ->
                                     List.length gs1' = List.length gs1 -> Q gs1' t' gs2' gs1 t gs2)) as [H | H].
  - intros gs1' [A' | t'] gs2' E'; [ left; intros ? ? ? ? [=] |].
    destruct (List.nth_error gs (List.length gs1')) as [[A | t] |] eqn:Hn.
    + left; intros ? gs1 t gs2 _ E Hl; exfalso.
      destruct (split_at_pos _ _ _ _ E) as (_ & Hn' & _); rewrite <- Hl, Hn in Hn'; discriminate.
    + destruct (split_of_pos _ _ _ Hn) as [E Hl].
      destruct (f gs1' t' gs2' _ _ _ E' E (eq_sym Hl)) as [HQ | HQ].
      * left; intros t'' gs1 t0 gs2 [= <-] E0 Hl0.
        destruct (split_at_pos _ _ _ _ E0) as (Hg1 & Hn0 & Hg2); rewrite <- Hl0, Hn in Hn0; injection Hn0 as <-.
        rewrite Hg1, Hg2, <- Hl0; exact HQ.
      * right; intros H'; exact (HQ (H' _ _ _ _ eq_refl E (eq_sym Hl))).
    + left; intros ? gs1 t gs2 _ E Hl; exfalso.
      destruct (split_at_pos _ _ _ _ E) as (_ & Hn' & _); rewrite <- Hl, Hn in Hn'; discriminate.
  - left; intros gs1' t' gs2' gs1 t gs2 E' E Hl; exact (H _ _ _ E' _ _ _ _ eq_refl E Hl).
  - right; intros H'; apply H; intros gs1' g' gs2' E' t' gs1 t gs2 -> E Hl; exact (H' _ _ _ _ _ _ E' E Hl).
Defined.

(** The same with one bound. *)
Definition rec_pairs_bound_dec (gs' gs : list carg)
    (Q : list carg -> ptyp -> list carg -> list carg -> ptyp -> list carg -> nat -> Prop)
    (Hmono : forall gs1' t' gs2' gs1 t gs2 l l', l <= l' -> Q gs1' t' gs2' gs1 t gs2 l -> Q gs1' t' gs2' gs1 t gs2 l')
    (f : forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
       List.length gs1' = List.length gs1 -> {l | Q gs1' t' gs2' gs1 t gs2 l} + {forall l, ~ Q gs1' t' gs2' gs1 t gs2 l}) :
  {l | forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
     List.length gs1' = List.length gs1 -> Q gs1' t' gs2' gs1 t gs2 l}
  + {forall l, ~ forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
     List.length gs1' = List.length gs1 -> Q gs1' t' gs2' gs1 t gs2 l}.
Proof.
  pose (R := fun n l => forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
                List.length gs1' = n -> List.length gs1 = n -> Q gs1' t' gs2' gs1 t gs2 l).
  assert (HR : forall l, (forall n, In n (List.seq 0 (List.length gs')) -> R n l) <->
                 forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
                   List.length gs1' = List.length gs1 -> Q gs1' t' gs2' gs1 t gs2 l).
  { intros l; split.
    - intros H gs1' t' gs2' gs1 t gs2 E' E Hl; apply (H (List.length gs1')); [| exact E' | exact E | reflexivity | symmetry; exact Hl ].
      apply List.in_seq; subst gs'; rewrite List.length_app; cbn; lia.
    - intros H n _ gs1' t' gs2' gs1 t gs2 E' E Hl' Hl; apply H; [ exact E' | exact E | lia ]. }
  destruct (bound_in_dec R (fun n l l' Hle H gs1' t' gs2' gs1 t gs2 E' E Hl' Hl =>
                              Hmono _ _ _ _ _ _ _ _ Hle (H _ _ _ _ _ _ E' E Hl' Hl))
              (List.seq 0 (List.length gs'))) as [[l Hl] | Hl].
  - intros n _; unfold R.
    destruct (List.nth_error gs' n) as [[A' | t'] |] eqn:Hn'.
    + left; exists 0; intros gs1' t'' gs2' gs1 t0 gs2 E' _ Hl' _; exfalso.
      destruct (split_at_pos _ _ _ _ E') as (_ & Hn0 & _); rewrite Hl', Hn' in Hn0; discriminate.
    + destruct (List.nth_error gs n) as [[A | t] |] eqn:Hn.
      * left; exists 0; intros gs1' t'' gs2' gs1 t0 gs2 _ E _ Hl; exfalso.
        destruct (split_at_pos _ _ _ _ E) as (_ & Hn0 & _); rewrite Hl, Hn in Hn0; discriminate.
      * destruct (split_of_pos _ _ _ Hn') as [E' Hl'], (split_of_pos _ _ _ Hn) as [E Hl].
        destruct (f _ _ _ _ _ _ E' E (eq_trans Hl' (eq_sym Hl))) as [[l HQ] | HQ].
        -- left; exists l; intros gs1' t'' gs2' gs1 t0 gs2 E1 E2 Hl1 Hl2.
           destruct (split_at_pos _ _ _ _ E1) as (Ha1 & Hn1 & Hb1); rewrite Hl1, Hn' in Hn1; injection Hn1 as <-.
           destruct (split_at_pos _ _ _ _ E2) as (Ha2 & Hn2 & Hb2); rewrite Hl2, Hn in Hn2; injection Hn2 as <-.
           rewrite Ha1, Hb1, Ha2, Hb2, Hl1, Hl2; exact HQ.
        -- right; intros l H; exact (HQ l (H _ _ _ _ _ _ E' E Hl' Hl)).
      * left; exists 0; intros gs1' t'' gs2' gs1 t0 gs2 _ E _ Hl; exfalso.
        destruct (split_at_pos _ _ _ _ E) as (_ & Hn0 & _); rewrite Hl, Hn in Hn0; discriminate.
    + left; exists 0; intros gs1' t'' gs2' gs1 t0 gs2 E' _ Hl' _; exfalso.
      destruct (split_at_pos _ _ _ _ E') as (_ & Hn0 & _); rewrite Hl', Hn' in Hn0; discriminate.
  - left; exists l; apply HR; exact Hl.
  - right; intros l H; apply (Hl l); apply HR; exact H.
Defined.

(** A property at the positions three lists all have, decided at each. *)
Definition forall_nth3_dec {X Y Z : Type} (R : X -> Y -> Z -> Prop) (f : forall x y z, {R x y z} + {~ R x y z}) :
  forall (L1 : list X) (L2 : list Y) (L3 : list Z),
    {forall j x y z, List.nth_error L1 j = Some x -> List.nth_error L2 j = Some y -> List.nth_error L3 j = Some z -> R x y z}
    + {~ forall j x y z, List.nth_error L1 j = Some x -> List.nth_error L2 j = Some y -> List.nth_error L3 j = Some z -> R x y z}.
Proof.
  fix go 1; intros [| x L1] [| y L2] [| z L3];
    try (left; intros [] ? ? ? [=] ; fail); try (left; intros [] ? ? ? ? [=]; fail); try (left; intros [] ? ? ? ? ? [=]; fail).
  destruct (f x y z) as [Hxyz | Hxyz]; [| right; intros H; apply Hxyz, (H 0); reflexivity ].
  destruct (go L1 L2 L3) as [HL | HL]; [ left | right ].
  - intros [| j] x' y' z' E1 E2 E3; cbn in E1, E2, E3;
      [ injection E1 as <-; injection E2 as <-; injection E3 as <-; exact Hxyz | exact (HL _ _ _ _ E1 E2 E3) ].
  - intros H; apply HL; intros j; apply (H (S j)).
Defined.

(** ** Deciding the Judgments a Group Asks For *)

Section Judgments.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.

  (** A term of a type in a context, which is checked first. *)
  Definition check_exp_at (Γ : ctx) (A M : exp) : {Θ ⍮ Ξ ⍮ Γ ⊢ M : A} + {~ Θ ⍮ Ξ ⍮ Γ ⊢ M : A} :=
    match check_ctx fctx_none Θ Ξ HΞ Γ with
    | left HΓ => check_exp fctx_none Θ Ξ Γ HΓ A M
    | right HnΓ => right (fun H => HnΓ (presup_exp_ctx H))
    end.

  Lemma typed_nbe_order' : forall Γ M A, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> nbe_order Θ Ξ Γ M A.
  Proof. intros * H; destruct (soundness H) as (W & HW & _); exact (nbe_order_sound _ _ _ _ _ _ HW). Qed.

  Lemma typ_nbe_ty_order : forall Γ A i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i -> nbe_ty_order Θ Ξ Γ A.
  Proof. intros * HA; destruct (@soundness_ty (gc_mk Θ Ξ) _ _ _ HA) as [W [HW _]]; exact (nbe_ty_order_sound _ _ _ _ _ HW). Qed.

  (** The least large universe a type is in: that of the universe it
      infers. *)
  Definition typ_least_dec (Γ : ctx) (A : typ) :
    { l | Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@l /\ forall j, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@j -> l <= j }
    + { forall j, ~ Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@j }.
  Proof.
    destruct (check_ctx fctx_none Θ Ξ HΞ Γ) as [HΓ | HnΓ]; [| right; intros j H; exact (HnΓ (presup_exp_ctx H)) ].
    destruct (@type_infer (gc_mk Θ Ξ) (fctx_none Θ Ξ) Γ HΓ A ltac:(apply user_exp_to_type_infer_order, user_exp_all))
      as [[UA (HAi & _ & _)] | HnA]; [| right; exact (not_wf_typ_of_no_infer _ _ _ _ HnA) ].
    destruct (univ_nf_idx_dec UA) as [[u Hu] | Hnu]; [| right; exact (not_wf_typ_of_infer_not_typ _ _ _ _ _ HAi Hnu) ].
    left; exists (unf_large u); split; [ exact (alg_type_infer_univ_sound' _ _ _ _ _ _ HAi Hu HΓ) |].
    intros j Hj.
    destruct (@alg_type_infer_large_typ_complete (gc_mk Θ Ξ) Γ j A (user_exp_all _) Hj) as (UA' & u' & HAi' & Hu' & Hle).
    pose proof (@functional_alg_type_infer (gc_mk Θ Ξ) _ _ _ _ HΞ HAi HAi') as <-.
    pose proof (is_univ_nf_functional _ _ _ Hu Hu') as <-.
    destruct u; cbn in Hle |- *; lia.
  Defined.

  (** Two terms typed at a type with one normal form are equal there. *)
  Lemma eq_of_nbe : forall Γ A M N W, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
      nbe Θ Ξ Γ M A W -> nbe Θ Ξ Γ N A W -> Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ N : A.
  Proof. intros * HM HN HMW HNW; etransitivity; [ exact (soundness' HM HMW) | symmetry; exact (soundness' HN HNW) ]. Qed.

  (** The equality of two terms at a type: both checked there, normalized
      and compared. *)
  Definition eq_at_dec (Γ : ctx) (A M N : exp) : {Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ N : A} + {~ Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ N : A}.
  Proof.
    destruct (check_exp_at Γ A M) as [HM | HnM]; [| right; intros H; apply HnM; gen_presups; assumption ].
    destruct (check_exp_at Γ A N) as [HN | HnN]; [| right; intros H; apply HnN; gen_presups; assumption ].
    destruct (@nbe_impl Θ Ξ (fctx_none Θ Ξ) Γ M A (typed_nbe_order' _ _ _ HM)) as [W1 HW1].
    destruct (@nbe_impl Θ Ξ (fctx_none Θ Ξ) Γ N A (typed_nbe_order' _ _ _ HN)) as [W2 HW2].
    destruct (nf_eq_dec W1 W2) as [<- | Hne]; [ left; exact (eq_of_nbe _ _ _ _ _ HM HN HW1 HW2) | right; intros H ].
    destruct (completeness H) as (W & HMW & HNW).
    apply Hne; rewrite (functional_nbe _ _ _ _ _ HW1 HMW), (functional_nbe _ _ _ _ _ HW2 HNW); reflexivity.
  Defined.

  (** Types equal at a universe are equal at every universe both are in. *)
  Lemma typ_eq_at_level : forall Γ A A' i l, Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@l -> Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@l -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@l.
  Proof.
    intros * H HA HA'.
    destruct (completeness H) as (W & HAW & HA'W).
    apply nbe_type_to_nbe_ty in HAW, HA'W.
    etransitivity; [ exact (@soundness_ty' (gc_mk Θ Ξ) _ _ _ _ HA HAW)
                   | symmetry; exact (@soundness_ty' (gc_mk Θ Ξ) _ _ _ _ HA' HA'W) ].
  Qed.

  (** Some universe two types are equal at: the least both are in. *)
  Definition typ_eq_least_dec (Γ : ctx) (A B : typ) :
    {l | Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ B : Typeω@l} + {forall l, ~ Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ B : Typeω@l}.
  Proof.
    destruct (typ_least_dec Γ A) as [[lA [HA _]] | HnA]; [| right; intros l Hl; apply (HnA l); gen_presups; assumption ].
    destruct (typ_least_dec Γ B) as [[lB [HB _]] | HnB]; [| right; intros l Hl; apply (HnB l); gen_presups; assumption ].
    destruct (eq_at_dec Γ Typeω@(Nat.max lA lB) A B) as [HE | HnE]; [ left; exists (Nat.max lA lB); exact HE |].
    right; intros l Hl; apply HnE.
    eapply typ_eq_at_level; [ exact Hl | apply (lift_exp_ge _ _ _ _ lA); [ lia | exact HA ]
                            | apply (lift_exp_ge _ _ _ _ lB); [ lia | exact HB ] ].
  Defined.

  (** The equality of two contexts' extensions, of assumptions on the
      left: entry by entry, each pair of types at the least universe both
      are in. *)
  Fixpoint ext_eq_dec (Γ : ctx) (Ψ : ctx) {struct Ψ} :
    forall Ψ', tele_ass Ψ -> {Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'} + {~ Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'}.
  Proof.
    intros Ψ' Hass; destruct Ψ as [| e Ψ0].
    - destruct Ψ' as [| e' Ψ0']; [| right; intros H; inversion H ].
      destruct (check_ctx fctx_none Θ Ξ HΞ Γ) as [HΓ | HnΓ]; [ left; constructor; exact HΓ | right; intros H ].
      apply HnΓ; exact (presup_ext_eq_ctx H).
    - pose proof (List.Forall_inv_tail Hass) as Hass'.
      destruct e as [A | A M | U | A M U]; [| exfalso; destruct (List.Forall_inv Hass) as [? [=]] .. ].
      destruct Ψ' as [| [A' | A' M' | U' | A' M' U'] Ψ0']; try (right; intros H; inversion H; fail).
      destruct (ext_eq_dec Γ Ψ0 Ψ0' Hass') as [Hr | Hr]; [| right; intros H; apply Hr; inversion H; assumption ].
      destruct (typ_least_dec (Ψ0 ++ Γ) A) as [[lA [HA HAm]] | HnA];
        [| right; intros H; destruct (ext_eq_ass_inv _ _ _ _ _ _ _ H) as (i & _ & HA & _); exact (HnA _ HA) ].
      destruct (typ_least_dec (Ψ0' ++ Γ) A') as [[lA' [HA' HA'm]] | HnA'];
        [| right; intros H; destruct (ext_eq_ass_inv _ _ _ _ _ _ _ H) as (i & _ & _ & _ & HA'); exact (HnA' _ HA') ].
      destruct (typ_least_dec (Ψ0 ++ Γ) A') as [[lA'' [HA'' HA''m]] | HnA''];
        [| right; intros H; destruct (ext_eq_ass_inv _ _ _ _ _ _ _ H) as (i & _ & _ & HAA & _);
           apply (HnA'' i); gen_presups; assumption ].
      set (L := Nat.max lA (Nat.max lA' lA'')).
      destruct (eq_at_dec (Ψ0 ++ Γ) Typeω@L A A') as [HAA | HnAA].
      + left; eapply wf_ext_eq_ass with (i := L); [ exact Hr | apply (lift_exp_ge _ _ _ _ lA); [ lia | exact HA ]
                                                | exact HAA | apply (lift_exp_ge _ _ _ _ lA'); [ lia | exact HA' ] ].
      + right; intros H; apply HnAA.
        destruct (ext_eq_ass_inv _ _ _ _ _ _ _ H) as (i & _ & _ & HAA & _).
        eapply typ_eq_at_level; [ exact HAA | apply (lift_exp_ge _ _ _ _ lA); [ lia | exact HA ]
                                | apply (lift_exp_ge _ _ _ _ lA''); [ lia | exact HA'' ] ].
  Defined.

  (** Subtyping: both sides types, then the algorithmic check. *)
  Definition sub_dec (Γ : ctx) (A B : typ) : {Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ B} + {~ Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ B}.
  Proof.
    destruct (typ_least_dec Γ A) as [[lA [HA _]] | HnA];
      [| right; intros H; destruct (presup_subtyp_left H) as [i Hi]; exact (HnA _ Hi) ].
    destruct (typ_least_dec Γ B) as [[lB [HB _]] | HnB];
      [| right; intros H; destruct (presup_subtyp_right H) as [i Hi]; exact (HnB _ Hi) ].
    destruct (@subtyping_impl (gc_mk Θ Ξ) (fctx_none Θ Ξ) Γ A B
                (@subtyping_order_run (gc_mk Θ Ξ) Γ A B (typ_nbe_ty_order _ _ _ HA) (typ_nbe_ty_order _ _ _ HB))) as [Hs | Hns].
    - left; apply (@alg_subtyping_sound (gc_mk Θ Ξ) _ _ _ (Nat.max lA lB) Hs);
        [ apply (lift_exp_ge _ _ _ _ lA); [ lia | exact HA ] | apply (lift_exp_ge _ _ _ _ lB); [ lia | exact HB ] ].
    - right; intros H; exact (Hns (@alg_subtyping_complete (gc_mk Θ Ξ) _ _ _ H)).
  Defined.
End Judgments.

(** A decision of a property, read off the decision of an equivalent one:
    the two conversions, by instantiation. *)
Ltac dec_left H := left; intros; eapply H; eassumption.
Ltac dec_right H := let H' := fresh "H" in right; intros H'; apply H; intros; eapply H'; eassumption.

(** The lookups and the found values that name one thing name it once. *)
Ltac unify_found :=
  repeat match goal with
    | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst
    | H1 : ?f ?x = Some ?a, H2 : ?f ?x = Some ?b |- _ =>
        assert_fails (constr_eq a b); rewrite H1 in H2; injection H2; clear H2; intros; subst
    end.

(** A premise that holds vacuously, a lookup failing or two found values
    differing. *)
Ltac vacuous := left; intros; unify_found; congruence.

(** ** The Premises of the First Member, Decided

    [ind_nil_at], premise by premise.  The premises are named here, each
    the statement of [ind_nil_at]'s, and decided one at a time. *)

Section NilDecide.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.
  Variables (mp : qname) (D : ind_decl) (IsS : nat -> list exp).

  (** The uniform parameters end in the frames'. *)
  Definition uparams_suffix_dec : {Δ | ind_uparams D = Δ ++ gs_tele Ξ} + {forall Δ, ind_uparams D <> Δ ++ gs_tele Ξ}.
  Proof.
    destruct (Compare_dec.le_dec (List.length (gs_tele Ξ)) (List.length (ind_uparams D))) as [Hle | Hle];
      [| right; intros Δ HΔ; apply Hle; rewrite HΔ, List.length_app; lia ].
    destruct (list_eq_dec centry_eq_dec (List.skipn (List.length (ind_uparams D) - List.length (gs_tele Ξ)) (ind_uparams D))
                (gs_tele Ξ)) as [E | E].
    - left; exists (List.firstn (List.length (ind_uparams D) - List.length (gs_tele Ξ)) (ind_uparams D)).
      rewrite <- E at 2; symmetry; apply List.firstn_skipn.
    - right; intros Δ HΔ; apply E; rewrite HΔ, List.length_app, Nat.add_sub, List.skipn_app, List.skipn_all, Nat.sub_diag.
      reflexivity.
  Defined.

  (** The declared members come first. *)
  Definition order_ok_dec : {ind_order_ok D} + {~ ind_order_ok D}.
  Proof.
    destruct (members_dec D (fun k M => im_is_decl M = true <-> k < ind_ndecl D)) as [H | H].
    - intros k M _.
      destruct (bool_dec (im_is_decl M) true) as [Hd | Hd]; destruct (Compare_dec.lt_dec k (ind_ndecl D)) as [Hl | Hl];
        first [ left; split; intros; assumption | left; split; intros; contradiction
              | right; intros [H1 H2]; tauto ].
    - left; exact H.
    - right; exact H.
  Defined.

  (** The first member is declared, at [mp]. *)
  Definition first_member_dec : {M0 | ind_member D 0 = Some M0 /\ im_head M0 = mh_decl mp}
      + {forall M0, ~ (ind_member D 0 = Some M0 /\ im_head M0 = mh_decl mp)}.
  Proof.
    destruct (ind_member D 0) as [M0 |] eqn:H0; [| right; intros M0 [[=] _] ].
    destruct (im_head M0) as [pm | qc k Is vm] eqn:Hh; [| right; intros M0' [[= <-] Hh']; congruence ].
    destruct (qname_eq_dec pm mp) as [-> | Hne]; [ left; exists M0; split; [ reflexivity | exact Hh ] |].
    right; intros M0' [[= <-] Hh']; rewrite Hh in Hh'; injection Hh' as ->; contradiction.
  Defined.

  (** Each member's non-uniform parameters are assumptions. *)
  Definition nparams_ass_dec :
    {forall k Mk, ind_member D k = Some Mk -> tele_ass (im_nparams Mk)}
    + {~ forall k Mk, ind_member D k = Some Mk -> tele_ass (im_nparams Mk)} :=
    members_dec D (fun _ Mk => tele_ass (im_nparams Mk)) (fun _ Mk _ => tele_ass_dec (im_nparams Mk)).

  (** Each member's constructor names are distinct. *)
  Definition members_nodup_dec :
    {forall k Mk, ind_member D k = Some Mk -> List.NoDup (List.map fst (im_cons Mk))}
    + {~ forall k Mk, ind_member D k = Some Mk -> List.NoDup (List.map fst (im_cons Mk))} :=
    members_dec D (fun _ Mk => List.NoDup (List.map fst (im_cons Mk))) (fun _ Mk _ => nodup_dec (List.map fst (im_cons Mk))).

  (** Each non-uniform parameter is in the sort. *)
  Definition nparams_sort_dec :
    {forall k Mk Δ1 T Δ2, ind_member D k = Some Mk -> im_nparams Mk = Δ1 ++ ce_ass T :: Δ2 ->
       Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ}
    + {~ forall k Mk Δ1 T Δ2, ind_member D k = Some Mk -> im_nparams Mk = Δ1 ++ ce_ass T :: Δ2 ->
       Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ}.
  Proof.
    destruct (members_dec D (fun _ Mk => forall Δ1 e Δ2, im_nparams Mk = Δ1 ++ e :: Δ2 -> forall T, e = ce_ass T ->
                Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ)) as [H | H].
    - intros k Mk _; apply forall_split_dec; intros Δ1 [T | T M | U | T M U] Δ2 _; [| left; intros ? [=] .. ].
      destruct (check_exp_at Θ Ξ HΞ (Δ2 ++ ind_uparams D) (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ T) as [HT | HT];
        [ left; intros ? [= <-]; exact HT | right; intros H; exact (HT (H T eq_refl)) ].
    - left; intros k Mk Δ1 T Δ2 Hk E; exact (H k Mk Hk Δ1 _ Δ2 E T eq_refl).
    - right; intros H'; apply H; intros k Mk Hk Δ1 e Δ2 E T ->; exact (H' k Mk Δ1 T Δ2 Hk E).
  Defined.

  (** Each non-recursive argument is in the sort. *)
  Definition args_sort_dec :
    {forall k Mk c gs gs1 A gs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_arg A :: gs2 ->
       Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ im_params D Mk ⊢ A : (ind_sort D)[wk_shiftn (List.length (cargs_strat gs1) + im_nn Mk)]ʷ}
    + {~ forall k Mk c gs gs1 A gs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_arg A :: gs2 ->
       Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ im_params D Mk ⊢ A : (ind_sort D)[wk_shiftn (List.length (cargs_strat gs1) + im_nn Mk)]ʷ}.
  Proof.
    destruct (members_dec D (fun _ Mk => forall cg, In cg (im_cons Mk) -> forall gs1 g gs2, snd cg = gs1 ++ g :: gs2 ->
                forall A, g = ca_arg A ->
                Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ im_params D Mk
                  ⊢ A : (ind_sort D)[wk_shiftn (List.length (cargs_strat gs1) + im_nn Mk)]ʷ)) as [H | H].
    - intros k Mk _; apply forall_in_dec; intros cg _; apply forall_split_dec; intros gs1 [A | t] gs2 _; [| left; intros ? [=] ].
      destruct (check_exp_at Θ Ξ HΞ (cargs_strat gs1 ++ im_params D Mk)
                  (ind_sort D)[wk_shiftn (List.length (cargs_strat gs1) + im_nn Mk)]ʷ A) as [HA | HA];
        [ left; intros ? [= <-]; exact HA | right; intros H; exact (HA (H A eq_refl)) ].
    - left; intros k Mk c gs gs1 A gs2 Hk Hin E; exact (H k Mk Hk (c, gs) Hin gs1 _ gs2 E A eq_refl).
    - right; intros H'; apply H; intros k Mk Hk [c gs] Hin gs1 g gs2 E A ->; exact (H' k Mk c gs gs1 A gs2 Hk Hin E).
  Defined.

  (** Each domain of a recursive argument's shape is in the sort. *)
  Definition doms_sort_dec :
    {forall k Mk c gs gs1 t gs2 Bs1 B Bs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) ->
       gs = gs1 ++ ca_rec t :: gs2 -> ptyp_doms t = Bs1 ++ B :: Bs2 ->
       Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ cargs_strat gs1 ++ im_params D Mk
         ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_strat gs1) + im_nn Mk)]ʷ}
    + {~ forall k Mk c gs gs1 t gs2 Bs1 B Bs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) ->
       gs = gs1 ++ ca_rec t :: gs2 -> ptyp_doms t = Bs1 ++ B :: Bs2 ->
       Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ cargs_strat gs1 ++ im_params D Mk
         ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_strat gs1) + im_nn Mk)]ʷ}.
  Proof.
    destruct (members_dec D (fun _ Mk => forall cg, In cg (im_cons Mk) -> forall gs1 g gs2, snd cg = gs1 ++ g :: gs2 ->
                forall t, g = ca_rec t -> forall Bs1 B Bs2, ptyp_doms t = Bs1 ++ B :: Bs2 ->
                Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ cargs_strat gs1 ++ im_params D Mk
                  ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_strat gs1) + im_nn Mk)]ʷ)) as [H | H].
    - intros k Mk _; apply forall_in_dec; intros cg _; apply forall_split_dec; intros gs1 [A | t] gs2 _; [ left; intros ? [=] |].
      destruct (forall_split_dec (ptyp_doms t)
                  (fun Bs1 B Bs2 => Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ cargs_strat gs1 ++ im_params D Mk
                     ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_strat gs1) + im_nn Mk)]ʷ))
        as [HB | HB].
      + intros Bs1 B Bs2 _.
        exact (check_exp_at Θ Ξ HΞ (doms_ctx Bs1 ++ cargs_strat gs1 ++ im_params D Mk)
                 (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_strat gs1) + im_nn Mk)]ʷ B).
      + left; intros ? [= <-]; exact HB.
      + right; intros H; exact (HB (H t eq_refl)).
    - left; intros k Mk c gs gs1 t gs2 Bs1 B Bs2 Hk Hin E Ed; exact (H k Mk Hk (c, gs) Hin gs1 _ gs2 E t eq_refl Bs1 B Bs2 Ed).
    - right; intros H'; apply H; intros k Mk Hk [c gs] Hin gs1 g gs2 E t -> Bs1 B Bs2 Ed;
        exact (H' k Mk c gs gs1 t gs2 Bs1 B Bs2 Hk Hin E Ed).
  Defined.

  (** Each recursive argument gives its member as many parameters as it
      has. *)
  Definition plen_dec :
    {forall k Mk c gs, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> cargs_plen D gs}
    + {~ forall k Mk c gs, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> cargs_plen D gs}.
  Proof.
    destruct (members_dec D (fun _ Mk => forall cg, In cg (im_cons Mk) -> cargs_plen D (snd cg))) as [H | H].
    - intros k Mk _; apply forall_in_dec; intros cg _; unfold cargs_plen.
      destruct (forall_split_dec (snd cg) (fun gs1 g gs2 => forall t, g = ca_rec t ->
                  exists Mj, ind_member D (ptyp_mem t) = Some Mj /\ List.length (ptyp_ps t) = im_nn Mj)) as [Hs | Hs].
      + intros gs1 [A | t] gs2 _; [ left; intros ? [=] |].
        destruct (ind_member D (ptyp_mem t)) as [Mj |] eqn:Hj;
          [| right; intros H; destruct (H t eq_refl) as (Mj' & Hj' & _); rewrite Hj in Hj'; discriminate ].
        destruct (Nat.eq_dec (List.length (ptyp_ps t)) (im_nn Mj)) as [E | E].
        * left; intros ? [= <-]; exists Mj; split; assumption.
        * right; intros H; destruct (H t eq_refl) as (Mj' & Hj' & E'); rewrite Hj in Hj'; injection Hj' as <-; contradiction.
      + left; intros gs1 t gs2 E; exact (Hs gs1 _ gs2 E t eq_refl).
      + right; intros H; apply Hs; intros gs1 g gs2 E t ->; exact (H gs1 t gs2 E).
    - left; intros k Mk c gs Hk Hin; exact (H k Mk Hk (c, gs) Hin).
    - right; intros H'; apply H; intros k Mk Hk [c gs] Hin; exact (H' k Mk c gs Hk Hin).
  Defined.

  (** Each parameter of a recursive argument is typed at its member's
      non-uniform telescope. *)
  Definition rec_ps_dec :
    {forall k Mk c gs gs1 t gs2 Mj j P T, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) ->
       gs = gs1 ++ ca_rec t :: gs2 -> ind_member D (ptyp_mem t) = Some Mj ->
       nth_error (ptyp_ps t) j = Some P ->
       nth_error (tele_insts (im_nparams Mj)
                    (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_strat gs1) + im_nn Mk))) (ptyp_ps t)) j
         = Some T ->
       Θ ⍮ Ξ ⍮ ptyp_tele t ++ cargs_strat gs1 ++ im_params D Mk ⊢ P : T}
    + {~ forall k Mk c gs gs1 t gs2 Mj j P T, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) ->
       gs = gs1 ++ ca_rec t :: gs2 -> ind_member D (ptyp_mem t) = Some Mj ->
       nth_error (ptyp_ps t) j = Some P ->
       nth_error (tele_insts (im_nparams Mj)
                    (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_strat gs1) + im_nn Mk))) (ptyp_ps t)) j
         = Some T ->
       Θ ⍮ Ξ ⍮ ptyp_tele t ++ cargs_strat gs1 ++ im_params D Mk ⊢ P : T}.
  Proof.
    destruct (members_dec D (fun _ Mk => forall cg, In cg (im_cons Mk) -> forall gs1 g gs2, snd cg = gs1 ++ g :: gs2 ->
                forall t, g = ca_rec t -> forall Mj, ind_member D (ptyp_mem t) = Some Mj ->
                forall j P T, nth_error (ptyp_ps t) j = Some P ->
                nth_error (tele_insts (im_nparams Mj)
                             (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_strat gs1) + im_nn Mk))) (ptyp_ps t)) j
                  = Some T ->
                Θ ⍮ Ξ ⍮ ptyp_tele t ++ cargs_strat gs1 ++ im_params D Mk ⊢ P : T)) as [H | H].
    - intros k Mk _; apply forall_in_dec; intros cg _; apply forall_split_dec; intros gs1 [A | t] gs2 _; [ left; intros ? [=] |].
      destruct (ind_member D (ptyp_mem t)) as [Mj |] eqn:Hj; [| left; intros ? [= <-] Mj' Hj'; rewrite Hj in Hj'; discriminate ].
      destruct (forall_nth2_dec (fun P T => Θ ⍮ Ξ ⍮ ptyp_tele t ++ cargs_strat gs1 ++ im_params D Mk ⊢ P : T)
                  (fun P T => check_exp_at Θ Ξ HΞ (ptyp_tele t ++ cargs_strat gs1 ++ im_params D Mk) T P) (ptyp_ps t)
                  (tele_insts (im_nparams Mj)
                     (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_strat gs1) + im_nn Mk))) (ptyp_ps t)))
        as [HP | HP].
      + left; intros ? [= <-] Mj' Hj'; rewrite Hj in Hj'; injection Hj' as <-; exact HP.
      + right; intros H; exact (HP (H t eq_refl Mj Hj)).
    - left; intros k Mk c gs gs1 t gs2 Mj j P T Hk Hin E Hj HP HT; exact (H k Mk Hk (c, gs) Hin gs1 _ gs2 E t eq_refl Mj Hj j P T HP HT).
    - right; intros H'; apply H; intros k Mk Hk [c gs] Hin gs1 g gs2 E t -> Mj Hj j P T HP HT;
        exact (H' k Mk c gs gs1 t gs2 Mj j P T Hk Hin E Hj HP HT).
  Defined.

  (** The correspondence of a view's arguments with its container's,
      computed. *)
  Definition cargs_corr_dec (vm : list nat) (gs' gs : list carg) : {cargs_corr vm gs' gs} + {~ cargs_corr vm gs' gs} :=
    match cargs_corrb vm gs' gs as b return cargs_corrb vm gs' gs = b -> _ with
    | true => fun E => left (cargs_corrb_sound _ _ _ E)
    | false => fun E => right (fun H => diff_false_true (eq_trans (eq_sym E) (cargs_corrb_complete _ _ _ H)))
    end eq_refl.

  (** Each view is of a declared member of a filed group, at as many
      uniform arguments as it has, with a map of one entry per container
      member taking the viewed member to the view, and the viewed member's
      constructors, their arguments corresponding. *)
  Definition views_exist_dec :
    {forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       exists D' Mk', ind_lookup Θ Ξ qc = Some D' /\ ind_member D' k' = Some Mk' /\ k' < ind_ndecl D' /\
         List.length Is = ind_nu D' /\ List.length vm = List.length (ind_members D') /\
         List.nth_error vm k' = Some k /\
         List.map fst (im_cons Mk) = List.map fst (im_cons Mk') /\
         (forall c gs' gs, ind_con Mk' c = Some gs' -> ind_con Mk c = Some gs -> cargs_corr vm gs' gs)}
    + {~ forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       exists D' Mk', ind_lookup Θ Ξ qc = Some D' /\ ind_member D' k' = Some Mk' /\ k' < ind_ndecl D' /\
         List.length Is = ind_nu D' /\ List.length vm = List.length (ind_members D') /\
         List.nth_error vm k' = Some k /\
         List.map fst (im_cons Mk) = List.map fst (im_cons Mk') /\
         (forall c gs' gs, ind_con Mk' c = Some gs' -> ind_con Mk c = Some gs -> cargs_corr vm gs' gs)}.
  Proof.
    apply views_dec; intros k Mk qc k' Is vm Hk Hh.
    Local Ltac views_exist_rej :=
      let H := fresh "H" in
      right; intros H; destruct H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?); unify_found; first [ contradiction | congruence ].
    destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| views_exist_rej ].
    destruct (ind_member D' k') as [Mk' |] eqn:Hk'; [| views_exist_rej ].
    destruct (Compare_dec.lt_dec k' (ind_ndecl D')) as [Hlt | Hlt]; [| views_exist_rej ].
    destruct (Nat.eq_dec (List.length Is) (ind_nu D')) as [HIs | HIs]; [| views_exist_rej ].
    destruct (Nat.eq_dec (List.length vm) (List.length (ind_members D'))) as [Hvm | Hvm]; [| views_exist_rej ].
    destruct (option_nat_eq_dec (List.nth_error vm k') (Some k)) as [Hvk | Hvk]; [| views_exist_rej ].
    destruct (list_eq_dec string_dec (List.map fst (im_cons Mk)) (List.map fst (im_cons Mk'))) as [Hn | Hn];
      [| views_exist_rej ].
    destruct (con_pairs_dec Mk' Mk (fun _ gs' gs => cargs_corr vm gs' gs) (fun _ gs' gs _ _ => cargs_corr_dec vm gs' gs))
      as [Hc | Hc]; [| views_exist_rej ].
    left; exists D', Mk'; repeat split; assumption.
  Defined.

  (** Each view's instance is [IsS] with the members as variables. *)
  Definition link_dec :
    {forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       Is = List.map (fun I => I[grp_sb mp D]) (IsS k)}
    + {~ forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       Is = List.map (fun I => I[grp_sb mp D]) (IsS k)}.
  Proof. apply views_dec; intros k Mk qc k' Is vm _ _; apply (list_eq_dec exp_eq_dec). Defined.

  (** Each instance argument is typed at the container's uniform
      telescope, over the members as variables. *)
  Definition iss_typed_dec :
    {forall k Mk qc k' Is vm D' j I T, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> nth_error (IsS k) j = Some I ->
       nth_error (tele_insts (ind_uparams D') Id (IsS k)) j = Some T ->
       Θ ⍮ Ξ ⍮ grp_sctx D ⊢ I : T}
    + {~ forall k Mk qc k' Is vm D' j I T, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> nth_error (IsS k) j = Some I ->
       nth_error (tele_insts (ind_uparams D') Id (IsS k)) j = Some T ->
       Θ ⍮ Ξ ⍮ grp_sctx D ⊢ I : T}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall j I T, nth_error (IsS k) j = Some I -> nth_error (tele_insts (ind_uparams D') Id (IsS k)) j = Some T ->
                Θ ⍮ Ξ ⍮ grp_sctx D ⊢ I : T)) as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| left; intros ? [=] ].
      destruct (forall_nth2_dec (fun I T => Θ ⍮ Ξ ⍮ grp_sctx D ⊢ I : T) (fun I T => check_exp_at Θ Ξ HΞ (grp_sctx D) T I)
                  (IsS k) (tele_insts (ind_uparams D') Id (IsS k))) as [HI | HI];
        [ left; intros ? [= <-]; exact HI | right; intros H; exact (HI (H _ eq_refl)) ].
    - dec_left H.
    - dec_right H.
  Defined.

  (** A view maps a declared container member to a view of that member at
      the same instance. *)
  Definition decl_maps_dec :
    {forall k Mk qc k' Is vm D' i' Mi' v pm', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_decl pm' ->
       nth_error vm i' = Some v ->
       exists Mv vm', ind_member D v = Some Mv /\ im_head Mv = mh_view qc i' Is vm'}
    + {~ forall k Mk qc k' Is vm D' i' Mi' v pm', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_decl pm' ->
       nth_error vm i' = Some v ->
       exists Mv vm', ind_member D v = Some Mv /\ im_head Mv = mh_view qc i' Is vm'}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall i' Mi', ind_member D' i' = Some Mi' -> forall pm', im_head Mi' = mh_decl pm' ->
                forall v, nth_error vm i' = Some v ->
                exists Mv vm', ind_member D v = Some Mv /\ im_head Mv = mh_view qc i' Is vm')) as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| left; intros ? [=] ].
      destruct (members_dec D' (fun i' Mi' => forall pm', im_head Mi' = mh_decl pm' -> forall v, nth_error vm i' = Some v ->
                  exists Mv vm', ind_member D v = Some Mv /\ im_head Mv = mh_view qc i' Is vm')) as [HM | HM].
      + intros i' Mi' _.
        destruct (im_head Mi') as [pm' | q2 k2 Is2 vm2] eqn:Hh'; [| left; intros ? [=] ].
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| left; intros ? _ ? [=] ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv;
          [| right; intros H; destruct (H pm' eq_refl v eq_refl) as (? & ? & Hm & _); rewrite Hmv in Hm; discriminate ].
        destruct (im_head Mv) as [pmv | qv kv Iv vmv] eqn:Hhv;
          [ right; intros H; destruct (H pm' eq_refl v eq_refl) as (? & ? & Hm & Hhm); rewrite Hmv in Hm; injection Hm as <-;
            congruence |].
        destruct (qname_eq_dec qv qc) as [-> | Hq];
          [| right; intros H; destruct (H pm' eq_refl v eq_refl) as (? & ? & Hm & Hhm); rewrite Hmv in Hm; injection Hm as <-;
             rewrite Hhv in Hhm; injection Hhm; intros; contradiction ].
        destruct (Nat.eq_dec kv i') as [-> | Hk2];
          [| right; intros H; destruct (H pm' eq_refl v eq_refl) as (? & ? & Hm & Hhm); rewrite Hmv in Hm; injection Hm as <-;
             rewrite Hhv in Hhm; injection Hhm; intros; contradiction ].
        destruct (list_eq_dec exp_eq_dec Iv Is) as [-> | HI];
          [| right; intros H; destruct (H pm' eq_refl v eq_refl) as (? & ? & Hm & Hhm); rewrite Hmv in Hm; injection Hm as <-;
             rewrite Hhv in Hhm; injection Hhm; intros; contradiction ].
        left; intros ? _ ? [= <-]; exists Mv, vmv; split; [ exact Hmv | exact Hhv ].
      + left; intros ? [= <-]; exact HM.
      + right; intros H'; apply HM; exact (H' D' eq_refl).
    - dec_left H.
    - dec_right H.
  Defined.

  (** A view maps a container view to a view of the same member at as many
      arguments. *)
  Definition view_maps_len_dec :
    {forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' ->
       nth_error vm i' = Some v ->
       exists Mv X vm', ind_member D v = Some Mv /\ im_head Mv = mh_view q'' k'' X vm' /\ List.length X = List.length Is''}
    + {~ forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' ->
       nth_error vm i' = Some v ->
       exists Mv X vm', ind_member D v = Some Mv /\ im_head Mv = mh_view q'' k'' X vm' /\ List.length X = List.length Is''}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall i' Mi', ind_member D' i' = Some Mi' -> forall q'' k'' Is'' vm'', im_head Mi' = mh_view q'' k'' Is'' vm'' ->
                forall v, nth_error vm i' = Some v ->
                exists Mv X vm', ind_member D v = Some Mv /\ im_head Mv = mh_view q'' k'' X vm' /\
                  List.length X = List.length Is'')) as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| left; intros ? [=] ].
      destruct (members_dec D' (fun i' Mi' => forall q'' k'' Is'' vm'', im_head Mi' = mh_view q'' k'' Is'' vm'' ->
                  forall v, nth_error vm i' = Some v ->
                  exists Mv X vm', ind_member D v = Some Mv /\ im_head Mv = mh_view q'' k'' X vm' /\
                    List.length X = List.length Is'')) as [HM | HM].
      + intros i' Mi' _.
        destruct (im_head Mi') as [pm' | q2 k2 Is2 vm2] eqn:Hh'; [ left; intros ? ? ? ? [=] |].
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| left; intros ? ? ? ? _ ? [=] ].
        Local Ltac view_maps_len_rej Hmv Hhv :=
          let H := fresh "H" in
          right; intros H; destruct (H _ _ _ _ eq_refl _ eq_refl) as (? & ? & ? & Hm & Hhm & Hlen);
          rewrite Hmv in Hm; try (injection Hm as <-; rewrite Hhv in Hhm; injection Hhm; intros; subst); first [ discriminate | contradiction | congruence ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv; [| right; intros H; destruct (H _ _ _ _ eq_refl _ eq_refl) as (? & ? & ? & Hm & _);
                                                            rewrite Hmv in Hm; discriminate ].
        destruct (im_head Mv) as [pmv | qv kv Iv vmv] eqn:Hhv;
          [ right; intros H; destruct (H _ _ _ _ eq_refl _ eq_refl) as (? & ? & ? & Hm & Hhm & _); rewrite Hmv in Hm;
            injection Hm as <-; congruence |].
        destruct (qname_eq_dec qv q2) as [-> | Hq];
          [| right; intros H; destruct (H _ _ _ _ eq_refl _ eq_refl) as (? & ? & ? & Hm & Hhm & _); rewrite Hmv in Hm;
             injection Hm as <-; rewrite Hhv in Hhm; injection Hhm; intros; contradiction ].
        destruct (Nat.eq_dec kv k2) as [-> | Hk2];
          [| right; intros H; destruct (H _ _ _ _ eq_refl _ eq_refl) as (? & ? & ? & Hm & Hhm & _); rewrite Hmv in Hm;
             injection Hm as <-; rewrite Hhv in Hhm; injection Hhm; intros; contradiction ].
        destruct (Nat.eq_dec (List.length Iv) (List.length Is2)) as [HL | HL];
          [| right; intros H; destruct (H _ _ _ _ eq_refl _ eq_refl) as (? & ? & ? & Hm & Hhm & HL'); rewrite Hmv in Hm;
             injection Hm as <-; rewrite Hhv in Hhm; injection Hhm; intros; subst; contradiction ].
        left; intros ? ? ? ? [= <- <- <- <-] ? [= <-]; exists Mv, Iv, vmv; repeat split; assumption.
      + left; intros ? [= <-]; exact HM.
      + right; intros H'; apply HM; exact (H' D' eq_refl).
    - dec_left H.
    - dec_right H.
  Defined.

  (** The view a view maps a container view to has the container view's
      arguments at this view's instance. *)
  Definition view_is_eq_dec :
    {forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm' j' C C' T,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' ->
       ind_lookup Θ Ξ q'' = Some D'' ->
       nth_error vm i' = Some v -> ind_member D v = Some Mv -> im_head Mv = mh_view q'' k'' X vm' ->
       nth_error (IsS v) j' = Some C ->
       nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
       nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T ->
       Θ ⍮ Ξ ⍮ grp_sctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)]}
    + {~ forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm' j' C C' T,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' ->
       ind_lookup Θ Ξ q'' = Some D'' ->
       nth_error vm i' = Some v -> ind_member D v = Some Mv -> im_head Mv = mh_view q'' k'' X vm' ->
       nth_error (IsS v) j' = Some C ->
       nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
       nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T ->
       Θ ⍮ Ξ ⍮ grp_sctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)]}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall i' Mi', ind_member D' i' = Some Mi' -> forall q'' k'' Is'' vm'', im_head Mi' = mh_view q'' k'' Is'' vm'' ->
                forall D'', ind_lookup Θ Ξ q'' = Some D'' -> forall v, nth_error vm i' = Some v ->
                forall Mv, ind_member D v = Some Mv -> forall X vm', im_head Mv = mh_view q'' k'' X vm' ->
                forall j' C C' T, nth_error (IsS v) j' = Some C ->
                nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
                nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T ->
                Θ ⍮ Ξ ⍮ grp_sctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)])) as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| left; intros ? [=] ].
      destruct (members_dec D' (fun i' Mi' => forall q'' k'' Is'' vm'', im_head Mi' = mh_view q'' k'' Is'' vm'' ->
                  forall D'', ind_lookup Θ Ξ q'' = Some D'' -> forall v, nth_error vm i' = Some v ->
                  forall Mv, ind_member D v = Some Mv -> forall X vm', im_head Mv = mh_view q'' k'' X vm' ->
                  forall j' C C' T, nth_error (IsS v) j' = Some C ->
                  nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
                  nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T ->
                  Θ ⍮ Ξ ⍮ grp_sctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)])) as [HM | HM].
      + intros i' Mi' _.
        destruct (im_head Mi') as [pm' | q2 k2 Is2 vm2] eqn:Hh'; [ vacuous |].
        destruct (ind_lookup Θ Ξ q2) as [D2 |] eqn:Hl2; [| vacuous ].
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| vacuous ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv; [| vacuous ].
        destruct (im_head Mv) as [pmv | qv kv Iv vmv] eqn:Hhv; [ vacuous |].
        destruct (qname_eq_dec qv q2) as [-> | Hq]; [| vacuous ].
        destruct (Nat.eq_dec kv k2) as [-> | Hk2]; [| vacuous ].
        destruct (forall_nth3_dec (fun C C' T => Θ ⍮ Ξ ⍮ grp_sctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)])
                    (fun C C' T => eq_at_dec Θ Ξ HΞ (grp_sctx D) T[sb_of_list Id (IsS k)] C C')
                    (IsS v) (List.map (fun I => I[sb_of_list Id (IsS k)]) Is2) (tele_insts (ind_uparams D2) Id Is2))
          as [HC | HC].
        * left; intros ? ? ? ? [= <- <- <- <-] D2' Hl2' v' Hv' Mv' Hmv' X vm' Hhv'; unify_found; intros; eapply HC; eassumption.
        * right; intros H; exact (HC (H _ _ _ _ eq_refl _ Hl2 _ eq_refl _ Hmv _ _ Hhv)).
      + left; intros ? [= <-]; exact HM.
      + right; intros H'; apply HM; exact (H' D' eq_refl).
    - dec_left H.
    - dec_right H.
  Defined.

  (** A mapped member's non-uniform parameters are the container
      member's at the instance. *)
  Definition nparams_eq_dec (HPass : forall k Mk, ind_member D k = Some Mk -> tele_ass (im_nparams Mk)) :
    {forall k Mk qc k' Is vm D' i' Mi' v Mv, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv ->
       Θ ⍮ Ξ ⍮ grp_sctx D ⊢ˣ tele_wk (im_nparams Mv) (self_wk D 0) ≈ tele_sub (im_nparams Mi') (sb_of_list Id (IsS k))}
    + {~ forall k Mk qc k' Is vm D' i' Mi' v Mv, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv ->
       Θ ⍮ Ξ ⍮ grp_sctx D ⊢ˣ tele_wk (im_nparams Mv) (self_wk D 0) ≈ tele_sub (im_nparams Mi') (sb_of_list Id (IsS k))}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall i' Mi', ind_member D' i' = Some Mi' -> forall v, nth_error vm i' = Some v ->
                forall Mv, ind_member D v = Some Mv ->
                Θ ⍮ Ξ ⍮ grp_sctx D ⊢ˣ tele_wk (im_nparams Mv) (self_wk D 0) ≈ tele_sub (im_nparams Mi') (sb_of_list Id (IsS k))))
      as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| left; intros ? [=] ].
      destruct (members_dec D' (fun i' Mi' => forall v, nth_error vm i' = Some v -> forall Mv, ind_member D v = Some Mv ->
                  Θ ⍮ Ξ ⍮ grp_sctx D ⊢ˣ tele_wk (im_nparams Mv) (self_wk D 0)
                    ≈ tele_sub (im_nparams Mi') (sb_of_list Id (IsS k)))) as [HM | HM].
      + intros i' Mi' _.
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| left; intros ? [=] ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv; [| vacuous ].
        destruct (ext_eq_dec Θ Ξ HΞ (grp_sctx D) (tele_wk (im_nparams Mv) (self_wk D 0))
                    (tele_sub (im_nparams Mi') (sb_of_list Id (IsS k))) (tele_ass_wk _ _ (HPass _ _ Hmv))) as [HE | HE];
          [ left; intros; unify_found; exact HE | right; intros H; exact (HE (H _ eq_refl _ Hmv)) ].
      + left; intros ? [= <-]; exact HM.
      + right; intros H'; apply HM; exact (H' D' eq_refl).
    - dec_left H.
    - dec_right H.
  Defined.

  (** A mapped member's constructor arguments are the container member's
      at the instance. *)
  Definition cargs_eq_dec :
    {forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       Θ ⍮ Ξ ⍮ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
         ⊢ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id (IsS k))) ≈ scargs_ctx D IsS Mv gs}
    + {~ forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       Θ ⍮ Ξ ⍮ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
         ⊢ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id (IsS k))) ≈ scargs_ctx D IsS Mv gs}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall i' Mi', ind_member D' i' = Some Mi' -> forall v, nth_error vm i' = Some v ->
                forall Mv, ind_member D v = Some Mv -> forall c gs' gs, ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
                Θ ⍮ Ξ ⍮ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
                  ⊢ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id (IsS k))) ≈ scargs_ctx D IsS Mv gs))
      as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| left; intros ? [=] ].
      destruct (members_dec D' (fun i' Mi' => forall v, nth_error vm i' = Some v -> forall Mv, ind_member D v = Some Mv ->
                  forall c gs' gs, ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
                  Θ ⍮ Ξ ⍮ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
                    ⊢ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id (IsS k))) ≈ scargs_ctx D IsS Mv gs))
        as [HM | HM].
      + intros i' Mi' _.
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| left; intros ? [=] ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv; [| vacuous ].
        destruct (con_pairs_dec Mi' Mv (fun c gs' gs => Θ ⍮ Ξ ⍮ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
                    ⊢ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id (IsS k))) ≈ scargs_ctx D IsS Mv gs))
          as [HC | HC].
        * intros c gs' gs _ _.
          exact (ext_eq_dec Θ Ξ HΞ _ _ _ (tele_ass_sub _ _ (cargs_ctx_aux_ass _ _ _ _ _))).
        * left; intros; unify_found; eapply HC; eauto.
        * right; intros H; exact (HC (H _ eq_refl _ Hmv)).
      + left; intros ? [= <-]; exact HM.
      + right; intros H'; apply HM; exact (H' D' eq_refl).
    - dec_left H.
    - dec_right H.
  Defined.

  (** A property at every argument recursive both in a view's container
      member and in the member the view takes it to, decided at each: the
      view [k] of the container at [qc], [D'], its member [Mi'], taken to
      [Mv], at a constructor both have, the recursive arguments [t'] and [t]
      after [gs1'] and [gs1]. *)
  Definition view_rec_pairs_dec
      (Q : nat -> qname -> ind_decl -> imember -> imember -> list carg -> ptyp -> list carg -> ptyp -> Prop)
      (f : forall k qc D' Mi' Mv gs1' t' gs1 t, {Q k qc D' Mi' Mv gs1' t' gs1 t} + {~ Q k qc D' Mi' Mv gs1' t' gs1 t}) :
    {forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       Q k qc D' Mi' Mv gs1' t' gs1 t}
    + {~ forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       Q k qc D' Mi' Mv gs1' t' gs1 t}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall i' Mi', ind_member D' i' = Some Mi' -> forall v, nth_error vm i' = Some v ->
                forall Mv, ind_member D v = Some Mv -> forall c gs' gs, ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
                forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
                List.length gs1' = List.length gs1 -> Q k qc D' Mi' Mv gs1' t' gs1 t)) as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| vacuous ].
      destruct (members_dec D' (fun i' Mi' => forall v, nth_error vm i' = Some v -> forall Mv, ind_member D v = Some Mv ->
                  forall c gs' gs, ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
                  forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
                  List.length gs1' = List.length gs1 -> Q k qc D' Mi' Mv gs1' t' gs1 t)) as [HM | HM].
      + intros i' Mi' _.
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| vacuous ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv; [| vacuous ].
        destruct (con_pairs_dec Mi' Mv (fun c gs' gs => forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' ->
                    gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 -> Q k qc D' Mi' Mv gs1' t' gs1 t))
          as [HC | HC].
        * intros c gs' gs _ _.
          exact (rec_pairs_dec gs' gs (fun gs1' t' _ gs1 t _ => Q k qc D' Mi' Mv gs1' t' gs1 t) (fun _ _ _ _ _ _ _ _ _ => f _ _ _ _ _ _ _ _ _)).
        * left; intros; unify_found; eapply HC; eauto.
        * right; intros H; apply HC; intros; eapply H; eauto.
      + left; intros; unify_found; eapply HM; eauto.
      + right; intros H'; apply HM; intros; eapply H'; eauto.
    - dec_left H.
    - dec_right H.
  Defined.

  (** The same with one bound. *)
  Definition view_rec_pairs_bound_dec
      (Q : nat -> qname -> ind_decl -> imember -> imember -> list carg -> ptyp -> list carg -> ptyp -> nat -> Prop)
      (Hmono : forall k qc D' Mi' Mv gs1' t' gs1 t l l', l <= l' -> Q k qc D' Mi' Mv gs1' t' gs1 t l -> Q k qc D' Mi' Mv gs1' t' gs1 t l')
      (f : forall k qc D' Mi' Mv gs1' t' gs1 t,
         {l | Q k qc D' Mi' Mv gs1' t' gs1 t l} + {forall l, ~ Q k qc D' Mi' Mv gs1' t' gs1 t l}) :
    {l | forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       Q k qc D' Mi' Mv gs1' t' gs1 t l}
    + {forall l, ~ forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       Q k qc D' Mi' Mv gs1' t' gs1 t l}.
  Proof.
    destruct (views_bound_dec D (fun k Mk qc k' Is vm l => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall i' Mi', ind_member D' i' = Some Mi' -> forall v, nth_error vm i' = Some v ->
                forall Mv, ind_member D v = Some Mv -> forall c gs' gs, ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
                forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
                List.length gs1' = List.length gs1 -> Q k qc D' Mi' Mv gs1' t' gs1 t l)) as [[l H] | H].
    - intros ? ? ? ? ? ? ? ? Hle HQ; intros; eapply Hmono; [ exact Hle | eapply HQ; eassumption ].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| left; exists 0; intros; unify_found; congruence ].
      destruct (members_bound_dec D' (fun i' Mi' l => forall v, nth_error vm i' = Some v -> forall Mv, ind_member D v = Some Mv ->
                  forall c gs' gs, ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
                  forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 ->
                  List.length gs1' = List.length gs1 -> Q k qc D' Mi' Mv gs1' t' gs1 t l)) as [[l HM] | HM].
      + intros ? ? ? ? Hle HQ; intros; eapply Hmono; [ exact Hle | eapply HQ; eassumption ].
      + intros i' Mi' _.
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| left; exists 0; intros; unify_found; congruence ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv; [| left; exists 0; intros; unify_found; congruence ].
        destruct (con_pairs_bound_dec Mi' Mv (fun c gs' gs l => forall gs1' t' gs2' gs1 t gs2, gs' = gs1' ++ ca_rec t' :: gs2' ->
                    gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 -> Q k qc D' Mi' Mv gs1' t' gs1 t l))
          as [[l HC] | HC].
        * intros ? ? ? ? ? Hle HQ; intros; eapply Hmono; [ exact Hle | eapply HQ; eassumption ].
        * intros c gs' gs _ _.
          exact (rec_pairs_bound_dec gs' gs (fun gs1' t' _ gs1 t _ l => Q k qc D' Mi' Mv gs1' t' gs1 t l)
                   (fun _ _ _ _ _ _ _ _ Hle HQ => Hmono _ _ _ _ _ _ _ _ _ _ _ Hle HQ)
                   (fun _ _ _ _ _ _ _ _ _ => f _ _ _ _ _ _ _ _ _)).
        * left; exists l; intros; unify_found; eapply HC; eauto.
        * right; intros l H; apply (HC l); intros; eapply H; eauto.
      + left; exists l; intros; unify_found; eapply HM; eauto.
      + right; intros l' H'; apply (HM l'); intros; eapply H'; eauto.
    - left; exists l; intros; eapply H; eauto.
    - right; intros l H'; apply (H l); intros; eapply H'; eauto.
  Defined.

  (** Each domain of the shapes of an argument recursive in both is the
      container's at the instance, at one universe. *)
  Definition doms_eq_bound_dec :
    {i | forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 d,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       d < ptyp_depth t ->
       Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t))) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
         ⊢ (ptyp_dom_at (cargs_pat gs1') d t')[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
         ≈ (ptyp_dom_at (cargs_pat gs1) d t)[self_wk D (d + List.length gs1 + im_nn Mv)]ʷ : Typeω@i}
    + {forall i, ~ forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 d,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       d < ptyp_depth t ->
       Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t))) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
         ⊢ (ptyp_dom_at (cargs_pat gs1') d t')[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
         ≈ (ptyp_dom_at (cargs_pat gs1) d t)[self_wk D (d + List.length gs1 + im_nn Mv)]ʷ : Typeω@i}.
  Proof.
    destruct (view_rec_pairs_bound_dec
                (fun k qc D' Mi' Mv gs1' t' gs1 t i => forall d, d < ptyp_depth t ->
                   Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t))) (self_wk D (List.length gs1 + im_nn Mv))
                             ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
                     ⊢ (ptyp_dom_at (cargs_pat gs1') d t')[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
                     ≈ (ptyp_dom_at (cargs_pat gs1) d t)[self_wk D (d + List.length gs1 + im_nn Mv)]ʷ : Typeω@i))
      as [[i H] | H].
    - intros ? ? ? ? ? ? ? ? ? ? ? Hle HQ d Hd; exact (lift_exp_eq_ge _ _ _ _ _ _ _ Hle (HQ d Hd)).
    - intros k qc D' Mi' Mv gs1' t' gs1 t.
      destruct (bound_in_dec (fun d i =>
                  Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t))) (self_wk D (List.length gs1 + im_nn Mv))
                            ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
                    ⊢ (ptyp_dom_at (cargs_pat gs1') d t')[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
                    ≈ (ptyp_dom_at (cargs_pat gs1) d t)[self_wk D (d + List.length gs1 + im_nn Mv)]ʷ : Typeω@i)
                  (fun d l l' Hle HQ => lift_exp_eq_ge _ _ _ _ _ _ _ Hle HQ) (List.seq 0 (ptyp_depth t))) as [[i HD] | HD].
      + intros d _; exact (typ_eq_least_dec Θ Ξ HΞ _ _ _).
      + left; exists i; intros d Hd; apply HD, List.in_seq; lia.
      + right; intros l Hl; apply (HD l); intros d Hd; apply List.in_seq in Hd; apply Hl; lia.
    - left; exists i; intros; eapply H; eauto.
    - right; intros l H'; apply (H l); intros; eapply H'; eauto.
  Defined.

  (** The non-uniform parameters of the members the shapes end in, typed
      and equal to the container's at the instance. *)
  Definition ps_typed_dec :
    {forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 Mj j P' P T,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       ind_member D (ptyp_mem t) = Some Mj ->
       nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P' -> nth_error (ptyp_ps_at (cargs_pat gs1) t) j = Some P ->
       nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                    (ptyp_ps_at (cargs_pat gs1) t)) j = Some T ->
       Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
         ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
         : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ}
    + {~ forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 Mj j P' P T,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       ind_member D (ptyp_mem t) = Some Mj ->
       nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P' -> nth_error (ptyp_ps_at (cargs_pat gs1) t) j = Some P ->
       nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                    (ptyp_ps_at (cargs_pat gs1) t)) j = Some T ->
       Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
         ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
         : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ}.
  Proof.
    destruct (view_rec_pairs_dec (fun k qc D' Mi' Mv gs1' t' gs1 t => forall Mj, ind_member D (ptyp_mem t) = Some Mj ->
                forall j P' P T, nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P' ->
                nth_error (ptyp_ps_at (cargs_pat gs1) t) j = Some P ->
                nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                             (ptyp_ps_at (cargs_pat gs1) t)) j = Some T ->
                Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                          ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
                  ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
                  : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ)) as [H | H].
    - intros k qc D' Mi' Mv gs1' t' gs1 t.
      destruct (ind_member D (ptyp_mem t)) as [Mj |] eqn:Hj; [| vacuous ].
      destruct (forall_nth3_dec
                  (fun P' P T => Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                                         ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
                     ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
                     : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ)
                  (fun P' P T => check_exp_at Θ Ξ HΞ _ _ _)
                  (ptyp_ps_at (cargs_pat gs1') t') (ptyp_ps_at (cargs_pat gs1) t)
                  (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                     (ptyp_ps_at (cargs_pat gs1) t))) as [HP | HP].
      + left; intros; unify_found; eapply HP; eauto.
      + right; intros H; apply HP; intros; eapply H; eauto.
    - dec_left H.
    - dec_right H.
  Defined.

  Definition ps_eq_dec :
    {forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 Mj j P' P T,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       ind_member D (ptyp_mem t) = Some Mj ->
       nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P' -> nth_error (ptyp_ps_at (cargs_pat gs1) t) j = Some P ->
       nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                    (ptyp_ps_at (cargs_pat gs1) t)) j = Some T ->
       Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
         ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
         ≈ P[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ
         : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ}
    + {~ forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 Mj j P' P T,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       ind_member D (ptyp_mem t) = Some Mj ->
       nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P' -> nth_error (ptyp_ps_at (cargs_pat gs1) t) j = Some P ->
       nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                    (ptyp_ps_at (cargs_pat gs1) t)) j = Some T ->
       Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
         ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
         ≈ P[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ
         : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ}.
  Proof.
    destruct (view_rec_pairs_dec (fun k qc D' Mi' Mv gs1' t' gs1 t => forall Mj, ind_member D (ptyp_mem t) = Some Mj ->
                forall j P' P T, nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P' ->
                nth_error (ptyp_ps_at (cargs_pat gs1) t) j = Some P ->
                nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                             (ptyp_ps_at (cargs_pat gs1) t)) j = Some T ->
                Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                          ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
                  ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
                  ≈ P[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ
                  : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ)) as [H | H].
    - intros k qc D' Mi' Mv gs1' t' gs1 t.
      destruct (ind_member D (ptyp_mem t)) as [Mj |] eqn:Hj; [| vacuous ].
      destruct (forall_nth3_dec
                  (fun P' P T => Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                                         ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
                     ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
                     ≈ P[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ
                     : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ)
                  (fun P' P T => eq_at_dec Θ Ξ HΞ _ _ _ _)
                  (ptyp_ps_at (cargs_pat gs1') t') (ptyp_ps_at (cargs_pat gs1) t)
                  (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                     (ptyp_ps_at (cargs_pat gs1) t))) as [HP | HP].
      + left; intros; unify_found; eapply HP; eauto.
      + right; intros H; apply HP; intros; eapply H; eauto.
    - dec_left H.
    - dec_right H.
  Defined.

  (** The sort of each view's container at the instance is in the
      group's. *)
  Definition sort_sub_dec :
    {forall k Mk qc k' Is vm D', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' ->
       Θ ⍮ Ξ ⍮ grp_sctx D ⊢ (ind_sort D')[sb_of_list Id (IsS k)] ⊆ (ind_sort D)[self_wk D 0]ʷ}
    + {~ forall k Mk qc k' Is vm D', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' ->
       Θ ⍮ Ξ ⍮ grp_sctx D ⊢ (ind_sort D')[sb_of_list Id (IsS k)] ⊆ (ind_sort D)[self_wk D 0]ʷ}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                Θ ⍮ Ξ ⍮ grp_sctx D ⊢ (ind_sort D')[sb_of_list Id (IsS k)] ⊆ (ind_sort D)[self_wk D 0]ʷ)) as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| left; intros ? [=] ].
      destruct (sub_dec Θ Ξ HΞ (grp_sctx D) (ind_sort D')[sb_of_list Id (IsS k)] (ind_sort D)[self_wk D 0]ʷ) as [HS | HS];
        [ left; intros ? [= <-]; exact HS | right; intros H; exact (HS (H _ eq_refl)) ].
    - dec_left H.
    - dec_right H.
  Defined.

  (** Each view's members are those of the container's group. *)
  Definition vwrap_dec :
    {forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       exists D', ind_lookup Θ Ξ qc = Some D' /\ vwrap_ok D D' vm}
    + {~ forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       exists D', ind_lookup Θ Ξ qc = Some D' /\ vwrap_ok D D' vm}.
  Proof.
    apply views_dec; intros k Mk qc k' Is vm _ _.
    destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| right; intros (D' & HD' & _); discriminate ].
    destruct (vwrap_check D D' vm) eqn:Hc.
    - left; exists D'; split; [ reflexivity | exact (vwrap_check_sound _ _ _ Hc) ].
    - right; intros (D'' & [= <-] & Hw); rewrite (vwrap_check_complete _ _ _ Hw) in Hc; discriminate.
  Defined.

  (** A premise of [ind_nil_at] that fails: the group is not checked. *)
  Local Ltac nil_rej :=
    let Hn := fresh "Hn" in
    right; intros Hn; destruct Hn;
    first [ contradiction
          | exfalso; match goal with HN : forall _, ~ _ |- _ => eapply HN; solve [ eassumption | split; eassumption ] end ].

  (** The group checked at the instances [IsS]: [ind_nil_at], premise by
      premise, the universe of the sort and of the views' domains the
      largest either asks for. *)
  Definition ind_nil_at_dec : {ind_nil_at Θ Ξ mp D IsS} + {~ ind_nil_at Θ Ξ mp D IsS}.
  Proof.
    destruct uparams_suffix_dec as [[Δ HΔ] | HnΔ]; [| nil_rej ].
    destruct (tele_ass_dec (ind_uparams D)) as [Hass | Hass]; [| nil_rej ].
    destruct (decl_mvc_dec D) as [Hmvc | Hmvc]; [| nil_rej ].
    destruct (Compare_dec.le_dec (List.length (gs_tele Ξ)) (ind_nu D)) as [Hle | Hle]; [| nil_rej ].
    destruct (check_ctx fctx_none Θ Ξ HΞ (ind_uparams D)) as [HU | HU]; [| nil_rej ].
    destruct order_ok_dec as [Hord | Hord]; [| nil_rej ].
    destruct first_member_dec as [[M0 [HM0 Hh0]] | HnM0]; [| nil_rej ].
    destruct (ind_sort_univ_dec (ind_sort D)) as [HSu | HSu]; [| nil_rej ].
    destruct (typ_least_dec Θ Ξ HΞ (ind_uparams D) (ind_sort D)) as [[lS [HS _]] | HnS]; [| nil_rej ].
    destruct (check_level fctx_none Θ Ξ (ind_uparams D) HU (ind_sort_lvl (ind_sort D))) as [[n Hn] | Hnn]; [| nil_rej ].
    destruct nparams_ass_dec as [HPass | HPass]; [| nil_rej ].
    destruct members_nodup_dec as [Hnd | Hnd]; [| nil_rej ].
    destruct nparams_sort_dec as [HNs | HNs]; [| nil_rej ].
    destruct args_sort_dec as [HAs | HAs]; [| nil_rej ].
    destruct doms_sort_dec as [HDs | HDs]; [| nil_rej ].
    destruct plen_dec as [HPl | HPl]; [| nil_rej ].
    destruct rec_ps_dec as [HPs | HPs]; [| nil_rej ].
    destruct views_exist_dec as [HVe | HVe]; [| nil_rej ].
    destruct link_dec as [HLk | HLk]; [| nil_rej ].
    destruct iss_typed_dec as [HIt | HIt]; [| nil_rej ].
    destruct decl_maps_dec as [HDm | HDm]; [| nil_rej ].
    destruct view_maps_len_dec as [HVl | HVl]; [| nil_rej ].
    destruct view_is_eq_dec as [HIe | HIe]; [| nil_rej ].
    destruct (nparams_eq_dec HPass) as [HNe | HNe]; [| nil_rej ].
    destruct cargs_eq_dec as [HCe | HCe]; [| nil_rej ].
    destruct doms_eq_bound_dec as [[lD HDe] | HnDe]; [| nil_rej ].
    destruct ps_typed_dec as [HPt | HPt]; [| nil_rej ].
    destruct ps_eq_dec as [HPe | HPe]; [| nil_rej ].
    destruct sort_sub_dec as [HSs | HSs]; [| nil_rej ].
    destruct (rank_check Θ Ξ D) eqn:Hrk;
      [| right; intros Hn0; destruct Hn0;
         rewrite (rank_check_complete _ _ _ (decls_of_ctx _ _ _ HU) ltac:(eassumption)) in Hrk; discriminate ].
    destruct vwrap_dec as [HVw | HVw]; [| nil_rej ].
    destruct (view_maps_check Θ Ξ D) eqn:Hvm;
      [| right; intros Hn0; destruct Hn0; rewrite (view_maps_check_complete _ _ _ ltac:(eassumption)) in Hvm; discriminate ].
    left; apply (mk_ind_nil_at Θ Ξ mp D IsS Δ M0 (Nat.max lS lD) n); try assumption.
    - apply (lift_exp_ge _ _ _ _ lS); [ lia | exact HS ].
    - intros; apply (lift_exp_eq_ge _ _ _ _ _ lD); [ lia | eapply HDe; eassumption ].
    - exists (grp_rank Θ Ξ D); exact (rank_check_sound _ _ _ Hrk).
    - exact (view_maps_check_sound _ _ _ Hvm).
  Defined.
End NilDecide.

(** ** Classifying the Arguments as Written

    Why an argument is rejected, for the checker's message, along the
    [Π]s of its type while their domains are free of the [Self]s:
    - [0]: it depends on a recursive argument before it;
    - [1]: a [Self] occurs elsewhere;
    - [2]: a [Self] occurs in a domain, so not strictly positively;
    - [4]: a [Self] is an argument of a head that does not compute (an
      opaque definition, an axiom or a parameter), so its occurrence
      cannot be seen to be positive;
    - [cls_why_unapplied k]: [Self_k], the declared member [k], is the head
      and is not applied to the uniform parameters as declared;
    - [cls_why_nested H]: a [Self] occurs in an argument of the type former [H]
      that is not one of its uniform arguments, or [H] is no declared
      member of a filed group. *)
Inductive cls_why : Set :=
(** One of the reasons above, by its code *)
| cls_why_code : nat -> cls_why
(** The declared member [k], written as the head, not applied to the
    uniform parameters as declared *)
| cls_why_unapplied : nat -> cls_why
(** A [Self] in a non-uniform argument of a nested occurrence, or one under
    a type former of no declared member: the head *)
| cls_why_nested : exp -> cls_why.

(** Whether no [Self] occurs in [T], [d] domains down, past the arguments
    before ([pat]) and [np] parameters. *)
Definition selfs_free (np n : nat) (pat : list bool) (d : nat) (T : exp) : bool :=
  match img_pat (cls_pat d np n (List.repeat false (List.length pat))) T with Some _ => true | None => false end.

Fixpoint sh_reason (np n : nat) (pat : list bool) (d : nat) (T : exp) : cls_why :=
  match T with
  | a_pi A B => if selfs_free np n pat d A then sh_reason np n pat (S d) B else cls_why_code 2
  | _ =>
      match app_head T with
      (* [Self_0] is outermost: the variable [b + i] is [Self_(n-1-i)]. *)
      | a_var j => let b := d + List.length pat + np in
                   if (b <=? j) && (j <? b + n) then cls_why_unapplied (n - 1 - (j - b)) else cls_why_code 4
      | a_mem _ _ => cls_why_code 4
      | a_ind qc k => cls_why_nested (a_ind qc k)
      | _ => cls_why_code 1
      end
  end.

(** The reason an argument [T] is rejected. *)
Definition cls_reason (np n : nat) (pat : list bool) (T : exp) : cls_why :=
  if selfs_free np n pat 0 T then cls_why_code 0 else sh_reason np n pat 0 T.

Section Classify.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.

  (** An argument as written, or, failing that, as its normal form. *)
  Definition cls_arg_in_dec (Γ : ctx) (nu np n : nat) (pat : list bool) (T : exp) :
    ({g | cls_arg_in Θ Ξ Γ nu np n pat T g} + {r : cls_why | forall g, ~ cls_arg_in Θ Ξ Γ nu np n pat T g})%type.
  Proof.
    destruct (cls_arg grp_none nu np n pat T) as [g |] eqn:Hs; [ left; exists g; apply cls_in_syn; exact Hs |].
    destruct (typ_least_dec Θ Ξ HΞ Γ T) as [[i [HT _]] | HnT].
    2:{ right; exists (cls_reason np n pat T); intros g H; inversion H as [g' Hg' | i W g' _ HT _ _]; subst;
        [ congruence | exact (HnT _ HT) ]. }
    destruct (@nbe_ty_impl Θ Ξ (fctx_none Θ Ξ) Γ T (typ_nbe_ty_order Θ Ξ _ _ _ HT)) as [W HW].
    destruct (cls_arg (grp_info Θ Ξ) nu np n pat (nf_to_exp W)) as [g |] eqn:Hn.
    - left; exists g; eapply cls_in_nf; eassumption.
    - right; exists (cls_reason np n pat (nf_to_exp W)).
      intros g H; inversion H as [g' Hg' | i' W' g' _ _ HW' Hg']; subst; [ congruence |].
      pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-; congruence.
  Defined.

  (** The arguments of a constructor, each in the context of those before
      it; a rejection names the argument and why. *)
  Definition cls_args_in_dec (Γp : ctx) (nu np n : nat) :
    forall (args : list (string * exp)) (pat : list bool) (args1 : list (string * exp)),
      ({gs | cls_args_in Θ Ξ Γp nu np n pat args1 args gs}
       + {e : (string * cls_why) | forall gs, ~ cls_args_in Θ Ξ Γp nu np n pat args1 args gs})%type.
  Proof.
    fix go 1; intros [| [y T] args] pat args1.
    - left; exists nil; constructor.
    - destruct (cls_arg_in_dec (rtele args1 ++ Γp) nu np n pat T) as [[g Hg] | [r Hg]].
      + destruct (go args (rcarg_bit g :: pat) (args1 ++ (y, T) :: nil)) as [[gs Hgs] | [e He]].
        * left; exists (g :: gs); constructor; assumption.
        * right; exists e; intros gs' H; inversion H; subst.
          match goal with Hg' : cls_arg_in _ _ _ _ _ _ _ _ ?g' |- _ =>
            pose proof (cls_arg_in_functional _ _ _ _ _ _ _ _ _ _ Hg Hg') as <- end.
          eapply He; eassumption.
      + right; exists (y, r); intros gs' H; inversion H; subst; eapply Hg; eassumption.
  Defined.

  (** The constructors of a member; a rejection names the constructor, the
      argument and why. *)
  Definition cls_cons_in_dec (Γp : ctx) (nu np n : nat) :
    forall (rcs : list (string * list (string * exp))),
      ({cs | cls_cons_in Θ Ξ Γp nu np n rcs cs}
       + {e : (string * string * cls_why) | forall cs, ~ cls_cons_in Θ Ξ Γp nu np n rcs cs})%type.
  Proof.
    unfold cls_cons_in; fix go 1; intros [| [c args] rcs].
    - left; exists nil; constructor.
    - destruct (cls_args_in_dec Γp nu np n args nil nil) as [[gs Hgs] | [[y r] He]].
      + destruct (go rcs) as [[cs Hcs] | [e He]].
        * left; exists ((c, gs) :: cs); constructor; [ split; [ reflexivity | exact Hgs ] | exact Hcs ].
        * right; exists e; intros cs' H; inversion H; subst; eapply He; eassumption.
      + right; exists (c, y, r); intros cs' H; inversion H as [| ? [c' gs'] ? ? [_ Hc]]; subst; eapply He; exact Hc.
  Defined.

  (** The constructors of a declared member. *)
  Definition rm_cls_dec (R : raw_decl) (Mr : raw_member) :
    ({cs | rm_cls Θ Ξ R Mr cs} + {e : (string * string * cls_why) | forall cs, ~ rm_cls Θ Ξ R Mr cs})%type :=
    cls_cons_in_dec (rm_pctx Ξ R Mr) (rd_nu R) (List.length (raw_member_nparams Mr) + rd_nu R) (rd_n R) (raw_member_cons Mr).

  (** The declared members' constructors, member by member; a rejection
      names the member too. *)
  Fixpoint rms_cls_dec (R : raw_decl) (ms : list raw_member) :
    ({css | Forall2 (rm_cls Θ Ξ R) ms css}
     + {e : (string * string * string * cls_why) | forall css, ~ Forall2 (rm_cls Θ Ξ R) ms css})%type.
  Proof.
    destruct ms as [| Mr ms'].
    - left; exists nil; constructor.
    - destruct (rm_cls_dec R Mr) as [[cs Hcs] | [[[c y] r] He]].
      + destruct (rms_cls_dec R ms') as [[css Hcss] | [e He']].
        * left; exists (cs :: css); constructor; assumption.
        * right; exists e; intros css H; inversion H; subst; eapply He'; eassumption.
      + right; exists (raw_member_name Mr, c, y, r); intros css H; inversion H; subst; eapply He; eassumption.
  Defined.

  (** ** The Views' Relations, at a View *)

  (** Why a view is rejected, for the checker's message. *)
  Inductive view_why : Set :=
  (** The instance is no declared member of a filed group *)
  | view_why_container : view_why
  (** A container's argument at the instance is rejected: the constructor,
      the argument and why *)
  | view_why_cls : string -> string -> cls_why -> view_why
  (** A non-uniform parameter or a sibling's instance at the instance is
      not a type, or not typed *)
  | view_why_untyped : view_why
  (** A non-uniform parameter at the instance mentions the group *)
  | view_why_mentions_group : view_why.

  (** The constructors of a view, classified. *)
  Definition view_cls_dec (R : raw_decl) (x : rview) :
    ({cs | view_cls Θ Ξ R x cs} + {e : view_why | forall cs, ~ view_cls Θ Ξ R x cs})%type.
  Proof.
    destruct x as [[qc k] Cs].
    destruct (ind_lookup_f Θ Ξ qc) as [[D' |] Hl]; [| right; exists view_why_container; intros cs H; inversion H; congruence ].
    destruct (ind_member D' k) as [Mk' |] eqn:Hk; [| right; exists view_why_container; intros cs H; inversion H; subst; unify_found; congruence ].
    destruct (cls_cons_in_dec (tele_sub (im_nparams Mk') (sb_of_list sb_id Cs) ++ rd_uctx Ξ R) (rd_nu R) (im_nn Mk' + rd_nu R) (rd_n R)
                (List.map (fun cg => (fst cg, ctx_args (tele_sub (cargs_ctx qc D' Mk' (snd cg)) (sb_qn (im_nn Mk') (sb_of_list sb_id Cs)))))
                   (im_cons Mk'))) as [[cs Hcs] | [[[c y] r] He]].
    - left; exists cs; econstructor; eassumption.
    - right; exists (view_why_cls c y r); intros cs H; inversion H; subst; unify_found; eapply He; eassumption.
  Defined.

  (** A telescope of assumptions normalized entry by entry, each a type
      first. *)
  Fixpoint nbe_tele_dec (Γ : ctx) (Δ : ctx) {struct Δ} : {Δ' | nbe_tele Θ Ξ Γ Δ Δ'} + {forall Δ', ~ nbe_tele Θ Ξ Γ Δ Δ'}.
  Proof.
    destruct Δ as [| [A | A M | U | A M U] Δ0].
    - left; exists nil; constructor.
    - destruct (nbe_tele_dec Γ Δ0) as [[Δ0' H0] | H0]; [| right; intros Δ' H; inversion H; subst; eapply H0; eassumption ].
      destruct (typ_least_dec Θ Ξ HΞ (Δ0 ++ Γ) A) as [[i [HA _]] | HnA];
        [| right; intros Δ' H; inversion H as [| ? ? ? ? [i HA] _ _]; subst; exact (HnA _ HA) ].
      destruct (@nbe_ty_impl Θ Ξ (fctx_none Θ Ξ) (Δ0 ++ Γ) A (typ_nbe_ty_order Θ Ξ _ _ _ HA)) as [W HW].
      left; exists (ce_ass (nf_to_exp W) :: Δ0'); constructor; [ exists i; exact HA | exact HW | exact H0 ].
    - right; intros Δ' H; inversion H.
    - right; intros Δ' H; inversion H.
    - right; intros Δ' H; inversion H.
  Defined.

  (** The non-uniform parameters of a view, filed. *)
  Definition view_nps_dec (R : raw_decl) (x : rview) :
    ({Nv | view_nps Θ Ξ R x Nv} + {e : view_why | forall Nv, ~ view_nps Θ Ξ R x Nv})%type.
  Proof.
    destruct x as [[qc k] Cs].
    destruct (ind_lookup_f Θ Ξ qc) as [[D' |] Hl]; [| right; exists view_why_container; intros Nv H; inversion H; congruence ].
    destruct (ind_member D' k) as [Mk' |] eqn:Hk; [| right; exists view_why_container; intros Nv H; inversion H; subst; unify_found; congruence ].
    destruct (nbe_tele_dec (rd_uctx Ξ R) (tele_sub (im_nparams Mk') (sb_of_list sb_id Cs))) as [[Ws HWs] | HnWs].
    2:{ right; exists view_why_untyped; intros Nv H; inversion H; subst; unify_found; eapply HnWs; eassumption. }
    destruct (img_tele (List.repeat false (rd_nu R) ++ List.repeat true (rd_n R)) Ws) as [Nv |] eqn:Hi.
    - left; exists Nv; econstructor; eassumption.
    - right; exists view_why_mentions_group; intros Nv H; inversion H; subst; unify_found.
      match goal with H1 : nbe_tele _ _ _ _ ?W1 |- _ => pose proof (nbe_tele_functional _ _ _ _ _ _ HWs H1) as <- end.
      congruence.
  Defined.

  (** Terms normalized pointwise at types, each typed first. *)
  Fixpoint nbes_dec (Γ : ctx) (Ms : list exp) (As : list typ) {struct Ms} :
    {Ws | nbes Θ Ξ Γ Ms As Ws} + {forall Ws, ~ nbes Θ Ξ Γ Ms As Ws}.
  Proof.
    destruct Ms as [| M Ms'], As as [| A As']; try (right; intros Ws H; inversion H; fail).
    - left; exists nil; constructor.
    - destruct (nbes_dec Γ Ms' As') as [[Ws' HWs'] | HnWs']; [| right; intros Ws H; inversion H; subst; eapply HnWs'; eassumption ].
      destruct (check_exp_at Θ Ξ HΞ Γ A M) as [HM | HnM]; [| right; intros Ws H; inversion H; subst; contradiction ].
      destruct (@nbe_impl Θ Ξ (fctx_none Θ Ξ) Γ M A (typed_nbe_order' Θ Ξ _ _ _ HM)) as [W HW].
      left; exists (W :: Ws'); constructor; assumption.
  Defined.

  (** The members of a container's group from position [i], at [Cs]. *)
  Fixpoint sibs_from_dec (Γc : ctx) (qc : qname) (Cs : list exp) (i : nat) (ms : list imember) {struct ms} :
    {ss | sibs_from Θ Ξ Γc qc Cs i ms ss} + {forall ss, ~ sibs_from Θ Ξ Γc qc Cs i ms ss}.
  Proof.
    destruct ms as [| M ms'].
    - left; exists nil; constructor.
    - destruct (sibs_from_dec Γc qc Cs (S i) ms') as [[ss Hss] | Hnss];
        [| right; intros ss H; inversion H; subst; eapply Hnss; eassumption ].
      destruct (im_head M) as [pm | qv kv Iv vmv] eqn:Hh.
      + left; exists ((qc, i, Cs) :: ss); eapply sibs_from_decl; eassumption.
      + destruct (ind_lookup_f Θ Ξ qv) as [[Dv |] Hlv]; [| right; intros ss' H; inversion H; subst; unify_found; congruence ].
        destruct (nbes_dec Γc (List.map (fun I => I[sb_of_list sb_id Cs]) Iv)
                    (List.map (fun T => T[sb_of_list sb_id Cs]) (tele_insts (ind_uparams Dv) sb_id Iv))) as [[Ws HWs] | HnWs].
        * left; exists ((qv, kv, List.map nf_to_exp Ws) :: ss); eapply sibs_from_view; eassumption.
        * right; intros ss' H; inversion H; subst; unify_found; [ congruence |].
          match goal with Hh' : im_head M = mh_view _ _ _ _ |- _ => rewrite Hh in Hh'; injection Hh'; intros; subst end.
          unify_found; eapply HnWs; eassumption.
  Defined.

  (** The siblings of a view. *)
  Definition view_sibs_dec (R : raw_decl) (x : rview) :
    ({ss | view_sibs Θ Ξ R x ss} + {e : view_why | forall ss, ~ view_sibs Θ Ξ R x ss})%type.
  Proof.
    destruct x as [[qc k] Cs].
    destruct (ind_lookup_f Θ Ξ qc) as [[D' |] Hl]; [| right; exists view_why_container; intros ss H; inversion H; congruence ].
    destruct (sibs_from_dec (rd_uctx Ξ R) qc Cs 0 (ind_members D')) as [[ss Hss] | Hnss].
    - left; exists ss; econstructor; eassumption.
    - right; exists view_why_untyped; intros ss H; inversion H; subst; unify_found; eapply Hnss; eassumption.
  Defined.
End Classify.

(** ** The Declaration's Relations Cross [gds_equiv]

    The checker decides a declaration at the units the unit imported, the
    judgment holds at the units filed: the two have the same lookups, so
    the same normal forms ([GlobalExt]), and the same judgments
    ([deps_grow]). *)

Lemma gds_equiv_lookup : forall Θ Θ' fp, gds_equiv Θ Θ' -> gds_lookup Θ fp = gds_lookup Θ' fp.
Proof.
  intros * [H1 H2]; destruct (gds_lookup Θ fp) as [U |] eqn:E.
  - symmetry; exact (H1 _ _ E).
  - destruct (gds_lookup Θ' fp) as [U |] eqn:E'; [| reflexivity ].
    rewrite (H2 _ _ E') in E; discriminate.
Qed.

Lemma gds_equiv_resolve : forall Θ Θ' Ξ p, gds_equiv Θ Θ' -> gc_resolve Θ Ξ p = gc_resolve Θ' Ξ p.
Proof. intros * He; unfold gc_resolve, gc_resolve_u; rewrite (gds_equiv_lookup _ _ _ He); reflexivity. Qed.

Lemma gds_equiv_module : forall Θ Θ' Ξ p, gds_equiv Θ Θ' -> gc_module Θ Ξ p = gc_module Θ' Ξ p.
Proof. intros * He; unfold gc_module, gc_module_u; rewrite (gds_equiv_lookup _ _ _ He); reflexivity. Qed.

Lemma gds_equiv_body : forall Θ Θ' Ξ p, gds_equiv Θ Θ' -> gc_body Θ Ξ p = gc_body Θ' Ξ p.
Proof. intros * He; unfold gc_body; rewrite (gds_equiv_lookup _ _ _ He); reflexivity. Qed.

Lemma gds_equiv_ind_lookup : forall Θ Θ' Ξ p, gds_equiv Θ Θ' -> ind_lookup Θ Ξ p = ind_lookup Θ' Ξ p.
Proof. intros * He; rewrite !ind_lookup_unfold, !ind_mlookup_unfold, (gds_equiv_module _ _ _ _ He); reflexivity. Qed.

(** The entries are found alike: in the frames, or in the dependencies. *)
Lemma gds_equiv_entry : forall Θ Θ' Ξ p, gds_equiv Θ Θ' -> gc_entry Θ Ξ p = gc_entry Θ' Ξ p.
Proof. intros * He; unfold gc_entry, gc_entry_u; rewrite (gds_equiv_lookup _ _ (q_unit p) He); reflexivity. Qed.

(** The record types are found alike: in the frames, or in the entries. *)
Lemma gds_equiv_record_lookup : forall Θ Θ' Ξ p, gds_equiv Θ Θ' -> record_lookup Θ Ξ p = record_lookup Θ' Ξ p.
Proof.
  intros * He; unfold record_lookup, gc_entry, gc_entry_u.
  rewrite (gds_equiv_lookup _ _ (q_unit p) He); reflexivity.
Qed.

(** What module expressions denote reads the dependencies through their
    lookups alone ([gc_unit], [gc_loc]). *)
Lemma gds_equiv_mdenote_all : forall Θ Θ' Ξ, gds_equiv Θ Θ' ->
    (forall Γ H R, mdenote Θ Ξ Γ H R -> mdenote Θ' Ξ Γ H R) /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R -> udenote Θ' Ξ Γ o U R) /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R -> edenote Θ' Ξ Γ o E R) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> body_xp Θ' Ξ Γ Φ Φx) /\
    (forall Γ H its gs, items_gen Θ Ξ Γ H its gs -> items_gen Θ' Ξ Γ H its gs).
Proof.
  intros * He.
  assert (Hu : forall H, gc_unit Θ Ξ H = gc_unit Θ' Ξ H).
  { intros H; unfold gc_unit; destruct (mod_qname H) as [mp |]; [| reflexivity ].
    rewrite (gds_equiv_lookup _ _ (q_unit mp) He); reflexivity. }
  apply mdenote_all_ind; intros; rewrite ?Hu in *; econstructor; eauto.
  all: unfold gc_loc in *; rewrite <- (gds_equiv_body _ _ _ _ He); assumption.
Qed.

Corollary gds_equiv_mdenote : forall Θ Θ' Ξ Γ H R, gds_equiv Θ Θ' -> mdenote Θ Ξ Γ H R -> mdenote Θ' Ξ Γ H R.
Proof. intros * He; exact (proj1 (gds_equiv_mdenote_all _ _ _ He) _ _ _). Qed.

Section Equiv.
  Variables (Θ Θ' : gdeps) (Ξ : gstack).
  Hypothesis He : gds_equiv Θ Θ'.
  Hypothesis HΞ' : ⊢ᵍ Θ' ⍮ Ξ.

  Let Hb : ⊢ Θ' ⍮ Ξ ⍮ ⋅ := wf_ctx_empty _ _ HΞ'.

  Lemma equiv_nbe_ty : forall Γ A W, nbe_ty Θ Ξ Γ A W -> nbe_ty Θ' Ξ Γ A W.
  Proof.
    apply nbe_ty_ext; intros; [ apply gds_equiv_resolve | apply gds_equiv_module | apply gds_equiv_ind_lookup
                               | apply gds_equiv_entry | reflexivity | reflexivity | apply gds_equiv_body
                               | apply gds_equiv_record_lookup ]; exact He.
  Qed.

  Lemma equiv_nbe : forall Γ M A W, nbe Θ Ξ Γ M A W -> nbe Θ' Ξ Γ M A W.
  Proof.
    assert (Hs : (forall p, gc_resolve Θ Ξ p = gc_resolve Θ' Ξ p) /\ (forall p, gc_module Θ Ξ p = gc_module Θ' Ξ p) /\
                 (forall p, ind_lookup Θ Ξ p = ind_lookup Θ' Ξ p) /\ (forall p, gc_entry Θ Ξ p = gc_entry Θ' Ξ p) /\
                 (forall p, gc_frame Ξ p = gc_frame Ξ p) /\ (forall p, gs_find_ind Ξ p = gs_find_ind Ξ p) /\
                 (forall p, gc_body Θ Ξ p = gc_body Θ' Ξ p) /\ (forall p, record_lookup Θ Ξ p = record_lookup Θ' Ξ p))
      by (repeat split; intros; first [ reflexivity | apply gds_equiv_resolve | apply gds_equiv_module
                                       | apply gds_equiv_ind_lookup | apply gds_equiv_entry | apply gds_equiv_body
                                       | apply gds_equiv_record_lookup ];
          exact He).
    destruct Hs as (Hres & Hmod & Hind & Hia & Hfr & Hfi & Hbody & Hrec).
    pose proof (eval_ext _ _ _ _ Hres Hmod Hind Hia Hfr Hfi Hbody Hrec) as Hev;
      pose proof (read_ext _ _ _ _ Hres Hmod Hind Hia Hfr Hfi Hbody Hrec) as Hrd.
    pose proof (initial_env_ext _ _ _ _ Hres Hmod Hind Hia Hfr Hfi Hbody Hrec) as Hie.
    destruct_all.
    intros * []; econstructor; eauto.
  Qed.

  (** The classification reads the filed groups through [grp_info] alone. *)
  Lemma cls_sh_ext : forall (g1 g2 : qname -> nat -> option nat) nu np n pat, (forall q0 k, g1 q0 k = g2 q0 k) ->
      forall T d, cls_sh g1 nu np n pat d T = cls_sh g2 nu np n pat d T.
  Proof.
    intros * Hg T; induction T; intros d; cbn [cls_sh]; try reflexivity;
      try (destruct (app_head _) eqn:?; try reflexivity; unfold cls_nest; rewrite Hg; reflexivity).
    destruct (img_pat _ _); [ rewrite IHT2; reflexivity | reflexivity ].
  Qed.

  Lemma cls_arg_ext : forall (g1 g2 : qname -> nat -> option nat) nu np n pat, (forall q0 k, g1 q0 k = g2 q0 k) ->
      forall T, cls_arg g1 nu np n pat T = cls_arg g2 nu np n pat T.
  Proof. intros * Hg T; unfold cls_arg; rewrite (cls_sh_ext g1 g2 _ _ _ _ Hg); reflexivity. Qed.

  Lemma equiv_typ : forall Γ A i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i -> Θ' ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
  Proof. intros; eapply equiv_exp; eassumption. Qed.

  Lemma equiv_cls_arg_in : forall Γ nu np n pat T g,
      cls_arg_in Θ Ξ Γ nu np n pat T g -> cls_arg_in Θ' Ξ Γ nu np n pat T g.
  Proof.
    intros * H; destruct H as [g Hg | i W g Hn HT HW Hg]; [ apply cls_in_syn; exact Hg |].
    eapply cls_in_nf; [ exact Hn | exact (equiv_exp _ _ _ _ _ _ He HΞ' HT) | exact (equiv_nbe_ty _ _ _ HW) |].
    rewrite <- (cls_arg_ext (grp_info Θ Ξ)); [ exact Hg |].
    intros; unfold grp_info; rewrite (gds_equiv_ind_lookup _ _ _ _ He); reflexivity.
  Qed.

  Lemma equiv_cls_args_in : forall Γp nu np n pat args1 args gs,
      cls_args_in Θ Ξ Γp nu np n pat args1 args gs -> cls_args_in Θ' Ξ Γp nu np n pat args1 args gs.
  Proof. induction 1; constructor; [ apply equiv_cls_arg_in | ]; assumption. Qed.

  Lemma equiv_cls_cons_in : forall Γp nu np n rcs cs,
      cls_cons_in Θ Ξ Γp nu np n rcs cs -> cls_cons_in Θ' Ξ Γp nu np n rcs cs.
  Proof.
    intros *; unfold cls_cons_in; apply Forall2_impl; intros rc c [Hf Hc]; split; [ exact Hf | exact (equiv_cls_args_in _ _ _ _ _ _ _ _ Hc) ].
  Qed.

  Lemma equiv_rm_cls : forall R ms css, Forall2 (rm_cls Θ Ξ R) ms css -> Forall2 (rm_cls Θ' Ξ R) ms css.
  Proof. intros *; apply Forall2_impl; intros; apply equiv_cls_cons_in; assumption. Qed.

  Lemma equiv_view_cls : forall R x cs, view_cls Θ Ξ R x cs -> view_cls Θ' Ξ R x cs.
  Proof.
    intros * []; econstructor; [ rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); eassumption | eassumption |].
    apply equiv_cls_cons_in; assumption.
  Qed.

  Lemma equiv_nbe_tele : forall Γ Δ Δ', nbe_tele Θ Ξ Γ Δ Δ' -> nbe_tele Θ' Ξ Γ Δ Δ'.
  Proof.
    induction 1 as [| A Δ W Δ' [i HA] HW _ IH]; constructor; [ exists i; exact (equiv_typ _ _ _ HA) | exact (equiv_nbe_ty _ _ _ HW) | exact IH ].
  Qed.

  Lemma equiv_view_nps : forall R x Nv, view_nps Θ Ξ R x Nv -> view_nps Θ' Ξ R x Nv.
  Proof.
    intros * []; econstructor; [ rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); eassumption | eassumption | | eassumption ].
    apply equiv_nbe_tele; assumption.
  Qed.

  Lemma equiv_nbes : forall Γ Ms As Ws, nbes Θ Ξ Γ Ms As Ws -> nbes Θ' Ξ Γ Ms As Ws.
  Proof.
    induction 1; constructor; [ exact (equiv_exp _ _ _ _ _ _ He HΞ' ltac:(eassumption)) | exact (equiv_nbe _ _ _ _ ltac:(eassumption)) | assumption ].
  Qed.

  Lemma equiv_sibs_from : forall Γc qc Cs i ms ss, sibs_from Θ Ξ Γc qc Cs i ms ss -> sibs_from Θ' Ξ Γc qc Cs i ms ss.
  Proof.
    induction 1; [ constructor | eapply sibs_from_decl; eassumption |].
    eapply sibs_from_view; [ eassumption | rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); eassumption | apply equiv_nbes; eassumption | assumption ].
  Qed.

  Lemma equiv_view_sibs : forall R x ss, view_sibs Θ Ξ R x ss -> view_sibs Θ' Ξ R x ss.
  Proof.
    intros * []; econstructor; [ rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); eassumption | apply equiv_sibs_from; assumption ].
  Qed.

  Lemma equiv_rd_filed : forall R Vs Ss csD csV Nvs, rd_filed Θ Ξ R Vs Ss csD csV Nvs = rd_filed Θ' Ξ R Vs Ss csD csV Nvs.
  Proof.
    intros; unfold rd_filed; destruct (raw_decl_members R) as [| Mr0 Mrs]; [ reflexivity |].
    assert (Hrv : forall σ n Vs0 xs Ss0 css Nvs0, rvs_filed Θ Ξ σ n Vs0 xs Ss0 css Nvs0 = rvs_filed Θ' Ξ σ n Vs0 xs Ss0 css Nvs0).
    { intros σ n Vs0 xs; induction xs as [| x xs IH]; intros [| ss Ss0] [| cs css] [| Nv Nvs0]; cbn; try reflexivity.
      rewrite IH; unfold rv_filed; destruct x as [[qc k] Cs]; rewrite (gds_equiv_ind_lookup _ _ _ _ He); reflexivity. }
    rewrite Hrv; reflexivity.
  Qed.

  Lemma equiv_view_rank_ok : forall D rk, view_rank_ok Θ Ξ D rk -> view_rank_ok Θ' Ξ D rk.
  Proof.
    intros * [Hd Hn]; constructor; [ exact Hd |].
    intros *; rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); eapply Hn.
  Qed.

  Lemma equiv_view_maps_coherent : forall D, view_maps_coherent Θ Ξ D -> view_maps_coherent Θ' Ξ D.
  Proof. intros D H; unfold view_maps_coherent in *; intros *; rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); eapply H. Qed.

  (** The group, checked at the instances [IsS], at the units filed. *)
  Lemma equiv_ind_nil_at : forall mp D IsS, ind_nil_at Θ Ξ mp D IsS -> ind_nil_at Θ' Ξ mp D IsS.
  Proof.
    destruct (deps_grow Θ Θ' Ξ (proj1 He) Hb) as (Hc & Hx & Hq & Hs & Hext & _ & _).
    assert (Hl : forall p, ind_lookup Θ Ξ p = ind_lookup Θ' Ξ p) by (intros; apply gds_equiv_ind_lookup, He).
    intros * [Δ M0 i n H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28
                H29 H30 [rk Hrk] H32 H33].
    apply (mk_ind_nil_at Θ' Ξ mp D IsS Δ M0 i n); auto.
    all: try (intros; rewrite <- ?Hl in *; eauto; fail).
    - exists rk; apply equiv_view_rank_ok, Hrk.
    - apply equiv_view_maps_coherent, H33.
  Qed.
End Equiv.
