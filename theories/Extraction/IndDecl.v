From Stdlib Require Import Arith List ListDec String PeanoNat Bool Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System Fresh.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Core Require Import Soundness Completeness.
From Mctt.Core.Consequences Require Import Consistency.
From Mctt.Core.Semantic Require Import GlobalExt.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Extraction Require Import Lookup LookupTwins PseudoMonadic NbE Subtyping TypeCheckBase IndCheck TypeCheck GlobalCheck.
Import Syntax_Notations GlobalCtx_Notations.

(** * Deciding a Declaration

    The well-formedness of a group of inductive declarations as entries of
    a frame, each with an empty module ([wf_gentry_ind_nil],
    [wf_gentry_ind_mem_nil]), decided premise by premise: the syntactic ones
    by computation, the judgments by [Extraction.GlobalCheck].  The
    premises quantifying over the members, the arguments of the
    constructors and the non-uniform parameters are decided along the
    lists, at each way of splitting them ([forall_split_dec]).  The checks
    of the views' rank, maps and members ([rank_check], [view_wrap_check],
    [view_maps_check]) are complete as well as sound. *)

(** ** Module Variables

    [exp_mvc], computed. *)

Fixpoint exp_mvcb (n : nat) (M : exp) {struct M} : bool :=
  match M with
  | a_typ _ | a_level _ | a_level_sort | a_llit _ | a_prop | a_True | a_tt | a_False => true
  | a_succl M | a_univ M | a_left M | a_right M => exp_mvcb n M
  | a_maxl M N | a_absurd M N => exp_mvcb n M && exp_mvcb n N
  | a_conj P Q M N => exp_mvcb n P && exp_mvcb (S n) Q && exp_mvcb n M && exp_mvcb n N
  | a_ind _ _ | a_con _ _ _ => true
  | a_elim _ _ Us _ Bks M =>
      (fix us_mvcb (Us : list exp) : bool :=
         match Us with
         | nil => true
         | U :: Us' => exp_mvcb n U && us_mvcb Us'
         end) Us &&
      (fix blocks_mvcb (Bks : list eblock) : bool :=
         match Bks with
         | nil => true
         | eb_mk nm Z A Bs :: Bks' =>
             exp_mvcb (nm - 1 + n) Z &&
             exp_mvcb (nm + n) A &&
             (fix brs_mvcb (Bs : list (string * nat * exp)) : bool :=
                match Bs with
                | nil => true
                | b :: Bs' => exp_mvcb (snd (fst b) + n) (snd b) && brs_mvcb Bs'
                end) Bs &&
             blocks_mvcb Bks'
         end) Bks &&
      exp_mvcb n M
  | a_pi _ _ A B | a_fn A B | a_and A B => exp_mvcb n A && exp_mvcb (S n) B
  | a_app M N => exp_mvcb n M && exp_mvcb n N
  | a_var _ => true
  | a_let b B => binding_mvcb n b && exp_mvcb (S n) B
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
with binding_mvcb (n : nat) (b : binding) {struct b} : bool :=
  match b with
  | b_def A M => exp_mvcb n A && exp_mvcb n M
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
  | gm_open Φ H _ Φg => gmod_mvcb n Φ && modexp_mvcb (gm_binders Φ + n) H && gmod_mvcb (gm_binders Φ + n) Φg
  end
with gentry_mvcb (n : nat) (E : gentry) {struct E} : bool :=
  match E with
  | ge_def _ _ _ A B => exp_mvcb n A && match B with Some M => exp_mvcb n M | None => true end
  | ge_mod _ U => gunit_mvcb n U
  | ge_ind _ _ _ D Φ => gmod_mvcb (ind_nu D + n) Φ
  | ge_def_mod _ A M U => exp_mvcb n A && exp_mvcb n M && gunit_mvcb n U
  | ge_record _ _ R Φ => gmod_mvcb (S (List.length (record_params R)) + n) Φ
  end
with centry_mvcb (n : nat) (e : centry) {struct e} : bool :=
  match e with
  | ce_ass _ A => exp_mvcb n A
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
    List.Forall (fun b => (forall n, exp_mvcb n (eb_scrutinee_type b) = true <-> exp_mvc n (eb_scrutinee_type b)) /\
                          (forall n, exp_mvcb n (eb_motive b) = true <-> exp_mvc n (eb_motive b)) /\
                          List.Forall (fun br => forall n, exp_mvcb n (snd br) = true <-> exp_mvc n (snd br)) (eb_brs b)) Bks ->
    (fix blocks_mvcb (Bks : list eblock) : bool :=
       match Bks with
       | nil => true
       | eb_mk nm Z A Bs :: Bks' =>
           exp_mvcb (nm - 1 + n) Z &&
           exp_mvcb (nm + n) A &&
           (fix brs_mvcb (Bs : list (string * nat * exp)) : bool :=
              match Bs with
              | nil => true
              | b :: Bs' => exp_mvcb (snd (fst b) + n) (snd b) && brs_mvcb Bs'
              end) Bs &&
           blocks_mvcb Bks'
       end) Bks = true <->
    all_blocks (fun nm Z A Bs => exp_mvc (nm - 1 + n) Z /\ exp_mvc (nm + n) A /\
                                  all_brs (fun k B => exp_mvc (k + n) B) Bs) Bks.
Proof.
  intros n Bks HB; induction HB as [| [nm Z A Bs] Bks (HZ & HA & HBs) _ IH]; cbn in *; [ split; auto |].
  rewrite !andb_true_iff, HZ, HA, IH, (brs_mvcb_spec n Bs HBs); tauto.
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
  (forall b n, binding_mvcb n b = true <-> binding_mvc n b) /\
  (forall U n, gunit_mvcb n U = true <-> gunit_mvc n U) /\
  (forall D n, moddef_mvcb n D = true <-> moddef_mvc n D) /\
  (forall Φ n, gmod_mvcb n Φ = true <-> gmod_mvc n Φ) /\
  (forall E n, gentry_mvcb n E = true <-> gentry_mvc n E) /\
  (forall e n, centry_mvcb n e = true <-> centry_mvc n e).
Proof.
  apply syn_mut_ind; intros;
    cbn [exp_mvcb modexp_mvcb binding_mvcb gunit_mvcb moddef_mvcb gmod_mvcb gentry_mvcb centry_mvcb
         exp_mvc modexp_mvc binding_mvc gunit_mvc moddef_mvc gmod_mvc gentry_mvc centry_mvc].
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
  - (* a unit: its telescope *)
    match goal with |- ?l = true /\ _ <-> ?r /\ _ => enough (Ht : l = true <-> r) by (rewrite Ht; reflexivity) end.
    clear - H; induction H as [| e Δ He _ IH]; cbn; [ split; auto |].
    rewrite andb_true_iff, He, IH; reflexivity.
  - destruct B as [M |]; [ rewrite (H0 M eq_refl) | split; intros [? _]; split; auto ]; reflexivity.
Qed.

(** A constructor argument without free module variables, computed. *)
Definition carg_mvcb (g : carg) : bool :=
  match g with
  | ca_arg _ A => exp_mvcb 0 A
  | ca_rec t => forallb (exp_mvcb 0) (ptyp_doms t) && forallb (exp_mvcb 0) (ptyp_ps t)
  end.

(** A member's head without free module variables, computed. *)
Definition mhead_mvcb (h : mhead) : bool :=
  match h with
  | mh_decl _ => true
  | mh_view _ _ Is _ => forallb (exp_mvcb 0) Is
  | mh_record _ Is _ => forallb (exp_mvcb 0) Is
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
  intros [pm | qc k Is vm | qr Is fl]; cbn;
    [ split; auto | apply (forallb_Forall _ _ _ (fun M => He M 0)) | apply (forallb_Forall _ _ _ (fun M => He M 0)) ].
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

    [rank_check], [view_wrap_check] and [view_maps_check] accept every group
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

Lemma cargs_correspondb_complete : forall vm gs' gs, cargs_correspond vm gs' gs -> cargs_correspondb vm gs' gs = true.
Proof.
  induction gs' as [| [r' A' | t'] gs' IH]; intros [| [r A | t] gs] H; cbn in H |- *; try contradiction; auto.
  - destruct H as [-> H]; destruct (abs_kind_eq_dec r r) as [_ | Hne]; [ cbn; auto | contradiction ].
  - destruct H as [-> H]; destruct (abs_kind_eq_dec ak_relevant ak_relevant) as [_ | Hne]; [ cbn; auto | contradiction ].
  - destruct H as (Hj & Hd & H); rewrite Hj, Nat.eqb_refl, Hd, Nat.eqb_refl; cbn; auto.
Qed.

(** A view's members that are the container's members pass the check. *)
Theorem view_wrap_check_complete : forall D D' vm, view_wrap_ok D D' vm -> view_wrap_check D D' vm = true.
Proof.
  intros * [Hl Hm]; unfold view_wrap_check; apply andb_true_iff; split; [ apply Nat.eqb_eq; exact Hl |].
  apply List.forallb_forall; intros [i' Mi'] Hin; cbn [fst snd].
  pose proof (in_combine_seq0 _ _ _ Hin) as HMi'.
  destruct (List.nth_error vm i') as [v |] eqn:Hv; [| reflexivity ].
  destruct (Hm _ _ _ HMi' Hv) as (Mv & HMv & Hnn & Hnames & Hcorr).
  rewrite HMv, Hnn, Nat.eqb_refl; cbn.
  destruct (list_eq_dec string_dec _ _) as [_ | Hne]; [| contradiction ]; cbn.
  apply List.forallb_forall; intros [c gs'] Hcg; cbn [fst snd].
  destruct (ind_con Mv c) as [gs |] eqn:Hc; [| reflexivity ].
  exact (cargs_correspondb_complete _ _ _ (Hcorr _ _ _ Hcg Hc)).
Qed.

Lemma view_map_at_check_complete : forall vm M vmv, view_map_at vm M vmv -> view_map_at_check vm M vmv = true.
Proof.
  intros * H; unfold view_map_at in H; unfold view_map_at_check.
  destruct (im_head M); [| | contradiction ]; destruct (list_eq_dec _ _ _) as [_ | Hne]; first [ reflexivity | contradiction ].
Qed.

(** Views that agree on their maps pass the check. *)
Theorem view_maps_check_complete : forall Θ Ξ D, view_maps_coherent Θ Ξ D -> view_maps_check Θ Ξ D = true.
Proof.
  intros * H; unfold view_maps_check; apply List.forallb_forall; intros Mk HMk.
  apply List.In_nth_error in HMk as [k HMk].
  destruct (im_head Mk) as [pm | qc k' Is vm | qr Is fl] eqn:Hh; [ reflexivity | | reflexivity ].
  destruct (ind_lookup Θ Ξ qc) as [D' |] eqn:Hl; [| reflexivity ].
  apply List.forallb_forall; intros [i' Mi'] Hin; cbn [fst snd].
  pose proof (in_combine_seq0 _ _ _ Hin) as HMi'.
  destruct (List.nth_error vm i') as [v |] eqn:Hv; [| reflexivity ].
  destruct (ind_member D v) as [Mv |] eqn:HMv; [| reflexivity ].
  destruct (im_head Mv) as [pm' | qv kv Iv vmv | qr' Is' fl'] eqn:HhMv; [ reflexivity | | reflexivity ].
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

(** A member a constructor's recursive arguments end in is that of one of
    them. *)
Lemma in_cargs_rec_mems_inv : forall gs j, In j (cargs_rec_mems gs) ->
    exists gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 /\ ptyp_mem t = j.
Proof.
  induction gs as [| [rA A | t] gs IH]; intros j Hj; cbn in Hj; [ contradiction | |].
  - destruct (IH _ Hj) as (gs1 & t & gs2 & -> & <-); exists (ca_arg rA A :: gs1), t, gs2; split; reflexivity.
  - destruct Hj as [<- | Hj]; [ exists nil, t, gs; split; reflexivity |].
    destruct (IH _ Hj) as (gs1 & t' & gs2 & -> & <-); exists (ca_rec t :: gs1), t', gs2; split; reflexivity.
Qed.

(** A member's head is a declared member's or not. *)
Lemma mhead_decl_cases : forall M : imember, (exists pm, im_head M = mh_decl pm) \/ (forall pm, im_head M <> mh_decl pm).
Proof. intros M; destruct (im_head M); [ left; eauto | right; congruence | right; congruence ]. Qed.

Section RankComplete.
  Variables (Θ : gdeps) (Ξ : gstack) (D : ind_decl) (rk : nat -> nat).
  Hypothesis HDs : decls_typed Θ Ξ.
  Hypothesis Hrk : view_rank_ok Θ Ξ D rk.

  Lemma cargs_nest_targets_lt : forall D' r gs' gs j, cargs_nest_ok D D' rk r gs' gs ->
      In j (cargs_nest_targets D D' gs' gs) -> rk j < r.
  Proof.
    intros D' r; induction gs' as [| [A' | t'] gs' IH]; intros [| [A | t] gs] j Hok Hj; cbn in Hok, Hj; try contradiction;
      first [ destruct Hok as [Hlt Hok]; destruct Hj as [<- | Hj]; [ exact Hlt | exact (IH _ _ Hok Hj) ]
            | exact (IH _ _ Hok Hj) | idtac ].
    destruct Hok as [Hlv Hok]; apply List.in_app_or in Hj as [Hj | Hj]; [| exact (IH _ _ Hok Hj) ].
    apply List.in_map_iff in Hj as (l & <- & Hl); apply List.filter_In in Hl as [Hl Hn].
    apply Hlv; [ exact Hl | destruct (leaf_in D' t' l); [ discriminate Hn | reflexivity ] ].
  Qed.

  (** A view's rank is above that of every member it nests through. *)
  Lemma member_nest_targets_lt : forall k Mk j, ind_member D k = Some Mk -> In j (member_nest_targets Θ Ξ D Mk) -> rk j < rk k.
  Proof.
    intros * HMk Hj; unfold member_nest_targets in Hj.
    destruct (im_head Mk) as [pm | qc k' Is vm | qr Is fl] eqn:Hh; [ contradiction | |].
    2: { (** A record view: above each member its recursive fields end in *)
      apply List.in_concat in Hj as (l & Hl & Hj); apply List.in_map_iff in Hl as ([c gs] & <- & Hcg); cbn [snd] in Hj.
      destruct (in_cargs_rec_mems_inv _ _ Hj) as (gs1 & t & gs2 & Egs & <-).
      exact (view_rank_ok_rview _ _ _ _ Hrk _ _ _ _ _ _ _ _ _ _ HMk Hh Hcg Egs). }
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
    exact (cargs_nest_targets_lt _ _ _ _ _ (view_rank_ok_nest _ _ _ _ Hrk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh Hl HMi' Hv HMv Hc' Hc) Hj).
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

  (** A view's or a record view's candidate rank: one above those of the
      members it nests through *)
  Lemma iter_view : forall m k Mk, ind_member D k = Some Mk -> (forall pm, im_head Mk <> mh_decl pm) ->
      grp_rank_iter Θ Ξ D (S m) k =
        S (List.fold_right Nat.max 0 (List.map (grp_rank_iter Θ Ξ D m) (member_nest_targets Θ Ξ D Mk))).
  Proof.
    intros * Hk Hh; cbn [grp_rank_iter]; rewrite Hk.
    destruct (im_head Mk) eqn:E; [ exfalso; exact (Hh _ eq_refl) | reflexivity | reflexivity ].
  Qed.

  (** The candidate rank of a member is stable after as many rounds as
      there are members below it. *)
  Lemma iter_stable : forall r k m, rk k = r -> rank_below k < m ->
      grp_rank_iter Θ Ξ D m k = grp_rank_iter Θ Ξ D (S m) k.
  Proof.
    induction r as [r IH] using lt_wf_ind; intros k m Hr Hm.
    destruct m as [| m]; [ lia |].
    destruct (ind_member D k) as [Mk |] eqn:Hk; [| rewrite !iter_nonmember by exact Hk; reflexivity ].
    destruct (mhead_decl_cases Mk) as [[pm Hh] | Hh]; [ cbn [grp_rank_iter]; rewrite Hk, Hh; reflexivity |].
    rewrite (iter_view m _ _ Hk Hh), (iter_view (S m) _ _ Hk Hh).
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
    destruct (mhead_decl_cases Mk) as [[pm Hh] | Hh].
    - rewrite Hh; cbn [grp_rank_iter]; unfold ind_member; rewrite HMk, Hh; reflexivity.
    - replace (match im_head Mk with
               | mh_decl _ => Nat.eqb (grp_rank_iter Θ Ξ D (S n') k) 0
               | _ => List.forallb (fun j => Nat.ltb (grp_rank_iter Θ Ξ D (S n') j) (grp_rank_iter Θ Ξ D (S n') k))
                        (member_nest_targets Θ Ξ D Mk)
               end)
        with (List.forallb (fun j => Nat.ltb (grp_rank_iter Θ Ξ D (S n') j) (grp_rank_iter Θ Ξ D (S n') k))
                (member_nest_targets Θ Ξ D Mk))
        by (destruct (im_head Mk) eqn:E; [ exfalso; exact (Hh _ eq_refl) | reflexivity | reflexivity ]).
      apply List.forallb_forall; intros j Hj; apply Nat.ltb_lt.
      assert (Hjk : rk j < rk k) by exact (member_nest_targets_lt _ _ _ HMk Hj).
      assert (Hj' : grp_rank_iter Θ Ξ D n' j = grp_rank_iter Θ Ξ D (S n') j).
      { assert (Hcase : (exists Mj, ind_member D j = Some Mj) \/ ind_member D j = None)
          by (destruct (ind_member D j); eauto).
        destruct Hcase as [[Mj Hjm] | Hjm].
        - assert (Hjn : j < S n') by (rewrite <- En; apply List.nth_error_Some; unfold ind_member in Hjm; congruence).
          pose proof (rank_below_lt k j ltac:(rewrite En; exact Hjn) Hjk).
          apply (iter_stable (rk j)); [ reflexivity | lia ].
        - rewrite !iter_nonmember by exact Hjm; reflexivity. }
      rewrite <- Hj', (iter_view n' _ _ HMk Hh).
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
  - intros k Mk Hk; destruct (im_head Mk) as [pm | qc k' Is vm | qr Is fl] eqn:Hh;
      [ left; intros; discriminate | | left; intros; discriminate ].
    destruct (f _ _ _ _ _ _ Hk Hh) as [HQ | HQ];
      [ left; intros ? ? ? ? [= <- <- <- <-]; exact HQ | right; intros H'; exact (HQ (H' _ _ _ _ eq_refl)) ].
  - left; intros * Hk Hh; exact (H _ _ Hk _ _ _ _ Hh).
  - right; intros H'; apply H; intros * Hk * Hh; exact (H' _ _ _ _ _ _ Hk Hh).
Defined.

(** A property of every record view of a group, decided at each. *)
Definition rviews_dec (D : ind_decl) (Q : nat -> imember -> qname -> list exp -> list string -> Prop)
    (f : forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
       {Q k Mk qr Is fl} + {~ Q k Mk qr Is fl}) :
  {forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl -> Q k Mk qr Is fl}
  + {~ forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl -> Q k Mk qr Is fl}.
Proof.
  destruct (members_dec D (fun k Mk => forall qr Is fl, im_head Mk = mh_record qr Is fl -> Q k Mk qr Is fl))
    as [H | H].
  - intros k Mk Hk; destruct (im_head Mk) as [pm | qc k' Is vm | qr Is fl] eqn:Hh;
      [ left; intros; discriminate | left; intros; discriminate |].
    destruct (f _ _ _ _ _ Hk Hh) as [HQ | HQ];
      [ left; intros ? ? ? [= <- <- <-]; exact HQ | right; intros H'; exact (HQ (H' _ _ _ eq_refl)) ].
  - left; intros * Hk Hh; exact (H _ _ Hk _ _ _ Hh).
  - right; intros H'; apply H; intros * Hk * Hh; exact (H' _ _ _ _ _ Hk Hh).
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
  - intros k Mk Hk; destruct (im_head Mk) as [pm | qc k' Is vm | qr Is fl] eqn:Hh;
      [ left; exists 0; intros; discriminate | | left; exists 0; intros; discriminate ].
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
  (** The fast context the decisions look names up in; the judgments are
      at the Core context it stands for. *)
  Variable F : FCtx.
  #[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  (** The decision of [levels_abstractable] the checker is given *)
  Variable levels_abstractable_dec : forall G Δ E, ⊢ Θ ⍮ Ξ ⍮ Δ ++ G ->
      { levels_abstractable Θ Ξ G Δ E } + { ~ levels_abstractable Θ Ξ G Δ E }.
  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.

  (** A term of a type in a context, which is checked first. *)
  Definition check_exp_at (Γ : ctx) (A M : exp) : {Θ ⍮ Ξ ⍮ Γ ⊢ M : A} + {~ Θ ⍮ Ξ ⍮ Γ ⊢ M : A} :=
    match check_ctx F levels_abstractable_dec HΞ Γ with
    | left HΓ => check_exp F levels_abstractable_dec Γ HΓ A M
    | right HnΓ => right (fun H => HnΓ (presup_exp_ctx H))
    end.

  Lemma typed_nbe_order' : forall Γ M A, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> nbe_order Θ Ξ Γ M A.
  Proof. intros * H; destruct (soundness H) as (W & HW & _); exact (nbe_order_sound _ _ _ _ _ _ HW). Qed.

  Lemma typ_nbe_ty_order : forall Γ A i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i -> nbe_ty_order Θ Ξ Γ A.
  Proof. intros * HA; destruct (@soundness_ty (fc_gctx F) _ _ _ HA) as [W [HW _]]; exact (nbe_ty_order_sound _ _ _ _ _ HW). Qed.

  (** A type of a sort in a context, which is checked first. *)
  Definition type_sorted_dec (Γ : ctx) (A : typ) :
      {r & {i | Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort r Typeω@i}} + {forall r i, ~ Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort r Typeω@i} :=
    match check_ctx F levels_abstractable_dec HΞ Γ with
    | left HΓ => check_type F levels_abstractable_dec Γ HΓ A
    | right HnΓ => inright (fun r i H => HnΓ (presup_exp_ctx H))
    end.

  (** A type in a context: [LevelSort], or a type of a sort. *)
  Definition type_dec (Γ : ctx) (A : typ) : {Θ ⍮ Ξ ⍮ Γ ⊢ᵗ A} + {~ Θ ⍮ Ξ ⍮ Γ ⊢ᵗ A}.
  Proof.
    destruct (check_ctx F levels_abstractable_dec HΞ Γ) as [HΓ | HnΓ]; [| right; intros H; exact (HnΓ (wf_type_ctx _ _ H)) ].
    destruct (exp_eq_dec A LevelSort) as [-> | HnL]; [ left; exact (wf_type_level_sort HΓ) |].
    destruct (check_type F levels_abstractable_dec Γ HΓ A) as [(r & i & HA) | HnA];
      [ left; exact (type_of_check_type F Γ A r i HA) | right ].
    intros H; inversion H as [A0 S HS HA0 | HG]; subst; [| exact (HnL eq_refl) ].
    destruct (type_sort_kind_sort _ HS) as (κ & i & ->); exact (HnA _ _ HA0).
  Defined.

  (** The least large universe a type is in: that of the universe it
      infers. *)
  Definition typ_least_dec (Γ : ctx) (A : typ) :
    { l | Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@l /\ forall j, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@j -> l <= j }
    + { forall j, ~ Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@j }.
  Proof.
    destruct (check_ctx F levels_abstractable_dec HΞ Γ) as [HΓ | HnΓ]; [| right; intros j H; exact (HnΓ (presup_exp_ctx H)) ].
    destruct (type_infer F levels_abstractable_dec Γ HΓ A (type_infer_order_all A))
      as [[UA HAi] | HnA]; [| right; exact (not_wf_typ_of_no_infer_gc _ _ HnA) ].
    destruct (univ_nf_idx_dec UA) as [[u Hu] | Hnu]; [| right; exact (not_wf_typ_of_infer_not_typ_gc _ _ _ HAi Hnu) ].
    left; exists (universe_nf_large_index u); split; [ exact (alg_type_infer_univ_sound_gc _ _ _ _ HAi Hu HΓ) |].
    intros j Hj.
    destruct (@alg_type_infer_large_typ_complete (fc_gctx F) Γ j A (user_exp_all _) Hj) as (UA' & u' & HAi' & Hu' & Hle).
    pose proof (@functional_alg_type_infer (fc_gctx F) _ _ _ _ HΞ HAi HAi') as <-.
    pose proof (is_univ_nf_functional _ _ _ Hu Hu') as <-.
    destruct u; cbn in Hle |- *; lia.
  Defined.

  (** The sort of a parameter: [LevelSort] for a type of levels, the
      universe at [l] otherwise *)
  Definition param_bool_sort (l : nat) (b : bool) : exp := if b then LevelSort else Typeω@l.

  Lemma param_bool_sort_ok : forall l b, parameter_sort l (param_bool_sort l b).
  Proof. intros l []; constructor. Qed.

  (** The parameters [Δ] over [Γ] are types of a universe at [l] or types
      of levels, as [bs] says of each, outermost first. *)
  Definition params_sorts_ok (Γ Δ : ctx) (l : nat) (bs : list bool) : Prop :=
    forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 ->
      Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ T : param_bool_sort l (List.nth (List.length Δ2) (List.rev bs) false).

  (** The flag of a parameter one more entry leaves in place *)
  Lemma nth_rev_cons_lt : forall (bs : list bool) b n, n < List.length bs ->
      List.nth n (List.rev (b :: bs)) false = List.nth n (List.rev bs) false.
  Proof. intros; cbn; rewrite List.app_nth1; [ reflexivity | rewrite List.length_rev; lia ]. Qed.

  Lemma nth_rev_cons_eq : forall (bs : list bool) b, List.nth (List.length bs) (List.rev (b :: bs)) false = b.
  Proof. intros; cbn; rewrite List.app_nth2; rewrite List.length_rev; [ rewrite Nat.sub_diag; reflexivity | lia ]. Qed.

  (** A level and the sorts of the assumptions of a telescope, each in the
      context of the entries after it: of the universe that contains every
      type of a universe among them, or of levels ([parameter_sort]). *)
  Fixpoint params_sorts_dec (Γ Δ : ctx) {struct Δ} :
    { lb : nat * list bool | List.length (snd lb) = List.length Δ /\ params_sorts_ok Γ Δ (fst lb) (snd lb) }
    + { forall l, ~ params_evaluated Θ Ξ Γ Δ l }.
  Proof.
    destruct Δ as [| e Δ'].
    - left; exists (0, nil); split; [ reflexivity | intros Δ1 κ T Δ2 E; exfalso; destruct Δ1; discriminate ].
    - destruct (params_sorts_dec Γ Δ') as [[[l' bs'] [Hlen Hok]] | Hn']; cbn [fst snd] in *;
        [| right; intros l H; apply (Hn' l); intros Δ1 κ T Δ2 E; apply (H (e :: Δ1) κ T Δ2); rewrite E; reflexivity ].
      (** The entries before, at a level at least [l'] *)
      assert (Htail : forall k b, l' <= k -> forall Δ1 κ T Δ2, Δ' = Δ1 ++ ce_ass κ T :: Δ2 ->
                 Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ T : param_bool_sort k (List.nth (List.length Δ2) (List.rev (b :: bs')) false)).
      { intros k b Hk Δ1 κ T Δ2 E.
        assert (Hlt : List.length Δ2 < List.length bs')
          by (rewrite Hlen, E, List.length_app; cbn; lia).
        rewrite (nth_rev_cons_lt _ _ _ Hlt).
        pose proof (Hok _ _ _ _ E) as HT.
        destruct (List.nth (List.length Δ2) (List.rev bs') false); cbn in HT |- *;
          [ exact HT | eapply (lift_exp_ge _ _ _ _ l'); [ exact Hk | exact HT ] ]. }
      destruct e as [κ T | T M | U | T M U].
      + destruct (typ_least_dec (Δ' ++ Γ) T) as [[lT [HT _]] | HnT].
        * left; exists (Nat.max l' lT, false :: bs'); cbn [fst snd]; split; [ cbn; lia |].
          intros [| e1 Δ1] κ0 T0 Δ2 E; cbn in E; injection E as E1 E2.
          -- subst; rewrite <- Hlen, nth_rev_cons_eq; cbn.
             eapply (lift_exp_ge _ _ _ _ lT); [ lia | exact HT ].
          -- subst; eapply Htail; [| reflexivity ]; lia.
        * destruct (check_exp_at (Δ' ++ Γ) LevelSort T) as [HL | HnL].
          -- left; exists (l', true :: bs'); cbn [fst snd]; split; [ cbn; lia |].
             intros [| e1 Δ1] κ0 T0 Δ2 E; cbn in E; injection E as E1 E2.
             ++ subst; rewrite <- Hlen, nth_rev_cons_eq; exact HL.
             ++ subst; eapply Htail; [| reflexivity ]; lia.
          -- right; intros l H; destruct (H nil κ T Δ' eq_refl) as [HT | HT]; [ exact (HnT l HT) | exact (HnL HT) ].
      + left; exists (l', false :: bs'); cbn [fst snd]; split; [ cbn; lia |].
        intros [| e1 Δ1] κ0 T0 Δ2 E; cbn in E; injection E as E1 E2; [ discriminate | subst; eapply Htail; [ lia | reflexivity ] ].
      + left; exists (l', false :: bs'); cbn [fst snd]; split; [ cbn; lia |].
        intros [| e1 Δ1] κ0 T0 Δ2 E; cbn in E; injection E as E1 E2; [ discriminate | subst; eapply Htail; [ lia | reflexivity ] ].
      + left; exists (l', false :: bs'); cbn [fst snd]; split; [ cbn; lia |].
        intros [| e1 Δ1] κ0 T0 Δ2 E; cbn in E; injection E as E1 E2; [ discriminate | subst; eapply Htail; [ lia | reflexivity ] ].
  Defined.

  (** The equality of two terms at a type: both checked there, normalized
      and compared up to proofs. *)
  Definition eq_at_dec (Γ : ctx) (A M N : exp) : {Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ N : A} + {~ Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ N : A}.
  Proof.
    destruct (check_exp_at Γ A M) as [HM | HnM]; [| right; intros H; apply HnM; gen_presups; assumption ].
    destruct (check_exp_at Γ A N) as [HN | HnN]; [| right; intros H; apply HnN; gen_presups; assumption ].
    destruct (nbe_impl F Γ M A (typed_nbe_order' _ _ _ HM)) as [W1 HW1].
    destruct (nbe_impl F Γ N A (typed_nbe_order' _ _ _ HN)) as [W2 HW2].
    destruct (nf_eq_upto_proofs_dec W1 W2) as [E | Hne]; [ left; exact (soundness_upto_proofs HM HN HW1 HW2 E) | right; intros H ].
    destruct (completeness H) as (W & W' & HMW & HNW & E).
    apply Hne; rewrite (functional_nbe _ _ _ _ _ HW1 HMW), (functional_nbe _ _ _ _ _ HW2 HNW); exact E.
  Defined.

  (** Types equal at a universe are equal at every universe both are in. *)
  Lemma typ_eq_at_level : forall Γ A A' i l, Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
      Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@l -> Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@l -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@l.
  Proof.
    intros * H HA HA'.
    destruct (completeness H) as (W & W' & HAW & HA'W & E).
    apply nbe_type_to_nbe_ty in HAW, HA'W.
    exact (@exp_eq_of_nbe_ty_same (fc_gctx F) _ _ _ _ _ _ (type_sort_universe l) HA HA' HAW HA'W E).
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

  (** Subtyping: both sides types, then the algorithmic check. *)
  Definition sub_dec (Γ : ctx) (A B : typ) : {Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ B} + {~ Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ B}.
  Proof.
    (** Both sides are types of sorts ([presup_subtyp_left_sorted]) *)
    destruct (type_sorted_dec Γ A) as [(rA & iA & HA) | HnA];
      [| right; intros H; destruct (presup_subtyp_left_sorted H) as (S & HS & HA');
         destruct (type_sort_kind_sort _ HS) as (κ & i & ->); exact (HnA _ _ HA') ].
    destruct (type_sorted_dec Γ B) as [(rB & iB & HB) | HnB];
      [| right; intros H; destruct (presup_subtyp_right_sorted H) as (S & HS & HB');
         destruct (type_sort_kind_sort _ HS) as (κ & i & ->); exact (HnB _ _ HB') ].
    pose proof (wf_type_of_sort _ (type_sort_kind_universe rA iA) HA) as HtA.
    pose proof (wf_type_of_sort _ (type_sort_kind_universe rB iB) HB) as HtB.
    destruct (subtyping_impl F Γ A B
                (@subtyping_order_run (fc_gctx F) Γ A B (nbe_order_of_type _ _ HtA) (nbe_order_of_type _ _ HtB))) as [Hs | Hns].
    - left; exact (@alg_subtyping_sound_sort (fc_gctx F) _ _ _ _ _ (type_sort_kind_universe rA iA) (type_sort_kind_universe rB iB) Hs HA HB).
    - right; intros H; exact (Hns (@alg_subtyping_complete (fc_gctx F) _ _ _ H)).
  Defined.

  (** The equality of two contexts' extensions, of assumptions on the
      left: entry by entry, each pair of types each below the other
      ([wf_ext_eq_ass]), each a type of its own sort. *)
  Fixpoint ext_eq_dec (Γ : ctx) (Ψ : ctx) {struct Ψ} :
    forall Ψ', all_assumptions Ψ -> {Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'} + {~ Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'}.
  Proof.
    intros Ψ' Hass; destruct Ψ as [| e Ψ0].
    - destruct Ψ' as [| e' Ψ0']; [| right; intros H; inversion H ].
      destruct (check_ctx F levels_abstractable_dec HΞ Γ) as [HΓ | HnΓ]; [ left; constructor; exact HΓ | right; intros H ].
      apply HnΓ; exact (presup_ext_eq_ctx H).
    - pose proof (List.Forall_inv_tail Hass) as Hass'.
      destruct e as [κ A | A M | U | A M U]; [| exfalso; destruct (List.Forall_inv Hass) as (? & ? & [=]) .. ].
      destruct Ψ' as [| [κ' A' | A' M' | U' | A' M' U'] Ψ0']; try (right; intros H; inversion H; fail).
      destruct (abs_kind_eq_dec κ κ') as [<- | Hκ]; [| right; intros H; inversion H; contradiction ].
      destruct (ext_eq_dec Γ Ψ0 Ψ0' Hass') as [Hr | Hr]; [| right; intros H; apply Hr; inversion H; assumption ].
      (** Each head: a type of the sort of the kind *)
      destruct (type_sorted_dec (Ψ0 ++ Γ) A) as [(rA & iA & HA) | HnA];
        [| right; intros H; destruct (ext_eq_ass_inv _ _ _ _ _ _ _ _ H) as [S HSk _ _ _ HA0 _ _ _];
           destruct (sort_kind_abs_kind_sort_inv _ _ HSk) as [j ->]; exact (HnA _ _ HA0) ].
      destruct (type_sorted_dec (Ψ0' ++ Γ) A') as [(rA' & iA' & HA') | HnA'];
        [| right; intros H; destruct (ext_eq_ass_inv _ _ _ _ _ _ _ _ H) as [_ _ S' HSk' _ _ HA0' _ _];
           destruct (sort_kind_abs_kind_sort_inv _ _ HSk') as [j ->]; exact (HnA' _ _ HA0') ].
      destruct (abs_kind_eq_dec rA κ) as [-> | HrA];
        [| right; intros H; destruct (ext_eq_ass_inv _ _ _ _ _ _ _ _ H) as [S HSk _ _ _ HA0 _ _ _];
           destruct (sort_kind_abs_kind_sort_inv _ _ HSk) as [j ->]; exact (HrA (kind_sort_unique _ _ _ _ _ _ HA HA0)) ].
      destruct (abs_kind_eq_dec rA' κ) as [-> | HrA'];
        [| right; intros H; destruct (ext_eq_ass_inv _ _ _ _ _ _ _ _ H) as [_ _ S' HSk' _ _ HA0' _ _];
           destruct (sort_kind_abs_kind_sort_inv _ _ HSk') as [j ->]; exact (HrA' (kind_sort_unique _ _ _ _ _ _ HA' HA0')) ].
      destruct (sub_dec (Ψ0 ++ Γ) A A') as [Hs | Hns];
        [| right; intros H; destruct (ext_eq_ass_inv _ _ _ _ _ _ _ _ H) as [_ _ _ _ _ _ _ Hs _]; exact (Hns Hs) ].
      destruct (sub_dec (Ψ0 ++ Γ) A' A) as [Hs' | Hns'];
        [| right; intros H; destruct (ext_eq_ass_inv _ _ _ _ _ _ _ _ H) as [_ _ _ _ _ _ _ _ Hs']; exact (Hns' Hs') ].
      left; eapply wf_ext_eq_ass; [ exact Hr | exact HA | apply sort_kind_abs_kind_sort | exact HA' | apply sort_kind_abs_kind_sort
                                  | exact Hs | exact Hs' ].
  Defined.
End Judgments.

(** A decision of a property, read off the decision of an equivalent one:
    the two conversions, by instantiation. *)
Ltac decision_left H := left; intros; eapply H; eassumption.
Ltac decision_right H := let H' := fresh "H" in right; intros H'; apply H; intros; eapply H'; eassumption.

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

(** ** Rewriting What a Decision Decides

    A decision of [P'] or [Q'] decides [P] or [Q] when they are the same
    propositions.  [rewrite_dec H] rewrites with [H] in the propositions a
    [sumbool] or [sumor] goal decides, the decision term untouched: a
    [rewrite] in the goal itself would build a computational [eq_rect]
    whose arguments name the sides of [H], which extraction then needs,
    even though it erases them; on a Core lookup of a fast context's
    decoding, that would pull the decoding into the extracted code
    ([Extraction.Decoding]). *)
Definition sumbool_iff {P Q P' Q' : Prop} (HP : P <-> P') (HQ : Q <-> Q') (d : {P'} + {Q'}) : {P} + {Q} :=
  match d with
  | left hp => left (proj2 HP hp)
  | right hq => right (proj2 HQ hq)
  end.

(** The same for a [sumor]: the witness kept, both Props rewritten by
    equivalences *)
Definition sumor_iff {A : Type} {P P' : A -> Prop} {Q Q' : Prop} (HP : forall a, P a <-> P' a) (HQ : Q <-> Q')
    (d : {a | P' a} + {Q'}) : {a | P a} + {Q} :=
  match d with
  | inleft (exist _ a hp) => inleft (exist _ a (proj2 (HP a) hp))
  | inright hq => inright (proj2 HQ hq)
  end.

Ltac rewrite_dec H :=
  first [ refine (sumbool_iff _ _ _); [ rewrite ?H; apply iff_refl | rewrite ?H; apply iff_refl | cbv beta ]
        | refine (sumor_iff _ _ _); [ intros; rewrite ?H; apply iff_refl | rewrite ?H; apply iff_refl | cbv beta ] ].

(** ** The Premises of the First Member, Decided

    [ind_nil_at], premise by premise.  The premises are named here, each
    the statement of [ind_nil_at]'s, and decided one at a time. *)

Section NilDecide.
  (** The fast context the decisions look names up in *)
  Variable F : FCtx.
  #[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  (** The decision of [levels_abstractable] the checker is given *)
  Variable levels_abstractable_dec : forall G Δ E, ⊢ Θ ⍮ Ξ ⍮ Δ ++ G ->
      { levels_abstractable Θ Ξ G Δ E } + { ~ levels_abstractable Θ Ξ G Δ E }.
  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.
  Variables (mp : qname) (D : ind_decl) (IsS : nat -> list exp).

  (** The uniform parameters end in the frames'. *)
  Definition uparams_suffix_dec : {Δ | ind_uparams D = Δ ++ gs_tele Ξ} + {forall Δ, ind_uparams D <> Δ ++ gs_tele Ξ}.
  Proof.
    (* the frames' telescope, computed fast; read in Core in the proofs
       only, so that no computational term mentions the decoding *)
    destruct (Compare_dec.le_dec (List.length (fc_tele F)) (List.length (ind_uparams D))) as [Hle | Hle];
      [| right; rewrite (fc_tele_ok F); intros Δ HΔ; apply Hle; rewrite HΔ, List.length_app; lia ].
    destruct (list_eq_dec centry_eq_dec (List.skipn (List.length (ind_uparams D) - List.length (fc_tele F)) (ind_uparams D))
                (fc_tele F)) as [E | E].
    - left; exists (List.firstn (List.length (ind_uparams D) - List.length (fc_tele F)) (ind_uparams D)).
      rewrite (fc_tele_ok F); rewrite <- E at 2; symmetry; apply List.firstn_skipn.
    - right; rewrite (fc_tele_ok F); intros Δ HΔ; apply E;
        rewrite HΔ, List.length_app, Nat.add_sub, List.skipn_app, List.skipn_all, Nat.sub_diag.
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
    destruct (im_head M0) as [pm | qc k Is vm | qr Is fl] eqn:Hh; [| right; intros M0' [[= <-] Hh']; congruence .. ].
    destruct (qname_eq_dec pm mp) as [-> | Hne]; [ left; exists M0; split; [ reflexivity | exact Hh ] |].
    right; intros M0' [[= <-] Hh']; rewrite Hh in Hh'; injection Hh' as ->; contradiction.
  Defined.

  (** Each member's non-uniform parameters are assumptions. *)
  Definition nparams_ass_dec :
    {forall k Mk, ind_member D k = Some Mk -> all_assumptions (im_nparams Mk)}
    + {~ forall k Mk, ind_member D k = Some Mk -> all_assumptions (im_nparams Mk)} :=
    members_dec D (fun _ Mk => all_assumptions (im_nparams Mk)) (fun _ Mk _ => all_assumptions_dec (im_nparams Mk)).

  (** Each member's constructor names are distinct. *)
  Definition members_nodup_dec :
    {forall k Mk, ind_member D k = Some Mk -> List.NoDup (List.map fst (im_cons Mk))}
    + {~ forall k Mk, ind_member D k = Some Mk -> List.NoDup (List.map fst (im_cons Mk))} :=
    members_dec D (fun _ Mk => List.NoDup (List.map fst (im_cons Mk))) (fun _ Mk _ => nodup_dec (List.map fst (im_cons Mk))).

  (** Each non-uniform parameter is in the sort. *)
  Definition nparams_sort_dec :
    {forall k Mk Δ1 κ T Δ2, ind_member D k = Some Mk -> im_nparams Mk = Δ1 ++ ce_ass κ T :: Δ2 ->
       Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ}
    + {~ forall k Mk Δ1 κ T Δ2, ind_member D k = Some Mk -> im_nparams Mk = Δ1 ++ ce_ass κ T :: Δ2 ->
       Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ}.
  Proof.
    destruct (members_dec D (fun _ Mk => forall Δ1 e Δ2, im_nparams Mk = Δ1 ++ e :: Δ2 -> forall κ T, e = ce_ass κ T ->
                Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ)) as [H | H].
    - intros k Mk _; apply forall_split_dec; intros Δ1 [κ T | T M | U | T M U] Δ2 _; [| left; intros ? ? [=] .. ].
      destruct (check_exp_at F levels_abstractable_dec HΞ (Δ2 ++ ind_uparams D) (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ T) as [HT | HT];
        [ left; intros ? ? [= <- <-]; exact HT | right; intros H; exact (HT (H κ T eq_refl)) ].
    - left; intros k Mk Δ1 κ T Δ2 Hk E; exact (H k Mk Hk Δ1 _ Δ2 E κ T eq_refl).
    - right; intros H'; apply H; intros k Mk Hk Δ1 e Δ2 E κ T ->; exact (H' k Mk Δ1 κ T Δ2 Hk E).
  Defined.

  (** The non-uniform parameters are of the sort, a universe: of the kind
      [ak_relevant]. *)
  Definition nparams_relevant_dec :
    {forall k Mk Δ1 κ T Δ2, ind_member D k = Some Mk -> im_nparams Mk = Δ1 ++ ce_ass κ T :: Δ2 -> κ = ak_relevant}
    + {~ forall k Mk Δ1 κ T Δ2, ind_member D k = Some Mk -> im_nparams Mk = Δ1 ++ ce_ass κ T :: Δ2 -> κ = ak_relevant}.
  Proof.
    destruct (members_dec D (fun _ Mk => forall Δ1 e Δ2, im_nparams Mk = Δ1 ++ e :: Δ2 -> forall κ T, e = ce_ass κ T ->
                κ = ak_relevant)) as [H | H].
    - intros k Mk _; apply forall_split_dec; intros Δ1 [κ T | T M | U | T M U] Δ2 _; [| left; intros ? ? [=] .. ].
      destruct (abs_kind_eq_dec κ ak_relevant) as [E | E];
        [ left; intros ? ? [= <- <-]; exact E | right; intros H; exact (E (H κ T eq_refl)) ].
    - left; intros k Mk Δ1 κ T Δ2 Hk E; exact (H k Mk Hk Δ1 _ Δ2 E κ T eq_refl).
    - right; intros H'; apply H; intros k Mk Hk Δ1 e Δ2 E κ T ->; exact (H' k Mk Δ1 κ T Δ2 Hk E).
  Defined.

  (** Each non-recursive argument is in the sort its tag gives: the
      declaration's at [relevant], [Prop] at [propositional]. *)
  Definition args_sort_dec :
    {forall k Mk c gs gs1 r A gs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_arg r A :: gs2 ->
       Θ ⍮ Ξ ⍮ cargs_nonrec_ctx gs1 ++ im_params D Mk
         ⊢ A : abs_kind_sort r (ind_sort D)[wk_shiftn (List.length (cargs_nonrec_ctx gs1) + im_nn Mk)]ʷ}
    + {~ forall k Mk c gs gs1 r A gs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_arg r A :: gs2 ->
       Θ ⍮ Ξ ⍮ cargs_nonrec_ctx gs1 ++ im_params D Mk
         ⊢ A : abs_kind_sort r (ind_sort D)[wk_shiftn (List.length (cargs_nonrec_ctx gs1) + im_nn Mk)]ʷ}.
  Proof.
    destruct (members_dec D (fun _ Mk => forall cg, In cg (im_cons Mk) -> forall gs1 g gs2, snd cg = gs1 ++ g :: gs2 ->
                forall r A, g = ca_arg r A ->
                Θ ⍮ Ξ ⍮ cargs_nonrec_ctx gs1 ++ im_params D Mk
                  ⊢ A : abs_kind_sort r (ind_sort D)[wk_shiftn (List.length (cargs_nonrec_ctx gs1) + im_nn Mk)]ʷ)) as [H | H].
    - intros k Mk _; apply forall_in_dec; intros cg _; apply forall_split_dec; intros gs1 [r A | t] gs2 _; [| left; intros ? ? [=] ].
      destruct (check_exp_at F levels_abstractable_dec HΞ (cargs_nonrec_ctx gs1 ++ im_params D Mk)
                  (abs_kind_sort r (ind_sort D)[wk_shiftn (List.length (cargs_nonrec_ctx gs1) + im_nn Mk)]ʷ) A) as [HA | HA];
        [ left; intros ? ? [= <- <-]; exact HA | right; intros H; exact (HA (H r A eq_refl)) ].
    - left; intros k Mk c gs gs1 r A gs2 Hk Hin E; exact (H k Mk Hk (c, gs) Hin gs1 _ gs2 E r A eq_refl).
    - right; intros H'; apply H; intros k Mk Hk [c gs] Hin gs1 g gs2 E r A ->; exact (H' k Mk c gs gs1 r A gs2 Hk Hin E).
  Defined.

  (** No non-recursive argument is of a type of levels ([carg_kind]). *)
  Definition args_kind_dec :
    {forall k Mk c gs gs1 r A gs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_arg r A :: gs2 ->
       carg_kind r}
    + {~ forall k Mk c gs gs1 r A gs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_arg r A :: gs2 ->
       carg_kind r}.
  Proof.
    destruct (members_dec D (fun _ Mk => forall cg, In cg (im_cons Mk) -> forall gs1 g gs2, snd cg = gs1 ++ g :: gs2 ->
                forall r A, g = ca_arg r A -> carg_kind r)) as [H | H].
    - intros k Mk _; apply forall_in_dec; intros cg _; apply forall_split_dec; intros gs1 [r A | t] gs2 _; [| left; intros ? ? [=] ].
      destruct r; [ left; intros ? ? [= <- <-]; constructor | left; intros ? ? [= <- <-]; constructor
                  | right; intros H; specialize (H ak_level A eq_refl); inversion H ].
    - left; intros k Mk c gs gs1 r A gs2 Hk Hin E; exact (H k Mk Hk (c, gs) Hin gs1 _ gs2 E r A eq_refl).
    - right; intros H'; apply H; intros k Mk Hk [c gs] Hin gs1 g gs2 E r A ->; exact (H' k Mk c gs gs1 r A gs2 Hk Hin E).
  Defined.

  (** Each domain of a recursive argument's shape is in the sort. *)
  Definition doms_sort_dec :
    {forall k Mk c gs gs1 t gs2 Bs1 B Bs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) ->
       gs = gs1 ++ ca_rec t :: gs2 -> ptyp_doms t = Bs1 ++ B :: Bs2 ->
       Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ cargs_nonrec_ctx gs1 ++ im_params D Mk
         ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_nonrec_ctx gs1) + im_nn Mk)]ʷ}
    + {~ forall k Mk c gs gs1 t gs2 Bs1 B Bs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) ->
       gs = gs1 ++ ca_rec t :: gs2 -> ptyp_doms t = Bs1 ++ B :: Bs2 ->
       Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ cargs_nonrec_ctx gs1 ++ im_params D Mk
         ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_nonrec_ctx gs1) + im_nn Mk)]ʷ}.
  Proof.
    destruct (members_dec D (fun _ Mk => forall cg, In cg (im_cons Mk) -> forall gs1 g gs2, snd cg = gs1 ++ g :: gs2 ->
                forall t, g = ca_rec t -> forall Bs1 B Bs2, ptyp_doms t = Bs1 ++ B :: Bs2 ->
                Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ cargs_nonrec_ctx gs1 ++ im_params D Mk
                  ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_nonrec_ctx gs1) + im_nn Mk)]ʷ)) as [H | H].
    - intros k Mk _; apply forall_in_dec; intros cg _; apply forall_split_dec; intros gs1 [A | t] gs2 _; [ left; intros ? [=] |].
      destruct (forall_split_dec (ptyp_doms t)
                  (fun Bs1 B Bs2 => Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ cargs_nonrec_ctx gs1 ++ im_params D Mk
                     ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_nonrec_ctx gs1) + im_nn Mk)]ʷ))
        as [HB | HB].
      + intros Bs1 B Bs2 _.
        exact (check_exp_at F levels_abstractable_dec HΞ (doms_ctx Bs1 ++ cargs_nonrec_ctx gs1 ++ im_params D Mk)
                 (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_nonrec_ctx gs1) + im_nn Mk)]ʷ B).
      + left; intros ? [= <-]; exact HB.
      + right; intros H; exact (HB (H t eq_refl)).
    - left; intros k Mk c gs gs1 t gs2 Bs1 B Bs2 Hk Hin E Ed; exact (H k Mk Hk (c, gs) Hin gs1 _ gs2 E t eq_refl Bs1 B Bs2 Ed).
    - right; intros H'; apply H; intros k Mk Hk [c gs] Hin gs1 g gs2 E t -> Bs1 B Bs2 Ed;
        exact (H' k Mk c gs gs1 t gs2 Bs1 B Bs2 Hk Hin E Ed).
  Defined.

  (** Each recursive argument gives its member as many parameters as it
      has. *)
  Definition params_length_dec :
    {forall k Mk c gs, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> cargs_params_length D gs}
    + {~ forall k Mk c gs, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> cargs_params_length D gs}.
  Proof.
    destruct (members_dec D (fun _ Mk => forall cg, In cg (im_cons Mk) -> cargs_params_length D (snd cg))) as [H | H].
    - intros k Mk _; apply forall_in_dec; intros cg _; unfold cargs_params_length.
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
                    (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec_ctx gs1) + im_nn Mk))) (ptyp_ps t)) j
         = Some T ->
       Θ ⍮ Ξ ⍮ ptyp_tele t ++ cargs_nonrec_ctx gs1 ++ im_params D Mk ⊢ P : T}
    + {~ forall k Mk c gs gs1 t gs2 Mj j P T, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) ->
       gs = gs1 ++ ca_rec t :: gs2 -> ind_member D (ptyp_mem t) = Some Mj ->
       nth_error (ptyp_ps t) j = Some P ->
       nth_error (tele_insts (im_nparams Mj)
                    (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec_ctx gs1) + im_nn Mk))) (ptyp_ps t)) j
         = Some T ->
       Θ ⍮ Ξ ⍮ ptyp_tele t ++ cargs_nonrec_ctx gs1 ++ im_params D Mk ⊢ P : T}.
  Proof.
    destruct (members_dec D (fun _ Mk => forall cg, In cg (im_cons Mk) -> forall gs1 g gs2, snd cg = gs1 ++ g :: gs2 ->
                forall t, g = ca_rec t -> forall Mj, ind_member D (ptyp_mem t) = Some Mj ->
                forall j P T, nth_error (ptyp_ps t) j = Some P ->
                nth_error (tele_insts (im_nparams Mj)
                             (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec_ctx gs1) + im_nn Mk))) (ptyp_ps t)) j
                  = Some T ->
                Θ ⍮ Ξ ⍮ ptyp_tele t ++ cargs_nonrec_ctx gs1 ++ im_params D Mk ⊢ P : T)) as [H | H].
    - intros k Mk _; apply forall_in_dec; intros cg _; apply forall_split_dec; intros gs1 [A | t] gs2 _; [ left; intros ? [=] |].
      destruct (ind_member D (ptyp_mem t)) as [Mj |] eqn:Hj; [| left; intros ? [= <-] Mj' Hj'; rewrite Hj in Hj'; discriminate ].
      destruct (forall_nth2_dec (fun P T => Θ ⍮ Ξ ⍮ ptyp_tele t ++ cargs_nonrec_ctx gs1 ++ im_params D Mk ⊢ P : T)
                  (fun P T => check_exp_at F levels_abstractable_dec HΞ (ptyp_tele t ++ cargs_nonrec_ctx gs1 ++ im_params D Mk) T P) (ptyp_ps t)
                  (tele_insts (im_nparams Mj)
                     (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_nonrec_ctx gs1) + im_nn Mk))) (ptyp_ps t)))
        as [HP | HP].
      + left; intros ? [= <-] Mj' Hj'; rewrite Hj in Hj'; injection Hj' as <-; exact HP.
      + right; intros H; exact (HP (H t eq_refl Mj Hj)).
    - left; intros k Mk c gs gs1 t gs2 Mj j P T Hk Hin E Hj HP HT; exact (H k Mk Hk (c, gs) Hin gs1 _ gs2 E t eq_refl Mj Hj j P T HP HT).
    - right; intros H'; apply H; intros k Mk Hk [c gs] Hin gs1 g gs2 E t -> Mj Hj j P T HP HT;
        exact (H' k Mk c gs gs1 t gs2 Mj j P T Hk Hin E Hj HP HT).
  Defined.

  (** The correspondence of a view's arguments with its container's,
      computed. *)
  Definition cargs_correspond_dec (vm : list nat) (gs' gs : list carg) : {cargs_correspond vm gs' gs} + {~ cargs_correspond vm gs' gs} :=
    match cargs_correspondb vm gs' gs as b return cargs_correspondb vm gs' gs = b -> _ with
    | true => fun E => left (cargs_correspondb_sound _ _ _ E)
    | false => fun E => right (fun H => diff_false_true (eq_trans (eq_sym E) (cargs_correspondb_complete _ _ _ H)))
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
         (forall c gs' gs, ind_con Mk' c = Some gs' -> ind_con Mk c = Some gs -> cargs_correspond vm gs' gs)}
    + {~ forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       exists D' Mk', ind_lookup Θ Ξ qc = Some D' /\ ind_member D' k' = Some Mk' /\ k' < ind_ndecl D' /\
         List.length Is = ind_nu D' /\ List.length vm = List.length (ind_members D') /\
         List.nth_error vm k' = Some k /\
         List.map fst (im_cons Mk) = List.map fst (im_cons Mk') /\
         (forall c gs' gs, ind_con Mk' c = Some gs' -> ind_con Mk c = Some gs -> cargs_correspond vm gs' gs)}.
  Proof.
    apply views_dec; intros k Mk qc k' Is vm Hk Hh.
    Local Ltac views_exist_reject :=
      let H := fresh "H" in
      right; intros H; destruct H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?); unify_found; first [ contradiction | congruence ].
    destruct (ind_lookup_f F qc) as [[D' |] Hl]; rewrite_dec Hl; [| views_exist_reject ].
    destruct (ind_member D' k') as [Mk' |] eqn:Hk'; [| views_exist_reject ].
    destruct (Compare_dec.lt_dec k' (ind_ndecl D')) as [Hlt | Hlt]; [| views_exist_reject ].
    destruct (Nat.eq_dec (List.length Is) (ind_nu D')) as [HIs | HIs]; [| views_exist_reject ].
    destruct (Nat.eq_dec (List.length vm) (List.length (ind_members D'))) as [Hvm | Hvm]; [| views_exist_reject ].
    destruct (option_nat_eq_dec (List.nth_error vm k') (Some k)) as [Hvk | Hvk]; [| views_exist_reject ].
    destruct (list_eq_dec string_dec (List.map fst (im_cons Mk)) (List.map fst (im_cons Mk'))) as [Hn | Hn];
      [| views_exist_reject ].
    destruct (con_pairs_dec Mk' Mk (fun _ gs' gs => cargs_correspond vm gs' gs) (fun _ gs' gs _ _ => cargs_correspond_dec vm gs' gs))
      as [Hc | Hc]; [| views_exist_reject ].
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
  Definition instances_typed_dec :
    {forall k Mk qc k' Is vm D' j I T, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> nth_error (IsS k) j = Some I ->
       nth_error (tele_insts (ind_uparams D') Id (IsS k)) j = Some T ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ I : T}
    + {~ forall k Mk qc k' Is vm D' j I T, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> nth_error (IsS k) j = Some I ->
       nth_error (tele_insts (ind_uparams D') Id (IsS k)) j = Some T ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ I : T}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall j I T, nth_error (IsS k) j = Some I -> nth_error (tele_insts (ind_uparams D') Id (IsS k)) j = Some T ->
                Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ I : T)) as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup_f F qc) as [[D' |] Hl]; rewrite_dec Hl; [| left; intros ? [=] ].
      destruct (forall_nth2_dec (fun I T => Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ I : T) (fun I T => check_exp_at F levels_abstractable_dec HΞ (grp_selfs_ctx D) T I)
                  (IsS k) (tele_insts (ind_uparams D') Id (IsS k))) as [HI | HI];
        [ left; intros ? [= <-]; exact HI | right; intros H; exact (HI (H _ eq_refl)) ].
    - decision_left H.
    - decision_right H.
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
      destruct (ind_lookup_f F qc) as [[D' |] Hl]; rewrite_dec Hl; [| left; intros ? [=] ].
      destruct (members_dec D' (fun i' Mi' => forall pm', im_head Mi' = mh_decl pm' -> forall v, nth_error vm i' = Some v ->
                  exists Mv vm', ind_member D v = Some Mv /\ im_head Mv = mh_view qc i' Is vm')) as [HM | HM].
      + intros i' Mi' _.
        destruct (im_head Mi') as [pm' | q2 k2 Is2 vm2 | q2 Is2 fl2] eqn:Hh'; [| left; intros ? [=] .. ].
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| left; intros ? _ ? [=] ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv;
          [| right; intros H; destruct (H pm' eq_refl v eq_refl) as (? & ? & Hm & _); rewrite Hmv in Hm; discriminate ].
        destruct (im_head Mv) as [pmv | qv kv Iv vmv | qv Iv flv] eqn:Hhv;
          [ right; intros H; destruct (H pm' eq_refl v eq_refl) as (? & ? & Hm & Hhm); rewrite Hmv in Hm; injection Hm as <-;
            congruence | |
            right; intros H; destruct (H pm' eq_refl v eq_refl) as (? & ? & Hm & Hhm); rewrite Hmv in Hm; injection Hm as <-;
            congruence ].
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
    - decision_left H.
    - decision_right H.
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
      destruct (ind_lookup_f F qc) as [[D' |] Hl]; rewrite_dec Hl; [| left; intros ? [=] ].
      destruct (members_dec D' (fun i' Mi' => forall q'' k'' Is'' vm'', im_head Mi' = mh_view q'' k'' Is'' vm'' ->
                  forall v, nth_error vm i' = Some v ->
                  exists Mv X vm', ind_member D v = Some Mv /\ im_head Mv = mh_view q'' k'' X vm' /\
                    List.length X = List.length Is'')) as [HM | HM].
      + intros i' Mi' _.
        destruct (im_head Mi') as [pm' | q2 k2 Is2 vm2 | q2 Is2 fl2] eqn:Hh'; [ left; intros ? ? ? ? [=] | | left; intros ? ? ? ? [=] ].
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| left; intros ? ? ? ? _ ? [=] ].
        Local Ltac view_maps_len_reject Hmv Hhv :=
          let H := fresh "H" in
          right; intros H; destruct (H _ _ _ _ eq_refl _ eq_refl) as (? & ? & ? & Hm & Hhm & Hlen);
          rewrite Hmv in Hm; try (injection Hm as <-; rewrite Hhv in Hhm; injection Hhm; intros; subst); first [ discriminate | contradiction | congruence ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv; [| right; intros H; destruct (H _ _ _ _ eq_refl _ eq_refl) as (? & ? & ? & Hm & _);
                                                            rewrite Hmv in Hm; discriminate ].
        destruct (im_head Mv) as [pmv | qv kv Iv vmv | qv Iv flv] eqn:Hhv;
          [ right; intros H; destruct (H _ _ _ _ eq_refl _ eq_refl) as (? & ? & ? & Hm & Hhm & _); rewrite Hmv in Hm;
            injection Hm as <-; congruence | |
            right; intros H; destruct (H _ _ _ _ eq_refl _ eq_refl) as (? & ? & ? & Hm & Hhm & _); rewrite Hmv in Hm;
            injection Hm as <-; congruence ].
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
    - decision_left H.
    - decision_right H.
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
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)]}
    + {~ forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm' j' C C' T,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' ->
       ind_lookup Θ Ξ q'' = Some D'' ->
       nth_error vm i' = Some v -> ind_member D v = Some Mv -> im_head Mv = mh_view q'' k'' X vm' ->
       nth_error (IsS v) j' = Some C ->
       nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
       nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)]}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall i' Mi', ind_member D' i' = Some Mi' -> forall q'' k'' Is'' vm'', im_head Mi' = mh_view q'' k'' Is'' vm'' ->
                forall D'', ind_lookup Θ Ξ q'' = Some D'' -> forall v, nth_error vm i' = Some v ->
                forall Mv, ind_member D v = Some Mv -> forall X vm', im_head Mv = mh_view q'' k'' X vm' ->
                forall j' C C' T, nth_error (IsS v) j' = Some C ->
                nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
                nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T ->
                Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)])) as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup_f F qc) as [[D' |] Hl]; rewrite_dec Hl; [| left; intros ? [=] ].
      destruct (members_dec D' (fun i' Mi' => forall q'' k'' Is'' vm'', im_head Mi' = mh_view q'' k'' Is'' vm'' ->
                  forall D'', ind_lookup Θ Ξ q'' = Some D'' -> forall v, nth_error vm i' = Some v ->
                  forall Mv, ind_member D v = Some Mv -> forall X vm', im_head Mv = mh_view q'' k'' X vm' ->
                  forall j' C C' T, nth_error (IsS v) j' = Some C ->
                  nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
                  nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T ->
                  Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)])) as [HM | HM].
      + intros i' Mi' _.
        destruct (im_head Mi') as [pm' | q2 k2 Is2 vm2 | q2 Is2 fl2] eqn:Hh'; [ vacuous | | vacuous ].
        destruct (ind_lookup_f F q2) as [[D2 |] Hl2]; rewrite_dec Hl2; [| vacuous ].
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| vacuous ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv; [| vacuous ].
        destruct (im_head Mv) as [pmv | qv kv Iv vmv | qv Iv flv] eqn:Hhv; [ vacuous | | vacuous ].
        destruct (qname_eq_dec qv q2) as [-> | Hq]; [| vacuous ].
        destruct (Nat.eq_dec kv k2) as [-> | Hk2]; [| vacuous ].
        destruct (forall_nth3_dec (fun C C' T => Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)])
                    (fun C C' T => eq_at_dec F levels_abstractable_dec HΞ (grp_selfs_ctx D) T[sb_of_list Id (IsS k)] C C')
                    (IsS v) (List.map (fun I => I[sb_of_list Id (IsS k)]) Is2) (tele_insts (ind_uparams D2) Id Is2))
          as [HC | HC].
        * left; intros ? ? ? ? [= <- <- <- <-] D2' Hl2' v' Hv' Mv' Hmv' X vm' Hhv'; unify_found; intros; eapply HC; eassumption.
        * right; intros H; exact (HC (H _ _ _ _ eq_refl _ Hl2 _ eq_refl _ Hmv _ _ Hhv)).
      + left; intros ? [= <-]; exact HM.
      + right; intros H'; apply HM; exact (H' D' eq_refl).
    - decision_left H.
    - decision_right H.
  Defined.

  (** A mapped member's non-uniform parameters are the container
      member's at the instance. *)
  Definition nparams_eq_dec (HPass : forall k Mk, ind_member D k = Some Mk -> all_assumptions (im_nparams Mk)) :
    {forall k Mk qc k' Is vm D' i' Mi' v Mv, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ˣ tele_wk (im_nparams Mv) (self_wk D 0) ≈ tele_sub (im_nparams Mi') (sb_of_list Id (IsS k))}
    + {~ forall k Mk qc k' Is vm D' i' Mi' v Mv, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ˣ tele_wk (im_nparams Mv) (self_wk D 0) ≈ tele_sub (im_nparams Mi') (sb_of_list Id (IsS k))}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall i' Mi', ind_member D' i' = Some Mi' -> forall v, nth_error vm i' = Some v ->
                forall Mv, ind_member D v = Some Mv ->
                Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ˣ tele_wk (im_nparams Mv) (self_wk D 0) ≈ tele_sub (im_nparams Mi') (sb_of_list Id (IsS k))))
      as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup_f F qc) as [[D' |] Hl]; rewrite_dec Hl; [| left; intros ? [=] ].
      destruct (members_dec D' (fun i' Mi' => forall v, nth_error vm i' = Some v -> forall Mv, ind_member D v = Some Mv ->
                  Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ˣ tele_wk (im_nparams Mv) (self_wk D 0)
                    ≈ tele_sub (im_nparams Mi') (sb_of_list Id (IsS k)))) as [HM | HM].
      + intros i' Mi' _.
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| left; intros ? [=] ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv; [| vacuous ].
        destruct (ext_eq_dec F levels_abstractable_dec HΞ (grp_selfs_ctx D) (tele_wk (im_nparams Mv) (self_wk D 0))
                    (tele_sub (im_nparams Mi') (sb_of_list Id (IsS k))) (all_assumptions_wk _ _ (HPass _ _ Hmv))) as [HE | HE];
          [ left; intros; unify_found; exact HE | right; intros H; exact (HE (H _ eq_refl _ Hmv)) ].
      + left; intros ? [= <-]; exact HM.
      + right; intros H'; apply HM; exact (H' D' eq_refl).
    - decision_left H.
    - decision_right H.
  Defined.

  (** A mapped member's constructor arguments are the container member's
      at the instance. *)
  Definition cargs_eq_dec :
    {forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       Θ ⍮ Ξ ⍮ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
         ⊢ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id (IsS k))) ≈ self_cargs_ctx D IsS Mv gs}
    + {~ forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       Θ ⍮ Ξ ⍮ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
         ⊢ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id (IsS k))) ≈ self_cargs_ctx D IsS Mv gs}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall i' Mi', ind_member D' i' = Some Mi' -> forall v, nth_error vm i' = Some v ->
                forall Mv, ind_member D v = Some Mv -> forall c gs' gs, ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
                Θ ⍮ Ξ ⍮ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
                  ⊢ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id (IsS k))) ≈ self_cargs_ctx D IsS Mv gs))
      as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup_f F qc) as [[D' |] Hl]; rewrite_dec Hl; [| left; intros ? [=] ].
      destruct (members_dec D' (fun i' Mi' => forall v, nth_error vm i' = Some v -> forall Mv, ind_member D v = Some Mv ->
                  forall c gs' gs, ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
                  Θ ⍮ Ξ ⍮ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
                    ⊢ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id (IsS k))) ≈ self_cargs_ctx D IsS Mv gs))
        as [HM | HM].
      + intros i' Mi' _.
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| left; intros ? [=] ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv; [| vacuous ].
        destruct (con_pairs_dec Mi' Mv (fun c gs' gs => Θ ⍮ Ξ ⍮ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
                    ⊢ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id (IsS k))) ≈ self_cargs_ctx D IsS Mv gs))
          as [HC | HC].
        * intros c gs' gs _ _.
          exact (ext_eq_dec F levels_abstractable_dec HΞ _ _ _ (all_assumptions_sub _ _ (cargs_ctx_aux_ass _ _ _ _ _))).
        * left; intros; unify_found; eapply HC; eauto.
        * right; intros H; exact (HC (H _ eq_refl _ Hmv)).
      + left; intros ? [= <-]; exact HM.
      + right; intros H'; apply HM; exact (H' D' eq_refl).
    - decision_left H.
    - decision_right H.
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
      destruct (ind_lookup_f F qc) as [[D' |] Hl]; rewrite_dec Hl; [| vacuous ].
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
    - decision_left H.
    - decision_right H.
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
      destruct (ind_lookup_f F qc) as [[D' |] Hl]; rewrite_dec Hl; [| left; exists 0; intros; unify_found; congruence ].
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
       Θ ⍮ Ξ ⍮ tele_wk (shape_domains_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t))) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
         ⊢ (ptyp_dom_at (cargs_pat gs1') d t')[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
         ≈ (ptyp_dom_at (cargs_pat gs1) d t)[self_wk D (d + List.length gs1 + im_nn Mv)]ʷ : Typeω@i}
    + {forall i, ~ forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 d,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       d < ptyp_depth t ->
       Θ ⍮ Ξ ⍮ tele_wk (shape_domains_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t))) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
         ⊢ (ptyp_dom_at (cargs_pat gs1') d t')[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
         ≈ (ptyp_dom_at (cargs_pat gs1) d t)[self_wk D (d + List.length gs1 + im_nn Mv)]ʷ : Typeω@i}.
  Proof.
    destruct (view_rec_pairs_bound_dec
                (fun k qc D' Mi' Mv gs1' t' gs1 t i => forall d, d < ptyp_depth t ->
                   Θ ⍮ Ξ ⍮ tele_wk (shape_domains_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t))) (self_wk D (List.length gs1 + im_nn Mv))
                             ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
                     ⊢ (ptyp_dom_at (cargs_pat gs1') d t')[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
                     ≈ (ptyp_dom_at (cargs_pat gs1) d t)[self_wk D (d + List.length gs1 + im_nn Mv)]ʷ : Typeω@i))
      as [[i H] | H].
    - intros ? ? ? ? ? ? ? ? ? ? ? Hle HQ d Hd; exact (lift_exp_eq_ge _ _ _ _ _ _ _ Hle (HQ d Hd)).
    - intros k qc D' Mi' Mv gs1' t' gs1 t.
      destruct (bound_in_dec (fun d i =>
                  Θ ⍮ Ξ ⍮ tele_wk (shape_domains_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t))) (self_wk D (List.length gs1 + im_nn Mv))
                            ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
                    ⊢ (ptyp_dom_at (cargs_pat gs1') d t')[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
                    ≈ (ptyp_dom_at (cargs_pat gs1) d t)[self_wk D (d + List.length gs1 + im_nn Mv)]ʷ : Typeω@i)
                  (fun d l l' Hle HQ => lift_exp_eq_ge _ _ _ _ _ _ _ Hle HQ) (List.seq 0 (ptyp_depth t))) as [[i HD] | HD].
      + intros d _; exact (typ_eq_least_dec F levels_abstractable_dec HΞ _ _ _).
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
       Θ ⍮ Ξ ⍮ tele_wk (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
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
       Θ ⍮ Ξ ⍮ tele_wk (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
         ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
         : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ}.
  Proof.
    destruct (view_rec_pairs_dec (fun k qc D' Mi' Mv gs1' t' gs1 t => forall Mj, ind_member D (ptyp_mem t) = Some Mj ->
                forall j P' P T, nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P' ->
                nth_error (ptyp_ps_at (cargs_pat gs1) t) j = Some P ->
                nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                             (ptyp_ps_at (cargs_pat gs1) t)) j = Some T ->
                Θ ⍮ Ξ ⍮ tele_wk (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                          ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
                  ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
                  : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ)) as [H | H].
    - intros k qc D' Mi' Mv gs1' t' gs1 t.
      destruct (ind_member D (ptyp_mem t)) as [Mj |] eqn:Hj; [| vacuous ].
      destruct (forall_nth3_dec
                  (fun P' P T => Θ ⍮ Ξ ⍮ tele_wk (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                                         ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
                     ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
                     : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ)
                  (fun P' P T => check_exp_at F levels_abstractable_dec HΞ _ _ _)
                  (ptyp_ps_at (cargs_pat gs1') t') (ptyp_ps_at (cargs_pat gs1) t)
                  (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                     (ptyp_ps_at (cargs_pat gs1) t))) as [HP | HP].
      + left; intros; unify_found; eapply HP; eauto.
      + right; intros H; apply HP; intros; eapply H; eauto.
    - decision_left H.
    - decision_right H.
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
       Θ ⍮ Ξ ⍮ tele_wk (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
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
       Θ ⍮ Ξ ⍮ tele_wk (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
         ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
         ≈ P[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ
         : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ}.
  Proof.
    destruct (view_rec_pairs_dec (fun k qc D' Mi' Mv gs1' t' gs1 t => forall Mj, ind_member D (ptyp_mem t) = Some Mj ->
                forall j P' P T, nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P' ->
                nth_error (ptyp_ps_at (cargs_pat gs1) t) j = Some P ->
                nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                             (ptyp_ps_at (cargs_pat gs1) t)) j = Some T ->
                Θ ⍮ Ξ ⍮ tele_wk (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                          ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
                  ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
                  ≈ P[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ
                  : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ)) as [H | H].
    - intros k qc D' Mi' Mv gs1' t' gs1 t.
      destruct (ind_member D (ptyp_mem t)) as [Mj |] eqn:Hj; [| vacuous ].
      destruct (forall_nth3_dec
                  (fun P' P T => Θ ⍮ Ξ ⍮ tele_wk (shape_domains_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                                         ++ self_cargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_selfs_ctx D
                     ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
                     ≈ P[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ
                     : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ)
                  (fun P' P T => eq_at_dec F levels_abstractable_dec HΞ _ _ _ _)
                  (ptyp_ps_at (cargs_pat gs1') t') (ptyp_ps_at (cargs_pat gs1) t)
                  (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                     (ptyp_ps_at (cargs_pat gs1) t))) as [HP | HP].
      + left; intros; unify_found; eapply HP; eauto.
      + right; intros H; apply HP; intros; eapply H; eauto.
    - decision_left H.
    - decision_right H.
  Defined.

  (** The sort of each view's container at the instance is in the
      group's. *)
  Definition sort_sub_dec :
    {forall k Mk qc k' Is vm D', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ (ind_sort D')[sb_of_list Id (IsS k)] ⊆ (ind_sort D)[self_wk D 0]ʷ}
    + {~ forall k Mk qc k' Is vm D', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ (ind_sort D')[sb_of_list Id (IsS k)] ⊆ (ind_sort D)[self_wk D 0]ʷ}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ (ind_sort D')[sb_of_list Id (IsS k)] ⊆ (ind_sort D)[self_wk D 0]ʷ)) as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup_f F qc) as [[D' |] Hl]; rewrite_dec Hl; [| left; intros ? [=] ].
      destruct (sub_dec F levels_abstractable_dec HΞ (grp_selfs_ctx D) (ind_sort D')[sb_of_list Id (IsS k)] (ind_sort D)[self_wk D 0]ʷ) as [HS | HS];
        [ left; intros ? [= <-]; exact HS | right; intros H; exact (HS (H _ eq_refl)) ].
    - decision_left H.
    - decision_right H.
  Defined.

  (** Each view's members are those of the container's group. *)
  Definition view_wrap_dec :
    {forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       exists D', ind_lookup Θ Ξ qc = Some D' /\ view_wrap_ok D D' vm}
    + {~ forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       exists D', ind_lookup Θ Ξ qc = Some D' /\ view_wrap_ok D D' vm}.
  Proof.
    apply views_dec; intros k Mk qc k' Is vm _ _.
    destruct (ind_lookup_f F qc) as [[D' |] Hl]; rewrite_dec Hl; [| right; intros (D' & HD' & _); discriminate ].
    destruct (view_wrap_check D D' vm) eqn:Hc.
    - left; exists D'; split; [ reflexivity | exact (view_wrap_check_sound _ _ _ Hc) ].
    - right; intros (D'' & [= <-] & Hw); rewrite (view_wrap_check_complete _ _ _ Hw) in Hc; discriminate.
  Defined.

  (** ** The Record Views

      The records are looked up through the filed units ([record_lookup_f]). *)

  (** A record view's head names a filed record at its arguments, its
      fields named as the record's. *)
  Definition rview_record_facts_dec (qr : qname) (Is : list exp) (fl : list string) :
    {exists R, rview_record_facts Θ Ξ R qr Is fl} + {~ exists R, rview_record_facts Θ Ξ R qr Is fl}.
  Proof.
    destruct (record_lookup_f F qr) as [[R |] Hl];
      [| right; intros (R & HR); rewrite (rview_record_lookup _ _ _ _ _ _ HR) in Hl; discriminate ].
    Local Ltac rview_facts_reject Hl :=
      let R' := fresh "R'" in let HL := fresh "HL" in
      right; intros (R' & [HL ? ? ? ?]); rewrite Hl in HL; injection HL as <-; contradiction.
    destruct (list_eq_dec string_dec fl (List.map fst (record_fields R))) as [Hn | Hn]; [| rview_facts_reject Hl ].
    destruct (Nat.eq_dec (List.length Is) (List.length (record_params R))) as [Hc | Hc]; [| rview_facts_reject Hl ].
    destruct (all_assumptions_dec (record_params R)) as [Ha | Ha]; [| rview_facts_reject Hl ].
    destruct (nodup_dec fl) as [Hd | Hd]; [| rview_facts_reject Hl ].
    left; exists R; constructor; assumption.
  Defined.

  (** A record view's one constructor, [rview_con], of one argument per
      field *)
  Definition rview_con_dec (Mk : imember) (fl : list string) :
    {exists gs, im_cons Mk = (rview_con, gs) :: nil /\ List.length gs = List.length fl}
    + {~ exists gs, im_cons Mk = (rview_con, gs) :: nil /\ List.length gs = List.length fl}.
  Proof.
    destruct (im_cons Mk) as [| [c gs] [| cg rest]];
      [ right; intros (gs & E & _); discriminate | | right; intros (gs' & E & _); discriminate ].
    destruct (string_dec c rview_con) as [-> | Hc]; [| right; intros (gs' & E & _); injection E; intros; congruence ].
    destruct (Nat.eq_dec (List.length gs) (List.length fl)) as [HL | HL];
      [ left; exists gs; split; [ reflexivity | exact HL ] | right; intros (gs' & E & HL'); injection E as <-; contradiction ].
  Defined.

  (** A record view's constructor's arguments are of the record's fields'
      sorts. *)
  Definition rview_kinds_dec (Mk : imember) (qr : qname) :
    {forall R gs, record_lookup Θ Ξ qr = Some R -> im_cons Mk = (rview_con, gs) :: nil ->
       cargs_kinds gs = record_field_kinds R}
    + {~ forall R gs, record_lookup Θ Ξ qr = Some R -> im_cons Mk = (rview_con, gs) :: nil ->
       cargs_kinds gs = record_field_kinds R}.
  Proof.
    destruct (record_lookup_f F qr) as [[R |] Hl]; [| left; intros ? ? Hl'; congruence ].
    destruct (im_cons Mk) as [| [c gs] [| cg rest]] eqn:Ec; [ left; intros ? ? ? [=] | | left; intros ? ? ? [=] ].
    destruct (string_dec c rview_con) as [-> | Hc]; [| left; intros ? ? ? [= ? _]; congruence ].
    destruct (list_eq_dec abs_kind_eq_dec (cargs_kinds gs) (record_field_kinds R)) as [HE | HE];
      [ left; intros R' gs' Hl' [= <-]; rewrite Hl in Hl'; injection Hl' as <-; exact HE
      | right; intros H; exact (HE (H _ _ Hl eq_refl)) ].
  Defined.

  (** The fields of a record view end only in record views before it. *)
  Definition rview_order_dec : {rview_order_ok D} + {~ rview_order_ok D}.
  Proof.
    destruct (rviews_dec D (fun j Mj _ _ _ => forall c gs, im_cons Mj = (c, gs) :: nil ->
                forall gs1 g gs2, gs = gs1 ++ g :: gs2 -> forall t, g = ca_rec t ->
                forall Mi, ind_member D (ptyp_mem t) = Some Mi -> im_is_rview Mi = true -> ptyp_mem t < j)) as [H | H].
    - intros j Mj qr Is fl _ _.
      destruct (im_cons Mj) as [| [c gs] [| cg rest]] eqn:Ec; [ left; intros ? ? [=] | | left; intros ? ? [=] ].
      destruct (forall_split_dec gs (fun gs1 g gs2 => forall t, g = ca_rec t ->
                  forall Mi, ind_member D (ptyp_mem t) = Some Mi -> im_is_rview Mi = true -> ptyp_mem t < j)) as [HS | HS].
      + intros gs1 [A | t] gs2 _; [ left; intros ? [=] |].
        destruct (ind_member D (ptyp_mem t)) as [Mi |] eqn:HMi; [| left; intros ? [= <-] ? HMi'; congruence ].
        destruct (im_is_rview Mi) eqn:Er; [| left; intros ? [= <-] ? HMi' Er'; rewrite HMi in HMi'; injection HMi' as <-; congruence ].
        destruct (Compare_dec.lt_dec (ptyp_mem t) j) as [Hlt | Hlt];
          [ left; intros ? [= <-] _ _ _; exact Hlt | right; intros H; exact (Hlt (H t eq_refl Mi HMi Er)) ].
      + left; intros c' gs' [= <- <-]; intros; subst; eapply HS; eauto.
      + right; intros H; apply HS; intros gs1 g gs2 E; exact (H c gs eq_refl gs1 g gs2 E).
    - left; intros j Mj qr Is fl c gs gs1 t gs2 Mi Hj Hh Hc E HMi Er; exact (H j Mj qr Is fl Hj Hh c gs Hc gs1 _ gs2 E t eq_refl Mi HMi Er).
    - right; intros Ho; apply H; intros j Mj qr Is fl Hj Hh c gs Hc gs1 g gs2 E t -> Mi HMi Er;
        exact (Ho j Mj qr Is fl c gs gs1 t gs2 Mi Hj Hh Hc E HMi Er).
  Defined.

  (** The record views come last. *)
  Definition rview_suffix_dec : {rview_suffix_ok D} + {~ rview_suffix_ok D}.
  Proof.
    unfold rview_suffix_ok; apply members_dec; intros k M _.
    destruct (bool_dec (im_is_rview M) true) as [Hd | Hd]; destruct (Compare_dec.le_dec (ind_nblk D) k) as [Hl | Hl];
      first [ left; split; intros; assumption | left; split; intros; contradiction | right; intros [H1 H2]; tauto ].
  Defined.

  (** The record views' facts without a judgment. *)
  Definition rview_struct_dec : {rview_struct_ok Θ Ξ D} + {~ rview_struct_ok Θ Ξ D}.
  Proof.
    destruct (rviews_dec D (fun _ _ qr Is fl => exists R, rview_record_facts Θ Ξ R qr Is fl)
                (fun _ _ qr Is fl _ _ => rview_record_facts_dec qr Is fl)) as [H1 | H1];
      [| right; intros Hs; apply H1; exact (rview_struct_record _ _ _ Hs) ].
    destruct (rviews_dec D (fun _ Mk _ _ _ => im_nparams Mk = nil)
                (fun _ Mk _ _ _ _ _ => list_eq_dec centry_eq_dec (im_nparams Mk) nil)) as [H2 | H2];
      [| right; intros Hs; apply H2; exact (rview_struct_nparams _ _ _ Hs) ].
    destruct (rviews_dec D (fun _ Mk _ _ fl => exists gs, im_cons Mk = (rview_con, gs) :: nil /\ List.length gs = List.length fl)
                (fun _ Mk _ _ fl _ _ => rview_con_dec Mk fl)) as [H3 | H3];
      [| right; intros Hs; apply H3; exact (rview_struct_con _ _ _ Hs) ].
    destruct (rviews_dec D (fun _ Mk qr _ _ => forall R gs, record_lookup Θ Ξ qr = Some R -> im_cons Mk = (rview_con, gs) :: nil ->
                              cargs_kinds gs = record_field_kinds R)
                (fun _ Mk qr _ _ _ _ => rview_kinds_dec Mk qr)) as [H6 | H6];
      [| right; intros Hs; apply H6; intros * Hk Hh R gs Hl Hc; exact (rview_struct_kinds _ _ _ Hs _ _ _ _ _ _ _ Hk Hh Hl Hc) ].
    destruct rview_suffix_dec as [H4 | H4]; [| right; intros Hs; exact (H4 (rview_struct_suffix _ _ _ Hs)) ].
    destruct rview_order_dec as [H5 | H5]; [| right; intros Hs; exact (H5 (rview_struct_order _ _ _ Hs)) ].
    left; constructor; try assumption.
    intros * Hk Hh Hl Hc; exact (H6 _ _ _ _ _ Hk Hh _ _ Hl Hc).
  Defined.

  (** Each record view's instance is [IsS] with the members as variables. *)
  Definition rview_instance_link_dec :
    {forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
       Is = List.map (fun I => I[grp_sb mp D]) (IsS k)}
    + {~ forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
       Is = List.map (fun I => I[grp_sb mp D]) (IsS k)}.
  Proof. apply rviews_dec; intros k Mk qr Is fl _ _; apply (list_eq_dec exp_eq_dec). Defined.

  (** Each record view's instance argument is typed at the record's
      parameters, over the members as variables. *)
  Definition rview_instance_typed_dec :
    {forall k Mk qr Is fl R j I T, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
       record_lookup Θ Ξ qr = Some R -> nth_error (IsS k) j = Some I ->
       nth_error (tele_insts (record_params R) Id (IsS k)) j = Some T ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ I : T}
    + {~ forall k Mk qr Is fl R j I T, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
       record_lookup Θ Ξ qr = Some R -> nth_error (IsS k) j = Some I ->
       nth_error (tele_insts (record_params R) Id (IsS k)) j = Some T ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ I : T}.
  Proof.
    destruct (rviews_dec D (fun k Mk qr Is fl => forall R, record_lookup Θ Ξ qr = Some R ->
                forall j I T, nth_error (IsS k) j = Some I -> nth_error (tele_insts (record_params R) Id (IsS k)) j = Some T ->
                Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ I : T)) as [H | H].
    - intros k Mk qr Is fl _ _.
      destruct (record_lookup_f F qr) as [[R |] Hl]; [| left; intros ? Hl'; congruence ].
      destruct (forall_nth2_dec (fun I T => Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ I : T) (fun I T => check_exp_at F levels_abstractable_dec HΞ (grp_selfs_ctx D) T I)
                  (IsS k) (tele_insts (record_params R) Id (IsS k))) as [HI | HI];
        [ left; intros R' Hl'; rewrite Hl in Hl'; injection Hl' as <-; exact HI | right; intros H; exact (HI (H _ Hl)) ].
    - decision_left H.
    - decision_right H.
  Defined.

  (** A record view's fields at the record's instance are its
      constructor's arguments. *)
  Definition rview_fields_eq_dec :
    {forall k Mk qr Is fl R c gs, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
       record_lookup Θ Ξ qr = Some R -> im_cons Mk = (c, gs) :: nil ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ˣ tele_sub (record_fctx R (List.length (record_fields R))) (sb_of_list Id (IsS k))
                             ≈ self_cargs_ctx D IsS Mk gs}
    + {~ forall k Mk qr Is fl R c gs, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
       record_lookup Θ Ξ qr = Some R -> im_cons Mk = (c, gs) :: nil ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ˣ tele_sub (record_fctx R (List.length (record_fields R))) (sb_of_list Id (IsS k))
                             ≈ self_cargs_ctx D IsS Mk gs}.
  Proof.
    destruct (rviews_dec D (fun k Mk qr Is fl => forall R, record_lookup Θ Ξ qr = Some R -> forall c gs,
                im_cons Mk = (c, gs) :: nil ->
                Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ˣ tele_sub (record_fctx R (List.length (record_fields R))) (sb_of_list Id (IsS k))
                                      ≈ self_cargs_ctx D IsS Mk gs)) as [H | H].
    - intros k Mk qr Is fl _ _.
      destruct (record_lookup_f F qr) as [[R |] Hl]; [| left; intros ? Hl'; congruence ].
      destruct (im_cons Mk) as [| [c gs] [| cg rest]] eqn:Ec; [ left; intros ? ? ? ? [=] | | left; intros ? ? ? ? [=] ].
      destruct (ext_eq_dec F levels_abstractable_dec HΞ (grp_selfs_ctx D) (tele_sub (record_fctx R (List.length (record_fields R))) (sb_of_list Id (IsS k)))
                  (self_cargs_ctx D IsS Mk gs)
                  (all_assumptions_sub (record_fctx R (List.length (record_fields R))) (sb_of_list Id (IsS k))
                                (record_fctx_ass R _)))
        as [HE | HE];
        [ left; intros R' Hl' c' gs' [= <- <-]; rewrite Hl in Hl'; injection Hl' as <-; exact HE
        | right; intros H; exact (HE (H _ Hl _ _ eq_refl)) ].
    - decision_left H.
    - decision_right H.
  Defined.

  (** The sort of each record view's record at the instance is in the
      group's. *)
  Definition rview_sort_sub_dec :
    {forall k Mk qr Is fl R, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
       record_lookup Θ Ξ qr = Some R ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ (record_sort R)[sb_of_list Id (IsS k)] ⊆ (ind_sort D)[self_wk D 0]ʷ}
    + {~ forall k Mk qr Is fl R, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
       record_lookup Θ Ξ qr = Some R ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ (record_sort R)[sb_of_list Id (IsS k)] ⊆ (ind_sort D)[self_wk D 0]ʷ}.
  Proof.
    destruct (rviews_dec D (fun k Mk qr Is fl => forall R, record_lookup Θ Ξ qr = Some R ->
                Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ (record_sort R)[sb_of_list Id (IsS k)] ⊆ (ind_sort D)[self_wk D 0]ʷ)) as [H | H].
    - intros k Mk qr Is fl _ _.
      destruct (record_lookup_f F qr) as [[R |] Hl]; [| left; intros ? Hl'; congruence ].
      destruct (sub_dec F levels_abstractable_dec HΞ (grp_selfs_ctx D) (record_sort R)[sb_of_list Id (IsS k)] (ind_sort D)[self_wk D 0]ʷ) as [HS | HS];
        [ left; intros R' Hl'; rewrite Hl in Hl'; injection Hl' as <-; exact HS | right; intros H; exact (HS (H _ Hl)) ].
    - decision_left H.
    - decision_right H.
  Defined.

  (** Each record view's type is in the group's sort. *)
  Definition rview_typed_dec :
    {forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ apps_exp (a_record qr) (IsS k) : (ind_sort D)[self_wk D 0]ʷ}
    + {~ forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ apps_exp (a_record qr) (IsS k) : (ind_sort D)[self_wk D 0]ʷ}.
  Proof.
    apply rviews_dec; intros k Mk qr Is fl _ _.
    exact (check_exp_at F levels_abstractable_dec HΞ (grp_selfs_ctx D) (ind_sort D)[self_wk D 0]ʷ (apps_exp (a_record qr) (IsS k))).
  Defined.

  (** A view takes its container's record views to record views of the
      same record and as many arguments. *)
  Definition rview_maps_dec :
    {forall k Mk qc k' Is vm D' i' Mi' v q'' Is'' fl'', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_record q'' Is'' fl'' ->
       nth_error vm i' = Some v ->
       exists Mv X, ind_member D v = Some Mv /\ im_head Mv = mh_record q'' X fl'' /\ List.length X = List.length Is''}
    + {~ forall k Mk qc k' Is vm D' i' Mi' v q'' Is'' fl'', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_record q'' Is'' fl'' ->
       nth_error vm i' = Some v ->
       exists Mv X, ind_member D v = Some Mv /\ im_head Mv = mh_record q'' X fl'' /\ List.length X = List.length Is''}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall i' Mi', ind_member D' i' = Some Mi' -> forall q'' Is'' fl'', im_head Mi' = mh_record q'' Is'' fl'' ->
                forall v, nth_error vm i' = Some v ->
                exists Mv X, ind_member D v = Some Mv /\ im_head Mv = mh_record q'' X fl'' /\
                  List.length X = List.length Is'')) as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup_f F qc) as [[D' |] Hl]; [| left; intros ? Hl'; congruence ].
      destruct (members_dec D' (fun i' Mi' => forall q'' Is'' fl'', im_head Mi' = mh_record q'' Is'' fl'' ->
                  forall v, nth_error vm i' = Some v ->
                  exists Mv X, ind_member D v = Some Mv /\ im_head Mv = mh_record q'' X fl'' /\
                    List.length X = List.length Is'')) as [HM | HM].
      + intros i' Mi' _.
        destruct (im_head Mi') as [pm' | q2 k2 Is2 vm2 | q2 Is2 fl2] eqn:Hh'; [ left; intros ? ? ? [=] .. |].
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| left; intros ? ? ? _ ? [=] ].
        Local Ltac rview_maps_reject :=
          let H := fresh "H" in
          right; intros H; destruct (H _ _ _ eq_refl _ eq_refl) as (? & ? & Hm & Hhm & Hlen); unify_found;
          first [ discriminate | congruence ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv; [| rview_maps_reject ].
        destruct (im_head Mv) as [pmv | qv kv Iv vmv | qv Iv flv] eqn:Hhv; [ rview_maps_reject | rview_maps_reject |].
        destruct (qname_eq_dec qv q2) as [-> | Hq]; [| rview_maps_reject ].
        destruct (list_eq_dec string_dec flv fl2) as [-> | Hf]; [| rview_maps_reject ].
        destruct (Nat.eq_dec (List.length Iv) (List.length Is2)) as [HL | HL]; [| rview_maps_reject ].
        left; intros ? ? ? [= <- <- <-] ? [= <-]; exists Mv, Iv; repeat split; assumption.
      + left; intros D'' Hl'; rewrite ?Hl in Hl'; injection Hl' as <-; exact HM.
      + right; intros H'; apply HM; exact (H' D' Hl).
    - decision_left H.
    - decision_right H.
  Defined.

  (** The record view a view takes a container's record view to has the
      container's arguments at this view's instance. *)
  Definition rview_instance_eq_dec :
    {forall k Mk qc k' Is vm D' i' Mi' v q'' Is'' fl'' R'' Mv X fl j' C C' T,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_record q'' Is'' fl'' ->
       record_lookup Θ Ξ q'' = Some R'' ->
       nth_error vm i' = Some v -> ind_member D v = Some Mv -> im_head Mv = mh_record q'' X fl ->
       nth_error (IsS v) j' = Some C ->
       nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
       nth_error (tele_insts (record_params R'') Id Is'') j' = Some T ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)]}
    + {~ forall k Mk qc k' Is vm D' i' Mi' v q'' Is'' fl'' R'' Mv X fl j' C C' T,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_record q'' Is'' fl'' ->
       record_lookup Θ Ξ q'' = Some R'' ->
       nth_error vm i' = Some v -> ind_member D v = Some Mv -> im_head Mv = mh_record q'' X fl ->
       nth_error (IsS v) j' = Some C ->
       nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
       nth_error (tele_insts (record_params R'') Id Is'') j' = Some T ->
       Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)]}.
  Proof.
    destruct (views_dec D (fun k Mk qc k' Is vm => forall D', ind_lookup Θ Ξ qc = Some D' ->
                forall i' Mi', ind_member D' i' = Some Mi' -> forall q'' Is'' fl'', im_head Mi' = mh_record q'' Is'' fl'' ->
                forall R'', record_lookup Θ Ξ q'' = Some R'' -> forall v, nth_error vm i' = Some v ->
                forall Mv, ind_member D v = Some Mv -> forall X fl, im_head Mv = mh_record q'' X fl ->
                forall j' C C' T, nth_error (IsS v) j' = Some C ->
                nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
                nth_error (tele_insts (record_params R'') Id Is'') j' = Some T ->
                Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)])) as [H | H].
    - intros k Mk qc k' Is vm _ _.
      destruct (ind_lookup_f F qc) as [[D' |] Hl]; [| left; intros ? Hl'; congruence ].
      destruct (members_dec D' (fun i' Mi' => forall q'' Is'' fl'', im_head Mi' = mh_record q'' Is'' fl'' ->
                  forall R'', record_lookup Θ Ξ q'' = Some R'' -> forall v, nth_error vm i' = Some v ->
                  forall Mv, ind_member D v = Some Mv -> forall X fl, im_head Mv = mh_record q'' X fl ->
                  forall j' C C' T, nth_error (IsS v) j' = Some C ->
                  nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
                  nth_error (tele_insts (record_params R'') Id Is'') j' = Some T ->
                  Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)])) as [HM | HM].
      + intros i' Mi' _.
        destruct (im_head Mi') as [pm' | q2 k2 Is2 vm2 | q2 Is2 fl2] eqn:Hh'; [ vacuous | vacuous |].
        destruct (record_lookup_f F q2) as [[R2 |] Hl2]; [| vacuous ].
        destruct (List.nth_error vm i') as [v |] eqn:Hv; [| vacuous ].
        destruct (ind_member D v) as [Mv |] eqn:Hmv; [| vacuous ].
        destruct (im_head Mv) as [pmv | qv kv Iv vmv | qv Iv flv] eqn:Hhv; [ vacuous | vacuous |].
        destruct (qname_eq_dec qv q2) as [-> | Hq]; [| vacuous ].
        destruct (forall_nth3_dec (fun C C' T => Θ ⍮ Ξ ⍮ grp_selfs_ctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)])
                    (fun C C' T => eq_at_dec F levels_abstractable_dec HΞ (grp_selfs_ctx D) T[sb_of_list Id (IsS k)] C C')
                    (IsS v) (List.map (fun I => I[sb_of_list Id (IsS k)]) Is2) (tele_insts (record_params R2) Id Is2))
          as [HC | HC].
        * left; intros ? ? ? [= <- <- <-] R2' Hl2' v' Hv' Mv' Hmv' X fl Hhv'; unify_found; intros; eapply HC; eassumption.
        * right; intros H; exact (HC (H _ _ _ eq_refl _ Hl2 _ eq_refl _ Hmv _ _ Hhv)).
      + left; intros D'' Hl'; rewrite ?Hl in Hl'; injection Hl' as <-; exact HM.
      + right; intros H'; apply HM; exact (H' D' Hl).
    - decision_left H.
    - decision_right H.
  Defined.

  (** A premise of [ind_nil_at] that fails: the group is not checked. *)
  Local Ltac nil_reject :=
    let Hn := fresh "Hn" in
    right; intros Hn; destruct Hn;
    first [ contradiction
          | exfalso; match goal with HN : forall _, ~ _ |- _ => eapply HN; solve [ eassumption | split; eassumption ] end ].

  (** The group checked at the instances [IsS]: [ind_nil_at], premise by
      premise, the universe of the sort and of the views' domains the
      largest either asks for. *)
  Definition ind_nil_at_dec : {ind_nil_at Θ Ξ mp D IsS} + {~ ind_nil_at Θ Ξ mp D IsS}.
  Proof.
    destruct uparams_suffix_dec as [[Δ HΔ] | HnΔ]; [| nil_reject ].
    destruct (all_assumptions_dec (ind_uparams D)) as [Hass | Hass]; [| nil_reject ].
    destruct (decl_mvc_dec D) as [Hmvc | Hmvc]; [| nil_reject ].
    destruct (Compare_dec.le_dec (List.length (fc_tele F)) (ind_nu D)) as [Hle | Hle];
      rewrite <- (fc_tele_ok F) in Hle; [| nil_reject ].
    destruct (check_ctx F levels_abstractable_dec HΞ (ind_uparams D)) as [HU | HU]; [| nil_reject ].
    destruct order_ok_dec as [Hord | Hord]; [| nil_reject ].
    destruct first_member_dec as [[M0 [HM0 Hh0]] | HnM0]; [| nil_reject ].
    destruct (ind_sort_univ_dec (ind_sort D)) as [HSu | HSu]; [| nil_reject ].
    destruct (typ_least_dec F levels_abstractable_dec HΞ (ind_uparams D) (ind_sort D)) as [[lS [HS _]] | HnS]; [| nil_reject ].
    destruct (check_level F levels_abstractable_dec (ind_uparams D) HU (ind_sort_lvl (ind_sort D))) as [[n Hn] | Hnn]; [| nil_reject ].
    destruct nparams_ass_dec as [HPass | HPass]; [| nil_reject ].
    destruct members_nodup_dec as [Hnd | Hnd]; [| nil_reject ].
    destruct nparams_sort_dec as [HNs | HNs]; [| nil_reject ].
    destruct nparams_relevant_dec as [HNr | HNr]; [| nil_reject ].
    destruct args_sort_dec as [HAs | HAs]; [| nil_reject ].
    destruct args_kind_dec as [HAk | HAk]; [| nil_reject ].
    destruct doms_sort_dec as [HDs | HDs]; [| nil_reject ].
    destruct params_length_dec as [HPl | HPl]; [| nil_reject ].
    destruct rec_ps_dec as [HPs | HPs]; [| nil_reject ].
    destruct views_exist_dec as [HVe | HVe]; [| nil_reject ].
    destruct link_dec as [HLk | HLk]; [| nil_reject ].
    destruct instances_typed_dec as [HIt | HIt]; [| nil_reject ].
    destruct decl_maps_dec as [HDm | HDm]; [| nil_reject ].
    destruct view_maps_len_dec as [HVl | HVl]; [| nil_reject ].
    destruct view_is_eq_dec as [HIe | HIe]; [| nil_reject ].
    destruct (nparams_eq_dec HPass) as [HNe | HNe]; [| nil_reject ].
    destruct cargs_eq_dec as [HCe | HCe]; [| nil_reject ].
    destruct doms_eq_bound_dec as [[lD HDe] | HnDe]; [| nil_reject ].
    destruct ps_typed_dec as [HPt | HPt]; [| nil_reject ].
    destruct ps_eq_dec as [HPe | HPe]; [| nil_reject ].
    destruct sort_sub_dec as [HSs | HSs]; [| nil_reject ].
    destruct rview_struct_dec as [HRs | HRs]; [| nil_reject ].
    destruct rview_instance_link_dec as [HRl | HRl]; [| nil_reject ].
    destruct rview_instance_typed_dec as [HRi | HRi]; [| nil_reject ].
    destruct rview_fields_eq_dec as [HRe | HRe]; [| nil_reject ].
    destruct rview_sort_sub_dec as [HRss | HRss]; [| nil_reject ].
    destruct rview_typed_dec as [HRt | HRt]; [| nil_reject ].
    destruct rview_maps_dec as [HRm | HRm]; [| nil_reject ].
    destruct rview_instance_eq_dec as [HRie | HRie]; [| nil_reject ].
    destruct (rank_check_f F D) eqn:Hrk; rewrite rank_check_f_ok in Hrk;
      [| right; intros Hn0; destruct Hn0;
         rewrite (rank_check_complete _ _ _ (decls_of_ctx _ _ _ HU) ltac:(eassumption)) in Hrk; discriminate ].
    destruct view_wrap_dec as [HVw | HVw]; [| nil_reject ].
    destruct (view_maps_check_f F D) eqn:Hvm; rewrite view_maps_check_f_ok in Hvm;
      [| right; intros Hn0; destruct Hn0; rewrite (view_maps_check_complete _ _ _ ltac:(eassumption)) in Hvm; discriminate ].
    destruct (params_sorts_dec F levels_abstractable_dec HΞ (gs_tele Ξ) Δ) as [[[lP bs] [_ HP]] | HnP];
      [| right; intros Hn0; destruct Hn0;
         match goal with
         | HΔ0 : ind_uparams D = ?Δ0 ++ gs_tele Ξ, Hps0 : forall k, parameter_sort _ _,
           HP0 : forall Δ1 κ T Δ2, ?Δ0 = _ -> _ |- _ =>
             assert (Δ0 = Δ) as -> by (eapply app_inv_tail; rewrite <- HΔ0; exact HΔ);
             exact (HnP _ (params_evaluated_of_sorts _ _ _ _ _ _ Hps0 HP0))
         end ].
    cbn [fst snd] in HP.
    left; apply (mk_ind_nil_at Θ Ξ mp D IsS Δ M0 (Nat.max lS lD) n lP
                   (fun k => param_bool_sort lP (List.nth k (List.rev bs) false))); try assumption.
    all: try (intros k; apply param_bool_sort_ok; fail).
    all: try (intros Δ1 κ T Δ2 E; exact (HP _ _ _ _ E); fail).
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
    - [classify_why_unapplied k]: [Self_k], the declared member [k], is the head
      and is not applied to the uniform parameters as declared;
    - [classify_why_nested H]: a [Self] occurs in an argument of the type former [H]
      that is not one of its uniform arguments, or [H] is no declared
      member of a filed group;
    - [classify_why_self_arg j k Δ H]: in a record's instance, [Self_j] is an
      argument of the neutral head [H] ([selfs_guarded]). *)
Inductive classify_why : Set :=
(** One of the reasons above, by its code *)
| classify_why_code : nat -> classify_why
(** The declared member [k], written as the head, not applied to the
    uniform parameters as declared *)
| classify_why_unapplied : nat -> classify_why
(** A [Self] in a non-uniform argument of a nested occurrence, or one under
    a type former of no declared member: the head *)
| classify_why_nested : exp -> classify_why
(** A record's instance that is not guarded: the member [j] of the [Self]
    that occurs, the head [H] it is an argument of, and the context [Δ]
    [H] is in, its first [k] entries unnamed (the domains and binders
    crossed inside the argument's type) *)
| classify_why_self_arg : nat -> nat -> ctx -> exp -> classify_why
(** The argument's type is classified only as its normal form, and that
    holds a proof ([nf_proof_free]): the instance it nests at could not be
    strengthened past the arguments before it *)
| classify_why_proof : classify_why
(** The instance the argument nests at is not keyed: its arguments are not
    of the container's or the record's parameters' types
    ([view_inst_key]) *)
| classify_why_instance : classify_why
(** A recursive argument written at a kind other than [ak_relevant]: it
    is a type of the group, in its universe *)
| classify_why_rec_kind : classify_why.

(** The offset, among the [n] [Self]s from the variable [lo] on, of the
    first one some term of [Ms] mentions. *)
Definition first_self_mentioned (lo n : nat) (Ms : list exp) : option nat :=
  List.find (fun x => List.existsb (mentions_vars (lo + x) 1) Ms) (List.seq 0 n).

(** Where [selfs_neutral_head] finds a [Self] as an argument of a neutral
    head: the [Self]'s member (the variable [lo + x] is [Self_(n-1-x)]),
    the binders crossed, and the head. *)
Fixpoint self_arg_site (lo n depth : nat) (M : exp) {struct M} : option (nat * nat * exp) :=
  match M with
  | a_pi _ _ A B =>
      match self_arg_site lo n depth A with
      | Some r => Some r
      | None => self_arg_site (S lo) n (S depth) B
      end
  | a_app M1 M2 =>
      if head_takes_selfs lo n (app_head M1) then
        match self_arg_spine lo n depth M1 with
        | Some r => Some r
        | None => self_arg_site lo n depth M2
        end
      else
        match first_self_mentioned lo n (app_args M) with
        | Some x => Some (n - 1 - x, depth, app_head M1)
        | None => None
        end
  | _ => None
  end
(** The arguments of an application spine whose head may take a [Self] *)
with self_arg_spine (lo n depth : nat) (M : exp) {struct M} : option (nat * nat * exp) :=
  match M with
  | a_app M1 M2 =>
      match self_arg_spine lo n depth M1 with
      | Some r => Some r
      | None => self_arg_site lo n depth M2
      end
  | _ => None
  end.

(** The first argument of a record's instance with such a site. *)
Fixpoint self_arg_sites (lo n : nat) (Is : list exp) : option (nat * nat * exp) :=
  match Is with
  | nil => None
  | M :: Is' => match self_arg_site lo n 0 M with Some r => Some r | None => self_arg_sites lo n Is' end
  end.

(** A reason's context, its unnamed entries over [Γ]. *)
Definition self_arg_in (Γ : ctx) (r : classify_why) : classify_why :=
  match r with
  | classify_why_self_arg j k _ H => classify_why_self_arg j k (List.repeat (ce_ass ak_relevant (a_typ 0)) k ++ Γ) H
  | _ => r
  end.

(** Whether no [Self] occurs in [T], [d] domains down, past the arguments
    before ([pat]) and [np] parameters. *)
Definition selfs_free (np n : nat) (pat : list bool) (d : nat) (T : exp) : bool :=
  match image_pat (classify_pat d np n (List.repeat false (List.length pat))) T with Some _ => true | None => false end.

Fixpoint shape_reason (np n : nat) (pat : list bool) (d : nat) (T : exp) : classify_why :=
  match T with
  | a_pi ak_relevant ak_relevant A B => if selfs_free np n pat d A then shape_reason np n pat (S d) B else classify_why_code 2
  | _ =>
      match app_head T with
      (* [Self_0] is outermost: the variable [b + i] is [Self_(n-1-i)]. *)
      | a_var j => let b := d + List.length pat + np in
                   if (b <=? j) && (j <? b + n) then classify_why_unapplied (n - 1 - (j - b)) else classify_why_code 4
      | a_mem _ _ => classify_why_code 4
      | a_ind qc k => classify_why_nested (a_ind qc k)
      | a_record _ =>
          match self_arg_sites (d + List.length pat + np) n (app_args T) with
          | Some (j, k, h) => classify_why_self_arg j (d + k) nil h
          | None => classify_why_code 1
          end
      | _ => classify_why_code 1
      end
  end.

(** The reason an argument [T] is rejected. *)
Definition classify_reason (np n : nat) (pat : list bool) (T : exp) : classify_why :=
  if selfs_free np n pat 0 T then classify_why_code 0 else shape_reason np n pat 0 T.

(** The classification reads the filed groups through [grp_info] alone. *)
Lemma classify_shape_ext : forall (g1 g2 : qname -> nat -> option nat) recs nu np n pat, (forall q0 k, g1 q0 k = g2 q0 k) ->
    forall T d, classify_shape g1 recs nu np n pat d T = classify_shape g2 recs nu np n pat d T.
Proof.
  intros * Hg T; induction T; intros d; cbn [classify_shape]; try reflexivity;
    try (destruct (app_head _) eqn:?; try reflexivity; unfold classify_nest; rewrite Hg; reflexivity).
  destruct (image_pat _ _); [ rewrite IHT2; reflexivity | reflexivity ].
Qed.

(** The same for an argument *)
Lemma classify_arg_ext : forall (g1 g2 : qname -> nat -> option nat) recs nu np n pat, (forall q0 k, g1 q0 k = g2 q0 k) ->
    forall T, classify_arg g1 recs nu np n pat T = classify_arg g2 recs nu np n pat T.
Proof. intros * Hg T; unfold classify_arg; rewrite (classify_shape_ext g1 g2 _ _ _ _ _ Hg); reflexivity. Qed.

Section Classify.
  (** The fast context the classification looks names up in *)
  Variable F : FCtx.
  #[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  (** The decision of [levels_abstractable] the checker is given *)
  Variable levels_abstractable_dec : forall G Δ E, ⊢ Θ ⍮ Ξ ⍮ Δ ++ G ->
      { levels_abstractable Θ Ξ G Δ E } + { ~ levels_abstractable Θ Ξ G Δ E }.
  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.

  (** [raw_decl_uniform_ctx], the frames' telescope fast *)
  Definition raw_decl_uniform_ctx_f (R : raw_decl) : ctx :=
    tele_wk (raw_decl_uparams R) (wk_shiftn (raw_decl_nmembers R)) ++ raw_decl_selfs R ++ fc_tele F.

  Lemma raw_decl_uniform_ctx_f_ok : forall R, raw_decl_uniform_ctx_f R = raw_decl_uniform_ctx Ξ R.
  Proof. intros; unfold raw_decl_uniform_ctx_f, raw_decl_uniform_ctx; rewrite (fc_tele_ok F); reflexivity. Qed.

  (** [raw_member_args_ctx], the frames' telescope fast *)
  Definition raw_member_args_ctx_f (R : raw_decl) (Mr : raw_member) : ctx :=
    tele_wk (raw_member_nparams Mr ++ raw_decl_uparams R) (wk_shiftn (raw_decl_nmembers R)) ++ raw_decl_selfs R ++ fc_tele F.

  Lemma raw_member_args_ctx_f_ok : forall R Mr, raw_member_args_ctx_f R Mr = raw_member_args_ctx Ξ R Mr.
  Proof. intros; unfold raw_member_args_ctx_f, raw_member_args_ctx; rewrite (fc_tele_ok F); reflexivity. Qed.

  (** The number of parameters of the record at [qr], if it is one, read
      through the filed units ([rec_info]). *)
  Definition rec_info_f (qr : qname) : option nat :=
    option_map (fun R => List.length (record_params R)) (proj1_sig (record_lookup_f F qr)).

  Lemma rec_info_f_ok : forall qr, rec_info_f qr = rec_info Θ Ξ qr.
  Proof. intros qr; unfold rec_info_f, rec_info; destruct (record_lookup_f F qr) as [o E]; cbn; rewrite E; reflexivity. Qed.

  (** Terms normalized pointwise at types, each typed first. *)
  Fixpoint nbes_dec (Γ : ctx) (Ms : list exp) (As : list typ) {struct Ms} :
    {Ws | nbes Θ Ξ Γ Ms As Ws} + {forall Ws, ~ nbes Θ Ξ Γ Ms As Ws}.
  Proof.
    destruct Ms as [| M Ms'], As as [| A As']; try (right; intros Ws H; inversion H; fail).
    - left; exists nil; constructor.
    - destruct (nbes_dec Γ Ms' As') as [[Ws' HWs'] | HnWs']; [| right; intros Ws H; inversion H; subst; eapply HnWs'; eassumption ].
      destruct (check_exp_at F levels_abstractable_dec HΞ Γ A M) as [HM | HnM]; [| right; intros Ws H; inversion H; subst; contradiction ].
      destruct (nbe_impl F Γ M A (typed_nbe_order' F _ _ _ HM)) as [W HW].
      left; exists (W :: Ws'); constructor; assumption.
  Defined.

  (** The key of an instance: its arguments normalized at the parameters'
      types of the container or the record ([view_inst_key]). *)
  Definition view_inst_key_dec (Γ : ctx) (x : view_inst) : {y | view_inst_key Θ Ξ Γ x y} + {forall y, ~ view_inst_key Θ Ξ Γ x y}.
  Proof.
    destruct x as [qc k Cs | qr Is].
    - destruct (ind_lookup_f F qc) as [[D' |] Hl]; [| right; intros y H; inversion H; subst; unify_found; congruence ].
      destruct (nbes_dec Γ Cs (tele_insts (ind_uparams D') sb_id Cs)) as [[Ws HWs] | HnWs].
      + left; exists (vk_ind qc k Ws); econstructor; eassumption.
      + right; intros y H; inversion H; subst; unify_found; eapply HnWs; eassumption.
    - destruct (record_lookup_f F qr) as [[Rr |] Hl]; [| right; intros y H; inversion H; subst; unify_found; congruence ].
      destruct (nbes_dec Γ Is (tele_insts (record_params Rr) sb_id Is)) as [[Ws HWs] | HnWs].
      + left; exists (vk_record qr Ws); econstructor; eassumption.
      + right; intros y H; inversion H; subst; unify_found; eapply HnWs; eassumption.
  Defined.

  (** A shape as classified, its instance keyed. *)
  Fixpoint written_ptyp_key_dec (Γ : ctx) (t : written_ptyp) {struct t} :
    {t' | written_ptyp_key Θ Ξ Γ t t'} + {forall t', ~ written_ptyp_key Θ Ξ Γ t t'}.
  Proof.
    destruct t as [j Ps | x Ns | B t].
    - left; exists (classified_ptyp_self j Ps); constructor.
    - destruct (view_inst_key_dec Γ x) as [[y Hy] | Hny].
      + left; exists (classified_ptyp_nest y Ns); constructor; exact Hy.
      + right; intros t' H; inversion H; subst; eapply Hny; eassumption.
    - destruct (written_ptyp_key_dec Γ t) as [[t' Ht] | Hnt].
      + left; exists (classified_ptyp_pi B t'); constructor; exact Ht.
      + right; intros t'' H; inversion H; subst; eapply Hnt; eassumption.
  Defined.

  (** An argument as classified, its instance keyed. *)
  Definition written_carg_key_dec (Γ : ctx) (g : written_carg) :
    {g' | written_carg_key Θ Ξ Γ g g'} + {forall g', ~ written_carg_key Θ Ξ Γ g g'}.
  Proof.
    destruct g as [κ A | t]; [ left; exists (classified_carg_arg κ A); constructor |].
    destruct (written_ptyp_key_dec Γ t) as [[t' Ht] | Hnt].
    - left; exists (classified_carg_rec_case t'); constructor; exact Ht.
    - right; intros g' H; inversion H; subst; eapply Hnt; eassumption.
  Defined.

  (** An argument as written, or, failing that, as its normal form, the
      instance it nests at keyed. *)
  Definition classify_arg_in_dec (Γ : ctx) (nu np n : nat) (pat : list bool) (T : exp) :
    ({g | classify_arg_in Θ Ξ Γ nu np n pat T g} + {r : classify_why | forall g, ~ classify_arg_in Θ Ξ Γ nu np n pat T g})%type.
  Proof.
    destruct (classify_arg grp_none rec_none nu np n pat T) as [gw |] eqn:Hs.
    { destruct (written_carg_key_dec (List.skipn (List.length pat + (np - nu)) Γ) gw) as [[g Hg] | Hng].
      - left; exists g; eapply classify_in_syn; eassumption.
      - right; exists classify_why_instance; intros g H; inversion H as [gw' g' Hs' Hk | i W gw' g' Hn _ _ _ _ _]; subst;
          [ rewrite Hs in Hs'; injection Hs' as <-; exact (Hng _ Hk) | congruence ]. }
    destruct (typ_least_dec F levels_abstractable_dec HΞ Γ T) as [[i [HT _]] | HnT].
    2:{ right; exists (classify_reason np n pat T); intros g H; inversion H as [gw' g' Hs' _ | i W gw' g' _ HT _ _ _ _]; subst;
        [ congruence | exact (HnT _ HT) ]. }
    destruct (nbe_ty_impl F Γ T (typ_nbe_ty_order F _ _ _ HT)) as [W HW].
    destruct (nf_proof_freeb W) eqn:Hpf.
    2:{ right; exists classify_why_proof.
        intros g H; inversion H as [gw' g' Hs' _ | i' W' gw' g' _ _ HW' HW'pf _ _]; subst; [ congruence |].
        pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-.
        apply (proj1 nf_proof_freeb_iff) in HW'pf; congruence. }
    apply (proj1 nf_proof_freeb_iff) in Hpf.
    destruct (classify_arg (grp_info_f F) rec_info_f nu np n pat (nf_to_exp W)) as [gw |] eqn:Hn;
      rewrite (classify_arg_rec_ext _ _ _ rec_info_f_ok), (classify_arg_ext _ _ _ _ _ _ _ (grp_info_f_ok F)) in Hn.
    - destruct (written_carg_key_dec (List.skipn (List.length pat + (np - nu)) Γ) gw) as [[g Hg] | Hng].
      + left; exists g; eapply classify_in_nf; eassumption.
      + right; exists classify_why_instance.
        intros g H; inversion H as [gw' g' Hs' _ | i' W' gw' g' _ _ HW' _ Hn' Hk]; subst; [ congruence |].
        pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-.
        rewrite Hn in Hn'; injection Hn' as <-; exact (Hng _ Hk).
    - right; exists (self_arg_in Γ (classify_reason np n pat (nf_to_exp W))).
      intros g H; inversion H as [gw' g' Hs' _ | i' W' gw' g' _ _ HW' _ Hn' _]; subst; [ congruence |].
      pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-; congruence.
  Defined.

  (** The arguments of a constructor, each in the context of those before
      it; a rejection names the argument and why. *)
  Definition classify_args_in_dec (Γp : ctx) (nu np n : nat) :
    forall (args : list (string * abs_kind * exp)) (pat : list bool) (args1 : list (string * abs_kind * exp)),
      ({gs | classify_args_in Θ Ξ Γp nu np n pat args1 args gs}
       + {e : (string * classify_why) | forall gs, ~ classify_args_in Θ Ξ Γp nu np n pat args1 args gs})%type.
  Proof.
    fix go 1; intros [| [[y κ] T] args] pat args1.
    - left; exists nil; constructor.
    - destruct (classify_arg_in_dec (raw_args_tele args1 ++ Γp) nu np n pat T) as [[g Hg] | [r Hg]].
      + (** A recursive argument is of the kind [ak_relevant] *)
        assert (Hk : { classified_carg_bit g = true -> κ = ak_relevant } + { ~ (classified_carg_bit g = true -> κ = ak_relevant) }).
        { destruct (classified_carg_bit g); [| left; intros [=] ].
          destruct (abs_kind_eq_dec κ ak_relevant) as [E | E]; [ left; intros _; exact E | right; intros H; exact (E (H eq_refl)) ]. }
        destruct Hk as [Hk | Hk].
        2:{ right; exists (y, classify_why_rec_kind); intros gs' H; inversion H; subst.
            match goal with Hg' : classify_arg_in _ _ _ _ _ _ _ _ ?g' |- _ =>
              pose proof (classify_arg_in_functional _ _ _ _ _ _ _ _ _ _ Hg Hg') as <- end.
            contradiction. }
        destruct (go args (classified_carg_bit g :: pat) (args1 ++ (y, κ, T) :: nil)) as [[gs Hgs] | [e He]].
        * left; exists (classified_carg_tag κ g :: gs); constructor; assumption.
        * right; exists e; intros gs' H; inversion H; subst.
          match goal with Hg' : classify_arg_in _ _ _ _ _ _ _ _ ?g' |- _ =>
            pose proof (classify_arg_in_functional _ _ _ _ _ _ _ _ _ _ Hg Hg') as <- end.
          eapply He; eassumption.
      + right; exists (y, r); intros gs' H; inversion H; subst; eapply Hg; eassumption.
  Defined.

  (** The constructors of a member; a rejection names the constructor, the
      argument and why. *)
  Definition classify_cons_in_dec (Γp : ctx) (nu np n : nat) :
    forall (rcs : list (string * list (string * abs_kind * exp))),
      ({cs | classify_cons_in Θ Ξ Γp nu np n rcs cs}
       + {e : (string * string * classify_why) | forall cs, ~ classify_cons_in Θ Ξ Γp nu np n rcs cs})%type.
  Proof.
    unfold classify_cons_in; fix go 1; intros [| [c args] rcs].
    - left; exists nil; constructor.
    - destruct (classify_args_in_dec Γp nu np n args nil nil) as [[gs Hgs] | [[y r] He]].
      + destruct (go rcs) as [[cs Hcs] | [e He]].
        * left; exists ((c, gs) :: cs); constructor; [ split; [ reflexivity | exact Hgs ] | exact Hcs ].
        * right; exists e; intros cs' H; inversion H; subst; eapply He; eassumption.
      + right; exists (c, y, r); intros cs' H; inversion H as [| ? [c' gs'] ? ? [_ Hc]]; subst; eapply He; exact Hc.
  Defined.

  (** The constructors of a declared member. *)
  Definition raw_member_classify_dec (R : raw_decl) (Mr : raw_member) :
    ({cs | raw_member_classify Θ Ξ R Mr cs} + {e : (string * string * classify_why) | forall cs, ~ raw_member_classify Θ Ξ R Mr cs})%type.
  Proof.
    (* decided at the fast context; read in Core in the proofs only *)
    destruct (classify_cons_in_dec (raw_member_args_ctx_f R Mr) (raw_decl_nu R) (List.length (raw_member_nparams Mr) + raw_decl_nu R) (raw_decl_nmembers R)
                (raw_member_cons Mr)) as [[cs Hcs] | [e He]];
      [ left; exists cs | right; exists e ]; unfold raw_member_classify; rewrite <- raw_member_args_ctx_f_ok; [ exact Hcs | exact He ].
  Defined.

  (** The declared members' constructors, member by member; a rejection
      names the member too. *)
  Fixpoint raw_members_classify_dec (R : raw_decl) (ms : list raw_member) :
    ({css | Forall2 (raw_member_classify Θ Ξ R) ms css}
     + {e : (string * string * string * classify_why) | forall css, ~ Forall2 (raw_member_classify Θ Ξ R) ms css})%type.
  Proof.
    destruct ms as [| Mr ms'].
    - left; exists nil; constructor.
    - destruct (raw_member_classify_dec R Mr) as [[cs Hcs] | [[[c y] r] He]].
      + destruct (raw_members_classify_dec R ms') as [[css Hcss] | [e He']].
        * left; exists (cs :: css); constructor; assumption.
        * right; exists e; intros css H; inversion H; subst; eapply He'; eassumption.
      + right; exists (raw_member_name Mr, c, y, r); intros css H; inversion H; subst; eapply He; eassumption.
  Defined.

  (** ** The Views' Relations, at a View *)

  (** Why a view is rejected, for the checker's message. *)
  Inductive view_why : Set :=
  (** The instance is no declared member of a filed group, or no record *)
  | view_why_container : view_why
  (** A container's argument at the instance is rejected: the constructor,
      the argument and why *)
  | view_why_classify : string -> string -> classify_why -> view_why
  (** A non-uniform parameter or a sibling's instance at the instance is
      not a type, or not typed *)
  | view_why_untyped : view_why
  (** A non-uniform parameter at the instance mentions the group *)
  | view_why_mentions_group : view_why.

  (** The constructors of a view, classified. *)
  Definition view_classify_dec (R : raw_decl) (x : view_key) :
    ({cs | view_classify Θ Ξ R x cs} + {e : view_why | forall cs, ~ view_classify Θ Ξ R x cs})%type.
  Proof.
    destruct x as [qc k Cs | qr Is].
    2:{ destruct (record_lookup_f F qr) as [[Rr |] Hl];
          [| right; exists view_why_container; intros cs H; inversion H; congruence ].
        destruct (classify_cons_in_dec (raw_decl_uniform_ctx_f R) (raw_decl_nu R) (raw_decl_nu R) (raw_decl_nmembers R)
                    ((rview_con, ctx_args (tele_sub (record_fctx Rr (List.length (record_fields Rr))) (sb_of_list sb_id (List.map nf_to_exp Is))))
                       :: nil)) as [[cs Hcs] | [[[c y] r] He]]; rewrite (raw_decl_uniform_ctx_f_ok R) in *.
        - left; exists cs; econstructor; eassumption.
        - right; exists (view_why_classify c y r); intros cs H; inversion H; subst; unify_found; eapply He; eassumption. }
    destruct (ind_lookup_f F qc) as [[D' |] Hl]; [| right; exists view_why_container; intros cs H; inversion H; congruence ].
    destruct (ind_member D' k) as [Mk' |] eqn:Hk; [| right; exists view_why_container; intros cs H; inversion H; subst; unify_found; congruence ].
    destruct (classify_cons_in_dec (tele_sub (im_nparams Mk') (sb_of_list sb_id (List.map nf_to_exp Cs)) ++ raw_decl_uniform_ctx_f R) (raw_decl_nu R) (im_nn Mk' + raw_decl_nu R) (raw_decl_nmembers R)
                (List.map (fun cg => (fst cg, ctx_args (tele_sub (cargs_ctx qc D' Mk' (snd cg)) (sb_qn (im_nn Mk') (sb_of_list sb_id (List.map nf_to_exp Cs))))))
                   (im_cons Mk'))) as [[cs Hcs] | [[[c y] r] He]]; rewrite (raw_decl_uniform_ctx_f_ok R) in *.
    - left; exists cs; econstructor; eassumption.
    - right; exists (view_why_classify c y r); intros cs H; inversion H; subst; unify_found; eapply He; eassumption.
  Defined.

  (** A telescope of assumptions normalized entry by entry, each a type
      first. *)
  Fixpoint nbe_tele_dec (Γ : ctx) (Δ : ctx) {struct Δ} : {Δ' | nbe_tele Θ Ξ Γ Δ Δ'} + {forall Δ', ~ nbe_tele Θ Ξ Γ Δ Δ'}.
  Proof.
    destruct Δ as [| [κ A | A M | U | A M U] Δ0].
    - left; exists nil; constructor.
    - destruct (nbe_tele_dec Γ Δ0) as [[Δ0' H0] | H0]; [| right; intros Δ' H; inversion H; subst; eapply H0; eassumption ].
      destruct (type_sorted_dec F levels_abstractable_dec HΞ (Δ0 ++ Γ) A) as [(r & i & HA) | HnA];
        [| right; intros Δ' H; inversion H as [| ? ? ? ? ? [j HA] _ _]; subst; exact (HnA _ _ HA) ].
      destruct (abs_kind_eq_dec r κ) as [-> | Hr];
        [| right; intros Δ' H; inversion H as [| ? ? ? ? ? [j HA'] _ _]; subst;
           exact (Hr (kind_sort_unique _ _ _ _ _ _ HA HA')) ].
      destruct (nbe_ty_impl F (Δ0 ++ Γ) A (nbe_order_of_type _ _ (wf_type_of_sort _ (type_sort_kind_universe κ i) HA))) as [W HW].
      left; exists (ce_ass κ (nf_to_exp W) :: Δ0'); constructor; [ exists i; exact HA | exact HW | exact H0 ].
    - right; intros Δ' H; inversion H.
    - right; intros Δ' H; inversion H.
    - right; intros Δ' H; inversion H.
  Defined.

  (** The non-uniform parameters of a view, filed. *)
  Definition view_nparams_dec (R : raw_decl) (x : view_key) :
    ({Nv | view_nparams Θ Ξ R x Nv} + {e : view_why | forall Nv, ~ view_nparams Θ Ξ R x Nv})%type.
  Proof.
    destruct x as [qc k Cs | qr Is]; [| left; exists nil; constructor ].
    destruct (ind_lookup_f F qc) as [[D' |] Hl]; [| right; exists view_why_container; intros Nv H; inversion H; congruence ].
    destruct (ind_member D' k) as [Mk' |] eqn:Hk; [| right; exists view_why_container; intros Nv H; inversion H; subst; unify_found; congruence ].
    destruct (nbe_tele_dec (raw_decl_uniform_ctx_f R) (tele_sub (im_nparams Mk') (sb_of_list sb_id (List.map nf_to_exp Cs)))) as [[Ws HWs] | HnWs];
      rewrite (raw_decl_uniform_ctx_f_ok R) in *.
    2:{ right; exists view_why_untyped; intros Nv H; inversion H; subst; unify_found; eapply HnWs; eassumption. }
    destruct (image_tele (List.repeat false (raw_decl_nu R) ++ List.repeat true (raw_decl_nmembers R)) Ws) as [Nv |] eqn:Hi.
    - left; exists Nv; econstructor; eassumption.
    - right; exists view_why_mentions_group; intros Nv H; inversion H; subst; unify_found.
      match goal with H1 : nbe_tele _ _ _ _ ?W1 |- _ => pose proof (nbe_tele_functional _ _ _ _ _ _ HWs H1) as <- end.
      congruence.
  Defined.

  (** The members of a container's group from position [i], at [Cs]. *)
  Fixpoint siblings_from_dec (Γc : ctx) (qc : qname) (Cs : list nf) (i : nat) (ms : list imember) {struct ms} :
    {ss | siblings_from Θ Ξ Γc qc Cs i ms ss} + {forall ss, ~ siblings_from Θ Ξ Γc qc Cs i ms ss}.
  Proof.
    destruct ms as [| M ms'].
    - left; exists nil; constructor.
    - destruct (siblings_from_dec Γc qc Cs (S i) ms') as [[ss Hss] | Hnss];
        [| right; intros ss H; inversion H; subst; eapply Hnss; eassumption ].
      destruct (im_head M) as [pm | qv kv Iv vmv | qr Ir flr] eqn:Hh;
        [ left; exists (vk_ind qc i Cs :: ss); eapply siblings_from_decl; eassumption | |].
      + destruct (ind_lookup_f F qv) as [[Dv |] Hlv];
          [| right; intros ss' H; inversion H; subst; unify_found; congruence ].
        destruct (nbes_dec Γc (List.map (fun I => I[sb_of_list sb_id (List.map nf_to_exp Cs)]) Iv)
                    (List.map (fun T => T[sb_of_list sb_id (List.map nf_to_exp Cs)]) (tele_insts (ind_uparams Dv) sb_id Iv))) as [[Ws HWs] | HnWs].
        * left; exists (vk_ind qv kv Ws :: ss); eapply siblings_from_view; eassumption.
        * right; intros ss' H; inversion H; subst; unify_found; try congruence.
          match goal with Hh' : im_head M = mh_view _ _ _ _ |- _ => rewrite Hh in Hh'; injection Hh'; intros; subst end.
          unify_found; eapply HnWs; eassumption.
      + destruct (record_lookup_f F qr) as [[Rr |] Hlr];
          [| right; intros ss' H; inversion H; subst; unify_found; congruence ].
        destruct (nbes_dec Γc (List.map (fun I => I[sb_of_list sb_id (List.map nf_to_exp Cs)]) Ir)
                    (List.map (fun T => T[sb_of_list sb_id (List.map nf_to_exp Cs)]) (tele_insts (record_params Rr) sb_id Ir))) as [[Ws HWs] | HnWs].
        * left; exists (vk_record qr Ws :: ss); eapply siblings_from_record; eassumption.
        * right; intros ss' H; inversion H; subst; unify_found; try congruence.
          match goal with Hh' : im_head M = mh_record _ _ _ |- _ => rewrite Hh in Hh'; injection Hh'; intros; subst end.
          unify_found; eapply HnWs; eassumption.
  Defined.

  (** The siblings of a view. *)
  Definition view_siblings_dec (R : raw_decl) (x : view_key) :
    ({ss | view_siblings Θ Ξ R x ss} + {e : view_why | forall ss, ~ view_siblings Θ Ξ R x ss})%type.
  Proof.
    destruct x as [qc k Cs | qr Is]; [| left; exists (vk_record qr Is :: nil); constructor ].
    destruct (ind_lookup_f F qc) as [[D' |] Hl]; [| right; exists view_why_container; intros ss H; inversion H; congruence ].
    destruct (siblings_from_dec (raw_decl_uniform_ctx_f R) qc Cs 0 (ind_members D')) as [[ss Hss] | Hnss]; rewrite (raw_decl_uniform_ctx_f_ok R) in *.
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
    intros * [ρ a Hi Ha Hw]; econstructor; [ eauto | eauto |].
    destruct Hw as [w Hp Hr | m w Hk Hm Hw]; [ apply nbe_term_proof; eauto | eapply nbe_term_evaluated; eauto ].
  Qed.


  Lemma equiv_typ : forall Γ A i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i -> Θ' ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i.
  Proof. intros; eapply equiv_exp; eassumption. Qed.

  Lemma equiv_nbes : forall Γ Ms As Ws, nbes Θ Ξ Γ Ms As Ws -> nbes Θ' Ξ Γ Ms As Ws.
  Proof.
    induction 1; constructor; [ exact (equiv_exp _ _ _ _ _ _ He HΞ' ltac:(eassumption)) | exact (equiv_nbe _ _ _ _ ltac:(eassumption)) | assumption ].
  Qed.

  Lemma equiv_view_inst_key : forall Γ x y, view_inst_key Θ Ξ Γ x y -> view_inst_key Θ' Ξ Γ x y.
  Proof.
    intros * [qc k Cs D' Ws Hl HWs | qr Is Rr Ws Hl HWs]; econstructor.
    - rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); exact Hl.
    - exact (equiv_nbes _ _ _ _ HWs).
    - rewrite <- (gds_equiv_record_lookup _ _ _ _ He); exact Hl.
    - exact (equiv_nbes _ _ _ _ HWs).
  Qed.

  Lemma equiv_written_carg_key : forall Γ g g', written_carg_key Θ Ξ Γ g g' -> written_carg_key Θ' Ξ Γ g g'.
  Proof.
    intros * [κ A | t t' Ht]; constructor.
    induction Ht; constructor; [ exact (equiv_view_inst_key _ _ _ ltac:(eassumption)) | assumption ].
  Qed.

  Lemma equiv_classify_arg_in : forall Γ nu np n pat T g,
      classify_arg_in Θ Ξ Γ nu np n pat T g -> classify_arg_in Θ' Ξ Γ nu np n pat T g.
  Proof.
    intros * H; destruct H as [gw g Hg Hk | i W gw g Hn HT HW Hpf Hg Hk];
      [ eapply classify_in_syn; [ exact Hg | exact (equiv_written_carg_key _ _ _ Hk) ] |].
    eapply classify_in_nf; [ exact Hn | exact (equiv_exp _ _ _ _ _ _ He HΞ' HT) | exact (equiv_nbe_ty _ _ _ HW) | exact Hpf | |
                            exact (equiv_written_carg_key _ _ _ Hk) ].
    rewrite <- (classify_arg_ext (grp_info Θ Ξ)) by (intros; unfold grp_info; rewrite (gds_equiv_ind_lookup _ _ _ _ He); reflexivity).
    rewrite <- (classify_arg_rec_ext _ (rec_info Θ Ξ)) by (intros; unfold rec_info; rewrite (gds_equiv_record_lookup _ _ _ _ He); reflexivity).
    exact Hg.
  Qed.

  Lemma equiv_classify_args_in : forall Γp nu np n pat args1 args gs,
      classify_args_in Θ Ξ Γp nu np n pat args1 args gs -> classify_args_in Θ' Ξ Γp nu np n pat args1 args gs.
  Proof. induction 1; constructor; [ apply equiv_classify_arg_in | | ]; assumption. Qed.

  Lemma equiv_classify_cons_in : forall Γp nu np n rcs cs,
      classify_cons_in Θ Ξ Γp nu np n rcs cs -> classify_cons_in Θ' Ξ Γp nu np n rcs cs.
  Proof.
    intros *; unfold classify_cons_in; apply Forall2_impl; intros rc c [Hf Hc]; split; [ exact Hf | exact (equiv_classify_args_in _ _ _ _ _ _ _ _ Hc) ].
  Qed.

  Lemma equiv_raw_member_classify : forall R ms css, Forall2 (raw_member_classify Θ Ξ R) ms css -> Forall2 (raw_member_classify Θ' Ξ R) ms css.
  Proof. intros *; apply Forall2_impl; intros; apply equiv_classify_cons_in; assumption. Qed.

  Lemma equiv_view_classify : forall R x cs, view_classify Θ Ξ R x cs -> view_classify Θ' Ξ R x cs.
  Proof.
    intros * [| ]; econstructor.
    - rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); eassumption.
    - eassumption.
    - apply equiv_classify_cons_in; assumption.
    - rewrite <- (gds_equiv_record_lookup _ _ _ _ He); eassumption.
    - apply equiv_classify_cons_in; assumption.
  Qed.

  Lemma equiv_nbe_tele : forall Γ Δ Δ', nbe_tele Θ Ξ Γ Δ Δ' -> nbe_tele Θ' Ξ Γ Δ Δ'.
  Proof.
    induction 1 as [| κ A Δ W Δ' [i HA] HW _ IH]; constructor;
      [ exists i; eapply equiv_exp; eassumption | exact (equiv_nbe_ty _ _ _ HW) | exact IH ].
  Qed.

  Lemma equiv_view_nparams : forall R x Nv, view_nparams Θ Ξ R x Nv -> view_nparams Θ' Ξ R x Nv.
  Proof.
    intros * [| ]; [| constructor ].
    econstructor; [ rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); eassumption | eassumption | | eassumption ].
    apply equiv_nbe_tele; assumption.
  Qed.


  Lemma equiv_siblings_from : forall Γc qc Cs i ms ss, siblings_from Θ Ξ Γc qc Cs i ms ss -> siblings_from Θ' Ξ Γc qc Cs i ms ss.
  Proof.
    induction 1; [ constructor | eapply siblings_from_decl; eassumption | |].
    - eapply siblings_from_view; [ eassumption | rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); eassumption | apply equiv_nbes; eassumption
                             | assumption ].
    - eapply siblings_from_record; [ eassumption | rewrite <- (gds_equiv_record_lookup _ _ _ _ He); eassumption
                               | apply equiv_nbes; eassumption | assumption ].
  Qed.

  Lemma equiv_view_siblings : forall R x ss, view_siblings Θ Ξ R x ss -> view_siblings Θ' Ξ R x ss.
  Proof.
    intros * [| ]; [| constructor ].
    econstructor; [ rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); eassumption | apply equiv_siblings_from; assumption ].
  Qed.

  Lemma equiv_raw_decl_filed : forall R Vs Ss csD csV Nvs, raw_decl_filed Θ Ξ R Vs Ss csD csV Nvs = raw_decl_filed Θ' Ξ R Vs Ss csD csV Nvs.
  Proof.
    intros; unfold raw_decl_filed; destruct (raw_decl_members R) as [| Mr0 Mrs]; [ reflexivity |].
    assert (Hrv : forall σ n Ks0 xs Vs0 Ss0 css Nvs0,
               raw_views_filed Θ Ξ σ n Ks0 xs Vs0 Ss0 css Nvs0 = raw_views_filed Θ' Ξ σ n Ks0 xs Vs0 Ss0 css Nvs0).
    { intros σ n Ks0 xs; induction xs as [| x xs IH]; intros; cbn; [ reflexivity |].
      rewrite IH; unfold raw_view_filed; destruct x as [qc k Cs | qr Is];
        [ rewrite (gds_equiv_ind_lookup _ _ _ _ He) | rewrite (gds_equiv_record_lookup _ _ _ _ He) ]; reflexivity. }
    rewrite Hrv; reflexivity.
  Qed.

  Lemma equiv_view_rank_ok : forall D rk, view_rank_ok Θ Ξ D rk -> view_rank_ok Θ' Ξ D rk.
  Proof.
    intros * [Hd Hn Hr]; constructor; [ exact Hd | | exact Hr ].
    intros *; rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); eapply Hn.
  Qed.

  (** Nor do the record views' facts without a judgment. *)
  Lemma equiv_rview_struct_ok : forall D, rview_struct_ok Θ Ξ D -> rview_struct_ok Θ' Ξ D.
  Proof.
    intros * [Hr Hn Hc Hrel Hsu Ho]; constructor; try assumption.
    - intros * Hk Hh; destruct (Hr _ _ _ _ _ Hk Hh) as [R [Hl Hnm Hct Has Hnd]]; exists R; constructor; try assumption.
      rewrite <- (gds_equiv_record_lookup _ _ _ _ He); exact Hl.
    - intros * Hk Hh Hl; rewrite <- (gds_equiv_record_lookup _ _ _ _ He) in Hl; exact (Hrel _ _ _ _ _ _ _ Hk Hh Hl).
  Qed.

  Lemma equiv_view_maps_coherent : forall D, view_maps_coherent Θ Ξ D -> view_maps_coherent Θ' Ξ D.
  Proof. intros D H; unfold view_maps_coherent in *; intros *; rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); eapply H. Qed.

  (** The group, checked at the instances [IsS], at the units filed. *)
  Lemma equiv_ind_nil_at : forall mp D IsS, ind_nil_at Θ Ξ mp D IsS -> ind_nil_at Θ' Ξ mp D IsS.
  Proof.
    destruct (deps_grow Θ Θ' Ξ (proj1 He) Hb) as (Hc & Hx & Hq & Hs & Hext & _ & _).
    assert (Hl : forall p, ind_lookup Θ Ξ p = ind_lookup Θ' Ξ p) by (intros; apply gds_equiv_ind_lookup, He).
    assert (Hr : forall p, record_lookup Θ Ξ p = record_lookup Θ' Ξ p) by (intros; apply gds_equiv_record_lookup, He).
    intros * H; destruct H.
    apply (mk_ind_nil_at Θ' Ξ mp D IsS Δ M0 i n param_level param_sorts); auto.
    all: try (intros; rewrite <- ?Hl, <- ?Hr in *; eauto; fail).
    all: try (apply equiv_rview_struct_ok; assumption).
    all: try (match goal with Hrk : exists rk, view_rank_ok _ _ _ rk |- _ =>
                destruct Hrk as [rk Hrk]; exists rk; apply equiv_view_rank_ok, Hrk end).
    all: try (apply equiv_view_maps_coherent; assumption).
  Qed.
End Equiv.
