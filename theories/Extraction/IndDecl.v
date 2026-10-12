From Stdlib Require Import List ListDec String PeanoNat Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import GlobalPresup Command.
From Mctt.Extraction Require Import PseudoMonadic TypeCheckBase IndCheck GlobalCheck.
Import Syntax_Notations GlobalCtx_Notations.

(** * Deciding a Declaration

    The well-formedness of an inductive declaration as an entry of a frame
    ([wf_gentry_indty]), decided premise by premise: the syntactic ones by
    computation, the judgments by [Extraction.GlobalCheck].  The premises
    quantifying over the arguments of the constructors and over the
    non-uniform parameters are decided along the lists, at each way of
    splitting them ([forall_split_dec]). *)

(** ** Module Variables

    [exp_mvc], computed. *)

Fixpoint exp_mvcb (n : nat) (M : exp) {struct M} : bool :=
  match M with
  | a_typ _ | a_level _ | a_llit _ | a_nat | a_zero | a_True | a_true | a_False => true
  | a_succ M | a_succl M | a_univ M => exp_mvcb n M
  | a_maxl M N => exp_mvcb n M && exp_mvcb n N
  | a_natrec A MZ MS M => exp_mvcb (S n) A && exp_mvcb n MZ && exp_mvcb (S (S n)) MS && exp_mvcb n M
  | a_exfalso A M => exp_mvcb (S n) A && exp_mvcb n M
  | a_ind _ | a_con _ _ => true
  | a_elim nm A Bs M =>
      exp_mvcb (nm + n) A &&
      (fix brs_mvcb (Bs : list (string * nat * exp)) : bool :=
         match Bs with
         | nil => true
         | b :: Bs' => exp_mvcb (snd (fst b) + n) (snd b) && brs_mvcb Bs'
         end) Bs &&
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
  | md_body Φ => gmod_mvcb n Φ
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
  | ge_ind _ _ => true
  end
with centry_mvcb (n : nat) (e : centry) {struct e} : bool :=
  match e with
  | ce_ass A => exp_mvcb n A
  | ce_def A M => exp_mvcb n A && exp_mvcb n M
  | ce_mod U => gunit_mvcb n U
  end.

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
         exp_mvc modexp_mvc bnd_mvc gunit_mvc moddef_mvc gmod_mvc gentry_mvc centry_mvc];
    rewrite ?andb_true_iff.
  all: repeat match goal with IH : forall n : nat, _ <-> _ |- _ => setoid_rewrite IH; clear IH end.
  all: try (split; auto; fail).
  - tauto.
  - (* an eliminator: its branches *)
    match goal with |- (_ /\ ?l = true) /\ _ <-> _ /\ ?r /\ _ => enough (Hb : l = true <-> r) by (rewrite Hb; tauto) end.
    clear - H0; induction H0 as [| b Bs Hb _ IH]; cbn; [ split; auto |].
    rewrite andb_true_iff, Hb, IH; reflexivity.
  - apply Nat.ltb_lt.
  - destruct oA as [A |]; [ rewrite (H A eq_refl) | split; intros [_ ?]; split; auto ]; reflexivity.
  - (* a unit: its telescope *)
    match goal with |- ?l = true /\ _ <-> ?r /\ _ => enough (Ht : l = true <-> r) by (rewrite Ht; reflexivity) end.
    clear - H; induction H as [| e Δ He _ IH]; cbn; [ split; auto |].
    rewrite andb_true_iff, He, IH; reflexivity.
  - destruct B as [M |]; [ rewrite (H0 M eq_refl) | split; intros [? _]; split; auto ]; reflexivity.
Qed.

Definition carg_mvcb (g : carg) : bool :=
  match g with
  | ca_arg A => exp_mvcb 0 A
  | ca_rec Ps => forallb (exp_mvcb 0) Ps
  end.

Definition decl_mvcb (D : ind_decl) : bool :=
  forallb (centry_mvcb 0) (ind_params D) && exp_mvcb 0 (ind_sort D) &&
  forallb (fun cg => forallb carg_mvcb (snd cg)) (ind_cons D).

Lemma forallb_Forall : forall {X} (f : X -> bool) (P : X -> Prop) l,
    (forall x, f x = true <-> P x) -> forallb f l = true <-> List.Forall P l.
Proof.
  intros * Hf; rewrite forallb_forall, List.Forall_forall; split; intros H x Hx; apply Hf; auto.
Qed.

Lemma carg_mvcb_spec : forall g, carg_mvcb g = true <-> carg_mvc g.
Proof.
  destruct mvcb_spec as (He & _).
  intros [A | Ps]; cbn; [ apply He | apply forallb_Forall; intros; apply He ].
Qed.

Lemma decl_mvcb_spec : forall D, decl_mvcb D = true <-> decl_mvc D.
Proof.
  destruct mvcb_spec as (He & _ & _ & _ & _ & _ & _ & Hc).
  intros D; unfold decl_mvcb, decl_mvc, ctx_mvc; rewrite !andb_true_iff.
  rewrite (forallb_Forall _ _ _ (fun e => Hc e 0)), He.
  rewrite (forallb_Forall _ (fun cg => List.Forall carg_mvc (snd cg)))
    by (intros; apply forallb_Forall, carg_mvcb_spec).
  rewrite List.Forall_forall.
  split; [ intros [[? ?] HF]; repeat split; auto; intros c gs Hin; exact (proj1 (List.Forall_forall _ _) HF (c, gs) Hin)
         | intros (? & ? & HF); repeat split; auto; apply List.Forall_forall; intros [c gs] Hin; exact (HF c gs Hin) ].
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

(** ** Quantifying over the Splits of a List *)

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

(** ** The Entry *)

Lemma wf_gentry_ind_iff : forall Θ Ξ mp pv D,
    Θ ⍮ Ξ ⍮ mp ⊢e ge_ind pv D <->
    (exists Δ, ind_params D = Δ ++ gs_tele Ξ) /\ List.length (gs_tele Ξ) <= ind_nu D /\ decl_typed Θ Ξ D.
Proof.
  intros; split.
  - intros H; inversion H; subst.
    split; [ eexists; eassumption |]; split; [ assumption |].
    unfold decl_typed; split; [ assumption | split; [ assumption | repeat split; eauto ] ].
  - intros ([Δ HΔ] & Hle & Hass & Hmvc & Hnp & HP & HS & [i Hi] & [n Hn] & HA & HPl & HPt & HN & Hnd).
    econstructor; eassumption.
Qed.

Lemma gs_ind_shape : forall Ξ D,
    (exists Δ, ind_params (gs_ind Ξ D) = Δ ++ gs_tele Ξ) /\ List.length (gs_tele Ξ) <= ind_nu (gs_ind Ξ D).
Proof. intros; unfold gs_ind; cbn; split; [ eexists; reflexivity | lia ]. Qed.

Section Decide.
  Variables (Θ : gdeps) (Ξ : gstack) (HΞ : ⊢g Θ ⍮ Ξ).

  (** A term of a type in a context, which is checked first. *)
  Definition check_exp_at (Γ : ctx) (A M : exp) : {Θ ⍮ Ξ ⍮ Γ ⊢ M : A} + {~ Θ ⍮ Ξ ⍮ Γ ⊢ M : A} :=
    match check_ctx Θ Ξ HΞ Γ with
    | left HΓ => check_exp Θ Ξ Γ HΓ A M
    | right HnΓ => right (fun H => HnΓ (presup_exp_ctx H))
    end.

  Definition args_dec (D : ind_decl) :
    {forall c gs gs1 A gs2, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_arg A :: gs2 ->
       Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D
         ⊢ A : (ind_sort D)[wk_shiftn (List.length (cargs_strat gs1) + ind_nn D)]ʷ}
    + {~ forall c gs gs1 A gs2, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_arg A :: gs2 ->
       Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D
         ⊢ A : (ind_sort D)[wk_shiftn (List.length (cargs_strat gs1) + ind_nn D)]ʷ}.
  Proof.
    assert (f : forall cg, List.In cg (ind_cons D) ->
      {forall gs1 g gs2, snd cg = gs1 ++ g :: gs2 -> forall A, g = ca_arg A ->
         Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D
           ⊢ A : (ind_sort D)[wk_shiftn (List.length (cargs_strat gs1) + ind_nn D)]ʷ}
      + {~ forall gs1 g gs2, snd cg = gs1 ++ g :: gs2 -> forall A, g = ca_arg A ->
         Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D
           ⊢ A : (ind_sort D)[wk_shiftn (List.length (cargs_strat gs1) + ind_nn D)]ʷ}).
    { intros cg _; apply forall_split_dec; intros gs1 [A | Ps] gs2 _.
      - destruct (check_exp_at (cargs_strat gs1 ++ ind_params D)
                    (ind_sort D)[wk_shiftn (List.length (cargs_strat gs1) + ind_nn D)]ʷ A) as [HA | HA].
        + left; intros ? [= <-]; exact HA.
        + right; intros H; exact (HA (H A eq_refl)).
      - left; intros ? [=]. }
    destruct (forall_in_dec _ _ f) as [H | H]; [ left | right ].
    - intros c gs gs1 A gs2 Hin E; exact (H (c, gs) Hin gs1 _ gs2 E A eq_refl).
    - intros H'; apply H; intros [c gs] Hin gs1 g gs2 E A ->; exact (H' c gs gs1 A gs2 Hin E).
  Defined.

  Definition recs_dec (D : ind_decl) :
    {(forall c gs gs1 Ps gs2, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec Ps :: gs2 ->
        List.length Ps = ind_nn D) /\
     (forall c gs gs1 Ps gs2 k P T, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec Ps :: gs2 ->
        List.nth_error Ps k = Some P ->
        List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length (cargs_strat gs1) + ind_nn D))) Ps) k
          = Some T ->
        Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D ⊢ P : T)}
    + {~ ((forall c gs gs1 Ps gs2, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec Ps :: gs2 ->
        List.length Ps = ind_nn D) /\
     (forall c gs gs1 Ps gs2 k P T, List.In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec Ps :: gs2 ->
        List.nth_error Ps k = Some P ->
        List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length (cargs_strat gs1) + ind_nn D))) Ps) k
          = Some T ->
        Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D ⊢ P : T))}.
  Proof.
    assert (f : forall cg, List.In cg (ind_cons D) ->
      {forall gs1 g gs2, snd cg = gs1 ++ g :: gs2 -> forall Ps, g = ca_rec Ps ->
         List.length Ps = ind_nn D /\
         forall k P T, List.nth_error Ps k = Some P ->
           List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length (cargs_strat gs1) + ind_nn D))) Ps) k
             = Some T ->
           Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D ⊢ P : T}
      + {~ forall gs1 g gs2, snd cg = gs1 ++ g :: gs2 -> forall Ps, g = ca_rec Ps ->
         List.length Ps = ind_nn D /\
         forall k P T, List.nth_error Ps k = Some P ->
           List.nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length (cargs_strat gs1) + ind_nn D))) Ps) k
             = Some T ->
           Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D ⊢ P : T}).
    { intros cg _; apply forall_split_dec; intros gs1 [A | Ps] gs2 _; [ left; intros ? [=] |].
      destruct (Nat.eq_dec (List.length Ps) (ind_nn D)) as [Hl | Hl];
        [| right; intros H; exact (Hl (proj1 (H Ps eq_refl))) ].
      destruct (forall_nth2_dec (fun P T => Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ ind_params D ⊢ P : T)
                  (fun P T => check_exp_at (cargs_strat gs1 ++ ind_params D) T P) Ps
                  (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length (cargs_strat gs1) + ind_nn D))) Ps))
        as [HP | HP].
      - left; intros ? [= <-]; split; [ exact Hl | exact HP ].
      - right; intros H; exact (HP (proj2 (H Ps eq_refl))). }
    destruct (forall_in_dec _ _ f) as [H | H]; [ left; split | right ].
    - intros c gs gs1 Ps gs2 Hin E; exact (proj1 (H (c, gs) Hin gs1 _ gs2 E Ps eq_refl)).
    - intros c gs gs1 Ps gs2 k P T Hin E; exact (proj2 (H (c, gs) Hin gs1 _ gs2 E Ps eq_refl) k P T).
    - intros [H1 H2]; apply H; intros [c gs] Hin gs1 g gs2 E Ps ->.
      split; [ exact (H1 c gs gs1 Ps gs2 Hin E) | exact (fun k P T => H2 c gs gs1 Ps gs2 k P T Hin E) ].
  Defined.

  Definition nparams_dec (D : ind_decl) :
    {forall Δ1 T Δ2, ind_nparams D = Δ1 ++ ce_ass T :: Δ2 ->
       Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ}
    + {~ forall Δ1 T Δ2, ind_nparams D = Δ1 ++ ce_ass T :: Δ2 ->
       Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ}.
  Proof.
    destruct (forall_split_dec (ind_nparams D)
                (fun Δ1 e Δ2 => forall T, e = ce_ass T ->
                   Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ))
      as [H | H].
    - intros Δ1 [T | T M | U] Δ2 _; [| left; intros ? [=] .. ].
      destruct (check_exp_at (Δ2 ++ ind_uparams D) (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ T) as [HT | HT].
      + left; intros ? [= <-]; exact HT.
      + right; intros H; exact (HT (H T eq_refl)).
    - left; intros Δ1 T Δ2 E; exact (H Δ1 _ Δ2 E T eq_refl).
    - right; intros H'; apply H; intros Δ1 e Δ2 E T ->; exact (H' Δ1 T Δ2 E).
  Defined.

  Definition decl_typed_dec (D : ind_decl) : {decl_typed Θ Ξ D} + {~ decl_typed Θ Ξ D}.
  Proof.
    unfold decl_typed.
    destruct (tele_ass_dec (ind_params D)) as [Hass | Hn]; [| right; intros (H & _); exact (Hn H) ].
    destruct (decl_mvc_dec D) as [Hmv | Hn]; [| right; intros (_ & H & _); exact (Hn H) ].
    destruct (Compare_dec.le_dec (ind_nu D) (ind_np D)) as [Hle | Hn]; [| right; intros (_ & _ & H & _); exact (Hn H) ].
    destruct (check_ctx Θ Ξ HΞ (ind_params D)) as [HP | Hn]; [| right; intros (_ & _ & _ & H & _); exact (Hn H) ].
    destruct (ind_sort_univ_dec (ind_sort D)) as [HS | Hn]; [| right; intros (_ & _ & _ & _ & H & _); exact (Hn H) ].
    destruct (check_ctx Θ Ξ HΞ (ind_uparams D)) as [HU | Hn];
      [| right; intros (_ & _ & _ & _ & _ & [i Hi] & _); exact (Hn (presup_exp_ctx Hi)) ].
    destruct (check_typ Θ Ξ (ind_uparams D) HU (ind_sort D)) as [[i Hi] | Hn];
      [| right; intros (_ & _ & _ & _ & _ & [i Hi] & _); exact (Hn i Hi) ].
    destruct (check_level Θ Ξ (ind_uparams D) HU (ind_sort_lvl (ind_sort D))) as [[n Hl] | Hn];
      [| right; intros (_ & _ & _ & _ & _ & _ & [n Hl] & _); exact (Hn n Hl) ].
    destruct (args_dec D) as [HA | Hn]; [| right; intros (_ & _ & _ & _ & _ & _ & _ & H & _); exact (Hn H) ].
    destruct (recs_dec D) as [[HPl HPt] | Hn];
      [| right; intros (_ & _ & _ & _ & _ & _ & _ & _ & HPl & HPt & _); exact (Hn (conj HPl HPt)) ].
    destruct (nparams_dec D) as [HN | Hn];
      [| right; intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _); exact (Hn H) ].
    destruct (nodup_dec (List.map fst (ind_cons D))) as [Hnd | Hn];
      [| right; intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H); exact (Hn H) ].
    left; split; [ exact Hass | split; [ exact Hmv | repeat split; eauto ] ].
  Defined.

  (** The entry a declaration is filed as. *)
  Definition ind_entry_dec (mp : qname) (pv : bool) (D : ind_decl) :
    {Θ ⍮ Ξ ⍮ mp ⊢e ge_ind pv (gs_ind Ξ D)} + {~ Θ ⍮ Ξ ⍮ mp ⊢e ge_ind pv (gs_ind Ξ D)} :=
    match decl_typed_dec (gs_ind Ξ D) with
    | left H => left (proj2 (wf_gentry_ind_iff _ _ _ _ _)
                        (conj (proj1 (gs_ind_shape Ξ D)) (conj (proj2 (gs_ind_shape Ξ D)) H)))
    | right Hn => right (fun H => Hn (proj2 (proj2 (proj1 (wf_gentry_ind_iff _ _ _ _ _) H))))
    end.
End Decide.

(** The entry crosses [gds_equiv] as the term judgments do. *)
Lemma equiv_gentry_ind : forall Θ Θ' Ξ mp pv D,
    gds_equiv Θ Θ' -> ⊢g Θ' ⍮ Ξ -> Θ ⍮ Ξ ⍮ mp ⊢e ge_ind pv D -> Θ' ⍮ Ξ ⍮ mp ⊢e ge_ind pv D.
Proof.
  intros * [Hs _] HΞ H; apply wf_gentry_ind_iff in H as (HΔ & Hle & HD).
  apply wf_gentry_ind_iff; split; [ exact HΔ | split; [ exact Hle |] ].
  eapply decl_typed_emb; [| exact HD ].
  constructor; [ exact HΞ | apply gc_sub_deps; exact Hs ].
Qed.
