(** * Scoping

    Every well-formed term is well scoped: its λ-variables are among the local
    binders.  What this buys is closedness of globals: every entry of a
    well-formed global context is stored generalized over its telescope, so its
    type and body have no free λ-variable, and weakening and substitution leave
    them alone.  The rules for globals rely on exactly that instead of premising
    it.

    Scoping is proved for all eleven judgments at once: the term judgments need
    closedness of what resolution hands back, which comes from [⊢g], which is
    checked by the term judgments. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Definitions.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Definitions

    [exp_scoped n M]: every free variable of [M] is below [n], at either sort.
    A telescope's entry is scoped by the entries below it. *)

Fixpoint exp_scoped (n : nat) (M : exp) : Prop :=
  match M with
  | a_typ _ | a_level _ | a_llit _ | a_nat | a_zero | a_True | a_true | a_False => True
  | a_succ M | a_succl M | a_univ M => exp_scoped n M
  | a_maxl M N => exp_scoped n M /\ exp_scoped n N
  | a_natrec A MZ MS M =>
      exp_scoped (S n) A /\ exp_scoped n MZ /\ exp_scoped (S (S n)) MS /\ exp_scoped n M
  | a_exfalso A M => exp_scoped (S n) A /\ exp_scoped n M
  | a_ind _ | a_con _ _ => True
  | a_elim nm A Bs M => exp_scoped (nm + n) A /\ all_brs (fun k B => exp_scoped (k + n) B) Bs /\ exp_scoped n M
  | a_pi A B | a_fn A B => exp_scoped n A /\ exp_scoped (S n) B
  | a_app M N => exp_scoped n M /\ exp_scoped n N
  | a_var x => x < n
  | a_let b B => bnd_scoped n b /\ exp_scoped (S n) B
  | a_mem H _ => modexp_scoped n H
  end
with modexp_scoped (n : nat) (H : modexp) : Prop :=
  match H with
  | me_unit _ => True
  | me_var x => x < n
  | me_mem H _ => modexp_scoped n H
  | me_app H N => modexp_scoped n H /\ exp_scoped n N
  | me_lit U => gunit_scoped n U
  end
with bnd_scoped (n : nat) (b : bnd) : Prop :=
  match b with
  | b_def oA M => match oA with Some A => exp_scoped n A | None => True end /\ exp_scoped n M
  | b_mod U => gunit_scoped n U
  end
with gunit_scoped (n : nat) (U : gunit) : Prop :=
  match U with
  | gu_mk Δ D =>
      (fix tele_scoped (Δ : list centry) : Prop :=
         match Δ with
         | nil => True
         | e :: Δ' => centry_scoped (List.length Δ' + n) e /\ tele_scoped Δ'
         end) Δ /\
      moddef_scoped (List.length Δ + n) D
  end
with moddef_scoped (n : nat) (D : moddef) : Prop :=
  match D with
  | md_body Φ => gmod_scoped n Φ
  | md_alias E => modexp_scoped n E
  end
with gmod_scoped (n : nat) (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ _ E => gmod_scoped n Φ /\ gentry_scoped (gm_binders Φ + n) E
  | gm_open Φ H _ => gmod_scoped n Φ /\ modexp_scoped (gm_binders Φ + n) H
  end
with gentry_scoped (n : nat) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B => exp_scoped n A /\ match B with Some M => exp_scoped n M | None => True end
  | ge_mod _ U => gunit_scoped n U
  | ge_ind _ _ => True
  end
with centry_scoped (n : nat) (e : centry) : Prop :=
  match e with
  | ce_ass A => exp_scoped n A
  | ce_def A M => exp_scoped n A /\ exp_scoped n M
  | ce_mod U => gunit_scoped n U
  end.

Abbreviation ce_scoped := centry_scoped.

(** Each binding is scoped by the bindings below it, and the bottom one by [n]. *)
Fixpoint ctx_scoped (n : nat) (Γ : ctx) : Prop :=
  match Γ with
  | nil => True
  | e :: Γ => ce_scoped (length Γ + n) e /\ ctx_scoped n Γ
  end.

Lemma gunit_scoped_mk : forall n Δ D,
    gunit_scoped n (gu_mk Δ D) <-> ctx_scoped n Δ /\ moddef_scoped (List.length Δ + n) D.
Proof.
  intros; cbn; enough (Heq : (fix tele_scoped (Δ : list centry) : Prop :=
         match Δ with
         | nil => True
         | e :: Δ' => centry_scoped (List.length Δ' + n) e /\ tele_scoped Δ'
         end) Δ <-> ctx_scoped n Δ) by (rewrite Heq; reflexivity).
  induction Δ; cbn; [ reflexivity | rewrite IHΔ; reflexivity ].
Qed.

#[global] Arguments gunit_scoped : simpl never.

Definition opt_scoped (n : nat) (B : option exp) : Prop :=
  match B with
  | None => True
  | Some M => exp_scoped n M
  end.

Definition sentry_scoped (n : nat) (e : sentry) : Prop :=
  match e with
  | se_var x => x < n
  | se_exp M => exp_scoped n M
  | se_mod H => modexp_scoped n H
  end.

(** ** Syntactic Facts *)

Lemma wk_q_bound : forall φ n m,
    (forall x, x < n -> φ x < m) -> forall x, x < S n -> wk_q φ x < S m.
Proof. intros * H [|x] ?; cbn; [ lia |]. specialize (H x ltac:(lia)); lia. Qed.

Lemma wk_qn_bound : forall k φ n m,
    (forall x, x < n -> φ x < m) -> forall x, x < k + n -> wk_qn k φ x < k + m.
Proof. induction k; intros * H x Hx; cbn; auto; apply wk_q_bound with (n := k + n); [ apply IHk; exact H | lia ]. Qed.

Lemma wk_q_fix : forall φ n,
    (forall x, x < n -> φ x = x) -> forall x, x < S n -> wk_q φ x = x.
Proof. intros * H [|x] ?; cbn; [ reflexivity |]. rewrite H by lia; reflexivity. Qed.

Lemma wk_qn_fix : forall k φ n,
    (forall x, x < n -> φ x = x) -> forall x, x < k + n -> wk_qn k φ x = x.
Proof. induction k; intros * H x Hx; cbn; auto; apply wk_q_fix with (n := k + n); [ apply IHk; exact H | lia ]. Qed.

Lemma sb_q_fix : forall σ n,
    (forall x, x < n -> σ x = se_var x) -> forall x, x < S n -> (q σ) x = se_var x.
Proof.
  intros * H [|x] ?; rewrite ?sb_q_zero, ?sb_q_succ; [ reflexivity |].
  rewrite H by lia; reflexivity.
Qed.

Lemma sb_qn_fix : forall k σ n,
    (forall x, x < n -> σ x = se_var x) -> forall x, x < k + n -> (sb_qn k σ) x = se_var x.
Proof. induction k; intros * H x Hx; cbn; auto; apply sb_q_fix with (n := k + n); [ apply IHk; exact H | lia ]. Qed.

(** The laws below are stated for every sort at once, like those of
    [Substitution]. *)

Ltac scoped_case :=
  intros; cbn in *;
  repeat match goal with
         | H : gunit_scoped _ (gu_mk _ _) |- _ => rewrite gunit_scoped_mk in H
         | |- gunit_scoped _ (gu_mk _ _) => rewrite gunit_scoped_mk
         end;
  rewrite ?gunit_wk_mk, ?gunit_sub_mk, ?length_tele_wk, ?length_tele_sub,
    ?gm_binders_wk, ?gm_binders_sub in *;
  repeat match goal with
         | H : gunit_scoped _ (gu_mk _ _) |- _ => rewrite gunit_scoped_mk in H
         | |- gunit_scoped _ (gu_mk _ _) => rewrite gunit_scoped_mk
         end;
  destruct_all.

(** The branches of an eliminator: an induction over the [Forall] the
    principle carries, the hypotheses about the list reverted first. *)
Ltac brs_case :=
  match goal with
  | HF : List.Forall _ ?Bs |- _ =>
      repeat match goal with H : context [Bs] |- _ => lazymatch H with HF => fail | _ => revert H end end;
      induction HF as [| [[? ?] ?] ? HB ? IH]; intros; cbn [all_brs List.map fst snd] in *; destruct_all
  end.

Lemma syn_scoped_mono :
  (forall M n m, n <= m -> exp_scoped n M -> exp_scoped m M) /\
  (forall H n m, n <= m -> modexp_scoped n H -> modexp_scoped m H) /\
  (forall b n m, n <= m -> bnd_scoped n b -> bnd_scoped m b) /\
  (forall U n m, n <= m -> gunit_scoped n U -> gunit_scoped m U) /\
  (forall D n m, n <= m -> moddef_scoped n D -> moddef_scoped m D) /\
  (forall Φ n m, n <= m -> gmod_scoped n Φ -> gmod_scoped m Φ) /\
  (forall E n m, n <= m -> gentry_scoped n E -> gentry_scoped m E) /\
  (forall e n m, n <= m -> centry_scoped n e -> centry_scoped m e).
Proof.
  syn_mut_ind; scoped_case;
    repeat match goal with
           | B : option exp |- _ => destruct B
           end; cbn in *; destruct_all;
    repeat split; try lia; eauto with arith.
  1: brs_case; [ exact I | split; [ eapply HB; [| eassumption ]; lia | auto ] ].
  clear - H H1 H2; induction H; cbn in *; destruct_all; [ auto |].
  split; [ eapply H; [| eassumption ]; lia | auto ].
Qed.

Lemma exp_scoped_mono : forall M n m, n <= m -> exp_scoped n M -> exp_scoped m M.
Proof. exact (proj1 syn_scoped_mono). Qed.

Lemma modexp_scoped_mono : forall H n m, n <= m -> modexp_scoped n H -> modexp_scoped m H.
Proof. exact (proj1 (proj2 syn_scoped_mono)). Qed.

Lemma gunit_scoped_mono : forall U n m, n <= m -> gunit_scoped n U -> gunit_scoped m U.
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_scoped_mono)))). Qed.

Lemma sentry_exp_scoped : forall n e, sentry_scoped n e -> exp_scoped n (sentry_exp e).
Proof. intros n []; cbn; auto. Qed.

Lemma sentry_modexp_scoped : forall n e, sentry_scoped n e -> modexp_scoped n (sentry_modexp e).
Proof. intros n []; cbn; auto. Qed.

#[local] Hint Resolve sentry_exp_scoped sentry_modexp_scoped : mctt.

(** One case of a scoping law: the induction hypotheses, with the bound lifted
    under the binders. *)
#[local] Arguments gunit_wk : simpl never.
#[local] Arguments gunit_sub : simpl never.

Ltac scoped_law_case lift1 lift :=
  scoped_case;
  repeat match goal with
         | B : option exp |- _ => destruct B
         end; cbn in *; destruct_all;
  repeat split;
  rewrite ?length_tele_wk, ?length_tele_sub;
  eauto using lift1, lift with mctt.

Lemma tele_wk_scoped_gen : forall Δ,
    List.Forall (fun e => forall n m φ, ce_scoped n e -> (forall x, x < n -> φ x < m) -> ce_scoped m (centry_wk e φ)) Δ ->
    forall n m φ, ctx_scoped n Δ -> (forall x, x < n -> φ x < m) -> ctx_scoped m (tele_wk Δ φ).
Proof.
  induction 1; intros * HΔ Hφ; cbn in *; destruct_all; [ auto |].
  rewrite length_tele_wk; split; eauto using wk_qn_bound.
Qed.

#[local] Hint Resolve tele_wk_scoped_gen : mctt.

Lemma syn_scoped_wk :
  (forall M n m φ, exp_scoped n M -> (forall x, x < n -> φ x < m) -> exp_scoped m M[φ]ʷ) /\
  (forall H n m φ, modexp_scoped n H -> (forall x, x < n -> φ x < m) -> modexp_scoped m (modexp_wk H φ)) /\
  (forall b n m φ, bnd_scoped n b -> (forall x, x < n -> φ x < m) -> bnd_scoped m (bnd_wk b φ)) /\
  (forall U n m φ, gunit_scoped n U -> (forall x, x < n -> φ x < m) -> gunit_scoped m (gunit_wk U φ)) /\
  (forall D n m φ, moddef_scoped n D -> (forall x, x < n -> φ x < m) -> moddef_scoped m (moddef_wk D φ)) /\
  (forall Φ n m φ, gmod_scoped n Φ -> (forall x, x < n -> φ x < m) -> gmod_scoped m (gmod_wk Φ φ)) /\
  (forall E n m φ, gentry_scoped n E -> (forall x, x < n -> φ x < m) -> gentry_scoped m (gentry_wk E φ)) /\
  (forall e n m φ, centry_scoped n e -> (forall x, x < n -> φ x < m) -> centry_scoped m (centry_wk e φ)).
Proof.
  pose proof wk_q_bound as lift1; pose proof wk_qn_bound as lift.
  syn_mut_ind; scoped_law_case lift1 lift.
  all: brs_case; [ exact I | split; [ eapply HB; [ eassumption | eapply lift; eassumption ] | auto ] ].
Qed.

Lemma exp_scoped_wk : forall M n m φ,
    exp_scoped n M -> (forall x, x < n -> φ x < m) -> exp_scoped m M[φ]ʷ.
Proof. exact (proj1 syn_scoped_wk). Qed.

Lemma modexp_scoped_wk : forall H n m φ,
    modexp_scoped n H -> (forall x, x < n -> φ x < m) -> modexp_scoped m (modexp_wk H φ).
Proof. exact (proj1 (proj2 syn_scoped_wk)). Qed.

Lemma gunit_scoped_wk : forall U n m φ,
    gunit_scoped n U -> (forall x, x < n -> φ x < m) -> gunit_scoped m (gunit_wk U φ).
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_scoped_wk)))). Qed.

Lemma centry_scoped_wk : forall e n m φ,
    centry_scoped n e -> (forall x, x < n -> φ x < m) -> centry_scoped m (centry_wk e φ).
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_wk))))))). Qed.

Corollary exp_scoped_shift : forall M n, exp_scoped n M -> exp_scoped (S n) M[↑]ʷ.
Proof. intros; eapply exp_scoped_wk; [ eassumption |]; cbn; lia. Qed.

Lemma sentry_scoped_shift : forall e n, sentry_scoped n e -> sentry_scoped (S n) (sentry_wk e ↑).
Proof.
  intros [] * H; cbn in *; [ lia | eapply exp_scoped_wk | eapply modexp_scoped_wk ];
    try eassumption; cbn; lia.
Qed.

Lemma sb_q_bound : forall σ n m,
    (forall x, x < n -> sentry_scoped m (σ x)) ->
    forall x, x < S n -> sentry_scoped (S m) ((q σ) x).
Proof.
  intros * H [|x] ?; rewrite ?sb_q_zero, ?sb_q_succ; cbn; [ lia |].
  apply sentry_scoped_shift, H; lia.
Qed.

Lemma sb_qn_bound : forall k σ n m,
    (forall x, x < n -> sentry_scoped m (σ x)) ->
    forall x, x < k + n -> sentry_scoped (k + m) ((sb_qn k σ) x).
Proof. induction k; intros * H x Hx; cbn; auto; apply sb_q_bound with (n := k + n); [ apply IHk; exact H | lia ]. Qed.

Lemma tele_sub_scoped_gen : forall Δ,
    List.Forall (fun e => forall n m σ, ce_scoped n e -> (forall x, x < n -> sentry_scoped m (σ x)) -> ce_scoped m (centry_sub e σ)) Δ ->
    forall n m σ, ctx_scoped n Δ -> (forall x, x < n -> sentry_scoped m (σ x)) -> ctx_scoped m (tele_sub Δ σ).
Proof.
  induction 1; intros * HΔ Hσ; cbn in *; destruct_all; [ auto |].
  rewrite length_tele_sub; split; eauto using sb_qn_bound.
Qed.

#[local] Hint Resolve tele_sub_scoped_gen : mctt.

Lemma syn_scoped_sub :
  (forall M n m σ, exp_scoped n M -> (forall x, x < n -> sentry_scoped m (σ x)) -> exp_scoped m M[σ]) /\
  (forall H n m σ, modexp_scoped n H -> (forall x, x < n -> sentry_scoped m (σ x)) -> modexp_scoped m H[σ]ᵐ) /\
  (forall b n m σ, bnd_scoped n b -> (forall x, x < n -> sentry_scoped m (σ x)) -> bnd_scoped m (bnd_sub b σ)) /\
  (forall U n m σ, gunit_scoped n U -> (forall x, x < n -> sentry_scoped m (σ x)) -> gunit_scoped m U[σ]ᵘ) /\
  (forall D n m σ, moddef_scoped n D -> (forall x, x < n -> sentry_scoped m (σ x)) -> moddef_scoped m (moddef_sub D σ)) /\
  (forall Φ n m σ, gmod_scoped n Φ -> (forall x, x < n -> sentry_scoped m (σ x)) -> gmod_scoped m (gmod_sub Φ σ)) /\
  (forall E n m σ, gentry_scoped n E -> (forall x, x < n -> sentry_scoped m (σ x)) -> gentry_scoped m (gentry_sub E σ)) /\
  (forall e n m σ, centry_scoped n e -> (forall x, x < n -> sentry_scoped m (σ x)) -> centry_scoped m (centry_sub e σ)).
Proof.
  pose proof sb_q_bound as lift1; pose proof sb_qn_bound as lift.
  syn_mut_ind; scoped_law_case lift1 lift.
  all: brs_case; [ exact I | split; [ eapply HB; [ eassumption | eapply lift; eassumption ] | auto ] ].
Qed.

Lemma exp_scoped_sub : forall M n m σ,
    exp_scoped n M -> (forall x, x < n -> sentry_scoped m (σ x)) -> exp_scoped m M[σ].
Proof. exact (proj1 syn_scoped_sub). Qed.

Lemma modexp_scoped_sub : forall H n m σ,
    modexp_scoped n H -> (forall x, x < n -> sentry_scoped m (σ x)) -> modexp_scoped m H[σ]ᵐ.
Proof. exact (proj1 (proj2 syn_scoped_sub)). Qed.

Lemma gunit_scoped_sub : forall U n m σ,
    gunit_scoped n U -> (forall x, x < n -> sentry_scoped m (σ x)) -> gunit_scoped m U[σ]ᵘ.
Proof. exact (proj1 (proj2 (proj2 (proj2 syn_scoped_sub)))). Qed.

Lemma tele_wk_id_gen : forall Δ,
    List.Forall (fun e => forall n φ, ce_scoped n e -> (forall x, x < n -> φ x = x) -> centry_wk e φ = e) Δ ->
    forall n φ, ctx_scoped n Δ -> (forall x, x < n -> φ x = x) -> tele_wk Δ φ = Δ.
Proof.
  induction 1; intros * HΔ Hφ; cbn in *; destruct_all; [ auto |].
  f_equal; eauto using wk_qn_fix.
Qed.

Lemma tele_sub_id_gen : forall Δ,
    List.Forall (fun e => forall n σ, ce_scoped n e -> (forall x, x < n -> σ x = se_var x) -> centry_sub e σ = e) Δ ->
    forall n σ, ctx_scoped n Δ -> (forall x, x < n -> σ x = se_var x) -> tele_sub Δ σ = Δ.
Proof.
  induction 1; intros * HΔ Hσ; cbn in *; destruct_all; [ auto |].
  f_equal; eauto using sb_qn_fix.
Qed.

Ltac scoped_id_case lift1 lift tele :=
  scoped_case;
  repeat match goal with
         | B : option exp |- _ => destruct B
         end; cbn in *; destruct_all;
  try (match goal with
       | H : forall x, x < _ -> ?σ x = se_var x |- context [?σ ?y] => rewrite H by assumption; reflexivity
       end);
  f_equal;
  try match goal with |- Some _ = Some _ => f_equal end;
  eauto using lift1, lift, tele.

Lemma syn_scoped_wk_id :
  (forall M n φ, exp_scoped n M -> (forall x, x < n -> φ x = x) -> M[φ]ʷ = M) /\
  (forall H n φ, modexp_scoped n H -> (forall x, x < n -> φ x = x) -> modexp_wk H φ = H) /\
  (forall b n φ, bnd_scoped n b -> (forall x, x < n -> φ x = x) -> bnd_wk b φ = b) /\
  (forall U n φ, gunit_scoped n U -> (forall x, x < n -> φ x = x) -> gunit_wk U φ = U) /\
  (forall D n φ, moddef_scoped n D -> (forall x, x < n -> φ x = x) -> moddef_wk D φ = D) /\
  (forall Φ n φ, gmod_scoped n Φ -> (forall x, x < n -> φ x = x) -> gmod_wk Φ φ = Φ) /\
  (forall E n φ, gentry_scoped n E -> (forall x, x < n -> φ x = x) -> gentry_wk E φ = E) /\
  (forall e n φ, centry_scoped n e -> (forall x, x < n -> φ x = x) -> centry_wk e φ = e).
Proof.
  pose proof wk_q_fix as lift1; pose proof wk_qn_fix as lift.
  syn_mut_ind; scoped_id_case lift1 lift tele_wk_id_gen.
  all: brs_case; [ reflexivity | f_equal; [ f_equal; eapply HB; [ eassumption | eapply lift; eassumption ] | auto ] ].
Qed.

Lemma syn_scoped_sub_id :
  (forall M n σ, exp_scoped n M -> (forall x, x < n -> σ x = se_var x) -> M[σ] = M) /\
  (forall H n σ, modexp_scoped n H -> (forall x, x < n -> σ x = se_var x) -> H[σ]ᵐ = H) /\
  (forall b n σ, bnd_scoped n b -> (forall x, x < n -> σ x = se_var x) -> bnd_sub b σ = b) /\
  (forall U n σ, gunit_scoped n U -> (forall x, x < n -> σ x = se_var x) -> U[σ]ᵘ = U) /\
  (forall D n σ, moddef_scoped n D -> (forall x, x < n -> σ x = se_var x) -> moddef_sub D σ = D) /\
  (forall Φ n σ, gmod_scoped n Φ -> (forall x, x < n -> σ x = se_var x) -> gmod_sub Φ σ = Φ) /\
  (forall E n σ, gentry_scoped n E -> (forall x, x < n -> σ x = se_var x) -> gentry_sub E σ = E) /\
  (forall e n σ, centry_scoped n e -> (forall x, x < n -> σ x = se_var x) -> centry_sub e σ = e).
Proof.
  pose proof sb_q_fix as lift1; pose proof sb_qn_fix as lift.
  syn_mut_ind; scoped_id_case lift1 lift tele_sub_id_gen.
  all: brs_case; [ reflexivity | f_equal; [ f_equal; eapply HB; [ eassumption | eapply lift; eassumption ] | auto ] ].
Qed.

Lemma exp_scoped_wk_id : forall M n φ,
    exp_scoped n M -> (forall x, x < n -> φ x = x) -> M[φ]ʷ = M.
Proof. exact (proj1 syn_scoped_wk_id). Qed.

Lemma exp_scoped_sub_id : forall M n σ,
    exp_scoped n M -> (forall x, x < n -> σ x = se_var x) -> M[σ] = M.
Proof. exact (proj1 syn_scoped_sub_id). Qed.

(** Two substitutions, or two weakenings, that agree on the free variables
    of a term act on it alike. *)
Lemma wk_q_agree : forall φ ψ n,
    (forall x, x < n -> φ x = ψ x) -> forall x, x < S n -> wk_q φ x = wk_q ψ x.
Proof. intros * H [|x] ?; cbn; [ reflexivity |]. rewrite H by lia; reflexivity. Qed.

Lemma wk_qn_agree : forall k φ ψ n,
    (forall x, x < n -> φ x = ψ x) -> forall x, x < k + n -> wk_qn k φ x = wk_qn k ψ x.
Proof. induction k; intros * H x Hx; cbn; auto; apply wk_q_agree with (n := k + n); [ apply IHk; exact H | lia ]. Qed.

Lemma sb_q_agree : forall σ τ n,
    (forall x, x < n -> σ x = τ x) -> forall x, x < S n -> (q σ) x = (q τ) x.
Proof.
  intros * H [|x] ?; rewrite ?sb_q_zero, ?sb_q_succ; [ reflexivity |].
  rewrite H by lia; reflexivity.
Qed.

Lemma sb_qn_agree : forall k σ τ n,
    (forall x, x < n -> σ x = τ x) -> forall x, x < k + n -> (sb_qn k σ) x = (sb_qn k τ) x.
Proof. induction k; intros * H x Hx; cbn; auto; apply sb_q_agree with (n := k + n); [ apply IHk; exact H | lia ]. Qed.

Lemma tele_wk_agree_gen : forall Δ,
    List.Forall (fun e => forall n φ ψ, ce_scoped n e -> (forall x, x < n -> φ x = ψ x) -> centry_wk e φ = centry_wk e ψ) Δ ->
    forall n φ ψ, ctx_scoped n Δ -> (forall x, x < n -> φ x = ψ x) -> tele_wk Δ φ = tele_wk Δ ψ.
Proof.
  induction 1; intros * HΔ Hφ; cbn in *; destruct_all; [ auto |].
  f_equal; eauto using wk_qn_agree.
Qed.

Lemma tele_sub_agree_gen : forall Δ,
    List.Forall (fun e => forall n σ τ, ce_scoped n e -> (forall x, x < n -> σ x = τ x) -> centry_sub e σ = centry_sub e τ) Δ ->
    forall n σ τ, ctx_scoped n Δ -> (forall x, x < n -> σ x = τ x) -> tele_sub Δ σ = tele_sub Δ τ.
Proof.
  induction 1; intros * HΔ Hσ; cbn in *; destruct_all; [ auto |].
  f_equal; eauto using sb_qn_agree.
Qed.

Ltac scoped_agree_case lift1 lift tele :=
  scoped_case;
  repeat match goal with
         | B : option exp |- _ => destruct B
         end; cbn in *; destruct_all;
  try (match goal with
       | H : forall x, x < _ -> ?σ x = ?τ x |- context [?σ ?y] => rewrite H by assumption; reflexivity
       end);
  f_equal;
  try match goal with |- Some _ = Some _ => f_equal end;
  eauto using lift1, lift, tele.

Lemma syn_scoped_wk_agree :
  (forall M n φ ψ, exp_scoped n M -> (forall x, x < n -> φ x = ψ x) -> M[φ]ʷ = M[ψ]ʷ) /\
  (forall H n φ ψ, modexp_scoped n H -> (forall x, x < n -> φ x = ψ x) -> modexp_wk H φ = modexp_wk H ψ) /\
  (forall b n φ ψ, bnd_scoped n b -> (forall x, x < n -> φ x = ψ x) -> bnd_wk b φ = bnd_wk b ψ) /\
  (forall U n φ ψ, gunit_scoped n U -> (forall x, x < n -> φ x = ψ x) -> gunit_wk U φ = gunit_wk U ψ) /\
  (forall D n φ ψ, moddef_scoped n D -> (forall x, x < n -> φ x = ψ x) -> moddef_wk D φ = moddef_wk D ψ) /\
  (forall Φ n φ ψ, gmod_scoped n Φ -> (forall x, x < n -> φ x = ψ x) -> gmod_wk Φ φ = gmod_wk Φ ψ) /\
  (forall E n φ ψ, gentry_scoped n E -> (forall x, x < n -> φ x = ψ x) -> gentry_wk E φ = gentry_wk E ψ) /\
  (forall e n φ ψ, centry_scoped n e -> (forall x, x < n -> φ x = ψ x) -> centry_wk e φ = centry_wk e ψ).
Proof.
  pose proof wk_q_agree as lift1; pose proof wk_qn_agree as lift.
  syn_mut_ind; scoped_agree_case lift1 lift tele_wk_agree_gen.
  all: brs_case; [ reflexivity | f_equal; [ f_equal; eapply HB; [ eassumption | eapply lift; eassumption ] | auto ] ].
Qed.

Lemma syn_scoped_sub_agree :
  (forall M n σ τ, exp_scoped n M -> (forall x, x < n -> σ x = τ x) -> M[σ] = M[τ]) /\
  (forall H n σ τ, modexp_scoped n H -> (forall x, x < n -> σ x = τ x) -> H[σ]ᵐ = H[τ]ᵐ) /\
  (forall b n σ τ, bnd_scoped n b -> (forall x, x < n -> σ x = τ x) -> bnd_sub b σ = bnd_sub b τ) /\
  (forall U n σ τ, gunit_scoped n U -> (forall x, x < n -> σ x = τ x) -> U[σ]ᵘ = U[τ]ᵘ) /\
  (forall D n σ τ, moddef_scoped n D -> (forall x, x < n -> σ x = τ x) -> moddef_sub D σ = moddef_sub D τ) /\
  (forall Φ n σ τ, gmod_scoped n Φ -> (forall x, x < n -> σ x = τ x) -> gmod_sub Φ σ = gmod_sub Φ τ) /\
  (forall E n σ τ, gentry_scoped n E -> (forall x, x < n -> σ x = τ x) -> gentry_sub E σ = gentry_sub E τ) /\
  (forall e n σ τ, centry_scoped n e -> (forall x, x < n -> σ x = τ x) -> centry_sub e σ = centry_sub e τ).
Proof.
  pose proof sb_q_agree as lift1; pose proof sb_qn_agree as lift.
  syn_mut_ind; scoped_agree_case lift1 lift tele_sub_agree_gen.
  all: brs_case; [ reflexivity | f_equal; [ f_equal; eapply HB; [ eassumption | eapply lift; eassumption ] | auto ] ].
Qed.

Lemma exp_scoped_wk_agree : forall M n φ ψ,
    exp_scoped n M -> (forall x, x < n -> φ x = ψ x) -> M[φ]ʷ = M[ψ]ʷ.
Proof. exact (proj1 syn_scoped_wk_agree). Qed.

Lemma exp_scoped_sub_agree : forall M n σ τ,
    exp_scoped n M -> (forall x, x < n -> σ x = τ x) -> M[σ] = M[τ].
Proof. exact (proj1 syn_scoped_sub_agree). Qed.

Lemma tele_scoped_sub_agree : forall Δ n σ τ,
    ctx_scoped n Δ -> (forall x, x < n -> σ x = τ x) -> tele_sub Δ σ = tele_sub Δ τ.
Proof.
  intros; eapply tele_sub_agree_gen; [| eassumption | assumption ].
  apply List.Forall_forall; intros e _ k ρ ρ' He Hρ.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_sub_agree)))))) _ _ _ _ He Hρ).
Qed.

Lemma tele_scoped_wk_agree : forall Δ n φ ψ,
    ctx_scoped n Δ -> (forall x, x < n -> φ x = ψ x) -> tele_wk Δ φ = tele_wk Δ ψ.
Proof.
  intros; eapply tele_wk_agree_gen; [| eassumption | assumption ].
  apply List.Forall_forall; intros e _ k ρ ρ' He Hρ.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_wk_agree)))))) _ _ _ _ He Hρ).
Qed.

(** ** Module Variables

    A term all of whose module variables are bound in it ([exp_mvc], in
    [Inductives]) is moved alike by substitutions that send the same terms:
    a variable sent as [se_var] and as [se_exp] of the variable. *)


Lemma gunit_mvc_mk : forall n Δ D,
    gunit_mvc n (gu_mk Δ D) <->
    (fix tele_mvc (Δ : list centry) : Prop :=
       match Δ with
       | nil => True
       | e :: Δ' => centry_mvc (List.length Δ' + n) e /\ tele_mvc Δ'
       end) Δ /\ moddef_mvc (List.length Δ + n) D.
Proof. intros; reflexivity. Qed.


(** Substitutions that send the same terms everywhere, and the same
    entries below [d], act alike on a term whose module variables are all
    bound below [d]. *)
Lemma sb_q_exp_agree : forall σ τ,
    (forall x, sentry_exp (σ x) = sentry_exp (τ x)) -> forall x, sentry_exp ((q σ) x) = sentry_exp ((q τ) x).
Proof.
  intros * H [| x]; rewrite ?sb_q_zero, ?sb_q_succ; [ reflexivity |].
  rewrite <- !sentry_exp_wk, H; reflexivity.
Qed.

Lemma sb_qn_exp_agree : forall k σ τ,
    (forall x, sentry_exp (σ x) = sentry_exp (τ x)) -> forall x, sentry_exp ((sb_qn k σ) x) = sentry_exp ((sb_qn k τ) x).
Proof. induction k; intros * H x; cbn; auto; apply sb_q_exp_agree; auto. Qed.

Lemma tele_sub_mvc_gen : forall Δ,
    List.Forall (fun e => forall n σ τ, centry_mvc n e -> (forall x, x < n -> σ x = τ x) ->
                   (forall x, sentry_exp (σ x) = sentry_exp (τ x)) -> centry_sub e σ = centry_sub e τ) Δ ->
    forall n σ τ,
      (fix tele_mvc (Δ : list centry) : Prop :=
         match Δ with
         | nil => True
         | e :: Δ' => centry_mvc (List.length Δ' + n) e /\ tele_mvc Δ'
         end) Δ ->
      (forall x, x < n -> σ x = τ x) -> (forall x, sentry_exp (σ x) = sentry_exp (τ x)) ->
      tele_sub Δ σ = tele_sub Δ τ.
Proof.
  induction 1; intros * HΔ Hσ He; cbn in *; destruct_all; [ auto |].
  f_equal; eauto using sb_qn_agree, sb_qn_exp_agree.
Qed.

Ltac mvc_case :=
  intros; cbn in *;
  repeat match goal with
         | H : gunit_mvc _ (gu_mk _ _) |- _ => rewrite gunit_mvc_mk in H
         end;
  rewrite ?gunit_sub_mk, ?length_tele_sub, ?gm_binders_sub in *;
  destruct_all;
  repeat match goal with
         | B : option exp |- _ => destruct B
         end; cbn in *; destruct_all;
  try (match goal with
       | H : forall x, x < _ -> ?σ x = ?τ x |- context [?σ ?y] => rewrite H by assumption; reflexivity
       end);
  try (match goal with
       | H : forall x, sentry_exp (?σ x) = sentry_exp (?τ x) |- sentry_exp (?σ ?y) = _ => apply H
       end);
  f_equal;
  try match goal with |- Some _ = Some _ => f_equal end;
  eauto using sb_q_agree, sb_qn_agree, sb_q_exp_agree, sb_qn_exp_agree, tele_sub_mvc_gen.

Lemma syn_mvc_sub_agree :
  (forall M n σ τ, exp_mvc n M -> (forall x, x < n -> σ x = τ x) ->
     (forall x, sentry_exp (σ x) = sentry_exp (τ x)) -> M[σ] = M[τ]) /\
  (forall H n σ τ, modexp_mvc n H -> (forall x, x < n -> σ x = τ x) ->
     (forall x, sentry_exp (σ x) = sentry_exp (τ x)) -> H[σ]ᵐ = H[τ]ᵐ) /\
  (forall b n σ τ, bnd_mvc n b -> (forall x, x < n -> σ x = τ x) ->
     (forall x, sentry_exp (σ x) = sentry_exp (τ x)) -> bnd_sub b σ = bnd_sub b τ) /\
  (forall U n σ τ, gunit_mvc n U -> (forall x, x < n -> σ x = τ x) ->
     (forall x, sentry_exp (σ x) = sentry_exp (τ x)) -> U[σ]ᵘ = U[τ]ᵘ) /\
  (forall D n σ τ, moddef_mvc n D -> (forall x, x < n -> σ x = τ x) ->
     (forall x, sentry_exp (σ x) = sentry_exp (τ x)) -> moddef_sub D σ = moddef_sub D τ) /\
  (forall Φ n σ τ, gmod_mvc n Φ -> (forall x, x < n -> σ x = τ x) ->
     (forall x, sentry_exp (σ x) = sentry_exp (τ x)) -> gmod_sub Φ σ = gmod_sub Φ τ) /\
  (forall E n σ τ, gentry_mvc n E -> (forall x, x < n -> σ x = τ x) ->
     (forall x, sentry_exp (σ x) = sentry_exp (τ x)) -> gentry_sub E σ = gentry_sub E τ) /\
  (forall e n σ τ, centry_mvc n e -> (forall x, x < n -> σ x = τ x) ->
     (forall x, sentry_exp (σ x) = sentry_exp (τ x)) -> centry_sub e σ = centry_sub e τ).
Proof.
  syn_mut_ind; mvc_case.
  all: try solve [ eauto 8 using sb_q_agree, sb_q_exp_agree ].
  all: brs_case; [ reflexivity | f_equal; [ f_equal; eapply HB; eauto using sb_qn_agree, sb_qn_exp_agree | auto ] ].
Qed.

(** A term with no free module variable: substitutions that send the same
    terms act alike on it, whatever they send its module variables to. *)
Corollary exp_mvc_sub_agree : forall M σ τ,
    exp_mvc 0 M -> (forall x, sentry_exp (σ x) = sentry_exp (τ x)) -> M[σ] = M[τ].
Proof. intros; eapply (proj1 syn_mvc_sub_agree); [ eassumption | lia | assumption ]. Qed.

(** A weakening that keeps the bound module variables bound keeps a term's
    module variables bound. *)
Lemma tele_wk_mvc_gen : forall Δ,
    List.Forall (fun e => forall n φ, centry_mvc n e -> (forall x, x < n -> φ x < n) -> centry_mvc n (centry_wk e φ)) Δ ->
    forall n φ,
      (fix tele_mvc (Δ : list centry) : Prop :=
         match Δ with
         | nil => True
         | e :: Δ' => centry_mvc (List.length Δ' + n) e /\ tele_mvc Δ'
         end) Δ ->
      (forall x, x < n -> φ x < n) ->
      (fix tele_mvc (Δ : list centry) : Prop :=
         match Δ with
         | nil => True
         | e :: Δ' => centry_mvc (List.length Δ' + n) e /\ tele_mvc Δ'
         end) (tele_wk Δ φ).
Proof.
  induction 1 as [| e Δ He HΔ IH]; intros * Htele Hφ; cbn in *; destruct_all; [ auto |].
  rewrite length_tele_wk; split; [ apply He; [ assumption | apply wk_qn_bound; exact Hφ ] | apply IH; assumption ].
Qed.

Ltac mvc_wk_case :=
  intros; cbn in *;
  repeat match goal with
         | H : gunit_mvc _ (gu_mk _ _) |- _ => rewrite gunit_mvc_mk in H
         end;
  rewrite ?gunit_wk_mk, ?length_tele_wk, ?gm_binders_wk in *;
  repeat match goal with
         | |- gunit_mvc _ (gu_mk _ _) => rewrite gunit_mvc_mk
         end;
  destruct_all;
  repeat match goal with
         | B : option exp |- _ => destruct B
         end; cbn in *; destruct_all;
  repeat split;
  rewrite ?length_tele_wk;
  eauto using wk_q_bound, wk_qn_bound.

Lemma syn_mvc_wk :
  (forall M n φ, exp_mvc n M -> (forall x, x < n -> φ x < n) -> exp_mvc n M[φ]ʷ) /\
  (forall H n φ, modexp_mvc n H -> (forall x, x < n -> φ x < n) -> modexp_mvc n (modexp_wk H φ)) /\
  (forall b n φ, bnd_mvc n b -> (forall x, x < n -> φ x < n) -> bnd_mvc n (bnd_wk b φ)) /\
  (forall U n φ, gunit_mvc n U -> (forall x, x < n -> φ x < n) -> gunit_mvc n (gunit_wk U φ)) /\
  (forall D n φ, moddef_mvc n D -> (forall x, x < n -> φ x < n) -> moddef_mvc n (moddef_wk D φ)) /\
  (forall Φ n φ, gmod_mvc n Φ -> (forall x, x < n -> φ x < n) -> gmod_mvc n (gmod_wk Φ φ)) /\
  (forall E n φ, gentry_mvc n E -> (forall x, x < n -> φ x < n) -> gentry_mvc n (gentry_wk E φ)) /\
  (forall e n φ, centry_mvc n e -> (forall x, x < n -> φ x < n) -> centry_mvc n (centry_wk e φ)).
Proof.
  syn_mut_ind; mvc_wk_case.
  all: try solve [ eapply tele_wk_mvc_gen; eassumption ].
  all: brs_case; [ exact I | split; [ eapply HB; [ eassumption | eapply wk_qn_bound; eassumption ] | auto ] ].
Qed.

Corollary exp_mvc_wk : forall M φ, exp_mvc 0 M -> exp_mvc 0 M[φ]ʷ.
Proof. intros; eapply (proj1 syn_mvc_wk); [ eassumption | lia ]. Qed.

(** The same for a term of [n] free variables: the substitutions need only
    send the same terms to those. *)
Corollary exp_scoped_mvc_agree : forall M n σ τ,
    exp_scoped n M -> exp_mvc 0 M -> (forall x, x < n -> sentry_exp (σ x) = sentry_exp (τ x)) -> M[σ] = M[τ].
Proof.
  intros * Hs Hm Hag.
  transitivity (M[fun x => if x <? n then τ x else σ x]).
  - apply exp_mvc_sub_agree; [ exact Hm |]; intros x; destruct (Nat.ltb_spec x n); [ apply Hag; lia | reflexivity ].
  - eapply exp_scoped_sub_agree; [ exact Hs |]; intros x Hx; destruct (Nat.ltb_spec x n); [ reflexivity | lia ].
Qed.

(** A term with no free variable is fixed by every weakening and every
    substitution, and so is a unit. *)
Corollary exp_closed_wk : forall M φ, exp_scoped 0 M -> M[φ]ʷ = M.
Proof. intros; eapply exp_scoped_wk_id; [ eassumption | lia ]. Qed.

Corollary exp_closed_sub : forall M σ, exp_scoped 0 M -> M[σ] = M.
Proof. intros; eapply exp_scoped_sub_id; [ eassumption | lia ]. Qed.

Corollary gunit_closed_wk : forall U φ, gunit_scoped 0 U -> gunit_wk U φ = U.
Proof. intros; eapply (proj1 (proj2 (proj2 (proj2 syn_scoped_wk_id)))); [ eassumption | lia ]. Qed.

Corollary gunit_closed_sub : forall U σ, gunit_scoped 0 U -> U[σ]ᵘ = U.
Proof. intros; eapply (proj1 (proj2 (proj2 (proj2 syn_scoped_sub_id)))); [ eassumption | lia ]. Qed.

Corollary tele_closed_wk : forall Δ φ, ctx_scoped 0 Δ -> tele_wk Δ φ = Δ.
Proof.
  intros; eapply tele_wk_id_gen; [| eassumption | lia ].
  apply List.Forall_forall; intros e _ n ψ He Hψ.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_wk_id)))))) _ _ _ He Hψ).
Qed.

Corollary tele_closed_sub : forall Δ σ, ctx_scoped 0 Δ -> tele_sub Δ σ = Δ.
Proof.
  intros; eapply tele_sub_id_gen; [| eassumption | lia ].
  apply List.Forall_forall; intros e _ n τ He Hτ.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_sub_id)))))) _ _ _ He Hτ).
Qed.

Lemma tele_wk_scoped : forall Δ n m φ,
    ctx_scoped n Δ -> (forall x, x < n -> φ x < m) -> ctx_scoped m (tele_wk Δ φ).
Proof.
  intros; eapply tele_wk_scoped_gen; [| eassumption | assumption ].
  apply List.Forall_forall; intros e _ k l ψ He Hψ.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_wk)))))) _ _ _ _ He Hψ).
Qed.

Lemma tele_sub_scoped : forall Δ n m σ,
    ctx_scoped n Δ -> (forall x, x < n -> sentry_scoped m (σ x)) -> ctx_scoped m (tele_sub Δ σ).
Proof.
  intros; eapply tele_sub_scoped_gen; [| eassumption | assumption ].
  apply List.Forall_forall; intros e _ k l τ He Hτ.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_sub)))))) _ _ _ _ He Hτ).
Qed.

(** ** Telescopes *)

Lemma ctx_scoped_app : forall Γ Δ n,
    ctx_scoped n (Γ ++ Δ) <-> ctx_scoped (length Δ + n) Γ /\ ctx_scoped n Δ.
Proof.
  induction Γ; intros; cbn; [ tauto |].
  rewrite IHΓ, List.length_app, Nat.add_assoc; tauto.
Qed.


Lemma ctx_scoped_lookup : forall Γ x A n,
    ctx_scoped n Γ ->
    Γ ∋ #x : A ->
    exp_scoped (length Γ + n) A.
Proof.
  intros * HΓ Hlk; induction Hlk; cbn in *; destruct_all;
    apply exp_scoped_shift; auto.
Qed.

Lemma ctx_lookup_def_lookup : forall Γ x A M, Γ ∋ #x ≔ M : A -> Γ ∋ #x : A.
Proof.
  induction 1; constructor; assumption.
Qed.

#[export]
Hint Resolve ctx_lookup_def_lookup : mctt.

Lemma ctx_scoped_lookup_def : forall Γ x A M n,
    ctx_scoped n Γ ->
    Γ ∋ #x ≔ M : A ->
    exp_scoped (length Γ + n) M.
Proof.
  intros * HΓ Hlk; induction Hlk; cbn in *; destruct_all;
    apply exp_scoped_shift; auto.
Qed.

Lemma ctx_lookup_length : forall Γ x A, Γ ∋ #x : A -> x < length Γ.
Proof.
  induction 1; cbn; lia.
Qed.

Lemma ctx_lookup_app_left : forall Γ Δ x A, Γ ∋ #x : A -> Γ ++ Δ ∋ #x : A.
Proof. induction 1; cbn; constructor; assumption. Qed.

Lemma ctx_pi_scoped : forall Δ A n,
    ctx_scoped n Δ ->
    exp_scoped (length Δ + n) A ->
    exp_scoped n (ctx_pi Δ A).
Proof.
  induction Δ as [| [] Δ IHΔ]; intros * HΔ HA; cbn in *; destruct_all; [ assumption | | |].
  all: apply IHΔ; cbn; auto.
Qed.

Lemma ctx_fn_scoped : forall Δ M n,
    ctx_scoped n Δ ->
    exp_scoped (length Δ + n) M ->
    exp_scoped n (ctx_fn Δ M).
Proof.
  induction Δ as [| [] Δ IHΔ]; intros * HΔ HM; cbn in *; destruct_all; [ assumption | | |].
  all: apply IHΔ; cbn; auto.
Qed.

(** The substitutions the rules instantiate with. *)

Lemma exp_scoped_sub1 : forall A M n,
    exp_scoped (S n) A -> exp_scoped n M -> exp_scoped n A[Id,,M].
Proof. intros; eapply exp_scoped_sub; [ eassumption |]; intros [|x] ?; cbn; auto; lia. Qed.

Lemma exp_scoped_sub2 : forall A M N n,
    exp_scoped (S (S n)) A -> exp_scoped n M -> exp_scoped n N -> exp_scoped n A[Id,,M,,N].
Proof. intros; eapply exp_scoped_sub; [ eassumption |]; intros [|[|x]] ?; cbn; auto; lia. Qed.

Lemma exp_scoped_sub_succ : forall A n,
    exp_scoped (S n) A -> exp_scoped (S (S n)) A[Wk⨟Wk,,succ #1].
Proof. intros; eapply exp_scoped_sub; [ eassumption |]; intros [|x] ?; cbn; lia. Qed.

Lemma exp_scoped_sub1_mod : forall A H n,
    exp_scoped (S n) A -> modexp_scoped n H -> exp_scoped n A[Id ,,ₘ H].
Proof. intros; eapply exp_scoped_sub; [ eassumption |]; intros [|x] ?; cbn; auto; lia. Qed.

#[local]
Hint Resolve exp_scoped_sub1 exp_scoped_sub2 exp_scoped_sub_succ exp_scoped_shift exp_scoped_sub1_mod : mctt.

Lemma ctx_lookup_mod_length : forall Γ x U, Γ ∋ #x ⇒ₘ U -> x < length Γ.
Proof. induction 1; cbn; lia. Qed.

Lemma length_body_ctx : forall Φ, length (body_ctx Φ) = gm_binders Φ.
Proof. induction Φ as [| Φ IH x [? ? ? [] | | ] | Φ IH c]; cbn; rewrite ?length_app, ?repeat_length; auto. Qed.

(** A typed body, with no local import, is scoped when the context it binds
    is. *)
Lemma gmod_scoped_of_body_ctx : forall Φ Φ' n,
    body_shape Φ Φ' ->
    (ctx_scoped n (body_ctx Φ) -> gmod_scoped n Φ) /\ (ctx_scoped n (body_ctx Φ') -> gmod_scoped n Φ').
Proof.
  induction Φ as [| Φ IH x E | Φ IH c]; intros [| Φ' x' E' | Φ' c'] n Hs; cbn in Hs; try contradiction.
  - split; intros; exact I.
  - destruct Hs as (Hs & -> & HE); destruct (IH _ n Hs) as [IH1 IH2].
    destruct E as [? ? ? [] | | ], E' as [? ? ? [] | | ]; cbn in HE; try contradiction;
      split; intros HΦ; cbn in *; destruct_all; repeat split; auto;
      first [ rewrite <- length_body_ctx; assumption | rewrite <- (length_body_ctx Φ'); assumption ].
Qed.

(** ** Inductive Types

    A declaration is closed: its parameters are a closed telescope of
    assumptions, its sort is in the uniform ones, and the types of the
    arguments of its constructors are in the parameters and the
    non-recursive arguments before them. *)

Definition decl_closed (D : ind_decl) : Prop :=
  tele_ass (ind_params D) /\ ind_nu D <= ind_np D /\ ctx_scoped 0 (ind_params D) /\
  exp_scoped (ind_nu D) (ind_sort D) /\
  (forall c gs gs1 A gs2, In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_arg A :: gs2 ->
     exp_scoped (List.length (cargs_strat gs1) + ind_np D) A) /\
  (forall c gs gs1 Ps gs2, In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec Ps :: gs2 ->
     List.Forall (exp_scoped (List.length (cargs_strat gs1) + ind_np D)) Ps) /\
  (forall c gs gs1 Ps gs2, In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec Ps :: gs2 ->
     List.length Ps = ind_nn D).

Lemma exp_scoped_apps : forall Ns M n,
    exp_scoped n (apps M Ns) <-> exp_scoped n M /\ List.Forall (exp_scoped n) Ns.
Proof.
  induction Ns as [| N Ns IH]; intros; cbn; [ split; [ auto | tauto ] |].
  rewrite IH, List.Forall_cons_iff; cbn; tauto.
Qed.

Lemma vars_from_scoped : forall k m n, k + m <= n -> List.Forall (exp_scoped n) (vars_from k m).
Proof.
  intros * H; unfold vars_from; apply List.Forall_map, List.Forall_forall.
  intros i Hi; apply List.in_rev, List.in_seq in Hi; cbn; lia.
Qed.

Lemma sb_of_list_bound : forall Ms σ n m,
    (forall x, x < n -> sentry_scoped m (σ x)) -> List.Forall (exp_scoped m) Ms ->
    forall x, x < List.length Ms + n -> sentry_scoped m (sb_of_list σ Ms x).
Proof.
  induction Ms as [| M Ms IH]; intros * Hσ HMs x Hx; cbn in *; [ auto |].
  inversion_clear HMs.
  apply (IH _ (S n)); [| assumption | lia ].
  intros [| y] Hy; cbn; [ assumption | apply Hσ; lia ].
Qed.

Lemma sb_id_bound : forall n x, x < n -> sentry_scoped n (Id x).
Proof. intros; cbn; assumption. Qed.

Lemma exp_scoped_sb_of_list : forall A Ms n,
    exp_scoped (List.length Ms + n) A -> List.Forall (exp_scoped n) Ms -> exp_scoped n A[sb_of_list Id Ms].
Proof. intros; eapply exp_scoped_sub; [ eassumption |]; apply sb_of_list_bound; [ exact (sb_id_bound n) | assumption ]. Qed.

(** The number of non-recursive arguments a pattern tells. *)
Fixpoint pat_nargs (pat : list bool) : nat :=
  match pat with
  | nil => 0
  | false :: pat' => S (pat_nargs pat')
  | true :: pat' => pat_nargs pat'
  end.

Lemma wk_pat_bound : forall pat n x, x < pat_nargs pat + n -> wk_pat pat x < List.length pat + n.
Proof.
  induction pat as [| [] pat IH]; intros * Hx; cbn in *; [ lia | |].
  - unfold wk_compose, wk_shift; specialize (IH n x Hx); lia.
  - destruct x as [| x]; cbn; [ lia |]; specialize (IH n x ltac:(lia)); lia.
Qed.

Lemma length_cargs_strat_app : forall gs1 gs2,
    List.length (cargs_strat (gs1 ++ gs2)) = List.length (cargs_strat gs1) + List.length (cargs_strat gs2).
Proof. induction gs1 as [| [] gs1 IH]; intros; cbn; rewrite ?length_app, ?IH; cbn; lia. Qed.

Lemma length_ind_uparams : forall D, ind_nu D <= ind_np D -> List.length (ind_uparams D) = ind_nu D.
Proof. intros; unfold ind_uparams, ind_nn, ind_np in *; rewrite length_skipn; lia. Qed.

Lemma cargs_ctx_aux_scoped : forall p D gs pat k,
    ind_nu D <= ind_np D ->
    pat_nargs pat = k ->
    (forall gs1 A gs2, gs = gs1 ++ ca_arg A :: gs2 ->
       exp_scoped (k + List.length (cargs_strat gs1) + ind_np D) A) ->
    (forall gs1 Ps gs2, gs = gs1 ++ ca_rec Ps :: gs2 ->
       List.Forall (exp_scoped (k + List.length (cargs_strat gs1) + ind_np D)) Ps) ->
    ctx_scoped (List.length pat + ind_np D) (cargs_ctx_aux p D pat gs).
Proof.
  induction gs as [| [A | Ps] gs IH]; intros * Hle Hk HA HPs; cbn; [ exact I | |].
  all: rewrite ctx_scoped_app; cbn; split; [| split; [| exact I ] ].
  - apply (IH (false :: pat) (S k) Hle); cbn; [ rewrite Hk; reflexivity | |].
    + intros gs1 A' gs2 ->; specialize (HA (ca_arg A :: gs1) A' gs2 eq_refl); cbn in HA.
      rewrite length_app in HA; cbn in HA; match goal with |- exp_scoped ?n _ => replace n with (k + (length (cargs_strat gs1) + 1) + ind_np D) by lia end; exact HA.
    + intros gs1 Ps gs2 ->; specialize (HPs (ca_arg A :: gs1) Ps gs2 eq_refl); cbn in HPs.
      rewrite length_app in HPs; cbn in HPs; match goal with |- List.Forall (exp_scoped ?n) _ => replace n with (k + (length (cargs_strat gs1) + 1) + ind_np D) by lia end; exact HPs.
  - specialize (HA nil A gs eq_refl); cbn in HA.
    eapply exp_scoped_wk; [ exact HA |]; intros x Hx; rewrite ?Nat.add_0_r; apply wk_pat_bound; lia.
  - apply (IH (true :: pat) k Hle); cbn; [ exact Hk | |].
    + intros gs1 A' gs2 ->; exact (HA (ca_rec Ps :: gs1) A' gs2 eq_refl).
    + intros gs1 Ps' gs2 ->; exact (HPs (ca_rec Ps :: gs1) Ps' gs2 eq_refl).
  - specialize (HPs nil Ps gs eq_refl); cbn in HPs; rewrite Nat.add_0_r in HPs.
    apply exp_scoped_apps; split; [ exact I |]; apply List.Forall_app; split.
    + unfold ind_uvars; apply vars_from_scoped; unfold ind_nn; lia.
    + apply List.Forall_map; eapply List.Forall_impl; [| exact HPs ].
      intros P HP; eapply exp_scoped_wk; [ exact HP |]; intros; apply wk_pat_bound; lia.
Qed.

Lemma decl_closed_ind_ty : forall D, decl_closed D -> exp_scoped 0 (ind_ty D).
Proof.
  intros D (_ & Hle & HΔ & HS & _); unfold ind_ty; apply ctx_pi_scoped; [ assumption |].
  eapply exp_scoped_wk; [ exact HS |]; intros x Hx; unfold ind_nn in *.
  cbn; unfold ind_np in *; lia.
Qed.

Lemma decl_closed_con_ty : forall p D c gs, decl_closed D -> In (c, gs) (ind_cons D) -> exp_scoped 0 (con_ty p D gs).
Proof.
  intros p D c gs (_ & Hle & HΔ & _ & HA & HPs & _) Hin; unfold con_ty; apply ctx_pi_scoped; [ assumption |].
  rewrite Nat.add_0_r; apply ctx_pi_scoped.
  - apply (cargs_ctx_aux_scoped p D gs nil 0 Hle eq_refl); intros; cbn; eauto.
  - apply exp_scoped_apps; split; [ exact I |].
    unfold ind_pvars; apply vars_from_scoped; rewrite length_cargs_ctx; unfold ind_np; lia.
Qed.

(** Lists typed one by one at as many types are scoped. *)
Lemma nth_typed_scoped : forall Ms (Ts : list typ) n,
    List.length Ts = List.length Ms ->
    (forall k M T, nth_error Ms k = Some M -> nth_error Ts k = Some T -> exp_scoped n M) ->
    List.Forall (exp_scoped n) Ms.
Proof.
  intros * Hl H; apply List.Forall_forall; intros M HM.
  destruct (List.In_nth_error _ _ HM) as [k Hk].
  destruct (nth_error Ts k) as [T |] eqn:HT; [ eauto |].
  apply List.nth_error_None in HT; assert (Hk' : nth_error Ms k <> None) by congruence; apply List.nth_error_Some in Hk'; lia.
Qed.

Lemma length_tele_insts_params : forall D σ Ps,
    tele_ass (ind_params D) -> List.length Ps = ind_np D -> List.length (tele_insts (ind_params D) σ Ps) = List.length Ps.
Proof. intros * HΔ Hl; rewrite length_tele_insts by exact HΔ; unfold ind_np in *; lia. Qed.

Lemma length_tele_insts_cargs : forall p D gs σ As,
    List.length As = List.length gs -> List.length (tele_insts (cargs_ctx p D gs) σ As) = List.length As.
Proof. intros * Hl; rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; lia. Qed.

Lemma elim_brs_scoped : forall p D Us A Bs m,
    brs_names (ind_cons D) Bs ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> exp_scoped (List.length (elim_bctx p D gs A Us) + m) B) ->
    all_brs (fun k B => exp_scoped (k + m) B) Bs.
Proof.
  intros * Hn Hk HB; apply all_brs_Forall, List.Forall_forall; intros [[c n] B] Hin; cbn.
  destruct (brs_names_con _ _ _ _ _ Hn Hin) as [gs Hgs].
  rewrite (Hk _ _ _ _ Hgs Hin); specialize (HB _ _ _ _ Hgs Hin); rewrite length_elim_bctx in HB.
  replace (ind_nn D + length gs + cargs_nrec gs) with (cargs_nrec gs + length gs + ind_nn D) by lia; exact HB.
Qed.

Lemma brs_nth_same : forall (Bs Bs' : list (String.string * nat * exp)) k c n B,
    List.map fst Bs = List.map fst Bs' -> nth_error Bs k = Some (c, n, B) -> exists B', nth_error Bs' k = Some (c, n, B').
Proof.
  intros * Hm Hk; apply (f_equal (fun l => nth_error l k)) in Hm; rewrite !nth_error_map, Hk in Hm.
  destruct (nth_error Bs' k) as [[[c' n'] B'] |]; cbn in Hm; [ injection Hm as -> ->; eauto | discriminate ].
Qed.

Lemma elim_brs_scoped' : forall p D Us A Bs (Bs' : list (String.string * nat * exp)) m,
    brs_names (ind_cons D) Bs ->
    List.map fst Bs = List.map fst Bs' ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall k c gs n B B', nth_error Bs k = Some (c, n, B) -> nth_error Bs' k = Some (c, n, B') ->
       ind_con D c = Some gs -> exp_scoped (List.length (elim_bctx p D gs A Us) + m) B') ->
    all_brs (fun k B => exp_scoped (k + m) B) Bs'.
Proof.
  intros * Hn Hm Hk HB; apply all_brs_Forall, List.Forall_forall; intros [[c n] B'] Hin'; cbn.
  destruct (List.In_nth_error _ _ Hin') as [k Hk'].
  destruct (brs_nth_same _ _ _ _ _ _ (eq_sym Hm) Hk') as [B HkB].
  pose proof (List.nth_error_In _ _ HkB) as Hin.
  destruct (brs_names_con _ _ _ _ _ Hn Hin) as [gs Hgs].
  rewrite (Hk _ _ _ _ Hgs Hin); specialize (HB _ _ _ _ _ _ HkB Hk' Hgs); rewrite length_elim_bctx in HB.
  replace (ind_nn D + length gs + cargs_nrec gs) with (cargs_nrec gs + length gs + ind_nn D) by lia; exact HB.
Qed.

Lemma elim_ihs_scoped : forall nm A Bs gs As m,
    (forall N, exp_scoped m N -> exp_scoped m (a_elim nm A Bs N)) ->
    List.Forall (exp_scoped m) As -> List.Forall (exp_scoped m) (elim_ihs nm A Bs gs As).
Proof.
  induction gs as [| [] gs IH]; intros [| N As] m He HAs; cbn; try constructor; inversion_clear HAs; auto.
Qed.

(** The motive's instance at the non-uniform parameters and the scrutinee. *)
Lemma elim_inst_scoped : forall D A Ps N m,
    ind_nu D <= ind_np D -> List.length Ps = ind_np D ->
    exp_scoped (S (ind_nn D) + m) A -> List.Forall (exp_scoped m) Ps -> exp_scoped m N ->
    exp_scoped m A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ N :: nil)].
Proof.
  intros * Hle Hl HA HPs HN; apply exp_scoped_sb_of_list.
  - rewrite length_app, length_skipn; cbn; unfold ind_nn in *; replace (length Ps - ind_nu D + 1 + m) with (S (ind_np D - ind_nu D + m)) by lia; exact HA.
  - apply List.Forall_app; split; [| constructor; auto ].
    rewrite <- (firstn_skipn (ind_nu D) Ps) in HPs; apply List.Forall_app in HPs as [_ HPs]; exact HPs.
Qed.

Lemma elim_brs_scoped_l : forall p D Us A Bs (Bs' : list (String.string * nat * exp)) m,
    brs_names (ind_cons D) Bs ->
    List.map fst Bs = List.map fst Bs' ->
    (forall c gs n B, ind_con D c = Some gs -> In (c, n, B) Bs -> n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) ->
    (forall k c gs n B B', nth_error Bs k = Some (c, n, B) -> nth_error Bs' k = Some (c, n, B') ->
       ind_con D c = Some gs -> exp_scoped (List.length (elim_bctx p D gs A Us) + m) B) ->
    all_brs (fun k B => exp_scoped (k + m) B) Bs.
Proof.
  intros * Hn Hm Hk HB; eapply elim_brs_scoped; [ eassumption | eassumption |].
  intros * Hgs Hin.
  destruct (List.In_nth_error _ _ Hin) as [k Hk'].
  destruct (brs_nth_same _ _ _ _ _ _ Hm Hk') as [B' HkB'].
  eauto.
Qed.

Lemma decl_closed_nu : forall D, decl_closed D -> ind_nu D <= ind_np D.
Proof. intros D (_ & H & _); exact H. Qed.

Lemma decl_closed_params : forall D, decl_closed D -> tele_ass (ind_params D).
Proof. intros D (H & _); exact H. Qed.

Lemma Forall_skipn' : forall {A} (P : A -> Prop) n l, List.Forall P l -> List.Forall P (List.skipn n l).
Proof. intros * H; rewrite <- (firstn_skipn n l) in H; apply List.Forall_app in H as [_ H]; exact H. Qed.

Lemma Forall_firstn' : forall {A} (P : A -> Prop) n l, List.Forall P l -> List.Forall P (List.firstn n l).
Proof. intros * H; rewrite <- (firstn_skipn n l) in H; apply List.Forall_app in H as [H _]; exact H. Qed.

Lemma decl_closed_intro : forall D,
    tele_ass (ind_params D) -> ind_nu D <= ind_np D -> ctx_scoped 0 (ind_params D) ->
    exp_scoped (List.length (ind_uparams D)) (ind_sort D) ->
    (forall c gs gs1 A gs2, In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_arg A :: gs2 ->
       exp_scoped (List.length (cargs_strat gs1 ++ ind_params D)) A) ->
    (forall c gs gs1 Ps gs2, In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec Ps :: gs2 ->
       List.length Ps = ind_nn D) ->
    (forall c gs gs1 Ps gs2 k P T, In (c, gs) (ind_cons D) -> gs = gs1 ++ ca_rec Ps :: gs2 ->
       nth_error Ps k = Some P ->
       nth_error (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length (cargs_strat gs1) + ind_nn D))) Ps) k
         = Some T ->
       exp_scoped (List.length (cargs_strat gs1 ++ ind_params D)) P) ->
    decl_closed D.
Proof.
  intros D Hass Hle HΔ HS HA Hl HPs; repeat split; try assumption.
  - rewrite length_ind_uparams in HS by assumption; exact HS.
  - intros * Hin Heq; specialize (HA _ _ _ _ _ Hin Heq); rewrite length_app in HA; exact HA.
  - intros * Hin Heq; eapply (nth_typed_scoped _ (tele_insts (ind_nparams D) (sb_of_wk (wk_shiftn (List.length (cargs_strat gs1) + ind_nn D))) Ps)).
    + rewrite length_tele_insts; [ rewrite length_nparams, (Hl _ _ _ _ _ Hin Heq); lia |].
      apply Forall_firstn'; exact Hass.
    + intros k P T Hk HT; specialize (HPs _ _ _ _ _ _ _ _ Hin Heq Hk HT); rewrite length_app in HPs; exact HPs.
Qed.

(** ** Closed Entries

    What resolution hands back is closed: a definition's type and body, a body
    module's full telescope, and an alias. *)

Definition entry_closed (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B => exp_scoped 0 A /\ opt_scoped 0 B
  | ge_mod _ _ => True
  | ge_ind _ D => decl_closed D
  end.

Definition modres_closed (r : modres) : Prop :=
  match r with
  | mr_body T => ctx_scoped 0 T
  | mr_alias U _ => gunit_scoped 0 U
  end.

(** Every definition and every module a module resolves to is closed, the
    module's own telescope being [T]. *)
Definition mod_closed (T : ctx) (Φ : gmod) : Prop :=
  (forall ip E, gm_resolve Φ ip = Some E -> entry_closed E) /\
  (forall x ip r, gm_submodule T Φ x ip = Some r -> modres_closed r).

Definition unit_closed (T : ctx) (Φ : gmod) : Prop := ctx_scoped 0 T /\ mod_closed T Φ.

Definition units_closed (Θ : gdeps) : Prop :=
  forall fp U, gds_lookup Θ fp = Some U -> unit_closed (gu_params U) (gu_mod U).

Fixpoint stack_closed (Ξ : gstack) : Prop :=
  match Ξ with
  | nil => True
  | (_, U) :: Ξ' => stack_closed Ξ' /\ unit_closed (gu_params U ++ gs_tele Ξ') (gu_mod U)
  end.

Definition gctx_closed (Θ : gdeps) (Ξ : gstack) : Prop :=
  units_closed Θ /\ stack_closed Ξ.

Lemma stack_closed_in : forall Ξ mp U,
    stack_closed Ξ -> List.In (mp, U) Ξ -> exists T, unit_closed T (gu_mod U).
Proof.
  induction Ξ as [| [mq V] Ξ IH]; intros * HΞ Hin; cbn in *; [ contradiction |].
  destruct HΞ as [HΞ HV]; destruct Hin as [[= <- <-] | Hin]; eauto.
Qed.

Lemma stack_closed_find : forall Ξ p U ip T,
    stack_closed Ξ -> gs_find_tele Ξ p = Some (U, ip, T) -> unit_closed (gu_params U ++ T) (gu_mod U).
Proof.
  induction Ξ as [| [mq V] Ξ IH]; intros * HΞ Hf; cbn in *; [ discriminate |].
  destruct HΞ as [HΞ HV].
  destruct (qname_strip mq p); [ injection Hf as <- <- <-; exact HV | eauto ].
Qed.

Lemma gctx_closed_resolve : forall Θ Ξ p b pv A B,
    gctx_closed Θ Ξ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    exp_scoped 0 A /\ opt_scoped 0 B.
Proof.
  intros * [HΘ HΞ] Hr.
  destruct (gc_resolve_inv _ _ _ _ Hr) as [(mp & U & ip & Hin & Hm) | (fp & U & Hl & Hm)].
  - destruct (stack_closed_in _ _ _ HΞ Hin) as (T & _ & HU & _).
    exact (HU _ _ Hm).
  - destruct (HΘ _ _ Hl) as (_ & HU & _); exact (HU _ _ Hm).
Qed.

Lemma gctx_closed_ind : forall Θ Ξ p D,
    gctx_closed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> decl_closed D.
Proof.
  intros * [HΘ HΞ] Hl; destruct (ind_lookup_resolve _ _ _ _ Hl) as [pv Hr].
  destruct (gc_resolve_inv _ _ _ _ Hr) as [(mp & U & ip & Hin & Hm) | (fp & U & Hl' & Hm)].
  - destruct (stack_closed_in _ _ _ HΞ Hin) as (T & _ & HU & _).
    exact (HU _ _ Hm).
  - destruct (HΘ _ _ Hl') as (_ & HU & _); exact (HU _ _ Hm).
Qed.

Lemma gctx_closed_module : forall Θ Ξ p r,
    gctx_closed Θ Ξ ->
    gc_module Θ Ξ p = Some r ->
    modres_closed r.
Proof.
  intros * [HΘ HΞ] Hr; unfold gc_module in Hr.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T] |] eqn:Hf; [ discriminate | |].
  - destruct (stack_closed_find _ _ _ _ _ HΞ Hf) as (_ & _ & HU); exact (HU _ _ _ Hr).
  - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
    destruct (HΘ _ _ Hl) as (HT & _ & HU).
    destruct (q_chain p) as [| x ip]; cbn in Hr; [ injection Hr as <-; exact HT | exact (HU _ _ _ Hr) ].
Qed.

Lemma mod_closed_nil : forall T, mod_closed T ⋄.
Proof. split; intros; discriminate. Qed.

(** What an entry adds is closed if the entry is. *)
Definition entry_ok (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ _ _ | ge_ind _ _ => entry_closed E
  | ge_mod _ (gu_mk Δ (md_body Φ)) => unit_closed (Δ ++ T) Φ
  | ge_mod _ U => gunit_scoped 0 U
  end.

Lemma mod_closed_ext : forall T Φ x E, mod_closed T Φ -> entry_ok T E -> mod_closed T (Φ ⊳ x ↦ E).
Proof.
  intros * [HΦ HΦm] HE; split.
  - intros ip E0 Hr; cbn in Hr.
    destruct ip as [| y ip']; [ discriminate |].
    destruct (String.eqb y x); [| eapply HΦ; eassumption ].
    destruct ip' as [| z ip''], E as [b pv A B | pm [Δ' [Φ' | E']] | pv D]; try discriminate; cbn in HE.
    + injection Hr as <-; exact HE.
    + injection Hr as <-; exact HE.
    + destruct HE as (_ & HE & _); eapply HE; eassumption.
  - intros y ip r Hr; cbn in Hr.
    destruct (String.eqb y x); [| eapply HΦm; eassumption ].
    destruct E as [b pv A B | pm [Δ' [Φ' | E']] | pv D]; try discriminate; cbn in HE.
    + destruct ip as [| z ip']; [ injection Hr as <-; apply HE |].
      destruct HE as (_ & _ & HE); eapply HE; eassumption.
    + injection Hr as <-; exact HE.
Qed.

(** A chain from a unit has no variable. *)
Lemma mod_qname_scoped : forall H p n, mod_qname H = Some p -> modexp_scoped n H.
Proof.
  induction H; intros * Hp; cbn in *; try discriminate; auto.
  destruct (mod_qname H) eqn:E; [ eauto | discriminate ].
Qed.

(** ** Every Judgment is Well Scoped *)

#[local] Arguments gctx_closed : simpl never.
#[local] Arguments mod_closed : simpl never.
#[local] Arguments unit_closed : simpl never.

Definition ctx_ok (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : Prop :=
  ctx_scoped 0 Γ /\ gctx_closed Θ Ξ.

Lemma ctx_scoped_app_iff : forall Ψ Γ, ctx_scoped 0 (Ψ ++ Γ) <-> ctx_scoped (length Γ) Ψ /\ ctx_scoped 0 Γ.
Proof. intros; rewrite ctx_scoped_app, Nat.add_0_r; reflexivity. Qed.

(** The cases of inductive types: the motive is under [S (ind_nn D)]
    binders, a branch under as many as its context has, and the lists of
    parameters and arguments are typed one by one. *)
Ltac ind_motive_scoped :=
  subst; rewrite ?length_elim_mctx, ?length_tele_sub, ?length_nparams in *; assumption.

Ltac ind_brs_scoped :=
  first
    [ eapply elim_brs_scoped; [ eassumption | eassumption |];
      intros; rewrite <- length_app;
      match goal with IH : forall c gs n B, _ -> _ -> _ |- _ =>
        edestruct IH as (_ & ? & _); [ eassumption | eassumption | eassumption ] end
    | eapply elim_brs_scoped'; [ eassumption | eassumption | eassumption |];
      intros; rewrite <- length_app;
      match goal with IH : forall k c gs n B B', _ -> _ -> _ -> _ |- _ =>
        edestruct IH as (_ & _ & ? & _); [ eassumption | eassumption | eassumption | eassumption ] end
    | eapply elim_brs_scoped_l; [ eassumption | eassumption | eassumption |];
      intros; rewrite <- length_app;
      match goal with IH : forall k c gs n B B', _ -> _ -> _ -> _ |- _ =>
        edestruct IH as (_ & ? & _); [ eassumption | eassumption | eassumption | eassumption ] end ].

Ltac ind_list_scoped :=
  repeat first
    [ apply List.Forall_nil
    | apply List.Forall_app; split
    | apply List.Forall_cons; [ first [ assumption | apply exp_scoped_apps; split; [ exact I | ind_list_scoped ] ] |]
    | apply Forall_skipn'
    | apply Forall_firstn'
    | match goal with H : exp_scoped _ (apps_exp _ ?L) |- List.Forall _ ?L =>
        apply exp_scoped_apps in H as [_ H]; exact H end
    | match goal with IH : forall k P T, nth_error ?L k = Some P -> _ -> _ /\ exp_scoped _ P /\ _
                       |- List.Forall _ ?L =>
        eapply nth_typed_scoped;
          [| let Hk := fresh "Hk" in let HT := fresh "HT" in
             intros ? ? ? Hk HT; edestruct IH as (_ & ? & _); [ exact Hk | exact HT | eassumption ] ];
          first [ apply length_tele_insts_params; [ eapply decl_closed_params; eassumption | assumption ]
                | apply length_tele_insts_cargs; assumption ]
      end
    | apply elim_ihs_scoped; [ intros ? ?; cbn; split; [ ind_motive_scoped | split; [ ind_brs_scoped | assumption ] ] |] ].

Ltac ind_scoped :=
  first
    [ eapply exp_scoped_mono; [| eapply decl_closed_ind_ty; eassumption ]; lia
    | eapply exp_scoped_mono; [| eapply decl_closed_con_ty; [ eassumption | apply cons_lookup_in; eassumption ] ]; lia
    | ind_motive_scoped
    | ind_brs_scoped
    | apply exp_scoped_apps; split; [ exact I | ind_list_scoped ]
    | eapply elim_inst_scoped;
        [ eapply decl_closed_nu; eassumption | assumption | ind_motive_scoped | ind_list_scoped
        | first [ assumption | apply exp_scoped_apps; split; [ exact I | ind_list_scoped ] ] ]
    | apply exp_scoped_sb_of_list; [| ind_list_scoped ];
      match goal with
      | IH : forall c gs n B, _ -> _ -> _, Hl : brs_lookup _ _ = Some (_, _) |- _ =>
          let HB := fresh "HB" in
          edestruct IH as (_ & HB & _); [ eassumption | apply brs_lookup_in; exact Hl |];
          rewrite length_app, length_elim_bctx in HB; eapply exp_scoped_mono; [| exact HB ];
          rewrite !length_app, length_skipn, length_elim_ihs by assumption;
          unfold ind_nn in *; lia
      end ].

Theorem wf_scoped :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ctx_ok Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ) M /\ exp_scoped (length Γ) A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ) M /\ exp_scoped (length Γ) M' /\
      exp_scoped (length Γ) A) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ) A /\ exp_scoped (length Γ) A') /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
      ctx_ok Θ Ξ Γ /\ ctx_scoped (length Γ) Ψ /\ ctx_scoped (length Γ) Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
      ctx_ok Θ Ξ Γ /\ gunit_scoped (length Γ) U /\ gunit_scoped (length Γ) U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
      ctx_ok Θ Ξ Γ /\ modexp_scoped (length Γ) H /\ modexp_scoped (length Γ) H') /\
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢e E -> entry_ok (gs_tele Ξ) E) /\
  (forall Θ Ξ mp Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ Δ ⊢m Φ -> unit_closed (Δ ++ gs_tele Ξ) Φ) /\
  (forall Θ Ξ, ⊢g Θ ⍮ Ξ -> gctx_closed Θ Ξ).
Proof.
  apply wf_mut_ind_all; intros;
    repeat match goal with H : let_ann _ _ |- _ => destruct H as [-> | ->] end;
    unfold ctx_ok in *; cbn in *; destruct_all;
    rewrite ?length_app, ?ctx_scoped_app_iff in *; destruct_all.
  all: repeat match goal with |- _ /\ _ => split end; try assumption;
    eauto using exp_scoped_sub1, exp_scoped_sub2, exp_scoped_sub_succ, exp_scoped_shift, mod_closed_nil, exp_scoped_sub1_mod, mod_qname_scoped.
  all: try match goal with
    | |- exp_scoped (length ?Γ + 0) _ => rewrite Nat.add_0_r; assumption
    | H : ?Γ ∋ # ?x : ?A |- ?x < _ => apply ctx_lookup_length in H; assumption
    | H : ?Γ ∋ # ?x ⇒ₘ ?U |- ?x < _ => apply ctx_lookup_mod_length in H; assumption
    | H : ?Γ ∋ # ?x ≔ ?M : ?A, HΓ : ctx_scoped 0 ?Γ |- exp_scoped _ ?M =>
        pose proof (ctx_scoped_lookup_def _ _ _ _ _ HΓ H) as Hs; rewrite Nat.add_0_r in Hs; exact Hs
    | H : ?Γ ∋ # ?x ≔ ?M : ?A |- ?x < _ =>
        apply ctx_lookup_def_lookup, ctx_lookup_length in H; assumption
    | H : ?Γ ∋ # ?x ≔ ?M : ?A, HΓ : ctx_scoped 0 ?Γ |- exp_scoped _ ?A =>
        apply ctx_lookup_def_lookup in H;
        pose proof (ctx_scoped_lookup _ _ _ _ HΓ H) as Hs; rewrite Nat.add_0_r in Hs; exact Hs
    | H : ?Γ ∋ # ?x : ?A, HΓ : ctx_scoped 0 ?Γ |- exp_scoped _ ?A =>
        pose proof (ctx_scoped_lookup _ _ _ _ HΓ H) as Hs; rewrite Nat.add_0_r in Hs; exact Hs
    | H : gc_resolve _ _ _ = Some (ge_def _ _ _ _), Hc : gctx_closed _ _ |- exp_scoped _ _ =>
        destruct (gctx_closed_resolve _ _ _ _ _ _ _ Hc H) as [HA HB]; cbn in HB;
        eapply exp_scoped_mono; [| first [ exact HA | exact HB ] ]; lia
    end.
  all: try lia.
  all: try (rewrite Nat.add_0_r; assumption).
  all: try (rewrite ?Nat.add_0_r in *; eapply exp_scoped_sub2; [ eassumption | eassumption | cbn; repeat split; assumption ]).
  all: try (apply ctx_pi_scoped; [ assumption | rewrite Nat.add_0_r; assumption ]).
  all: try (apply ctx_fn_scoped; [ assumption | rewrite Nat.add_0_r; assumption ]).
  all: try (rewrite gunit_scoped_mk, ?ctx_scoped_app_iff, ?length_app; repeat split; assumption).
  all: try match goal with Hl : ind_lookup _ _ _ = Some ?D, Hc : gctx_closed _ _ |- _ =>
         pose proof (gctx_closed_ind _ _ _ _ Hc Hl) end.
  all: try solve [ ind_scoped ].
  all: try solve [ eapply decl_closed_intro; try eassumption; intros;
                   match goal with IH : forall c gs gs1 x gs2, _ -> _ -> _ |- _ =>
                     edestruct IH as (_ & ? & _); eassumption end ].
  - (* a body unit, left *)
    rewrite gunit_scoped_mk; rewrite ctx_scoped_app in *; destruct_all; split; [ assumption |].
    apply (gmod_scoped_of_body_ctx _ _ _ H4); assumption.
  - (* a body unit, right *)
    rewrite gunit_scoped_mk; rewrite ctx_scoped_app in *; destruct_all; split; [ assumption |].
    rewrite <- H3; apply (gmod_scoped_of_body_ctx _ _ _ H4); rewrite H3; assumption.
  - (* a filed alias *)
    rewrite gunit_scoped_mk; cbn; rewrite ctx_scoped_app_iff, length_app, Nat.add_0_r; repeat split; assumption.
  - split; [ apply ctx_scoped_app_iff; split; assumption | apply mod_closed_nil ].
  - match goal with H : unit_closed _ Φ |- _ => destruct H end.
    split; [ assumption | apply mod_closed_ext; assumption ].
  - split; [ intros ? ? Hl; discriminate | exact I ].
  - (* a filed unit: its closed frame, or the units before it *)
    match goal with
    | H : gctx_closed _ _ |- gctx_closed ((?f, _) :: _) nil =>
        destruct H as [HΘ [_ HU]]; split; [| exact I ];
        intros fq0 V0 Hl; cbn in Hl; destruct (path_beq fq0 f);
        [ injection Hl as <-; rewrite List.app_nil_r in HU; exact HU | exact (HΘ _ _ Hl) ]
    end.
  - (* a frame *)
    match goal with H : gctx_closed _ _ |- _ => destruct H as [HΘ HΞ] end.
    split; [ assumption | cbn; split; assumption ].
Qed.

(** ** Consequences *)

Corollary wf_gctx_closed : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> gctx_closed Θ Ξ.
Proof. intros * HΓ; destruct wf_scoped as [Hc _]; apply (Hc _ _ _ HΓ). Qed.

(** In a well-formed context, what a global resolves to has no free
    λ-variable. *)
Corollary wf_gc_resolve_closed : forall Θ Ξ Γ p b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    exp_scoped 0 A /\ opt_scoped 0 B.
Proof.
  intros * HΓ Hr; eapply gctx_closed_resolve; [ eapply wf_gctx_closed | ]; eassumption.
Qed.

Corollary wf_gc_resolve_type_closed : forall Θ Ξ Γ p b pv A B,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    exp_scoped 0 A.
Proof. intros; eapply wf_gc_resolve_closed; eassumption. Qed.

Corollary wf_gc_resolve_body_closed : forall Θ Ξ Γ p b pv A M,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A (Some M)) ->
    exp_scoped 0 M.
Proof. intros * HΓ Hr; apply (wf_gc_resolve_closed _ _ _ _ _ _ _ _ HΓ Hr). Qed.
