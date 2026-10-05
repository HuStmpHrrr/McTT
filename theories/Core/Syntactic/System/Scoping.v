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
  | a_typ _ | a_nat | a_zero | a_True | a_true | a_False => True
  | a_succ M => exp_scoped n M
  | a_natrec A MZ MS M =>
      exp_scoped (S n) A /\ exp_scoped n MZ /\ exp_scoped (S (S n)) MS /\ exp_scoped n M
  | a_exfalso A M => exp_scoped (S n) A /\ exp_scoped n M
  | a_pi A B | a_fn A B => exp_scoped n A /\ exp_scoped (S n) B
  | a_app M N => exp_scoped n M /\ exp_scoped n N
  | a_var x => x < n
  | a_let b B => bnd_scoped n b /\ exp_scoped (S n) B
  | a_mem H _ => modexp_scoped n H
  | a_const _ => True
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
  | gm_ext Φ _ E => gmod_scoped n Φ /\ gentry_scoped (S n) E
  | gm_open Φ H _ _ => gmod_scoped n Φ /\ modexp_scoped (S n) H
  end
with gentry_scoped (n : nat) (E : gentry) : Prop :=
  match E with
  | ge_def _ A oM => exp_scoped n A /\ match oM with Some M => exp_scoped n M | None => True end
  | ge_mod _ U => gunit_scoped n U
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
  rewrite ?gunit_wk_mk, ?gunit_sub_mk, ?length_tele_wk, ?length_tele_sub in *;
  repeat match goal with
         | H : gunit_scoped _ (gu_mk _ _) |- _ => rewrite gunit_scoped_mk in H
         | |- gunit_scoped _ (gu_mk _ _) => rewrite gunit_scoped_mk
         end;
  destruct_all.

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
Proof. intros n []; cbn; auto; intros; repeat constructor. Qed.

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
Qed.

Lemma exp_scoped_wk_id : forall M n φ,
    exp_scoped n M -> (forall x, x < n -> φ x = x) -> M[φ]ʷ = M.
Proof. exact (proj1 syn_scoped_wk_id). Qed.

Lemma exp_scoped_sub_id : forall M n σ,
    exp_scoped n M -> (forall x, x < n -> σ x = se_var x) -> M[σ] = M.
Proof. exact (proj1 syn_scoped_sub_id). Qed.

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

(** ** Closed Global Contexts

    Every unit filed is closed, and so is every constant's type and body, if
    it has one. *)

Definition oexp_scoped (n : nat) (oM : option exp) : Prop :=
  match oM with Some M => exp_scoped n M | None => True end.

Definition gctx_closed (Θ : gctx) : Prop :=
  (forall fp U, gc_unit Θ fp = Some U -> gunit_scoped 0 U) /\
  (forall c A oM b, gc_const Θ c = Some (A, oM, b) -> exp_scoped 0 A /\ oexp_scoped 0 oM).

Lemma gctx_closed_nil : gctx_closed nil.
Proof. split; intros; discriminate. Qed.

Lemma gctx_closed_unit : forall Θ fp U, gctx_closed Θ -> gunit_scoped 0 U -> gctx_closed (gd_unit fp U :: Θ).
Proof.
  intros * [HU HC] H; split; cbn; [| exact HC ].
  intros fq V Hl; destruct (path_beq fq fp); [ injection Hl as <-; exact H | eauto ].
Qed.

Lemma gctx_closed_const : forall Θ c A oM b, gctx_closed Θ -> exp_scoped 0 A -> oexp_scoped 0 oM ->
    gctx_closed (gd_const c A oM b :: Θ).
Proof.
  intros * [HU HC] HA HM; split; cbn; [ exact HU |].
  intros c' A' M' b' Hl; destruct (qname_beq c' c); [ injection Hl as <- <- <-; auto | eauto ].
Qed.

Lemma gctx_closed_unit_lookup : forall Θ fp U, gctx_closed Θ -> gc_unit Θ fp = Some U -> gunit_scoped 0 U.
Proof. intros * [H _]; apply H. Qed.

Lemma gctx_closed_const_lookup : forall Θ c A oM b, gctx_closed Θ -> gc_const Θ c = Some (A, oM, b) ->
    exp_scoped 0 A /\ oexp_scoped 0 oM.
Proof. intros * [_ H]; apply H. Qed.

(** ** Every Judgment is Well Scoped *)

#[local] Arguments gctx_closed : simpl never.

Definition ctx_ok (Θ : gctx) (Γ : ctx) : Prop :=
  ctx_scoped 0 Γ /\ gctx_closed Θ.

Lemma ctx_scoped_app_iff : forall Ψ Γ, ctx_scoped 0 (Ψ ++ Γ) <-> ctx_scoped (length Γ) Ψ /\ ctx_scoped 0 Γ.
Proof. intros; rewrite ctx_scoped_app, Nat.add_0_r; reflexivity. Qed.

Lemma gunit_scoped_body_ext : forall n Δ Φ x E,
    gunit_scoped n (gu_body Δ (Φ ⊳ x ↦ E)) <-> gunit_scoped n (gu_body Δ Φ) /\ gentry_scoped (S (length Δ + n)) E.
Proof. intros; rewrite !gunit_scoped_mk; cbn; tauto. Qed.

Theorem wf_scoped :
  (forall Θ Γ, ⊢ Θ ⍮ Γ -> ctx_ok Θ Γ) /\
  (forall Θ Γ A M, Θ ⍮ Γ ⊢ M : A ->
      ctx_ok Θ Γ /\ exp_scoped (length Γ) M /\ exp_scoped (length Γ) A) /\
  (forall Θ Γ A M M', Θ ⍮ Γ ⊢ M ≈ M' : A ->
      ctx_ok Θ Γ /\ exp_scoped (length Γ) M /\ exp_scoped (length Γ) M' /\
      exp_scoped (length Γ) A) /\
  (forall Θ Γ A A', Θ ⍮ Γ ⊢ A ⊆ A' ->
      ctx_ok Θ Γ /\ exp_scoped (length Γ) A /\ exp_scoped (length Γ) A') /\
  (forall Θ Γ Ψ Ψ', Θ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
      ctx_ok Θ Γ /\ ctx_scoped (length Γ) Ψ /\ ctx_scoped (length Γ) Ψ') /\
  (forall Θ Γ U U', Θ ⍮ Γ ⊢ᵘ U ≈ U' ->
      ctx_ok Θ Γ /\ gunit_scoped (length Γ) U /\ gunit_scoped (length Γ) U') /\
  (forall Θ Γ H H', Θ ⍮ Γ ⊢ᵐ H ≈ H' ->
      ctx_ok Θ Γ /\ modexp_scoped (length Γ) H /\ modexp_scoped (length Γ) H') /\
  (forall Θ, ⊢g Θ -> gctx_closed Θ).
Proof.
  apply wf_mut_ind_all; intros;
    repeat match goal with H : let_ann _ _ |- _ => destruct H as [-> | ->] end;
    unfold ctx_ok in *; cbn in *; destruct_all;
    rewrite ?length_app, ?ctx_scoped_app_iff in *; destruct_all.
  all: try (rewrite gunit_scoped_body_ext; cbn in *; rewrite ?length_app in *;
            repeat split; try assumption;
            match goal with |- gentry_scoped _ _ => cbn; rewrite ?Nat.add_0_r; repeat split; assumption end).
  all: repeat match goal with |- _ /\ _ => split end; try assumption;
    eauto using exp_scoped_sub1, exp_scoped_sub2, exp_scoped_sub_succ, exp_scoped_shift, exp_scoped_sub1_mod,
      gctx_closed_nil, gctx_closed_unit, gctx_closed_const.
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
    | H : gc_const _ _ = Some _, Hc : gctx_closed _ |- exp_scoped _ _ =>
        destruct (gctx_closed_const_lookup _ _ _ _ _ Hc H) as [HA HB];
        eapply exp_scoped_mono; [| first [ exact HA | exact HB ] ]; lia
    end.
  all: try lia.
  all: try (rewrite Nat.add_0_r; assumption).
  all: try (rewrite ?Nat.add_0_r in *; eapply exp_scoped_sub2; [ eassumption | eassumption | cbn; repeat split; assumption ]).
  all: try (rewrite gunit_scoped_mk, ?ctx_scoped_app_iff, ?length_app; repeat split; assumption).
  (** The units: their parameters, then each entry under its self slot. *)
  all: rewrite ?gunit_scoped_body_ext; rewrite !gunit_scoped_mk in *; cbn in *; destruct_all;
    repeat split; try assumption; rewrite ?Nat.add_0_r in *; try assumption.
Qed.

(** ** Consequences *)

Corollary wf_gctx_closed : forall Θ Γ, ⊢ Θ ⍮ Γ -> gctx_closed Θ.
Proof. intros * HΓ; destruct wf_scoped as [Hc _]; apply (Hc _ _ HΓ). Qed.

(** In a well-formed context, a constant has no free variable, nor has a
    unit. *)
Corollary wf_gc_const_closed : forall Θ Γ c A oM b,
    ⊢ Θ ⍮ Γ ->
    gc_const Θ c = Some (A, oM, b) ->
    exp_scoped 0 A /\ oexp_scoped 0 oM.
Proof. intros * HΓ Hr; eapply gctx_closed_const_lookup; [ eapply wf_gctx_closed | ]; eassumption. Qed.

Corollary wf_gc_unit_closed : forall Θ Γ fp U,
    ⊢ Θ ⍮ Γ ->
    gc_unit Θ fp = Some U ->
    gunit_scoped 0 U.
Proof. intros * HΓ Hr; eapply gctx_closed_unit_lookup; [ eapply wf_gctx_closed | ]; eassumption. Qed.
