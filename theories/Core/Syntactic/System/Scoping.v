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
  | gm_check Φ c => gmod_scoped n Φ /\ bcheck_scoped (gm_binders Φ + n) c
  end
with bcheck_scoped (n : nat) (c : bcheck) : Prop :=
  match c with
  | bc_import E _ => modexp_scoped n E
  end
with gentry_scoped (n : nat) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B => exp_scoped n A /\ match B with Some M => exp_scoped n M | None => True end
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

Lemma syn_scoped_mono :
  (forall M n m, n <= m -> exp_scoped n M -> exp_scoped m M) /\
  (forall H n m, n <= m -> modexp_scoped n H -> modexp_scoped m H) /\
  (forall b n m, n <= m -> bnd_scoped n b -> bnd_scoped m b) /\
  (forall U n m, n <= m -> gunit_scoped n U -> gunit_scoped m U) /\
  (forall D n m, n <= m -> moddef_scoped n D -> moddef_scoped m D) /\
  (forall Φ n m, n <= m -> gmod_scoped n Φ -> gmod_scoped m Φ) /\
  (forall c n m, n <= m -> bcheck_scoped n c -> bcheck_scoped m c) /\
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
  (forall c n m φ, bcheck_scoped n c -> (forall x, x < n -> φ x < m) -> bcheck_scoped m (bcheck_wk c φ)) /\
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
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_wk)))))))). Qed.

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
  (forall c n m σ, bcheck_scoped n c -> (forall x, x < n -> sentry_scoped m (σ x)) -> bcheck_scoped m (bcheck_sub c σ)) /\
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
  (forall c n φ, bcheck_scoped n c -> (forall x, x < n -> φ x = x) -> bcheck_wk c φ = c) /\
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
  (forall c n σ, bcheck_scoped n c -> (forall x, x < n -> σ x = se_var x) -> bcheck_sub c σ = c) /\
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
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_wk_id))))))) _ _ _ He Hψ).
Qed.

Corollary tele_closed_sub : forall Δ σ, ctx_scoped 0 Δ -> tele_sub Δ σ = Δ.
Proof.
  intros; eapply tele_sub_id_gen; [| eassumption | lia ].
  apply List.Forall_forall; intros e _ n τ He Hτ.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_sub_id))))))) _ _ _ He Hτ).
Qed.

Lemma tele_wk_scoped : forall Δ n m φ,
    ctx_scoped n Δ -> (forall x, x < n -> φ x < m) -> ctx_scoped m (tele_wk Δ φ).
Proof.
  intros; eapply tele_wk_scoped_gen; [| eassumption | assumption ].
  apply List.Forall_forall; intros e _ k l ψ He Hψ.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_wk))))))) _ _ _ _ He Hψ).
Qed.

Lemma tele_sub_scoped : forall Δ n m σ,
    ctx_scoped n Δ -> (forall x, x < n -> sentry_scoped m (σ x)) -> ctx_scoped m (tele_sub Δ σ).
Proof.
  intros; eapply tele_sub_scoped_gen; [| eassumption | assumption ].
  apply List.Forall_forall; intros e _ k l τ He Hτ.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_sub))))))) _ _ _ _ He Hτ).
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
Proof. induction Φ as [| Φ IH x [? ? ? [] | ] | Φ IH c]; cbn; auto. Qed.

(** A body is scoped when the context it binds is, and its check entries are. *)
Lemma gmod_scoped_of_body_ctx : forall Φ n,
    ctx_scoped n (body_ctx Φ) ->
    (forall Φ0 c, List.In (Φ0, c) (gm_checks Φ) -> bcheck_scoped (gm_binders Φ0 + n) c) ->
    gmod_scoped n Φ.
Proof.
  induction Φ as [| Φ IH x [? ? ? [] | ] | Φ IH c]; intros * HΦ Hc; cbn in *; destruct_all;
    repeat split; auto; try (rewrite <- length_body_ctx; assumption).
Qed.

(** ** Closed Entries

    What resolution hands back is closed: a definition's type and body, a body
    module's full telescope, and an alias. *)

Definition entry_closed (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B => exp_scoped 0 A /\ opt_scoped 0 B
  | ge_mod _ _ => True
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
  | ge_def _ _ _ _ => entry_closed E
  | ge_mod _ (gu_mk Δ (md_body Φ)) => unit_closed (Δ ++ T) Φ
  | ge_mod _ U => gunit_scoped 0 U
  end.

Lemma mod_closed_ext : forall T Φ x E, mod_closed T Φ -> entry_ok T E -> mod_closed T (Φ ⊳ x ↦ E).
Proof.
  intros * [HΦ HΦm] HE; split.
  - intros ip E0 Hr; cbn in Hr.
    destruct ip as [| y ip']; [ discriminate |].
    destruct (String.eqb y x); [| eapply HΦ; eassumption ].
    destruct ip' as [| z ip''], E as [b pv A B | pm [Δ' [Φ' | E']]]; try discriminate; cbn in HE.
    + injection Hr as <-; exact HE.
    + destruct HE as (_ & HE & _); eapply HE; eassumption.
  - intros y ip r Hr; cbn in Hr.
    destruct (String.eqb y x); [| eapply HΦm; eassumption ].
    destruct E as [b pv A B | pm [Δ' [Φ' | E']]]; try discriminate; cbn in HE.
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

(** The check entries of a body of some shape are imports. *)
Lemma body_shape_checks : forall Φ Φ',
    body_shape Φ Φ' ->
    (forall Φ0 c, List.In (Φ0, c) (gm_checks Φ) -> exists E ns, c = bc_import E ns) /\
    (forall Φ0 c, List.In (Φ0, c) (gm_checks Φ') -> exists E ns, c = bc_import E ns).
Proof.
  induction Φ as [| Φ IH x E | Φ IH c]; intros [| Φ' x' E' | Φ' c'] Hs; cbn in Hs; try contradiction.
  - split; intros ? ? [].
  - destruct Hs as [Hs _]; exact (IH _ Hs).
  - destruct Hs as [Hs Hc]; destruct (IH _ Hs) as [IH1 IH2].
    destruct c as [E ns], c' as [E' ns']; cbn in Hc.
    split; intros Φ0 c0 [[= <- <-] | Hin]; eauto.
Qed.

(** ** Every Judgment is Well Scoped *)

#[local] Arguments gctx_closed : simpl never.
#[local] Arguments mod_closed : simpl never.
#[local] Arguments unit_closed : simpl never.

Definition ctx_ok (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : Prop :=
  ctx_scoped 0 Γ /\ gctx_closed Θ Ξ.

Lemma ctx_scoped_app_iff : forall Ψ Γ, ctx_scoped 0 (Ψ ++ Γ) <-> ctx_scoped (length Γ) Ψ /\ ctx_scoped 0 Γ.
Proof. intros; rewrite ctx_scoped_app, Nat.add_0_r; reflexivity. Qed.

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
  (forall Θ d, wf_gdep Θ d -> units_closed Θ /\
      forall fp U, List.In (fp, U) d -> unit_closed (gu_params U) (gu_mod U)) /\
  (forall Θ, wf_gdeps Θ -> units_closed Θ) /\
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
  - (* a body unit, left *)
    rewrite gunit_scoped_mk; rewrite ctx_scoped_app in *; destruct_all; split; [ assumption |].
    apply gmod_scoped_of_body_ctx; [ assumption |].
    intros Φ0 c Hin; destruct (proj1 (body_shape_checks _ _ H4) _ _ Hin) as (E & ns & ->); cbn.
    match goal with H : forall _ _ _, List.In _ (gm_checks Φ) -> _ /\ _ |- _ => destruct (H _ _ _ Hin) as (_ & HE & _) end.
    rewrite !length_app, length_body_ctx in HE; exact HE.
  - (* a body unit, right *)
    rewrite gunit_scoped_mk; rewrite ctx_scoped_app in *; destruct_all; split; [ assumption |].
    rewrite <- H3; apply gmod_scoped_of_body_ctx; [ rewrite H3; assumption |].
    intros Φ0 c Hin; destruct (proj2 (body_shape_checks _ _ H4) _ _ Hin) as (E & ns & ->); cbn.
    match goal with H : forall _ _ _, List.In _ (gm_checks Φ') -> _ /\ _ |- _ => destruct (H _ _ _ Hin) as (_ & HE & _) end.
    rewrite !length_app, length_body_ctx, <- H3 in HE; exact HE.
  - (* a filed alias *)
    rewrite gunit_scoped_mk; cbn; rewrite ctx_scoped_app_iff, length_app, Nat.add_0_r; repeat split; assumption.
  - split; [ apply ctx_scoped_app_iff; split; assumption | apply mod_closed_nil ].
  - match goal with H : unit_closed _ Φ |- _ => destruct H end.
    split; [ assumption | apply mod_closed_ext; assumption ].
  - (* a unit filed at the level *)
    intros fq0 V0 [[= <- <-] | Hin]; [ rewrite List.app_nil_r in *; assumption | eauto ].
  - intros fq0 V0 Hl; discriminate.
  - (* a level filed on top: its own units, or the ones below *)
    intros fq0 V0 Hl; unfold gds_lookup in Hl; cbn in Hl.
    apply gd_lookup_app_inv in Hl as [Hl | Hl];
      [ match goal with H : forall _ _, List.In _ _ -> _ |- _ => eapply H, gd_lookup_in, Hl end
      | match goal with H : units_closed _ |- _ => eapply H, Hl end ].
  - split; [ assumption | exact I ].
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
