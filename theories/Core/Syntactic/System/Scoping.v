(** * Scoping

    Every well-formed term is well scoped: its λ-variables are among the local
    binders.  What this buys is closedness of globals: every entry of a
    well-formed global context is stored generalized over its telescope, so its
    type and body have no free λ-variable, and weakening and substitution leave
    them alone.  The rules for globals rely on exactly that instead of premising
    it.

    Scoping is proved for all eleven judgments at once: the term judgments need
    closedness of what resolution hands back, which comes from [⊢ᵍ], which is
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

(** [exp_scoped n M], with its mutual parts for the subterms' sorts. *)
Fixpoint exp_scoped (n : nat) (M : exp) : Prop :=
  match M with
  | a_typ _ | a_level _ | a_llit _ | a_True | a_true | a_False => True
  | a_succl M | a_univ M => exp_scoped n M
  | a_maxl M N => exp_scoped n M /\ exp_scoped n N
  | a_exfalso A M => exp_scoped (S n) A /\ exp_scoped n M
  | a_ind _ _ | a_con _ _ _ | a_nlit _ | a_ntok => True
  | a_elim _ Us _ Bks M =>
      all_list (exp_scoped n) Us /\
      all_blocks (fun nm oZ A Bs => opt_all (exp_scoped (nm - 1 + n)) oZ /\ exp_scoped (nm + n) A /\
                                    all_brs (fun k B => exp_scoped (k + n) B) Bs) Bks /\ exp_scoped n M
  | a_pi A B | a_fn A B => exp_scoped n A /\ exp_scoped (S n) B
  | a_app M N => exp_scoped n M /\ exp_scoped n N
  | a_var x => x < n
  | a_let b B => bnd_scoped n b /\ exp_scoped (S n) B
  | a_mem H _ => modexp_scoped n H
  | a_record _ => True
  | a_tuple T fs => exp_scoped n T /\ all_list (fun f => exp_scoped n (snd f)) fs
  | a_proj _ M => exp_scoped n M
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
  | md_body sm Φ => sm = sm_open /\ gmod_scoped n Φ
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
  | ge_ind _ _ _ D Φ => gmod_scoped (ind_nu D + n) Φ
  | ge_ind_alias _ Δ _ _ _ Ns =>
      (fix tele_closed (Δ : list centry) : Prop :=
         match Δ with
         | nil => True
         | e :: Δ' => centry_scoped (List.length Δ') e /\ tele_closed Δ'
         end) Δ /\
      (fix args_scoped (Ns : list exp) : Prop :=
         match Ns with
         | nil => True
         | N :: Ns' => exp_scoped (List.length Δ) N /\ args_scoped Ns'
         end) Ns
  | ge_record _ _ R Φ => gmod_scoped (S (List.length (record_params R)) + n) Φ
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
  (forall E n m, n <= m -> gentry_scoped n E -> gentry_scoped m E) /\
  (forall e n m, n <= m -> centry_scoped n e -> centry_scoped m e).
Proof.
  syn_mut_ind; scoped_case;
    repeat match goal with
           | B : option exp |- _ => destruct B
           end; cbn in *; destruct_all;
    repeat split; try lia; eauto with arith.
  all: try ups_case ltac:(fun H => eapply H; [| eassumption ]; lia).
  all: try fields_case ltac:(fun H => eapply H; [| eassumption ]; lia).
  1: blocks_case ltac:(fun H => eapply H; [| eassumption ]; lia).
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
  all: try ups_case ltac:(fun H => eapply H; eassumption).
  all: try fields_case ltac:(fun H => eapply H; eassumption).
  all: blocks_case ltac:(fun H => eapply H; [ eassumption | eapply lift; eassumption ]).
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
  all: try ups_case ltac:(fun H => eapply H; eassumption).
  all: try fields_case ltac:(fun H => eapply H; eassumption).
  all: blocks_case ltac:(fun H => eapply H; [ eassumption | eapply lift; eassumption ]).
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
  all: try ups_eq_case ltac:(fun H => eapply H; eassumption).
  all: try fields_eq_case ltac:(fun H => eapply H; eassumption).
  all: blocks_eq_case ltac:(fun H => eapply H; [ eassumption | eapply lift; eassumption ]).
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
  all: try ups_eq_case ltac:(fun H => eapply H; eassumption).
  all: try fields_eq_case ltac:(fun H => eapply H; eassumption).
  all: blocks_eq_case ltac:(fun H => eapply H; [ eassumption | eapply lift; eassumption ]).
Qed.

Lemma exp_scoped_wk_id : forall M n φ,
    exp_scoped n M -> (forall x, x < n -> φ x = x) -> M[φ]ʷ = M.
Proof. exact (proj1 syn_scoped_wk_id). Qed.

Lemma exp_scoped_sub_id : forall M n σ,
    exp_scoped n M -> (forall x, x < n -> σ x = se_var x) -> M[σ] = M.
Proof. exact (proj1 syn_scoped_sub_id). Qed.

Lemma sb_q_agree : forall σ τ n,
    (forall x, x < n -> σ x = τ x) -> forall x, x < S n -> (q σ) x = (q τ) x.
Proof.
  intros * H [|x] ?; rewrite ?sb_q_zero, ?sb_q_succ; [ reflexivity |].
  rewrite H by lia; reflexivity.
Qed.

Lemma sb_qn_agree : forall k σ τ n,
    (forall x, x < n -> σ x = τ x) -> forall x, x < k + n -> (sb_qn k σ) x = (sb_qn k τ) x.
Proof. induction k; intros * H x Hx; cbn; auto; apply sb_q_agree with (n := k + n); [ apply IHk; exact H | lia ]. Qed.

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
  all: try ups_eq_case ltac:(fun H => eapply H; eassumption).
  all: try fields_eq_case ltac:(fun H => eapply H; eassumption).
  all: blocks_eq_case ltac:(fun H => eapply H; [ eassumption | eapply lift; eassumption ]).
Qed.

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

(** Allowing more module variables keeps them allowed. *)
Lemma syn_mvc_mono :
  (forall M n m, n <= m -> exp_mvc n M -> exp_mvc m M) /\
  (forall H n m, n <= m -> modexp_mvc n H -> modexp_mvc m H) /\
  (forall b n m, n <= m -> bnd_mvc n b -> bnd_mvc m b) /\
  (forall U n m, n <= m -> gunit_mvc n U -> gunit_mvc m U) /\
  (forall D n m, n <= m -> moddef_mvc n D -> moddef_mvc m D) /\
  (forall Φ n m, n <= m -> gmod_mvc n Φ -> gmod_mvc m Φ) /\
  (forall E n m, n <= m -> gentry_mvc n E -> gentry_mvc m E) /\
  (forall e n m, n <= m -> centry_mvc n e -> centry_mvc m e).
Proof.
  syn_mut_ind; intros; cbn in *;
    repeat match goal with
           | H : gunit_mvc _ (gu_mk _ _) |- _ => rewrite gunit_mvc_mk in H
           | |- gunit_mvc _ (gu_mk _ _) => rewrite gunit_mvc_mk
           end;
    destruct_all;
    repeat match goal with
           | B : option exp |- _ => destruct B
           end; cbn in *; destruct_all;
    repeat split; try lia; eauto with arith.
  all: try ups_case ltac:(fun H => eapply H; [| eassumption ]; lia).
  all: try fields_case ltac:(fun H => eapply H; [| eassumption ]; lia).
  - blocks_case ltac:(fun H => eapply H; [| eassumption ]; lia).
  - clear - H H1 H2; induction H; cbn in *; destruct_all; [ auto |].
    split; [ eapply H; [| eassumption ]; lia | auto ].
    apply IHForall; assumption.
Qed.

Corollary exp_mvc_mono : forall M n m, n <= m -> exp_mvc n M -> exp_mvc m M.
Proof. exact (proj1 syn_mvc_mono). Qed.

(** A [Π] over assumptions without module variables. *)
Lemma ctx_pi_mvc : forall Δ A n,
    tele_ass Δ -> List.Forall (centry_mvc n) Δ -> exp_mvc (List.length Δ + n) A -> exp_mvc n (ctx_pi Δ A).
Proof.
  induction Δ as [| e Δ IH]; intros * Hass Hm HA; cbn in *; [ exact HA |].
  inversion Hass as [| ? ? [B ->] Hass']; inversion Hm; subst; cbn in *.
  apply IH; [ exact Hass' | assumption |]; cbn; split; [| exact HA ].
  eapply exp_mvc_mono; [| eassumption ]; lia.
Qed.


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
  all: try solve [ eauto 8 using sb_q_agree, sb_q_exp_agree, sb_qn_agree, sb_qn_exp_agree ].
  all: try ups_eq_case ltac:(fun H => eapply H; eassumption).
  all: try fields_eq_case ltac:(fun H => eapply H; eassumption).
  all: blocks_eq_case ltac:(fun H => eapply H; eauto using sb_qn_agree, sb_qn_exp_agree).
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
  all: try ups_case ltac:(fun H => eapply H; eassumption).
  all: try fields_case ltac:(fun H => eapply H; eassumption).
  all: blocks_case ltac:(fun H => eapply H; [ eassumption | eapply wk_qn_bound; eassumption ]).
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

Lemma exp_scoped_sub1_mod : forall A H n,
    exp_scoped (S n) A -> modexp_scoped n H -> exp_scoped n A[Id ,,ₘ H].
Proof. intros; eapply exp_scoped_sub; [ eassumption |]; intros [|x] ?; cbn; auto; lia. Qed.

#[local]
Hint Resolve exp_scoped_sub1 exp_scoped_sub2 exp_scoped_shift exp_scoped_sub1_mod : mctt.

Lemma ctx_lookup_mod_length : forall Γ x U, Γ ∋ #x ≔ₘ U -> x < length Γ.
Proof. induction 1; cbn; lia. Qed.

Lemma length_body_ctx : forall Φ, length (body_ctx Φ) = gm_binders Φ.
Proof. induction Φ as [| Φ IH x [? ? ? [] | | | | ] | Φ IH c]; cbn; rewrite ?length_app, ?repeat_length; auto. Qed.

(** A typed body, with no local open, is scoped when the context it binds
    is. *)
Lemma gmod_scoped_of_body_ctx : forall Φ Φ' n,
    gm_nopens Φ = 0 ->
    body_shape Φ Φ' ->
    (ctx_scoped n (body_ctx Φ) -> gmod_scoped n Φ) /\ (ctx_scoped n (body_ctx Φ') -> gmod_scoped n Φ').
Proof.
  induction Φ as [| Φ IH x E | Φ IH c]; intros [| Φ' x' E' | Φ' c'] n Ho Hs; cbn in Hs, Ho; try contradiction; try discriminate.
  - split; intros; exact I.
  - destruct Hs as (Hs & -> & HE); destruct (IH _ n Ho Hs) as [IH1 IH2].
    destruct E as [? ? ? [] | | | | ], E' as [? ? ? [] | | | | ]; cbn in HE; try contradiction;
      split; intros HΦ; cbn in *; destruct_all; repeat split; auto;
      first [ rewrite <- length_body_ctx; assumption | rewrite <- (length_body_ctx Φ'); assumption ].
Qed.

Lemma gens_append_scoped_prefix : forall gs Φ k n, gmod_scoped n (gens_append Φ k gs) -> gmod_scoped n Φ.
Proof.
  induction gs as [| g gs IH]; intros * H; cbn in H; [ assumption |].
  destruct (ig_entry g); apply IH in H; destruct H; assumption.
Qed.

(** A body is scoped when its expansion is and the target of each of its
    opens is, where it stands. *)
Lemma gmod_scoped_of_xp : forall Θ Ξ Γ Φ Φx n,
    body_xp Θ Ξ Γ Φ Φx -> gmod_scoped n Φx ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> modexp_scoped (length Ψ + n) H) ->
    gmod_scoped n Φ.
Proof.
  induction 1 as [| Γ Φ Φx x E Hx IH | Γ Φ Φx H its R T gs Hx IH _ _ Hg]; intros HΦ Ho; cbn [gmod_scoped] in HΦ |- *; auto.
  - destruct HΦ as [HΦ HE]; split; [ apply IH; assumption |].
    rewrite <- (body_xp_binders _ _ _ _ _ Hx); assumption.
  - rewrite (body_opens_open _ _ _ _ _ _ _ _ _ Hg) in Ho.
    split.
    + apply IH; [ eapply gens_append_scoped_prefix; eassumption |].
      intros k Ψ H' Hk; exact (Ho (S k) _ _ Hk).
    + rewrite <- (body_xp_binders _ _ _ _ _ Hx), <- length_body_ctx; exact (Ho 0 _ _ eq_refl).
Qed.

Lemma body_shape_sym : forall Φ Φ', body_shape Φ Φ' -> body_shape Φ' Φ.
Proof.
  induction Φ as [| Φ IH x E | Φ IH c its]; intros [| Φ' x' E' | Φ' c' its'] Hs; cbn in *; try contradiction; auto;
    destruct_all; subst; repeat split; auto.
  destruct E as [? ? ? [] | | | | ], E' as [? ? ? [] | | | | ]; cbn in *; destruct_all; subst; auto.
Qed.

Lemma body_shape_refl : forall Φ Φ', body_shape Φ Φ' ->
    body_shape Φ Φ /\ body_shape Φ' Φ' /\ gm_names Φ = gm_names Φ'.
Proof.
  induction Φ as [| Φ IH x E | Φ IH c its]; intros [| Φ' x' E' | Φ' c' its'] H; cbn in H |- *; try contradiction.
  - auto.
  - destruct H as (HΦ & <- & HE); destruct (IH _ HΦ) as (H1 & H2 & H3).
    destruct E as [b pv A [M |] | pm U | ? ? ? | ? ? ? ? | ? ? ?], E' as [b' pv' A' [M' |] | pm' U' | ? ? ? | ? ? ? ? | ? ? ?]; cbn in HE |- *; try contradiction;
      intuition congruence.
  - destruct H as (HΦ & <-); destruct (IH _ HΦ) as (H1 & H2 & H3); intuition congruence.
Qed.

(** The names of a body, read through its opens, are its own. *)
Lemma gens_append_names : forall gs Φ k, gm_names (gens_append Φ k gs) = rev (map ig_name gs) ++ gm_names Φ.
Proof.
  induction gs as [| g gs IH]; intros; [ reflexivity |].
  destruct g; cbn [gens_append ig_entry]; rewrite IH; cbn; rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma items_gen_names : forall Θ Ξ g Γ H its gs, items_gen Θ Ξ g Γ H its gs -> map ig_name gs = map iitem_name its.
Proof. induction 1; cbn; f_equal; assumption. Qed.

Lemma body_xp_names : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> gm_names Φx = gm_names Φ.
Proof.
  induction 1; cbn [gm_names]; [ reflexivity | f_equal; assumption |].
  rewrite gens_append_names, (items_gen_names _ _ _ _ _ _ _ H3), IHbody_xp; reflexivity.
Qed.

(** The shape of an expansion is that of the body's own entries. *)
Lemma body_shape_gens_l : forall gs Φ k, body_shape (gens_append Φ k gs) (gens_append Φ k gs) -> body_shape Φ Φ.
Proof.
  induction gs as [| g gs IH]; intros * Hs; [ exact Hs |].
  destruct g; cbn [gens_append ig_entry] in Hs; apply IH in Hs; exact (proj1 Hs).
Qed.

Lemma body_shape_of_xp : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> body_shape Φx Φx -> body_shape Φ Φ.
Proof.
  induction 1; intros Hs; cbn in Hs |- *; [ exact I | destruct Hs as (Hs & _ & HE); repeat split; auto |].
  split; [ apply IHbody_xp; eapply body_shape_gens_l; exact Hs | reflexivity ].
Qed.


(** A body of a unit shape with no open can be filled in, and so can a body
    of its shape. *)
Lemma body_shape_fill : forall Φ Φ', gm_nopens Φ = 0 -> body_shape Φ Φ' -> gm_fill Φ <> None /\ gm_fill Φ' <> None.
Proof.
  induction Φ as [| Φ IH x E | Φ IH c its]; intros [| Φ' x' E' | Φ' c' its'] Ho Hs; cbn in Ho, Hs |- *;
    try contradiction; try discriminate; [ split; discriminate |].
  destruct Hs as (Hs & _ & HE); destruct (IH _ Ho Hs) as [H1 H2].
  destruct E as [? ? ? [] | | | | ], E' as [? ? ? [] | | | | ]; cbn in HE |- *; try contradiction;
    (split; [ destruct (gm_fill Φ) | destruct (gm_fill Φ') ]; cbn; congruence).
Qed.

Lemma body_shape_nopens : forall Φ Φ', body_shape Φ Φ' -> gm_nopens Φ = gm_nopens Φ'.
Proof.
  induction Φ as [| Φ IH x E | Φ IH c its]; intros [| Φ' x' E' | Φ' c' its'] Hs; cbn in *; try contradiction; auto;
    destruct_all; auto.
Qed.

(** The opens of two bodies of the same shape correspond. *)
Lemma body_opens_nth : forall Θ Ξ Γ Γ' Φ Φ' Φx Φx' k p,
    body_xp Θ Ξ Γ Φ Φx -> body_xp Θ Ξ Γ' Φ' Φx' -> body_shape Φ Φ' ->
    nth_error (body_opens Φ Φx) k = Some p -> exists p', nth_error (body_opens Φ' Φx') k = Some p'.
Proof.
  intros * Hx Hx' Hs Hk.
  destruct (nth_error (body_opens Φ' Φx') k) as [p' |] eqn:E; [ eauto |].
  apply nth_error_None in E; rewrite (body_opens_length _ _ _ _ _ Hx'), <- (body_shape_nopens _ _ Hs),
    <- (body_opens_length _ _ _ _ _ Hx) in E.
  assert (k < length (body_opens Φ Φx)) by (apply nth_error_Some; congruence); lia.
Qed.

(** ** Inductive Types

    A declaration is closed: its parameters are a closed telescope of
    assumptions, its sort is in the uniform ones, and the types of the
    arguments of its constructors are in the parameters and the
    non-recursive arguments before them; the components of a shape too,
    each under the domains before it. *)

(** A shape is scoped at [n]: each domain under those before it, and the
    leaf's parameters under all of them. *)
Fixpoint ptyp_scoped (n : nat) (t : ptyp) : Prop :=
  match t with
  | pt_pi B t => exp_scoped n B /\ ptyp_scoped (S n) t
  | pt_self _ Ps => List.Forall (exp_scoped n) Ps
  end.

(** A member of a closed group is closed: its non-uniform parameters are a
    telescope of assumptions over the uniform ones, a view's uniform
    arguments are over the uniform parameters, and the types of the
    arguments of its constructors are in its parameters and the
    non-recursive arguments before them; a shape ends in a member of the
    group, at its number of non-uniform parameters. *)
Record member_closed (D : ind_decl) (M : imember) : Prop := mk_member_closed
  { (** The non-uniform parameters are assumptions *)
    mc_ass : tele_ass (im_nparams M)
    (** They are over the uniform ones *)
  ; mc_nparams : ctx_scoped (ind_nu D) (im_nparams M)
    (** A view's uniform arguments are over the uniform parameters *)
  ; mc_head : forall qc k' Is vm, im_head M = mh_view qc k' Is vm -> List.Forall (exp_scoped (ind_nu D)) Is
    (** A non-recursive argument is over the parameters and the
        non-recursive arguments before it *)
  ; mc_args : forall c gs gs1 A gs2, In (c, gs) (im_cons M) -> gs = gs1 ++ ca_arg A :: gs2 ->
      exp_scoped (List.length (cargs_strat gs1) + im_np D M) A
    (** So is a recursive argument's shape *)
  ; mc_recs : forall c gs gs1 t gs2, In (c, gs) (im_cons M) -> gs = gs1 ++ ca_rec t :: gs2 ->
      ptyp_scoped (List.length (cargs_strat gs1) + im_np D M) t
    (** A shape ends in a member, at its number of non-uniform
        parameters *)
  ; mc_rec_len : forall c gs, In (c, gs) (im_cons M) -> cargs_plen D gs }.

(** A closed group: see the section header. *)
Record decl_closed (D : ind_decl) : Prop := mk_decl_closed
  { (** The uniform parameters are assumptions *)
    dc_ass : tele_ass (ind_uparams D)
    (** They are a closed telescope *)
  ; dc_uparams : ctx_scoped 0 (ind_uparams D)
    (** The sort is over the uniform parameters *)
  ; dc_sort : exp_scoped (ind_nu D) (ind_sort D)
    (** Every member is closed *)
  ; dc_members : forall k M, ind_member D k = Some M -> member_closed D M }.

Lemma ptyp_scoped_mono : forall t n m, n <= m -> ptyp_scoped n t -> ptyp_scoped m t.
Proof.
  induction t as [k Ps | B t IH]; intros * Hle H; cbn in *;
    [ eapply List.Forall_impl; [| exact H ]; intros; eapply exp_scoped_mono; eassumption
    | destruct H; split; [ eapply exp_scoped_mono; eassumption | eapply IH; [| eassumption ]; lia ] ].
Qed.

(** A shape is scoped when its domains and its leaf are, each under the
    domains before. *)
Lemma ptyp_scoped_intro : forall t n,
    (forall Bs1 B Bs2, ptyp_doms t = Bs1 ++ B :: Bs2 -> exp_scoped (List.length Bs1 + n) B) ->
    List.Forall (exp_scoped (ptyp_depth t + n)) (ptyp_ps t) ->
    ptyp_scoped n t.
Proof.
  induction t as [k Ps | B t IH]; intros n HB HP; cbn in *; [ exact HP |].
  split; [ exact (HB nil B (ptyp_doms t) eq_refl) |].
  apply IH.
  - intros Bs1 B' Bs2 E; specialize (HB (B :: Bs1) B' Bs2 ltac:(rewrite E; reflexivity)); cbn in HB.
    replace (List.length Bs1 + S n) with (S (List.length Bs1 + n)) by lia; exact HB.
  - unfold ptyp_depth in *; cbn in HP; replace (List.length (ptyp_doms t) + S n) with (S (List.length (ptyp_doms t) + n)) by lia;
      exact HP.
Qed.

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

(** A record's module telescope is closed when its parameters are: the
    value's type is the type former at the parameters as variables. *)
Lemma record_mod_tele_scoped : forall p R,
    ctx_scoped 0 (record_params R) -> ctx_scoped 0 (record_mod_tele p R).
Proof.
  intros * H; unfold record_mod_tele, record_self; cbn; split; [| exact H ].
  rewrite Nat.add_0_r; apply exp_scoped_apps; split; [ exact I | apply vars_from_scoped; lia ].
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

(** The members as variables: the context of the [Self]s has one entry per
    declared member, and [grp_sb] sends it into the uniform parameters. *)
Lemma ind_ndecl_le : forall D, ind_ndecl D <= List.length (ind_members D).
Proof.
  intros D; unfold ind_ndecl; induction (ind_members D) as [| M ms IH]; cbn; [ lia |].
  destruct (im_is_decl M); cbn; lia.
Qed.

Lemma length_grp_selfs_from : forall D j ms, List.length (grp_selfs_from D j ms) = List.length ms.
Proof. intros D j ms; revert j; induction ms as [| M ms IH]; intros; cbn; [ reflexivity | rewrite length_app, IH; cbn; lia ]. Qed.

Lemma length_grp_sctx : forall D, List.length (grp_sctx D) = ind_ndecl D + ind_nu D.
Proof.
  intros; unfold grp_sctx, grp_selfs, ind_nu; rewrite length_app, length_grp_selfs_from, List.length_firstn.
  pose proof (ind_ndecl_le D); lia.
Qed.

Lemma grp_sb_bound : forall pq D x, x < List.length (grp_sctx D) -> sentry_scoped (ind_nu D) (grp_sb pq D x).
Proof.
  intros * Hx; rewrite length_grp_sctx in Hx; unfold grp_sb.
  apply (sb_of_list_bound _ _ (ind_nu D)).
  - intros; apply sb_id_bound; assumption.
  - apply List.Forall_map, List.Forall_forall; intros j _.
    apply exp_scoped_apps; split; [ exact I | apply vars_from_scoped; lia ].
  - rewrite length_map, List.length_seq; lia.
Qed.

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

(** The parameters of a member of a closed group are closed. *)
Lemma decl_closed_params : forall D k M, decl_closed D -> ind_member D k = Some M -> ctx_scoped 0 (im_params D M).
Proof.
  intros * HD HM; pose proof (dc_members _ HD _ _ HM) as HMc; unfold im_params.
  apply ctx_scoped_app; split; [ rewrite Nat.add_0_r; apply (mc_nparams _ _ HMc) | apply (dc_uparams _ HD) ].
Qed.

Lemma decl_closed_params_ass : forall D k M, decl_closed D -> ind_member D k = Some M -> tele_ass (im_params D M).
Proof.
  intros * HD HM; pose proof (dc_members _ HD _ _ HM) as HMc; unfold im_params.
  apply List.Forall_app; split; [ apply (mc_ass _ _ HMc) | apply (dc_ass _ HD) ].
Qed.

(** A member at uniform and non-uniform parameters as scoped as they are
    is so. *)
Lemma ind_mty_scoped : forall pq D j Us Ns n,
    decl_closed D -> List.length Us = ind_nu D ->
    List.Forall (exp_scoped n) Us -> List.Forall (exp_scoped n) Ns -> exp_scoped n (ind_mty pq D j Us Ns).
Proof.
  intros * HD Hl HUs HNs; unfold ind_mty.
  destruct (ind_member D j) as [Mj |] eqn:Hj; [| exact I ].
  unfold im_ty_at, im_pre; apply exp_scoped_apps; split; [ exact I |].
  apply List.Forall_app; split; [| exact HNs ].
  destruct (im_head Mj) as [pm | qc k' Is vm] eqn:Hh; [ exact HUs |].
  apply List.Forall_map; eapply List.Forall_impl; [| exact (mc_head _ _ (dc_members _ HD _ _ Hj) _ _ _ _ Hh) ].
  intros I HI; apply exp_scoped_sb_of_list; [| exact HUs ].
  eapply exp_scoped_mono; [| exact HI ]; lia.
Qed.

(** The type of a shape is scoped. *)
Lemma ptyp_ty_scoped : forall pq D nn t pat,
    decl_closed D ->
    ptyp_scoped (pat_nargs pat + (nn + ind_nu D)) t ->
    exp_scoped (List.length pat + (nn + ind_nu D)) (ptyp_ty pq D nn pat t).
Proof.
  intros pq D nn t; induction t as [k Ps | B t IH]; intros pat HD Ht; cbn in *.
  - apply ind_mty_scoped; [ exact HD | unfold ind_uvars; apply length_vars_from | |].
    + unfold ind_uvars; apply vars_from_scoped; lia.
    + apply List.Forall_map; eapply List.Forall_impl; [| exact Ht ];
        intros P HP; eapply exp_scoped_wk; [ exact HP |]; intros; apply wk_pat_bound; lia.
  - destruct Ht as [HB Ht]; split.
    + eapply exp_scoped_wk; [ exact HB |]; intros; apply wk_pat_bound; lia.
    + exact (IH (false :: pat) HD Ht).
Qed.

Lemma cargs_ctx_aux_scoped : forall pq D nn gs pat k,
    decl_closed D ->
    pat_nargs pat = k ->
    (forall gs1 A gs2, gs = gs1 ++ ca_arg A :: gs2 ->
       exp_scoped (k + List.length (cargs_strat gs1) + (nn + ind_nu D)) A) ->
    (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
       ptyp_scoped (k + List.length (cargs_strat gs1) + (nn + ind_nu D)) t) ->
    ctx_scoped (List.length pat + (nn + ind_nu D)) (cargs_ctx_aux pq D nn pat gs).
Proof.
  induction gs as [| [A | t] gs IH]; intros * HD Hk HA HPs; cbn; [ exact I | |].
  all: rewrite ctx_scoped_app; cbn; split; [| split; [| exact I ] ].
  - apply (IH (false :: pat) (S k) HD); cbn; [ rewrite Hk; reflexivity | |].
    + intros gs1 A' gs2 ->; specialize (HA (ca_arg A :: gs1) A' gs2 eq_refl); cbn in HA.
      rewrite length_app in HA; cbn in HA; match goal with |- exp_scoped ?n _ => replace n with (k + (length (cargs_strat gs1) + 1) + (nn + ind_nu D)) by lia end; exact HA.
    + intros gs1 Ps gs2 ->; specialize (HPs (ca_arg A :: gs1) Ps gs2 eq_refl); cbn in HPs.
      rewrite length_app in HPs; cbn in HPs; match goal with |- ptyp_scoped ?n _ => replace n with (k + (length (cargs_strat gs1) + 1) + (nn + ind_nu D)) by lia end; exact HPs.
  - specialize (HA nil A gs eq_refl); cbn in HA.
    eapply exp_scoped_wk; [ exact HA |]; intros x Hx; rewrite ?Nat.add_0_r; apply wk_pat_bound; lia.
  - apply (IH (true :: pat) k HD); cbn; [ exact Hk | |].
    + intros gs1 A' gs2 ->; exact (HA (ca_rec t :: gs1) A' gs2 eq_refl).
    + intros gs1 Ps' gs2 ->; exact (HPs (ca_rec t :: gs1) Ps' gs2 eq_refl).
  - specialize (HPs nil t gs eq_refl); cbn in HPs; rewrite Nat.add_0_r in HPs.
    apply ptyp_ty_scoped; [ exact HD | rewrite Hk; exact HPs ].
Qed.

Lemma decl_closed_ind_ty : forall D k M, decl_closed D -> ind_member D k = Some M -> exp_scoped 0 (ind_ty D M).
Proof.
  intros * HD HM; unfold ind_ty; apply ctx_pi_scoped; [ eapply decl_closed_params; eassumption |].
  eapply exp_scoped_wk; [ exact (dc_sort _ HD) |]; intros x Hx; unfold im_params, im_nn, ind_nu in *.
  cbn; rewrite length_app; lia.
Qed.

(** The [Π] over the parameters but the outermost [k] is scoped by them. *)
Lemma decl_closed_ind_ty_at : forall D j M k, decl_closed D -> ind_member D j = Some M -> k <= im_np D M ->
    exp_scoped k (ctx_pi (List.firstn (im_np D M - k) (im_params D M)) (ind_sort D)[wk_shiftn (im_nn M)]ʷ).
Proof.
  intros D j M k HD HM Hk; pose proof (decl_closed_params _ _ _ HD HM) as HΔ.
  assert (Hlen : List.length (im_params D M) = im_np D M)
    by (unfold im_params, im_np, im_nn, ind_nu; rewrite length_app; reflexivity).
  rewrite <- (List.firstn_skipn (im_np D M - k) (im_params D M)) in HΔ.
  apply ctx_scoped_app in HΔ as [HΔ1 _]; rewrite Nat.add_0_r in HΔ1.
  rewrite List.length_skipn, Hlen in HΔ1.
  replace (im_np D M - (im_np D M - k)) with k in HΔ1 by lia.
  apply ctx_pi_scoped; [ exact HΔ1 |].
  rewrite List.length_firstn, Hlen; eapply exp_scoped_wk; [ exact (dc_sort _ HD) |]; intros x Hx;
    unfold im_np, ind_nu in *; cbn; lia.
Qed.

(** The type of a member at some of its parameters is as scoped as they
    are. *)
Lemma ind_ty_at_scoped : forall D j M Ns n,
    decl_closed D -> ind_member D j = Some M -> List.Forall (exp_scoped n) Ns -> exp_scoped n (ind_ty_at D M Ns).
Proof.
  intros * HD HM HNs; unfold ind_ty_at; apply exp_scoped_sb_of_list; [| exact HNs ].
  destruct (Nat.le_gt_cases (List.length Ns) (im_np D M)).
  - eapply exp_scoped_mono; [| eapply decl_closed_ind_ty_at; eassumption ]; lia.
  - replace (im_np D M - List.length Ns) with (im_np D M - im_np D M) by lia.
    eapply exp_scoped_mono; [| eapply decl_closed_ind_ty_at; [ eassumption | eassumption | lia ] ]; lia.
Qed.

Lemma decl_closed_con_ty : forall p D k M c gs, decl_closed D -> ind_member D k = Some M -> In (c, gs) (im_cons M) ->
    exp_scoped 0 (con_ty p D k M gs).
Proof.
  intros p D k M c gs HD HM Hin; pose proof (dc_members _ HD _ _ HM) as HMc.
  unfold con_ty; apply ctx_pi_scoped; [ eapply decl_closed_params; eassumption |].
  rewrite Nat.add_0_r; apply ctx_pi_scoped.
  - assert (Hl : List.length (im_params D M) = im_nn M + ind_nu D)
      by (unfold im_params, im_nn, ind_nu; rewrite length_app; reflexivity).
    rewrite Hl; apply (cargs_ctx_aux_scoped p D (im_nn M) gs nil 0 HD eq_refl); intros; cbn.
    + eapply (mc_args _ _ HMc); eassumption.
    + eapply (mc_recs _ _ HMc); eassumption.
  - rewrite length_cargs_ctx; apply ind_mty_scoped; [ exact HD | unfold ind_uvars; apply length_vars_from | |];
      apply vars_from_scoped; unfold im_params, im_nn, ind_nu; rewrite length_app; lia.
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

(** The same for the right sides of pointwise equations. *)
Lemma nth_typed_scoped_r : forall (Ms Ms' Ts : list typ) n,
    List.length Ms' = List.length Ms -> List.length Ts = List.length Ms ->
    (forall k M M' T, nth_error Ms k = Some M -> nth_error Ms' k = Some M' -> nth_error Ts k = Some T -> exp_scoped n M') ->
    List.Forall (exp_scoped n) Ms'.
Proof.
  intros * Hl' Hl H; apply List.Forall_forall; intros M' HM'.
  destruct (List.In_nth_error _ _ HM') as [k Hk].
  assert (Hk' : k < List.length Ms') by (apply List.nth_error_Some; congruence).
  destruct (nth_error Ms k) as [M |] eqn:HM; [| apply List.nth_error_None in HM; lia ].
  destruct (nth_error Ts k) as [T |] eqn:HT; [ eauto | apply List.nth_error_None in HT; lia ].
Qed.

(** A view's uniform arguments, read from their form with the members as
    variables, are over the uniform parameters. *)
Lemma view_is_scoped : forall pq D (IsS : nat -> list exp) k Is (Ts : list typ),
    Is = List.map (fun I => I[grp_sb pq D]) (IsS k) ->
    List.length Ts = List.length (IsS k) ->
    (forall j I T, nth_error (IsS k) j = Some I -> nth_error Ts j = Some T -> exp_scoped (List.length (grp_sctx D)) I) ->
    List.Forall (exp_scoped (ind_nu D)) Is.
Proof.
  intros * -> Hl H; apply List.Forall_map.
  eapply List.Forall_impl; [| exact (nth_typed_scoped _ _ _ Hl H) ].
  intros I HI; eapply exp_scoped_sub; [ exact HI | apply grp_sb_bound ].
Qed.

Lemma length_im_params : forall D M, List.length (im_params D M) = im_np D M.
Proof. intros; unfold im_params, im_np, im_nn, ind_nu; rewrite length_app; reflexivity. Qed.

Lemma length_tele_insts_params : forall D M σ Ps,
    tele_ass (im_params D M) -> List.length Ps = im_np D M -> List.length (tele_insts (im_params D M) σ Ps) = List.length Ps.
Proof. intros * HΔ Hl; rewrite length_tele_insts by exact HΔ; rewrite length_im_params; lia. Qed.

Lemma length_tele_insts_cargs : forall p D M gs σ As,
    List.length As = List.length gs -> List.length (tele_insts (cargs_ctx p D M gs) σ As) = List.length As.
Proof. intros * Hl; rewrite length_tele_insts by apply cargs_ctx_aux_ass; rewrite length_cargs_ctx; lia. Qed.

Lemma elim_brs_scoped : forall p D M Us As Bs m,
    brs_names (im_cons M) Bs ->
    (forall c gs n B, ind_con M c = Some gs -> In (c, n, B) Bs -> n = (im_nn M + List.length gs + cargs_nrec gs)%nat) ->
    (forall c gs n B, ind_con M c = Some gs -> In (c, n, B) Bs -> exp_scoped (List.length (elim_bctx p D M gs As Us) + m) B) ->
    all_brs (fun k B => exp_scoped (k + m) B) Bs.
Proof.
  intros * Hn Hk HB; apply all_brs_Forall, List.Forall_forall; intros [[c n] B] Hin; cbn.
  destruct (brs_names_con _ _ _ _ _ Hn Hin) as [gs Hgs].
  rewrite (Hk _ _ _ _ Hgs Hin); specialize (HB _ _ _ _ Hgs Hin); rewrite length_elim_bctx in HB.
  replace (im_nn M + length gs + cargs_nrec gs) with (cargs_nrec gs + length gs + im_nn M) by lia; exact HB.
Qed.

Lemma brs_nth_same : forall (Bs Bs' : list (String.string * nat * exp)) k c n B,
    List.map fst Bs = List.map fst Bs' -> nth_error Bs k = Some (c, n, B) -> exists B', nth_error Bs' k = Some (c, n, B').
Proof.
  intros * Hm Hk; apply (f_equal (fun l => nth_error l k)) in Hm; rewrite !nth_error_map, Hk in Hm.
  destruct (nth_error Bs' k) as [[[c' n'] B'] |]; cbn in Hm; [ injection Hm as -> ->; eauto | discriminate ].
Qed.

Lemma elim_brs_scoped' : forall p D M Us As Bs (Bs' : list (String.string * nat * exp)) m,
    brs_names (im_cons M) Bs ->
    List.map fst Bs = List.map fst Bs' ->
    (forall c gs n B, ind_con M c = Some gs -> In (c, n, B) Bs -> n = (im_nn M + List.length gs + cargs_nrec gs)%nat) ->
    (forall k c gs n B B', nth_error Bs k = Some (c, n, B) -> nth_error Bs' k = Some (c, n, B') ->
       ind_con M c = Some gs -> exp_scoped (List.length (elim_bctx p D M gs As Us) + m) B') ->
    all_brs (fun k B => exp_scoped (k + m) B) Bs'.
Proof.
  intros * Hn Hm Hk HB; apply all_brs_Forall, List.Forall_forall; intros [[c n] B'] Hin'; cbn.
  destruct (List.In_nth_error _ _ Hin') as [k Hk'].
  destruct (brs_nth_same _ _ _ _ _ _ (eq_sym Hm) Hk') as [B HkB].
  pose proof (List.nth_error_In _ _ HkB) as Hin.
  destruct (brs_names_con _ _ _ _ _ Hn Hin) as [gs Hgs].
  rewrite (Hk _ _ _ _ Hgs Hin); specialize (HB _ _ _ _ _ _ HkB Hk' Hgs); rewrite length_elim_bctx in HB.
  replace (im_nn M + length gs + cargs_nrec gs) with (cargs_nrec gs + length gs + im_nn M) by lia; exact HB.
Qed.

Lemma brs_wk_scoped : forall Bs m n φ, all_brs (fun k B => exp_scoped (k + m) B) Bs ->
    (forall x, x < m -> φ x < n) -> all_brs (fun k B => exp_scoped (k + n) B) (brs_wk Bs φ).
Proof.
  induction Bs as [| [[c k] B] Bs IH]; intros * HB Hφ; cbn in *; [ exact I |].
  destruct HB as [HB HBs]; split; [| eapply IH; eassumption ].
  eapply exp_scoped_wk; [ exact HB |]; apply wk_qn_bound; exact Hφ.
Qed.

Lemma Forall_skipn' : forall {A} (P : A -> Prop) n l, List.Forall P l -> List.Forall P (List.skipn n l).
Proof. intros * H; rewrite <- (firstn_skipn n l) in H; apply List.Forall_app in H as [_ H]; exact H. Qed.

Lemma Forall_firstn' : forall {A} (P : A -> Prop) n l, List.Forall P l -> List.Forall P (List.firstn n l).
Proof. intros * H; rewrite <- (firstn_skipn n l) in H; apply List.Forall_app in H as [H _]; exact H. Qed.

(** The blocks of an eliminator, scoped. *)
Definition blocks_scoped (m : nat) (Bks : list eblock) : Prop :=
  all_blocks (fun nm oZ A Bs => opt_all (exp_scoped (nm - 1 + m)) oZ /\ exp_scoped (nm + m) A /\
                                all_brs (fun k B => exp_scoped (k + m) B) Bs) Bks.

Lemma exp_scoped_elim : forall n oq Us k Bks M,
    exp_scoped n (a_elim oq Us k Bks M) <-> List.Forall (exp_scoped n) Us /\ blocks_scoped n Bks /\ exp_scoped n M.
Proof. intros; cbn [exp_scoped]; rewrite all_list_Forall; reflexivity. Qed.

Lemma blocks_wk_scoped : forall Bks m n φ, blocks_scoped m Bks ->
    (forall x, x < m -> φ x < n) -> blocks_scoped n (blocks_wk Bks φ).
Proof.
  induction Bks as [| [nm oZ A Bs] Bks IH]; intros * HB Hφ; cbn in *; [ exact I |].
  destruct HB as [(HZ & HA & HBs) HBks]; split; [| eapply IH; eassumption ].
  split; [| split ].
  - destruct oZ; cbn in *; [| exact I ]; eapply exp_scoped_wk; [ exact HZ |]; apply wk_qn_bound; exact Hφ.
  - eapply exp_scoped_wk; [ exact HA |]; apply wk_qn_bound; exact Hφ.
  - exact (brs_wk_scoped _ _ _ _ HBs Hφ).
Qed.

Lemma sb_ext_bound : forall σ N n m,
    (forall x, x < n -> sentry_scoped m (σ x)) -> exp_scoped m N ->
    forall x, x < S n -> sentry_scoped m ((σ ,, N) x).
Proof. intros * H HN [| x] Hx; cbn; [ exact HN | apply H; lia ]. Qed.

Lemma qname_mod_scoped : forall p n, modexp_scoped n (qname_mod p).
Proof.
  intros [fp ch] n; unfold qname_mod; cbn [q_unit q_chain].
  generalize (me_unit fp) (I : modexp_scoped n (me_unit fp)).
  induction ch as [| y ch IH]; intros H HH; cbn; [ exact HH | apply IH; exact HH ].
Qed.

Lemma qname_term_scoped : forall p n, exp_scoped n (qname_term p).
Proof.
  intros [fp ch] n; unfold qname_term; cbn [q_unit q_chain].
  generalize (me_unit fp) (I : modexp_scoped n (me_unit fp)).
  induction ch as [| y ch IH]; intros H HH; [ exact I |].
  destruct ch as [| z ch]; [ exact HH | apply IH; exact HH ].
Qed.

(** The blocks' binder counts are the members': the premise of the
    eliminator's rules that the lemmas below need. *)
Definition blocks_nm_ok (D : ind_decl) (Bks : list eblock) : Prop :=
  forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk).

Lemma elim_at_scoped : forall pq D oq Us Bks j M m,
    decl_closed D -> List.length Us = ind_nu D -> List.Forall (exp_scoped m) Us ->
    blocks_nm_ok D Bks -> blocks_scoped m Bks -> exp_scoped m M ->
    exp_scoped m (elim_at pq D oq Us Bks j M).
Proof.
  intros * HD Hl HUs Hnm HB HM; unfold elim_at.
  apply (proj2 (exp_scoped_elim _ _ _ _ _ _)); split; [ exact HUs | split; [ exact HB | exact HM ] ].
Qed.

Lemma blocks_nm_ok_wk : forall D Bks φ, blocks_nm_ok D Bks -> blocks_nm_ok D (blocks_wk Bks φ).
Proof.
  intros * H k Mk b HM Hb; unfold blocks_wk in Hb; rewrite List.nth_error_map in Hb.
  destruct (List.nth_error Bks k) as [[nm oZ A Bs] |] eqn:E; cbn in Hb; [| discriminate ].
  injection Hb as <-; cbn; exact (H _ _ _ HM E).
Qed.

Lemma ptyp_ih_scoped : forall pq D oq t Us Bks σ M m k,
    decl_closed D -> List.length Us = ind_nu D -> List.Forall (exp_scoped m) Us ->
    blocks_nm_ok D Bks -> blocks_scoped m Bks ->
    (forall x, x < k -> sentry_scoped m (σ x)) -> ptyp_scoped k t -> exp_scoped m M ->
    exp_scoped m (ptyp_ih pq D oq Us Bks σ M t).
Proof.
  intros pq D oq t; induction t as [k0 Ps | B t IH]; intros * HD Hl HUs Hnm HBs Hσ Ht HM; cbn in *;
    [ split; [ apply all_list_Forall; exact HUs | split; assumption ] |].
  destruct Ht as [HB Ht]; split; [ eapply exp_scoped_sub; eassumption |].
  eapply IH; [ exact HD | rewrite length_map; exact Hl | | apply blocks_nm_ok_wk; exact Hnm | | apply sb_q_bound; exact Hσ | exact Ht | ].
  - apply List.Forall_map; eapply List.Forall_impl; [| exact HUs ]; intros U HU; apply exp_scoped_shift; exact HU.
  - eapply blocks_wk_scoped; [ exact HBs |]; cbn; lia.
  - cbn; split; [ apply exp_scoped_shift; exact HM | lia ].
Qed.

Lemma elim_ihs_scoped : forall pq D oq Us Bks gs σ As m k,
    decl_closed D -> List.length Us = ind_nu D -> List.Forall (exp_scoped m) Us ->
    blocks_nm_ok D Bks -> blocks_scoped m Bks ->
    (forall x, x < k -> sentry_scoped m (σ x)) ->
    (forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> ptyp_scoped (List.length (cargs_strat gs1) + k) t) ->
    List.Forall (exp_scoped m) As -> List.Forall (exp_scoped m) (elim_ihs pq D oq Us Bks σ gs As).
Proof.
  induction gs as [| [A0 | t] gs IH]; intros σ [| N As] m k HD Hl HUs Hnm HBs Hσ Ht HAs; cbn; try constructor;
    inversion_clear HAs.
  - eapply (IH _ _ _ (S k)); [ eassumption .. | apply sb_ext_bound; assumption | | assumption ].
    intros gs1 t gs2 ->; specialize (Ht (ca_arg A0 :: gs1) t gs2 eq_refl); cbn in Ht; rewrite length_app in Ht; cbn in Ht.
    eapply ptyp_scoped_mono; [| exact Ht ]; lia.
  - eapply ptyp_ih_scoped; [ eassumption .. | exact (Ht nil t gs eq_refl) | assumption ].
  - eapply IH; [ eassumption .. | | assumption ].
    intros gs1 t' gs2 ->; exact (Ht (ca_rec t :: gs1) t' gs2 eq_refl).
Qed.

(** The recursive results of [ι]: the shapes' domains instantiated by the
    parameters and the arguments. *)
Lemma elim_ihs_scoped_at : forall pq D oq k M c gs Bks Ps As m,
    decl_closed D -> ind_member D k = Some M -> ind_con M c = Some gs -> List.length Ps = im_np D M ->
    blocks_nm_ok D Bks -> blocks_scoped m Bks ->
    List.Forall (exp_scoped m) Ps -> List.Forall (exp_scoped m) As ->
    List.Forall (exp_scoped m) (elim_ihs pq D oq (List.firstn (ind_nu D) Ps) Bks (sb_of_list Id Ps) gs As).
Proof.
  intros * Hc HM Hcon Hl Hnm HBs HPs HAs; pose proof (mc_recs _ _ (dc_members _ Hc _ _ HM)) as Ht.
  eapply (elim_ihs_scoped _ _ _ _ _ _ _ _ _ (List.length Ps + 0)); [ exact Hc | | | exact Hnm | exact HBs | | | exact HAs ].
  - rewrite List.length_firstn; unfold im_np in Hl; lia.
  - apply Forall_firstn'; exact HPs.
  - apply sb_of_list_bound; [ intros; lia | exact HPs ].
  - intros gs1 t gs2 E; rewrite Nat.add_0_r, Hl; exact (Ht _ _ _ _ _ (cons_lookup_in _ _ _ Hcon) E).
Qed.

(** The motive's instance at the non-uniform parameters and the scrutinee. *)
Lemma elim_inst_scoped : forall D M A Ps N m,
    List.length Ps = im_np D M ->
    exp_scoped (S (im_nn M) + m) A -> List.Forall (exp_scoped m) Ps -> exp_scoped m N ->
    exp_scoped m A[sb_of_list Id (List.skipn (ind_nu D) Ps ++ N :: nil)].
Proof.
  intros * Hl HA HPs HN; apply exp_scoped_sb_of_list.
  - rewrite length_app, length_skipn; cbn; unfold im_np in *; replace (length Ps - ind_nu D + 1 + m) with (S (im_nn M + m)) by lia; exact HA.
  - apply List.Forall_app; split; [| constructor; auto ].
    exact (Forall_skipn' _ _ _ HPs).
Qed.

Lemma elim_brs_scoped_l : forall p D M Us As Bs (Bs' : list (String.string * nat * exp)) m,
    brs_names (im_cons M) Bs ->
    List.map fst Bs = List.map fst Bs' ->
    (forall c gs n B, ind_con M c = Some gs -> In (c, n, B) Bs -> n = (im_nn M + List.length gs + cargs_nrec gs)%nat) ->
    (forall k c gs n B B', nth_error Bs k = Some (c, n, B) -> nth_error Bs' k = Some (c, n, B') ->
       ind_con M c = Some gs -> exp_scoped (List.length (elim_bctx p D M gs As Us) + m) B) ->
    all_brs (fun k B => exp_scoped (k + m) B) Bs.
Proof.
  intros * Hn Hm Hk HB; eapply elim_brs_scoped; [ eassumption | eassumption |].
  intros * Hgs Hin.
  destruct (List.In_nth_error _ _ Hin) as [k Hk'].
  destruct (brs_nth_same _ _ _ _ _ _ Hm Hk') as [B' HkB'].
  eauto.
Qed.


(** The blocks of an eliminator, read position by position. *)
Lemma all_blocks_nth : forall {A : Set} (f : nat -> option A -> A -> list (String.string * nat * A) -> Prop) Bks,
    (forall k b, List.nth_error Bks k = Some b -> f (eb_nm b) (eb_ann b) (eb_motive b) (eb_brs b)) ->
    all_blocks f Bks.
Proof.
  induction Bks as [| [nm oZ M Bs] Bks IH]; intros H; cbn; [ exact I |].
  split; [ exact (H 0 _ eq_refl) | apply IH; intros k b Hk; exact (H (S k) b Hk) ].
Qed.

Lemma all_blocks_nth_inv : forall {A : Set} (f : nat -> option A -> A -> list (String.string * nat * A) -> Prop) Bks k b,
    all_blocks f Bks -> List.nth_error Bks k = Some b -> f (eb_nm b) (eb_ann b) (eb_motive b) (eb_brs b).
Proof.
  induction Bks as [| [nm oZ M Bs] Bks IH]; intros * H Hk; [ destruct k; discriminate |].
  destruct H as [Hb H]; destruct k as [| k]; cbn in Hk; [ injection Hk as <-; exact Hb | exact (IH _ _ H Hk) ].
Qed.

Lemma blocks_scoped_nth : forall m Bks k b, blocks_scoped m Bks -> List.nth_error Bks k = Some b ->
    opt_all (exp_scoped (eb_nm b - 1 + m)) (eb_ann b) /\ exp_scoped (eb_nm b + m) (eb_motive b) /\
    all_brs (fun k B => exp_scoped (k + m) B) (eb_brs b).
Proof. intros * H Hk; exact (all_blocks_nth_inv _ _ _ _ H Hk). Qed.

Lemma nth_error_member : forall D (Bks : list eblock) k b,
    List.length Bks = List.length (ind_members D) -> List.nth_error Bks k = Some b ->
    exists Mk, ind_member D k = Some Mk.
Proof.
  intros * Hl Hk; unfold ind_member.
  destruct (List.nth_error (ind_members D) k) eqn:E; [ eauto |].
  apply List.nth_error_None in E; assert (Hk' : List.nth_error Bks k <> None) by congruence.
  apply List.nth_error_Some in Hk'; lia.
Qed.

(** The blocks of an eliminator, scoped, from what typing says of each:
    the annotation under the member's non-uniform parameters, the motive
    under them and the scrutinee, each branch under its context. *)
Lemma elim_blocks_scoped : forall p D Us Bks m,
    List.length Bks = List.length (ind_members D) ->
    blocks_nm_ok D Bks ->
    (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
       exp_scoped (im_nn Mk + m) Z) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       exp_scoped (S (im_nn Mk) + m) (eb_motive b)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
       exp_scoped (List.length (elim_bctx p D Mk gs (blocks_motives Bks) Us) + m) B) ->
    blocks_scoped m Bks.
Proof.
  intros * Hl Hnm HZ HA Hn Hk HB; apply all_blocks_nth; intros k b Hb.
  destruct (nth_error_member _ _ _ _ Hl Hb) as [Mk HMk].
  pose proof (Hnm _ _ _ HMk Hb) as Enm.
  split; [| split ].
  - destruct (eb_ann b) as [Z |] eqn:EZ; cbn; [| exact I ].
    rewrite Enm; replace (S (im_nn Mk) - 1 + m) with (im_nn Mk + m) by lia; exact (HZ _ _ _ _ HMk Hb EZ).
  - rewrite Enm; exact (HA _ _ _ HMk Hb).
  - eapply elim_brs_scoped; [ exact (Hn _ _ _ HMk Hb) | intros; eapply Hk; eassumption | intros; eapply HB; eassumption ].
Qed.

(** The same where the branches are given position by position against the
    left blocks' ([elim_brs_scoped']). *)
Lemma elim_blocks_scoped' : forall p D Us Bks Bks' m,
    List.length Bks' = List.length (ind_members D) ->
    blocks_nm_ok D Bks' ->
    (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_ann b = Some Z ->
       exp_scoped (im_nn Mk + m) Z) ->
    (forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
       exp_scoped (S (im_nn Mk) + m) (eb_motive b')) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k b b', List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
       List.map fst (eb_brs b) = List.map fst (eb_brs b')) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
    (forall k Mk b b' i c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       List.nth_error Bks' k = Some b' ->
       nth_error (eb_brs b) i = Some (c, n, B) -> nth_error (eb_brs b') i = Some (c, n, B') ->
       ind_con Mk c = Some gs ->
       exp_scoped (List.length (elim_bctx p D Mk gs (blocks_motives Bks) Us) + m) B') ->
    List.length Bks = List.length (ind_members D) ->
    blocks_scoped m Bks'.
Proof.
  intros * Hl' Hnm HZ HA Hn Hm Hk HB Hl; apply all_blocks_nth; intros k b' Hb'.
  destruct (nth_error_member _ _ _ _ Hl' Hb') as [Mk HMk].
  destruct (List.nth_error Bks k) as [b |] eqn:Hb;
    [| apply List.nth_error_None in Hb; assert (Hk' : List.nth_error Bks' k <> None) by congruence;
       apply List.nth_error_Some in Hk'; lia ].
  pose proof (Hnm _ _ _ HMk Hb') as Enm.
  split; [| split ].
  - destruct (eb_ann b') as [Z |] eqn:EZ; cbn; [| exact I ].
    rewrite Enm; replace (S (im_nn Mk) - 1 + m) with (im_nn Mk + m) by lia; exact (HZ _ _ _ _ HMk Hb' EZ).
  - rewrite Enm; exact (HA _ _ _ _ HMk Hb Hb').
  - eapply elim_brs_scoped'; [ exact (Hn _ _ _ HMk Hb) | exact (Hm _ _ _ Hb Hb') | intros; eapply Hk; eassumption |].
    intros; eapply HB; eassumption.
Qed.

(** The left blocks, where the branches are given position by position. *)
Lemma elim_blocks_scoped_l : forall p D Us Bks (Bks' : list eblock) m,
    List.length Bks = List.length (ind_members D) ->
    blocks_nm_ok D Bks ->
    (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
       exp_scoped (im_nn Mk + m) Z) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       exp_scoped (S (im_nn Mk) + m) (eb_motive b)) ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k b b', List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
       List.map fst (eb_brs b) = List.map fst (eb_brs b')) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
    (forall k Mk b b' i c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       List.nth_error Bks' k = Some b' ->
       nth_error (eb_brs b) i = Some (c, n, B) -> nth_error (eb_brs b') i = Some (c, n, B') ->
       ind_con Mk c = Some gs ->
       exp_scoped (List.length (elim_bctx p D Mk gs (blocks_motives Bks) Us) + m) B) ->
    List.length Bks' = List.length (ind_members D) ->
    blocks_scoped m Bks.
Proof.
  intros * Hl Hnm HZ HA Hn Hm Hk HB Hl'; apply all_blocks_nth; intros k b Hb.
  destruct (nth_error_member _ _ _ _ Hl Hb) as [Mk HMk].
  destruct (List.nth_error Bks' k) as [b' |] eqn:Hb';
    [| apply List.nth_error_None in Hb'; assert (Hk' : List.nth_error Bks k <> None) by congruence;
       apply List.nth_error_Some in Hk'; lia ].
  pose proof (Hnm _ _ _ HMk Hb) as Enm.
  split; [| split ].
  - destruct (eb_ann b) as [Z |] eqn:EZ; cbn; [| exact I ].
    rewrite Enm; replace (S (im_nn Mk) - 1 + m) with (im_nn Mk + m) by lia; exact (HZ _ _ _ _ HMk Hb EZ).
  - rewrite Enm; exact (HA _ _ _ HMk Hb).
  - eapply elim_brs_scoped_l; [ exact (Hn _ _ _ HMk Hb) | exact (Hm _ _ _ Hb Hb') | intros; eapply Hk; eassumption |].
    intros; eapply HB; eassumption.
Qed.

(** The uniform arguments of a member's type at uniform parameters as
    scoped as they are. *)
Lemma im_pre_scoped : forall D k M Us n,
    decl_closed D -> ind_member D k = Some M -> List.length Us = ind_nu D ->
    List.Forall (exp_scoped n) Us -> List.Forall (exp_scoped n) (im_pre M Us).
Proof.
  intros * HD HM Hl HUs; unfold im_pre.
  destruct (im_head M) as [pm | qc k' Is vm] eqn:Hh; [ exact HUs |].
  apply List.Forall_map; eapply List.Forall_impl; [| exact (mc_head _ _ (dc_members _ HD _ _ HM) _ _ _ _ Hh) ].
  intros I HI; apply exp_scoped_sb_of_list; [| exact HUs ].
  eapply exp_scoped_mono; [| exact HI ]; lia.
Qed.

(** ** The Container's Blocks at a View *)

Lemma cargs_corr_length : forall vm gs' gs, cargs_corr vm gs' gs -> List.length gs' = List.length gs.
Proof.
  induction gs' as [| [] gs' IH]; intros [| [] gs] H; cbn in *; try contradiction; try reflexivity;
    f_equal; apply IH; tauto.
Qed.

Lemma length_wrap_ihs : forall vm gs' gs ihs r' nr',
    cargs_corr vm gs' gs -> List.length (wrap_ihs gs' gs ihs r' nr') = cargs_nrec gs.
Proof.
  induction gs' as [| [] gs' IH]; intros [| [] gs] * H; cbn in *; try contradiction; try reflexivity;
    try (f_equal; apply IH; tauto); apply IH; tauto.
Qed.

Lemma wrap_ihs_scoped : forall vm gs' gs ihs r' nr' N,
    cargs_corr vm gs' gs -> r' + cargs_nrec gs' <= nr' -> nr' <= N ->
    List.Forall (exp_scoped N) ihs -> List.Forall (exp_scoped N) (wrap_ihs gs' gs ihs r' nr').
Proof.
  assert (Htl : forall N (ihs : list exp), List.Forall (exp_scoped N) ihs -> List.Forall (exp_scoped N) (List.tl ihs))
    by (intros ? [] H; cbn; [ constructor | inversion H; assumption ]).
  assert (Hhd : forall N (ihs : list exp), List.Forall (exp_scoped N) ihs -> exp_scoped N (List.hd a_True ihs))
    by (intros ? [] H; cbn; [ exact I | inversion H; assumption ]).
  induction gs' as [| [] gs' IH]; intros [| [] gs] * H Hr HN Hihs; cbn in *; try contradiction.
  - constructor.
  - apply IH; [ exact H | lia | lia | exact Hihs ].
  - constructor; [ apply Hhd, Hihs | apply IH; [ exact H | lia | lia | apply Htl, Hihs ] ].
  - constructor; [ cbn; lia | apply IH; [ tauto | lia | lia | apply Htl, Hihs ] ].
Qed.

(** A branch of the container's block, scoped. *)
Lemma wrap_br_scoped : forall pq D vm Us Bks Mv Bs c gs' m,
    decl_closed D -> List.length Us = ind_nu D -> List.Forall (exp_scoped m) Us ->
    blocks_nm_ok D Bks -> blocks_scoped m Bks ->
    member_closed D Mv ->
    (forall gs, ind_con Mv c = Some gs -> cargs_corr vm gs' gs) ->
    (exists gs, ind_con Mv c = Some gs) ->
    (forall gs n B, ind_con Mv c = Some gs -> In (c, n, B) Bs -> n = (im_nn Mv + List.length gs + cargs_nrec gs)%nat) ->
    all_brs (fun k B => exp_scoped (k + m) B) Bs ->
    exp_scoped (snd (fst (wrap_br pq D Us Bks Mv Bs c gs')) + m) (snd (wrap_br pq D Us Bks Mv Bs c gs')).
Proof.
  intros * HD Hl HUs Hnm HBks HMv Hcorr [gs Hgs] Hn HBs; unfold wrap_br; rewrite Hgs; cbn [fst snd].
  pose proof (Hcorr _ Hgs) as Hc; pose proof (cargs_corr_length _ _ _ Hc) as Hlen.
  destruct (brs_lookup Bs c) as [[n B] |] eqn:Hb; [| exact I ].
  pose proof (Hn _ _ _ Hgs (brs_lookup_in _ _ _ _ Hb)) as En.
  assert (HB : exp_scoped (n + m) B).
  { rewrite all_brs_Forall, List.Forall_forall in HBs; exact (HBs _ (brs_lookup_in _ _ _ _ Hb)). }
  set (n' := (im_nn Mv + length gs' + cargs_nrec gs')%nat).
  match goal with |- exp_scoped _ (_[sb_of_list _ ?L]) =>
    assert (HL : List.length L = n) by
      (rewrite !length_app, !length_vars_from, (length_wrap_ihs _ _ _ _ _ _ Hc); lia);
    eapply exp_scoped_sub; [ exact HB |]; rewrite <- HL; apply sb_of_list_bound;
      [ intros x Hx; cbn; unfold wk_shiftn; lia |]
  end.
  - assert (HUs' : List.Forall (exp_scoped (n' + m)) (List.map (fun U => U[wk_shiftn n']ʷ) Us)).
    { apply List.Forall_map; eapply List.Forall_impl; [| exact HUs ]; intros U HU.
      eapply exp_scoped_wk; [ exact HU |]; intros; unfold wk_shiftn; lia. }
    apply List.Forall_app; split; [| apply List.Forall_app; split ].
    + apply vars_from_scoped; subst n'; lia.
    + apply vars_from_scoped; subst n'; lia.
    + eapply wrap_ihs_scoped; [ exact Hc | lia | subst n'; lia |].
      eapply (elim_ihs_scoped _ _ _ _ _ _ _ _ _ (List.length Us + im_nn Mv)).
      * exact HD.
      * rewrite length_map; exact Hl.
      * exact HUs'.
      * apply blocks_nm_ok_wk; exact Hnm.
      * eapply blocks_wk_scoped; [ exact HBks |]; intros; unfold wk_shiftn; lia.
      * intros x Hx; apply (sb_of_list_bound _ _ 0); [ intros y Hy; lia | | ].
        -- apply List.Forall_app; split; [ exact HUs' | apply vars_from_scoped; subst n'; lia ].
        -- rewrite length_app, length_map, length_vars_from; lia.
      * intros gs1 t gs2 E; pose proof (mc_recs _ _ HMv _ _ _ _ _ (cons_lookup_in _ _ _ Hgs) E) as Ht.
        eapply ptyp_scoped_mono; [| exact Ht ]; unfold im_np; lia.
      * apply vars_from_scoped; subst n'; lia.
Qed.

(** The container's blocks at a view, scoped. *)
Lemma vwrap_scoped : forall pq D D' vm Us Bks m,
    decl_closed D -> vwrap_ok D D' vm -> List.length Us = ind_nu D -> List.Forall (exp_scoped m) Us ->
    blocks_nm_ok D Bks -> blocks_scoped m Bks ->
    (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
    (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
       ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mk + List.length gs + cargs_nrec gs)%nat) ->
    blocks_scoped m (vwrap pq D D' vm Us Bks).
Proof.
  intros * HD Hvw Hl HUs Hnm HBks Hnames Hn; apply all_blocks_nth; intros k b Hb.
  destruct (nth_error_vwrap_from _ _ _ _ _ _ _ _ _ Hb) as (Mi' & HMi' & ->); cbn [Nat.add].
  unfold vwrap_block.
  destruct (List.nth_error vm k) as [v |] eqn:Hv;
    [| apply List.nth_error_None in Hv; pose proof (vwo_length _ _ _ Hvw) as Hlv;
       assert (Hk : List.nth_error (ind_members D') k <> None) by congruence;
       apply List.nth_error_Some in Hk; unfold ind_member in *; lia ].
  rewrite (List.nth_error_nth _ _ _ Hv).
  destruct (vwo_members _ _ _ Hvw _ _ _ HMi' Hv) as (Mv & HMv & Hnn & Hcs & Hcorr).
  destruct (List.nth_error Bks v) as [[nm oZ A Bs] |] eqn:Hbv; [| cbn; repeat split; exact I ].
  rewrite HMv; cbn [eb_nm eb_ann eb_motive eb_brs opt_all].
  destruct (blocks_scoped_nth _ _ _ _ HBks Hbv) as (_ & HA & HBs); cbn in HA, HBs.
  split; [ exact I | split; [ exact HA |] ].
  apply all_brs_Forall, List.Forall_forall; intros [[c n] B] Hin.
  apply List.in_map_iff in Hin as ([c' gs'] & Ecg & Hin'); cbn [fst snd] in Ecg.
  pose proof (f_equal (fun t => snd (fst t)) Ecg) as En'; pose proof (f_equal snd Ecg) as EB; cbn in En', EB.
  rewrite <- En', <- EB.
  assert (Hc' : c' = c) by (pose proof (f_equal (fun t => fst (fst t)) Ecg) as E; cbn in E; exact E); subst c'.
  eapply wrap_br_scoped; [ exact HD | exact Hl | exact HUs | exact Hnm | exact HBks | exact (dc_members _ HD _ _ HMv) | | | | exact HBs ].
  - intros gs Hgs; exact (Hcorr _ _ _ Hin' Hgs).
  - assert (Hc : In c (List.map fst (im_cons Mv))) by (rewrite Hcs; apply List.in_map_iff; exists (c, gs'); auto).
    apply List.in_map_iff in Hc as ([c0 gs0] & E0 & Hin0); cbn in E0; subst c0.
    exact (cons_lookup_of_in _ _ _ Hin0).
  - intros; eapply Hn; [ exact HMv | exact Hbv | eassumption | eassumption ].
Qed.

(** A telescope whose entries are each scoped by the ones below it and [n]. *)
Lemma ctx_scoped_intro : forall Δ n,
    (forall Δ1 T Δ2, Δ = Δ1 ++ ce_ass T :: Δ2 -> exp_scoped (List.length Δ2 + n) T) ->
    tele_ass Δ -> ctx_scoped n Δ.
Proof.
  induction Δ as [| e Δ IH]; intros n H Hass; cbn; [ exact I |].
  inversion Hass as [| ? ? [A ->] Hass']; subst.
  split; [ exact (H nil A Δ eq_refl) |].
  apply IH; [| exact Hass' ]; intros Δ1 T Δ2 ->; exact (H (ce_ass A :: Δ1) T Δ2 eq_refl).
Qed.

Lemma member_closed_intro : forall D M,
    tele_ass (ind_uparams D) ->
    (forall j Mj, ind_member D j = Some Mj -> tele_ass (im_nparams Mj)) ->
    tele_ass (im_nparams M) ->
    (forall Δ1 T Δ2, im_nparams M = Δ1 ++ ce_ass T :: Δ2 -> exp_scoped (List.length (Δ2 ++ ind_uparams D)) T) ->
    (forall qc k' Is vm, im_head M = mh_view qc k' Is vm -> List.Forall (exp_scoped (List.length (ind_uparams D))) Is) ->
    (forall c gs gs1 A gs2, In (c, gs) (im_cons M) -> gs = gs1 ++ ca_arg A :: gs2 ->
       exp_scoped (List.length (cargs_strat gs1 ++ im_params D M)) A) ->
    (forall c gs gs1 t gs2 Bs1 B Bs2, In (c, gs) (im_cons M) -> gs = gs1 ++ ca_rec t :: gs2 ->
       ptyp_doms t = Bs1 ++ B :: Bs2 ->
       exp_scoped (List.length (doms_ctx Bs1 ++ cargs_strat gs1 ++ im_params D M)) B) ->
    (forall c gs, In (c, gs) (im_cons M) -> cargs_plen D gs) ->
    (forall c gs gs1 t gs2 Mj k P T, In (c, gs) (im_cons M) -> gs = gs1 ++ ca_rec t :: gs2 ->
       ind_member D (ptyp_mem t) = Some Mj ->
       nth_error (ptyp_ps t) k = Some P ->
       nth_error (tele_insts (im_nparams Mj)
                    (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_strat gs1) + im_nn M))) (ptyp_ps t)) k
         = Some T ->
       exp_scoped (List.length (ptyp_tele t ++ cargs_strat gs1 ++ im_params D M)) P) ->
    member_closed D M.
Proof.
  intros D M HassU HassM Hass HN Hh HA HB Hl HPs; constructor; try assumption.
  - apply ctx_scoped_intro; [| exact Hass ]; intros * E; specialize (HN _ _ _ E); rewrite length_app in HN; exact HN.
  - intros * Hin Heq; specialize (HA _ _ _ _ _ Hin Heq); rewrite length_app, length_im_params in HA; exact HA.
  - intros * Hin Heq; apply ptyp_scoped_intro.
    + intros Bs1 B Bs2 E; specialize (HB _ _ _ _ _ _ _ _ Hin Heq E).
      unfold doms_ctx in HB; rewrite !length_app, length_rev, length_map, length_im_params in HB.
      eapply exp_scoped_mono; [| exact HB ]; lia.
    + destruct (Hl _ _ Hin _ _ _ Heq) as (Mj & HMj & HlMj).
      eapply (nth_typed_scoped _ (tele_insts (im_nparams Mj)
                (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_strat gs1) + im_nn M))) (ptyp_ps t))).
      * rewrite length_tele_insts; [ unfold im_nn in HlMj; lia | exact (HassM _ _ HMj) ].
      * intros k P T Hk HT; specialize (HPs _ _ _ _ _ _ _ _ _ Hin Heq HMj Hk HT).
        unfold ptyp_tele, doms_ctx, ptyp_depth in *; rewrite !length_app, length_rev, length_map, length_im_params in HPs.
        eapply exp_scoped_mono; [| exact HPs ]; lia.
Qed.

Lemma decl_closed_intro : forall D,
    tele_ass (ind_uparams D) -> ctx_scoped 0 (ind_uparams D) ->
    exp_scoped (List.length (ind_uparams D)) (ind_sort D) ->
    (forall k M, ind_member D k = Some M -> member_closed D M) ->
    decl_closed D.
Proof. intros D Hass HΔ HS HM; constructor; assumption. Qed.

(** A module applied to arguments is as scoped as the module and the
    arguments. *)
Lemma me_apps_scoped_iff : forall Ns H n,
    modexp_scoped n (me_apps H Ns) <-> modexp_scoped n H /\ List.Forall (exp_scoped n) Ns.
Proof.
  induction Ns as [| N Ns IH]; intros; cbn; [ split; [ auto | intros []; assumption ] |].
  rewrite IH; cbn; split; [ intros [[] ?]; auto | intros [? HN]; inversion HN; subst; auto ].
Qed.

Lemma ctx_scoped_app_iff : forall Ψ Γ, ctx_scoped 0 (Ψ ++ Γ) <-> ctx_scoped (length Γ) Ψ /\ ctx_scoped 0 Γ.
Proof. intros; rewrite ctx_scoped_app, Nat.add_0_r; reflexivity. Qed.

(** ** Closed Entries

    What resolution hands back is closed: a definition's type and body, a body
    module's full telescope, and an alias. *)

(** A closed entry: see the section header; an inductive member's group is
    [decl_closed]. *)
Definition entry_closed (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B => exp_scoped 0 A /\ opt_scoped 0 B
  | ge_mod _ _ => True
  | ge_ind _ _ _ D _ => decl_closed D
  | ge_ind_alias _ Δ _ _ _ Ns => ctx_scoped 0 Δ /\ Forall (exp_scoped (List.length Δ)) Ns
  | ge_record _ _ _ _ => True
  end.

(** The declaration a module of a member of a group records is closed. *)
Definition dec_closed (oD : option indref) : Prop :=
  match oD with
  | Some (_, _, D) => decl_closed D
  | None => True
  end.

Definition modres_closed (r : modres) : Prop :=
  match r with
  | mr_body T oD => ctx_scoped 0 T /\ dec_closed oD
  | mr_alias U => gunit_scoped 0 U
  end.

(** A body stored closed over a telescope of length [k]: every definition
    is closed, every closed submodule is closed over the telescope and its
    own parameters, every other submodule is closed, and so is every
    inductive type and inductive alias; a closed body has no local open.
    Local modules are open: the scoping of local syntax ([moddef_scoped])
    admits no closed body. *)
Fixpoint body_closed (k : nat) (Φ : gmod) {struct Φ} : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ' _ E =>
      body_closed k Φ' /\
      match E with
      | ge_def _ _ A B => exp_scoped 0 A /\ opt_scoped 0 B
      | ge_mod _ (gu_mk Δ (md_body sm Φ1)) => sm = sm_closed /\ ctx_scoped k Δ /\ body_closed (List.length Δ + k) Φ1
      | ge_mod _ U => gunit_scoped 0 U
      | ge_ind _ _ _ D Φ1 => decl_closed D /\ body_closed (List.length (ind_uparams D)) Φ1
      | ge_ind_alias _ Δ _ _ _ Ns => ctx_scoped 0 Δ /\ List.Forall (exp_scoped (List.length Δ)) Ns
      | ge_record _ p R Φ1 =>
          (ctx_scoped 0 (record_fctx R (List.length (record_fields R)) ++ record_params R) /\
           exp_scoped (List.length (record_params R)) (record_sort R)) /\
          body_closed (List.length (record_mod_tele p R)) Φ1
      end
  | gm_open _ _ _ => False
  end.

(** Every definition and every module a module resolves to is closed, the
    module's own telescope being [T]. *)
Definition mod_closed (T : ctx) (Φ : gmod) : Prop :=
  (forall ip E, gm_resolve Φ ip = Some E -> entry_closed E) /\
  (forall x ip r, gm_submodule T Φ x ip = Some r -> modres_closed r).

Definition unit_closed (T : ctx) (Φ : gmod) : Prop := ctx_scoped 0 T /\ body_closed (List.length T) Φ.

Definition units_closed (Θ : gdeps) : Prop :=
  forall fp U, gds_lookup Θ fp = Some U -> unit_closed (gu_params U) (gu_mod U).

(** A frame's kind is closed: the declaration of the member a type's open
    frame is the module of, or of the record type it is the module of. *)
Definition kind_closed (K : frame_kind) : Prop :=
  match K with
  | fk_module => True
  | fk_ind _ _ D => decl_closed D
  | fk_record R =>
      ctx_scoped 0 (record_fctx R (List.length (record_fields R)) ++ record_params R) /\
      exp_scoped (List.length (record_params R)) (record_sort R)
  end.

Fixpoint stack_closed (Ξ : gstack) : Prop :=
  match Ξ with
  | nil => True
  | (_, K, U) :: Ξ' => stack_closed Ξ' /\ unit_closed (gu_params U ++ gs_tele Ξ') (gu_mod U) /\ kind_closed K
  end.

Definition gctx_closed (Θ : gdeps) (Ξ : gstack) : Prop :=
  units_closed Θ /\ stack_closed Ξ.

(** What a closed body resolves to is closed. *)
Lemma unit_closed_mod : forall Φ T, unit_closed T Φ -> mod_closed T Φ.
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] T [HT HΦ]; cbn in HΦ; [ split; intros; discriminate | | contradiction ].
  destruct HΦ as [HΦ HE]; destruct (IH Φ T (conj HT HΦ)) as [IHr IHm]; split.
  - intros [| x ip] E0 Hr; cbn in Hr; [ discriminate |].
    destruct (String.eqb x y); [| eapply IHr; exact Hr ].
    destruct ip as [| z ip], E as [b pv A B | pm [Δ [sm Φ1 | E1]] | pv pq k0 D Φ1 | pv Δa pma pa ka Nsa | pv pr Rr Φ1]; try discriminate.
    + injection Hr as <-; exact HE.
    + destruct HE as (-> & HΔ & HΦ1).
      assert (Hu : unit_closed (Δ ++ T) Φ1) by (split; [ apply ctx_scoped_app_iff; auto | rewrite length_app; exact HΦ1 ]).
      exact (proj1 (IH _ _ Hu) _ _ Hr).
    + destruct HE as [HD HΦ1].
      assert (Hu : unit_closed (ind_uparams D) Φ1) by (split; [ apply (dc_uparams _ HD) | exact HΦ1 ]).
      exact (proj1 (IH _ _ Hu) _ _ Hr).
    + destruct HE as [[HF _] HΦ1].
      assert (Hu : unit_closed (record_mod_tele pr Rr) Φ1)
        by (split; [ exact (record_mod_tele_scoped _ _ (proj2 (proj1 (ctx_scoped_app_iff _ _) HF))) | exact HΦ1 ]).
      exact (proj1 (IH _ _ Hu) _ _ Hr).
  - intros x ip r Hr; cbn in Hr.
    destruct (String.eqb x y); [| eapply IHm; exact Hr ].
    destruct E as [b pv A B | pm [Δ [sm Φ1 | E1]] | pv pq k0 D Φ1 | pv Δa pma pa ka Nsa | pv pr Rr Φ1]; try discriminate.
    + destruct HE as (-> & HΔ & HΦ1).
      assert (Hu : unit_closed (Δ ++ T) Φ1) by (split; [ apply ctx_scoped_app_iff; auto | rewrite length_app; exact HΦ1 ]).
      destruct ip as [| z ip]; [ injection Hr as <-; split; [ apply Hu | exact I ] |].
      exact (proj2 (IH _ _ Hu) _ _ _ Hr).
    + destruct ip; [ injection Hr as <-; exact HE | discriminate ].
    + destruct HE as [HD HΦ1].
      assert (Hu : unit_closed (ind_uparams D) Φ1) by (split; [ apply (dc_uparams _ HD) | exact HΦ1 ]).
      destruct ip as [| z ip]; [ injection Hr as <-; split; [ apply Hu | exact HD ] |].
      exact (proj2 (IH _ _ Hu) _ _ _ Hr).
    + destruct ip; [ injection Hr as <- | discriminate ].
      destruct HE as [HΔ HNs]; apply gunit_scoped_mk; split; [ exact HΔ |].
      cbn; apply me_apps_scoped_iff; split; [ apply qname_mod_scoped |].
      eapply Forall_impl; [| exact HNs ]; intros; cbn; rewrite Nat.add_0_r; assumption.
    + destruct HE as [[HF _] HΦ1].
      assert (Hu : unit_closed (record_mod_tele pr Rr) Φ1)
        by (split; [ exact (record_mod_tele_scoped _ _ (proj2 (proj1 (ctx_scoped_app_iff _ _) HF))) | exact HΦ1 ]).
      destruct ip as [| z ip]; [ injection Hr as <-; split; [ apply Hu | exact I ] |].
      exact (proj2 (IH _ _ Hu) _ _ _ Hr).
Qed.

Lemma stack_closed_in : forall Ξ mp K U,
    stack_closed Ξ -> List.In (mp, K, U) Ξ -> exists T, unit_closed T (gu_mod U).
Proof.
  induction Ξ as [| [[mq Kq] V] Ξ IH]; intros * HΞ Hin; cbn in *; [ contradiction |].
  destruct HΞ as [HΞ [HV _]]; destruct Hin as [[= <- <- <-] | Hin]; eauto.
Qed.

(** The declaration a type's open frame carries is closed. *)
Lemma stack_closed_ind : forall Ξ p pq k D, stack_closed Ξ -> gs_find_ind Ξ p = Some (pq, k, D) -> decl_closed D.
Proof.
  induction Ξ as [| [[mq Kq] V] Ξ IH]; intros * HΞ Hf; cbn in *; [ discriminate |].
  destruct HΞ as [HΞ [_ HK]].
  destruct (qname_strip mq p) as [[| ? ?] |]; [| discriminate | eauto ].
  destruct Kq; [ discriminate | injection Hf as -> -> ->; exact HK | discriminate ].
Qed.

(** The declaration a record's open frame carries is closed. *)
Lemma stack_closed_record : forall Ξ p R, stack_closed Ξ -> gs_find_record Ξ p = Some R ->
    ctx_scoped 0 (record_fctx R (List.length (record_fields R)) ++ record_params R) /\
    exp_scoped (List.length (record_params R)) (record_sort R).
Proof.
  induction Ξ as [| [[mq Kq] V] Ξ IH]; intros * HΞ Hf; cbn in *; [ discriminate |].
  destruct HΞ as [HΞ [_ HK]].
  destruct (qname_strip mq p) as [[| ? ?] |]; [| discriminate | eauto ].
  destruct Kq; [ discriminate | discriminate | injection Hf as ->; exact HK ].
Qed.

Lemma stack_closed_find : forall Ξ p U ip T,
    stack_closed Ξ -> gs_find_tele Ξ p = Some (U, ip, T) -> unit_closed (gu_params U ++ T) (gu_mod U).
Proof.
  induction Ξ as [| [[mq Kq] V] Ξ IH]; intros * HΞ Hf; cbn in *; [ discriminate |].
  destruct HΞ as [HΞ [HV _]].
  destruct (qname_strip mq p); [ injection Hf as <- <- <-; exact HV | eauto ].
Qed.

Lemma gctx_closed_resolve : forall Θ Ξ p b pv A B,
    gctx_closed Θ Ξ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    exp_scoped 0 A /\ opt_scoped 0 B.
Proof.
  intros * [HΘ HΞ] Hr.
  destruct (gc_resolve_inv _ _ _ _ Hr) as [(mp & K & U & ip & Hin & Hm) | (fp & U & Hl & Hm)].
  - destruct (stack_closed_in _ _ _ _ HΞ Hin) as (T & HU).
    exact (proj1 (unit_closed_mod _ _ HU) _ _ Hm).
  - exact (proj1 (unit_closed_mod _ _ (HΘ _ _ Hl)) _ _ Hm).
Qed.

Lemma gctx_closed_module : forall Θ Ξ p r,
    gctx_closed Θ Ξ ->
    gc_module Θ Ξ p = Some r ->
    modres_closed r.
Proof.
  intros * [HΘ HΞ] Hr; unfold gc_module, gc_module_u in Hr.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T] |] eqn:Hf; [ discriminate | |].
  - exact (proj2 (unit_closed_mod _ _ (stack_closed_find _ _ _ _ _ HΞ Hf)) _ _ _ Hr).
  - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
    pose proof (HΘ _ _ Hl) as HU0; destruct HU0 as [HT _]; destruct (unit_closed_mod _ _ (HΘ _ _ Hl)) as [_ HU].
    destruct (q_chain p) as [| x ip]; cbn in Hr; [ injection Hr as <-; split; [ exact HT | exact I ] | exact (HU _ _ _ Hr) ].
Qed.

Lemma gctx_closed_mind : forall Θ Ξ p pq k D,
    gctx_closed Θ Ξ -> ind_mlookup Θ Ξ p = Some (pq, k, D) -> decl_closed D.
Proof.
  intros * HΘ Hl; destruct (ind_mlookup_module _ _ _ _ Hl) as [[T Hm] | Hf].
  - exact (proj2 (gctx_closed_module _ _ _ _ HΘ Hm)).
  - exact (stack_closed_ind _ _ _ _ _ (proj2 HΘ) Hf).
Qed.

Lemma gctx_closed_ind : forall Θ Ξ p D,
    gctx_closed Θ Ξ -> ind_lookup Θ Ξ p = Some D -> decl_closed D.
Proof.
  intros * HΘ Hl; destruct (ind_lookup_mlookup _ _ _ _ Hl) as [pq Hm]; exact (gctx_closed_mind _ _ _ _ _ _ HΘ Hm).
Qed.

Lemma mod_closed_nil : forall T, ctx_scoped 0 T -> unit_closed T ⋄.
Proof. intros; split; [ assumption | exact I ]. Qed.

(** What an entry adds is closed if the entry is. *)
Definition entry_ok (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ _ _ => entry_closed E
  | ge_mod _ (gu_mk Δ (md_body sm Φ)) => sm = sm_closed /\ unit_closed (Δ ++ T) Φ
  | ge_mod _ U => gunit_scoped 0 U
  | ge_ind _ _ _ D Φ => decl_closed D /\ unit_closed (ind_uparams D) Φ
  | ge_ind_alias _ _ _ _ _ _ => entry_closed E
  | ge_record _ p R Φ =>
      (ctx_scoped 0 (record_fctx R (List.length (record_fields R)) ++ record_params R) /\
       exp_scoped (List.length (record_params R)) (record_sort R)) /\
      unit_closed (record_mod_tele p R) Φ
  end.


(** What an inductive alias records is closed: its telescope, and the
    arguments over it. *)
Lemma gctx_closed_ind_alias : forall Θ Ξ pq Δ pm p k Ns,
    gctx_closed Θ Ξ -> ind_alias_lookup Θ Ξ pq = Some (Δ, pm, p, k, Ns) ->
    ctx_scoped 0 Δ /\ List.Forall (exp_scoped (List.length Δ)) Ns.
Proof.
  intros * Hc Hl.
  pose proof (gctx_closed_module _ _ _ _ Hc (ind_alias_lookup_module _ _ _ _ _ _ _ _ Hl)) as Hm; cbn in Hm.
  apply gunit_scoped_mk in Hm as [HΔ Hm]; cbn in Hm.
  apply me_apps_scoped_iff in Hm as [_ HNs]; rewrite Nat.add_0_r in HNs; auto.
Qed.

Lemma mod_closed_ext : forall T Φ x E, unit_closed T Φ -> entry_ok T E -> unit_closed T (Φ ⊳ x ↦ E).
Proof.
  intros * [HT HΦ] HE; split; [ exact HT |]; cbn; split; [ exact HΦ |].
  destruct E as [b pv A B | pm [Δ [sm Φ1 | E1]] | pv pq k0 D Φ1 | pv Δa pma pa ka Nsa | pv pr Rr Φ1]; cbn in HE |- *; try exact HE.
  - destruct HE as (-> & HΔ & HΦ1); apply ctx_scoped_app_iff in HΔ as [HΔ _].
    rewrite length_app in HΦ1; auto.
  - destruct HE as [HD [_ HΦ1]]; auto.
  - destruct HE as [HR [_ HΦ1]]; auto.
Qed.

(** A chain from a unit has no variable. *)
Lemma mod_qname_scoped : forall H p n, mod_qname H = Some p -> modexp_scoped n H.
Proof.
  induction H; intros * Hp; cbn in *; try discriminate; auto.
  destruct (mod_qname H) eqn:E; [ eauto | discriminate ].
Qed.

