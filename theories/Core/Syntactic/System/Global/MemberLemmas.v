(** * Member Types under Weakening and Substitution

    The syntactic helpers of [Members] commute with the operations: a
    telescope, a body and a member chain are moved entry by entry, under the
    binders before each entry.  The relation [member_type] and the function
    [member_unfold] commute with a weakening and with a substitution that sends
    every module slot to the same unit ([wf_sub]'s module field), and they grow
    with the global context. *)

From Stdlib Require Import Lia List PeanoNat Morphisms.
From Stdlib Require String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Export Scoping.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Lifting under Many Binders *)

Lemma wk_qn_add : forall a b φ, wk_eq (wk_qn a (wk_qn b φ)) (wk_qn (a + b) φ).
Proof. induction a; intros; cbn; [ reflexivity | apply wk_q_cong, IHa ]. Qed.

Lemma sb_qn_add : forall a b σ, sb_eq (sb_qn a (sb_qn b σ)) (sb_qn (a + b) σ).
Proof. induction a; intros; cbn; [ reflexivity | apply sb_q_cong, IHa ]. Qed.

(** ** Telescopes *)

Lemma tele_wk_app : forall Ψ Δ φ,
    tele_wk (Ψ ++ Δ) φ = tele_wk Ψ (wk_qn (length Δ) φ) ++ tele_wk Δ φ.
Proof.
  induction Ψ; intros; cbn; [ reflexivity |].
  rewrite IHΨ; f_equal; apply centry_wk_wk_eq.
  rewrite length_app, wk_qn_add; reflexivity.
Qed.

Lemma tele_sub_app : forall Ψ Δ σ,
    tele_sub (Ψ ++ Δ) σ = tele_sub Ψ (sb_qn (length Δ) σ) ++ tele_sub Δ σ.
Proof.
  induction Ψ; intros; cbn; [ reflexivity |].
  rewrite IHΨ; f_equal; apply centry_sub_sb_eq.
  rewrite length_app, sb_qn_add; reflexivity.
Qed.

Lemma ctx_pi_wk : forall Δ A φ,
    (ctx_pi Δ A)[φ]ʷ = ctx_pi (tele_wk Δ φ) A[wk_qn (length Δ) φ]ʷ.
Proof.
  induction Δ as [| [] Δ IH]; intros; cbn; [ reflexivity | | | |]; rewrite IH; cbn;
    first [ reflexivity | rewrite exp_wk_sub_extend_dm; reflexivity ].
Qed.

Lemma ctx_pi_sub : forall Δ A σ,
    (ctx_pi Δ A)[σ] = ctx_pi (tele_sub Δ σ) A[sb_qn (length Δ) σ].
Proof.
  induction Δ as [| [] Δ IH]; intros; cbn; [ reflexivity | | | |]; rewrite IH; cbn;
    first [ reflexivity | rewrite exp_sub_sub_extend_dm; reflexivity ].
Qed.

Lemma ctx_fn_wk : forall Δ M φ,
    (ctx_fn Δ M)[φ]ʷ = ctx_fn (tele_wk Δ φ) M[wk_qn (length Δ) φ]ʷ.
Proof.
  induction Δ as [| [] Δ IH]; intros; cbn; [ reflexivity | | | |]; rewrite IH; cbn;
    first [ reflexivity | rewrite exp_wk_sub_extend_dm; reflexivity ].
Qed.

Lemma ctx_fn_sub : forall Δ M σ,
    (ctx_fn Δ M)[σ] = ctx_fn (tele_sub Δ σ) M[sb_qn (length Δ) σ].
Proof.
  induction Δ as [| [] Δ IH]; intros; cbn; [ reflexivity | | | |]; rewrite IH; cbn;
    first [ reflexivity | rewrite exp_sub_sub_extend_dm; reflexivity ].
Qed.

(** ** Bodies *)

(** A local import's placeholders are closed. *)
Lemma tele_wk_placeholders : forall n φ, tele_wk (repeat (ce_ass a_True) n) φ = repeat (ce_ass a_True) n.
Proof. induction n; intros; cbn; rewrite ?IHn; reflexivity. Qed.

Lemma body_ctx_wk : forall Φ φ, body_ctx (gmod_wk Φ φ) = tele_wk (body_ctx Φ) φ.
Proof.
  induction Φ as [| Φ IH x [? ? ? [] | | | | ] | Φ IH c]; intros; cbn; auto;
    rewrite ?tele_wk_app, ?tele_wk_placeholders, IH, ?length_body_ctx; reflexivity.
Qed.

(** A local import's placeholders are closed. *)
Lemma tele_sub_placeholders : forall n σ, tele_sub (repeat (ce_ass a_True) n) σ = repeat (ce_ass a_True) n.
Proof. induction n; intros; cbn; rewrite ?IHn; reflexivity. Qed.

Lemma body_ctx_sub : forall Φ σ, body_ctx (gmod_sub Φ σ) = tele_sub (body_ctx Φ) σ.
Proof.
  induction Φ as [| Φ IH x [? ? ? [] | | | | ] | Φ IH c]; intros; cbn; auto;
    rewrite ?tele_sub_app, ?tele_sub_placeholders, IH, ?length_body_ctx; reflexivity.
Qed.

Lemma gm_names_wk : forall Φ φ, gm_names (gmod_wk Φ φ) = gm_names Φ.
Proof. induction Φ; intros; cbn; rewrite ?IHΦ; reflexivity. Qed.

Lemma gm_names_sub : forall Φ σ, gm_names (gmod_sub Φ σ) = gm_names Φ.
Proof. induction Φ; intros; cbn; rewrite ?IHΦ; reflexivity. Qed.

Lemma gm_prefix_upto_wk : forall Φ x φ,
    gm_prefix_upto (gmod_wk Φ φ) x = option_map (fun Φ' => gmod_wk Φ' φ) (gm_prefix_upto Φ x).
Proof.
  induction Φ; intros; cbn; auto.
  - destruct (String.eqb x s); auto.
  - destruct (existsb _ _); auto.
Qed.

Lemma gm_prefix_upto_sub : forall Φ x σ,
    gm_prefix_upto (gmod_sub Φ σ) x = option_map (fun Φ' => gmod_sub Φ' σ) (gm_prefix_upto Φ x).
Proof.
  induction Φ; intros; cbn; auto.
  - destruct (String.eqb x s); auto.
  - destruct (existsb _ _); auto.
Qed.

Lemma gens_body_ctx_length : forall gs k, List.length (body_ctx (gens_append gm_nil k gs)) = List.length gs.
Proof. intros; rewrite length_body_ctx, gens_append_binders; cbn; lia. Qed.

(** The open that declares a name, in a weakened or substituted body. *)
Lemma gm_item_upto_wk : forall Φ x φ,
    gm_item_upto (gmod_wk Φ φ) x =
    option_map (fun r => match r with (Φ0, H, its1, it) => (gmod_wk Φ0 φ, modexp_wk H (wk_qn (gm_binders Φ0) φ), its1, it) end)
               (gm_item_upto Φ x).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros; cbn; auto.
  - destruct (String.eqb x y); auto.
  - destruct (items_upto x its) as [[its1 it] |]; auto.
Qed.

Lemma gm_item_upto_sub : forall Φ x σ,
    gm_item_upto (gmod_sub Φ σ) x =
    option_map (fun r => match r with (Φ0, H, its1, it) => (gmod_sub Φ0 σ, H[sb_qn (gm_binders Φ0) σ]ᵐ, its1, it) end)
               (gm_item_upto Φ x).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros; cbn; auto.
  - destruct (String.eqb x y); auto.
  - destruct (items_upto x its) as [[its1 it] |]; auto.
Qed.

(** *** Generated Entries under the Operations *)

Lemma generated_item_entry_wk : forall g φ, generated_item_entry (generated_item_wk g φ) = (fst (generated_item_entry g), gentry_wk (snd (generated_item_entry g)) φ).
Proof. destruct g; reflexivity. Qed.

Lemma generated_item_entry_sub : forall g σ, generated_item_entry (generated_item_sub g σ) = (fst (generated_item_entry g), gentry_sub (snd (generated_item_entry g)) σ).
Proof. destruct g; reflexivity. Qed.

Lemma wk_qn_shiftn_comm : forall k r φ, wk_eq (wk_shiftn k ⊙ wk_qn (r + k) φ) (wk_qn r φ ⊙ wk_shiftn k).
Proof.
  intros k r φ x; cbn [wk_compose wk_shiftn]; revert x; induction k as [| k IH]; intros x.
  - rewrite !Nat.add_0_r; reflexivity.
  - replace (r + S k) with (S (r + k)) by lia; replace (x + S k) with (S (x + k)) by lia.
    cbn [wk_qn wk_q]; rewrite IH; lia.
Qed.

(** The entries an open generates, after a weakening or a substitution of
    the body they extend: each is moved under the entries before it. *)
Lemma gens_append_wk : forall gs Φ k φ, k <= gm_binders Φ ->
    gmod_wk (gens_append Φ k gs) φ =
    gens_append (gmod_wk Φ φ) k (List.map (fun g => generated_item_wk g (wk_qn (gm_binders Φ - k) φ)) gs).
Proof.
  induction gs as [| g gs IH]; intros * Hk; cbn [gens_append List.map]; [ reflexivity |].
  rewrite generated_item_entry_wk; destruct (generated_item_entry g) as [d E] eqn:Eg; cbn [fst snd].
  rewrite IH by (cbn; lia); cbn [gmod_wk gm_binders].
  replace (S (gm_binders Φ) - S k) with (gm_binders Φ - k) by lia.
  do 2 f_equal; rewrite !gentry_wk_wk; apply gentry_wk_wk_eq.
  set (r := gm_binders Φ - k); replace (gm_binders Φ) with (r + k) by (subst r; lia); apply wk_qn_shiftn_comm.
Qed.

Lemma gens_append_sub : forall gs Φ k σ, k <= gm_binders Φ ->
    gmod_sub (gens_append Φ k gs) σ =
    gens_append (gmod_sub Φ σ) k (List.map (fun g => generated_item_sub g (sb_qn (gm_binders Φ - k) σ)) gs).
Proof.
  induction gs as [| g gs IH]; intros * Hk; cbn [gens_append List.map]; [ reflexivity |].
  rewrite generated_item_entry_sub; destruct (generated_item_entry g) as [d E] eqn:Eg; cbn [fst snd].
  rewrite IH by (cbn; lia); cbn [gmod_sub gm_binders].
  replace (S (gm_binders Φ) - S k) with (gm_binders Φ - k) by lia.
  do 2 f_equal; apply gentry_wk_sub_comm_ext; intros x.
  set (r := gm_binders Φ - k); replace (gm_binders Φ) with (k + r) by (subst r; lia).
  rewrite sb_qn_plus, sb_qn_ge by (cbn; lia); cbn [wk_shiftn]; replace (x + k - k) with x by lia; reflexivity.
Qed.

Lemma mod_qname_wk_eq : forall H φ, mod_qname (modexp_wk H φ) = mod_qname H.
Proof. induction H as [| | H IH y | H IH N |]; intros; cbn; rewrite ?IH; reflexivity. Qed.

(** The prefix of a body up to an entry is a prefix of its context. *)
Lemma gm_prefix_upto_body_ctx : forall Φ x Φx,
    gm_prefix_upto Φ x = Some Φx -> exists Ψ, body_ctx Φ = Ψ ++ body_ctx Φx.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros * H; cbn in H; try discriminate.
  - destruct (String.eqb x y); [ injection H as <-; exists nil; reflexivity |].
    destruct (IH _ _ H) as [Ψ HΨ]; cbn.
    destruct E as [? ? ? [] | | | | ]; rewrite HΨ; eexists (_ :: Ψ); reflexivity.
  - destruct (existsb _ _); [ discriminate |].
    destruct (IH _ _ H) as [Ψ HΨ]; cbn; rewrite HΨ, app_assoc; eexists; reflexivity.
Qed.

(** ** Module Expressions *)

Lemma member_ref_wk : forall ch H φ,
    (member_ref H ch)[φ]ʷ = member_ref (modexp_wk H φ) ch.
Proof. induction ch as [| x [| y ch] IH]; intros; cbn; auto; apply IH. Qed.

Lemma member_ref_sub : forall ch H σ,
    (member_ref H ch)[σ] = member_ref H[σ]ᵐ ch.
Proof. induction ch as [| x [| y ch] IH]; intros; cbn; auto; apply IH. Qed.

Lemma apps_wk : forall args M φ, (apps M args)[φ]ʷ = apps M[φ]ʷ (map (fun N => N[φ]ʷ) args).
Proof. induction args; intros; cbn; auto; apply IHargs. Qed.

Lemma apps_sub : forall args M σ, (apps M args)[σ] = apps M[σ] (map (fun N => N[σ]) args).
Proof. induction args; intros; cbn; auto; apply IHargs. Qed.

(** ** Chains from a Unit *)

Lemma mod_qname_wk : forall H p φ, mod_qname H = Some p -> modexp_wk H φ = H.
Proof.
  induction H as [fp | x | H IHH y | H IHH N | U]; intros * Hp; cbn in *; try discriminate; auto.
  destruct (mod_qname H) eqn:E; [ erewrite IHH; eauto | discriminate ].
Qed.

Lemma mod_qname_sub : forall H p σ, mod_qname H = Some p -> H[σ]ᵐ = H.
Proof.
  induction H as [fp | x | H IHH y | H IHH N | U]; intros * Hp; cbn in *; try discriminate; auto.
  destruct (mod_qname H) eqn:E; [ erewrite IHH; eauto | discriminate ].
Qed.

Lemma mod_qname_spine : forall H p, mod_qname H = Some p -> modexp_spine H = (me_unit (q_unit p), nil, q_chain p).
Proof.
  induction H as [fp | x | H IHH y | H IHH N | U]; intros * Hp; cbn in *; try discriminate.
  - injection Hp as <-; reflexivity.
  - destruct (mod_qname H) as [p0 |] eqn:E; [| discriminate ]; injection Hp as <-.
    rewrite (IHH _ eq_refl); reflexivity.
Qed.

Lemma mod_qname_noargs : forall H p, mod_qname H = Some p -> me_noargs H.
Proof.
  induction H as [fp | x | H IHH y | H IHH N | U]; intros * Hp; cbn in *; try discriminate; auto.
  destruct (mod_qname H) eqn:E; [ eauto | discriminate ].
Qed.

Lemma me_mems_app : forall pre1 pre2 H, me_mems H (pre1 ++ pre2) = me_mems (me_mems H pre1) pre2.
Proof. induction pre1; intros; cbn; auto. Qed.

Lemma mod_qname_mems : forall pre H p, mod_qname H = Some p ->
    mod_qname (me_mems H pre) = Some (q_abs (q_unit p) (q_chain p ++ pre)).
Proof.
  induction pre as [| y pre IH]; intros * Hp; cbn [me_mems].
  - rewrite Hp, app_nil_r; destruct p; reflexivity.
  - rewrite (IH _ (q_abs (q_unit p) (q_chain p ++ y :: nil))) by (cbn; rewrite Hp; reflexivity).
    cbn [q_unit q_chain]; rewrite <- app_assoc; reflexivity.
Qed.

Lemma me_mems_sub : forall pre H σ,
    H[σ]ᵐ = H -> (me_mems H pre)[σ]ᵐ = me_mems H pre.
Proof.
  induction pre as [| y pre IH]; intros * HH; cbn; [ exact HH |].
  apply IH; cbn; rewrite HH; reflexivity.
Qed.

Lemma qname_mod_sub : forall p σ, (qname_mod p)[σ]ᵐ = qname_mod p.
Proof. intros [fp ch] σ; apply me_mems_sub; reflexivity. Qed.

Lemma qname_mod_qname : forall p, mod_qname (qname_mod p) = Some p.
Proof.
  intros [fp ch]; unfold qname_mod; cbn [q_unit q_chain].
  rewrite (mod_qname_mems ch (me_unit fp) (q_abs fp nil) eq_refl); reflexivity.
Qed.

Lemma mod_qname_inv : forall H p, mod_qname H = Some p -> H = qname_mod p.
Proof.
  induction H as [fp | x | H IHH y | H IHH N | U]; intros * Hp; cbn in *; try discriminate.
  - injection Hp as <-; reflexivity.
  - destruct (mod_qname H) as [p0 |] eqn:E; [| discriminate ]; injection Hp as <-.
    rewrite (IHH _ eq_refl); unfold qname_mod; cbn [q_unit q_chain].
    rewrite me_mems_app; reflexivity.
Qed.

(** A root that a weakening or a same-unit substitution sends to a root. *)
Definition me_root (H : modexp) : Prop :=
  match H with
  | me_unit _ | me_var _ | me_lit _ => True
  | _ => False
  end.

Lemma modexp_spine_root : forall H R args pre, modexp_spine H = (R, args, pre) -> me_root R.
Proof.
  induction H; intros * Hs; cbn in Hs; try (injection Hs as <- <- <-; exact I);
    destruct (modexp_spine H) as [[R' args'] pre']; injection Hs as <- <- <-; eauto.
Qed.

Lemma modexp_spine_wk : forall H R args pre φ,
    modexp_spine H = (R, args, pre) ->
    modexp_spine (modexp_wk H φ) = (modexp_wk R φ, map (fun N => N[φ]ʷ) args, pre).
Proof.
  induction H as [| | H IHH y | H IHH N |]; intros * Hs; cbn in Hs |- *; try (injection Hs as <- <- <-; reflexivity).
  - destruct (modexp_spine H) as [[R' args'] pre'] eqn:E; injection Hs as <- <- <-.
    rewrite (IHH _ _ _ _ eq_refl); reflexivity.
  - destruct (modexp_spine H) as [[R' args'] pre'] eqn:E; injection Hs as <- <- <-.
    rewrite (IHH _ _ _ _ eq_refl), map_app; reflexivity.
Qed.

Lemma me_noargs_wk : forall H φ, me_noargs H -> me_noargs (modexp_wk H φ).
Proof. induction H; intros; cbn in *; auto. Qed.



(** ** The [Π] of a Type *)

Lemma pi_view_wk : forall A φ B C,
    pi_view A = Some (B, C) -> pi_view A[φ]ʷ = Some (B[φ]ʷ, C[wk_q φ]ʷ).
Proof.
  induction A; repeat match goal with H0 : list_all _ _ _ |- _ => clear H0 end; intros * H; try destruct b as [B0 N | U]; cbn in H |- *; try discriminate.
  - injection H as <- <-; reflexivity.
  - destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ].
    injection H as <- <-; rewrite (IHA _ _ _ eq_refl).
    f_equal; f_equal.
    + symmetry; apply exp_wk_sub_extend.
    + rewrite exp_wk_sub, exp_sub_wk; apply exp_sub_sb_eq.
      intros [| [| x]]; reduce_index; try reflexivity.
      cbn; f_equal; symmetry; apply exp_wk_shift_wk_q.
  - destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ].
    injection H as <- <-; rewrite (IHA _ _ _ eq_refl).
    f_equal; f_equal.
    + rewrite exp_wk_sub, exp_sub_wk; apply exp_sub_sb_eq; intros [| x]; reduce_index; reflexivity.
    + rewrite exp_wk_sub, exp_sub_wk; apply exp_sub_sb_eq.
      intros [| [| x]]; reduce_index; try reflexivity.
      cbn; f_equal; f_equal; symmetry; apply gunit_wk_shift_wk_q.
Qed.

Lemma pi_view_sub : forall A σ B C,
    pi_view A = Some (B, C) -> pi_view A[σ] = Some (B[σ], C[q σ]).
Proof.
  induction A; repeat match goal with H0 : list_all _ _ _ |- _ => clear H0 end; intros * H; try destruct b as [B0 N | U]; cbn in H |- *; try discriminate.
  - injection H as <- <-; reflexivity.
  - destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ].
    injection H as <- <-; rewrite (IHA _ _ _ eq_refl).
    f_equal; f_equal; rewrite !exp_sub_sub; apply exp_sub_sb_eq.
    + intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
    + rewrite !sb_q_compose; apply sb_q_cong.
      intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
  - destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ].
    injection H as <- <-; rewrite (IHA _ _ _ eq_refl).
    f_equal; f_equal; rewrite !exp_sub_sub; apply exp_sub_sb_eq.
    + intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
    + rewrite !sb_q_compose; apply sb_q_cong.
      intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
Qed.

(** ** Scoping of Member Types *)

Lemma ctx_scoped_lookup_mod : forall Γ x U n,
    ctx_scoped n Γ -> Γ ∋ #x ≔ₘ U -> gunit_scoped (length Γ + n) U.
Proof.
  intros * HΓ Hlk; induction Hlk; cbn in *; destruct_all;
    eapply gunit_scoped_wk; eauto; cbn; lia.
Qed.

Lemma ctx_scoped_placeholders : forall k n, ctx_scoped n (repeat (ce_ass a_True) k).
Proof. induction k; intros; cbn; auto. Qed.

Lemma gmod_scoped_body_ctx : forall Φ n, gmod_scoped n Φ -> ctx_scoped n (body_ctx Φ).
Proof.
  induction Φ as [| Φ IH x [? ? ? [] | | | | ] | Φ IH c]; intros * HΦ; cbn in *; destruct_all;
    try (apply ctx_scoped_app; split; [ apply ctx_scoped_placeholders | auto ]);
    repeat split; auto; rewrite length_body_ctx; assumption.
Qed.

Lemma gm_prefix_upto_scoped : forall Φ x Φx n,
    gm_prefix_upto Φ x = Some Φx -> gmod_scoped n Φ -> gmod_scoped n Φx.
Proof.
  induction Φ as [| Φ IH y E | Φ IH c]; intros * H HΦ; cbn in *; try discriminate; destruct_all.
  - destruct (String.eqb x y); [ injection H as <-; cbn; auto | eauto ].
  - destruct (existsb _ _); [ discriminate | eauto ].
Qed.

Lemma gentry_scoped_wk : forall E n m φ,
    gentry_scoped n E -> (forall x, x < n -> φ x < m) -> gentry_scoped m (gentry_wk E φ).
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_wk))))))). Qed.

(** The entries an open generates, each scoped in the context of the open,
    extend a scoped body. *)
Lemma gens_append_scoped : forall gs Φ k n, gmod_scoped n Φ -> k <= gm_binders Φ ->
    List.Forall (fun g => gentry_scoped (gm_binders Φ - k + n) (snd (generated_item_entry g))) gs ->
    gmod_scoped n (gens_append Φ k gs).
Proof.
  induction gs as [| g gs IH]; intros * HΦ Hk Hg; cbn [gens_append]; [ assumption |].
  inversion Hg as [| ? ? Hg1 Hgs]; subst.
  destruct (generated_item_entry g) as [d E] eqn:Eg; cbn [snd] in Hg1.
  apply IH; [ cbn; split; [ assumption | eapply gentry_scoped_wk; [ exact Hg1 | cbn; lia ] ] | cbn; lia |].
  cbn [gm_binders]; replace (S (gm_binders Φ) - S k) with (gm_binders Φ - k) by lia; exact Hgs.
Qed.

Lemma pi_view_scoped : forall A B C n,
    pi_view A = Some (B, C) -> exp_scoped n A -> exp_scoped n B /\ exp_scoped (S n) C.
Proof.
  induction A; repeat match goal with H0 : list_all _ _ _ |- _ => clear H0 end; intros * H HA; try destruct b as [B0 N | U]; cbn in H, HA; try discriminate; destruct_all.
  - injection H as <- <-; auto.
  - destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ]; injection H as <- <-.
    destruct (IHA _ _ _ eq_refl H1) as [HB HC]; split.
    + eapply exp_scoped_sub; [ eassumption |]; intros [| x] ?; reduce_index; cbn [sentry_scoped wk_shift]; auto; lia.
    + eapply exp_scoped_sub; [ eassumption |].
      intros [| [| x]] ?; reduce_index; cbn [sentry_scoped wk_shift]; try lia.
      eapply exp_scoped_wk; [ eassumption |]; cbn; lia.
  - destruct (pi_view A) as [[B' C'] |] eqn:E; [| discriminate ]; injection H as <- <-.
    destruct (IHA _ _ _ eq_refl H1) as [HB HC]; split.
    + eapply exp_scoped_sub; [ eassumption |]; intros [| x] ?; reduce_index; cbn [sentry_scoped wk_shift]; auto; lia.
    + eapply exp_scoped_sub; [ eassumption |].
      intros [| [| x]] ?; reduce_index; cbn [sentry_scoped wk_shift]; try lia.
      eapply gunit_scoped_wk; [ eassumption |]; cbn; lia.
Qed.

(** ** Arities

    [tele_view] is read on the reversed telescope; these lemmas move the
    operations through the reversal, an entry at a time from the outside. *)

Lemma ctx_pi_app : forall T Δ A, ctx_pi (T ++ Δ) A = ctx_pi Δ (ctx_pi T A).
Proof. induction T as [| [] T IH]; intros; cbn; auto. Qed.

Lemma ctx_pi_rev_cons : forall e R A,
    ctx_pi (rev (e :: R)) A =
    match e with
    | ce_ass B => a_pi B (ctx_pi (rev R) A)
    | ce_def B N => a_let (b_def (Some B) N) (ctx_pi (rev R) A)
    | ce_mod U => a_let (b_mod U) (ctx_pi (rev R) A)
    | ce_dm _ N U => (ctx_pi (rev R) A)[Id ,,ᵈ N ‖ me_lit U]
    end.
Proof. intros; cbn [rev]; rewrite ctx_pi_app; destruct e; reflexivity. Qed.

(** The [Π] an arity type is, substituted. *)
Lemma pi_view_ctx_pi_sub : forall R σ,
    pi_view (ctx_pi (rev R) a_True)[σ] =
    option_map (fun BC => ((fst BC)[σ], (snd BC)[q σ])) (pi_view (ctx_pi (rev R) a_True)).
Proof.
  induction R as [| e R IH]; intros σ; [ reflexivity |].
  rewrite !ctx_pi_rev_cons; destruct e as [B | B N | U | B N U].
  - reflexivity.
  - cbn [exp_sub bnd_sub pi_view option_map]; rewrite IH.
    destruct (pi_view (ctx_pi (rev R) a_True)) as [[B' C'] |]; cbn; [| reflexivity ].
    f_equal; f_equal; [ apply (exp_sub_extend_comm_gen _ _ (se_exp N)) | apply (exp_sub_q_extend_comm_gen _ _ (se_exp N)) ].
  - cbn [exp_sub bnd_sub pi_view option_map]; rewrite IH.
    destruct (pi_view (ctx_pi (rev R) a_True)) as [[B' C'] |]; cbn; [| reflexivity ].
    f_equal; f_equal;
      [ apply (exp_sub_extend_comm_gen _ _ (se_mod (me_lit U))) | apply (exp_sub_q_extend_comm_gen _ _ (se_mod (me_lit U))) ].
  - rewrite exp_sub_sub_extend_dm, (exp_sub_sub _ (q σ)), IH, IH.
    destruct (pi_view (ctx_pi (rev R) a_True)) as [[B' C'] |]; cbn; [| reflexivity ].
    f_equal; f_equal.
    + rewrite <- exp_sub_sub; apply (exp_sub_extend_comm_gen _ _ (se_dm N (me_lit U))).
    + rewrite <- (exp_sub_sb_eq _ _ _ (sb_q_compose _ _)), <- exp_sub_sub.
      apply (exp_sub_q_extend_comm_gen _ _ (se_dm N (me_lit U))).
Qed.

(** The [Π] the arity type of a telescope is, is its outermost parameter. *)
Lemma tele_view_pi : forall T,
    pi_view (ctx_pi T a_True) = option_map (fun BT => (fst BT, ctx_pi (snd BT) a_True)) (tele_view T).
Proof.
  intros T; unfold tele_view; rewrite <- (rev_involutive T) at 1; generalize (rev T) as R; clear T.
  induction R as [| [B | B N | U | B N U] R IH]; [ reflexivity | | | |]; rewrite ctx_pi_rev_cons; cbn [pi_view tele_open].
  - reflexivity.
  - rewrite IH; destruct (tele_open R) as [[B' T'] |]; cbn; [ rewrite ctx_pi_sub; reflexivity | reflexivity ].
  - rewrite IH; destruct (tele_open R) as [[B' T'] |]; cbn; [ rewrite ctx_pi_sub; reflexivity | reflexivity ].
  - rewrite pi_view_ctx_pi_sub, IH; destruct (tele_open R) as [[B' T'] |]; cbn; [ rewrite ctx_pi_sub; reflexivity | reflexivity ].
Qed.

Lemma tele_wk_rev_cons : forall e R φ,
    tele_wk (rev (e :: R)) φ = rev (centry_wk e φ :: rev (tele_wk (rev R) (wk_q φ))).
Proof.
  intros; cbn [rev]; rewrite tele_wk_app, rev_involutive; cbn; reflexivity.
Qed.

Lemma tele_sub_rev_cons : forall e R σ,
    tele_sub (rev (e :: R)) σ = rev (centry_sub e σ :: rev (tele_sub (rev R) (q σ))).
Proof.
  intros; cbn [rev]; rewrite tele_sub_app, rev_involutive; cbn; reflexivity.
Qed.

Lemma tele_view_wk : forall T φ,
    tele_view (tele_wk T φ) = option_map (fun BT => ((fst BT)[φ]ʷ, tele_wk (snd BT) (wk_q φ))) (tele_view T).
Proof.
  intros T; unfold tele_view; rewrite <- (rev_involutive T); generalize (rev T) as R; clear T.
  induction R as [| [B | B N | U | B N U] R IH]; intros φ; [ reflexivity | | | |];
    rewrite tele_wk_rev_cons, !rev_involutive; cbn [centry_wk tele_open].
  - rewrite rev_involutive; reflexivity.
  - specialize (IH (wk_q φ)); rewrite rev_involutive in IH; rewrite IH.
    destruct (tele_open R) as [[B' T'] |]; cbn; [| reflexivity ].
    f_equal; f_equal.
    + symmetry; apply exp_wk_sub_extend.
    + rewrite tele_wk_sub, <- tele_sub_of_wk, tele_sub_sub; apply tele_sub_sb_eq.
      intros [| [| x]]; reduce_index; try reflexivity.
      cbn; f_equal; symmetry; apply exp_wk_shift_wk_q.
  - specialize (IH (wk_q φ)); rewrite rev_involutive in IH; rewrite IH.
    destruct (tele_open R) as [[B' T'] |]; cbn; [| reflexivity ].
    f_equal; f_equal.
    + rewrite exp_wk_sub, exp_sub_wk; apply exp_sub_sb_eq; intros [| x]; reduce_index; reflexivity.
    + rewrite tele_wk_sub, <- tele_sub_of_wk, tele_sub_sub; apply tele_sub_sb_eq.
      intros [| [| x]]; reduce_index; try reflexivity.
      cbn; f_equal; f_equal; symmetry; apply gunit_wk_shift_wk_q.
  - specialize (IH (wk_q φ)); rewrite rev_involutive in IH; rewrite IH.
    destruct (tele_open R) as [[B' T'] |]; cbn; [| reflexivity ].
    f_equal; f_equal.
    + rewrite exp_wk_sub, exp_sub_wk; apply exp_sub_sb_eq; intros [| x]; reduce_index; reflexivity.
    + rewrite tele_wk_sub, <- tele_sub_of_wk, tele_sub_sub; apply tele_sub_sb_eq.
      intros [| [| x]]; reduce_index; try reflexivity.
      cbn; f_equal; [ symmetry; apply exp_wk_shift_wk_q | f_equal; symmetry; apply gunit_wk_shift_wk_q ].
Qed.

Lemma tele_view_sub : forall T σ,
    tele_view (tele_sub T σ) = option_map (fun BT => ((fst BT)[σ], tele_sub (snd BT) (q σ))) (tele_view T).
Proof.
  intros T; unfold tele_view; rewrite <- (rev_involutive T); generalize (rev T) as R; clear T.
  induction R as [| [B | B N | U | B N U] R IH]; intros σ; [ reflexivity | | | |];
    rewrite tele_sub_rev_cons, !rev_involutive; cbn [centry_sub tele_open].
  - rewrite rev_involutive; reflexivity.
  - specialize (IH (q σ)); rewrite rev_involutive in IH; rewrite IH.
    destruct (tele_open R) as [[B' T'] |]; cbn; [| reflexivity ].
    f_equal; f_equal; rewrite ?exp_sub_sub, ?tele_sub_sub; [ apply exp_sub_sb_eq | apply tele_sub_sb_eq ].
    + intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
    + rewrite !sb_q_compose; apply sb_q_cong.
      intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
  - specialize (IH (q σ)); rewrite rev_involutive in IH; rewrite IH.
    destruct (tele_open R) as [[B' T'] |]; cbn; [| reflexivity ].
    f_equal; f_equal; rewrite ?exp_sub_sub, ?tele_sub_sub; [ apply exp_sub_sb_eq | apply tele_sub_sb_eq ].
    + intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
    + rewrite !sb_q_compose; apply sb_q_cong.
      intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
  - specialize (IH (q σ)); rewrite rev_involutive in IH; rewrite IH.
    destruct (tele_open R) as [[B' T'] |]; cbn; [| reflexivity ].
    f_equal; f_equal; rewrite ?exp_sub_sub, ?tele_sub_sub; [ apply exp_sub_sb_eq | apply tele_sub_sb_eq ].
    + intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
    + rewrite !sb_q_compose; apply sb_q_cong.
      intros [| x]; reduce_index; [ reflexivity |].
      rewrite sentry_sub_shift_extend; apply sentry_sub_id.
Qed.

Lemma ctx_scoped_rev_cons : forall e R n,
    ctx_scoped n (rev (e :: R)) <-> ce_scoped n e /\ ctx_scoped (S n) (rev R).
Proof. intros; cbn [rev]; rewrite ctx_scoped_app; cbn; tauto. Qed.

Lemma tele_view_scoped : forall T B T' n,
    tele_view T = Some (B, T') -> ctx_scoped n T -> exp_scoped n B /\ ctx_scoped (S n) T'.
Proof.
  intros T; unfold tele_view; rewrite <- (rev_involutive T); generalize (rev T) as R; clear T.
  intros R; rewrite rev_involutive; induction R as [| [B0 | B0 N | U | B0 N U] R IH]; intros * Hv HT;
    cbn [tele_open] in Hv; [ discriminate | | | |];
    apply ctx_scoped_rev_cons in HT as [He HR]; cbn in He; destruct_all.
  - injection Hv as <- <-; auto.
  - destruct (tele_open R) as [[B' T0] |] eqn:E; [| discriminate ]; injection Hv as <- <-.
    destruct (IH _ _ _ eq_refl HR) as [HB HT0]; split.
    + apply exp_scoped_sub1; assumption.
    + eapply tele_sub_scoped; [ eassumption |].
      apply sb_q_bound; intros [| x] ?; cbn; auto; lia.
  - destruct (tele_open R) as [[B' T0] |] eqn:E; [| discriminate ]; injection Hv as <- <-.
    destruct (IH _ _ _ eq_refl HR) as [HB HT0]; split.
    + apply exp_scoped_sub1_mod; cbn; assumption.
    + eapply tele_sub_scoped; [ eassumption |].
      apply sb_q_bound; intros [| x] ?; cbn; auto; lia.
  - destruct (tele_open R) as [[B' T0] |] eqn:E; [| discriminate ]; injection Hv as <- <-.
    destruct (IH _ _ _ eq_refl HR) as [HB HT0]; split.
    + apply exp_scoped_sub1_dm; cbn; assumption.
    + eapply tele_sub_scoped; [ eassumption |].
      apply sb_q_bound; intros [| x] ?; cbn; [ split; assumption | lia ].
Qed.

Lemma ctx_scoped_closed : forall T n, ctx_scoped 0 T -> ctx_scoped n T.
Proof.
  intros * HT; rewrite <- (tele_closed_wk T (fun x => x) HT).
  eapply tele_wk_scoped; [ exact HT | lia ].
Qed.

Lemma ctx_scoped_mono' : forall Δ n m, n <= m -> ctx_scoped n Δ -> ctx_scoped m Δ.
Proof.
  induction Δ as [| e Δ IH]; intros * Hle HΔ; cbn in *; [ exact I |]; destruct HΔ as [He HΔ].
  split; [| eauto ].
  eapply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_mono))))))); [| exact He ]; lia.
Qed.

(** *** Descriptions

    A description is scoped at [n] when its parts are: a closed module's
    stored unit is closed ([unit_closed]), and its arguments and an
    inductive type's are terms over the outside parameters. *)

(** [ds_scoped n R]: the description [R] is scoped at [n]. *)
Fixpoint ds_scoped (n : nat) (R : mdesc) : Prop :=
  match R with
  | ds_term A om => exp_scoped n A /\ opt_scoped n om
  | ds_open Δ Φ Φx => gunit_scoped n (gu_open Δ Φ) /\ gunit_scoped n (gu_open Δ Φx)
  | ds_closed Θ _ T Φ Ns => ctx_scoped n Θ /\ unit_closed T Φ /\ List.Forall (exp_scoped (length Θ + n)) Ns
  | ds_dm Θd A M Rm =>
      ctx_scoped n Θd /\ (exp_scoped (length Θd + n) A /\ exp_scoped (length Θd + n) M) /\ ds_scoped n Rm
  end.

(** Scoped at [n], a description is scoped further out. *)
Lemma ds_scoped_mono : forall R n m, n <= m -> ds_scoped n R -> ds_scoped m R.
Proof.
  induction R as [A om | Δ Φ Φx | Θ0 ? T Φ Ns0 | Θ0 A M Rm IH]; intros * Hle HR; cbn in *.
  - destruct HR as [HA Hom]; split; [ eapply exp_scoped_mono; [| exact HA ]; lia |].
    destruct om; cbn in *; [ eapply exp_scoped_mono; [| exact Hom ]; lia | exact I ].
  - destruct HR as [HR1 HR2]; split; [ eapply gunit_scoped_mono; [| exact HR1 ] | eapply gunit_scoped_mono; [| exact HR2 ] ]; lia.
  - destruct HR as (HΘ0 & HU & HNs0); split; [ eapply ctx_scoped_mono'; [| exact HΘ0 ]; lia | split; [ exact HU |] ].
    eapply List.Forall_impl; [| exact HNs0 ]; intros; eapply exp_scoped_mono; [| eassumption ]; lia.
  - destruct HR as (HΘ0 & [HA HM] & HRm); split; [ eapply ctx_scoped_mono'; [| exact HΘ0 ]; lia |].
    split; [ split; eapply exp_scoped_mono; [| exact HA | | exact HM ]; lia | exact (IH _ _ Hle HRm) ].
Qed.

Lemma sentry_scoped_sub : forall e m k σ,
    sentry_scoped m e -> (forall x, x < m -> sentry_scoped k (σ x)) -> sentry_scoped k (sentry_sub e σ).
Proof.
  intros [x | M | H | M H] * He Hσ; cbn in *;
    [ auto | eapply exp_scoped_sub; eauto | eapply modexp_scoped_sub; eauto
    | destruct He; split; [ eapply exp_scoped_sub | eapply modexp_scoped_sub ]; eauto ].
Qed.

Lemma sb_compose_bound : forall σ τ a b c,
    (forall x, x < a -> sentry_scoped b (σ x)) -> (forall x, x < b -> sentry_scoped c (τ x)) ->
    forall x, x < a -> sentry_scoped c ((σ ⨟ τ) x).
Proof. intros * Hσ Hτ x Hx; cbn; eapply sentry_scoped_sub; eauto. Qed.

Lemma sb_id_ext_bound : forall N n, exp_scoped n N -> forall x, x < S n -> sentry_scoped n ((Id,,N) x).
Proof. intros * HN [| x] Hx; cbn; [ exact HN | lia ]. Qed.

Lemma sb_id_extm_bound : forall U n, gunit_scoped n U -> forall x, x < S n -> sentry_scoped n ((Id ,,ₘ me_lit U) x).
Proof. intros * HU [| x] Hx; cbn; [ exact HU | lia ]. Qed.

Lemma sb_id_extdm_bound : forall N U n, exp_scoped n N -> gunit_scoped n U ->
    forall x, x < S n -> sentry_scoped n ((Id ,,ᵈ N ‖ me_lit U) x).
Proof. intros * HN HU [| x] Hx; cbn; [ split; assumption | lia ]. Qed.

Lemma ctx_scoped_rev_cons_iff : forall e R n,
    ctx_scoped n (rev (e :: R)) <-> ce_scoped n e /\ ctx_scoped (S n) (rev R).
Proof. exact ctx_scoped_rev_cons. Qed.

(** The outermost assumption of a scoped telescope, the rest, and the
    substitution are scoped. *)
Lemma tele_split_scoped : forall R n, ctx_scoped n (rev R) ->
    (forall B T τ, tele_split R = inl (B, T, τ) ->
       exp_scoped n B /\ ctx_scoped (S n) T /\ forall x, x < length R + n -> sentry_scoped (length T + S n) (τ x)) /\
    (forall τ, tele_split R = inr τ -> forall x, x < length R + n -> sentry_scoped n (τ x)).
Proof.
  induction R as [| [B0 | B0 N | U | B0 N U] R IH]; intros n HR; cbn [tele_split]; split.
  - discriminate.
  - intros τ [= <-] x Hx; cbn in *; lia.
  - intros * [= <- <- <-]; apply ctx_scoped_rev_cons in HR as [HB HR]; cbn in HB.
    split; [ exact HB | split; [ exact HR | intros x Hx; cbn in *; rewrite length_rev; lia ] ].
  - discriminate.
  - apply ctx_scoped_rev_cons in HR as [HN HR]; cbn in HN; destruct HN as [HB0 HN].
    destruct (IH (S n) HR) as [IHl _].
    intros * Hs; destruct (tele_split R) as [[[B' T'] τ'] |] eqn:E; [| discriminate ].
    injection Hs as <- <- <-.
    destruct (IHl _ _ _ eq_refl) as (HB' & HT' & Hτ'); split; [| split ].
    + apply exp_scoped_sub1; assumption.
    + eapply tele_sub_scoped; [ eassumption |]; apply sb_q_bound, sb_id_ext_bound, HN.
    + intros x Hx; rewrite length_tele_sub.
      eapply sb_compose_bound; [ intros y Hy; apply Hτ'; exact Hy | | cbn [length] in Hx; lia ].
      replace (length T' + S (S n)) with (S (length T') + S n) by lia.
      replace (length T' + S n) with (S (length T') + n) by lia.
      apply (sb_qn_bound (S (length T'))), sb_id_ext_bound, HN.
  - apply ctx_scoped_rev_cons in HR as [HN HR]; cbn in HN; destruct HN as [HB0 HN].
    destruct (IH (S n) HR) as [_ IHr].
    intros * Hs; destruct (tele_split R) as [[[B' T'] τ'] |] eqn:E; [ discriminate |].
    injection Hs as <-; intros x Hx.
    eapply sb_compose_bound; [ intros y Hy; apply IHr; [ reflexivity | exact Hy ] | apply sb_id_ext_bound, HN | cbn [length] in Hx; lia ].
  - apply ctx_scoped_rev_cons in HR as [HU HR]; cbn in HU.
    destruct (IH (S n) HR) as [IHl _].
    intros * Hs; destruct (tele_split R) as [[[B' T'] τ'] |] eqn:E; [| discriminate ].
    injection Hs as <- <- <-.
    destruct (IHl _ _ _ eq_refl) as (HB' & HT' & Hτ'); split; [| split ].
    + apply exp_scoped_sub1_mod; cbn; assumption.
    + eapply tele_sub_scoped; [ eassumption |]; apply sb_q_bound, sb_id_extm_bound, HU.
    + intros x Hx; rewrite length_tele_sub.
      eapply sb_compose_bound; [ intros y Hy; apply Hτ'; exact Hy | | cbn [length] in Hx; lia ].
      replace (length T' + S (S n)) with (S (length T') + S n) by lia.
      replace (length T' + S n) with (S (length T') + n) by lia.
      apply (sb_qn_bound (S (length T'))), sb_id_extm_bound, HU.
  - apply ctx_scoped_rev_cons in HR as [HU HR]; cbn in HU.
    destruct (IH (S n) HR) as [_ IHr].
    intros * Hs; destruct (tele_split R) as [[[B' T'] τ'] |] eqn:E; [ discriminate |].
    injection Hs as <-; intros x Hx.
    eapply sb_compose_bound; [ intros y Hy; apply IHr; [ reflexivity | exact Hy ] | apply sb_id_extm_bound, HU | cbn [length] in Hx; lia ].
  - apply ctx_scoped_rev_cons in HR as [HU HR]; cbn in HU; destruct HU as (HB0 & HN & HU).
    destruct (IH (S n) HR) as [IHl _].
    intros * Hs; destruct (tele_split R) as [[[B' T'] τ'] |] eqn:E; [| discriminate ].
    injection Hs as <- <- <-.
    destruct (IHl _ _ _ eq_refl) as (HB' & HT' & Hτ'); split; [| split ].
    + apply exp_scoped_sub1_dm; cbn; assumption.
    + eapply tele_sub_scoped; [ eassumption |]; apply sb_q_bound, sb_id_extdm_bound; assumption.
    + intros x Hx; rewrite length_tele_sub.
      eapply sb_compose_bound; [ intros y Hy; apply Hτ'; exact Hy | | cbn [length] in Hx; lia ].
      replace (length T' + S (S n)) with (S (length T') + S n) by lia.
      replace (length T' + S n) with (S (length T') + n) by lia.
      apply (sb_qn_bound (S (length T'))), sb_id_extdm_bound; assumption.
  - apply ctx_scoped_rev_cons in HR as [HU HR]; cbn in HU; destruct HU as (HB0 & HN & HU).
    destruct (IH (S n) HR) as [_ IHr].
    intros * Hs; destruct (tele_split R) as [[[B' T'] τ'] |] eqn:E; [ discriminate |].
    injection Hs as <-; intros x Hx.
    eapply sb_compose_bound;
      [ intros y Hy; apply IHr; [ reflexivity | exact Hy ] | apply sb_id_extdm_bound; assumption | cbn [length] in Hx; lia ].
Qed.

Lemma fn_view_scoped : forall M M' n, fn_view M = Some M' -> exp_scoped n M -> exp_scoped (S n) M'.
Proof.
  induction M; repeat match goal with H0 : list_all _ _ _ |- _ => clear H0 end; intros * H HM; try destruct b as [B0 N | U]; cbn in H, HM; try discriminate; destruct_all.
  - injection H as <-; assumption.
  - destruct (fn_view M) as [M0 |] eqn:E; [| discriminate ]; injection H as <-.
    eapply exp_scoped_sub; [ apply IHM; [ reflexivity | eassumption ] |].
    apply sb_q_bound, sb_id_ext_bound; assumption.
  - destruct (fn_view M) as [M0 |] eqn:E; [| discriminate ]; injection H as <-.
    eapply exp_scoped_sub; [ apply IHM; [ reflexivity | eassumption ] |].
    apply sb_q_bound, sb_id_extm_bound; assumption.
Qed.

Lemma map_sub_scoped : forall Ns σ a b,
    List.Forall (exp_scoped a) Ns -> (forall x, x < a -> sentry_scoped b (σ x)) ->
    List.Forall (exp_scoped b) (List.map (fun M => M[σ]) Ns).
Proof.
  intros * HNs Hσ; apply List.Forall_map; eapply List.Forall_impl; [| exact HNs ].
  intros M HM; eapply exp_scoped_sub; eassumption.
Qed.

Lemma open_at_scoped : forall Δ Φ N n B Δ' τ,
    gunit_scoped n (gu_open Δ Φ) -> exp_scoped n N -> tele_split (rev Δ) = inl (B, Δ', τ) ->
    gunit_scoped n (gu_open (tele_sub Δ' (Id,,N)) (gmod_sub Φ (τ ⨟ sb_qn (List.length Δ') (Id,,N)))).
Proof.
  intros * HR HN E.
  rewrite gunit_scoped_mk in HR; destruct HR as [HΔ [_ HΦ]].
  rewrite <- (rev_involutive Δ) in HΔ.
  destruct (tele_split_scoped (rev Δ) n HΔ) as [Hl _].
  destruct (Hl _ _ _ E) as (_ & HΔ' & Hτ); cbn.
  apply gunit_scoped_mk; split; [ eapply tele_sub_scoped; [ eassumption | apply sb_id_ext_bound, HN ] |].
  split; [ reflexivity |]; rewrite length_tele_sub.
  eapply syn_scoped_sub; [ eassumption |].
  eapply sb_compose_bound; [ intros x Hx; apply Hτ; rewrite length_rev; exact Hx |].
  apply sb_qn_bound, sb_id_ext_bound, HN.
Qed.

Lemma ds_at_scoped : forall R N R' n,
    ds_scoped n R -> exp_scoped n N -> ds_at R N = Some R' -> ds_scoped n R'.
Proof.
  induction R as [A om | Δ Φ Φx | Θ ? T Φ Ns | Θ A M Rm IHR]; intros * HR HN Ha; cbn in HR, Ha.
  - destruct HR as [HA Hom].
    destruct (pi_view A) as [[B C] |] eqn:E; [| discriminate ].
    destruct (pi_view_scoped _ _ _ _ E HA) as [_ HC].
    destruct om as [M |]; [ destruct (fn_view M) as [M' |] eqn:Ef; [| discriminate ] |]; injection Ha as <-; cbn.
    + split; [ apply exp_scoped_sub1; assumption |].
      apply exp_scoped_sub1; [ eapply fn_view_scoped; eassumption | assumption ].
    + split; [ apply exp_scoped_sub1; assumption | exact I ].
  - destruct HR as [HR1 HR2].
    destruct (tele_split (rev Δ)) as [[[B Δ'] τ] |] eqn:E; [| discriminate ]; injection Ha as <-.
    split; eapply open_at_scoped; eassumption.
  - destruct HR as (HΘ & HU & HNs).
    rewrite <- (rev_involutive Θ) in HΘ.
    destruct (tele_split_scoped (rev Θ) n HΘ) as [Hl Hr].
    destruct (tele_split (rev Θ)) as [[[B Θ'] τ] |] eqn:E; injection Ha as <-; cbn.
    + destruct (Hl _ _ _ eq_refl) as (_ & HΘ' & Hτ).
      split; [ eapply tele_sub_scoped; [ eassumption | apply sb_id_ext_bound, HN ] | split; [ exact HU |] ].
      rewrite length_tele_sub; eapply map_sub_scoped; [ exact HNs |].
      eapply sb_compose_bound; [ intros x Hx; apply Hτ; rewrite length_rev; exact Hx |].
      apply sb_qn_bound, sb_id_ext_bound, HN.
    + split; [ exact I | split; [ exact HU |] ].
      apply List.Forall_app; split; [| constructor; [ exact HN | constructor ] ].
      eapply map_sub_scoped; [ exact HNs |]; intros x Hx; apply (Hr _ eq_refl); rewrite length_rev; exact Hx.
  - destruct HR as (HΘ & [HA HM] & HRm).
    destruct (ds_at Rm N) as [Rm' |] eqn:Er; [| discriminate ].
    pose proof (IHR _ _ _ HRm HN Er) as HRm'.
    rewrite <- (rev_involutive Θ) in HΘ.
    destruct (tele_split_scoped (rev Θ) n HΘ) as [Hl _].
    destruct (tele_split (rev Θ)) as [[[B Θ'] τ] | τ] eqn:E; injection Ha as <-; [ cbn | exact HRm' ].
    destruct (Hl _ _ _ eq_refl) as (_ & HΘ' & Hτ).
    assert (Hb : forall x, x < length Θ + n -> sentry_scoped (length (tele_sub Θ' (Id,,N)) + n) ((τ ⨟ sb_qn (length Θ') (Id,,N)) x)).
    { rewrite length_tele_sub; eapply sb_compose_bound; [ intros x Hx; apply Hτ; rewrite length_rev; exact Hx |].
      apply sb_qn_bound, sb_id_ext_bound, HN. }
    split; [ eapply tele_sub_scoped; [ eassumption | apply sb_id_ext_bound, HN ] |].
    split; [ split; eapply exp_scoped_sub; eassumption | exact HRm' ].
Qed.

Lemma ds_ats_scoped : forall Ns R R' n,
    ds_scoped n R -> List.Forall (exp_scoped n) Ns -> ds_ats R Ns = Some R' -> ds_scoped n R'.
Proof.
  induction Ns as [| N Ns IH]; intros * HR HNs Ha; cbn in Ha; [ injection Ha as <-; exact HR |].
  inversion HNs; subst.
  destruct (ds_at R N) as [R0 |] eqn:E; [| discriminate ].
  eapply IH; [ eapply ds_at_scoped; eassumption | assumption | exact Ha ].
Qed.

(** A type former applied is no [λ]. *)
Lemma app_const_fn_view : forall M, app_const M = true -> fn_view M = None.
Proof. intros M H; destruct M; cbn in H |- *; try discriminate; reflexivity. Qed.

(** Nor does a substitution make it one. *)
Lemma app_const_sub : forall M σ, app_const M = true -> app_const M[σ] = true.
Proof. fix IH 1; intros M σ H; destruct M; cbn in H |- *; try discriminate; try reflexivity; apply IH; exact H. Qed.

(** [ds_at_tm] extends [ds_at]. *)
Lemma ds_at_tm_of_at : forall R N R', ds_at R N = Some R' -> ds_at_tm R N = Some R'.
Proof.
  intros [A [M |] | | |] N R' Ha; cbn [ds_at_tm]; try exact Ha.
  cbn in Ha |- *; destruct (pi_view A) as [[? ?] |]; [| discriminate ].
  destruct (fn_view M); [ exact Ha | discriminate ].
Qed.

(** So [ds_ats_tm] extends [ds_ats], argument by argument. *)
Lemma ds_ats_tm_of_ats : forall Ns R R', ds_ats R Ns = Some R' -> ds_ats_tm R Ns = Some R'.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha |- *; [ exact Ha |].
  destruct (ds_at R N) as [R0 |] eqn:E; [| discriminate ].
  rewrite (ds_at_tm_of_at _ _ _ E); exact (IH _ _ Ha).
Qed.

(** A scoped description given a scoped argument by [ds_at_tm] is scoped:
    by [β] as [ds_at], or a type former applied to the argument. *)
Lemma ds_at_tm_scoped : forall R N R' n,
    ds_scoped n R -> exp_scoped n N -> ds_at_tm R N = Some R' -> ds_scoped n R'.
Proof.
  intros [A [M |] | | |] * HR HN Ha; cbn [ds_at_tm] in Ha; try (eapply ds_at_scoped; eassumption).
  destruct HR as [HA HM]; destruct (pi_view A) as [[B C] |] eqn:E; [| discriminate ].
  destruct (pi_view_scoped _ _ _ _ E HA) as [_ HC].
  destruct (fn_view M) as [M' |] eqn:Ef; [| destruct (app_const M); [| discriminate ] ]; injection Ha as <-; cbn.
  - split; [ apply exp_scoped_sub1; assumption |].
    apply exp_scoped_sub1; [ eapply fn_view_scoped; eassumption | assumption ].
  - split; [ apply exp_scoped_sub1; assumption | split; assumption ].
Qed.

(** So is one given scoped arguments by [ds_ats_tm]. *)
Lemma ds_ats_tm_scoped : forall Ns R R' n,
    ds_scoped n R -> List.Forall (exp_scoped n) Ns -> ds_ats_tm R Ns = Some R' -> ds_scoped n R'.
Proof.
  induction Ns as [| N Ns IH]; intros * HR HNs Ha; cbn in Ha; [ injection Ha as <-; exact HR |].
  inversion HNs; subst.
  destruct (ds_at_tm R N) as [R0 |] eqn:E; [| discriminate ].
  eapply IH; [ eapply ds_at_tm_scoped; eassumption | assumption | exact Ha ].
Qed.

Lemma ds_up_scoped : forall Θ' R n,
    ctx_scoped n Θ' -> ds_scoped (length Θ' + n) R -> ds_scoped n (ds_up Θ' R).
Proof.
  intros Θ' R; induction R as [A om | Δ Φ Φx | Θ ? T Φ Ns | Θd A M Rm IHR]; intros n HΘ HR; cbn in *.
  - destruct HR as [HA Hom]; split; [ apply ctx_pi_scoped; assumption |].
    destruct om; cbn in *; [ apply ctx_fn_scoped; assumption | exact I ].
  - rewrite !gunit_scoped_mk in *; destruct HR as [[HΔ HD] [_ HD']];
      split; (split; [ apply ctx_scoped_app; split; assumption |]); rewrite length_app, <- Nat.add_assoc; assumption.
  - destruct HR as (HΘ0 & HU & HNs); split; [ apply ctx_scoped_app; split; assumption | split; [ exact HU |] ].
    rewrite length_app, <- Nat.add_assoc; exact HNs.
  - destruct HR as (HΘ0 & HAM & HRm); rewrite length_app, <- Nat.add_assoc.
    split; [ apply ctx_scoped_app; split; assumption | split; [ exact HAM | exact (IHR _ HΘ HRm) ] ].
Qed.

(** A record entry of a closed body has a closed declaration. *)
Lemma gm_entry_record_closed : forall Φ k ip pv pr R Φ', body_closed k Φ -> gm_entry Φ ip = Some (ge_record pv pr R Φ') ->
    ctx_scoped 0 (record_fctx R (length (record_fields R)) ++ record_params R) /\
    exp_scoped (length (record_params R)) (record_sort R).
Proof.
  fix IH 1; intros [| Φ y E0 | Φ H its] k [| x ip] * HΦ He; cbn in He, HΦ; try discriminate; try contradiction.
  destruct HΦ as [HΦ HE0].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ _ HΦ He) ].
  destruct ip as [| z ip]; [ injection He as ->; exact (proj1 HE0) |].
  destruct E0 as [b pv0 A B | pm [Δ [sm Φ1 | E1]] | pv0 pq k0 D Φ1 | pv0 Aa Ma Ua | pv0 pr0 Rr Φ1]; try discriminate.
  - destruct HE0 as (_ & _ & HΦ1); exact (IH _ _ _ _ _ _ _ HΦ1 He).
  - destruct HE0 as [_ HΦ1]; exact (IH _ _ _ _ _ _ _ HΦ1 He).
  - destruct HE0 as [_ HΦ1]; exact (IH _ _ _ _ _ _ _ HΦ1 He).
Qed.

(** What a closed global context reads as a record has a closed
    declaration: an open frame's, or a filed entry's. *)
Lemma gctx_closed_record_decl : forall Θ Ξ p R, gctx_closed Θ Ξ -> record_lookup Θ Ξ p = Some R ->
    ctx_scoped 0 (record_fctx R (length (record_fields R)) ++ record_params R) /\
    exp_scoped (length (record_params R)) (record_sort R).
Proof.
  intros * [HΘ HΞ] Hl; unfold record_lookup in Hl.
  destruct (gs_find_record Ξ p) as [R0 |] eqn:Hf; [ injection Hl as <-; exact (stack_closed_record _ _ _ HΞ Hf) |].
  destruct (gc_entry Θ Ξ p) as [[| | | | pv pr R0 Φ] |] eqn:He; try discriminate; injection Hl as <-.
  unfold gc_entry, gc_entry_u in He.
  destruct (gs_find Ξ p) as [[U ip] |] eqn:Hg.
  - destruct (gs_find_unit _ _ _ _ Hg) as (mp & K & Hin & _).
    destruct (stack_closed_in _ _ _ _ HΞ Hin) as (T & _ & HU).
    exact (gm_entry_record_closed _ _ _ _ _ _ _ HU He).
  - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hu; [| discriminate ].
    destruct (HΘ _ _ Hu) as (_ & HU).
    exact (gm_entry_record_closed _ _ _ _ _ _ _ HU He).
Qed.

(** The [Π] over the innermost [m] parameters of a record's sort is over
    the others. *)
Lemma record_ty_at_body_scoped : forall R m,
    ctx_scoped 0 (record_params R) -> exp_scoped (length (record_params R)) (record_sort R) ->
    m <= length (record_params R) ->
    exp_scoped (length (record_params R) - m) (ctx_pi (List.firstn m (record_params R)) (record_sort R)).
Proof.
  intros * HP HS Hm.
  rewrite <- (List.firstn_skipn m (record_params R)) in HP, HS.
  rewrite List.length_app in HS; apply ctx_scoped_app_iff in HP as [HP1 _].
  replace (length (record_params R) - m) with (length (List.skipn m (record_params R)))
    by (rewrite List.length_skipn; reflexivity).
  apply ctx_pi_scoped; [ exact HP1 |].
  rewrite List.length_firstn, Nat.min_l by exact Hm.
  rewrite List.length_firstn, Nat.min_l in HS by exact Hm; exact HS.
Qed.

(** The [Π] the type former's type at [Ns] instantiates is over [Ns]. *)
Lemma record_ty_at_inner_scoped : forall R (Ns : list exp),
    ctx_scoped 0 (record_params R) -> exp_scoped (length (record_params R)) (record_sort R) ->
    exp_scoped (List.length Ns)
      (ctx_pi (List.firstn (length (record_params R) - List.length Ns) (record_params R)) (record_sort R)).
Proof.
  intros * HP HS.
  destruct (Nat.le_gt_cases (List.length Ns) (length (record_params R))).
  - eapply exp_scoped_mono; [| apply record_ty_at_body_scoped; [ exact HP | exact HS | lia ] ]; lia.
  - replace (length (record_params R) - List.length Ns) with 0 by lia.
    eapply exp_scoped_mono; [| apply record_ty_at_body_scoped; [ exact HP | exact HS | lia ] ]; lia.
Qed.

(** The type of a record's type former at arguments is scoped where the
    arguments are. *)
Lemma record_ty_at_scoped : forall R Ns n,
    ctx_scoped 0 (record_params R) -> exp_scoped (length (record_params R)) (record_sort R) ->
    List.Forall (exp_scoped n) Ns -> exp_scoped n (record_ty_at R Ns).
Proof.
  intros * HP HS HNs; unfold record_ty_at; apply exp_scoped_sb_of_list; [| exact HNs ].
  eapply exp_scoped_mono; [| apply record_ty_at_inner_scoped; [ exact HP | exact HS ] ]; lia.
Qed.

(** The term part and the δ-reduct of a scoped description are scoped. *)
Lemma ds_ty_scoped : forall R A n, ds_scoped n R -> ds_ty R = Some A -> exp_scoped n A.
Proof.
  intros * HR Ht; destruct R as [A0 om | | | Θ' A0 M0 Rm]; cbn in *; try discriminate.
  - injection Ht as <-; apply HR.
  - injection Ht as <-; destruct HR as (HΘ & [HA _] & _); apply ctx_pi_scoped; [ exact HΘ | exact HA ].
Qed.

Lemma ds_red_scoped : forall R M n, ds_scoped n R -> ds_red R = Some M -> exp_scoped n M.
Proof.
  intros [A om | | | Θ' A M0 Rm] * HR Hr; cbn in *; try discriminate.
  - subst; apply HR.
  - injection Hr as <-; destruct HR as (HΘ & [_ HM] & _); apply ctx_fn_scoped; [ exact HΘ | exact HM ].
Qed.

(** A member's type former at no argument is its type. *)
Lemma ind_ty_at_nil : forall D M, ind_ty_at D M nil = ctx_pi (im_params D M) (exp_wk (ind_sort D) (wk_shiftn (im_nn M))).
Proof. intros; unfold ind_ty_at; cbn [List.length sb_of_list]; rewrite Nat.sub_0_r, <- length_im_params, List.firstn_all; apply exp_sub_id. Qed.

(** A record type former at no argument is its type. *)
Lemma record_ty_at_nil : forall R, record_ty_at R nil = ctx_pi (record_params R) (record_sort R).
Proof. intros; unfold record_ty_at; cbn [List.length sb_of_list]; rewrite Nat.sub_0_r, List.firstn_all; apply exp_sub_id. Qed.

(** The type former of a member of a closed declaration is scoped. *)
Lemma ind_former_desc_scoped : forall pq k D Mk Rm n, decl_closed D -> ind_member D k = Some Mk ->
    ds_scoped n Rm -> ds_scoped n (ind_former_desc pq k D Mk Rm).
Proof.
  intros * HD HMk HRm; cbn; split; [ exact I | split; [ split; [| exact I ] | exact HRm ] ].
  rewrite <- ind_ty_at_nil; eapply ind_ty_at_scoped; [ exact HD | exact HMk | constructor ].
Qed.

(** The type former of a closed record declaration is scoped. *)
Lemma record_former_desc_scoped : forall p R Rm n,
    ctx_scoped 0 (record_params R) -> exp_scoped (length (record_params R)) (record_sort R) ->
    ds_scoped n Rm -> ds_scoped n (record_former_desc p R Rm).
Proof.
  intros * HP HS HRm; cbn; split; [ exact I | split; [ split; [| exact I ] | exact HRm ] ].
  rewrite <- record_ty_at_nil; apply record_ty_at_scoped; [ exact HP | exact HS | constructor ].
Qed.

(** The entry a path names, closed. *)
Lemma body_closed_prefix : forall Φ k y Φ1, body_closed k Φ -> gm_prefix_upto Φ y = Some Φ1 -> body_closed k Φ1.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros * HΦ Hp; cbn in Hp, HΦ; try discriminate; [| contradiction ].
  destruct (String.eqb y x); [ injection Hp as <-; cbn; exact HΦ | exact (IH _ _ _ (proj1 HΦ) Hp) ].
Qed.

Lemma gm_entry_closed : forall Φ k ip E, body_closed k Φ -> gm_entry Φ ip = Some E ->
    exists k', match E with
               | ge_def _ _ A B => exp_scoped 0 A /\ opt_scoped 0 B
               | ge_mod _ (gu_mk Δ (md_body sm Φ1)) => sm = sm_closed /\ ctx_scoped k' Δ /\ body_closed (length Δ + k') Φ1
               | ge_mod _ U => gunit_scoped 0 U
               | ge_ind _ _ _ D Φ1 => decl_closed D /\ body_closed (length (ind_uparams D)) Φ1
               | ge_def_mod _ A M U => exp_scoped 0 A /\ exp_scoped 0 M /\ gunit_scoped 0 U
               | ge_record _ pr R Φ1 =>
                   (ctx_scoped 0 (record_fctx R (length (record_fields R)) ++ record_params R) /\
                    exp_scoped (length (record_params R)) (record_sort R)) /\
                   body_closed (length (record_mod_tele pr R)) Φ1
               end.
Proof.
  fix IH 1; intros [| Φ y E0 | Φ H its] k [| x ip] E HΦ He; cbn in He, HΦ; try discriminate; try contradiction.
  destruct HΦ as [HΦ HE0].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ HΦ He) ].
  destruct ip as [| z ip]; [ injection He as <-; exists k; exact HE0 |].
  destruct E0 as [b pv A B | pm [Δ [sm Φ1 | E1]] | pv pq k0 D Φ1 | pv Aa Ma Ua | pv pr Rr Φ1]; try discriminate.
  - destruct HE0 as (_ & _ & HΦ1); exact (IH _ _ _ _ HΦ1 He).
  - destruct HE0 as [_ HΦ1]; exact (IH _ _ _ _ HΦ1 He).
  - destruct HE0 as [_ HΦ1]; exact (IH _ _ _ _ HΦ1 He).
Qed.

(** What a closed body's entry denotes is read in any context: the entry
    is closed. *)
Definition entry_sc (n : nat) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B => exp_scoped n A /\ opt_scoped n B
  | ge_mod _ U => gunit_scoped n U \/ exists T Φ, U = gu_body T Φ /\ unit_closed T Φ
  (** An inductive or a record entry: its declaration closed, so that its
      type former is *)
  | ge_ind _ _ _ D _ => decl_closed D
  | ge_def_mod _ A M U => exp_scoped n A /\ exp_scoped n M /\ gunit_scoped n U
  | ge_record _ _ R _ => ctx_scoped 0 (record_params R) /\ exp_scoped (length (record_params R)) (record_sort R)
  end.

(** The entries before a member, filled in, are over the body's
    parameters. *)
Lemma gm_fill_bound : forall Φ m σ, gmod_scoped m Φ -> gm_fill Φ = Some σ ->
    forall x, x < gm_binders Φ + m -> sentry_scoped m (σ x).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros m σ HΦ Hf x Hx; cbn in Hf, HΦ, Hx.
  - injection Hf as <-; cbn; exact Hx.
  - destruct HΦ as [HΦ HE].
    destruct E as [b pv A [M |] | pv U | ? ? ? ? | pv A M U | ? ? ?]; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:E0; cbn in Hf; try discriminate; injection Hf as <-.
    + destruct x as [| x]; cbn.
      * cbn in HE; destruct HE as [_ HM]; eapply exp_scoped_sub; [ exact HM | apply IH; [ exact HΦ | reflexivity ] ].
      * apply IH; [ exact HΦ | reflexivity | lia ].
    + destruct x as [| x]; cbn.
      * cbn in HE; eapply gunit_scoped_sub; [ exact HE | apply IH; [ exact HΦ | reflexivity ] ].
      * apply IH; [ exact HΦ | reflexivity | lia ].
    + destruct x as [| x]; cbn.
      * cbn in HE; destruct HE as (_ & HM & HU); split;
          [ eapply exp_scoped_sub; [ exact HM | apply IH; [ exact HΦ | reflexivity ] ]
          | eapply gunit_scoped_sub; [ exact HU | apply IH; [ exact HΦ | reflexivity ] ] ].
      * apply IH; [ exact HΦ | reflexivity | lia ].
  - discriminate.
Qed.

(** A description moved along a substitution of bounded entries. *)
Lemma ds_sub_scoped : forall R m k σ, ds_scoped m R -> (forall x, x < m -> sentry_scoped k (σ x)) ->
    ds_scoped k (ds_sub R σ).
Proof.
  induction R as [A om | Δ Φ Φx | Θ ? T Φ Ns | Θ A M Rm IHR]; intros * HR Hσ; cbn in *.
  - destruct HR as [HA Hom]; split; [ eapply exp_scoped_sub; eassumption |].
    destruct om; cbn in *; [ eapply exp_scoped_sub; eassumption | exact I ].
  - destruct HR as [HR1 HR2]; split;
      [ pose proof (gunit_scoped_sub _ _ _ _ HR1 Hσ) as Hs | pose proof (gunit_scoped_sub _ _ _ _ HR2 Hσ) as Hs ];
      rewrite gunit_sub_mk in Hs; exact Hs.
  - destruct HR as (HΘ & HU & HNs); split; [ eapply tele_sub_scoped; eassumption | split; [ exact HU |] ].
    rewrite length_tele_sub; apply List.Forall_map; eapply List.Forall_impl; [| exact HNs ].
    intros M HM; cbn; eapply exp_scoped_sub; [ exact HM | apply sb_qn_bound; exact Hσ ].
  - destruct HR as (HΘ & [HA HM] & HRm); split; [ eapply tele_sub_scoped; eassumption |].
    rewrite length_tele_sub.
    split; [ split; eapply exp_scoped_sub; first [ eassumption | apply sb_qn_bound; exact Hσ ] | exact (IHR _ _ _ HRm Hσ) ].
Qed.

Lemma ds_entry_scoped : forall R y Γy E rd n,
    ds_scoped n R -> ds_entry R y = Some (Γy, E, rd) ->
    ctx_scoped n Γy /\ entry_sc (length Γy + n) E /\
    match rd with
    | reader_open Δ Φ' => Γy = body_ctx Φ' ++ Δ /\ ctx_scoped n Δ /\ gmod_scoped (length Δ + n) Φ'
    | reader_closed Θ Ns M => Γy = nil /\ ctx_scoped n Θ /\ List.Forall (exp_scoped (length Θ + n)) Ns /\ exp_scoped (length Θ + n) M
    end.
Proof.
  intros [A om | Δ Φw Φ | Θ p0 T Φ Ns | Θd A M Rm] * HR He; cbn in He, HR; try discriminate.
  - destruct HR as [_ HR]; rewrite gunit_scoped_mk in HR; destruct HR as [HΔ [_ HΦ]].
    destruct (gm_prefix_upto Φ y) as [[| Φ' x E' | Φ' H its] |] eqn:Hp; try discriminate.
    destruct E' as [[|] pv A0 [B |] | pv U | pv pq k0 D Φ1 | pv Aa Ma Ua | pv pr Rr Φ1]; try discriminate.
    all: injection He as <- <- <-.
    all: pose proof (gm_prefix_upto_scoped _ _ _ _ Hp HΦ) as HΦx; cbn in HΦx; destruct HΦx as [HΦ' HE'].
    all: assert (Hc : ctx_scoped n (body_ctx Φ' ++ Δ))
      by (apply ctx_scoped_app; split; [ apply gmod_scoped_body_ctx; assumption | assumption ]).
    all: split; [ exact Hc | split; [| split; [ reflexivity | split; assumption ] ] ].
    all: rewrite length_app, length_body_ctx, <- Nat.add_assoc; cbn in HE' |- *.
    + destruct HE' as [HA HB]; cbn; split; auto.
    + left; exact HE'.
    + exact HE'.
  - destruct HR as (HΘ & [HT HΦ] & HNs).
    destruct (gm_prefix_upto Φ y) as [[| Φ' x E' | Φ' H its] |] eqn:Hp; try discriminate.
    injection He as <- <- <-.
    pose proof (body_closed_prefix _ _ _ _ HΦ Hp) as HΦx; cbn in HΦx; destruct HΦx as [_ HE'].
    split; [ exact I | split; [| split; [ reflexivity | split; [ assumption | split; [ assumption |] ] ] ] ];
      [| apply exp_scoped_apps; split; [ apply qname_mod_scoped | exact HNs ] ].
    cbn [length]; destruct E' as [b pv A0 B | pv [Δ [[|] Φ1 | E1]] | pv pq k0 D Φ1 | pv Aa Ma Ua | pv pr Rr Φ1]; cbn in HE' |- *.
    + destruct HE' as [HA HB]; split; [ eapply exp_scoped_mono; [| exact HA ]; lia |].
      destruct B; cbn in *; [ eapply exp_scoped_mono; [| exact HB ]; lia | exact I ].
    + destruct HE' as [[=] _].
    + destruct HE' as (_ & HΔ & HΦ1); right; do 2 eexists; split; [ reflexivity |].
      split; [ apply ctx_scoped_app; split; [ rewrite Nat.add_0_r; exact HΔ | exact HT ] | rewrite length_app; exact HΦ1 ].
    + left; eapply gunit_scoped_mono; [| exact HE' ]; lia.
    + exact (proj1 HE').
    + destruct HE' as (HA & HM & HU); split; [| split ];
        [ eapply exp_scoped_mono; [| exact HA ]; lia | eapply exp_scoped_mono; [| exact HM ]; lia
        | eapply gunit_scoped_mono; [| exact HU ]; lia ].
    + destruct HE' as [[HF HS] _]; split; [ exact (proj2 (proj1 (ctx_scoped_app_iff _ _) HF)) | exact HS ].
Qed.

Lemma ds_self_scoped : forall M R n, exp_scoped n M -> ds_scoped n R -> ds_scoped n (ds_self M R).
Proof. intros M R n HM HR; destruct R as [A [] | | | ? ? ?]; cbn in *; try exact HR; split; [ apply HR | exact HM ]. Qed.

Lemma ds_named_scoped : forall Θ Ns M R n, exp_scoped n M -> ds_scoped n R -> ds_scoped n (ds_named Θ Ns M R).
Proof. intros [|] [|] * HM HR; cbn; first [ exact HR | apply ds_self_scoped; assumption ]. Qed.

Lemma ds_ats_read_scoped : forall R Ns R' n,
    ds_scoped n R -> List.Forall (exp_scoped n) Ns -> ds_ats_read R Ns = Some R' -> ds_scoped n R'.
Proof.
  intros * HR HNs Ha; destruct (ds_ats_read_inv _ _ _ Ha) as [Ha' | (A & M & Rm & B & M' & Rm' & -> & -> & Ht & Hm)];
    [ eapply ds_ats_scoped; eassumption |].
  destruct HR as (_ & [HA HM] & HRm); cbn [length] in HA, HM.
  pose proof (ds_ats_tm_scoped _ _ _ _ (conj HA HM : ds_scoped n (ds_term A (Some M))) HNs Ht) as [HB HM'].
  split; [ exact I | split; [ split; assumption | eapply ds_ats_scoped; eassumption ] ].
Qed.

Lemma ds_read_scoped : forall rd R R' n Γy,
    match rd with
    | reader_open Δ Φ' => Γy = body_ctx Φ' ++ Δ /\ ctx_scoped n Δ /\ gmod_scoped (length Δ + n) Φ'
    | reader_closed Θ Ns M => Γy = nil /\ ctx_scoped n Θ /\ List.Forall (exp_scoped (length Θ + n)) Ns /\ exp_scoped (length Θ + n) M
    end ->
    ctx_scoped n Γy -> ds_scoped (length Γy + n) R -> ds_read rd R = Some R' -> ds_scoped n R'.
Proof.
  intros [Δ Φ' | Θ Ns M] * Hrd HΓy HR Hr; cbn in Hr.
  - destruct Hrd as (-> & HΔ & HΦ').
    destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [| discriminate ]; injection Hr as <-.
    apply ds_up_scoped; [ exact HΔ |].
    eapply ds_sub_scoped; [ exact HR |].
    rewrite length_app, length_body_ctx, <- Nat.add_assoc; exact (gm_fill_bound _ _ _ HΦ' Hf).
  - destruct Hrd as (-> & HΘ & HNs & HM); cbn in HR.
    destruct (ds_ats_read R Ns) as [R0 |] eqn:E; [| discriminate ]; injection Hr as <-.
    apply ds_up_scoped; [ exact HΘ |].
    apply ds_named_scoped; [ exact HM |].
    eapply ds_ats_read_scoped; [| exact HNs | exact E ].
    eapply ds_scoped_mono; [| exact HR ]; lia.
Qed.

(** A body module of a closed body is closed, over its full telescope. *)
Lemma gm_subbody_closed : forall Φ T x ip T' Φ',
    unit_closed T Φ -> gm_subbody T Φ x ip = Some (T', Φ') -> unit_closed T' Φ'.
Proof.
  fix IH 1; intros [| Φ y E0 | Φ H its] T x ip T' Φ' [HT HΦ] He; cbn in He, HΦ; try discriminate; try contradiction.
  destruct HΦ as [HΦ HE0].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ (conj HT HΦ) He) ].
  destruct E0 as [b pv A B | pm [Δ [sm Φ1 | E1]] | pv pq k0 D Φ1 | pv Aa Ma Ua | pv pr Rr Φ1]; try discriminate.
  - destruct HE0 as (_ & HΔ & HΦ1).
    assert (HU : unit_closed (Δ ++ T) Φ1)
      by (split; [ apply ctx_scoped_app; split; [ rewrite Nat.add_0_r; exact HΔ | exact HT ] | rewrite length_app; exact HΦ1 ]).
    destruct ip as [| z ip]; [ injection He as <- <-; exact HU | exact (IH _ _ _ _ _ _ HU He) ].
  - destruct HE0 as [HD HΦ1].
    assert (HU : unit_closed (ind_uparams D) Φ1) by (split; [ apply (decl_closed_uparams _ HD) | exact HΦ1 ]).
    destruct ip as [| z ip]; [ injection He as <- <-; exact HU | exact (IH _ _ _ _ _ _ HU He) ].
  - destruct HE0 as [[HF _] HΦ1].
    assert (HU : unit_closed (record_mod_tele pr Rr) Φ1)
      by (split; [ exact (record_mod_tele_scoped _ _ (proj2 (proj1 (ctx_scoped_app_iff _ _) HF))) | exact HΦ1 ]).
    destruct ip as [| z ip]; [ injection He as <- <-; exact HU | exact (IH _ _ _ _ _ _ HU He) ].
Qed.

Lemma gctx_closed_body : forall Θ Ξ p T Φ,
    gctx_closed Θ Ξ -> gc_body Θ Ξ p = Some (T, Φ) -> unit_closed T Φ.
Proof.
  intros * [HΘ HΞ] Hb; unfold gc_body in Hb.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Hf; [ discriminate | |].
  - exact (gm_subbody_closed _ _ _ _ _ _ (stack_closed_find _ _ _ _ _ HΞ Hf) Hb).
  - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
    destruct (q_chain p) as [| x ip]; cbn in Hb; [ injection Hb as <- <-; exact (HΘ _ _ Hl) |].
    exact (gm_subbody_closed _ _ _ _ _ _ (HΘ _ _ Hl) Hb).
Qed.

(** The module part and its telescope. *)
Lemma gctx_closed_entry_ind : forall Θ Ξ p pv pq k D Φ,
    gctx_closed Θ Ξ -> gc_entry Θ Ξ p = Some (ge_ind pv pq k D Φ) -> unit_closed (ind_uparams D) Φ.
Proof.
  intros * [HΘ HΞ] He; unfold gc_entry, gc_entry_u in He.
  destruct (gs_find Ξ p) as [[U ip] |] eqn:Hf.
  - destruct (gs_find_unit _ _ _ _ Hf) as (mp & K & Hin & _).
    destruct (stack_closed_in _ _ _ _ HΞ Hin) as (T & _ & HU).
    destruct (gm_entry_closed _ _ _ _ HU He) as (_ & HD & HΦ).
    split; [ apply (decl_closed_uparams _ HD) | exact HΦ ].
  - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:Hl; [| discriminate ].
    destruct (HΘ _ _ Hl) as (_ & HU).
    destruct (gm_entry_closed _ _ _ _ HU He) as (_ & HD & HΦ).
    split; [ apply (decl_closed_uparams _ HD) | exact HΦ ].
Qed.

(** The body at a located path, closed. *)
Lemma gc_loc_closed : forall Θ Ξ p T Φ, gctx_closed Θ Ξ -> gc_loc Θ Ξ p = Some (T, Φ) -> unit_closed T Φ.
Proof.
  intros * Hc Hl; unfold gc_loc in Hl.
  destruct (gc_frame Ξ p) as [r |] eqn:Hf; [ injection Hl as -> | eapply gctx_closed_body; eassumption ].
  unfold gc_frame in Hf.
  destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ0 | E]] [| x ip]] T0] |] eqn:Hft; try discriminate.
  injection Hf as <- <-; exact (stack_closed_find _ _ _ _ _ (proj2 Hc) Hft).
Qed.

Lemma ds_mod_scoped : forall R R' n, ds_scoped n R -> ds_mod R = Some R' -> ds_scoped n R'.
Proof.
  intros R; induction R as [A om | Δ Φ | Θ0 ? T Φ Ns | Θ0 A M Rm IH]; intros R' n HR Hm;
    cbn in Hm; try discriminate; try (injection Hm as <-; exact HR).
  exact (IH _ _ (proj2 (proj2 HR)) Hm).
Qed.

(** The unit a loaded unit or an open frame is, closed. *)
Lemma gctx_closed_unit : forall Θ Ξ H T Φ, gctx_closed Θ Ξ -> gc_unit Θ Ξ H = Some (T, Φ) -> unit_closed T Φ.
Proof.
  intros * [HΘ HΞ] Hu; unfold gc_unit in Hu.
  destruct (mod_qname H) as [mp |]; [| discriminate ].
  destruct (gs_find_tele Ξ mp) as [[[U [| ? ?]] T0] |] eqn:Hf.
  - destruct U as [Δ [[|] Φ0 | E]], (gs_find_ind Ξ mp), (gs_find_record Ξ mp); try discriminate; injection Hu as <- <-.
    exact (stack_closed_find _ _ _ _ _ HΞ Hf).
  - discriminate.
  - destruct (q_chain mp), (gds_lookup Θ (q_unit mp)) as [[Δ [[|] Φ0 | E]] |] eqn:Hl; try discriminate.
    injection Hu as <- <-; exact (HΘ _ _ Hl).
Qed.

(** A closed body has no local open: its expansion is itself. *)
Lemma body_xp_closed : forall Θ Ξ Γ Φ Φx k, body_closed k Φ -> body_xp Θ Ξ Γ Φ Φx -> Φx = Φ.
Proof.
  intros * HΦ Hx; revert HΦ; induction Hx; intros HΦ; cbn in HΦ; [ reflexivity | | contradiction ].
  rewrite IHHx by apply HΦ; reflexivity.
Qed.

(** The module slots a module expression scoped at [m] may name, the [m]
    innermost bindings, hold units scoped at [m]. *)
Definition slots_ok (m : nat) (Γ : ctx) : Prop :=
  forall x U, x < m -> Γ ∋ #x ≔ₘ U -> gunit_scoped m U.

Lemma slots_ok_ctx : forall Γ, ctx_scoped 0 Γ -> slots_ok (length Γ) Γ.
Proof.
  intros * HΓ x U _ Hl; pose proof (ctx_scoped_lookup_mod _ _ _ _ HΓ Hl) as HU; rewrite Nat.add_0_r in HU; exact HU.
Qed.

Lemma slots_ok_cons : forall m Γ e, slots_ok m Γ -> ce_scoped m e -> slots_ok (S m) (e :: Γ).
Proof.
  intros * HΓ He x U Hx Hl; inversion Hl; subst.
  - eapply gunit_scoped_wk; [ exact He |]; cbn; lia.
  - eapply gunit_scoped_wk; [ exact (proj2 (proj2 He)) |]; cbn; lia.
  - match goal with Hl0 : Γ ∋ # ?n ≔ₘ ?U0 |- _ => pose proof (HΓ n U0 ltac:(lia) Hl0) as HU end.
    eapply gunit_scoped_wk; [ exact HU |]; cbn; lia.
Qed.

Lemma slots_ok_app : forall Γy m Γ, slots_ok m Γ -> ctx_scoped m Γy -> slots_ok (length Γy + m) (Γy ++ Γ).
Proof.
  induction Γy as [| e Γy IH]; intros * HΓ HΓy; cbn in *; [ exact HΓ |].
  destruct HΓy as [He HΓy]; apply slots_ok_cons; [ apply IH; assumption | exact He ].
Qed.

Lemma mdenote_scoped_all : forall Θ Ξ, gctx_closed Θ Ξ ->
    (forall Γ H R, mdenote Θ Ξ Γ H R -> forall m, slots_ok m Γ -> modexp_scoped m H -> ds_scoped m R) /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R -> forall m, slots_ok m Γ ->
       (gunit_scoped m U \/ exists T Φ, U = gu_body T Φ /\ unit_closed T Φ) -> ds_scoped m R) /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R -> forall m, slots_ok m Γ -> entry_sc m E -> ds_scoped m R) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> forall m, slots_ok m Γ -> gmod_scoped m Φ -> gmod_scoped m Φx) /\
    (forall Γ H its gs, items_gen Θ Ξ Γ H its gs -> forall m, slots_ok m Γ -> modexp_scoped m H ->
       List.Forall (fun g => gentry_scoped m (snd (generated_item_entry g))) gs).
Proof.
  intros Θ Ξ Hc; apply mdenote_all_ind; intros; cbn in *.
  - (* a unit *) split; [ exact I | split; [ eapply gctx_closed_unit; eassumption | constructor ] ].
  - (* a type's open frame *)
    match goal with Hf : gs_find_ind _ ?p = Some (?pq, ?k, ?D), HMk : ind_member ?D ?k = Some ?Mk,
                    Hl : gc_loc _ _ ?p = Some (?Tm, ?Φm), HΓ : slots_ok ?m _ |- _ =>
      exact (ind_former_desc_scoped pq k D Mk (ds_closed nil p Tm Φm nil) m (stack_closed_ind _ _ _ _ _ (proj2 Hc) Hf) HMk
               (conj I (conj (gc_loc_closed _ _ _ _ _ Hc Hl) (List.Forall_nil (exp_scoped _))))) end.
  - (* a slot *)
    match goal with IH : forall m, slots_ok m ?Γ -> _ -> _, HΓ : slots_ok ?m ?Γ, Hl : ?Γ ∋ # ?x ≔ₘ _, Hx : ?x < ?m |- _ =>
      apply IH; [ exact HΓ | left; exact (HΓ _ _ Hx Hl) ] end.
  - (* a literal *)
    match goal with IH : forall m, slots_ok m ?Γ -> _ -> _ |- _ => apply IH; [ assumption | left; assumption ] end.
  - (* an application *)
    destruct_all; eapply ds_at_scoped; [| eassumption | eassumption ].
    match goal with IH : forall m, slots_ok m ?Γ -> _ -> _ |- _ => apply IH; assumption end.
  - (* a selection *)
    match goal with
    | IH0 : forall m, slots_ok m ?Γ -> modexp_scoped m ?H0 -> ds_scoped m ?R0, Hm : ds_mod ?R0 = Some _,
      He : ds_entry _ _ = Some _, Hr : ds_read _ _ = Some _,
      IH1 : forall m, slots_ok m (_ ++ ?Γ) -> entry_sc m _ -> ds_scoped m _, HΓ : slots_ok ?m ?Γ |- _ =>
        pose proof (ds_mod_scoped _ _ _ (IH0 m HΓ ltac:(assumption)) Hm) as HR0m;
        destruct (ds_entry_scoped _ _ _ _ _ _ HR0m He) as (HΓy & HE & Hrd);
        eapply ds_read_scoped; [ exact Hrd | exact HΓy | | exact Hr ];
        apply IH1; [ apply slots_ok_app; assumption | exact HE ]
    end.
  - (* a record's open frame *)
    match goal with Hf : gs_find_record _ ?p = Some ?R,
                    Hl : gc_loc _ _ ?p = Some (?Tm, ?Φm), HΓ : slots_ok ?m _ |- _ =>
      destruct (stack_closed_record _ _ _ (proj2 Hc) Hf) as [HF HS];
      exact (record_former_desc_scoped p R (ds_closed nil p Tm Φm nil) m (proj2 (proj1 (ctx_scoped_app_iff _ _) HF)) HS
               (conj I (conj (gc_loc_closed _ _ _ _ _ Hc Hl) (List.Forall_nil (exp_scoped _))))) end.
  - (* a body *)
    match goal with Hu : gunit_scoped _ _ \/ _ |- _ => destruct Hu as [HU | (T & Φ0 & Heq & HU)]; [| injection Heq as -> -> -> ] end.
    + rewrite gunit_scoped_mk in HU; destruct HU as [HΔ [-> HΦ]]; cbn in *.
      match goal with Hb : Some _ = Some _ |- _ => injection Hb as <- end.
      split; apply gunit_scoped_mk; (split; [ exact HΔ | split; [ reflexivity |] ]); [ exact HΦ |].
      match goal with IH : forall m, slots_ok m (_ ++ _) -> _ -> _ |- _ => apply IH end;
        [ apply slots_ok_app; assumption | exact HΦ ].
    + cbn in *; match goal with Hx : body_xp _ _ _ _ _ |- _ => rewrite (body_xp_closed _ _ _ _ _ _ (proj2 HU) Hx) in * end.
      match goal with Hb : option_map _ ?o = Some _ |- _ => destruct o; cbn in Hb; [ injection Hb as <- | discriminate ] end.
      split; [ exact I | split; [ exact HU | constructor ] ].
  - (* an alias *)
    match goal with Hu : gunit_scoped _ _ \/ _ |- _ => destruct Hu as [HU | (T & Φ0 & [=] & _)] end.
    rewrite gunit_scoped_mk in HU; destruct HU as [HΔ HE]; cbn in HE.
    apply ds_up_scoped; [ exact HΔ |].
    eapply ds_mod_scoped; [| eassumption ].
    match goal with IH : forall m, slots_ok m (_ ++ _) -> _ -> _ |- _ => apply IH end;
      [ apply slots_ok_app; assumption | exact HE ].
  - (* a definition *)
    match goal with HE : _ /\ _ |- _ => destruct HE as [HA HB] end.
    split; [ exact HA |]; destruct b; [ exact HB | exact I ].
  - (* a module *) match goal with IH : forall m, _ -> _ -> _ |- _ => apply IH; assumption end.
  - (* an inductive type *)
    match goal with HMk : ind_member ?D ?k = Some ?Mk, Hl : gc_loc _ _ ?pm = Some (?Tm, ?Φm),
                    HD : decl_closed ?D, HΓ : slots_ok ?m _ |- _ =>
      exact (ind_former_desc_scoped pq k D Mk (ds_closed nil pm Tm Φm nil) m HD HMk
               (conj I (conj (gc_loc_closed _ _ _ _ _ Hc Hl) (List.Forall_nil (exp_scoped _))))) end.
  - (* a definition with a module part *)
    destruct_all; split; [ exact I | split; [ split; assumption |] ].
    match goal with IH : forall m, _ -> _ -> _ |- _ => apply IH; [ assumption | left; assumption ] end.
  - (* a record type *)
    match goal with HPS : ctx_scoped 0 (record_params ?R) /\ _, Hl : gc_loc _ _ ?p = Some (?Tm, ?Φm),
                    HΓ : slots_ok ?m _ |- _ =>
      exact (record_former_desc_scoped p R (ds_closed nil p Tm Φm nil) m (proj1 HPS) (proj2 HPS)
               (conj I (conj (gc_loc_closed _ _ _ _ _ Hc Hl) (List.Forall_nil (exp_scoped _))))) end.
  - (* the empty body *) exact I.
  - (* an entry *)
    destruct_all; split; [ eauto |].
    match goal with Hx : body_xp _ _ _ _ _ |- _ => rewrite (body_xp_binders _ _ _ _ _ Hx) end; assumption.
  - (* an open: its generated entries *)
    destruct_all.
    match goal with IH : forall m, slots_ok m ?Γ -> gmod_scoped m ?Φ -> gmod_scoped m ?Φx, Hx : body_xp _ _ _ ?Φ ?Φx,
                    HΓ : slots_ok ?m ?Γ |- _ =>
      assert (HΦx : gmod_scoped m Φx) by (apply IH; assumption) end.
    apply gens_append_scoped; [ assumption | lia |].
    rewrite Nat.sub_0_r, <- length_body_ctx.
    match goal with IH : forall m, _ -> _ -> List.Forall _ _ |- _ => apply IH end;
      [ apply slots_ok_app; [ assumption | apply gmod_scoped_body_ctx; assumption ] |].
    rewrite length_body_ctx; match goal with Hx : body_xp _ _ _ _ _ |- _ => rewrite (body_xp_binders _ _ _ _ _ Hx) end; assumption.
  - constructor.
  - constructor; [ cbn; split; [ exact I | assumption ] | eauto ].
  - constructor; [ cbn; split; [| assumption ] | eauto ].
    match goal with IH : forall m, slots_ok m ?Γ -> _ -> exp_scoped m ?A /\ _ |- exp_scoped ?m0 ?A =>
      exact (proj1 (IH m0 ltac:(assumption) ltac:(assumption))) end.
  - constructor; [ cbn; split; [ exact I | assumption ] | eauto ].
  - constructor; [| eauto ]; cbn; repeat split; try assumption; try exact I.
    match goal with IH : forall m, slots_ok m ?Γ -> _ -> ds_scoped m ?R, Ht : ds_ty ?R = Some ?A |- exp_scoped ?m0 ?A =>
      exact (ds_ty_scoped _ _ _ (IH m0 ltac:(assumption) ltac:(assumption)) Ht) end.
Qed.


(** What a closed body's term entry describes is closed. *)
Lemma entry_term_scoped : forall k Φ x Φ0 E o R m,
    body_closed k Φ -> gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) -> entry_term o E = Some R ->
    ds_scoped m R.
Proof.
  intros * HΦ Hp He; pose proof (body_closed_prefix _ _ _ _ HΦ Hp) as [_ HE].
  destruct E as [b pv A B | pv U | pv pq k0 D Φ1 | pv A M U | pv pr Rr Φ1]; cbn in He; try discriminate.
  2: destruct (ind_member D k0) as [Mk |] eqn:HMk; cbn in He; [| discriminate ].
  4: destruct o; cbn in He; [| discriminate ].
  all: injection He as <-; cbn in *.
  - destruct HE as [HA HB]; split; [ eapply exp_scoped_mono; [| exact HA ]; lia |].
    destruct b, B; cbn in *; try exact I; eapply exp_scoped_mono; [| exact HB ]; lia.
  - destruct HE as [HD _]; split; [| exact I ].
    rewrite <- ind_ty_at_nil; eapply ind_ty_at_scoped; [ exact HD | exact HMk | constructor ].
  - destruct HE as (HA & HM & _); split; eapply exp_scoped_mono; [| exact HA | | exact HM ]; lia.
  - destruct HE as [[HF HS] _]; split; [| exact I ].
    rewrite <- record_ty_at_nil; apply record_ty_at_scoped; [ exact (proj2 (proj1 (ctx_scoped_app_iff _ _) HF)) | exact HS | constructor ].
Qed.

(** The alias unit of a closed body's entry is closed. *)
Lemma entry_alias_unit_scoped : forall k Φ y Φ0 E Ua m,
    body_closed k Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_alias_unit E = Some Ua -> gunit_scoped m Ua.
Proof.
  intros * HΦ Hp He; pose proof (body_closed_prefix _ _ _ _ HΦ Hp) as [_ HE].
  destruct E as [b pv A B | pv [Ta [sm Φ1 | E']] | pv pq D Φ1 | pv A M [Ta [sm Φ1 | E']] | pv Rr Φ1]; cbn in He; try discriminate; injection He as <-; cbn in HE.
  - eapply gunit_scoped_mono; [| exact HE ]; lia.
  - eapply gunit_scoped_mono; [| exact (proj2 (proj2 HE)) ]; lia.
Qed.

Lemma gunit_abs_scoped : forall Δ U m,
    ctx_scoped m Δ -> gunit_scoped (length Δ + m) U -> gunit_scoped m (gunit_abs Δ U).
Proof.
  intros Δ [Δy D] m HΔ HU; cbn [gunit_abs]; rewrite gunit_scoped_mk in *; destruct HU as [HΔy HD].
  split; [ apply ctx_scoped_app; split; assumption | rewrite length_app, <- Nat.add_assoc; exact HD ].
Qed.

(** The unit a module description stands for is scoped as it is. *)
Lemma ds_unit_scoped : forall R m, ds_scoped m R -> modexp_scoped m (ds_unit R).
Proof.
  intros [A om | Δ Φ Φx | Θ p T Φ Ns | Θd A M Rm] m HR; cbn in HR |- *.
  - apply gunit_scoped_mk; split; [ exact I | cbn; split; [ reflexivity | exact I ] ].
  - exact (proj1 HR).
  - destruct Θ as [| e Θ]; cbn in HR |- *; destruct HR as (HΘ & _ & HNs).
    + apply me_apps_scoped_iff; split; [ apply qname_mod_scoped | exact HNs ].
    + apply gunit_scoped_mk; split; [ exact HΘ |]; cbn.
      apply me_apps_scoped_iff; split; [ apply qname_mod_scoped | exact HNs ].
  - apply gunit_scoped_mk; split; [ exact I | cbn; split; [ reflexivity | exact I ] ].
Qed.

(** A literal given its outermost parameter, instantiated. *)
Lemma beta_unit_scoped : forall Δ X D n N,
    gunit_scoped n (gu_mk (Δ ++ ce_ass X :: nil) D) -> exp_scoped n N ->
    gunit_scoped n (gu_mk (tele_sub Δ (Id,,N)) (moddef_sub D (sb_qn (length Δ) (Id,,N)))).
Proof.
  intros * HU HN; rewrite gunit_scoped_mk in *; destruct HU as [HΔX HD].
  apply ctx_scoped_app in HΔX as [HΔ _]; cbn [length] in HΔ.
  assert (Hσ : forall x, x < 1 + n -> sentry_scoped n ((Id,,N) x)) by (intros [|x] ?; cbn; auto; lia).
  split; [ eapply tele_sub_scoped; eassumption |].
  rewrite length_tele_sub; eapply (proj1 (proj2 (proj2 (proj2 (proj2 syn_scoped_sub))))); [ exact HD |].
  rewrite length_app; cbn [length]; rewrite <- Nat.add_assoc; apply sb_qn_bound; exact Hσ.
Qed.
(** ** Every Judgment is Well Scoped *)

#[local] Arguments gctx_closed : simpl never.
#[local] Arguments mod_closed : simpl never.
#[local] Arguments unit_closed : simpl never.

Definition ctx_ok (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : Prop :=
  ctx_scoped 0 Γ /\ gctx_closed Θ Ξ.


(** The cases of inductive types: the motive is under [S (ind_nn D)]
    binders, a branch under as many as its context has, and the lists of
    parameters and arguments are typed one by one. *)
Ltac ind_motive_scoped :=
  subst; rewrite ?length_elim_mctx, ?length_tele_sub in *; assumption.

(** A term the premise of a rule types, scoped by the premise's induction
    hypothesis: the hypothesis is found by trying them. *)
Ltac ind_pick_close H :=
  rewrite ?length_app, ?length_tele_sub, ?length_elim_mctx in H;
  first [ exact H
        | eapply exp_scoped_mono; [| exact H ]; unfold im_nn in *; lia
        | rewrite ?length_app; exact H
        | (* an annotation, the head of the annotated context of its motive *)
          let H' := fresh "Hs" in
          cbn [ctx_scoped centry_scoped] in H; destruct H as [H' _]; rewrite ?length_tele_sub in H';
          first [ exact H' | eapply exp_scoped_mono; [| exact H' ]; unfold im_nn in *; lia ] ].

Ltac ind_pick :=
  match goal with
  | |- exp_scoped _ _ =>
      match goal with IH : _ |- _ =>
        let H := fresh "Hs" in
        first [ edestruct IH as (_ & H & _); [ eassumption .. |]; ind_pick_close H
              | edestruct IH as (_ & _ & H & _); [ eassumption .. |]; ind_pick_close H ]
      end
  end.

(** The declaration of a group is closed, by the induction hypotheses of
    the premises of its rule, found by their shapes. *)
Ltac ind_decl_scoped :=
  match goal with
  | Hc : gctx_closed _ _,
    HN : forall k Mk Δ1 T Δ2, ind_member _ k = Some Mk -> im_nparams Mk = _ -> (_ /\ _) /\ exp_scoped _ T /\ _,
    HA : forall k Mk c gs gs1 A gs2, ind_member _ k = Some Mk -> In _ _ -> gs = _ -> (_ /\ _) /\ exp_scoped _ A /\ _,
    HB : forall k Mk c gs gs1 t gs2 Bs1 B Bs2, ind_member _ k = Some Mk -> In _ _ -> gs = _ -> ptyp_doms t = _ ->
           (_ /\ _) /\ exp_scoped _ B /\ _,
    HL : forall k Mk c gs, ind_member _ k = Some Mk -> In _ _ -> cargs_plen _ gs,
    HP : forall k Mk c gs gs1 t gs2 Mj j P T, ind_member _ k = Some Mk -> In _ _ -> gs = _ -> ind_member _ _ = Some Mj ->
           nth_error _ j = Some P -> nth_error _ j = Some T -> (_ /\ _) /\ exp_scoped _ P /\ _,
    HX : forall k Mk qc k' Is vm, ind_member _ k = Some Mk -> im_head Mk = mh_view qc k' Is vm -> exists D', _,
    HS : forall k Mk qc k' Is vm, ind_member _ k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
           Is = List.map _ _,
    HI : forall k Mk qc k' Is vm D' j I T, ind_member _ k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
           ind_lookup _ _ qc = Some D' -> nth_error _ j = Some I -> nth_error _ j = Some T ->
           (_ /\ _) /\ exp_scoped _ I /\ _,
    HRD : rview_struct_ok _ _ _,
    HRS : forall k Mk qr Is fl, ind_member _ k = Some Mk -> im_head Mk = mh_record qr Is fl -> Is = List.map _ _,
    HRI : forall k Mk qr Is fl R j I T, ind_member _ k = Some Mk -> im_head Mk = mh_record qr Is fl ->
           record_lookup _ _ qr = Some R -> nth_error _ j = Some I -> nth_error _ j = Some T ->
           (_ /\ _) /\ exp_scoped _ I /\ _
    |- decl_closed _ =>
      apply decl_closed_intro; [ assumption | assumption | assumption |];
      let HMk := fresh "HMk" in
      intros ? ? HMk; apply member_closed_intro; [ assumption | assumption | eauto | | | | | | | | | ];
      [ let E := fresh "E" in let HT := fresh "HT" in
        intros * E; edestruct HN as (_ & HT & _); [ exact HMk | exact E | exact HT ]
      | let Hh := fresh "Hh" in let D' := fresh "D'" in let HD' := fresh "HD'" in let HlIs := fresh "HlIs" in
        let HSk := fresh "HSk" in
        intros * Hh; destruct (HX _ _ _ _ _ _ HMk Hh) as (D' & ? & HD' & _ & _ & HlIs & _);
        pose proof (HS _ _ _ _ _ _ HMk Hh) as HSk;
        lazymatch type of HSk with _ = List.map _ ?L =>
          eapply (view_is_scoped _ _ _ _ _ (tele_insts (ind_uparams D') Id L)) end;
        [ exact HSk
        | rewrite length_tele_insts by exact (decl_closed_ass _ (gctx_closed_ind _ _ _ _ Hc HD'));
          rewrite HSk, length_map in HlIs; unfold ind_nu in HlIs; lia
        | let HI0 := fresh "HI0" in let HT0 := fresh "HT0" in let HIs := fresh "HIs" in
          intros ? ? ? HI0 HT0; edestruct HI as (_ & HIs & _); [ exact HMk | exact Hh | exact HD' | exact HI0 | exact HT0 | exact HIs ] ]
      | let Hh := fresh "Hh" in let R := fresh "R" in let HRf := fresh "HRf" in let HSk := fresh "HSk" in
        intros * Hh; destruct (rview_struct_record _ _ _ HRD _ _ _ _ _ HMk Hh) as [R HRf];
        pose proof (HRS _ _ _ _ _ HMk Hh) as HSk;
        lazymatch type of HSk with _ = List.map _ ?L =>
          eapply (view_is_scoped _ _ _ _ _ (tele_insts (record_params R) Id L)) end;
        [ exact HSk
        | rewrite length_tele_insts by exact (rview_record_ass _ _ _ _ _ _ HRf);
          pose proof (rview_record_count _ _ _ _ _ _ HRf) as HlIs; rewrite HSk, length_map in HlIs; lia
        | let HI0 := fresh "HI0" in let HT0 := fresh "HT0" in let HIs := fresh "HIs" in
          intros ? ? ? HI0 HT0; edestruct HRI as (_ & HIs & _);
            [ exact HMk | exact Hh | exact (rview_record_lookup _ _ _ _ _ _ HRf) | exact HI0 | exact HT0 | exact HIs ] ]
      | let Hh := fresh "Hh" in intros * Hh; exact (rview_struct_nparams _ _ _ HRD _ _ _ _ _ HMk Hh)
      | let Hh := fresh "Hh" in let Hin := fresh "Hin" in let gs0 := fresh "gs0" in let Hc0 := fresh "Hc0" in
        let Hl0 := fresh "Hl0" in
        intros * Hh Hin; destruct (rview_struct_con _ _ _ HRD _ _ _ _ _ HMk Hh) as (gs0 & Hc0 & Hl0);
        rewrite Hc0 in Hin; destruct Hin as [Hin | []]; injection Hin as _ <-; symmetry; exact Hl0
      | let Hin := fresh "Hin" in let E := fresh "E" in let HA0 := fresh "HA0" in
        intros * Hin E; edestruct HA as (_ & HA0 & _); [ exact HMk | exact Hin | exact E | exact HA0 ]
      | let Hin := fresh "Hin" in let E := fresh "E" in let Ed := fresh "Ed" in let HB0 := fresh "HB0" in
        intros * Hin E Ed; edestruct HB as (_ & HB0 & _); [ exact HMk | exact Hin | exact E | exact Ed | exact HB0 ]
      | let Hin := fresh "Hin" in intros * Hin; eapply HL; [ exact HMk | exact Hin ]
      | let Hin := fresh "Hin" in let E := fresh "E" in let HMj := fresh "HMj" in let HP0 := fresh "HP0" in
        let HT0 := fresh "HT0" in let HPs := fresh "HPs" in
        intros * Hin E HMj HP0 HT0; edestruct HP as (_ & HPs & _);
          [ exact HMk | exact Hin | exact E | exact HMj | exact HP0 | exact HT0 | exact HPs ] ]
  end.


Ltac ind_blocks_scoped :=
  first
    [ eapply elim_blocks_scoped; [ eassumption | eassumption | | | eassumption | eassumption |]; intros; ind_pick
    | eapply elim_blocks_scoped'; [ eassumption | eassumption | | | eassumption | eassumption | eassumption | | eassumption ];
      intros; ind_pick
    | eapply elim_blocks_scoped_l; [ eassumption | eassumption | | | eassumption | eassumption | eassumption | | eassumption ];
      intros; ind_pick ].

Ltac ind_brs_scoped := ind_blocks_scoped.

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
          first [ apply length_tele_insts_params; [ eapply decl_closed_params_ass; eassumption | assumption ]
                | apply length_tele_insts_cargs; assumption ]
      end
    | match goal with IH : forall k P P' T, nth_error ?L0 k = Some P -> nth_error ?L k = Some P' -> _ -> _ /\ _ /\ exp_scoped _ P' /\ _
                       |- List.Forall _ ?L =>
        eapply (nth_typed_scoped_r L0);
          [ congruence
          | apply length_tele_insts_params; [ eapply decl_closed_params_ass; eassumption | assumption ]
          | let Hk := fresh "Hk" in let Hk' := fresh "Hk'" in let HT := fresh "HT" in
            intros ? ? ? ? Hk Hk' HT; edestruct IH as (_ & _ & ? & _); [ exact Hk | exact Hk' | exact HT | eassumption ] ]
      end
    | eapply im_pre_scoped; [ eassumption | eassumption | rewrite List.length_firstn; unfold im_np in *; lia |]
    | eapply elim_ihs_scoped_at; [ eassumption | eassumption | eassumption | assumption | eassumption | ind_blocks_scoped | |] ].

Ltac ind_scoped :=
  first
    [ eapply exp_scoped_mono; [| eapply decl_closed_ind_ty; eassumption ]; lia
    | eapply exp_scoped_mono; [| eapply decl_closed_con_ty; [ eassumption | eassumption | apply cons_lookup_in; eassumption ] ]; lia
    | ind_motive_scoped
    | ind_blocks_scoped
    | eapply vwrap_scoped; [ eassumption | eassumption | rewrite List.length_firstn; unfold im_np in *; lia
                           | ind_list_scoped | eassumption | ind_blocks_scoped | eassumption | eassumption ]
    | apply exp_scoped_apps; split; [ exact I | ind_list_scoped ]
    | eapply ind_mty_scoped; [ eassumption | rewrite List.length_firstn; unfold im_np in *; lia | ind_list_scoped | ind_list_scoped ]
    | eapply elim_inst_scoped;
        [ eassumption | ind_pick | ind_list_scoped
        | first [ assumption | apply exp_scoped_apps; split; [ exact I | ind_list_scoped ] ] ]
    | apply exp_scoped_sb_of_list; [| ind_list_scoped ];
      match goal with
      | IH : forall k Mk b c gs n B, _ -> _ -> _ -> _ -> _, Hl : brs_lookup _ _ = Some (_, _) |- _ =>
          let HB := fresh "HB" in
          edestruct IH as (_ & HB & _); [ eassumption | eassumption | eassumption | apply brs_lookup_in; exact Hl |];
          rewrite length_app, length_elim_bctx in HB; eapply exp_scoped_mono; [| exact HB ];
          rewrite !length_app, length_skipn, length_elim_ihs by assumption;
          unfold im_np, im_nn in *; lia
      end ].

(** The context of a record's first [m] fields over its parameters is
    closed when the parameters are and each field's type is scoped by the
    fields before it and the parameters. *)
Lemma record_fctx_scoped : forall R m, m <= length (record_fields R) ->
    (forall k f T, List.nth_error (record_fields R) k = Some (f, T) -> k < m -> exp_scoped (k + length (record_params R)) T) ->
    ctx_scoped 0 (record_params R) -> ctx_scoped 0 (record_fctx R m ++ record_params R).
Proof.
  intros R; induction m as [| m IH]; intros Hm HT HΔ; [ exact HΔ |].
  destruct (List.nth_error (record_fields R) m) as [[f T] |] eqn:Hk;
    [| apply List.nth_error_None in Hk; lia ].
  rewrite (record_fctx_succ _ _ _ _ Hk); cbn [List.app ctx_scoped]; split.
  - rewrite length_app, length_record_fctx, Nat.add_0_r by lia; exact (HT _ _ _ Hk ltac:(lia)).
  - apply IH; [ lia | intros; eapply HT; [ eassumption | lia ] | exact HΔ ].
Qed.

Theorem wf_scoped :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ctx_ok Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ) M /\ exp_scoped (length Γ) A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ) M /\ exp_scoped (length Γ) M' /\
      exp_scoped (length Γ) A) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
      ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ) A /\ exp_scoped (length Γ) A') /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> ctx_ok Θ Ξ Γ /\ exp_scoped (length Γ) U) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
      ctx_ok Θ Ξ Γ /\ ctx_scoped (length Γ) Ψ /\ ctx_scoped (length Γ) Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
      ctx_ok Θ Ξ Γ /\ gunit_scoped (length Γ) U /\ gunit_scoped (length Γ) U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
      ctx_ok Θ Ξ Γ /\ modexp_scoped (length Γ) H /\ modexp_scoped (length Γ) H') /\
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E -> entry_ok (gs_tele Ξ) E) /\
  (forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> unit_closed (Δ ++ gs_tele Ξ) Φ /\ kind_closed K) /\
  (forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> gctx_closed Θ Ξ).
Proof.
  apply wf_mut_ind_all; intros;
    repeat match goal with H : let_ann _ _ |- _ => destruct H as [-> | ->] end;
    unfold ctx_ok in *; cbn in *; destruct_all;
    rewrite ?length_app, ?ctx_scoped_app_iff in *; destruct_all.
  all: repeat match goal with |- _ /\ _ => split end; try assumption;
    eauto using exp_scoped_sub1, exp_scoped_sub2, exp_scoped_shift, mod_closed_nil, exp_scoped_sub1_mod, mod_qname_scoped.
  all: try match goal with
    | |- exp_scoped (length ?Γ + 0) _ => rewrite Nat.add_0_r; assumption
    | H : ?Γ ∋ # ?x : ?A |- ?x < _ => apply ctx_lookup_length in H; assumption
    | H : ?Γ ∋ # ?x ≔ₘ ?U |- ?x < _ => apply ctx_lookup_mod_length in H; assumption
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
  all: repeat match goal with
    | Hm : mdenote _ _ ?Γ (me_mem ?H0 _) ?R, Hc : gctx_closed _ _, HΓ : ctx_scoped 0 ?Γ, HH : modexp_scoped _ ?H0 |- _ =>
        pose proof (proj1 (mdenote_scoped_all _ _ Hc) _ _ _ Hm _ (slots_ok_ctx _ HΓ) HH); clear Hm
    | Hd : ds_mod ?R = Some _, HR : ds_scoped _ ?R |- _ =>
        pose proof (ds_mod_scoped _ _ _ HR Hd); clear Hd
    end; destruct_all.
  all: try (apply ds_unit_scoped; assumption).
  all: try match goal with
    | HR : ds_scoped _ ?R, Ht : ds_ty ?R = Some _ |- exp_scoped _ _ =>
        eapply ds_ty_scoped; eassumption
    | HR : ds_scoped _ ?R, Ht : ds_red ?R = Some _ |- exp_scoped _ _ =>
        eapply ds_red_scoped; eassumption
    end.
  all: try match goal with Heq : ?H = me_apps _ _ |- modexp_scoped _ ?H => rewrite Heq end.
  all: try match goal with Hs : exp_scoped _ (apps (a_ind _) ?Ns) |- modexp_scoped _ (me_apps (qname_mod _) ?Ns) =>
         apply me_apps_scoped_iff; split; [ apply qname_mod_scoped | exact (proj2 (proj1 (exp_scoped_apps _ _ _) Hs)) ] end.
  all: try match goal with Hs : modexp_scoped _ (me_apps _ ?Ns), HH : modexp_scoped _ ?H0 |- modexp_scoped _ (me_apps ?H0 ?Ns) =>
         apply me_apps_scoped_iff in Hs; apply me_apps_scoped_iff; split; [ exact HH | exact (proj2 Hs) ] end.
  all: try (rewrite Nat.add_0_r; assumption).
  all: try (rewrite ?Nat.add_0_r in *; eapply exp_scoped_sub2; [ eassumption | eassumption | cbn; repeat split; assumption ]).
  all: try (apply ctx_pi_scoped; [ assumption | rewrite Nat.add_0_r; assumption ]).
  all: try (apply ctx_fn_scoped; [ assumption | rewrite Nat.add_0_r; assumption ]).
  all: try (rewrite gunit_scoped_mk, ?ctx_scoped_app_iff, ?length_app; repeat split; assumption).
  all: repeat match goal with Hl : ind_lookup _ _ _ = Some ?D, Hc : gctx_closed _ _ |- _ =>
         lazymatch goal with _ : decl_closed D |- _ => fail | _ => pose proof (gctx_closed_ind _ _ _ _ Hc Hl) end end.
  all: try match goal with
    | HA : ctx_scoped 0 ?Δ /\ _ |- exp_scoped _ (ctx_pi ?Δ (ind_ty_at _ _)) =>
        destruct HA; eapply exp_scoped_mono; [| apply ctx_pi_scoped; [ eassumption | rewrite Nat.add_0_r; apply ind_ty_at_scoped; eassumption ] ]; lia
    | HA : ctx_scoped 0 ?Δ /\ _ |- exp_scoped _ (ctx_fn ?Δ _) =>
        destruct HA; eapply exp_scoped_mono; [| apply ctx_fn_scoped; [ eassumption | rewrite Nat.add_0_r; apply exp_scoped_apps; split; [ exact I | eassumption ] ] ]; lia
    end.
  all: try match goal with Hs : exp_scoped _ (apps _ ?Ns) |- List.Forall _ ?Ns =>
         exact (proj2 (proj1 (exp_scoped_apps _ _ _) Hs)) end.
  all: try solve [ ind_scoped ].
  all: try solve [ ind_decl_scoped ].
  all: try match goal with HM : forall M, ?o = Some M -> (_ /\ _) /\ _ |- opt_scoped _ (option_map _ ?o) =>
         destruct o as [M0 |]; cbn;
         [ destruct (HM M0 eq_refl) as (_ & ? & _); apply ctx_fn_scoped; [ assumption | rewrite Nat.add_0_r; assumption ]
         | exact I ] end.
  all: try solve [ (* a body unit, either side *)
    rewrite gunit_scoped_mk; split; [ assumption |]; cbn [moddef_scoped]; split; [ reflexivity |];
    match goal with Hx : body_xp _ _ _ ?Φ ?Φx, HC0 : ctx_scoped _ (body_ctx ?Φx ++ _) |- gmod_scoped _ ?Φ =>
      let HC := fresh "HC" in
      pose proof (proj1 (proj1 (ctx_scoped_app _ _ _) HC0)) as HC;
      eapply gmod_scoped_of_xp; [ exact Hx | first
          [ match goal with Hs : body_shape Φx _ |- _ =>
              exact (proj1 (gmod_scoped_of_body_ctx _ _ _ (body_xp_nopens _ _ _ _ _ Hx) Hs) HC) end
          | match goal with Hs : body_shape _ Φx, Hx0 : body_xp _ _ _ _ ?Φx0 |- _ =>
              exact (proj2 (gmod_scoped_of_body_ctx _ _ _ (body_xp_nopens _ _ _ _ _ Hx0) Hs) HC) end ]
      | intros ? ? ? Hk;
        match goal with IH : forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> _ |- _ =>
          edestruct IH as (_ & HH & _); [ exact Hk |]; rewrite !length_app in HH; exact HH end ]
    end ].
  all: try solve [ (* a filed alias *)
    rewrite gunit_scoped_mk; cbn; rewrite ctx_scoped_app_iff, length_app, Nat.add_0_r; repeat split; assumption ].
  all: try solve [ (* the module of an inductive type, before its members *)
    split; [ apply ctx_scoped_uparams; assumption | exact I ] ].
  all: try solve [ (* one more member of the module of an inductive type *)
    apply mod_closed_ext; [ assumption |];
    cbn; split; [ apply ctx_pi_scoped | apply ctx_fn_scoped ]; first [ assumption | rewrite Nat.add_0_r; assumption ] ].
  all: try solve [ split; [ apply ctx_scoped_app_iff; split; assumption | exact I ] ].
  all: try solve [ apply mod_closed_ext; assumption ].
  all: try solve [ split; [ intros ? ? Hl; discriminate | exact I ] ].
  all: try solve [ (* a filed unit: its closed frame, or the units before it *)
    match goal with
    | H : gctx_closed _ _ |- gctx_closed ((?f, _) :: _) nil =>
        destruct H as [HΘ [_ [HU _]]]; split; [| exact I ];
        intros fq0 V0 Hl; cbn in Hl; destruct (path_beq fq0 f);
        [ injection Hl as <-; rewrite List.app_nil_r in HU; exact HU | exact (HΘ _ _ Hl) ]
    end ].
  all: try solve [ (* a frame *)
    match goal with H : gctx_closed _ _ |- _ => destruct H as [HΘ HΞ] end;
    split; [ assumption | cbn; split; [ assumption | split; assumption ] ] ].
  all: try solve [ (* a declared member with the body of its module, over its uniform parameters *)
    match goal with
    | HU : ind_uparams ?D = _ |- unit_closed (ind_uparams ?D) _ => rewrite HU; assumption
    | HU : ind_uparams ?D = ?T, Hc : unit_closed (ind_uparams ?D) ?Φ |- unit_closed ?T ?Φ => rewrite <- HU; exact Hc
    end ].
  all: try solve [ (* a record with the body of its module, over its parameters and a value *)
    match goal with
    | HU : record_params ?R = ?T, Hc : unit_closed (?e :: ?T) ?Φ |- unit_closed (record_mod_tele _ ?R) ?Φ =>
        rewrite <- HU in Hc; exact Hc
    | HU : record_params ?R = ?T, Hc : unit_closed (record_mod_tele _ ?R) ?Φ |- unit_closed (?e :: ?T) ?Φ =>
        rewrite <- HU; exact Hc
    end ].
  all: try solve [ (* the module of a record, before its members *)
    split; [ apply record_mod_tele_scoped; assumption | exact I ] ].
  (* a filed member at arguments *)
  all: try solve [ apply exp_scoped_apps; split; [ apply qname_mod_scoped |];
    match goal with Hs : modexp_scoped _ (me_apps _ ?Ns) |- List.Forall _ ?Ns => exact (proj2 (proj1 (me_apps_scoped_iff _ _ _) Hs)) end ].
  (* a literal given its outermost parameter *)
  all: try solve [ first [ eapply (beta_unit_scoped _ _ (md_body _ _)) | eapply (beta_unit_scoped _ _ (md_alias _)) ]; eassumption ].
  (* a slot's unit *)
  all: try solve [ match goal with H : ?Γ ∋ # ?x ≔ₘ ?U, HΓ : ctx_scoped 0 ?Γ |- gunit_scoped _ ?U =>
    pose proof (ctx_scoped_lookup_mod _ _ _ _ HΓ H) as Hs; rewrite Nat.add_0_r in Hs; exact Hs end ].
  (* a loaded unit or an open frame *)
  all: try solve [ match goal with H : gc_unit _ _ ?H0 = Some _ |- modexp_scoped _ ?H0 =>
    unfold gc_unit in H; destruct (mod_qname H0) eqn:Hq; [ eapply mod_qname_scoped; exact Hq | discriminate ] end ].
  (* an alias of a literal, and the literal over both telescopes *)
  all: try solve [ match goal with HU : gunit_scoped _ (gu_mk ?Δ' ?D) |- gunit_scoped _ _ =>
    apply gunit_scoped_mk in HU; destruct HU as [HU1 HU2]; rewrite gunit_scoped_mk;
    first [ cbn [moddef_scoped modexp_scoped]; split; [ assumption | rewrite gunit_scoped_mk; split; assumption ]
          | rewrite ctx_scoped_app, length_app; split; [ split; assumption | rewrite <- Nat.add_assoc; exact HU2 ] ] end ].
  (* the uniform parameters an eliminator carries *)
  all: try solve [ try match goal with Heq : ?o = List.firstn _ _ |- all_list _ ?o => subst o end;
                   apply all_list_Forall;
                   first [ eapply im_pre_scoped; [ eassumption | eassumption | rewrite List.length_firstn; unfold im_np in *; lia |];
                           ind_list_scoped
                         | ind_list_scoped ] ].
  (* records: a closed type former's type, and a tuple's fields *)
  all: try solve [ match goal with H : exp_scoped 0 ?A |- exp_scoped _ ?A => eapply exp_scoped_mono; [| exact H ]; lia end ].
  all: try solve [ match goal with
    | Hfs : List.map fst ?fs = List.map fst ?fl,
      IH : forall k f M U, List.nth_error ?fs k = Some (f, M) -> _ -> _ |- all_list _ ?fs =>
        apply all_list_snd_of_nth; intros k f M Hk;
        destruct (map_fst_nth _ _ _ _ _ Hfs Hk) as [U HU]; edestruct (IH _ _ _ _ Hk HU) as (_ & ? & _); assumption
    end ].
  (* a record's declaration: the context of its fields is closed *)
  all: try solve [ match goal with
    | HΔ : ctx_scoped 0 (record_params ?R) |- ctx_scoped _ (record_fctx ?R _) =>
        apply ctx_scoped_app_iff, (record_fctx_scoped R _ (le_n _)); [| exact HΔ ];
        intros k f T Hk Hlt;
        match goal with IH : _ |- _ =>
          destruct (IH _ _ _ Hk) as (_ & HT & _);
          rewrite length_app, length_record_fctx in HT by lia; exact HT
        end
    end ].
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

(** In a well-formed context, the type and the term of a def-mod are
    closed. *)
Corollary wf_def_mod_closed : forall Θ Ξ Γ p pv A M U,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    gc_entry Θ Ξ p = Some (ge_def_mod pv A M U) ->
    exp_scoped 0 A /\ exp_scoped 0 M.
Proof.
  intros * HΓ He; pose proof (gctx_closed_entry _ _ _ _ (wf_gctx_closed _ _ _ HΓ) He) as (HA & HM & _).
  split; assumption.
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
(** *** Descriptions under a Substitution

    The parts of a description over the context are substituted; a closed
    module's stored unit is not, being closed.  Weakenings are the
    substitutions [ι φ] ([mdenote_wk_all]). *)

Definition rd_sub (rd : reader) (σ : sub) : reader :=
  match rd with
  | reader_open Δ Φ' => reader_open (tele_sub Δ σ) (gmod_sub Φ' (sb_qn (length Δ) σ))
  | reader_closed Θ Ns M => reader_closed (tele_sub Θ σ) (List.map (fun M => M[sb_qn (length Θ) σ]) Ns) M[sb_qn (length Θ) σ]
  end.

Lemma map_sub_sub : forall Ns σ τ, List.map (fun M => M[τ]) (List.map (fun M => M[σ]) Ns) = List.map (fun M => M[σ ⨟ τ]) Ns.
Proof. intros; rewrite List.map_map; apply List.map_ext; intros; apply exp_sub_sub. Qed.

Lemma map_sub_sb_eq : forall Ns σ τ, sb_eq σ τ -> List.map (fun M => M[σ]) Ns = List.map (fun M => M[τ]) Ns.
Proof. intros; apply List.map_ext; intros; apply exp_sub_sb_eq; assumption. Qed.


(** Substituting a description twice. *)
Lemma ds_sub_sub_ext : forall R σ τ δ, sb_eq (σ ⨟ τ) δ -> ds_sub (ds_sub R σ) τ = ds_sub R δ.
Proof.
  induction R as [A om | Δ Φ Φx | Θ ? T Φ Ns | Θ A M Rm IH]; intros * Heq; cbn.
  - rewrite (exp_sub_sub_ext _ _ _ _ Heq); f_equal; destruct om; cbn; [ rewrite (exp_sub_sub_ext _ _ _ _ Heq) |]; reflexivity.
  - rewrite tele_sub_sub, (tele_sub_sb_eq _ _ _ Heq), length_tele_sub; f_equal;
      apply gmod_sub_sub_ext, sb_qn_compose_ext; exact Heq.
  - rewrite tele_sub_sub, (tele_sub_sb_eq _ _ _ Heq), length_tele_sub, List.map_map; f_equal.
    apply List.map_ext; intros; apply exp_sub_sub_ext, sb_qn_compose_ext; exact Heq.
  - rewrite tele_sub_sub, (tele_sub_sb_eq _ _ _ Heq), length_tele_sub, (IH _ _ _ Heq); f_equal;
      apply exp_sub_sub_ext, sb_qn_compose_ext; exact Heq.
Qed.
Lemma ds_self_sub : forall M R σ, ds_sub (ds_self M R) σ = ds_self M[σ] (ds_sub R σ).
Proof. intros M [A [] | | |] σ; reflexivity. Qed.

Lemma ds_named_sub : forall Θ Ns M R σ, ds_sub (ds_named Θ Ns M R) σ = ds_named Θ Ns M[σ] (ds_sub R σ).
Proof. intros [|] [|] *; cbn; first [ reflexivity | apply ds_self_sub ]. Qed.

Lemma ds_up_sub : forall Θ' R σ,
    ds_sub (ds_up Θ' R) σ = ds_up (tele_sub Θ' σ) (ds_sub R (sb_qn (length Θ') σ)).
Proof.
  intros Θ' R; induction R as [A om | Δ Φ | Θ ? T Φ Ns | Θ A M Rm IH]; intros σ; cbn.
  - rewrite ctx_pi_sub; f_equal; destruct om; cbn; [ rewrite ctx_fn_sub |]; reflexivity.
  - rewrite tele_sub_app, length_app, sb_qn_plus, ?length_tele_sub; reflexivity.
  - rewrite tele_sub_app, length_app, sb_qn_plus, ?length_tele_sub; reflexivity.
  - rewrite tele_sub_app, length_app, sb_qn_plus, ?length_tele_sub, IH; reflexivity.
Qed.

Lemma fn_view_sub : forall M σ M', fn_view M = Some M' -> fn_view M[σ] = Some M'[q σ].
Proof.
  induction M; repeat match goal with H0 : list_all _ _ _ |- _ => clear H0 end; intros * H; try destruct b as [B0 N | U]; cbn in H |- *; try discriminate.
  - injection H as <-; reflexivity.
  - destruct (fn_view M) as [M0 |] eqn:E; [| discriminate ].
    injection H as <-; rewrite (IHM _ _ eq_refl).
    f_equal; rewrite !exp_sub_sub; apply exp_sub_sb_eq.
    rewrite !sb_q_compose; apply sb_q_cong.
    intros [| x]; reduce_index; [ reflexivity |].
    rewrite sentry_sub_shift_extend; apply sentry_sub_id.
  - destruct (fn_view M) as [M0 |] eqn:E; [| discriminate ].
    injection H as <-; rewrite (IHM _ _ eq_refl).
    f_equal; rewrite !exp_sub_sub; apply exp_sub_sb_eq.
    rewrite !sb_q_compose; apply sb_q_cong.
    intros [| x]; reduce_index; [ reflexivity |].
    rewrite sentry_sub_shift_extend; apply sentry_sub_id.
Qed.

(** Substituting a single term past a lifted substitution, under [k] more
    binders. *)
Lemma sb_qn_extend_comm : forall k σ N,
    sb_eq (sb_qn (S k) σ ⨟ sb_qn k (Id,,N[σ])) (sb_qn k (Id,,N) ⨟ sb_qn k σ).
Proof.
  intros; replace (S k) with (k + 1) by lia; rewrite sb_qn_plus; cbn [sb_qn].
  transitivity (sb_qn k (q σ ⨟ (Id,,N[σ]))); [ apply sb_qn_compose_ext; reflexivity |].
  symmetry; transitivity (sb_qn k ((Id,,N) ⨟ σ)); [ apply sb_qn_compose_ext; reflexivity |].
  apply sb_qn_cong; rewrite sb_q_extend, sb_extend_compose, sb_compose_id_left; reflexivity.
Qed.

Lemma sb_qn_extendm_comm : forall k σ U,
    sb_eq (sb_qn (S k) σ ⨟ sb_qn k (Id ,,ₘ me_lit U[σ]ᵘ)) (sb_qn k (Id ,,ₘ me_lit U) ⨟ sb_qn k σ).
Proof.
  intros; replace (S k) with (k + 1) by lia; rewrite sb_qn_plus; cbn [sb_qn].
  transitivity (sb_qn k (q σ ⨟ (Id ,,ₘ me_lit U[σ]ᵘ))); [ apply sb_qn_compose_ext; reflexivity |].
  symmetry; transitivity (sb_qn k ((Id ,,ₘ me_lit U) ⨟ σ)); [ apply sb_qn_compose_ext; reflexivity |].
  apply sb_qn_cong; rewrite sb_q_extend_gen, sb_extend_compose_gen, sb_compose_id_left; reflexivity.
Qed.

Lemma sb_qn_extenddm_comm : forall k σ N U,
    sb_eq (sb_qn (S k) σ ⨟ sb_qn k (Id ,,ᵈ N[σ] ‖ me_lit U[σ]ᵘ)) (sb_qn k (Id ,,ᵈ N ‖ me_lit U) ⨟ sb_qn k σ).
Proof.
  intros; replace (S k) with (k + 1) by lia; rewrite sb_qn_plus; cbn [sb_qn].
  transitivity (sb_qn k (q σ ⨟ (Id ,,ᵈ N[σ] ‖ me_lit U[σ]ᵘ))); [ apply sb_qn_compose_ext; reflexivity |].
  symmetry; transitivity (sb_qn k ((Id ,,ᵈ N ‖ me_lit U) ⨟ σ)); [ apply sb_qn_compose_ext; reflexivity |].
  apply sb_qn_cong; rewrite sb_q_extend_gen, sb_extend_compose_gen, sb_compose_id_left; reflexivity.
Qed.

Lemma sb_qn_S : forall k σ, sb_qn (S k) σ = sb_qn k (q σ).
Proof. intros; replace (S k) with (k + 1) by lia; rewrite sb_qn_plus; reflexivity. Qed.

Lemma tele_split_sub : forall R σ,
    match tele_split R, tele_split (rev (tele_sub (rev R) σ)) with
    | inl (B, T, τ), inl (B', T', τ') =>
        B' = B[σ] /\ T' = tele_sub T (q σ) /\ sb_eq (sb_qn (length R) σ ⨟ τ') (τ ⨟ sb_qn (S (length T)) σ)
    | inr τ, inr τ' => sb_eq (sb_qn (length R) σ ⨟ τ') (τ ⨟ σ)
    | _, _ => False
    end.
Proof.
  induction R as [| [B0 | B0 N | U | B0 N U] R IH]; intros σ.
  - cbn; rewrite sb_compose_id_right, sb_compose_id_left; reflexivity.
  - rewrite tele_sub_rev_cons, rev_involutive; cbn [centry_sub tele_split length].
    split; [ reflexivity | split; [ rewrite rev_involutive; reflexivity |] ].
    rewrite length_rev, sb_compose_id_right, sb_compose_id_left; reflexivity.
  - rewrite tele_sub_rev_cons, rev_involutive; cbn [centry_sub tele_split length].
    specialize (IH (q σ)).
    destruct (tele_split R) as [[[B' T'] τ] | τ], (tele_split (rev (tele_sub (rev R) (q σ)))) as [[[B'' T''] τ'] | τ'];
      try contradiction.
    + destruct IH as (-> & -> & Hτ); split; [| split ].
      * apply exp_sub_extend_comm.
      * rewrite !tele_sub_sub; apply tele_sub_sb_eq.
        rewrite !sb_q_compose; apply sb_q_cong.
        rewrite sb_q_extend, sb_extend_compose, sb_compose_id_left; reflexivity.
      * rewrite length_tele_sub, <- sb_compose_assoc.
        rewrite ?length_tele_sub, sb_qn_S, Hτ, !sb_compose_assoc; apply sb_compose_Proper; [ reflexivity |].
        rewrite <- sb_qn_S; apply sb_qn_extend_comm.
    + rewrite ?length_tele_sub in *.
      rewrite <- sb_compose_assoc.
      rewrite sb_qn_S, IH, !sb_compose_assoc; apply sb_compose_Proper; [ reflexivity |].
      rewrite sb_q_extend, sb_extend_compose, sb_compose_id_left; reflexivity.
  - rewrite tele_sub_rev_cons, rev_involutive; cbn [centry_sub tele_split length].
    specialize (IH (q σ)).
    destruct (tele_split R) as [[[B' T'] τ] | τ], (tele_split (rev (tele_sub (rev R) (q σ)))) as [[[B'' T''] τ'] | τ'];
      try contradiction.
    + destruct IH as (-> & -> & Hτ); split; [| split ].
      * rewrite !exp_sub_sub; apply exp_sub_sb_eq.
        rewrite sb_q_extend_gen, sb_extend_compose_gen, sb_compose_id_left; reflexivity.
      * rewrite !tele_sub_sub; apply tele_sub_sb_eq.
        rewrite !sb_q_compose; apply sb_q_cong.
        rewrite sb_q_extend_gen, sb_extend_compose_gen, sb_compose_id_left; reflexivity.
      * rewrite length_tele_sub, <- sb_compose_assoc.
        rewrite ?length_tele_sub, sb_qn_S, Hτ, !sb_compose_assoc; apply sb_compose_Proper; [ reflexivity |].
        rewrite <- sb_qn_S; apply sb_qn_extendm_comm.
    + rewrite ?length_tele_sub in *.
      rewrite <- sb_compose_assoc.
      rewrite sb_qn_S, IH, !sb_compose_assoc; apply sb_compose_Proper; [ reflexivity |].
      rewrite sb_q_extend_gen, sb_extend_compose_gen, sb_compose_id_left; reflexivity.
  - rewrite tele_sub_rev_cons, rev_involutive; cbn [centry_sub tele_split length].
    specialize (IH (q σ)).
    destruct (tele_split R) as [[[B' T'] τ] | τ], (tele_split (rev (tele_sub (rev R) (q σ)))) as [[[B'' T''] τ'] | τ'];
      try contradiction.
    + destruct IH as (-> & -> & Hτ); split; [| split ].
      * rewrite !exp_sub_sub; apply exp_sub_sb_eq.
        rewrite sb_q_extend_gen, sb_extend_compose_gen, sb_compose_id_left; reflexivity.
      * rewrite !tele_sub_sub; apply tele_sub_sb_eq.
        rewrite !sb_q_compose; apply sb_q_cong.
        rewrite sb_q_extend_gen, sb_extend_compose_gen, sb_compose_id_left; reflexivity.
      * rewrite length_tele_sub, <- sb_compose_assoc.
        rewrite ?length_tele_sub, sb_qn_S, Hτ, !sb_compose_assoc; apply sb_compose_Proper; [ reflexivity |].
        rewrite <- sb_qn_S; apply sb_qn_extenddm_comm.
    + rewrite ?length_tele_sub in *.
      rewrite <- sb_compose_assoc.
      rewrite sb_qn_S, IH, !sb_compose_assoc; apply sb_compose_Proper; [ reflexivity |].
      rewrite sb_q_extend_gen, sb_extend_compose_gen, sb_compose_id_left; reflexivity.
Qed.

Lemma ds_at_sub : forall R N R' σ,
    ds_at R N = Some R' -> ds_at (ds_sub R σ) N[σ] = Some (ds_sub R' σ).
Proof.
  induction R as [A om | Δ Φ | Θ ? T Φ Ns | Θ A M Rm IH]; intros N R' σ Ha; cbn in Ha |- *.
  - destruct (pi_view A) as [[B C] |] eqn:E; [| discriminate ].
    rewrite (pi_view_sub _ _ _ _ E).
    destruct om as [M |]; cbn.
    + destruct (fn_view M) as [M' |] eqn:Ef; [| discriminate ]; injection Ha as <-.
      rewrite (fn_view_sub _ _ _ Ef); cbn; rewrite !exp_sub_extend_comm; reflexivity.
    + injection Ha as <-; cbn; rewrite exp_sub_extend_comm; reflexivity.
  - pose proof (tele_split_sub (rev Δ) σ) as Hs; rewrite rev_involutive in Hs.
    destruct (tele_split (rev Δ)) as [[[B Δ'] τ] | τ], (tele_split (rev (tele_sub Δ σ))) as [[[B' Δ''] τ'] | τ'];
      try contradiction; try discriminate.
    injection Ha as <-; destruct Hs as (-> & -> & Hτ); cbn; f_equal; f_equal.
    + rewrite !tele_sub_sub; apply tele_sub_sb_eq.
      rewrite sb_q_extend, sb_extend_compose, sb_compose_id_left; reflexivity.
    + rewrite !gmod_sub_sub, length_tele_sub, length_tele_sub; apply gmod_sub_sb_eq.
      rewrite length_rev in Hτ; rewrite <- sb_compose_assoc, Hτ, !sb_compose_assoc.
      apply sb_compose_Proper; [ reflexivity | apply sb_qn_extend_comm ].
    + rewrite !gmod_sub_sub, length_tele_sub, length_tele_sub; apply gmod_sub_sb_eq.
      rewrite length_rev in Hτ; rewrite <- sb_compose_assoc, Hτ, !sb_compose_assoc.
      apply sb_compose_Proper; [ reflexivity | apply sb_qn_extend_comm ].
  - pose proof (tele_split_sub (rev Θ) σ) as Hs; rewrite rev_involutive in Hs.
    destruct (tele_split (rev Θ)) as [[[B Θ'] τ] | τ], (tele_split (rev (tele_sub Θ σ))) as [[[B' Θ''] τ'] | τ'];
      try contradiction; injection Ha as <-; cbn; f_equal; f_equal.
    + destruct Hs as (-> & -> & Hτ).
      rewrite !tele_sub_sub; apply tele_sub_sb_eq.
      rewrite sb_q_extend, sb_extend_compose, sb_compose_id_left; reflexivity.
    + destruct Hs as (-> & -> & Hτ).
      rewrite !map_sub_sub, length_tele_sub, length_tele_sub; apply map_sub_sb_eq.
      rewrite length_rev in Hτ; rewrite <- sb_compose_assoc, Hτ, !sb_compose_assoc.
      apply sb_compose_Proper; [ reflexivity | apply sb_qn_extend_comm ].
    + rewrite List.map_app; cbn; f_equal.
      rewrite !map_sub_sub; apply map_sub_sb_eq; rewrite length_rev in Hs; exact Hs.
  - destruct (ds_at Rm N) as [Rm' |] eqn:Ea; [| discriminate ]; rewrite (IH _ _ σ Ea).
    pose proof (tele_split_sub (rev Θ) σ) as Hs; rewrite rev_involutive in Hs.
    destruct (tele_split (rev Θ)) as [[[B Θ'] τ] | τ], (tele_split (rev (tele_sub Θ σ))) as [[[B' Θ''] τ'] | τ'];
      try contradiction; injection Ha as <-; cbn; [| reflexivity ].
    destruct Hs as (-> & -> & Hτ); rewrite length_rev in Hτ.
    assert (Hc : sb_eq (sb_qn (length Θ) σ ⨟ (τ' ⨟ sb_qn (length (tele_sub Θ' (q σ))) (Id,,N[σ])))
                       ((τ ⨟ sb_qn (length Θ') (Id,,N)) ⨟ sb_qn (length (tele_sub Θ' (Id,,N))) σ)).
    { rewrite !length_tele_sub, <- sb_compose_assoc, Hτ, !sb_compose_assoc.
      apply sb_compose_Proper; [ reflexivity | apply sb_qn_extend_comm ]. }
    f_equal; f_equal.
    + rewrite !tele_sub_sub; apply tele_sub_sb_eq.
      rewrite sb_q_extend, sb_extend_compose, sb_compose_id_left; reflexivity.
    + rewrite !exp_sub_sub; apply exp_sub_sb_eq; exact Hc.
    + rewrite !exp_sub_sub; apply exp_sub_sb_eq; exact Hc.
Qed.

Lemma ds_ats_sub : forall Ns R R' σ,
    ds_ats R Ns = Some R' -> ds_ats (ds_sub R σ) (List.map (fun M => M[σ]) Ns) = Some (ds_sub R' σ).
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha |- *; [ injection Ha as <-; reflexivity |].
  destruct (ds_at R N) as [R0 |] eqn:E; [| discriminate ].
  rewrite (ds_at_sub _ _ _ σ E); apply IH; exact Ha.
Qed.

(** [ds_at_tm] commutes with substitution: a [λ] or a type former applied
    stays one under [σ]. *)
Lemma ds_at_tm_sub : forall R N R' σ,
    ds_at_tm R N = Some R' -> ds_at_tm (ds_sub R σ) N[σ] = Some (ds_sub R' σ).
Proof.
  intros [A [M |] | | |] N R' σ Ha; cbn [ds_at_tm] in Ha; try exact (ds_at_sub _ _ _ σ Ha).
  destruct (pi_view A) as [[B C] |] eqn:E; [| discriminate ].
  cbn [ds_sub ds_at_tm option_map]; rewrite (pi_view_sub _ _ _ _ E).
  destruct (fn_view M) as [M' |] eqn:Ef.
  - injection Ha as <-; rewrite (fn_view_sub _ _ _ Ef); cbn; rewrite !exp_sub_extend_comm; reflexivity.
  - destruct (app_const M) eqn:Hc; [| discriminate ]; injection Ha as <-.
    rewrite (app_const_fn_view _ (app_const_sub _ σ Hc)), (app_const_sub _ σ Hc); cbn; rewrite exp_sub_extend_comm; reflexivity.
Qed.

(** So does [ds_ats_tm], argument by argument. *)
Lemma ds_ats_tm_sub : forall Ns R R' σ,
    ds_ats_tm R Ns = Some R' -> ds_ats_tm (ds_sub R σ) (List.map (fun M => M[σ]) Ns) = Some (ds_sub R' σ).
Proof.
  induction Ns as [| N Ns IH]; intros * Ha; cbn in Ha |- *; [ injection Ha as <-; reflexivity |].
  destruct (ds_at_tm R N) as [R0 |] eqn:E; [| discriminate ].
  rewrite (ds_at_tm_sub _ _ _ σ E); apply IH; exact Ha.
Qed.

Lemma ds_ats_read_sub : forall Ns R R' σ,
    ds_ats_read R Ns = Some R' -> ds_ats_read (ds_sub R σ) (List.map (fun M => M[σ]) Ns) = Some (ds_sub R' σ).
Proof.
  intros Ns R R' σ Ha; destruct R as [| | | [| e Θd] A M Rm]; cbn [ds_ats_read ds_sub tele_sub] in Ha |- *;
    try (apply (ds_ats_sub _ _ _ σ Ha)).
  (* a definition with a module part: its term part and its module part,
     each given the arguments *)
  destruct (ds_ats_tm (ds_term A (Some M)) Ns) as [[B [M' |] | | |] |] eqn:Et; try discriminate.
  destruct (ds_ats Rm Ns) as [Rm' |] eqn:E; [| discriminate ]; injection Ha as <-.
  cbn [length sb_qn ds_sub].
  pose proof (ds_ats_tm_sub _ _ _ σ Et) as Ht'; cbn [ds_sub option_map] in Ht'; rewrite Ht', (ds_ats_sub _ _ _ σ E); reflexivity.
Qed.

(** A closed description is not moved. *)
Lemma ds_closed_sub : forall R σ, ds_scoped 0 R -> ds_sub R σ = R.
Proof.
  induction R as [A om | Δ Φ | Θ p0 T Φ Ns | Θ A M Rm IH]; intros σ HR; cbn in *.
  - destruct HR as [HA Hom]; rewrite exp_closed_sub by exact HA; destruct om; cbn in *; [ rewrite exp_closed_sub by exact Hom |]; reflexivity.
  - destruct HR as [HR1 HR2].
    pose proof (gunit_closed_sub _ σ HR1) as H; rewrite gunit_sub_mk in H; cbn in H; injection H as -> ->.
    pose proof (gunit_closed_sub _ σ HR2) as H; rewrite gunit_sub_mk in H; cbn in H; injection H as _ ->; reflexivity.
  - destruct HR as (HΘ & _ & HNs); rewrite tele_closed_sub by exact HΘ; f_equal.
    rewrite <- (List.map_id Ns) at 2; apply List.map_ext_in; intros M HM.
    eapply exp_scoped_sub_id; [ eapply List.Forall_forall in HNs; [ exact HNs | exact HM ] |].
    intros x Hx; apply sb_qn_lt; lia.
  - destruct HR as (HΘ & [HA HM] & HRm); rewrite tele_closed_sub by exact HΘ; rewrite IH by exact HRm; f_equal.
    + eapply exp_scoped_sub_id; [ exact HA |]; intros x Hx; apply sb_qn_lt; lia.
    + eapply exp_scoped_sub_id; [ exact HM |]; intros x Hx; apply sb_qn_lt; lia.
Qed.

(** The term part and the δ-reduct, substituted. *)
Lemma sb_of_list_compose_gen : forall Ns σ σ' τ n,
    (forall x, x < n -> (σ ⨟ τ) x = σ' x) ->
    forall x, x < length Ns + n -> (sb_of_list σ Ns ⨟ τ) x = sb_of_list σ' (List.map (fun M => M[τ]) Ns) x.
Proof.
  induction Ns as [| N Ns IH]; intros * Hσ x Hx; cbn in *; [ apply Hσ; lia |].
  apply (IH _ _ _ (S n)); [| lia ].
  intros [| y] Hy; cbn; [ reflexivity | apply Hσ; lia ].
Qed.

Lemma ds_ty_sub : forall R A σ, ds_ty R = Some A -> ds_ty (ds_sub R σ) = Some A[σ].
Proof.
  intros * Ht; destruct R as [A0 om | | | Θ' A0 M0 Rm]; cbn in *; try discriminate.
  - injection Ht as <-; reflexivity.
  - injection Ht as <-; rewrite ctx_pi_sub; reflexivity.
Qed.

Lemma ds_red_sub : forall R M σ, ds_red R = Some M -> ds_red (ds_sub R σ) = Some M[σ].
Proof.
  intros [A om | | | Θ' A M0 Rm] * Hr; cbn in *; try discriminate.
  - subst; reflexivity.
  - injection Hr as <-; rewrite ctx_fn_sub; reflexivity.
Qed.

Lemma ds_mod_sub : forall R R' σ, ds_mod R = Some R' -> ds_mod (ds_sub R σ) = Some (ds_sub R' σ).
Proof.
  intros R; induction R as [A om | Δ Φ | Θ0 p0 T Φ Ns | Θ0 A M Rm IH]; intros R' σ Hm;
    cbn in *; try discriminate; try (injection Hm as <-; reflexivity).
  exact (IH _ _ Hm).
Qed.

Lemma ds_tele_sub : forall R T σ,
    (forall Θ p T0 Φ Ns, R = ds_closed Θ p T0 Φ Ns -> ctx_scoped 0 T0) ->
    ds_tele R = Some T -> ds_tele (ds_sub R σ) = Some (tele_sub T σ).
Proof.
  intros [A om | Δ Φ | Θ p0 T0 Φ Ns | Θ A M Rm] * Hcl Ht; cbn in *; try discriminate.
  - injection Ht as <-; reflexivity.
  - specialize (Hcl _ _ _ _ _ eq_refl).
    rewrite List.length_map; destruct (Nat.leb_spec (length Ns) (length T0)) as [Hle |]; [| discriminate ].
    injection Ht as <-; f_equal.
    rewrite tele_sub_app, tele_sub_sub, ?length_tele_sub; f_equal.
    eapply tele_scoped_sub_agree.
    + rewrite <- (List.firstn_skipn (length T0 - length Ns) T0) in Hcl.
      apply ctx_scoped_app in Hcl as [HF _].
      rewrite List.length_skipn in HF; replace (length T0 - (length T0 - length Ns)) with (length Ns) in HF by lia.
      rewrite Nat.add_0_r in HF; exact HF.
    + intros x Hx; symmetry; apply (sb_of_list_compose_gen _ _ _ _ 0); [ intros; lia | lia ].
Qed.


(** Filling in the entries before a member commutes with a substitution of
    the body's context. *)
Lemma gm_fill_sub : forall Φ n σ τ, gm_fill Φ = Some τ ->
    exists τ', gm_fill (gmod_sub Φ (sb_qn n σ)) = Some τ' /\
               sb_eq (sb_qn (gm_binders Φ + n) σ ⨟ τ') (τ ⨟ sb_qn n σ).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hf; cbn in Hf.
  - injection Hf as <-; exists Id; split; [ reflexivity |].
    cbn [gm_binders Nat.add]; rewrite sb_compose_id_right, sb_compose_id_left; reflexivity.
  - destruct E as [b pv A [M |] | pv U | ? ? ? ? | pv A M U | ? ? ?]; try discriminate;
      destruct (gm_fill Φ) as [τ0 |] eqn:E0; cbn in Hf; try discriminate; injection Hf as <-;
      destruct (IH n σ _ eq_refl) as (τ0' & Hf' & Heq).
    + exists (τ0' ,, M[sb_qn (gm_binders Φ) (sb_qn n σ)][τ0']); cbn; rewrite Hf'; cbn; split; [ reflexivity |].
      rewrite sb_q_compose_extend, sb_extend_compose, <- sb_qn_plus, Heq, !exp_sub_sub, Heq; reflexivity.
    + exists (τ0' ,,ₘ me_lit (U[sb_qn (gm_binders Φ) (sb_qn n σ)]ᵘ)[τ0']ᵘ); cbn; rewrite Hf'; cbn; split; [ reflexivity |].
      rewrite sb_q_compose_extend_gen, sb_extend_compose_gen, <- sb_qn_plus, Heq; cbn [sentry_sub modexp_sub].
      rewrite !gunit_sub_sub, Heq; reflexivity.
    + exists (τ0' ,,ᵈ M[sb_qn (gm_binders Φ) (sb_qn n σ)][τ0'] ‖ me_lit (U[sb_qn (gm_binders Φ) (sb_qn n σ)]ᵘ)[τ0']ᵘ);
        cbn; rewrite Hf'; cbn; split; [ reflexivity |].
      rewrite sb_q_compose_extend_gen, sb_extend_compose_gen, <- sb_qn_plus, Heq; cbn [sentry_sub modexp_sub].
      rewrite !exp_sub_sub, !gunit_sub_sub, Heq; reflexivity.
  - discriminate.
Qed.

(** A body can be filled in exactly when it can after a substitution. *)
Lemma gm_fill_sub_none : forall Φ τ, gm_fill (gmod_sub Φ τ) = None <-> gm_fill Φ = None.
Proof.
  assert (Hom : forall A B (f : A -> B) (o : option A), option_map f o = None <-> o = None)
    by (intros ? ? ? []; cbn; split; congruence).
  induction Φ as [| Φ IH y E | Φ IH H its]; intros; cbn; [ split; discriminate | | split; reflexivity ].
  destruct E as [b pv A [M |] | pv U | ? ? ? ? | ? ? ? ? | ? ? ?]; cbn; rewrite ?Hom, ?IH; tauto.
Qed.

(** The entry of a substituted body named [y], and the entries before it. *)
Lemma gm_prefix_sub_inv : forall Φ τ y Φ0w Ew, gm_prefix_upto (gmod_sub Φ τ) y = Some (gm_ext Φ0w y Ew) ->
    exists Φ0 E, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) /\ Φ0w = gmod_sub Φ0 τ /\
      Ew = gentry_sub E (sb_qn (gm_binders Φ0) τ).
Proof.
  intros * Hp; rewrite gm_prefix_upto_sub in Hp.
  destruct (gm_prefix_upto Φ y) as [Φ1 |] eqn:Hp0; cbn in Hp; [| discriminate ]; injection Hp as Hp.
  destruct Φ1 as [| Φ0 z E | ? ? ?]; cbn in Hp; try discriminate; injection Hp as H1 H2 H3; subst.
  exists Φ0, E; split; [ first [ exact Hp0 | reflexivity ] | split; reflexivity ].
Qed.

(** The parts of a substituted entry are its parts substituted. *)
Lemma entry_tm_sub_inv : forall E σ A' M', entry_tm (gentry_sub E σ) = Some (A', M') ->
    exists A M, entry_tm E = Some (A, M) /\ A' = A[σ] /\ M' = M[σ].
Proof.
  intros [b pv A [M |] | | | pv A M U |] * He; cbn in He; try discriminate; injection He as <- <-.
  all: do 2 eexists; split; [ reflexivity | split; reflexivity ].
Qed.

Lemma entry_unit_sub_inv : forall E σ U', entry_unit (gentry_sub E σ) = Some U' ->
    exists U, entry_unit E = Some U /\ U' = U[σ]ᵘ.
Proof.
  intros [| pv U | | pv A M U |] * He; cbn in He; try discriminate; injection He as <-.
  all: eexists; split; reflexivity.
Qed.

Lemma entry_tm_sub : forall E σ A M, entry_tm E = Some (A, M) -> entry_tm (gentry_sub E σ) = Some (A[σ], M[σ]).
Proof. intros [b pv A0 [M0 |] | | | pv A0 M0 U |] * He; cbn in He |- *; try discriminate; injection He as <- <-; reflexivity. Qed.

Lemma entry_unit_sub : forall E σ U, entry_unit E = Some U -> entry_unit (gentry_sub E σ) = Some U[σ]ᵘ.
Proof. intros [| pv U0 | | pv A M U0 |] * He; cbn in He |- *; try discriminate; injection He as <-; reflexivity. Qed.

(** The type and body of an entry, filled in after a substitution, are the
    filled-in ones substituted. *)
Lemma fill_sub_exp : forall A k n σ τ τ', sb_eq (sb_qn (k + n) σ ⨟ τ') (τ ⨟ sb_qn n σ) ->
    A[sb_qn k (sb_qn n σ)][τ'] = A[τ][sb_qn n σ].
Proof. intros * Heq; rewrite <- sb_qn_plus, !exp_sub_sub, Heq; reflexivity. Qed.

Lemma fill_sub_modexp : forall H k n σ τ τ', sb_eq (sb_qn (k + n) σ ⨟ τ') (τ ⨟ sb_qn n σ) ->
    H[sb_qn k (sb_qn n σ)]ᵐ[τ']ᵐ = H[τ]ᵐ[sb_qn n σ]ᵐ.
Proof. intros * Heq; rewrite <- sb_qn_plus, !modexp_sub_sub, Heq; reflexivity. Qed.

Lemma fill_sub_unit : forall U k n σ τ τ', sb_eq (sb_qn (k + n) σ ⨟ τ') (τ ⨟ sb_qn n σ) ->
    U[sb_qn k (sb_qn n σ)]ᵘ[τ']ᵘ = U[τ]ᵘ[sb_qn n σ]ᵘ.
Proof. intros * Heq; rewrite <- sb_qn_plus, !gunit_sub_sub, Heq; reflexivity. Qed.
(** The entries of a description, substituted. *)
Lemma ds_entry_sub_open : forall Δ Φw Φ y Γy E rd σ,
    ds_entry (ds_open Δ Φw Φ) y = Some (Γy, E, rd) ->
    ds_entry (ds_sub (ds_open Δ Φw Φ) σ) y = Some (tele_sub Γy σ, gentry_sub E (sb_qn (length Γy) σ), rd_sub rd σ).
Proof.
  intros * He; cbn in *.
  rewrite gm_prefix_upto_sub.
  destruct (gm_prefix_upto Φ y) as [[| Φ' x E' | Φ' H its] |]; cbn in *; try discriminate.
  destruct E' as [[|] ? ? [] | | | | ]; try discriminate; injection He as <- <- <-; cbn.
  all: rewrite tele_sub_app, body_ctx_sub, length_app, length_body_ctx, sb_qn_plus; reflexivity.
Qed.

Lemma ds_entry_open_rd : forall Δ Φw Φ y Γy E rd, ds_entry (ds_open Δ Φw Φ) y = Some (Γy, E, rd) ->
    exists Φ', Γy = body_ctx Φ' ++ Δ /\ rd = reader_open Δ Φ'.
Proof.
  intros * He; cbn in He.
  destruct (gm_prefix_upto Φ y) as [[| Φ' x E' | Φ' H its] |]; try discriminate.
  destruct E' as [[|] ? ? [] | | | | ]; try discriminate; injection He as <- <- <-; eauto.
Qed.

Lemma ds_entry_sub_closed : forall Θ p T Φ Ns y Γy E rd σ,
    ds_entry (ds_closed Θ p T Φ Ns) y = Some (Γy, E, rd) ->
    ds_entry (ds_sub (ds_closed Θ p T Φ Ns) σ) y = Some (Γy, E, rd_sub rd σ).
Proof.
  intros * He; cbn in *.
  destruct (gm_prefix_upto Φ y) as [[| Φ' x E' | Φ' H its] |]; cbn in *; try discriminate.
  injection He as <- <- <-; cbn; rewrite apps_sub; cbn; rewrite qname_mod_sub; reflexivity.
Qed.

Lemma ds_entry_closed : forall Θ p T Φ Ns y Γy E rd,
    unit_closed T Φ -> ds_entry (ds_closed Θ p T Φ Ns) y = Some (Γy, E, rd) ->
    Γy = nil /\ entry_sc 0 E /\ rd = reader_closed Θ Ns (apps (a_mem (qname_mod p) y) Ns).
Proof.
  intros * HU He.
  pose proof (ds_entry_scoped (ds_closed Θ p T Φ Ns) y Γy E rd 0) as Hs; cbn in He.
  destruct (gm_prefix_upto Φ y) as [[| Φ' x E' | Φ' H its] |] eqn:Hp; try discriminate.
  injection He as <- <- <-; split; [ reflexivity | split; [| reflexivity ] ].
  destruct HU as [HT HΦ].
  pose proof (body_closed_prefix _ _ _ _ HΦ Hp) as HΦx; cbn in HΦx; destruct HΦx as [_ HE'].
  cbn [length]; destruct E' as [b pv A0 B | pv [Δ [[|] Φ1 | E1]] | pv pq k0 D Φ1 | pv Aa Ma Ua | pv pr Rr Φ1]; cbn in HE' |- *.
  - exact HE'.
  - destruct HE' as [[=] _].
  - destruct HE' as (_ & HΔ & HΦ1); right; do 2 eexists; split; [ reflexivity |].
    split; [ apply ctx_scoped_app; split; [ rewrite Nat.add_0_r; exact HΔ | exact HT ] | rewrite length_app; exact HΦ1 ].
  - left; exact HE'.
  - exact (proj1 HE').
  - exact HE'.
  - destruct HE' as [[HF HS] _]; split; [ exact (proj2 (proj1 (ctx_scoped_app_iff _ _) HF)) | exact HS ].
Qed.

(** A closed unit and a closed body are not moved. *)
Lemma body_closed_sub_id : forall Φ k σ, body_closed k Φ -> (forall x, x < k -> σ x = se_var x) -> gmod_sub Φ σ = Φ.
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] k σ HΦ Hσ; cbn in HΦ |- *; [ reflexivity | | contradiction ].
  destruct HΦ as [HΦ HE]; rewrite (IH Φ k σ HΦ Hσ); f_equal.
  assert (Hσ' : forall x, x < gm_binders Φ + k -> sb_qn (gm_binders Φ) σ x = se_var x) by (apply sb_qn_fix; exact Hσ).
  destruct E as [b pv A B | pv [Δ [sm Φ1 | E1]] | pv pq k0 D Φ1 | pv Aa Ma Ua | pv pr Rr Φ1]; cbn in HE |- *.
  - destruct HE as [HA HB]; rewrite exp_closed_sub by exact HA; destruct B; cbn in *; [ rewrite exp_closed_sub by exact HB |]; reflexivity.
  - destruct HE as (-> & HΔ & HΦ1).
    rewrite gunit_sub_mk; cbn [moddef_sub]; f_equal; f_equal.
    + eapply tele_sub_id_gen; [| exact HΔ |].
      * apply List.Forall_forall; intros e _ n τ He Hτ.
        exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_scoped_sub_id)))))) _ _ _ He Hτ).
      * intros x Hx; apply Hσ'; lia.
    + f_equal; eapply IH; [ exact HΦ1 |].
      apply sb_qn_fix; intros x Hx; apply Hσ'; lia.
  - rewrite gunit_closed_sub by exact HE; reflexivity.
  - destruct HE as [HD HΦ1]; f_equal.
    eapply IH; [ exact HΦ1 |].
    intros x Hx; rewrite sb_qn_lt by (unfold ind_nu; lia); reflexivity.
  - destruct HE as (HA & HM & HU); rewrite !exp_closed_sub, gunit_closed_sub by assumption; reflexivity.
  - destruct HE as [_ HΦ1]; f_equal; eapply IH; [ exact HΦ1 |].
    intros x Hx; exact (sb_qn_lt (S (length (record_params Rr))) _ x Hx).
Qed.

Lemma unit_closed_sub : forall T Φ σ, unit_closed T Φ -> (gu_body T Φ)[σ]ᵘ = gu_body T Φ.
Proof.
  intros * [HT HΦ]; rewrite gunit_sub_mk, tele_closed_sub by exact HT; cbn [moddef_sub]; f_equal; f_equal.
  eapply body_closed_sub_id; [ exact HΦ |]; intros x Hx; apply sb_qn_lt; lia.
Qed.

(** What a closed entry denotes is closed, and it denotes the same anywhere. *)
Lemma entry_closed_sub : forall E σ, entry_sc 0 E ->
    match E with ge_ind _ _ _ _ _ | ge_record _ _ _ _ => True | _ => gentry_sub E σ = E end.
Proof.
  intros [b pv A B | pv U | pv pq k D Φ | pv A M U | pv pr R Φ] σ HE; cbn in HE |- *; [| | exact I | | exact I ].
  - destruct HE as [HA HB]; rewrite exp_closed_sub by exact HA; destruct B; cbn in *; [ rewrite exp_closed_sub by exact HB |]; reflexivity.
  - destruct HE as [HU | (T & Φ & -> & HU)]; [ rewrite gunit_closed_sub by exact HU | rewrite unit_closed_sub by exact HU ]; reflexivity.
  - destruct HE as (HA & HM & HU); rewrite !exp_closed_sub, gunit_closed_sub by assumption; reflexivity.
Qed.


(** ** Descriptions under a Substitution, and Weakening *)

Definition sub_mod_compat (σ : sub) (Γ Δ : ctx) : Prop :=
  forall x U, Δ ∋ #x ≔ₘ U ->
    sentry_modexp (σ x) = me_lit U[σ]ᵘ \/ exists y, σ x = se_var y /\ Γ ∋ #y ≔ₘ U[σ]ᵘ.

(** The root of a module expression, if it is a slot, is a module slot of
    [Γ].  A same-unit substitution sends such a root to a root. *)
Fixpoint me_slot_root (Γ : ctx) (H : modexp) : Prop :=
  match H with
  | me_mem H _ | me_app H _ => me_slot_root Γ H
  | me_var x => exists U, Γ ∋ #x ≔ₘ U
  | _ => True
  end.

Lemma mod_qname_slot_root : forall Γ H p, mod_qname H = Some p -> me_slot_root Γ H.
Proof.
  induction H as [fp | x | H IHH y | H IHH N | U]; intros * Hp; cbn in *; try discriminate; auto.
  destruct (mod_qname H) eqn:E; [ eauto | discriminate ].
Qed.

Lemma modexp_spine_sub : forall H R args pre σ Γ Δ,
    sub_mod_compat σ Γ Δ ->
    me_slot_root Δ H ->
    modexp_spine H = (R, args, pre) ->
    modexp_spine H[σ]ᵐ = (R[σ]ᵐ, map (fun N => N[σ]) args, pre).
Proof.
  induction H as [| n | H IHH y | H IHH N |]; intros * Hσ Hr Hs; cbn in Hr, Hs |- *;
    try (injection Hs as <- <- <-; reflexivity).
  - injection Hs as <- <- <-; destruct Hr as [U HU]; cbn.
    destruct (Hσ _ _ HU) as [-> | (y & -> & _)]; reflexivity.
  - destruct (modexp_spine H) as [[R' args'] pre'] eqn:E; injection Hs as <- <- <-.
    rewrite (IHH _ _ _ _ _ _ Hσ Hr eq_refl); reflexivity.
  - destruct (modexp_spine H) as [[R' args'] pre'] eqn:E; injection Hs as <- <- <-.
    rewrite (IHH _ _ _ _ _ _ Hσ Hr eq_refl), map_app; reflexivity.
Qed.

Lemma me_noargs_sub : forall H σ Γ Δ,
    sub_mod_compat σ Γ Δ -> me_slot_root Δ H -> me_noargs H -> me_noargs H[σ]ᵐ.
Proof.
  induction H as [| n | H IHH y | H IHH N |]; intros * Hσ Hr HH; cbn in *; eauto.
  destruct Hr as [U HU]; destruct (Hσ _ _ HU) as [-> | (y & -> & _)]; exact I.
Qed.

Lemma sub_mod_compat_q : forall σ Γ Δ e,
    sub_mod_compat σ Γ Δ -> sub_mod_compat (q σ) (centry_sub e σ :: Γ) (e :: Δ).
Proof.
  intros * Hσ x U Hlk; inversion Hlk; subst; cbn.
  1,2: right; exists 0; rewrite sb_q_zero, gunit_wk_shift_sub_q; split; [ reflexivity | constructor ].
  rewrite sb_q_succ, gunit_wk_shift_sub_q.
  match goal with Hl : _ ∋ # _ ≔ₘ _ |- _ => destruct (Hσ _ _ Hl) as [Heq | (y & -> & Hy)] end;
    [ left; rewrite <- sentry_modexp_wk, Heq; reflexivity |].
  right; exists (S y); split; [ reflexivity | constructor; assumption ].
Qed.

Lemma sub_mod_compat_ext : forall Ψ σ Γ Δ,
    sub_mod_compat σ Γ Δ -> sub_mod_compat (sb_qn (length Ψ) σ) (tele_sub Ψ σ ++ Γ) (Ψ ++ Δ).
Proof. induction Ψ; intros; cbn; auto using sub_mod_compat_q. Qed.

(** The same at the module slots below [m] only: what a module expression
    scoped at [m] denotes reads no other slot. *)
Definition sub_mod_compat_lt (m : nat) (σ : sub) (Γ Δ : ctx) : Prop :=
  forall x U, x < m -> Δ ∋ #x ≔ₘ U ->
    sentry_modexp (σ x) = me_lit U[σ]ᵘ \/ exists y, σ x = se_var y /\ Γ ∋ #y ≔ₘ U[σ]ᵘ.

Lemma sub_mod_compat_lt_of : forall m σ Γ Δ, sub_mod_compat σ Γ Δ -> sub_mod_compat_lt m σ Γ Δ.
Proof. intros * Hσ x U _ Hl; exact (Hσ _ _ Hl). Qed.

Lemma sub_mod_compat_lt_q : forall m σ Γ Δ e,
    sub_mod_compat_lt m σ Γ Δ -> sub_mod_compat_lt (S m) (q σ) (centry_sub e σ :: Γ) (e :: Δ).
Proof.
  intros * Hσ x U Hx Hlk; inversion Hlk; subst; cbn.
  1,2: right; exists 0; rewrite sb_q_zero, gunit_wk_shift_sub_q; split; [ reflexivity | constructor ].
  rewrite sb_q_succ, gunit_wk_shift_sub_q.
  match goal with Hl : _ ∋ # ?n ≔ₘ ?U0 |- _ => destruct (Hσ n U0 ltac:(lia) Hl) as [Heq | (y & -> & Hy)] end;
    [ left; rewrite <- sentry_modexp_wk, Heq; reflexivity |].
  right; exists (S y); split; [ reflexivity | constructor; assumption ].
Qed.

Lemma sub_mod_compat_lt_ext : forall Ψ m σ Γ Δ,
    sub_mod_compat_lt m σ Γ Δ -> sub_mod_compat_lt (length Ψ + m) (sb_qn (length Ψ) σ) (tele_sub Ψ σ ++ Γ) (Ψ ++ Δ).
Proof. induction Ψ; intros; cbn; auto using sub_mod_compat_lt_q. Qed.

Lemma sub_mod_compat_compose : forall σ τ Γ0 Γ1 Δ,
    sub_mod_compat σ Γ1 Δ -> sub_mod_compat τ Γ0 Γ1 -> sub_mod_compat (σ ⨟ τ) Γ0 Δ.
Proof.
  intros * Hσ Hτ x U Hl; cbn [sb_compose].
  destruct (Hσ _ _ Hl) as [Heq | (y & -> & Hy)].
  - left; rewrite <- sentry_modexp_sub, Heq; cbn [modexp_sub]; rewrite gunit_sub_sub; reflexivity.
  - cbn [sentry_sub]; destruct (Hτ _ _ Hy) as [Heq | (z & -> & Hz)]; rewrite ?gunit_sub_sub in *; [ left | right; eauto ]; exact Heq.
Qed.

(** Substituting away an entry that is not a module. *)
Lemma sub_mod_compat_single_term : forall Γ e N, (forall U, e <> ce_mod U) -> (forall A M U, e <> ce_dm A M U) ->
    sub_mod_compat (Id,,N) Γ (e :: Γ).
Proof.
  intros * He Hd x U Hl; inversion Hl; subst; [ exfalso; eapply He; reflexivity | exfalso; eapply Hd; reflexivity |].
  right; eexists; split; [ reflexivity |].
  rewrite gunit_sub_shift_extend, gunit_sub_id; assumption.
Qed.

Lemma sub_mod_compat_single_mod : forall Γ U, sub_mod_compat (Id ,,ₘ me_lit U) Γ (ce_mod U :: Γ).
Proof.
  intros * x U0 Hl; inversion Hl; subst; rewrite gunit_sub_shift_extend, gunit_sub_id.
  - left; reflexivity.
  - right; eexists; split; [ reflexivity | assumption ].
Qed.

Lemma sub_mod_compat_single_dm : forall Γ A M U, sub_mod_compat (Id ,,ᵈ M ‖ me_lit U) Γ (ce_dm A M U :: Γ).
Proof.
  intros * x U0 Hl; inversion Hl; subst; rewrite gunit_sub_shift_extend, gunit_sub_id.
  - left; reflexivity.
  - right; eexists; split; [ reflexivity | assumption ].
Qed.

(** Filling in the entries of a local body. *)
Lemma sub_mod_compat_fill : forall Φ σ Γ0, gm_fill Φ = Some σ -> sub_mod_compat σ Γ0 (body_ctx Φ ++ Γ0).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hf; cbn in Hf; try discriminate.
  - injection Hf as <-; cbn; intros x U Hl; right; exists x; rewrite gunit_sub_id; split; [ reflexivity | exact Hl ].
  - destruct E as [b pv A [M |] | pv U | | pv A M U | ]; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:E0; cbn in Hf; try discriminate; injection Hf as <-;
      specialize (IH _ Γ0 eq_refl); cbn [body_ctx List.app]; intros x U' Hl; inversion Hl; subst.
    + rewrite gunit_sub_shift_extend; cbn; auto.
    + left; rewrite gunit_sub_shift_extend; reflexivity.
    + rewrite gunit_sub_shift_extend; cbn; auto.
    + left; rewrite gunit_sub_shift_extend; reflexivity.
    + rewrite gunit_sub_shift_extend; cbn; auto.
Qed.

(** The substitution splitting a telescope at its outermost assumption
    sends module slots to module slots or to their units. *)
Lemma tele_split_compat : forall R Γ,
    match tele_split R with
    | inl (B, T, τ) => sub_mod_compat τ (T ++ ce_ass B :: Γ) (rev R ++ Γ)
    | inr τ => sub_mod_compat τ Γ (rev R ++ Γ)
    end.
Proof.
  induction R as [| [B0 | B0 N | U | B0 N U] R IH]; intros Γ; cbn [rev tele_split].
  - intros x U Hl; right; exists x; split; [ reflexivity | rewrite gunit_sub_id; exact Hl ].
  - rewrite <- List.app_assoc; cbn [List.app].
    intros x U Hl; right; exists x; split; [ reflexivity | rewrite gunit_sub_id; exact Hl ].
  - specialize (IH (ce_def B0 N :: Γ)); rewrite <- List.app_assoc; cbn [List.app].
    pose proof (sub_mod_compat_single_term Γ (ce_def B0 N) N ltac:(intros; discriminate) ltac:(intros; discriminate)) as Hs.
    destruct (tele_split R) as [[[B' T'] τ] | τ].
    + pose proof (sub_mod_compat_ext (T' ++ ce_ass B' :: nil) _ _ _ Hs) as Hx.
      rewrite tele_sub_app, length_app in Hx; cbn [tele_sub centry_sub length] in Hx.
      rewrite <- !List.app_assoc in Hx; cbn [List.app] in Hx.
      replace (length T' + 1) with (S (length T')) in Hx by lia.
      eapply sub_mod_compat_compose; [ exact IH | exact Hx ].
    + eapply sub_mod_compat_compose; [ exact IH | exact Hs ].
  - specialize (IH (ce_mod U :: Γ)); rewrite <- List.app_assoc; cbn [List.app].
    pose proof (sub_mod_compat_single_mod Γ U) as Hs.
    destruct (tele_split R) as [[[B' T'] τ] | τ].
    + pose proof (sub_mod_compat_ext (T' ++ ce_ass B' :: nil) _ _ _ Hs) as Hx.
      rewrite tele_sub_app, length_app in Hx; cbn [tele_sub centry_sub length] in Hx.
      rewrite <- !List.app_assoc in Hx; cbn [List.app] in Hx.
      replace (length T' + 1) with (S (length T')) in Hx by lia.
      eapply sub_mod_compat_compose; [ exact IH | exact Hx ].
    + eapply sub_mod_compat_compose; [ exact IH | exact Hs ].
  - specialize (IH (ce_dm B0 N U :: Γ)); rewrite <- List.app_assoc; cbn [List.app].
    pose proof (sub_mod_compat_single_dm Γ B0 N U) as Hs.
    destruct (tele_split R) as [[[B' T'] τ] | τ].
    + pose proof (sub_mod_compat_ext (T' ++ ce_ass B' :: nil) _ _ _ Hs) as Hx.
      rewrite tele_sub_app, length_app in Hx; cbn [tele_sub centry_sub length] in Hx.
      rewrite <- !List.app_assoc in Hx; cbn [List.app] in Hx.
      replace (length T' + 1) with (S (length T')) in Hx by lia.
      eapply sub_mod_compat_compose; [ exact IH | exact Hx ].
    + eapply sub_mod_compat_compose; [ exact IH | exact Hs ].
Qed.

Lemma gm_prefix_upto_mod_sub : forall Φ x Φ' pm U σ,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_mod pm U)) ->
    gm_prefix_upto (gmod_sub Φ σ) x = Some (gm_ext (gmod_sub Φ' σ) x (ge_mod pm U[sb_qn (gm_binders Φ') σ]ᵘ)).
Proof. intros * H; rewrite gm_prefix_upto_sub, H; reflexivity. Qed.

Lemma gm_prefix_upto_def_sub : forall Φ x Φ' b pv A B σ,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) ->
    gm_prefix_upto (gmod_sub Φ σ) x =
    Some (gm_ext (gmod_sub Φ' σ) x (ge_def b pv A[sb_qn (gm_binders Φ') σ]
                                        (option_map (fun M => M[sb_qn (gm_binders Φ') σ]) B))).
Proof. intros * H; rewrite gm_prefix_upto_sub, H; cbn; destruct B; reflexivity. Qed.

Lemma ctx_pi_body_sub : forall Φ' Δ A σ,
    (ctx_pi (body_ctx Φ' ++ Δ) A)[σ] =
    ctx_pi (body_ctx (gmod_sub Φ' (sb_qn (length Δ) σ)) ++ tele_sub Δ σ)
      A[sb_qn (gm_binders Φ') (sb_qn (length Δ) σ)].
Proof.
  intros; rewrite ctx_pi_sub, tele_sub_app, body_ctx_sub; f_equal.
  apply exp_sub_sb_eq; rewrite sb_qn_add, length_app, length_body_ctx; reflexivity.
Qed.
Lemma mod_qname_sub_eq : forall H σ Γ Δ, sub_mod_compat σ Γ Δ -> me_slot_root Δ H -> mod_qname H[σ]ᵐ = mod_qname H.
Proof.
  induction H as [fp | x | H IH y | H IH N | U]; intros * Hσ Hr; cbn in *; try reflexivity.
  - destruct Hr as [U HU]; destruct (Hσ _ _ HU) as [-> | (y & -> & _)]; reflexivity.
  - rewrite (IH _ _ _ Hσ Hr); reflexivity.
Qed.


(** ** Descriptions under a Weakening *)

Definition wk_mod_compat (φ : wk) (Γ Δ : ctx) : Prop :=
  forall x U, Δ ∋ #x ≔ₘ U -> Γ ∋ #(φ x) ≔ₘ gunit_wk U φ.

Lemma wk_mod_compat_q : forall φ Γ Δ e,
    wk_mod_compat φ Γ Δ -> wk_mod_compat (wk_q φ) (centry_wk e φ :: Γ) (e :: Δ).
Proof.
  intros * Hφ x U Hlk; inversion Hlk; subst; cbn.
  1,2: rewrite gunit_wk_shift_wk_q; constructor.
  rewrite gunit_wk_shift_wk_q; constructor; auto.
Qed.

Lemma wk_mod_compat_ext : forall Ψ φ Γ Δ,
    wk_mod_compat φ Γ Δ -> wk_mod_compat (wk_qn (length Ψ) φ) (tele_wk Ψ φ ++ Γ) (Ψ ++ Δ).
Proof. induction Ψ; intros; cbn; auto using wk_mod_compat_q. Qed.

Lemma gm_prefix_upto_mod_wk : forall Φ x Φ' pm U φ,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_mod pm U)) ->
    gm_prefix_upto (gmod_wk Φ φ) x = Some (gm_ext (gmod_wk Φ' φ) x (ge_mod pm (gunit_wk U (wk_qn (gm_binders Φ') φ)))).
Proof. intros * H; rewrite gm_prefix_upto_wk, H; reflexivity. Qed.

Lemma gm_prefix_upto_def_wk : forall Φ x Φ' b pv A B φ,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) ->
    gm_prefix_upto (gmod_wk Φ φ) x =
    Some (gm_ext (gmod_wk Φ' φ) x (ge_def b pv A[wk_qn (gm_binders Φ') φ]ʷ
                                        (option_map (fun M => M[wk_qn (gm_binders Φ') φ]ʷ) B))).
Proof. intros * H; rewrite gm_prefix_upto_wk, H; cbn; destruct B; reflexivity. Qed.

(** The type of a body member after a weakening of its unit. *)
Lemma ctx_pi_body_wk : forall Φ' Δ A φ,
    (ctx_pi (body_ctx Φ' ++ Δ) A)[φ]ʷ =
    ctx_pi (body_ctx (gmod_wk Φ' (wk_qn (length Δ) φ)) ++ tele_wk Δ φ)
      A[wk_qn (gm_binders Φ') (wk_qn (length Δ) φ)]ʷ.
Proof.
  intros; rewrite ctx_pi_wk, tele_wk_app, body_ctx_wk; f_equal.
  apply exp_wk_wk_eq; rewrite wk_qn_add, length_app, length_body_ctx; reflexivity.
Qed.

Lemma entry_sc_mono0 : forall E m, entry_sc 0 E -> m >= 0 -> entry_sc m E.
Proof.
  intros [b pv A B | pv U | pv pq D Φ | pv A M U | pv Rr Φ] m HE _; cbn in *; auto.
  - destruct HE as [HA HB]; split; [ eapply exp_scoped_mono; [| exact HA ]; lia |].
    destruct B; cbn in *; [ eapply exp_scoped_mono; [| exact HB ]; lia | exact I ].
  - destruct HE as [HU | HU]; [ left; eapply gunit_scoped_mono; [| exact HU ]; lia | right; exact HU ].
  - destruct HE as (HA & HM & HU); split; [| split ];
      first [ eapply exp_scoped_mono; [| eassumption ]; lia | eapply gunit_scoped_mono; [| eassumption ]; lia ].
Qed.

(** *** What a Module Expression Denotes, Substituted *)

Lemma ds_epath_sub : forall R y σ, ds_epath (ds_sub R σ) y = ds_epath R y.
Proof. intros [] y σ; reflexivity. Qed.

(** A body with no local open is its own expansion, read anywhere. *)
Lemma body_xp_closed_any : forall Θ Ξ Γ Φ k, body_closed k Φ -> body_xp Θ Ξ Γ Φ Φ.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; intros * HΦ; cbn in HΦ; [ constructor | | contradiction ].
  constructor; eapply IH; apply HΦ.
Qed.

(** What a closed entry denotes does not depend on the context. *)
Lemma edenote_closed_any : forall Θ Ξ Γ' o E R σ,
    entry_sc 0 E -> edenote Θ Ξ Γ' o (gentry_sub E σ) R -> edenote Θ Ξ Γ' o E R.
Proof.
  intros * HE Hd; pose proof (entry_closed_sub E σ HE) as Hs.
  destruct E as [b pv A B | pv U | pv pq k D Φ | pv A M U | pv pr Rr Φ];
    [ rewrite Hs in Hd; exact Hd | rewrite Hs in Hd; exact Hd | clear Hs; cbn in Hd; inversion Hd; subst; econstructor; eassumption
    | rewrite Hs in Hd; exact Hd | clear Hs; cbn in Hd; inversion Hd; subst; econstructor; eassumption ].
Qed.

Lemma mdenote_sub_lt_all : forall Θ Ξ, gctx_closed Θ Ξ ->
    (forall Δ H R, mdenote Θ Ξ Δ H R -> forall m, slots_ok m Δ -> modexp_scoped m H ->
       forall Γ σ, sub_mod_compat_lt m σ Γ Δ -> mdenote Θ Ξ Γ H[σ]ᵐ (ds_sub R σ)) /\
    (forall Δ o U R, udenote Θ Ξ Δ o U R -> forall m, slots_ok m Δ ->
       (gunit_scoped m U \/ exists T Φ, U = gu_body T Φ /\ unit_closed T Φ) ->
       forall Γ σ, sub_mod_compat_lt m σ Γ Δ -> udenote Θ Ξ Γ o U[σ]ᵘ (ds_sub R σ)) /\
    (forall Δ o E R, edenote Θ Ξ Δ o E R -> forall m, slots_ok m Δ -> entry_sc m E ->
       forall Γ σ, sub_mod_compat_lt m σ Γ Δ -> edenote Θ Ξ Γ o (gentry_sub E σ) (ds_sub R σ)) /\
    (forall Δ Φ Φx, body_xp Θ Ξ Δ Φ Φx -> forall m, slots_ok m Δ -> gmod_scoped m Φ ->
       forall Γ σ, sub_mod_compat_lt m σ Γ Δ -> body_xp Θ Ξ Γ (gmod_sub Φ σ) (gmod_sub Φx σ)) /\
    (forall Δ H its gs, items_gen Θ Ξ Δ H its gs -> forall m, slots_ok m Δ -> modexp_scoped m H ->
       forall Γ σ, sub_mod_compat_lt m σ Γ Δ ->
       items_gen Θ Ξ Γ H[σ]ᵐ its (List.map (fun g => generated_item_sub g σ) gs)).
Proof.
  intros Θ Ξ Hc; pose proof (mdenote_scoped_all _ _ Hc) as (Hsm & Hsu & Hse & Hsb & _).
  apply mdenote_all_ind.
  - (* a unit *)
    intros Γ H p T Φ hq e m HS HH Γ' σ Hσ.
    rewrite (mod_qname_sub _ _ σ hq); cbn; apply mdenote_unit; assumption.
  - (* a type's open frame: closed *)
    intros Γ H p pq k D Mk Tm Φm hq e eMk el m HS HH Γ' σ Hσ.
    rewrite (mod_qname_sub _ _ σ hq).
    rewrite (ds_closed_sub _ σ (ind_former_desc_scoped pq k D Mk (ds_closed nil p Tm Φm nil) 0
                                  (stack_closed_ind _ _ _ _ _ (proj2 Hc) e) eMk
                                  (conj I (conj (gc_loc_closed _ _ _ _ _ Hc el) (List.Forall_nil (exp_scoped _)))))).
    eapply mdenote_ind_frame; eassumption.
  - (* a slot *)
    intros Γ x U R l u IHu m HS HH Γ' σ Hσ; cbn in HH.
    destruct (Hσ _ _ HH l) as [Hx | (y & Hx & Hy)]; cbn; rewrite Hx; cbn [sentry_modexp].
    + apply mdenote_lit; eapply IHu; [ eassumption | left; exact (HS _ _ HH l) | eassumption ].
    + eapply mdenote_slot; [ exact Hy |]; eapply IHu; [ eassumption | left; exact (HS _ _ HH l) | eassumption ].
  - (* a literal *)
    intros Γ U R u IHu m HS HH Γ' σ Hσ; cbn in *.
    apply mdenote_lit; eapply IHu; [ eassumption | left; eassumption | eassumption ].
  - (* an application *)
    intros Γ H N R R' d IHd e m HS HH Γ' σ Hσ; cbn in *; destruct HH as [HH HN].
    eapply mdenote_app; [ eapply IHd; eassumption | apply ds_at_sub; exact e ].
  - (* a selection *)
    intros Γ H y R0 R0m Γy E rd R R' d0 IH0 em ee de IHe er m HS HH Γ' σ Hσ; cbn in HH |- *.
    pose proof (ds_mod_scoped _ _ _ (Hsm _ _ _ d0 m HS HH) em) as HR0m.
    destruct R0m as [A0 om | Δ0 Φ0 | Θ0 q0 T0 Φ0 Ns0 | A0 M0 Rm0]; cbn in ee; try discriminate.
    + (* an open body *)
      destruct (ds_entry_scoped _ _ _ _ _ _ HR0m ee) as (HΓy & HE & _).
      destruct (ds_entry_open_rd Δ0 Φ0 _ _ _ _ _ ee) as (Φ' & -> & ->).
      eapply mdenote_mem; [ eapply IH0; eassumption | apply ds_mod_sub; exact em | apply ds_entry_sub_open; exact ee | |].
      * rewrite ds_epath_sub; eapply IHe; [ apply slots_ok_app; eassumption | exact HE |].
        apply sub_mod_compat_lt_ext; assumption.
      * cbn in er |- *.
        destruct (gm_fill Φ') as [τ |] eqn:Hf; cbn in er; [| discriminate ]; injection er as <-.
        destruct (gm_fill_sub Φ' (length Δ0) σ τ Hf) as (τ' & -> & Heq); cbn; f_equal.
        rewrite ds_up_sub; f_equal.
        rewrite length_app, length_body_ctx, (ds_sub_sub_ext _ _ _ _ Heq); symmetry; apply ds_sub_sub_ext; reflexivity.
    + (* a closed body *)
      destruct HR0m as (HΘ0 & HU0 & HNs0).
      destruct (ds_entry_closed Θ0 q0 T0 Φ0 Ns0 _ _ _ _ HU0 ee) as (-> & HE & ->).
      assert (HR : ds_scoped 0 R) by (eapply Hse; [ exact de | intros ? ? Hx; lia | exact HE ]).
      eapply mdenote_mem with (R := R); [ eapply IH0; eassumption | apply ds_mod_sub; exact em | apply ds_entry_sub_closed; exact ee | |].
      * rewrite ds_epath_sub; apply (edenote_closed_any _ _ _ _ _ _ σ HE).
        rewrite <- (ds_closed_sub R σ HR) at 1.
        eapply IHe; [ cbn; eassumption | eapply entry_sc_mono0; [ exact HE | lia ] |]; cbn; assumption.
      * cbn in er |- *.
        destruct (ds_ats_read R Ns0) as [R1 |] eqn:Ea; [| discriminate ]; injection er as <-.
        rewrite ds_up_sub, ds_named_sub,
          (ds_named_length Θ0 (tele_sub Θ0 σ) Ns0 (List.map (fun M => M[sb_qn (length Θ0) σ]) Ns0))
          by (rewrite ?length_tele_sub, ?length_map; reflexivity).
        rewrite <- (ds_closed_sub R (sb_qn (length Θ0) σ) HR) at 1.
        rewrite (ds_ats_read_sub _ _ _ _ Ea); reflexivity.
  - (* a record's open frame: closed *)
    intros Γ H p R Tm Φm hq e el m HS HH Γ' σ Hσ.
    rewrite (mod_qname_sub _ _ σ hq).
    destruct (stack_closed_record _ _ _ (proj2 Hc) e) as [HF HS0].
    rewrite (ds_closed_sub _ σ (record_former_desc_scoped p R (ds_closed nil p Tm Φm nil) 0
                                  (proj2 (proj1 (ctx_scoped_app_iff _ _) HF)) HS0
                                  (conj I (conj (gc_loc_closed _ _ _ _ _ Hc el) (List.Forall_nil (exp_scoped _)))))).
    eapply mdenote_record_frame; eassumption.
  - (* a body *)
    intros Γ o Δ sm Φ Φx R bx IHbx eb m HS HU Γ' σ Hσ.
    destruct HU as [HU | (T & Φ0 & Heq & HU)].
    + rewrite gunit_scoped_mk in HU; destruct HU as [HΔ [-> HΦ]].
      cbn in eb; injection eb as <-.
      rewrite gunit_sub_mk; cbn [moddef_sub].
      eapply udenote_body; [| reflexivity ]; eapply IHbx; [ apply slots_ok_app; eassumption | exact HΦ |].
      apply sub_mod_compat_lt_ext; assumption.
    + injection Heq as -> -> ->.
      rewrite (body_xp_closed _ _ _ _ _ _ (proj2 HU) bx) in eb.
      rewrite (unit_closed_sub _ _ _ HU).
      destruct o as [pq |]; cbn in eb; [ injection eb as <- | discriminate ]; cbn.
      eapply udenote_body; [ eapply body_xp_closed_any, (proj2 HU) | reflexivity ].
  - (* an alias *)
    intros Γ o Δ E R R' d IHd em m HS HU Γ' σ Hσ.
    destruct HU as [HU | (T & Φ0 & [=] & _)].
    rewrite gunit_scoped_mk in HU; destruct HU as [HΔ HE]; cbn in HE.
    rewrite gunit_sub_mk; cbn [moddef_sub]; rewrite ds_up_sub.
    eapply udenote_alias; [| apply ds_mod_sub; exact em ].
    eapply IHd; [ apply slots_ok_app; eassumption | exact HE |].
    apply sub_mod_compat_lt_ext; assumption.
  - (* a definition *)
    intros Γ o b pv A oM m HS HE Γ' σ Hσ; cbn; destruct b, oM; constructor.
  - (* a module *)
    intros Γ o pv U R u IHu m HS HE Γ' σ Hσ; cbn in *; constructor; eapply IHu; eassumption.
  - (* an inductive type: its type former, closed *)
    intros Γ o pv pq k D Φ Mk pm Tm Φm eMk epm el m HS HE Γ' σ Hσ; cbn in HE.
    rewrite (ds_closed_sub _ σ (ind_former_desc_scoped pq k D Mk (ds_closed nil pm Tm Φm nil) 0 HE eMk
                                  (conj I (conj (gc_loc_closed _ _ _ _ _ Hc el) (List.Forall_nil (exp_scoped _)))))).
    cbn [gentry_sub]; econstructor; eassumption.
  - (* a definition with a module part *)
    intros Γ o pv A M Δ E Rm u IHu m HS HE Γ' σ Hσ; cbn in HE |- *; destruct HE as (_ & _ & HU).
    pose proof (IHu m HS (or_introl HU) Γ' σ Hσ) as Hu'.
    rewrite gunit_sub_mk in Hu' |- *; cbn [moddef_sub] in Hu' |- *; constructor; exact Hu'.
  - (* a record type: its type former, closed *)
    intros Γ p pv pr R Φ Tm Φm el m HS HE Γ' σ Hσ; cbn in HE.
    rewrite (ds_closed_sub _ σ (record_former_desc_scoped p R (ds_closed nil p Tm Φm nil) 0 (proj1 HE) (proj2 HE)
                                  (conj I (conj (gc_loc_closed _ _ _ _ _ Hc el) (List.Forall_nil (exp_scoped _)))))).
    cbn [gentry_sub]; econstructor; eassumption.
  - (* the empty body *) intros; constructor.
  - (* an entry *)
    intros Γ Φ Φx x E bx IHbx m HS HΦ Γ' σ Hσ; cbn in *; destruct HΦ as [HΦ HE].
    rewrite (body_xp_binders _ _ _ _ _ bx); constructor; eapply IHbx; eassumption.
  - (* an open *)
    intros Γ Φ Φx H its R Rm gs bx IHbx d IHd em ig IHig iok m HS HΦ Γ' σ Hσ; cbn in *; destruct HΦ as [HΦ HH].
    rewrite gens_append_sub by lia; rewrite Nat.sub_0_r.
    rewrite <- (body_xp_binders _ _ _ _ _ bx).
    pose proof (sub_mod_compat_lt_ext (body_ctx Φx) _ _ _ _ Hσ) as Hσ'.
    rewrite <- body_ctx_sub, length_body_ctx in Hσ'.
    assert (HΦx : gmod_scoped m Φx) by (eapply Hsb; eassumption).
    assert (Hok : slots_ok (length (body_ctx Φx) + m) (body_ctx Φx ++ Γ))
      by (apply slots_ok_app; [ assumption | apply gmod_scoped_body_ctx; assumption ]).
    rewrite length_body_ctx in Hok.
    rewrite <- (body_xp_binders _ _ _ _ _ bx) in HH.
    eapply body_xp_open; [ eapply IHbx; eassumption | eapply IHd; eassumption | apply ds_mod_sub; exact em
                    | eapply IHig; [ exact Hok | exact HH | exact Hσ' ] | assumption ].
  - intros; constructor.
  - intros Γ H d pv its gs ig IHig m HS HH Γ' σ Hσ; cbn.
    eapply items_gen_self; eapply IHig; eassumption.
  - intros Γ H n d pv A om its gs dm IHdm ig IHig m HS HH Γ' σ Hσ.
    cbn [List.map generated_item_sub]; eapply items_gen_def; [| eapply IHig; eassumption ].
    exact (IHdm m HS HH Γ' σ Hσ).
  - intros Γ H n d pv R its gs dm IHdm Hmod ig IHig m HS HH Γ' σ Hσ.
    cbn [List.map generated_item_sub]; eapply items_gen_mod; [ exact (IHdm m HS HH Γ' σ Hσ) | | eapply IHig; eassumption ].
    destruct R; cbn in *; tauto.
  - intros Γ H n d pv R A Rm its gs dm IHdm Ht Hmod ig IHig m HS HH Γ' σ Hσ.
    cbn [List.map generated_item_sub]; eapply items_gen_dm;
      [ exact (IHdm m HS HH Γ' σ Hσ) | apply ds_ty_sub; exact Ht | apply ds_mod_sub; exact Hmod | eapply IHig; eassumption ].
Qed.

Lemma mdenote_sub_all : forall Θ Ξ, gctx_closed Θ Ξ ->
    (forall Δ H R, mdenote Θ Ξ Δ H R -> forall m, slots_ok m Δ -> modexp_scoped m H ->
       forall Γ σ, sub_mod_compat σ Γ Δ -> mdenote Θ Ξ Γ H[σ]ᵐ (ds_sub R σ)) /\
    (forall Δ o U R, udenote Θ Ξ Δ o U R -> forall m, slots_ok m Δ ->
       (gunit_scoped m U \/ exists T Φ, U = gu_body T Φ /\ unit_closed T Φ) ->
       forall Γ σ, sub_mod_compat σ Γ Δ -> udenote Θ Ξ Γ o U[σ]ᵘ (ds_sub R σ)) /\
    (forall Δ o E R, edenote Θ Ξ Δ o E R -> forall m, slots_ok m Δ -> entry_sc m E ->
       forall Γ σ, sub_mod_compat σ Γ Δ -> edenote Θ Ξ Γ o (gentry_sub E σ) (ds_sub R σ)) /\
    (forall Δ Φ Φx, body_xp Θ Ξ Δ Φ Φx -> forall m, slots_ok m Δ -> gmod_scoped m Φ ->
       forall Γ σ, sub_mod_compat σ Γ Δ -> body_xp Θ Ξ Γ (gmod_sub Φ σ) (gmod_sub Φx σ)) /\
    (forall Δ H its gs, items_gen Θ Ξ Δ H its gs -> forall m, slots_ok m Δ -> modexp_scoped m H ->
       forall Γ σ, sub_mod_compat σ Γ Δ ->
       items_gen Θ Ξ Γ H[σ]ᵐ its (List.map (fun g => generated_item_sub g σ) gs)).
Proof.
  intros Θ Ξ Hc; destruct (mdenote_sub_lt_all _ _ Hc) as (Hm & Hu & He & Hb & Hi).
  repeat split; intros; [ eapply Hm | eapply Hu | eapply He | eapply Hb | eapply Hi ];
    eauto using sub_mod_compat_lt_of.
Qed.

(** A closed module expression denotes the same in every context. *)
Corollary mdenote_closed_any : forall Θ Ξ, gctx_closed Θ Ξ -> forall Δ H R Γ,
    mdenote Θ Ξ Δ H R -> modexp_scoped 0 H -> mdenote Θ Ξ Γ H R.
Proof.
  intros * Hc * Hm HH.
  assert (HS : slots_ok 0 Δ) by (intros ? ? Hx; lia).
  pose proof (proj1 (mdenote_scoped_all _ _ Hc) _ _ _ Hm _ HS HH) as HR.
  pose proof (proj1 (mdenote_sub_lt_all _ _ Hc) _ _ _ Hm _ HS HH Γ Id ltac:(intros ? ? Hx; lia)) as Hm'.
  rewrite (ds_closed_sub _ _ HR), modexp_sub_id in Hm'; exact Hm'.
Qed.

(** A weakening is the substitution [ι φ]. *)
Lemma wk_mod_compat_sub : forall φ Γ Δ, wk_mod_compat φ Γ Δ -> sub_mod_compat (ι φ) Γ Δ.
Proof.
  intros * Hφ x U Hl; right; exists (φ x); split; [ reflexivity |].
  rewrite gunit_sub_of_wk; apply Hφ, Hl.
Qed.

Corollary mdenote_sub : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ H R, mdenote Θ Ξ Δ H R -> ctx_scoped 0 Δ -> modexp_scoped (length Δ) H ->
    forall Γ σ, sub_mod_compat σ Γ Δ -> mdenote Θ Ξ Γ H[σ]ᵐ (ds_sub R σ).
Proof.
  intros * Hc * Hm HΔ HH * Hσ.
  exact (proj1 (mdenote_sub_all _ _ Hc) _ _ _ Hm _ (slots_ok_ctx _ HΔ) HH _ _ Hσ).
Qed.

Corollary mdenote_wk : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ H R, mdenote Θ Ξ Δ H R -> ctx_scoped 0 Δ -> modexp_scoped (length Δ) H ->
    forall Γ φ, wk_mod_compat φ Γ Δ -> mdenote Θ Ξ Γ (modexp_wk H φ) (ds_sub R (ι φ)).
Proof.
  intros * Hc * Hm HΔ HH * Hφ; rewrite <- modexp_sub_of_wk.
  eapply mdenote_sub; [ eassumption .. | apply wk_mod_compat_sub, Hφ ].
Qed.

Corollary body_xp_sub : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ Φ Φx, body_xp Θ Ξ Δ Φ Φx -> ctx_scoped 0 Δ -> gmod_scoped (length Δ) Φ ->
    forall Γ σ, sub_mod_compat σ Γ Δ -> body_xp Θ Ξ Γ (gmod_sub Φ σ) (gmod_sub Φx σ).
Proof.
  intros * Hc * Hx HΔ HΦ * Hσ.
  exact (proj1 (proj2 (proj2 (proj2 (mdenote_sub_all _ _ Hc)))) _ _ _ Hx _ (slots_ok_ctx _ HΔ) HΦ _ _ Hσ).
Qed.

Corollary body_xp_wk : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ Φ Φx, body_xp Θ Ξ Δ Φ Φx -> ctx_scoped 0 Δ -> gmod_scoped (length Δ) Φ ->
    forall Γ φ, wk_mod_compat φ Γ Δ -> body_xp Θ Ξ Γ (gmod_wk Φ φ) (gmod_wk Φx φ).
Proof.
  intros * Hc * Hx HΔ HΦ * Hφ; rewrite <- !gmod_sub_of_wk.
  eapply body_xp_sub; [ eassumption .. | apply wk_mod_compat_sub, Hφ ].
Qed.

(** The parts of a description, weakened. *)
Lemma ds_ty_wk : forall R A φ, ds_ty R = Some A -> ds_ty (ds_sub R (ι φ)) = Some A[φ]ʷ.
Proof. intros; rewrite <- exp_sub_of_wk; apply ds_ty_sub; assumption. Qed.

Lemma ds_red_wk : forall R M φ, ds_red R = Some M -> ds_red (ds_sub R (ι φ)) = Some M[φ]ʷ.
Proof. intros; rewrite <- exp_sub_of_wk; apply ds_red_sub; assumption. Qed.

(** A δ-reduct of a moved description is that of the description, moved. *)
Lemma ds_red_sub_inv : forall R M σ, ds_red (ds_sub R σ) = Some M -> exists M0, ds_red R = Some M0 /\ M = M0[σ].
Proof.
  intros R M σ Hr; destruct (ds_red R) as [M0 |] eqn:E.
  - exists M0; split; [ reflexivity |]; rewrite (ds_red_sub _ _ σ E) in Hr; injection Hr as <-; reflexivity.
  - destruct R as [A [M1 |] | | | ]; cbn in E, Hr; discriminate.
Qed.

Lemma ds_red_wk_inv : forall R M φ, ds_red (ds_sub R (ι φ)) = Some M -> exists M0, ds_red R = Some M0 /\ M = M0[φ]ʷ.
Proof.
  intros * Hr; destruct (ds_red_sub_inv _ _ _ Hr) as (M0 & HM0 & ->); exists M0; split; [ exact HM0 |].
  rewrite exp_sub_of_wk; reflexivity.
Qed.


(** ** What a Unit Binds, Substituted *)

Lemma me_apps_sub : forall Ns H σ, (me_apps H Ns)[σ]ᵐ = me_apps H[σ]ᵐ (List.map (fun M => M[σ]) Ns).
Proof. induction Ns as [| N Ns IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(** The unit a description stands for, moved, is that of the description
    moved. *)
Lemma ds_unit_sub : forall R σ, ds_unit (ds_sub R σ) = (ds_unit R)[σ]ᵐ.
Proof.
  intros [A om | Δ Φ | [| e Θ] p T Φ Ns | Θd A M Rm] σ; cbn [ds_sub ds_unit].
  - reflexivity.
  - cbn; rewrite gunit_sub_mk; reflexivity.
  - cbn [tele_sub]; rewrite me_apps_sub, qname_mod_sub; reflexivity.
  - cbn [tele_sub ds_unit]; cbn [modexp_sub]; rewrite gunit_sub_mk; cbn [moddef_sub].
    rewrite me_apps_sub, qname_mod_sub; reflexivity.
  - reflexivity.
Qed.


Lemma ds_red_sub_opt : forall R σ, ds_red (ds_sub R σ) = option_map (fun M => M[σ]) (ds_red R).
Proof. intros [A [M |] | | | ] σ; cbn; try reflexivity; rewrite ctx_fn_sub, ?apps_exp_sub; reflexivity. Qed.

Lemma gunit_abs_sub : forall Δ U σ, (gunit_abs Δ U)[σ]ᵘ = gunit_abs (tele_sub Δ σ) U[sb_qn (length Δ) σ]ᵘ.
Proof.
  intros Δ [Δy D] σ; cbn [gunit_abs]; rewrite !gunit_sub_mk, tele_sub_app, length_app, sb_qn_plus; reflexivity.
Qed.

Lemma gunit_abs_wk : forall Δ U φ, gunit_wk (gunit_abs Δ U) φ = gunit_abs (tele_wk Δ φ) (gunit_wk U (wk_qn (length Δ) φ)).
Proof.
  intros Δ [Δy D] φ; cbn [gunit_abs]; rewrite !gunit_wk_mk; cbn [gunit_abs]; rewrite tele_wk_app, length_app; f_equal.
  apply moddef_wk_wk_eq; symmetry; apply wk_qn_add.
Qed.

Lemma body_opens_wk : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> forall φ,
    body_opens (gmod_wk Φ φ) (gmod_wk Φx φ) =
    List.map (fun p => (tele_wk (fst p) φ, modexp_wk (snd p) (wk_qn (length (fst p)) φ))) (body_opens Φ Φx).
Proof.
  induction 1 as [| Γ Φ Φx x E Hx IH | Γ Φ Φx H its R T gs Hx IH _ _ Hg]; intros φ.
  - reflexivity.
  - cbn [gmod_wk body_opens gm_dropn]; apply IH.
  - cbn [gmod_wk]; rewrite gens_append_wk by lia; rewrite Nat.sub_0_r.
    rewrite body_opens_open_len by (rewrite List.length_map; eapply items_gen_length; eassumption).
    rewrite (body_opens_open _ _ _ _ _ _ _ _ Hg); cbn [List.map fst snd]; rewrite IH.
    rewrite body_ctx_wk, length_body_ctx, (body_xp_binders _ _ _ _ _ Hx); reflexivity.
Qed.

Lemma body_opens_sub : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> forall σ,
    body_opens (gmod_sub Φ σ) (gmod_sub Φx σ) =
    List.map (fun p => (tele_sub (fst p) σ, (snd p)[sb_qn (length (fst p)) σ]ᵐ)) (body_opens Φ Φx).
Proof.
  induction 1 as [| Γ Φ Φx x E Hx IH | Γ Φ Φx H its R T gs Hx IH _ _ Hg]; intros σ.
  - reflexivity.
  - cbn [gmod_sub body_opens gm_dropn]; apply IH.
  - cbn [gmod_sub]; rewrite gens_append_sub by lia; rewrite Nat.sub_0_r.
    rewrite body_opens_open_len by (rewrite List.length_map; eapply items_gen_length; eassumption).
    rewrite (body_opens_open _ _ _ _ _ _ _ _ Hg); cbn [List.map fst snd]; rewrite IH.
    rewrite body_ctx_sub, length_body_ctx, (body_xp_binders _ _ _ _ _ Hx); reflexivity.
Qed.

Lemma body_opens_at_wk : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> forall φ,
    body_opens_at (gmod_wk Φ φ) (gmod_wk Φx φ) =
    List.map (fun p => (gmod_wk (fst p) φ, modexp_wk (snd p) (wk_qn (gm_binders (fst p)) φ))) (body_opens_at Φ Φx).
Proof.
  induction 1 as [| Γ Φ Φx x E Hx IH | Γ Φ Φx H its R T gs Hx IH _ _ Hg]; intros φ.
  - reflexivity.
  - cbn [gmod_wk body_opens_at gm_dropn]; apply IH.
  - cbn [gmod_wk]; rewrite gens_append_wk by lia; rewrite Nat.sub_0_r.
    rewrite body_opens_at_open_len by (rewrite List.length_map; eapply items_gen_length; eassumption).
    rewrite (body_opens_at_open _ _ _ _ _ _ _ _ Hg); cbn [List.map fst snd]; rewrite IH.
    rewrite (body_xp_binders _ _ _ _ _ Hx); reflexivity.
Qed.

Lemma body_opens_at_sub : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> forall σ,
    body_opens_at (gmod_sub Φ σ) (gmod_sub Φx σ) =
    List.map (fun p => (gmod_sub (fst p) σ, (snd p)[sb_qn (gm_binders (fst p)) σ]ᵐ)) (body_opens_at Φ Φx).
Proof.
  induction 1 as [| Γ Φ Φx x E Hx IH | Γ Φ Φx H its R T gs Hx IH _ _ Hg]; intros σ.
  - reflexivity.
  - cbn [gmod_sub body_opens_at gm_dropn]; apply IH.
  - cbn [gmod_sub]; rewrite gens_append_sub by lia; rewrite Nat.sub_0_r.
    rewrite body_opens_at_open_len by (rewrite List.length_map; eapply items_gen_length; eassumption).
    rewrite (body_opens_at_open _ _ _ _ _ _ _ _ Hg); cbn [List.map fst snd]; rewrite IH.
    rewrite (body_xp_binders _ _ _ _ _ Hx); reflexivity.
Qed.

Lemma gens_append_body_ctx : forall gs Φ k, exists Ψ, body_ctx (gens_append Φ k gs) = Ψ ++ body_ctx Φ.
Proof.
  induction gs as [| g gs IH]; intros; cbn [gens_append]; [ exists nil; reflexivity |].
  destruct (generated_item_entry g) as [d E]; destruct (IH (gm_ext Φ d (gentry_wk E (wk_shiftn k))) (S k)) as [Ψ HΨ].
  rewrite HΨ; cbn [body_ctx].
  destruct (gentry_wk E (wk_shiftn k)) as [? ? ? [] | | | | ]; eexists (Ψ ++ _ :: nil); rewrite <- List.app_assoc; reflexivity.
Qed.

(** The context an open's prefix makes is the inner part of the body's. *)
Lemma body_opens_prefix : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx ->
    forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> exists Ψr, body_ctx Φx = Ψr ++ Ψ.
Proof.
  induction 1 as [| Γ Φ Φx x E Hx IH | Γ Φ Φx H its R T gs Hx IH _ _ Hg]; intros k Ψ H' Hk.
  - destruct k; discriminate.
  - cbn [body_opens gm_dropn] in Hk; destruct (IH _ _ _ Hk) as [Ψr HΨr]; cbn [body_ctx].
    destruct E as [? ? ? [] | | | | ]; eexists (_ :: Ψr); rewrite HΨr; reflexivity.
  - rewrite (body_opens_open _ _ _ _ _ _ _ _ Hg) in Hk.
    destruct (gens_append_body_ctx gs Φx 0) as [Ψg HΨg]; rewrite HΨg.
    destruct k as [| k]; cbn in Hk; [ injection Hk as <- <-; exists Ψg; reflexivity |].
    destruct (IH _ _ _ Hk) as [Ψr HΨr]; rewrite HΨr; exists (Ψg ++ Ψr); apply List.app_assoc.
Qed.

(** ** The Scoping of a Judgment's Parts *)

Corollary wf_ctx_scoped : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ctx_scoped 0 Γ.
Proof. intros * H; exact (proj1 ((proj1 wf_scoped) _ _ _ H)). Qed.

Corollary wf_unit_eq_scoped : forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
    ctx_scoped 0 Γ /\ gunit_scoped (length Γ) U /\ gunit_scoped (length Γ) U'.
Proof.
  intros * H; destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 wf_scoped)))))) _ _ _ _ _ H) as ((? & _) & ? & ?); auto.
Qed.

Corollary wf_modexp_eq_scoped : forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
    ctx_scoped 0 Γ /\ modexp_scoped (length Γ) H /\ modexp_scoped (length Γ) H'.
Proof.
  intros * HH; destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 wf_scoped))))))) _ _ _ _ _ HH) as ((? & _) & ? & ?); auto.
Qed.

Corollary wf_ext_eq_scoped : forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    ctx_scoped 0 Γ /\ ctx_scoped (length Γ) Ψ /\ ctx_scoped (length Γ) Ψ'.
Proof.
  intros * H; destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 wf_scoped))))) _ _ _ _ _ H) as ((? & _) & ? & ?); auto.
Qed.

Corollary tele_view_wk_some : forall T B T1 φ, tele_view T = Some (B, T1) ->
    tele_view (tele_wk T φ) = Some (B[φ]ʷ, tele_wk T1 (wk_q φ)).
Proof. intros * Hv; rewrite tele_view_wk, Hv; reflexivity. Qed.

Corollary tele_view_sub_some : forall T B T1 σ, tele_view T = Some (B, T1) ->
    tele_view (tele_sub T σ) = Some (B[σ], tele_sub T1 (q σ)).
Proof. intros * Hv; rewrite tele_view_sub, Hv; reflexivity. Qed.

(** The telescope of the module part, substituted. *)
Lemma ds_mtele_sub : forall R T σ n,
    ds_scoped n R -> ds_mtele R = Some T -> ds_mtele (ds_sub R σ) = Some (tele_sub T σ).
Proof.
  intros * HR Ht; unfold ds_mtele in *.
  destruct (ds_mod R) as [Rm |] eqn:Hm; [| discriminate ].
  rewrite (ds_mod_sub _ _ σ Hm).
  pose proof (ds_mod_scoped _ _ _ HR Hm) as HRm.
  apply ds_tele_sub; [| exact Ht ].
  intros * ->; cbn in HRm; destruct HRm as (_ & [HT _] & _); exact HT.
Qed.

Lemma ds_mtele_wk : forall R T φ n,
    ds_scoped n R -> ds_mtele R = Some T -> ds_mtele (ds_sub R (ι φ)) = Some (tele_wk T φ).
Proof. intros; rewrite <- tele_sub_of_wk; eapply ds_mtele_sub; eassumption. Qed.

(** What a well-formed module expression denotes, scoped. *)
Lemma wf_mdenote_scoped : forall Θ Ξ Γ H H' R,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ H R -> ds_scoped (length Γ) R.
Proof.
  intros * HH Hm; destruct (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & HHs & _).
  eapply (proj1 (mdenote_scoped_all _ _ (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)))); [ exact Hm | apply slots_ok_ctx, HΓ | exact HHs ].
Qed.

Lemma wf_mdenote_mem_scoped : forall Θ Ξ Γ H H' x R,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ (me_mem H x) R -> ds_scoped (length Γ) R.
Proof.
  intros * HH Hm; destruct (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & HHs & _).
  eapply (proj1 (mdenote_scoped_all _ _ (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)))); [ exact Hm | apply slots_ok_ctx, HΓ | exact HHs ].
Qed.
