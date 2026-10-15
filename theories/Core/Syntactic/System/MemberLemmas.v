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
  induction Δ as [| [] Δ IH]; intros; cbn; [ reflexivity | | |]; rewrite IH; cbn; reflexivity.
Qed.

Lemma ctx_pi_sub : forall Δ A σ,
    (ctx_pi Δ A)[σ] = ctx_pi (tele_sub Δ σ) A[sb_qn (length Δ) σ].
Proof.
  induction Δ as [| [] Δ IH]; intros; cbn; [ reflexivity | | |]; rewrite IH; cbn; reflexivity.
Qed.

Lemma ctx_fn_wk : forall Δ M φ,
    (ctx_fn Δ M)[φ]ʷ = ctx_fn (tele_wk Δ φ) M[wk_qn (length Δ) φ]ʷ.
Proof.
  induction Δ as [| [] Δ IH]; intros; cbn; [ reflexivity | | |]; rewrite IH; cbn; reflexivity.
Qed.

Lemma ctx_fn_sub : forall Δ M σ,
    (ctx_fn Δ M)[σ] = ctx_fn (tele_sub Δ σ) M[sb_qn (length Δ) σ].
Proof.
  induction Δ as [| [] Δ IH]; intros; cbn; [ reflexivity | | |]; rewrite IH; cbn; reflexivity.
Qed.

(** ** Bodies *)

(** A local import's placeholders are closed. *)
Lemma tele_wk_placeholders : forall n φ, tele_wk (repeat (ce_ass a_True) n) φ = repeat (ce_ass a_True) n.
Proof. induction n; intros; cbn; rewrite ?IHn; reflexivity. Qed.

Lemma body_ctx_wk : forall Φ φ, body_ctx (gmod_wk Φ φ) = tele_wk (body_ctx Φ) φ.
Proof.
  induction Φ as [| Φ IH x [? ? ? [] | | | ] | Φ IH c]; intros; cbn; auto;
    rewrite ?tele_wk_app, ?tele_wk_placeholders, IH, ?length_body_ctx; reflexivity.
Qed.

(** A local import's placeholders are closed. *)
Lemma tele_sub_placeholders : forall n σ, tele_sub (repeat (ce_ass a_True) n) σ = repeat (ce_ass a_True) n.
Proof. induction n; intros; cbn; rewrite ?IHn; reflexivity. Qed.

Lemma body_ctx_sub : forall Φ σ, body_ctx (gmod_sub Φ σ) = tele_sub (body_ctx Φ) σ.
Proof.
  induction Φ as [| Φ IH x [? ? ? [] | | | ] | Φ IH c]; intros; cbn; auto;
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

Lemma ig_entry_wk : forall g φ, ig_entry (igen_wk g φ) = (fst (ig_entry g), gentry_wk (snd (ig_entry g)) φ).
Proof. destruct g; reflexivity. Qed.

Lemma ig_entry_sub : forall g σ, ig_entry (igen_sub g σ) = (fst (ig_entry g), gentry_sub (snd (ig_entry g)) σ).
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
    gens_append (gmod_wk Φ φ) k (List.map (fun g => igen_wk g (wk_qn (gm_binders Φ - k) φ)) gs).
Proof.
  induction gs as [| g gs IH]; intros * Hk; cbn [gens_append List.map]; [ reflexivity |].
  rewrite ig_entry_wk; destruct (ig_entry g) as [d E] eqn:Eg; cbn [fst snd].
  rewrite IH by (cbn; lia); cbn [gmod_wk gm_binders].
  replace (S (gm_binders Φ) - S k) with (gm_binders Φ - k) by lia.
  do 2 f_equal; rewrite !gentry_wk_wk; apply gentry_wk_wk_eq.
  set (r := gm_binders Φ - k); replace (gm_binders Φ) with (r + k) by (subst r; lia); apply wk_qn_shiftn_comm.
Qed.

Lemma gens_append_sub : forall gs Φ k σ, k <= gm_binders Φ ->
    gmod_sub (gens_append Φ k gs) σ =
    gens_append (gmod_sub Φ σ) k (List.map (fun g => igen_sub g (sb_qn (gm_binders Φ - k) σ)) gs).
Proof.
  induction gs as [| g gs IH]; intros * Hk; cbn [gens_append List.map]; [ reflexivity |].
  rewrite ig_entry_sub; destruct (ig_entry g) as [d E] eqn:Eg; cbn [fst snd].
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
    destruct E as [? ? ? [] | | | ]; rewrite HΨ; eexists (_ :: Ψ); reflexivity.
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
  induction A; intros * H; try destruct b as [B0 N | U]; cbn in H |- *; try discriminate.
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
  induction A; intros * H; try destruct b as [B0 N | U]; cbn in H |- *; try discriminate.
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
    ctx_scoped n Γ -> Γ ∋ #x ⇒ₘ U -> gunit_scoped (length Γ + n) U.
Proof.
  intros * HΓ Hlk; induction Hlk; cbn in *; destruct_all;
    eapply gunit_scoped_wk; eauto; cbn; lia.
Qed.

Lemma ctx_scoped_placeholders : forall k n, ctx_scoped n (repeat (ce_ass a_True) k).
Proof. induction k; intros; cbn; auto. Qed.

Lemma gmod_scoped_body_ctx : forall Φ n, gmod_scoped n Φ -> ctx_scoped n (body_ctx Φ).
Proof.
  induction Φ as [| Φ IH x [? ? ? [] | | | ] | Φ IH c]; intros * HΦ; cbn in *; destruct_all;
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
    List.Forall (fun g => gentry_scoped (gm_binders Φ - k + n) (snd (ig_entry g))) gs ->
    gmod_scoped n (gens_append Φ k gs).
Proof.
  induction gs as [| g gs IH]; intros * HΦ Hk Hg; cbn [gens_append]; [ assumption |].
  inversion Hg as [| ? ? Hg1 Hgs]; subst.
  destruct (ig_entry g) as [d E] eqn:Eg; cbn [snd] in Hg1.
  apply IH; [ cbn; split; [ assumption | eapply gentry_scoped_wk; [ exact Hg1 | cbn; lia ] ] | cbn; lia |].
  cbn [gm_binders]; replace (S (gm_binders Φ) - S k) with (gm_binders Φ - k) by lia; exact Hgs.
Qed.

Lemma pi_view_scoped : forall A B C n,
    pi_view A = Some (B, C) -> exp_scoped n A -> exp_scoped n B /\ exp_scoped (S n) C.
Proof.
  induction A; intros * H HA; try destruct b as [B0 N | U]; cbn in H, HA; try discriminate; destruct_all.
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
    end.
Proof. intros; cbn [rev]; rewrite ctx_pi_app; destruct e; reflexivity. Qed.

(** The [Π] the arity type of a telescope is, is its outermost parameter. *)
Lemma tele_view_pi : forall T,
    pi_view (ctx_pi T a_True) = option_map (fun BT => (fst BT, ctx_pi (snd BT) a_True)) (tele_view T).
Proof.
  intros T; unfold tele_view; rewrite <- (rev_involutive T) at 1; generalize (rev T) as R; clear T.
  induction R as [| [B | B N | U] R IH]; [ reflexivity | | |]; rewrite ctx_pi_rev_cons; cbn [pi_view tele_open].
  - reflexivity.
  - rewrite IH; destruct (tele_open R) as [[B' T'] |]; cbn; [ rewrite ctx_pi_sub; reflexivity | reflexivity ].
  - rewrite IH; destruct (tele_open R) as [[B' T'] |]; cbn; [ rewrite ctx_pi_sub; reflexivity | reflexivity ].
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
  induction R as [| [B | B N | U] R IH]; intros φ; [ reflexivity | | |];
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
Qed.

Lemma tele_view_sub : forall T σ,
    tele_view (tele_sub T σ) = option_map (fun BT => ((fst BT)[σ], tele_sub (snd BT) (q σ))) (tele_view T).
Proof.
  intros T; unfold tele_view; rewrite <- (rev_involutive T); generalize (rev T) as R; clear T.
  induction R as [| [B | B N | U] R IH]; intros σ; [ reflexivity | | |];
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
Qed.

Lemma ctx_scoped_rev_cons : forall e R n,
    ctx_scoped n (rev (e :: R)) <-> ce_scoped n e /\ ctx_scoped (S n) (rev R).
Proof. intros; cbn [rev]; rewrite ctx_scoped_app; cbn; tauto. Qed.

Lemma tele_view_scoped : forall T B T' n,
    tele_view T = Some (B, T') -> ctx_scoped n T -> exp_scoped n B /\ ctx_scoped (S n) T'.
Proof.
  intros T; unfold tele_view; rewrite <- (rev_involutive T); generalize (rev T) as R; clear T.
  intros R; rewrite rev_involutive; induction R as [| [B0 | B0 N | U] R IH]; intros * Hv HT; cbn [tele_open] in Hv; [ discriminate | | |];
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
Qed.

(** *** Member Types *)

Definition mres_scoped (n : nat) (R : mres) : Prop :=
  match R with
  | mr_term A => exp_scoped n A
  | mr_mod T | mr_indm T => ctx_scoped n T
  end.

Lemma mres_ty_scoped : forall R n, mres_scoped n R -> exp_scoped n (mres_ty R).
Proof. intros [A | T | T] n H; cbn in *; [ exact H | apply ctx_pi_scoped; [ exact H | exact I ] | apply ctx_pi_scoped; [ exact H | exact I ] ]. Qed.

Lemma mres_gen_scoped : forall Δ R n,
    ctx_scoped n Δ -> mres_scoped (length Δ + n) R -> mres_scoped n (mres_gen Δ R).
Proof.
  intros Δ [A | T | T] n HΔ HR; cbn in *; [ apply ctx_pi_scoped; assumption | apply ctx_scoped_app; auto | apply ctx_scoped_app; auto ].
Qed.

Lemma mres_app_scoped : forall R N R' n,
    mres_app R N = Some R' -> mres_scoped n R -> exp_scoped n N -> mres_scoped n R'.
Proof.
  intros [A | T | T] * Ha HR HN; cbn in *.
  - destruct (pi_view A) as [[B C] |] eqn:E; [| discriminate ]; injection Ha as <-; cbn.
    destruct (pi_view_scoped _ _ _ _ E HR) as [_ HC]; apply exp_scoped_sub1; assumption.
  - unfold tele_inst in Ha; destruct (tele_view T) as [[B T'] |] eqn:E; [| discriminate ]; injection Ha as <-; cbn.
    destruct (tele_view_scoped _ _ _ _ E HR) as [_ HT']; eapply tele_sub_scoped; [ eassumption |].
    intros [| x] ?; cbn; auto; lia.
  - unfold tele_inst in Ha; destruct (tele_view T) as [[B T'] |] eqn:E; [| discriminate ]; injection Ha as <-; cbn.
    destruct (tele_view_scoped _ _ _ _ E HR) as [_ HT']; eapply tele_sub_scoped; [ eassumption |].
    intros [| x] ?; cbn; auto; lia.
Qed.

Lemma mres_closed_wk : forall R φ, mres_scoped 0 R -> mres_wk R φ = R.
Proof. intros [A | T | T] φ H; cbn in *; [ rewrite exp_closed_wk | rewrite tele_closed_wk | rewrite tele_closed_wk ]; auto. Qed.

Lemma mres_closed_sub : forall R σ, mres_scoped 0 R -> mres_sub R σ = R.
Proof. intros [A | T | T] σ H; cbn in *; [ rewrite exp_closed_sub | rewrite tele_closed_sub | rewrite tele_closed_sub ]; auto. Qed.

Lemma mres_tl_wk : forall R T φ, mres_tl R = Some T -> mres_tl (mres_wk R φ) = Some (tele_wk T φ).
Proof. intros [] * H; cbn in *; congruence. Qed.

Lemma mres_tl_sub : forall R T σ, mres_tl R = Some T -> mres_tl (mres_sub R σ) = Some (tele_sub T σ).
Proof. intros [] * H; cbn in *; congruence. Qed.

Lemma mres_tl_ty : forall R T, mres_tl R = Some T -> mres_ty R = ctx_pi T a_True /\ mres_kind R = mk_mod.
Proof. intros [] * H; cbn in *; try discriminate; injection H as ->; auto. Qed.

Lemma mres_kind_gen : forall Δ R, mres_kind (mres_gen Δ R) = mres_kind R.
Proof. intros Δ []; reflexivity. Qed.

Lemma mres_kind_wk : forall R φ, mres_kind (mres_wk R φ) = mres_kind R.
Proof. intros []; reflexivity. Qed.

Lemma mres_kind_sub : forall R σ, mres_kind (mres_sub R σ) = mres_kind R.
Proof. intros []; reflexivity. Qed.

Lemma mres_ty_gen : forall Δ R, mres_ty (mres_gen Δ R) = ctx_pi Δ (mres_ty R).
Proof. intros Δ [A | T | T]; cbn; [ reflexivity | apply ctx_pi_app | apply ctx_pi_app ]. Qed.

Lemma mres_ty_wk : forall R φ, mres_ty (mres_wk R φ) = (mres_ty R)[φ]ʷ.
Proof. intros [A | T | T] φ; cbn; [ reflexivity | rewrite ctx_pi_wk; reflexivity | rewrite ctx_pi_wk; reflexivity ]. Qed.

Lemma mres_ty_sub : forall R σ, mres_ty (mres_sub R σ) = (mres_ty R)[σ].
Proof. intros [A | T | T] σ; cbn; [ reflexivity | rewrite ctx_pi_sub; reflexivity | rewrite ctx_pi_sub; reflexivity ]. Qed.

Lemma mres_gen_wk : forall Δ R φ,
    mres_wk (mres_gen Δ R) φ = mres_gen (tele_wk Δ φ) (mres_wk R (wk_qn (length Δ) φ)).
Proof. intros Δ [A | T | T] φ; cbn; [ rewrite ctx_pi_wk | rewrite tele_wk_app | rewrite tele_wk_app ]; reflexivity. Qed.

Lemma mres_gen_sub : forall Δ R σ,
    mres_sub (mres_gen Δ R) σ = mres_gen (tele_sub Δ σ) (mres_sub R (sb_qn (length Δ) σ)).
Proof. intros Δ [A | T | T] σ; cbn; [ rewrite ctx_pi_sub | rewrite tele_sub_app | rewrite tele_sub_app ]; reflexivity. Qed.

Lemma mres_gen_app : forall Ψ Δ R, mres_gen (Ψ ++ Δ) R = mres_gen Δ (mres_gen Ψ R).
Proof. intros Ψ Δ [A | T | T]; cbn; [ rewrite ctx_pi_app | rewrite app_assoc | rewrite app_assoc ]; reflexivity. Qed.

Lemma mres_gen_nil : forall R, mres_gen nil R = R.
Proof. intros [A | T | T]; cbn; [| rewrite app_nil_r | rewrite app_nil_r ]; reflexivity. Qed.

(** Applying a member type is applying its type. *)
Lemma mres_app_ty : forall R N R', mres_app R N = Some R' ->
    exists B C, pi_view (mres_ty R) = Some (B, C) /\ mres_ty R' = C[Id,,N] /\ mres_kind R' = mres_kind R.
Proof.
  intros [A | T | T] * Ha; cbn in *.
  - destruct (pi_view A) as [[B C] |] eqn:E; [| discriminate ]; injection Ha as <-; eauto.
  - unfold tele_inst in Ha; destruct (tele_view T) as [[B T'] |] eqn:E; [| discriminate ]; injection Ha as <-.
    exists B, (ctx_pi T' a_True); rewrite tele_view_pi, E; cbn.
    rewrite ctx_pi_sub; auto.
  - unfold tele_inst in Ha; destruct (tele_view T) as [[B T'] |] eqn:E; [| discriminate ]; injection Ha as <-.
    exists B, (ctx_pi T' a_True); rewrite tele_view_pi, E; cbn.
    rewrite ctx_pi_sub; auto.
Qed.

Lemma mres_app_of_pi : forall R N B C, pi_view (mres_ty R) = Some (B, C) ->
    exists R', mres_app R N = Some R'.
Proof.
  intros [A | T | T] * Hp; cbn in *.
  - rewrite Hp; eauto.
  - rewrite tele_view_pi in Hp; unfold tele_inst.
    destruct (tele_view T) as [[B0 T0] |]; cbn in *; [ eauto | discriminate ].
  - rewrite tele_view_pi in Hp; unfold tele_inst.
    destruct (tele_view T) as [[B0 T0] |]; cbn in *; [ eauto | discriminate ].
Qed.

Lemma mres_app_wk : forall R N R' φ, mres_app R N = Some R' ->
    mres_app (mres_wk R φ) N[φ]ʷ = Some (mres_wk R' φ).
Proof.
  intros [A | T | T] * Ha; cbn in *.
  - destruct (pi_view A) as [[B C] |] eqn:E; [| discriminate ]; injection Ha as <-.
    rewrite (pi_view_wk _ _ _ _ E); cbn; rewrite exp_wk_sub_extend; reflexivity.
  - unfold tele_inst in *; rewrite tele_view_wk.
    destruct (tele_view T) as [[B T'] |] eqn:E; [| discriminate ]; injection Ha as <-; cbn.
    f_equal; f_equal.
    rewrite tele_wk_sub, <- tele_sub_of_wk, tele_sub_sub; apply tele_sub_sb_eq.
    intros [| x]; reduce_index; reflexivity.
  - unfold tele_inst in *; rewrite tele_view_wk.
    destruct (tele_view T) as [[B T'] |] eqn:E; [| discriminate ]; injection Ha as <-; cbn.
    f_equal; f_equal.
    rewrite tele_wk_sub, <- tele_sub_of_wk, tele_sub_sub; apply tele_sub_sb_eq.
    intros [| x]; reduce_index; reflexivity.
Qed.

Lemma mres_app_sub : forall R N R' σ, mres_app R N = Some R' ->
    mres_app (mres_sub R σ) N[σ] = Some (mres_sub R' σ).
Proof.
  intros [A | T | T] * Ha; cbn in *.
  - destruct (pi_view A) as [[B C] |] eqn:E; [| discriminate ]; injection Ha as <-.
    rewrite (pi_view_sub _ _ _ _ E); cbn; rewrite exp_sub_extend_comm; reflexivity.
  - unfold tele_inst in *; rewrite tele_view_sub.
    destruct (tele_view T) as [[B T'] |] eqn:E; [| discriminate ]; injection Ha as <-; cbn.
    f_equal; f_equal.
    rewrite !tele_sub_sub; apply tele_sub_sb_eq.
    intros [| x]; reduce_index; [ reflexivity |].
    rewrite sentry_sub_shift_extend; apply sentry_sub_id.
  - unfold tele_inst in *; rewrite tele_view_sub.
    destruct (tele_view T) as [[B T'] |] eqn:E; [| discriminate ]; injection Ha as <-; cbn.
    f_equal; f_equal.
    rewrite !tele_sub_sub; apply tele_sub_sb_eq.
    intros [| x]; reduce_index; [ reflexivity |].
    rewrite sentry_sub_shift_extend; apply sentry_sub_id.
Qed.

Lemma ctx_scoped_closed : forall T n, ctx_scoped 0 T -> ctx_scoped n T.
Proof.
  intros * HT; rewrite <- (tele_closed_wk T (fun x => x) HT).
  eapply tele_wk_scoped; [ exact HT | lia ].
Qed.

Lemma mres_scoped_closed : forall R n, mres_scoped 0 R -> mres_scoped n R.
Proof.
  intros [A | T | T] n H; cbn in *; [ eapply exp_scoped_mono; [| exact H ]; lia | apply ctx_scoped_closed; exact H | apply ctx_scoped_closed; exact H ].
Qed.

Lemma member_type_scoped_all : forall Θ Ξ,
    (forall Γ H ch R, member_type Θ Ξ Γ H ch R ->
       gctx_closed Θ Ξ -> ctx_scoped 0 Γ -> modexp_scoped (length Γ) H -> mres_scoped (length Γ) R) /\
    (forall Γ U ch R, unit_member_type Θ Ξ Γ U ch R ->
       gctx_closed Θ Ξ -> ctx_scoped 0 Γ -> gunit_scoped (length Γ) U -> mres_scoped (length Γ) R) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx ->
       gctx_closed Θ Ξ -> ctx_scoped 0 Γ -> gmod_scoped (length Γ) Φ -> gmod_scoped (length Γ) Φx) /\
    (forall io Γ H its gs, items_gen Θ Ξ io Γ H its gs ->
       gctx_closed Θ Ξ -> ctx_scoped 0 Γ -> modexp_scoped (length Γ) H ->
       List.Forall (fun g => gentry_scoped (length Γ) (snd (ig_entry g))) gs).
Proof.
  intros Θ Ξ; apply member_type_both_ind; intros; cbn [mres_scoped] in *; cbn in *; destruct_all.
  - match goal with Hc : gctx_closed _ _, Hr : gc_resolve _ _ _ = _ |- _ => destruct (gctx_closed_resolve _ _ _ _ _ _ _ Hc Hr) as [HA _] end.
    eapply exp_scoped_mono; [| eassumption ]; lia.
  - match goal with Hc : gctx_closed _ _, Hr : gc_module _ _ _ = _ |- _ => pose proof (gctx_closed_module _ _ _ _ Hc Hr) as HT end; cbn in HT.
    apply ctx_scoped_closed; apply HT.
  - match goal with Hc : gctx_closed _ _, Hr : gc_module _ _ _ = _ |- _ => pose proof (gctx_closed_module _ _ _ _ Hc Hr) as HT end; cbn in HT.
    apply ctx_scoped_closed; apply HT.
  - match goal with Hc : gctx_closed _ _, Hr : gc_module _ _ _ = _ |- _ => pose proof (gctx_closed_module _ _ _ _ Hc Hr) as HU end; cbn in HU.
    match goal with IH : _ -> _ -> _ -> mres_scoped 0 ?R |- mres_scoped _ ?R => apply mres_scoped_closed, IH; [ assumption | exact I | exact HU ] end.
  - match goal with IH : _ -> _ -> gunit_scoped _ ?U -> _, Hl : _ ∋ # _ ⇒ₘ ?U, HΓ : ctx_scoped 0 _ |- _ =>
      apply IH; [ assumption | assumption |]; pose proof (ctx_scoped_lookup_mod _ _ _ _ HΓ Hl) as HU; rewrite Nat.add_0_r in HU; exact HU end.
  - auto.
  - match goal with IH : _ -> _ -> _ -> _ |- _ => apply IH; assumption end.
  - eapply mres_app_scoped; [ eassumption | | assumption ].
    match goal with IH : _ -> _ -> _ -> _ |- _ => apply IH; assumption end.
  - rewrite gunit_scoped_mk in *; destruct_all; assumption.
  - rewrite gunit_scoped_mk in *; destruct_all; cbn in *.
    match goal with IH : _ -> _ -> gmod_scoped _ Φ -> gmod_scoped _ Φx |- _ =>
      assert (HΦx : gmod_scoped (length Δ + length Γ) Φx)
        by (rewrite <- length_app; apply IH; [ assumption | apply ctx_scoped_app_iff; split; assumption | rewrite length_app; assumption ]) end.
    match goal with Hp : gm_prefix_upto _ _ = _ |- _ => pose proof (gm_prefix_upto_scoped _ _ _ _ Hp HΦx) as HΦ' end; cbn in HΦ'; destruct_all.
    apply ctx_pi_scoped; [ apply ctx_scoped_app; split; [ apply gmod_scoped_body_ctx; assumption | assumption ] |].
    rewrite length_app, length_body_ctx, <- Nat.add_assoc; assumption.
  - rewrite gunit_scoped_mk in *; destruct_all; cbn in *.
    match goal with IH : _ -> _ -> gmod_scoped _ Φ -> gmod_scoped _ Φx |- _ =>
      assert (HΦx : gmod_scoped (length Δ + length Γ) Φx)
        by (rewrite <- length_app; apply IH; [ assumption | apply ctx_scoped_app_iff; split; assumption | rewrite length_app; assumption ]) end.
    match goal with Hp : gm_prefix_upto _ _ = _ |- _ => pose proof (gm_prefix_upto_scoped _ _ _ _ Hp HΦx) as HΦ' end; cbn in HΦ'; destruct_all.
    apply mres_gen_scoped; [ apply ctx_scoped_app; split; [ apply gmod_scoped_body_ctx; assumption | assumption ] |].
    rewrite length_app, length_body_ctx, <- Nat.add_assoc.
    match goal with IH : _ -> _ -> _ -> mres_scoped _ ?R |- mres_scoped _ ?R =>
      replace (gm_binders Φ' + (length Δ + length Γ)) with (length (body_ctx Φ' ++ Δ ++ Γ)) by (rewrite !length_app, length_body_ctx; lia); apply IH end.
    + assumption.
    + apply ctx_scoped_app_iff; split; [| apply ctx_scoped_app_iff; split; assumption ].
      rewrite length_app; apply gmod_scoped_body_ctx; assumption.
    + rewrite !length_app, length_body_ctx; assumption.
  - rewrite gunit_scoped_mk in *; destruct_all; cbn in *.
    apply mres_gen_scoped; [ assumption |].
    rewrite <- length_app; match goal with IH : _ -> _ -> _ -> mres_scoped _ ?R |- mres_scoped _ ?R => apply IH end;
      [ assumption | apply ctx_scoped_app_iff; split; assumption | rewrite length_app; assumption ].
  - (* the empty body *) exact I.
  - (* an entry *)
    split; [ auto |].
    match goal with Hx : body_xp _ _ _ _ _ |- _ => rewrite (body_xp_binders _ _ _ _ _ Hx) end; assumption.
  - (* an open: its generated entries *)
    match goal with IH : _ -> _ -> gmod_scoped _ Φ -> gmod_scoped _ Φx |- _ =>
      assert (HΦx : gmod_scoped (length Γ) Φx) by (apply IH; assumption) end.
    apply gens_append_scoped; [ assumption | lia |].
    rewrite Nat.sub_0_r, <- length_body_ctx, <- length_app.
    match goal with IH : _ -> _ -> _ -> List.Forall _ gs |- _ => apply IH end.
    + assumption.
    + apply ctx_scoped_app_iff; split; [ apply gmod_scoped_body_ctx; assumption | assumption ].
    + rewrite length_app, length_body_ctx; match goal with Hx : body_xp _ _ _ _ _ |- _ => rewrite (body_xp_binders _ _ _ _ _ Hx) end; assumption.
  - constructor.
  - constructor; [ cbn; split; [ exact I | assumption ] | auto ].
  - constructor; [ cbn; split; [| assumption ] | auto ].
    match goal with IH : _ -> _ -> _ -> exp_scoped _ ?A |- exp_scoped _ ?A => apply IH; assumption end.
  - constructor; [ cbn; split; [ exact I | assumption ] | auto ].
  - constructor; [ exact I | auto ].
  - constructor; [ cbn; split; [ exact I | assumption ] | auto ].
Qed.

Corollary member_type_scoped : forall Θ Ξ,
    (forall Γ H ch R, member_type Θ Ξ Γ H ch R ->
       gctx_closed Θ Ξ -> ctx_scoped 0 Γ -> modexp_scoped (length Γ) H -> mres_scoped (length Γ) R) /\
    (forall Γ U ch R, unit_member_type Θ Ξ Γ U ch R ->
       gctx_closed Θ Ξ -> ctx_scoped 0 Γ -> gunit_scoped (length Γ) U -> mres_scoped (length Γ) R).
Proof. intros; destruct (member_type_scoped_all Θ Ξ) as (H1 & H2 & _); split; assumption. Qed.

Corollary body_xp_scoped : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx ->
    gctx_closed Θ Ξ -> ctx_scoped 0 Γ -> gmod_scoped (length Γ) Φ -> gmod_scoped (length Γ) Φx.
Proof. intros Θ Ξ; exact (proj1 (proj2 (proj2 (member_type_scoped_all Θ Ξ)))). Qed.

(** ** Member Types under a Weakening *)

(** A weakening sends a module slot to a slot of the same unit. *)
Definition wk_mod_compat (φ : wk) (Γ Δ : ctx) : Prop :=
  forall x U, Δ ∋ #x ⇒ₘ U -> Γ ∋ #(φ x) ⇒ₘ gunit_wk U φ.

Lemma wk_mod_compat_q : forall φ Γ Δ e,
    wk_mod_compat φ Γ Δ -> wk_mod_compat (wk_q φ) (centry_wk e φ :: Γ) (e :: Δ).
Proof.
  intros * Hφ x U Hlk; inversion Hlk; subst; cbn.
  - rewrite gunit_wk_shift_wk_q; constructor.
  - rewrite gunit_wk_shift_wk_q; constructor; auto.
Qed.

Lemma wk_mod_compat_ext : forall Ψ φ Γ Δ,
    wk_mod_compat φ Γ Δ -> wk_mod_compat (wk_qn (length Ψ) φ) (tele_wk Ψ φ ++ Γ) (Ψ ++ Δ).
Proof. induction Ψ; intros; cbn; auto using wk_mod_compat_q. Qed.

Lemma gm_prefix_upto_ext_wk : forall Φ x Φ' E φ,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x E) ->
    gm_prefix_upto (gmod_wk Φ φ) x = Some (gm_ext (gmod_wk Φ' φ) x (gentry_wk E (wk_qn (gm_binders Φ') φ))).
Proof. intros * H; rewrite gm_prefix_upto_wk, H; reflexivity. Qed.

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

Lemma member_type_wk_all : forall Θ Ξ,
    gctx_closed Θ Ξ ->
    (forall Δ H ch R, member_type Θ Ξ Δ H ch R ->
       forall Γ φ, wk_mod_compat φ Γ Δ -> member_type Θ Ξ Γ (modexp_wk H φ) ch (mres_wk R φ)) /\
    (forall Δ U ch R, unit_member_type Θ Ξ Δ U ch R ->
       forall Γ φ, wk_mod_compat φ Γ Δ -> unit_member_type Θ Ξ Γ (gunit_wk U φ) ch (mres_wk R φ)) /\
    (forall Δ Φ Φx, body_xp Θ Ξ Δ Φ Φx ->
       forall Γ φ, wk_mod_compat φ Γ Δ -> body_xp Θ Ξ Γ (gmod_wk Φ φ) (gmod_wk Φx φ)) /\
    (forall io Δ H its gs, items_gen Θ Ξ io Δ H its gs ->
       forall Γ φ, wk_mod_compat φ Γ Δ ->
       items_gen Θ Ξ io Γ (modexp_wk H φ) its (List.map (fun g => igen_wk g φ) gs)).
Proof.
  intros Θ Ξ Hc; apply member_type_both_ind; intros; cbn [modexp_wk].
  - destruct (gctx_closed_resolve _ _ _ _ _ _ _ Hc e) as [HA _].
    cbn [mres_wk]; rewrite exp_closed_wk by assumption; eapply mt_unit_def; eassumption.
  - pose proof (proj1 (gctx_closed_module _ _ _ _ Hc e)) as HT; cbn in HT.
    cbn [mres_wk]; rewrite tele_closed_wk by assumption; eapply mt_unit_mod; eassumption.
  - pose proof (proj1 (gctx_closed_module _ _ _ _ Hc e)) as HT; cbn in HT.
    cbn [mres_wk]; rewrite tele_closed_wk by assumption; eapply mt_unit_ind; eassumption.
  - pose proof (gctx_closed_module _ _ _ _ Hc e) as HU; cbn in HU.
    rewrite mres_closed_wk; [ eapply mt_unit_alias; eassumption |].
    exact (proj2 (member_type_scoped Θ Ξ) nil U r R u Hc I HU).
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; [ rewrite mres_kind_wk; assumption | eauto ].
  - econstructor; [ eauto | apply mres_app_wk; eassumption ].
  - rewrite gunit_wk_mk; cbn; constructor.
  - rewrite gunit_wk_mk; cbn [mres_wk]; rewrite ctx_pi_body_wk; eapply umt_def.
    + apply tele_ass_wk; assumption.
    + apply H; apply wk_mod_compat_ext; assumption.
    + apply gm_prefix_upto_def_wk; eassumption.
  - rewrite gunit_wk_mk, mres_gen_wk, tele_wk_app, <- body_ctx_wk; eapply umt_mod; [ rewrite mres_kind_wk; assumption | .. ].
    + apply tele_ass_wk; assumption.
    + apply H; apply wk_mod_compat_ext; assumption.
    + apply gm_prefix_upto_mod_wk; eassumption.
    + replace (body_ctx (gmod_wk Φ' (wk_qn (length Δ) φ)) ++ tele_wk Δ φ ++ Γ0)
        with (tele_wk (body_ctx Φ' ++ Δ) φ ++ Γ0)
        by (rewrite tele_wk_app, body_ctx_wk, <- List.app_assoc; reflexivity).
      replace (gunit_wk Uy (wk_qn (gm_binders Φ') (wk_qn (length Δ) φ)))
        with (gunit_wk Uy (wk_qn (length (body_ctx Φ' ++ Δ)) φ))
        by (apply gunit_wk_wk_eq; rewrite wk_qn_add, length_app, length_body_ctx; reflexivity).
      apply H0; rewrite List.app_assoc; apply wk_mod_compat_ext; assumption.
  - rewrite gunit_wk_mk, mres_gen_wk; cbn; constructor; [ apply tele_ass_wk; assumption |].
    apply H; apply wk_mod_compat_ext; assumption.
  - constructor.
  - cbn [gmod_wk]; match goal with Hx : body_xp _ _ _ _ _ |- _ => rewrite (body_xp_binders _ _ _ _ _ Hx) end;
      constructor; auto.
  - cbn [gmod_wk]; rewrite gens_append_wk by lia; rewrite Nat.sub_0_r.
    match goal with Hx : body_xp _ _ _ ?Φ0 ?Φx0 |- body_xp _ _ _ (gm_open (gmod_wk ?Φ0 _) _ _) _ =>
      rewrite <- (body_xp_binders _ _ _ _ _ Hx) end.
    match goal with Hφ : wk_mod_compat ?φ ?Γ' ?Δ' |- body_xp _ _ ?Γ' _ (gens_append (gmod_wk ?Φx0 ?φ) _ _) =>
      pose proof (wk_mod_compat_ext (body_ctx Φx0) _ _ _ Hφ) as Hφ' end.
    rewrite <- body_ctx_wk, length_body_ctx in Hφ'.
    eapply bx_open; [ eauto | eauto | apply mres_tl_wk; eassumption | eauto | assumption ].
  - constructor.
  - constructor; auto.
  - cbn [List.map igen_wk exp_wk]; constructor; eauto.
  - cbn [List.map igen_wk modexp_wk]; eapply ign_mod; eauto.
  - cbn [List.map igen_wk]; eapply ign_ind; [ eauto | rewrite mod_qname_wk_eq; eassumption | eassumption | eauto ].
  - cbn [List.map igen_wk modexp_wk]; eapply ign_ind_mod; [ eauto | | eauto ].
    intros mp Hq; rewrite mod_qname_wk_eq in Hq; eauto.
Qed.

Corollary member_type_wk : forall Θ Ξ,
    gctx_closed Θ Ξ ->
    (forall Δ H ch R, member_type Θ Ξ Δ H ch R ->
       forall Γ φ, wk_mod_compat φ Γ Δ -> member_type Θ Ξ Γ (modexp_wk H φ) ch (mres_wk R φ)) /\
    (forall Δ U ch R, unit_member_type Θ Ξ Δ U ch R ->
       forall Γ φ, wk_mod_compat φ Γ Δ -> unit_member_type Θ Ξ Γ (gunit_wk U φ) ch (mres_wk R φ)).
Proof. intros * Hc; destruct (member_type_wk_all _ _ Hc) as (H1 & H2 & _); split; assumption. Qed.

Corollary body_xp_wk : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ Φ Φx, body_xp Θ Ξ Δ Φ Φx ->
    forall Γ φ, wk_mod_compat φ Γ Δ -> body_xp Θ Ξ Γ (gmod_wk Φ φ) (gmod_wk Φx φ).
Proof. intros * Hc; exact (proj1 (proj2 (proj2 (member_type_wk_all _ _ Hc)))). Qed.

Corollary unit_xp_wk : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ U Ux, unit_xp Θ Ξ Δ U Ux ->
    forall Γ φ, wk_mod_compat φ Γ Δ -> unit_xp Θ Ξ Γ (gunit_wk U φ) (gunit_wk Ux φ).
Proof.
  intros * Hc * HU * Hφ; destruct HU as [Δu Φ Φx Hx | Δu E]; rewrite !gunit_wk_mk; cbn [moddef_wk]; constructor.
  eapply body_xp_wk; [ eassumption | eassumption | apply wk_mod_compat_ext; assumption ].
Qed.

Corollary member_type_wk_res : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ H ch R, member_type Θ Ξ Δ H ch R ->
    forall Γ φ, wk_mod_compat φ Γ Δ -> member_type Θ Ξ Γ (modexp_wk H φ) ch (mres_wk R φ).
Proof. intros * Hc * Hm * Hφ; exact (proj1 (member_type_wk _ _ Hc) _ _ _ _ Hm _ _ Hφ). Qed.

Corollary member_type_wk_term : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ H ch A, member_type Θ Ξ Δ H ch (mr_term A) ->
    forall Γ φ, wk_mod_compat φ Γ Δ -> member_type Θ Ξ Γ (modexp_wk H φ) ch (mr_term A[φ]ʷ).
Proof. intros * Hc * Hm * Hφ; exact (proj1 (member_type_wk _ _ Hc) _ _ _ _ Hm _ _ Hφ). Qed.

Corollary member_type_wk_mod : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ H ch T, member_type Θ Ξ Δ H ch (mr_mod T) ->
    forall Γ φ, wk_mod_compat φ Γ Δ -> member_type Θ Ξ Γ (modexp_wk H φ) ch (mr_mod (tele_wk T φ)).
Proof. intros * Hc * Hm * Hφ; exact (proj1 (member_type_wk _ _ Hc) _ _ _ _ Hm _ _ Hφ). Qed.

Corollary tele_view_wk_some : forall T B T1 φ, tele_view T = Some (B, T1) ->
    tele_view (tele_wk T φ) = Some (B[φ]ʷ, tele_wk T1 (wk_q φ)).
Proof. intros * Hv; rewrite tele_view_wk, Hv; reflexivity. Qed.

(** ** Member Types under a Substitution *)

(** A substitution sends a module slot to the unit it holds, transported: as a
    literal, or as a slot holding that unit. *)
Definition sub_mod_compat (σ : sub) (Γ Δ : ctx) : Prop :=
  forall x U, Δ ∋ #x ⇒ₘ U ->
    σ x = se_mod (me_lit U[σ]ᵘ) \/ exists y, σ x = se_var y /\ Γ ∋ #y ⇒ₘ U[σ]ᵘ.

(** The root of a module expression, if it is a slot, is a module slot of
    [Γ].  A same-unit substitution sends such a root to a root. *)
Fixpoint me_slot_root (Γ : ctx) (H : modexp) : Prop :=
  match H with
  | me_mem H _ | me_app H _ => me_slot_root Γ H
  | me_var x => exists U, Γ ∋ #x ⇒ₘ U
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
  - right; exists 0; rewrite sb_q_zero, gunit_wk_shift_sub_q; split; [ reflexivity | constructor ].
  - rewrite sb_q_succ, gunit_wk_shift_sub_q.
    match goal with Hl : _ ∋ # _ ⇒ₘ _ |- _ => destruct (Hσ _ _ Hl) as [-> | (y & -> & Hy)] end; [ left; reflexivity |].
    right; exists (S y); split; [ reflexivity | constructor; assumption ].
Qed.

Lemma sub_mod_compat_ext : forall Ψ σ Γ Δ,
    sub_mod_compat σ Γ Δ -> sub_mod_compat (sb_qn (length Ψ) σ) (tele_sub Ψ σ ++ Γ) (Ψ ++ Δ).
Proof. induction Ψ; intros; cbn; auto using sub_mod_compat_q. Qed.

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

Lemma member_type_slot_root : forall Θ Ξ H Δ ch R, member_type Θ Ξ Δ H ch R -> me_slot_root Δ H.
Proof.
  induction H as [fp | x | H IH y | H IH N | U]; intros * Hm; inversion Hm; subst; cbn; eauto.
Qed.

Lemma mod_qname_sub_eq : forall H σ Γ Δ, sub_mod_compat σ Γ Δ -> me_slot_root Δ H -> mod_qname H[σ]ᵐ = mod_qname H.
Proof.
  induction H as [fp | x | H IH y | H IH N | U]; intros * Hσ Hr; cbn in *; try reflexivity.
  - destruct Hr as [U HU]; destruct (Hσ _ _ HU) as [-> | (y & -> & _)]; reflexivity.
  - rewrite (IH _ _ _ Hσ Hr); reflexivity.
Qed.

Lemma member_type_sub_all : forall Θ Ξ,
    gctx_closed Θ Ξ ->
    (forall Δ H ch R, member_type Θ Ξ Δ H ch R ->
       forall Γ σ, sub_mod_compat σ Γ Δ -> member_type Θ Ξ Γ H[σ]ᵐ ch (mres_sub R σ)) /\
    (forall Δ U ch R, unit_member_type Θ Ξ Δ U ch R ->
       forall Γ σ, sub_mod_compat σ Γ Δ -> unit_member_type Θ Ξ Γ U[σ]ᵘ ch (mres_sub R σ)) /\
    (forall Δ Φ Φx, body_xp Θ Ξ Δ Φ Φx ->
       forall Γ σ, sub_mod_compat σ Γ Δ -> body_xp Θ Ξ Γ (gmod_sub Φ σ) (gmod_sub Φx σ)) /\
    (forall io Δ H its gs, items_gen Θ Ξ io Δ H its gs ->
       forall Γ σ, sub_mod_compat σ Γ Δ ->
       items_gen Θ Ξ io Γ H[σ]ᵐ its (List.map (fun g => igen_sub g σ) gs)).
Proof.
  intros Θ Ξ Hc; apply member_type_both_ind; intros; cbn [modexp_sub].
  - destruct (gctx_closed_resolve _ _ _ _ _ _ _ Hc e) as [HA _].
    cbn [mres_sub]; rewrite exp_closed_sub by assumption; eapply mt_unit_def; eassumption.
  - pose proof (proj1 (gctx_closed_module _ _ _ _ Hc e)) as HT; cbn in HT.
    cbn [mres_sub]; rewrite tele_closed_sub by assumption; eapply mt_unit_mod; eassumption.
  - pose proof (proj1 (gctx_closed_module _ _ _ _ Hc e)) as HT; cbn in HT.
    cbn [mres_sub]; rewrite tele_closed_sub by assumption; eapply mt_unit_ind; eassumption.
  - pose proof (gctx_closed_module _ _ _ _ Hc e) as HU; cbn in HU.
    rewrite mres_closed_sub; [ eapply mt_unit_alias; eassumption |].
    exact (proj2 (member_type_scoped Θ Ξ) nil U r R u Hc I HU).
  - destruct (H0 _ _ c) as [-> | (y & -> & Hy)]; cbn [sentry_modexp].
    + eapply mt_lit; eauto.
    + eapply mt_var; eauto.
  - econstructor; eauto.
  - econstructor; [ rewrite mres_kind_sub; assumption | eauto ].
  - econstructor; [ eauto | apply mres_app_sub; eassumption ].
  - rewrite gunit_sub_mk; cbn; constructor.
  - rewrite gunit_sub_mk; cbn [mres_sub]; rewrite ctx_pi_body_sub; eapply umt_def.
    + apply tele_ass_sub; assumption.
    + apply H; apply sub_mod_compat_ext; assumption.
    + apply gm_prefix_upto_def_sub; eassumption.
  - rewrite gunit_sub_mk, mres_gen_sub, tele_sub_app, <- body_ctx_sub; eapply umt_mod; [ rewrite mres_kind_sub; assumption | .. ].
    + apply tele_ass_sub; assumption.
    + apply H; apply sub_mod_compat_ext; assumption.
    + apply gm_prefix_upto_mod_sub; eassumption.
    + replace (body_ctx (gmod_sub Φ' (sb_qn (length Δ) σ)) ++ tele_sub Δ σ ++ Γ0)
        with (tele_sub (body_ctx Φ' ++ Δ) σ ++ Γ0)
        by (rewrite tele_sub_app, body_ctx_sub, <- List.app_assoc; reflexivity).
      replace (Uy[sb_qn (gm_binders Φ') (sb_qn (length Δ) σ)]ᵘ)
        with (Uy[sb_qn (length (body_ctx Φ' ++ Δ)) σ]ᵘ)
        by (apply gunit_sub_sb_eq; rewrite sb_qn_add, length_app, length_body_ctx; reflexivity).
      apply H0; rewrite List.app_assoc; apply sub_mod_compat_ext; assumption.
  - rewrite gunit_sub_mk, mres_gen_sub; cbn; constructor; [ apply tele_ass_sub; assumption |].
    apply H; apply sub_mod_compat_ext; assumption.
  - constructor.
  - cbn [gmod_sub]; match goal with Hx : body_xp _ _ _ _ _ |- _ => rewrite (body_xp_binders _ _ _ _ _ Hx) end;
      constructor; auto.
  - cbn [gmod_sub]; rewrite gens_append_sub by lia; rewrite Nat.sub_0_r.
    match goal with Hx : body_xp _ _ _ ?Φ0 ?Φx0 |- body_xp _ _ _ (gm_open (gmod_sub ?Φ0 _) _ _) _ =>
      rewrite <- (body_xp_binders _ _ _ _ _ Hx) end.
    match goal with Hσ : sub_mod_compat ?σ ?Γ' ?Δ' |- body_xp _ _ ?Γ' _ (gens_append (gmod_sub ?Φx0 ?σ) _ _) =>
      pose proof (sub_mod_compat_ext (body_ctx Φx0) _ _ _ Hσ) as Hσ' end.
    rewrite <- body_ctx_sub, length_body_ctx in Hσ'.
    eapply bx_open; [ eauto | eauto | apply mres_tl_sub; eassumption | eauto | assumption ].
  - constructor.
  - constructor; auto.
  - cbn [List.map igen_sub exp_sub]; constructor; eauto.
  - cbn [List.map igen_sub]; eapply ign_mod; eauto.
  - cbn [List.map igen_sub]; eapply ign_ind; [ eauto | | eassumption | eauto ].
    erewrite mod_qname_sub_eq; [ eassumption | eassumption | eapply member_type_slot_root; eassumption ].
  - cbn [List.map igen_sub]; eapply ign_ind_mod; [ eauto | | eauto ].
    intros mp Hq; erewrite mod_qname_sub_eq in Hq; [ eauto | eassumption | eapply member_type_slot_root; eassumption ].
Qed.

Corollary member_type_sub : forall Θ Ξ,
    gctx_closed Θ Ξ ->
    (forall Δ H ch R, member_type Θ Ξ Δ H ch R ->
       forall Γ σ, sub_mod_compat σ Γ Δ -> member_type Θ Ξ Γ H[σ]ᵐ ch (mres_sub R σ)) /\
    (forall Δ U ch R, unit_member_type Θ Ξ Δ U ch R ->
       forall Γ σ, sub_mod_compat σ Γ Δ -> unit_member_type Θ Ξ Γ U[σ]ᵘ ch (mres_sub R σ)).
Proof. intros * Hc; destruct (member_type_sub_all _ _ Hc) as (H1 & H2 & _); split; assumption. Qed.

Corollary body_xp_sub : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ Φ Φx, body_xp Θ Ξ Δ Φ Φx ->
    forall Γ σ, sub_mod_compat σ Γ Δ -> body_xp Θ Ξ Γ (gmod_sub Φ σ) (gmod_sub Φx σ).
Proof. intros * Hc; exact (proj1 (proj2 (proj2 (member_type_sub_all _ _ Hc)))). Qed.

Corollary unit_xp_sub : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ U Ux, unit_xp Θ Ξ Δ U Ux ->
    forall Γ σ, sub_mod_compat σ Γ Δ -> unit_xp Θ Ξ Γ U[σ]ᵘ Ux[σ]ᵘ.
Proof.
  intros * Hc * HU * Hσ; destruct HU as [Δu Φ Φx Hx | Δu E]; rewrite !gunit_sub_mk; cbn [moddef_sub]; constructor.
  eapply body_xp_sub; [ eassumption | eassumption | apply sub_mod_compat_ext; assumption ].
Qed.

Corollary member_type_sub_res : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ H ch R, member_type Θ Ξ Δ H ch R ->
    forall Γ σ, sub_mod_compat σ Γ Δ -> member_type Θ Ξ Γ H[σ]ᵐ ch (mres_sub R σ).
Proof. intros * Hc * Hm * Hσ; exact (proj1 (member_type_sub _ _ Hc) _ _ _ _ Hm _ _ Hσ). Qed.

Corollary member_type_sub_term : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ H ch A, member_type Θ Ξ Δ H ch (mr_term A) ->
    forall Γ σ, sub_mod_compat σ Γ Δ -> member_type Θ Ξ Γ H[σ]ᵐ ch (mr_term A[σ]).
Proof. intros * Hc * Hm * Hσ; exact (proj1 (member_type_sub _ _ Hc) _ _ _ _ Hm _ _ Hσ). Qed.

Corollary member_type_sub_mod : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ H ch T, member_type Θ Ξ Δ H ch (mr_mod T) ->
    forall Γ σ, sub_mod_compat σ Γ Δ -> member_type Θ Ξ Γ H[σ]ᵐ ch (mr_mod (tele_sub T σ)).
Proof. intros * Hc * Hm * Hσ; exact (proj1 (member_type_sub _ _ Hc) _ _ _ _ Hm _ _ Hσ). Qed.

Corollary tele_view_sub_some : forall T B T1 σ, tele_view T = Some (B, T1) ->
    tele_view (tele_sub T σ) = Some (B[σ], tele_sub T1 (q σ)).
Proof. intros * Hv; rewrite tele_view_sub, Hv; reflexivity. Qed.

(** ** The Opens of an Expansion under the Operations *)

Lemma gm_dropn_wk : forall n Φ φ, gm_dropn n (gmod_wk Φ φ) = gmod_wk (gm_dropn n Φ) φ.
Proof. induction n as [| n IH]; intros [| Φ x E | Φ H its] φ; cbn; auto. Qed.

Lemma gm_dropn_sub : forall n Φ σ, gm_dropn n (gmod_sub Φ σ) = gmod_sub (gm_dropn n Φ) σ.
Proof. induction n as [| n IH]; intros [| Φ x E | Φ H its] σ; cbn; auto. Qed.

Lemma body_opens_wk : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> forall φ,
    body_opens (gmod_wk Φ φ) (gmod_wk Φx φ) =
    List.map (fun p => (tele_wk (fst p) φ, modexp_wk (snd p) (wk_qn (length (fst p)) φ))) (body_opens Φ Φx).
Proof.
  induction 1 as [| Γ Φ Φx x E Hx IH | Γ Φ Φx H its R T gs Hx IH _ _ Hg]; intros φ.
  - reflexivity.
  - cbn [gmod_wk body_opens gm_dropn]; apply IH.
  - cbn [gmod_wk]; rewrite gens_append_wk by lia; rewrite Nat.sub_0_r.
    rewrite body_opens_open_len by (rewrite List.length_map; eapply items_gen_length; eassumption).
    rewrite (body_opens_open _ _ _ _ _ _ _ _ _ Hg); cbn [List.map fst snd]; rewrite IH.
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
    rewrite (body_opens_open _ _ _ _ _ _ _ _ _ Hg); cbn [List.map fst snd]; rewrite IH.
    rewrite body_ctx_sub, length_body_ctx, (body_xp_binders _ _ _ _ _ Hx); reflexivity.
Qed.

Lemma gens_append_body_ctx : forall gs Φ k, exists Ψ, body_ctx (gens_append Φ k gs) = Ψ ++ body_ctx Φ.
Proof.
  induction gs as [| g gs IH]; intros; cbn [gens_append]; [ exists nil; reflexivity |].
  destruct (ig_entry g) as [d E]; destruct (IH (gm_ext Φ d (gentry_wk E (wk_shiftn k))) (S k)) as [Ψ HΨ].
  rewrite HΨ; cbn [body_ctx].
  destruct (gentry_wk E (wk_shiftn k)) as [? ? ? [] | | | ]; eexists (Ψ ++ _ :: nil); rewrite <- List.app_assoc; reflexivity.
Qed.

(** The context an open's prefix makes is the inner part of the body's. *)
Lemma body_opens_prefix : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx ->
    forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> exists Ψr, body_ctx Φx = Ψr ++ Ψ.
Proof.
  induction 1 as [| Γ Φ Φx x E Hx IH | Γ Φ Φx H its R T gs Hx IH _ _ Hg]; intros k Ψ H' Hk.
  - destruct k; discriminate.
  - cbn [body_opens gm_dropn] in Hk; destruct (IH _ _ _ Hk) as [Ψr HΨr]; cbn [body_ctx].
    destruct E as [? ? ? [] | | | ]; eexists (_ :: Ψr); rewrite HΨr; reflexivity.
  - rewrite (body_opens_open _ _ _ _ _ _ _ _ _ Hg) in Hk.
    destruct (gens_append_body_ctx gs Φx 0) as [Ψg HΨg]; rewrite HΨg.
    destruct k as [| k]; cbn in Hk; [ injection Hk as <- <-; exists Ψg; reflexivity |].
    destruct (IH _ _ _ Hk) as [Ψr HΨr]; rewrite HΨr; exists (Ψg ++ Ψr); apply List.app_assoc.
Qed.

(** ** Expansions and δ-Reducts under the Operations *)

(** The three forms an expansion takes. *)
Lemma member_expansion_inv : forall U ch M,
    member_expansion U ch = Some M ->
    (exists Δ E, U = gu_mk Δ (md_alias E) /\ ch <> nil /\ M = ctx_fn Δ (member_ref E ch)) \/
    (exists Δ Φ x Φ' b pv A B, U = gu_mk Δ (md_body Φ) /\ ch = x :: nil /\
       gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) /\
       M = ctx_fn (body_ctx (gm_ext Φ' x (ge_def b pv A B)) ++ Δ) (a_var 0)) \/
    (exists Δ Φ y ch' Φ' pm Uy, U = gu_mk Δ (md_body Φ) /\ ch = y :: ch' /\ ch' <> nil /\
       gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) /\
       M = ctx_fn (body_ctx (gm_ext Φ' y (ge_mod pm Uy)) ++ Δ) (member_ref (me_var 0) ch')).
Proof.
  intros [Δ [Φ | E]] [| x ch'] M H; unfold member_expansion in H; try discriminate.
  - right.
    destruct (gm_prefix_upto Φ x) as [Φx |] eqn:Ex; [| discriminate ].
    destruct Φx as [| Φ' y [b pv A B | pm Uy | pv D Φd | pv Δa pa Nsa] | Φ' c]; try discriminate;
      destruct ch' as [| z ch'']; try discriminate; injection H as <-.
    + pose proof Ex as Ex'; unfold gm_prefix_upto in Ex'.
      assert (y = x) as ->.
      { clear - Ex. induction Φ as [| Φ IH w E | Φ IH c its]; cbn in Ex; try discriminate;
          [ destruct (String.eqb_spec x w) as [-> |]; [ congruence | auto ] | destruct (existsb _ _); [ discriminate | auto ] ]. }
      left; do 8 eexists; repeat split; eassumption.
    + assert (y = x) as ->.
      { clear - Ex. induction Φ as [| Φ IH w E | Φ IH c its]; cbn in Ex; try discriminate;
          [ destruct (String.eqb_spec x w) as [-> |]; [ congruence | auto ] | destruct (existsb _ _); [ discriminate | auto ] ]. }
      right; do 7 eexists; repeat split; try eassumption; discriminate.
  - left; injection H as <-; do 2 eexists; repeat split; discriminate.
Qed.

Lemma member_expansion_alias : forall Δ E ch,
    ch <> nil -> member_expansion (gu_mk Δ (md_alias E)) ch = Some (ctx_fn Δ (member_ref E ch)).
Proof. intros * Hch; destruct ch; [ contradiction | reflexivity ]. Qed.

Lemma member_expansion_def : forall Δ Φ x Φ' b pv A B,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) ->
    member_expansion (gu_mk Δ (md_body Φ)) (x :: nil) =
    Some (ctx_fn (body_ctx (gm_ext Φ' x (ge_def b pv A B)) ++ Δ) (a_var 0)).
Proof. intros * H; unfold member_expansion; rewrite H; reflexivity. Qed.

Lemma member_expansion_mod : forall Δ Φ y ch' Φ' pm Uy,
    ch' <> nil ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
    member_expansion (gu_mk Δ (md_body Φ)) (y :: ch') =
    Some (ctx_fn (body_ctx (gm_ext Φ' y (ge_mod pm Uy)) ++ Δ) (member_ref (me_var 0) ch')).
Proof. intros * Hch H; unfold member_expansion; rewrite H; destruct ch'; [ contradiction | reflexivity ]. Qed.

Lemma member_expansion_wk : forall U ch M φ,
    member_expansion U ch = Some M ->
    member_expansion (gunit_wk U φ) ch = Some M[φ]ʷ.
Proof.
  intros * H; apply member_expansion_inv in H as
    [(Δ & E & -> & Hch & ->) | [(Δ & Φ & x & Φ' & b & pv & A & B & -> & -> & Hp & ->) | (Δ & Φ & y & ch' & Φ' & pm & Uy & -> & -> & Hch & Hp & ->)]];
    rewrite gunit_wk_mk; cbn [moddef_wk].
  - rewrite member_expansion_alias by assumption; rewrite ctx_fn_wk, member_ref_wk; reflexivity.
  - erewrite member_expansion_def by (apply gm_prefix_upto_def_wk; eassumption).
    rewrite ctx_fn_wk, tele_wk_app; destruct B; cbn [body_ctx tele_wk option_map centry_wk];
      rewrite body_ctx_wk, length_body_ctx; cbn; reflexivity.
  - erewrite member_expansion_mod by first [ assumption | apply gm_prefix_upto_mod_wk; eassumption ].
    rewrite ctx_fn_wk, tele_wk_app; cbn [body_ctx tele_wk centry_wk]; rewrite body_ctx_wk, length_body_ctx;
      f_equal; f_equal; cbn [exp_wk bnd_wk length].
    rewrite member_ref_wk; f_equal; f_equal; rewrite ?length_app, ?length_body_ctx;
      apply gunit_wk_wk_eq; rewrite wk_qn_add; reflexivity.
Qed.

Lemma member_expansion_sub : forall U ch M σ,
    member_expansion U ch = Some M ->
    member_expansion U[σ]ᵘ ch = Some M[σ].
Proof.
  intros * H; apply member_expansion_inv in H as
    [(Δ & E & -> & Hch & ->) | [(Δ & Φ & x & Φ' & b & pv & A & B & -> & -> & Hp & ->) | (Δ & Φ & y & ch' & Φ' & pm & Uy & -> & -> & Hch & Hp & ->)]];
    rewrite gunit_sub_mk; cbn [moddef_sub].
  - rewrite member_expansion_alias by assumption; rewrite ctx_fn_sub, member_ref_sub; reflexivity.
  - erewrite member_expansion_def by (apply gm_prefix_upto_def_sub; eassumption).
    rewrite ctx_fn_sub, tele_sub_app; destruct B; cbn [body_ctx tele_sub option_map centry_sub];
      rewrite body_ctx_sub, length_body_ctx; cbn; reflexivity.
  - erewrite member_expansion_mod by first [ assumption | apply gm_prefix_upto_mod_sub; eassumption ].
    rewrite ctx_fn_sub, tele_sub_app; cbn [body_ctx tele_sub centry_sub]; rewrite body_ctx_sub, length_body_ctx;
      f_equal; f_equal; cbn [exp_sub bnd_sub length].
    rewrite member_ref_sub; f_equal; f_equal; rewrite ?length_app, ?length_body_ctx;
      apply gunit_sub_sb_eq; rewrite sb_qn_add; reflexivity.
Qed.

Lemma member_ref_scoped : forall ch H n, modexp_scoped n H -> exp_scoped n (member_ref H ch).
Proof. induction ch as [| x [| y ch] IH]; intros; cbn; auto. apply IH; cbn; assumption. Qed.

Lemma member_expansion_scoped : forall U ch M n,
    member_expansion U ch = Some M -> gunit_scoped n U -> exp_scoped n M.
Proof.
  intros * H HU; apply member_expansion_inv in H as
    [(Δ & E & -> & Hch & ->) | [(Δ & Φ & x & Φ' & b & pv & A & B & -> & -> & Hp & ->) | (Δ & Φ & y & ch' & Φ' & pm & Uy & -> & -> & Hch & Hp & ->)]];
    rewrite gunit_scoped_mk in HU; destruct HU as [HΔ HD]; cbn in HD.
  - apply ctx_fn_scoped; [ assumption | apply member_ref_scoped; assumption ].
  - pose proof (gm_prefix_upto_scoped _ _ _ _ Hp HD) as HΦ.
    apply ctx_fn_scoped; [ apply ctx_scoped_app; split; [ apply gmod_scoped_body_ctx; assumption | assumption ] |].
    rewrite length_app; destruct B; cbn; lia.
  - pose proof (gm_prefix_upto_scoped _ _ _ _ Hp HD) as HΦ.
    apply ctx_fn_scoped; [ apply ctx_scoped_app; split; [ apply gmod_scoped_body_ctx; assumption | assumption ] |].
    apply member_ref_scoped; cbn; rewrite length_app; cbn; lia.
Qed.

(** What the δ-reduct of a chain from a unit is: the global itself, or the
    expansion of a member of a closed alias. *)
Lemma member_unfold_path_closed : forall Θ Ξ Γ fp ch M,
    gctx_closed Θ Ξ -> member_unfold_ch Θ Ξ Γ (me_unit fp) ch M -> exp_scoped 0 M.
Proof.
  intros * Hc H; inversion H; subst; [ apply member_ref_scoped; exact I |].
  match goal with Em : gc_module _ _ _ = Some _ |- _ => pose proof (gctx_closed_module _ _ _ _ Hc Em) as HU; cbn in HU end.
  eapply member_expansion_scoped; eassumption.
Qed.

Lemma unit_noitem_wk : forall U ch φ, unit_noitem U ch -> unit_noitem (gunit_wk U φ) ch.
Proof.
  intros [Δ [Φ | E]] [| x ch] φ Hn; rewrite gunit_wk_mk; cbn [moddef_wk unit_noitem] in *; auto.
  rewrite gm_item_upto_wk, Hn; reflexivity.
Qed.

Lemma unit_noitem_sub : forall U ch σ, unit_noitem U ch -> unit_noitem U[σ]ᵘ ch.
Proof.
  intros [Δ [Φ | E]] [| x ch] σ Hn; rewrite gunit_sub_mk; cbn [moddef_sub unit_noitem] in *; auto.
  rewrite gm_item_upto_sub, Hn; reflexivity.
Qed.

Lemma unit_unfold_wk : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ U ch M, unit_unfold Θ Ξ Δ U ch M ->
    forall Γ φ, wk_mod_compat φ Γ Δ -> unit_unfold Θ Ξ Γ (gunit_wk U φ) ch M[φ]ʷ.
Proof.
  intros * Hc * Hu * Hφ; destruct Hu as [U Ux ch M Hx Hn HM | Δu Φ x ch Φ0 H its1 it Φx0 Hi Hx0 Hne].
  - eapply uu_entry; [ eapply unit_xp_wk; eassumption | apply unit_noitem_wk; exact Hn | apply member_expansion_wk; exact HM ].
  - rewrite gunit_wk_mk; cbn [moddef_wk].
    rewrite ctx_fn_wk, tele_wk_app, member_ref_wk, <- body_ctx_wk.
    rewrite (modexp_wk_wk_eq H _ (wk_qn (gm_binders Φ0) (wk_qn (length Δu) φ)))
      by (rewrite wk_qn_add, length_app, length_body_ctx, (body_xp_binders _ _ _ _ _ Hx0); reflexivity).
    eapply uu_item; [ rewrite gm_item_upto_wk, Hi; reflexivity | | exact Hne ].
    eapply body_xp_wk; [ eassumption | eassumption | apply wk_mod_compat_ext; assumption ].
Qed.

Lemma unit_unfold_sub : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Δ U ch M, unit_unfold Θ Ξ Δ U ch M ->
    forall Γ σ, sub_mod_compat σ Γ Δ -> unit_unfold Θ Ξ Γ U[σ]ᵘ ch M[σ].
Proof.
  intros * Hc * Hu * Hσ; destruct Hu as [U Ux ch M Hx Hn HM | Δu Φ x ch Φ0 H its1 it Φx0 Hi Hx0 Hne].
  - eapply uu_entry; [ eapply unit_xp_sub; eassumption | apply unit_noitem_sub; exact Hn | apply member_expansion_sub; exact HM ].
  - rewrite gunit_sub_mk; cbn [moddef_sub].
    rewrite ctx_fn_sub, tele_sub_app, member_ref_sub, <- body_ctx_sub.
    rewrite (modexp_sub_sb_eq H _ (sb_qn (gm_binders Φ0) (sb_qn (length Δu) σ)))
      by (rewrite sb_qn_add, length_app, length_body_ctx, (body_xp_binders _ _ _ _ _ Hx0); reflexivity).
    eapply uu_item; [ rewrite gm_item_upto_sub, Hi; reflexivity | | exact Hne ].
    eapply body_xp_sub; [ eassumption | eassumption | apply sub_mod_compat_ext; assumption ].
Qed.

Lemma member_unfold_wk : forall Θ Ξ,
    gctx_closed Θ Ξ ->
    forall Δ H ch M, member_unfold_ch Θ Ξ Δ H ch M ->
    forall Γ φ, wk_mod_compat φ Γ Δ -> member_unfold_ch Θ Ξ Γ (modexp_wk H φ) ch M[φ]ʷ.
Proof.
  intros Θ Ξ Hc; induction 1; intros * Hφ; cbn [modexp_wk exp_wk].
  - rewrite member_ref_wk; cbn; eapply muc_unit_def; eassumption.
  - rewrite exp_closed_wk; [ eapply muc_unit_alias; eassumption |].
    eapply member_unfold_path_closed with (Γ := nil); [ eassumption | eapply muc_unit_alias; eassumption ].
  - apply ctx_find_mod_spec, Hφ, ctx_find_mod_spec in H.
    eapply muc_var; [ exact H | eapply unit_unfold_wk; eassumption ].
  - eapply muc_lit; eapply unit_unfold_wk; eassumption.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma member_unfold_sub : forall Θ Ξ,
    gctx_closed Θ Ξ ->
    forall Δ H ch M, member_unfold_ch Θ Ξ Δ H ch M ->
    forall Γ σ, sub_mod_compat σ Γ Δ -> member_unfold_ch Θ Ξ Γ H[σ]ᵐ ch M[σ].
Proof.
  intros Θ Ξ Hc; induction 1; intros * Hσ; cbn [modexp_sub exp_sub].
  - rewrite member_ref_sub; cbn; eapply muc_unit_def; eassumption.
  - rewrite exp_closed_sub; [ eapply muc_unit_alias; eassumption |].
    eapply member_unfold_path_closed with (Γ := nil); [ eassumption | eapply muc_unit_alias; eassumption ].
  - apply ctx_find_mod_spec in H; destruct (Hσ _ _ H) as [-> | (y & -> & Hy)]; cbn [sentry_modexp].
    + eapply muc_lit; eapply unit_unfold_sub; eassumption.
    + apply ctx_find_mod_spec in Hy.
      eapply muc_var; [ exact Hy | eapply unit_unfold_sub; eassumption ].
  - eapply muc_lit; eapply unit_unfold_sub; eassumption.
  - constructor; auto.
  - constructor; auto.
Qed.

(** ** Member Types as the Global Context Grows *)

(** The module of an inductive type names no definition and is no alias. *)
Lemma ind_lookup_not_def : forall Θ Ξ p D,
    ind_lookup Θ Ξ p = Some D -> gc_resolve Θ Ξ p = None /\ forall U r, gc_module Θ Ξ p <> Some (mr_alias U r).
Proof.
  intros * H; destruct (ind_lookup_module _ _ _ _ H) as [T Hm].
  split; [ exact (gc_module_resolve _ _ _ _ Hm) | rewrite Hm; discriminate ].
Qed.

Lemma member_type_gc_sub_all : forall Θ1 Ξ1 Θ2 Ξ2,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 ->
    (forall Γ H ch R, member_type Θ1 Ξ1 Γ H ch R -> member_type Θ2 Ξ2 Γ H ch R) /\
    (forall Γ U ch R, unit_member_type Θ1 Ξ1 Γ U ch R -> unit_member_type Θ2 Ξ2 Γ U ch R) /\
    (forall Γ Φ Φx, body_xp Θ1 Ξ1 Γ Φ Φx -> body_xp Θ2 Ξ2 Γ Φ Φx) /\
    (forall io Γ H its gs, items_gen Θ1 Ξ1 io Γ H its gs -> items_gen Θ2 Ξ2 io Γ H its gs).
Proof.
  intros * Hs; apply member_type_both_ind; intros; econstructor; solve [ eauto using gc_sub_resolve, gc_sub_module ].
Qed.

Lemma member_type_gc_sub : forall Θ1 Ξ1 Θ2 Ξ2,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 ->
    (forall Γ H ch R, member_type Θ1 Ξ1 Γ H ch R -> member_type Θ2 Ξ2 Γ H ch R) /\
    (forall Γ U ch R, unit_member_type Θ1 Ξ1 Γ U ch R -> unit_member_type Θ2 Ξ2 Γ U ch R).
Proof. intros * Hs; destruct (member_type_gc_sub_all _ _ _ _ Hs) as (H1 & H2 & _); split; assumption. Qed.

Lemma unit_xp_gc_sub : forall Θ1 Ξ1 Θ2 Ξ2, gc_sub Θ1 Ξ1 Θ2 Ξ2 ->
    forall Γ U Ux, unit_xp Θ1 Ξ1 Γ U Ux -> unit_xp Θ2 Ξ2 Γ U Ux.
Proof. intros * Hs * []; constructor; apply (member_type_gc_sub_all _ _ _ _ Hs); assumption. Qed.

Lemma unit_unfold_gc_sub : forall Θ1 Ξ1 Θ2 Ξ2, gc_sub Θ1 Ξ1 Θ2 Ξ2 ->
    forall Γ U ch M, unit_unfold Θ1 Ξ1 Γ U ch M -> unit_unfold Θ2 Ξ2 Γ U ch M.
Proof.
  intros * Hs * []; [ eapply uu_entry; [ eapply unit_xp_gc_sub | |]; eassumption |].
  eapply uu_item; [ eassumption | apply (member_type_gc_sub_all _ _ _ _ Hs); eassumption | eassumption ].
Qed.

Lemma member_unfold_gc_sub : forall Θ1 Ξ1 Θ2 Ξ2,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 ->
    forall Γ H ch M, member_unfold_ch Θ1 Ξ1 Γ H ch M -> member_unfold_ch Θ2 Ξ2 Γ H ch M.
Proof.
  intros * Hs; induction 1.
  - eapply muc_unit_def; eapply gc_sub_resolve; eassumption.
  - pose proof (gc_sub_module _ _ _ _ _ _ Hs H0) as Em2.
    eapply muc_unit_alias; [ | exact Em2 | eassumption ].
    intros * Er; rewrite (gc_module_resolve _ _ _ _ Em2) in Er; discriminate.
  - eapply muc_var; [ eassumption | eapply unit_unfold_gc_sub; eassumption ].
  - eapply muc_lit; eapply unit_unfold_gc_sub; eassumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.
