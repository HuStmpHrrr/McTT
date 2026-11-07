(** * Typing What Module Expressions Denote

    The typing lemmas presupposition needs about telescopes, and the
    invariant of descriptions: what a well-formed module expression denotes
    is typed ([desc_ok]).  Its term part is a type, its δ-reduct inhabits
    it, its arguments are typed against the parameters they fill, and the
    entries of its module part denote typed descriptions in turn. *)

From Stdlib Require Import Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System.Global Require Export Paths.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Telescopes *)

Lemma ctx_lookup_app_r : forall E T x A,
    T ∋ #x : A ->
    E ++ T ∋ #(x + length E) : A[wk_shiftn (length E)]ʷ.
Proof.
  induction E as [| B E IH]; intros * H; cbn.
  - rewrite Nat.add_0_r, (exp_wk_wk_eq _ _ _ wk_shiftn_zero), exp_wk_id; assumption.
  - rewrite Nat.add_succ_r, <- (exp_wk_wk_eq _ _ _ (wk_shiftn_succ _)), <- exp_wk_wk.
    constructor; auto.
Qed.

Lemma ctx_lookup_def_app_r : forall E T x A M,
    T ∋ #x ≔ M : A ->
    E ++ T ∋ #(x + length E) ≔ M[wk_shiftn (length E)]ʷ : A[wk_shiftn (length E)]ʷ.
Proof.
  induction E as [| B E IH]; intros * H; cbn.
  - rewrite Nat.add_0_r, !(exp_wk_wk_eq _ _ _ wk_shiftn_zero), !exp_wk_id; assumption.
  - rewrite Nat.add_succ_r, <- !(exp_wk_wk_eq _ _ _ (wk_shiftn_succ _)), <- !exp_wk_wk.
    constructor; auto.
Qed.

Lemma ctx_lookup_mod_app_r : forall E T x U,
    T ∋ #x ≔ₘ U ->
    E ++ T ∋ #(x + length E) ≔ₘ gunit_wk U (wk_shiftn (length E)).
Proof.
  induction E as [| B E IH]; intros * H; cbn.
  - rewrite Nat.add_0_r, (gunit_wk_wk_eq _ _ _ wk_shiftn_zero), gunit_wk_id; assumption.
  - rewrite Nat.add_succ_r, <- (gunit_wk_wk_eq _ _ _ (wk_shiftn_succ _)), <- gunit_wk_wk.
    constructor; auto.
Qed.

Lemma wf_wk_shiftn_app : forall Θ Ξ E T,
    ⊢ Θ ⍮ Ξ ⍮ E ++ T ->
    ⊢ Θ ⍮ Ξ ⍮ T ->
    Θ ⍮ Ξ ⍮ E ++ T ⊢ʷ wk_shiftn (length E) : T.
Proof.
  intros; econstructor; [ eassumption | assumption | | |];
    intros; [ apply ctx_lookup_app_r | apply ctx_lookup_def_app_r | apply ctx_lookup_mod_app_r ]; assumption.
Qed.

Lemma ctx_app_wf_right : forall Θ Ξ E T, ⊢ Θ ⍮ Ξ ⍮ E ++ T -> ⊢ Θ ⍮ Ξ ⍮ T.
Proof.
  induction E as [| B E IH]; intros * H; cbn in *; [ assumption |].
  apply IH; eapply ctx_decomp_tail; eassumption.
Qed.

(** A frame's parameters are assumptions. *)
Lemma wf_gmod_tele_all_assumptions : forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> all_assumptions Δ.
Proof. induction 1; try assumption; constructor; [ do 2 eexists; reflexivity | assumption ]. Qed.

(** So are all the frames' parameters of a well-formed stack. *)
Lemma wf_gstack_tele_all_assumptions : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> all_assumptions (gs_tele Ξ).
Proof.
  induction 1; cbn [gs_tele]; [ constructor | constructor |].
  apply List.Forall_app; split; [ eapply wf_gmod_tele_all_assumptions; eassumption | assumption ].
Qed.

(** A sort other than [LevelSort] is a term of a large universe;
    [LevelSort] itself is of no sort. *)
Lemma type_sort_large : forall Θ Ξ Γ C, ⊢ Θ ⍮ Ξ ⍮ Γ -> type_sort C -> C <> LevelSort -> exists i, Θ ⍮ Ξ ⍮ Γ ⊢ C : Typeω@i.
Proof.
  intros * HΓ [] Hn; [ exists (S i); apply wf_typ; exact HΓ | | contradiction (Hn eq_refl) ].
  exists 0; apply wf_prop_large; exact HΓ.
Qed.

(** [wf_let] and its [ζ] at a sort [C], which [C[Id,,M]] is by
    computation only.  A sort other than [LevelSort] is in a large
    universe, which any binding may build. *)
Lemma wf_let_sort : forall Θ Ξ Γ A M B Srt C,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt ->
    type_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
    type_sort C ->
    C <> LevelSort ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B : C.
Proof.
  intros * HA HS HM HB HC Hn; rewrite <- (type_sort_sub C (Id,,M) HC).
  destruct (type_sort_large _ _ _ _ (presup_exp_ctx HB) HC Hn) as [i Hi].
  eapply wf_let; [ exact HA | exact HS | exact HM | exact Hi | constructor | exact HB ].
Qed.

Lemma wf_exp_eq_let_zeta_sort : forall Θ Ξ Γ A M B Srt C,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt ->
    type_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
    type_sort C ->
    C <> LevelSort ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ B[Id,,M] : C.
Proof.
  intros * HA HS HM HB HC Hn; rewrite <- (type_sort_sub C (Id,,M) HC).
  destruct (type_sort_large _ _ _ _ (presup_exp_ctx HB) HC Hn) as [i Hi].
  eapply wf_exp_eq_let_zeta; [ exact HA | exact HS | exact HM | exact Hi | constructor | exact HB ].
Qed.

(** The same for a local module. *)
Lemma wf_let_mod_sort : forall Θ Ξ Γ U B C,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C ->
    type_sort C ->
    C <> LevelSort ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B : C.
Proof.
  intros * HU HB HC Hn; destruct (type_sort_large _ _ _ C (presup_exp_ctx HB) HC Hn) as [i HCS].
  rewrite <- (type_sort_sub C (Id ,,ₘ me_lit U) HC); eapply wf_let_mod; [ exact HU | exact HCS | constructor | constructor | exact HB ].
Qed.

Lemma wf_exp_eq_let_mod_zeta_sort : forall Θ Ξ Γ U B C,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C ->
    type_sort C ->
    C <> LevelSort ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C.
Proof.
  intros * HU HB HC Hn; destruct (type_sort_large _ _ _ C (presup_exp_ctx HB) HC Hn) as [i HCS].
  rewrite <- (type_sort_sub C (Id ,,ₘ me_lit U) HC);
    eapply wf_exp_eq_let_mod_zeta; [ exact HU | exact HCS | constructor | constructor | exact HB ].
Qed.

(** [wf_let] at a universe, which [Typeω@j[Id,,M]] is by computation only. *)
Lemma wf_let_typ : forall Θ Ξ Γ A M B Srt j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt ->
    type_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B : Typeω@j.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B : Typeω@j[Id,,M]) as Hl
    by (eapply wf_let with (Srt := Srt);
        [ eassumption | eassumption | eassumption | apply wf_typ; eauto using presup_exp_ctx | constructor | eassumption ]).
  exact Hl.
Qed.

Lemma wf_exp_eq_let_zeta_typ : forall Θ Ξ Γ A M B Srt j,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Srt ->
    type_sort Srt ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ B[Id,,M] : Typeω@j.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B ≈ B[Id,,M] : Typeω@j[Id,,M]) as Hl
      by (eapply wf_exp_eq_let_zeta with (Srt := Srt);
          [ eassumption | eassumption | eassumption | apply wf_typ; eauto using presup_exp_ctx | constructor | eassumption ]).
  exact Hl.
Qed.

(** The same for a local module. *)
Lemma wf_let_mod_typ : forall Θ Ξ Γ U B j,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B : Typeω@j.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B : Typeω@j[Id ,,ₘ me_lit U]) as Hl
    by (eapply wf_let_mod; [ eassumption | econstructor; eauto using presup_exp_ctx | constructor | constructor | eassumption ]).
  exact Hl.
Qed.

Lemma wf_exp_eq_let_mod_zeta_typ : forall Θ Ξ Γ U B j,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
    Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : Typeω@j ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : Typeω@j.
Proof.
  intros.
  assert (Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : Typeω@j[Id ,,ₘ me_lit U]) as Hl
      by (eapply wf_exp_eq_let_mod_zeta; [ eassumption | econstructor; eauto using presup_exp_ctx | constructor | constructor | eassumption ]).
  exact Hl.
Qed.

#[export]
Hint Resolve wf_let_typ wf_exp_eq_let_zeta_typ wf_let_mod_typ wf_exp_eq_let_mod_zeta_typ : mctt.

(** The kinds of a [Π] out of a domain of any kind into a codomain of a
    kind that is not of levels ([pi_kinds]). *)
Lemma pi_kinds_not_level : forall κd r, r <> ak_level -> pi_kinds κd r.
Proof. intros κd [] Hr; [ constructor | constructor | contradiction ]. Qed.

(** A [Π] out of a domain of the kind [κd] (of a sort of that kind) into
    a type of the sort of the kind [r] next to a large universe, [r] not of
    levels, is of that sort: into a type of a large universe at a common
    level, into a proposition a proposition. *)
Lemma wf_pi_sort_at : forall Θ Ξ Γ κd r B A Srt i,
    Θ ⍮ Ξ ⍮ Γ ⊢ B : Srt ->
    sort_kind Srt κd ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} B ⊢ A : abs_kind_sort r Typeω@i ->
    r <> ak_level ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ a_pi κd r B A : abs_kind_sort r Typeω@j.
Proof.
  intros * HB HS HA Hr; pose proof (pi_kinds_not_level κd _ Hr) as Hk; destruct HS as [k | |].
  - exists (max k i); exact (wf_pi_at_max _ _ _ ak_relevant r _ _ _ _ HB HA Hk).
  - exists i; eapply wf_pi with (U := Typeω@i) (κd := ak_propositional) (κc := r);
      [ apply wf_is_univ_large; eapply presup_exp_ctx, HB | exact HB | rewrite abs_kind_sort_wk; exact HA | exact Hk ].
  - exists i; eapply wf_pi with (U := Typeω@i) (κd := ak_level) (κc := r);
      [ apply wf_is_univ_large; eapply presup_exp_ctx, HB | exact HB | rewrite abs_kind_sort_wk; exact HA | exact Hk ].
Qed.

(** The congruence of [wf_pi_sort_at]. *)
Lemma wf_exp_eq_pi_sort_at : forall Θ Ξ Γ κd r B B' A A' Srt i,
    Θ ⍮ Ξ ⍮ Γ ⊢ B : Srt ->
    sort_kind Srt κd ->
    Θ ⍮ Ξ ⍮ Γ ⊢ B ≈ B' : Srt ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} B ⊢ A ≈ A' : abs_kind_sort r Typeω@i ->
    r <> ak_level ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ a_pi κd r B A ≈ a_pi κd r B' A' : abs_kind_sort r Typeω@j.
Proof.
  intros * HB HS HBB HA Hr; pose proof (pi_kinds_not_level κd _ Hr) as Hk; destruct HS as [k | |].
  - exists (max k i); exact (wf_exp_eq_pi_cong_at_max _ _ _ ak_relevant r _ _ _ _ _ _ HB HBB HA Hk).
  - exists i; eapply wf_exp_eq_pi_cong with (U := Typeω@i) (κd := ak_propositional) (κc := r);
      [ apply wf_is_univ_large; eapply presup_exp_ctx, HB | exact HB | exact HBB | rewrite abs_kind_sort_wk; exact HA | exact Hk ].
  - exists i; eapply wf_exp_eq_pi_cong with (U := Typeω@i) (κd := ak_level) (κc := r);
      [ apply wf_is_univ_large; eapply presup_exp_ctx, HB | exact HB | exact HBB | rewrite abs_kind_sort_wk; exact HA | exact Hk ].
Qed.

(** Into a type of a large universe. *)
Corollary wf_pi_sort : forall Θ Ξ Γ κd B A Srt i,
    Θ ⍮ Ξ ⍮ Γ ⊢ B : Srt ->
    sort_kind Srt κd ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} B ⊢ A : Typeω@i ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ Π{κd} B A : Typeω@j.
Proof. intros * HB HS HA; exact (wf_pi_sort_at _ _ _ _ ak_relevant _ _ _ _ HB HS HA ltac:(discriminate)). Qed.

(** The [Π] at [r] over a telescope into a term of the sort at [r] is of
    the sort at [r], and the [λ] over it of a term of that type is of it. *)
Lemma ctx_pi_at_wf : forall Θ Ξ r Δ Γ A i,
    r <> ak_level ->
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : abs_kind_sort r Typeω@i ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi_at r Δ A : abs_kind_sort r Typeω@j.
Proof.
  intros Θ Ξ r Δ Γ A i Hr; revert Γ A i.
  assert (HC : forall i, type_sort (abs_kind_sort r Typeω@i)) by (intros; apply type_sort_abs_kind; constructor).
  assert (HCn : forall i, abs_kind_sort r Typeω@i <> LevelSort) by (intros ? E; destruct r; cbn in E; try discriminate E; contradiction).
  induction Δ as [| [κ B | B N | U | B N U] Δ IH]; intros * HΔ HA; cbn in *; [ eauto | | | |];
    inversion HΔ; subst.
  - match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : ?S, HS : sort_kind ?S _ |- _ =>
      destruct (wf_pi_sort_at _ _ _ _ _ _ _ _ _ HB HS HA Hr) as [j Hj];
      eapply IH; [ eauto using presup_exp_ctx | exact Hj ]
    end.
  - (** A definition is generalized as a [let], which is of the type's own
        sort. *)
    eapply IH; [ eauto using presup_exp_ctx |].
    match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : ?S, HS : type_sort ?S, HN : _ ⍮ _ ⍮ _ ⊢ N : B |- _ =>
      eapply (wf_let_sort _ _ _ B N A S); [ exact HB | exact HS | exact HN | exact HA | apply HC | apply HCn ] end.
  - (** So is a module slot, as a [let module]. *)
    eapply IH; [ eauto using presup_unit_eq_ctx |].
    eapply wf_let_mod_sort; [ eassumption | exact HA | apply HC | apply HCn ].
  - (** A definition with a module part is substituted by its body and
        unit. *)
    eapply IH with (i := i); [ eauto using presup_exp_ctx |].
    rewrite <- (type_sort_sub _ (Id ,,ᵈ N ‖ me_lit U) (HC i)).
    eapply sub_preserves_exp; [ eassumption | eapply wf_sub_single_dm; eassumption ].
Qed.

Lemma ctx_fn_at_wf : forall Θ Ξ r Δ Γ A M i,
    r <> ak_level ->
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : abs_kind_sort r Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ M : ctx_pi_at r Δ A.
Proof.
  intros Θ Ξ r Δ Γ A M i Hr; revert Γ A M i.
  assert (HC : forall i, type_sort (abs_kind_sort r Typeω@i)) by (intros; apply type_sort_abs_kind; constructor).
  assert (HCn : forall i, abs_kind_sort r Typeω@i <> LevelSort) by (intros ? E; destruct r; cbn in E; try discriminate E; contradiction).
  assert (Hm : motive_kind r) by (destruct r; [ constructor | constructor | contradiction ]).
  induction Δ as [| [κ B | B N | U | B N U] Δ IH]; intros * HΔ HA HM; cbn in *; [ assumption | | | |];
    inversion HΔ; subst.
  - match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : ?S, HS : sort_kind ?S _ |- _ =>
      destruct (wf_pi_sort_at _ _ _ _ _ _ _ _ _ HB HS HA Hr) as [j Hj];
      eapply IH with (i := j); [ eauto using presup_exp_ctx | exact Hj |];
      eapply wf_fn; [ exact HB | exact HS | exact HA | exact (pi_kinds_not_level _ _ Hr) | exact HM ]
    end.
  - (** The body's [let] has the type [A[Id,,N]], which is the type's [let] by
        ζ. *)
    match goal with HB : _ ⍮ _ ⍮ _ ⊢ B : ?S, HS : type_sort ?S, HN : _ ⍮ _ ⍮ _ ⊢ N : B |- _ =>
      assert (Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ ℓ B ≔ N in A : abs_kind_sort r Typeω@i)
        by (eapply (wf_let_sort _ _ _ B N A S); [ exact HB | exact HS | exact HN | exact HA | apply HC | apply HCn ]);
      eapply IH with (i := i); [ eauto using presup_exp_ctx | eassumption |];
      eapply wf_exp_subtyp';
        [ eapply wf_let with (A := B) (Srt := S);
          [ exact HB | exact HS | exact HN | exact HA | apply level_closed_motive_kind, Hm | exact HM ] |];
      eapply wf_subtyp_refl; [ eassumption | apply HC |];
      eapply wf_exp_eq_sym, (wf_exp_eq_let_zeta_sort _ _ _ B N A S);
        [ exact HB | exact HS | exact HN | exact HA | apply HC | apply HCn ]
    end.
  - assert (Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ ℓₘ U in A : abs_kind_sort r Typeω@i) by (eapply wf_let_mod_sort; [ eassumption | exact HA | apply HC | apply HCn ]).
    eapply IH with (i := i); [ eauto using presup_unit_eq_ctx | eassumption |].
    eapply wf_exp_subtyp'; [ eapply wf_let_mod; [ eassumption | exact HA | apply HC | apply module_body_motive_kind, Hm | exact HM ] |].
    eapply wf_subtyp_refl; [ eassumption | apply HC |].
    eapply wf_exp_eq_sym, wf_exp_eq_let_mod_zeta_sort; [ eassumption | exact HA | apply HC | apply HCn ].
  - (** A definition with a module part: the body and the type are
        substituted alike. *)
    assert (Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ˢ Id ,,ᵈ N ‖ me_lit U : (Δ ++ Γ) ▸ₘ B ≔ N ‖ U) by (eapply wf_sub_single_dm; eassumption).
    eapply IH with (i := i); [ eauto using presup_exp_ctx | |].
    + rewrite <- (type_sort_sub _ (Id ,,ᵈ N ‖ me_lit U) (HC i)); eapply sub_preserves_exp; eassumption.
    + eapply sub_preserves_exp; eassumption.
Qed.

(** The outermost assumption of a telescope of parameters of types of
    levels is a type of levels, and so are the rest. *)
Lemma level_sorted_parameters_cons : forall κ B Δ,
    level_sorted_parameters (ce_ass κ B :: Δ) -> κ = ak_level /\ level_sorted_parameters Δ.
Proof.
  intros * HL; split; [ exact (HL nil κ B Δ eq_refl) |].
  intros Δ1 κ' T Δ2 ->; exact (HL (_ :: Δ1) κ' T Δ2 eq_refl).
Qed.

(** Parameters of types of levels, together. *)
Lemma level_sorted_app : forall Δy Δ,
    level_sorted_parameters Δy -> level_sorted_parameters Δ -> level_sorted_parameters (Δy ++ Δ).
Proof.
  intros * Hy HΔ Δ1 κ T Δ2 E.
  destruct (List.app_eq_app _ _ _ _ E) as (Δc & [[E1 E2] | [E1 E2]]).
  - destruct Δc as [| e Δc]; cbn in E2.
    + apply HΔ with (Δ1 := nil) (T := T) (Δ2 := Δ2); rewrite E2; reflexivity.
    + injection E2 as <- ->; exact (Hy _ _ _ _ E1).
  - exact (HΔ _ _ _ _ E2).
Qed.

(** Parameters of types of levels, apart. *)
Lemma level_sorted_app_inv : forall Δy Δ,
    level_sorted_parameters (Δy ++ Δ) -> level_sorted_parameters Δy /\ level_sorted_parameters Δ.
Proof.
  intros * H; split; intros Δ1 κ T Δ2 E.
  - apply (H Δ1 κ T (Δ2 ++ Δ)); rewrite E, <- List.app_assoc; reflexivity.
  - apply (H (Δy ++ Δ1) κ T Δ2); rewrite E, <- List.app_assoc; reflexivity.
Qed.

(** Each parameter of a telescope may be abstracted at a kind whose
    level case has only levels as parameters. *)
Lemma pi_kinds_of_level_sorted : forall T r, (r = ak_level -> level_sorted_parameters T) ->
    forall Δ1 κ B Δ2, T = Δ1 ++ ce_ass κ B :: Δ2 -> pi_kinds κ r.
Proof.
  intros * Hl * HT; destruct r; [ constructor | constructor |].
  rewrite (Hl eq_refl _ _ _ _ HT); constructor.
Qed.

(** The [Π] of levels ([ctx_pi_at ak_level]) over a telescope whose
    assumptions are types of levels into a type of levels is a type of
    levels; a [let] over a type of levels is one. *)
Lemma ctx_pi_level_wf : forall Θ Ξ Δ Γ A,
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    all_assumptions Δ ->
    level_sorted_parameters Δ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : LevelSort ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi_at ak_level Δ A : LevelSort.
Proof.
  intros Θ Ξ.
  (** A telescope of assumptions only: a [let] of a definition or a local
      module at a type of levels would build a level from a non-level. *)
  induction Δ as [| [κ B | B N | U | B N U] Δ IH]; intros * HΔ Ha HL HA; cbn in *; [ assumption | | | |];
    inversion Ha as [| ? ? (? & ? & He) Ha']; subst; try discriminate.
  destruct (level_sorted_parameters_cons _ _ _ HL) as [-> HL'].
  destruct (ctx_decomp_kind HΔ) as (Srt & HS & HB); inversion HS; subst.
  eapply IH; [ eauto using presup_exp_ctx | exact Ha' | exact HL' |].
  eapply wf_pi with (U := Typeω@0) (κd := ak_level) (κc := ak_level);
    [ apply wf_is_univ_large; eapply presup_exp_ctx, HB | exact HB | exact HA | constructor ].
Qed.

(** The [λ] over such a telescope of a term of a type of levels is of the
    [Π]. *)
Lemma ctx_fn_level_wf : forall Θ Ξ Δ Γ A M,
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    all_assumptions Δ ->
    level_sorted_parameters Δ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : LevelSort ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ M : ctx_pi_at ak_level Δ A.
Proof.
  intros Θ Ξ.
  induction Δ as [| [κ B | B N | U | B N U] Δ IH]; intros * HΔ Ha HL HA HM; cbn in *; [ assumption | | | |];
    inversion Ha as [| ? ? (? & ? & He) Ha']; subst; try discriminate.
  destruct (level_sorted_parameters_cons _ _ _ HL) as [-> HL'].
  destruct (ctx_decomp_kind HΔ) as (Srt & HS & HB); inversion HS; subst.
  assert (HPi : Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ Πₗ B A : LevelSort)
    by (eapply wf_pi with (U := Typeω@0) (κd := ak_level) (κc := ak_level);
        [ apply wf_is_univ_large; eapply presup_exp_ctx, HB | exact HB | exact HA | constructor ]).
  eapply IH; [ eauto using presup_exp_ctx | exact Ha' | exact HL' | exact HPi |].
  eapply wf_fn with (i := 0); [ exact HB | constructor | exact HA | constructor | exact HM ].
Qed.

(** At [relevant], into a type of a large universe. *)
Corollary ctx_pi_wf : forall Θ Ξ Δ Γ A i,
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Typeω@i ->
    exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ A : Typeω@j.
Proof. intros * HΔ HA; exact (ctx_pi_at_wf _ _ ak_relevant _ _ _ _ ltac:(discriminate) HΔ HA). Qed.

Corollary ctx_fn_wf : forall Θ Ξ Δ Γ A M i,
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ M : ctx_pi Δ A.
Proof. intros * HΔ HA HM; exact (ctx_fn_at_wf _ _ ak_relevant _ _ _ _ _ ltac:(discriminate) HΔ HA HM). Qed.

Corollary ctx_pi_wf0 : forall Θ Ξ Δ A i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    exists j, Θ ⍮ Ξ ⍮ ⋅ ⊢ ctx_pi Δ A : Typeω@j.
Proof.
  intros; eapply ctx_pi_wf; rewrite List.app_nil_r; [ eauto using presup_exp_ctx | eassumption ].
Qed.

Corollary ctx_fn_wf0 : forall Θ Ξ Δ A M i,
    Θ ⍮ Ξ ⍮ Δ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ Δ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ ctx_fn Δ M : ctx_pi Δ A.
Proof.
  intros; eapply ctx_fn_wf; rewrite List.app_nil_r; [ eauto using presup_exp_ctx | eassumption.. ].
Qed.

(** The [Π] into the kind [r] (not of levels) over a telescope into a term
    of the sort of [r] is of that sort, and the [λ] over it of a term of
    that type is of it: the type and the body of a definition filed over
    its parameters. *)
Lemma ctx_pi_type : forall Θ Ξ r Δ Γ A i,
    r <> ak_level ->
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : abs_kind_sort r Typeω@i ->
    (exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi_at r Δ A : abs_kind_sort r Typeω@j) /\
    forall M, Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ M : ctx_pi_at r Δ A.
Proof.
  intros * Hr HΔ HA; split; [ eapply ctx_pi_at_wf; eassumption |].
  intros M HM; eapply ctx_fn_at_wf; eassumption.
Qed.

(** The same at any kind [r], a type of levels only over parameters of
    types of levels (as [wf_gentry_def] asks). *)
Lemma ctx_pi_type_kind : forall Θ Ξ r Δ Γ A i,
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    (r = ak_level -> all_assumptions Δ) ->
    (r = ak_level -> level_sorted_parameters Δ) ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : abs_kind_sort r Typeω@i ->
    (exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi_at r Δ A : abs_kind_sort r Typeω@j) /\
    forall M, Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ M : ctx_pi_at r Δ A.
Proof.
  intros * HΔ Ha HL HA; destruct r; try (eapply ctx_pi_type; [ discriminate | eassumption .. ]).
  specialize (HL eq_refl); specialize (Ha eq_refl); cbn [abs_kind_sort] in HA |- *.
  split; [ exists 0; eapply ctx_pi_level_wf; eassumption |].
  intros M HM; eapply ctx_fn_level_wf; eassumption.
Qed.

(** A closed judgment holds in any context. *)
Lemma closed_weaken_exp : forall Θ Ξ Γ M A,
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ ⋅ ⊢ M : A ->
    exp_scoped 0 M -> exp_scoped 0 A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * HΓ HM HsM HsA.
  rewrite <- (exp_closed_wk M (wk_shiftn (length Γ)) HsM),
    <- (exp_closed_wk A (wk_shiftn (length Γ)) HsA).
  eapply wk_preserves_exp; [ exact HM |].
  pose proof (wf_wk_shiftn_app Θ Ξ Γ nil) as Hw; rewrite List.app_nil_r in Hw.
  apply Hw; [ assumption | constructor; eapply ctx_wf_gctx; eassumption ].
Qed.

(** ** Telescopes Filled by Lists of Terms

    A telescope of assumptions over [Γ] is filled by terms of [Γ] typed one by
    one at the instances of its types: the terms are a substitution into it,
    and a term of a [Π] over it applies to them. *)

Lemma ctx_ext_refl : forall Θ Ξ Δ Γ, all_assumptions Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ.
Proof.
  induction Δ as [| e Δ IH]; intros * Hass HΔ; cbn in *; [ constructor; assumption |].
  apply List.Forall_cons_iff in Hass as [(κ & A & ->) Hass'].
  pose proof (ctx_decomp_left HΔ) as HΔ'; destruct (ctx_decomp_kind HΔ) as (Srt & HS & HA).
  eapply wf_ext_eq_ass_same; [ apply IH; assumption | exact HA | exact HS | exact HA ].
Qed.

Lemma ctx_sub_wf : forall Θ Ξ Γ Γ' Δ σ,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ : Γ -> all_assumptions Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ σ ++ Γ'.
Proof.
  intros * Hσ Hass HΔ; eapply ext_eq_ctx_left, sub_preserves_ext; [ apply ctx_ext_refl; eassumption | exact Hσ ].
Qed.

Lemma wf_sub_of_list : forall Θ Ξ Δ Γ Γ0 σ Ms,
    all_assumptions Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ0 -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Γ0 ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ σ Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list σ Ms : Δ ++ Γ0.
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ Hl HMs.
  - destruct Ms; [ exact Hσ | discriminate ].
  - unfold all_assumptions in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [(κ0 & A0 & ->) _].
    rewrite List.length_app in Hl; cbn in Hl.
    destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; cbn in Hl.
    rewrite <- List.app_assoc in HΔ |- *; cbn [List.app] in HΔ |- *.
    destruct (ctx_decomp_sort_kind (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ0 (Srt & HS & HA0)].
    cbn [sb_of_list]; eapply IH; [ exact Hass | exact HΔ | | lia |].
    + eapply wf_sub_extend; [ exact Hσ | exact HA0 | exact HS |].
      apply (HMs 0); [ reflexivity | rewrite tele_insts_snoc; reflexivity ].
    + intros k' N T HN HT; apply (HMs (S k')); [ exact HN | rewrite tele_insts_snoc; exact HT ].
Qed.

Corollary wf_sub_of_list_id : forall Θ Ξ Δ Γ Ms,
    all_assumptions Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Ms : Δ ++ Γ.
Proof. intros; eapply wf_sub_of_list; eauto using wf_sub_id, ctx_app_wf_tail. Qed.

Lemma wf_apps_ctx_pi_n : forall r n Θ Ξ Δ Γ B i M Ms,
    List.length Δ = n ->
    all_assumptions Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ B : abs_kind_sort r Typeω@i ->
    (r = ak_level -> level_sorted_parameters Δ) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ctx_pi_at r Δ B ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ms : B[sb_of_list Id Ms].
Proof.
  intros r; assert (HC : forall i, type_sort (abs_kind_sort r Typeω@i)) by (intros; apply type_sort_abs_kind; constructor).
  induction n as [| n IH]; intros * Hn Hass HΔ HB HL HM Hl HMs.
  - destruct Δ; [| discriminate ]; destruct Ms; [| discriminate ]; cbn; rewrite exp_sub_id; exact HM.
  - destruct (List.exists_last (l := Δ)) as (Δ0 & e & ->); [ intros ->; discriminate |].
    rename Δ0 into Δ.
    rewrite List.length_app in Hn; cbn in Hn.
    unfold all_assumptions in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [(κ0 & A0 & ->) _].
    rewrite List.length_app in Hl; cbn in Hl.
    destruct Ms as [| M0 Ms]; [ cbn in Hl; lia |]; cbn in Hl.
    rewrite ctx_pi_snoc in HM; rewrite <- List.app_assoc in HΔ, HB; cbn [List.app] in HΔ, HB.
    destruct (ctx_decomp_sort_kind (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ (Srt & HS & HA0)].
    (* the parameters inside the outermost, and the outermost's kind *)
    assert (HL' : r = ak_level -> level_sorted_parameters Δ /\ κ0 = ak_level).
    { intros Hr; destruct (level_sorted_app_inv _ _ (HL Hr)) as [HL1 HL2].
      split; [ exact HL1 | exact (HL2 nil κ0 A0 nil eq_refl) ]. }
    assert (Hk : pi_kinds κ0 r)
      by (destruct r; [ constructor | constructor | destruct (HL' eq_refl) as [_ ->]; constructor ]).
    destruct (ctx_pi_type_kind _ _ r Δ _ B _ HΔ (fun _ => Hass) (fun Hr => proj1 (HL' Hr)) HB) as [[j HPi] _].
    assert (HM0 : Θ ⍮ Ξ ⍮ Γ ⊢ M0 : A0)
      by (rewrite <- (exp_sub_id A0); apply (HMs 0); [ reflexivity | rewrite tele_insts_snoc; reflexivity ]).
    assert (Happ : Θ ⍮ Ξ ⍮ Γ ⊢ M $ M0 : (ctx_pi_at r Δ B)[Id,,M0])
      by (eapply wf_app with (Srt := Srt) (i := j); [ exact HA0 | exact HS | exact HPi | exact Hk | exact HM | exact HM0 ]).
    rewrite ctx_pi_sub in Happ.
    pose proof (wf_sub_single _ _ _ _ _ _ _ HA0 HS HM0) as Hs.
    assert (HΔ' : ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ (Id,,M0) ++ Γ) by (eapply ctx_sub_wf; eassumption).
    pose proof (wf_sub_ext _ _ _ _ _ _ Hs HΔ' HΔ) as Hs'.
    cbn [apps_exp sb_of_list].
    replace (B[sb_of_list (Id,,M0) Ms]) with (B[sb_qn (List.length Δ) (Id,,M0)][sb_of_list Id Ms])
      by (replace (List.length Δ) with (List.length Ms) by lia; apply exp_sub_qn_of_list).
    eapply (IH _ _ (tele_sub Δ (Id,,M0))); [ rewrite length_tele_sub; lia | apply all_assumptions_sub; exact Hass | exact HΔ' |
               | intros Hr; exact (level_sorted_parameters_sub _ _ (proj1 (HL' Hr))) | exact Happ
               | rewrite length_tele_sub; lia |].
    + pose proof (sub_preserves_exp _ _ _ _ _ _ _ HB Hs') as HBs; rewrite type_sort_sub in HBs by apply HC; exact HBs.
    + intros k' N T HN HT; apply (HMs (S k')); [ exact HN |].
      rewrite tele_insts_snoc; cbn [List.nth_error].
      rewrite tele_insts_tele_sub in HT; rewrite <- HT; f_equal.
      apply tele_insts_sb_eq; symmetry; apply sb_compose_id_right.
Qed.

(** A member at its arguments: at the kind [r] of its filed [Π]s. *)
Corollary wf_apps_ctx_pi_at : forall Θ Ξ r Δ Γ B i M Ms,
    all_assumptions Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ B : abs_kind_sort r Typeω@i ->
    (r = ak_level -> level_sorted_parameters Δ) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ctx_pi_at r Δ B ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ms : B[sb_of_list Id Ms].
Proof. intros; eapply wf_apps_ctx_pi_n; eauto. Qed.

Corollary wf_apps_ctx_pi : forall Θ Ξ Δ Γ B i M Ms,
    all_assumptions Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ctx_pi Δ B ->
    List.length Ms = List.length Δ ->
    (forall k N T, List.nth_error Ms k = Some N -> List.nth_error (tele_insts Δ Id Ms) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
    Θ ⍮ Ξ ⍮ Γ ⊢ apps M Ms : B[sb_of_list Id Ms].
Proof. intros; eapply (wf_apps_ctx_pi_n ak_relevant); eauto; discriminate. Qed.



(** ** Telescopes Substituted *)

(** An extension read off a context. *)
Lemma ext_of_ctx' : forall Θ Ξ X Γ, ⊢ Θ ⍮ Ξ ⍮ X ++ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ X ≈ X.
Proof.
  induction X as [| [κ A | A M | U | A M U] X IH]; intros * H; cbn in H.
  - constructor; exact H.
  - inversion H; subst.
    match goal with HA : _ ⍮ _ ⍮ X ++ Γ ⊢ A : ?S, HS : sort_kind ?S _ |- _ =>
      eapply wf_ext_eq_ass_same; [ apply IH; eauto using presup_exp_ctx | exact HA | exact HS | exact HA ] end.
  - inversion H; subst.
    match goal with HA : _ ⍮ _ ⍮ X ++ Γ ⊢ A : ?S, HS : type_sort ?S, HM : _ ⍮ _ ⍮ X ++ Γ ⊢ M : A |- _ =>
      eapply wf_ext_eq_def_same;
        [ apply IH; eauto using presup_exp_ctx | exact HA | exact HS | exact HA | exact HM | exact HM ] end.
  - inversion H; subst.
    match goal with HU : _ ⍮ _ ⍮ X ++ Γ ⊢ᵘ U ≈ U |- _ =>
      eapply wf_ext_eq_mod; [ apply IH; eauto using presup_unit_eq_ctx | exact HU | exact HU ] end.
  - inversion H; subst.
    match goal with HA : _ ⍮ _ ⍮ X ++ Γ ⊢ A : Typeω@_, HM : _ ⍮ _ ⍮ X ++ Γ ⊢ M : A,
                    HU : _ ⍮ _ ⍮ X ++ Γ ⊢ᵘ U ≈ U |- _ =>
      eapply wf_ext_eq_dm;
        [ apply IH; eauto using presup_exp_ctx | exact HA | eapply wf_exp_eq_refl; exact HA | exact HM
        | eapply wf_exp_eq_refl; exact HM | exact HA | exact HM | exact HU | exact HU ] end.
Qed.

Lemma ctx_sub_wf_gen : forall Θ Ξ Γ Γ' Ψ σ,
    Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ : Γ -> ⊢ Θ ⍮ Ξ ⍮ Ψ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ tele_sub Ψ σ ++ Γ'.
Proof.
  intros * Hσ HΨ; eapply ext_eq_ctx_left, sub_preserves_ext; [ apply ext_of_ctx'; exact HΨ | exact Hσ ].
Qed.

(** The outermost assumption of a telescope, past the definitions and
    modules outside it, and the substitution removing those. *)
Lemma tele_split_wf : forall Θ Ξ R Γ, ⊢ Θ ⍮ Ξ ⍮ rev R ++ Γ ->
    match tele_split R with
    | inl (B, T, τ) =>
        Θ ⍮ Ξ ⍮ Γ ⊢ᵗ B /\ ⊢ Θ ⍮ Ξ ⍮ T ++ ce_ass (tele_split_kind R) B :: Γ /\
        Θ ⍮ Ξ ⍮ T ++ ce_ass (tele_split_kind R) B :: Γ ⊢ˢ τ : rev R ++ Γ
    | inr τ => Θ ⍮ Ξ ⍮ Γ ⊢ˢ τ : rev R ++ Γ
    end.
Proof.
  induction R as [| [κ0 B0 | B0 N | U | B0 N U] R IH]; intros * HR; cbn [rev tele_split tele_split_kind] in *.
  - exact (wf_sub_id _ _ _ HR).
  - rewrite <- List.app_assoc in *; cbn [List.app] in *.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HR)) as [_ HB].
    split; [ exact HB | split; [ exact HR | exact (wf_sub_id _ _ _ HR) ] ].
  - rewrite <- List.app_assoc in HR; cbn [List.app] in HR.
    pose proof (ctx_app_wf_tail _ _ _ _ HR) as HD.
    destruct (ctx_decomp_def HD) as (HΓ & _ & HN).
    destruct (ctx_decomp_def_sorted HD) as (Srt & HS & HB0).
    pose proof (wf_sub_single_def _ _ _ _ _ _ HB0 HS HN) as Hs.
    specialize (IH _ HR).
    rewrite <- List.app_assoc; cbn [List.app].
    destruct (tele_split R) as [[[B' T'] τ] | τ].
    + destruct IH as (HB' & HT' & Hτ).
      split; [ exact (sub_preserves_type _ _ _ _ _ _ HB' Hs) |].
      assert (HT'' : ⊢ Θ ⍮ Ξ ⍮ tele_sub (T' ++ ce_ass (tele_split_kind R) B' :: nil) (Id,,N) ++ Γ)
        by (eapply ctx_sub_wf_gen; [ exact Hs | rewrite <- List.app_assoc; exact HT' ]).
      rewrite tele_sub_app in HT''; cbn [tele_sub centry_sub length] in HT''; rewrite <- List.app_assoc in HT''; cbn [List.app] in HT''.
      split; [ exact HT'' |].
      eapply wf_sub_compose; [ exact Hτ |].
      pose proof (wf_sub_ext _ _ (T' ++ ce_ass (tele_split_kind R) B' :: nil) _ _ _ Hs) as Hx.
      rewrite tele_sub_app, length_app in Hx; cbn [tele_sub centry_sub length] in Hx.
      rewrite <- !List.app_assoc in Hx; cbn [List.app] in Hx.
      replace (length T' + 1) with (S (length T')) in Hx by lia.
      apply Hx; [ exact HT'' | exact HT' ].
    + eapply wf_sub_compose; [ exact IH | exact Hs ].
  - rewrite <- List.app_assoc in HR; cbn [List.app] in HR.
    pose proof (ctx_app_wf_tail _ _ _ _ HR) as HD.
    destruct (ctx_decomp_mod HD) as (HΓ & HU).
    pose proof (wf_sub_single_mod _ _ _ _ HU) as Hs.
    specialize (IH _ HR).
    rewrite <- List.app_assoc; cbn [List.app].
    destruct (tele_split R) as [[[B' T'] τ] | τ].
    + destruct IH as (HB' & HT' & Hτ).
      split; [ exact (sub_preserves_type _ _ _ _ _ _ HB' Hs) |].
      assert (HT'' : ⊢ Θ ⍮ Ξ ⍮ tele_sub (T' ++ ce_ass (tele_split_kind R) B' :: nil) (Id ,,ₘ me_lit U) ++ Γ)
        by (eapply ctx_sub_wf_gen; [ exact Hs | rewrite <- List.app_assoc; exact HT' ]).
      rewrite tele_sub_app in HT''; cbn [tele_sub centry_sub length] in HT''; rewrite <- List.app_assoc in HT''; cbn [List.app] in HT''.
      split; [ exact HT'' |].
      eapply wf_sub_compose; [ exact Hτ |].
      pose proof (wf_sub_ext _ _ (T' ++ ce_ass (tele_split_kind R) B' :: nil) _ _ _ Hs) as Hx.
      rewrite tele_sub_app, length_app in Hx; cbn [tele_sub centry_sub length] in Hx.
      rewrite <- !List.app_assoc in Hx; cbn [List.app] in Hx.
      replace (length T' + 1) with (S (length T')) in Hx by lia.
      apply Hx; [ exact HT'' | exact HT' ].
    + eapply wf_sub_compose; [ exact IH | exact Hs ].
  - rewrite <- List.app_assoc in HR; cbn [List.app] in HR.
    pose proof (ctx_app_wf_tail _ _ _ _ HR) as HD.
    destruct (ctx_decomp_dm HD) as (HΓ & [i HB0] & HN & HU).
    pose proof (wf_sub_single_dm _ _ _ _ _ _ _ HB0 HN HU) as Hs.
    specialize (IH _ HR).
    rewrite <- List.app_assoc; cbn [List.app].
    destruct (tele_split R) as [[[B' T'] τ] | τ].
    + destruct IH as (HB' & HT' & Hτ).
      split; [ exact (sub_preserves_type _ _ _ _ _ _ HB' Hs) |].
      assert (HT'' : ⊢ Θ ⍮ Ξ ⍮ tele_sub (T' ++ ce_ass (tele_split_kind R) B' :: nil) (Id ,,ᵈ N ‖ me_lit U) ++ Γ)
        by (eapply ctx_sub_wf_gen; [ exact Hs | rewrite <- List.app_assoc; exact HT' ]).
      rewrite tele_sub_app in HT''; cbn [tele_sub centry_sub length] in HT''; rewrite <- List.app_assoc in HT''; cbn [List.app] in HT''.
      split; [ exact HT'' |].
      eapply wf_sub_compose; [ exact Hτ |].
      pose proof (wf_sub_ext _ _ (T' ++ ce_ass (tele_split_kind R) B' :: nil) _ _ _ Hs) as Hx.
      rewrite tele_sub_app, length_app in Hx; cbn [tele_sub centry_sub length] in Hx.
      rewrite <- !List.app_assoc in Hx; cbn [List.app] in Hx.
      replace (length T' + 1) with (S (length T')) in Hx by lia.
      apply Hx; [ exact HT'' | exact HT' ].
    + eapply wf_sub_compose; [ exact IH | exact Hs ].
Qed.

(** ** What Well-Formed Module Expressions Denote Exists *)

Lemma tele_open_split : forall R B T, tele_open R = Some (B, T) -> exists τ, tele_split R = inl (B, T, τ).
Proof.
  induction R as [| [κ0 B0 | B0 N | U | B0 N U] R IH]; intros * H; cbn in H |- *; try discriminate.
  - injection H as <- <-; eauto.
  - destruct (tele_open R) as [[B' T'] |]; [| discriminate ]; injection H as <- <-.
    destruct (IH _ _ eq_refl) as (τ & ->); eauto.
  - destruct (tele_open R) as [[B' T'] |]; [| discriminate ]; injection H as <- <-.
    destruct (IH _ _ eq_refl) as (τ & ->); eauto.
  - destruct (tele_open R) as [[B' T'] |]; [| discriminate ]; injection H as <- <-.
    destruct (IH _ _ eq_refl) as (τ & ->); eauto.
Qed.

(** The parameters inside the outermost one are parameters. *)
Lemma tele_split_ass : forall Θ B Θ'' τ, all_assumptions Θ -> tele_split (rev Θ) = inl (B, Θ'', τ) -> all_assumptions Θ''.
Proof.
  intros * Ha Hs.
  destruct (List.exists_last (l := Θ)) as (Θ0 & e & ->); [ intros ->; discriminate |].
  apply List.Forall_app in Ha as [Ha0 He]; apply List.Forall_cons_iff in He as [(κX & X & ->) _].
  rewrite rev_app_distr in Hs; cbn in Hs; injection Hs as _ <- _; rewrite rev_involutive; exact Ha0.
Qed.

(** A telescope of assumptions split at its outermost parameter is the
    rest followed by it, unmoved. *)
Lemma tele_split_ass_eq : forall Θ B Θ'' τ, all_assumptions Θ -> tele_split (rev Θ) = inl (B, Θ'', τ) ->
    Θ = Θ'' ++ ce_ass (tele_split_kind (rev Θ)) B :: nil /\ τ = Id.
Proof.
  intros * Ha Hs.
  destruct (List.exists_last (l := Θ)) as (Θ0 & e & ->); [ intros ->; discriminate |].
  apply List.Forall_app in Ha as [Ha0 He]; apply List.Forall_cons_iff in He as [(κX & X & ->) _].
  rewrite rev_app_distr in Hs |- *; cbn in Hs |- *; injection Hs as <- <- <-; rewrite rev_involutive; split; reflexivity.
Qed.

(** A module part is a module. *)
Lemma mdesc_mod_is_mod : forall R R', mdesc_mod R = Some R' -> mdesc_is_mod R'.
Proof.
  intros R; induction R as [| | | ? ? ? Rm IH]; intros R' Hm; cbn in Hm; try discriminate;
    try (injection Hm as <-; exact I).
  exact (IH _ Hm).
Qed.

Lemma udenote_is_mod : forall Θ Ξ Γ o U R, udenote Θ Ξ Γ o U R -> mdesc_is_mod R.
Proof.
  intros * Hu; inversion Hu; subst;
    [ match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ =>
        destruct sm, o; cbn in Hb; try discriminate; injection Hb as <-; exact I end |].
  match goal with Hm : mdesc_mod _ = Some ?R1 |- _ =>
    pose proof (mdesc_mod_is_mod _ _ Hm) as HR1; destruct R1; cbn in HR1 |- *; tauto end.
Qed.

Lemma mdesc_is_mod_mod : forall R, mdesc_is_mod R -> mdesc_mod R = Some R.
Proof. intros * H; destruct R; cbn in *; tauto. Qed.

(** "R at N" is defined where an application of a module is typed: a
    module part with a parameter left. *)
Lemma mdesc_at_total : forall R T B T1 N,
    mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) -> exists R', mdesc_at R N = Some R'.
Proof.
  intros R; induction R as [r A om | Δ Φ | Θ0 ? T0 Φ Ns | Θ0 A M Rm IH];
    intros * Ht Hv; cbn in *.
  - discriminate.
  - injection Ht as ->; unfold tele_view in Hv; destruct (tele_open_split _ _ _ Hv) as (τ & ->); eauto.
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; eauto.
  - unfold mdesc_mod_tele in IH; destruct (IH _ _ _ N Ht Hv) as (Rm' & ->).
    destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; eauto.
Qed.

(** An application keeps the module part. *)
Lemma mdesc_at_mod : forall R N R' Rm, mdesc_mod R = Some Rm -> mdesc_at R N = Some R' -> exists Rm', mdesc_mod R' = Some Rm'.
Proof.
  intros R; induction R as [r A om | Δ Φ | Θ0 ? T0 Φ Ns | Θ0 A M Rm0 IH];
    intros * Hm Ha; cbn in Hm, Ha; try discriminate.
  3: destruct (mdesc_at Rm0 N) as [Rm0' |] eqn:Ea; [| discriminate ];
     destruct (IH _ _ _ Hm Ea) as (Rm1 & HRm1);
     destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; cbn; eauto.
  - destruct (tele_split (rev Δ)) as [[[? ?] ?] | ?]; [ injection Ha as <-; eexists; reflexivity | discriminate ].
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; eexists; reflexivity.
Qed.

(** A slot's unit, read one binder further. *)
Lemma udenote_shift : forall Θ Ξ Γ e U R, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> gunit_scoped (length Γ) U ->
    udenote Θ Ξ Γ None U R -> udenote Θ Ξ (e :: Γ) None (gunit_wk U ↑) (mdesc_sub R (ι ↑)).
Proof.
  intros * He HU Hu.
  pose proof (wf_wk_shift _ _ _ _ He) as Hφ.
  pose proof (wf_gctx_closed _ _ _ (ctx_decomp_tail He)) as Hc.
  rewrite <- gunit_sub_of_wk.
  eapply (proj1 (proj2 (mdenote_sub_all _ _ Hc))); [ exact Hu | exact (slots_ok_ctx _ (wf_ctx_scoped _ _ _ (ctx_decomp_tail He))) | left; exact HU |].
  apply wk_mod_compat_sub, (wf_wk_mod_compat _ _ _ _ _ Hφ).
Qed.

Definition slots_denote (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : Prop :=
  forall x U, Γ ∋ #x ≔ₘ U -> exists R, udenote Θ Ξ Γ None U R.

Lemma slots_denote_cons : forall Θ Ξ Γ e, ⊢ Θ ⍮ Ξ ⍮ e :: Γ -> slots_denote Θ Ξ Γ ->
    (forall U, e = ce_mod U -> exists R, udenote Θ Ξ Γ None U R) ->
    (forall A M U, e = ce_dm A M U -> exists R, udenote Θ Ξ Γ None U R) -> slots_denote Θ Ξ (e :: Γ).
Proof.
  intros * He HΓ H0 Hd x U Hl; inversion Hl; subst.
  - destruct (H0 _ eq_refl) as [R HR]; eexists; eapply udenote_shift; [ exact He | | exact HR ].
    destruct (ctx_decomp_mod He) as [_ HU]; destruct (wf_unit_eq_scoped _ _ _ _ _ HU) as (_ & HUs & _); exact HUs.
  - destruct (Hd _ _ _ eq_refl) as [R HR]; eexists; eapply udenote_shift; [ exact He | | exact HR ].
    destruct (ctx_decomp_dm He) as (_ & _ & _ & HU); destruct (wf_unit_eq_scoped _ _ _ _ _ HU) as (_ & HUs & _); exact HUs.
  - match goal with Hl0 : Γ ∋ # ?n ≔ₘ ?U0 |- _ =>
      destruct (HΓ _ _ Hl0) as [R HR]; eexists; eapply udenote_shift; [ exact He | | exact HR ];
      pose proof (ctx_scoped_lookup_mod _ _ _ 0 (wf_ctx_scoped _ _ _ (ctx_decomp_tail He)) Hl0) as Hs;
      rewrite Nat.add_0_r in Hs; exact Hs end.
Qed.


(** ** Applying Abstracted Descriptions *)

Lemma ctx_fn_app : forall T Δ M, ctx_fn (T ++ Δ) M = ctx_fn Δ (ctx_fn T M).
Proof. induction T as [| [] T IH]; intros; cbn; auto. Qed.

(** An abstracted description given its outermost parameter is the
    description substituted, abstracted over the rest. *)
Lemma mdesc_at_up : forall Θ'' κ B R N,
    mdesc_at (mdesc_up (Θ'' ++ ce_ass κ B :: nil) R) N =
    Some (mdesc_up (tele_sub Θ'' (Id,,N)) (mdesc_sub R (sb_qn (length Θ'') (Id,,N)))).
Proof.
  intros Θ'' κ B R; induction R as [r A om | Δ Φ | Θ0 ? T Φ Ns | Θ0 A M Rm IH]; intros N;
    cbn [mdesc_up mdesc_sub].
  - cbn [mdesc_at]; rewrite ctx_pi_app; cbn [ctx_pi pi_view].
    destruct om as [M |]; cbn [option_map].
    + rewrite ctx_fn_app; cbn [ctx_fn fn_view].
      rewrite ctx_pi_sub, ctx_fn_sub; reflexivity.
    + rewrite ctx_pi_sub; reflexivity.
  - cbn [mdesc_at]; rewrite List.app_assoc, rev_app_distr; cbn [rev List.app tele_split].
    rewrite rev_involutive, tele_sub_app, length_app; f_equal; f_equal;
      apply gmod_sub_sb_eq; rewrite sb_compose_id_left, sb_qn_plus; reflexivity.
  - cbn [mdesc_at]; rewrite List.app_assoc, rev_app_distr; cbn [rev List.app tele_split].
    rewrite rev_involutive, tele_sub_app, length_app.
    rewrite (map_sub_sb_eq Ns (Id ⨟ sb_qn (length Θ0 + length Θ'') (Id,,N)) (sb_qn (length Θ0) (sb_qn (length Θ'') (Id,,N))));
      [ reflexivity |].
    rewrite sb_compose_id_left, sb_qn_plus; reflexivity.
  - cbn [mdesc_at]; rewrite IH, List.app_assoc, rev_app_distr; cbn [rev List.app tele_split].
    rewrite rev_involutive, tele_sub_app, length_app.
    assert (Hq : sb_eq (Id ⨟ sb_qn (length Θ0 + length Θ'') (Id,,N)) (sb_qn (length Θ0) (sb_qn (length Θ'') (Id,,N))))
      by (rewrite sb_compose_id_left, sb_qn_plus; reflexivity).
    rewrite (exp_sub_sb_eq A _ _ Hq), (exp_sub_sb_eq M _ _ Hq); reflexivity.
Qed.

(** A term abstracted over a telescope of assumptions is a [λ] at each of
    its parameters, so [mdesc_term_part_at] reads it as [mdesc_at] does. *)
Lemma mdesc_term_part_at_up_term : forall T1 κ C r A om N,
    mdesc_term_part_at (mdesc_up (T1 ++ ce_ass κ C :: nil) (mdesc_term r A om)) N = mdesc_at (mdesc_up (T1 ++ ce_ass κ C :: nil) (mdesc_term r A om)) N.
Proof.
  intros; destruct om as [M |]; cbn [mdesc_up option_map mdesc_term_part_at mdesc_at]; [| reflexivity ].
  rewrite ctx_pi_app, ctx_fn_app; reflexivity.
Qed.

(** So, at no more arguments than the telescope has parameters, [mdesc_term_part_ats]
    reads a term abstracted over a telescope of assumptions as [mdesc_ats]
    does. *)
Lemma mdesc_term_part_ats_up : forall Ns T r A om, all_assumptions T -> length Ns <= length T ->
    mdesc_term_part_ats (mdesc_up T (mdesc_term r A om)) Ns = mdesc_ats (mdesc_up T (mdesc_term r A om)) Ns.
Proof.
  induction Ns as [| N Ns IH]; intros * Ha Hl; [ reflexivity |].
  destruct (List.exists_last (l := T)) as (T1 & e & ->); [ intros ->; cbn in Hl; lia |].
  unfold all_assumptions in Ha; apply List.Forall_app in Ha as [Ha1 He]; apply List.Forall_cons_iff in He as [(κC & C & ->) _].
  cbn [mdesc_term_part_ats mdesc_ats]; rewrite mdesc_term_part_at_up_term, mdesc_at_up; cbn [mdesc_sub].
  apply IH; [ apply all_assumptions_sub; exact Ha1 | rewrite length_tele_sub; rewrite List.length_app in Hl; cbn in Hl; lia ].
Qed.

(** ** A Literal Given its Outermost Parameter *)

Lemma mdesc_up_nil : forall R, mdesc_up nil R = R.
Proof.
  induction R as [r A [M |] | Δ Φ | Θ p T Φ Ns | Θ A M Rm IH]; cbn; rewrite ?List.app_nil_r;
    [ reflexivity .. | rewrite IH; reflexivity ].
Qed.

Lemma mdesc_up_cat : forall A B R, mdesc_up (A ++ B) R = mdesc_up B (mdesc_up A R).
Proof.
  intros A B R; induction R as [r A0 om | Δ Φ | Θ p T Φ Ns | Θ A0 M Rm IH]; cbn;
    rewrite ?List.app_assoc; try reflexivity.
  - rewrite ctx_pi_app; f_equal; destruct om; cbn; [ rewrite ctx_fn_app |]; reflexivity.
  - rewrite IH; reflexivity.
Qed.

(** The telescope of a module abstracted further takes the new parameters
    outermost. *)
Lemma mdesc_tele_up : forall Θ' Rm T, mdesc_tele Rm = Some T -> mdesc_tele (mdesc_up Θ' Rm) = Some (T ++ Θ').
Proof.
  intros * Ht; destruct Rm; cbn in Ht |- *; try discriminate.
  - injection Ht as <-; reflexivity.
  - destruct (Nat.leb _ _); [ injection Ht as <-; rewrite app_assoc; reflexivity | discriminate ].
Qed.

(** The module part of an abstracted description is the module part,
    abstracted. *)
Lemma mdesc_mod_up : forall Θ' R, mdesc_mod (mdesc_up Θ' R) = option_map (mdesc_up Θ') (mdesc_mod R).
Proof.
  intros Θ' R; induction R as [| | | Θ0 A M Rm IH]; cbn; try reflexivity.
  exact IH.
Qed.

(** The telescope of the module part of a description abstracted over
    [Θd] ends with [Θd], outermost. *)
Lemma mdesc_mod_tele_up_inv : forall Θd R T, mdesc_mod_tele (mdesc_up Θd R) = Some T -> exists T0, T = T0 ++ Θd.
Proof.
  intros * Ht; unfold mdesc_mod_tele in Ht; rewrite mdesc_mod_up in Ht.
  destruct (mdesc_mod R) as [Rm |] eqn:Hm; cbn [option_map] in Ht; [| discriminate ].
  pose proof (mdesc_mod_is_mod _ _ Hm) as Hmm.
  destruct Rm; cbn in Hmm, Ht; try contradiction; try discriminate.
  - injection Ht as <-; eauto.
  - destruct (Nat.leb _ _); [ injection Ht as <-; rewrite app_assoc; eauto | discriminate ].
Qed.

(** A unit of the context after [Δ], abstracted over [Δ]. *)
Lemma udenote_abs : forall Θ Ξ Γ Δ U R, udenote Θ Ξ (Δ ++ Γ) None U R -> udenote Θ Ξ Γ None (gunit_abs Δ U) (mdesc_up Δ R).
Proof.
  intros * Hu; inversion Hu; subst; cbn [gunit_abs].
  - match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => destruct sm; cbn in Hb; [ injection Hb as <- | discriminate ] end.
    eapply udenote_body; [ rewrite <- app_assoc; eassumption | reflexivity ].
  - rewrite <- mdesc_up_cat; eapply udenote_alias; [ rewrite <- app_assoc; eassumption | eassumption ].
Qed.

Lemma sub_mod_compat_single : forall Γ κ X N, sub_mod_compat (Id,,N) Γ (ce_ass κ X :: Γ).
Proof.
  intros * x U Hl; inversion Hl; subst; right; eexists; split; [ reflexivity |].
  rewrite gunit_sub_shift_extend, gunit_sub_id; assumption.
Qed.

(** A unit read with its outermost parameter in the context. *)
Lemma udenote_last : forall Θ Ξ Γ Δ κ X D R,
    udenote Θ Ξ Γ None (gu_mk (Δ ++ ce_ass κ X :: nil) D) R ->
    exists R1, udenote Θ Ξ (ce_ass κ X :: Γ) None (gu_mk Δ D) R1 /\ R = mdesc_up (ce_ass κ X :: nil) R1.
Proof.
  intros * Hu; inversion Hu; subst.
  - match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => destruct sm; cbn in Hb; [| discriminate ]; injection Hb as <- end.
    exists (mdesc_open Δ Φ Φx); split; [ eapply udenote_body; [ rewrite <- List.app_assoc in *; eassumption | reflexivity ] | reflexivity ].
  - exists (mdesc_up Δ R'); split; [ eapply udenote_alias; [ rewrite <- List.app_assoc in *; eassumption | eassumption ] |].
    rewrite mdesc_up_cat; reflexivity.
Qed.

(** [β]: what the literal given an argument denotes is what the instantiated
    literal does. *)
Lemma udenote_beta : forall Θ Ξ, gctx_closed Θ Ξ -> forall Γ Δ κ X D N R,
    ctx_scoped 0 Γ -> gunit_scoped (length Γ) (gu_mk (Δ ++ ce_ass κ X :: nil) D) ->
    udenote Θ Ξ Γ None (gu_mk (Δ ++ ce_ass κ X :: nil) D) R ->
    exists R', mdesc_at R N = Some R' /\ udenote Θ Ξ Γ None (gu_mk Δ D)[Id,,N]ᵘ R'.
Proof.
  intros Θ Ξ Hc * HΓ HU Hu.
  destruct (udenote_last _ _ _ _ _ _ _ _ Hu) as (R1 & Hu1 & ->).
  rewrite gunit_scoped_mk, ctx_scoped_app, List.length_app in HU; destruct HU as [[HΔ HX] HD]; cbn in HX, HΔ.
  exists (mdesc_sub R1 (Id,,N)); split.
  - change (ce_ass κ X :: nil) with (nil ++ ce_ass κ X :: nil); rewrite mdesc_at_up; cbn [tele_sub sb_qn length].
    rewrite mdesc_up_nil; reflexivity.
  - eapply (proj1 (proj2 (mdenote_sub_all _ _ Hc))); [ exact Hu1 | apply (slots_ok_ctx (ce_ass κ X :: Γ)) | left | apply sub_mod_compat_single ].
    + cbn [ctx_scoped]; split; [ rewrite Nat.add_0_r; apply HX | exact HΓ ].
    + rewrite gunit_scoped_mk; cbn [length]; split; [ exact HΔ |].
      replace (length Δ + S (length Γ)) with (length Δ + 1 + length Γ) by lia; exact HD.
Qed.

(** Both sides of [β] denote one module. *)
Lemma mdenote_beta : forall Θ Ξ Γ Δ κ X D N,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass κ X :: nil) D ≈ gu_mk (Δ ++ ce_ass κ X :: nil) D ->
    forall R, udenote Θ Ξ Γ None (gu_mk (Δ ++ ce_ass κ X :: nil) D) R ->
    exists R', mdenote Θ Ξ Γ (me_app (me_lit (gu_mk (Δ ++ ce_ass κ X :: nil) D)) N) R' /\
      mdenote Θ Ξ Γ (me_lit (gu_mk Δ D)[Id,,N]ᵘ) R' /\ mdesc_mod R' = Some R'.
Proof.
  intros * HU R Hu.
  destruct (wf_unit_eq_scoped _ _ _ _ _ HU) as (HΓ & HUs & _).
  pose proof (wf_gctx_closed _ _ _ (presup_unit_eq_ctx HU)) as Hc.
  destruct (udenote_beta _ _ Hc _ _ _ _ _ N _ HΓ HUs Hu) as (R' & Ha & Hu').
  exists R'; split; [ eapply mdenote_app; [ apply mdenote_lit; exact Hu | exact Ha ] |].
  split; [ apply mdenote_lit; exact Hu' | apply mdesc_is_mod_mod; eapply udenote_is_mod; exact Hu' ].
Qed.


(** ** Typed Descriptions *)

Lemma tele_sub_closed : forall Δ σ, ctx_scoped 0 Δ -> tele_sub Δ σ = Δ.
Proof.
  intros * HΔ; rewrite (tele_scoped_sub_agree _ _ σ Id HΔ) by lia; apply tele_sub_id.
Qed.


Lemma gens_append_noopen : forall gs Φ k, gm_noopen Φ -> gm_noopen (gens_append Φ k gs).
Proof.
  induction gs as [| g gs IH]; intros * Hn; cbn; [ exact Hn |].
  destruct (generated_item_entry g); apply IH; exact Hn.
Qed.

Lemma body_xp_result_noopen : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> gm_noopen Φx.
Proof. induction 1; cbn; auto using gens_append_noopen. Qed.

(** ** Closed Telescopes and Their Outermost Parameters *)

Lemma wf_sub_to_nil : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id : ⋅.
Proof.
  intros * HΓ; econstructor; [ exact HΓ | constructor; eapply ctx_wf_gctx; exact HΓ | | |];
    intros * Hl; inversion Hl.
Qed.

(** A closed telescope well formed over nothing is so over any context. *)
Lemma closed_tele_wf : forall Θ Ξ T Γ, ctx_scoped 0 T -> ⊢ Θ ⍮ Ξ ⍮ T -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ ⍮ Ξ ⍮ T ++ Γ.
Proof.
  intros * Hs HT HΓ.
  rewrite <- (tele_sub_closed T Id Hs).
  eapply ctx_sub_wf_gen; [ exact (wf_sub_to_nil _ _ _ HΓ) | rewrite List.app_nil_r; exact HT ].
Qed.

Lemma tele_view_ass : forall T B T', all_assumptions T -> tele_view T = Some (B, T') ->
    exists κ, T = T' ++ ce_ass κ B :: nil.
Proof.
  intros * Ha Hv; unfold tele_view in Hv.
  destruct (rev T) as [| e R] eqn:Er; [ discriminate |].
  assert (Ha' : all_assumptions (rev T)) by (apply List.Forall_rev; exact Ha).
  rewrite Er in Ha'; inversion Ha' as [| ? ? (κ & A & HA) _]; subst e.
  cbn in Hv; injection Hv as <- <-; exists κ.
  rewrite <- (rev_involutive T), Er; reflexivity.
Qed.

(** The outermost assumption of a telescope extended inside by more. *)
Lemma tele_open_app_inl : forall R1 R2 B T τ, tele_split R1 = inl (B, T, τ) ->
    exists T', tele_open (R1 ++ R2) = Some (B, T').
Proof.
  induction R1 as [| [κ0 B0 | B0 N | U | B0 N U] R1 IH]; intros * Hs; cbn in Hs |- *; try discriminate.
  1: injection Hs as <- <- <-; eauto.
  all: destruct (tele_split R1) as [[[B' T'] τ'] |] eqn:E; [| discriminate ]; injection Hs as <- <- <-;
       destruct (IH R2 _ _ _ eq_refl) as (T'' & ->); eauto.
Qed.

Lemma tele_open_app_inr : forall R1 R2 τ B T, tele_split R1 = inr τ -> tele_open (R1 ++ R2) = Some (B, T) ->
    exists B0 T0, tele_open R2 = Some (B0, T0) /\ B = B0[τ].
Proof.
  induction R1 as [| [κ0 B0 | B0 N | U | B0 N U] R1 IH]; intros * Hs Ho; cbn in Hs, Ho |- *; try discriminate.
  1: injection Hs as <-; exists B, T; split; [ exact Ho | symmetry; apply exp_sub_id ].
  all: destruct (tele_split R1) as [[[B' T'] τ'] | τ'] eqn:E; [ discriminate |]; injection Hs as <-;
       destruct (tele_open (R1 ++ R2)) as [[B1 T1] |] eqn:Ho1; [| discriminate ]; injection Ho as <- _;
       destruct (IH _ _ _ _ eq_refl Ho1) as (B2 & T2 & HR2 & ->); exists B2, T2; split; [ exact HR2 | apply exp_sub_sub ].
Qed.

(** A closed module or an inductive type with no outside parameter records
    its arguments. *)
Lemma mdesc_ats_closed_nil : forall Ns p T Φ Ms, mdesc_ats (mdesc_closed nil p T Φ Ms) Ns = Some (mdesc_closed nil p T Φ (Ms ++ Ns)).
Proof.
  induction Ns as [| N Ns IH]; intros; cbn; [ rewrite List.app_nil_r; reflexivity |].
  rewrite (List.map_ext _ (fun M => M) exp_sub_id), List.map_id, IH, <- List.app_assoc; reflexivity.
Qed.

(** A definition with a module part and no outside parameter, given
    arguments as a module, is its module part given them. *)
Lemma mdesc_ats_dm_nil : forall Ns A M Rm, Ns <> nil -> mdesc_ats (mdesc_dm nil A M Rm) Ns = mdesc_ats Rm Ns.
Proof.
  intros [| N Ns] * Hn; [ contradiction |]; cbn [mdesc_ats mdesc_at].
  destruct (mdesc_at Rm N); reflexivity.
Qed.

(** ** What a Filed Module Denotes *)

Lemma mdenote_apps : forall Θ Ξ Γ Ns H R R', mdenote Θ Ξ Γ H R -> mdesc_ats R Ns = Some R' ->
    mdenote Θ Ξ Γ (me_apps H Ns) R'.
Proof.
  induction Ns as [| N Ns IH]; intros * Hm Ha; cbn in Ha |- *; [ injection Ha as <-; exact Hm |].
  destruct (mdesc_at R N) as [R1 |] eqn:E; [| discriminate ].
  eapply IH; [ eapply mdenote_app; eassumption | exact Ha ].
Qed.

(** A stored module, a body or the module of a member of a group of
    inductive types or of a record type, is denoted by its path: its module
    part is the stored body at the path. *)
Lemma qname_mod_denote : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ Γ, loc Θ Ξ p T Φ ->
    exists R, mdenote Θ Ξ Γ (qname_mod p) R /\
      (R = mdesc_closed nil p T Φ nil \/ exists A M, R = mdesc_dm nil A M (mdesc_closed nil p T Φ nil)).
Proof.
  intros Θ Ξ Hg * Hl.
  destruct (mdenote_of_loc_any _ _ Hg _ _ _ _ Γ (mod_qname_qname_mod p) Hl) as (R & Hm & _ & HR).
  exists R; split; [ exact Hm |]; unfold loc_desc in HR.
  destruct (ind_mlookup Θ Ξ p) as [[[pq k] D] |] eqn:Hi.
  - destruct HR as (Mk & _ & ->); right; do 2 eexists; reflexivity.
  - destruct (record_lookup Θ Ξ p) as [Rr |] eqn:Hr; [| left; exact HR ].
    subst R; right; do 2 eexists; reflexivity.
Qed.

Lemma filed_denote : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ Γ Ns, gc_loc Θ Ξ p = Some (T, Φ) ->
    exists R, mdenote Θ Ξ Γ (me_apps (qname_mod p) Ns) R /\ mdesc_mod R = Some (mdesc_closed nil p T Φ Ns).
Proof.
  intros Θ Ξ Hg * Hgl.
  assert (Hl : loc Θ Ξ p T Φ) by (unfold gc_loc in Hgl; destruct (gc_frame Ξ p) eqn:E;
    [ injection Hgl as ->; left; exact E | right; exact Hgl ]).
  destruct (qname_mod_denote _ _ Hg _ _ _ Γ Hl) as (R & Hm & [-> | (A & M & ->)]).
  - exists (mdesc_closed nil p T Φ (nil ++ Ns)); split; [ eapply mdenote_apps; [ exact Hm | apply mdesc_ats_closed_nil ] | reflexivity ].
  - destruct Ns as [| N Ns].
    + exists (mdesc_dm nil A M (mdesc_closed nil p T Φ nil)); split; [ exact Hm | reflexivity ].
    + exists (mdesc_closed nil p T Φ (nil ++ N :: Ns)); split; [| reflexivity ].
      eapply mdenote_apps; [ exact Hm |]; rewrite mdesc_ats_dm_nil by discriminate; apply mdesc_ats_closed_nil.
Qed.

(** ** Descriptions Read Where They Are Stored

    What a module expression denotes is read where it is: a local body is
    expanded, with no open left, and a closed module is the body stored at
    its path ([mdesc_canonical]).  So the unit a module part stands for
    ([mdesc_unit]) denotes that module part again. *)

Fixpoint mdesc_canonical (Θ : gdeps) (Ξ : gstack) (R : mdesc) : Prop :=
  match R with
  | mdesc_open _ _ Φx => gm_noopen Φx
  | mdesc_closed _ p T Φ _ => loc Θ Ξ p T Φ
  | mdesc_dm _ _ _ Rm => mdesc_canonical Θ Ξ Rm
  | _ => True
  end.

Lemma mdesc_canonical_mod : forall Θ Ξ R Rm, mdesc_canonical Θ Ξ R -> mdesc_mod R = Some Rm -> mdesc_canonical Θ Ξ Rm.
Proof.
  intros Θ Ξ R; induction R as [r A om | Δ Φ | Θ0 p T Φ Ns | Θ0 A M Rm0 IH];
    intros Rm Hc Hm; try (cbn in Hm |- *; discriminate);
    try (cbn in Hm |- *; injection Hm as <-; exact Hc).
  exact (IH _ Hc Hm).
Qed.

Lemma mdesc_canonical_at : forall Θ Ξ R N R', mdesc_canonical Θ Ξ R -> mdesc_at R N = Some R' -> mdesc_canonical Θ Ξ R'.
Proof.
  intros Θ Ξ R; induction R as [r A om | Δ Φ | Θ0 p T Φ Ns | Θ0 A M Rm IH];
    intros N R' Hc Ha; cbn in Ha, Hc.
  - destruct (pi_view A) as [[? ?] |]; [| discriminate ].
    destruct om as [M |]; [ destruct (fn_view M); [| discriminate ] |]; injection Ha as <-; exact I.
  - destruct (tele_split (rev Δ)) as [[[? ?] ?] | ?]; [ injection Ha as <-; cbn; apply gm_noopen_sub; exact Hc | discriminate ].
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; exact Hc.
  - destruct (mdesc_at Rm N) as [Rm' |] eqn:Ea; [| discriminate ].
    destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; exact (IH _ _ Hc Ea).
Qed.

Lemma mdesc_canonical_ats : forall Θ Ξ Ns R R', mdesc_canonical Θ Ξ R -> mdesc_ats R Ns = Some R' -> mdesc_canonical Θ Ξ R'.
Proof.
  intros Θ Ξ; induction Ns as [| N Ns IH]; intros * Hc Ha; cbn in Ha; [ injection Ha as <-; exact Hc |].
  destruct (mdesc_at R N) as [R1 |] eqn:E; [| discriminate ].
  exact (IH _ _ (mdesc_canonical_at _ _ _ _ _ Hc E) Ha).
Qed.

Lemma mdesc_canonical_up : forall Θ Ξ Θ' R, mdesc_canonical Θ Ξ R -> mdesc_canonical Θ Ξ (mdesc_up Θ' R).
Proof. intros Θ Ξ Θ' R; induction R; intros Hc; cbn in *; auto. Qed.

Lemma mdesc_canonical_sub : forall Θ Ξ R σ, mdesc_canonical Θ Ξ R -> mdesc_canonical Θ Ξ (mdesc_sub R σ).
Proof. intros Θ Ξ R σ; induction R; intros Hc; cbn in *; auto; apply gm_noopen_sub; exact Hc. Qed.

Lemma mdesc_canonical_read : forall Θ Ξ rd R R', mdesc_canonical Θ Ξ R -> mdesc_read rd R = Some R' -> mdesc_canonical Θ Ξ R'.
Proof.
  intros Θ Ξ [Δ Φ' | Θ' Ns M] * Hc Hr; cbn in Hr.
  - destruct (gm_fill Φ') as [σ |]; cbn in Hr; [ injection Hr as <- | discriminate ].
    apply mdesc_canonical_up, mdesc_canonical_sub; exact Hc.
  - destruct (mdesc_ats_read R Ns) as [R1 |] eqn:E; cbn in Hr; [ injection Hr as <- | discriminate ].
    assert (H1 : mdesc_canonical Θ Ξ R1).
    { destruct (mdesc_ats_read_inv _ _ _ E) as [E' | (A & M0 & Rm & ? & B & M' & Rm' & -> & -> & _ & E')];
        [ exact (mdesc_canonical_ats _ _ _ _ _ Hc E') | exact (mdesc_canonical_ats _ _ _ Rm _ Hc E') ]. }
    apply mdesc_canonical_up; apply mdesc_named_cases; destruct R1 as [? ? [] | | |]; exact H1.
Qed.

Lemma body_xp_noopen_id : forall Θ Ξ Γ Φ Φx, gm_noopen Φ -> body_xp Θ Ξ Γ Φ Φx -> Φx = Φ.
Proof.
  intros * HΦ Hx; revert HΦ; induction Hx; intros HΦ; cbn in HΦ; [ reflexivity | | contradiction ].
  rewrite IHHx by exact HΦ; reflexivity.
Qed.

Theorem mdenote_canon_all : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ ->
    (forall Γ H R, mdenote Θ Ξ Γ H R -> mdesc_canonical Θ Ξ R) /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R ->
       (forall qq Δ Φ, o = Some qq -> U = gu_mk Δ (md_body sm_closed Φ) -> loc Θ Ξ qq Δ Φ) -> mdesc_canonical Θ Ξ R) /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R ->
       (forall qq pv Δ Φ, o = Some qq -> E = ge_mod pv (gu_mk Δ (md_body sm_closed Φ)) -> loc Θ Ξ qq Δ Φ) -> mdesc_canonical Θ Ξ R) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> True) /\
    (forall Γ H its gs, items_gen Θ Ξ Γ H its gs -> True).
Proof.
  intros Θ Ξ Hg; apply mdenote_all_ind; intros; try exact I.
  (* a type former: its module part, stored where [gc_loc] finds it *)
  all: try match goal with Hl : gc_loc _ _ _ = Some _ |- mdesc_canonical _ _ (_ _ _ _ _ (mdesc_closed _ _ _ _ _)) =>
         exact (gc_loc_loc _ _ _ _ _ Hl) end.
  all: try match goal with Hl : gc_loc _ _ _ = Some _ |- mdesc_canonical _ _ (_ _ _ (mdesc_closed _ _ _ _ _)) =>
         exact (gc_loc_loc _ _ _ _ _ Hl) end.
  - (* a loaded unit or an open frame *)
    match goal with Hu : gc_unit _ _ _ = Some _ |- _ => destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq & Hl) end.
    match goal with Hq0 : mod_qname _ = Some _ |- _ => rewrite Hq0 in Hq; injection Hq as <- end; exact Hl.
  - (* a slot *) match goal with IH : (forall qq Δ Φ, None = Some qq -> _) -> _ |- _ => apply IH; discriminate end.
  - (* a literal *) match goal with IH : (forall qq Δ Φ, None = Some qq -> _) -> _ |- _ => apply IH; discriminate end.
  - (* an application *) eapply mdesc_canonical_at; eassumption.
  - (* a selection *)
    rename H0 into IH0, e into Hmod, e0 into He, H1 into IHe, e2 into Hr.
    pose proof (mdesc_canonical_mod _ _ _ _ IH0 Hmod) as Hc.
    eapply mdesc_canonical_read; [| exact Hr ].
    apply IHe; intros qq pv Δ Φ1 Ho HE; subst E.
    destruct R0m as [r A om | Δ0 Φ0 | Θ0 p T Φ Ns | ? ? ? ?]; cbn in He, Ho; try discriminate.
    injection Ho as <-.
    destruct (gm_prefix_upto Φ y) as [[| Φ' x E0 | Φ' H0 its] |] eqn:Hp; try discriminate; injection He as _ HE _.
    destruct (gm_prefix_entry _ _ _ Hp) as (Φ0 & E1 & [= <- <- <-] & Hen).
    destruct E0 as [| pv0 [Δ1 [[|] Φ2 | E2]] | | | ]; cbn in HE; try discriminate.
    injection HE as <- <- <-.
    destruct (loc_child_mod _ _ Hg _ _ _ Hc _ _ _ _ _ Hen) as [Hb _]; right; exact Hb.
  - (* a body *)
    match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => rename Hb into Hds end.
    match goal with Hx : body_xp _ _ _ _ _ |- _ => rename Hx into Hbx end.
    match goal with Hs : forall qq Δ Φ, _ -> _ -> loc _ _ _ _ _ |- _ => rename Hs into Hst end.
    destruct sm; cbn in Hds.
    + injection Hds as <-; exact (body_xp_result_noopen _ _ _ _ _ Hbx).
    + destruct o as [qq |]; cbn in Hds; [ injection Hds as <- | discriminate ].
      pose proof (Hst qq Δ Φ eq_refl eq_refl) as Hl.
      pose proof (body_closed_noopen _ _ (proj2 (loc_closed _ _ Hg _ _ _ Hl))) as Hn.
      rewrite (body_xp_noopen_id _ _ _ _ _ Hn Hbx); exact Hl.
  - (* an alias *)
    apply mdesc_canonical_up; eapply mdesc_canonical_mod; eassumption.
  - (* a module *)
    match goal with IH : (forall qq Δ Φ, _ -> _ -> _) -> mdesc_canonical _ _ _, Hs : forall qq pv Δ Φ, _ -> _ -> _ |- _ =>
      apply IH; intros qq Δ Φ Ho HU; subst; exact (Hs qq _ Δ Φ eq_refl eq_refl) end.
  - (* a definition with a module part: its module part, an alias *)
    match goal with IH : (forall qq Δ Φ, _ -> _ -> _) -> mdesc_canonical _ _ _ |- _ =>
      apply IH; intros qq Δ0 Φ0 _ HU; discriminate HU end.
Qed.

Lemma mdenote_canon : forall Θ Ξ Γ H R, ⊢ᵍ Θ ⍮ Ξ -> mdenote Θ Ξ Γ H R -> mdesc_canonical Θ Ξ R.
Proof. intros * Hg Hm; exact (proj1 (mdenote_canon_all _ _ Hg) _ _ _ Hm). Qed.

(** ** Local Bodies Read Where They Are

    The expansion an open description carries is the expansion of its
    written body where the description is read ([mdesc_xp]): so the literal
    of the written body denotes the description again ([mdesc_unit_denote]). *)

Fixpoint mdesc_xp (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (R : mdesc) : Prop :=
  match R with
  | mdesc_open Δ Φ Φx => body_xp Θ Ξ (Δ ++ Γ) Φ Φx
  | mdesc_dm _ _ _ Rm => mdesc_xp Θ Ξ Γ Rm
  | _ => True
  end.

Lemma mdesc_xp_sub : forall Θ Ξ, gctx_closed Θ Ξ -> forall Γ R m Γ' σ,
    slots_ok m Γ -> mdesc_scoped m R -> mdesc_xp Θ Ξ Γ R -> sub_mod_compat σ Γ' Γ -> mdesc_xp Θ Ξ Γ' (mdesc_sub R σ).
Proof.
  intros Θ Ξ Hc Γ R; induction R as [| Δ Φ Φx | | ? ? ? Rm IH]; intros * HS HR Hx Hσ; cbn in *; try exact I.
  - destruct HR as [HR _]; rewrite gunit_scoped_mk in HR; destruct HR as [HΔ [_ HΦ]].
    eapply (proj1 (proj2 (proj2 (proj2 (mdenote_sub_all _ _ Hc))))); [ exact Hx | apply slots_ok_app; eassumption | exact HΦ |].
    apply sub_mod_compat_ext; exact Hσ.
  - exact (IH _ _ _ HS (proj2 (proj2 HR)) Hx Hσ).
Qed.

Lemma mdesc_xp_at : forall Θ Ξ, gctx_closed Θ Ξ -> forall Γ R N R' m,
    slots_ok m Γ -> mdesc_scoped m R -> mdesc_xp Θ Ξ Γ R -> mdesc_at R N = Some R' -> mdesc_xp Θ Ξ Γ R'.
Proof.
  intros Θ Ξ Hc Γ R; induction R as [r A om | Δ Φ Φx | Θ0 p T Φ Ns | Θ0 A M Rm IH];
    intros N R' m HS HR Hx Ha; cbn in Ha.
  4: { destruct (mdesc_at Rm N) as [Rm' |] eqn:Ea; [| discriminate ].
       destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-;
         exact (IH _ _ _ HS (proj2 (proj2 HR)) Hx Ea). }
  - destruct (pi_view A) as [[? ?] |]; [| discriminate ].
    destruct om as [M |]; [ destruct (fn_view M) |]; try discriminate; injection Ha as <-; exact I.
  - destruct (tele_split (rev Δ)) as [[[B Δ'] τ] |] eqn:E; [| discriminate ]; injection Ha as <-; cbn [mdesc_xp] in *.
    destruct HR as [HR _]; rewrite gunit_scoped_mk in HR; destruct HR as [HΔ [_ HΦ]].
    pose proof (tele_split_compat (rev Δ) Γ) as Hτ; rewrite E, rev_involutive in Hτ.
    eapply (proj1 (proj2 (proj2 (proj2 (mdenote_sub_all _ _ Hc))))); [ exact Hx | apply slots_ok_app; eassumption | exact HΦ |].
    eapply sub_mod_compat_compose; [ exact Hτ |].
    apply sub_mod_compat_ext, sub_mod_compat_single_term; intros; discriminate.
  - destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; exact I.
Qed.

Lemma mdesc_xp_ats : forall Θ Ξ, gctx_closed Θ Ξ -> forall Γ Ns R R' m,
    slots_ok m Γ -> mdesc_scoped m R -> List.Forall (exp_scoped m) Ns -> mdesc_xp Θ Ξ Γ R -> mdesc_ats R Ns = Some R' -> mdesc_xp Θ Ξ Γ R'.
Proof.
  intros Θ Ξ Hc Γ; induction Ns as [| N Ns IH]; intros * HS HR HNs Hx Ha; cbn in Ha; [ injection Ha as <-; exact Hx |].
  inversion HNs; subst.
  destruct (mdesc_at R N) as [R1 |] eqn:E; [| discriminate ].
  eapply IH; [ exact HS | eapply mdesc_at_scoped; eassumption | assumption | eapply mdesc_xp_at; eassumption | exact Ha ].
Qed.

Lemma mdesc_xp_up : forall Θ Ξ Γ Θ' R, mdesc_xp Θ Ξ (Θ' ++ Γ) R -> mdesc_xp Θ Ξ Γ (mdesc_up Θ' R).
Proof.
  intros Θ Ξ Γ Θ' R; induction R; intros Hx; cbn in *; try exact I; [ rewrite <- List.app_assoc; exact Hx | auto ].
Qed.

Lemma mdesc_xp_mod : forall Θ Ξ Γ R Rm, mdesc_xp Θ Ξ Γ R -> mdesc_mod R = Some Rm -> mdesc_xp Θ Ξ Γ Rm.
Proof.
  intros Θ Ξ Γ R; induction R as [| | | ? ? ? R0 IH]; intros Rm Hx Hm;
    try (cbn in Hm; discriminate); try (cbn in Hm; injection Hm as <-; exact Hx).
  exact (IH _ Hx Hm).
Qed.

Lemma mdesc_xp_self : forall Θ Ξ Γ M R, mdesc_xp Θ Ξ Γ R -> mdesc_xp Θ Ξ Γ (mdesc_self M R).
Proof. intros * Hx; destruct R as [? ? [] | | |]; exact Hx. Qed.

Lemma mdesc_xp_named : forall Θ Ξ Γ Θ' Ns M R, mdesc_xp Θ Ξ Γ R -> mdesc_xp Θ Ξ Γ (mdesc_named Θ' Ns M R).
Proof. intros * Hx; apply mdesc_named_cases; [ exact Hx | apply mdesc_xp_self; exact Hx ]. Qed.

Theorem mdenote_xp_all : forall Θ Ξ, gctx_closed Θ Ξ ->
    (forall Γ H R, mdenote Θ Ξ Γ H R -> forall m, slots_ok m Γ -> modexp_scoped m H -> mdesc_xp Θ Ξ Γ R) /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R -> forall m, slots_ok m Γ ->
       (gunit_scoped m U \/ exists T Φ, U = gu_body T Φ /\ unit_closed T Φ) -> mdesc_xp Θ Ξ Γ R) /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R -> forall m, slots_ok m Γ -> entry_sc m E -> mdesc_xp Θ Ξ Γ R) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> True) /\
    (forall Γ H its gs, items_gen Θ Ξ Γ H its gs -> True).
Proof.
  intros Θ Ξ Hc; pose proof (mdenote_scoped_all _ _ Hc) as (Hsm & Hsu & Hse & _).
  apply mdenote_all_ind; intros; try exact I.
  - (* a slot *)
    match goal with IH : forall m, slots_ok m ?Γ -> _ -> _, HΓ : slots_ok ?m ?Γ, Hl : ?Γ ∋ # ?x ≔ₘ _,
                    Hx : modexp_scoped _ (me_var _) |- _ =>
      cbn in Hx; apply (IH m HΓ); left; exact (HΓ _ _ Hx Hl) end.
  - (* a literal *)
    match goal with IH : forall m, slots_ok m ?Γ -> _ -> _ |- _ => eapply IH; [ eassumption | left; cbn in *; assumption ] end.
  - (* an application *)
    rename H0 into IH, e into Ha, H1 into HS, H2 into HH; cbn in HH; destruct HH as [HH HN].
    eapply mdesc_xp_at; [ exact Hc | exact HS | eapply Hsm; eassumption | eapply IH; eassumption | exact Ha ].
  - (* a selection *)
    rename H0 into IH0, e into Hmod, e0 into He, H1 into IHe; rename H2 into HS, H3 into HH; cbn in HH.
    match goal with Hr0 : mdesc_read _ _ = Some _ |- _ => rename Hr0 into Hr end.
    match goal with Hm0 : mdenote _ _ _ H R0 |- _ => rename Hm0 into Hd0 end.
    match goal with Hed : edenote _ _ _ _ E R |- _ => rename Hed into Hde end.
    pose proof (mdesc_mod_scoped _ _ _ (Hsm _ _ _ Hd0 _ HS HH) Hmod) as HR0m.
    destruct (mdesc_entry_scoped _ _ _ _ _ _ HR0m He) as (HΓy & HE & Hrd).
    assert (HSy : slots_ok (length Γy + m0) (Γy ++ Γ)) by (apply slots_ok_app; assumption).
    pose proof (IHe _ HSy HE) as Hx.
    pose proof (Hse _ _ _ _ Hde _ HSy HE) as HRs.
    destruct rd as [Δ Φ' | Θ0 Ns M]; cbn in Hr.
    + destruct Hrd as (-> & HΔ & HΦ').
      destruct (gm_fill Φ') as [σ |] eqn:Hf; cbn in Hr; [| discriminate ]; injection Hr as <-.
      apply mdesc_xp_up.
      eapply mdesc_xp_sub; [ exact Hc | exact HSy | exact HRs | exact Hx |].
      rewrite <- List.app_assoc; apply sub_mod_compat_fill; exact Hf.
    + destruct Hrd as (-> & HΘ0 & HNs & HM); cbn [List.app length] in *.
      destruct (mdesc_ats_read R Ns) as [R1 |] eqn:Ea; cbn in Hr; [| discriminate ]; injection Hr as <-.
      apply mdesc_xp_up, mdesc_xp_named.
      (* a closed entry: closed, read under the outside parameters *)
      destruct R0m as [| | Θa pa Ta Φa Nsa |]; cbn in He; try discriminate;
        [ destruct (gm_prefix_upto _ y) as [[| ? ? [[|] ? ? ? [] | | | | ] | ] |]; discriminate |].
      destruct HR0m as (_ & HU0 & _).
      destruct (mdesc_entry_closed _ _ _ _ _ _ _ _ _ HU0 He) as (_ & HE0 & _).
      assert (HR0 : mdesc_scoped 0 R) by (eapply Hse; [ exact Hde | intros ? ? Hx0; lia | exact HE0 ]).
      assert (Hw : mdesc_xp Θ Ξ (Θ0 ++ Γ) R).
      { rewrite <- (mdesc_closed_sub R (ι (wk_shiftn (length Θ0))) HR0).
        eapply (mdesc_xp_sub _ _ Hc _ _ 0); [ intros ? ? Hlt; exfalso; lia | exact HR0 | exact Hx |].
        apply wk_mod_compat_sub; intros x U Hl.
        replace (wk_shiftn (length Θ0) x) with (x + length Θ0) by reflexivity.
        apply ctx_lookup_mod_app_r; exact Hl. }
      destruct (mdesc_ats_read_inv _ _ _ Ea) as [Ea' | (A & M0 & Rm & ? & B & M' & Rm' & -> & -> & _ & Ea')].
      * eapply mdesc_xp_ats; [ exact Hc | apply slots_ok_app; eassumption | eapply mdesc_scoped_mono; [| exact HR0 ]; lia | exact HNs | exact Hw | exact Ea' ].
      * cbn in Hw |- *; destruct HR0 as (_ & _ & HRm0).
        eapply mdesc_xp_ats; [ exact Hc | apply slots_ok_app; eassumption | eapply mdesc_scoped_mono; [| exact HRm0 ]; lia | exact HNs | exact Hw | exact Ea' ].
  - (* a body *)
    match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => destruct sm, o; cbn in Hb; try discriminate; injection Hb as <- end;
      first [ assumption | exact I ].
  - (* an alias *)
    match goal with Hu : gunit_scoped _ _ \/ _ |- _ => destruct Hu as [HU | (T & Φ0 & [=] & _)] end.
    rewrite gunit_scoped_mk in HU; destruct HU as [HΔ HE]; cbn in HE.
    apply mdesc_xp_up; eapply mdesc_xp_mod; [| eassumption ].
    match goal with IH : forall m, slots_ok m (_ ++ _) -> _ -> _ |- _ => eapply IH end;
      [ apply slots_ok_app; eassumption | exact HE ].
  - (* a module *)
    match goal with IH : forall m, slots_ok m _ -> _ -> _ |- _ => eapply IH; [ eassumption |] end.
    cbn in *; assumption.
  - (* a definition with a module part: its module part *)
    match goal with IH : forall m, slots_ok m _ -> _ -> _ |- _ => eapply IH; [ eassumption |] end.
    cbn in *; left; tauto.
Qed.

Corollary mdenote_xp : forall Θ Ξ, gctx_closed Θ Ξ ->
    forall Γ H R, mdenote Θ Ξ Γ H R -> ctx_scoped 0 Γ -> modexp_scoped (length Γ) H -> mdesc_xp Θ Ξ Γ R.
Proof. intros * Hc * Hm HΓ HH; exact (proj1 (mdenote_xp_all _ _ Hc) _ _ _ Hm _ (slots_ok_ctx _ HΓ) HH). Qed.

(** What a well-formed module expression denotes is read where it is. *)
Lemma wf_mdenote_xp : forall Θ Ξ Γ H H' R,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ H R -> mdesc_xp Θ Ξ Γ R.
Proof.
  intros * HH Hm; destruct (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & HHs & _).
  eapply (proj1 (mdenote_xp_all _ _ (wf_gctx_closed _ _ _ (presup_modexp_eq_ctx HH)))); [ exact Hm | apply slots_ok_ctx, HΓ | exact HHs ].
Qed.

Lemma wf_mdenote_mod_xp : forall Θ Ξ Γ H H' R Rm,
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote Θ Ξ Γ H R -> mdesc_mod R = Some Rm -> mdesc_xp Θ Ξ Γ Rm.
Proof. intros * HH Hm Hd; eapply mdesc_xp_mod; [ eapply wf_mdenote_xp; eassumption | exact Hd ]. Qed.

Lemma mdesc_is_mod_up : forall Θ' R, mdesc_is_mod R -> mdesc_is_mod (mdesc_up Θ' R).
Proof. intros * H; destruct R; cbn in *; tauto. Qed.

Lemma mdesc_at_is_mod : forall R N R', mdesc_is_mod R -> mdesc_at R N = Some R' -> mdesc_is_mod R'.
Proof.
  intros * Hm Ha; destruct R as [| Δ Φ | Θ p T Φ Ns |]; cbn in Hm, Ha; try contradiction.
  - destruct (tele_split (rev Δ)) as [[[? ?] ?] |]; [ injection Ha as <-; exact I | discriminate ].
  - destruct (tele_split (rev Θ)) as [[[? ?] ?] | ?]; injection Ha as <-; exact I.
Qed.

Lemma mdesc_ats_is_mod : forall Ns R R', mdesc_is_mod R -> mdesc_ats R Ns = Some R' -> mdesc_is_mod R'.
Proof.
  induction Ns as [| N Ns IH]; intros * Hm Ha; cbn in Ha; [ injection Ha as <-; exact Hm |].
  destruct (mdesc_at R N) as [R1 |] eqn:E; [| discriminate ].
  exact (IH _ _ (mdesc_at_is_mod _ _ _ Hm E) Ha).
Qed.

(** Reading a term as a name changes nothing else. *)
Lemma mdesc_self_mod : forall M R, mdesc_is_mod R -> mdesc_self M R = R.
Proof. intros M [] H; cbn in H; first [ contradiction | reflexivity ]. Qed.

(** The unit a module part stands for denotes it. *)
Lemma mdesc_unit_denote : forall Θ Ξ Rm, ⊢ᵍ Θ ⍮ Ξ -> mdesc_canonical Θ Ξ Rm -> mdesc_is_mod Rm ->
    forall Γ, mdesc_xp Θ Ξ Γ Rm -> exists R, mdenote Θ Ξ Γ (mdesc_unit Rm) R /\ mdesc_mod R = Some Rm.
Proof.
  intros * Hg Hc Hm Γ Hx; destruct Rm as [r A om | Δ Φ Φx | [| e Θ'] p T Φ Ns | ? ? ? ?]; cbn in Hm, Hc, Hx |- *; try contradiction.
  - exists (mdesc_open Δ Φ Φx); split; [| reflexivity ].
    apply mdenote_lit; eapply udenote_body; [ exact Hx | reflexivity ].
  - exact (filed_denote _ _ Hg _ _ _ Γ Ns (gc_loc_of_loc _ _ Hg _ _ _ Hc)).
  - destruct (filed_denote _ _ Hg _ _ _ ((e :: Θ') ++ Γ) Ns (gc_loc_of_loc _ _ Hg _ _ _ Hc)) as (R & HR & HRm).
    exists (mdesc_up (e :: Θ') (mdesc_closed nil p T Φ Ns)); split; [ apply mdenote_lit; eapply udenote_alias; eassumption | reflexivity ].
Qed.

Theorem denote_exists :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> slots_denote Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> slots_denote Θ Ξ Γ) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> slots_denote Θ Ξ Γ) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> slots_denote Θ Ξ Γ) /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> slots_denote Θ Ξ Γ) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     slots_denote Θ Ξ Γ /\ slots_denote Θ Ξ (Ψ ++ Γ) /\ slots_denote Θ Ξ (Ψ' ++ Γ)) /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
     slots_denote Θ Ξ Γ /\ (exists R, udenote Θ Ξ Γ None U R) /\ (exists R, udenote Θ Ξ Γ None U' R)) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     slots_denote Θ Ξ Γ /\
     (exists R Rm, mdenote Θ Ξ Γ H R /\ mdesc_mod R = Some Rm) /\
     (exists R Rm, mdenote Θ Ξ Γ H' R /\ mdesc_mod R = Some Rm)).
Proof.
  apply syntactic_wf_mut_ind; intros; destruct_conjs.
  (* the context of a judgment is the context of one of its premises *)
  all: try match goal with |- slots_denote _ _ ?G => solve [ assumption ] end.
  (* the empty context *)
  all: try solve [ intros x U Hl; inversion Hl ].
  (* context extensions *)
  all: try solve [ apply slots_denote_cons; [ econstructor; eassumption | assumption | .. ];
                   first [ intros; discriminate | intros ? [= <-]; eauto | intros ? ? ? [= <- <- <-]; eauto ] ].
  all: try match goal with |- slots_denote _ _ _ /\ _ => split; [ assumption |] end.
  (* extensions of extensions *)
  all: try solve [ cbn [List.app]; split; (apply slots_denote_cons;
      [ first [ econstructor; eassumption | eapply wf_ctx_extend_mod; eapply wf_unit_eq_refl_left; eassumption
              | eapply wf_ctx_extend_dm; [ eassumption | eassumption | eapply wf_unit_eq_refl_left; eassumption ] ]
      | assumption | .. ];
      first [ intros; discriminate | intros ? [= <-]; eauto | intros ? ? ? [= <- <- <-]; eauto ]) ].
  all: try solve [
    match goal with Hm : mdenote _ _ _ ?H ?R, Ht : mdesc_mod_tele ?R = Some _
      |- (exists _ _, mdenote _ _ _ ?H _ /\ _) /\ (exists _ _, mdenote _ _ _ ?H _ /\ _) =>
        unfold mdesc_mod_tele in Ht; destruct (mdesc_mod R) as [Rm |] eqn:Hmd; [| discriminate ];
        split; exists R, Rm; split; assumption
    end ].
  all: try solve [ split; assumption ].
  all: try solve [ split; eexists; eassumption ].
  (* units *)
  all: try solve [ split; eexists; econstructor; solve [ eassumption | reflexivity ] ].
  (* an alias of a literal, and the literal over both telescopes *)
  all: try solve [
    match goal with HR : udenote _ _ _ None (gu_mk ?Δ' ?D) ?R
      |- (exists _, udenote _ _ _ _ (gu_mk ?Δ (md_alias (me_lit (gu_mk ?Δ' ?D)))) _) /\ _ =>
        split; [ eexists; eapply udenote_alias; [ apply mdenote_lit; exact HR | apply mdesc_is_mod_mod, (udenote_is_mod _ _ _ _ _ _ HR) ] |];
        change (gu_mk (Δ' ++ Δ) D) with (gunit_abs Δ (gu_mk Δ' D)); eexists; apply udenote_abs; exact HR
    end ].
  (* two module expressions denoting the same module *)
  all: try solve [
    match goal with
    | Hm : mdenote _ _ _ ?H ?R, Hm' : mdenote _ _ _ ?H' ?R, Hd : mdesc_mod ?R = Some ?Rm
      |- (exists _ _, mdenote _ _ _ ?H _ /\ _) /\ (exists _ _, mdenote _ _ _ ?H' _ /\ _) =>
        split; exists R, Rm; split; assumption
    end ].
  (* a unit *)
  all: try solve [ split; do 2 eexists; (split; [ econstructor; eassumption | reflexivity ]) ].
  (* a slot *)
  all: try solve [
    match goal with Hs : slots_denote _ _ _, Hl : _ ∋ # _ ≔ₘ _ |- _ => destruct (Hs _ _ Hl) as [R HR] end;
    split; exists R, R; (split; [ econstructor; eassumption | apply mdesc_is_mod_mod, (udenote_is_mod _ _ _ _ _ _ HR) ]) ].
  (* a literal *)
  all: try solve [
    match goal with HR : udenote _ _ _ _ ?U ?R, HR' : udenote _ _ _ _ ?U' ?R' |- (exists _ _, mdenote _ _ _ (me_lit ?U) _ /\ _) /\ (exists _ _, mdenote _ _ _ (me_lit ?U') _ /\ _) =>
      split; [ exists R, R | exists R', R' ];
      (split; [ econstructor; eassumption | apply mdesc_is_mod_mod; eapply udenote_is_mod; eassumption ]) end ].
  (* a unit or a selection: a module part with a telescope *)
  all: try solve [
    match goal with
    | Hm : mdenote _ _ _ ?H ?R, Ht : mdesc_mod_tele ?R = Some _, Hm' : mdenote _ _ _ ?H' ?R', Ht' : mdesc_mod_tele ?R' = Some _
      |- (exists _ _, mdenote _ _ _ ?H _ /\ _) /\ (exists _ _, mdenote _ _ _ ?H' _ /\ _) =>
        unfold mdesc_mod_tele in Ht, Ht';
        destruct (mdesc_mod R) as [Rm |] eqn:Hmd; [| discriminate ];
        destruct (mdesc_mod R') as [Rm' |] eqn:Hmd'; [| discriminate ];
        split; [ exists R, Rm | exists R', Rm' ]; split; assumption
    end ].
  (* an application *)
  all: try solve [
    match goal with
    | Hm : mdenote _ _ _ ?H ?R, Ht : mdesc_mod_tele ?R = Some ?T, Hv : tele_view ?T = Some _,
      Hm' : mdenote _ _ _ ?H' ?R', Ht' : mdesc_mod_tele ?R' = Some ?T', Hv' : tele_view ?T' = Some _
      |- (exists _ _, mdenote _ _ _ (me_app ?H ?N) _ /\ _) /\ (exists _ _, mdenote _ _ _ (me_app ?H' ?N') _ /\ _) =>
        destruct (mdesc_at_total _ _ _ _ N Ht Hv) as (R1 & Ha);
        destruct (mdesc_at_total _ _ _ _ N' Ht' Hv') as (R1' & Ha');
        unfold mdesc_mod_tele in Ht, Ht';
        destruct (mdesc_mod R) as [Rm |] eqn:Hmd; [| discriminate ];
        destruct (mdesc_mod R') as [Rm' |] eqn:Hmd'; [| discriminate ];
        destruct (mdesc_at_mod _ _ _ _ Hmd Ha) as (Rm1 & Hm1);
        destruct (mdesc_at_mod _ _ _ _ Hmd' Ha') as (Rm1' & Hm1');
        split; do 2 eexists; (split; [ econstructor; eassumption | eassumption ])
    end ].
  all: try solve [ split; do 2 eexists; split; eassumption ].
  (* a loaded unit or an open frame *)
  all: try solve [
    match goal with Hu : gc_unit _ _ ?H = Some ?TΦ |- _ =>
      destruct TΦ as [T Φ]; destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq & _);
      split; exists (mdesc_closed nil mp T Φ nil), (mdesc_closed nil mp T Φ nil); (split; [ apply mdenote_unit; assumption | reflexivity ])
    end ].
  (* [β]: both sides denote one module *)
  all: try solve [
    match goal with HU : wf_unit_eq _ _ _ (gu_mk (?Δ ++ ce_ass ?κ ?X :: nil) ?D) _, HR : udenote _ _ _ None (gu_mk _ ?D) ?R
      |- (exists _ _, mdenote _ _ _ (me_app _ ?N) _ /\ _) /\ _ =>
        let Hb1 := fresh "Hb" in let Hb2 := fresh "Hb" in let Hb3 := fresh "Hb" in
        destruct (mdenote_beta _ _ _ _ _ _ _ N HU _ HR) as (R' & Hb1 & Hb2 & Hb3);
        rewrite gunit_sub_mk in Hb2; cbn [moddef_sub] in Hb2;
        split; exists R', R'; split; assumption
    end ].
  (* an alias with no parameter *)
  all: try solve [
    match goal with HE : mdenote _ _ _ ?E ?R, HEm : mdesc_mod ?R = Some ?Rm |- (exists _ _, mdenote _ _ _ (me_lit (gu_mk nil (md_alias ?E))) _ /\ _) /\ _ =>
      split; [ exists (mdesc_up nil Rm), (mdesc_up nil Rm); split; [ apply mdenote_lit; econstructor; eassumption |]
             | exists R, Rm; split; assumption ];
      rewrite mdesc_up_nil; apply mdesc_is_mod_mod; exact (mdesc_mod_is_mod _ _ HEm)
    end ].
  (* a selection: the unit its module part stands for *)
  all: try solve [
    match goal with Hm : mdenote _ _ ?G (me_mem ?H ?y) ?R, Hd : mdesc_mod ?R = Some ?Rm,
      HH : wf_modexp_eq _ _ _ (me_mem ?H ?y) _
      |- (exists _ _, mdenote _ _ _ (me_mem ?H ?y) _ /\ _) /\ (exists _ _, mdenote _ _ _ (mdesc_unit ?Rm) _ /\ _) =>
        let Hg := fresh "Hg" in
        pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HH)) as Hg;
        destruct (mdesc_unit_denote _ _ _ Hg (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hg Hm) Hd) (mdesc_mod_is_mod _ _ Hd) G
                    (wf_mdenote_mod_xp _ _ _ _ _ _ _ HH Hm Hd))
          as (R' & HR' & HR'm);
        split; [ exists R, Rm | exists R', Rm ]; split; assumption
    end ].
  (* a body unit's expansion: its own expansion *)
  all: match goal with |- (exists _, udenote _ _ _ None (gu_open _ ?Φ) _) /\
                          (exists _, udenote _ _ _ None (gu_open _ (gm_expand ?Φ)) _) =>
         split; [ eexists; eassumption |];
         eexists; econstructor; [ apply body_xp_noopen, gm_noopen_expand | reflexivity ]
       end.
Qed.

(** A stored module is a well-formed module expression: its root is a
    loaded unit or an open frame, and each selection below it denotes a
    module with a telescope. *)
Lemma loc_modexp_wf : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> forall p T Φ, loc Θ Ξ p T Φ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ᵐ qname_mod p ≈ qname_mod p.
Proof.
  intros Θ Ξ Γ HΓ; pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  intros [u ch]; revert u; induction ch as [| y ch IH] using List.rev_ind; intros u T Φ Hl.
  - destruct (qname_mod_denote _ _ Hg _ _ _ Γ Hl) as (R & Hm & _).
    unfold qname_mod in Hm |- *; cbn [q_unit q_chain me_mems] in Hm |- *.
    inversion Hm; subst; [ eapply wf_me_unit; eassumption | |]; exfalso;
      [ match goal with Hk : gs_find_ind _ _ = Some _, Hq : mod_qname _ = Some _ |- _ =>
          cbn in Hq; injection Hq as <-; destruct (frame_ind_parent _ _ Hg _ _ Hk) as (mq & y & Hp) end
      | match goal with Hk : gs_find_record _ _ = Some _, Hq : mod_qname _ = Some _ |- _ =>
          cbn in Hq; injection Hq as <-; destruct (frame_record_parent _ _ Hg _ _ Hk) as (mq & y & Hp) end ];
      destruct mq as [? cq]; unfold qname_in in Hp; cbn in Hp; injection Hp as _ Hc;
      destruct cq; discriminate.
  - change {| q_unit := u; q_chain := ch ++ y :: nil |} with (qname_in {| q_unit := u; q_chain := ch |} y) in *.
    destruct (qname_mod_denote _ _ Hg _ _ _ Γ Hl) as (R & Hm & HR).
    assert (Ht : exists T0, mdesc_mod_tele R = Some T0).
    { destruct HR as [-> | (A & M & ->)]; unfold mdesc_mod_tele; cbn; eexists; reflexivity. }
    destruct Ht as (T0 & Ht).
    assert (Hp : exists T' Φ', loc Θ Ξ {| q_unit := u; q_chain := ch |} T' Φ').
    { destruct Hl as [Hf | Hb].
      - unfold gc_frame in Hf.
        destruct (gs_find_tele Ξ (qname_in {| q_unit := u; q_chain := ch |} y)) as [[[U [| ? ?]] T1] |] eqn:Ef;
          try (destruct U as [? [[|] ? | ?]]); try discriminate.
        destruct (frame_parent _ _ Hg _ _ _ _ Ef) as (T' & Φ' & Hf' & _); exists T', Φ'; left; exact Hf'.
      - destruct (gc_body_module _ _ _ _ _ Hb) as [oD Hmd].
        destruct (parent_loc_any _ _ Hg _ _ _ _ _ Hb Hmd) as (Tq & Φq & Hlq & _).
        exists Tq, Φq; exact Hlq. }
    destruct Hp as (T' & Φ' & Hp).
    rewrite qname_mod_in in Hm |- *.
    eapply wf_me_mem; [ exact (IH _ _ _ Hp) | exact Hm | exact Ht | exact Hm | exact Ht ].
Qed.


(** A description is left alone by a substitution fixing its variables. *)
Lemma mdesc_sub_fix : forall R n σ, mdesc_scoped n R -> (forall x, x < n -> σ x = se_var x) -> mdesc_sub R σ = R.
Proof.
  induction R as [r A om | Δ Φ Φx | Θ0 ? T Φ Ns | Θ0 A M Rm IH]; intros * HR Hσ; cbn in HR |- *.
  4: { destruct HR as (HΘ & [HA HM] & HRm).
       rewrite (tele_scoped_sub_agree _ _ σ Id HΘ ltac:(intros; rewrite Hσ by lia; reflexivity)), tele_sub_id, (IH _ _ HRm Hσ).
       f_equal; [ eapply (proj1 syn_scoped_sub_id); [ exact HA | apply sb_qn_fix; exact Hσ ]
                | eapply (proj1 syn_scoped_sub_id); [ exact HM | apply sb_qn_fix; exact Hσ ] ]. }
  - destruct HR as [HA Hom]; rewrite (proj1 syn_scoped_sub_id _ _ _ HA Hσ).
    destruct om as [M |]; cbn in *; [ rewrite (proj1 syn_scoped_sub_id _ _ _ Hom Hσ) |]; reflexivity.
  - destruct HR as [HR1 [HR2 _]].
    pose proof (proj1 (proj2 (proj2 (proj2 syn_scoped_sub_id))) _ _ _ HR1 Hσ) as HU.
    pose proof (proj1 (proj2 (proj2 (proj2 syn_scoped_sub_id))) _ _ _ HR2 Hσ) as HU2.
    rewrite gunit_sub_mk in HU, HU2; injection HU as HΔ HΦ; injection HU2 as _ HΦx; rewrite HΔ, HΦ, HΦx; reflexivity.
  - destruct HR as (HΘ & _ & HNs).
    rewrite (tele_scoped_sub_agree _ _ σ Id HΘ ltac:(intros; rewrite Hσ by lia; reflexivity)), tele_sub_id.
    f_equal; rewrite <- (List.map_id Ns) at 2; apply List.map_ext_in; intros M HM.
    eapply (proj1 syn_scoped_sub_id); [ eapply List.Forall_forall in HNs; [ exact HNs | exact HM ] |].
    apply sb_qn_fix; exact Hσ.
Qed.

(** A judgment over a closed telescope, read over the telescope on top of
    any context. *)
Lemma closed_tele_weaken_exp : forall Θ Ξ T Γ M A,
    ctx_scoped 0 T -> Θ ⍮ Ξ ⍮ T ⊢ M : A -> ⊢ Θ ⍮ Ξ ⍮ T ++ Γ -> Θ ⍮ Ξ ⍮ T ++ Γ ⊢ M : A.
Proof.
  intros * Hs HM HTΓ.
  destruct (proj1 (proj2 wf_scoped) _ _ _ _ _ HM) as (_ & HsM & HsA).
  assert (Hσ : Θ ⍮ Ξ ⍮ tele_sub T Id ++ Γ ⊢ˢ sb_qn (length T) Id : T ++ ⋅).
  { apply wf_sub_ext; [ apply wf_sub_to_nil, (ctx_app_wf_tail _ _ _ _ HTΓ) | rewrite tele_sub_id; exact HTΓ |
      rewrite List.app_nil_r; eapply presup_exp_ctx; exact HM ]. }
  rewrite tele_sub_id in Hσ; rewrite List.app_nil_r in Hσ.
  pose proof (sub_preserves_exp _ _ _ _ _ _ _ HM Hσ) as H.
  assert (Hfix : forall x, x < length T -> sb_qn (length T) Id x = se_var x)
    by (intros x Hx; apply (sb_qn_fix _ _ 0); [ intros; lia | lia ]).
  rewrite (proj1 syn_scoped_sub_id _ _ _ HsM Hfix), (proj1 syn_scoped_sub_id _ _ _ HsA Hfix) in H; exact H.
Qed.

(** What a coherent body says of one of its entries. *)
Definition ge_coherent (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ r A _ => exists A0, A = ctx_pi_at r T A0
  | ge_mod _ (gu_mk Δ (md_body _ Φ')) => all_assumptions Δ /\ gm_coherent (Δ ++ T) Φ'
  | ge_mod _ (gu_mk Δ (md_alias _)) => exists Δ0, Δ = Δ0 ++ T /\ all_assumptions Δ0
  | ge_ind _ _ _ D Φ' => (exists Δ0, ind_uparams D = Δ0 ++ T /\ all_assumptions Δ0) /\ gm_coherent (ind_uparams D) Φ'
  | ge_def_mod _ A M U =>
      (exists A0 M0, A = ctx_pi T A0 /\ M = ctx_fn T M0) /\ exists Δ0 E, U = gu_mk (Δ0 ++ T) (md_alias E) /\ all_assumptions Δ0
  | ge_record _ p R Φ' => (exists Δ0, record_params R = Δ0 ++ T /\ all_assumptions Δ0) /\ gm_coherent (record_mod_tele p R) Φ'
  end.

Lemma gm_coherent_prefix : forall T Φ y Φ0 E, gm_coherent T Φ -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> ge_coherent T E.
Proof.
  induction Φ as [| Φ IH x E0 | Φ IH H its]; intros * Hc Hp; cbn in Hc, Hp; [ discriminate | |].
  - destruct (String.eqb y x); [ injection Hp as -> -> -> |].
    + destruct E as [b pv ra AB | ? [Δ [? Φ' | E']] | ? ? ? D Φ' | ? Aa Ma Ua | ? pr Rr ΦR]; cbn; first [ apply Hc | exact I ].
    + destruct E0 as [b pv ra AB | ? [Δ [? Φ' | E']] | ? ? ? D Φ' | ? Aa Ma Ua | ? pr Rr ΦR];
        (eapply IH; [ first [ apply Hc | exact Hc ] | exact Hp ]).
  - destruct (existsb _ _); [ discriminate | eauto ].
Qed.

Lemma loc_coherent : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p T Φ, loc Θ Ξ p T Φ -> gm_coherent T Φ.
Proof.
  intros * Hg * [Hl | Hl]; [| exact (gc_body_coherent _ _ Hg _ _ _ Hl) ].
  unfold gc_frame in Hl.
  destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ0 | E]] [| ? ?]] T0] |] eqn:Ef; try discriminate.
  injection Hl as <- <-; exact (wf_gstack_coherent _ _ Hg _ _ _ _ Ef).
Qed.


(** The entries of a local body before a member, filled in, form a
    well-typed substitution. *)
Lemma wf_gm_fill : forall Θ Ξ Φ Γ0 σ,
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Γ0 -> gm_fill Φ = Some σ -> Θ ⍮ Ξ ⍮ Γ0 ⊢ˢ σ : body_ctx Φ ++ Γ0.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * HΦ Hf; cbn in Hf |- *.
  - injection Hf as <-; apply wf_sub_id; exact HΦ.
  - destruct E as [b pv ra A [M |] | pv U | ? ? ? ? | ? ? ? ? | ? ? ?]; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:E0; cbn in Hf; try discriminate; injection Hf as <-; cbn [body_ctx List.app] in HΦ |- *.
    + destruct (ctx_decomp_def HΦ) as (HΓ & _ & HM).
      destruct (ctx_decomp_def_sorted HΦ) as (Srt & HS & HA).
      pose proof (IH _ _ HΓ eq_refl) as Hσ.
      eapply wf_sub_extend_def; [ exact Hσ | exact HA | exact HS | exact HM | eapply sub_preserves_exp; eassumption |].
      apply wf_exp_eq_refl; eapply sub_preserves_exp; eassumption.
    + destruct (ctx_decomp_mod HΦ) as (HΓ & HU).
      pose proof (IH _ _ HΓ eq_refl) as Hσ.
      eapply wf_sub_extend_mod; [ exact Hσ | exact HU | eapply sub_preserves_unit; eassumption ].
    + destruct (ctx_decomp_dm HΦ) as (HΓ & [i HA] & HM & HU).
      pose proof (IH _ _ HΓ eq_refl) as Hσ.
      eapply wf_sub_extend_dm; [ exact Hσ | exact HA | exact HM | exact HU | eapply sub_preserves_exp; eassumption
                               | apply wf_exp_eq_refl; eapply sub_preserves_exp; eassumption
                               | eapply sub_preserves_unit; eassumption ].
  - discriminate.
Qed.

(** ** The Parts of a Well-formed Unit

    A well-formed literal unit is a well-formed body or alias over a
    telescope of assumptions ([unit_full]).  Its parts are invariant under
    moving parameters between the unit and the context. *)

(** The body before a member of a well-formed body unit, the member
    included, extends a well-formed context. *)
Lemma body_prefix_wf : forall Θ Ξ Γ Δ Φ x Φx,
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Δ ++ Γ -> gm_prefix_upto Φ x = Some Φx ->
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ Δ ++ Γ.
Proof.
  intros * HC Hx.
  destruct (gm_prefix_upto_body_ctx _ _ _ Hx) as [Ψ HΨ]; rewrite HΨ, <- app_assoc in HC.
  exact (ctx_app_wf_right _ _ _ _ HC).
Qed.

(** The module part of the last entry of a well-formed body, a module or
    a definition with a module part, is a well-formed unit over the body
    before it. *)
Lemma body_ext_unit_wf : forall Θ Ξ Φ y E U Γ,
    ⊢ Θ ⍮ Ξ ⍮ body_ctx (gm_ext Φ y E) ++ Γ -> entry_unit E = Some U ->
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Γ /\ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Γ ⊢ᵘ U ≈ U.
Proof.
  intros * H HE; destruct E; cbn in HE; try discriminate; injection HE as <-; cbn [body_ctx List.app] in H.
  - exact (ctx_decomp_mod H).
  - destruct (ctx_decomp_dm H) as (? & _ & _ & ?); split; assumption.
Qed.

(** The module part of an entry of a well-formed body, a module or a
    definition with a module part, is a well-formed unit. *)
Lemma body_prefix_mod_wf : forall Θ Ξ Γ Δ Φ y Φ' E Uy,
    ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Δ ++ Γ -> gm_prefix_upto Φ y = Some (gm_ext Φ' y E) -> entry_unit E = Some Uy ->
    Θ ⍮ Ξ ⍮ body_ctx Φ' ++ Δ ++ Γ ⊢ᵘ Uy ≈ Uy.
Proof.
  intros * HC Hx HE; pose proof (body_prefix_wf _ _ _ _ _ _ _ HC Hx) as H.
  exact (proj2 (body_ext_unit_wf _ _ _ _ _ _ _ H HE)).
Qed.

(** The sorts of the types of the term parts of a well-formed body. *)
Lemma body_levels : forall Θ Ξ Γ Φ, ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Γ -> gm_noopen Φ ->
    exists entry_sort : String.string -> exp, (forall y, type_sort (entry_sort y)) /\
      forall y Φ0 E A M, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) ->
      entry_tm E = Some (A, M) -> Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ Γ ⊢ A : entry_sort y.
Proof.
  intros Θ Ξ Γ Φ; induction Φ as [| Φ IH x E | Φ IH H its]; intros HC Hn; cbn in Hn.
  - exists (fun _ => Typeω@0); split; [ constructor | intros * Hp; discriminate ].
  - assert (HC' : ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Γ)
      by (destruct E as [? ? ? ? [] | | | | ]; cbn [body_ctx List.app] in HC; exact (ctx_decomp_tail HC)).
    destruct (IH HC' Hn) as (es & Hes & Hlv).
    assert (Hcase : exists S, type_sort S /\ forall A M, entry_tm E = Some (A, M) -> Θ ⍮ Ξ ⍮ body_ctx Φ ++ Γ ⊢ A : S).
    { destruct E as [b pv ra A [M |] | | | pv A M U | ]; try (exists (Typeω@0); split; [ constructor | intros; discriminate ]);
        cbn [body_ctx List.app] in HC.
      - destruct (ctx_decomp_def_sorted HC) as (S & HS & Hi).
        exists S; split; [ exact HS | intros * [= <- <-]; exact Hi ].
      - destruct (ctx_decomp_dm HC) as (_ & [i Hi] & _).
        exists (Typeω@i); split; [ constructor | intros * [= <- <-]; exact Hi ]. }
    destruct Hcase as (S & HS & Hi).
    exists (fun z => if String.eqb z x then S else es z); split.
    + intros z; cbv beta; destruct (String.eqb z x); [ exact HS | apply Hes ].
    + intros y Φ0 E0 A M Hp HE; cbn in Hp; cbv beta.
      destruct (String.eqb_spec y x) as [-> | Hne].
      * injection Hp as <- ->; exact (Hi _ _ HE).
      * apply String.eqb_neq in Hne; rewrite ?Hne in Hp |- *; exact (Hlv _ _ _ _ _ Hp HE).
  - contradiction.
Qed.

(** The entry of a body of the same shape named as one of the other's. *)
Lemma shape_prefix : forall Φ Φ' y Φ0 E, body_shape Φ Φ' -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) ->
    exists Φ0' E', gm_prefix_upto Φ' y = Some (gm_ext Φ0' y E') /\ body_shape Φ0 Φ0' /\ entry_shape E E'.
Proof.
  induction Φ as [| Φ IH x E0 | Φ IH H its]; intros [| Φ' x' E0' | Φ' H' its'] * Hs Hp; cbn in Hs, Hp |- *; try contradiction; try discriminate.
  - destruct Hs as (Hs & <- & HE).
    destruct (String.eqb y x); [ injection Hp as ? ? ?; subst; do 2 eexists; split; [ reflexivity | split; assumption ] |].
    exact (IH _ _ _ _ Hs Hp).
  - destruct Hs as (Hs & <- & _); destruct (List.existsb _ _); [ discriminate | exact (IH _ _ _ _ Hs Hp) ].
Qed.

Lemma fill_prefix : forall Φ y Φ0 E, gm_fill Φ <> None -> gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) ->
    exists σ, gm_fill Φ0 = Some σ.
Proof.
  induction Φ as [| Φ IH x E0 | Φ IH H its]; intros * Hf Hp; cbn in Hf, Hp; try discriminate.
  - assert (Hf0 : gm_fill Φ <> None)
      by (destruct E0 as [? ? ? ? [] | | | | ]; try contradiction; destruct (gm_fill Φ); cbn in Hf; congruence).
    destruct (String.eqb y x); [ injection Hp as ? ? ?; subst; destruct (gm_fill Φ0) eqn:Ef; [ eauto | contradiction ] |].
    exact (IH _ _ _ Hf0 Hp).
  - contradiction.
Qed.

(** Entries of the same shape both have a term part, or neither. *)
Lemma entry_shape_tm : forall E E' A M, entry_shape E E' -> entry_tm E = Some (A, M) ->
    exists A' M', entry_tm E' = Some (A', M').
Proof.
  intros [? ? ? ? [] | | | | ] [? ? ? ? [] | | | | ] * HS HE; cbn in *; try contradiction; try discriminate; eauto.
Qed.

Lemma entry_shape_tm_r : forall E E' A' M', entry_shape E E' -> entry_tm E' = Some (A', M') ->
    exists A M, entry_tm E = Some (A, M).
Proof.
  intros [? ? ? ? [] | | | | ] [? ? ? ? [] | | | | ] * HS HE; cbn in *; try contradiction; try discriminate; eauto.
Qed.

(** Entries of the same shape have the same kind. *)
Lemma entry_shape_kind : forall E E', entry_shape E E' -> entry_kind E = entry_kind E'.
Proof.
  intros [? ? ? ? [] | | | | ] [? ? ? ? [] | | | | ] HS; cbn in *; try contradiction; destruct_all; congruence.
Qed.

(** The definitions of the left side of a body equation, filled in, at
    their sorts: the rule compares them with the right side's, entry by
    entry. *)
Lemma body_defs_left : forall (P : String.string -> exp -> sub -> Prop) Φx Φx',
    gm_nopens Φx = 0 -> body_shape Φx Φx' ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> P y A σ) ->
    forall y Φ0 E A M σ, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
      gm_fill Φ0 = Some σ -> P y A σ.
Proof.
  intros * Hnp Hsx HP * Hp HE Hf0.
  destruct (body_shape_fill _ _ Hnp Hsx) as [_ Hf'].
  destruct (shape_prefix _ _ _ _ _ Hsx Hp) as (Φ0' & E' & Hp' & _ & HS).
  destruct (fill_prefix _ _ _ _ Hf' Hp') as (σ' & Hf0').
  destruct (entry_shape_tm _ _ _ _ HS HE) as (A' & M' & HE').
  eauto.
Qed.

(** The parts of a well-formed open body unit [gu_open Δ Φ] over [Γ]. *)
#[warnings="-cannot-define-projection"]
Record unit_body_full (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (Φ : gmod) : Prop := mk_unit_body_full
  { (** The body as its local opens expand it *)
    unit_body_expansion : gmod
    (** The sort of the type of each definition, by its name *)
  ; unit_body_entry_sort : String.string -> exp
    (** A level containing every parameter type of a universe *)
  ; unit_body_param_level : nat
    (** The sort of each parameter, by its position from the outside *)
  ; unit_body_param_sorts : nat -> exp
    (** Each is the universe at the level or [LevelSort] *)
  ; unit_body_param_sorts_ok : forall k, parameter_sort unit_body_param_level (unit_body_param_sorts k)
    (** The expansion is the body's *)
  ; unit_body_xp : body_xp Θ Ξ (Δ ++ Γ) Φ unit_body_expansion
    (** Its entries extend a well-formed context *)
  ; unit_body_ctx : ⊢ Θ ⍮ Ξ ⍮ body_ctx unit_body_expansion ++ Δ ++ Γ
    (** Each entry sort is a type sort *)
  ; unit_body_sorts : forall y, type_sort (unit_body_entry_sort y)
    (** Each definition's sort is a sort of its kind *)
  ; unit_body_tags : forall y Φ0 E A M,
      gm_prefix_upto unit_body_expansion y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
      sort_kind (unit_body_entry_sort y) (entry_kind E)
    (** Each definition, filled in, is typed at its sort, its body at its
        type *)
  ; unit_body_defs : forall y Φ0 E A M σ,
      gm_prefix_upto unit_body_expansion y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) -> gm_fill Φ0 = Some σ ->
      Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A[σ] : unit_body_entry_sort y /\ Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M[σ] : A[σ]
    (** The target of each local open is a module there *)
  ; unit_body_opens : forall k Ψ H, nth_error (body_opens Φ unit_body_expansion) k = Some (Ψ, H) ->
      Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊢ᵐ H ≈ H
    (** The parameters are assumptions *)
  ; unit_body_ass : all_assumptions Δ
    (** The body has its own shape *)
  ; unit_body_shape : body_shape Φ Φ
    (** So has its expansion *)
  ; unit_body_xshape : body_shape unit_body_expansion unit_body_expansion
    (** The names of the body are distinct *)
  ; unit_body_nodup : List.NoDup (gm_names Φ)
    (** The parameters are types of their sorts *)
  ; unit_body_params : forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 ->
      Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ T : unit_body_param_sorts (List.length Δ2)
    (** Whether every parameter is a type of levels *)
  ; unit_body_level_flag : bool
    (** What the body denotes under the parameters, as a literal with none *)
  ; unit_body_target : mdesc
    (** The flag premise of [wf_unit_eq_body]: the parameters are types of
        levels, or the body has no member of a type of levels *)
  ; unit_body_levels : levels_flag Θ Ξ Γ Δ (me_lit (gu_open nil Φ)) unit_body_level_flag unit_body_target
    (** No local open opens a module still being defined *)
  ; unit_body_frame_free : forall k Ψ H, nth_error (body_opens Φ unit_body_expansion) k = Some (Ψ, H) ->
      frame_free_target Θ Ξ (Ψ ++ Δ ++ Γ) H }.

(** The parts of a well-formed alias unit [gu_mk Δ (md_alias E)] over [Γ]. *)
#[warnings="-cannot-define-projection"]
Record unit_alias_full (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (E : modexp) : Prop := mk_unit_alias_full
  { (** A level containing every parameter type of a universe *)
    unit_alias_param_level : nat
    (** The sort of each parameter, by its position from the outside *)
  ; unit_alias_param_sorts : nat -> exp
    (** Each is the universe at the level or [LevelSort] *)
  ; unit_alias_param_sorts_ok : forall k, parameter_sort unit_alias_param_level (unit_alias_param_sorts k)
    (** The parameters extend a well-formed context *)
  ; unit_alias_ctx : ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ
    (** The parameters are assumptions *)
  ; unit_alias_ass : all_assumptions Δ
    (** The target is a module under them *)
  ; unit_alias_target : Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E
    (** The parameters are types of their sorts *)
  ; unit_alias_params : forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 ->
      Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ T : unit_alias_param_sorts (List.length Δ2)
    (** Whether every parameter is a type of levels *)
  ; unit_alias_level_flag : bool
    (** What the target denotes under the parameters *)
  ; unit_alias_target_desc : mdesc
    (** The flag premise of [wf_unit_eq_alias]: the parameters are types of
        levels, or the target has no member of a type of levels *)
  ; unit_alias_levels : levels_flag Θ Ξ Γ Δ E unit_alias_level_flag unit_alias_target_desc
    (** The target is no module still being defined *)
  ; unit_alias_frame_free : frame_free_target Θ Ξ (Δ ++ Γ) E }.

(** The parts of a well-formed literal unit.  The parameters of a body or
    an alias are types of a universe at one level or types of levels
    ([param_level] and [param_sorts] of the unit rules). *)
Definition unit_full (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (U : gunit) : Prop :=
  match U with
  | gu_mk Δ (md_body sm_open Φ) => unit_body_full Θ Ξ Γ Δ Φ
  | gu_mk Δ (md_body sm_closed _) => False
  | gu_mk Δ (md_alias E) => unit_alias_full Θ Ξ Γ Δ E
  end.

(** A body's definitions, filled in, are typed when its entries extend a
    well-formed context. *)
Lemma body_defs_wf : forall Θ Ξ Γ Δ Φx, ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ Δ ++ Γ -> gm_noopen Φx ->
    exists entry_sort : String.string -> exp, (forall y, type_sort (entry_sort y)) /\
      forall y Φ0 E A M σ,
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) -> gm_fill Φ0 = Some σ ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A[σ] : entry_sort y /\ Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M[σ] : A[σ].
Proof.
  intros * HΦ Hn.
  destruct (body_levels _ _ _ _ HΦ Hn) as (es & Hes & Hlv); exists es; split; [ exact Hes |].
  intros y Φ0 E A M σ Hp HE Hf.
  pose proof (body_prefix_wf _ _ _ _ _ _ _ HΦ Hp) as HΦ1.
  assert (HΦ0M : ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ Δ ++ Γ /\ Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ Δ ++ Γ ⊢ M : A)
    by (destruct E as [? ? ? ? [] | | | | ]; cbn in HE; try discriminate; injection HE as <- <-;
        cbn [body_ctx List.app] in HΦ1;
        first [ destruct (ctx_decomp_def HΦ1) as (? & _ & ?) | destruct (ctx_decomp_dm HΦ1) as (? & _ & ? & _) ];
        split; assumption).
  destruct HΦ0M as [HΦ0 HM].
  pose proof (wf_gm_fill _ _ _ _ _ HΦ0 Hf) as Hσ.
  split; [ exact (sub_preserves_sort _ _ _ _ _ _ _ (Hlv _ _ _ _ _ Hp HE) (Hes y) Hσ) | exact (sub_preserves_exp _ _ _ _ _ _ _ HM Hσ) ].
Qed.

Lemma unit_eq_of_full : forall Θ Ξ Γ U, unit_full Θ Ξ Γ U -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U.
Proof.
  intros * HU; destruct U as [Δ [[] Φ | E]]; cbn in HU; try contradiction.
  - destruct HU as [Φx es l ps Hps Hx HC Hes Htg Hd Ho Ha Hs Hsx Hn Hp lv Rt HF Hff].
    assert (HΔ : ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ) by exact (ctx_app_wf_tail _ _ _ _ HC).
    assert (Hsame : forall y Φ0 E Φ0' E', gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) ->
              gm_prefix_upto Φx y = Some (gm_ext Φ0' y E') -> Φ0' = Φ0 /\ E' = E)
      by (intros * H1 H2; rewrite H1 in H2; injection H2 as -> ->; split; reflexivity).
    eapply wf_unit_eq_body with (entry_sort := es) (param_level := l) (param_sorts := ps) (lv := lv) (Rt := Rt)
                                (lv' := lv) (Rt' := Rt); try eassumption; try reflexivity;
      try exact (levels_flag_sorted _ _ _ _ _ _ _ HF); try exact (levels_flag_denotes _ _ _ _ _ _ _ HF);
      try exact (levels_flag_no_level _ _ _ _ _ _ _ HF).
    (* the term parts and the module parts, both sides the same *)
    all: try solve [ intros * H1 HE1 H2 HE2 Hf1 Hf2;
                     destruct (Hsame _ _ _ _ _ H1 H2) as [-> ->]; rewrite HE1 in HE2;
                     first [ injection HE2 as -> -> | injection HE2 as -> ];
                     rewrite Hf1 in Hf2; injection Hf2 as ->;
                     first [ exact (proj1 (Hd _ _ _ _ _ _ H1 HE1 Hf1))
                           | exact (proj2 (Hd _ _ _ _ _ _ H1 HE1 Hf1))
                           | apply wf_exp_eq_refl; exact (proj1 (Hd _ _ _ _ _ _ H1 HE1 Hf1))
                           | apply wf_exp_eq_refl; exact (proj2 (Hd _ _ _ _ _ _ H1 HE1 Hf1))
                           | pose proof (body_prefix_mod_wf _ _ _ _ _ _ _ _ _ HC H1 HE1) as HU0;
                             apply (sub_preserves_unit _ _ _ _ _ _ _ HU0);
                             apply wf_gm_fill; [ exact (presup_unit_eq_ctx HU0) | exact Hf1 ] ] ].
    + apply ext_of_ctx'; exact HΔ.
    + apply ext_of_ctx'; rewrite <- app_assoc; exact HC.
    + apply ext_of_ctx'; rewrite <- app_assoc; exact HC.
    + (* the opens, each filled in *)
      intros k Φ0 H Φ0' H' σ σ' Hk Hk' Hf Hf'.
      rewrite Hk in Hk'; injection Hk' as <- <-; rewrite Hf in Hf'; injection Hf' as <-.
      pose proof (Ho _ _ _ (body_opens_at_nth _ _ _ _ _ Hk)) as HH.
      eapply sub_preserves_modexp; [ exact HH |].
      apply wf_gm_fill; [ exact (presup_modexp_eq_ctx HH) | exact Hf ].
    + intros k Φ0 H Φ0' H' σ σ' Hk Hk' Hf Hf'.
      rewrite Hk in Hk'; injection Hk' as <- <-; rewrite Hf in Hf'; injection Hf' as <-.
      pose proof (Ho _ _ _ (body_opens_at_nth _ _ _ _ _ Hk)) as HH.
      eapply sub_preserves_modexp; [ exact HH |].
      apply wf_gm_fill; [ exact (presup_modexp_eq_ctx HH) | exact Hf ].
  - destruct HU as [l ps Hps HΔ Ha HE Hp lv Rt HF Hff].
    eapply wf_unit_eq_alias with (param_level := l) (param_sorts := ps) (lv := lv) (Rt := Rt) (lv' := lv) (Rt' := Rt);
      try eassumption;
      try exact (levels_flag_sorted _ _ _ _ _ _ _ HF); try exact (levels_flag_denotes _ _ _ _ _ _ _ HF);
      try exact (levels_flag_no_level _ _ _ _ _ _ _ HF).
    apply ext_of_ctx'; exact HΔ.
Qed.

(** A well-formed body extension with well-formed open targets, whose
    definitions, filled in, are typed at the sorts of their tags, is a
    well-formed body unit. *)
Lemma unit_full_body : forall Θ Ξ Γ Δ Φ Φx,
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx -> ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ Δ ++ Γ ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊢ᵐ H ≈ H) ->
    all_assumptions Δ -> body_shape Φ Φ -> body_shape Φx Φx -> List.NoDup (gm_names Φ) ->
    forall l ps, (forall k, parameter_sort l (ps k)) ->
    (forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ T : ps (List.length Δ2)) ->
    forall es, (forall y, type_sort (es y)) ->
    (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       sort_kind (es y) (entry_kind E)) ->
    (forall y Φ0 E A M σ, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_fill Φ0 = Some σ -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A[σ] : es y) ->
    forall lv Rt, levels_flag Θ Ξ Γ Δ (me_lit (gu_open nil Φ)) lv Rt ->
    (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> frame_free_target Θ Ξ (Ψ ++ Δ ++ Γ) H) ->
    unit_full Θ Ξ Γ (gu_open Δ Φ).
Proof.
  intros * Hx HC Ho Ha Hs Hsx Hn l ps Hps Hp es Hes Htg HA lv Rt HF Hff.
  destruct (body_defs_wf _ _ _ _ _ HC (body_xp_result_noopen _ _ _ _ _ Hx)) as (es0 & _ & Hd).
  cbn [unit_full]; refine (mk_unit_body_full _ _ _ _ _ Φx es l ps Hps Hx HC Hes Htg _ Ho Ha Hs Hsx Hn Hp lv Rt HF Hff).
  intros * Hp0 HE Hf; split; [ exact (HA _ _ _ _ _ _ Hp0 HE Hf) | exact (proj2 (Hd _ _ _ _ _ _ Hp0 HE Hf)) ].
Qed.

(** ** Relevant Parameters *)

(** A parameter type [T] over [Γ] is a type of the universe at level [l]
    or a type of levels. *)
Definition param_typed (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (T : typ) (l : nat) : Prop :=
  Θ ⍮ Ξ ⍮ Γ ⊢ T : Typeω@l \/ Θ ⍮ Ξ ⍮ Γ ⊢ T : LevelSort.

(** The parameters [Δ] over [Γ] are types of the universe at level [l] or
    types of levels, each in the context of the parameters outside it: the
    premise (R) of the unit rules, of which [param_sorts] tells which. *)
Definition params_evaluated (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (l : nat) : Prop :=
  forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> param_typed Θ Ξ (Δ2 ++ Γ) T l.

(** The premise (R) of a rule gives parameters of evaluated kinds. *)
Lemma params_evaluated_of_sorts : forall Θ Ξ Γ Δ l ps,
    (forall k, parameter_sort l (ps k)) ->
    (forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> Θ ⍮ Ξ ⍮ Δ2 ++ Γ ⊢ T : ps (List.length Δ2)) ->
    params_evaluated Θ Ξ Γ Δ l.
Proof.
  intros * Hps HT Δ1 κ T Δ2 E; pose proof (HT _ _ _ _ E) as H.
  destruct (Hps (List.length Δ2)) as [|]; [ left | right ]; congruence.
Qed.

(** No parameters are of evaluated kinds at every level. *)
Lemma params_evaluated_nil : forall Θ Ξ Γ l, params_evaluated Θ Ξ Γ nil l.
Proof. intros * Δ1 κ T Δ2 E; destruct Δ1; discriminate. Qed.

(** A larger level contains every parameter type too. *)
Lemma param_typed_max_left : forall Θ Ξ Γ T l j, param_typed Θ Ξ Γ T l -> param_typed Θ Ξ Γ T (max l j).
Proof. intros * [H | H]; [ left; apply lift_exp_max_left; exact H | right; exact H ]. Qed.

Lemma param_typed_max_right : forall Θ Ξ Γ T l j, param_typed Θ Ξ Γ T l -> param_typed Θ Ξ Γ T (max j l).
Proof. intros * [H | H]; [ left; apply lift_exp_max_right; exact H | right; exact H ]. Qed.

Lemma params_evaluated_max : forall Θ Ξ Γ Δ l j,
    params_evaluated Θ Ξ Γ Δ l -> params_evaluated Θ Ξ Γ Δ (max l j).
Proof. intros * H Δ1 κ T Δ2 E; apply param_typed_max_left; exact (H _ _ _ _ E). Qed.

(** Inner parameters [Δy] over outer ones [Δ]: together, at a common
    level. *)
Lemma params_evaluated_app : forall Θ Ξ Γ Δy Δ l l',
    params_evaluated Θ Ξ (Δ ++ Γ) Δy l -> params_evaluated Θ Ξ Γ Δ l' ->
    params_evaluated Θ Ξ Γ (Δy ++ Δ) (max l l').
Proof.
  intros * Hy HΔ Δ1 κ T Δ2 E.
  destruct (List.app_eq_app _ _ _ _ E) as (Δc & [[E1 E2] | [E1 E2]]).
  - destruct Δc as [| e Δc]; cbn in E2.
    + apply param_typed_max_right; apply HΔ with (Δ1 := nil) (κ := κ); rewrite E2; reflexivity.
    + injection E2 as <- ->; apply param_typed_max_left; rewrite <- List.app_assoc; exact (Hy _ _ _ _ E1).
  - apply param_typed_max_right; exact (HΔ _ _ _ _ E2).
Qed.

(** One more parameter, of a type of a universe or a type of levels. *)
Lemma params_evaluated_snoc : forall Θ Ξ Γ Δ κ T l (j : nat),
    params_evaluated Θ Ξ Γ Δ l -> param_typed Θ Ξ (Δ ++ Γ) T j ->
    params_evaluated Θ Ξ Γ (ce_ass κ T :: Δ) (max j l).
Proof.
  intros * HΔ HT.
  apply (params_evaluated_app _ _ _ (ce_ass κ T :: nil) Δ j l); [| exact HΔ ].
  intros [| e Δ1] κ' T' Δ2 E; cbn in E; [ injection E as <- <- <-; exact HT | destruct Δ1; discriminate ].
Qed.

(** And apart. *)
Lemma params_evaluated_app_inv : forall Θ Ξ Γ Δy Δ l,
    params_evaluated Θ Ξ Γ (Δy ++ Δ) l ->
    params_evaluated Θ Ξ (Δ ++ Γ) Δy l /\ params_evaluated Θ Ξ Γ Δ l.
Proof.
  intros * H; split; intros Δ1 κ T Δ2 E.
  - rewrite List.app_assoc; apply (H Δ1 κ); rewrite E, <- List.app_assoc; reflexivity.
  - apply (H (Δy ++ Δ1) κ); rewrite E, <- List.app_assoc; reflexivity.
Qed.

(** Relevant parameters moved by a substitution, into a well-formed
    context. *)
Lemma params_evaluated_sub : forall Θ Ξ Γ Γ' Δ σ l,
    params_evaluated Θ Ξ Γ Δ l -> Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ : Γ ->
    ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ σ ++ Γ' ->
    params_evaluated Θ Ξ Γ' (tele_sub Δ σ) l.
Proof.
  intros * HR Hσ HΔ HΔ' Δ1' κ T' Δ2' E.
  pose proof E as E0.
  destruct (tele_sub_split_ass _ _ _ _ _ _ E) as (Δ1 & T & Δ2 & -> & -> & ->).
  assert (Hs : Θ ⍮ Ξ ⍮ tele_sub Δ2 σ ++ Γ' ⊢ˢ sb_qn (List.length Δ2) σ : Δ2 ++ Γ).
  { apply wf_sub_ext; [ exact Hσ | |].
    - rewrite E0, <- List.app_assoc in HΔ'; cbn in HΔ'.
      exact (ctx_decomp_tail (ctx_app_wf_tail _ _ _ _ HΔ')).
    - rewrite <- List.app_assoc in HΔ; cbn in HΔ.
      exact (ctx_decomp_tail (ctx_app_wf_tail _ _ _ _ HΔ)). }
  destruct (HR Δ1 κ T Δ2 eq_refl) as [H | H]; [ left | right ];
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ H Hs) as H'; cbn in H'; exact H'.
Qed.

(** [desc_levels_abstractable Θ Ξ Γ Δ R]: the description [R], read
    under the parameters [Δ] over [Γ], can be abstracted over them
    ([mdesc_up]): every parameter is a type of levels, or [R] has no member
    of a type of levels ([wf_no_level_members]).  A member of a type of
    levels abstracted over a parameter of a universe would have no type. *)
Definition desc_levels_abstractable (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (R : mdesc) : Prop :=
  level_sorted_parameters Δ \/ Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ⁿˡ R.

(** What abstracting the description [R] over [Δ] needs of [Δ]: for a
    term, whose type becomes a [Π] at its tag, that it can be abstracted;
    for a module part, whose unit takes them as parameters, parameters
    of evaluated kinds too ([params_evaluated]), and, when there are any,
    that it is no module still being defined: an alias never names an open
    frame ([frame_free_target]). *)
Definition up_evaluated (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (R : mdesc) (l : nat) : Prop :=
  match R with
  | mdesc_term _ _ _ => desc_levels_abstractable Θ Ξ Γ Δ R
  | _ => params_evaluated Θ Ξ Γ Δ l /\ desc_levels_abstractable Θ Ξ Γ Δ R /\ (Δ <> nil -> ~ desc_reads_frame Ξ R)
  end.

(** Relevant parameters over which the description can be abstracted are
    enough for every description that is no module still being defined. *)
Lemma up_evaluated_of : forall Θ Ξ Γ Δ R l, params_evaluated Θ Ξ Γ Δ l -> desc_levels_abstractable Θ Ξ Γ Δ R ->
    (Δ <> nil -> ~ desc_reads_frame Ξ R) -> up_evaluated Θ Ξ Γ Δ R l.
Proof. intros * H Ha Hf; destruct R; cbn; first [ exact Ha | exact (conj H (conj Ha Hf)) ]. Qed.

(** A description with no member of a type of levels, substituted. *)
Lemma sub_preserves_no_level : forall Θ Ξ Δ R Γ σ,
    Θ ⍮ Ξ ⍮ Δ ⊢ⁿˡ R -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_sub R σ.
Proof. intros * H Hσ; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 sub_preserves_wf)))))) _ _ _ _ H _ _ Hσ). Qed.

(** A description that can be abstracted over [Δ], substituted. *)
Lemma desc_levels_abstractable_sub : forall Θ Ξ Γ Δ R Γ' σ,
    desc_levels_abstractable Θ Ξ Γ Δ R -> Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ : Γ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ σ ++ Γ' ->
    desc_levels_abstractable Θ Ξ Γ' (tele_sub Δ σ) (mdesc_sub R (sb_qn (length Δ) σ)).
Proof.
  intros * [HL | HN] Hσ HΓ HΓ'; [ left; exact (level_sorted_parameters_sub _ _ HL) | right ].
  apply (sub_preserves_no_level _ _ _ _ _ _ HN); apply wf_sub_ext; assumption.
Qed.

(** No parameter: every description can be abstracted. *)
Lemma desc_levels_abstractable_nil : forall Θ Ξ Γ R, desc_levels_abstractable Θ Ξ Γ nil R.
Proof. intros; left; intros [| ? ?] ? ? ? E; discriminate. Qed.


(** The module a description with no member of a type of levels is read
    as has none. *)
Lemma no_level_mod : forall Θ Ξ Γ R R', Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R -> mdesc_mod R = Some R' -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R'.
Proof.
  intros * H Hm; destruct R; cbn in Hm; try discriminate; try (injection Hm as <-; exact H).
  inversion H; subst; eauto.
Qed.

(** An open description, read with its parameters split differently
    between itself and the context. *)
Lemma no_level_open_shift : forall Θ Ξ Γ1 Δ1 Γ2 Δ2 Φw Φx, Δ1 ++ Γ1 = Δ2 ++ Γ2 ->
    Θ ⍮ Ξ ⍮ Γ1 ⊢ⁿˡ mdesc_open Δ1 Φw Φx -> Θ ⍮ Ξ ⍮ Γ2 ⊢ⁿˡ mdesc_open Δ2 Φw Φx.
Proof.
  intros * E H; inversion H; subst.
  eapply wf_no_level_open; [ eassumption | | first [ rewrite <- E; eassumption | eassumption ] .. ].
  match goal with Hx : _ ⍮ _ ⍮ _ ⊢ˣ _ ≈ _ |- _ => pose proof (ext_eq_ctx_left _ _ _ _ _ Hx) as HC end.
  apply ext_of_ctx'; rewrite <- List.app_assoc, <- E, List.app_assoc; exact HC.
Qed.

(** A closed description, at any outer parameters, arguments and
    context. *)
Lemma no_level_closed_any : forall Θ Ξ Γ1 Θ1 Ns1 Γ2 Θ2 Ns2 p T Φ,
    Θ ⍮ Ξ ⍮ Γ1 ⊢ⁿˡ mdesc_closed Θ1 p T Φ Ns1 -> Θ ⍮ Ξ ⍮ Γ2 ⊢ⁿˡ mdesc_closed Θ2 p T Φ Ns2.
Proof. intros * H; inversion H; subst; eapply wf_no_level_closed; eassumption. Qed.

(** A module description has no member of a type of levels abstracted
    exactly when it has none under the parameters. *)
Lemma no_level_up_mod : forall Θ Ξ Γ Δ R, mdesc_is_mod R ->
    Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_up Δ R <-> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ⁿˡ R.
Proof.
  intros * HR; destruct R; cbn in HR |- *; try contradiction; split; intros H.
  - eapply no_level_open_shift; [| exact H ]; rewrite List.app_assoc; reflexivity.
  - eapply no_level_open_shift; [| exact H ]; rewrite List.app_assoc; reflexivity.
  - eapply no_level_closed_any; exact H.
  - eapply no_level_closed_any; exact H.
Qed.

(** A description with no member of a type of levels, abstracted over
    any telescope: a term's type becomes a [Π] into a universe, which is
    still a type of a universe. *)
Lemma no_level_up : forall Θ Ξ Γ Δ R, ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ ->
    Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ⁿˡ R -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_up Δ R.
Proof.
  intros * HΔ HN; destruct R as [r A om | | | Θd A M Rm]; cbn [mdesc_up].
  - inversion HN; subst; apply wf_no_level_term; assumption.
  - exact (proj2 (no_level_up_mod _ _ _ _ (mdesc_open _ _ _) I) HN).
  - exact (proj2 (no_level_up_mod _ _ _ _ (mdesc_closed _ _ _ _ _) I) HN).
  - inversion HN; subst; constructor; intros Rw HRw.
    rewrite mdesc_mod_up in HRw; destruct (mdesc_mod Rm) as [R0 |] eqn:HR0; cbn in HRw; [ injection HRw as <- | discriminate ].
    match goal with Hm : forall _, Some R0 = Some _ -> _ |- _ => pose proof (Hm _ eq_refl) as HN0 end.
    exact (proj2 (no_level_up_mod _ _ _ _ _ (mdesc_mod_is_mod _ _ HR0)) HN0).
Qed.

(** A description with no member of a type of levels, abstracted over
    [Δa] and given arguments for its outermost parameters, has none. *)
Lemma no_level_ats_up : forall Θ Ξ Ns Γ Δa R R',
    ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ -> all_assumptions Δa -> length Ns <= length Δa ->
    (forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts Δa Id Ns) k = Some A -> Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
    Θ ⍮ Ξ ⍮ Δa ++ Γ ⊢ⁿˡ R -> mdesc_ats (mdesc_up Δa R) Ns = Some R' -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R'.
Proof.
  intros Θ Ξ; induction Ns as [| N Ns IH]; intros * HΔ Ha Hl HNs HN Hats.
  - injection Hats as <-; exact (no_level_up _ _ _ _ _ HΔ HN).
  - destruct (List.exists_last (l := Δa)) as (Δ1 & e & ->); [ intros ->; cbn in Hl; lia |].
    unfold all_assumptions in Ha; apply List.Forall_app in Ha as [Ha1 He]; apply List.Forall_cons_iff in He as [(κC & C & ->) _].
    rewrite tele_insts_snoc in HNs.
    pose proof (HNs 0 N C[Id] eq_refl eq_refl) as HN0; rewrite exp_sub_id in HN0.
    rewrite <- List.app_assoc in HΔ, HN; cbn [List.app] in HΔ, HN.
    destruct (ctx_decomp_sort_kind (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ (Srt & HS & HC)].
    pose proof (wf_sub_single _ _ _ _ _ _ _ HC HS HN0) as Hs1.
    assert (HΔN : ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
    assert (Hσ : Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ ⊢ˢ sb_qn (length Δ1) (Id,,N) : Δ1 ++ ce_ass κC C :: Γ)
      by (apply wf_sub_ext; assumption).
    cbn [mdesc_ats] in Hats; rewrite mdesc_at_up in Hats.
    eapply (IH _ _ _ _ HΔN); [ apply all_assumptions_sub; exact Ha1 | rewrite length_tele_sub; rewrite List.length_app in Hl; cbn in Hl; lia
                             | | exact (sub_preserves_no_level _ _ _ _ _ _ HN Hσ) | exact Hats ].
    intros k N1 A HN1 HA.
    rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (Id,,N)) in HA by apply sb_compose_id_right.
    exact (HNs (S k) N1 A HN1 HA).
Qed.


(** A description that can be abstracted over [Δy ++ Δ] can be over [Δy]
    alone. *)
Lemma desc_levels_abstractable_app_inv : forall Θ Ξ Γ Δy Δ R,
    desc_levels_abstractable Θ Ξ Γ (Δy ++ Δ) R -> desc_levels_abstractable Θ Ξ (Δ ++ Γ) Δy R.
Proof.
  intros * [HL | HN]; [ left; exact (proj1 (level_sorted_app_inv _ _ HL)) | right; rewrite List.app_assoc; exact HN ].
Qed.

Lemma up_evaluated_app_inv : forall Θ Ξ Γ Δy Δ R l,
    up_evaluated Θ Ξ Γ (Δy ++ Δ) R l -> up_evaluated Θ Ξ (Δ ++ Γ) Δy R l.
Proof.
  intros * H; destruct R; cbn [up_evaluated] in H |- *;
    first [ exact (desc_levels_abstractable_app_inv _ _ _ _ _ _ H)
          | destruct H as (HR & HL & Hf);
            refine (conj (proj1 (params_evaluated_app_inv _ _ _ _ _ _ HR))
                      (conj (desc_levels_abstractable_app_inv _ _ _ _ _ _ HL) _));
            intros Hn; apply Hf; destruct Δy; [ contradiction | discriminate ] ].
Qed.

(** What abstracting needs, substituted. *)
Lemma up_evaluated_sub : forall Θ Ξ Γ Δ R l Γ' σ,
    up_evaluated Θ Ξ Γ Δ R l -> Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ : Γ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ σ ++ Γ' ->
    up_evaluated Θ Ξ Γ' (tele_sub Δ σ) (mdesc_sub R (sb_qn (length Δ) σ)) l.
Proof.
  intros * H Hσ HΓ HΓ'.
  assert (Hfr : (Δ <> nil -> ~ desc_reads_frame Ξ R) ->
            tele_sub Δ σ <> nil -> ~ desc_reads_frame Ξ (mdesc_sub R (sb_qn (length Δ) σ)))
    by (intros Hf Hn Hr; apply Hf; [ intros ->; exact (Hn eq_refl) | exact (desc_reads_frame_sub _ _ _ Hr) ]).
  destruct R; cbn [mdesc_sub up_evaluated] in H, Hfr |- *;
    first [ exact (desc_levels_abstractable_sub _ _ _ _ _ _ _ H Hσ HΓ HΓ')
          | destruct H as (HR & HL & Hf);
            exact (conj (params_evaluated_sub _ _ _ _ _ _ _ HR Hσ HΓ HΓ')
                     (conj (desc_levels_abstractable_sub _ _ _ _ _ _ _ HL Hσ HΓ HΓ') (Hfr Hf))) ].
Qed.

(** The module of a definition with a module part that can be abstracted
    can be. *)
Lemma desc_levels_abstractable_dm_mod : forall Θ Ξ Γ Δ Θd A M Rm R1,
    desc_levels_abstractable Θ Ξ Γ Δ (mdesc_dm Θd A M Rm) -> mdesc_mod Rm = Some R1 ->
    desc_levels_abstractable Θ Ξ Γ Δ R1.
Proof.
  intros * [HL | HN] Hm; [ left; exact HL | right; eapply no_level_mod; [ exact HN | cbn; exact Hm ] ].
Qed.

(** Closed parameters of evaluated kinds, read over a context. *)
Lemma params_evaluated_closed : forall Θ Ξ Γ Δ l,
    ctx_scoped 0 Δ -> params_evaluated Θ Ξ nil Δ l -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ -> params_evaluated Θ Ξ Γ Δ l.
Proof.
  intros * Hs HR HΔ Δ1 κ T Δ2 E; subst Δ.
  pose proof (HR _ _ _ _ eq_refl) as HT; rewrite List.app_nil_r in HT.
  apply ctx_scoped_app_iff in Hs as [_ Hs].
  change (ce_ass κ T :: Δ2) with ((ce_ass κ T :: nil) ++ Δ2) in Hs; apply ctx_scoped_app_iff in Hs as [_ Hs2].
  rewrite <- List.app_assoc in HΔ; cbn [List.app] in HΔ.
  pose proof (proj1 (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ))) as HΔ2.
  destruct HT as [HT | HT]; [ left | right ]; exact (closed_tele_weaken_exp _ _ _ _ _ _ Hs2 HT HΔ2).
Qed.

(** A term over a closed telescope [T], whose type is of the sort of its
    kind [r], of the types of levels only over parameters of types of
    levels (a stored definition's): it can be abstracted over [T] read over
    any context. *)
Lemma closed_term_levels_abstractable : forall Θ Ξ Γ T r A i om,
    ctx_scoped 0 T -> ⊢ Θ ⍮ Ξ ⍮ T ++ Γ ->
    (r = ak_level -> level_sorted_parameters T) ->
    Θ ⍮ Ξ ⍮ T ⊢ A : abs_kind_sort r Typeω@i ->
    desc_levels_abstractable Θ Ξ Γ T (mdesc_term r A om).
Proof.
  intros * Hs HTΓ HL HA; destruct r; try (left; exact (HL eq_refl)).
  all: right; apply wf_no_level_term; discriminate.
Qed.

(** A term with no member of a type of levels has none whatever its
    δ-reduct. *)
Lemma no_level_term_any : forall Θ Ξ Γ r A om om',
    Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_term r A om -> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_term r A om'.
Proof. intros * H; inversion H; subst; eapply wf_no_level_term; eassumption. Qed.

(** ** Descriptions Reading No Open Frame *)

(** Abstracting keeps where a module part is stored. *)
Lemma desc_reads_frame_up : forall Ξ Δ R, desc_reads_frame Ξ (mdesc_up Δ R) <-> desc_reads_frame Ξ R.
Proof.
  intros *; unfold desc_reads_frame; rewrite mdesc_mod_up.
  destruct (mdesc_mod R) as [[r A om | Δ0 Φ0 Φx0 | Θ0 p0 T0 Φ0 Ns0 | Θd A M Rm] |]; cbn;
    split; intros (Θ' & p & T & Φ & Ns & Hm & Hf); try discriminate.
  - injection Hm as _ <- <- <- _; do 5 eexists; split; [ reflexivity | exact Hf ].
  - injection Hm as _ <- <- <- _; do 5 eexists; split; [ reflexivity | exact Hf ].
Qed.

(** A closed module reads no open frame exactly when it is stored at
    none. *)
Lemma closed_frame_free_iff : forall Ξ Θ' p T Φ Ns, ~ desc_reads_frame Ξ (mdesc_closed Θ' p T Φ Ns) <-> gc_frame Ξ p = None.
Proof.
  intros *; split.
  - intros Hn; destruct (gc_frame Ξ p) eqn:Ef; [| reflexivity ].
    exfalso; apply Hn; do 5 eexists; split; [ reflexivity | rewrite Ef; discriminate ].
  - intros Hf (? & ? & ? & ? & ? & Hm & Hf'); cbn in Hm; injection Hm as _ <- _ _ _; exact (Hf' Hf).
Qed.

(** A definition with a module part reads an open frame as its module part
    does. *)
Lemma desc_reads_frame_dm : forall Ξ Θd A M R, desc_reads_frame Ξ (mdesc_dm Θd A M R) <-> desc_reads_frame Ξ R.
Proof. intros *; unfold desc_reads_frame; cbn [mdesc_mod]; reflexivity. Qed.

(** A description whose module part reads an open frame reads it. *)
Lemma desc_reads_frame_mod : forall Ξ R R1, mdesc_mod R = Some R1 -> desc_reads_frame Ξ R1 -> desc_reads_frame Ξ R.
Proof.
  intros * Hm (Θ' & p & T & Φ & Ns & Hm1 & Hf).
  pose proof (mdesc_mod_is_mod _ _ Hm) as HR1.
  destruct R1; cbn in HR1, Hm1; try contradiction; try discriminate.
  injection Hm1 as -> -> -> -> ->; do 5 eexists; split; [ exact Hm | exact Hf ].
Qed.

(** Given an argument, a description reads an open frame only where it
    did: a closed module keeps its location. *)
Lemma desc_reads_frame_at : forall Ξ R N R', mdesc_at R N = Some R' -> desc_reads_frame Ξ R' -> desc_reads_frame Ξ R.
Proof.
  intros Ξ R; induction R as [r A om | Δ Φ Φx | Θ0 p T Φ Ns | Θd A M Rm IH]; intros N R' Ha Hr; cbn in Ha.
  - destruct (pi_view A) as [[? ?] |]; [| discriminate ].
    destruct om as [M |]; [ destruct (fn_view M); [| discriminate ] |]; injection Ha as <-;
      destruct Hr as (? & ? & ? & ? & ? & Hm & _); discriminate.
  - destruct (tele_split (rev Δ)) as [[[? ?] ?] |]; [ injection Ha as <- | discriminate ].
    destruct Hr as (? & ? & ? & ? & ? & Hm & _); discriminate.
  - destruct Hr as (Θ' & p' & T' & Φ' & Ns' & Hm & Hf).
    destruct (tele_split (rev Θ0)) as [[[? ?] ?] | ?]; injection Ha as <-; cbn in Hm.
    all: injection Hm as _ <- _ _ _; do 5 eexists; split; [ reflexivity | exact Hf ].
  - destruct (mdesc_at Rm N) as [Rm' |] eqn:E; [| discriminate ].
    apply (proj2 (desc_reads_frame_dm _ _ _ _ _)); apply (IH _ _ E).
    destruct (tele_split (rev Θd)) as [[[? ?] ?] |]; injection Ha as <-; [ exact (proj1 (desc_reads_frame_dm _ _ _ _ _) Hr) | exact Hr ].
Qed.

Lemma desc_reads_frame_ats : forall Ξ Ns R R', mdesc_ats R Ns = Some R' -> desc_reads_frame Ξ R' -> desc_reads_frame Ξ R.
Proof.
  intros Ξ; induction Ns as [| N Ns IH]; intros * Ha Hr; cbn in Ha; [ injection Ha as <-; exact Hr |].
  destruct (mdesc_at R N) as [R1 |] eqn:E; [| discriminate ].
  exact (desc_reads_frame_at _ _ _ _ E (IH _ _ Ha Hr)).
Qed.

Lemma desc_reads_frame_ats_read : forall Ξ Ns R R', mdesc_ats_read R Ns = Some R' -> desc_reads_frame Ξ R' -> desc_reads_frame Ξ R.
Proof.
  intros * Ha Hr; destruct R as [| | | [| ? ?] A M Rm]; cbn [mdesc_ats_read] in Ha; try exact (desc_reads_frame_ats _ _ _ _ Ha Hr).
  destruct (mdesc_term_part_ats _ Ns) as [[? ? [?|] | | |] |]; try discriminate.
  destruct (mdesc_ats Rm Ns) as [Rm' |] eqn:E; [| discriminate ]; injection Ha as <-.
  apply (proj2 (desc_reads_frame_dm _ _ _ _ _)); exact (desc_reads_frame_ats _ _ _ _ E (proj1 (desc_reads_frame_dm _ _ _ _ _) Hr)).
Qed.

(** Naming a term keeps where module parts are stored. *)
Lemma desc_reads_frame_named : forall Ξ Θ Ns M R, desc_reads_frame Ξ (mdesc_named Θ Ns M R) <-> desc_reads_frame Ξ R.
Proof.
  intros *; unfold mdesc_named; destruct Θ, Ns; try reflexivity.
  all: destruct R as [? ? [|] | | |]; reflexivity.
Qed.

(** An alias whose target reads no open frame denotes a description
    reading none. *)
Lemma alias_frame_free_denote : forall Θ Ξ Γ Δ E R, ⊢ᵍ Θ ⍮ Ξ ->
    frame_free_target Θ Ξ (Δ ++ Γ) E -> udenote Θ Ξ Γ None (gu_mk Δ (md_alias E)) R -> ~ desc_reads_frame Ξ R.
Proof.
  intros * Hg (R1 & Hm1 & Hn) Hu Hr; inversion Hu; subst.
  match goal with Hm : mdenote _ _ _ E ?R0, Hmd : mdesc_mod ?R0 = Some ?R' |- _ =>
    rewrite <- (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm _ Hm1) in Hn;
    apply Hn; apply (desc_reads_frame_mod _ _ _ Hmd); exact (proj1 (desc_reads_frame_up _ _ _) Hr) end.
Qed.

(** What a well-formed unit denotes, read where it is written, reads no
    open frame: a body is an open description, and an alias's target reads
    none ([frame_free_target]). *)
Lemma wf_unit_frame_free : forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
    (forall R, udenote Θ Ξ Γ None U R -> ~ desc_reads_frame Ξ R) /\
    (forall R, udenote Θ Ξ Γ None U' R -> ~ desc_reads_frame Ξ R).
Proof.
  assert (Hbody : forall Θ Ξ Γ Δ sm Φ R, udenote Θ Ξ Γ None (gu_mk Δ (md_body sm Φ)) R -> ~ desc_reads_frame Ξ R).
  { intros * Hu (Θ' & p & T & Φ0 & Ns & Hm & _); inversion Hu; subst.
    match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => destruct sm; cbn in Hb; [ injection Hb as <- | discriminate ] end.
    cbn in Hm; discriminate. }
  induction 1.
  - split; intros R Hu; eapply Hbody; exact Hu.
  - assert (Hg : ⊢ᵍ Θ ⍮ Ξ) by exact (ctx_wf_gctx _ _ _ (presup_ext_eq_ctx H)).
    split; intros R Hu; (eapply alias_frame_free_denote; [ exact Hg | | exact Hu ]); eassumption.
  - assert (Hg : ⊢ᵍ Θ ⍮ Ξ) by exact (ctx_wf_gctx _ _ _ (presup_ext_eq_ctx H)).
    split; intros R Hu.
    + eapply alias_frame_free_denote; [ exact Hg | | exact Hu ]; eassumption.
    + destruct D as [sm Φ | E']; [ eapply Hbody; exact Hu |].
      (* the merged alias: its target is the literal's target *)
      match goal with Hff : frame_free_target _ _ _ (me_lit _) |- _ => destruct Hff as (R1 & Hm1 & Hn) end.
      inversion Hm1; subst; try (match goal with Hq : mod_qname _ = Some _ |- _ => cbn in Hq; discriminate end).
      match goal with Hu1 : udenote _ _ (Δ ++ Γ) None _ _ |- _ => inversion Hu1; subst end.
      inversion Hu; subst.
      match goal with Hm2 : mdenote _ _ ((Δ' ++ Δ) ++ Γ) E' ?R2, Hmd2 : mdesc_mod ?R2 = Some _,
                      Hm3 : mdenote _ _ (Δ' ++ Δ ++ Γ) E' ?R3, Hmd3 : mdesc_mod ?R3 = Some _ |- _ =>
        rewrite <- List.app_assoc in Hm2;
        pose proof (proj1 (mdenote_functional_all _ _ Hg) _ _ _ Hm2 _ Hm3) as <-;
        rewrite Hmd2 in Hmd3; injection Hmd3 as <- end.
      intros Hr; apply Hn; apply (proj2 (desc_reads_frame_up _ _ _)); exact (proj1 (desc_reads_frame_up _ _ _) Hr).
  - split; intros R Hu; eapply Hbody; exact Hu.
  - tauto.
  - tauto.
Qed.

Section DescOk.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** The arguments [Ns] fill, in order, the outermost parameters of the
      closed telescope [T], in [Γ]. *)
  #[warnings="-cannot-define-projection"]
  Record args_ok (Γ : ctx) (T : ctx) (Ns : list exp) : Prop := mk_args_ok
    { args_ok_rest : ctx
    ; args_ok_filled : ctx
    ; args_ok_split : T = args_ok_rest ++ args_ok_filled
    ; args_ok_length_field : length args_ok_filled = length Ns
    ; args_ok_ass : all_assumptions args_ok_filled
    ; args_ok_scoped : ctx_scoped 0 args_ok_filled
    ; args_ok_wf : ⊢ Θ ⍮ Ξ ⍮ args_ok_filled ++ Γ
    ; args_ok_args : forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts args_ok_filled Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊢ N : A }.

  (** [desc_ok Γ R]: the description [R] is typed in [Γ].  A term is of a
      type, its δ-reduct of that type; a term part with a module part is
      both, typed alike; an open module's expanded body is a well-formed
      extension, each of its module entries denoting typed descriptions, and
      its written body is a well-formed unit under its parameters; a closed module is
      stored, at a location of a past global context it grew from, and given
      typed arguments: so a description stays typed as the global context
      grows. *)
  Inductive desc_ok : ctx -> mdesc -> Prop :=
  (** A term of the kind [r]: its type is of the sort of [r] next to a
      large universe (a type of the universe, a proposition, or a type of
      levels), its δ-reduct of that type *)
  | desc_ok_term : forall Γ r A om i,
      Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort r Typeω@i ->
      (forall M, om = Some M -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A) ->
      desc_ok Γ (mdesc_term r A om)
  (** An open module: a well-formed expanded body whose module parts of
      entries (of modules and of definitions with a module part) denote
      typed descriptions, and a well-formed written body *)
  | desc_ok_open : forall Γ Δ Φw Φ param_level,
      ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ ++ Δ ++ Γ ->
      gm_noopen Φ ->
      (forall y Φ0 E U, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
         forall R, udenote Θ Ξ (body_ctx Φ0 ++ Δ ++ Γ) None U R -> desc_ok (body_ctx Φ0 ++ Δ ++ Γ) R) ->
      all_assumptions Δ -> body_shape Φ Φ -> List.NoDup (gm_names Φ) ->
      Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ gu_open nil Φw ≈ gu_open nil Φw ->
      (** The outer parameters are types of a universe: [param_level] is a
          level containing every parameter type; by cumulativity any common
          upper bound works *)
      params_evaluated Θ Ξ Γ Δ param_level ->
      (** Each definition, filled in, is of the sort of its kind next to a
          large universe *)
      (forall y Φ0 E A M σ, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
         gm_fill Φ0 = Some σ ->
         exists i, Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A[σ] : abs_kind_sort (entry_kind E) Typeω@i) ->
      (** Its entries can be read over the parameters: they are types of
          levels, or no entry has a type of levels *)
      desc_levels_abstractable Θ Ξ Γ Δ (mdesc_open nil Φw Φ) ->
      desc_ok Γ (mdesc_open Δ Φw Φ)
  (** A closed module: stored at a location of a past global context, given
      typed arguments *)
  | desc_ok_closed : forall Γ Θ' T Φ Ns Θ0 Ξ0 p param_level,
      ⊢ᵍ Θ0 ⍮ Ξ0 -> gc_sub Θ0 Ξ0 Θ Ξ -> loc Θ0 Ξ0 p T Φ ->
      all_assumptions T -> ctx_scoped 0 T -> ⊢ Θ ⍮ Ξ ⍮ T ->
      ⊢ Θ ⍮ Ξ ⍮ Θ' ++ Γ ->
      args_ok (Θ' ++ Γ) T Ns ->
      all_assumptions Θ' ->
      (** The outer parameters are types of a universe, as for
          [desc_ok_open] *)
      params_evaluated Θ Ξ Γ Θ' param_level ->
      (** Its entries can be read over the outer parameters, as for
          [desc_ok_open] *)
      desc_levels_abstractable Θ Ξ Γ Θ' (mdesc_closed nil p T Φ Ns) ->
      (** Abstracted over outer parameters, it is no module still being
          defined: an alias never names an open frame
          ([frame_free_target]) *)
      (Θ' <> nil -> gc_frame Ξ p = None) ->
      desc_ok Γ (mdesc_closed Θ' p T Φ Ns)
  (** A definition with a module part, or the type former of an inductive
      or a record type with its module, both parts over the outside
      parameters [Θd]: its term part is typed as a transparent
      definition's is, its type a type and its body of that type; its
      module part is a typed description there, abstracted over [Θd].  The
      two parts are abstracted alike, so filling [Θd]'s outermost parameter
      fills both: this is coherence between the two parts of a
      description, forced by [desc_ok_at], which types the argument at the
      module part's outermost parameter; it is no constraint on stored
      entries, whose two parts are checked apart.  Nothing else ties
      them. *)
  | desc_ok_dm : forall Γ Θd A M Rm param_level i,
      ⊢ Θ ⍮ Ξ ⍮ Θd ++ Γ ->
      all_assumptions Θd ->
      Θ ⍮ Ξ ⍮ Θd ++ Γ ⊢ A : Typeω@i ->
      Θ ⍮ Ξ ⍮ Θd ++ Γ ⊢ M : A ->
      desc_ok (Θd ++ Γ) Rm ->
      (** The outside parameters are types of a universe, as for
          [desc_ok_open]: the module part is abstracted over them *)
      params_evaluated Θ Ξ Γ Θd param_level ->
      (** The module part can be abstracted over them *)
      desc_levels_abstractable Θ Ξ Γ Θd (mdesc_dm nil A M Rm) ->
      (** Abstracted over them, it is no module still being defined, as
          for [desc_ok_closed] *)
      (Θd <> nil -> ~ desc_reads_frame Ξ Rm) ->
      desc_ok Γ (mdesc_dm Θd A M (mdesc_up Θd Rm)).

  Lemma args_ok_sub : forall Γ T Ns Γ' σ, args_ok Γ T Ns -> Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ : Γ ->
      args_ok Γ' T (List.map (fun M => M[σ]) Ns).
  Proof.
    intros * [T1 T2 -> Hl Ha Hs HT2 HN] Hσ.
    exists T1 T2; [ reflexivity | rewrite length_map; exact Hl | exact Ha | exact Hs
                   | rewrite <- (tele_sub_closed T2 σ Hs); eapply ctx_sub_wf_gen; eassumption |].
    intros k N A HNk HAk.
    rewrite List.nth_error_map in HNk; destruct (nth_error Ns k) as [N0 |] eqn:HN0; [| discriminate ]; injection HNk as <-.
    rewrite <- (tele_insts_sub T2 0 Id Id σ Ns Ha Hs ltac:(intros; lia)), List.nth_error_map in HAk.
    destruct (nth_error (tele_insts T2 Id Ns) k) as [A0 |] eqn:HA0; [| discriminate ]; injection HAk as <-.
    exact (sub_preserves_exp _ _ _ _ _ _ _ (HN _ _ _ HN0 HA0) Hσ).
  Qed.

  (** A typed description moves along a substitution. *)
  Lemma desc_ok_sub : ⊢ᵍ Θ ⍮ Ξ -> forall Γ R, desc_ok Γ R ->
      forall Γ' σ, Θ ⍮ Ξ ⍮ Γ' ⊢ˢ σ : Γ -> desc_ok Γ' (mdesc_sub R σ).
  Proof.
    intros Hg.
    induction 1 as [Γ r A om iA HA HM
                   | Γ Δ Φw Φ lΔ HΦ Hn Hent IH HaΔ Hsh Hnd HUw HRΔ Htg HLΔ
                   | Γ Θ' T Φ Ns Θ0 Ξ0 p lΘ Hg0 Hsub0 Hloc Ha Hs HT HΘ' Hargs HaΘ HRΘ HLΘ HFΘ
                   | Γ Θd A M Rm lΘ iA HΘd HaΘ HAt HM HRm IH HRΘd HLΘd HFΘd];
      intros Γ' σ Hσ.
    4: { (* a definition with a module part *)
         cbn [mdesc_sub]; rewrite mdesc_up_sub.
         assert (HΘ'' : ⊢ Θ ⍮ Ξ ⍮ tele_sub Θd σ ++ Γ') by (eapply ctx_sub_wf_gen; eassumption).
         assert (Hσq : Θ ⍮ Ξ ⍮ tele_sub Θd σ ++ Γ' ⊢ˢ sb_qn (length Θd) σ : Θd ++ Γ) by (apply wf_sub_ext; assumption).
         econstructor.
         - exact HΘ''.
         - apply all_assumptions_sub; exact HaΘ.
         - exact (sub_preserves_exp _ _ _ _ _ _ _ HAt Hσq).
         - exact (sub_preserves_exp _ _ _ _ _ _ _ HM Hσq).
         - exact (IH _ _ Hσq).
         - exact (params_evaluated_sub _ _ _ _ _ _ _ HRΘd Hσ HΘd HΘ'').
         - exact (desc_levels_abstractable_sub _ _ _ _ _ _ _ HLΘd Hσ HΘd HΘ'').
         - intros Hn Hr; apply HFΘd; [ intros ->; exact (Hn eq_refl) | exact (desc_reads_frame_sub _ _ _ Hr) ]. }
    all: cbn [mdesc_sub].
    - econstructor; [|].
      + pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA Hσ) as HAσ.
        rewrite type_sort_sub in HAσ by (apply type_sort_abs_kind; constructor); exact HAσ.
      + intros M HM'; destruct om as [M0 |]; cbn in HM'; [ injection HM' as <- | discriminate ].
        exact (sub_preserves_exp _ _ _ _ _ _ _ (HM M0 eq_refl) Hσ).
    - econstructor.
      10: exact (desc_levels_abstractable_sub _ _ _ _ _ _ _ HLΔ Hσ (ctx_app_wf_tail _ _ _ _ HΦ)
                   (ctx_sub_wf_gen _ _ _ _ _ _ Hσ (ctx_app_wf_tail _ _ _ _ HΦ))).
      8: exact (params_evaluated_sub _ _ _ _ _ _ _ HRΔ Hσ (ctx_app_wf_tail _ _ _ _ HΦ)
                  (ctx_sub_wf_gen _ _ _ _ _ _ Hσ (ctx_app_wf_tail _ _ _ _ HΦ))).
      4: apply all_assumptions_sub; exact HaΔ.
      4: apply body_shape_sub; exact Hsh.
      4: rewrite gm_names_sub; exact Hnd.
      4: { pose proof (sub_preserves_unit _ _ _ _ _ _ _ HUw
                         (wf_sub_ext _ _ _ _ _ _ Hσ
                            (ctx_sub_wf_gen _ _ _ _ _ _ Hσ (ctx_app_wf_tail _ _ _ _ HΦ))
                            (ctx_app_wf_tail _ _ _ _ HΦ))) as HU'.
           rewrite gunit_sub_mk in HU'; exact HU'. }
      + rewrite (body_ctx_sub _ _ (gm_noopen_nopens _ Hn)), List.app_assoc, <- tele_sub_app.
        eapply ctx_sub_wf_gen; [ exact Hσ | rewrite <- List.app_assoc; exact HΦ ].
      + apply gm_noopen_sub; exact Hn.
      + intros y Φ0' E' U' Hp' HE' R2 Hu2.
        rewrite gm_prefix_upto_sub in Hp'.
        destruct (gm_prefix_upto Φ y) as [Φ1 |] eqn:Hp; cbn in Hp'; [| discriminate ].
        destruct (gm_prefix_entry _ _ _ Hp) as (Φ0 & E & -> & _).
        cbn in Hp'; injection Hp' as <- <-.
        destruct (entry_unit_sub_inv _ _ _ HE') as (U & HE & ->).
        destruct (gm_prefix_body_ctx _ _ _ Hn Hp) as (Ψ & HΨ).
        pose proof (gm_prefix_upto_nopens _ _ _ Hp (gm_noopen_nopens _ Hn)) as Hn0; cbn [gm_nopens] in Hn0.
        rewrite HΨ in HΦ.
        pose proof (ctx_app_wf_tail _ _ _ _ ltac:(rewrite <- List.app_assoc in HΦ; exact HΦ)) as HΦ0.
        destruct (body_ext_unit_wf _ _ _ _ _ _ _ HΦ0 HE) as [HΓ0 HU].
        destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & [R HR] & _).
        set (σy := sb_qn (length (body_ctx Φ0 ++ Δ)) σ).
        assert (HΓ0' : ⊢ Θ ⍮ Ξ ⍮ tele_sub (body_ctx Φ0 ++ Δ) σ ++ Γ')
          by (eapply ctx_sub_wf_gen; [ exact Hσ | rewrite <- List.app_assoc; exact HΓ0 ]).
        assert (Hσy : Θ ⍮ Ξ ⍮ tele_sub (body_ctx Φ0 ++ Δ) σ ++ Γ' ⊢ˢ σy : (body_ctx Φ0 ++ Δ) ++ Γ)
          by (apply wf_sub_ext; [ exact Hσ | exact HΓ0' | rewrite <- List.app_assoc; exact HΓ0 ]).
        destruct (wf_unit_eq_scoped _ _ _ _ _ HU) as (HΓs & HUs & _).
        pose proof (proj1 (proj2 (mdenote_sub_all _ _ (wf_gstack_closed _ _ Hg))) _ _ _ _ HR _
                      (slots_ok_ctx _ HΓs) (or_introl HUs) _ _
                      (wf_sub_mod_compat _ _ _ _ _ ltac:(rewrite <- List.app_assoc in Hσy; exact Hσy))) as HRs.
        rewrite tele_sub_app, <- List.app_assoc in HRs.
        replace (U[σy]ᵘ) with (gunit_sub U (sb_qn (gm_binders Φ0) (sb_qn (length Δ) σ))) in HRs
          by (unfold σy; rewrite List.length_app, (length_body_ctx _ Hn0), sb_qn_plus; reflexivity).
        rewrite <- (body_ctx_sub _ _ Hn0) in HRs.
        pose proof (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ HRs _ Hu2) as <-.
        eapply (IH y Φ0 E U ltac:(exact Hp) HE R HR).
        rewrite (body_ctx_sub _ _ Hn0); rewrite tele_sub_app in Hσy; rewrite <- !List.app_assoc in Hσy; exact Hσy.
      + (* the definitions, filled in, at the sorts of their tags *)
        intros y Φ0w Ew Aw Mw σw Hpw HEw Hfw.
        destruct (gm_prefix_sub_inv _ _ _ _ _ Hpw) as (Φ0 & E & Hp0 & -> & ->).
        destruct (entry_tm_sub_inv _ _ _ _ HEw) as (A & M & HE & -> & ->).
        destruct (gm_fill Φ0) as [σf |] eqn:Hf0;
          [| apply (proj2 (gm_fill_sub_none Φ0 (sb_qn (length Δ) σ))) in Hf0; congruence ].
        destruct (gm_fill_sub Φ0 (length Δ) σ σf Hf0) as (τ & Hτ & Heq); rewrite Hτ in Hfw; injection Hfw as <-.
        rewrite (fill_sub_exp _ _ _ _ _ _ Heq).
        replace (entry_kind (gentry_sub E _)) with (entry_kind E) by (destruct E; reflexivity).
        destruct (Htg _ _ _ _ _ _ Hp0 HE Hf0) as (i & Hi); exists i.
        pose proof (sub_preserves_exp _ _ _ _ _ _ _ Hi
                      (wf_sub_ext _ _ _ _ _ _ Hσ
                         (ctx_sub_wf_gen _ _ _ _ _ _ Hσ (ctx_app_wf_tail _ _ _ _ HΦ))
                         (ctx_app_wf_tail _ _ _ _ HΦ))) as Hs.
        rewrite type_sort_sub in Hs by (apply type_sort_abs_kind; constructor); exact Hs.
    - assert (HΘ'' : ⊢ Θ ⍮ Ξ ⍮ tele_sub Θ' σ ++ Γ') by (eapply ctx_sub_wf_gen; eassumption).
      econstructor; [ exact Hg0 | exact Hsub0 | exact Hloc | exact Ha | exact Hs | exact HT | exact HΘ'' | | apply all_assumptions_sub; exact HaΘ
                    | exact (params_evaluated_sub _ _ _ _ _ _ _ HRΘ Hσ HΘ' HΘ'')
                    | exact (desc_levels_abstractable_sub _ _ _ _ _ _ _ HLΘ Hσ HΘ' HΘ'')
                    | intros Hn; apply HFΘ; intros ->; exact (Hn eq_refl) ].
      eapply args_ok_sub; [ exact Hargs | apply wf_sub_ext; assumption ].
  Qed.

  (** One more argument, for the next parameter. *)
  Lemma args_ok_snoc : forall Γ T Ns C T1' N, args_ok Γ T Ns -> all_assumptions T -> ctx_scoped 0 T -> ⊢ Θ ⍮ Ξ ⍮ T ->
      tele_view (List.firstn (length T - length Ns) T) = Some (C, T1') ->
      Θ ⍮ Ξ ⍮ Γ ⊢ N : C[sb_of_list Id Ns] -> args_ok Γ T (Ns ++ N :: nil).
  Proof.
    intros * [T1 T2 -> Hl Ha2 Hs2 HT2 HN] Ha Hs HT Hv HN0.
    replace (firstn (length (T1 ++ T2) - length Ns) (T1 ++ T2)) with T1 in Hv
      by (rewrite List.length_app, <- Hl, Nat.add_sub, List.firstn_app, Nat.sub_diag, List.firstn_O, List.app_nil_r, List.firstn_all; reflexivity).
    apply List.Forall_app in Ha as [Ha1 _].
    destruct (tele_view_ass _ _ _ Ha1 Hv) as (κC & ->).
    rewrite <- List.app_assoc in Hs, HT; cbn [List.app] in Hs, HT.
    assert (Hs' : ctx_scoped 0 (ce_ass κC C :: T2)) by (apply ctx_scoped_app_iff in Hs as [_ Hs]; exact Hs).
    exists T1' (ce_ass κC C :: T2).
    - rewrite <- List.app_assoc; reflexivity.
    - cbn; rewrite List.length_app, Hl; cbn; lia.
    - constructor; [ eauto | exact Ha2 ].
    - exact Hs'.
    - apply closed_tele_wf; [ exact Hs' | exact (ctx_app_wf_tail _ _ _ _ HT) | exact (ctx_app_wf_tail _ _ _ _ HT2) ].
    - intros k N1 A HNk HAk.
      change (ce_ass κC C :: T2) with ((ce_ass κC C :: nil) ++ T2) in HAk.
      rewrite tele_insts_app in HAk by (first [ exact Ha2 | lia ]).
      destruct (Nat.lt_ge_cases k (length Ns)) as [Hk | Hk].
      + rewrite List.nth_error_app1 in HNk by exact Hk.
        rewrite List.nth_error_app1 in HAk by (rewrite length_tele_insts by exact Ha2; lia).
        exact (HN _ _ _ HNk HAk).
      + rewrite List.nth_error_app2 in HNk by exact Hk.
        rewrite List.nth_error_app2 in HAk by (rewrite length_tele_insts by exact Ha2; lia).
        rewrite length_tele_insts in HAk by exact Ha2.
        rewrite <- Hl, Nat.min_id in HAk; rewrite <- Hl in HNk.
        destruct (k - length T2) as [| k'] eqn:Ek; cbn in HNk, HAk; [| destruct k'; discriminate ].
        injection HNk as <-; injection HAk as <-; exact HN0.
  Qed.

  Lemma sb_of_list_map_agree : forall Ns τ x, x < length Ns ->
      (sb_of_list Id Ns ⨟ τ) x = sb_of_list Id (List.map (fun M => M[τ]) Ns) x.
  Proof.
    intros * Hx; unfold sb_compose.
    rewrite (sb_of_list_nth _ _ _ a_prop Hx), (sb_of_list_nth _ _ _ a_prop[τ]) by (rewrite length_map; exact Hx).
    rewrite length_map, (List.map_nth (fun M => M[τ])); reflexivity.
  Qed.

  (** Supplying the next parameter of a module part over the outside
      parameters [Θ'] and the arguments [Ns] of a closed telescope [T]: an
      outside parameter, past the definitions and modules outside it, or
      else the next parameter of [T]. *)
  Lemma args_at : forall Γ Θ' T Ns B T1 N,
      all_assumptions T -> ctx_scoped 0 T -> ⊢ Θ ⍮ Ξ ⍮ T -> ⊢ Θ ⍮ Ξ ⍮ Θ' ++ Γ -> args_ok (Θ' ++ Γ) T Ns ->
      tele_view (tele_sub (List.firstn (length T - length Ns) T) (sb_of_list Id Ns) ++ Θ') = Some (B, T1) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ N : B ->
      match tele_split (rev Θ') with
      | inl (_, Θ'', τ) =>
          ⊢ Θ ⍮ Ξ ⍮ tele_sub Θ'' (Id,,N) ++ Γ /\
          args_ok (tele_sub Θ'' (Id,,N) ++ Γ) T (List.map (fun M => M[τ ⨟ sb_qn (length Θ'') (Id,,N)]) Ns)
      | inr τ => args_ok Γ T (List.map (fun M => M[τ]) Ns ++ N :: nil)
      end.
  Proof.
    intros * Ha Hs HT HΘ' Hargs Hv HN.
    unfold tele_view in Hv; rewrite List.rev_app_distr in Hv.
    pose proof (tele_split_wf _ _ (rev Θ') Γ ltac:(rewrite rev_involutive; exact HΘ')) as Hsw.
    rewrite rev_involutive in Hsw.
    destruct (tele_split (rev Θ')) as [[[B' Θ''] τ] | τ] eqn:Es.
    - destruct (tele_open_app_inl _ (rev (tele_sub (List.firstn (length T - length Ns) T) (sb_of_list Id Ns))) _ _ _ Es) as (T' & Ho).
      rewrite Ho in Hv; injection Hv as <- _.
      destruct Hsw as (_ & HΘ'' & Hτ).
      destruct (ctx_decomp_kind (ctx_app_wf_tail _ _ _ _ HΘ'')) as (Srt & HS & HB).
      pose proof (wf_sub_single _ _ _ _ _ _ _ HB HS HN) as Hs1.
      assert (HΘN : ⊢ Θ ⍮ Ξ ⍮ tele_sub Θ'' (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
      split; [ exact HΘN |].
      eapply args_ok_sub; [ exact Hargs |].
      eapply wf_sub_compose; [ exact Hτ | apply wf_sub_ext; assumption ].
    - destruct (tele_open_app_inr _ _ _ _ _ Es Hv) as (B0 & T0 & Ho & ->).
      fold (tele_view (tele_sub (List.firstn (length T - length Ns) T) (sb_of_list Id Ns))) in Ho.
      rewrite tele_view_sub in Ho.
      destruct (tele_view (List.firstn (length T - length Ns) T)) as [[C T1'] |] eqn:HvC; cbn in Ho; [| discriminate ].
      injection Ho as <- _.
      pose proof (args_ok_sub _ _ _ _ _ Hargs Hsw) as Hargs'.
      eapply args_ok_snoc; [ exact Hargs' | exact Ha | exact Hs | exact HT | rewrite length_map; exact HvC |].
      rewrite exp_sub_sub in HN.
      destruct Hargs as [T1x T2 -> Hl _ _ _ _].
      replace (firstn (length (T1x ++ T2) - length Ns) (T1x ++ T2)) with T1x in HvC
        by (rewrite List.length_app, <- Hl, Nat.add_sub, List.firstn_app, Nat.sub_diag, List.firstn_O, List.app_nil_r, List.firstn_all; reflexivity).
      apply List.Forall_app in Ha as [Ha1 _].
      destruct (tele_view_ass _ _ _ Ha1 HvC) as (κC & ->).
      rewrite <- List.app_assoc in Hs; cbn [List.app] in Hs.
      apply ctx_scoped_app_iff in Hs as [_ Hs]; cbn in Hs; destruct Hs as [HC _].
      rewrite Hl, Nat.add_0_r in HC.
      erewrite exp_scoped_sub_agree; [ exact HN | exact HC |].
      intros; symmetry; apply sb_of_list_map_agree; assumption.
  Qed.

  Lemma desc_ok_up : forall Γ Θ'' R l, desc_ok (Θ'' ++ Γ) R -> ⊢ Θ ⍮ Ξ ⍮ Θ'' ++ Γ -> all_assumptions Θ'' ->
      up_evaluated Θ Ξ Γ Θ'' R l -> desc_ok Γ (mdesc_up Θ'' R).
  Proof.
    intros Γ Θ'' R l HR HΘ HaΘ HRΘ; inversion HR; subst; cbn [mdesc_up]; cbn [up_evaluated] in HRΘ.
    all: try match goal with HL : desc_levels_abstractable _ _ (_ ++ _) _ _ |- _ => rename HL into HL1 end.
    4: { (* a definition with a module part: both parts abstracted further *)
         destruct HRΘ as (HRp & HL2 & HF2).
         rewrite <- mdesc_up_cat.
         econstructor; [ rewrite <- List.app_assoc; assumption | apply List.Forall_app; split; assumption
                       | rewrite <- List.app_assoc; eassumption .. | apply params_evaluated_app; eassumption | |].
         - destruct HL2 as [HL2 | HN2]; [ destruct HL1 as [HL1 | HN1] |].
           + left; exact (level_sorted_app _ _ HL1 HL2).
           + right; rewrite <- List.app_assoc; exact HN1.
           + right; inversion HN2; subst; constructor; intros Rm' HRm'.
             match goal with Hm : forall _, mdesc_mod (mdesc_up ?Θd _) = Some _ -> _ |- _ =>
               pose proof (Hm (mdesc_up Θd Rm') ltac:(rewrite mdesc_mod_up, HRm'; reflexivity)) as HN end.
             rewrite <- List.app_assoc; exact (proj1 (no_level_up_mod _ _ _ _ _ (mdesc_mod_is_mod _ _ HRm')) HN).
         - (* over the outer parameters too, it is no module still being defined *)
           intros Hn Hr; destruct Θ'' as [| e Θ1].
           + rewrite List.app_nil_r in Hn.
             match goal with HF1 : _ <> nil -> ~ desc_reads_frame _ _ |- _ => exact (HF1 Hn Hr) end.
           + apply HF2; [ discriminate |]; apply (proj2 (desc_reads_frame_dm _ _ _ _ _)), (proj2 (desc_reads_frame_up _ _ _)).
             exact Hr. }
    2: { (* an open module: its parameters extended *)
         destruct HRΘ as (HRp & HL2 & _).
         eapply desc_ok_open;
           [ rewrite <- !List.app_assoc; eassumption | eassumption | rewrite <- !List.app_assoc; eassumption
           | apply List.Forall_app; split; assumption | eassumption | eassumption
           | rewrite <- !List.app_assoc; eassumption | apply params_evaluated_app; eassumption
           | rewrite <- !List.app_assoc; eassumption |].
         destruct HL2 as [HL2 | HN2]; [ destruct HL1 as [HL1 | HN1] |].
         - left; exact (level_sorted_app _ _ HL1 HL2).
         - right; rewrite <- List.app_assoc; exact HN1.
         - right; eapply no_level_open_shift; [| exact HN2 ]; rewrite <- List.app_assoc; reflexivity. }
    2: { (* a closed module: its outer parameters extended *)
         destruct HRΘ as (HRp & HL2 & HF2).
         eapply desc_ok_closed;
           [ eassumption .. | rewrite <- !List.app_assoc; eassumption | rewrite <- !List.app_assoc; eassumption
           | apply List.Forall_app; split; assumption | apply params_evaluated_app; eassumption | |].
         - destruct HL2 as [HL2 | HN2]; [ destruct HL1 as [HL1 | HN1] |].
           + left; exact (level_sorted_app _ _ HL1 HL2).
           + right; eapply no_level_closed_any; exact HN1.
           + right; eapply no_level_closed_any; exact HN2.
         - (* over the outer parameters too, it is no module still being defined *)
           intros Hn; destruct Θ'' as [| e Θ1].
           + rewrite List.app_nil_r in Hn.
             match goal with HF1 : _ <> nil -> gc_frame _ _ = None |- _ => exact (HF1 Hn) end.
           + destruct (gc_frame Ξ p) eqn:Ef; [| reflexivity ].
             exfalso; apply HF2; [ discriminate |]; do 5 eexists; split; [ reflexivity | rewrite Ef; discriminate ]. }
    (* a term: its type a [Π] over the parameters, at its kind *)
    match goal with HA : _ ⍮ _ ⍮ _ ⊢ _ : abs_kind_sort _ Typeω@_,
                    HM : forall M, _ = Some M -> _ |- _ => rename HA into HAt, HM into HMt end.
    destruct HRΘ as [HL2 | HN2].
    - destruct (ctx_pi_type_kind _ _ _ _ _ _ _ HΘ (fun _ => HaΘ) (fun _ => HL2) HAt) as [[j Hty] Hfn].
      econstructor; [ exact Hty |].
      intros M HM'; destruct om as [M0 |]; cbn in HM'; [ injection HM' as <- | discriminate ].
      exact (Hfn _ (HMt M0 eq_refl)).
    - inversion HN2; subst.
      match goal with HAi : _ ⍮ _ ⍮ _ ⊢ _ : abs_kind_sort _ Typeω@_, Hr : _ <> ak_level |- _ =>
        destruct (ctx_pi_type _ _ _ _ _ _ _ Hr HΘ HAi) as [[j Hty] Hfn] end.
      econstructor; [ exact Hty |].
      intros M HM'; destruct om as [M0 |]; cbn in HM'; [ injection HM' as <- | discriminate ].
      exact (Hfn _ (HMt M0 eq_refl)).
  Qed.

  (** An open description read in the context extended by its parameters. *)
  Lemma desc_ok_open_root : forall Γ Δ Φw Φ, all_assumptions Δ -> desc_ok Γ (mdesc_open Δ Φw Φ) -> desc_ok (Δ ++ Γ) (mdesc_open nil Φw Φ).
  Proof.
    intros * Ha H; inversion H; subst; eapply desc_ok_open with (param_level := 0); cbn [List.app] in *;
      first [ eassumption | apply params_evaluated_nil | apply desc_levels_abstractable_nil | constructor ].
  Qed.

  (** Back, the parameters being relevant and the entries readable over
      them. *)
  Lemma desc_ok_open_unroot : forall Γ Δ Φw Φ l, all_assumptions Δ -> params_evaluated Θ Ξ Γ Δ l ->
      desc_levels_abstractable Θ Ξ Γ Δ (mdesc_open nil Φw Φ) ->
      desc_ok (Δ ++ Γ) (mdesc_open nil Φw Φ) -> desc_ok Γ (mdesc_open Δ Φw Φ).
  Proof.
    intros * Ha HR HL H; inversion H; subst; econstructor; cbn [List.app] in *; first [ eassumption | constructor ].
  Qed.

  Lemma desc_ok_closed_root : forall Γ Θ' p T Φ Ns, all_assumptions Θ' -> desc_ok Γ (mdesc_closed Θ' p T Φ Ns) -> desc_ok (Θ' ++ Γ) (mdesc_closed nil p T Φ Ns).
  Proof.
    intros * Ha H; inversion H; subst; eapply desc_ok_closed with (param_level := 0); cbn [List.app] in *;
      first [ eassumption | apply params_evaluated_nil | apply desc_levels_abstractable_nil | constructor
            | let Hne := fresh "Hne" in intros Hne; contradiction (Hne eq_refl) ].
  Qed.

  Lemma desc_ok_closed_unroot : forall Γ Θ' p T Φ Ns l, all_assumptions Θ' -> params_evaluated Θ Ξ Γ Θ' l ->
      desc_levels_abstractable Θ Ξ Γ Θ' (mdesc_closed nil p T Φ Ns) ->
      (Θ' <> nil -> gc_frame Ξ p = None) ->
      desc_ok (Θ' ++ Γ) (mdesc_closed nil p T Φ Ns) -> desc_ok Γ (mdesc_closed Θ' p T Φ Ns).
  Proof. intros * Ha HR HL HF H; inversion H; subst; econstructor; cbn [List.app] in *; first [ eassumption | constructor ]. Qed.

  (** "R at N", where the module part of [R] takes a parameter [N] fills. *)
  Lemma desc_ok_at : ⊢ᵍ Θ ⍮ Ξ -> forall Γ R T B T1 N R',
      desc_ok Γ R -> mdesc_mod_tele R = Some T -> tele_view T = Some (B, T1) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ N : B -> mdesc_at R N = Some R' -> desc_ok Γ R'.
  Proof.
    intros Hg Γ R T B T1 N R' HR; revert T B T1 N R'.
    induction HR as [Γ r A om iA HA HM
                    | Γ Δ Φw Φ lΔ HΦ Hn Hent IHent HaΔ Hsh Hnd HUw HRΔ Htg HLΔ
                    | Γ Θ' T0 Φ Ns Θ0 Ξ0 p lΘ Hg0 Hsub0 Hloc Ha0 Hs0 HT0 HΘ' Hargs HaΘ HRΘ HLΘ HFΘ
                    | Γ Θd A M Rm lΘ iA HΘd HaΘd HBt HMt HRm IH HRΘd HLΘd HFΘd];
      intros T B T1 N R' Ht Hv HN Ha.
    4: { (* a definition with a module part: the outside parameter, when
            there is one, is filled in both parts *)
      pose proof (mdesc_mod_tele_up_inv _ _ _ Ht) as (T2 & ->).
      unfold mdesc_mod_tele in Ht; cbn [mdesc_mod] in Ht; fold (mdesc_mod_tele (mdesc_up Θd Rm)) in Ht.
      cbn [mdesc_at] in Ha.
      destruct (mdesc_at (mdesc_up Θd Rm) N) as [Rm' |] eqn:Eat; [| discriminate ].
      assert (HΘc : Θd = nil \/ exists Θ0 e0, Θd = Θ0 ++ e0 :: nil)
        by (destruct Θd as [| e Θr]; [ left; reflexivity |];
            right; destruct (List.exists_last (l := e :: Θr)) as (Θ0 & e0 & E); [ discriminate | eauto ]).
      destruct HΘc as [-> | (Θ0 & e0 & ->)].
      - (* none: the module part only *)
        cbn in Ha; injection Ha as <-.
        rewrite mdesc_up_nil in Ht, Eat; cbn [List.app] in *.
        exact (IH _ _ _ _ _ Ht Hv HN Eat).
      - unfold all_assumptions in HaΘd; apply List.Forall_app in HaΘd as [Ha1 He];
          apply List.Forall_cons_iff in He as [(κX & X & ->) _].
        unfold tele_view in Hv; rewrite !rev_app_distr in Hv; cbn in Hv; injection Hv as <- _.
        rewrite mdesc_at_up in Eat; injection Eat as <-.
        rewrite rev_app_distr in Ha; cbn [rev List.app tele_split] in Ha; rewrite rev_involutive in Ha; injection Ha as <-.
        destruct (params_evaluated_app_inv _ _ _ _ _ _ HRΘd) as [HRΘ0 _].
        pose proof (desc_levels_abstractable_app_inv _ _ _ _ _ _ HLΘd) as HLΘ0.
        rewrite <- List.app_assoc in HΘd, HBt, HMt, HRm; cbn [List.app] in HΘd, HBt, HMt, HRm, HRΘ0, HLΘ0.
        destruct (ctx_decomp_sort_kind (ctx_app_wf_tail _ _ _ _ HΘd)) as [HΓ (Srt & HS & HX)].
        pose proof (wf_sub_single _ _ _ _ _ _ _ HX HS HN) as Hs1.
        assert (HΘN : ⊢ Θ ⍮ Ξ ⍮ tele_sub Θ0 (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
        assert (Hσ : Θ ⍮ Ξ ⍮ tele_sub Θ0 (Id,,N) ++ Γ ⊢ˢ sb_qn (length Θ0) (Id,,N) : Θ0 ++ ce_ass κX X :: Γ)
          by (apply wf_sub_ext; assumption).
        assert (Hq : sb_eq (Id ⨟ sb_qn (length Θ0) (Id,,N)) (sb_qn (length Θ0) (Id,,N)))
          by (rewrite sb_compose_id_left; reflexivity).
        rewrite (exp_sub_sb_eq A _ _ Hq), (exp_sub_sb_eq M _ _ Hq).
        econstructor.
        + exact HΘN.
        + apply all_assumptions_sub; exact Ha1.
        + exact (sub_preserves_exp _ _ _ _ _ _ _ HBt Hσ).
        + exact (sub_preserves_exp _ _ _ _ _ _ _ HMt Hσ).
        + exact (desc_ok_sub Hg _ _ HRm _ _ Hσ).
        + exact (params_evaluated_sub _ _ _ _ _ _ _ HRΘ0 Hs1 HΘd HΘN).
        + exact (desc_levels_abstractable_sub _ _ _ _ _ _ _ HLΘ0 Hs1 HΘd HΘN).
        + intros _ Hr; apply HFΘd; [ destruct Θ0; discriminate | exact (desc_reads_frame_sub _ _ _ Hr) ]. }
    all: unfold mdesc_mod_tele in Ht; cbn in Ht, Ha; unfold mdesc_tele in Ht.
    - discriminate.
    - (* an open module *)
      injection Ht as <-.
      unfold tele_view in Hv; destruct (tele_open_split _ _ _ Hv) as (τ & Es).
      rewrite Es in Ha; injection Ha as <-.
      pose proof (tele_split_wf Θ Ξ (rev Δ) Γ) as Hsw; rewrite rev_involutive, Es in Hsw.
      destruct (Hsw ltac:(eapply ctx_app_wf_tail; exact HΦ)) as (_ & HT1 & Hτ).
      destruct (ctx_decomp_kind (ctx_app_wf_tail _ _ _ _ HT1)) as (Srt & HS & HB).
      pose proof (wf_sub_single _ _ _ _ _ _ _ HB HS HN) as Hs1.
      assert (HT1N : ⊢ Θ ⍮ Ξ ⍮ tele_sub T1 (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
      assert (HσN : Θ ⍮ Ξ ⍮ tele_sub T1 (Id,,N) ++ Γ ⊢ˢ τ ⨟ sb_qn (length T1) (Id,,N) : Δ ++ Γ)
        by (eapply wf_sub_compose; [ exact Hτ | apply wf_sub_ext; assumption ]).
      assert (HaT1 : all_assumptions (tele_sub T1 (Id,,N)))
        by (apply all_assumptions_sub; exact (tele_split_ass _ _ _ _ HaΔ Es)).
      (* the inner parameters, relevant over the outermost, moved by [N] *)
      destruct (tele_split_ass_eq _ _ _ _ HaΔ Es) as [EΔ _].
      assert (HRT1 : params_evaluated Θ Ξ Γ (tele_sub T1 (Id,,N)) lΔ).
      { rewrite EΔ in HRΔ; destruct (params_evaluated_app_inv _ _ _ _ _ _ HRΔ) as [HR1 _].
        eapply params_evaluated_sub; [ exact HR1 | exact Hs1 | exact HT1 | exact HT1N ]. }
      assert (HLT1 : desc_levels_abstractable Θ Ξ Γ (tele_sub T1 (Id,,N))
                       (mdesc_sub (mdesc_open nil Φw Φ) (τ ⨟ sb_qn (length T1) (Id,,N)))).
      { destruct (tele_split_ass_eq _ _ _ _ HaΔ Es) as [EΔ' ->].
        rewrite (mdesc_sub_sb_eq _ _ _ (sb_compose_id_left _)).
        rewrite EΔ' in HLΔ; apply desc_levels_abstractable_app_inv in HLΔ; cbn [List.app] in HLΔ.
        exact (desc_levels_abstractable_sub _ _ _ _ _ _ _ HLΔ Hs1 HT1 HT1N). }
      apply (desc_ok_open_unroot _ _ _ _ _ HaT1 HRT1 HLT1).
      assert (HR : desc_ok Γ (mdesc_open Δ Φw Φ)) by (econstructor; eassumption).
      apply (desc_ok_open_root _ _ _ _ HaΔ) in HR.
      exact (desc_ok_sub Hg _ _ HR _ _ HσN).
    - (* a closed module *)
      destruct (Nat.leb (length Ns) (length T0)); [| discriminate ]; injection Ht as <-.
      pose proof (args_at _ _ _ _ _ _ _ Ha0 Hs0 HT0 HΘ' Hargs Hv HN) as Hat.
      destruct (tele_split (rev Θ')) as [[[B' Θ''] τ] | τ] eqn:Es; injection Ha as <-.
      + destruct Hat as [HΘN HargsN].
        destruct (tele_split_ass_eq _ _ _ _ HaΘ Es) as [EΘ _].
        assert (HRΘ'' : params_evaluated Θ Ξ Γ (tele_sub Θ'' (Id,,N)) lΘ).
        { rewrite EΘ in HRΘ, HΘ'; destruct (params_evaluated_app_inv _ _ _ _ _ _ HRΘ) as [HR1 HRB].
          rewrite <- List.app_assoc in HΘ'; cbn [List.app] in HΘ'.
          destruct (ctx_decomp_sort_kind (ctx_app_wf_tail _ _ _ _ HΘ')) as [HΓ (SB & HSB & HB')].
          eapply params_evaluated_sub; [ exact HR1 | | exact HΘ' | exact HΘN ].
          eapply wf_sub_single; [ exact HB' | exact HSB |].
          (* the argument is at the outermost of the outer parameters *)
          rewrite EΘ, List.app_assoc in Hv; unfold tele_view in Hv; rewrite List.rev_app_distr in Hv; cbn in Hv.
          injection Hv as <- _; exact HN. }
        eapply desc_ok_closed; try eassumption.
        * apply all_assumptions_sub; exact (tele_split_ass _ _ _ _ HaΘ Es).
        * destruct HLΘ as [HL | HNc]; [ left | right; eapply no_level_closed_any; exact HNc ].
          rewrite EΘ in HL; destruct (level_sorted_app_inv _ _ HL) as [HL1 _].
          exact (level_sorted_parameters_sub _ _ HL1).
        * intros _; apply HFΘ; rewrite EΘ; destruct Θ''; discriminate.
      + eapply desc_ok_closed with (param_level := 0); try eassumption;
          [ cbn [List.app]; eapply ctx_app_wf_tail; exact HΘ' | constructor | apply params_evaluated_nil
          | apply desc_levels_abstractable_nil | let Hne := fresh "Hne" in intros Hne; contradiction (Hne eq_refl) ].
  Qed.

  (** The module part. *)
  Lemma desc_ok_mod : ⊢ᵍ Θ ⍮ Ξ -> forall Γ R Rm, desc_ok Γ R -> mdesc_mod R = Some Rm -> desc_ok Γ Rm.
  Proof.
    intros Hg Γ R Rm HR; revert Rm.
    induction HR as [| | | Γ Θd A M Rm lΘ iA HΘd HaΘd _ _ HRm IH HRΘd HLΘd HFΘd]; intros Rm0 Hm.
    4: { (* a definition with a module part: its module part *)
         cbn [mdesc_mod] in Hm; rewrite mdesc_mod_up in Hm.
         destruct (mdesc_mod Rm) as [R1 |] eqn:E; cbn [option_map] in Hm; [ injection Hm as <- | discriminate ].
         apply (desc_ok_up _ _ _ lΘ); [ exact (IH _ eq_refl) | exact HΘd | exact HaΘd |].
         apply up_evaluated_of; [ exact HRΘd | exact (desc_levels_abstractable_dm_mod _ _ _ _ _ _ _ _ _ HLΘd E) |].
         intros Hn Hr; exact (HFΘd Hn (desc_reads_frame_mod _ _ _ E Hr)). }
    all: try (cbn in Hm; discriminate); try (cbn in Hm; injection Hm as <-; econstructor; eassumption).
  Qed.

  (** An entry of an open module: a definition is typed by the extension the
      body is, a module entry by the clause for it; the entries before it are
      filled in by a well-typed substitution. *)
  Lemma desc_ok_entry_open : ⊢ᵍ Θ ⍮ Ξ -> forall Γ Δ Φw Φ y Γy E rd R R',
      desc_ok Γ (mdesc_open Δ Φw Φ) -> mdesc_entry (mdesc_open Δ Φw Φ) y = Some (Γy, E, rd) ->
      edenote Θ Ξ (Γy ++ Γ) None E R -> mdesc_read rd R = Some R' -> desc_ok Γ R'.
  Proof.
    intros Hg * HR He Hed Hr; inversion HR as [| Γ0 Δ0 Φw0 Φ0 lΔ HΦ Hn Hent HaΔ Hsh Hnd HUw HRΔ Htg HLΔ | |]; subst.
    cbn in He; destruct (gm_prefix_upto Φ y) as [[| Φ1 x E1 | ? ? ?] |] eqn:Hp; try discriminate.
    destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & _).
    destruct (gm_prefix_body_ctx _ _ _ Hn Hp) as (Ψ & HΨ).
    rewrite HΨ in HΦ.
    assert (HΦ1 : ⊢ Θ ⍮ Ξ ⍮ body_ctx (Φ1 ⊳ y ↦ E1) ++ Δ ++ Γ)
      by (eapply ctx_app_wf_tail; rewrite <- List.app_assoc in HΦ; exact HΦ).
    assert (HΦ1' : ⊢ Θ ⍮ Ξ ⍮ body_ctx Φ1 ++ Δ ++ Γ)
      by (destruct E1 as [? ? ? ? [] | | | | ]; cbn [body_ctx List.app] in HΦ1; eauto using ctx_decomp_tail).
    destruct E1 as [[|] pv ra A [M |] | pv U | | pv A M U | ]; try discriminate; injection He as <- <- <-; cbn in Hr.
    all: destruct (gm_fill Φ1) as [σ |] eqn:Hf; cbn in Hr; [ injection Hr as <- | discriminate ].
    all: pose proof (wf_gm_fill _ _ _ _ _ HΦ1' Hf) as Hσ.
    all: apply (desc_ok_up _ _ _ lΔ); [| exact (wf_sub_dom _ _ _ _ _ Hσ) | exact HaΔ | apply up_evaluated_of; [ exact HRΔ | |] ].
    (* the entry is no module still being defined: a module entry's unit
       is well formed where it is, and a definition is no module *)
    all: try (match goal with |- _ <> nil -> ~ desc_reads_frame _ _ =>
      let Hn := fresh "Hn" in let Hr0 := fresh "Hr0" in
      intros Hn Hr0; apply desc_reads_frame_sub in Hr0; rewrite <- List.app_assoc in Hed; inversion Hed; subst;
      first
      [ destruct Hr0 as (? & ? & ? & ? & ? & Hm0 & _); cbn in Hm0; discriminate
      | match goal with Hu : udenote _ _ _ None ?U _ |- _ =>
          cbn [body_ctx List.app] in HΦ1;
          let HU0 := fresh "HU0" in
          first [ destruct (ctx_decomp_mod HΦ1) as [_ HU0] | destruct (ctx_decomp_dm HΦ1) as (_ & _ & _ & HU0) ];
          first [ exact (proj1 (wf_unit_frame_free _ _ _ _ _ HU0) _ Hu Hr0)
                | exact (proj1 (wf_unit_frame_free _ _ _ _ _ HU0) _ Hu (proj1 (desc_reads_frame_dm _ _ _ _ _) Hr0)) ]
        end ]
    end).
    (* the entry can be abstracted over the parameters: they are types of
       levels, or the entry, as the body's expansion types it, has no
       member of a type of levels *)
    all: try (destruct HLΔ as [HL | HN]; [ left; exact HL | right ];
      inversion HN; subst; cbn [List.app] in *;
      match goal with
      | HNU : forall _ _ _ _, _ -> entry_unit _ = _ -> udenote _ _ _ _ _ _,
        HNn : forall _ _ _ _, _ -> entry_unit _ = _ -> wf_no_level_members _ _ _ _ |- _ =>
          inversion Hed; subst;
          first
          [ apply wf_no_level_term;
            match goal with HNL : forall _ _ _ _ _, _ -> entry_tm _ = _ -> entry_kind _ <> ak_level |- _ =>
              exact (HNL _ _ _ _ _ Hp eq_refl) end
          | match goal with Hu : udenote _ _ _ _ _ _ |- _ =>
              rewrite <- List.app_assoc in Hu;
              pose proof (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ (HNU _ _ _ _ Hp eq_refl) _ Hu) as Heq end;
            subst; exact (sub_preserves_no_level _ _ _ _ _ _ (HNn _ _ _ _ Hp eq_refl) Hσ)
          | cbn [mdesc_sub]; apply wf_no_level_dm; intros Rw HRw;
            destruct (mdesc_mod_sub_inv _ _ _ HRw) as (R0 & HR0 & ->);
            match goal with Hu : udenote _ _ _ _ _ _ |- _ =>
              rewrite <- List.app_assoc in Hu;
              pose proof (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ (HNU _ _ _ _ Hp eq_refl) _ Hu) as Heq end;
            subst; exact (sub_preserves_no_level _ _ _ _ _ _ (no_level_mod _ _ _ _ _ (HNn _ _ _ _ Hp eq_refl) HR0) Hσ) ]
      end; fail).
    1: { (* a local definition, transparent: filled in, at the sort of its
            tag *)
         inversion Hed; subst; cbn [mdesc_sub option_map].
         destruct (Htg _ _ _ _ _ _ Hp eq_refl Hf) as (i & Hi).
         cbn [body_ctx List.app] in HΦ1; destruct (ctx_decomp_def HΦ1) as (_ & _ & HM).
         econstructor; [ exact Hi | intros ? [= <-]; exact (sub_preserves_exp _ _ _ _ _ _ _ HM Hσ) ]. }
    all: eapply desc_ok_sub; [ exact Hg | | exact Hσ ].
    - inversion Hed; subst; cbn [body_ctx List.app] in HΦ1.
      eapply Hent; [ exact Hp | reflexivity |].
      rewrite List.app_assoc; assumption.
    - (* a local definition with a module part: its term part typed as a
         definition's, its module part by the clause for it *)
      inversion Hed; subst; cbn [body_ctx List.app] in HΦ1.
      destruct (ctx_decomp_dm HΦ1) as (HΓ1 & [i HA] & HM & _).
      rewrite <- (mdesc_up_nil Rm); eapply desc_ok_dm with (param_level := 0); cbn [List.app];
        [ exact HΓ1 | constructor | exact HA | exact HM | | apply params_evaluated_nil | apply desc_levels_abstractable_nil
        | let Hne := fresh "Hne" in intros Hne; contradiction (Hne eq_refl) ].
      eapply Hent; [ exact Hp | reflexivity |].
      rewrite List.app_assoc; assumption.
  Qed.

  (** A description abstracted over [Δa], given arguments for the outermost
      parameters of [Δa]. *)
  Lemma ats_up_ok : ⊢ᵍ Θ ⍮ Ξ -> forall Ns Γ Δa R l,
      ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ -> all_assumptions Δa -> length Ns <= length Δa ->
      (forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts Δa Id Ns) k = Some A -> Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
      desc_ok (Δa ++ Γ) R -> up_evaluated Θ Ξ Γ Δa R l ->
      exists R', mdesc_ats (mdesc_up Δa R) Ns = Some R' /\ desc_ok Γ R'.
  Proof.
    intros Hg; induction Ns as [| N Ns IH]; intros * HΔ Ha Hl HNs HR HRΔ.
    - exists (mdesc_up Δa R); split; [ reflexivity | eapply desc_ok_up; eassumption ].
    - destruct (List.exists_last (l := Δa)) as (Δ1 & e & ->); [ intros ->; cbn in Hl; lia |].
      unfold all_assumptions in Ha; apply List.Forall_app in Ha as [Ha1 He]; apply List.Forall_cons_iff in He as [(κC & C & ->) _].
      rewrite tele_insts_snoc in HNs.
      pose proof (HNs 0 N C[Id] eq_refl eq_refl) as HN; rewrite exp_sub_id in HN.
      (* the inner parameters, relevant over the outermost when a module part
         needs them, and over which the description can be abstracted *)
      pose proof (up_evaluated_app_inv _ _ _ _ _ _ _ HRΔ) as HRΔ1; cbn [List.app] in HRΔ1.
      rewrite <- List.app_assoc in HΔ, HR; cbn [List.app] in HΔ, HR.
      destruct (ctx_decomp_sort_kind (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ (Srt & HS & HC)].
      pose proof (wf_sub_single _ _ _ _ _ _ _ HC HS HN) as Hs1.
      assert (HΔN : ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
      assert (Hσ : Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ ⊢ˢ sb_qn (length Δ1) (Id,,N) : Δ1 ++ ce_ass κC C :: Γ)
        by (apply wf_sub_ext; assumption).
      cbn [mdesc_ats]; rewrite mdesc_at_up.
      apply (IH _ _ _ l).
      + exact HΔN.
      + apply all_assumptions_sub; exact Ha1.
      + rewrite length_tele_sub; rewrite List.length_app in Hl; cbn in Hl; lia.
      + intros k N1 A HN1 HA.
        rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (Id,,N)) in HA by apply sb_compose_id_right.
        exact (HNs (S k) N1 A HN1 HA).
      + exact (desc_ok_sub Hg _ _ HR _ _ Hσ).
      + exact (up_evaluated_sub _ _ _ _ _ _ _ _ HRΔ1 Hs1 HΔ HΔN).
  Qed.

  (** A term of no δ-reduct abstracted over [Δa], given arguments for the
      outermost parameters of [Δa], is typed with the name [M] it is read as,
      at the arguments, as its δ-reduct. *)
  Lemma ats_up_self_ok : ⊢ᵍ Θ ⍮ Ξ -> forall Ns Γ Δa r A M,
      ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ -> all_assumptions Δa -> length Ns <= length Δa ->
      (forall k N B, nth_error Ns k = Some N -> nth_error (tele_insts Δa Id Ns) k = Some B -> Θ ⍮ Ξ ⍮ Γ ⊢ N : B) ->
      (exists i, Θ ⍮ Ξ ⍮ Δa ++ Γ ⊢ A : abs_kind_sort r Typeω@i) ->
      desc_levels_abstractable Θ Ξ Γ Δa (mdesc_term r A None) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ M : ctx_pi_at r Δa A ->
      exists R', mdesc_ats (mdesc_up Δa (mdesc_term r A None)) Ns = Some R' /\ desc_ok Γ (mdesc_self (apps M Ns) R').
  Proof.
    intros Hg; induction Ns as [| N Ns IH]; intros * HΔ Ha Hl HNs (iA & HA) HL HM.
    - exists (mdesc_up Δa (mdesc_term r A None)); split; [ reflexivity |]; cbn.
      assert (HPi : exists j, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi_at r Δa A : abs_kind_sort r Typeω@j).
      { destruct HL as [HL | HN].
        - exact (proj1 (ctx_pi_type_kind _ _ _ _ _ _ _ HΔ (fun _ => Ha) (fun _ => HL) HA)).
        - inversion HN; subst.
          match goal with Hr : r <> ak_level |- _ => exact (ctx_pi_at_wf _ _ _ _ _ _ _ Hr HΔ HA) end. }
      destruct HPi as [j Hj]; econstructor; [ exact Hj | intros ? [= <-]; exact HM ].
    - destruct (List.exists_last (l := Δa)) as (Δ1 & e & ->); [ intros ->; cbn in Hl; lia |].
      unfold all_assumptions in Ha; apply List.Forall_app in Ha as [Ha1 He]; apply List.Forall_cons_iff in He as [(κC & C & ->) _].
      rewrite tele_insts_snoc in HNs.
      pose proof (HNs 0 N C[Id] eq_refl eq_refl) as HN; rewrite exp_sub_id in HN.
      pose proof (desc_levels_abstractable_app_inv _ _ _ _ _ _ HL) as HL1; cbn [List.app] in HL1.
      (* with a codomain of levels, the parameters are of levels *)
      assert (HL' : r = ak_level -> level_sorted_parameters Δ1 /\ κC = ak_level).
      { intros Hr; destruct HL as [HL0 | HN0].
        - destruct (level_sorted_app_inv _ _ HL0) as [H1 H2]; split; [ exact H1 | exact (H2 nil κC C nil eq_refl) ].
        - exfalso; inversion HN0; subst; match goal with H : _ <> ak_level |- _ => exact (H eq_refl) end. }
      rewrite <- List.app_assoc in HΔ, HA; cbn [List.app] in HΔ, HA.
      destruct (ctx_decomp_sort_kind (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ (Srt & HS & HC)].
      pose proof (wf_sub_single _ _ _ _ _ _ _ HC HS HN) as Hs1.
      assert (HΔN : ⊢ Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ) by (eapply ctx_sub_wf_gen; eassumption).
      assert (Hσ : Θ ⍮ Ξ ⍮ tele_sub Δ1 (Id,,N) ++ Γ ⊢ˢ sb_qn (length Δ1) (Id,,N) : Δ1 ++ ce_ass κC C :: Γ)
        by (apply wf_sub_ext; assumption).
      rewrite ctx_pi_snoc in HM.
      (* the [Π] over the inner parameters, a function at the outermost *)
      assert (Happ : Θ ⍮ Ξ ⍮ Γ ⊢ M $ N : (ctx_pi_at r Δ1 A)[Id,,N]).
      { assert (Hk : pi_kinds κC r)
          by (destruct r; [ constructor | constructor | destruct (HL' eq_refl) as [_ ->]; constructor ]).
        destruct (ctx_pi_type_kind _ _ r Δ1 _ A _ HΔ (fun _ => Ha1) (fun Hr => proj1 (HL' Hr)) HA) as [[j HPi] _].
        eapply wf_app with (Srt := Srt) (i := j); [ exact HC | exact HS | exact HPi | exact Hk | exact HM | exact HN ]. }
      rewrite ctx_pi_sub in Happ.
      cbn [mdesc_ats]; rewrite mdesc_at_up; cbn [mdesc_sub option_map].
      apply (IH _ _ _ _ (M $ N)).
      + exact HΔN.
      + apply all_assumptions_sub; exact Ha1.
      + rewrite length_tele_sub; rewrite List.length_app in Hl; cbn in Hl; lia.
      + intros k' N1 B HN1 HB.
        rewrite tele_insts_tele_sub, (tele_insts_sb_eq _ _ (Id,,N)) in HB by apply sb_compose_id_right.
        exact (HNs (S k') N1 B HN1 HB).
      + exists iA; pose proof (sub_preserves_exp _ _ _ _ _ _ _ HA Hσ) as HAσ.
        rewrite type_sort_sub in HAσ by (apply type_sort_abs_kind; constructor); exact HAσ.
      + exact (desc_levels_abstractable_sub _ _ _ _ _ _ _ HL1 Hs1 HΔ HΔN).
      + exact Happ.
  Qed.

  Lemma args_ok_ext : forall Γ T Ns Δ0, args_ok Γ T Ns -> args_ok Γ (Δ0 ++ T) Ns.
  Proof.
    intros * [T1 T2 -> Hl Ha Hs HT HN]; exists (Δ0 ++ T1) T2; try assumption; rewrite List.app_assoc; reflexivity.
  Qed.

  Lemma args_ok_length : forall Γ T Ns, args_ok Γ T Ns -> length Ns <= length T.
  Proof. intros * [T1 T2 -> Hl _ _ _ _]; rewrite List.length_app; lia. Qed.

  Lemma args_ok_insts : forall Γ T Ns, args_ok Γ T Ns ->
      forall k N A, nth_error Ns k = Some N -> nth_error (tele_insts T Id Ns) k = Some A -> Θ ⍮ Ξ ⍮ Γ ⊢ N : A.
  Proof.
    intros * [T1 T2 -> Hl Ha _ _ HN] * HNk HAk.
    rewrite <- (List.app_nil_r Ns) in HAk.
    rewrite tele_insts_app in HAk by (first [ exact Ha | lia ]).
    rewrite List.nth_error_app1 in HAk.
    - exact (HN _ _ _ HNk HAk).
    - rewrite length_tele_insts by exact Ha.
      assert (k < length Ns) by (apply List.nth_error_Some; congruence); lia.
  Qed.

  (** A description over a closed telescope on top of [Γ] is one on top of
      any extension of [Γ], when it mentions nothing of [Γ]. *)
  Lemma desc_ok_tele_weaken : ⊢ᵍ Θ ⍮ Ξ -> forall Δa Γ' Γ R,
      ctx_scoped 0 Δa -> ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ -> ⊢ Θ ⍮ Ξ ⍮ Δa ++ Γ' ++ Γ ->
      mdesc_scoped (length Δa) R -> desc_ok (Δa ++ Γ) R -> desc_ok (Δa ++ Γ' ++ Γ) R.
  Proof.
    intros Hg * Hs HΔΓ HΔΓ' HR Hok.
    pose proof (ctx_app_wf_tail _ _ _ _ HΔΓ') as HΓ'Γ.
    assert (Hw : Θ ⍮ Ξ ⍮ Γ' ++ Γ ⊢ˢ ι (wk_shiftn (length Γ')) : Γ)
      by (apply wf_sub_of_wk, wf_wk_shiftn_app; [ exact HΓ'Γ | exact (ctx_app_wf_tail _ _ _ _ HΓ'Γ) ]).
    assert (Hσ : Θ ⍮ Ξ ⍮ Δa ++ Γ' ++ Γ ⊢ˢ sb_qn (length Δa) (ι (wk_shiftn (length Γ'))) : Δa ++ Γ).
    { pose proof (wf_sub_ext _ _ Δa _ _ _ Hw) as Hx; rewrite tele_sub_closed in Hx by exact Hs.
      exact (Hx HΔΓ' HΔΓ). }
    pose proof (desc_ok_sub Hg _ _ Hok _ _ Hσ) as H.
    rewrite (mdesc_sub_fix _ _ _ HR) in H; [ exact H |].
    intros x Hx; apply (sb_qn_fix _ _ 0); [ intros; lia | lia ].
  Qed.
End DescOk.
