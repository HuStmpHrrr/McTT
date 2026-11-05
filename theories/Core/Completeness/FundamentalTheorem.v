(** * The Fundamental Theorem of the PER Model

    Every judgment of a global context holds semantically
    ([completeness_fundamental]), along every sound embedding: by induction on
    the derivation, each rule is its semantic rule, stated and proved in the
    file of its construct.  The case of each rule only applies its semantic
    rule.

    The theorem then gives the rest.  Each entry of a global context is
    valid where it is checked, so a well-formed global context embeds
    soundly into itself ([valid_gctx_embedding_refl]), from what [Global/Embedding.v] makes of
    valid entries.  At that embedding the theorem states each judgment of
    one global context by its relation there ([completeness_fundamental_ctx]
    and the corollaries after it). *)

From Stdlib Require Import Lia List.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Global Require Import
  MemberLemmas MemberWf Modules Paths DescTyping LookupSound.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax.
From Mctt.Core.Completeness Require Import ContextCases FunctionCases LetCases LevelCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution.
From Mctt.Core.Completeness Require Import
  SubtypingCases PropCases UniverseCases VariableCases UnitCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Instance.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness.Inductives Require Import Model ArgTypes Con.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope.
From Mctt.Core.Completeness.Inductives Require Import Elim.
From Mctt.Core.Completeness Require Import IndCases ElimCases.
From Mctt.Core.Completeness.Inductives Require Import Iota.
From Mctt.Core.Completeness Require Import IotaCases ModuleCases RecordCases.
From Mctt.Core.Completeness.Records Require Model.
From Mctt.Core.Completeness.Modules Require Import ValidUnit.
From Mctt.Core.Completeness.Global Require Import Embedding.
From Mctt.Core.Completeness Require Export LogicalRelation.
From Mctt.Core.Syntactic Require Export SystemOpt.
From Mctt.Core.Semantic Require Import Realizability.
Import Domain_Notations Syntax_Notations Wk_Notations GlobalCtx_Notations Fixed_Notations.
#[local] Open Scope list_scope.

(** ** Scoping side conditions

    A kept proof is read back over the context it is met in, so the
    semantic cases of the rules that keep a term ask for its scoping; it
    comes from the term's typing ([wf_scoped]). *)
Lemma wf_exp_scoped_term : forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> exp_scoped (List.length Γ) M.
Proof. intros * H; exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ H))). Qed.

Lemma wf_exp_eq_scoped_left : forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> exp_scoped (List.length Γ) M.
Proof. intros * H; exact (proj1 (proj2 (proj1 (proj2 (proj2 wf_scoped)) _ _ _ _ _ _ H))). Qed.

Lemma wf_exp_eq_scoped_right : forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> exp_scoped (List.length Γ) M'.
Proof. intros * H; exact (proj1 (proj2 (proj2 (proj1 (proj2 (proj2 wf_scoped)) _ _ _ _ _ _ H)))). Qed.

Lemma wf_unit_eq_scoped_left : forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> gunit_scoped (List.length Γ) U.
Proof.
  intros * H; destruct wf_scoped as (_ & _ & _ & _ & _ & _ & Hu & _); exact (proj1 (proj2 (Hu _ _ _ _ _ H))).
Qed.

Lemma wf_unit_eq_scoped_right : forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> gunit_scoped (List.length Γ) U'.
Proof.
  intros * H; destruct wf_scoped as (_ & _ & _ & _ & _ & _ & Hu & _); exact (proj2 (proj2 (Hu _ _ _ _ _ H))).
Qed.

(** A list each of whose entries satisfies [Q]. *)
Lemma forall_of_nth_error : forall {X} (Q : X -> Prop) (l : list X), (forall k x, nth_error l k = Some x -> Q x) -> Forall Q l.
Proof.
  intros * H; apply Forall_forall; intros x Hx.
  destruct (In_nth_error _ _ Hx) as [k Hk]; exact (H _ _ Hk).
Qed.

(** An entry of a list at an index of a list at least as long. *)
Lemma nth_error_of_length : forall {X Y} (l : list X) (l' : list Y) k x,
    nth_error l k = Some x -> List.length l <= List.length l' -> exists y, nth_error l' k = Some y.
Proof.
  intros * Hk Hl; destruct (nth_error l' k) as [y |] eqn:E; [ eauto |].
  apply nth_error_None in E; assert (k < List.length l) by (apply nth_error_Some; congruence); lia.
Qed.

(** The block of an eliminator, scoped, from its typing. *)
Lemma blocks_scoped_of_elim : forall Θ Ξ Γ r p Us m Bks M T,
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim r p Us m Bks M : T -> blocks_scoped (List.length Γ) Bks.
Proof. intros * H; exact (proj1 (proj2 (proj1 (exp_scoped_elim _ _ _ _ _ _ _) (wf_exp_scoped_term _ _ _ _ _ H)))). Qed.

(** The field values of a tuple, scoped, from its typing. *)
Lemma tuple_fields_scoped : forall Θ Ξ Γ T fs A,
    Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs : A -> Forall (exp_scoped (List.length Γ)) (map snd fs).
Proof.
  intros * H; pose proof (wf_exp_scoped_term _ _ _ _ _ H) as Hs; cbn [exp_scoped] in Hs.
  destruct Hs as [_ Hs]; rewrite all_list_Forall in Hs; apply Forall_map; exact Hs.
Qed.

Lemma blocks_scoped_of_elim_eq : forall Θ Ξ Γ r p Us m Bks M N T,
    Θ ⍮ Ξ ⍮ Γ ⊢ a_elim r p Us m Bks M ≈ N : T -> blocks_scoped (List.length Γ) Bks.
Proof. intros * H; exact (proj1 (proj2 (proj1 (exp_scoped_elim _ _ _ _ _ _ _) (wf_exp_eq_scoped_left _ _ _ _ _ _ H)))). Qed.

Lemma blocks_scoped_of_elim_eq_right : forall Θ Ξ Γ r p Us m Bks M N T,
    Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ a_elim r p Us m Bks M : T -> blocks_scoped (List.length Γ) Bks.
Proof. intros * H; exact (proj1 (proj2 (proj1 (exp_scoped_elim _ _ _ _ _ _ _) (wf_exp_eq_scoped_right _ _ _ _ _ _ H)))). Qed.

(** The length of the instances of a telescope at arguments, at least the
    arguments' number: of a member's parameters, of a constructor's
    arguments, or of a record's parameters. *)
(** A well-formed context of the global context of the hypotheses. *)
Ltac ctx_judgment :=
  first [ match goal with H : ⊢ _ ⍮ _ ⍮ _ |- _ => exact H end
        | match goal with H : _ ⍮ _ ⍮ _ ⊢ _ : _ |- _ => exact (presup_exp_ctx H) end
        | match goal with H : _ ⍮ _ ⍮ _ ⊢ _ ≈ _ : _ |- _ => exact (presup_exp_eq_ctx H) end ].

Ltac tele_insts_long :=
  first
    [ lia
    | rewrite length_tele_insts_cargs by assumption; lia
    | match goal with
      | Hl : ind_lookup ?T ?X _ = Some ?D, HMk : ind_member ?D _ = Some ?Mk |- _ =>
          let HΓ := fresh "HΓ" in
          assert (HΓ : exists G, ⊢ T ⍮ X ⍮ G) by (eexists; ctx_judgment);
          destruct HΓ as [? HΓ];
          rewrite length_tele_insts_params;
          [ lia | exact (decl_closed_params_ass _ _ _ (proj2 (decl_of_lookup _ _ _ _ _ HΓ Hl)) HMk) | lia ]
      end
    | match goal with
      | Hl : record_lookup ?T ?X _ = Some ?R |- _ =>
          let HΓ := fresh "HΓ" in
          assert (HΓ : exists G, ⊢ T ⍮ X ⍮ G) by (eexists; ctx_judgment);
          destruct HΓ as [? HΓ];
          let G := constr:(ctx_wf_gctx _ _ _ HΓ) in
          rewrite length_tele_insts by exact (typed_params_ass _ _ _ (record_lookup_typed _ _ G (gctx_valid_syn _ _ G) _ _ Hl));
          lia
      end ].

(** The field [k] of two lists of field values of one record, and of its
    declaration, from the value at [k] of the first. *)
Ltac field_pair fs gs Fs Hn Hn' k M HP :=
  rewrite nth_error_map in HP;
  let f := fresh "f" in let M0 := fresh "M0" in let U := fresh "U" in let M1 := fresh "M1" in
  destruct (nth_error fs k) as [[f M0] |] eqn:Hfk; cbn in HP; [| discriminate ]; injection HP as <-;
  assert (Hf : nth_error (map fst Fs) k = Some f) by (rewrite <- Hn, nth_error_map, Hfk; reflexivity);
  rewrite nth_error_map in Hf;
  destruct (nth_error Fs k) as [[? U] |] eqn:HFk; cbn in Hf; [| discriminate ]; injection Hf as ->;
  assert (Hg : nth_error (map fst gs) k = Some f) by (rewrite Hn', nth_error_map, HFk; reflexivity);
  rewrite nth_error_map in Hg;
  destruct (nth_error gs k) as [[? M1] |] eqn:Hfk'; cbn in Hg; [| discriminate ]; injection Hg as ->.

(** The entries of a list of arguments, scoped, from their typings at the
    instances of a telescope ([args_ok]), or from the equal pairs of two
    lists, or a record's field values from their typings. *)
Ltac args_scoped :=
  apply forall_of_nth_error; intros ?k ?P ?HP;
  first
    [ match goal with
      | H : forall k P T, nth_error ?Ps k = Some P -> nth_error ?Ts k = Some T -> _ ⍮ _ ⍮ _ ⊢ P : T,
        HP : nth_error ?Ps ?k = Some ?P |- _ =>
          let T := fresh "T" in let HT := fresh "HT" in
          destruct (nth_error_of_length Ps Ts k P HP ltac:(tele_insts_long)) as [T HT];
          exact (wf_exp_scoped_term _ _ _ _ _ (H _ _ _ HP HT))
      end
    | match goal with
      | H : forall k P P' T, nth_error ?Ps k = Some P -> nth_error ?Ps' k = Some P' -> nth_error ?Ts k = Some T ->
              _ ⍮ _ ⍮ _ ⊢ P ≈ P' : T,
        HP : nth_error ?Ps ?k = Some ?P |- _ =>
          let P' := fresh "P'" in let HP' := fresh "HP'" in let T := fresh "T" in let HT := fresh "HT" in
          destruct (nth_error_of_length Ps Ps' k P HP ltac:(lia)) as [P' HP'];
          destruct (nth_error_of_length Ps Ts k P HP ltac:(tele_insts_long)) as [T HT];
          exact (wf_exp_eq_scoped_left _ _ _ _ _ _ (H _ _ _ _ HP HP' HT))
      end
    | match goal with
      | H : forall k P P' T, nth_error ?Ps k = Some P -> nth_error ?Ps' k = Some P' -> nth_error ?Ts k = Some T ->
              _ ⍮ _ ⍮ _ ⊢ P ≈ P' : T,
        HP' : nth_error ?Ps' ?k = Some ?P' |- _ =>
          let P := fresh "P" in let HP := fresh "HP" in let T := fresh "T" in let HT := fresh "HT" in
          destruct (nth_error_of_length Ps' Ps k P' HP' ltac:(lia)) as [P HP];
          destruct (nth_error_of_length Ps Ts k P HP ltac:(tele_insts_long)) as [T HT];
          exact (wf_exp_eq_scoped_right _ _ _ _ _ _ (H _ _ _ _ HP HP' HT))
      end
    | match goal with
      | HP : nth_error (map snd ?fs) ?k = Some ?M,
        Hn : map fst ?fs = map fst ?Fs,
        H : forall k f M U, nth_error ?fs k = Some (f, M) -> nth_error ?Fs k = Some (f, U) -> _ ⍮ _ ⍮ _ ⊢ M : _ |- _ =>
          rewrite nth_error_map in HP;
          destruct (nth_error fs k) as [[f M0] |] eqn:Hfk; cbn in HP; [| discriminate ]; injection HP as <-;
          assert (Hf : nth_error (map fst Fs) k = Some f) by (rewrite <- Hn, nth_error_map, Hfk; reflexivity);
          rewrite nth_error_map in Hf;
          destruct (nth_error Fs k) as [[f' U] |] eqn:HFk; cbn in Hf; [| discriminate ]; injection Hf as ->;
          exact (wf_exp_scoped_term _ _ _ _ _ (H _ _ _ _ Hfk HFk))
      end
    | match goal with
      | HP : nth_error (map snd ?fs) ?k = Some ?M,
        Hn : map fst ?fs = map fst ?Fs, Hn' : map fst ?fs' = map fst ?Fs,
        H : forall k f M M' U, nth_error ?fs k = Some (f, M) -> nth_error ?fs' k = Some (f, M') ->
              nth_error ?Fs k = Some (f, U) -> _ ⍮ _ ⍮ _ ⊢ M ≈ M' : _ |- _ =>
          field_pair fs fs' Fs Hn Hn' k M HP;
          eapply wf_exp_eq_scoped_left; eapply H; eassumption
      end
    | match goal with
      | HP : nth_error (map snd ?fs') ?k = Some ?M',
        Hn : map fst ?fs = map fst ?Fs, Hn' : map fst ?fs' = map fst ?Fs,
        H : forall k f M M' U, nth_error ?fs k = Some (f, M) -> nth_error ?fs' k = Some (f, M') ->
              nth_error ?Fs k = Some (f, U) -> _ ⍮ _ ⍮ _ ⊢ M ≈ M' : _ |- _ =>
          field_pair fs' fs Fs Hn' Hn k M' HP;
          eapply wf_exp_eq_scoped_right; eapply H; eassumption
      end ].

(** A scoping side condition from a typing hypothesis of the term or unit. *)
Ltac scoped_side :=
  match goal with
  | |- Forall (exp_scoped _) _ => args_scoped
  | |- Forall (exp_scoped _) (map snd ?fs) =>
      match goal with H : _ ⍮ _ ⍮ _ ⊢ a_tuple _ fs : _ |- _ => exact (tuple_fields_scoped _ _ _ _ _ _ H) end
  | |- blocks_scoped _ ?Bks =>
      first [ (** the eliminator's group: the one of the blocks' number *)
              match goal with HB : length Bks = ind_nblk ?D, Hl : ind_lookup _ _ ?p = Some ?D |- _ =>
                eapply blocks_scoped_of_elim; eapply (wf_elim _ _ p D); eassumption end
            | eapply blocks_scoped_of_elim_eq; eapply wf_exp_eq_elim_cong; eassumption
            | eapply blocks_scoped_of_elim_eq_right; eapply wf_exp_eq_elim_cong; eassumption
            | eapply blocks_scoped_of_elim_eq; eapply wf_exp_eq_elim_iota; eassumption
            | eapply blocks_scoped_of_elim_eq; eapply wf_exp_eq_elim_view; eassumption ]
  | |- exp_scoped _ ?M =>
      first [ match goal with H : _ ⍮ _ ⍮ _ ⊢ M : _ |- _ => exact (wf_exp_scoped_term _ _ _ _ _ H) end
            | match goal with H : _ ⍮ _ ⍮ _ ⊢ M ≈ _ : _ |- _ => exact (wf_exp_eq_scoped_left _ _ _ _ _ _ H) end
            | match goal with H : _ ⍮ _ ⍮ _ ⊢ _ ≈ M : _ |- _ => exact (wf_exp_eq_scoped_right _ _ _ _ _ _ H) end ]
  | |- gunit_scoped _ ?U =>
      first [ match goal with H : _ ⍮ _ ⍮ _ ⊢ᵘ U ≈ _ |- _ => exact (wf_unit_eq_scoped_left _ _ _ _ _ H) end
            | match goal with H : _ ⍮ _ ⍮ _ ⊢ᵘ _ ≈ U |- _ => exact (wf_unit_eq_scoped_right _ _ _ _ _ H) end ]
  end.

Theorem completeness_fundamental :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊨ Θ ⍮ Ξ ⍮ Γ) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊨ M : A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ ⍮ Ξ ⍮ Γ ⊨ M ≈ M' : A) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ ⍮ Ξ ⍮ Γ ⊨ A ⊆ A') /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> Θ ⍮ Ξ ⍮ Γ ⊨ᵤ U) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ ⍮ Ξ ⍮ Γ ⊨ˣ Ψ ≈ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ ⍮ Ξ ⍮ Γ ⊨ᵘ U ≈ U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ ⍮ Ξ ⍮ Γ ⊨ᵐ H ≈ H').
Proof.
  apply syntactic_wf_mut_ind; intros;
    [ (** contexts *)
      eapply sem_ctx_empty | eapply sem_ctx_extend | eapply sem_ctx_extend_def | eapply sem_ctx_extend_mod
    | eapply sem_ctx_extend_dm
    | (** terms *)
      eapply sem_typ | eapply sem_univ | eapply sem_level | eapply sem_level_sort | eapply sem_llit | eapply sem_succl
    | eapply sem_maxl
    | eapply sem_prop | eapply sem_True | eapply sem_tt | eapply sem_False | eapply sem_absurd
    | eapply sem_and | eapply sem_conj | eapply sem_left | eapply sem_right
    | eapply sem_ind | eapply sem_con
    | eapply sem_elim | eapply sem_pi | eapply sem_fn
    | (** the function's premise first: it fixes the domain, which the
          conclusion does not *)
      eapply sem_app; [ | | | | eassumption | | ]
    | eapply sem_let
    | eapply sem_let_mod
    | eapply sem_mem | eapply sem_vlookup | eapply sem_record | eapply sem_tuple | eapply sem_proj | eapply sem_exp_subtyp
    | (** term equality *)
      eapply sem_exp_eq_typ_cong | eapply sem_exp_eq_univ_cong | eapply sem_exp_eq_level_cong
    | eapply sem_exp_eq_level_sort_cong | eapply sem_exp_eq_llit_cong | eapply sem_exp_eq_succl_cong | eapply sem_exp_eq_maxl_cong
    | eapply sem_exp_eq_llit_succl | eapply sem_exp_eq_maxl_absorb | eapply sem_exp_eq_maxl_zero
    | eapply sem_exp_eq_maxl_assoc | eapply sem_exp_eq_maxl_comm | eapply sem_exp_eq_maxl_idem
    | eapply sem_exp_eq_succl_maxl | eapply sem_exp_eq_maxl_succl
    | eapply sem_exp_eq_prop_cong | eapply sem_exp_eq_True_cong | eapply sem_exp_eq_False_cong
    | eapply sem_exp_eq_absurd_cong | eapply sem_exp_eq_and_cong
    | eapply sem_exp_eq_ind_cong | eapply sem_exp_eq_con_cong
    | eapply sem_exp_eq_elim_cong | eapply sem_exp_eq_pi_cong | eapply sem_exp_eq_fn_cong
    | eapply sem_exp_eq_app_cong | eapply sem_exp_eq_let_cong | eapply sem_exp_eq_let_mod_cong
    | eapply sem_exp_eq_mem_cong | eapply sem_exp_eq_var | eapply sem_exp_eq_pi_beta
    | eapply sem_exp_eq_elim_iota | eapply sem_exp_eq_elim_view | eapply sem_exp_eq_con_view | eapply sem_exp_eq_con_rview
    | eapply sem_exp_eq_let_zeta | eapply sem_exp_eq_let_mod_zeta
    | eapply sem_exp_eq_mem_delta | eapply sem_exp_eq_var_delta | eapply sem_exp_eq_fn_eta
    | eapply sem_exp_eq_irrelevant | eapply sem_exp_eq_record_cong | eapply sem_exp_eq_tuple_cong
    | eapply sem_exp_eq_proj_cong | eapply sem_exp_eq_field_beta | eapply sem_exp_eq_record_eta
    | eapply sem_exp_eq_subtyp | eapply sem_exp_eq_sym | eapply sem_exp_eq_trans
    | (** subtyping *)
      eapply sem_subtyp_refl | eapply sem_subtyp_trans | eapply sem_subtyp_univ | eapply sem_subtyp_suniv
    | eapply sem_subtyp_level | eapply sem_subtyp_small_large | eapply sem_subtyp_pi
    | (** universes *)
      eapply sem_is_univ_large | eapply sem_is_univ_small
    | (** extensions *)
      eapply sem_ext_eq_nil | eapply sem_ext_eq_ass | eapply sem_ext_eq_def | eapply sem_ext_eq_mod
    | eapply sem_ext_eq_dm
    | (** units: the first premise is the conclusion of the rule *)
      eapply sem_unit_eq_body; [ eapply wf_unit_eq_body; eassumption | .. ]
    | eapply sem_unit_eq_alias; [ eapply wf_unit_eq_alias; eassumption | .. ]
    | eapply sem_unit_eq_flatten; [ eapply wf_unit_eq_flatten; eassumption | .. ]
    | eapply sem_unit_eq_expand | eapply sem_unit_eq_sym | eapply sem_unit_eq_trans
    | (** module expressions *)
      eapply sem_me_unit | eapply sem_me_var | eapply sem_me_lit | eapply sem_me_mem | eapply sem_me_app
    | eapply sem_me_delta_slot | eapply sem_me_delta_sel | eapply sem_me_beta_body | eapply sem_me_beta_alias
    | eapply sem_me_beta_alias0 | eapply sem_me_sym | eapply sem_me_trans ];
    (** A premise whose sort or index is not fixed by the conclusion (the
        [Srt] of [sem_let], the [P] of [sem_right]) may match a wrong
        hypothesis first; [multimatch] backtracks over the choices. *)
    first [ scoped_side | multimatch goal with H : _ |- _ => exact H end ].
Qed.

(** Judgments read along a sound embedding. *)
Lemma valid_exp_under_ctx_of_embedding : forall Θ Ξ Θ2 Ξ2 Γ A M, valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M.
Proof.
  intros * Hμ HM; destruct completeness_fundamental as (_ & Ke & _).
  exact (sem_exp_eq_at_rel (Ke _ _ _ _ _ HM _ _ Hμ)).
Qed.

Lemma rel_ctx_wf_of_embedding : forall Θ Ξ Θ2 Ξ2 Γ, valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> ⊢ Θ ⍮ Ξ ⍮ Γ -> @rel_ctx_wf (gc_mk Θ2 Ξ2) Γ.
Proof.
  intros * Hμ HΓ; destruct completeness_fundamental as (Kc & _).
  exact (valid_ctx_rel_ctx_wf (Kc _ _ _ HΓ _ _ Hμ)).
Qed.

Lemma rel_exp_eq_of_embedding : forall Θ Ξ Θ2 Ξ2 Γ A M M', valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    @rel_exp_under_ctx (gc_mk Θ2 Ξ2) Γ A M M'.
Proof.
  intros * Hμ HM; destruct completeness_fundamental as (_ & _ & Kq & _).
  exact (sem_exp_eq_at_rel (Kq _ _ _ _ _ _ HM _ _ Hμ)).
Qed.

Lemma rel_ext_of_embedding : forall Θ Ξ Θ2 Ξ2 Γ Ψ Ψ', valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
    @rel_ext_under_ctx (gc_mk Θ2 Ξ2) Γ Ψ Ψ'.
Proof.
  intros * Hμ HΨ; destruct completeness_fundamental as (_ & _ & _ & _ & _ & Kx & _).
  exact (sem_ext_eq_at_rel (Kx _ _ _ _ _ HΨ _ _ Hμ)).
Qed.

Lemma rel_subtyp_of_embedding : forall Θ Ξ Θ2 Ξ2 Γ A A', valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
    @rel_subtyp_under_ctx (gc_mk Θ2 Ξ2) Γ A A'.
Proof.
  intros * Hμ HA; destruct completeness_fundamental as (_ & _ & _ & Ks & _).
  exact (sem_subtyp_at_rel (Ks _ _ _ _ _ HA _ _ Hμ)).
Qed.

(** ** Each entry is valid where it is checked *)

(** A definition, its type of the sort of its kind: the [Π] at its kind
    and the [λ] over its telescope of a valid type and a valid body.  The
    [Π]s into its kind are formed: at [ak_level] every parameter is a
    level ([pi_kinds_of_level_sorted]). *)
Lemma valid_entry_def : forall Θ Ξ T r A M i b pv Θ2 Ξ2,
    Θ ⍮ Ξ ⍮ T ⊢ A : abs_kind_sort r Typeω@i ->
    (r = ak_level -> level_sorted_parameters T) -> tele_ass T ->
    Θ ⍮ Ξ ⍮ T ⊢ M : A -> bodies_valid_along_embeddings valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θ Ξ -> gctx_embedding Θ Ξ Θ2 Ξ2 ->
    gds_valid valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θ Ξ Θ2 Ξ2 Θ -> gs_valid valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θ Ξ Θ2 Ξ2 Ξ ->
    forall Θs Ξs, valid_entry Θs Ξs Θ2 Ξ2 T (ge_def b pv r (ctx_pi_at r T A) (Some (ctx_fn T M))).
Proof.
  intros * HA HL _ HM _ He HΘ HΞ Θs Ξs.
  pose proof (valid_gctx_embedding_of _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HM)) He HΘ HΞ) as Hμ.
  apply (mk_valid_def_entry _ _ _ _ _ _ A i (Some M)); [ reflexivity | reflexivity
    | exact (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ HA)
    | intros ? [= <-]; exact (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ HM)
    | exact (pi_kinds_of_level_sorted _ _ HL) ].
Qed.

(** An axiom, of no type of levels: the [Π] over its telescope of a valid
    type. *)
Lemma valid_entry_ax : forall Θ Ξ r A i b pv Θ2 Ξ2 Θs Ξs,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : abs_kind_sort r Typeω@i -> r <> ak_level -> tele_ass (gs_tele Ξ) ->
    bodies_valid_along_embeddings valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θ Ξ -> gctx_embedding_with_bodies Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    valid_entry Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_def b pv r (ctx_pi_at r (gs_tele Ξ) A) None).
Proof.
  intros * HA Hr _ HG He _.
  pose proof (valid_gctx_embedding_of_bodies_valid _ _ _ _ (ctx_wf_gctx _ _ _ (presup_exp_ctx HA)) HG He) as Hμ.
  apply (mk_valid_def_entry _ _ _ _ _ _ A i None); [ reflexivity | reflexivity
    | exact (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ HA) | intros ? [=]
    | exact (pi_kinds_of_level_sorted _ _ (fun Hl => False_ind _ (Hr Hl))) ].
Qed.

Lemma valid_entry_alias : forall Θ Ξ pv Δ E l (lv : bool) Rt Θ2 Ξ2 Θs Ξs,
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    params_evaluated Θ Ξ (gs_tele Ξ) Δ l ->
    levels_flag Θ Ξ ⋅ (Δ ++ gs_tele Ξ) E lv Rt ->
    bodies_valid_along_embeddings valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θ Ξ -> gctx_embedding_with_bodies Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    valid_entry Θs Ξs Θ2 Ξ2 (gs_tele Ξ) (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
Proof.
  intros * HΔ _ HE HP [HFs HFd HFn] HG He Hs HgS; cbn.
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) as Hg.
  pose proof (valid_gctx_embedding_of_bodies_valid _ _ _ _ Hg HG He) as Hμ.
  assert (Ht : tele_ass (Δ ++ gs_tele Ξ)) by (apply List.Forall_app; split; [ exact HΔ | exact (gs_tele_ass_of_bodies_valid _ _ _ _ HG He) ]).
  assert (HE' : Θ ⍮ Ξ ⍮ (Δ ++ gs_tele Ξ) ++ ⋅ ⊢ᵐ E ≈ E) by (rewrite app_nil_r; exact HE).
  assert (HC : ⊢ Θ ⍮ Ξ ⍮ (Δ ++ gs_tele Ξ) ++ ⋅) by (rewrite app_nil_r; exact (presup_modexp_eq_ctx HE)).
  destruct (params_evaluated_over_stack _ _ _ _ Hg HP) as [l' HP'].
  destruct (params_evaluated_sorts _ _ _ _ _ HP') as (ps & Hps & HPs).
  assert (HU : Θ ⍮ Ξ ⍮ ⋅ ⊢ᵘ gu_mk (Δ ++ gs_tele Ξ) (md_alias E) ≈ gu_mk (Δ ++ gs_tele Ξ) (md_alias E))
    by (apply wf_unit_eq_alias with (param_level := l') (param_sorts := ps) (lv := lv) (Rt := Rt) (lv' := lv) (Rt' := Rt);
        [ exact (ext_of_ctx _ _ _ _ HC) | exact Ht | exact Ht | exact HE' | exact HE' | exact Hps | exact HPs | exact HPs
        | exact HFs | exact HFd | exact HFn | exact HFs | exact HFd | exact HFn ]).
  destruct completeness_fundamental as (_ & _ & _ & _ & _ & _ & Ku & _).
  destruct (Ku _ _ _ _ _ HU _ _ Hμ) as [_ _ HK _].
  exact (valid_unit_grow _ _ _ _ Hg {| gctx_embedding_wf := HgS; gctx_embedding_resolution := Hs |} _ _ HK).
Qed.

(** Relevant parameters are so in the PER model, along a sound embedding. *)
Lemma rel_params_evaluated_of_embedding : forall Θ Ξ Θ2 Ξ2 Γ Δ l, valid_gctx_embedding Θ Ξ Θ2 Ξ2 ->
    params_evaluated Θ Ξ Γ Δ l -> @rel_params_evaluated (gc_mk Θ2 Ξ2) Γ Δ l.
Proof.
  intros * Hμ HP Δ1 κ A Δ2 E; destruct (HP _ _ _ _ E) as [H | H]; [ left | right ];
    exact (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ H).
Qed.

(** A parameter type at the source is one at the target, along a sound
    embedding. *)
Lemma rel_param_typed_of_embedding : forall Θ Ξ Θ2 Ξ2 Γ A l, valid_gctx_embedding Θ Ξ Θ2 Ξ2 ->
    param_typed Θ Ξ Γ A l -> @rel_param_typed (gc_mk Θ2 Ξ2) Γ A l.
Proof.
  intros * Hμ [H | H]; [ left | right ]; exact (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ H).
Qed.

Lemma valid_mod_tele_nil : forall Θ Ξ Δ l Θ2 Ξ2,
    tele_ass Δ -> ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ -> params_evaluated Θ Ξ (gs_tele Ξ) Δ l ->
    bodies_valid_along_embeddings valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θ Ξ -> gctx_embedding_with_bodies Θ Ξ Θ2 Ξ2 ->
    valid_mod_tele Θ2 Ξ2 (Δ ++ gs_tele Ξ).
Proof.
  intros * HΔ HC HP HG He.
  pose proof (ctx_wf_gctx _ _ _ HC) as Hg.
  pose proof (valid_gctx_embedding_of_bodies_valid _ _ _ _ Hg HG He) as Hμ.
  destruct (params_evaluated_over_stack _ _ _ _ Hg HP) as [l' HP'].
  constructor; [ exact (rel_ctx_wf_of_embedding _ _ _ _ _ Hμ HC) | | exists l'; exact (rel_params_evaluated_of_embedding _ _ _ _ _ _ _ Hμ HP') ].
  apply List.Forall_app; split; [ exact HΔ | exact (gs_tele_ass_of_bodies_valid _ _ _ _ HG He) ].
Qed.

(** A type at a sort is a type. *)
Lemma sort_large_sem : forall {GC : GCtx} S φ Γ X, ind_sort_univ S -> Γ ⊨ X : S[φ]ʷ -> exists j : nat, Γ ⊨ X : Typeω@j.
Proof.
  intros * [[i ->] | [t ->]] H; cbn [exp_wk] in H; [ exists i; exact H | exists 0; eapply rel_exp_suniv_tm_large; exact H ].
Qed.

(** A declaration typed at the source is valid at the target: its
    judgments, read in the PER model, member by member, and its views with
    the members as variables ([views_self_typed], read semantically). *)
Lemma valid_ind_decl_of_typed : forall Θ Ξ D l Θ2 Ξ2, decl_typed Θ Ξ D -> params_evaluated Θ Ξ nil (ind_uparams D) l ->
    valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> @valid_ind_decl (gc_mk Θ2 Ξ2) D.
Proof.
  intros * Hdt HPr Hμ.
  pose proof (decl_typed_sort_univ _ _ _ Hdt) as Hsu.
  pose proof (gctx_embedding_resolution _ _ _ _ (valid_gctx_embedding_embedding _ _ _ _ Hμ)) as Hs.
  pose proof (valid_gctx_embedding_wf _ _ _ _ Hμ) as Hg.
  assert (Harg : forall k Mk c gs j r A, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
             List.nth_error (cargs_nonrec gs) j = Some A -> List.nth_error (cargs_nonrec_kinds gs) j = Some r ->
             @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (nonrec_args_prefix gs j ++ im_params D Mk) (abs_kind_sort r (ind_sort D)[wk_shiftn (j + im_nn Mk)]ʷ) A A /\
             exists i : nat, @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (nonrec_args_prefix gs j ++ im_params D Mk) (abs_kind_sort r Typeω@i) A A).
  { intros * HMk Hcon HA0 Hr.
    destruct (nonrec_nth_split _ _ _ HA0) as (gs1 & gs2 & r0 & Heq & Hk).
    assert (r0 = r) as <- by (rewrite Heq, <- Hk, nonrec_kind_at in Hr; congruence).
    pose proof (decl_typed_args _ _ _ Hdt _ _ _ _ _ _ _ _ HMk (cons_lookup_in _ _ _ Hcon) Heq) as HT.
    pose proof (decl_typed_args_kind _ _ _ Hdt _ _ _ _ _ _ _ _ HMk (cons_lookup_in _ _ _ Hcon) Heq) as Hck.
    assert (Hls : List.length (cargs_strat gs1) = j) by (rewrite cargs_strat_nonrec, List.length_rev, length_cargs_nonrec_tele; exact Hk).
    rewrite Hls, (nonrec_args_prefix_cargs_strat gs1 (ca_arg r0 A :: gs2)), Hk, <- Heq in HT.
    pose proof (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ HT) as H.
    split; [ exact H |].
    destruct Hck; cbn [abs_kind_sort] in H |- *; [ exact (sort_large_sem _ _ _ _ Hsu H) | exists 0; exact H ]. }
  assert (Hstrat : forall k Mk c gs j, ind_member D k = Some Mk -> ind_con Mk c = Some gs -> j <= List.length (cargs_nonrec gs) ->
             @rel_ctx_wf (gc_mk Θ2 Ξ2) (nonrec_args_prefix gs j ++ im_params D Mk)).
  { intros k Mk c gs j HMk Hcon; induction j as [| j IH]; intros Hj.
    + unfold nonrec_args_prefix; cbn [List.firstn List.rev List.app].
      exact (rel_ctx_wf_of_embedding _ _ _ _ _ Hμ (member_params_wf _ _ _ _ _ Hdt HMk)).
    + destruct (nth_error_lt_some' (cargs_nonrec_tele gs) j ltac:(rewrite length_cargs_nonrec_tele; lia)) as [e He].
      destruct (proj1 (List.Forall_forall _ _) (tele_ass_cargs_nonrec_tele gs) e (List.nth_error_In _ _ He)) as (κ & A & ->).
      destruct (cargs_nonrec_tele_nth _ _ _ _ He) as [HA0 Hr].
      assert (Hst : nonrec_args_prefix gs (S j) = ce_ass κ A :: nonrec_args_prefix gs j).
      { unfold nonrec_args_prefix; rewrite (firstn_S_snoc _ _ _ He).
        rewrite List.rev_app_distr; reflexivity. }
      rewrite Hst; cbn [List.app].
      destruct (Harg _ _ _ _ _ _ _ HMk Hcon HA0 Hr) as (_ & i & Hi).
      exact (@rel_ctx_wf_ext_sort (gc_mk Θ2 Ξ2) _ _ _ _ (IH ltac:(lia)) (sort_kind_abs_kind_sort _ _) Hi). }
  assert (Hdom : forall k Mk c gs gs1 t gs2 j B, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
             gs = gs1 ++ ca_rec t :: gs2 -> List.nth_error (ptyp_doms t) j = Some B ->
             @rel_exp_under_ctx (gc_mk Θ2 Ξ2)
               (doms_ctx (List.firstn j (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk)
               ((ind_sort D)[wk_shiftn (j + List.length (cargs_nonrec gs1) + im_nn Mk)]ʷ) B B /\
             exists i : nat, @rel_exp_under_ctx (gc_mk Θ2 Ξ2)
               (doms_ctx (List.firstn j (ptyp_doms t)) ++ nonrec_args_prefix gs (List.length (cargs_nonrec gs1)) ++ im_params D Mk)
               (Typeω@i) B B).
  { intros * HMk Hcon Heq HB.
    assert (Hsplit : ptyp_doms t = List.firstn j (ptyp_doms t) ++ B :: List.skipn (S j) (ptyp_doms t))
      by (rewrite <- (skipn_nth_cons' _ _ _ HB), List.firstn_skipn; reflexivity).
    pose proof (decl_typed_doms _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ HMk (cons_lookup_in _ _ _ Hcon) Heq Hsplit) as HT.
    assert (Hk : List.length (List.firstn j (ptyp_doms t)) = j)
      by (rewrite List.length_firstn; assert (j < List.length (ptyp_doms t)) by (apply List.nth_error_Some; congruence); lia).
    assert (Hls : List.length (cargs_strat gs1) = List.length (cargs_nonrec gs1))
      by (rewrite cargs_strat_nonrec, List.length_rev, length_cargs_nonrec_tele; reflexivity).
    rewrite Hk, Hls, (nonrec_args_prefix_cargs_strat gs1 (ca_rec t :: gs2)), <- Heq in HT.
    pose proof (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ HT) as H.
    split; [ exact H | exact (sort_large_sem _ _ _ _ Hsu H) ]. }
  constructor.
  - destruct (decl_typed_uparams _ _ _ Hdt) as [HU _]; exact (rel_ctx_wf_of_embedding _ _ _ _ _ Hμ HU).
  - exists l; exact (rel_params_evaluated_of_embedding _ _ _ _ _ _ _ Hμ HPr).
  - destruct (decl_typed_sort _ _ _ Hdt) as [i HS]; exists i; exact (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ HS).
  - destruct (decl_typed_sort_lvl _ _ _ Hdt) as [n HS]; exists n; exact (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ HS).
  - intros * HMk; exact (rel_ctx_wf_of_embedding _ _ _ _ _ Hμ (member_params_wf _ _ _ _ _ Hdt HMk)).
  - intros * HMk; destruct (ind_ty_typed0 _ _ _ _ _ Hdt HMk) as [j Hj]; exists j.
    exact (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ Hj).
  - intros * HMk HA0.
    destruct (nparams_nth_split _ _ _ _ HA0) as [Δ1 HΔ1].
    assert (Hk : j < im_nn Mk) by (unfold im_nn; rewrite <- List.length_rev; apply List.nth_error_Some; congruence).
    pose proof (decl_typed_nparams _ _ _ Hdt _ _ _ _ _ _ HMk HΔ1) as HT; rewrite length_nparams_prefix in HT by lia.
    pose proof (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ HT) as H.
    split; [ exact H | exact (sort_large_sem _ _ _ _ Hsu H) ].
  - intros * HMk HA0.
    destruct (nparams_nth_split _ _ _ _ HA0) as [Δ1 HΔ1].
    exact (decl_typed_nparams_kind _ _ _ Hdt _ _ _ _ _ _ HMk HΔ1).
  - exact Hstrat.
  - exact Harg.
  - intros * HMk Hcon Hr.
    destruct (nonrec_kind_split _ _ _ Hr) as (gs1 & A & gs2 & Heq).
    exact (decl_typed_args_kind _ _ _ Hdt _ _ _ _ _ _ _ _ HMk (cons_lookup_in _ _ _ Hcon) Heq).
  - exact (decl_typed_nodup _ _ _ Hdt).
  - intros * HMk Hcon Heq HMj HPk HT.
    assert (Hls : List.length (cargs_nonrec gs1) = List.length (cargs_strat gs1))
      by (rewrite cargs_strat_nonrec, List.length_rev, length_cargs_nonrec_tele; reflexivity).
    rewrite Hls in HT.
    pose proof (decl_typed_rec_ps _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ HMk (cons_lookup_in _ _ _ Hcon) Heq HMj HPk HT) as H.
    rewrite (nonrec_args_prefix_cargs_strat gs1 (ca_rec t :: gs2)), <- Heq in H.
    exact (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ H).
  - exact Hdom.
  - intros * HMk Hcon; exact (decl_typed_params_length _ _ _ Hdt _ _ _ _ HMk (cons_lookup_in _ _ _ Hcon)).
  - intros k Mk c gs gs1 t gs2 j HMk Hcon Heq; induction j as [| j IH]; intros Hj.
    + cbn [List.firstn doms_ctx List.map List.rev List.app].
      apply (Hstrat k Mk c); [ exact HMk | exact Hcon | rewrite Heq, cargs_nonrec_app, List.length_app; lia ].
    + destruct (nth_error_lt_some' (ptyp_doms t) j ltac:(lia)) as [B HB].
      rewrite (firstn_S_snoc _ _ _ HB), doms_ctx_snoc; cbn [List.app].
      destruct (Hdom _ _ _ _ _ _ _ _ _ HMk Hcon Heq HB) as (_ & i & Hi).
      exact (@rel_ctx_wf_ext_typ (gc_mk Θ2 Ξ2) _ _ _ (IH ltac:(lia)) Hi).
  - destruct (decl_typed_selfs _ _ _ Hdt) as [IsS HV]; exists IsS.
    (** The containers, found at the source. *)
    pose proof (decl_typed_container _ _ _ _ D Hs Hdt) as Hcont.
    assert (Hcont2 : forall k Mk qc k' Is vm D' i' Mi' q'' k'' Is'' vm'' D'', ind_member D k = Some Mk ->
               im_head Mk = mh_view qc k' Is vm -> ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' ->
               im_head Mi' = mh_view q'' k'' Is'' vm'' -> ind_lookup Θ2 Ξ2 q'' = Some D'' -> ind_lookup Θ Ξ q'' = Some D'').
    { intros * HMk Hh Hq HMi' Hh' Hq2.
      exact (decl_typed_container _ _ _ _ D' Hs (proj1 (decl_of_glookup _ _ _ _ Hg Hq)) _ _ _ _ _ _ _ HMi' Hh' Hq2). }
    constructor.
    + exact (views_self_typed_link _ _ _ _ HV).
    + intros * HMk Hh Hq HI HT.
      apply (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ).
      eapply (views_self_typed_is _ _ _ _ HV); [ exact HMk | exact Hh | exact (Hcont _ _ _ _ _ _ _ HMk Hh Hq) | exact HI | exact HT ].
    + intros * HMk Hh Hq HMi' Hh' Hq'' Hv HMv HhMv HC HC' HT.
      pose proof (Hcont _ _ _ _ _ _ _ HMk Hh Hq) as HqS.
      apply (rel_exp_eq_of_embedding _ _ _ _ _ _ _ _ Hμ).
      eapply (views_self_typed_view_is _ _ _ _ HV);
        [ exact HMk | exact Hh | exact HqS | exact HMi' | exact Hh' | exact (Hcont2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMk Hh HqS HMi' Hh' Hq'')
        | exact Hv | exact HMv | exact HhMv | exact HC | exact HC' | exact HT ].
    + intros * HMk Hh Hq HMi' Hv HMv.
      apply (rel_ext_of_embedding _ _ _ _ _ _ _ Hμ).
      eapply (views_self_typed_nparams _ _ _ _ HV); [ exact HMk | exact Hh | exact (Hcont _ _ _ _ _ _ _ HMk Hh Hq) | exact HMi' | exact Hv | exact HMv ].
    + intros * HMk Hh Hq HMi' Hv HMv Hc' Hc0.
      apply (rel_ext_of_embedding _ _ _ _ _ _ _ Hμ).
      eapply (views_self_typed_args _ _ _ _ HV);
        [ exact HMk | exact Hh | exact (Hcont _ _ _ _ _ _ _ HMk Hh Hq) | exact HMi' | exact Hv | exact HMv | exact Hc' | exact Hc0 ].
    + intros * HMk Hh Hq HMi' Hv HMv Hc' Hc0 Heq' Heq Hl1 Hd.
      edestruct (views_self_typed_doms _ _ _ _ HV) as [i Hi];
        [ exact HMk | exact Hh | exact (Hcont _ _ _ _ _ _ _ HMk Hh Hq) | exact HMi' | exact Hv | exact HMv | exact Hc' | exact Hc0
        | exact Heq' | exact Heq | exact Hl1 | exact Hd |].
      exists i; exact (rel_exp_eq_of_embedding _ _ _ _ _ _ _ _ Hμ Hi).
    + intros * HMk Hh Hq HMi' Hv HMv Hc' Hc0 Heq' Heq Hl1 HMj HP' HP HT.
      apply (rel_exp_eq_of_embedding _ _ _ _ _ _ _ _ Hμ).
      eapply (views_self_typed_ps _ _ _ _ HV);
        [ exact HMk | exact Hh | exact (Hcont _ _ _ _ _ _ _ HMk Hh Hq) | exact HMi' | exact Hv | exact HMv | exact Hc' | exact Hc0
        | exact Heq' | exact Heq | exact Hl1 | exact HMj | exact HP' | exact HP | exact HT ].
    + intros * HMk Hh Hq.
      apply (rel_subtyp_of_embedding _ _ _ _ _ _ _ Hμ).
      eapply (views_self_typed_sort _ _ _ _ HV); [ exact HMk | exact Hh | exact (Hcont _ _ _ _ _ _ _ HMk Hh Hq) ].
    + exact (views_self_typed_record_link _ _ _ _ HV).
    + intros * HMk Hh HlR HI HT.
      destruct (rview_struct_record _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMk Hh) as [R' HR'].
      pose proof (rview_record_lookup _ _ _ _ _ _ HR') as HlR'.
      cbn in HlR; rewrite (record_lookup_gc_sub _ _ _ _ _ _ Hs HlR') in HlR; injection HlR as <-.
      apply (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ).
      exact (views_self_typed_record_instances _ _ _ _ HV _ _ _ _ _ _ _ _ _ HMk Hh HlR' HI HT).
    + intros * HMk Hh HlR Hcs.
      destruct (rview_struct_record _ _ _ (decl_typed_record_struct _ _ _ Hdt) _ _ _ _ _ HMk Hh) as [R' HR'].
      pose proof (rview_record_lookup _ _ _ _ _ _ HR') as HlR'.
      cbn in HlR; rewrite (record_lookup_gc_sub _ _ _ _ _ _ Hs HlR') in HlR; injection HlR as <-.
      apply (rel_ext_of_embedding _ _ _ _ _ _ _ Hμ).
      exact (views_self_typed_record_fields _ _ _ _ HV _ _ _ _ _ _ _ _ HMk Hh HlR' Hcs).
    + intros * HMk Hh; apply (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ).
      exact (views_self_typed_record_type _ _ _ _ HV _ _ _ _ _ HMk Hh).
Qed.

Lemma valid_entry_ind : forall Θ Ξ D l Θ2 Ξ2,
    decl_typed Θ Ξ D -> params_evaluated Θ Ξ nil (ind_uparams D) l ->
    bodies_valid_along_embeddings valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θ Ξ -> gctx_embedding_with_bodies Θ Ξ Θ2 Ξ2 -> valid_ind_decl_entry Θ2 Ξ2 D /\ valid_mod_tele Θ2 Ξ2 (ind_uparams D).
Proof.
  intros * Hdt HPr HG He.
  destruct (decl_typed_uparams _ _ _ Hdt) as [HUw HUa].
  pose proof (valid_gctx_embedding_of_bodies_valid _ _ _ _ (ctx_wf_gctx _ _ _ HUw) HG He) as Hμ.
  split; [ split; [ exact (valid_ind_decl_of_typed _ _ _ _ _ _ Hdt HPr Hμ) |] |].
  - intros k Mk Δ1 Δ2 HMk Hpar.
    assert (Hass : tele_ass (im_params D Mk))
      by (apply List.Forall_app; split; [ exact (decl_typed_nparams_ass _ _ _ Hdt _ _ HMk) | exact HUa ]).
    destruct (ind_ty_typed0 _ _ _ _ _ Hdt HMk) as [j Hj]; unfold ind_ty in Hj.
    pose proof (proj1 (ctx_pi_split_typed _ _ _ _ Hass Hj) _ _ Hpar) as H; rewrite app_nil_r in H.
    exists j; exact (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ H).
  - constructor; [ exact (rel_ctx_wf_of_embedding _ _ _ _ _ Hμ HUw) | exact HUa | exists l; exact (rel_params_evaluated_of_embedding _ _ _ _ _ _ _ Hμ HPr) ].
Qed.

(** A record declaration typed at the source is valid at the target: its
    judgments, read in the PER model. *)
Lemma valid_record_decl_of_typed : forall Θ Ξ R l Θ2 Ξ2, record_typed Θ Ξ R ->
    @rel_params_evaluated (gc_mk Θ2 Ξ2) nil (record_params R) l ->
    valid_gctx_embedding Θ Ξ Θ2 Ξ2 -> @valid_record_decl (gc_mk Θ2 Ξ2) R.
Proof.
  intros * Ht HPr Hμ.
  pose proof (typed_sort _ _ _ Ht) as HS.
  constructor.
  - exact (rel_ctx_wf_of_embedding _ _ _ _ _ Hμ (presup_is_univ_ctx HS)).
  - exists l; exact HPr.
  - destruct (wf_is_univ_typ HS) as [i Hi]; exists i; exact (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ Hi).
  - exact (rel_ctx_wf_of_embedding _ _ _ _ _ Hμ (record_typed_fctx_wf _ _ _ Ht _ (le_n _))).
  - intros * Hk; exact (valid_exp_under_ctx_of_embedding _ _ _ _ _ _ _ Hμ (typed_fields _ _ _ Ht _ _ _ Hk)).
  - exact (typed_field_kinds _ _ _ Ht).
Qed.

Lemma valid_entry_record : forall Θ Ξ R l Θ2 Ξ2,
    record_typed Θ Ξ R -> params_evaluated Θ Ξ nil (record_params R) l ->
    bodies_valid_along_embeddings valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θ Ξ ->
    gctx_embedding_with_bodies Θ Ξ Θ2 Ξ2 -> valid_record_decl_entry Θ2 Ξ2 R.
Proof.
  intros * Ht HPr HG He.
  pose proof (valid_gctx_embedding_of_bodies_valid _ _ _ _ (ctx_wf_gctx _ _ _ (presup_is_univ_ctx (typed_sort _ _ _ Ht))) HG He) as Hμ.
  exact (valid_record_decl_of_typed _ _ _ _ _ _ Ht (rel_params_evaluated_of_embedding _ _ _ _ _ _ _ Hμ HPr) Hμ).
Qed.

(** A record's module telescope, at a target where the record is found:
    its parameters, valid there, and a value of it, of the type former at
    the parameters as variables, a type of the sort. *)
Lemma valid_mod_tele_record : forall Θ Ξ p R Θ2 Ξ2,
    record_typed Θ Ξ R -> bodies_valid_along_embeddings valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry Θ Ξ ->
    gctx_embedding_with_bodies Θ Ξ Θ2 Ξ2 -> record_lookup Θ2 Ξ2 p = Some R ->
    valid_mod_tele Θ2 Ξ2 (record_params R) -> valid_mod_tele Θ2 Ξ2 (record_mod_tele p R).
Proof.
  intros * Ht HG He Hl [HP Ha [l0 Hr]].
  pose proof (valid_gctx_embedding_of_bodies_valid _ _ _ _ (ctx_wf_gctx _ _ _ (presup_is_univ_ctx (typed_sort _ _ _ Ht))) HG He) as Hμ.
  pose proof (valid_record_decl_of_typed _ _ _ _ _ _ Ht Hr Hμ) as Hvr; pose proof Hvr as [HPv HPrv [i HSv] HFv HTv HFk].
  assert (Hc : record_closed R) by exact (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ (gctx_embedding_with_bodies_wf _ _ _ _ He)) Hl).
  pose proof (@Records.Model.valid_exp_under_ctx_record (gc_mk Θ2 Ξ2) p R Hl Hc Ha (typed_nodup _ _ _ Ht)
                (record_typed_sort_univ _ _ _ Ht) HFv (ex_intro _ i HSv) HTv HPrv HFk) as HF0.
  pose proof (@valid_apps_vars (gc_mk Θ2 Ξ2) _ (record_params R) ⋅ (record_sort R) i (a_record p) eq_refl Ha
                ltac:(rewrite List.app_nil_r; exact HP) ltac:(rewrite List.app_nil_r; exact HSv) HF0) as Hself.
  rewrite List.app_nil_r in Hself; cbn [exp_wk] in Hself.
  (** The value's type is a type of a universe. *)
  assert (Hk : exists k, @rel_exp_under_ctx (gc_mk Θ2 Ξ2) (record_params R) (Typeω@k) (record_self p R) (record_self p R)).
  { unfold record_self.
    destruct (record_typed_sort_univ _ _ _ Ht) as [[j HU] | [L HU]]; rewrite HU in Hself.
    - exists j; exact Hself.
    - exists 0; exact (@rel_exp_suniv_tm_large (gc_mk Θ2 Ξ2) _ _ _ _ 0 Hself). }
  destruct Hk as [k Hk].
  (** The value is a relevant parameter: the sort is a universe. *)
  assert (Hsk : sort_exp_kind (record_sort R) = ak_relevant)
    by (destruct (record_typed_sort_univ _ _ _ Ht) as [[j HU] | [L HU]]; rewrite HU; reflexivity).
  unfold record_mod_tele; rewrite Hsk.
  constructor; [ exact (@rel_ctx_wf_extend (gc_mk Θ2 Ξ2) _ _ _ HP Hk) | constructor; [ do 2 eexists; reflexivity | exact Ha ] |].
  exists (max k l0); apply (@rel_params_evaluated_cons_iff (gc_mk Θ2 Ξ2)); split.
  - intros κ A [= _ <-]; rewrite List.app_nil_r; left; exact (@rel_exp_cumu_ge (gc_mk Θ2 Ξ2) k (max k l0) _ _ _ ltac:(lia) Hk).
  - exact (@rel_params_evaluated_ge (gc_mk Θ2 Ξ2) _ _ l0 (max k l0) ltac:(lia) Hr).
Qed.

(** ** Every well-formed global context embeds soundly into itself *)

Theorem valid_gctx_embedding_refl : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> valid_gctx_embedding Θ Ξ Θ Ξ.
Proof.
  intros * Hg; apply valid_gctx_embedding_of_bodies_valid; [ exact Hg | | apply gctx_embedding_with_bodies_refl; exact Hg ].
  exact (global_valid valid_entry valid_mod_tele valid_ind_decl_entry valid_record_decl_entry valid_entry_def valid_entry_ax valid_entry_alias valid_mod_tele_nil valid_entry_ind
           valid_entry_record valid_mod_tele_record _ _ Hg).
Qed.

(** ** The fundamental theorem at the identity embedding

    At the identity embedding, the semantic judgments of a global context
    [GC] are the relations at [GC]: the corollaries below state
    [completeness_fundamental] so for contexts, terms, term equality,
    subtyping and the module judgments.  There is no substitution part, and
    there cannot be: [wf_sub] constrains [σ] only at the indices [Δ] types,
    whereas [eval_sub] is total, so [⋅ ⊢ˢ (fun _ => zero $ zero) : ⋅] holds
    vacuously while its semantic counterpart would need [zero zero] to have
    a value.  The concrete semantic substitutions that are needed are built
    directly by the lemmas of [LogicalRelation/Substitution.v].  Context refinement and
    context equality are not separate judgments: they are [Δ ⊢ˢ Id : Γ] in
    one direction and in both. *)

Section FundamentalTheorem.
  Context {GC : GCtx}.

  (** The identity is sound at a well-formed global context. *)
  Lemma valid_gctx_embedding_refl_gc : ⊢ᵍ gc_deps ⍮ gc_stack -> valid_gctx_embedding gc_deps gc_stack gc_deps gc_stack.
  Proof. exact (valid_gctx_embedding_refl _ _). Qed.

  Corollary completeness_fundamental_ctx : forall Γ, ⊢ Γ -> ⊨ Γ.
  Proof.
    intros * H; pose proof (valid_gctx_embedding_refl_gc (ctx_wf_gctx _ _ _ H)) as Hid.
    destruct completeness_fundamental as (Kc & _).
    pose proof (valid_ctx_rel_ctx_wf (Kc _ _ _ H _ _ Hid)) as H'; destruct GC; exact H'.
  Qed.

  Corollary completeness_fundamental_exp : forall Γ M A, Γ ⊢ M : A -> Γ ⊨ M : A.
  Proof.
    intros * H; pose proof (valid_gctx_embedding_refl_gc (ctx_wf_gctx _ _ _ (presup_exp_ctx H))) as Hid.
    destruct completeness_fundamental as (_ & Ke & _).
    pose proof (sem_exp_eq_at_rel (Ke _ _ _ _ _ H _ _ Hid)) as H'; destruct GC; exact H'.
  Qed.

  Corollary completeness_fundamental_exp_eq : forall Γ M M' A, Γ ⊢ M ≈ M' : A -> Γ ⊨ M ≈ M' : A.
  Proof.
    intros * H; pose proof (valid_gctx_embedding_refl_gc (ctx_wf_gctx _ _ _ (presup_exp_eq_ctx H))) as Hid.
    destruct completeness_fundamental as (_ & _ & Kq & _).
    pose proof (sem_exp_eq_at_rel (Kq _ _ _ _ _ _ H _ _ Hid)) as H'; destruct GC; exact H'.
  Qed.

  Corollary completeness_fundamental_subtyp : forall Γ A A', Γ ⊢ A ⊆ A' -> Γ ⊨ A ⊆ A'.
  Proof.
    intros * H; pose proof (valid_gctx_embedding_refl_gc (ctx_wf_gctx _ _ _ (presup_subtyp_ctx H))) as Hid.
    destruct completeness_fundamental as (_ & _ & _ & Ks & _).
    pose proof (sem_subtyp_at_rel (Ks _ _ _ _ _ H _ _ Hid)) as H'; destruct GC; exact H'.
  Qed.

  (** The module judgments. *)
  Corollary completeness_fundamental_modules :
    (forall Γ Ψ Ψ', gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Γ ⊨ˣ Ψ ≈ Ψ') /\
      (forall Γ U U', gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U' -> Γ ⊨ᵘ U ≈ U') /\
      (forall Γ H H', gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H' -> Γ ⊨ᵐ H ≈ H').
  Proof.
    destruct completeness_fundamental as (_ & _ & _ & _ & _ & Kx & Ku & Km).
    split; [| split ]; intros * HJ;
      [ pose proof (valid_gctx_embedding_refl_gc (ctx_wf_gctx _ _ _ (presup_ext_eq_ctx HJ))) as Hid
      | pose proof (valid_gctx_embedding_refl_gc (ctx_wf_gctx _ _ _ (presup_unit_eq_ctx HJ))) as Hid
      | pose proof (valid_gctx_embedding_refl_gc (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HJ))) as Hid ];
      [ pose proof (sem_ext_eq_at_rel (Kx _ _ _ _ _ HJ _ _ Hid)) as HR
      | pose proof (sem_unit_eq_at_rel (Ku _ _ _ _ _ HJ _ _ Hid)) as HR
      | pose proof (sem_modexp_eq_at_rel (Km _ _ _ _ _ HJ _ _ Hid)) as HR ];
      destruct GC; exact HR.
  Qed.

End FundamentalTheorem.

Section Corollaries.
  Context {GC : GCtx}.

(** The substitution instance soundness needs, in its [Π]-β case, at
    any tag: the PER model of substitutions does not read it. *)
Corollary completeness_fundamental_sub_single : forall Γ κ M A,
    Γ ⊢ M : A ->
    Γ ⊨ˢ Id,,M : Γ ▹{κ} A.
Proof.
  intros * HM.
  pose proof (wf_exp_scoped_term _ _ _ _ _ HM) as Hs.
  apply completeness_fundamental_exp in HM.
  pose proof (presup_rel_exp_under_ctx HM) as [i HA].
  pose proof HM as [env_relΓ HΓ _ _].
  eapply rel_sub_under_ctx_extend;
    [ apply (rel_sub_id (ex_intro _ _ HΓ)) | eassumption | rewrite exp_sub_id; eassumption | exact Hs | exact Hs ].
Qed.

(** The weakening instance soundness needs, in its variable case.  [⟦A[↑]ʷ⟧(ρ)]
    and [⟦A⟧(ρ↯)] are not equal; this relatedness replaces the equation, and
    moving [P] and [El] along it with [glu_univ_elem_resp_per_univ] is all
    soundness does with it. *)
Corollary completeness_fundamental_typ_shift : forall {Γ e A} {i : nat} {env_rel ρ},
    ⊢ (e :: Γ)%list ->
    Γ ⊢ A : Typeω@i ->
    EF (e :: Γ)%list ≈ (e :: Γ)%list ∈ per_ctx_env ↘ env_rel ->
    Dom ρ ≈ ρ ∈ env_rel ->
    exists a a',
      ⟦ A[↑]ʷ ⟧ ρ ↘ a /\
      ⟦ A ⟧ ρ↯ ↘ a' /\
      Dom a ≈ a' ∈ per_univ i.
Proof.
  intros * ? ? Hper Hρ.
  assert ((e :: Γ)%list ⊨ʷ ↑ : Γ)
    by (apply rel_wk_under_ctx_shift, completeness_fundamental_ctx; eassumption).
  assert (Γ ⊨ A : Typeω@i) by (apply completeness_fundamental_exp; eassumption).
  destruct (rel_exp_of_typ_inversion_wk ltac:(eassumption) ltac:(eassumption))
    as [env_rel' [Hper' Hbridge]].
  handle_per_ctx_env_irrel.
  destruct (Hbridge _ _ Hρ) as [a [a' ?]].
  rewrite eval_wk_shift in *.
  exists a, a'; eassumption.
Qed.

End Corollaries.

#[export]
Hint Resolve completeness_fundamental_ctx completeness_fundamental_exp
             completeness_fundamental_exp_eq completeness_fundamental_subtyp
             completeness_fundamental_sub_single : mctt.
