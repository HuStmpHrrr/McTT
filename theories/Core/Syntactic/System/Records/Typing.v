(** * Records: Inversion and the Types of Projections

    The type former of a record is introduced by one rule, [wf_record],
    whose premises carry the declaration's typing; [wf_record_inversion]
    reads them off a derivation.  With them, the projections of two equal
    elements of a record type are equal at the fields' types, field by
    field ([record_pre_eq]): the type of each field at the projections
    before it moves along the equalities of those, as the closed telescope
    of the fields over the parameters instantiates ([record_field_typ_cong]). *)

From Stdlib Require Import Lia List PeanoNat.
From Stdlib Require String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export SystemOpt.
From Mctt.Core.Syntactic Require Import CoreInversions.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Syntactic.System.Records Require Export Syntax.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

  (** What the type former [a_record p] is typed by: the premises of
      [wf_record], and its type below [T]. *)
  #[warnings="-cannot-define-projection"]
  Record record_former_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (p : qname) (T : typ) : Prop := mk_record_former_inv
    { (** The declaration *)
      former_decl : record_decl
      (** It is filed at [p] *)
    ; former_lookup : record_lookup Θ Ξ p = Some former_decl
      (** Its field names are distinct *)
    ; former_nodup : List.NoDup (List.map fst (record_fields former_decl))
      (** Its parameters are assumptions *)
    ; former_params_ass : tele_ass (record_params former_decl)
      (** The universe of the type former's type *)
    ; former_level : nat
      (** The type former's type is a type *)
    ; former_ty_wf : Θ ⍮ Ξ ⍮ ⋅ ⊢ record_ty former_decl : Typeω@former_level
      (** The fields over the parameters are a context *)
    ; former_fctx_wf : ⊢ Θ ⍮ Ξ ⍮ record_fctx former_decl (List.length (record_fields former_decl)) ++ record_params former_decl
      (** The sort is a universe over the parameters *)
    ; former_sort : Θ ⍮ Ξ ⍮ record_params former_decl ⊢ᵤ record_sort former_decl
      (** Each field is a type of the sort over the fields before it *)
    ; former_fields : forall k f U, List.nth_error (record_fields former_decl) k = Some (f, U) ->
        Θ ⍮ Ξ ⍮ record_fctx former_decl k ++ record_params former_decl ⊢ U : (record_sort former_decl)[wk_shiftn k]ʷ
      (** The type former's type is below [T] *)
    ; former_sub : Θ ⍮ Ξ ⍮ Γ ⊢ record_ty former_decl ⊆ T }.

  Lemma wf_record_inversion : forall {Θ Ξ Γ p T}, Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : T -> record_former_inv Θ Ξ Γ p T.
  Proof.
    intros * H; dependent induction H.
    - econstructor; try eassumption; eapply wf_subtyp_of_typed; econstructor; eassumption.
    - destruct (IHwf_exp1 _ eq_refl) as [R Hl Hnd Hass i0 Hty Hf Hs HF Hsub].
      econstructor; try eassumption; eapply wf_subtyp_trans; eassumption.
  Qed.

  (** What a tuple is typed by: the premises of [wf_tuple], and its
      annotation below [A]. *)
  #[warnings="-cannot-define-projection"]
  Record record_tuple_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (T : typ) (fs : list (String.string * exp)) (A : typ) : Prop :=
    mk_record_tuple_inv
    { (** The record type's path *)
      tuple_path : qname
      (** Its declaration *)
    ; tuple_decl : record_decl
      (** The parameters the annotation is at *)
    ; tuple_params : list exp
      (** The universe of the annotation *)
    ; tuple_level : nat
      (** The annotation is a type *)
    ; tuple_typ : Θ ⍮ Ξ ⍮ Γ ⊢ T : Typeω@tuple_level
      (** It is the record type at the parameters *)
    ; tuple_eq : Θ ⍮ Ξ ⍮ Γ ⊢ T ≈ apps_exp (a_record tuple_path) tuple_params : Typeω@tuple_level
      (** The type former is typed *)
    ; tuple_former : Θ ⍮ Ξ ⍮ Γ ⊢ a_record tuple_path : record_ty tuple_decl
      (** The declaration is found at the path *)
    ; tuple_lookup : record_lookup Θ Ξ tuple_path = Some tuple_decl
      (** One parameter per parameter *)
    ; tuple_len : List.length tuple_params = List.length (record_params tuple_decl)
      (** Each typed at the parameters' telescope *)
    ; tuple_params_typed : forall k N B, List.nth_error tuple_params k = Some N ->
        List.nth_error (tele_insts (record_params tuple_decl) Id tuple_params) k = Some B -> Θ ⍮ Ξ ⍮ Γ ⊢ N : B
      (** The fields are named as the declaration's *)
    ; tuple_names : List.map fst fs = List.map fst (record_fields tuple_decl)
      (** Each field is typed at its type *)
    ; tuple_fields_typed : forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields tuple_decl) k = Some (f, U) ->
        Θ ⍮ Ξ ⍮ Γ ⊢ M : U[sb_of_list Id (tuple_params ++ List.firstn k (List.map snd fs))]
      (** The annotation is below [A] *)
    ; tuple_sub : Θ ⍮ Ξ ⍮ Γ ⊢ T ⊆ A }.

  Lemma wf_tuple_inversion : forall {Θ Ξ Γ T fs A}, Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs : A -> record_tuple_inv Θ Ξ Γ T fs A.
  Proof.
    intros * H; dependent induction H.
    - econstructor; try eassumption; eapply wf_subtyp_of_typed; econstructor; eassumption.
    - destruct (IHwf_exp1 _ _ eq_refl) as [p0 R0 Ns0 i0 HT0 HTe0 Hr0 Hl0 Hn0 HNs0 Hfs0 HMs0 Hsub0].
      econstructor; try eassumption; eapply wf_subtyp_trans; eassumption.
  Qed.

  (** What a projection is typed by: the premises of [wf_proj], and the
      field's type below [A]. *)
  #[warnings="-cannot-define-projection"]
  Record record_proj_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (f : String.string) (M : exp) (A : typ) : Prop :=
    mk_record_proj_inv
    { (** The record type's path *)
      proj_path : qname
      (** Its declaration *)
    ; proj_decl : record_decl
      (** The parameters of the element's type *)
    ; proj_params : list exp
      (** The field's position *)
    ; proj_index : nat
      (** The field's type *)
    ; proj_field_typ : typ
      (** The universe of the field's type there *)
    ; proj_level : nat
      (** The element is of the record type at the parameters *)
    ; proj_elem : Θ ⍮ Ξ ⍮ Γ ⊢ M : apps_exp (a_record proj_path) proj_params
      (** The type former is typed *)
    ; proj_former : Θ ⍮ Ξ ⍮ Γ ⊢ a_record proj_path : record_ty proj_decl
      (** The declaration is found at the path *)
    ; proj_lookup : record_lookup Θ Ξ proj_path = Some proj_decl
      (** One parameter per parameter *)
    ; proj_len : List.length proj_params = List.length (record_params proj_decl)
      (** Each typed at the parameters' telescope *)
    ; proj_params_typed : forall k N B, List.nth_error proj_params k = Some N ->
        List.nth_error (tele_insts (record_params proj_decl) Id proj_params) k = Some B -> Θ ⍮ Ξ ⍮ Γ ⊢ N : B
      (** The field is the declaration's at the position *)
    ; proj_field : List.nth_error (record_fields proj_decl) proj_index = Some (f, proj_field_typ)
      (** Its type there is a type *)
    ; proj_typ : Θ ⍮ Ξ ⍮ Γ ⊢ proj_field_typ[sb_of_list Id (proj_params ++ record_pre proj_decl proj_index M)] : Typeω@proj_level
      (** It is below [A] *)
    ; proj_sub : Θ ⍮ Ξ ⍮ Γ ⊢ proj_field_typ[sb_of_list Id (proj_params ++ record_pre proj_decl proj_index M)] ⊆ A }.

  Lemma wf_proj_inversion : forall {Θ Ξ Γ f M A}, Θ ⍮ Ξ ⍮ Γ ⊢ a_proj f M : A -> record_proj_inv Θ Ξ Γ f M A.
  Proof.
    intros * H; dependent induction H.
    - econstructor; try eassumption; eapply wf_subtyp_of_typed; econstructor; eassumption.
    - destruct (IHwf_exp1 _ _ eq_refl) as [p0 R0 Ns0 k0 U0 i0 HM0 Hr0 Hl0 Hn0 HNs0 Hfk0 HU0 Hsub0].
      econstructor; try eassumption; eapply wf_subtyp_trans; eassumption.
  Qed.

  (** The type former at its own type, from any typing of it, or of it
      applied. *)
  Lemma wf_record_own : forall Θ Ξ Γ p T R, Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : T -> record_lookup Θ Ξ p = Some R ->
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R.
  Proof.
    intros * H Hl; assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
    destruct (wf_record_inversion H) as [R0 Hl0 Hnd Hass i Hty HF HS HFs _].
    rewrite Hl in Hl0; injection Hl0 as <-; eapply wf_record; eassumption.
  Qed.

  Lemma wf_record_own_apps : forall Θ Ξ Γ p Ns T R, Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp (a_record p) Ns : T -> record_lookup Θ Ξ p = Some R ->
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R.
  Proof. intros * H Hl; destruct (wf_apps_head _ _ _ H) as [T' HT']; eapply wf_record_own; eassumption. Qed.

  (** ** The Fields over the Parameters *)

  Lemma record_fctx_ass : forall R k, tele_ass (record_fctx R k).
  Proof.
    intros; unfold record_fctx, tele_ass; apply List.Forall_rev, List.Forall_map, List.Forall_forall; intros; eauto.
  Qed.

  Lemma record_fctx_params_ass : forall R k, tele_ass (record_params R) -> tele_ass (record_fctx R k ++ record_params R).
  Proof. intros * H; apply List.Forall_app; split; [ apply record_fctx_ass | exact H ]. Qed.

  (** The first [k] fields over the parameters are a context, under any
      context. *)
  Lemma record_fctx_app_wf : forall Θ Ξ R k Γ, k <= List.length (record_fields R) -> record_closed R ->
      tele_ass (record_params R) ->
      ⊢ Θ ⍮ Ξ ⍮ record_fctx R (List.length (record_fields R)) ++ record_params R -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      ⊢ Θ ⍮ Ξ ⍮ (record_fctx R k ++ record_params R) ++ Γ.
  Proof.
    intros * Hk Hc Hass HF HΓ.
    apply wf_ctx_closed_app;
      [ apply record_fctx_params_ass; exact Hass
      | apply record_fctx_scoped; [ exact Hk | intros; eapply closed_fields; eassumption | exact (closed_params _ Hc) ]
      | | exact HΓ ].
    unfold record_fctx in HF |- *.
    rewrite List.firstn_all, <- (List.firstn_skipn k (record_fields R)), List.map_app, List.rev_app_distr in HF.
    rewrite <- List.app_assoc in HF; exact (ctx_app_wf_tail _ _ _ _ HF).
  Qed.

  (** A field's type is a type over the fields before it. *)
  Lemma record_field_typ_wf : forall Θ Ξ R k f U, List.nth_error (record_fields R) k = Some (f, U) ->
      ⊢ Θ ⍮ Ξ ⍮ record_fctx R (List.length (record_fields R)) ++ record_params R ->
      exists i, Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R ⊢ U : Typeω@i.
  Proof.
    intros * Hk HF.
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
    unfold record_fctx in HF |- *.
    rewrite List.firstn_all, <- (List.firstn_skipn (S k) (record_fields R)), (firstn_succ_nth _ _ _ Hk) in HF.
    rewrite !List.map_app, !List.rev_app_distr, <- !List.app_assoc in HF; cbn [List.map List.rev List.app] in HF.
    pose proof (ctx_app_wf_tail _ _ _ _ HF) as HF'.
    exact (ctx_decomp_right HF').
  Qed.

  Lemma tele_insts_cons_snoc : forall Δ T σ L x, tele_ass Δ -> List.length L = List.length Δ ->
      tele_insts (ce_ass T :: Δ) σ (L ++ x :: nil) = tele_insts Δ σ L ++ T[sb_of_list σ L] :: nil.
  Proof.
    intros * Hass Hl; change (ce_ass T :: Δ) with ((ce_ass T :: nil) ++ Δ).
    rewrite tele_insts_app by assumption; reflexivity.
  Qed.

  (** Equal instances of the fields' telescope give equal types to a field
      over it. *)
  Lemma record_field_typ_cong : forall Θ Ξ Γ R k f U Ms Ms',
      record_closed R -> tele_ass (record_params R) ->
      ⊢ Θ ⍮ Ξ ⍮ record_fctx R (List.length (record_fields R)) ++ record_params R -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.nth_error (record_fields R) k = Some (f, U) ->
      List.length Ms = k + List.length (record_params R) -> List.length Ms' = k + List.length (record_params R) ->
      (forall j N N' A, List.nth_error Ms j = Some N -> List.nth_error Ms' j = Some N' ->
         List.nth_error (tele_insts (record_fctx R k ++ record_params R) Id Ms) j = Some A -> Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A) ->
      exists i, Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id Ms] ≈ U[sb_of_list Id Ms'] : Typeω@i.
  Proof.
    intros * Hc Hass HF HΓ Hk HMl HMl' HMs.
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
    destruct (record_field_typ_wf _ _ _ _ _ _ Hk HF) as [i HU].
    assert (HΔΓ : ⊢ Θ ⍮ Ξ ⍮ (record_fctx R k ++ record_params R) ++ Γ) by (apply record_fctx_app_wf; auto; lia).
    assert (Hlen : List.length (record_fctx R k ++ record_params R) = k + List.length (record_params R))
      by (rewrite List.length_app, length_record_fctx by lia; reflexivity).
    assert (HUΓ : Θ ⍮ Ξ ⍮ (record_fctx R k ++ record_params R) ++ Γ ⊢ U : Typeω@i).
    { apply wf_exp_closed_app; [ apply record_fctx_params_ass; exact Hass
                               | apply record_fctx_scoped; [ lia | intros; eapply closed_fields; eassumption | exact (closed_params _ Hc) ]
                               | rewrite Hlen; exact (closed_fields _ Hc _ _ _ Hk) | cbn; exact I | exact HU | exact HΓ ]. }
    assert (Hσ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Ms ≈ sb_of_list Id Ms' : (record_fctx R k ++ record_params R) ++ Γ).
    { eapply wf_sub_eq_of_list; [ apply record_fctx_params_ass; exact Hass | exact HΔΓ | apply wf_sub_eq_refl; mauto 3
                                | rewrite Hlen; exact HMl | rewrite Hlen; exact HMl' | exact HMs ]. }
    exists i; exact (sub_eq_preserves_typ _ _ _ _ _ _ _ _ HUΓ Hσ).
  Qed.

  (** A term over a closed telescope, at equal instances of it. *)
  Lemma closed_tele_exp_cong : forall Θ Ξ Γ Δ M A Ms Ms',
      tele_ass Δ -> ctx_scoped 0 Δ -> exp_scoped (List.length Δ) M -> exp_scoped (List.length Δ) A ->
      Θ ⍮ Ξ ⍮ Δ ⊢ M : A -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Ms = List.length Δ -> List.length Ms' = List.length Δ ->
      (forall j N N' T, List.nth_error Ms j = Some N -> List.nth_error Ms' j = Some N' ->
         List.nth_error (tele_insts Δ Id Ms) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : T) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ M[sb_of_list Id Ms] ≈ M[sb_of_list Id Ms'] : A[sb_of_list Id Ms].
  Proof.
    intros * Hass Hs HsM HsA HM HΓ Hl Hl' HMs.
    assert (HΔ : ⊢ Θ ⍮ Ξ ⍮ Δ) by (gen_presups; assumption).
    assert (HΔΓ : ⊢ Θ ⍮ Ξ ⍮ Δ ++ Γ) by (apply wf_ctx_closed_app; assumption).
    pose proof (wf_exp_closed_app _ _ _ _ _ _ Hass Hs HsM HsA HM HΓ) as HMΓ.
    assert (Hσ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Ms ≈ sb_of_list Id Ms' : Δ ++ Γ)
      by (eapply wf_sub_eq_of_list; [ exact Hass | exact HΔΓ | apply wf_sub_eq_refl; mauto 3 | exact Hl | exact Hl' | exact HMs ]).
    exact (sub_eq_preserves_exp _ _ _ _ _ HMΓ _ _ _ Hσ).
  Qed.

  (** The sort at equal parameters. *)
  Lemma record_sort_inst_cong : forall Θ Ξ Γ R Ns Ns',
      record_closed R -> tele_ass (record_params R) -> Θ ⍮ Ξ ⍮ record_params R ⊢ᵤ record_sort R -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Ns = List.length (record_params R) -> List.length Ns' = List.length (record_params R) ->
      (forall j N N' T, List.nth_error Ns j = Some N -> List.nth_error Ns' j = Some N' ->
         List.nth_error (tele_insts (record_params R) Id Ns) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : T) ->
      exists i, Θ ⍮ Ξ ⍮ Γ ⊢ (record_sort R)[sb_of_list Id Ns] ≈ (record_sort R)[sb_of_list Id Ns'] : Typeω@i.
  Proof.
    intros * Hc Hass HS HΓ Hl Hl' HNs.
    destruct (wf_is_univ_typ HS) as [i Hi]; exists i.
    exact (closed_tele_exp_cong _ _ _ _ _ (Typeω@i) _ _ Hass (closed_params _ Hc) (closed_sort _ Hc) I Hi HΓ Hl Hl' HNs).
  Qed.

  (** The sort at parameters is below a large universe. *)
  Lemma record_sort_large : forall Θ Ξ Γ p R Ns,
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
      exists n, Θ ⍮ Ξ ⍮ Γ ⊢ (record_sort R)[sb_of_list Id Ns] ⊆ Typeω@n.
  Proof.
    intros * Hrt Hl Hn HNs.
    destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HS HFs _].
    rewrite Hl in Hl0; injection Hl0 as <-.
    assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
    pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
    pose proof (closed_sort _ Hc) as HsS.
    assert (HU : (exists j, record_sort R = Typeω@j) \/
                 (exists L m, record_sort R = Type⟨L⟩ /\ Θ ⍮ Ξ ⍮ record_params R ⊢ L : Level@m))
      by (inversion HS; subst; eauto 6).
    destruct HU as [[j Heq] | (L & m & Heq & HL)]; rewrite Heq in *.
    - exists j; cbn [exp_sub].
      eapply wf_subtyp_refl'; apply wf_exp_eq_refl; apply wf_typ; exact HΓ.
    - exists 0; cbn [exp_sub].
      eapply wf_subtyp_small_large; [ exact HΓ |].
      assert (HLL : Θ ⍮ Ξ ⍮ Γ ⊢ L[sb_of_list Id Ns] ≈ L[sb_of_list Id Ns] : Level@m[sb_of_list Id Ns]).
      { apply (closed_tele_exp_cong _ _ _ _ L (Level@m) _ _ Hass (closed_params _ Hc) ltac:(cbn in HsS; exact HsS) I HL HΓ Hn Hn).
        intros j0 N N' T HN HN' HT; rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; exact (HNs _ _ _ HN HT). }
      cbn [exp_sub] in HLL; gen_presups; eassumption.
  Qed.

  (** A field's type at equal instances of the fields' telescope, at the
      sort. *)
  Lemma record_field_sort_cong : forall Θ Ξ Γ R k f U Ns Ls Ms',
      record_closed R -> tele_ass (record_params R) ->
      (forall k f U, List.nth_error (record_fields R) k = Some (f, U) ->
         Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R ⊢ U : (record_sort R)[wk_shiftn k]ʷ) -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.nth_error (record_fields R) k = Some (f, U) ->
      List.length Ns = List.length (record_params R) -> List.length Ls = k ->
      List.length Ms' = k + List.length (record_params R) ->
      (forall j N N' A, List.nth_error (Ns ++ Ls) j = Some N -> List.nth_error Ms' j = Some N' ->
         List.nth_error (tele_insts (record_fctx R k ++ record_params R) Id (Ns ++ Ls)) j = Some A -> Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ Ls)] ≈ U[sb_of_list Id Ms'] : (record_sort R)[sb_of_list Id Ns].
  Proof.
    intros * Hc Hass HFs HΓ Hk HNl HLl HMl HMs.
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hk).
    assert (Hlen : List.length (record_fctx R k ++ record_params R) = k + List.length (record_params R))
      by (rewrite List.length_app, length_record_fctx by lia; reflexivity).
    replace ((record_sort R)[sb_of_list Id Ns]) with ((record_sort R)[wk_shiftn (List.length Ls)]ʷ[sb_of_list Id (Ns ++ Ls)])
      by apply exp_shift_past.
    rewrite HLl.
    apply (closed_tele_exp_cong _ _ _ (record_fctx R k ++ record_params R));
      [ apply record_fctx_params_ass; exact Hass
      | apply record_fctx_scoped; [ lia | intros; eapply closed_fields; eassumption | exact (closed_params _ Hc) ]
      | rewrite Hlen; exact (closed_fields _ Hc _ _ _ Hk)
      | rewrite Hlen; eapply exp_scoped_wk; [ exact (closed_sort _ Hc) | intros x Hx; unfold wk_shiftn; lia ]
      | exact (HFs _ _ _ Hk) | exact HΓ | rewrite List.length_app; lia | rewrite Hlen; exact HMl | exact HMs ].
  Qed.

  (** The parameters a record type is at: the right side of an equal
      instance is an instance, and the type former applies to equal
      instances equally. *)
  Lemma record_params_eq_right : forall Θ Ξ Γ R Xs Ys,
      record_closed R -> tele_ass (record_params R) ->
      ⊢ Θ ⍮ Ξ ⍮ record_fctx R (List.length (record_fields R)) ++ record_params R -> ⊢ Θ ⍮ Ξ ⍮ Γ ->
      List.length Xs = List.length (record_params R) -> List.length Ys = List.length (record_params R) ->
      (forall j X Y T, List.nth_error Xs j = Some X -> List.nth_error Ys j = Some Y ->
         List.nth_error (tele_insts (record_params R) Id Xs) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ Y : T) ->
      forall j Y T, List.nth_error Ys j = Some Y -> List.nth_error (tele_insts (record_params R) Id Ys) j = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊢ Y : T.
  Proof.
    intros * Hc Hass HF HΓ HXl HYl HXY j Y T HY HT.
    assert (HΔΓ : ⊢ Θ ⍮ Ξ ⍮ record_params R ++ Γ)
      by (pose proof (record_fctx_app_wf _ _ R 0 Γ ltac:(lia) Hc Hass HF HΓ) as H; exact H).
    assert (Hj : j < List.length Xs) by (rewrite HXl, <- HYl; exact (nth_error_lt_length _ _ _ HY)).
    destruct (nth_error_lt_some Xs j Hj) as [X HX].
    destruct (nth_error_lt_some (tele_insts (record_params R) Id Xs) j) as [T0 HT0].
    { rewrite length_tele_insts by exact Hass; lia. }
    destruct (tele_insts_cong (record_params R) Γ Γ Id Id Xs Ys Hass HΔΓ ltac:(apply wf_sub_eq_refl; mauto 3) HXl HYl HXY
                _ _ _ HT0 HT) as [i HTT].
    pose proof (HXY _ _ _ _ HX HY HT0) as HE.
    eapply wf_conv'; [| exact HTT ]; gen_presups; eassumption.
  Qed.

  Lemma wf_exp_eq_record_apps : forall Θ Ξ Γ p R Xs Ys,
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
      List.length Xs = List.length (record_params R) -> List.length Ys = List.length (record_params R) ->
      (forall j X Y T, List.nth_error Xs j = Some X -> List.nth_error Ys j = Some Y ->
         List.nth_error (tele_insts (record_params R) Id Xs) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ Y : T) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp (a_record p) Xs ≈ apps_exp (a_record p) Ys : (record_sort R)[sb_of_list Id Xs].
  Proof.
    intros * Hr Hl HXl HYl HXY.
    destruct (wf_record_inversion Hr) as [R0 Hl0 Hnd Hass i0 Hty HF HS HFs _].
    rewrite Hl in Hl0; injection Hl0 as <-.
    assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
    pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
    destruct (wf_is_univ_typ HS) as [i Hi].
    eapply wf_exp_eq_apps_closed_pi;
      [ exact Hass | exact (closed_params _ Hc) | exact (closed_sort _ Hc) | exact Hi | exact HΓ
      | apply wf_exp_eq_refl; exact Hr | exact HXl | exact HYl | exact HXY ].
  Qed.

  (** ** The Projections of Equal Elements *)

  Lemma record_pre_succ : forall R k f U M, List.nth_error (record_fields R) k = Some (f, U) ->
      record_pre R (S k) M = record_pre R k M ++ a_proj f M :: nil.
  Proof. intros * Hk; unfold record_pre; rewrite (firstn_succ_nth _ _ _ Hk), List.map_app; reflexivity. Qed.

  (** The parameters and the projections of two equal elements before the
      field [k] are equal at the instances of the fields' telescope. *)
  Lemma record_pre_eq : forall Θ Ξ Γ M M' p R Ns,
      Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : apps_exp (a_record p) Ns ->
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
      List.length Ns = List.length (record_params R) ->
      (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
      forall k, k <= List.length (record_fields R) ->
      forall j N N' A, List.nth_error (Ns ++ record_pre R k M) j = Some N -> List.nth_error (Ns ++ record_pre R k M') j = Some N' ->
        List.nth_error (tele_insts (record_fctx R k ++ record_params R) Id (Ns ++ record_pre R k M)) j = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A.
  Proof.
    intros * HMM Hr Hl Hn HNs.
    destruct (wf_record_inversion Hr) as [R0 Hl0 Hnd Hass i Hty HF HS HFs _].
    rewrite Hl in Hl0; injection Hl0 as <-.
    assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
    pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
    assert (HM' : Θ ⍮ Ξ ⍮ Γ ⊢ M' : apps_exp (a_record p) Ns) by (gen_presups; assumption).
    induction k as [| k IH]; intros Hk j N N' A HN HN' HA.
    - cbn [record_pre List.firstn List.map] in HN, HN', HA; rewrite List.app_nil_r in HN, HN', HA.
      cbn [record_fctx List.firstn List.map List.rev List.app] in HA.
      rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; exact (HNs _ _ _ HN HA).
    - destruct (List.nth_error (record_fields R) k) as [[f U] |] eqn:Hfk; [| apply List.nth_error_None in Hfk; lia ].
      rewrite (record_pre_succ _ _ _ _ M Hfk), List.app_assoc in HN, HA.
      rewrite (record_pre_succ _ _ _ _ M' Hfk), List.app_assoc in HN'.
      rewrite (record_fctx_succ _ _ _ _ Hfk), <- List.app_comm_cons in HA.
      assert (HlL : List.length (Ns ++ record_pre R k M) = k + List.length (record_params R))
        by (rewrite List.length_app, length_record_pre by lia; lia).
      assert (HlL' : List.length (Ns ++ record_pre R k M') = k + List.length (record_params R))
        by (rewrite List.length_app, length_record_pre by lia; lia).
      rewrite tele_insts_cons_snoc in HA
        by (try (apply record_fctx_params_ass; exact Hass); rewrite HlL, List.length_app, length_record_fctx by lia; lia).
      pose proof (IH ltac:(lia)) as IHk.
      destruct (record_field_typ_cong _ _ _ _ _ _ _ _ _ Hc Hass HF HΓ Hfk HlL HlL' IHk) as [i0 HUU].
      assert (HUl : Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k M)] : Typeω@i0) by (gen_presups; assumption).
      assert (HUr : Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k M')] : Typeω@i0) by (gen_presups; assumption).
      assert (Hlen : List.length (tele_insts (record_fctx R k ++ record_params R) Id (Ns ++ record_pre R k M))
                     = k + List.length (record_params R)).
      { rewrite length_tele_insts by (apply record_fctx_params_ass; exact Hass).
        rewrite List.length_app, length_record_fctx, HlL by lia; lia. }
      destruct (Nat.lt_ge_cases j (k + List.length (record_params R))) as [Hj | Hj].
      + rewrite List.nth_error_app1 in HN, HA by lia; rewrite List.nth_error_app1 in HN' by lia.
        exact (IHk _ _ _ _ HN HN' HA).
      + rewrite List.nth_error_app2 in HN, HA by lia; rewrite List.nth_error_app2 in HN' by lia.
        rewrite HlL in HN; rewrite HlL' in HN'; rewrite Hlen in HA.
        replace (j - (k + List.length (record_params R))) with 0 in HN, HN', HA by
          (destruct (j - (k + List.length (record_params R))) eqn:E; [ reflexivity |];
           exfalso; cbn in HN; destruct n; discriminate).
        cbn in HN, HN', HA; injection HN as <-; injection HN' as <-; injection HA as <-.
        assert (Hp : Θ ⍮ Ξ ⍮ Γ ⊢ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R k M)])
          by (eapply wf_proj; [ gen_presups; eassumption | exact Hr | exact Hl | exact Hn | exact HNs | exact Hfk | exact HUl ]).
        assert (Hp' : Θ ⍮ Ξ ⍮ Γ ⊢ a_proj f M' : U[sb_of_list Id (Ns ++ record_pre R k M')])
          by (eapply wf_proj; [ exact HM' | exact Hr | exact Hl | exact Hn | exact HNs | exact Hfk | exact HUr ]).
        eapply wf_exp_eq_proj_cong; [ exact HMM | exact Hr | exact Hl | exact Hn | exact HNs | exact Hfk | exact HUl |].
        eapply wf_conv'; [ exact Hp' | symmetry; exact HUU ].
  Qed.

  (** So a field's types at the projections of two equal elements are
      equal. *)
  Corollary record_proj_typ_eq : forall Θ Ξ Γ M M' p R Ns k f U,
      Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : apps_exp (a_record p) Ns ->
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
      List.length Ns = List.length (record_params R) ->
      (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
      List.nth_error (record_fields R) k = Some (f, U) ->
      exists i, Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k M)] ≈ U[sb_of_list Id (Ns ++ record_pre R k M')] : Typeω@i.
  Proof.
    intros * HMM Hr Hl Hn HNs Hfk.
    destruct (wf_record_inversion Hr) as [R0 Hl0 Hnd Hass i Hty HF HS HFs _].
    rewrite Hl in Hl0; injection Hl0 as <-.
    assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
    eapply record_field_typ_cong;
      [ exact (wf_record_closed _ _ _ _ _ HΓ Hl) | exact Hass | exact HF | exact HΓ | exact Hfk
      | rewrite List.length_app, length_record_pre by lia; lia | rewrite List.length_app, length_record_pre by lia; lia |].
    exact (record_pre_eq _ _ _ _ _ _ _ _ HMM Hr Hl Hn HNs k ltac:(lia)).
  Qed.

  (** ** Instances along a Weakening, and η-Expansions *)

  Lemma record_field_wk : forall R k f U Ns L φ, record_closed R -> List.nth_error (record_fields R) k = Some (f, U) ->
      List.length Ns = List.length (record_params R) -> List.length L = k ->
      U[sb_of_list Id (Ns ++ L)][φ]ʷ = U[sb_of_list Id (List.map (fun N => N[φ]ʷ) Ns ++ List.map (fun N => N[φ]ʷ) L)].
  Proof.
    intros * HR Hk HN HL; rewrite <- exp_sub_of_wk, (record_field_sub _ _ _ _ _ _ _ HR Hk HN HL), !map_sub_of_wk; reflexivity.
  Qed.

  Lemma record_pre_wk : forall R k M φ, List.map (fun N => N[φ]ʷ) (record_pre R k M) = record_pre R k M[φ]ʷ.
  Proof. intros; unfold record_pre; rewrite List.map_map; reflexivity. Qed.

  (** The values of the first fields of an η-expansion are the projections
      before them. *)
  Lemma record_eta_fields_pre : forall R k M, List.firstn k (List.map snd (record_eta_fields R M)) = record_pre R k M.
  Proof. intros; unfold record_eta_fields, record_pre; rewrite List.map_map, List.firstn_map; reflexivity. Qed.

  Lemma record_eta_fields_names : forall R M, List.map fst (record_eta_fields R M) = List.map fst (record_fields R).
  Proof. intros; unfold record_eta_fields; rewrite List.map_map; reflexivity. Qed.

  Lemma record_eta_fields_nth : forall R M k f U, List.nth_error (record_fields R) k = Some (f, U) ->
      List.nth_error (record_eta_fields R M) k = Some (f, a_proj f M).
  Proof. intros * Hk; unfold record_eta_fields; rewrite List.nth_error_map, Hk; reflexivity. Qed.

  (** ** Projections, η-Expansions and Tuples at a Universe

      Below, the sort of the record type at its parameters is below a
      universe [Typeω@n], which then holds the fields' types. *)

  (** The projections of equal elements are equal, at the field's type at
      the projections of the left one; the field's types at both are
      equal. *)
  Lemma record_proj_cong_at : forall Θ Ξ Γ M M' p R Ns n k f U,
      Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : apps_exp (a_record p) Ns ->
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ (record_sort R)[sb_of_list Id Ns] ⊆ Typeω@n ->
      List.nth_error (record_fields R) k = Some (f, U) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k M)] ≈ U[sb_of_list Id (Ns ++ record_pre R k M')] : Typeω@n /\
      Θ ⍮ Ξ ⍮ Γ ⊢ a_proj f M ≈ a_proj f M' : U[sb_of_list Id (Ns ++ record_pre R k M)].
  Proof.
    intros * HMM Hrt Hl Hn HNs HS Hfk.
    destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HSu HFs _].
    rewrite Hl in Hl0; injection Hl0 as <-.
    assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
    pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
    pose proof (record_pre_eq _ _ _ _ _ _ _ _ HMM Hrt Hl Hn HNs k ltac:(lia)) as Hpe.
    pose proof (record_field_sort_cong _ _ _ R k f U Ns (record_pre R k M) (Ns ++ record_pre R k M')
                  Hc Hass HFs HΓ Hfk Hn
                  ltac:(apply length_record_pre; lia) ltac:(rewrite List.length_app, length_record_pre by lia; lia) Hpe) as HTT.
    assert (HTTn : Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k M)] ≈ U[sb_of_list Id (Ns ++ record_pre R k M')] : Typeω@n)
      by (eapply wf_exp_eq_subtyp'; [ exact HTT | exact HS ]).
    assert (HUl : Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k M)] : Typeω@n) by (gen_presups; eassumption).
    assert (Hp' : Θ ⍮ Ξ ⍮ Γ ⊢ a_proj f M' : U[sb_of_list Id (Ns ++ record_pre R k M')])
      by (eapply wf_proj; [ gen_presups; eassumption | exact Hrt | exact Hl | exact Hn | exact HNs | exact Hfk | gen_presups; eassumption ]).
    split; [ exact HTTn |].
    eapply wf_exp_eq_proj_cong; [ exact HMM | exact Hrt | exact Hl | exact Hn | exact HNs | exact Hfk | exact HUl |].
    eapply wf_conv'; [ exact Hp' | symmetry; exact HTTn ].
  Qed.

  (** The η-expansion of an element of a record type is one. *)
  Lemma wf_record_eta_tuple : forall Θ Ξ Γ M p R Ns n,
      Θ ⍮ Ξ ⍮ Γ ⊢ M : apps_exp (a_record p) Ns ->
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ (record_sort R)[sb_of_list Id Ns] ⊆ Typeω@n ->
      Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp (a_record p) Ns : Typeω@n ->
      Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple (apps_exp (a_record p) Ns) (record_eta_fields R M) : apps_exp (a_record p) Ns.
  Proof.
    intros * HM Hrt Hl Hn HNs HS HT.
    eapply wf_tuple; [ exact HT | apply wf_exp_eq_refl; exact HT | exact Hrt | exact Hl | exact Hn | exact HNs
                     | apply record_eta_fields_names |].
    intros k f N U Hk Hfk.
    rewrite (record_eta_fields_nth _ M _ _ _ Hfk) in Hk; injection Hk as <-.
    rewrite record_eta_fields_pre.
    destruct (record_proj_cong_at _ _ _ M M p R Ns n k f U ltac:(apply wf_exp_eq_refl; exact HM) Hrt Hl Hn HNs HS Hfk)
      as [_ Hpp].
    gen_presups; eassumption.
  Qed.

  (** The parameters and the fields of two tuples equal field by field,
      each at its type at the left one's parameters and fields before it,
      are equal at the instances of the fields' telescope. *)
  Lemma record_fields_insts_eq : forall Θ Ξ Γ p R Ns Ns' (fs fs' : list (String.string * exp)),
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
      List.length Ns = List.length (record_params R) -> List.length Ns' = List.length (record_params R) ->
      (forall j X Y T, List.nth_error Ns j = Some X -> List.nth_error Ns' j = Some Y ->
         List.nth_error (tele_insts (record_params R) Id Ns) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ Y : T) ->
      List.map fst fs = List.map fst (record_fields R) -> List.map fst fs' = List.map fst fs ->
      (forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
         List.nth_error (record_fields R) k = Some (f, U) ->
         Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
      forall k, k <= List.length (record_fields R) ->
      forall j N N' A, List.nth_error (Ns ++ List.firstn k (List.map snd fs)) j = Some N ->
        List.nth_error (Ns' ++ List.firstn k (List.map snd fs')) j = Some N' ->
        List.nth_error (tele_insts (record_fctx R k ++ record_params R) Id (Ns ++ List.firstn k (List.map snd fs))) j = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A.
  Proof.
    intros * Hrt Hl Hn Hn' HNN Hfs Hfs' HMM.
    destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i Hty HF HS HFs _].
    rewrite Hl in Hl0; injection Hl0 as <-.
    assert (Hlf : List.length fs = List.length (record_fields R))
      by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
    assert (Hlf' : List.length fs' = List.length fs)
      by (rewrite <- (List.length_map fst fs'), <- (List.length_map fst fs), Hfs'; reflexivity).
    induction k as [| k IH]; intros Hk j N N' A HN HN' HA.
    - cbn [List.firstn] in HN, HN', HA; rewrite List.app_nil_r in HN, HN', HA.
      cbn [record_fctx List.firstn List.map List.rev List.app] in HA.
      exact (HNN _ _ _ _ HN HN' HA).
    - destruct (List.nth_error (record_fields R) k) as [[f U] |] eqn:Hfk; [| apply List.nth_error_None in Hfk; lia ].
      destruct (nth_error_lt_some fs k ltac:(lia)) as [[g M] Hg].
      destruct (nth_error_lt_some fs' k ltac:(lia)) as [[g' M'] Hg'].
      assert (g = f) as ->.
      { pose proof (List.map_nth_error fst _ _ Hg) as E1; pose proof (List.map_nth_error fst _ _ Hfk) as E2.
        rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
      assert (g' = f) as ->.
      { pose proof (List.map_nth_error fst _ _ Hg') as E1; pose proof (List.map_nth_error fst _ _ Hg) as E2.
        rewrite Hfs' in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
      assert (Hs : List.firstn (S k) (List.map snd fs) = List.firstn k (List.map snd fs) ++ M :: nil)
        by (apply firstn_succ_nth; rewrite List.nth_error_map, Hg; reflexivity).
      assert (Hs' : List.firstn (S k) (List.map snd fs') = List.firstn k (List.map snd fs') ++ M' :: nil)
        by (apply firstn_succ_nth; rewrite List.nth_error_map, Hg'; reflexivity).
      rewrite Hs, List.app_assoc in HN, HA; rewrite Hs', List.app_assoc in HN'.
      rewrite (record_fctx_succ _ _ _ _ Hfk), <- List.app_comm_cons in HA.
      assert (HlL : List.length (Ns ++ List.firstn k (List.map snd fs)) = k + List.length (record_params R))
        by (rewrite List.length_app, List.length_firstn, List.length_map; lia).
      assert (HlL' : List.length (Ns' ++ List.firstn k (List.map snd fs')) = k + List.length (record_params R))
        by (rewrite List.length_app, List.length_firstn, List.length_map; lia).
      rewrite tele_insts_cons_snoc in HA
        by (try (apply record_fctx_params_ass; exact Hass); rewrite HlL, List.length_app, length_record_fctx by lia; lia).
      pose proof (IH ltac:(lia)) as IHk.
      assert (Hlen : List.length (tele_insts (record_fctx R k ++ record_params R) Id (Ns ++ List.firstn k (List.map snd fs)))
                     = k + List.length (record_params R)).
      { rewrite length_tele_insts by (apply record_fctx_params_ass; exact Hass).
        rewrite List.length_app, length_record_fctx by lia; lia. }
      destruct (Nat.lt_ge_cases j (k + List.length (record_params R))) as [Hj | Hj].
      + rewrite List.nth_error_app1 in HN, HA by lia; rewrite List.nth_error_app1 in HN' by lia.
        exact (IHk _ _ _ _ HN HN' HA).
      + rewrite List.nth_error_app2 in HN, HA by lia; rewrite List.nth_error_app2 in HN' by lia.
        rewrite HlL in HN; rewrite HlL' in HN'; rewrite Hlen in HA.
        replace (j - (k + List.length (record_params R))) with 0 in HN, HN', HA by
          (destruct (j - (k + List.length (record_params R))) eqn:E; [ reflexivity |];
           exfalso; cbn in HN; destruct n; discriminate).
        cbn in HN, HN', HA; injection HN as <-; injection HN' as <-; injection HA as <-.
        exact (HMM _ _ _ _ _ Hg Hg' Hfk).
  Qed.

  (** A field's type at the projections of an element, at equal
      parameters. *)
  Lemma record_field_params_cong : forall Θ Ξ Γ M p R Ns Ns' n k f U,
      Θ ⍮ Ξ ⍮ Γ ⊢ M : apps_exp (a_record p) Ns ->
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
      List.length Ns = List.length (record_params R) -> List.length Ns' = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
      (forall j X Y T, List.nth_error Ns j = Some X -> List.nth_error Ns' j = Some Y ->
         List.nth_error (tele_insts (record_params R) Id Ns) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ Y : T) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ (record_sort R)[sb_of_list Id Ns] ⊆ Typeω@n ->
      List.nth_error (record_fields R) k = Some (f, U) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k M)] ≈ U[sb_of_list Id (Ns' ++ record_pre R k M)] : Typeω@n.
  Proof.
    intros * HM Hrt Hl Hn Hn' HNs HNN HS Hfk.
    destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i Hty HF HSu HFs _].
    rewrite Hl in Hl0; injection Hl0 as <-.
    assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
    pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
    eapply wf_exp_eq_subtyp'; [| exact HS ].
    eapply (record_field_sort_cong _ _ _ R k f U Ns (record_pre R k M) (Ns' ++ record_pre R k M));
      [ exact Hc | exact Hass | exact HFs | exact HΓ | exact Hfk | exact Hn | apply length_record_pre; lia
      | rewrite List.length_app, length_record_pre by lia; lia |].
    rewrite <- !(record_eta_fields_pre R k M).
    eapply (record_fields_insts_eq _ _ _ p R Ns Ns' (record_eta_fields R M) (record_eta_fields R M));
      [ exact Hrt | exact Hl | exact Hn | exact Hn' | exact HNN | apply record_eta_fields_names | reflexivity | | lia ].
    intros k' f' M1 M1' U' Hk1 Hk1' Hfk'.
    rewrite (record_eta_fields_nth _ M _ _ _ Hfk') in Hk1, Hk1'; injection Hk1 as <-; injection Hk1' as <-.
    rewrite record_eta_fields_pre.
    exact (proj2 (record_proj_cong_at _ _ _ M M p R Ns n k' f' U' ltac:(apply wf_exp_eq_refl; exact HM) Hrt Hl Hn HNs HS Hfk')).
  Qed.

  (** Two tuples at equal parameters, equal field by field, each at its
      type at the left one's parameters and fields before it. *)
  Lemma wf_exp_eq_tuple_fields : forall Θ Ξ Γ p R Ns Ns' n (fs fs' : list (String.string * exp)),
      Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple (apps_exp (a_record p) Ns) fs : apps_exp (a_record p) Ns ->
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
      List.length Ns = List.length (record_params R) -> List.length Ns' = List.length (record_params R) ->
      (forall j X Y T, List.nth_error Ns j = Some X -> List.nth_error Ns' j = Some Y ->
         List.nth_error (tele_insts (record_params R) Id Ns) j = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ Y : T) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ (record_sort R)[sb_of_list Id Ns] ⊆ Typeω@n ->
      List.map fst fs = List.map fst (record_fields R) -> List.map fst fs' = List.map fst fs ->
      (forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
         List.nth_error (record_fields R) k = Some (f, U) ->
         Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple (apps_exp (a_record p) Ns) fs ≈ a_tuple (apps_exp (a_record p) Ns') fs' : apps_exp (a_record p) Ns.
  Proof.
    intros * Ht Hrt Hl Hn Hn' HNN HS Hfs Hfs' HMM.
    destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i Hty HF HSu HFs _].
    rewrite Hl in Hl0; injection Hl0 as <-.
    assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
    pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
    assert (HappsU : Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp (a_record p) Ns ≈ apps_exp (a_record p) Ns' : Typeω@n)
      by (eapply wf_exp_eq_subtyp'; [ exact (wf_exp_eq_record_apps _ _ _ _ _ _ _ Hrt Hl Hn Hn' HNN) | exact HS ]).
    assert (HNt' : forall j Y T, List.nth_error Ns' j = Some Y -> List.nth_error (tele_insts (record_params R) Id Ns') j = Some T ->
               Θ ⍮ Ξ ⍮ Γ ⊢ Y : T)
      by (eapply (record_params_eq_right _ _ _ R Ns Ns'); eassumption).
    assert (Hlf : List.length fs = List.length (record_fields R))
      by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
    assert (Hlf' : List.length fs' = List.length fs)
      by (rewrite <- (List.length_map fst fs'), <- (List.length_map fst fs), Hfs'; reflexivity).
    pose proof (record_fields_insts_eq _ _ _ p R Ns Ns' fs fs' Hrt Hl Hn Hn' HNN Hfs Hfs' HMM) as Hins.
    assert (HNt : forall j X T, List.nth_error Ns j = Some X -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some T ->
               Θ ⍮ Ξ ⍮ Γ ⊢ X : T).
    { intros j X T HX HT.
      assert (Hj : j < List.length Ns') by (rewrite Hn', <- Hn; exact (nth_error_lt_length _ _ _ HX)).
      destruct (nth_error_lt_some Ns' j Hj) as [Y HY].
      pose proof (HNN _ _ _ _ HX HY HT) as HXY; gen_presups; assumption. }
    eapply wf_exp_eq_tuple_cong; [ exact Ht | exact HappsU | apply wf_exp_eq_refl; gen_presups; eassumption
                                 | exact Hl | exact Hn | exact HNt | exact Hfs | exact Hfs' | exact HMM |].
    eapply wf_conv'; [| symmetry; exact HappsU ].
    eapply wf_tuple; [ gen_presups; eassumption | apply wf_exp_eq_refl; gen_presups; eassumption | exact Hrt | exact Hl
                     | exact Hn' | exact HNt' | rewrite Hfs'; exact Hfs |].
    intros k f M' U Hk' Hfk.
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
    destruct (nth_error_lt_some fs k ltac:(lia)) as [[g M] Hg].
    assert (g = f) as ->.
    { pose proof (List.map_nth_error fst _ _ Hg) as E1; pose proof (List.map_nth_error fst _ _ Hfk) as E2.
      rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
    pose proof (HMM _ _ _ _ _ Hg Hk' Hfk) as HE.
    pose proof (record_field_sort_cong _ _ _ R k f U Ns (List.firstn k (List.map snd fs)) (Ns' ++ List.firstn k (List.map snd fs'))
                  Hc Hass HFs HΓ Hfk Hn ltac:(rewrite List.length_firstn, List.length_map; lia)
                  ltac:(rewrite List.length_app, List.length_firstn, List.length_map; lia) (Hins k ltac:(lia))) as HTT.
    eapply wf_conv'; [ gen_presups; eassumption | eapply wf_exp_eq_subtyp'; [ exact HTT | exact HS ] ].
  Qed.

  (** The entries and names of a list of pairs. *)
  Lemma nth_error_combine_both : forall {A B : Type} (l1 : list A) (l2 : list B) k x y,
      List.nth_error l1 k = Some x -> List.nth_error l2 k = Some y -> List.nth_error (List.combine l1 l2) k = Some (x, y).
  Proof.
    induction l1 as [| a l1 IH]; intros [| b l2] [| k] * H1 H2; cbn in *; try discriminate; [ congruence | auto ].
  Qed.

  Lemma map_fst_combine : forall {A B : Type} (l1 : list A) (l2 : list B),
      List.length l1 = List.length l2 -> List.map fst (List.combine l1 l2) = l1.
  Proof. induction l1 as [| a l1 IH]; intros [| b l2] H; cbn in *; try discriminate; [ reflexivity | f_equal; auto ]. Qed.

  (** ** The Projections of a Tuple *)

  (** The field [k] of a tuple whose projections before it are its fields
      before it, at the fields' telescope: the field's types at both are
      equal, and its projection is its field, by field-β. *)
  Lemma tuple_field_step : forall Θ Ξ Γ T fs p R Ns i,
      Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs : T ->
      Θ ⍮ Ξ ⍮ Γ ⊢ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
      List.map fst fs = List.map fst (record_fields R) ->
      (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
         Θ ⍮ Ξ ⍮ Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
      forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
      (forall j N N' A, List.nth_error (Ns ++ record_pre R k (a_tuple T fs)) j = Some N ->
         List.nth_error (Ns ++ List.firstn k (List.map snd fs)) j = Some N' ->
         List.nth_error (tele_insts (record_fctx R k ++ record_params R) Id (Ns ++ record_pre R k (a_tuple T fs))) j = Some A ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k (a_tuple T fs))]
        ≈ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] : (record_sort R)[sb_of_list Id Ns] /\
      Θ ⍮ Ξ ⍮ Γ ⊢ a_proj f (a_tuple T fs) ≈ M : U[sb_of_list Id (Ns ++ record_pre R k (a_tuple T fs))].
  Proof.
    intros * Ht HT Hrt Hl Hn HNs Hfs HMs k f M U Hk Hfk Hpre.
    destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i1 Hty HF HS HFs _].
    rewrite Hl in Hl0; injection Hl0 as <-.
    assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
    pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
    assert (Hlf : List.length fs = List.length (record_fields R))
      by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
    destruct (record_field_typ_cong _ _ _ _ _ _ _ (Ns ++ record_pre R k (a_tuple T fs)) (Ns ++ List.firstn k (List.map snd fs))
                Hc Hass HF HΓ Hfk ltac:(rewrite List.length_app, length_record_pre by lia; lia)
                ltac:(rewrite List.length_app, List.length_firstn, List.length_map; lia) Hpre) as [i0 HUU].
    split.
    { eapply record_field_sort_cong; [ exact Hc | exact Hass | exact HFs | exact HΓ | exact Hfk | exact Hn
                                     | apply length_record_pre; lia
                                     | rewrite List.length_app, List.length_firstn, List.length_map; lia | exact Hpre ]. }
    assert (Ht' : Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs : apps_exp (a_record p) Ns) by (eapply wf_conv'; [ exact Ht | exact HT ]).
    assert (HUl : Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k (a_tuple T fs))] : Typeω@i0) by (gen_presups; assumption).
    assert (Hp : Θ ⍮ Ξ ⍮ Γ ⊢ a_proj f (a_tuple T fs) : U[sb_of_list Id (Ns ++ record_pre R k (a_tuple T fs))])
      by (eapply wf_proj; [ exact Ht' | exact Hrt | exact Hl | exact Hn | exact HNs | exact Hfk | exact HUl ]).
    assert (HM : Θ ⍮ Ξ ⍮ Γ ⊢ M : U[sb_of_list Id (Ns ++ record_pre R k (a_tuple T fs))])
      by (eapply wf_conv'; [ exact (HMs _ _ _ _ Hk Hfk) | symmetry; exact HUU ]).
    eapply wf_exp_eq_field_beta; [ exact Ht | | exact Hp | exact HM ].
    apply (field_lookup_nth _ k); [ rewrite Hfs; exact Hnd | exact Hk ].
  Qed.

  (** The parameters and the projections of a tuple before the field [k]
      are equal to its parameters and its fields before it, at the
      instances of the fields' telescope. *)
  Lemma tuple_pre_eq : forall Θ Ξ Γ T fs p R Ns i,
      Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs : T ->
      Θ ⍮ Ξ ⍮ Γ ⊢ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
      List.map fst fs = List.map fst (record_fields R) ->
      (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
         Θ ⍮ Ξ ⍮ Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
      forall k, k <= List.length (record_fields R) ->
      forall j N N' A, List.nth_error (Ns ++ record_pre R k (a_tuple T fs)) j = Some N ->
        List.nth_error (Ns ++ List.firstn k (List.map snd fs)) j = Some N' ->
        List.nth_error (tele_insts (record_fctx R k ++ record_params R) Id (Ns ++ record_pre R k (a_tuple T fs))) j = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A.
  Proof.
    intros * Ht HT Hrt Hl Hn HNs Hfs HMs.
    destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i1 Hty HF HS HFs _].
    rewrite Hl in Hl0; injection Hl0 as <-.
    assert (Hlf : List.length fs = List.length (record_fields R))
      by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
    set (t := a_tuple T fs).
    induction k as [| k IH]; intros Hk j N N' A HN HN' HA.
    - cbn [record_pre List.firstn List.map] in HN, HN', HA; rewrite List.app_nil_r in HN, HN', HA.
      cbn [record_fctx List.firstn List.map List.rev List.app] in HA.
      rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; exact (HNs _ _ _ HN HA).
    - destruct (List.nth_error (record_fields R) k) as [[f U] |] eqn:Hfk; [| apply List.nth_error_None in Hfk; lia ].
      destruct (nth_error_lt_some fs k ltac:(lia)) as [[g M] Hg].
      assert (g = f) as ->.
      { pose proof (List.map_nth_error fst _ _ Hg) as E1; pose proof (List.map_nth_error fst _ _ Hfk) as E2.
        rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
      pose proof (IH ltac:(lia)) as IHk.
      destruct (tuple_field_step _ _ _ _ _ _ _ _ _ Ht HT Hrt Hl Hn HNs Hfs HMs k f M U Hg Hfk IHk) as [_ Hpk].
      assert (Hs : List.firstn (S k) (List.map snd fs) = List.firstn k (List.map snd fs) ++ M :: nil)
        by (apply firstn_succ_nth; rewrite List.nth_error_map, Hg; reflexivity).
      rewrite (record_pre_succ _ _ _ _ t Hfk), List.app_assoc in HN, HA.
      rewrite Hs, List.app_assoc in HN'.
      rewrite (record_fctx_succ _ _ _ _ Hfk), <- List.app_comm_cons in HA.
      assert (HlL : List.length (Ns ++ record_pre R k t) = k + List.length (record_params R))
        by (rewrite List.length_app, length_record_pre by lia; lia).
      assert (HlL' : List.length (Ns ++ List.firstn k (List.map snd fs)) = k + List.length (record_params R))
        by (rewrite List.length_app, List.length_firstn, List.length_map; lia).
      rewrite tele_insts_cons_snoc in HA
        by (try (apply record_fctx_params_ass; exact Hass); rewrite HlL, List.length_app, length_record_fctx by lia; lia).
      assert (Hlen : List.length (tele_insts (record_fctx R k ++ record_params R) Id (Ns ++ record_pre R k t))
                     = k + List.length (record_params R)).
      { rewrite length_tele_insts by (apply record_fctx_params_ass; exact Hass).
        rewrite List.length_app, length_record_fctx, HlL by lia; lia. }
      destruct (Nat.lt_ge_cases j (k + List.length (record_params R))) as [Hj | Hj].
      + rewrite List.nth_error_app1 in HN, HA by lia; rewrite List.nth_error_app1 in HN' by lia.
        exact (IHk _ _ _ _ HN HN' HA).
      + rewrite List.nth_error_app2 in HN, HA by lia; rewrite List.nth_error_app2 in HN' by lia.
        rewrite HlL in HN; rewrite HlL' in HN'; rewrite Hlen in HA.
        replace (j - (k + List.length (record_params R))) with 0 in HN, HN', HA by
          (destruct (j - (k + List.length (record_params R))) eqn:E; [ reflexivity |];
           exfalso; cbn in HN; destruct n; discriminate).
        cbn in HN, HN', HA; injection HN as <-; injection HN' as <-; injection HA as <-.
        exact Hpk.
  Qed.

  (** So the projection of a tuple is its field, at the field's type at the
      tuple's projections, which is its type at the tuple's fields. *)
  Corollary tuple_proj_eq : forall Θ Ξ Γ T fs p R Ns i,
      Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs : T ->
      Θ ⍮ Ξ ⍮ Γ ⊢ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
      Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup Θ Ξ p = Some R ->
      List.length Ns = List.length (record_params R) ->
      (forall j N A, List.nth_error Ns j = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) j = Some A ->
         Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
      List.map fst fs = List.map fst (record_fields R) ->
      (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
         Θ ⍮ Ξ ⍮ Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
      forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k (a_tuple T fs))]
        ≈ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))] : (record_sort R)[sb_of_list Id Ns] /\
      Θ ⍮ Ξ ⍮ Γ ⊢ a_proj f (a_tuple T fs) ≈ M : U[sb_of_list Id (Ns ++ record_pre R k (a_tuple T fs))].
  Proof.
    intros * Ht HT Hrt Hl Hn HNs Hfs HMs k f M U Hk Hfk.
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
    eapply tuple_field_step; try eassumption.
    eapply tuple_pre_eq; try eassumption; lia.
  Qed.
