From Stdlib Require Import Arith List ListDec String PeanoNat Lia.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing Strengthening.
From Mctt.Core Require Import Base.
From Mctt.Core Require Import Consequences.Consistency Semantic.Realizability.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Extraction Require Import Lookup NbE PseudoMonadic TypeCheckBase IndCheck.
Import Domain_Notations Wk_Notations Fixed_Notations.

(** * Checking the Forms of Record Types

    The cases of [alg_type_infer_record], [alg_type_infer_tuple] and [alg_type_infer_proj], shared by both
    checkers ([Extraction.TypeCheck] and [Reference.TypeCheck]).  The type
    former recurses on nothing; a tuple recurses on its annotation and its
    fields, and a projection on its element, and they take those recursive
    calls as arguments, so that the mutual fixpoints of the checkers only
    pass them on. *)

Section Fixed_GCtx.
Variable F : FCtx.
#[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.

(** Whether a normal form is a record type at parameters. *)
#[derive(equations=no,eliminator=no)]
Equations get_record_nf (A : nf) : { p & { Rs | A = nf_record p Rs } } + { forall p Rs, A <> nf_record p Rs } :=
| nf_record p Rs => pureo (existT _ p (exist _ Rs _))
| _ => inright _
.

Extraction Inline get_record_nf.

(** What an inference returns: the type, which infers a universe and is a
    type. *)
Definition infer_post (G : ctx) (M : exp) (A : nf) : Prop :=
  G ⊢a M ⟹ A /\ (exists UA u, G ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ A : Typeω@i).

(** ** The Type Former *)

Lemma record_ty_order : forall G p R, ⊢ G -> record_lookup gc_deps gc_stack p = Some R ->
    nbe_ty_order gc_deps gc_stack G (record_ty R).
Proof.
  intros * HG Hl; destruct (record_former_typed _ _ _ HG Hl) as [j [_ Hj]].
  exact (nbe_order_of_typ _ _ _ Hj).
Qed.

Lemma record_ty_post : forall G p R W, ⊢ G -> record_lookup gc_deps gc_stack p = Some R ->
    nbe_ty_f G (record_ty R) W -> infer_post G (a_record p) W.
Proof.
  intros * HG Hl HW; destruct (record_former_typed _ _ _ HG Hl) as [j [_ Hj]].
  split; [ econstructor; eassumption | eapply level_of_nbe; eassumption ].
Qed.

(** A record's type former. *)
Definition record_infer G (HG : ⊢ G) (P : tenv G) p :
  { A : nf | infer_post G (a_record p) A } + { forall A, ~ G ⊢a a_record p ⟹ A }.
Proof.
  destruct (record_lookup_f F p) as [[R |] Hl]; [| right; intros A H; inversion H; congruence ].
  refine (let (W, HW) := nbe_ty_env_impl F G P (record_ty R) (record_ty_order G p R HG Hl) in
          inleft (exist _ W (record_ty_post G p R W HG Hl HW))).
Defined.

(** ** Projections *)

Lemma proj_typed : forall G M p Rs R f k U, ⊢ G -> G ⊢a M ⟹ nf_record p Rs ->
    record_lookup gc_deps gc_stack p = Some R -> List.nth_error (record_fields R) k = Some (f, U) ->
    exists m, G ⊢ U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)] : Typeω@m.
Proof.
  intros * HG HM Hl Hfk.
  destruct (alg_proj_typed _ _ _ _ _ _ _ _ HG (alg_type_infer_sound HM HG) Hl Hfk) as (m & Hm & _); eauto.
Qed.

Lemma proj_order : forall G M p Rs R f k U, ⊢ G -> G ⊢a M ⟹ nf_record p Rs ->
    record_lookup gc_deps gc_stack p = Some R -> List.nth_error (record_fields R) k = Some (f, U) ->
    nbe_ty_order gc_deps gc_stack G U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)].
Proof. intros * HG HM Hl Hfk; destruct (proj_typed _ _ _ _ _ _ _ _ HG HM Hl Hfk) as [m Hm]; exact (nbe_order_of_typ _ _ _ Hm). Qed.

Lemma proj_post : forall G M p Rs R f k U W, ⊢ G -> G ⊢a M ⟹ nf_record p Rs ->
    record_lookup gc_deps gc_stack p = Some R -> field_index (record_fields R) f = Some k ->
    List.nth_error (record_fields R) k = Some (f, U) ->
    nbe_ty_f G U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)] W -> infer_post G (a_proj f M) W.
Proof.
  intros * HG HM Hl Hfi Hfk HW; destruct (proj_typed _ _ _ _ _ _ _ _ HG HM Hl Hfk) as [m Hm].
  split; [ econstructor; eassumption | eapply level_of_nbe; eassumption ].
Qed.

(** A projection, from the inference of its element. *)
Definition proj_infer G (HG : ⊢ G) (P : tenv G) f M
  (IM : { A : nf | infer_post G M A } + { forall A, ~ G ⊢a M ⟹ A }) :
  { A : nf | infer_post G (a_proj f M) A } + { forall A, ~ G ⊢a a_proj f M ⟹ A }.
Proof.
  pose proof (ctx_wf_gctx _ _ _ HG) as Hg.
  destruct IM as [[A [HM _]] | HN]; [| right; intros A H; inversion H; subst; eapply HN; eassumption ].
  destruct (get_record_nf A) as [(p & Rs & ->) | Hne];
    [| right; intros W H; inversion H; subst;
       match goal with H' : G ⊢a M ⟹ _ |- _ => pose proof (functional_alg_type_infer Hg HM H') as E end;
       exact (Hne _ _ E) ].
  destruct (record_lookup_f F p) as [[R |] Hl];
    [| right; intros W H; inversion H; subst;
       match goal with H' : G ⊢a M ⟹ _ |- _ => pose proof (functional_alg_type_infer Hg HM H') as E end;
       injection E as <- <-; congruence ].
  destruct (field_index (record_fields R) f) as [k |] eqn:Hfi;
    [| right; intros W H; inversion H; subst;
       match goal with H' : G ⊢a M ⟹ _ |- _ => pose proof (functional_alg_type_infer Hg HM H') as E end;
       injection E as <- <-; unify_lookups; congruence ].
  destruct (List.nth_error (record_fields R) k) as [[g U] |] eqn:Hfk;
    [| right; intros W H; inversion H; subst;
       match goal with H' : G ⊢a M ⟹ _ |- _ => pose proof (functional_alg_type_infer Hg HM H') as E end;
       injection E as <- <-; unify_lookups; congruence ].
  destruct (string_dec g f) as [-> | Hgf];
    [| right; intros W H; inversion H; subst;
       match goal with H' : G ⊢a M ⟹ _ |- _ => pose proof (functional_alg_type_infer Hg HM H') as E end;
       injection E as <- <-; unify_lookups; congruence ].
  refine (let (W, HW) := nbe_ty_env_impl F G P U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)]
                           (proj_order G M p Rs R f k U HG HM Hl Hfk) in
          inleft (exist _ W (proj_post G M p Rs R f k U W HG HM Hl Hfi Hfk HW))).
Defined.

(** ** Tuples *)

(** What [alg_type_infer_tuple] asks of the field [k] of a tuple, at the parameters
    [Rs]. *)
Definition field_checks (G : ctx) (R : record_decl) (Rs : list nf) (fs : list (string * exp)) (k : nat) : Prop :=
  forall f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
    G ⊢a M ⟸ U[sb_of_list Id (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs))].

(** The parameters of a record type a type normalises to, typed. *)
Lemma record_nf_params : forall G T p Rs R i, G ⊢ T : Typeω@i -> nbe_ty_f G T (nf_record p Rs) ->
    record_lookup gc_deps gc_stack p = Some R ->
    List.length (List.map nf_to_exp Rs) = List.length (record_params R) /\
    (forall j N A, List.nth_error (List.map nf_to_exp Rs) j = Some N ->
       List.nth_error (tele_insts (record_params R) Id (List.map nf_to_exp Rs)) j = Some A -> G ⊢ N : A).
Proof.
  intros * HT Hn Hl.
  assert (HTR : G ⊢ T ≈ nf_record p Rs : Typeω@i) by (eapply soundness_ty'; eassumption).
  cbn [nf_to_exp] in HTR.
  assert (HRa : G ⊢ apps (a_record p) (List.map nf_to_exp Rs) : Typeω@i) by (gen_presups; assumption).
  pose proof (wf_record_apps_len _ _ _ _ _ Hl HRa) as HRl.
  split; [ exact HRl | exact (wf_record_apps_inv _ _ _ _ _ Hl HRa HRl) ].
Qed.

(** The type of the field [k], when the fields before it check: a type. *)
Lemma tuple_field_typed : forall G T (fs : list (string * exp)) p Rs R i, ⊢ G ->
    G ⊢ T : Typeω@i -> nbe_ty_f G T (nf_record p Rs) -> record_lookup gc_deps gc_stack p = Some R ->
    List.map fst fs = List.map fst (record_fields R) ->
    forall k, (forall j, j < k -> field_checks G R Rs fs j) ->
    forall f U, List.nth_error (record_fields R) k = Some (f, U) ->
      exists m, G ⊢ U[sb_of_list Id (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs))] : Typeω@m.
Proof.
  intros * HG HT Hn Hl Hfs.
  destruct (record_nf_params _ _ _ _ _ _ HT Hn Hl) as [HRl HRt].
  destruct (record_former_typed _ _ _ HG Hl) as [j0 [Hrt _]].
  destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HS HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  pose proof (wf_record_closed _ _ _ _ _ HG Hl) as Hc.
  assert (Hlf : List.length fs = List.length (record_fields R))
    by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
  intros k; induction k as [k IH] using lt_wf_ind; intros Hprev f U Hfk.
  assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
  pose proof (tuple_prefix_insts _ _ _ _ Hass HRl Hfs HRt k ltac:(lia)) as Hins.
  assert (Hins' : forall j N B, List.nth_error (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs)) j = Some N ->
             List.nth_error (tele_insts (record_fctx R k ++ record_params R) Id (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs))) j
               = Some B -> G ⊢ N : B).
  { apply Hins; intros j g M U' Hj HM HU'.
    destruct (IH j Hj ltac:(intros j' Hj'; apply Hprev; lia) g U' HU') as [m Hm].
    exact (alg_type_check_sound (Hprev j Hj g M U' HM HU') HG Hm). }
  assert (Hl1 : List.length (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs)) = k + List.length (record_params R))
    by (rewrite ?List.length_app, ?List.length_firstn, ?List.length_map in *; lia).
  destruct (record_field_typ_cong _ _ _ R k f U _ _ Hc Hass HF HG Hfk Hl1 Hl1
              ltac:(intros j1 N N' B HN HN' HB; rewrite HN in HN'; injection HN' as <-; apply wf_exp_eq_refl; exact (Hins' _ _ _ HN HB)))
    as [m HUU].
  exists m; gen_presups; assumption.
Qed.

Lemma tuple_post : forall G T (fs : list (string * exp)) UT u p Rs R, ⊢ G ->
    G ⊢a T ⟹ UT -> is_univ_nf UT u -> nbe_ty_f G T (nf_record p Rs) -> record_lookup gc_deps gc_stack p = Some R ->
    List.map fst fs = List.map fst (record_fields R) -> (forall j, field_checks G R Rs fs j) ->
    infer_post G (a_tuple T fs) (nf_record p Rs).
Proof.
  intros * HG HTi Hu Hn Hl Hfs HQ.
  assert (HTs : G ⊢ T : UT) by exact (alg_type_infer_sound HTi HG).
  rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HTs.
  pose proof (wf_exp_unf_large HTs) as HTl.
  split; [ eapply alg_type_infer_tuple; [ exact HTi | exact Hu | exact Hn | exact Hl | exact Hfs | intros k; exact (HQ k) ]
         | eapply level_of_nbe; eassumption ].
Qed.

(** A tuple, from the inference of its annotation and a check of each field
    at any type. *)
Definition tuple_infer G (HG : ⊢ G) (P : tenv G) T (fs : list (string * exp))
  (IT : { A : nf | infer_post G T A } + { forall A, ~ G ⊢a T ⟹ A })
  (CF : forall fm, List.In fm fs -> forall A, (exists i, G ⊢ A : Typeω@i) -> { G ⊢a snd fm ⟸ A } + { ~ G ⊢a snd fm ⟸ A }) :
  { A : nf | infer_post G (a_tuple T fs) A } + { forall A, ~ G ⊢a a_tuple T fs ⟹ A }.
Proof.
  pose proof (ctx_wf_gctx _ _ _ HG) as Hg.
  destruct IT as [[UT [HTi _]] | HN]; [| right; intros A H; inversion H; subst; eapply HN; eassumption ].
  destruct (univ_nf_idx_dec UT) as [[u Hu] | Hnu];
    [| right; intros A H; inversion H; subst;
       match goal with H' : G ⊢a T ⟹ _ |- _ => pose proof (functional_alg_type_infer Hg HTi H') as <- end;
       eapply Hnu; eassumption ].
  assert (HTs : G ⊢ T : UT) by exact (alg_type_infer_sound HTi HG).
  rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HTs.
  pose proof (wf_exp_unf_large HTs) as HTl.
  destruct (nbe_ty_env_impl F G P T (nbe_order_of_typ _ _ _ HTl)) as [W HW].
  destruct (get_record_nf W) as [(p & Rs & ->) | Hne];
    [| right; intros A H; inversion H; subst;
       match goal with Hn' : nbe_ty _ _ G T _ |- _ => exact (Hne _ _ (functional_nbe_ty _ _ _ _ HW Hn')) end ].
  destruct (record_lookup_f F p) as [[R |] Hl];
    [| right; intros A H; inversion H; subst;
       match goal with Hn' : nbe_ty _ _ G T _ |- _ => pose proof (functional_nbe_ty _ _ _ _ HW Hn') as E end;
       injection E as <- <-; congruence ].
  destruct (list_eq_dec string_dec (List.map fst fs) (List.map fst (record_fields R))) as [Hfs | Hfs];
    [| right; intros A H; inversion H; subst;
       match goal with Hn' : nbe_ty _ _ G T _ |- _ => pose proof (functional_nbe_ty _ _ _ _ HW Hn') as E end;
       injection E as <- <-; unify_lookups; contradiction ].
  (** The fields, one after the other: each at a type, once the fields
      before it check. *)
  assert (Hstep : forall j, j < List.length fs -> (forall j', j' < j -> field_checks G R Rs fs j') ->
             { field_checks G R Rs fs j } + { ~ field_checks G R Rs fs j }).
  { intros j Hj Hprev.
    destruct (List.nth_error fs j) as [[f M] |] eqn:Hk; [| left; intros ? ? ? H1; congruence ].
    destruct (List.nth_error (record_fields R) j) as [[g U] |] eqn:Hfk; [| left; intros ? ? ? _ H2; congruence ].
    destruct (string_dec f g) as [<- | Hfg]; [| left; intros ? ? ? H1 H2; rewrite Hk in H1; rewrite Hfk in H2; congruence ].
    destruct (CF (f, M) (List.nth_error_In _ _ Hk) _
                (tuple_field_typed _ _ _ _ _ _ _ HG HTl HW Hl Hfs j Hprev f U Hfk)) as [Hc | Hc].
    - left; intros f' M' U' H1 H2; rewrite Hk in H1; rewrite Hfk in H2; injection H1 as <- <-; injection H2 as <-; exact Hc.
    - right; intros H; exact (Hc (H f M U Hk Hfk)). }
  destruct (forall_lt_dec (field_checks G R Rs fs) (List.length fs) Hstep) as [HQ | HQ].
  - left; exists (nf_record p Rs).
    apply (tuple_post G T fs UT u p Rs R HG HTi Hu HW Hl Hfs).
    intros j; destruct (Nat.lt_ge_cases j (List.length fs)) as [Hj | Hj]; [ exact (HQ j Hj) |].
    intros f M U H1; apply List.nth_error_None in Hj; congruence.
  - right; intros A H; inversion H; subst.
    match goal with Hn' : nbe_ty _ _ G T _ |- _ => pose proof (functional_nbe_ty _ _ _ _ HW Hn') as E end.
    injection E as <- <-; unify_lookups.
    apply HQ; intros j Hj; intros f M U Hfj Hrj; eauto.
Defined.

End Fixed_GCtx.
