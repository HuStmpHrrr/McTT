(** * The Set Rules of Record Types

    A record type former is its global value, of its closed type; a tuple
    is the graph of its fields on their names, and a projection its value
    at the field's name. *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Weakening Substitution JudgmentSubstitution.
From Mctt.Core.SetModel.Interpretation.Global Require Import Model.
From Mctt.Core.SetModel.Cases Require Import UniverseCases ValidUnit MemberTypes Sel IndCases.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members Records.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths DescTyping MemberLemmas.
From Mctt.Core.Syntactic.System.Records Require Import Typing.
From Mctt.Core.Syntactic.System.Records Require Syntax.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing.
Import ListNotations.

Section Records.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).
  (** The global context is well formed *)
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  (** The valuation models the global context *)
  Hypothesis Hok : set_gctx_ok T γ.

(** ** Tuples *)

(** A tuple is a relation. *)
Lemma tuple_code_relation : forall fs, is_relation (tuple_code fs).
Proof.
  intros fs z Hz. apply set_mem_tuple_code in Hz. apply Exists_exists in Hz as [[f v] [_ E]].
  exists (string_code f), v. exact E.
Qed.

(** Of distinct names, a function. *)
Lemma tuple_code_functional : forall fs, NoDup (List.map fst fs) -> is_functional (tuple_code fs).
Proof.
  intros fs Hnd x y y' Hy Hy'. apply set_mem_tuple_code in Hy, Hy'.
  apply Exists_exists in Hy as [[f v] [Hin E]]. apply Exists_exists in Hy' as [[f' v'] [Hin' E']].
  cbn [fst snd] in E, E'. apply ordered_pair_inj in E as [Ex Ey]. apply ordered_pair_inj in E' as [Ex' Ey'].
  assert (Ef : f = f') by (apply string_code_inj; eapply set_eq_trans; [apply set_eq_sym; exact Ex | exact Ex']).
  subst f'.
  assert (Ev : v = v').
  { clear - Hnd Hin Hin'. induction fs as [| [g w] fs IH]; [destruct Hin |].
    cbn [List.map fst] in Hnd. inversion Hnd as [| ? ? Hg Hnd']; subst.
    destruct Hin as [Hin | Hin]; destruct Hin' as [Hin' | Hin'].
    - injection Hin as <- <-. injection Hin' as <-. reflexivity.
    - injection Hin as <- <-. exfalso. apply Hg. apply (in_map fst) in Hin'. exact Hin'.
    - injection Hin' as <- <-. exfalso. apply Hg. apply (in_map fst) in Hin. exact Hin.
    - exact (IH Hnd' Hin Hin'). }
  subst v'. eapply set_eq_trans; [exact Ey | apply set_eq_sym; exact Ey'].
Qed.

(** The field of a tuple of distinct names at a name is the value there. *)
Lemma tuple_field_at : forall fs f v, NoDup (List.map fst fs) -> In (f, v) fs -> set_eq (tuple_field (tuple_code fs) f) v.
Proof.
  intros * Hnd Hin. apply set_apply_char; [apply tuple_code_relation | apply tuple_code_functional; exact Hnd |].
  apply set_mem_tuple_code. apply Exists_exists. exists (f, v). split; [exact Hin | apply set_eq_refl].
Qed.

(** ** Equal Terms from Their Typings *)

(** Two terms of a type, of equal values, are equal. *)
Lemma set_exp_eq_of_sides : forall Γ A L R FA FL FL' GA GR GR', set_exp_eq_with T γ Γ A L L FA FL FL' ->
    set_exp_eq_with T γ Γ A R R GA GR GR' -> (forall ρ, set_env_in T γ Γ ρ -> set_eq (FL ρ) (GR ρ)) -> set_exp_eq T γ Γ A L R.
Proof.
  intros * [HA HL _ _ HLm] [_ HR _ _ _] E. exists FA, FL, GR. constructor; assumption.
Qed.

(** ** The Rules *)

Lemma set_rule_record : forall Γ p R i, ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_ctx T γ Γ -> record_lookup gc_deps gc_stack p = Some R ->
    gc_deps ⍮ gc_stack ⍮ nil ⊢ record_ty R : a_typ i -> set_exp_eq T γ nil (a_typ i) (record_ty R) (record_ty R) ->
    set_exp_eq T γ Γ (record_ty R) (a_record p) (a_record p).
Proof.
  intros * Hc HΓ HR Hw (FS & FA & FA' & [_ HFA _ _ _]). pose proof (set_gctx_ok_records _ _ Hok _ _ HR) as HSR.
  apply (set_exp_eq_closed_global T γ Hfn Hmods Hgw _ _ (global_record_former γ p) FA); try assumption.
  - exact (proj1 (proj2 (proj1 (proj2 wf_scoped) _ _ _ _ _ Hw))).
  - exact (set_record_ok_former_typed _ _ _ _ _ HSR _ HFA).
  - intros ρ. constructor.
Qed.

Lemma set_rule_record_cong : forall Γ p R i, ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_ctx T γ Γ -> record_lookup gc_deps gc_stack p = Some R ->
    gc_deps ⍮ gc_stack ⍮ nil ⊢ record_ty R : a_typ i -> set_exp_eq T γ nil (a_typ i) (record_ty R) (record_ty R) ->
    set_exp_eq T γ Γ (record_ty R) (a_record p) (a_record p).
Proof. exact set_rule_record. Qed.

Lemma set_rule_proj_cong : forall Γ C f M M' A FC FM FM' FA FP FP' GA GP GP', set_exp_eq_with T γ Γ C M M' FC FM FM' ->
    set_exp_eq_with T γ Γ A (a_proj f M) (a_proj f M) FA FP FP' -> set_exp_eq_with T γ Γ A (a_proj f M') (a_proj f M') GA GP GP' ->
    set_exp_eq T γ Γ A (a_proj f M) (a_proj f M').
Proof.
  intros * [_ HM HM' EM _] HL HR. apply (set_exp_eq_of_sides _ _ _ _ _ _ _ _ _ _ HL HR).
  pose proof HL as [_ HP _ _ _]. pose proof HR as [_ HP' _ _ _]. intros ρ Hρ.
  eapply set_eq_trans; [apply set_eq_sym; exact (set_denotes_unique _ _ _ _ _ HP _ _ _ Hρ
                                                    (set_interp_proj T γ _ _ _ _ _ (set_denotes_exists _ _ _ _ _ HM _ Hρ))) |].
  eapply set_eq_trans; [apply tuple_field_resp; exact (EM _ Hρ) |].
  exact (set_denotes_unique _ _ _ _ _ HP' _ _ _ Hρ (set_interp_proj T γ _ _ _ _ _ (set_denotes_exists _ _ _ _ _ HM' _ Hρ))).
Qed.

(** The fields' values keep the fields' names. *)
Lemma set_interp_fields_names : forall Γ ρ fs vs, set_interp_fields T γ Γ ρ fs vs -> List.map fst vs = List.map fst fs.
Proof. induction 1; cbn; [reflexivity | f_equal; assumption]. Qed.

(** A field's value, by position. *)
Lemma set_interp_fields_nth : forall Γ ρ fs vs, set_interp_fields T γ Γ ρ fs vs ->
    forall k f M, List.nth_error fs k = Some (f, M) -> exists v, List.nth_error vs k = Some (f, v) /\ set_interp T γ Γ ρ M v.
Proof.
  induction 1 as [| Γ ρ g N fs v vs HN Hfs IH]; intros [| k] f M Hk; cbn in Hk; try discriminate.
  - injection Hk as <- <-. exists v. split; [reflexivity | exact HN].
  - exact (IH _ _ _ Hk).
Qed.

(** By name. *)
Lemma set_interp_fields_lookup : forall Γ ρ fs vs, set_interp_fields T γ Γ ρ fs vs ->
    forall f M, field_lookup fs f = Some M -> exists v, In (f, v) vs /\ set_interp T γ Γ ρ M v.
Proof.
  induction 1 as [| Γ ρ g N fs v vs HN Hfs IH]; intros f M Hl; cbn in Hl; [discriminate |].
  destruct (String.eqb_spec f g) as [-> | _].
  - injection Hl as <-. exists v. split; [left; reflexivity | exact HN].
  - destruct (IH _ _ Hl) as (w & Hw & HM). exists w. split; [right; exact Hw | exact HM].
Qed.

(** Fields of equal values, position by position, have equal values. *)
Lemma set_interp_fields_eq : forall Γ ρ fs vs fs' vs', set_interp_fields T γ Γ ρ fs vs -> set_interp_fields T γ Γ ρ fs' vs' ->
    List.map fst fs' = List.map fst fs ->
    (forall k f M M' v v', List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
       set_interp T γ Γ ρ M v -> set_interp T γ Γ ρ M' v' -> set_eq v v') ->
    fields_set_eq vs vs'.
Proof.
  intros * H. revert fs' vs'. induction H as [| Γ ρ g N fs v vs HN Hfs IH]; intros fs' vs' H' Hn E.
  - destruct fs' as [| ? ?]; [| discriminate]. inversion H'; subst. constructor.
  - destruct fs' as [| [g' N'] fs']; [discriminate |]. cbn in Hn. injection Hn as -> Hn.
    inversion H' as [| ? ? ? ? ? w ws HN' Hfs']; subst. constructor.
    + split; [reflexivity | exact (E 0 g N N' v w eq_refl eq_refl HN HN')].
    + apply (IH _ _ Hfs' Hn). intros k. exact (E (S k)).
Qed.

Lemma set_rule_tuple_cong : forall Γ A fs A' fs' FA FL FL' GA GR GR', set_exp_eq_with T γ Γ A (a_tuple A fs) (a_tuple A fs) FA FL FL' ->
    set_exp_eq_with T γ Γ A (a_tuple A' fs') (a_tuple A' fs') GA GR GR' -> List.map fst fs' = List.map fst fs ->
    forall (R : record_decl), List.map fst fs = List.map fst (record_fields R) ->
    (forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
       List.nth_error (record_fields R) k = Some (f, U) -> exists B, set_exp_eq T γ Γ B M M') ->
    set_exp_eq T γ Γ A (a_tuple A fs) (a_tuple A' fs').
Proof.
  intros * HL HR Hn R HnR Hf0.
  assert (Hf : forall k f M M', List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') -> exists B, set_exp_eq T γ Γ B M M').
  { intros k f M M' Hk Hk'. pose proof (f_equal (fun l => List.nth_error l k) HnR) as E. cbn beta in E.
    rewrite !List.nth_error_map, Hk in E.
    destruct (List.nth_error (record_fields R) k) as [[g U] |] eqn:HU; cbn in E; [| discriminate]. injection E as <-.
    exact (Hf0 _ _ _ _ _ Hk Hk' HU). }
  apply (set_exp_eq_of_sides _ _ _ _ _ _ _ _ _ _ HL HR).
  pose proof HL as [_ HP _ _ _]. pose proof HR as [_ HP' _ _ _]. intros ρ Hρ.
  pose proof (set_denotes_exists _ _ _ _ _ HP _ Hρ) as H1. pose proof (set_denotes_exists _ _ _ _ _ HP' _ Hρ) as H2.
  inversion H1; subst. inversion H2; subst.
  apply tuple_code_resp.
  match goal with Hvs : set_interp_fields _ _ _ _ fs ?vs, Hvs' : set_interp_fields _ _ _ _ fs' ?vs' |- _ =>
    apply (set_interp_fields_eq _ _ _ _ _ _ Hvs Hvs' Hn) end.
  intros * Hk Hk' Hv Hv'. destruct (Hf _ _ _ _ Hk Hk') as (B & FB & FM & FM' & [_ HM HM' EM _]).
  eapply set_eq_trans; [exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Hρ Hv) |].
  eapply set_eq_trans; [exact (EM _ Hρ) |]. apply set_eq_sym. exact (set_denotes_unique _ _ _ _ _ HM' _ _ _ Hρ Hv').
Qed.

Lemma set_rule_field_beta : forall Γ A fs f M B FA FL FL' FB FP FP' GB GM GM', NoDup (List.map fst fs) ->
    set_exp_eq_with T γ Γ A (a_tuple A fs) (a_tuple A fs) FA FL FL' -> field_lookup fs f = Some M ->
    set_exp_eq_with T γ Γ B (a_proj f (a_tuple A fs)) (a_proj f (a_tuple A fs)) FB FP FP' ->
    set_exp_eq_with T γ Γ B M M GB GM GM' -> set_exp_eq T γ Γ B (a_proj f (a_tuple A fs)) M.
Proof.
  intros * Hnd [_ HL _ _ _] Hl HP HM. apply (set_exp_eq_of_sides _ _ _ _ _ _ _ _ _ _ HP HM).
  pose proof HP as [_ HPd _ _ _]. pose proof HM as [_ HMd _ _ _]. intros ρ Hρ.
  pose proof (set_denotes_exists _ _ _ _ _ HL _ Hρ) as H1.
  inversion H1; subst.
  match goal with Hvs : set_interp_fields _ _ _ _ fs ?vs |- _ =>
    destruct (set_interp_fields_lookup _ _ _ _ Hvs _ _ Hl) as (v & Hin & Hv);
    pose proof (set_interp_fields_names _ _ _ _ Hvs) as Hnames end.
  eapply set_eq_trans; [apply set_eq_sym; exact (set_denotes_unique _ _ _ _ _ HPd _ _ _ Hρ (set_interp_proj T γ _ _ _ _ _ H1)) |].
  match goal with E : tuple_code _ = FL ρ |- _ => rewrite <- E end.
  eapply set_eq_trans; [apply tuple_field_at; [rewrite Hnames; exact Hnd | exact Hin] |].
  exact (set_denotes_unique _ _ _ _ _ HMd _ _ _ Hρ Hv).
Qed.

(** ** Telescopes of Fields *)

(** The instances of the first [j] fields' telescope: each field's type
    at the values before it. *)
Lemma tele_insts_record_fctx : forall R j σ L i A, j <= List.length (record_fields R) -> List.length L = j ->
    List.nth_error (tele_insts (record_fctx R j) σ L) i = Some A ->
    exists f U, List.nth_error (record_fields R) i = Some (f, U) /\ i < j /\ A = exp_sub U (sb_of_list σ (List.firstn i L)).
Proof.
  intros R j. induction j as [| j IH]; intros σ L i A Hj HL Hi.
  - destruct L; [| discriminate]. cbn in Hi. destruct i; discriminate.
  - destruct (List.nth_error (record_fields R) j) as [[f U] |] eqn:Hfj; [| apply List.nth_error_None in Hfj; lia].
    destruct (List.exists_last (l := L) ltac:(intros ->; discriminate)) as (L' & x & ->).
    rewrite List.length_app in HL; cbn in HL.
    rewrite (record_fctx_succ _ _ _ _ Hfj), tele_insts_cons_snoc in Hi
      by (try apply record_fctx_ass; rewrite length_record_fctx by lia; lia).
    assert (HlT : List.length (tele_insts (record_fctx R j) σ L') = j)
      by (rewrite length_tele_insts by apply record_fctx_ass; rewrite length_record_fctx by lia; lia).
    destruct (Nat.lt_ge_cases i j) as [Hlt | Hge].
    + rewrite List.nth_error_app1 in Hi by lia. destruct (IH σ L' i A ltac:(lia) ltac:(lia) Hi) as (f' & U' & Hf' & Hl & ->).
      exists f', U'. split; [exact Hf' |]. split; [lia |]. rewrite List.firstn_app, (proj2 (Nat.sub_0_le i (List.length L'))) by lia.
      rewrite List.app_nil_r. reflexivity.
    + rewrite List.nth_error_app2 in Hi by lia. destruct (i - List.length (tele_insts (record_fctx R j) σ L')) as [| m] eqn:Hm;
        [| destruct m; discriminate].
      cbn in Hi. injection Hi as <-. assert (i = j) by lia. subst i.
      exists f, U. split; [exact Hfj |]. split; [lia |]. rewrite List.firstn_app, List.firstn_all2 by lia.
      replace (j - List.length L') with 0 by lia. rewrite List.app_nil_r. reflexivity.
Qed.

(** A telescope reading types denotes. *)
Lemma set_ctx_of_tele_types : forall Γ0 Δ Fs, set_tele_types T γ Γ0 Δ Fs -> set_ctx T γ Γ0 -> set_ctx T γ (Δ ++ Γ0).
Proof.
  induction 1 as [| κ A Δ Fs F HΔ IH HA]; intros HΓ0; [exact HΓ0 |]. cbn [List.app set_ctx set_entry_valid].
  split; [exact (IH HΓ0) |]. exists (fun ρ => F (set_env_values (Δ ++ Γ0) ρ)).
  apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ (IH HΓ0)). intros ρ Hρ. exact (HA ρ Hρ).
Qed.

(** The values of an environment of two telescopes, the outer first. *)
Lemma set_env_values_app : forall Δ1 Δ2 ρ,
    set_env_values (Δ1 ++ Δ2) ρ = set_env_values Δ2 (set_env_drop (List.length Δ1) ρ) ++ set_env_values Δ1 ρ.
Proof.
  induction Δ1 as [| e Δ1 IH]; intros Δ2 ρ; cbn [List.app List.length set_env_values].
  - rewrite List.app_nil_r. reflexivity.
  - rewrite IH, <- List.app_assoc. reflexivity.
Qed.

(** One more field fits, after the others. *)
Lemma set_fields_fit_snoc : forall Fs pre vs F v, set_fields_fit Fs pre vs -> set_mem v (code_carrier (F (pre ++ vs))) ->
    set_fields_fit (Fs ++ [F]) pre (vs ++ [v]).
Proof.
  induction 1 as [pre | G Gs pre w ws Hw Hws IH]; intros Hv; cbn [List.app].
  - constructor; [rewrite List.app_nil_r in Hv; exact Hv | constructor].
  - constructor; [exact Hw |]. apply IH. rewrite <- List.app_assoc. exact Hv.
Qed.

(** An environment of a telescope over another has its values fit the
    types it reads. *)
Lemma set_tele_types_fit : forall Γ0 Δ Fs, set_tele_types T γ Γ0 Δ Fs -> forall ρ, set_env_in T γ (Δ ++ Γ0) ρ ->
    set_fields_fit Fs (set_env_values Γ0 (set_env_drop (List.length Δ) ρ)) (set_env_values Δ ρ).
Proof.
  induction 1 as [| κ A Δ Fs F HΔ IH HA]; intros ρ Hρ; [constructor |].
  destruct Hρ as [Ht He]. cbn [set_env_values List.length]. apply set_fields_fit_snoc; [exact (IH _ Ht) |].
  cbn [set_entry_rel] in He. destruct He as (x & x' & a & [Hl _ Ha Hx _]). rewrite Hl. cbn [set_entry_value].
  pose proof (HA _ Ht) as HF. rewrite set_env_values_app in HF.
  eapply set_mem_eq_r; [apply code_carrier_resp;
                        exact (set_interp_functional T γ Hfn Hmods _ _ _ _ Ha _ _ (set_env_rel_eq T γ _ _ _ Ht) HF) |].
  exact Hx.
Qed.

(** The first fields of a record over its parameters denote, closed, and
    so does that telescope over any denoting context. *)
Lemma set_record_tele_ctx : forall Γ p R m, ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_ctx T γ Γ -> record_lookup gc_deps gc_stack p = Some R ->
    m <= List.length (record_fields R) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ record_fctx R (List.length (record_fields R)) ++ record_params R -> all_assumptions (record_params R) ->
    set_ctx T γ (record_fctx R m ++ record_params R) /\ ctx_scoped 0 (record_fctx R m ++ record_params R) /\
    ⊢ gc_deps ⍮ gc_stack ⍮ record_fctx R m ++ record_params R /\
    set_ctx T γ ((record_fctx R m ++ record_params R) ++ Γ) /\ ⊢ gc_deps ⍮ gc_stack ⍮ (record_fctx R m ++ record_params R) ++ Γ.
Proof.
  intros * Hc HΓ HR Hm HF Hass. pose proof (set_gctx_ok_records _ _ Hok _ _ HR) as HSR.
  pose proof (wf_record_closed _ _ _ _ _ Hc HR) as Hcl.
  pose proof (set_ctx_of_tele_types _ _ _ (set_record_ok_params _ _ _ _ _ HSR) I) as HP. rewrite List.app_nil_r in HP.
  pose proof (set_ctx_of_tele_types _ _ _ (set_record_ok_field_types _ _ _ _ _ HSR) HP) as HFn.
  destruct (record_fctx_split R m Hm) as (Ψ & HΨ). rewrite HΨ, <- List.app_assoc in HFn.
  assert (Hs : ctx_scoped 0 (record_fctx R m ++ record_params R))
    by (apply record_fctx_scoped; [exact Hm | intros; eapply closed_fields; eassumption | exact (closed_params _ Hcl)]).
  assert (Hcm : ⊢ gc_deps ⍮ gc_stack ⍮ record_fctx R m ++ record_params R)
    by (pose proof (record_fctx_app_wf _ _ _ m nil Hm Hcl Hass HF (wf_ctx_empty _ _ Hgw)) as H; rewrite List.app_nil_r in H; exact H).
  pose proof (set_ctx_app_r T γ _ _ HFn) as HCm.
  pose proof (record_fctx_app_wf _ _ _ m Γ Hm Hcl Hass HF Hc) as HcΓ.
  split; [exact HCm | split; [exact Hs | split; [exact Hcm | split; [| exact HcΓ]]]].
  pose proof (set_ctx_moved T γ Hfn Hmods (record_fctx R m ++ record_params R) nil Γ _ _ (set_gsub_drop T γ _ Hc) HΓ
                ltac:(rewrite List.app_nil_r; exact HCm) ltac:(rewrite List.app_nil_r; exact Hcm)) as H.
  rewrite tele_sub_closed in H by exact Hs. exact H.
Qed.

(** The parameters and the fields of a tuple are the arguments of the
    fields' telescope over the parameters, each at its instance. *)
Lemma record_args_typed : forall (P : exp -> typ -> Prop) R Ns fs, List.length Ns = List.length (record_params R) ->
    List.map fst fs = List.map fst (record_fields R) -> all_assumptions (record_params R) ->
    (forall k N B, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) sb_id Ns) k = Some B -> P N B) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       P M (exp_sub U (sb_of_list sb_id (Ns ++ List.firstn k (List.map snd fs))))) ->
    forall k N B, List.nth_error (Ns ++ List.map snd fs) k = Some N ->
      List.nth_error (tele_insts (record_fctx R (List.length (record_fields R)) ++ record_params R) sb_id (Ns ++ List.map snd fs)) k = Some B ->
      P N B.
Proof.
  intros * Hl Hn Hass HP HF k N B HN HB.
  assert (Hlf : List.length (List.map snd fs) = List.length (record_fields R))
    by (rewrite List.length_map, <- (List.length_map fst fs), Hn, List.length_map; reflexivity).
  rewrite tele_insts_app in HB by (exact Hass || exact Hl).
  assert (HlT : List.length (tele_insts (record_params R) sb_id Ns) = List.length Ns) by (rewrite length_tele_insts by exact Hass; lia).
  destruct (Nat.lt_ge_cases k (List.length Ns)) as [Hlt | Hge].
  - rewrite List.nth_error_app1 in HN by lia. rewrite List.nth_error_app1 in HB by lia. exact (HP _ _ _ HN HB).
  - rewrite List.nth_error_app2 in HN by lia. rewrite List.nth_error_app2 in HB by lia. rewrite HlT in HB.
    destruct (tele_insts_record_fctx _ _ _ _ _ _ (le_n _) Hlf HB) as (f & U & Hf & _ & ->).
    rewrite List.nth_error_map in HN. destruct (List.nth_error fs (k - List.length Ns)) as [[f' M] |] eqn:Hfs; [| discriminate].
    cbn in HN. injection HN as <-.
    assert (f' = f).
    { pose proof (f_equal (fun l => List.nth_error l (k - List.length Ns)) Hn) as E. cbn beta in E.
      rewrite !List.nth_error_map, Hfs, Hf in E. cbn in E. injection E as <-. reflexivity. }
    subst f'. rewrite <- sb_of_list_app. exact (HF _ _ _ _ Hfs Hf).
Qed.

(** Fields each of which denotes have their values as a function of the
    environment. *)
Lemma set_denotes_fields : forall Γ fs, (forall k f M, List.nth_error fs k = Some (f, M) -> exists F, set_denotes T γ Γ M F) ->
    exists Fs, forall ρ, set_env_in T γ Γ ρ -> set_interp_fields T γ Γ ρ fs (Fs ρ).
Proof.
  intros Γ fs. induction fs as [| [f M] fs IH]; intros HM; [exists (fun _ => nil); intros; constructor |].
  destruct (HM 0 f M eq_refl) as (FM & HFM). destruct (IH (fun k f' M' H => HM (S k) f' M' H)) as (Fs & HFs).
  exists (fun ρ => (f, FM ρ) :: Fs ρ). intros ρ Hρ. constructor; [exact (set_denotes_exists _ _ _ _ _ HFM _ Hρ) | exact (HFs _ Hρ)].
Qed.

(** The fields' values, as a list of terms' values. *)
Lemma set_interp_fields_list : forall Γ ρ fs vs, set_interp_fields T γ Γ ρ fs vs ->
    set_interp_list T γ Γ ρ (List.map snd fs) (List.map snd vs).
Proof. induction 1; cbn; constructor; assumption. Qed.

Lemma set_interp_list_app : forall Γ ρ Ms ms Ns ns, set_interp_list T γ Γ ρ Ms ms -> set_interp_list T γ Γ ρ Ns ns ->
    set_interp_list T γ Γ ρ (Ms ++ Ns) (ms ++ ns).
Proof. intros * H. induction H; intros HN; cbn; [exact HN | constructor; auto]. Qed.

Lemma length_set_env_values : forall Δ ρ, List.length (set_env_values Δ ρ) = List.length Δ.
Proof. induction Δ as [| e Δ IH]; intros ρ; cbn; [reflexivity | rewrite List.length_app, IH; cbn; lia]. Qed.

(** Equal lists split alike. *)
Lemma list_set_eq_app_inv : forall l1 l2 m1 m2, List.length l1 = List.length m1 -> list_set_eq (l1 ++ l2) (m1 ++ m2) ->
    list_set_eq l1 m1 /\ list_set_eq l2 m2.
Proof.
  induction l1 as [| x l1 IH]; intros l2 [| y m1] m2 Hl H; cbn in Hl; try discriminate; [split; [constructor | exact H] |].
  inversion H as [| ? ? ? ? Exy Hr]; subst. destruct (IH l2 m1 m2 ltac:(lia) Hr) as [H1 H2]. split; [constructor; assumption | exact H2].
Qed.

(** ** Environments of Telescopes Retargeted *)

Lemma set_env_extend_kinded_snoc : forall vs κs ρ κ x, List.length κs = List.length vs ->
    set_env_extend_kinded ρ (κs ++ [κ]) (vs ++ [x]) = set_env_extend (set_env_extend_kinded ρ κs vs) (set_entry_term κ x).
Proof.
  induction vs as [| v vs IH]; intros [| κ0 κs] ρ κ x Hl; cbn in Hl; try discriminate; [reflexivity |].
  cbn [List.app set_env_extend_kinded List.hd List.tl]. apply IH. lia.
Qed.

Lemma set_env_values_ext : forall Δ ρ ρ', (forall x, ρ x = ρ' x) -> set_env_values Δ ρ = set_env_values Δ ρ'.
Proof.
  induction Δ as [| e Δ IH]; intros ρ ρ' E; [reflexivity |]. cbn [set_env_values]. rewrite (IH (set_env_tail ρ) (set_env_tail ρ')), E;
    [reflexivity | intros x; apply E].
Qed.

Lemma ctx_kinds_cons : forall e Δ, ctx_kinds (e :: Δ) = ctx_kinds Δ ++ [centry_kind e].
Proof. intros. unfold ctx_kinds. cbn [List.map List.rev]. reflexivity. Qed.

Lemma length_ctx_kinds : forall Δ, List.length (ctx_kinds Δ) = List.length Δ.
Proof. intros. unfold ctx_kinds. rewrite List.length_rev, List.length_map. reflexivity. Qed.

(** An environment of a telescope over another, its values replaced by
    equal ones of the telescope's kinds, is related to it. *)
Lemma set_env_rel_retarget : forall Δ Γ0 ρ vs, all_assumptions Δ -> set_env_in T γ (Δ ++ Γ0) ρ ->
    list_set_eq (set_env_values Δ ρ) vs ->
    set_env_rel T γ (Δ ++ Γ0) ρ (set_env_extend_kinded (set_env_drop (List.length Δ) ρ) (ctx_kinds Δ) vs).
Proof.
  induction Δ as [| e Δ IH]; intros Γ0 ρ vs Hass Hρ E.
  - inversion E; subst. cbn [List.length set_env_extend_kinded List.app]. exact Hρ.
  - inversion Hass as [| ? ? (κ & A & ->) Hass']; subst. cbn [set_env_values] in E.
    destruct (List.Forall2_app_inv_l _ _ E) as (vs1 & vs2 & E1 & E2 & ->).
    inversion E2 as [| ? x' ? ? Ex Enil]; subst. inversion Enil; subst.
    assert (Hl : List.length (ctx_kinds Δ) = List.length vs1)
      by (rewrite length_ctx_kinds; rewrite <- (Forall2_length E1), length_set_env_values; reflexivity).
    rewrite ctx_kinds_cons, set_env_extend_kinded_snoc by exact Hl. cbn [centry_kind].
    destruct Hρ as [Ht He]. split.
    + exact (IH _ _ _ Hass' Ht E1).
    + cbn [set_entry_rel] in He |- *. destruct He as (x & x0 & a & [Hl0 _ Ha Hx _]).
      exists x, x', a. constructor; [exact Hl0 | reflexivity | exact Ha | exact Hx |].
      rewrite Hl0 in Ex. exact Ex.
Qed.

(** The values of such an environment are the given ones. *)
Lemma set_env_values_extend_kinded : forall Δ ρ vs, List.length vs = List.length Δ ->
    set_env_values Δ (set_env_extend_kinded ρ (ctx_kinds Δ) vs) = vs.
Proof.
  induction Δ as [| e Δ IH]; intros ρ vs Hl.
  - destruct vs; [reflexivity | discriminate].
  - destruct (List.exists_last (l := vs) ltac:(intros ->; discriminate)) as (vs1 & x & ->).
    rewrite List.length_app in Hl; cbn in Hl.
    rewrite ctx_kinds_cons, set_env_extend_kinded_snoc by (rewrite length_ctx_kinds; lia).
    cbn [set_env_values]. change (set_env_tail (set_env_extend ?r ?d)) with r. rewrite (IH ρ vs1 ltac:(lia)). reflexivity.
Qed.

Lemma set_rule_tuple : forall Γ A fs p R Ns i, ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_ctx T γ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup gc_deps gc_stack p = Some R ->
    List.length Ns = List.length (record_params R) ->
    (forall k N B, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) sb_id Ns) k = Some B ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ N : B) ->
    (forall k N B, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) sb_id Ns) k = Some B ->
       set_exp_eq T γ Γ B N N) ->
    List.map fst fs = List.map fst (record_fields R) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ M : exp_sub U (sb_of_list sb_id (Ns ++ List.firstn k (List.map snd fs)))) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       set_exp_eq T γ Γ (exp_sub U (sb_of_list sb_id (Ns ++ List.firstn k (List.map snd fs)))) M M) ->
    set_exp_eq T γ Γ (a_typ i) A (apps_exp (a_record p) Ns) ->
    set_exp_eq T γ Γ A (a_tuple A fs) (a_tuple A fs).
Proof.
  intros * Hc HΓ Hr HR Hl HNs HNr Hn HFs HFr (FS & FA & FAp & [_ HFA HFAp EA _]).
  destruct (wf_record_inversion Hr) as [R0 Hl0 Hnd Hass i0 _ HF _ _ _ _ _]. rewrite HR in Hl0. injection Hl0 as <-.
  pose proof (set_gctx_ok_records _ _ Hok _ _ HR) as HSR.
  set (n := List.length (record_fields R)).
  destruct (set_record_tele_ctx Γ p R n Hc HΓ HR (le_n _) HF Hass) as (HCT & HsT & HcT & HCTΓ & HcTΓ).
  assert (Hlf : List.length (List.map snd fs) = n)
    by (unfold n; rewrite List.length_map, <- (List.length_map fst fs), Hn, List.length_map; reflexivity).
  assert (Hlen : List.length (Ns ++ List.map snd fs) = List.length (record_fctx R n ++ record_params R))
    by (rewrite !List.length_app, length_record_fctx, Hl, Hlf by (unfold n; lia); lia).
  destruct (set_gsub_closed_inst T γ Hfn Hmods _ _ _ HΓ (record_fctx_params_ass _ _ Hass) HCTΓ HcTΓ Hlen
              (record_args_typed (fun N B => gc_deps ⍮ gc_stack ⍮ Γ ⊢ N : B) _ _ _ Hl Hn Hass HNs HFs)
              (record_args_typed (fun N B => set_exp_eq T γ Γ B N N) _ _ _ Hl Hn Hass HNr HFr)) as (Fι & Hι & Hvals).
  destruct (set_denotes_fields Γ fs) as (Fs & HFsd).
  { intros k f M Hk. assert (Hk' : exists U, List.nth_error (record_fields R) k = Some (f, U)).
    { pose proof (f_equal (fun l => List.nth_error l k) Hn) as E. cbn beta in E. rewrite !List.nth_error_map, Hk in E.
      destruct (List.nth_error (record_fields R) k) as [[f' U] |]; cbn in E; [injection E as ->; exists U; reflexivity | discriminate]. }
    destruct Hk' as (U & HU). destruct (HFr _ _ _ _ Hk HU) as (FU & FM & FM' & [_ HM _ _ _]). exists FM. exact HM. }
  assert (HT : set_denotes T γ Γ (a_tuple A fs) (fun ρ => tuple_code (Fs ρ)))
    by (apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ); intros ρ Hρ; constructor; exact (HFsd _ Hρ)).
  exists FA, (fun ρ => tuple_code (Fs ρ)), (fun ρ => tuple_code (Fs ρ)).
  constructor; [exact HFA | exact HT | exact HT | intros; apply set_eq_refl |]. intros ρ Hρ.
  (* the type: the record type at the parameters' values *)
  pose proof (set_denotes_exists _ _ _ _ _ HFAp _ Hρ) as Hap. destruct (set_interp_apps_inv T γ _ _ _ _ _ Hap) as (v0 & ns & Hv0 & Hns & Eap).
  inversion Hv0; subst.
  pose proof (set_interp_list_app _ _ _ _ _ _ Hns (set_interp_fields_list _ _ _ _ (HFsd _ Hρ))) as Hargs.
  pose proof (Hvals _ _ Hρ Hargs) as Ev.
  destruct (set_closed_inst_env T γ Hfn Hmods _ _ _ _ Hι HΓ HCT HsT HcT HcTΓ _ Hρ) as [Hin Evs].
  set (ρs := set_env_moved (List.length (record_fctx R n ++ record_params R)) (set_env_drop (List.length Γ)) (Fι ρ)) in *.
  rewrite <- Evs, set_env_values_app in Ev.
  rewrite length_record_fctx in Ev by (unfold n; lia).
  assert (Hlns : List.length ns = List.length Ns) by (clear - Hns; induction Hns; cbn; congruence).
  destruct (list_set_eq_app_inv ns _ (set_env_values (record_params R) (set_env_drop n ρs)) _
              ltac:(rewrite length_set_env_values, Hlns; exact Hl) Ev) as [Ens Ems].
  assert (Hρp : set_env_in T γ (record_params R) (set_env_drop n ρs)).
  { pose proof (set_env_rel_drop T γ (record_fctx R n) (record_params R) _ _ Hin) as H.
    rewrite length_record_fctx in H by (unfold n; lia). exact H. }
  pose proof (set_record_ok_former_value _ _ _ _ _ HSR _ Hρp) as Ef.
  eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact (EA _ Hρ) |]. rewrite Eap.
  eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; eapply set_eq_trans;
                        [apply apply_values_resp; [apply set_eq_refl | exact Ens] | exact Ef] |].
  eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
  apply (proj2 (set_record_ok_carrier _ _ _ _ _ HSR _ _ Hρp)).
  exists (set_env_values (record_fctx R n) ρs). constructor.
  - rewrite length_set_env_values, length_record_fctx by (unfold n; lia). rewrite (set_record_ok_names _ _ _ _ _ HSR), List.length_map.
    reflexivity.
  - rewrite (set_record_ok_names _ _ _ _ _ HSR), <- Hn.
    pose proof (set_interp_fields_names _ _ _ _ (HFsd _ Hρ)) as HnF.
    rewrite <- HnF. apply tuple_code_resp. clear - Ems. revert Ems. generalize (set_env_values (record_fctx R n) ρs).
    induction (Fs ρ) as [| [f v] l IH]; intros vs E; inversion E as [| ? w ? ws Ew Ews]; subst; constructor.
    + split; [reflexivity | exact Ew].
    + exact (IH _ Ews).
  - pose proof (set_tele_types_fit _ _ _ (set_record_ok_field_types _ _ _ _ _ HSR) _ Hin) as Hfit.
    rewrite length_record_fctx in Hfit by (unfold n; lia). exact Hfit.
Qed.

(** ** Projections *)

(** A field's value is of its type at the values before it. *)
Lemma set_fields_fit_nth : forall Fs pre vs, set_fields_fit Fs pre vs -> forall k F v, List.nth_error Fs k = Some F ->
    List.nth_error vs k = Some v -> set_mem v (code_carrier (F (pre ++ List.firstn k vs))).
Proof.
  induction 1 as [pre | G Gs pre w ws Hw Hws IH]; intros [| k] F v HF Hv; cbn in HF, Hv; try discriminate.
  - injection HF as <-. injection Hv as <-. rewrite List.app_nil_r. exact Hw.
  - cbn [List.firstn]. pose proof (IH _ _ _ HF Hv) as H. rewrite <- List.app_assoc in H. exact H.
Qed.

Lemma length_set_tele_types : forall Γ0 Δ Fs, set_tele_types T γ Γ0 Δ Fs -> List.length Fs = List.length Δ.
Proof. induction 1; cbn; [reflexivity | rewrite List.length_app; cbn; lia]. Qed.

(** An entry's type, read at the values before it. *)
Lemma set_tele_types_entry : forall Γ0 Δ Fs, set_tele_types T γ Γ0 Δ Fs -> forall X κ A Δ', Δ = X ++ ce_ass κ A :: Δ' ->
    exists F, set_reads T γ (Δ' ++ Γ0) A F /\ List.nth_error Fs (List.length Δ') = Some F.
Proof.
  induction 1 as [| κ0 A0 Δ Fs F HΔ IH HA]; intros [| x X] κ A Δ' E; cbn in E; try discriminate.
  - injection E as <- <- <-. exists F. split; [exact HA |].
    rewrite List.nth_error_app2 by (rewrite (length_set_tele_types _ _ _ HΔ); lia).
    rewrite (length_set_tele_types _ _ _ HΔ), Nat.sub_diag. reflexivity.
  - injection E as _ E. destruct (IH _ _ _ _ E) as (G & HG & Hn). exists G. split; [exact HG |].
    rewrite List.nth_error_app1; [exact Hn |]. rewrite (length_set_tele_types _ _ _ HΔ), E, List.length_app. cbn. lia.
Qed.

(** The arguments of the first [j] fields' telescope over the parameters,
    each at its instance. *)
Lemma record_args_typed_gen : forall (P : exp -> typ -> Prop) R Ns Ms j, j <= List.length (record_fields R) ->
    List.length Ns = List.length (record_params R) -> List.length Ms = j -> all_assumptions (record_params R) ->
    (forall k N B, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) sb_id Ns) k = Some B -> P N B) ->
    (forall i f U M, i < j -> List.nth_error (record_fields R) i = Some (f, U) -> List.nth_error Ms i = Some M ->
       P M (exp_sub U (sb_of_list sb_id (Ns ++ List.firstn i Ms)))) ->
    forall k N B, List.nth_error (Ns ++ Ms) k = Some N ->
      List.nth_error (tele_insts (record_fctx R j ++ record_params R) sb_id (Ns ++ Ms)) k = Some B -> P N B.
Proof.
  intros * Hj Hl HlM Hass HP HF k N B HN HB.
  rewrite tele_insts_app in HB by (exact Hass || exact Hl).
  assert (HlT : List.length (tele_insts (record_params R) sb_id Ns) = List.length Ns) by (rewrite length_tele_insts by exact Hass; lia).
  destruct (Nat.lt_ge_cases k (List.length Ns)) as [Hlt | Hge].
  - rewrite List.nth_error_app1 in HN by lia. rewrite List.nth_error_app1 in HB by lia. exact (HP _ _ _ HN HB).
  - rewrite List.nth_error_app2 in HN by lia. rewrite List.nth_error_app2 in HB by lia. rewrite HlT in HB.
    destruct (tele_insts_record_fctx _ _ _ _ _ _ Hj HlM HB) as (f & U & Hf & Hi & ->).
    rewrite <- sb_of_list_app. exact (HF _ _ _ _ Hi Hf HN).
Qed.

(** The projections of a value before a field. *)
Lemma set_interp_list_record_pre : forall Γ ρ M v R j, set_interp T γ Γ ρ M v ->
    set_interp_list T γ Γ ρ (record_pre R j M) (List.map (fun fT => tuple_field v (fst fT)) (List.firstn j (record_fields R))).
Proof.
  intros * HM. unfold record_pre. induction (List.firstn j (record_fields R)) as [| fT l IH]; cbn; constructor;
    [exact (set_interp_proj T γ _ _ _ _ _ HM) | exact IH].
Qed.

Lemma firstn_record_pre : forall R i j M, i <= j -> List.firstn i (record_pre R j M) = record_pre R i M.
Proof. intros. unfold record_pre. rewrite List.firstn_map, List.firstn_firstn. f_equal. f_equal. lia. Qed.

Lemma In_combine_nth : forall {X Y} (l1 : list X) (l2 : list Y) i a b, List.nth_error l1 i = Some a -> List.nth_error l2 i = Some b ->
    In (a, b) (List.combine l1 l2).
Proof.
  induction l1 as [| x l1 IH]; intros [| y l2] [| i] a b H1 H2; cbn in *; try discriminate.
  - injection H1 as <-. injection H2 as <-. left; reflexivity.
  - right. exact (IH _ _ _ _ H1 H2).
Qed.

Lemma map_fst_combine_le : forall {X Y} (l1 : list X) (l2 : list Y), List.length l1 <= List.length l2 -> List.map fst (List.combine l1 l2) = l1.
Proof.
  intros X Y l1. induction l1 as [| x l1 IH]; intros [| y l2] Hl; cbn in *; try reflexivity; try lia. f_equal. apply IH. lia.
Qed.

Lemma Forall2_of_nth : forall {X Y} (P : X -> Y -> Prop) l l', List.length l = List.length l' ->
    (forall i a b, List.nth_error l i = Some a -> List.nth_error l' i = Some b -> P a b) -> Forall2 P l l'.
Proof.
  induction l as [| x l IH]; intros [| y l'] Hl H; cbn in Hl; try discriminate; constructor.
  - exact (H 0 x y eq_refl eq_refl).
  - apply IH; [lia | intros i; exact (H (S i))].
Qed.

(** The projection of an element at a field, the projections before it
    typed, is of the field's type at them. *)
Lemma set_proj_field : forall Γ M p R Ns j f U FA FM FM', ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_ctx T γ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup gc_deps gc_stack p = Some R ->
    List.length Ns = List.length (record_params R) ->
    (forall k N B, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) sb_id Ns) k = Some B ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ N : B) ->
    (forall k N B, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) sb_id Ns) k = Some B ->
       set_exp_eq T γ Γ B N N) ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ M : apps_exp (a_record p) Ns ->
    set_exp_eq_with T γ Γ (apps_exp (a_record p) Ns) M M FA FM FM' ->
    List.nth_error (record_fields R) j = Some (f, U) ->
    (forall i f' U', i < j -> List.nth_error (record_fields R) i = Some (f', U') ->
       set_exp_eq T γ Γ (exp_sub U' (sb_of_list sb_id (Ns ++ record_pre R i M))) (a_proj f' M) (a_proj f' M)) ->
    exists FU, set_denotes T γ Γ (exp_sub U (sb_of_list sb_id (Ns ++ record_pre R j M))) FU /\
      forall ρ, set_env_in T γ Γ ρ -> set_mem (tuple_field (FM ρ) f) (code_carrier (FU ρ)).
Proof.
  intros * Hc HΓ Hr HR Hl HNs HNr HMw [HFA HFM _ _ HMm] Hfj Hpre.
  destruct (wf_record_inversion Hr) as [R0 Hl0 Hnd Hass i0 _ HF _ _ _ _ _]. rewrite HR in Hl0. injection Hl0 as <-.
  pose proof (set_gctx_ok_records _ _ Hok _ _ HR) as HSR. pose proof (wf_record_closed _ _ _ _ _ Hc HR) as Hcl.
  assert (Hj : j < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
  destruct (set_record_tele_ctx Γ p R j Hc HΓ HR ltac:(lia) HF Hass) as (HCT & HsT & HcT & HCTΓ & HcTΓ).
  assert (Hlp : List.length (record_pre R j M) = j) by (apply length_record_pre; lia).
  assert (Hlen : List.length (Ns ++ record_pre R j M) = List.length (record_fctx R j ++ record_params R))
    by (rewrite !List.length_app, length_record_fctx, Hl, Hlp by lia; lia).
  (* the arguments, typed *)
  assert (HMM : gc_deps ⍮ gc_stack ⍮ Γ ⊢ M ≈ M : apps_exp (a_record p) Ns) by mauto 3.
  pose proof (record_pre_eq _ _ _ _ _ _ _ _ HMM Hr HR Hl HNs j ltac:(lia)) as Hsyn.
  assert (Hsem : forall k N B, List.nth_error (Ns ++ record_pre R j M) k = Some N ->
            List.nth_error (tele_insts (record_fctx R j ++ record_params R) sb_id (Ns ++ record_pre R j M)) k = Some B ->
            set_exp_eq T γ Γ B N N).
  { apply (record_args_typed_gen (fun N B => set_exp_eq T γ Γ B N N) R Ns (record_pre R j M) j ltac:(lia) Hl Hlp Hass HNr).
    intros i f' U' N Hi Hf' HN. unfold record_pre in HN. rewrite List.nth_error_map, List.nth_error_firstn in HN.
    destruct (Nat.ltb_spec i j) as [_ | ]; [| lia]. rewrite Hf' in HN. cbn in HN. injection HN as <-.
    rewrite firstn_record_pre by lia. exact (Hpre _ _ _ Hi Hf'). }
  destruct (set_gsub_closed_inst T γ Hfn Hmods _ _ _ HΓ (record_fctx_params_ass _ _ Hass) HCTΓ HcTΓ Hlen
              (fun k N B HN HB => presup_exp_eq_left (Hsyn _ _ _ _ HN HN HB)) Hsem) as (Fι & Hι & Hvals).
  (* the field's type over the fields before it *)
  pose proof (set_record_ok_field_types _ _ _ _ _ HSR) as Htt.
  destruct (record_fctx_split R (S j) ltac:(lia)) as (X & HX). rewrite (record_fctx_succ _ _ _ _ Hfj) in HX.
  destruct (set_tele_types_entry _ _ _ Htt _ _ _ _ HX) as (Fj & HFj & HnF). rewrite length_record_fctx in HnF by lia.
  set (FX := fun ρ' => Fj (set_env_values (record_fctx R j ++ record_params R) ρ')).
  assert (HFX : set_denotes T γ (record_fctx R j ++ record_params R) U FX)
    by (apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HCT); intros ρ' Hρ'; exact (HFj _ Hρ')).
  assert (HUs : exp_scoped (List.length (record_fctx R j ++ record_params R)) U)
    by (rewrite List.length_app, length_record_fctx by lia; exact (closed_fields _ Hcl _ _ _ Hfj)).
  pose proof (set_closed_inst_denotes T γ Hfn Hmods _ _ _ _ _ _ Hι HΓ HCT HsT HcT HCTΓ HcTΓ HUs HFX) as HFU.
  eexists. split; [exact HFU |]. intros ρ Hρ.
  (* the element's tuple of fields *)
  pose proof (set_denotes_exists _ _ _ _ _ HFA _ Hρ) as Hap. destruct (set_interp_apps_inv T γ _ _ _ _ _ Hap) as (v0 & ns & Hv0 & Hns & Eap).
  inversion Hv0; subst.
  pose proof (set_interp_list_app _ _ _ _ _ _ Hns (set_interp_list_record_pre _ _ _ _ R j (set_denotes_exists _ _ _ _ _ HFM _ Hρ))) as Hargs.
  pose proof (Hvals _ _ Hρ Hargs) as Ev.
  destruct (set_closed_inst_env T γ Hfn Hmods _ _ _ _ Hι HΓ HCT HsT HcT HcTΓ _ Hρ) as [Hin Evs].
  set (ρs := set_env_moved (List.length (record_fctx R j ++ record_params R)) (set_env_drop (List.length Γ)) (Fι ρ)) in *.
  rewrite <- Evs, set_env_values_app, length_record_fctx in Ev by lia.
  assert (Hlns : List.length ns = List.length Ns) by (clear - Hns; induction Hns; cbn; congruence).
  destruct (list_set_eq_app_inv ns _ (set_env_values (record_params R) (set_env_drop j ρs)) _
              ltac:(rewrite length_set_env_values, Hlns; exact Hl) Ev) as [Ens Eps].
  assert (Hρp : set_env_in T γ (record_params R) (set_env_drop j ρs)).
  { pose proof (set_env_rel_drop T γ (record_fctx R j) (record_params R) _ _ Hin) as H.
    rewrite length_record_fctx in H by lia. exact H. }
  pose proof (HMm _ Hρ) as Hv. rewrite Eap in Hv.
  eapply set_mem_eq_r in Hv; [| apply code_carrier_resp; eapply set_eq_trans;
                                 [apply apply_values_resp; [apply set_eq_refl | exact Ens] | exact (set_record_ok_former_value _ _ _ _ _ HSR _ Hρp)]].
  eapply set_mem_eq_r in Hv; [| apply code_carrier_type_code].
  destruct (proj1 (set_record_ok_carrier _ _ _ _ _ HSR _ _ Hρp) Hv) as (vs & [Hlvs Etup Hfit]).
  rewrite (set_record_ok_names _ _ _ _ _ HSR) in Hlvs, Etup. rewrite List.length_map in Hlvs.
  (* the projections are the fields' values *)
  assert (Hat : forall i g W w, List.nth_error (record_fields R) i = Some (g, W) -> List.nth_error vs i = Some w ->
            set_eq (tuple_field (FM ρ) g) w).
  { intros i g W w Hg Hw. eapply set_eq_trans; [apply tuple_field_resp; exact Etup |]. apply tuple_field_at.
    - rewrite map_fst_combine_le by (rewrite List.length_map; lia). exact Hnd.
    - apply (In_combine_nth _ _ i); [rewrite List.nth_error_map, Hg; reflexivity | exact Hw]. }
  destruct (List.nth_error vs j) as [w |] eqn:Hw; [| apply List.nth_error_None in Hw; lia].
  eapply set_mem_eq_l; [apply set_eq_sym; exact (Hat _ _ _ _ Hfj Hw) |].
  pose proof (set_fields_fit_nth _ _ _ Hfit _ _ _ HnF Hw) as Hmem.
  (* the type at the projections is the type at the fields' values *)
  assert (Epre : list_set_eq (set_env_values (record_fctx R j) ρs) (List.firstn j vs)).
  { assert (E2 : list_set_eq (List.map (fun fT => tuple_field (FM ρ) (fst fT)) (List.firstn j (record_fields R))) (List.firstn j vs)).
    { apply Forall2_of_nth; [rewrite List.length_map, !List.length_firstn; lia |].
      intros i a b Ha Hb. rewrite List.nth_error_map, List.nth_error_firstn in Ha. rewrite List.nth_error_firstn in Hb.
      destruct (Nat.ltb i j); [| discriminate].
      destruct (List.nth_error (record_fields R) i) as [[g W] |] eqn:Hg; [| discriminate]. cbn in Ha. injection Ha as <-.
      exact (Hat _ _ _ _ Hg Hb). }
    clear - Eps E2. revert E2. generalize (List.firstn j vs). induction Eps as [| a b l l' Eab Hl IH]; intros vs' E2;
      inversion E2 as [| ? c ? cs Eac Hcs]; subst; constructor.
    - eapply set_eq_trans; [apply set_eq_sym; exact Eab | exact Eac].
    - exact (IH _ Hcs). }
  pose proof (set_env_rel_retarget _ _ _ _ (record_fctx_ass R j) Hin Epre) as Hrel.
  set (B := set_env_extend_kinded (set_env_drop (List.length (record_fctx R j)) ρs) (ctx_kinds (record_fctx R j)) (List.firstn j vs))
    in Hrel.
  destruct (set_env_rel_per T γ _ HCT) as [Hsym Htrans].
  pose proof (Htrans _ _ _ (Hsym _ _ Hrel) Hrel) as HB.
  pose proof (set_denotes_unique _ _ _ _ _ HFX _ _ _ Hrel (HFj _ HB)) as EB.
  assert (Hlj : List.length (List.firstn j vs) = j) by (rewrite List.length_firstn; lia).
  assert (EvB : set_env_values (record_fctx R j ++ record_params R) B =
                set_env_values (record_params R) (set_env_drop j ρs) ++ List.firstn j vs).
  { unfold B. rewrite set_env_values_app, set_env_values_extend_kinded by (rewrite length_record_fctx; lia).
    f_equal. apply set_env_values_ext. intros x. cbv [set_env_drop]. rewrite !length_record_fctx by lia.
    pose proof (set_env_extend_kinded_ge (List.firstn j vs) (ctx_kinds (record_fctx R j)) (fun x0 => ρs (j + x0)) x) as E.
    rewrite Hlj in E. exact E. }
  rewrite EvB in EB. cbn beta. eapply set_mem_eq_r; [apply code_carrier_resp; exact EB | exact Hmem].
Qed.

Lemma set_rule_proj : forall Γ M p R Ns k f U, ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_ctx T γ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_record p : record_ty R -> record_lookup gc_deps gc_stack p = Some R ->
    List.length Ns = List.length (record_params R) ->
    (forall k N B, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) sb_id Ns) k = Some B ->
       gc_deps ⍮ gc_stack ⍮ Γ ⊢ N : B) ->
    (forall k N B, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) sb_id Ns) k = Some B ->
       set_exp_eq T γ Γ B N N) ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ M : apps_exp (a_record p) Ns -> set_exp_eq T γ Γ (apps_exp (a_record p) Ns) M M ->
    List.nth_error (record_fields R) k = Some (f, U) ->
    set_exp_eq T γ Γ (exp_sub U (sb_of_list sb_id (Ns ++ record_pre R k M))) (a_proj f M) (a_proj f M).
Proof.
  intros * Hc HΓ Hr HR Hl HNs HNr HMw (FA & FM & FM' & HM) Hk.
  pose proof HM as [_ HFM _ _ _].
  assert (HP : forall g, set_denotes T γ Γ (a_proj g M) (fun ρ => tuple_field (FM ρ) g))
    by (intros g; apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ); intros ρ Hρ;
        exact (set_interp_proj T γ _ _ _ _ _ (set_denotes_exists _ _ _ _ _ HFM _ Hρ))).
  assert (Hall : forall j i f' U', i < j -> List.nth_error (record_fields R) i = Some (f', U') ->
            set_exp_eq T γ Γ (exp_sub U' (sb_of_list sb_id (Ns ++ record_pre R i M))) (a_proj f' M) (a_proj f' M)).
  { induction j as [| j IH]; intros i f' U' Hi Hf'; [lia |].
    destruct (Nat.lt_ge_cases i j) as [Hij | Hij]; [exact (IH _ _ _ Hij Hf') |]. assert (i = j) by lia. subst i.
    destruct (set_proj_field _ _ _ _ _ _ _ _ _ _ _ Hc HΓ Hr HR Hl HNs HNr HMw HM Hf' IH) as (FU & HFU & Hmem).
    exists FU, (fun ρ => tuple_field (FM ρ) f'), (fun ρ => tuple_field (FM ρ) f').
    constructor; [exact HFU | exact (HP f') | exact (HP f') | intros; apply set_eq_refl | exact Hmem]. }
  exact (Hall (S k) k f U ltac:(lia) Hk).
Qed.

End Records.
