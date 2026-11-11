(** * Members of Applied Module Expressions

    A member of a module expression lacking a parameter, applied to an
    argument, is the member of the module expression given the argument
    ([wf_exp_eq_mem_app]).  No rule says so: both sides are δ-equal to
    reducts related by [β], or the member is the filed member of a bare
    stored body ([mem_alias_filed]) and its application the self-named
    reduct of the member of the stored body at the argument. *)

From Stdlib Require Import Lia List PeanoNat RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System SystemOpt CoreInversions.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Modules Paths DescTyping LookupSound Presup.
From Mctt.Core.Soundness Require Import LogicalRelation ModuleValues Selection.
Import Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Import Fixed_Notations.

(** A description abstracted over a telescope ending in an assumption, as
    the term part's reduct: a [λ] over the outermost parameter. *)
Lemma reduct_up_last : forall Δ0 κ B X M,
    mdesc_reduct X = Some M ->
    mdesc_reduct (mdesc_up (Δ0 ++ ce_ass κ B :: nil) X) = Some (λ B (ctx_fn Δ0 M)).
Proof. intros * HM; rewrite mdesc_reduct_up, HM; cbn [option_map]; rewrite ctx_fn_app; reflexivity. Qed.

(** Parameters of types of levels, the inner ones. *)
Lemma level_sorted_parameters_app_l : forall Δ0 Δ1, level_sorted_parameters (Δ0 ++ Δ1) -> level_sorted_parameters Δ0.
Proof. intros * H Δa κ T Δb ->; eapply H; rewrite <- app_assoc; reflexivity. Qed.

(** A definition of a type of levels in an open module: the module's
    parameters are of types of levels ([desc_levels_abstractable]). *)
Lemma open_entry_level_params : forall Γ Δ Φw Φx y Φ0 E A M,
    desc_ok gc_deps gc_stack Γ (mdesc_open Δ Φw Φx) ->
    gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
    entry_kind E = ak_level -> level_sorted_parameters Δ.
Proof.
  intros * Hok Hp HE Hk; inversion Hok; subst.
  match goal with HL : desc_levels_abstractable _ _ _ _ _ |- _ => destruct HL as [HLs | Hnl] end; [ assumption |].
  exfalso; inversion Hnl; subst.
  match goal with Hne : forall y Φ0 E A M, gm_prefix_upto _ y = Some _ -> entry_tm E = Some (A, M) -> entry_kind E <> ak_level |- _ =>
    exact (Hne _ _ _ _ _ Hp HE Hk) end.
Qed.

(** A member of an open module lacking a parameter, applied to an
    argument, is the member of the module given it: both are δ-equal to
    their reducts, the first a [λ] over the parameter whose body is typed
    over it ([body_defs_wf], [ctx_fn_eq]), [β]-equal to the second. *)
Lemma mem_app_eq_open : ⊢ᵍ gc_deps ⍮ gc_stack -> forall Γ H N x R0 Δ Φw Φx R A,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H N -> names_no_frame H ->
    mdenote gc_deps gc_stack Γ H R0 -> mdesc_mod R0 = Some (mdesc_open Δ Φw Φx) ->
    mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A ->
    Γ ⊢ a_mem H x : A ->
    exists R' A', mdenote gc_deps gc_stack Γ (me_mem (me_app H N) x) R' /\ mdesc_type R' = Some A' /\
      Γ ⊢ a_mem H x $ N ≈ a_mem (me_app H N) x : A'.
Proof.
  intros Hgw * HHN Hq HR0 HR0m Hm HA HxA.
  pose proof (wf_gstack_closed _ _ Hgw) as Hc.
  destruct (proj1 (modexp_gen _ _ _ _ _ HHN)) as [HH (R0' & T & B & T1 & Srt & HR0' & HT & Hv & HB & HSrt & HNt)].
  rewrite (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ HR0' _ HR0) in HT.
  unfold mdesc_mod_tele in HT; rewrite HR0m in HT; cbn [mdesc_tele] in HT; injection HT as <-.
  pose proof (desc_ok_mod _ _ Hgw _ _ _ (me_desc_ok _ _ _ _ _ _ HH HR0) HR0m) as Hok.
  pose proof Hok as Hok0; inversion Hok0; subst.
  match goal with H : all_assumptions Δ |- _ => rename H into HΔa end.
  (** The outermost parameter *)
  destruct Δ as [| e Δ0 _] using rev_ind; [ cbn in Hv; discriminate |].
  pose proof HΔa as HΔa0; unfold all_assumptions in HΔa0; apply Forall_app in HΔa0 as [HΔ0a He1];
    apply Forall_cons_iff in He1 as [(κ & B0 & ->) _].
  rewrite tele_view_last in Hv; injection Hv as <- <-.
  (** The member's entry, read *)
  apply (mdenote_mem_no_frame _ _ _ _ _ Hgw Hq Hm); intros R0'' R0m Γy E rd R1 Hm0 HR0m' He Hed Hrd.
  rewrite (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ Hm0 _ HR0), HR0m in HR0m'; injection HR0m' as <-.
  pose proof He as He0; cbn in He0.
  destruct (gm_prefix_upto Φx x) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & Heq & _); injection Heq as <- -> <-.
  (** The term part, abstracted over the parameters *)
  assert (HX : exists r A1 M1, entry_tm E0 = Some (A1, M1) /\ entry_kind E0 = r /\ Γy = body_ctx Φ' ++ Δ0 ++ ce_ass κ B0 :: nil /\
            E = E0 /\ rd = reader_open (Δ0 ++ ce_ass κ B0 :: nil) Φ' /\ mdesc_kind R1 = r /\
            mdesc_type R1 = Some A1 /\ mdesc_reduct R1 = Some M1).
  { destruct E0 as [[|] pv r A1 [M1 |] | pv U | | pv A1 M1 U |]; try discriminate; injection He0 as <- <- <-.
    - inversion Hed; subst; exists r, A1, M1; repeat split; reflexivity.
    - exfalso; inversion Hed; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmm end.
      cbn [mdesc_read] in Hrd; destruct (gm_fill Φ'); cbn [option_map] in Hrd; [ injection Hrd as <- | discriminate ].
      destruct R1; cbn in Hmm; try contradiction; cbn in HA; discriminate.
    - inversion Hed; subst; exists ak_relevant, A1, M1; repeat split; reflexivity. }
  destruct HX as (r & A1 & M1 & HtE & HkE & -> & -> & -> & Hk1 & HA1 & HM1).
  assert (HrdR1 : mdesc_read (reader_open (Δ0 ++ ce_ass κ B0 :: nil) Φ') R1 = Some R) by exact Hrd.
  cbn [mdesc_read] in Hrd; destruct (gm_fill Φ') as [σf |] eqn:Hf; cbn [option_map] in Hrd; [ injection Hrd as <- | discriminate ].
  (** The reduct and the type before the argument: a [λ] and a [Π] over it *)
  set (Mb := ctx_fn Δ0 M1[σf]); set (Ab := ctx_pi_at r Δ0 A1[σf]).
  assert (HRr : mdesc_reduct (mdesc_up (Δ0 ++ ce_ass κ B0 :: nil) (mdesc_sub R1 σf)) = Some (λ B0 Mb))
    by exact (reduct_up_last _ _ _ _ _ (mdesc_reduct_sub _ _ _ HM1)).
  assert (HRt : mdesc_type (mdesc_up (Δ0 ++ ce_ass κ B0 :: nil) (mdesc_sub R1 σf)) = Some (a_pi κ r B0 Ab)).
  { rewrite (mdesc_type_up _ _ _ (mdesc_type_sub _ _ σf HA1)), mdesc_kind_sub, Hk1, ctx_pi_app; reflexivity. }
  rewrite HRt in HA; injection HA as <-.
  (** The member after the argument *)
  pose proof (mdesc_at_up Δ0 κ B0 (mdesc_sub R1 σf) N) as HRat.
  set (R' := mdesc_up (tele_sub Δ0 (Id,,N)) (mdesc_sub (mdesc_sub R1 σf) (sb_qn (List.length Δ0) (Id,,N)))) in HRat.
  assert (HtR' : mdesc_type R' = Some Ab[Id,,N]).
  { unfold R', Ab; rewrite (mdesc_type_up _ _ _ (mdesc_type_sub _ _ _ (mdesc_type_sub _ _ σf HA1))), !mdesc_kind_sub, Hk1, ctx_pi_sub;
      reflexivity. }
  assert (HrR' : mdesc_reduct R' = Some Mb[Id,,N]).
  { unfold R', Mb; rewrite mdesc_reduct_up, (mdesc_reduct_sub _ _ _ (mdesc_reduct_sub _ _ σf HM1)), ctx_fn_sub; reflexivity. }
  destruct (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & _ & _).
  pose proof (mdesc_mod_scoped _ _ _ (wf_mdenote_scoped _ _ _ _ _ _ HH HR0) HR0m) as Hs0.
  pose proof (mdesc_mod_is_mod _ _ HR0m) as HisR0m.
  destruct (mdesc_at_of_view _ _ N _ _ _ Hok HisR0m eq_refl ltac:(rewrite tele_view_last; reflexivity)) as (R0m' & HR0m').
  destruct (mdesc_at_of_mod_part _ _ _ _ HR0m HR0m') as (R0a & HR0a & HmR0a).
  rewrite (mdesc_is_mod_mod _ (mdesc_at_is_mod _ _ _ HisR0m HR0m')) in HmR0a.
  assert (HmX : mdenote gc_deps gc_stack Γ (me_app H N) R0a) by exact (mdenote_app _ _ _ _ _ _ _ HR0 HR0a).
  destruct (sel_at_open _ _ Hc _ _ _ _ _ _ _ _ _ _ _ _ _ HΓ Hs0 HΔa HR0m' He Hed HrdR1 HRat)
    as (Γy' & E' & rd' & R'' & He' & Hed' & Hrd').
  assert (Hpath : mdesc_entry_path R0m' x = None)
    by (cbn [mdesc_at] in HR0m'; destruct (tele_split (rev (Δ0 ++ ce_ass κ B0 :: nil))) as [[[? ?] ?] | ?];
        [ injection HR0m' as <-; reflexivity | discriminate ]).
  assert (HmNx : mdenote gc_deps gc_stack Γ (me_mem (me_app H N) x) R')
    by (eapply mdenote_mem; [ exact HmX | exact HmR0a | exact He' | rewrite Hpath; exact Hed' | exact Hrd' ]).
  (** The body over the parameter *)
  destruct (presup_exp_typ_sorted HxA ltac:(discriminate)) as (S & _ & HAS).
  destruct (wf_pi_parts_at _ _ _ _ _ _ _ _ HAS) as [? i _ _ HAb Hk].
  destruct (body_defs_wf _ _ _ _ _ H3 H4) as (es & _ & Hdefs).
  destruct (Hdefs _ _ _ _ _ _ Hp HtE Hf) as (_ & HMt).
  destruct (H12 _ _ _ _ _ _ Hp HtE Hf) as (j & HAj).
  rewrite <- app_assoc in HMt, HAj; cbn [app] in HMt, HAj.
  assert (HMb : Γ ▹{κ} B0 ⊢ Mb : Ab).
  { eapply presup_exp_eq_left; unfold Mb, Ab; eapply ctx_fn_eq;
      [ exact HΔ0a | exact (presup_exp_ctx HMt)
      | intros Hl; eapply level_sorted_parameters_app_l, open_entry_level_params;
        [ exact Hok | exact Hp | exact HtE | rewrite HkE; exact Hl ]
      | rewrite <- HkE; exact HAj | apply wf_exp_eq_refl; exact HMt ]. }
  exists R', Ab[Id,,N]; split; [ exact HmNx | split; [ exact HtR' |] ].
  eapply wf_exp_eq_trans;
    [ eapply wf_exp_eq_app_cong'; [ eapply wf_exp_eq_mem_delta; [ exact HH | exact Hm | exact HRt | exact HRr ] | apply wf_exp_eq_refl; exact HNt ] |].
  eapply wf_exp_eq_trans; [ eapply wf_exp_eq_pi_beta'; [ exact HAb | exact Hk | exact HMb | exact HNt ] |].
  apply wf_exp_eq_sym; eapply wf_exp_eq_mem_delta; [ exact HHN | exact HmNx | exact HtR' | exact HrR' ].
Qed.

End Fixed_GCtx.
