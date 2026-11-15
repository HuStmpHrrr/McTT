(** * Term Members of Valid Units

    A term member a valid unit, or a module expression valid in what it
    denotes, has by lookup is of the type lookup reads, and is its
    δ-reduct when it has one ([set_valid_unit_members_all]); whether it is
    a proof is read off the syntax as its kind says.  A unit lacking
    parameters gives its members as closures over them: the empty set for
    a proof, the graph of the member at each value otherwise
    ([set_unit_walk_type], [set_unit_walk_reduct]). *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.SetModel.Interpretation Require Import Respects Substitution.
From Mctt.Core.SetModel.Judgments Require Import Substitution.
From Mctt.Core.SetModel Require Import Judgments.
From Mctt.Core.SetModel Require Import Cases.PropCases Cases.FunctionCases Modules.ValidUnit.
From Mctt.Core.Syntactic Require Import Syntax Substitution Members CoreInversions.
From Mctt.Core.Syntactic.System Require Import Definitions Structural Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas DescTyping LookupSound.
From Mctt.Core.Completeness.Modules Require Import ValidUnit Mem Filed.
Import ListNotations.

Lemma ctx_pi_at_app : forall κc Δ1 Δ2 A, ctx_pi_at κc (Δ1 ++ Δ2) A = ctx_pi_at κc Δ2 (ctx_pi_at κc Δ1 A).
Proof. induction Δ1 as [| [] Δ1 IH]; intros; cbn; [reflexivity | apply IH ..]. Qed.

Section MemberTypes.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).
  (** The global context is well formed *)
  Hypothesis Hgw : ⊢ᵍ gc_deps ⍮ gc_stack.
  (** The context this one grew from, at which the derivations whose
      members are spoken of were checked: only its members are
      ([set_member_known]) *)
  Variable Θs : gdeps.
  Variable Ξs : gstack.

(** ** Families Over a Parameter *)

(** Values read past one more assumption respect equality of its value. *)
Lemma set_interp_family_respects : forall Γ ρ κ A X a F, set_env_eq γ ρ ρ ->
    (forall v, set_mem v (code_carrier a) -> set_interp T γ (ce_ass κ A :: Γ) (set_env_extend ρ (set_entry_term κ v)) X (F v)) ->
    respects_on (code_carrier a) F.
Proof.
  intros * Hρ HF v v' Hv E. pose proof (set_mem_eq_l _ _ _ E Hv) as Hv'.
  apply (set_interp_functional T γ Hfn Hmods _ _ _ _ (HF _ Hv) _ _ ltac:(apply set_env_eq_extend; [exact Hρ | constructor; exact E]) (HF _ Hv')).
Qed.

(** So do the modules of a unit over one more parameter. *)
Lemma set_interp_params_family_respects : forall Γ ρ P κ A L D a f x, set_env_eq γ ρ ρ ->
    (forall v, set_mem v (code_carrier a) ->
       set_interp_unit_params T γ (ce_ass κ A :: Γ) (set_env_extend ρ (set_entry_term κ v)) P L D (f v)) ->
    respects_on (code_carrier a) (fun v => select_term γ (f v) x).
Proof.
  intros * Hρ Hf v v' Hv E. pose proof (set_mem_eq_l _ _ _ E Hv) as Hv'. apply select_term_resp.
  apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (set_interp_functional_all T γ Hfn Hmods)))))) _ _ _ _ _ _ (Hf _ Hv) _ P _
           ltac:(apply set_env_eq_extend; [exact Hρ | constructor; exact E]) ltac:(intros; reflexivity) (Hf _ Hv')).
Qed.

(** ** Inversions *)

(** A [Π]'s value: the quantification or the dependent functions over its
    domain's value, of a family of its codomain's values. *)
Lemma set_interp_pi_inv : forall Γ ρ κd κc A B a, set_interp T γ Γ ρ (a_pi κd κc A B) a ->
    exists a1 F, set_interp T γ Γ ρ A a1 /\
      (forall v, set_mem v (code_carrier a1) -> set_interp T γ (ce_ass κd A :: Γ) (set_env_extend ρ (set_entry_term κd v)) B (F v)) /\
      ((κc = ak_propositional /\ a = forall_code a1 F) \/ (κc <> ak_propositional /\ a = pi_code a1 F)).
Proof. intros * H. inversion H; subst; do 2 eexists; (split; [eassumption | split; [eassumption | eauto]]). Qed.

(** [set_interp_fn_with Γ ρ A M v κd κc C B a X F]: the λ [a_fn A M],
    typed at a [Π] into types, has the value [v], the graph of the family
    [F] of its body's values on [X], a set equal to the carrier of the
    domain's value [a]. *)
Record set_interp_fn_with (Γ : ctx) (ρ : set_env) (A M : exp) (v : aczel_set) (κd κc : abs_kind) (C B : exp)
    (a X : aczel_set) (F : aczel_set -> aczel_set) : Prop :=
  { (** The λ is typed at the [Π] *)
    set_interp_fn_with_typed : gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_fn A M : a_pi κd κc C B
    (** into types *)
  ; set_interp_fn_with_kind : κc <> ak_propositional
    (** The domain reads [a] *)
  ; set_interp_fn_with_domain : set_interp T γ Γ ρ A a
    (** [X] is its carrier *)
  ; set_interp_fn_with_set : set_eq X (code_carrier a)
    (** The body reads [F x] at each element [x] of the carrier *)
  ; set_interp_fn_with_body : forall x, set_mem x (code_carrier a) ->
      set_interp T γ (ce_ass κd A :: Γ) (set_env_extend ρ (set_entry_term κd x)) M (F x)
    (** The value is the graph *)
  ; set_interp_fn_with_value : v = graph_set X F }.

(** A λ's value: the empty set, typed at a [Π] into propositions, or the
    graph of a family of its body's values, typed at another. *)
Lemma set_interp_fn_inv : forall Γ ρ A M v, set_interp T γ Γ ρ (a_fn A M) v ->
    (exists κd C B, gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_fn A M : a_pi κd ak_propositional C B /\ v = empty_set) \/
    (exists κd κc C B a X F, set_interp_fn_with Γ ρ A M v κd κc C B a X F).
Proof. intros * H. inversion H; subst; [left; eauto | right; do 7 eexists; constructor; eauto]. Qed.

(** ** Walking a Unit's Parameters *)

(** A member of a unit over the parameters [L], outermost first, is of
    the [Π] over them at the member's kind when it is of the type at every
    environment past them: a function of each parameter, the empty set
    for a proof. *)
Lemma set_unit_walk_type : forall L Γ ρ P D m r B x,
    all_assumptions L -> set_env_in T γ Γ ρ -> set_interp_unit_params T γ Γ ρ P L D m -> P nil x = is_proof_kind r ->
    (forall ρ' mD b, set_env_in T γ (List.rev L ++ Γ) ρ' -> set_interp_moddef T γ (List.rev L ++ Γ) ρ' D mD ->
       set_interp T γ (List.rev L ++ Γ) ρ' B b -> set_mem (select_term γ mD x) (code_carrier b)) ->
    (r = ak_propositional -> forall ρ' mD, set_env_in T γ (List.rev L ++ Γ) ρ' -> set_interp_moddef T γ (List.rev L ++ Γ) ρ' D mD ->
       set_eq (select_term γ mD x) empty_set) ->
    (r = ak_propositional -> set_eq (select_term γ m x) empty_set) /\
    (forall a, set_interp T γ Γ ρ (ctx_pi_at r (List.rev L) B) a -> set_mem (select_term γ m x) (code_carrier a)).
Proof.
  induction L as [| e L IH]; intros Γ ρ P D m r B x HL Hρ Hm HP Hb Hb0.
  - inversion Hm; subst. split; [intros Er; exact (Hb0 Er _ _ Hρ ltac:(eassumption)) |].
    intros a Ha. exact (Hb _ _ _ Hρ ltac:(eassumption) Ha).
  - inversion HL as [| ? ? (κ & A & ->) HL']; subst.
    inversion Hm as [| ? ? ? ? ? ? ? a0 f Hc HA Hf | | |]; subst.
    split; [intros ->; cbn [select_term]; rewrite HP; apply set_eq_refl |].
    intros a Ha. cbn [List.rev] in Ha. rewrite ctx_pi_at_app in Ha. cbn [ctx_pi_at] in Ha.
    pose proof (set_env_rel_eq T γ _ _ _ Hρ) as Eρ.
    assert (Hstep : forall v, set_mem v (code_carrier a0) ->
               (r = ak_propositional -> set_eq (select_term γ (f v) x) empty_set) /\
               (forall b, set_interp T γ (ce_ass κ A :: Γ) (set_env_extend ρ (set_entry_term κ v)) (ctx_pi_at r (List.rev L) B) b ->
                  set_mem (select_term γ (f v) x) (code_carrier b))).
    { intros v Hv. cbn [List.rev] in Hb, Hb0. rewrite <- List.app_assoc in Hb, Hb0.
      exact (IH _ _ P D _ r B x HL' (set_env_rel_extend_ass T γ _ _ _ _ _ _ _ _ Hρ HA Hv (set_eq_refl v)) (Hf _ Hv) HP Hb Hb0). }
    pose proof (set_interp_params_family_respects _ _ _ _ _ _ _ _ _ x Eρ Hf) as Hfr.
    destruct (set_interp_pi_inv _ _ _ _ _ _ _ Ha) as (a1 & F & HA1 & HF & [[-> ->] | [Hr ->]]).
    all: pose proof (set_interp_functional T γ Hfn Hmods _ _ _ _ HA _ _ Eρ HA1) as E01.
    all: pose proof (code_carrier_resp _ _ E01) as Ec.
    all: assert (H10 : forall v, set_mem v (code_carrier a1) -> set_mem v (code_carrier a0))
           by (intros v Hv; exact (set_mem_eq_r _ _ _ (set_eq_sym _ _ Ec) Hv)).
    + (* a proof: the empty set, true at every parameter *)
      cbn [select_term]. rewrite HP. cbn [is_proof_kind].
      unfold forall_code, prop_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
      apply set_mem_truth. split; [| apply set_eq_refl].
      intros v Hv. destruct (Hstep v (H10 _ Hv)) as [Hp1 Hm1].
      exact (set_mem_eq_l _ _ _ (Hp1 eq_refl) (Hm1 _ (HF _ Hv))).
    + (* otherwise the graph of the member at each parameter *)
      cbn [select_term]. rewrite HP. destruct r; [| contradiction |]; cbn [is_proof_kind].
      all: unfold pi_code; eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
      all: eapply set_mem_eq_l;
        [apply (graph_set_resp_on (code_carrier a1) (code_carrier a0) (fun v => select_term γ (f v) x)
                  (fun v => select_term γ (f v) x) (set_eq_sym _ _ Ec));
         intros v v' Hv E; exact (Hfr _ _ (H10 _ Hv) E) |].
      all: apply graph_set_function_on.
      all: try (intros v v' Hv E; apply code_carrier_resp; exact (set_interp_family_respects _ _ _ _ _ _ _ Eρ HF _ _ Hv E)).
      all: try (intros v v' Hv E; apply Hfr; [exact (H10 _ Hv) | exact E]).
      all: intros v Hv; exact (proj2 (Hstep v (H10 _ Hv)) (F v) (HF _ Hv)).
Qed.

(** The member is the [λ] over the parameters of its reduct when it is the
    reduct at every environment past them: each [λ] is typed at the
    member's kind, so it is a proof exactly when the member is. *)
Lemma set_unit_walk_reduct : forall L Γ ρ P D m r B N x,
    all_assumptions L -> set_env_in T γ Γ ρ -> set_interp_unit_params T γ Γ ρ P L D m -> P nil x = is_proof_kind r ->
    (forall L1 L2, L = L1 ++ L2 ->
       gc_deps ⍮ gc_stack ⍮ List.rev L1 ++ Γ ⊢ ctx_fn (List.rev L2) N : ctx_pi_at r (List.rev L2) B) ->
    (forall ρ' mD n, set_env_in T γ (List.rev L ++ Γ) ρ' -> set_interp_moddef T γ (List.rev L ++ Γ) ρ' D mD ->
       set_interp T γ (List.rev L ++ Γ) ρ' N n -> set_eq (select_term γ mD x) n) ->
    forall n, set_interp T γ Γ ρ (ctx_fn (List.rev L) N) n -> set_eq (select_term γ m x) n.
Proof.
  induction L as [| e L IH]; intros Γ ρ P D m r B N x HL Hρ Hm HP HN Hb n Hn.
  - inversion Hm; subst. exact (Hb _ _ _ Hρ ltac:(eassumption) Hn).
  - inversion HL as [| ? ? (κ & A & ->) HL']; subst.
    inversion Hm as [| ? ? ? ? ? ? ? a0 f Hc HA Hf | | |]; subst.
    cbn [List.rev] in Hn. rewrite ctx_fn_app in Hn. cbn [ctx_fn] in Hn.
    pose proof (HN nil (ce_ass κ A :: L) eq_refl) as Hty. cbn [List.rev List.app] in Hty.
    rewrite ctx_fn_app, ctx_pi_at_app in Hty. cbn [ctx_fn ctx_pi_at] in Hty.
    pose proof (set_env_rel_eq T γ _ _ _ Hρ) as Eρ.
    pose proof (set_interp_params_family_respects _ _ _ _ _ _ _ _ _ x Eρ Hf) as Hfr.
    destruct (set_interp_fn_inv _ _ _ _ _ Hn) as [(κd & C & B' & Hty' & ->) | (κd & κc & C & B' & a & X & F & [Hty' Hκc HA1 EX HF ->])].
    + (* a proof *)
      destruct (Hfn _ _ _ _ _ _ _ _ _ _ _ Hty Hty') as [_ ->]. cbn [select_term]. rewrite HP. apply set_eq_refl.
    + destruct (Hfn _ _ _ _ _ _ _ _ _ _ _ Hty Hty') as [<- <-]. cbn [select_term]. rewrite HP.
      destruct r; [| contradiction |]; cbn [is_proof_kind].
      all: pose proof (set_interp_functional T γ Hfn Hmods _ _ _ _ HA _ _ Eρ HA1) as E01.
      all: pose proof (code_carrier_resp _ _ E01) as Ec.
      all: apply (graph_set_resp_on _ _ _ _ (set_eq_trans _ _ _ Ec (set_eq_sym _ _ EX))); intros v v' Hv E.
      all: pose proof (set_mem_eq_l _ _ _ E Hv) as Hv'.
      all: eapply set_eq_trans; [exact (Hfr _ _ Hv E) |].
      all: apply (IH _ _ P D _ _ B N x HL' (set_env_rel_extend_ass T γ _ _ _ _ _ _ _ _ Hρ HA Hv' (set_eq_refl v')) (Hf _ Hv') HP);
        [ intros L1 L2 EL; subst L; pose proof (HN (ce_ass κ A :: L1) L2 eq_refl) as H0; cbn [List.rev] in H0;
          rewrite <- List.app_assoc in H0; exact H0
        | intros ρ' mD n Hρ' HmD Hn0; cbn [List.rev] in Hb; rewrite <- List.app_assoc in Hb; exact (Hb _ _ _ Hρ' HmD Hn0)
        | apply HF; exact (set_mem_eq_r _ _ _ Ec Hv') ].
Qed.

(** ** A Body's Definitions *)

(** The last entry of a body so named is the member its table gives that
    name, read in the environment the entries before it make. *)
Lemma set_interp_gmod_prefix : forall Ξ ρ Φ ms ρo, set_interp_gmod T γ Ξ ρ Φ ms ρo ->
    forall x Φ' E, gm_prefix_upto Φ x = Some (gm_ext Φ' x E) ->
    exists ms' ρ0 e, ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx Φ' ++ Ξ /\ set_interp_gmod T γ Ξ ρ Φ' ms' ρ0 /\
      set_interp_gentry T γ (body_ctx Φ' ++ Ξ) ρ0 E e /\ members_lookup ms x = Some e.
Proof.
  induction 1 as [| Ξ ρ Φ y E0 ms ρo e Hc HΦ IH HE]; intros x Φ' E Hp; cbn [gm_prefix_upto] in Hp; [discriminate |].
  rewrite members_lookup_snoc. destruct (String.eqb_spec x y) as [-> | Hne].
  - injection Hp as <- <-. exists ms, ρo, e. auto.
  - destruct (IH _ _ _ Hp) as (ms' & ρ0 & e' & H0 & H1 & H2 & H3). exists ms', ρ0, e'. auto.
Qed.

(** The type of a definition of a body, filled in, is of its kind's sort. *)
Lemma set_body_sorts_valid_entry : forall Φ D x Φ' E A M σ, set_body_sorts_valid T γ Φ D ->
    gm_prefix_upto Φ x = Some (gm_ext Φ' x E) -> entry_tm E = Some (A, M) -> gm_fill Φ' = Some σ ->
    exists i, set_rel_exp_eq T γ D (abs_kind_sort (entry_kind E) (a_typ i)) (exp_sub A σ) (exp_sub A σ).
Proof.
  induction Φ as [| Φ IH y E0 | Φ IH H its Φg _]; intros * Hs Hp HE Hf; cbn [gm_prefix_upto set_body_sorts_valid] in Hp, Hs;
    [discriminate | |].
  - destruct Hs as [Hs HE0]. destruct (String.eqb_spec x y) as [-> | _]; [injection Hp as <- <-; exact (HE0 _ _ _ HE Hf) |].
    exact (IH _ _ _ _ _ _ _ Hs Hp HE Hf).
  - destruct (List.existsb _ _); [discriminate | exact (IH _ _ _ _ _ _ _ Hs Hp HE Hf)].
Qed.

(** The entries of a body of definitions and modules, filled in,
    read at an environment the values the body's environment holds. *)
Lemma set_interp_gmod_fill : forall D ρ Φ ms ρo, set_interp_gmod T γ D ρ Φ ms ρo ->
    forall σ, gm_fill Φ = Some σ -> forall k, sub_entry_agrees T γ D ρ (σ k) (ρo k).
Proof.
  induction 1 as [D ρ | D ρ Φ y E ms ρo e Hc HΦ IH HE]; intros σ Hf k.
  - cbn in Hf. injection Hf as <-. split; constructor.
  - assert (Hsub : forall σ0, gm_fill Φ = Some σ0 -> sub_setting T γ (body_ctx Φ ++ D) ρo nil (body_ctx Φ ++ D) D σ0 ρ ρ).
    { intros σ0 Hf0. constructor; [reflexivity | exact (wf_gm_fill _ _ _ _ _ Hc Hf0) | intros x Hx; cbn in Hx; lia
                                  | intros; reflexivity | intros x; exact (IH _ Hf0 x)]. }
    destruct E as [b pv r A [M |] | pv U | | pv A M U |]; cbn in Hf; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; cbn in Hf; try discriminate; injection Hf as <-;
      inversion HE; subst; (destruct k as [| k]; [| exact (IH _ eq_refl k)]); cbn [sb_extend set_env_extend sentry_exp sentry_modexp].
    + split; [| exact (set_interp_me_unit T γ _ _ nil)].
      exact (set_interp_sub T γ _ _ _ _ ltac:(eassumption) Hc nil _ _ _ _ _ (Hsub _ eq_refl)).
    + split; [constructor |]. cbn [set_entry_module_part].
      apply (proj1 (proj2 (proj2 (proj2 (set_interp_sub_all T γ)))) _ _ (me_lit U) _ ltac:(constructor; eassumption) nil _ _ _ _ _
               Hc (Hsub _ eq_refl)).
    + split; cbn [set_entry_value set_entry_module_part].
      * exact (set_interp_sub T γ _ _ _ _ ltac:(eassumption) Hc nil _ _ _ _ _ (Hsub _ eq_refl)).
      * apply (proj1 (proj2 (proj2 (proj2 (set_interp_sub_all T γ)))) _ _ (me_lit U) _ ltac:(constructor; eassumption) nil _ _ _ _ _
                 Hc (Hsub _ eq_refl)).
Qed.

(** A module read in an environment of a context where its unit denotes
    equals itself. *)
Lemma set_interp_gunit_self_eq : forall Γ ρ U m, set_modexp_rel T γ Γ (me_lit U) (me_lit U) -> set_env_in T γ Γ ρ ->
    set_interp_gunit T γ Γ ρ U m -> set_module_eq γ m m.
Proof.
  intros * (F & F' & [HF _ _]) Hρ Hm.
  pose proof (set_modexp_denotes_unique _ _ _ _ _ HF _ _ _ Hρ (set_interp_me_lit T γ _ _ _ _ Hm)) as E.
  exact (set_module_eq_trans _ _ _ E (set_module_eq_sym _ _ E)).
Qed.

(** The environment a body of definitions and modules makes is one of its
    context. *)
Lemma set_interp_gmod_env_in : forall D ρ Φ ms ρo, set_interp_gmod T γ D ρ Φ ms ρo -> gm_fill Φ <> None ->
    set_env_in T γ D ρ -> set_ctx T γ (body_ctx Φ ++ D) -> set_env_in T γ (body_ctx Φ ++ D) ρo.
Proof.
  induction 1 as [D ρ | D ρ Φ y E ms ρo e Hc HΦ IH HE]; intros Hf Hρ HC; [exact Hρ |].
  destruct E as [b pv r A [M |] | pv U | | pv A M U |]; cbn in Hf, HC |- *; try (exfalso; apply Hf; reflexivity).
  all: destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; cbn in Hf; try (exfalso; apply Hf; reflexivity).
  all: destruct HC as [HC Hce]; pose proof (IH ltac:(discriminate) Hρ HC) as Hρo.
  all: split; [exact Hρo |]; inversion HE; subst; cbn [set_env_tail set_env_extend].
  - exists r, v, v, v. constructor; [reflexivity | reflexivity | assumption | apply set_eq_refl | apply set_eq_refl].
  - pose proof (set_interp_gunit_self_eq _ _ _ _ Hce Hρo ltac:(eassumption)) as Em.
    exists m, m, m. constructor; [reflexivity | reflexivity | assumption | exact Em | exact Em].
  - pose proof (set_interp_gunit_self_eq _ _ _ _ (proj2 Hce) Hρo ltac:(eassumption)) as Em.
    exists v, v, v, m, m, m. constructor; [reflexivity | reflexivity | assumption | assumption | apply set_eq_refl | apply set_eq_refl
                                         | exact Em | exact Em].
Qed.

(** A definition of a body of definitions and modules, filled in, at an
    environment: the member of the body's table is of the type filled in,
    a proposition at a proof, and is the definition filled in. *)
Lemma set_body_member_base : forall D ρ Φx ms ρo x Φ' E A0 M0 σ,
    gm_nopens Φx = 0 -> set_ctx T γ (body_ctx Φx ++ D) -> set_body_sorts_valid T γ Φx D -> set_env_in T γ D ρ ->
    set_interp_gmod T γ D ρ Φx ms ρo -> gm_prefix_upto Φx x = Some (gm_ext Φ' x E) -> entry_tm E = Some (A0, M0) ->
    gm_fill Φ' = Some σ ->
    (forall b, set_interp T γ D ρ (exp_sub A0 σ) b -> set_mem (select_term γ (set_module_members ms) x) (code_carrier b)) /\
    (entry_kind E = ak_propositional -> set_eq (select_term γ (set_module_members ms) x) empty_set) /\
    (forall n, set_interp T γ D ρ (exp_sub M0 σ) n -> set_eq (select_term γ (set_module_members ms) x) n).
Proof.
  intros * Hn HC Hsv Hρ Hm Hp HE Hf.
  destruct (set_interp_gmod_prefix _ _ _ _ _ Hm _ _ _ Hp) as (ms' & ρ0 & e & Hc0 & Hm0 & He & Hl).
  cbn [select_term]. rewrite Hl.
  destruct (prefix_body_ctx _ _ _ Hn Hp) as (X & HX). rewrite HX, <- List.app_assoc in HC.
  pose proof (set_ctx_app_r T γ _ _ HC) as HC1.
  destruct (set_body_sorts_valid_entry _ _ _ _ _ _ _ _ Hsv Hp HE Hf) as (i & Hsort).
  assert (Hsub : sub_setting T γ (body_ctx Φ' ++ D) ρ0 nil (body_ctx Φ' ++ D) D σ ρ ρ).
  { constructor; [reflexivity | exact (wf_gm_fill _ _ _ _ _ Hc0 Hf) | intros k Hk; cbn in Hk; lia
                 | intros; reflexivity | intros k; exact (set_interp_gmod_fill _ _ _ _ _ Hm0 _ Hf k)]. }
  pose proof (set_env_rel_eq T γ _ _ _ Hρ) as Eρ.
  assert (Hval : forall M v, set_interp T γ (body_ctx Φ' ++ D) ρ0 M v -> forall n, set_interp T γ D ρ (exp_sub M σ) n -> set_eq v n)
    by (intros M v HM n Hn0; exact (set_interp_functional T γ Hfn Hmods _ _ _ _ (set_interp_sub T γ _ _ _ _ HM Hc0 _ _ _ _ _ _ Hsub)
                                      _ _ Eρ Hn0)).
  assert (Hmem : forall A M v FA FM FM', set_exp_eq_with T γ (body_ctx Φ' ++ D) A M M FA FM FM' ->
            set_env_in T γ (body_ctx Φ' ++ D) ρ0 -> set_interp T γ (body_ctx Φ' ++ D) ρ0 M v ->
            forall b, set_interp T γ D ρ (exp_sub A σ) b -> set_mem v (code_carrier b) /\ set_eq (FA ρ0) b).
  { intros * [HA HM _ _ HMm] Hρ0 Hv b Hb.
    pose proof (Hval _ _ (set_denotes_exists _ _ _ _ _ HA _ Hρ0) _ Hb) as Eb. split; [| exact Eb].
    eapply set_mem_eq_r; [exact (code_carrier_resp _ _ Eb) |].
    eapply set_mem_eq_l; [apply set_eq_sym; exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Hρ0 Hv) |]. exact (HMm _ Hρ0). }
  destruct E as [b0 pv r A [M |] | | | pv A M U |]; cbn [entry_tm] in HE; try discriminate; injection HE as <- <-;
    cbn [body_ctx List.app set_ctx set_entry_valid entry_kind] in HC1 |- *; inversion He; subst; cbn [set_entry_value].
  - destruct HC1 as [HC0 (FA & FM & FM' & HAM)].
    pose proof (set_interp_gmod_env_in _ _ _ _ _ Hm0 ltac:(rewrite Hf; discriminate) Hρ HC0) as Hρ0.
    split; [intros b Hb; exact (proj1 (Hmem _ _ _ _ _ _ HAM Hρ0 ltac:(eassumption) _ Hb)) |].
    split; [| intros n Hn0; exact (Hval _ _ ltac:(eassumption) _ Hn0)].
    intros ->. destruct Hsort as (FS & FA' & FA'' & Hs). cbn [abs_kind_sort entry_kind] in Hs.
    destruct HAM as [HA HM _ _ HMm].
    apply (prop_code_carrier_empty (FA ρ0));
      [| eapply set_mem_eq_l; [apply set_eq_sym; exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Hρ0 ltac:(eassumption)) | exact (HMm _ Hρ0)]].
    eapply is_prop_code_resp;
      [apply set_eq_sym; exact (Hval _ _ (set_denotes_exists _ _ _ _ _ HA _ Hρ0) _
                                  (set_denotes_exists _ _ _ _ _ (set_exp_eq_left _ _ _ _ _ _ _ _ _ Hs) _ Hρ)) |].
    exact (set_prop_is_prop_code _ _ _ _ _ _ _ _ Hs Hρ).
  - destruct HC1 as [HC0 [(FA & FM & FM' & HAM) _]].
    pose proof (set_interp_gmod_env_in _ _ _ _ _ Hm0 ltac:(rewrite Hf; discriminate) Hρ HC0) as Hρ0.
    split; [intros b Hb; exact (proj1 (Hmem _ _ _ _ _ _ HAM Hρ0 ltac:(eassumption) _ Hb)) |].
    split; [discriminate | intros n Hn0; exact (Hval _ _ ltac:(eassumption) _ Hn0)].
Qed.

(** ** Members at an Environment *)

(** [set_member_values_at Γ ρ m x R A]: the term member [x] of the module
    [m], read as [R] of the type [A], is of the type at [ρ], its reduct's
    value there, and the empty set when it is a proof. *)
Record set_member_values_at (Γ : ctx) (ρ : set_env) (m : set_module) (x : string) (R : mdesc) (A : exp) : Prop :=
  { (** Of every value of the type *)
    set_member_values_type : forall a, set_interp T γ Γ ρ A a -> set_mem (select_term γ m x) (code_carrier a)
    (** Every value of the reduct *)
  ; set_member_values_reduct : forall N n, mdesc_reduct R = Some N -> set_interp T γ Γ ρ N n -> set_eq (select_term γ m x) n
    (** A proof is the empty set *)
  ; set_member_values_proof : mdesc_kind R = ak_propositional -> set_eq (select_term γ m x) empty_set }.

(** [set_members_values Γ H F]: every term member of [H] that [Θs ⍮ Ξs]
    has is so at every environment, of [F]'s modules. *)
Definition set_members_values (Γ : ctx) (H : modexp) (F : set_env -> set_module) : Prop :=
  forall x R A, set_member_known Θs Ξs Γ H x -> mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A ->
    forall ρ, set_env_in T γ Γ ρ -> set_member_values_at Γ ρ (F ρ) x R A.

Lemma set_members_valid_of_values : forall Γ H F, set_members_values Γ H F -> set_members_valid T γ Θs Ξs Γ H F.
Proof.
  intros * HV x R A FA Hk Hm Ht HFA ρ Hρ. destruct (HV _ _ _ Hk Hm Ht _ Hρ) as [Hty Hred _].
  split; [exact (Hty _ (set_denotes_exists _ _ _ _ _ HFA _ Hρ)) |].
  intros N FN HN HFN. exact (Hred _ _ HN (set_denotes_exists _ _ _ _ _ HFN _ Hρ)).
Qed.

(** [set_members_denote Γ H]: the type and the δ-reduct of every term
    member of [H] that [Θs ⍮ Ξs] has denote. *)
Definition set_members_denote (Γ : ctx) (H : modexp) : Prop :=
  forall x R A, set_member_known Θs Ξs Γ H x -> mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A ->
    (exists FA, set_denotes T γ Γ A FA) /\ forall M, mdesc_reduct R = Some M -> exists FM, set_denotes T γ Γ M FM.

(** ** Denotations Moved Along Fillings and Closed Over Parameters *)

(** The [Π] over a telescope of assumptions into a type denotes. *)
Lemma set_ctx_pi_denotes : forall T1 T2 r A0 FA, all_assumptions T1 -> set_ctx T γ (T1 ++ T2) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ T1 ++ T2 -> set_denotes T γ (T1 ++ T2) A0 FA -> exists F, set_denotes T γ T2 (ctx_pi_at r T1 A0) F.
Proof.
  induction T1 as [| e T1 IH]; intros T2 r A0 FA HT1 HC Hc HA; [exists FA; exact HA |].
  inversion HT1 as [| ? ? (κ & B & ->) HT1']; subst. cbn [ctx_pi_at].
  destruct HC as [HC (FB & HB)].
  pose proof (set_denotes_pi T γ _ κ r B A0 FB FA HC Hc HB HA) as HP.
  exact (IH _ _ _ _ HT1' HC (ctx_decomp_tail Hc) HP).
Qed.

(** The [λ] over a telescope of assumptions of a term denoting past it
    denotes, each partial [λ] typed. *)
Lemma set_ctx_fn_denotes : forall Δ Γ N r B FN, all_assumptions Δ -> set_ctx T γ (Δ ++ Γ) -> ⊢ gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ->
    (forall Δ1 Δ2, Δ = Δ1 ++ Δ2 -> gc_deps ⍮ gc_stack ⍮ Δ2 ++ Γ ⊢ ctx_fn Δ1 N : ctx_pi_at r Δ1 B) ->
    set_denotes T γ (Δ ++ Γ) N FN -> exists F, set_denotes T γ Γ (ctx_fn Δ N) F.
Proof.
  induction Δ as [| e Δ IH]; intros Γ N r B FN HΔ HC Hc Hty HN; [exists FN; exact HN |].
  inversion HΔ as [| ? ? (κ & A & ->) HΔ']; subst. cbn [ctx_fn]. cbn [List.app] in HC, Hc.
  destruct HC as [HC (FA & HA)].
  pose proof (Hty [ce_ass κ A] Δ eq_refl) as Hfn1. cbn [ctx_fn ctx_pi_at] in Hfn1.
  pose proof (set_denotes_fn T γ _ κ r A N A B FA FN Hfn HC Hfn1 Hc HA HN) as Hλ.
  apply (IH _ _ r (a_pi κ r A B) _ HΔ' HC (ctx_decomp_tail Hc) ltac:(intros Δ1 Δ2 ->; exact (Hty (ce_ass κ A :: Δ1) Δ2 eq_refl)) Hλ).
Qed.

Lemma set_gsub_id : forall Γ, ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_gsub_with T γ Γ sb_id Γ (fun ρ => ρ).
Proof.
  intros * Hc. constructor; [apply wf_sub_id; exact Hc | | intros ρ ρ' Hr; exact Hr].
  intros ρ x _. split; cbn; [exact (set_interp_var T γ _ ρ x) | exact (set_interp_me_var T γ _ ρ x)].
Qed.

(** A substitution extended by a definition's body moved along it. *)
Lemma set_gsub_extend_def : forall Γ σ Δ Fσ A M FM r, set_moves_with T γ nil Δ Γ σ Fσ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend σ (se_exp (exp_sub M σ)) : ce_def A M :: Δ -> set_denotes T γ Δ M FM ->
    set_gsub_with T γ Γ (sb_extend σ (se_exp (exp_sub M σ))) (ce_def A M :: Δ)
      (fun ρ => set_env_extend (Fσ ρ) (set_entry_term r (FM (Fσ ρ)))).
Proof.
  intros * Hs Hσ HM. pose proof Hs as [Hg HΓ _ _ _].
  pose proof (set_denotes_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs HM) as HMσ. cbn [tele_sub List.app List.length sb_qn] in HMσ.
  destruct (set_env_rel_per _ _ _ HΓ) as [Hsym Htrans]. constructor; [exact Hσ | |].
  - intros ρ [| x] Hρ; [split; cbn; [exact (set_denotes_exists _ _ _ _ _ HMσ _ Hρ) | constructor] |].
    exact (set_gsub_agrees _ _ _ _ _ _ Hg _ x Hρ).
  - intros ρ ρ' Hr.
    assert (Hl : set_env_in T γ Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
    assert (Hr' : set_env_in T γ Γ ρ') by (eapply Htrans; [apply Hsym; exact Hr | exact Hr]).
    pose proof (set_gsub_rel _ _ _ _ _ _ Hg _ _ Hr) as HrΔ.
    split; [exact HrΔ |]. cbn [set_entry_rel].
    exists r, (FM (Fσ ρ)), (FM (Fσ ρ')), (FM (Fσ ρ)).
    constructor; [reflexivity | reflexivity | exact (set_denotes_exists _ _ _ _ _ HM _ (set_gsub_rel _ _ _ _ _ _ Hg _ _ Hl))
                 | apply set_eq_refl |].
    exact (set_denotes_unique _ _ _ _ _ HM _ _ _ HrΔ (set_denotes_exists _ _ _ _ _ HM _ (set_gsub_rel _ _ _ _ _ _ Hg _ _ Hr'))).
Qed.

(** A substitution extended by a module slot's unit moved along it. *)
Lemma set_gsub_extend_mod : forall Γ σ Δ Fσ U FU, set_moves_with T γ nil Δ Γ σ Fσ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend σ (se_mod (me_lit (gunit_sub U σ))) : ce_mod U :: Δ ->
    set_modexp_denotes T γ Δ (me_lit U) FU ->
    set_gsub_with T γ Γ (sb_extend σ (se_mod (me_lit (gunit_sub U σ)))) (ce_mod U :: Δ)
      (fun ρ => set_env_extend (Fσ ρ) (set_entry_module (FU (Fσ ρ)))).
Proof.
  intros * Hs Hσ HU. pose proof Hs as [Hg HΓ _ _ _].
  pose proof (set_modexp_denotes_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs HU) as HUσ. cbn [tele_sub List.app List.length sb_qn] in HUσ.
  destruct (set_env_rel_per _ _ _ HΓ) as [Hsym Htrans]. constructor; [exact Hσ | |].
  - intros ρ [| x] Hρ; [split; cbn; [constructor | exact (set_modexp_denotes_exists _ _ _ _ _ HUσ _ Hρ)] |].
    exact (set_gsub_agrees _ _ _ _ _ _ Hg _ x Hρ).
  - intros ρ ρ' Hr.
    assert (Hl : set_env_in T γ Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
    assert (Hr' : set_env_in T γ Γ ρ') by (eapply Htrans; [apply Hsym; exact Hr | exact Hr]).
    pose proof (set_gsub_rel _ _ _ _ _ _ Hg _ _ Hr) as HrΔ. pose proof (set_gsub_rel _ _ _ _ _ _ Hg _ _ Hl) as HlΔ.
    pose proof (set_modexp_denotes_exists _ _ _ _ _ HU _ HlΔ) as Hn.
    split; [exact HrΔ |]. cbn [set_entry_rel].
    exists (FU (Fσ ρ)), (FU (Fσ ρ')), (FU (Fσ ρ)).
    constructor; [reflexivity | reflexivity | apply set_interp_me_lit_iff; exact Hn
                 | exact (set_modexp_denotes_unique _ _ _ _ _ HU _ _ _ HlΔ Hn) |].
    exact (set_modexp_denotes_unique _ _ _ _ _ HU _ _ _ HrΔ (set_modexp_denotes_exists _ _ _ _ _ HU _ (set_gsub_rel _ _ _ _ _ _ Hg _ _ Hr'))).
Qed.

(** A substitution extended by a definition with a module part, both
    moved along it. *)
Lemma set_gsub_extend_dm : forall Γ σ Δ Fσ A M U FM FU, set_moves_with T γ nil Δ Γ σ Fσ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend σ (se_dm (exp_sub M σ) (me_lit (gunit_sub U σ))) : ce_dm A M U :: Δ ->
    set_denotes T γ Δ M FM -> set_modexp_denotes T γ Δ (me_lit U) FU ->
    set_gsub_with T γ Γ (sb_extend σ (se_dm (exp_sub M σ) (me_lit (gunit_sub U σ)))) (ce_dm A M U :: Δ)
      (fun ρ => set_env_extend (Fσ ρ) (set_entry_both (FM (Fσ ρ)) (FU (Fσ ρ)))).
Proof.
  intros * Hs Hσ HM HU. pose proof Hs as [Hg HΓ _ _ _].
  pose proof (set_denotes_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs HM) as HMσ. cbn [tele_sub List.app List.length sb_qn] in HMσ.
  pose proof (set_modexp_denotes_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs HU) as HUσ. cbn [tele_sub List.app List.length sb_qn] in HUσ.
  destruct (set_env_rel_per _ _ _ HΓ) as [Hsym Htrans]. constructor; [exact Hσ | |].
  - intros ρ [| x] Hρ; [split; cbn; [exact (set_denotes_exists _ _ _ _ _ HMσ _ Hρ) | exact (set_modexp_denotes_exists _ _ _ _ _ HUσ _ Hρ)] |].
    exact (set_gsub_agrees _ _ _ _ _ _ Hg _ x Hρ).
  - intros ρ ρ' Hr.
    assert (Hl : set_env_in T γ Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
    assert (Hr' : set_env_in T γ Γ ρ') by (eapply Htrans; [apply Hsym; exact Hr | exact Hr]).
    pose proof (set_gsub_rel _ _ _ _ _ _ Hg _ _ Hr) as HrΔ. pose proof (set_gsub_rel _ _ _ _ _ _ Hg _ _ Hl) as HlΔ.
    pose proof (set_gsub_rel _ _ _ _ _ _ Hg _ _ Hr') as Hr'Δ.
    pose proof (set_modexp_denotes_exists _ _ _ _ _ HU _ HlΔ) as Hn.
    split; [exact HrΔ |]. cbn [set_entry_rel].
    exists (FM (Fσ ρ)), (FM (Fσ ρ')), (FM (Fσ ρ)), (FU (Fσ ρ)), (FU (Fσ ρ')), (FU (Fσ ρ)).
    constructor; [reflexivity | reflexivity | exact (set_denotes_exists _ _ _ _ _ HM _ HlΔ) | apply set_interp_me_lit_iff; exact Hn
                 | apply set_eq_refl
                 | exact (set_denotes_unique _ _ _ _ _ HM _ _ _ HrΔ (set_denotes_exists _ _ _ _ _ HM _ Hr'Δ))
                 | exact (set_modexp_denotes_unique _ _ _ _ _ HU _ _ _ HlΔ Hn)
                 | exact (set_modexp_denotes_unique _ _ _ _ _ HU _ _ _ HrΔ (set_modexp_denotes_exists _ _ _ _ _ HU _ Hr'Δ))].
Qed.

(** A body of definitions and modules, filled in, moves its context's
    terms to the context below it. *)
Lemma set_gsub_fill : forall Φ D σ, gm_fill Φ = Some σ -> set_ctx T γ D -> set_ctx T γ (body_ctx Φ ++ D) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx Φ ++ D -> exists Fσ, set_moves_with T γ nil (body_ctx Φ ++ D) D σ Fσ.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros D σ Hf HD HC Hc; cbn in Hf.
  - injection Hf as <-. exists (fun ρ => ρ). constructor; [exact (set_gsub_id _ Hc) | exact HD | exact HC | exact HD | exact Hc].
  - pose proof (wf_gm_fill _ _ _ _ _ Hc Hf) as Hσw.
    destruct E as [b pv r A [M |] | pv U | | pv A M U |]; try discriminate;
      destruct (gm_fill Φ) as [σ0 |] eqn:Hf0; cbn in Hf; try discriminate; injection Hf as <-;
      cbn [body_ctx List.app set_ctx] in HC, Hc |- *; pose proof HC as [HC0 Hce];
      destruct (IH _ _ eq_refl HD HC0 (ctx_decomp_tail Hc)) as (Fσ & Hs).
    + destruct Hce as (FA & FM & FM' & [_ HM _ _ _]).
      exists (fun ρ => set_env_extend (Fσ ρ) (set_entry_term r (FM (Fσ ρ)))).
      constructor; [exact (set_gsub_extend_def _ _ _ _ _ _ _ r Hs Hσw HM) | exact HD | exact HC | exact HD | exact Hc].
    + destruct Hce as (FU & FU' & [HU _ _]).
      exists (fun ρ => set_env_extend (Fσ ρ) (set_entry_module (FU (Fσ ρ)))).
      constructor; [exact (set_gsub_extend_mod _ _ _ _ _ _ Hs Hσw HU) | exact HD | exact HC | exact HD | exact Hc].
    + destruct Hce as [(FA & FM & FM' & [_ HM _ _ _]) (FU & FU' & [HU _ _])].
      exists (fun ρ => set_env_extend (Fσ ρ) (set_entry_both (FM (Fσ ρ)) (FU (Fσ ρ)))).
      constructor; [exact (set_gsub_extend_dm _ _ _ _ _ _ _ _ _ Hs Hσw HM HU) | exact HD | exact HC | exact HD | exact Hc].
  - discriminate.
Qed.

(** ** Members of Bodies *)

(** Whether a body's member is a proof is read at its last entry so named. *)
Lemma body_member_lookup_prefix : forall κs Φ x Φ' E, gm_noopen Φ -> gm_prefix_upto Φ x = Some (gm_ext Φ' x E) ->
    body_member_lookup γ κs Φ nil x = Some (gentry_is_proof E).
Proof.
  intros κs Φ. revert κs. induction Φ as [| Φ IH y E0 | Φ IH H its Φg _]; intros κs x Φ' E Hn Hp;
    cbn [gm_prefix_upto gm_noopen body_member_lookup chain_key] in Hp, Hn |- *; [discriminate | | contradiction].
  destruct (String.eqb_spec x y) as [-> | _]; [injection Hp as <- <-; reflexivity | exact (IH _ _ _ _ Hn Hp)].
Qed.

Lemma gentry_is_proof_tm : forall E A M, entry_tm E = Some (A, M) -> gentry_is_proof E = is_proof_kind (entry_kind E).
Proof. intros [] A M H; cbn in H |- *; try discriminate; reflexivity. Qed.

(** The [λ] over the inner part of a telescope of assumptions of a term,
    at a type of its kind's sort, is of the [Π] there. *)
Lemma ctx_fn_split_typed : forall r Δ Γ A M i, ⊢ gc_deps ⍮ gc_stack ⍮ Δ ++ Γ -> all_assumptions Δ ->
    (r = ak_level -> level_sorted_parameters Δ) ->
    gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ⊢ A : abs_kind_sort r (a_typ i) -> gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ⊢ M : A ->
    forall L1 L2, List.rev Δ = L1 ++ L2 ->
    gc_deps ⍮ gc_stack ⍮ List.rev L1 ++ Γ ⊢ ctx_fn (List.rev L2) M : ctx_pi_at r (List.rev L2) A.
Proof.
  intros * Hc HΔ Hl HA HM L1 L2 E.
  assert (EΔ : Δ = List.rev L2 ++ List.rev L1) by (rewrite <- List.rev_app_distr, <- E, List.rev_involutive; reflexivity).
  subst Δ. rewrite <- List.app_assoc in Hc, HA, HM.
  destruct (proj1 (List.Forall_app _ _ _) HΔ) as [HΔ2 _].
  destruct r; [apply (ctx_fn_at_wf _ _ _ _ _ _ _ i) | apply (ctx_fn_at_wf _ _ _ _ _ _ _ i) | apply ctx_fn_level_wf];
    try discriminate; try assumption.
  intros Δ1 κ B Δ2 Eq. apply (Hl eq_refl Δ1 κ B (Δ2 ++ List.rev L1)). rewrite Eq, <- List.app_assoc. reflexivity.
Qed.

(** A term member of a body over the parameters [Δ] is a proof as its
    entry's tag says, and is of its type, its reduct's value, at every
    environment: the closure over [Δ] of its definition filled in. *)
Lemma set_body_members : forall Γ Δ Φ Φx, set_body_ok T γ Γ Δ Φ Φx ->
    (forall κs x R A, mdenote gc_deps gc_stack Γ (me_mem (me_lit (gu_open Δ Φ)) x) R -> mdesc_type R = Some A ->
       modexp_member_proofs γ κs (me_lit (gu_open Δ Φ)) nil x = is_proof_kind (mdesc_kind R)) /\
    (forall F, set_modexp_denotes T γ Γ (me_lit (gu_open Δ Φ)) F -> set_members_values Γ (me_lit (gu_open Δ Φ)) F).
Proof.
  intros * Hok. destruct Hok as [Hw Hx HΔ _ HΓ HC Hsv _ _ _ _].
  pose proof (body_xp_result_noopen _ _ _ _ _ Hx) as Hno. pose proof (gm_noopen_nopens _ Hno) as Hn.
  pose proof (body_xp_expand _ _ _ _ _ Hx) as Hxe.
  assert (Hpf : forall κs x R A, mdenote gc_deps gc_stack Γ (me_mem (me_lit (gu_open Δ Φ)) x) R -> mdesc_type R = Some A ->
             modexp_member_proofs γ κs (me_lit (gu_open Δ Φ)) nil x = is_proof_kind (mdesc_kind R)).
  { intros κs x R A Hm Ht.
    destruct (body_mem_desc _ _ Hgw _ _ _ _ _ _ _ Hx Hm Ht) as (Φ' & E & A0 & M0 & σ & Hp & HEt & Hf & HA & Hred & Hk).
    cbn [modexp_member_proofs]. rewrite unit_member_proofs_tele_out. cbn [moddef_member_proofs].
    rewrite <- (proj2 (body_member_proofs_expand γ Φ _)), <- Hxe, (body_member_lookup_prefix _ _ _ _ _ Hno Hp), Hk.
    exact (gentry_is_proof_tm _ _ _ HEt). }
  split; [exact Hpf |].
  intros F HF x R A _ Hm Ht ρ Hρ.
  destruct (body_mem_desc _ _ Hgw _ _ _ _ _ _ _ Hx Hm Ht) as (Φ' & E & A0 & M0 & σ & Hp & HEt & Hf & HA & Hred & Hk).
  subst A.
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) as HFρ. apply set_interp_me_lit_iff in HFρ.
  inversion HFρ as [? ? ? ? P m HP HL]; subst.
  assert (HPx : P nil x = is_proof_kind (entry_kind E)) by (rewrite HP, <- Hk; exact (Hpf _ _ _ _ Hm Ht)).
  (* the body's typing: its definitions filled in are typed, at their kinds' sorts *)
  pose proof (gctx_valid_syn _ _ Hgw) as Hvs.
  assert (HmK : mdenote gc_deps gc_stack Γ (me_lit (gu_open Δ Φ)) (mdesc_open Δ Φ (gm_expand Φ)))
    by (constructor; econstructor; [exact Hx | reflexivity]).
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ Hw Hvs) as (_ & HR & _).
  pose proof (HR _ HmK) as Hd. inversion Hd as [| ? ? ? ? ? Hwx _ _ _ _ _ _ _ Hsorts _ | |]; subst.
  destruct (Hsorts _ _ _ _ _ _ Hp HEt Hf) as [iA HAσ].
  pose proof (ctx_app_wf_tail _ _ (body_ctx (gm_expand Φ)) (Δ ++ Γ) Hwx) as Hc.
  destruct (prefix_body_ctx _ _ _ Hn Hp) as (X & HX). rewrite HX, <- List.app_assoc in Hwx.
  pose proof (ctx_app_wf_tail _ _ X _ Hwx) as Hc1.
  assert (HM0 : ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx Φ' ++ Δ ++ Γ /\ gc_deps ⍮ gc_stack ⍮ body_ctx Φ' ++ Δ ++ Γ ⊢ M0 : A0).
  { destruct E as [b0 pv r A [M |] | | | pv A M U |]; cbn [entry_tm] in HEt; try discriminate; injection HEt as <- <-;
      cbn [body_ctx List.app] in Hc1.
    - destruct (ctx_decomp_def Hc1) as (H0 & _ & H1). exact (conj H0 H1).
    - destruct (ctx_decomp_dm Hc1) as (H0 & _ & H1 & _). exact (conj H0 H1). }
  destruct HM0 as [Hc0 HM0].
  assert (HMσ : gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ⊢ exp_sub M0 σ : exp_sub A0 σ)
    by (eapply sub_preserves_exp; [exact HM0 | exact (wf_gm_fill _ _ _ _ _ Hc0 Hf)]).
  assert (Hlv : entry_kind E = ak_level -> level_sorted_parameters Δ).
  { intros Ek Δ1 κ B Δ2 Eq. pose proof (member_pi_kinds _ _ Hgw _ _ _ _ _ _ _ Hw Hm Hk Ht HΔ Δ1 κ B Δ2 Eq) as Hpk.
    rewrite Ek in Hpk. inversion Hpk; reflexivity. }
  (* the closure over the parameters, of the body's member at each value *)
  destruct (set_unit_walk_type (List.rev Δ) Γ ρ P _ _ (entry_kind E) (exp_sub A0 σ) x (List.Forall_rev HΔ) Hρ HL HPx)
    as [Hw0 Hw1]; rewrite ?List.rev_involutive.
  { intros ρ' mD b Hρ' HmD Hb. inversion HmD; subst.
    exact (proj1 (set_body_member_base _ _ _ _ _ _ _ _ _ _ _ Hn HC Hsv Hρ' ltac:(eassumption) Hp HEt Hf) _ Hb). }
  { intros Ek ρ' mD Hρ' HmD. inversion HmD; subst.
    exact (proj1 (proj2 (set_body_member_base _ _ _ _ _ _ _ _ _ _ _ Hn HC Hsv Hρ' ltac:(eassumption) Hp HEt Hf)) Ek). }
  rewrite List.rev_involutive in Hw1.
  constructor; [exact Hw1 | | rewrite Hk; exact Hw0].
  - intros N n HN Hn0. rewrite Hred in HN; injection HN as <-. rewrite <- (List.rev_involutive Δ) in Hn0.
    apply (set_unit_walk_reduct (List.rev Δ) Γ ρ P _ _ (entry_kind E) (exp_sub A0 σ) (exp_sub M0 σ) x (List.Forall_rev HΔ) Hρ HL HPx);
      [ exact (ctx_fn_split_typed _ _ _ _ _ _ Hc HΔ Hlv HAσ HMσ) | | exact Hn0 ].
    intros ρ' mD n1 Hρ' HmD Hn1. rewrite List.rev_involutive in Hρ', HmD, Hn1. inversion HmD; subst.
    exact (proj2 (proj2 (set_body_member_base _ _ _ _ _ _ _ _ _ _ _ Hn HC Hsv Hρ' ltac:(eassumption) Hp HEt Hf)) _ Hn1).
Qed.

(** The type and the reduct of a term member of a body denote: the [Π]
    and the [λ] over the parameters of its definition's, moved along the
    body before it. *)
Lemma set_body_members_denote : forall Γ Δ Φ Φx, set_body_ok T γ Γ Δ Φ Φx -> set_members_denote Γ (me_lit (gu_open Δ Φ)).
Proof.
  intros * Hok x R A _ Hm Ht. destruct Hok as [Hw Hx HΔ _ HΓ HC _ _ _ _ _].
  pose proof (body_xp_result_noopen _ _ _ _ _ Hx) as Hno. pose proof (gm_noopen_nopens _ Hno) as Hn.
  destruct (body_mem_desc _ _ Hgw _ _ _ _ _ _ _ Hx Hm Ht) as (Φ' & E & A0 & M0 & σ & Hp & HEt & Hf & HA & Hred & Hk).
  pose proof (body_xp_expand _ _ _ _ _ Hx) as Hxe. subst Φx.
  (* the body's typing, as for its members' values *)
  pose proof (gctx_valid_syn _ _ Hgw) as Hvs.
  assert (HmK : mdenote gc_deps gc_stack Γ (me_lit (gu_open Δ Φ)) (mdesc_open Δ Φ (gm_expand Φ)))
    by (constructor; econstructor; [exact Hx | reflexivity]).
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ Hw Hvs) as (_ & HR & _).
  pose proof (HR _ HmK) as Hd. inversion Hd as [| ? ? ? ? ? Hwx _ _ _ _ _ _ _ Hsorts _ | |]; subst.
  destruct (Hsorts _ _ _ _ _ _ Hp HEt Hf) as [iA HAσ].
  pose proof (ctx_app_wf_tail _ _ (body_ctx (gm_expand Φ)) (Δ ++ Γ) Hwx) as Hc.
  destruct (prefix_body_ctx _ _ _ Hn Hp) as (X & HX). rewrite HX, <- List.app_assoc in Hwx, HC.
  pose proof (ctx_app_wf_tail _ _ X _ Hwx) as Hc1. pose proof (set_ctx_app_r T γ _ _ HC) as HC1.
  (* the definition denotes in the context the body before it makes *)
  assert (HM0 : ⊢ gc_deps ⍮ gc_stack ⍮ body_ctx Φ' ++ Δ ++ Γ /\ set_ctx T γ (body_ctx Φ' ++ Δ ++ Γ) /\
                gc_deps ⍮ gc_stack ⍮ body_ctx Φ' ++ Δ ++ Γ ⊢ M0 : A0 /\
                (exists FA0, set_denotes T γ (body_ctx Φ' ++ Δ ++ Γ) A0 FA0) /\
                exists FM0, set_denotes T γ (body_ctx Φ' ++ Δ ++ Γ) M0 FM0).
  { destruct E as [b0 pv r A1 [M1 |] | | | pv A1 M1 U |]; cbn [entry_tm] in HEt; try discriminate; injection HEt as <- <-;
      cbn [body_ctx List.app set_ctx set_entry_valid] in Hc1, HC1.
    - destruct (ctx_decomp_def Hc1) as (H0 & _ & H1). destruct HC1 as [HC0 (FA & FM & FM' & [HFA HFM _ _ _])].
      exact (conj H0 (conj HC0 (conj H1 (conj (ex_intro _ FA HFA) (ex_intro _ FM HFM))))).
    - destruct (ctx_decomp_dm Hc1) as (H0 & _ & H1 & _). destruct HC1 as [HC0 [(FA & FM & FM' & [HFA HFM _ _ _]) _]].
      exact (conj H0 (conj HC0 (conj H1 (conj (ex_intro _ FA HFA) (ex_intro _ FM HFM))))). }
  destruct HM0 as (Hc0 & HC0 & HM0 & (FA0 & HFA0) & FM0 & HFM0).
  pose proof (set_ctx_app_r T γ _ _ HC0) as HCΔ.
  destruct (set_gsub_fill _ _ _ Hf HCΔ HC0 Hc0) as (Fσ & Hs).
  split.
  { (* the type: the [Π] over the parameters *)
    pose proof (set_denotes_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs HFA0) as HAσd. cbn [tele_sub List.app List.length sb_qn] in HAσd.
    exact (set_ctx_pi_denotes _ _ _ _ _ HΔ HCΔ Hc HAσd). }
  intros M HM. rewrite Hred in HM. injection HM as <-.
  pose proof (set_denotes_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs HFM0) as HMσ. cbn [tele_sub List.app List.length sb_qn] in HMσ.
  assert (HMσw : gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ⊢ exp_sub M0 σ : exp_sub A0 σ)
    by (eapply sub_preserves_exp; [exact HM0 | exact (wf_gm_fill _ _ _ _ _ Hc0 Hf)]).
  assert (Hlv : entry_kind E = ak_level -> level_sorted_parameters Δ).
  { intros Ek Δ1 κ B Δ2 Eq. pose proof (member_pi_kinds _ _ Hgw _ _ _ _ _ _ _ Hw Hm Hk Ht HΔ Δ1 κ B Δ2 Eq) as Hpk.
    rewrite Ek in Hpk. inversion Hpk; reflexivity. }
  assert (Hty : forall Δ1 Δ2, Δ = Δ1 ++ Δ2 ->
            gc_deps ⍮ gc_stack ⍮ Δ2 ++ Γ ⊢ ctx_fn Δ1 (exp_sub M0 σ) : ctx_pi_at (entry_kind E) Δ1 (exp_sub A0 σ)).
  { intros Δ1 Δ2 ->. pose proof (ctx_fn_split_typed _ _ _ _ _ _ Hc HΔ Hlv HAσ HMσw (List.rev Δ2) (List.rev Δ1)
                                   ltac:(rewrite List.rev_app_distr; reflexivity)) as Hty.
    rewrite !List.rev_involutive in Hty. exact Hty. }
  exact (set_ctx_fn_denotes _ _ _ _ _ _ HΔ HCΔ Hc Hty HMσ).
Qed.

(** The members of equal modules agree. *)
Lemma set_member_values_at_resp : forall Γ ρ m m' x R A, set_module_eq γ m m' ->
    set_member_values_at Γ ρ m x R A -> set_member_values_at Γ ρ m' x R A.
Proof.
  intros * Em [Hty Hred Hpr]. pose proof (select_term_resp γ _ _ Em x) as Es.
  constructor.
  - intros a Ha. exact (set_mem_eq_l _ _ _ Es (Hty _ Ha)).
  - intros N n HN Hn. exact (set_eq_trans _ _ _ (set_eq_sym _ _ Es) (Hred _ _ HN Hn)).
  - intros Ek. exact (set_eq_trans _ _ _ (set_eq_sym _ _ Es) (Hpr Ek)).
Qed.

(** [set_members_proofs Γ H]: whether a term member of [H] that
    [Θs ⍮ Ξs] has is a proof is read off the syntax as its kind says, at
    slots coherent with [Γ]. *)
Definition set_members_proofs (Γ : ctx) (H : modexp) : Prop :=
  forall κs, set_slots_coherent γ Γ κs -> forall x R A, set_member_known Θs Ξs Γ H x ->
    mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A ->
    modexp_member_proofs γ κs H nil x = is_proof_kind (mdesc_kind R).

(** [set_members_all Γ H]: so, every term member of [H] that [Θs ⍮ Ξs]
    has is so at every environment, of every denotation of [H], and its
    reduct denotes. *)
Record set_members_all (Γ : ctx) (H : modexp) : Prop :=
  { (** Whether each is a proof is as its kind says *)
    set_members_all_proofs : set_members_proofs Γ H
    (** Each is of its type and its reduct's value, at every denotation
        of [H] *)
  ; set_members_all_values : forall F, set_modexp_denotes T γ Γ H F -> set_members_values Γ H F
    (** Each one's type and reduct denote *)
  ; set_members_all_denote : set_members_denote Γ H }.

(** ** Members of Aliases *)

(** Slots pushed past assumptions are coherent. *)
Lemma set_slots_coherent_tele_out : forall Δ Γ κs, all_assumptions Δ -> set_slots_coherent γ Γ κs ->
    set_slots_coherent γ (Δ ++ Γ) (tele_out_proofs γ κs (List.rev Δ)).
Proof.
  induction Δ as [| e Δ IH]; intros Γ κs HΔ Hκ; [exact Hκ |].
  inversion HΔ as [| ? ? (κ & A & ->) HΔ']; subst. cbn [List.rev]. rewrite tele_out_proofs_app. cbn [tele_out_proofs List.app].
  split; [| intros U HU; discriminate].
  apply (set_slots_coherent_resp γ _ _ _ ltac:(intros s ys x; reflexivity) (IH _ _ HΔ' Hκ)).
Qed.

(** A member a context has of an alias's module part is one it has of its
    target's: the alias's module part is its target's abstracted over the
    alias's parameters ([udenote_alias]), which keeps the entries and,
    for a filed module, the body. *)
Lemma set_member_known_alias : forall Γ Δ E x, set_member_known Θs Ξs Γ (me_lit (gu_mk Δ (md_alias E))) x ->
    set_member_known Θs Ξs (Δ ++ Γ) E x.
Proof.
  intros * Hk RE REm HmE HmodE.
  pose proof (mdesc_mod_is_mod _ _ HmodE) as Him.
  assert (HmA : mdenote gc_deps gc_stack Γ (me_lit (gu_mk Δ (md_alias E))) (mdesc_up Δ REm))
    by (constructor; econstructor; eassumption).
  assert (HmodA : mdesc_mod (mdesc_up Δ REm) = Some (mdesc_up Δ REm))
    by (destruct REm; cbn in Him |- *; first [contradiction | reflexivity]).
  destruct (Hk _ _ HmA HmodA) as (Rm1 & Hg & Hs).
  destruct REm as [| Δ' Φ Φx | Θ' p T0 Φ Ns |]; cbn in Him; try contradiction; cbn [mdesc_up] in Hg.
  - (* an open part is its own growth, with the same entries *)
    inversion Hg; subst. exists (mdesc_open Δ' Φ Φx). split; [apply mdesc_grows_same; reflexivity |].
    inversion Hs as [? ? e He | |]; subst.
    destruct (mdesc_entry (mdesc_open Δ' Φ Φx) x) eqn:He'; [eapply set_member_seen_entry; exact He' |].
    exfalso. cbn [mdesc_entry] in He, He'.
    destruct (gm_prefix_upto Φx x) as [[| ? ? E0 | ? ? ? ?] |]; try discriminate.
    destruct E0; repeat match goal with o : option _ |- _ => destruct o end;
      repeat match goal with b : bool |- _ => destruct b end; congruence.
  - (* a closed part grew from the same module's smaller body *)
    inversion Hg as [| ? ? Φ1 ? ? Hl1 Hl2 |]; subst; [cbn in *; discriminate |].
    exists (mdesc_closed Θ' p T0 Φ1 Ns). split; [apply mdesc_grows_closed; assumption |].
    inversion Hs as [? ? e He | ? ? ? ? ? ? ? Hst | ? ? ? ? ? ? ? ? Hfr]; subst.
    + destruct (mdesc_entry (mdesc_closed Θ' p T0 Φ1 Ns) x) eqn:He'; [eapply set_member_seen_entry; exact He' |].
      exfalso. cbn [mdesc_entry] in He, He'. destruct (gm_prefix_upto Φ1 x) as [[| ? ? ? | ? ? ? ?] |]; discriminate.
    + eapply set_member_seen_stored. exact Hst.
    + eapply set_member_seen_frame. exact Hfr.
Qed.

(** A term member of an alias over the parameters [Δ] is its target's
    over them: a proof as the target's is, and of its type, its reduct's
    value, at every environment.  When the target's module part is a
    filed module read bare and its member has no reduct, the alias's
    reduct is the member read by name ([Hbare]). *)
Lemma set_alias_members : forall Γ Δ E, set_alias_ok T γ Γ Δ E -> gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ⊢ᵐ E ≈ E ->
    (forall κs, set_slots_coherent γ (Δ ++ Γ) κs -> forall x R A, set_member_known Θs Ξs (Δ ++ Γ) E x ->
       mdenote gc_deps gc_stack (Δ ++ Γ) (me_mem E x) R ->
       mdesc_type R = Some A -> modexp_member_proofs γ κs E nil x = is_proof_kind (mdesc_kind R)) ->
    (forall FE, set_modexp_denotes T γ (Δ ++ Γ) E FE -> set_members_values (Δ ++ Γ) E FE) ->
    (forall x RE p T0 Φ0 r A0, mdenote gc_deps gc_stack (Δ ++ Γ) E RE -> mdesc_mod RE = Some (mdesc_closed nil p T0 Φ0 nil) ->
       mdenote gc_deps gc_stack (Δ ++ Γ) (me_mem E x) (mdesc_term r A0 None) ->
       gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ⊢ a_mem (qname_mod p) x : A0 /\
       forall FE, set_modexp_denotes T γ (Δ ++ Γ) E FE -> forall ρ', set_env_in T γ (Δ ++ Γ) ρ' ->
         forall m, set_interp_modexp T γ (Δ ++ Γ) ρ' (qname_mod p) m -> set_module_eq γ (FE ρ') m) ->
    (forall κs, set_slots_coherent γ Γ κs -> forall x R A, set_member_known Θs Ξs Γ (me_lit (gu_mk Δ (md_alias E))) x ->
       mdenote gc_deps gc_stack Γ (me_mem (me_lit (gu_mk Δ (md_alias E))) x) R ->
       mdesc_type R = Some A -> modexp_member_proofs γ κs (me_lit (gu_mk Δ (md_alias E))) nil x = is_proof_kind (mdesc_kind R)) /\
    (forall F, set_modexp_denotes T γ Γ (me_lit (gu_mk Δ (md_alias E))) F -> set_members_values Γ (me_lit (gu_mk Δ (md_alias E))) F).
Proof.
  intros * Hok HwE IHp IHv Hbare. destruct Hok as [Hw HΔ _ HΓ HΔΓ _ (FE & FE' & [HFE _ _])].
  pose proof (presup_modexp_eq_ctx HwE) as HcΔΓ.
  (* the target's member, or the filed member read by name *)
  assert (Hdesc : forall x R A, mdenote gc_deps gc_stack Γ (me_mem (me_lit (gu_mk Δ (md_alias E))) x) R -> mdesc_type R = Some A ->
            exists R' A', mdenote gc_deps gc_stack (Δ ++ Γ) (me_mem E x) R' /\ mdesc_type R' = Some A' /\
              mdesc_kind R = mdesc_kind R' /\ A = ctx_pi_at (mdesc_kind R') Δ A' /\
              ((mdesc_reduct R = option_map (ctx_fn Δ) (mdesc_reduct R')) \/
               (exists RE p T0 Φ0, mdenote gc_deps gc_stack (Δ ++ Γ) E RE /\ mdesc_mod RE = Some (mdesc_closed nil p T0 Φ0 nil) /\
                  R' = mdesc_term (mdesc_kind R') A' None /\ mdesc_reduct R = Some (ctx_fn Δ (a_mem (qname_mod p) x))))).
  { intros x R A Hm Ht.
    destruct (alias_mem_desc _ _ Hgw _ _ _ _ _ _ HcΔΓ Hm Ht) as (R' & Hm' & [-> | (r & A0 & RE & p & T0 & Φ0 & -> & HmE & HmdE & ->)]).
    - destruct (mdesc_type_up_inv _ _ _ Ht) as (A' & Ht' & ->).
      exists R', A'. repeat split; [exact Hm' | exact Ht' | apply mdesc_kind_up | left; apply mdesc_reduct_up].
    - cbn in Ht |- *. injection Ht as <-. exists (mdesc_term r A0 None), A0.
      repeat split; [exact Hm' | right; exists RE, p, T0, Φ0; repeat split; assumption]. }
  assert (Hpf : forall κs, set_slots_coherent γ Γ κs -> forall x R A, set_member_known Θs Ξs Γ (me_lit (gu_mk Δ (md_alias E))) x ->
             mdenote gc_deps gc_stack Γ (me_mem (me_lit (gu_mk Δ (md_alias E))) x) R -> mdesc_type R = Some A ->
             modexp_member_proofs γ κs (me_lit (gu_mk Δ (md_alias E))) nil x = is_proof_kind (mdesc_kind R)).
  { intros κs Hκ x R A Hkn Hm Ht. destruct (Hdesc _ _ _ Hm Ht) as (R' & A' & Hm' & Ht' & Hk & _).
    cbn [modexp_member_proofs]. rewrite unit_member_proofs_tele_out. cbn [moddef_member_proofs]. rewrite Hk.
    exact (IHp _ (set_slots_coherent_tele_out _ _ _ HΔ Hκ) _ _ _ (set_member_known_alias _ _ _ _ Hkn) Hm' Ht'). }
  split; [exact Hpf |].
  intros F HF x R A Hkn Hm Ht ρ Hρ.
  destruct (Hdesc _ _ _ Hm Ht) as (R' & A' & Hm' & Ht' & Hk & -> & Hred').
  pose proof (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) as HFρ. apply set_interp_me_lit_iff in HFρ.
  inversion HFρ as [? ? ? ? P m HP HL]; subst.
  assert (HPx : P nil x = is_proof_kind (mdesc_kind R'))
    by (rewrite HP, <- Hk; exact (Hpf _ (set_slots_coherent_env T γ _ _ Hρ) _ _ _ Hkn Hm Ht)).
  (* the target's member at each environment past the parameters *)
  assert (HE : forall ρ' mD, set_env_in T γ (Δ ++ Γ) ρ' -> set_interp_moddef T γ (Δ ++ Γ) ρ' (md_alias E) mD ->
            set_eq (select_term γ mD x) (select_term γ (FE ρ') x) /\ set_member_values_at (Δ ++ Γ) ρ' (FE ρ') x R' A').
  { intros ρ' mD Hρ' HmD. inversion HmD; subst. split.
    - apply select_term_resp. exact (set_modexp_denotes_unique _ _ _ _ _ HFE _ _ _ Hρ' ltac:(eassumption)).
    - exact (IHv _ HFE _ _ _ (set_member_known_alias _ _ _ _ Hkn) Hm' Ht' _ Hρ'). }
  destruct (set_unit_walk_type (List.rev Δ) Γ ρ P _ _ (mdesc_kind R') A' x (List.Forall_rev HΔ) Hρ HL HPx)
    as [Hw0 Hw1]; rewrite ?List.rev_involutive.
  { intros ρ' mD b Hρ' HmD Hb. destruct (HE _ _ Hρ' HmD) as [Es [Hty _ _]].
    exact (set_mem_eq_l _ _ _ (set_eq_sym _ _ Es) (Hty _ Hb)). }
  { intros Ek ρ' mD Hρ' HmD. destruct (HE _ _ Hρ' HmD) as [Es [_ _ Hpr]].
    exact (set_eq_trans _ _ _ Es (Hpr Ek)). }
  rewrite List.rev_involutive in Hw1.
  constructor; [exact Hw1 | | rewrite Hk; exact Hw0].
  (* the reduct: the target's over the parameters, or the filed member by name *)
  intros N n HN Hn0.
  pose proof (gctx_valid_syn _ _ Hgw) as Hvs.
  pose proof (mem_desc_ok _ _ _ _ _ _ _ Hvs HwE Hm') as Hd'.
  destruct (desc_ok_ty_at _ _ _ _ _ Hd' Ht') as [iA HAi].
  assert (Hlv : mdesc_kind R' = ak_level -> level_sorted_parameters Δ).
  { intros Ek Δ1 κ B Δ2 Eq. pose proof (member_pi_kinds _ _ Hgw _ _ _ _ _ _ _ Hw Hm Hk Ht HΔ Δ1 κ B Δ2 Eq) as Hpk.
    rewrite Ek in Hpk. inversion Hpk; reflexivity. }
  assert (Hred : exists N', N = ctx_fn Δ N' /\ gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ⊢ N' : A' /\
            forall ρ' mD n', set_env_in T γ (Δ ++ Γ) ρ' -> set_interp_moddef T γ (Δ ++ Γ) ρ' (md_alias E) mD ->
              set_interp T γ (Δ ++ Γ) ρ' N' n' -> set_eq (select_term γ mD x) n').
  { destruct Hred' as [Hup | (RE & p & T0 & Φ0 & HmE & HmdE & HR' & Hb)].
    - rewrite Hup in HN. destruct (mdesc_reduct R') as [N' |] eqn:HN'; cbn in HN; [injection HN as <- | discriminate].
      exists N'. split; [reflexivity | split; [exact (proj2 (desc_ok_ty_sorted _ _ Hvs _ _ _ Hd' Ht') _ HN') |]].
      intros ρ' mD n' Hρ' HmD Hn'. destruct (HE _ _ Hρ' HmD) as [Es [_ Hr _]].
      exact (set_eq_trans _ _ _ Es (Hr _ _ HN' Hn')).
    - rewrite Hb in HN. injection HN as <-. rewrite HR' in Hm'.
      destruct (Hbare _ _ _ _ _ _ _ HmE HmdE Hm') as [Hty Hmod].
      exists (a_mem (qname_mod p) x). split; [reflexivity | split; [exact Hty |]].
      intros ρ' mD n' Hρ' HmD Hn'. destruct (HE _ _ Hρ' HmD) as [Es _].
      inversion Hn'; subst. eapply set_eq_trans; [exact Es |]. apply select_term_resp.
      exact (Hmod _ HFE _ Hρ' _ ltac:(eassumption)). }
  destruct Hred as (N' & -> & HN' & Hb). rewrite <- (List.rev_involutive Δ) in Hn0.
  apply (set_unit_walk_reduct (List.rev Δ) Γ ρ P _ _ (mdesc_kind R') A' N' x (List.Forall_rev HΔ) Hρ HL HPx);
    [ exact (ctx_fn_split_typed _ _ _ _ _ _ HcΔΓ HΔ Hlv HAi HN') | | exact Hn0 ].
  rewrite List.rev_involutive. exact Hb.
Qed.

(** ** Filed Modules at Arguments *)

(** A path's proofness reads no slot. *)
Lemma mod_qname_member_proofs : forall H p, mod_qname H = Some p ->
    forall κs κs' ys x, modexp_member_proofs γ κs H ys x = modexp_member_proofs γ κs' H ys x.
Proof.
  induction H as [fp | k | H IH y | H IH N | U]; intros p Hp κs κs' ys x; cbn in Hp |- *; try discriminate; [reflexivity |].
  destruct (mod_qname H) as [q |] eqn:Hq; [| discriminate]. exact (IH _ eq_refl _ _ _ _).
Qed.

(** An application has its head's proofness. *)
Lemma me_apps_member_proofs : forall Ns H κs ys x, modexp_member_proofs γ κs (me_apps H Ns) ys x = modexp_member_proofs γ κs H ys x.
Proof. induction Ns as [| N Ns IH]; intros; cbn [me_apps]; [reflexivity | rewrite IH; reflexivity]. Qed.

(** An application's module: its head's at its arguments' values. *)
Lemma set_interp_me_apps_inv : forall Ns Γ ρ H m, set_interp_modexp T γ Γ ρ (me_apps H Ns) m ->
    exists m0 ns, set_interp_modexp T γ Γ ρ H m0 /\ set_interp_list T γ Γ ρ Ns ns /\ m = apply_module_args m0 ns.
Proof.
  induction Ns as [| N Ns IH]; intros Γ ρ H m Hm; cbn [me_apps] in Hm.
  - exists m, nil. split; [exact Hm | split; [constructor | reflexivity]].
  - destruct (IH _ _ _ _ Hm) as (m1 & ns & Hm1 & Hns & ->). inversion Hm1 as [| | | ? ? ? ? m0 n Hm0 Hn |]; subst.
    exists m0, (n :: ns). split; [assumption | split; [constructor; assumption | reflexivity]].
Qed.

Lemma apply_module_args_global : forall ns p args,
    apply_module_args (set_module_global p args) ns = set_module_global p (args ++ ns).
Proof.
  induction ns as [| n ns IH]; intros p args; unfold apply_module_args in *; cbn [fold_left apply_module];
    [rewrite List.app_nil_r; reflexivity | rewrite IH, <- List.app_assoc; reflexivity].
Qed.

(** The empty set applied is the empty set. *)
Lemma apply_values_empty : forall ns f, set_eq f empty_set -> set_eq (apply_values f ns) empty_set.
Proof.
  induction ns as [| n ns IH]; intros f Hf; [exact Hf |]. unfold apply_values in *. cbn [fold_left]. apply IH.
  eapply set_eq_trans; [apply set_apply_resp; [exact Hf | apply set_eq_refl] | apply set_apply_empty].
Qed.

(** A substitution extended by a term of the next assumption's type. *)
Lemma set_gsub_extend_ass : forall Γ σ Δ Fσ κ A N FA FN, set_gsub_with T γ Γ σ Δ Fσ -> set_ctx T γ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend σ (se_exp N) : ce_ass κ A :: Δ ->
    set_denotes T γ Δ A FA -> set_denotes T γ Γ N FN ->
    (forall ρ, set_env_in T γ Γ ρ -> set_mem (FN ρ) (code_carrier (FA (Fσ ρ)))) ->
    set_gsub_with T γ Γ (sb_extend σ (se_exp N)) (ce_ass κ A :: Δ) (fun ρ => set_env_extend (Fσ ρ) (set_entry_term κ (FN ρ))).
Proof.
  intros * Hg HΓ Hσ HA HN Hm. destruct (set_env_rel_per _ _ _ HΓ) as [Hsym Htrans]. constructor; [exact Hσ | |].
  - intros ρ [| x] Hρ; [split; cbn; [exact (set_denotes_exists _ _ _ _ _ HN _ Hρ) | constructor] |].
    exact (set_gsub_agrees _ _ _ _ _ _ Hg _ x Hρ).
  - intros ρ ρ' Hr.
    assert (Hl : set_env_in T γ Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
    assert (Hr' : set_env_in T γ Γ ρ') by (eapply Htrans; [apply Hsym; exact Hr | exact Hr]).
    pose proof (set_gsub_rel _ _ _ _ _ _ Hg _ _ Hl) as HlΔ.
    apply (set_env_rel_extend_ass T γ Δ (Fσ ρ) (Fσ ρ') κ A (FA (Fσ ρ))); [exact (set_gsub_rel _ _ _ _ _ _ Hg _ _ Hr)
      | exact (set_denotes_exists _ _ _ _ _ HA _ HlΔ) | exact (Hm _ Hl) |].
    apply set_eq_sym. exact (set_denotes_unique _ _ _ _ _ HN _ _ _ Hr (set_denotes_exists _ _ _ _ _ HN _ Hr')).
Qed.

(** A closed telescope's environments past any context: the entries
    below it dropped. *)
Lemma set_gsub_drop : forall Γ, ⊢ gc_deps ⍮ gc_stack ⍮ Γ ->
    set_gsub_with T γ Γ (sb_of_wk (wk_shiftn (List.length Γ))) nil (set_env_drop (List.length Γ)).
Proof.
  intros * Hc. constructor.
  - apply wf_sub_of_wk. pose proof (wf_wk_shiftn_app' _ _ Γ nil ltac:(rewrite List.app_nil_r; exact Hc)) as Hw.
    rewrite List.app_nil_r in Hw. exact Hw.
  - intros ρ x _. unfold sb_of_wk, wk_shiftn, set_env_drop. rewrite Nat.add_comm.
    split; cbn; [exact (set_interp_var T γ _ ρ _) | exact (set_interp_me_var T γ _ ρ _)].
  - intros ρ ρ' Hr. rewrite <- (List.app_nil_r Γ) in Hr. exact (set_env_rel_drop T γ _ _ _ _ Hr).
Qed.

Lemma set_interp_list_snoc_inv : forall Γ ρ Ns M vs, set_interp_list T γ Γ ρ (Ns ++ [M]) vs ->
    exists ns m, vs = ns ++ [m] /\ set_interp_list T γ Γ ρ Ns ns /\ set_interp T γ Γ ρ M m.
Proof.
  induction Ns as [| N Ns IH]; intros M vs H; cbn [List.app] in H; inversion H; subst.
  - inversion H6; subst. exists nil, v. auto using set_interp_list_nil.
  - destruct (IH _ _ H6) as (ns & m & -> & Hns & Hm). exists (v :: ns), m. split; [reflexivity | split; [constructor |]; assumption].
Qed.

(** Arguments filling a closed telescope of assumptions, each of its
    parameter's type instantiated by the ones before it, substitute it
    over the context: the values of the arguments fill it. *)
Lemma set_gsub_closed_inst : forall Tf Γ Ns, set_ctx T γ Γ -> all_assumptions Tf -> set_ctx T γ (Tf ++ Γ) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Tf ++ Γ -> List.length Ns = List.length Tf ->
    (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts Tf sb_id Ns) k = Some A -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ N : A) ->
    (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts Tf sb_id Ns) k = Some A -> set_rel_exp_eq T γ Γ A N N) ->
    exists Fσ, set_gsub_with T γ Γ (sb_of_list sb_id Ns) (Tf ++ Γ) Fσ /\
      forall ρ ns, set_env_in T γ Γ ρ -> set_interp_list T γ Γ ρ Ns ns -> list_set_eq ns (set_env_values Tf (Fσ ρ)).
Proof.
  induction Tf as [| e C IH]; intros Γ Ns HΓ HTf HC Hc Hl HNs HNr.
  - destruct Ns; [| discriminate]. exists (fun ρ => ρ). split; [exact (set_gsub_id _ Hc) |].
    intros ρ ns _ Hns. inversion Hns; subst. constructor.
  - inversion HTf as [| ? ? (κ & A & ->) HC']; subst.
    destruct (List.exists_last (l := Ns) ltac:(intros ->; discriminate)) as (Ns' & M & ->).
    rewrite List.length_app in Hl; cbn in Hl. assert (Hl' : List.length Ns' = List.length C) by lia.
    assert (Hti : tele_insts (ce_ass κ A :: C) sb_id (Ns' ++ [M]) = tele_insts C sb_id Ns' ++ [exp_sub A (sb_of_list sb_id Ns')]).
    { change (ce_ass κ A :: C) with ([ce_ass κ A] ++ C). rewrite tele_insts_app by (try exact HC'; lia). reflexivity. }
    assert (HlT : List.length (tele_insts C sb_id Ns') = List.length Ns') by (rewrite length_tele_insts by exact HC'; lia).
    rewrite Hti in HNs, HNr. cbn [List.app] in Hc, HC. destruct HC as [HC0 (FA & HA)].
    (* the arguments before the last, then the last *)
    assert (Hpre : forall k N A0, List.nth_error Ns' k = Some N -> List.nth_error (tele_insts C sb_id Ns') k = Some A0 ->
              List.nth_error (Ns' ++ [M]) k = Some N /\
              List.nth_error (tele_insts C sb_id Ns' ++ [exp_sub A (sb_of_list sb_id Ns')]) k = Some A0).
    { intros k N A0 HN HA0. assert (Hk : k < List.length Ns') by (apply List.nth_error_Some; congruence).
      split; rewrite List.nth_error_app1 by lia; assumption. }
    destruct (IH Γ Ns' HΓ HC' HC0 (ctx_decomp_tail Hc) Hl'
                (fun k N A0 HN HA0 => HNs k N A0 (proj1 (Hpre _ _ _ HN HA0)) (proj2 (Hpre _ _ _ HN HA0)))
                (fun k N A0 HN HA0 => HNr k N A0 (proj1 (Hpre _ _ _ HN HA0)) (proj2 (Hpre _ _ _ HN HA0))))
      as (Fσ & Hg & Hvals).
    assert (Hlast : List.nth_error (Ns' ++ [M]) (List.length Ns') = Some M /\
                    List.nth_error (tele_insts C sb_id Ns' ++ [exp_sub A (sb_of_list sb_id Ns')]) (List.length Ns') =
                    Some (exp_sub A (sb_of_list sb_id Ns'))).
    { split; rewrite List.nth_error_app2 by lia; [rewrite Nat.sub_diag | rewrite HlT, Nat.sub_diag]; reflexivity. }
    pose proof (HNs _ _ _ (proj1 Hlast) (proj2 Hlast)) as HM.
    destruct (HNr _ _ _ (proj1 Hlast) (proj2 Hlast)) as (FAσ & FM & FM' & [HAσ HMd _ _ HMm]).
    rewrite sb_of_list_app. cbn [sb_of_list].
    exists (fun ρ => set_env_extend (Fσ ρ) (set_entry_term κ (FM ρ))). split.
    + assert (Hs : set_moves_with T γ nil (C ++ Γ) Γ (sb_of_list sb_id Ns') Fσ)
        by (constructor; [exact Hg | exact HΓ | exact HC0 | exact HΓ | exact (ctx_decomp_tail Hc)]).
      pose proof (set_denotes_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs HA) as HAm.
      apply (set_gsub_extend_ass _ _ _ _ _ _ _ FA FM Hg HΓ); [| exact HA | exact HMd |].
      * inversion Hc; subst. eapply wf_sub_extend; [exact (set_gsub_typed _ _ _ _ _ _ Hg) | eassumption | eassumption | exact HM].
      * intros ρ Hρ. eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HAσ HAm Hρ) |].
        exact (HMm _ Hρ).
    + intros ρ ns Hρ Hns. destruct (set_interp_list_snoc_inv _ _ _ _ _ Hns) as (ns' & m & -> & Hns' & Hm).
      cbn [set_env_values]. apply List.Forall2_app; [exact (Hvals _ _ Hρ Hns') |]. constructor; [| constructor].
      exact (set_denotes_unique _ _ _ _ _ HMd _ _ _ Hρ Hm).
Qed.

Lemma set_env_values_above : forall Δ ρ ρb, set_env_values Δ (set_env_above (List.length Δ) ρ ρb) = set_env_values Δ ρ.
Proof. induction Δ as [| e Δ IH]; intros ρ ρb; [reflexivity |]. cbn [set_env_values List.length set_env_above]. f_equal. apply IH. Qed.

(** A term over a closed telescope [Tf] keeps its value read at the
    arguments' instance: the environment of [Tf] the instance makes, its
    entries below [Tf] dropped. *)
Lemma set_closed_inst_denotes : forall Tf Γ Ns Fι X FX, set_gsub_with T γ Γ (sb_of_list sb_id Ns) (Tf ++ Γ) Fι ->
    set_ctx T γ Γ -> set_ctx T γ Tf -> ctx_scoped 0 Tf -> ⊢ gc_deps ⍮ gc_stack ⍮ Tf -> set_ctx T γ (Tf ++ Γ) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Tf ++ Γ -> exp_scoped (List.length Tf) X -> set_denotes T γ Tf X FX ->
    set_denotes T γ Γ (exp_sub X (sb_of_list sb_id Ns))
      (fun ρ => FX (set_env_moved (List.length Tf) (set_env_drop (List.length Γ)) (Fι ρ))).
Proof.
  intros * Hι HΓ HT HTs HcT HCΓ HcΓ HXs HX.
  pose proof (ctx_app_wf_tail _ _ _ _ HcΓ) as HcΓ0.
  pose proof (set_gsub_drop _ HcΓ0) as Hd.
  assert (Hs1 : set_moves_with T γ Tf nil Γ (sb_of_wk (wk_shiftn (List.length Γ))) (set_env_drop (List.length Γ))).
  { constructor; [exact Hd | exact HΓ | rewrite List.app_nil_r; exact HT | rewrite tele_sub_closed by exact HTs; exact HCΓ |].
    rewrite List.app_nil_r. exact HcT. }
  rewrite <- (List.app_nil_r Tf) in HX at 1.
  pose proof (set_denotes_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs1 HX) as HX1.
  rewrite (tele_sub_closed _ _ HTs), (exp_scoped_sub_id _ _ _ HXs (fun x Hx => sb_qn_lt _ _ _ Hx)) in HX1.
  assert (Hs2 : set_moves_with T γ nil (Tf ++ Γ) Γ (sb_of_list sb_id Ns) Fι)
    by (constructor; [exact Hι | exact HΓ | exact HCΓ | exact HΓ | exact HcΓ]).
  exact (set_denotes_moved T γ Hfn Hmods _ _ _ _ _ _ _ Hs2 HX1).
Qed.

Lemma set_closed_inst_transport : forall Tf Γ Ns Fι X FX, set_gsub_with T γ Γ (sb_of_list sb_id Ns) (Tf ++ Γ) Fι ->
    set_ctx T γ Γ -> set_ctx T γ Tf -> ctx_scoped 0 Tf -> ⊢ gc_deps ⍮ gc_stack ⍮ Tf -> set_ctx T γ (Tf ++ Γ) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Tf ++ Γ -> exp_scoped (List.length Tf) X -> set_denotes T γ Tf X FX ->
    forall ρ a, set_env_in T γ Γ ρ -> set_interp T γ Γ ρ (exp_sub X (sb_of_list sb_id Ns)) a ->
    set_eq a (FX (set_env_moved (List.length Tf) (set_env_drop (List.length Γ)) (Fι ρ))).
Proof.
  intros * Hι HΓ HT HTs HcT HCΓ HcΓ HXs HX ρ a Hρ Ha.
  exact (set_denotes_unique _ _ _ _ _ (set_closed_inst_denotes _ _ _ _ _ _ Hι HΓ HT HTs HcT HCΓ HcΓ HXs HX) _ _ _ Hρ Ha).
Qed.

(** That environment is one of [Tf], of the arguments' values. *)
Lemma set_closed_inst_env : forall Tf Γ Ns Fι, set_gsub_with T γ Γ (sb_of_list sb_id Ns) (Tf ++ Γ) Fι ->
    set_ctx T γ Γ -> set_ctx T γ Tf -> ctx_scoped 0 Tf -> ⊢ gc_deps ⍮ gc_stack ⍮ Tf -> ⊢ gc_deps ⍮ gc_stack ⍮ Tf ++ Γ ->
    forall ρ, set_env_in T γ Γ ρ ->
    set_env_in T γ Tf (set_env_moved (List.length Tf) (set_env_drop (List.length Γ)) (Fι ρ)) /\
    set_env_values Tf (set_env_moved (List.length Tf) (set_env_drop (List.length Γ)) (Fι ρ)) = set_env_values Tf (Fι ρ).
Proof.
  intros * Hι HΓ HT HTs HcT HcΓ ρ Hρ. split; [| apply set_env_values_above].
  pose proof (set_gsub_drop _ (ctx_app_wf_tail _ _ _ _ HcΓ)) as Hd.
  pose proof (set_gsub_rel _ _ _ _ _ _ Hι _ _ Hρ) as Hιρ.
  rewrite <- (tele_sub_closed Tf (sb_of_wk (wk_shiftn (List.length Γ))) HTs) in Hιρ.
  pose proof (set_env_in_moved T γ Hfn Hmods _ _ _ _ _ _ Hd HΓ ltac:(rewrite List.app_nil_r; exact HT)
                ltac:(rewrite List.app_nil_r; exact HcT) Hιρ) as H.
  rewrite List.app_nil_r in H. exact H.
Qed.

(** A term applied to arguments: its value applied to theirs. *)
Lemma set_interp_apps_inv : forall Ns Γ ρ M v, set_interp T γ Γ ρ (apps_exp M Ns) v ->
    exists v0 ns, set_interp T γ Γ ρ M v0 /\ set_interp_list T γ Γ ρ Ns ns /\ v = apply_values v0 ns.
Proof.
  induction Ns as [| N Ns IH]; intros Γ ρ M v Hv; cbn [apps_exp] in Hv.
  - exists v, nil. split; [exact Hv | split; [constructor | reflexivity]].
  - destruct (IH _ _ _ _ Hv) as (v1 & ns & Hv1 & Hns & ->). inversion Hv1; subst.
    match goal with Hf : set_interp _ _ _ _ M ?f, Hn : set_interp _ _ _ _ N ?n |- _ =>
      exists f, (n :: ns); split; [exact Hf | split; [constructor; assumption | reflexivity]] end.
Qed.

(** A term applied to arguments: its value applied to theirs, conversely. *)
Lemma set_interp_apps : forall Ns Γ ρ M v ns, set_interp T γ Γ ρ M v -> set_interp_list T γ Γ ρ Ns ns ->
    set_interp T γ Γ ρ (apps_exp M Ns) (apply_values v ns).
Proof.
  induction Ns as [| N Ns IH]; intros Γ ρ M v ns Hv Hns; inversion Hns; subst; [exact Hv |].
  cbn [apps_exp apply_values List.fold_left]. apply IH; [constructor; assumption | assumption].
Qed.

(** Terms each of which denotes have their values as a function of the
    environment. *)
Lemma set_denotes_list : forall Γ Ns, (forall k N, List.nth_error Ns k = Some N -> exists FN, set_denotes T γ Γ N FN) ->
    exists Fs, forall ρ, set_env_in T γ Γ ρ -> set_interp_list T γ Γ ρ Ns (Fs ρ).
Proof.
  intros Γ Ns. induction Ns as [| N Ns IH]; intros HN; [exists (fun _ => nil); intros; constructor |].
  destruct (HN 0 N eq_refl) as (FN & HFN).
  destruct (IH (fun k N' HN' => HN (S k) N' HN')) as (Fs & HFs).
  exists (fun ρ => FN ρ :: Fs ρ). intros ρ Hρ. constructor; [exact (set_denotes_exists _ _ _ _ _ HFN _ Hρ) | exact (HFs _ Hρ)].
Qed.

Lemma app_split_length : forall {X} (l1 l2 l3 l4 : list X), l1 ++ l2 = l3 ++ l4 -> List.length l2 = List.length l4 -> l1 = l3 /\ l2 = l4.
Proof.
  intros X l1. induction l1 as [| a l1 IH]; intros l2 [| b l3] l4 E Hl; cbn [List.app] in E.
  - auto.
  - subst l2. cbn in Hl. rewrite List.length_app in Hl. lia.
  - subst l4. cbn in Hl. rewrite List.length_app in Hl. lia.
  - injection E as -> E. destruct (IH _ _ _ E Hl) as [-> ->]. auto.
Qed.

(** A typed description whose module part is a filed module read at
    arguments: its telescope is well formed, the arguments typed. *)
Lemma desc_ok_filed_args : forall Γ R p Tl Φ Ns, desc_ok gc_deps gc_stack Γ R ->
    mdesc_mod R = Some (mdesc_closed nil p Tl Φ Ns) -> ⊢ gc_deps ⍮ gc_stack ⍮ Tl /\ args_ok gc_deps gc_stack Γ Tl Ns.
Proof.
  intros Γ R p Tl Φ Ns Hd. revert p Tl Φ Ns.
  induction Hd as [| | Γ Θ' T0 Φ0 Ns0 Θ0 Ξ0 p0 lv _ _ _ _ _ HT0 _ Hargs | Γ Θd A M Rm lv i _ _ _ _ _ IH _ _ _];
    intros q Tq Φq Nq Hmod; cbn in Hmod; try discriminate.
  - injection Hmod as -> -> -> -> ->. cbn [List.app] in Hargs. exact (conj HT0 Hargs).
  - rewrite mdesc_mod_up in Hmod. destruct (mdesc_mod Rm) as [Rm0 |] eqn:Hm0; cbn in Hmod; [| discriminate].
    destruct Rm0 as [| | Θ1 p1 T1 Φ1 Ns1 |]; cbn in Hmod; try discriminate.
    injection Hmod as E -> -> -> ->. destruct Θ1, Θd; try discriminate. exact (IH _ _ _ _ eq_refl).
Qed.

(** A module expression whose module part is a filed module read bare:
    its term member with no reduct is the filed module's, typed by name. *)
Lemma bare_member_typed : forall Γ E RE p T0 Φ0 x r A0, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ E ≈ E ->
    mdenote gc_deps gc_stack Γ E RE -> mdesc_mod RE = Some (mdesc_closed nil p T0 Φ0 nil) ->
    mdenote gc_deps gc_stack Γ (me_mem E x) (mdesc_term r A0 None) ->
    loc gc_deps gc_stack p T0 Φ0 /\ gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_mem (qname_mod p) x : A0.
Proof.
  intros * HwE HmE HmodE Hm.
  pose proof (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hgw HmE) HmodE) as Hl; cbn in Hl.
  split; [exact Hl |].
  pose proof (presup_modexp_eq_ctx HwE) as HΓ.
  pose proof (gctx_valid_syn _ _ Hgw) as Hvs.
  destruct (desc_ok_ty_sorted _ _ Hvs _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hvs HwE Hm) eq_refl) as [(S & HS & HA0) _].
  destruct (qname_mod_denote _ _ Hgw _ _ _ Γ Hl) as (R2 & Hm2 & HR2).
  assert (Hmod2 : mdesc_mod R2 = Some (mdesc_closed nil p T0 Φ0 nil)) by (destruct HR2 as [-> | (A & M & ->)]; reflexivity).
  assert (Hm' : mdenote gc_deps gc_stack Γ (me_mem (qname_mod p) x) (mdesc_term r A0 None)).
  { inversion Hm as [? ? ? ? ? _ _ | ? ? ? pq k D ? ? ? _ _ _ _ | | | | ? ? ? R1 R1m Γy Ee rd R3 ? Hm1 Hmd1 He Hed Hr
                    | ? ? ? Rr ? ? _ _ _]; subst.
    pose proof (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ Hm1 _ HmE) as ->.
    rewrite HmodE in Hmd1. injection Hmd1 as <-.
    eapply mdenote_mem; [exact Hm2 | exact Hmod2 | exact He | exact Hed | exact Hr]. }
  eapply wf_mem; [exact (loc_modexp_wf _ _ _ HΓ _ _ _ Hl) | exact Hm' | reflexivity | exact HA0 | exact HS |].
  intros M HM; discriminate.
Qed.

(** A filed module's path reads its global module, when each module or
    frame the context files or has open is its own global module: the
    path is read down its chain, each step selecting the next module,
    each well formed in a well-formed context. *)
Lemma set_interp_filed_path :
    (forall q TΦ, gc_loc gc_deps gc_stack q = Some TΦ -> global_module γ q = set_module_global q nil) ->
    forall Γ, ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> forall p Tp Φp, loc gc_deps gc_stack p Tp Φp ->
    forall ρ, set_interp_modexp T γ Γ ρ (qname_mod p) (set_module_global p nil).
Proof.
  intros Hb Γ HΓ [fp ch]. induction ch as [| y ch IH] using List.rev_ind; intros Tp Φp Hl ρ.
  - cbn. constructor.
  - change {| q_unit := fp; q_chain := ch ++ [y] |} with (qname_in {| q_unit := fp; q_chain := ch |} y) in *.
    destruct (loc_parent _ _ Hgw _ _ _ _ Hl) as (T' & Φ' & Hl').
    pose proof (loc_modexp_wf _ _ _ HΓ _ _ _ Hl) as Hw.
    rewrite qname_mod_in in Hw |- *.
    replace (set_module_global (qname_in {| q_unit := fp; q_chain := ch |} y) nil)
      with (select_module γ (set_module_global {| q_unit := fp; q_chain := ch |} nil) y).
    + constructor; [exact (IH _ _ Hl' ρ) | exact Hw].
    + cbn [select_module apply_module_args fold_left]. exact (Hb _ _ (gc_loc_of_loc _ _ Hgw _ _ _ Hl)).
Qed.

(** The valuation models, here, everything the context [Θs ⍮ Ξs] the
    derivations were checked at resolves *)
Hypothesis Hemb : set_gctx_embedding Θs Ξs gc_deps gc_stack T γ.

(** Every module or frame this context files or has open is its own
    global module. *)
Lemma set_target_bodies : forall q TΦ, gc_loc gc_deps gc_stack q = Some TΦ -> global_module γ q = set_module_global q nil.
Proof. exact (set_gctx_embedding_bodies _ _ _ _ _ _ Hemb). Qed.

(** That context is well formed. *)
Lemma set_source_wf : ⊢ᵍ Θs ⍮ Ξs.
Proof. exact (set_gctx_embedding_source_wf _ _ _ _ _ _ Hemb). Qed.

(** This one grows out of it. *)
Lemma set_source_sub : gc_sub Θs Ξs gc_deps gc_stack.
Proof. exact (gctx_embedding_resolution _ _ _ _ (set_gctx_embedding_embedding _ _ _ _ _ _ Hemb)). Qed.

(** What it files or has open is modelled here, its members read with its
    own stack. *)
Lemma set_source_filed : forall p Tl Φ, gc_loc Θs Ξs p = Some (Tl, Φ) -> set_filed_mod T γ Ξs p Tl Φ.
Proof.
  intros * Hl. pose proof (set_gctx_embedding_filed _ _ _ _ _ _ Hemb _ _ _ Hl) as Hf.
  rewrite <- gc_mk_eta in Hf. exact Hf.
Qed.

(** Each group it declares is modelled here. *)
Lemma set_source_groups : forall p D, ind_lookup Θs Ξs p = Some D -> set_group_ok T γ p D (global_group γ p).
Proof.
  intros * HD. pose proof (set_gctx_embedding_groups _ _ _ _ _ _ Hemb _ _ HD) as HG.
  rewrite <- gc_mk_eta in HG. exact HG.
Qed.

(** So is each record type. *)
Lemma set_source_records : forall p R, record_lookup Θs Ξs p = Some R -> set_record_ok T γ p R (global_record γ p).
Proof.
  intros * HR. pose proof (set_gctx_embedding_records _ _ _ _ _ _ Hemb _ _ HR) as HSR.
  rewrite <- gc_mk_eta in HSR. exact HSR.
Qed.

(** An alias it files is the module its closed unit denotes here. *)
Lemma set_source_aliases : forall q Ua FU, gc_module Θs Ξs q = Some (mr_alias Ua) ->
    set_modexp_denotes T γ nil (me_lit Ua) FU -> set_module_eq γ (global_module γ q) (FU empty_set_env).
Proof.
  intros * Hq. pose proof (set_gctx_embedding_aliases _ _ _ _ _ _ Hemb _ _ FU Hq) as Ha.
  rewrite <- gc_mk_eta in Ha. exact Ha.
Qed.

(** A member [Θs ⍮ Ξs] denotes is one it has: read through the module
    part it reads; or a frame open on its stack, the frame itself or, as
    the type former of an inductive or record type, stored at the frame's
    parent ([mdenote_ind_frame]).  This is how a rule read at [Θs ⍮ Ξs]
    meets the members it may speak of. *)
Lemma set_member_known_of_source : forall Γ H x R1, mdenote Θs Ξs Γ (me_mem H x) R1 ->
    set_member_known Θs Ξs Γ H x.
Proof.
  intros * Hm RH RHm HmH HmodH.
  pose proof (set_gctx_embedding_embedding _ _ _ _ _ _ Hemb) as He.
  (* an open frame's parent is filed or open there *)
  assert (Hpar : forall pq, mod_qname (me_mem H x) = Some pq -> (exists U T1, gs_find_tele Ξs pq = Some (U, nil, T1)) ->
            exists mq Tq Φq, pq = qname_in mq x /\ H = qname_mod mq /\ gc_loc Θs Ξs mq = Some (Tq, Φq)).
  { intros pq Hq (U & T1 & Ht0). cbn in Hq. destruct (mod_qname H) as [mq |] eqn:Hq0; [| discriminate]. injection Hq as <-.
    change {| q_unit := q_unit mq; q_chain := q_chain mq ++ x :: nil |} with (qname_in mq x) in Ht0.
    destruct (frame_parent _ _ set_source_wf _ _ _ _ Ht0) as (Tq & Φq & Hfq & _).
    exists mq, Tq, Φq. split; [reflexivity | split; [exact (mod_qname_inv _ _ Hq0) | unfold gc_loc; rewrite Hfq; reflexivity]]. }
  (* [H]'s module part there, which has [x] *)
  assert (Hsrc : exists R0s R0sm, mdenote Θs Ξs Γ H R0s /\ mdesc_mod R0s = Some R0sm /\ set_member_seen Ξs R0sm x).
  { inversion Hm as [? ? pu Tu Φu Hq Hu | ? ? ? pq k D Mk ? ? Hq Hk HMk _ | | | | ? ? ? R1' R1m Γy E rd R2 ? Hm1 Hmd1 He1 _ _
                    | ? ? ? Rr ? ? Hq Hk]; subst.
    - (* the frame itself *)
      destruct (gc_unit_cases _ _ _ _ _ Hu) as (pf & Hq' & [Hf | (_ & Hc & _)]); rewrite Hq in Hq'; injection Hq' as <-.
      + assert (Ht0 : exists U T1, gs_find_tele Ξs pu = Some (U, nil, T1)).
        { unfold gc_frame in Hf; destruct (gs_find_tele Ξs pu) as [[[U [| ? ?]] T1] |];
            try (destruct U as [? [[|] ? | ?]]); try discriminate; eauto. }
        destruct (Hpar _ Hq Ht0) as (mq & Tq & Φq & -> & -> & Hlq).
        destruct (filed_denote _ _ set_source_wf _ _ _ Γ nil Hlq) as (R0s & HmR & HmodR).
        exists R0s, (mdesc_closed nil mq Tq Φq nil). split; [exact HmR | split; [exact HmodR |]].
        eapply set_member_seen_frame. exact Hf.
      + exfalso. cbn in Hq. destruct (mod_qname H) as [p0 |]; [| discriminate]. injection Hq as <-.
        cbn in Hc. destruct (q_chain p0); discriminate.
    - destruct (Hpar _ Hq (gs_find_ind_tele _ _ _ Hk)) as (mq & Tq & Φq & -> & -> & Hlq).
      destruct (filed_denote _ _ set_source_wf _ _ _ Γ nil Hlq) as (R0s & HmR & HmodR).
      exists R0s, (mdesc_closed nil mq Tq Φq nil). split; [exact HmR | split; [exact HmodR |]].
      eapply set_member_seen_stored. eapply stored_term_member_ind_former; eassumption.
    - exists R1', R1m. split; [exact Hm1 | split; [exact Hmd1 | eapply set_member_seen_entry; exact He1]].
    - destruct (Hpar _ Hq (gs_find_record_tele _ _ _ Hk)) as (mq & Tq & Φq & -> & -> & Hlq).
      destruct (filed_denote _ _ set_source_wf _ _ _ Γ nil Hlq) as (R0s & HmR & HmodR).
      exists R0s, (mdesc_closed nil mq Tq Φq nil). split; [exact HmR | split; [exact HmodR |]].
      eapply set_member_seen_stored. eapply stored_term_member_record_former; eassumption. }
  (* here, [H]'s module part is that one grown *)
  destruct Hsrc as (R0s & R0sm & HmHs & Hmods0 & Hseen).
  destruct (gctx_embedding_mdenote _ _ _ _ set_source_wf He _ _ _ HmHs) as (R0t & HmHt & Hgr).
  rewrite <- (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ HmH _ HmHt) in Hgr.
  destruct (mdesc_grows_mod _ _ _ _ _ _ _ Hgr Hmods0) as (R2m & Hmod2 & Hgrm).
  rewrite HmodH in Hmod2. injection Hmod2 as <-.
  exists R0sm. split; assumption.
Qed.

(** A member [Θs ⍮ Ξs] has of a filed module is one it has stored there,
    of the description stored here: an entry of its smaller body, grown
    here, or the type former of a frame open there. *)
Lemma set_member_known_stored : forall Γ H RH p Tl Φ Ns x R0, set_member_known Θs Ξs Γ H x ->
    mdenote gc_deps gc_stack Γ H RH -> mdesc_mod RH = Some (mdesc_closed nil p Tl Φ Ns) ->
    gc_loc gc_deps gc_stack p = Some (Tl, Φ) -> stored_term_member gc_stack Φ p x R0 ->
    exists Φ1, gc_loc Θs Ξs p = Some (Tl, Φ1) /\ stored_term_member Ξs Φ1 p x R0.
Proof.
  intros * Hk Hm Hmod Hl2 Hst2.
  destruct (Hk _ _ Hm Hmod) as (Rm1 & Hg & Hs).
  inversion Hg as [? Hcl | ? ? Φ1 ? ? ? Hl1 Hl2' |]; subst; [cbn in Hcl; discriminate |].
  pose proof (gc_loc_of_loc _ _ set_source_wf _ _ _ Hl1) as Hgl1.
  exists Φ1. split; [exact Hgl1 |].
  inversion Hs as [? ? e He | ? ? ? ? ? ? R1 Hst1 | ? ? ? ? ? ? Ty Φy Hfr]; subst.
  - (* an entry of the smaller body: the stored member here is it grown *)
    cbn [mdesc_entry] in He. destruct (gm_prefix_upto Φ1 x) as [Φx |] eqn:Hp; [| discriminate].
    destruct (gm_prefix_entry _ _ _ Hp) as (Φ0 & E & -> & Hent).
    destruct (loc_entry_grow _ _ _ _ set_source_wf Hgw set_source_sub _ _ _ _ _ _ _ Hl1 (gc_loc_loc _ _ _ _ _ Hl2) Hp)
      as (Φ0' & E2 & Hp2 & Hgr).
    destruct (gm_prefix_entry _ _ _ Hp2) as (? & ? & [= <- <-] & Hent2).
    pose proof (proj2 (loc_entry _ _ Hgw _ _ _ (gc_loc_loc _ _ _ _ _ Hl2) x E2) Hent2) as HeE2.
    destruct Hst2 as [Φ0'' E2' R0' Hp2' HE2' | pq k D Mk Hk' HMk | Rr Hr].
    + rewrite Hp2 in Hp2'. injection Hp2' as <- <-.
      eapply stored_term_member_entry; [exact Hp | rewrite <- (entry_grows_entry_term _ _ _ Hgr); exact HE2'].
    + (* an open frame's path names no entry *)
      exfalso. destruct (gs_find_ind_tele _ _ _ Hk') as (U & T0 & Ht).
      rewrite (gc_entry_tele_nil _ _ _ _ _ Ht) in HeE2. discriminate.
    + exfalso. destruct (gs_find_record_tele _ _ _ Hr) as (U & T0 & Ht).
      rewrite (gc_entry_tele_nil _ _ _ _ _ Ht) in HeE2. discriminate.
  - (* a stored member there: the same one here *)
    rewrite (stored_term_member_grow _ _ _ _ set_source_wf Hgw set_source_sub _ _ _ _ _ _ _ Hgl1 Hst1 Hl2 Hst2).
    exact Hst1.
  - (* a frame open there: the type former of an inductive or record type
       stored at it, or a module frame, which stores no term *)
    destruct (gs_find_ind Ξs (qname_in p x)) as [[[pq k] D] |] eqn:Hki.
    { destruct (frame_ind_loc _ _ set_source_wf _ _ _ _ Hki) as (? & ? & ? & ? & Mk & _ & _ & _ & HMk).
      assert (Hst1 : stored_term_member Ξs Φ1 p x
                (mdesc_term ak_relevant (ctx_pi (im_params D Mk) (exp_wk (ind_sort D) (wk_shiftn (im_nn Mk)))) (Some (a_ind pq k))))
        by (eapply stored_term_member_ind_former; eassumption).
      rewrite (stored_term_member_grow _ _ _ _ set_source_wf Hgw set_source_sub _ _ _ _ _ _ _ Hgl1 Hst1 Hl2 Hst2).
      exact Hst1. }
    destruct (gs_find_record Ξs (qname_in p x)) as [Rr |] eqn:Hkr.
    { assert (Hst1 : stored_term_member Ξs Φ1 p x
                (mdesc_term ak_relevant (ctx_pi (record_params Rr) (record_sort Rr)) (Some (a_record (qname_in p x)))))
        by (eapply stored_term_member_record_former; exact Hkr).
      rewrite (stored_term_member_grow _ _ _ _ set_source_wf Hgw set_source_sub _ _ _ _ _ _ _ Hgl1 Hst1 Hl2 Hst2).
      exact Hst1. }
    exfalso.
    destruct (gc_sub_frame_field _ _ _ _ set_source_sub _ _ _ Hfr) as (Φ' & [(Hfr2 & Hki2 & Hkr2) | (Hb2 & Hm2 & Hr2)]).
    + (* still open here: no term is stored at it *)
      assert (Ht2 : exists U T1, gs_find_tele gc_stack (qname_in p x) = Some (U, nil, T1)).
      { unfold gc_frame in Hfr2; destruct (gs_find_tele gc_stack (qname_in p x)) as [[[U [| ? ?]] T1] |];
          try (destruct U as [? [[|] ? | ?]]); try discriminate; eauto. }
      destruct Ht2 as (U & T1 & Ht2).
      destruct Hst2 as [Φ0 E2 R0' Hp2 HE2 | pq k D Mk Hk2 _ | Rr Hr2'].
      * destruct (gm_prefix_entry _ _ _ Hp2) as (? & ? & [= <- <-] & Hent2).
        pose proof (proj2 (loc_entry _ _ Hgw _ _ _ (gc_loc_loc _ _ _ _ _ Hl2) x E2) Hent2) as HeE2.
        rewrite (gc_entry_tele_nil _ _ _ _ _ Ht2) in HeE2. discriminate.
      * rewrite Hki2, Hki in Hk2. discriminate.
      * rewrite Hkr2, Hkr in Hr2'. discriminate.
    + (* filed here, as the module it was *)
      rewrite Hki in Hm2. rewrite Hkr in Hr2.
      destruct Hst2 as [Φ0 E2 R0' Hp2 HE2 | pq k D Mk Hk2 _ | Rr Hr2'].
      * destruct (gm_prefix_entry _ _ _ Hp2) as (? & ? & [= <- <-] & Hent2).
        destruct (gm_entry_head _ _ _ Hent2) as (z & ip & [= <- <-] & Hin).
        destruct (loc_read _ _ Hgw _ _ _ (gc_loc_loc _ _ _ _ _ Hl2) _ Hin nil) as (HeE2 & _ & HmS & HbS).
        rewrite <- qname_in_app in HeE2, HmS, HbS.
        destruct (gm_child_of_entry _ _ _ Tl Hent2) as [Em Eb]. rewrite Em in HmS. rewrite Eb in HbS.
        rewrite Hent2 in HeE2.
        destruct E2 as [b pv r A oM | pv U | pv pq k D ΦD | pv A M U | pv pr R ΦR];
          cbn in HE2, HmS, HbS; rewrite ?String.eqb_refl in HmS, HbS; try discriminate.
        -- rewrite HbS in Hb2. discriminate.
        -- rewrite HmS in Hm2. injection Hm2 as _ Hd. discriminate.
        -- exact (gc_entry_def_mod_not_body _ _ _ _ _ _ _ _ _ HeE2 Hm2).
        -- unfold record_lookup in Hr2. rewrite (gc_entry_record_frame_none _ _ _ _ HeE2), HeE2 in Hr2. discriminate.
      * destruct (gs_find_ind_tele _ _ _ Hk2) as (U & T1 & Ht2).
        unfold gc_body in Hb2. rewrite Ht2 in Hb2. discriminate.
      * destruct (gs_find_record_tele _ _ _ Hr2') as (U & T1 & Ht2).
        unfold gc_body in Hb2. rewrite Ht2 in Hb2. discriminate.
Qed.

(** An alias entry does not grow: its unit is the whole of it. *)
Lemma entry_grows_alias_eq : forall E1 E2 Ua, entry_grows E1 E2 -> entry_alias_unit E2 = Some Ua -> E1 = E2.
Proof.
  intros [| pv1 [Δ1 [sm1 Φ1 | E1']] | ? ? ? ? ? | ? ? ? ? | ? ? ? ?] [| pv2 [Δ2 [sm2 Φ2 | E2']] | ? ? ? ? ? | ? ? ? ? | ? ? ? ?] Ua Hg Ha;
    cbn in Hg, Ha; try discriminate; exact Hg.
Qed.

(** A member [Θs ⍮ Ξs] has of a filed module that is an alias here is the
    same alias entry of the module's body there: an entry there grows into
    this one, and an alias does not grow; a frame open there is no alias
    here, whether still open or filed as the module it was. *)
Lemma set_member_known_alias_entry : forall Γ H RH p Tl Φ Ns x Φ0 E Ua, set_member_known Θs Ξs Γ H x ->
    mdenote gc_deps gc_stack Γ H RH -> mdesc_mod RH = Some (mdesc_closed nil p Tl Φ Ns) ->
    gc_loc gc_deps gc_stack p = Some (Tl, Φ) -> gm_prefix_upto Φ x = Some (gm_ext Φ0 x E) -> entry_alias_unit E = Some Ua ->
    exists Φ1 Φ1', gc_loc Θs Ξs p = Some (Tl, Φ1) /\ gm_prefix_upto Φ1 x = Some (gm_ext Φ1' x E).
Proof.
  intros * Hk Hm Hmod Hl2 Hp HUa.
  destruct (Hk _ _ Hm Hmod) as (Rm1 & Hg & Hs).
  inversion Hg as [? Hcl | ? ? Φ1 ? ? ? Hl1 Hl2' |]; subst; [cbn in Hcl; discriminate |].
  pose proof (gc_loc_of_loc _ _ set_source_wf _ _ _ Hl1) as Hgl1.
  exists Φ1.
  (* the entry here, read at its path *)
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- <-] & Hent2).
  destruct (gm_entry_head _ _ _ Hent2) as (z & ip & [= <- <-] & Hin).
  destruct (loc_read _ _ Hgw _ _ _ (gc_loc_loc _ _ _ _ _ Hl2) _ Hin nil) as (HeE2 & _ & HmS & _).
  rewrite <- qname_in_app in HeE2, HmS. rewrite Hent2 in HeE2.
  destruct (gm_child_of_entry _ _ _ Tl Hent2) as [Em _]. rewrite Em in HmS.
  (* a frame open there is no alias here *)
  assert (Hnofr : forall Ty Φy, gc_frame Ξs (qname_in p x) = Some (Ty, Φy) -> False).
  { intros Ty Φy Hfr.
    destruct (gc_sub_frame_field _ _ _ _ set_source_sub _ _ _ Hfr) as (Φ' & [(Hfr2 & _ & _) | (_ & Hm2 & _)]).
    - assert (Ht2 : exists U T1, gs_find_tele gc_stack (qname_in p x) = Some (U, nil, T1)).
      { unfold gc_frame in Hfr2; destruct (gs_find_tele gc_stack (qname_in p x)) as [[[U [| ? ?]] T1] |];
          try (destruct U as [? [[|] ? | ?]]); try discriminate; eauto. }
      destruct Ht2 as (U & T1 & Ht2). rewrite (gc_entry_tele_nil _ _ _ _ _ Ht2) in HeE2. discriminate.
    - destruct E as [| pv [Ta [| Ea]] | | pv Ad Md [Ta [| Ea]] |]; cbn in HUa; try discriminate.
      + cbn in HmS. rewrite String.eqb_refl in HmS. rewrite HmS in Hm2. discriminate.
      + exact (gc_entry_def_mod_not_body _ _ _ _ _ _ _ _ _ HeE2 Hm2). }
  (* an entry there grows into this one, and is it *)
  assert (Hent1 : forall Φ1' E1, gm_prefix_upto Φ1 x = Some (gm_ext Φ1' x E1) ->
            exists Φ1'', gc_loc Θs Ξs p = Some (Tl, Φ1) /\ gm_prefix_upto Φ1 x = Some (gm_ext Φ1'' x E)).
  { intros Φ1' E1 Hp1.
    destruct (loc_entry_grow _ _ _ _ set_source_wf Hgw set_source_sub _ _ _ _ _ _ _ Hl1 Hl2' Hp1) as (Φ0' & E2 & Hp2 & Hgr).
    rewrite Hp in Hp2. injection Hp2 as <- <-.
    exists Φ1'. split; [exact Hgl1 | rewrite Hp1, (entry_grows_alias_eq _ _ _ Hgr HUa); reflexivity]. }
  inversion Hs as [? ? e He | ? ? ? ? ? ? R1 Hst1 | ? ? ? ? ? ? Ty Φy Hfr]; subst.
  - assert (Hp1 : exists Φ1' E1, gm_prefix_upto Φ1 x = Some (gm_ext Φ1' x E1)).
    { cbn [mdesc_entry] in He. destruct (gm_prefix_upto Φ1 x) as [Φx |] eqn:Hp1; [| discriminate].
      destruct (gm_prefix_entry _ _ _ Hp1) as (Φ1' & E1 & -> & _). eauto. }
    destruct Hp1 as (Φ1' & E1 & Hp1). exact (Hent1 _ _ Hp1).
  - destruct Hst1 as [Φ1' E1 R1' Hp1 _ | pq k D Mk Hki _ | Rr Hkr].
    + exact (Hent1 _ _ Hp1).
    + exfalso. destruct (frame_ind_loc _ _ set_source_wf _ _ _ _ Hki) as (? & ? & ? & ? & ? & _ & Hfr & _). exact (Hnofr _ _ Hfr).
    + exfalso. destruct (frame_record_loc _ _ set_source_wf _ _ Hkr) as (? & ? & ? & ? & _ & Hfr & _). exact (Hnofr _ _ Hfr).
  - exfalso. exact (Hnofr _ _ Hfr).
Qed.

(** A term member of a filed module at valid arguments: whether it is a
    proof is its stored kind; its value is the stored value applied to the
    arguments' values, of the [Π] over the rest of the telescope
    instantiated, and its reduct's value: the stored reduct instantiated,
    or the member read by name. *)
(** The type and the reduct of a term member of an alias over the
    parameters [Δ] denote: the [Π] and the [λ] over [Δ] of its target's,
    or of the filed member read by name. *)
Lemma set_alias_members_denote : forall Γ Δ E, set_alias_ok T γ Γ Δ E -> gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ⊢ᵐ E ≈ E ->
    set_members_denote (Δ ++ Γ) E -> set_members_denote Γ (me_lit (gu_mk Δ (md_alias E))).
Proof.
  intros * Hal HwE IHd x R A Hkn Hm Ht. destruct Hal as [Hw HΔ _ HΓ HΔΓ _ _].
  pose proof (set_member_known_alias _ _ _ _ Hkn) as HknE.
  pose proof (presup_modexp_eq_ctx HwE) as HcΔΓ. pose proof (gctx_valid_syn _ _ Hgw) as Hvs.
  (* the closures over the parameters of a type and a reduct denoting past them *)
  assert (Hfin : forall R0 A0 i, R = mdesc_up Δ R0 -> mdesc_type R0 = Some A0 ->
            gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ⊢ A0 : abs_kind_sort (mdesc_kind R0) (a_typ i) ->
            (exists FA0, set_denotes T γ (Δ ++ Γ) A0 FA0) ->
            (forall N0, mdesc_reduct R0 = Some N0 ->
               gc_deps ⍮ gc_stack ⍮ Δ ++ Γ ⊢ N0 : A0 /\ exists FN0, set_denotes T γ (Δ ++ Γ) N0 FN0) ->
            (exists FA, set_denotes T γ Γ A FA) /\ forall M, mdesc_reduct R = Some M -> exists FM, set_denotes T γ Γ M FM).
  { intros R0 A0 i -> HA0 HA0w (FA0 & HFA0) HN.
    destruct (mdesc_type_up_inv _ _ _ Ht) as (A1 & HA1 & EA). rewrite HA0 in HA1. injection HA1 as <-.
    split; [rewrite EA; exact (set_ctx_pi_denotes _ _ _ _ _ HΔ HΔΓ HcΔΓ HFA0) |].
    intros M HM. rewrite mdesc_reduct_up in HM.
    destruct (mdesc_reduct R0) as [N0 |] eqn:HN0; cbn in HM; [injection HM as <- | discriminate].
    destruct (HN _ eq_refl) as (HN0w & FN0 & HFN0).
    assert (Hlv : mdesc_kind R0 = ak_level -> level_sorted_parameters Δ).
    { intros Ek Δ1 κ B Δ2 Eq.
      pose proof (member_pi_kinds _ _ Hgw _ _ _ _ _ _ _ Hw Hm (mdesc_kind_up Δ R0) ltac:(rewrite Ht, EA; reflexivity) HΔ Δ1 κ B Δ2 Eq) as Hpk.
      rewrite Ek in Hpk. inversion Hpk; reflexivity. }
    assert (Hty : forall Δ1 Δ2, Δ = Δ1 ++ Δ2 ->
              gc_deps ⍮ gc_stack ⍮ Δ2 ++ Γ ⊢ ctx_fn Δ1 N0 : ctx_pi_at (mdesc_kind R0) Δ1 A0).
    { intros Δ1 Δ2 ->. pose proof (ctx_fn_split_typed _ _ _ _ _ _ HcΔΓ HΔ Hlv HA0w HN0w (List.rev Δ2) (List.rev Δ1)
                                     ltac:(rewrite List.rev_app_distr; reflexivity)) as Hty.
      rewrite !List.rev_involutive in Hty. exact Hty. }
    exact (set_ctx_fn_denotes _ _ _ _ _ _ HΔ HΔΓ HcΔΓ Hty HFN0). }
  destruct (alias_mem_desc _ _ Hgw _ _ _ _ _ _ HcΔΓ Hm Ht) as (R' & Hm' & [-> | (r & A0 & RE & p & T0 & Φ0 & -> & HmE & HmdE & ->)]).
  - (* the target's member *)
    destruct (mdesc_type_up_inv _ _ _ Ht) as (A' & Ht' & _).
    destruct (IHd _ _ _ HknE Hm' Ht') as [HA' HN'].
    pose proof (mem_desc_ok _ _ _ _ _ _ _ Hvs HwE Hm') as Hd'.
    destruct (desc_ok_ty_at _ _ _ _ _ Hd' Ht') as [i HAi].
    apply (Hfin _ _ i eq_refl Ht' HAi HA'). intros N0 HN0.
    exact (conj (proj2 (desc_ok_ty_sorted _ _ Hvs _ _ _ Hd' Ht') _ HN0) (HN' _ HN0)).
  - (* the filed member read by name *)
    destruct (bare_member_typed _ _ _ _ _ _ _ _ _ HwE HmE HmdE Hm') as [Hl Hty].
    pose proof (set_interp_filed_path set_target_bodies _ HcΔΓ _ _ _ Hl) as Hpath.
    assert (HFN : set_denotes T γ (Δ ++ Γ) (a_mem (qname_mod p) x) (fun _ => select_term γ (set_module_global p nil) x)).
    { apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΔΓ). intros ρ _. econstructor; [ exact (Hpath ρ) | exact Hty ]. }
    destruct (desc_ok_ty_at _ _ _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hvs HwE Hm') eq_refl) as [i HAi].
    apply (Hfin (mdesc_term r A0 (Some (a_mem (qname_mod p) x))) A0 i eq_refl eq_refl HAi (proj1 (IHd _ _ _ HknE Hm' eq_refl))).
    intros N0 HN0. cbn in HN0. injection HN0 as <-. exact (conj Hty (ex_intro _ _ HFN)).
Qed.

Lemma set_filed_members : forall Γ p Tl Φ Tr Tf Ns,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    gc_loc gc_deps gc_stack p = Some (Tl, Φ) -> set_ctx T γ Γ -> set_args_valid T γ Γ Tl Tr Tf Ns ->
    set_members_proofs Γ (me_apps (qname_mod p) Ns) /\
    forall F, set_modexp_denotes T γ Γ (me_apps (qname_mod p) Ns) F -> set_members_values Γ (me_apps (qname_mod p) Ns) F.
Proof.
  intros * Hw Hgl HΓ Ha.
  (* a member the smaller context has is stored in a body it files, modelled here *)
  assert (Hsrc : forall x R0, set_member_known Θs Ξs Γ (me_apps (qname_mod p) Ns) x -> stored_term_member gc_stack Φ p x R0 ->
            exists Φ1, set_filed_mod T γ Ξs p Tl Φ1 /\ stored_term_member Ξs Φ1 p x R0).
  { intros x R0 Hkn Hst. destruct (filed_denote _ _ Hgw _ _ _ Γ Ns Hgl) as (RK & HmK & HmodK).
    destruct (set_member_known_stored _ _ _ _ _ _ _ _ _ Hkn HmK HmodK Hgl Hst) as (Φ1 & Hl1 & Hst1).
    exact (ex_intro _ Φ1 (conj (set_source_filed _ _ _ Hl1) Hst1)). }
  (* the module's path reads its global module *)
  pose proof (presup_modexp_eq_ctx Hw) as HcΓ0.
  pose proof (gc_loc_loc _ _ _ _ _ Hgl) as Hlp.
  pose proof (fun Γ' HcΓ' ρ' => set_interp_filed_path set_target_bodies Γ' HcΓ' _ _ _ Hlp ρ') as Hpath.
  assert (Hglob : forall ρ' m, set_env_eq γ ρ' ρ' -> set_interp_modexp T γ Γ ρ' (qname_mod p) m ->
            set_module_eq γ m (set_module_global p nil)).
  { intros ρ' m Eρ Hm. exact (set_interp_modexp_functional T γ Hfn Hmods _ _ _ _ Hm _ _ Eρ (Hpath Γ HcΓ0 ρ')). }
  (* the stored member, read at the arguments *)
  assert (Hdesc : forall x R A, set_member_known Θs Ξs Γ (me_apps (qname_mod p) Ns) x ->
            mdenote gc_deps gc_stack Γ (me_mem (me_apps (qname_mod p) Ns) x) R -> mdesc_type R = Some A ->
            exists Φ1 R0 R1 A0 i, set_filed_mod T γ Ξs p Tl Φ1 /\ mdesc_term_part_ats R0 Ns = Some R1 /\
              set_filed_term_with T γ p Tl x R0 A0 i /\ mdesc_kind R = mdesc_kind R0 /\ mdesc_kind R1 = mdesc_kind R0 /\
              mdesc_type R = mdesc_type R1 /\
              mdesc_reduct R = mdesc_reduct (mdesc_named nil Ns (apps_exp (a_mem (qname_mod p) x) Ns) R1) /\
              stored_term_member gc_stack Φ p x R0).
  { intros x R A Hkn Hm Ht.
    destruct (filed_mem_desc _ _ Hgw _ _ _ _ _ _ _ _ Hgl Hm Ht) as (R0 & R1 & HR0 & Hats & Hk & Hty & Hred).
    destruct (Hsrc _ _ Hkn HR0) as (Φ1 & HFm & HR0s).
    assert (HrR1 : mdesc_kind R1 = mdesc_kind R0).
    { assert (HR0t : exists r A1 om, R0 = mdesc_term r A1 om).
      { destruct HR0 as [Φ0 E Rx Hp He | pq k D Mk Hk0 HMk | Rr Hk0]; [| eauto | eauto].
        destruct E; cbn [entry_term] in He;
          repeat (match type of He with context [option_map _ ?o] => destruct o; cbn [option_map] in He end);
          try discriminate; injection He as <-; eauto. }
      destruct HR0t as (r & A1 & om & ->).
      destruct (mdesc_term_part_ats_term _ _ _ _ _ Hats) as (A2 & om2 & ->); reflexivity. }
    destruct (set_filed_mod_terms _ _ _ _ _ _ HFm _ _ HR0s) as (A0 & i & Hft).
    exists Φ1, R0, R1, A0, i.
    split; [exact HFm | split; [exact Hats | split; [exact Hft | split; [rewrite Hk; exact HrR1 | split; [exact HrR1 |]]]]].
    split; [rewrite Hty; apply mdesc_type_named_m | split; [exact Hred | exact HR0]]. }
  split.
  - (* a proof as its stored kind says *)
    intros κs Hκ x R A Hkn Hm Ht.
    destruct (Hdesc _ _ _ Hkn Hm Ht) as (Φ1 & R0 & R1 & A0 & i & HFm & Hats & Hft & Hk & _ & _ & _ & HR0).
    rewrite me_apps_member_proofs, (mod_qname_member_proofs _ _ (mod_qname_qname_mod p) κs (env_slot_proofs γ empty_set_env)).
    rewrite <- (set_interp_modexp_member_proofs T γ _ _ _ _ (Hpath nil (wf_ctx_empty _ _ Hgw) empty_set_env)).
    cbn [module_member_proofs].
    rewrite (set_filed_term_proofs _ _ _ _ _ _ _ _ Hft), Hk. reflexivity.
  - intros F HF x R A Hkn Hm Ht ρ Hρ.
    destruct (Hdesc _ _ _ Hkn Hm Ht) as (Φ1 & R0 & R1 & A0 & i & HFm & Hats & Hft & Hk & HkR1 & Hty & Hred & HR0).
    pose proof (set_env_rel_eq T γ _ _ _ Hρ) as Eρ.
    destruct (set_interp_me_apps_inv _ _ _ _ _ (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ)) as (m0 & ns & Hm0 & Hns & EF).
    assert (EFg : set_module_eq γ (F ρ) (set_module_global p ns)).
    { rewrite EF, <- (List.app_nil_l ns), <- apply_module_args_global.
      apply apply_module_args_resp; [exact (Hglob _ _ Eρ Hm0) | apply list_set_eq_refl]. }
    apply (set_member_values_at_resp _ _ _ _ _ _ _ (set_module_eq_sym _ _ EFg)).
    (* the arguments' instance of the telescope, and the environment of it they make *)
    pose proof (gctx_valid_syn _ _ Hgw) as Hvs.
    destruct (filed_denote _ _ Hgw _ _ _ Γ Ns Hgl) as (RK & HmK & HmodK).
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ Hw Hvs) as (_ & HRK & _).
    destruct (desc_ok_filed_args _ _ _ _ _ _ (HRK _ HmK) HmodK) as [HcTl Hargs].
    destruct Ha as [-> Hlen HTfa HTfs HNr _].
    destruct Hargs as [rest filled Hspl Hl2 _ _ Hwf Hsyn].
    destruct (app_split_length _ _ _ _ Hspl ltac:(rewrite Hl2; exact Hlen)) as [_ <-].
    pose proof (presup_modexp_eq_ctx Hw) as HcΓ.
    pose proof (set_filed_mod_tele_ctx _ _ _ _ _ _ HFm) as HCTl.
    pose proof (set_ctx_app_r T γ _ _ HCTl) as HCTf.
    pose proof (ctx_app_wf_tail _ _ Tr Tf HcTl) as HcTf.
    assert (HCΓ : set_ctx T γ (Tf ++ Γ)).
    { pose proof (set_ctx_moved T γ Hfn Hmods Tf nil Γ _ _ (set_gsub_drop _ HcΓ) HΓ ltac:(rewrite List.app_nil_r; exact HCTf)
                    ltac:(rewrite List.app_nil_r; exact HcTf)) as H. rewrite tele_sub_closed in H by exact HTfs. exact H. }
    destruct (set_gsub_closed_inst _ _ _ HΓ HTfa HCΓ Hwf (eq_sym Hlen) Hsyn HNr) as (Fι & Hι & Hvals).
    destruct (set_closed_inst_env _ _ _ _ Hι HΓ HCTf HTfs HcTf Hwf _ Hρ) as [Hρ2 Hv2].
    set (ρ2 := set_env_moved (List.length Tf) (set_env_drop (List.length Γ)) (Fι ρ)) in *.
    assert (Ens : list_set_eq ns (set_env_values Tf ρ2)) by (rewrite Hv2; exact (Hvals _ _ Hρ Hns)).
    (* the stored member's type, the [Π] over the rest of the telescope *)
    destruct (set_filed_term_reads _ _ _ _ _ _ _ _ Hft Ns R1 Tr Tf eq_refl Hlen Hats) as [HtyR1 Hred1].
    rewrite Hty, HtyR1 in Ht. injection Ht as <-.
    destruct (set_filed_term_typed _ _ _ _ _ _ _ _ Hft) as (FS & FA0 & FA0' & [_ HA0 _ _ _]).
    destruct (proj1 (List.Forall_app _ _ _) (set_filed_mod_tele_assumptions _ _ _ _ _ _ HFm)) as [HTra _].
    destruct (set_ctx_pi_denotes _ _ (mdesc_kind R0) _ _ HTra HCTl HcTl HA0) as (FX & HX).
    pose proof (set_filed_mod_tele_scoped _ _ _ _ _ _ HFm) as HTls. apply ctx_scoped_app_iff in HTls as [HTrs _].
    pose proof (set_filed_term_scoped _ _ _ _ _ _ _ _ Hft) as HA0s. rewrite List.length_app in HA0s.
    pose proof (ctx_pi_scoped (mdesc_kind R0) _ _ _ HTrs HA0s) as HXs.
    set (g := snd (global_term γ (qname_in p x))) in *.
    assert (Eg : set_eq (select_term γ (set_module_global p ns) x) (apply_values g (set_env_values Tf ρ2)))
      by (apply apply_values_resp; [apply set_eq_refl | exact Ens]).
    constructor.
    + intros a Ha.
      pose proof (set_closed_inst_transport _ _ _ _ _ _ Hι HΓ HCTf HTfs HcTf HCΓ Hwf HXs HX _ _ Hρ Ha) as Ea.
      eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_eq_sym _ _ Ea) |].
      eapply set_mem_eq_l; [apply set_eq_sym; exact Eg |].
      exact (set_filed_term_value _ _ _ _ _ _ _ _ Hft Tr Tf ρ2 _ eq_refl Hρ2 (set_denotes_exists _ _ _ _ _ HX _ Hρ2)).
    + intros N n HN Hn. rewrite Hred in HN.
      destruct Hred1 as [HN1 | (M1 & [Hread Hvalid HM1s Hval])].
      * (* no stored reduct: the member read by name, or none *)
        assert (HR1t : exists r1 A1, R1 = mdesc_term r1 A1 None).
        { assert (HR0t : exists r A1 om, R0 = mdesc_term r A1 om).
          { destruct HR0 as [Φ0 E Rx Hp He | pq k D Mk Hk0 HMk | Rr Hk0]; [| eauto | eauto].
            destruct E; cbn [entry_term] in He;
              repeat (match type of He with context [option_map _ ?o] => destruct o; cbn [option_map] in He end);
              try discriminate; injection He as <-; eauto. }
          destruct HR0t as (r & A1 & om & ->). destruct (mdesc_term_part_ats_term _ _ _ _ _ Hats) as (A2 & om2 & ->).
          cbn in HN1. subst om2. eauto. }
        destruct HR1t as (r1 & A1 & ->).
        destruct (mdesc_named_term_none nil Ns (apps_exp (a_mem (qname_mod p) x) Ns) r1 A1) as [(E & _ & _) | E];
          rewrite E in HN; cbn in HN; [discriminate |]. injection HN as <-.
        destruct (set_interp_apps_inv _ _ _ _ _ Hn) as (v0 & ns' & Hv0 & Hns' & ->).
        inversion Hv0; subst.
        match goal with Hm1 : set_interp_modexp _ _ _ _ (qname_mod p) ?m1 |- _ => pose proof (Hglob _ _ Eρ Hm1) as Em1 end.
        pose proof (proj1 (proj2 (set_interp_functional_all T γ Hfn Hmods)) _ _ _ _ Hns _ _ Eρ Hns') as Ens'.
        cbn [select_term]. apply apply_values_resp; [| exact Ens'].
        apply set_eq_sym. exact (select_term_resp γ _ _ Em1 x).
      * (* a stored reduct, instantiated *)
        rewrite (mdesc_reduct_named_some _ _ _ _ _ Hread) in HN. injection HN as <-.
        destruct Hvalid as (FS' & FM1 & FM1' & [_ HM1 _ _ _]).
        pose proof (set_closed_inst_transport _ _ _ _ _ _ Hι HΓ HCTf HTfs HcTf HCΓ Hwf HM1s HM1 _ _ Hρ Hn) as En.
        eapply set_eq_trans; [exact Eg |].
        eapply set_eq_trans; [apply set_eq_sym; exact (Hval _ _ Hρ2 (set_denotes_exists _ _ _ _ _ HM1 _ Hρ2)) |].
        exact (set_eq_sym _ _ En).
    + intros Ekind. rewrite Hk in Ekind. cbn [select_term].
      exact (apply_values_empty _ _ (set_filed_term_proof _ _ _ _ _ _ _ _ Hft Ekind)).
Qed.

(** The δ-reduct of a typed description is of its type. *)
Lemma desc_ok_reduct_typed : forall Γ R A M, desc_ok gc_deps gc_stack Γ R -> mdesc_type R = Some A -> mdesc_reduct R = Some M ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ M : A.
Proof.
  intros * Hd Ht Hr.
  destruct Hd as [Γ r A0 om i HA0 HM | | | Γ Θd A0 M0 Rm lΘ iA HΘd HaΘd HBt HMt _]; cbn in Ht, Hr; try discriminate.
  - injection Ht as <-; exact (HM _ Hr).
  - injection Ht as <-; injection Hr as <-.
    exact (ctx_fn_at_wf _ _ ak_relevant _ _ _ _ _ ltac:(discriminate) HΘd HBt HMt).
Qed.

(** The reduct of a term member of a filed module at valid arguments
    denotes: the member read by name at the arguments, or the stored
    reduct instantiated by them. *)
Lemma set_filed_members_denote : forall Γ p Tl Φ Tr Tf Ns,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns ->
    gc_loc gc_deps gc_stack p = Some (Tl, Φ) -> set_ctx T γ Γ -> set_args_valid T γ Γ Tl Tr Tf Ns ->
    set_members_denote Γ (me_apps (qname_mod p) Ns).
Proof.
  intros * Hw Hgl HΓ Ha x R A Hkn Hm Ht.
  destruct (filed_mem_desc _ _ Hgw _ _ _ _ _ _ _ _ Hgl Hm Ht) as (R0 & R1 & HR0 & Hats & _ & Hty & Hred).
  (* the member, as the smaller context has it stored in a body it files *)
  destruct (filed_denote _ _ Hgw _ _ _ Γ Ns Hgl) as (RK0 & HmK0 & HmodK0).
  destruct (set_member_known_stored _ _ _ _ _ _ _ _ _ Hkn HmK0 HmodK0 Hgl HR0) as (Φ1 & Hl1 & HR0s).
  pose proof (set_source_filed _ _ _ Hl1) as HFm.
  destruct (set_filed_mod_terms _ _ _ _ _ _ HFm _ _ HR0s) as (A0 & i & Hft).
  (* the arguments' instance of the telescope, as for the members' values *)
  pose proof (gctx_valid_syn _ _ Hgw) as Hvs.
  destruct (filed_denote _ _ Hgw _ _ _ Γ Ns Hgl) as (RK & HmK & HmodK).
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ Hw Hvs) as (_ & HRK & _).
  destruct (desc_ok_filed_args _ _ _ _ _ _ (HRK _ HmK) HmodK) as [HcTl Hargs].
  destruct Ha as [-> Hlen HTfa HTfs HNs _].
  destruct Hargs as [rest filled Hspl Hl2 _ _ Hwf Hsyn].
  destruct (app_split_length _ _ _ _ Hspl ltac:(rewrite Hl2; exact Hlen)) as [_ <-].
  pose proof (presup_modexp_eq_ctx Hw) as HcΓ.
  pose proof (set_filed_mod_tele_ctx _ _ _ _ _ _ HFm) as HCTl.
  pose proof (set_ctx_app_r T γ _ _ HCTl) as HCTf.
  pose proof (ctx_app_wf_tail _ _ Tr Tf HcTl) as HcTf.
  assert (HCΓ : set_ctx T γ (Tf ++ Γ)).
  { pose proof (set_ctx_moved T γ Hfn Hmods Tf nil Γ _ _ (set_gsub_drop _ HcΓ) HΓ ltac:(rewrite List.app_nil_r; exact HCTf)
                  ltac:(rewrite List.app_nil_r; exact HcTf)) as H. rewrite tele_sub_closed in H by exact HTfs. exact H. }
  destruct (set_gsub_closed_inst _ _ _ HΓ HTfa HCΓ Hwf (eq_sym Hlen) Hsyn HNs) as (Fι & Hι & _).
  destruct (set_filed_term_reads _ _ _ _ _ _ _ _ Hft Ns R1 Tr Tf eq_refl Hlen Hats) as [HtyR1 Hred1].
  split.
  { (* the type: the [Π] over the rest of the telescope, instantiated *)
    rewrite Hty, mdesc_type_named_m, HtyR1 in Ht. injection Ht as <-.
    destruct (set_filed_term_typed _ _ _ _ _ _ _ _ Hft) as (FS & FA0 & FA0' & [_ HA0 _ _ _]).
    destruct (proj1 (List.Forall_app _ _ _) (set_filed_mod_tele_assumptions _ _ _ _ _ _ HFm)) as [HTra _].
    destruct (set_ctx_pi_denotes _ _ (mdesc_kind R0) _ _ HTra HCTl HcTl HA0) as (FX & HX).
    pose proof (set_filed_mod_tele_scoped _ _ _ _ _ _ HFm) as HTls. apply ctx_scoped_app_iff in HTls as [HTrs _].
    pose proof (set_filed_term_scoped _ _ _ _ _ _ _ _ Hft) as HA0s. rewrite List.length_app in HA0s.
    pose proof (ctx_pi_scoped (mdesc_kind R0) _ _ _ HTrs HA0s) as HXs.
    exact (ex_intro _ _ (set_closed_inst_denotes _ _ _ _ _ _ Hι HΓ HCTf HTfs HcTf HCΓ Hwf HXs HX)). }
  intros M HM.
  pose proof (desc_ok_reduct_typed _ _ _ _ (mem_desc_ok _ _ _ _ _ _ _ Hvs Hw Hm) Ht HM) as HMt.
  rewrite Hred in HM.
  destruct Hred1 as [HN1 | (M1 & [Hread Hvalid HM1s _])].
  - (* no stored reduct: the member read by name at the arguments *)
    assert (HR1t : exists r1 A1, R1 = mdesc_term r1 A1 None).
    { assert (HR0t : exists r A1 om, R0 = mdesc_term r A1 om).
      { destruct HR0 as [Φ0 E Rx Hp He | pq k D Mk Hk0 HMk | Rr Hk0]; [| eauto | eauto].
        destruct E; cbn [entry_term] in He;
          repeat (match type of He with context [option_map _ ?o] => destruct o; cbn [option_map] in He end);
          try discriminate; injection He as <-; eauto. }
      destruct HR0t as (r & A1 & om & ->). destruct (mdesc_term_part_ats_term _ _ _ _ _ Hats) as (A2 & om2 & ->).
      cbn in HN1. subst om2. eauto. }
    destruct HR1t as (r1 & A1 & ->).
    destruct (mdesc_named_term_none nil Ns (apps_exp (a_mem (qname_mod p) x) Ns) r1 A1) as [(E & _ & _) | E];
      rewrite E in HM; cbn in HM; [discriminate |]. injection HM as <-.
    pose proof (set_interp_filed_path set_target_bodies _ HcΓ _ _ _ (gc_loc_loc _ _ _ _ _ Hgl)) as Hpath.
    assert (HN : forall k N, List.nth_error Ns k = Some N -> exists FN, set_denotes T γ Γ N FN).
    { intros k N HN.
      destruct (List.nth_error (tele_insts Tf sb_id Ns) k) as [B |] eqn:EB.
      - destruct (HNs _ _ _ HN EB) as (FB & FN & FN' & [_ HFN _ _ _]). exists FN. exact HFN.
      - exfalso. apply List.nth_error_None in EB. rewrite length_tele_insts in EB by exact HTfa.
        assert (Hk : k < List.length Ns) by (apply List.nth_error_Some; congruence). lia. }
    destruct (set_denotes_list _ _ HN) as (Fs & HFs).
    exists (fun ρ => apply_values (select_term γ (set_module_global p nil) x) (Fs ρ)).
    apply (set_denotes_of_exists T γ Hfn Hmods _ _ _ HΓ). intros ρ Hρ.
    destruct (wf_apps_exp_head _ _ _ _ _ _ HMt) as (T0 & HT0).
    apply set_interp_apps; [econstructor; [exact (Hpath ρ) | exact HT0] | exact (HFs _ Hρ)].
  - (* a stored reduct, instantiated by the arguments *)
    rewrite (mdesc_reduct_named_some _ _ _ _ _ Hread) in HM. injection HM as <-.
    destruct Hvalid as (FS' & FM1 & FM1' & [_ HM1 _ _ _]).
    exact (ex_intro _ _ (set_closed_inst_denotes _ _ _ _ _ _ Hι HΓ HCTf HTfs HcTf HCΓ Hwf HM1s HM1)).
Qed.

(** A filed module read bare. *)
Lemma set_filed_members_bare : forall Γ p T0 Φ0, ⊢ gc_deps ⍮ gc_stack ⍮ Γ -> set_ctx T γ Γ ->
    gc_loc gc_deps gc_stack p = Some (T0, Φ0) -> set_members_all Γ (qname_mod p).
Proof.
  intros * Hc HΓ Hgl.
  assert (Hl : loc gc_deps gc_stack p T0 Φ0)
    by (unfold gc_loc in Hgl; destruct (gc_frame gc_stack p) eqn:E; [injection Hgl as ->; left; exact E | right; exact Hgl]).
  pose proof (loc_modexp_wf _ _ _ Hc _ _ _ Hl) as Hw.
  assert (Ha : set_args_valid T γ Γ T0 T0 nil nil).
  { constructor; [rewrite List.app_nil_r; reflexivity | reflexivity | constructor | exact I
                 | intros [| k] N A HN; discriminate | intros [| k] A HA; discriminate]. }
  destruct (set_filed_members Γ p T0 Φ0 T0 nil nil Hw Hgl HΓ Ha) as [Hp Hv].
  constructor; [exact Hp | exact Hv | exact (set_filed_members_denote Γ p T0 Φ0 T0 nil nil Hw Hgl HΓ Ha)].
Qed.

(** ** Members of Module Expressions Equal to Valid Units *)

(** A term member of a module expression is its unit's, of the same
    module part, or the type former of an open frame it names, filed at
    the frame's path. *)
Lemma set_modexp_member_cases : forall Γ H K R0 Rm RK x R A, set_modexp_valid_with T γ Γ H K R0 Rm RK ->
    mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A ->
    (exists p T0 Φ0, gc_loc gc_deps gc_stack p = Some (T0, Φ0) /\ H = qname_mod p) \/ mdenote gc_deps gc_stack Γ (me_mem K x) R.
Proof.
  intros * [HwH HmH HmodH _ HmK HmodK _] Hm Ht.
  assert (Hframe : forall pq, mod_qname (me_mem H x) = Some pq -> (exists U T1, gs_find_tele gc_stack pq = Some (U, nil, T1)) ->
            exists p T0 Φ0, gc_loc gc_deps gc_stack p = Some (T0, Φ0) /\ H = qname_mod p).
  { intros pq Hq (U & T1 & Ht0). cbn in Hq. destruct (mod_qname H) as [mq |] eqn:Hq0; [| discriminate]. injection Hq as <-.
    change {| q_unit := q_unit mq; q_chain := q_chain mq ++ x :: nil |} with (qname_in mq x) in Ht0.
    destruct (frame_parent _ _ Hgw _ _ _ _ Ht0) as (Tq & Φq & Hfq & _).
    exists mq, Tq, Φq. split; [unfold gc_loc; rewrite Hfq; reflexivity | exact (mod_qname_inv _ _ Hq0)]. }
  inversion Hm as [? ? ? ? ? _ _ | ? ? ? pq k D ? ? ? Hq Hk | | | | ? ? ? R1 R1m Γy E rd R2 ? Hm1 Hmd1 He Hed Hr
                  | ? ? ? Rr ? ? Hq Hk]; subst.
  - cbn in Ht. discriminate.
  - left. exact (Hframe _ Hq (gs_find_ind_tele _ _ _ Hk)).
  - right. pose proof (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ Hm1 _ HmH) as ->.
    rewrite HmodH in Hmd1. injection Hmd1 as <-.
    eapply mdenote_mem; [exact HmK | exact HmodK | exact He | exact Hed | exact Hr].
  - left. exact (Hframe _ Hq (gs_find_record_tele _ _ _ Hk)).
Qed.

Lemma set_valid_modexp_wf : forall Γ H, set_valid_modexp T γ Γ H -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros * HH. destruct HH as [? ? ? ? ? ? [Hw _ _ _ _ _ _] _]. exact Hw. Qed.

Lemma set_valid_unit_ctx : forall Γ K, set_valid_unit T γ Γ K -> set_ctx T γ Γ.
Proof. intros * HK. destruct HK as [? ? ? ? ? ? ? _ _ HΓ _ | ? ? ? ? [_ _ _ _ HΓ] _ _ | ? ? ? [_ _ _ HΓ] _]; exact HΓ. Qed.

(** A member [Θs ⍮ Ξs] has of a module expression equal to a unit is
    one it has of the unit: the two share their module part. *)
Lemma set_member_known_unit : forall Γ H K R0 Rm RK x, set_modexp_valid_with T γ Γ H K R0 Rm RK ->
    set_member_known Θs Ξs Γ H x -> set_member_known Θs Ξs Γ K x.
Proof.
  intros * [_ HmH HmodH _ HmK HmodK _] Hk RK' RKm HmK' HmodK'.
  rewrite (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ HmK' _ HmK), HmodK in HmodK'. injection HmodK' as <-.
  exact (Hk _ _ HmH HmodH).
Qed.

(** The members of a module expression equal to a valid unit are the
    unit's, or a frame's filed members. *)
Lemma set_modexp_members : forall Γ H K R0 Rm RK, set_modexp_valid_with T γ Γ H K R0 Rm RK -> set_members_all Γ K ->
    (forall p T0 Φ0, gc_loc gc_deps gc_stack p = Some (T0, Φ0) -> set_members_all Γ (qname_mod p)) ->
    set_members_all Γ H.
Proof.
  intros * Hv [IHp IHv IHr] Hfiled. pose proof Hv as [_ _ _ (F1 & FK & [HF1 HFK E1K]) _ _ Hpf].
  constructor.
  - intros κs Hκ x R A Hkn Hm Ht.
    destruct (set_modexp_member_cases _ _ _ _ _ _ _ _ _ Hv Hm Ht) as [(p & T0 & Φ0 & Hl & ->) | HmK].
    + exact (set_members_all_proofs _ _ (Hfiled _ _ _ Hl) _ Hκ _ _ _ Hkn Hm Ht).
    + rewrite (Hpf _ Hκ). exact (IHp _ Hκ _ _ _ (set_member_known_unit _ _ _ _ _ _ _ Hv Hkn) HmK Ht).
  - intros F HF x R A Hkn Hm Ht ρ Hρ.
    destruct (set_modexp_member_cases _ _ _ _ _ _ _ _ _ Hv Hm Ht) as [(p & T0 & Φ0 & Hl & ->) | HmK].
    + exact (set_members_all_values _ _ (Hfiled _ _ _ Hl) _ HF _ _ _ Hkn Hm Ht _ Hρ).
    + apply (set_member_values_at_resp _ _ (FK ρ));
        [| exact (IHv _ HFK _ _ _ (set_member_known_unit _ _ _ _ _ _ _ Hv Hkn) HmK Ht _ Hρ)].
      apply set_module_eq_sym. eapply set_module_eq_trans; [| exact (E1K _ Hρ)].
      apply set_module_eq_sym. exact (set_modexp_denotes_unique _ _ _ _ _ HF _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HF1 _ Hρ)).
  - intros x R A Hkn Hm Ht.
    destruct (set_modexp_member_cases _ _ _ _ _ _ _ _ _ Hv Hm Ht) as [(p & T0 & Φ0 & Hl & ->) | HmK].
    + exact (set_members_all_denote _ _ (Hfiled _ _ _ Hl) _ _ _ Hkn Hm Ht).
    + exact (IHr _ _ _ (set_member_known_unit _ _ _ _ _ _ _ Hv Hkn) HmK Ht).
Qed.

(** ** The Term Members of Valid Units *)

(** [set_names_filed Γ H]: when [H]'s module part is a filed module read
    bare, [H]'s modules are that module's. *)
Definition set_names_filed (Γ : ctx) (H : modexp) : Prop :=
  forall RH p T0 Φ0, mdenote gc_deps gc_stack Γ H RH -> mdesc_mod RH = Some (mdesc_closed nil p T0 Φ0 nil) ->
    forall F, set_modexp_denotes T γ Γ H F -> forall ρ, set_env_in T γ Γ ρ ->
    forall m, set_interp_modexp T γ Γ ρ (qname_mod p) m -> set_module_eq γ (F ρ) m.

Theorem set_valid_unit_members_all :
  (forall Γ K, set_valid_unit T γ Γ K -> set_members_all Γ K /\ set_names_filed Γ K) /\
  (forall Γ H, set_valid_modexp T γ Γ H -> set_members_all Γ H /\ set_names_filed Γ H).
Proof.
  apply (set_valid_unit_modexp_ind T γ).
  - (* a filed module at arguments *)
    intros Γ p T0 Φ Tr Tf Ns Hw Hgl HΓ Ha.
    split; [destruct (set_filed_members _ _ _ _ _ _ _ Hw Hgl HΓ Ha) as [Hp Hv];
            constructor; [exact Hp | exact Hv | exact (set_filed_members_denote _ _ _ _ _ _ _ Hw Hgl HΓ Ha)] |].
    intros RH q T1 Φ1 HmK Hmod F HF ρ Hρ m Hm.
    destruct (filed_denote _ _ Hgw _ _ _ Γ Ns Hgl) as (R2 & Hm2 & Hmod2).
    pose proof (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ HmK _ Hm2) as ->.
    rewrite Hmod2 in Hmod. injection Hmod as -> _ _ ->. cbn [me_apps] in HF.
    exact (set_module_eq_sym _ _ (set_modexp_denotes_unique _ _ _ _ _ HF _ _ _ Hρ Hm)).
  - (* a body *)
    intros Γ Δ Φ Φx Hok' _ _ _ _. destruct (set_body_members _ _ _ _ Hok') as [Hbp Hbv].
    split; [constructor; [intros κs _ x R A _; exact (Hbp κs x R A) | exact Hbv | exact (set_body_members_denote _ _ _ _ Hok')] |].
    intros RH q T1 Φ1 HmK Hmod.
    inversion HmK; subst; try (match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end).
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
    match goal with Hb : mdesc_body _ _ _ _ _ = Some _ |- _ => cbn in Hb; injection Hb as <- end. discriminate.
  - (* an alias *)
    intros Γ Δ E Hok' HEv [IHEm IHEn].
    pose proof (set_valid_modexp_wf _ _ HEv) as HwE.
    split.
    + destruct (set_alias_members _ _ _ Hok' HwE (set_members_all_proofs _ _ IHEm) (set_members_all_values _ _ IHEm)) as [Hap Hav].
      { intros x RE p T0 Φ0 r A0 HmE HmodE Hm'. split; [exact (proj2 (bare_member_typed _ _ _ _ _ _ _ _ _ HwE HmE HmodE Hm')) |].
        intros FE HFE ρ' Hρ' m Hm. exact (IHEn _ _ _ _ HmE HmodE _ HFE _ Hρ' _ Hm). }
      constructor; [exact Hap | exact Hav | exact (set_alias_members_denote _ _ _ Hok' HwE (set_members_all_denote _ _ IHEm))].
    + intros RH q T1 Φ1 HmK Hmod F HF ρ Hρ m Hm.
      inversion HmK; subst; try (match goal with Hq : mod_qname (me_lit _) = Some _ |- _ => cbn in Hq; discriminate end).
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu as [| ? ? ? ? RE' R' HmE' HmodE']; subst end.
      pose proof (mdesc_mod_is_mod _ _ HmodE') as HisR'.
      destruct R' as [| | Θ' p' T' Φ' Ns' |]; cbn in HisR', Hmod; try contradiction; try discriminate.
      injection Hmod as EΘ -> -> -> ->. destruct Θ', Δ; try discriminate. cbn [List.app] in *.
      destruct Hok' as [_ _ _ _ _ _ (FE & FE' & [HFE _ _])].
      pose proof (set_modexp_denotes_exists _ _ _ _ _ HF _ Hρ) as HFρ. apply set_interp_me_lit_iff in HFρ.
      inversion HFρ; subst. cbn [List.rev List.app] in *.
      match goal with HL : set_interp_unit_params _ _ _ _ _ nil _ _ |- _ => inversion HL; subst end.
      match goal with HD : set_interp_moddef _ _ _ _ (md_alias E) _ |- _ => inversion HD; subst end.
      eapply set_module_eq_trans; [| exact (IHEn _ _ _ _ HmE' HmodE' _ HFE _ Hρ _ Hm)].
      apply (set_modexp_denotes_unique _ _ _ _ _ HFE _ _ _ Hρ). assumption.
  - (* a module expression equal to a valid unit *)
    intros Γ H K R0 Rm RK Hv HK [IHKm IHKn]. pose proof Hv as [HwH HmH HmodH (F1 & FK & [HF1 HFK E1K]) HmK HmodK _].
    pose proof (presup_modexp_eq_ctx HwH) as Hc. pose proof (set_valid_unit_ctx _ _ HK) as HΓ.
    split; [exact (set_modexp_members _ _ _ _ _ _ Hv IHKm (fun p T0 Φ0 Hgl => set_filed_members_bare _ _ _ _ Hc HΓ Hgl)) |].
    intros RH q T1 Φ1 HmH' Hmod F HF ρ Hρ m Hm.
    pose proof (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ HmH' _ HmH) as ->. rewrite HmodH in Hmod. injection Hmod as ->.
    eapply set_module_eq_trans; [| exact (IHKn _ _ _ _ HmK HmodK _ HFK _ Hρ _ Hm)].
    eapply set_module_eq_trans; [| exact (E1K _ Hρ)].
    apply set_module_eq_sym. exact (set_modexp_denotes_unique _ _ _ _ _ HF _ _ _ Hρ (set_modexp_denotes_exists _ _ _ _ _ HF1 _ Hρ)).
Qed.

(** The term members of a valid module expression are of their types, and
    are their reducts, at every environment of a denotation of it. *)
Corollary set_valid_modexp_members : forall Γ H F, set_valid_modexp T γ Γ H -> set_modexp_denotes T γ Γ H F ->
    set_members_valid T γ Θs Ξs Γ H F.
Proof.
  intros * HH HF.
  exact (set_members_valid_of_values _ _ _ (set_members_all_values _ _ (proj1 (proj2 set_valid_unit_members_all _ _ HH)) _ HF)).
Qed.

(** The reducts of the term members of a valid module expression denote. *)
Corollary set_valid_modexp_members_denote : forall Γ H, set_valid_modexp T γ Γ H -> set_members_denote Γ H.
Proof. intros * HH. exact (set_members_all_denote _ _ (proj1 (proj2 set_valid_unit_members_all _ _ HH))). Qed.

End MemberTypes.
