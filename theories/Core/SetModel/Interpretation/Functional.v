(** * The Set Interpretation Is Functional

    Two derivations of a term, a module expression, a unit or a body, at
    environments with equal entries, give equal values
    ([set_interp_functional]).  Whether a λ is a proof is read off its
    typing; that two typings of a λ give it the same kinds is a hypothesis
    ([fn_kinds_unique]), a consequence of the NbE theorems.  A module
    applied outside its parameter's type is guarded ([set_module_cond]),
    so no other premise depends on more than the values. *)

From Stdlib Require Import String List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation Require Export Respects.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions.
Import ListNotations.

(** Two named lists of sets with the same names, in order, and equal
    values. *)
Definition fields_set_eq (fs fs' : list (string * aczel_set)) : Prop :=
  Forall2 (fun f f' => fst f = fst f' /\ set_eq (snd f) (snd f')) fs fs'.

Lemma tuple_code_resp : forall fs fs', fields_set_eq fs fs' -> set_eq (tuple_code fs) (tuple_code fs').
Proof.
  intros fs fs' H. unfold tuple_code. apply set_of_list_resp.
  induction H as [| [f v] [f' v'] fs fs' [Ef Ev] _ IH]; cbn in *; constructor; [| exact IH].
  subst f'. apply ordered_pair_resp; [apply set_eq_refl | exact Ev].
Qed.

Lemma tuple_field_resp : forall t t' f, set_eq t t' -> set_eq (tuple_field t f) (tuple_field t' f).
Proof. intros. unfold tuple_field. apply set_apply_resp; [assumption | apply set_eq_refl]. Qed.

Lemma set_entry_value_eq : forall e e', set_entry_eq e e' -> set_eq (set_entry_value e) (set_entry_value e').
Proof. exact set_entry_value_resp. Qed.

Section Functional.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** Two typings of a λ give it the same kinds. *)
Definition fn_kinds_unique : Prop :=
  forall Γ A M κd κc C B κd' κc' C' B', gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_fn A M : a_pi κd κc C B ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_fn A M : a_pi κd' κc' C' B' -> κd = κd' /\ κc = κc'.

  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq (global_module γ q) (global_module γ q).

Lemma universe_code_resp : forall l l' U U', set_eq l l' -> set_eq U U' -> set_eq (universe_code l U) (universe_code l' U').
Proof.
  intros * El EU. unfold universe_code. apply type_code_resp; [exact El |].
  apply separation_set_resp; [exact is_relevant_code_resp | exact is_relevant_code_resp | exact EU | tauto].
Qed.

Lemma set_members_eq_app : forall ms ms' ns ns', set_members_eq ms ms' -> set_members_eq ns ns' -> set_members_eq (ms ++ ns) (ms' ++ ns').
Proof. intros * H Hn. induction H; cbn; [exact Hn | constructor; assumption]. Qed.

Lemma list_set_eq_nth : forall l l' i d, list_set_eq l l' -> set_eq (List.nth i l d) (List.nth i l' d).
Proof. intros l l' i d H. revert i. induction H as [| x y l l' E _ IH]; intros [| i]; cbn; auto using set_eq_refl. Qed.

Lemma list_set_eq_map_tuple_field : forall fl v v', set_eq v v' ->
    list_set_eq (List.map (tuple_field v) fl) (List.map (tuple_field v') fl).
Proof. intros fl v v' E. induction fl; constructor; [apply tuple_field_resp; exact E | assumption]. Qed.

Lemma set_env_eq_extend : forall ρ ρ' e e', set_env_eq ρ ρ' -> set_entry_eq e e' -> set_env_eq (set_env_extend ρ e) (set_env_extend ρ' e').
Proof. exact set_env_extend_resp. Qed.

(** ** Functionality Across Related Contexts

    The values of a term read in two contexts related by [R] at equal
    environments are equal, when two typings of a λ in related contexts
    give it the same kinds and the relation survives growing both contexts
    by the same entries.  The same context ([R := eq]) is the instance of
    [set_interp_functional]; contexts extending one context by equal
    extensions are the other ([ContextRelation]). *)
Section Related.
  Variable R : ctx -> ctx -> Prop.
  (** Two typings of a λ in related contexts give it the same kinds *)
  Hypothesis R_fn_kinds : forall Δ Δ' A M κd κc C B κd' κc' C' B', R Δ Δ' ->
    gc_deps ⍮ gc_stack ⍮ Δ ⊢ a_fn A M : a_pi κd κc C B ->
    gc_deps ⍮ gc_stack ⍮ Δ' ⊢ a_fn A M : a_pi κd' κc' C' B' -> κd = κd' /\ κc = κc'.
  (** Related contexts grown by the same entries are related *)
  Hypothesis R_extend : forall Δ Δ' Φ, R Δ Δ' ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Φ ++ Δ -> ⊢ gc_deps ⍮ gc_stack ⍮ Φ ++ Δ' -> R (Φ ++ Δ) (Φ ++ Δ').

Lemma R_extend_one : forall Δ Δ' e, R Δ Δ' -> ⊢ gc_deps ⍮ gc_stack ⍮ e :: Δ -> ⊢ gc_deps ⍮ gc_stack ⍮ e :: Δ' ->
    R (e :: Δ) (e :: Δ').
Proof. intros * HR Hc Hc'. exact (R_extend Δ Δ' [e] HR Hc Hc'). Qed.

Lemma set_interp_functional_rel_all :
  (forall Γ ρ M v, set_interp T γ Γ ρ M v -> forall Γ' ρ' v', R Γ Γ' -> set_env_eq ρ ρ' -> set_interp T γ Γ' ρ' M v' ->
     set_eq v v') /\
  (forall Γ ρ Ms vs, set_interp_list T γ Γ ρ Ms vs -> forall Γ' ρ' vs', R Γ Γ' -> set_env_eq ρ ρ' ->
     set_interp_list T γ Γ' ρ' Ms vs' -> list_set_eq vs vs') /\
  (forall Γ ρ fs vs, set_interp_fields T γ Γ ρ fs vs -> forall Γ' ρ' vs', R Γ Γ' -> set_env_eq ρ ρ' ->
     set_interp_fields T γ Γ' ρ' fs vs' -> fields_set_eq vs vs') /\
  (forall Γ ρ H m, set_interp_modexp T γ Γ ρ H m -> forall Γ' ρ' m', R Γ Γ' -> set_env_eq ρ ρ' ->
     set_interp_modexp T γ Γ' ρ' H m' -> set_module_eq m m') /\
  (forall Γ ρ U m, set_interp_gunit T γ Γ ρ U m -> forall Γ' ρ' m', R Γ Γ' -> set_env_eq ρ ρ' ->
     set_interp_gunit T γ Γ' ρ' U m' -> set_module_eq m m') /\
  (forall Γ ρ P L D m, set_interp_unit_params T γ Γ ρ P L D m -> forall Γ' ρ' P' m', R Γ Γ' -> set_env_eq ρ ρ' ->
     (forall ys x, P ys x = P' ys x) -> set_interp_unit_params T γ Γ' ρ' P' L D m' -> set_module_eq m m') /\
  (forall Γ ρ D m, set_interp_moddef T γ Γ ρ D m -> forall Γ' ρ' m', R Γ Γ' -> set_env_eq ρ ρ' ->
     set_interp_moddef T γ Γ' ρ' D m' -> set_module_eq m m') /\
  (forall Γ ρ Φ ms ρo, set_interp_gmod T γ Γ ρ Φ ms ρo -> forall Γ' ρ' ms' ρo', R Γ Γ' -> set_env_eq ρ ρ' ->
     set_interp_gmod T γ Γ' ρ' Φ ms' ρo' -> set_members_eq ms ms' /\ set_env_eq ρo ρo') /\
  (forall Γ ρ E e, set_interp_gentry T γ Γ ρ E e -> forall Γ' ρ' e', R Γ Γ' -> set_env_eq ρ ρ' ->
     set_interp_gentry T γ Γ' ρ' E e' -> set_entry_eq e e') /\
  (forall Γ ρ r p Us Bks j v res, set_elim T γ Γ ρ r p Us Bks j v res -> forall Γ' ρ' v' res', R Γ Γ' -> set_env_eq ρ ρ' ->
     set_eq v v' -> set_elim T γ Γ' ρ' r p Us Bks j v' res' -> set_eq res res') /\
  (forall Γ ρ r p Us Bks gs vs ihs, set_ihs T γ Γ ρ r p Us Bks gs vs ihs -> forall Γ' ρ' vs' ihs', R Γ Γ' -> set_env_eq ρ ρ' ->
     list_set_eq vs vs' -> set_ihs T γ Γ' ρ' r p Us Bks gs vs' ihs' -> list_set_eq ihs ihs') /\
  (forall Γ ρ r p Us Bks t v ihs, set_ih T γ Γ ρ r p Us Bks t v ihs -> forall Γ' ρ' v' ihs', R Γ Γ' -> set_env_eq ρ ρ' ->
     set_eq v v' -> set_ih T γ Γ' ρ' r p Us Bks t v' ihs' -> list_set_eq ihs ihs').
Proof.
  Local Ltac inv H := inversion H; subst; clear H.
  apply (set_interp_combined_ind GC T γ).
  (** terms *)
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros Γ ρ t l _ IH Γ' ρ' v' HR He H'. inv H'. pose proof (IH _ _ _ HR He ltac:(eassumption)) as E.
    apply universe_code_resp; [exact E | apply small_universe_set_resp; exact E].
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros Γ ρ M l _ IH Γ' ρ' v' HR He H'. inv H'. apply successor_set_resp. eapply IH; eassumption.
  - intros Γ ρ M N l l' _ IH1 _ IH2 Γ' ρ' v' HR He H'. inv H'. apply union_set_resp. apply unordered_pair_set_resp;
      [eapply IH1 | eapply IH2]; eassumption.
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros Γ ρ P Q p F Hc _ IHP _ IHQ Γ' ρ' v' HR He H'. inv H'.
    pose proof (IHP _ _ _ HR He ltac:(eassumption)) as Ep.
    match goal with HQ' : forall x, set_mem x (code_carrier _) -> set_interp _ _ _ _ Q (?F0 x) |- _ =>
      assert (Eq : prop_true p -> set_eq (F empty_set) (F0 empty_set))
        by (intros Hp; eapply IHQ; [exact Hp | apply R_extend_one; [exact HR | exact Hc | eassumption]
                                   | apply set_env_eq_extend; [exact He | constructor; apply set_eq_refl]
                                   | apply HQ'; exact (prop_true_resp _ _ Ep Hp)]) end.
    apply prop_code_eq. split; intros [Hp1 Hp2]; split.
    + exact (prop_true_resp _ _ Ep Hp1).
    + exact (prop_true_resp _ _ (Eq Hp1) Hp2).
    + exact (prop_true_resp _ _ (set_eq_sym _ _ Ep) Hp1).
    + exact (prop_true_resp _ _ (set_eq_sym _ _ (Eq (prop_true_resp _ _ (set_eq_sym _ _ Ep) Hp1))) Hp2).
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros Γ ρ P M v _ IH Γ' ρ' v' HR He H'. inv H'. eapply IH; eassumption.
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros * HR He H'. inv H'; [apply set_eq_refl | contradiction].
  - intros Γ ρ r p Us m Bks M C v r0 Hr HC _ IHM _ IHE Γ' ρ' v' HR He H'. inv H'; [contradiction |].
    eapply IHE; [exact HR | exact He | eapply IHM; eassumption | eassumption].
  - intros Γ ρ κd A B a F Hc _ IHA _ IHB Γ' ρ' v' HR He H'. inv H'; [| contradiction].
    pose proof (IHA _ _ _ HR He ltac:(eassumption)) as Ea.
    apply forall_code_resp_on; [exact Ea |]. intros x x' Hx E.
    eapply IHB; [exact Hx | apply R_extend_one; [exact HR | exact Hc | eassumption]
                     | apply set_env_eq_extend; [exact He | constructor; exact E] |];
      match goal with HB' : forall y, set_mem y _ -> _ |- _ => apply HB' end; eapply set_mem_eq_l; [exact E |].
    eapply set_mem_eq_r; [apply code_carrier_resp; exact Ea | exact Hx].
  - intros Γ ρ κd κc A B a F Hκ Hc _ IHA _ IHB Γ' ρ' v' HR He H'. inv H'; [contradiction |].
    pose proof (IHA _ _ _ HR He ltac:(eassumption)) as Ea.
    apply pi_code_resp_on; [exact Ea |]. intros x x' Hx E.
    eapply IHB; [exact Hx | apply R_extend_one; [exact HR | exact Hc | eassumption]
                     | apply set_env_eq_extend; [exact He | constructor; exact E] |];
      match goal with HB' : forall y, set_mem y _ -> _ |- _ => apply HB' end; eapply set_mem_eq_l; [exact E |].
    eapply set_mem_eq_r; [apply code_carrier_resp; exact Ea | exact Hx].
  - intros Γ ρ A M κd C B HT Γ' ρ' v' HR He H'. inv H'; [apply set_eq_refl |].
    match goal with HT' : gc_deps ⍮ gc_stack ⍮ _ ⊢ a_fn _ _ : a_pi _ _ _ _, Hk : _ <> ak_propositional |- _ =>
      destruct (R_fn_kinds _ _ _ _ _ _ _ _ _ _ _ _ HR HT HT') as [_ <-]; contradiction end.
  - intros Γ ρ A M κd κc C B a F HT Hκ Hc _ IHA _ IHM Γ' ρ' v' HR He H'. inv H'.
    + match goal with HT' : gc_deps ⍮ gc_stack ⍮ _ ⊢ a_fn _ _ : a_pi _ ak_propositional _ _ |- _ =>
        destruct (R_fn_kinds _ _ _ _ _ _ _ _ _ _ _ _ HR HT HT') as [_ ->]; contradiction end.
    + match goal with HT' : gc_deps ⍮ gc_stack ⍮ _ ⊢ a_fn _ _ : a_pi ?κd' _ _ _ |- _ =>
        destruct (R_fn_kinds _ _ _ _ _ _ _ _ _ _ _ _ HR HT HT') as [<- _] end.
      pose proof (IHA _ _ _ HR He ltac:(eassumption)) as Ea.
      apply graph_set_resp_on; [apply code_carrier_resp; exact Ea |]. intros x x' Hx E.
      eapply IHM; [exact Hx | apply R_extend_one; [exact HR | exact Hc | eassumption]
                     | apply set_env_eq_extend; [exact He | constructor; exact E] |];
      match goal with HB' : forall y, set_mem y _ -> _ |- _ => apply HB' end; eapply set_mem_eq_l; [exact E |].
      eapply set_mem_eq_r; [apply code_carrier_resp; exact Ea | exact Hx].
  - intros Γ ρ M N f n _ IH1 _ IH2 Γ' ρ' v' HR He H'. inv H'. apply set_apply_resp; [eapply IH1 | eapply IH2]; eassumption.
  - intros Γ ρ x Γ' ρ' v' HR He H'. inv H'. apply set_entry_value_resp. apply He.
  - intros Γ ρ A M B v w Hc _ IHM _ IHB Γ' ρ' v' HR He H'. inv H'.
    eapply IHB; [apply R_extend_one; [exact HR | exact Hc | eassumption] | | eassumption]; apply set_env_eq_extend; [exact He | constructor; eapply IHM; eassumption].
  - intros Γ ρ U B m w Hc _ IHU _ IHB Γ' ρ' v' HR He H'. inv H'.
    eapply IHB; [apply R_extend_one; [exact HR | exact Hc | eassumption] | | eassumption]; apply set_env_eq_extend; [exact He | constructor; eapply IHU; eassumption].
  - intros Γ ρ A M U B v m w Hc _ IHM _ IHU _ IHB Γ' ρ' v' HR He H'. inv H'.
    eapply IHB; [apply R_extend_one; [exact HR | exact Hc | eassumption] | | eassumption]; apply set_env_eq_extend; [exact He | constructor; [eapply IHM | eapply IHU]; eassumption].
  - intros Γ ρ H x m _ IH Γ' ρ' v' HR He H'. inv H'. apply select_term_resp. eapply IH; eassumption.
  - intros * HR He H'. inv H'. apply set_eq_refl.
  - intros Γ ρ A fs vs _ IH Γ' ρ' v' HR He H'. inv H'. apply tuple_code_resp. eapply IH; eassumption.
  - intros Γ ρ f M v _ IH Γ' ρ' v' HR He H'. inv H'. apply tuple_field_resp. eapply IH; eassumption.
  (** lists and fields *)
  - intros * HR He H'. inv H'. constructor.
  - intros Γ ρ M Ms v vs _ IH1 _ IH2 Γ' ρ' vs' HR He H'. inv H'. constructor; [eapply IH1 | eapply IH2]; eassumption.
  - intros * HR He H'. inv H'. constructor.
  - intros Γ ρ f M fs v vs _ IH1 _ IH2 Γ' ρ' vs' HR He H'. inv H'. constructor; [split; [reflexivity |] |]; [eapply IH1 | eapply IH2]; eassumption.
  (** module expressions *)
  - intros * HR He H'. inv H'. constructor. constructor.
  - intros Γ ρ k Γ' ρ' m' HR He H'. inv H'. apply set_entry_module_part_resp. apply He.
  - intros Γ ρ H y m _ IH Γ' ρ' m' HR He H'. inv H'. apply select_module_resp; [exact Hmods |]. eapply IH; eassumption.
  - intros Γ ρ H N m n _ IH1 _ IH2 Γ' ρ' m' HR He H'. inv H'. apply apply_module_resp; [eapply IH1 | eapply IH2]; eassumption.
  - intros Γ ρ U m _ IH Γ' ρ' m' HR He H'. inv H'. eapply IH; eassumption.
  (** units *)
  - intros Γ ρ Δ D P m HP _ IH Γ' ρ' m' HR He H'. inv H'.
    eapply IH; [exact HR | exact He | | eassumption].
    match goal with HP' : forall ys x, ?P0 ys x = _ |- forall ys x, P ys x = ?P0 ys x =>
      intros ys x; rewrite HP, HP'; apply (proj1 (proj2 (unit_member_proofs_resp_all γ))); apply env_slot_proofs_resp; exact He end.
  - intros Γ ρ P D m _ IH Γ' ρ' P' m' HR He EP H'. inv H'. eapply IH; eassumption.
  - intros Γ ρ P κ A L D a f Hc _ IHA _ IHL Γ' ρ' P' m' HR He EP H'. inv H'.
    pose proof (IHA _ _ _ HR He ltac:(eassumption)) as Ea. constructor; [exact Ea | exact EP |]. intros x x' Hx E.
    eapply IHL; [exact Hx | apply R_extend_one; [exact HR | exact Hc | eassumption]
                     | apply set_env_eq_extend; [exact He | constructor; exact E] | exact EP |];
      match goal with HB' : forall y, set_mem y _ -> _ |- _ => apply HB' end; eapply set_mem_eq_l; [exact E |].
    eapply set_mem_eq_r; [apply code_carrier_resp; exact Ea | exact Hx].
  - intros Γ ρ P A M L D v m Hc _ IHM _ IHL Γ' ρ' P' m' HR He EP H'. inv H'.
    eapply IHL; [apply R_extend_one; [exact HR | exact Hc | eassumption] | | exact EP | eassumption];
      apply set_env_eq_extend; [exact He | constructor; eapply IHM; eassumption].
  - intros Γ ρ P U L D mu m Hc _ IHU _ IHL Γ' ρ' P' m' HR He EP H'. inv H'.
    eapply IHL; [apply R_extend_one; [exact HR | exact Hc | eassumption] | | exact EP | eassumption];
      apply set_env_eq_extend; [exact He | constructor; eapply IHU; eassumption].
  - intros Γ ρ P A M U L D v mu m Hc _ IHM _ IHU _ IHL Γ' ρ' P' m' HR He EP H'. inv H'.
    eapply IHL; [apply R_extend_one; [exact HR | exact Hc | eassumption] | | exact EP | eassumption];
      apply set_env_eq_extend; [exact He | constructor; [eapply IHM | eapply IHU]; eassumption].
  (** definitions *)
  - intros Γ ρ sm Φ ms ρo _ IH Γ' ρ' m' HR He H'. inv H'. constructor. eapply IH; eassumption.
  - intros Γ ρ E m _ IH Γ' ρ' m' HR He H'. inv H'. eapply IH; eassumption.
  (** bodies *)
  - intros Γ ρ Γ' ρ' ms' ρo' HR He H'. inv H'. split; [constructor | exact He].
  - intros Γ ρ Φ x E ms ρo e Hc HΦ IHΦ _ IHE Γ' ρ' ms' ρo' HR He H'. inv H'.
    destruct (IHΦ _ _ _ _ HR He ltac:(eassumption)) as [Ems Eo].
    pose proof (IHE _ _ _ (R_extend _ _ _ HR Hc ltac:(eassumption)) Eo ltac:(eassumption)) as Ee.
    split; [apply set_members_eq_app; [exact Ems | constructor; [exact Ee | constructor]] | apply set_env_eq_extend; assumption].
  (** entries *)
  - intros Γ ρ b pv r A M v _ IH Γ' ρ' e' HR He H'. inv H'. constructor. eapply IH; eassumption.
  - intros * HR He H'. inv H'. constructor. apply set_eq_refl.
  - intros Γ ρ pv U m _ IH Γ' ρ' e' HR He H'. inv H'. constructor. eapply IH; eassumption.
  - intros Γ ρ pv A M U v m _ IHM _ IHU Γ' ρ' e' HR He H'. inv H'. constructor; [eapply IHM | eapply IHU]; eassumption.
  - intros * HR He H'. inv H'. constructor. constructor. constructor.
  - intros * HR He H'. inv H'. constructor. constructor. constructor.
  (** the eliminator *)
  - intros Γ ρ r p Us Bks j v res D Mj pc k Dq Mk c gs ns vs nm Z A Bs n B ihs
      HD HMj Href HDq HMk Hgs Hv Hns Hvs Hb HB _ IHihs Hlen Hc _ IHB Γ' ρ' v' res' HR He Ev H'.
    inversion H' as [? ? ? ? ? ? ? ? ? D' Mj' pc' k' Dq' Mk' c' gs' ns' vs' nm' Z' A' Bs' n' B' ihs'
                     HD' HMj' Href' HDq' HMk' Hgs' Hv' Hns' Hvs' Hb' HB' Hihs' Hlen' Hc' HB'']; subst.
    rewrite HD in HD'. injection HD' as <-. rewrite HMj in HMj'. injection HMj' as <-.
    rewrite Href in Href'. injection Href' as <- <-. rewrite HDq in HDq'. injection HDq' as <-.
    rewrite HMk in HMk'. injection HMk' as <-.
    pose proof (set_eq_trans _ _ _ (set_eq_sym _ _ Hv) (set_eq_trans _ _ _ Ev Hv')) as E.
    apply ordered_pair_inj in E as [Ec El]. apply string_code_inj in Ec. subst c'.
    rewrite Hgs in Hgs'. injection Hgs' as <-. rewrite Hb in Hb'. injection Hb' as <- <- <- <-.
    rewrite HB in HB'. injection HB' as <- <-.
    apply list_code_inj in El. destruct (list_set_eq_app_split _ _ _ _ El ltac:(lia)) as [Ens Evs].
    pose proof (IHihs _ _ _ _ HR He Evs Hihs') as Eihs.
    eapply IHB; [apply R_extend; [exact HR | exact Hc | exact Hc'] | | exact HB''].
    apply set_env_extend_kinded_resp; [exact He |]. apply list_set_eq_app; [exact Ens | apply list_set_eq_app; assumption].
  - intros * HR He Ev H'. inv H'. constructor.
  - intros Γ ρ r p Us Bks κ T0 gs v vs ihs _ IH Γ' ρ' vs' ihs' HR He Ev H'. inv H'. inversion Ev; subst.
    eapply IH; eassumption.
  - intros Γ ρ r p Us Bks t gs v vs ihs1 ihs2 _ IH1 _ IH2 Γ' ρ' vs' ihs' HR He Ev H'. inv H'. inversion Ev; subst.
    apply list_set_eq_app; [eapply IH1 | eapply IH2]; eassumption.
  - intros Γ ρ r p Us Bks D j Mj Ps v r0 HD HMj Hrv _ IH Γ' ρ' v' ihs' HR He Ev H'. inv H'.
    + constructor; [| constructor]. eapply IH; eassumption.
    + exfalso. match goal with HD' : ind_lookup _ _ p = Some ?D', HM' : ind_member ?D' j = Some ?Mj', Hh : im_head ?Mj' = _ |- _ =>
        rewrite HD in HD'; injection HD' as <-; rewrite HMj in HM'; injection HM' as <-; unfold im_is_rview in Hrv; rewrite Hh in Hrv;
        discriminate end.
  - intros Γ ρ r p Us Bks D j Mj qr Is fl c gs Ps v rs HD HMj Hh Hc _ IH Γ' ρ' v' ihs' HR He Ev H'. inv H'.
    + exfalso. match goal with HD' : ind_lookup _ _ p = Some ?D', HM' : ind_member ?D' j = Some ?Mj', Hrv : im_is_rview ?Mj' = false |- _ =>
        rewrite HD in HD'; injection HD' as <-; rewrite HMj in HM'; injection HM' as <-; unfold im_is_rview in Hrv; rewrite Hh in Hrv;
        discriminate end.
    + match goal with HD' : ind_lookup _ _ p = Some ?D', HM' : ind_member ?D' j = Some ?Mj', Hh' : im_head ?Mj' = _, Hc' : im_cons ?Mj' = _ |- _ =>
        rewrite HD in HD'; injection HD' as <-; rewrite HMj in HM'; injection HM' as <-; rewrite Hh in Hh'; injection Hh' as <- <- <-;
        rewrite Hc in Hc'; injection Hc' as <- <- end.
      eapply IH; [exact HR | exact He | apply list_set_eq_map_tuple_field; exact Ev | eassumption].
  - intros Γ ρ r p Us Bks D B t v Rs HD _ IH Γ' ρ' v' ihs' HR He Ev H'. inv H'.
    match goal with HD' : ind_lookup _ _ p = Some ?D' |- _ => rewrite HD in HD'; injection HD' as <- end.
    match goal with HR : forall b, set_mem b (relation_domain v') -> set_ih _ _ _ _ _ _ _ _ _ _ (?Rs' b) |- _ =>
      rename HR into HRs'; set (Rs'0 := Rs') in * end.
    induction (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t))) as [| i is IHis]; cbn [List.map]; constructor; [| exact IHis].
    apply graph_set_resp_on; [apply relation_domain_resp; exact Ev |]. intros b b' Hb E.
    apply list_set_eq_nth. eapply IH; [exact Hb | exact HR | exact He | apply set_apply_resp; [exact Ev | exact E] |].
    apply HRs'. eapply set_mem_eq_l; [exact E |]. eapply set_mem_eq_r; [apply relation_domain_resp; exact Ev | exact Hb].
Qed.

End Related.

(** ** Functionality in One Context *)

Lemma set_interp_functional_all :
  (forall Γ ρ M v, set_interp T γ Γ ρ M v -> forall ρ' v', set_env_eq ρ ρ' -> set_interp T γ Γ ρ' M v' -> set_eq v v') /\
  (forall Γ ρ Ms vs, set_interp_list T γ Γ ρ Ms vs -> forall ρ' vs', set_env_eq ρ ρ' -> set_interp_list T γ Γ ρ' Ms vs' ->
     list_set_eq vs vs') /\
  (forall Γ ρ fs vs, set_interp_fields T γ Γ ρ fs vs -> forall ρ' vs', set_env_eq ρ ρ' -> set_interp_fields T γ Γ ρ' fs vs' ->
     fields_set_eq vs vs') /\
  (forall Γ ρ H m, set_interp_modexp T γ Γ ρ H m -> forall ρ' m', set_env_eq ρ ρ' -> set_interp_modexp T γ Γ ρ' H m' ->
     set_module_eq m m') /\
  (forall Γ ρ U m, set_interp_gunit T γ Γ ρ U m -> forall ρ' m', set_env_eq ρ ρ' -> set_interp_gunit T γ Γ ρ' U m' ->
     set_module_eq m m') /\
  (forall Γ ρ P L D m, set_interp_unit_params T γ Γ ρ P L D m -> forall ρ' P' m', set_env_eq ρ ρ' ->
     (forall ys x, P ys x = P' ys x) -> set_interp_unit_params T γ Γ ρ' P' L D m' -> set_module_eq m m') /\
  (forall Γ ρ D m, set_interp_moddef T γ Γ ρ D m -> forall ρ' m', set_env_eq ρ ρ' -> set_interp_moddef T γ Γ ρ' D m' ->
     set_module_eq m m') /\
  (forall Γ ρ Φ ms ρo, set_interp_gmod T γ Γ ρ Φ ms ρo -> forall ρ' ms' ρo', set_env_eq ρ ρ' ->
     set_interp_gmod T γ Γ ρ' Φ ms' ρo' -> set_members_eq ms ms' /\ set_env_eq ρo ρo') /\
  (forall Γ ρ E e, set_interp_gentry T γ Γ ρ E e -> forall ρ' e', set_env_eq ρ ρ' -> set_interp_gentry T γ Γ ρ' E e' ->
     set_entry_eq e e') /\
  (forall Γ ρ r p Us Bks j v res, set_elim T γ Γ ρ r p Us Bks j v res -> forall ρ' v' res', set_env_eq ρ ρ' -> set_eq v v' ->
     set_elim T γ Γ ρ' r p Us Bks j v' res' -> set_eq res res') /\
  (forall Γ ρ r p Us Bks gs vs ihs, set_ihs T γ Γ ρ r p Us Bks gs vs ihs -> forall ρ' vs' ihs', set_env_eq ρ ρ' ->
     list_set_eq vs vs' -> set_ihs T γ Γ ρ' r p Us Bks gs vs' ihs' -> list_set_eq ihs ihs') /\
  (forall Γ ρ r p Us Bks t v ihs, set_ih T γ Γ ρ r p Us Bks t v ihs -> forall ρ' v' ihs', set_env_eq ρ ρ' ->
     set_eq v v' -> set_ih T γ Γ ρ' r p Us Bks t v' ihs' -> list_set_eq ihs ihs').
Proof.
  assert (Hk : forall Δ Δ' A M κd κc C B κd' κc' C' B', Δ = Δ' ->
            gc_deps ⍮ gc_stack ⍮ Δ ⊢ a_fn A M : a_pi κd κc C B ->
            gc_deps ⍮ gc_stack ⍮ Δ' ⊢ a_fn A M : a_pi κd' κc' C' B' -> κd = κd' /\ κc = κc')
    by (intros * -> HT HT'; exact (Hfn _ _ _ _ _ _ _ _ _ _ _ HT HT')).
  assert (Hx : forall Δ Δ' Φ, Δ = Δ' -> ⊢ gc_deps ⍮ gc_stack ⍮ Φ ++ Δ -> ⊢ gc_deps ⍮ gc_stack ⍮ Φ ++ Δ' -> Φ ++ Δ = Φ ++ Δ')
    by (intros * -> _ _; reflexivity).
  destruct (set_interp_functional_rel_all eq Hk Hx)
    as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  repeat split; intros; [eapply H1 | eapply H2 | eapply H3 | eapply H4 | eapply H5 | eapply H6 | eapply H7 | eapply H8 | eapply H8
                        | eapply H9 | eapply H10 | eapply H11 | eapply H12]; eauto.
Qed.

Theorem set_interp_functional : forall Γ ρ M v, set_interp T γ Γ ρ M v ->
    forall ρ' v', set_env_eq ρ ρ' -> set_interp T γ Γ ρ' M v' -> set_eq v v'.
Proof. exact (proj1 set_interp_functional_all). Qed.

Theorem set_interp_modexp_functional : forall Γ ρ H m, set_interp_modexp T γ Γ ρ H m ->
    forall ρ' m', set_env_eq ρ ρ' -> set_interp_modexp T γ Γ ρ' H m' -> set_module_eq m m'.
Proof. exact (proj1 (proj2 (proj2 (proj2 set_interp_functional_all)))). Qed.

End Functional.
