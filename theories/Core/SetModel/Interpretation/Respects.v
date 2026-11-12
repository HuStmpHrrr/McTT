(** * The Operations on Values Respect Equality

    Reading an entry, looking up a member, extending an environment,
    applying a value and selecting a term member respect the equalities of
    values ([set_entry_eq], [set_module_eq], [set_env_eq]).  The
    uniqueness of a well-typed term's value, which these serve, is part of
    the fundamental theorem's set field. *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Interpretation Require Export Interp.
From Mctt.Core.Syntactic Require Import Syntax Substitution.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas.
Import ListNotations.

Section Operations.
  Variable γ : global_valuation.

(** ** The Equalities of Values Are Partial Equivalences *)

Scheme set_entry_eq_mut_ind := Minimality for set_entry_eq Sort Prop
with set_module_eq_mut_ind := Minimality for set_module_eq Sort Prop
with set_members_eq_mut_ind := Minimality for set_members_eq Sort Prop.
Combined Scheme set_value_eq_ind from set_entry_eq_mut_ind, set_module_eq_mut_ind, set_members_eq_mut_ind.

Lemma set_value_eq_sym :
  (forall e e', set_entry_eq γ e e' -> set_entry_eq γ e' e) /\
  (forall m m', set_module_eq γ m m' -> set_module_eq γ m' m) /\
  (forall ms ms', set_members_eq γ ms ms' -> set_members_eq γ ms' ms).
Proof.
  apply set_value_eq_ind.
  - intros κ v v' E. constructor. apply set_eq_sym. exact E.
  - intros m m' _ IH. constructor. exact IH.
  - intros v v' m m' E _ IH. constructor; [apply set_eq_sym; exact E | exact IH].
  - intros a a' P P' f f' Ea EP _ IH. constructor; [apply set_eq_sym; exact Ea | intros; symmetry; apply EP |]. intros x x' Hx E.
    apply IH; [| apply set_eq_sym; exact E].
    eapply set_mem_eq_l; [exact E |]. eapply set_mem_eq_r; [apply set_eq_sym; exact Ea | exact Hx].
  - intros ms ms' _ IH. constructor. exact IH.
  - intros p args args' E. constructor. apply list_set_eq_sym. exact E.
  - intros φ φ' P P' m m' Hφ EP _ IH. constructor; [tauto | intros; symmetry; apply EP | intros Hc; apply IH; apply Hφ; exact Hc].
  - intros φ P m m' Hφ _ IH EP. apply set_module_eq_cond_r; [exact Hφ | exact IH | exact EP].
  - intros φ P m m' Hφ _ IH EP. apply set_module_eq_cond_l; [exact Hφ | exact IH | exact EP].
  - constructor.
  - intros x e e' ms ms' _ IHe _ IHms. constructor; assumption.
Qed.

Corollary set_module_eq_sym : forall m m', set_module_eq γ m m' -> set_module_eq γ m' m.
Proof. exact (proj1 (proj2 set_value_eq_sym)). Qed.

Corollary set_entry_eq_sym : forall e e', set_entry_eq γ e e' -> set_entry_eq γ e' e.
Proof. exact (proj1 set_value_eq_sym). Qed.

(** ** The Operations Respect Equality *)

Lemma set_entry_value_resp : forall e e', set_entry_eq γ e e' -> set_eq (set_entry_value e) (set_entry_value e').
Proof. intros e e' H. destruct H; cbn [set_entry_value]; first [assumption | apply set_eq_refl]. Qed.

Lemma set_entry_module_part_resp : forall e e', set_entry_eq γ e e' ->
    set_module_eq γ (set_entry_module_part e) (set_entry_module_part e').
Proof. intros e e' H. destruct H; cbn; first [assumption | constructor; constructor]. Qed.

(** Equal tables have equal entries under every name. *)
Definition members_lookup_eq (o o' : option set_entry) : Prop :=
  match o, o' with
  | Some e, Some e' => set_entry_eq γ e e'
  | None, None => True
  | _, _ => False
  end.

Lemma members_lookup_resp : forall ms ms', set_members_eq γ ms ms' -> forall x,
    members_lookup_eq (members_lookup ms x) (members_lookup ms' x).
Proof.
  intros ms ms' H. induction H as [| y e e' ms ms' He Hms IH]; intros x; cbn; [exact I |].
  specialize (IH x). destruct (members_lookup ms x), (members_lookup ms' x); cbn in IH |- *; try contradiction; [exact IH |].
  destruct (String.eqb x y); cbn; trivial.
Qed.

Lemma set_env_extend_resp : forall ρ ρ' e e', set_env_eq γ ρ ρ' -> set_entry_eq γ e e' ->
    set_env_eq γ (set_env_extend ρ e) (set_env_extend ρ' e').
Proof. intros * Hρ He [| x]; cbn; [exact He | apply Hρ]. Qed.

Lemma set_env_extend_kinded_resp : forall vs vs' κs ρ ρ', set_env_eq γ ρ ρ' -> list_set_eq vs vs' ->
    set_env_eq γ (set_env_extend_kinded ρ κs vs) (set_env_extend_kinded ρ' κs vs').
Proof.
  intros vs vs' κs ρ ρ' Hρ H. revert κs ρ ρ' Hρ. induction H as [| v v' vs vs' Hv _ IH]; intros κs ρ ρ' Hρ; cbn; [exact Hρ |].
  apply IH. apply set_env_extend_resp; [exact Hρ | constructor; exact Hv].
Qed.

Lemma apply_values_resp : forall args args' f f', set_eq f f' -> list_set_eq args args' ->
    set_eq (apply_values f args) (apply_values f' args').
Proof.
  intros args args' f f' Hf H. revert f f' Hf. unfold apply_values.
  induction H as [| a a' args args' Ha _ IH]; intros f f' Hf; cbn [fold_left]; [exact Hf |].
  apply IH. apply set_apply_resp; assumption.
Qed.

(** Equal modules have the same members' proofness. *)
Lemma module_member_proofs_resp : forall ys m m', set_module_eq γ m m' -> forall x,
    module_member_proofs γ m ys x = module_member_proofs γ m' ys x.
Proof.
  induction ys as [| y ys IH]; intros m m' H x;
    destruct H as [a a' P P' f f' Ea EP Hf | ms ms' Hms | p args args' _ | φ φ' P P' m m' Hφ EP _
                  | φ P m m' Hφ _ EP | φ P m m' Hφ _ EP];
    try (cbn; apply EP); try (cbn; symmetry; apply EP); cbn; try reflexivity.
  - pose proof (members_lookup_resp _ _ Hms x) as E.
    destruct (members_lookup ms x) as [e |], (members_lookup ms' x) as [e' |]; cbn in E; try contradiction; [| reflexivity].
    destruct E; reflexivity.
  - pose proof (members_lookup_resp _ _ Hms y) as E.
    destruct (members_lookup ms y) as [e |], (members_lookup ms' y) as [e' |]; cbn in E; try contradiction; [| reflexivity].
    apply IH. apply set_entry_module_part_resp. exact E.
Qed.

Lemma apply_module_proofs : forall m v ys x, module_member_proofs γ (apply_module m v) ys x = module_member_proofs γ m ys x.
Proof. intros [] v [] x; reflexivity. Qed.

Lemma apply_module_args_proofs : forall args m ys x,
    module_member_proofs γ (apply_module_args m args) ys x = module_member_proofs γ m ys x.
Proof.
  induction args as [| a args IH]; intros m ys x; [reflexivity |]. unfold apply_module_args in *. cbn [fold_left].
  rewrite IH. apply apply_module_proofs.
Qed.

Lemma select_module_proofs : forall m y ys x, module_member_proofs γ (select_module γ m y) ys x = module_member_proofs γ m (y :: ys) x.
Proof.
  intros [dom P f | ms | p args | φ P m'] y ys x; cbn [select_module module_member_proofs].
  - destruct ys; reflexivity.
  - destruct (members_lookup ms y); [reflexivity | destruct ys; reflexivity].
  - apply apply_module_args_proofs.
  - destruct ys; reflexivity.
Qed.

Lemma set_value_eq_trans :
  (forall e1 e2, set_entry_eq γ e1 e2 -> forall e3, set_entry_eq γ e2 e3 -> set_entry_eq γ e1 e3) /\
  (forall m1 m2, set_module_eq γ m1 m2 -> forall m3, set_module_eq γ m2 m3 -> set_module_eq γ m1 m3) /\
  (forall ms1 ms2, set_members_eq γ ms1 ms2 -> forall ms3, set_members_eq γ ms2 ms3 -> set_members_eq γ ms1 ms3).
Proof.
  apply set_value_eq_ind.
  - intros κ v v' E e3 H. inversion H; subst. constructor. eapply set_eq_trans; eassumption.
  - intros m m' _ IH e3 H. inversion H; subst. constructor. apply IH. assumption.
  - intros v v' m m' Ev _ IH e3 H. inversion H; subst. constructor; [eapply set_eq_trans; eassumption | apply IH; assumption].
  - (* functions of a parameter *)
    intros a a' P P' f f' Ea EP Hf0 IH m3 H. remember (set_module_params a' P' f') as m2 eqn:E2.
    induction H as [? a'' ? P'' ? f'' Ea' EP' Hf' _ | | | | | φ Q m2' m3' Hφ H IHH EQ]; try discriminate.
    + injection E2 as <- <- <-. constructor; [eapply set_eq_trans; eassumption | intros; rewrite EP; apply EP' |]. intros x x' Hx E.
      eapply IH; [exact Hx | apply set_eq_refl |]. apply Hf'; [| exact E].
      eapply set_mem_eq_r; [exact Ea | exact Hx].
    + subst. apply set_module_eq_cond_r; [exact Hφ | exact (IHH eq_refl) |]. intros ys x. rewrite EQ. destruct ys; cbn; first [apply EP | symmetry; apply EP].
  - (* tables *)
    intros ms ms' Hms0 IH m3 H. remember (set_module_members ms') as m2 eqn:E2.
    induction H as [| ? ms'' Hms'' | | | | φ Q m2' m3' Hφ H IHH EQ]; try discriminate.
    + injection E2 as <-. constructor. apply IH. assumption.
    + subst. apply set_module_eq_cond_r; [exact Hφ | exact (IHH eq_refl) |]. intros ys x. rewrite EQ.
      symmetry. apply module_member_proofs_resp. constructor. exact Hms0.
  - (* global modules *)
    intros p args args' E m3 H. remember (set_module_global p args') as m2 eqn:E2.
    induction H as [| | ? ? args'' E' | | | φ Q m2' m3' Hφ H IHH EQ]; try discriminate.
    + injection E2 as <- <-. constructor. eapply list_set_eq_trans; eassumption.
    + subst. apply set_module_eq_cond_r; [exact Hφ | exact (IHH eq_refl) |]. intros ys x. rewrite EQ.
      symmetry. apply module_member_proofs_resp. constructor. exact E.
  - (* conditions *)
    intros φ φ' P P' m m' Hφ EP Hm0 IH m3 H. remember (set_module_cond φ' P' m') as m2 eqn:E2.
    induction H as [| | | ? φ'' ? P'' ? m'' Hφ' EP' Hm' _ | ψ Q n n' Hψ Hn _ EQ | ψ Q n n' Hψ H IHH EQ]; try discriminate.
    + injection E2 as <- <- <-.
      constructor; [tauto | intros; rewrite EP; apply EP' | intros Hc; apply IH; [exact Hc | apply Hm'; apply Hφ; exact Hc]].
    + injection E2 as <- <- <-. apply set_module_eq_cond_l; [apply Hφ; exact Hψ | apply IH; [apply Hφ; exact Hψ | exact Hn] |].
      intros ys x. rewrite EP. apply EQ.
    + subst. apply set_module_eq_cond_r; [exact Hψ | exact (IHH eq_refl) |]. intros ys x. rewrite EQ. destruct ys; cbn; first [apply EP | symmetry; apply EP].
  - (* a condition that holds, on the left *)
    intros φ P m m' Hφ Hm0 IH EP m3 H. apply set_module_eq_cond_l; [exact Hφ | exact (IH _ H) |].
    intros ys x. rewrite EP. apply module_member_proofs_resp. exact H.
  - (* a condition that holds, on the right *)
    intros φ P m m' Hφ Hm0 IH EP m3 H. remember (set_module_cond φ P m') as m2 eqn:E2.
    induction H as [| | | ? φ'' ? P'' ? m'' Hφ' EP' Hm' _ | ψ Q n n' Hψ Hn _ EQ | ψ Q n n' Hψ H IHH EQ]; try discriminate.
    + injection E2 as <- <- <-. apply set_module_eq_cond_r; [apply Hφ'; exact Hφ | exact (IH _ (Hm' Hφ)) |].
      intros ys x. rewrite <- EP'. apply EP.
    + injection E2 as <- <- <-. exact (IH _ Hn).
    + subst. apply set_module_eq_cond_r; [exact Hψ | exact (IHH eq_refl) |]. intros ys x. rewrite EQ. destruct ys; cbn; first [apply EP | symmetry; apply EP].
  - intros ms3 H. inversion H; subst. constructor.
  - intros x e e' ms ms' _ IHe _ IHms ms3 H. inversion H; subst. constructor; [apply IHe | apply IHms]; assumption.
Qed.

Corollary set_module_eq_trans : forall m1 m2 m3, set_module_eq γ m1 m2 -> set_module_eq γ m2 m3 -> set_module_eq γ m1 m3.
Proof. intros. eapply (proj1 (proj2 set_value_eq_trans)); eassumption. Qed.

Corollary set_entry_eq_trans : forall e1 e2 e3, set_entry_eq γ e1 e2 -> set_entry_eq γ e2 e3 -> set_entry_eq γ e1 e3.
Proof. intros. eapply (proj1 set_value_eq_trans); eassumption. Qed.

Lemma member_is_proof_resp : forall m m', set_module_eq γ m m' -> forall x, member_is_proof γ m x <-> member_is_proof γ m' x.
Proof. intros m m' H x. unfold member_is_proof. rewrite (module_member_proofs_resp nil _ _ H x). reflexivity. Qed.

Lemma select_term_resp : forall m m', set_module_eq γ m m' -> forall x, set_eq (select_term γ m x) (select_term γ m' x).
Proof.
  intros m m' H. induction H as [a a' P P' f f' Ea EP Hf IH | ms ms' Hms | p args args' Hargs | φ φ' P P' m m' Hφ EP _ IH
                                | φ P m m' Hφ _ IH _ | φ P m m' Hφ _ IH _]; intros x.
  - cbn [select_term]. rewrite (EP nil x). destruct (P' nil x); [apply set_eq_refl |].
    apply graph_set_resp_on; [exact Ea |]. intros v v' Hv E. apply IH; assumption.
  - cbn [select_term]. pose proof (members_lookup_resp _ _ Hms x) as E.
    destruct (members_lookup ms x), (members_lookup ms' x); cbn in E; try contradiction; [apply set_entry_value_resp; exact E | apply set_eq_refl].
  - cbn [select_term]. apply apply_values_resp; [apply set_eq_refl | exact Hargs].
  - cbn [select_term]. apply cond_resp_cond; [exact Hφ |]. intros Hc. apply IH. exact Hc.
  - cbn [select_term]. eapply set_eq_trans; [exact (cond_true _ _ Hφ) | apply IH].
  - cbn [select_term]. eapply set_eq_trans; [apply IH | apply set_eq_sym; exact (cond_true _ _ Hφ)].
Qed.

Lemma apply_module_resp : forall m m', set_module_eq γ m m' -> forall x x', set_eq x x' ->
    set_module_eq γ (apply_module m x) (apply_module m' x').
Proof.
  intros m m' H. induction H as [a a' P P' f f' Ea EP Hf _ | ms ms' Hms | p args args' Hargs | φ φ' P P' m m' Hφ EP _ IH
                                | φ P m m' Hφ _ IH EP | φ P m m' Hφ _ IH EP];
    intros x x' Ex; cbn [apply_module].
  - pose proof Ea as Ec. constructor; [| exact EP |].
    + split; intros Hx; [eapply set_mem_eq_l; [exact Ex | eapply set_mem_eq_r; [exact Ec | exact Hx]]
                        | eapply set_mem_eq_l; [apply set_eq_sym; exact Ex | eapply set_mem_eq_r; [apply set_eq_sym; exact Ec | exact Hx]]].
    + intros Hx. apply Hf; assumption.
  - constructor; exact Hms.
  - constructor. apply list_set_eq_app; [exact Hargs | constructor; [exact Ex | constructor]].
  - constructor; [exact Hφ | exact EP |]. intros Hc. apply IH; assumption.
  - apply set_module_eq_cond_l; [exact Hφ | exact (IH _ _ Ex) |]. intros ys z. rewrite EP. symmetry. apply apply_module_proofs.
  - apply set_module_eq_cond_r; [exact Hφ | exact (IH _ _ Ex) |]. intros ys z. rewrite EP. symmetry. apply apply_module_proofs.
Qed.

Lemma apply_module_args_resp : forall args args' m m', set_module_eq γ m m' -> list_set_eq args args' ->
    set_module_eq γ (apply_module_args m args) (apply_module_args m' args').
Proof.
  intros args args' m m' Hm H. revert m m' Hm. unfold apply_module_args.
  induction H as [| a a' args args' Ha _ IH]; intros m m' Hm; cbn [fold_left]; [exact Hm |].
  apply IH. apply apply_module_resp; assumption.
Qed.

(** ** A Unit's Proofness Respects Its Slots' *)

(** Two readings of the slots' proofness agree. *)
Definition slot_proofs_eq (κs κs' : nat -> member_proofness) : Prop := forall s ys x, κs s ys x = κs' s ys x.

Lemma env_slot_proofs_resp : forall ρ ρ', set_env_eq γ ρ ρ' -> slot_proofs_eq (env_slot_proofs γ ρ) (env_slot_proofs γ ρ').
Proof. intros * H s ys x. unfold env_slot_proofs. apply module_member_proofs_resp. apply set_entry_module_part_resp. apply H. Qed.

Lemma push_slot_proofs_resp : forall κs κs' P P', slot_proofs_eq κs κs' -> (forall ys x, P ys x = P' ys x) ->
    slot_proofs_eq (push_slot_proofs κs P) (push_slot_proofs κs' P').
Proof. intros * H HP [| s] ys x; cbn; [apply HP | apply H]. Qed.

Lemma unit_member_proofs_resp_all :
  (forall H κs κs', slot_proofs_eq κs κs' -> forall ys x, modexp_member_proofs γ κs H ys x = modexp_member_proofs γ κs' H ys x) /\
  (forall U κs κs', slot_proofs_eq κs κs' -> forall ys x, unit_member_proofs γ κs U ys x = unit_member_proofs γ κs' U ys x) /\
  (forall Φ κs κs', slot_proofs_eq κs κs' ->
     slot_proofs_eq (body_slot_proofs γ κs Φ) (body_slot_proofs γ κs' Φ) /\
     forall ys x, body_member_lookup γ κs Φ ys x = body_member_lookup γ κs' Φ ys x) /\
  (forall E κs κs', slot_proofs_eq κs κs' -> forall ys x, gentry_slot_proofs γ κs E ys x = gentry_slot_proofs γ κs' E ys x).
Proof.
  set (Pc := fun e => forall κs κs', slot_proofs_eq κs κs' -> forall ys x,
          (match e with ce_mod U' => unit_member_proofs γ κs U' | ce_dm _ _ U' => unit_member_proofs γ κs U'
                   | _ => no_slot_proofs γ end) ys x =
          (match e with ce_mod U' => unit_member_proofs γ κs' U' | ce_dm _ _ U' => unit_member_proofs γ κs' U'
                   | _ => no_slot_proofs γ end) ys x).
  set (Pm := fun H => forall κs κs', slot_proofs_eq κs κs' -> forall ys x,
          modexp_member_proofs γ κs H ys x = modexp_member_proofs γ κs' H ys x).
  set (Pu := fun U => forall κs κs', slot_proofs_eq κs κs' -> forall ys x,
          unit_member_proofs γ κs U ys x = unit_member_proofs γ κs' U ys x).
  set (Pd := fun D => forall κs κs', slot_proofs_eq κs κs' -> forall ys x,
          moddef_member_proofs γ κs D ys x = moddef_member_proofs γ κs' D ys x).
  set (Pg := fun Φ => forall κs κs', slot_proofs_eq κs κs' ->
          slot_proofs_eq (body_slot_proofs γ κs Φ) (body_slot_proofs γ κs' Φ) /\
          forall ys x, body_member_lookup γ κs Φ ys x = body_member_lookup γ κs' Φ ys x).
  set (Pn := fun E => forall κs κs', slot_proofs_eq κs κs' -> forall ys x,
          gentry_slot_proofs γ κs E ys x = gentry_slot_proofs γ κs' E ys x).
  assert (Hall : (forall H, Pm H) /\ (forall U, Pu U) /\ (forall Φ, Pg Φ) /\ (forall E, Pn E)).
  { split; [| split; [| split]];
      [apply (modexp_mut (fun _ => True) Pm (fun _ => True) Pu Pd Pg Pn Pc)
      | apply (gunit_mut (fun _ => True) Pm (fun _ => True) Pu Pd Pg Pn Pc)
      | apply (gmod_mut (fun _ => True) Pm (fun _ => True) Pu Pd Pg Pn Pc)
      | apply (gentry_mut (fun _ => True) Pm (fun _ => True) Pu Pd Pg Pn Pc)];
      unfold Pm, Pu, Pd, Pg, Pn, Pc; cbn; intros; try exact I.
    all: try reflexivity.
    all: try (match goal with Hk : slot_proofs_eq ?a ?b |- ?a _ _ _ = ?b _ _ _ => apply Hk end).
    all: try (match goal with IH : forall κs0 κs'0, slot_proofs_eq κs0 κs'0 -> forall ys0 x0, _ = _, Hk : slot_proofs_eq _ _ |- _ =>
                apply IH; exact Hk end).
    all: try (match goal with Hk : slot_proofs_eq _ _ |- slot_proofs_eq _ _ /\ _ => split; [exact Hk | intros; reflexivity] end).
    all: try (match goal with IH : forall κs0 κs'0, slot_proofs_eq κs0 κs'0 -> slot_proofs_eq _ _ /\ _, Hk : slot_proofs_eq _ _
                |- match _ with Some b => b | None => false end = _ => rewrite (proj2 (IH _ _ Hk)); reflexivity end).
    all: try (match goal with HD : forall κs0 κs'0, slot_proofs_eq κs0 κs'0 -> forall ys0 x0, moddef_member_proofs _ _ ?D _ _ = _,
                             HF : Forall _ ?Δ, Hk : slot_proofs_eq _ _ |- moddef_member_proofs _ _ ?D _ _ = _ =>
                apply HD; clear - HF Hk; induction HF as [| e Δ He HΔ IH];
                  [exact Hk | cbn; apply push_slot_proofs_resp; [exact IH | apply He; exact IH]] end).
    all: try (match goal with HΦ : forall κs0 κs'0, slot_proofs_eq κs0 κs'0 -> slot_proofs_eq (body_slot_proofs _ κs0 ?Φ) _ /\ _,
                             HΦg : forall κs0 κs'0, slot_proofs_eq κs0 κs'0 -> slot_proofs_eq (body_slot_proofs _ κs0 ?Φg) _ /\ _,
                             Hk : slot_proofs_eq ?a ?b |- slot_proofs_eq (body_slot_proofs _ (body_slot_proofs _ ?a ?Φ) ?Φg) _ /\ _ =>
                destruct (HΦ _ _ Hk) as [Hs Hl]; destruct (HΦg _ _ Hs) as [Hs' Hl']; split; [exact Hs' |];
                intros ys0 x0; rewrite Hl'; destruct (body_member_lookup _ _ Φg _ _); [reflexivity | apply Hl] end).
    (* the entries *)
    all: rename x into z; destruct (H _ _ H1) as [Hs Hl]; split; [apply push_slot_proofs_resp; [exact Hs | apply H0; exact Hs] |];
      intros ys0 x0; destruct (String.eqb (chain_key ys0 x0) z); [destruct ys0; [reflexivity | f_equal; apply H0; exact Hs] | apply Hl]. }
  exact Hall.
Qed.

(** A weakened unit has the proofness the unit has at the slots read
    through the weakening. *)
Lemma unit_member_proofs_wk_all :
  (forall H κs φ κs0, slot_proofs_eq κs0 (fun s => κs (φ s)) -> forall ys x,
     modexp_member_proofs γ κs (modexp_wk H φ) ys x = modexp_member_proofs γ κs0 H ys x) /\
  (forall U κs φ κs0, slot_proofs_eq κs0 (fun s => κs (φ s)) -> forall ys x,
     unit_member_proofs γ κs (gunit_wk U φ) ys x = unit_member_proofs γ κs0 U ys x).
Proof.
  set (Pc := fun e => forall κs φ κs0, slot_proofs_eq κs0 (fun s => κs (φ s)) -> forall ys x,
          (match centry_wk e φ with ce_mod U' => unit_member_proofs γ κs U' | ce_dm _ _ U' => unit_member_proofs γ κs U'
                   | _ => no_slot_proofs γ end) ys x =
          (match e with ce_mod U' => unit_member_proofs γ κs0 U' | ce_dm _ _ U' => unit_member_proofs γ κs0 U'
                   | _ => no_slot_proofs γ end) ys x).
  set (Pm := fun H => forall κs φ κs0, slot_proofs_eq κs0 (fun s => κs (φ s)) -> forall ys x,
          modexp_member_proofs γ κs (modexp_wk H φ) ys x = modexp_member_proofs γ κs0 H ys x).
  set (Pu := fun U => forall κs φ κs0, slot_proofs_eq κs0 (fun s => κs (φ s)) -> forall ys x,
          unit_member_proofs γ κs (gunit_wk U φ) ys x = unit_member_proofs γ κs0 U ys x).
  set (Pd := fun D => forall κs φ κs0, slot_proofs_eq κs0 (fun s => κs (φ s)) -> forall ys x,
          moddef_member_proofs γ κs (moddef_wk D φ) ys x = moddef_member_proofs γ κs0 D ys x).
  set (Pg := fun Φ => forall κs φ κs0, slot_proofs_eq κs0 (fun s => κs (φ s)) ->
          slot_proofs_eq (body_slot_proofs γ κs0 Φ) (fun s => body_slot_proofs γ κs (gmod_wk Φ φ) (wk_qn (gm_binders Φ) φ s)) /\
          forall ys x, body_member_lookup γ κs (gmod_wk Φ φ) ys x = body_member_lookup γ κs0 Φ ys x).
  set (Pn := fun E => forall κs φ κs0, slot_proofs_eq κs0 (fun s => κs (φ s)) -> forall ys x,
          gentry_slot_proofs γ κs (gentry_wk E φ) ys x = gentry_slot_proofs γ κs0 E ys x).
  assert (Hall : (forall H, Pm H) /\ (forall U, Pu U)).
  { split; [apply (modexp_mut (fun _ => True) Pm (fun _ => True) Pu Pd Pg Pn Pc)
           | apply (gunit_mut (fun _ => True) Pm (fun _ => True) Pu Pd Pg Pn Pc)];
      unfold Pm, Pu, Pd, Pg, Pn, Pc; cbn; intros; try exact I.
    all: try reflexivity.
    all: try (match goal with Hk : slot_proofs_eq ?a _ |- _ = ?a _ _ _ => symmetry; apply Hk end).
    all: try (match goal with IH : forall κs0 φ0 κs1, slot_proofs_eq κs1 _ -> forall ys0 x0, _ = _, Hk : slot_proofs_eq _ _ |- _ =>
                apply IH; exact Hk end).
    all: try (match goal with Hk : slot_proofs_eq ?a _ |- slot_proofs_eq ?a _ /\ _ => split; [exact Hk | intros; reflexivity] end).
    (* a unit: its telescope's slots *)
    all: try (match goal with HD : forall κs1 φ0 κs2, slot_proofs_eq κs2 _ -> forall ys0 x0, moddef_member_proofs _ _ (moddef_wk ?D _) _ _ = _,
                             HF : Forall _ ?Δ, Hk : slot_proofs_eq _ _ |- unit_member_proofs _ _ (gunit_wk (gu_mk ?Δ ?D) _) _ _ = _ =>
                cbn [gunit_wk unit_member_proofs]; apply HD; clear - HF Hk; induction HF as [| e Δ He HΔ IH];
                  [exact Hk | intros [| s] ys0 x0; cbn; [symmetry; apply He; exact IH | apply IH]] end).
    (* a body *)
    all: try (match goal with HΦ : forall κs1 φ0 κs2, slot_proofs_eq κs2 _ -> slot_proofs_eq (body_slot_proofs _ κs2 ?Φ) _ /\ _,
                             Hk : slot_proofs_eq _ _
                |- match body_member_lookup _ _ (gmod_wk ?Φ _) _ _ with Some b => b | None => false end = _ =>
                rewrite (proj2 (HΦ _ _ _ Hk)); reflexivity end).
    (* an entry, and an open *)
    all: first
      [ destruct (H _ _ _ H1) as [Hs Hl]; split;
          [intros [| s] ys0 x0; cbn; [symmetry; apply H0; exact Hs | apply Hs]
          | intros ys0 x0; destruct (String.eqb (chain_key ys0 x0) x);
            [destruct ys0; [f_equal; destruct E; reflexivity | f_equal; apply H0; exact Hs] | apply Hl]]
      | destruct (H0 _ _ _ H3) as [Hs Hl]; destruct (H2 _ _ _ Hs) as [Hs' Hl']; split;
          [intros s ys0 x0; rewrite wk_qn_plus; apply Hs'
          | intros ys0 x0; rewrite Hl'; destruct (body_member_lookup _ _ Φg _ _); [reflexivity | apply Hl]] ]. }
  exact Hall.
Qed.

(** The slots a substitution's entries read, past one more binder. *)
Lemma slot_proofs_sub_q : forall κs σ κs0 P P0,
    slot_proofs_eq κs0 (fun s => modexp_member_proofs γ κs (sentry_modexp (σ s))) -> (forall ys x, P0 ys x = P ys x) ->
    slot_proofs_eq (push_slot_proofs κs0 P0) (fun s => modexp_member_proofs γ (push_slot_proofs κs P) (sentry_modexp (sb_q σ s))).
Proof.
  intros * Hκ HP [| s] ys x; cbn; [apply HP |]. unfold sb_q, sb_extend, sb_wk.
  rewrite <- sentry_modexp_wk. rewrite (proj1 unit_member_proofs_wk_all _ (push_slot_proofs κs P) wk_shift κs); [apply Hκ |].
  intros s' ys' x'; reflexivity.
Qed.

(** A substituted unit has the proofness the unit has at the slots the
    substitution's entries read. *)
Lemma unit_member_proofs_sub_all :
  (forall H κs σ κs0, slot_proofs_eq κs0 (fun s => modexp_member_proofs γ κs (sentry_modexp (σ s))) -> forall ys x,
     modexp_member_proofs γ κs (modexp_sub H σ) ys x = modexp_member_proofs γ κs0 H ys x) /\
  (forall U κs σ κs0, slot_proofs_eq κs0 (fun s => modexp_member_proofs γ κs (sentry_modexp (σ s))) -> forall ys x,
     unit_member_proofs γ κs (gunit_sub U σ) ys x = unit_member_proofs γ κs0 U ys x).
Proof.
  set (Q := fun κs σ κs0 => slot_proofs_eq κs0 (fun s => modexp_member_proofs γ κs (sentry_modexp (σ s)))).
  set (Pc := fun e => forall κs σ κs0, Q κs σ κs0 -> forall ys x,
          (match centry_sub e σ with ce_mod U' => unit_member_proofs γ κs U' | ce_dm _ _ U' => unit_member_proofs γ κs U'
                   | _ => no_slot_proofs γ end) ys x =
          (match e with ce_mod U' => unit_member_proofs γ κs0 U' | ce_dm _ _ U' => unit_member_proofs γ κs0 U'
                   | _ => no_slot_proofs γ end) ys x).
  set (Pm := fun H => forall κs σ κs0, Q κs σ κs0 -> forall ys x,
          modexp_member_proofs γ κs (modexp_sub H σ) ys x = modexp_member_proofs γ κs0 H ys x).
  set (Pu := fun U => forall κs σ κs0, Q κs σ κs0 -> forall ys x,
          unit_member_proofs γ κs (gunit_sub U σ) ys x = unit_member_proofs γ κs0 U ys x).
  set (Pd := fun D => forall κs σ κs0, Q κs σ κs0 -> forall ys x,
          moddef_member_proofs γ κs (moddef_sub D σ) ys x = moddef_member_proofs γ κs0 D ys x).
  set (Pg := fun Φ => forall κs σ κs0, Q κs σ κs0 ->
          Q (body_slot_proofs γ κs (gmod_sub Φ σ)) (sb_qn (gm_binders Φ) σ) (body_slot_proofs γ κs0 Φ) /\
          forall ys x, body_member_lookup γ κs (gmod_sub Φ σ) ys x = body_member_lookup γ κs0 Φ ys x).
  set (Pn := fun E => forall κs σ κs0, Q κs σ κs0 -> forall ys x,
          gentry_slot_proofs γ κs (gentry_sub E σ) ys x = gentry_slot_proofs γ κs0 E ys x).
  assert (Hall : (forall H, Pm H) /\ (forall U, Pu U)).
  { split; [apply (modexp_mut (fun _ => True) Pm (fun _ => True) Pu Pd Pg Pn Pc)
           | apply (gunit_mut (fun _ => True) Pm (fun _ => True) Pu Pd Pg Pn Pc)];
      unfold Pm, Pu, Pd, Pg, Pn, Pc, Q; cbn; intros; try exact I.
    all: try reflexivity.
    all: try (match goal with Hk : slot_proofs_eq ?a _ |- _ = ?a _ _ _ => symmetry; apply Hk end).
    all: try (match goal with IH : forall κs0 σ0 κs1, slot_proofs_eq κs1 _ -> forall ys0 x0, _ = _, Hk : slot_proofs_eq _ _ |- _ =>
                apply IH; exact Hk end).
    all: try (match goal with Hk : slot_proofs_eq ?a _ |- slot_proofs_eq ?a _ /\ _ => split; [exact Hk | intros; reflexivity] end).
    all: try (match goal with HΦ : forall κs1 σ0 κs2, slot_proofs_eq κs2 _ -> slot_proofs_eq (body_slot_proofs _ κs2 ?Φ) _ /\ _,
                             Hk : slot_proofs_eq _ _
                |- match body_member_lookup _ _ (gmod_sub ?Φ _) _ _ with Some b => b | None => false end = _ =>
                rewrite (proj2 (HΦ _ _ _ Hk)); reflexivity end).
    (* a unit: its telescope's slots *)
    all: try (match goal with HD : forall κs1 σ0 κs2, slot_proofs_eq κs2 _ -> forall ys0 x0, moddef_member_proofs _ _ (moddef_sub ?D _) _ _ = _,
                             HF : Forall _ ?Δ, Hk : slot_proofs_eq _ _ |- unit_member_proofs _ _ (gunit_sub (gu_mk ?Δ ?D) _) _ _ = _ =>
                cbn [gunit_sub unit_member_proofs]; apply HD; clear - HF Hk; induction HF as [| e Δ He HΔ IH];
                  [exact Hk | cbn; apply slot_proofs_sub_q; [exact IH | intros; symmetry; apply He; exact IH]] end).
    (* an entry, and an open *)
    all: first
      [ destruct (H _ _ _ H1) as [Hs Hl]; split;
          [apply slot_proofs_sub_q; [exact Hs | intros; symmetry; apply H0; exact Hs]
          | intros ys0 x0; destruct (String.eqb (chain_key ys0 x0) x);
            [destruct ys0; [f_equal; destruct E; reflexivity | f_equal; apply H0; exact Hs] | apply Hl]]
      | destruct (H0 _ _ _ H3) as [Hs Hl]; destruct (H2 _ _ _ Hs) as [Hs' Hl']; split;
          [intros s ys0 x0; rewrite (Hs' s ys0 x0), (sb_qn_add (gm_binders Φg) (gm_binders Φ) σ s); reflexivity
          | intros ys0 x0; rewrite Hl'; destruct (body_member_lookup _ _ Φg _ _); [reflexivity | apply Hl]] ]. }
  exact Hall.
Qed.

  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).

Lemma select_module_resp : forall m m', set_module_eq γ m m' -> forall y,
    set_module_eq γ (select_module γ m y) (select_module γ m' y).
Proof.
  intros m m' H. induction H as [a a' P P' f f' Ea EP Hf IH | ms ms' Hms | p args args' Hargs | φ φ' P P' m m' Hφ EP _ IH
                                | φ P m m' Hφ _ IH EP | φ P m m' Hφ _ IH EP];
    intros y; cbn [select_module].
  - constructor; [exact Ea | intros; apply EP |]. intros v v' Hv E. apply IH; assumption.
  - pose proof (members_lookup_resp _ _ Hms y) as E.
    destruct (members_lookup ms y), (members_lookup ms' y); cbn in E; try contradiction;
      [apply set_entry_module_part_resp; exact E | constructor; constructor].
  - apply apply_module_args_resp; [apply Hmods | exact Hargs].
  - constructor; [exact Hφ | intros; apply EP |]. intros Hc. apply IH. exact Hc.
  - apply set_module_eq_cond_l; [exact Hφ | exact (IH y) |]. intros ys z. rewrite EP. symmetry. apply select_module_proofs.
  - apply set_module_eq_cond_r; [exact Hφ | exact (IH y) |]. intros ys z. rewrite EP. symmetry. apply select_module_proofs.
Qed.

End Operations.

Arguments set_module_eq_sym {γ}.
Arguments set_module_eq_trans {γ}.
Arguments set_entry_eq_sym {γ}.
Arguments set_entry_eq_trans {γ}.
Arguments set_entry_value_resp {γ}.
Arguments set_entry_module_part_resp {γ}.
Arguments members_lookup_resp {γ}.
Arguments set_env_extend_resp {γ}.
Arguments set_env_extend_kinded_resp {γ}.
Arguments apply_module_resp {γ}.
Arguments apply_module_args_resp {γ}.

(** ** A Module's Proofness Is Its Syntax's

    The module a module expression denotes has the proofness the
    expression's syntax gives at the slots of the environment
    ([set_interp_member_proofs]). *)

Section Proofness.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

Lemma members_lookup_snoc : forall ms z e k, members_lookup (ms ++ [(z, e)]) k = if String.eqb k z then Some e else members_lookup ms k.
Proof.
  induction ms as [| [y e0] ms IH]; intros z e k; cbn; [destruct (String.eqb k z); reflexivity |].
  rewrite IH. destruct (String.eqb k z) eqn:E; [reflexivity |]. reflexivity.
Qed.

(** A telescope's slots, outermost first. *)
Fixpoint tele_out_proofs (κs : nat -> member_proofness) (L : list centry) : nat -> member_proofness :=
  match L with
  | nil => κs
  | e :: L' =>
      tele_out_proofs
        (push_slot_proofs κs (match e with ce_mod U' => unit_member_proofs γ κs U' | ce_dm _ _ U' => unit_member_proofs γ κs U'
                                  | _ => no_slot_proofs γ end)) L'
  end.

Lemma tele_out_proofs_app : forall L1 L2 κs, tele_out_proofs κs (L1 ++ L2) = tele_out_proofs (tele_out_proofs κs L1) L2.
Proof. induction L1 as [| e L1 IH]; intros; [reflexivity | apply IH]. Qed.

Lemma tele_out_proofs_resp : forall L κs κs', slot_proofs_eq κs κs' -> slot_proofs_eq (tele_out_proofs κs L) (tele_out_proofs κs' L).
Proof.
  induction L as [| e L IH]; intros κs κs' H; [exact H |]. cbn [tele_out_proofs]. apply IH. apply push_slot_proofs_resp; [exact H |].
  intros ys x. destruct e; try reflexivity; apply (proj1 (proj2 (unit_member_proofs_resp_all γ))); exact H.
Qed.

(** A unit's proofness under its telescope read outermost first. *)
Lemma unit_member_proofs_tele_out : forall Δ D κs ys x,
    unit_member_proofs γ κs (gu_mk Δ D) ys x = moddef_member_proofs γ (tele_out_proofs κs (List.rev Δ)) D ys x.
Proof.
  intros Δ D κs. cbn [unit_member_proofs].
  assert (H : slot_proofs_eq
                ((fix tele (Δ0 : list centry) : nat -> member_proofness :=
                    match Δ0 with
                    | nil => κs
                    | e :: Δ' => push_slot_proofs (tele Δ')
                                   (match e with ce_mod U' => unit_member_proofs γ (tele Δ') U'
                                            | ce_dm _ _ U' => unit_member_proofs γ (tele Δ') U' | _ => no_slot_proofs γ end)
                    end) Δ) (tele_out_proofs κs (List.rev Δ))).
  { induction Δ as [| e Δ IH]; [intros s ys x; reflexivity |]. cbn [List.rev]. rewrite tele_out_proofs_app. cbn [tele_out_proofs].
    apply push_slot_proofs_resp; [exact IH |]. intros ys x. destruct e; try reflexivity; apply (proj1 (proj2 (unit_member_proofs_resp_all γ))); exact IH. }
  intros ys x. exact (proj1 (proj2 (unit_member_proofs_resp_all γ)) (gu_mk nil D) _ _ H ys x).
Qed.

(** A definition's proofness respects its slots'. *)
Lemma moddef_member_proofs_resp : forall D κs κs', slot_proofs_eq κs κs' -> forall ys x,
    moddef_member_proofs γ κs D ys x = moddef_member_proofs γ κs' D ys x.
Proof. intros D κs κs' H ys x. exact (proj1 (proj2 (unit_member_proofs_resp_all γ)) (gu_mk nil D) _ _ H ys x). Qed.

(** Grafted entries come after the body's. *)
Lemma body_member_proofs_graft : forall B A κs,
    slot_proofs_eq (body_slot_proofs γ κs (gm_graft A B)) (body_slot_proofs γ (body_slot_proofs γ κs A) B) /\
    forall ys x, body_member_lookup γ κs (gm_graft A B) ys x =
      match body_member_lookup γ (body_slot_proofs γ κs A) B ys x with Some b => Some b | None => body_member_lookup γ κs A ys x end.
Proof.
  induction B as [| B IH z E | B IH H its Bg _]; intros A κs; cbn [gm_graft body_slot_proofs body_member_lookup].
  - split; [intros s ys x; reflexivity | intros; reflexivity].
  - destruct (IH A κs) as [Hs Hl]. split.
    + apply push_slot_proofs_resp; [exact Hs |]. intros ys x. apply (proj2 (proj2 (proj2 (unit_member_proofs_resp_all γ)))). exact Hs.
    + intros ys x. destruct (String.eqb (chain_key ys x) z); [| apply Hl].
      destruct ys; [reflexivity |]. f_equal. apply (proj2 (proj2 (proj2 (unit_member_proofs_resp_all γ)))). exact Hs.
  - destruct (IH A κs) as [Hs Hl]. split.
    + apply (proj1 (proj1 (proj2 (proj2 (unit_member_proofs_resp_all γ))) Bg _ _ Hs)).
    + intros ys x. rewrite (proj2 (proj1 (proj2 (proj2 (unit_member_proofs_resp_all γ))) Bg _ _ Hs)).
      destruct (body_member_lookup γ _ Bg ys x); [reflexivity |]. rewrite Hl. reflexivity.
Qed.

(** A body's proofness is its expansion's. *)
Lemma body_member_proofs_expand : forall Φ κs,
    slot_proofs_eq (body_slot_proofs γ κs (gm_expand Φ)) (body_slot_proofs γ κs Φ) /\
    forall ys x, body_member_lookup γ κs (gm_expand Φ) ys x = body_member_lookup γ κs Φ ys x.
Proof.
  induction Φ as [| Φ IH z E | Φ IH H its Φg IHg]; intros κs; cbn [gm_expand body_slot_proofs body_member_lookup].
  - split; [intros s ys x; reflexivity | intros; reflexivity].
  - destruct (IH κs) as [Hs Hl]. split.
    + apply push_slot_proofs_resp; [exact Hs |]. intros ys x. apply (proj2 (proj2 (proj2 (unit_member_proofs_resp_all γ)))). exact Hs.
    + intros ys x. destruct (String.eqb (chain_key ys x) z); [| apply Hl].
      destruct ys; [reflexivity |]. f_equal. apply (proj2 (proj2 (proj2 (unit_member_proofs_resp_all γ)))). exact Hs.
  - destruct (IH κs) as [Hs Hl]. destruct (body_member_proofs_graft (gm_expand Φg) (gm_expand Φ) κs) as [Gs Gl].
    destruct (IHg (body_slot_proofs γ κs (gm_expand Φ))) as [Hgs Hgl].
    destruct (proj1 (proj2 (proj2 (unit_member_proofs_resp_all γ))) Φg _ _ Hs) as [Rs Rl]. split.
    + intros s ys x. rewrite Gs, Hgs. apply Rs.
    + intros ys x. rewrite Gl, Hgl, Rl. destruct (body_member_lookup γ _ Φg ys x); [reflexivity |]. apply Hl.
Qed.

Lemma set_interp_member_proofs_all :
  (forall Γ ρ M v, set_interp T γ Γ ρ M v -> True) /\
  (forall Γ ρ Ms vs, set_interp_list T γ Γ ρ Ms vs -> True) /\
  (forall Γ ρ fs vs, set_interp_fields T γ Γ ρ fs vs -> True) /\
  (forall Γ ρ H m, set_interp_modexp T γ Γ ρ H m -> forall ys x,
     module_member_proofs γ m ys x = modexp_member_proofs γ (env_slot_proofs γ ρ) H ys x) /\
  (forall Γ ρ U m, set_interp_gunit T γ Γ ρ U m -> forall ys x,
     module_member_proofs γ m ys x = unit_member_proofs γ (env_slot_proofs γ ρ) U ys x) /\
  (forall Γ ρ P L D m, set_interp_unit_params T γ Γ ρ P L D m -> forall κs, slot_proofs_eq (env_slot_proofs γ ρ) κs ->
     (forall ys x, P ys x = moddef_member_proofs γ (tele_out_proofs κs L) D ys x) ->
     forall ys x, module_member_proofs γ m ys x = P ys x) /\
  (forall Γ ρ D m, set_interp_moddef T γ Γ ρ D m -> forall ys x,
     module_member_proofs γ m ys x = moddef_member_proofs γ (env_slot_proofs γ ρ) D ys x) /\
  (forall Γ ρ Φ ms ρo, set_interp_gmod T γ Γ ρ Φ ms ρo ->
     slot_proofs_eq (env_slot_proofs γ ρo) (body_slot_proofs γ (env_slot_proofs γ ρ) Φ) /\
     forall ys x, module_member_proofs γ (set_module_members ms) ys x =
       match body_member_lookup γ (env_slot_proofs γ ρ) Φ ys x with Some b => b | None => false end) /\
  (forall Γ ρ E e, set_interp_gentry T γ Γ ρ E e ->
     (forall ys x, module_member_proofs γ (set_entry_module_part e) ys x = gentry_slot_proofs γ (env_slot_proofs γ ρ) E ys x) /\
     (match e with set_entry_term κ _ => is_proof_kind κ | _ => false end) = gentry_is_proof E) /\
  (forall Γ ρ r p Us Bks j v res, set_elim T γ Γ ρ r p Us Bks j v res -> True) /\
  (forall Γ ρ r p Us Bks gs vs ihs, set_ihs T γ Γ ρ r p Us Bks gs vs ihs -> True) /\
  (forall Γ ρ r p Us Bks t v ihs, set_ih T γ Γ ρ r p Us Bks t v ihs -> True).
Proof.
  apply (set_interp_combined_ind GC T γ); intros; try exact I.
  (* module expressions *)
  - reflexivity.
  - reflexivity.
  - cbn [modexp_member_proofs]. rewrite select_module_proofs. auto.
  - cbn [modexp_member_proofs]. rewrite apply_module_proofs. auto.
  - cbn [modexp_member_proofs]. auto.
  (* a unit *)
  - rewrite (H1 (env_slot_proofs γ ρ)); [apply H | intros s ys0 x0; reflexivity | intros ys0 x0; rewrite H; apply unit_member_proofs_tele_out].
  (* the telescope *)
  - rewrite H0, H2. apply moddef_member_proofs_resp. exact H1.
  - destruct ys; reflexivity.
  - apply (H3 (push_slot_proofs κs (no_slot_proofs γ))); [intros [| s] ys0 x0; [reflexivity | apply H4] | exact H5].
  - apply (H3 (push_slot_proofs κs (unit_member_proofs γ κs U))); [| exact H5].
    intros [| s] ys0 x0; [unfold env_slot_proofs; cbn; rewrite H1; apply (proj1 (proj2 (unit_member_proofs_resp_all γ))); exact H4
                         | apply H4].
  - apply (H5 (push_slot_proofs κs (unit_member_proofs γ κs U))); [| exact H7].
    intros [| s] ys0 x0; [unfold env_slot_proofs; cbn; rewrite H3; apply (proj1 (proj2 (unit_member_proofs_resp_all γ))); exact H6
                         | apply H6].
  (* definitions *)
  - rewrite (proj2 H0). cbn [moddef_member_proofs]. rewrite (proj2 (body_member_proofs_expand _ _)). reflexivity.
  - cbn [moddef_member_proofs]. auto.
  (* bodies *)
  - split; [intros s ys x; reflexivity | intros [| y ys] x; reflexivity].
  - destruct H1 as [Hs Hl]; destruct H3 as [He1 He2]. split.
    + intros [| s] ys0 x0; cbn [body_slot_proofs push_slot_proofs]; [| apply Hs]. unfold env_slot_proofs in He1 |- *.
      cbn [set_env_extend]. rewrite He1. apply (proj2 (proj2 (proj2 (unit_member_proofs_resp_all γ)))). exact Hs.
    + intros [| y ys0] x0; cbn [module_member_proofs body_member_lookup chain_key]; rewrite members_lookup_snoc.
      * destruct (String.eqb x0 x); [destruct e; exact He2 |]. exact (Hl nil x0).
      * destruct (String.eqb y x); [rewrite He1; apply (proj2 (proj2 (proj2 (unit_member_proofs_resp_all γ)))); exact Hs |].
        exact (Hl (y :: ys0) x0).
  (* entries *)
  - split; [intros; reflexivity | reflexivity].
  - split; [intros; reflexivity | reflexivity].
  - split; [exact H0 | reflexivity].
  - split; [assumption | reflexivity].
  - split; [intros; reflexivity | reflexivity].
  - split; [intros; reflexivity | reflexivity].
Qed.

Corollary set_interp_modexp_member_proofs : forall Γ ρ H m, set_interp_modexp T γ Γ ρ H m -> forall ys x,
    module_member_proofs γ m ys x = modexp_member_proofs γ (env_slot_proofs γ ρ) H ys x.
Proof. exact (proj1 (proj2 (proj2 (proj2 set_interp_member_proofs_all)))). Qed.

End Proofness.
