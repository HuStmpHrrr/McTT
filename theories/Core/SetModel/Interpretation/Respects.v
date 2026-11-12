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
Import ListNotations.

(** ** The Operations Respect Equality *)

Lemma set_entry_value_resp : forall e e', set_entry_eq e e' -> set_eq (set_entry_value e) (set_entry_value e').
Proof. intros e e' H. destruct H; cbn [set_entry_value]; first [assumption | apply set_eq_refl]. Qed.

Lemma set_entry_module_part_resp : forall e e', set_entry_eq e e' -> set_module_eq (set_entry_module_part e) (set_entry_module_part e').
Proof. intros e e' H. destruct H; cbn; first [assumption | constructor; constructor]. Qed.

(** Equal tables have equal entries under every name. *)
Definition members_lookup_eq (o o' : option set_entry) : Prop :=
  match o, o' with
  | Some e, Some e' => set_entry_eq e e'
  | None, None => True
  | _, _ => False
  end.

Lemma members_lookup_resp : forall ms ms', set_members_eq ms ms' -> forall x,
    members_lookup_eq (members_lookup ms x) (members_lookup ms' x).
Proof.
  intros ms ms' H. induction H as [| y e e' ms ms' He Hms IH]; intros x; cbn; [exact I |].
  specialize (IH x). destruct (members_lookup ms x), (members_lookup ms' x); cbn in IH |- *; try contradiction; [exact IH |].
  destruct (String.eqb x y); cbn; trivial.
Qed.

Lemma set_env_extend_resp : forall ρ ρ' e e', set_env_eq ρ ρ' -> set_entry_eq e e' ->
    set_env_eq (set_env_extend ρ e) (set_env_extend ρ' e').
Proof. intros * Hρ He [| x]; cbn; [exact He | apply Hρ]. Qed.

Lemma set_env_extend_kinded_resp : forall vs vs' κs ρ ρ', set_env_eq ρ ρ' -> list_set_eq vs vs' ->
    set_env_eq (set_env_extend_kinded ρ κs vs) (set_env_extend_kinded ρ' κs vs').
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

Section Operations.
  Variable γ : global_valuation.

Lemma member_is_proof_resp : forall m m', set_module_eq m m' -> forall x, member_is_proof γ m x <-> member_is_proof γ m' x.
Proof.
  intros m m' H. induction H as [a a' f f' Ea Hf IH | ms ms' Hms | p args args' _]; intros x; cbn.
  - pose proof (code_carrier_resp _ _ Ea) as Ec. split.
    + intros Hp v Hv. assert (Hv' : set_mem v (code_carrier a)) by (eapply set_mem_eq_r; [apply set_eq_sym; exact Ec | exact Hv]).
      apply (IH v v Hv' (set_eq_refl _)). apply Hp. exact Hv'.
    + intros Hp v Hv. apply (IH v v Hv (set_eq_refl _)). apply Hp. eapply set_mem_eq_r; [exact Ec | exact Hv].
  - pose proof (members_lookup_resp _ _ Hms x) as E.
    destruct (members_lookup ms x) as [e |], (members_lookup ms' x) as [e' |]; cbn in E; try contradiction.
    + split; intros [v Hv]; injection Hv as ->; inversion E; subst; eexists; reflexivity.
    + split; intros [v Hv]; discriminate.
  - reflexivity.
Qed.

Lemma select_term_resp : forall m m', set_module_eq m m' -> forall x, set_eq (select_term γ m x) (select_term γ m' x).
Proof.
  intros m m' H. induction H as [a a' f f' Ea Hf IH | ms ms' Hms | p args args' Hargs]; intros x.
  - change (set_eq (cond (~ member_is_proof γ (set_module_params a f) x) (graph_set (code_carrier a) (fun v => select_term γ (f v) x)))
                   (cond (~ member_is_proof γ (set_module_params a' f') x) (graph_set (code_carrier a') (fun v => select_term γ (f' v) x)))).
    apply cond_resp.
    + pose proof (member_is_proof_resp _ _ (set_module_eq_params a a' f f' Ea Hf) x). tauto.
    + apply graph_set_resp_on; [apply code_carrier_resp; exact Ea |]. intros v v' Hv E. apply IH; assumption.
  - cbn [select_term]. pose proof (members_lookup_resp _ _ Hms x) as E.
    destruct (members_lookup ms x), (members_lookup ms' x); cbn in E; try contradiction; [apply set_entry_value_resp; exact E | apply set_eq_refl].
  - cbn [select_term]. apply apply_values_resp; [apply set_eq_refl | exact Hargs].
Qed.

End Operations.
