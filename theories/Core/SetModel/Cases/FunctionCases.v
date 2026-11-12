(** * The Set Rules of Functions

    The denotations of [Π] types and of λs, from those of their parts,
    and the set judgments of the rules of functions.  A λ's kind is read
    off its typing: that two typings of one λ give it the same kinds is a
    hypothesis here ([fn_kinds_unique]), a consequence of the NbE
    theorems, discharged where the set fundamental theorem is proved. *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Cases Require Export PropCases.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions.
Import ListNotations.

Section Functions.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** Two typings of a λ give it the same kinds. *)
Definition fn_kinds_unique : Prop :=
  forall Γ A M κd κc C B κd' κc' C' B', gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_fn A M : a_pi κd κc C B ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_fn A M : a_pi κd' κc' C' B' -> κd = κd' /\ κc = κc'.

(** Two denotations of a term agree at an environment. *)
Lemma set_denotes_agree : forall Γ M F G ρ, set_denotes T γ Γ M F -> set_denotes T γ Γ M G -> set_env_in T γ Γ ρ ->
    set_eq (F ρ) (G ρ).
Proof. intros * HF HG Hρ. exact (set_denotes_unique _ _ _ _ _ HG _ _ _ Hρ (set_denotes_exists _ _ _ _ _ HF _ Hρ)). Qed.

(** The function of a binder's body over its domain. *)
Definition body_function (κ : abs_kind) (F : set_env -> aczel_set) (ρ : set_env) : aczel_set -> aczel_set :=
  fun x => F (set_env_extend ρ (set_entry_term κ x)).

(** A body's function respects equality on its domain. *)
Lemma body_function_respects : forall Γ κ A FA B FB ρ, set_ctx T γ Γ -> set_denotes T γ Γ A FA ->
    set_denotes T γ (ce_ass κ A :: Γ) B FB -> set_env_in T γ Γ ρ ->
    respects_on (code_carrier (FA ρ)) (body_function κ FB ρ).
Proof.
  intros * HΓ HA HB Hρ x y Hx E. unfold body_function.
  pose proof (set_denotes_exists _ _ _ _ _ HA _ Hρ) as Ha.
  pose proof (set_env_rel_extend_ass T γ Γ ρ ρ κ A _ x y Hρ Ha Hx E) as Hr.
  assert (Hy : set_mem y (code_carrier (FA ρ))) by (eapply set_mem_eq_l; [exact E | exact Hx]).
  apply set_eq_sym. apply (set_denotes_rel _ _ _ _ _ _ _ HB Hr). exact (set_env_in_extend_ass T γ Γ ρ κ A _ y Hρ Ha Hy).
Qed.

(** ** [Π] Types *)

(** The code of a [Π] of the kinds [κd], [κc], over the domain [FA ρ]
    into the codomains of [FB]. *)
Definition pi_denotation (κd κc : abs_kind) (FA FB : set_env -> aczel_set) (ρ : set_env) : aczel_set :=
  match κc with
  | ak_propositional => forall_code (FA ρ) (body_function κd FB ρ)
  | _ => pi_code (FA ρ) (body_function κd FB ρ)
  end.

Lemma set_denotes_pi : forall Γ κd κc A B FA FB, set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κd A :: Γ ->
    set_denotes T γ Γ A FA -> set_denotes T γ (ce_ass κd A :: Γ) B FB ->
    set_denotes T γ Γ (a_pi κd κc A B) (pi_denotation κd κc FA FB).
Proof.
  intros * HΓ Hc HA HB. destruct (set_env_rel_per _ _ _ HΓ) as [Hsym Htrans]. constructor.
  - intros ρ Hρ. pose proof (set_denotes_exists _ _ _ _ _ HA _ Hρ) as Ha.
    assert (Hb : forall x, set_mem x (code_carrier (FA ρ)) -> set_interp T γ (ce_ass κd A :: Γ) (set_env_extend ρ (set_entry_term κd x)) B (body_function κd FB ρ x))
      by (intros x Hx; apply (set_denotes_exists _ _ _ _ _ HB); exact (set_env_in_extend_ass T γ Γ ρ κd A _ x Hρ Ha Hx)).
    destruct κc; cbn [pi_denotation]; [eapply set_interp_pi; [discriminate | ..] | eapply set_interp_pi_prop | eapply set_interp_pi; [discriminate | ..]];
      eassumption.
  - intros ρ ρ' v Hr Hv.
    assert (Hρ : set_env_in T γ Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
    pose proof (set_denotes_exists _ _ _ _ _ HA _ Hρ) as Ha.
    assert (Hacross : forall a' F', set_eq a' (FA ρ) ->
              (forall x, set_mem x (code_carrier a') -> set_interp T γ (ce_ass κd A :: Γ) (set_env_extend ρ' (set_entry_term κd x)) B (F' x)) ->
              respects_across (code_carrier (FA ρ)) (body_function κd FB ρ) F').
    { intros a' F' Ea HF' x x' Hx E. unfold body_function. apply set_eq_sym.
      apply (set_denotes_unique _ _ _ _ _ HB _ _ _ (set_env_rel_extend_ass T γ Γ ρ ρ' κd A _ x x' Hr Ha Hx E)).
      apply HF'. eapply set_mem_eq_l; [exact E |]. eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact Ea | exact Hx]. }
    inversion Hv as [ | | | | | | | | | | | | | | | | | | | | | ? ? ? ? ? a' F' _ HA' HB' | ? ? ? ? ? ? a' F' Hκ _ HA' HB' | | | | | | | | | | | ]; subst;
      pose proof (set_denotes_unique _ _ _ _ _ HA _ _ _ Hr HA') as Ea; apply set_eq_sym.
    + cbn [pi_denotation]. apply forall_code_resp_on; [apply set_eq_sym; exact Ea | exact (Hacross _ _ Ea HB')].
    + destruct κc; [| contradiction |]; cbn [pi_denotation];
        (apply pi_code_resp_on; [apply set_eq_sym; exact Ea | exact (Hacross _ _ Ea HB')]).
Qed.

(** ** λs *)

(** The value of a λ of the kinds [κd], [κc]: a proof, or the graph of its
    body on the domain. *)
Definition fn_denotation (κd κc : abs_kind) (FA FM : set_env -> aczel_set) (ρ : set_env) : aczel_set :=
  match κc with
  | ak_propositional => empty_set
  | _ => graph_set (code_carrier (FA ρ)) (body_function κd FM ρ)
  end.

Lemma set_denotes_fn : forall Γ κd κc A M C B FA FM, fn_kinds_unique -> set_ctx T γ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_fn A M : a_pi κd κc C B -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κd A :: Γ ->
    set_denotes T γ Γ A FA -> set_denotes T γ (ce_ass κd A :: Γ) M FM ->
    set_denotes T γ Γ (a_fn A M) (fn_denotation κd κc FA FM).
Proof.
  intros * Hk HΓ HT Hc HA HM. destruct (set_env_rel_per _ _ _ HΓ) as [Hsym Htrans]. constructor.
  - intros ρ Hρ. pose proof (set_denotes_exists _ _ _ _ _ HA _ Hρ) as Ha.
    destruct κc; cbn [fn_denotation]; [eapply set_interp_fn; [exact HT | discriminate | exact Hc | exact Ha |]
                                     | eapply set_interp_fn_proof; exact HT
                                     | eapply set_interp_fn; [exact HT | discriminate | exact Hc | exact Ha |]];
      intros x Hx; apply (set_denotes_exists _ _ _ _ _ HM); exact (set_env_in_extend_ass T γ Γ ρ κd A _ x Hρ Ha Hx).
  - intros ρ ρ' v Hr Hv.
    assert (Hρ : set_env_in T γ Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
    pose proof (set_denotes_exists _ _ _ _ _ HA _ Hρ) as Ha.
    inversion Hv as [ | | | | | | | | | | | | | | | | | | | | | | | ? ? ? ? κd' C' B' HT' | ? ? ? ? κd' κc' C' B' a' F' HT' Hκ' _ HA' HM' | | | | | | | | | ];
      subst.
    + destruct (Hk _ _ _ _ _ _ _ _ _ _ _ HT HT') as [_ ->]. apply set_eq_refl.
    + destruct (Hk _ _ _ _ _ _ _ _ _ _ _ HT HT') as [<- <-].
      pose proof (set_denotes_unique _ _ _ _ _ HA _ _ _ Hr HA') as Ea.
      assert (Hacross : respects_across (code_carrier (FA ρ)) (body_function κd FM ρ) F').
      { intros x x' Hx E. unfold body_function. apply set_eq_sym.
        apply (set_denotes_unique _ _ _ _ _ HM _ _ _ (set_env_rel_extend_ass T γ Γ ρ ρ' κd A _ x x' Hr Ha Hx E)).
        apply HM'. eapply set_mem_eq_l; [exact E |]. eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact Ea | exact Hx]. }
      destruct κc; [| contradiction |]; cbn [fn_denotation]; apply set_eq_sym;
        (apply graph_set_resp_on; [apply code_carrier_resp; apply set_eq_sym; exact Ea | exact Hacross]).
Qed.

(** A term of [Prop]'s carrier is a proposition code. *)
Lemma is_prop_code_of_prop_universe : forall C, set_mem C (code_carrier prop_universe_code) -> is_prop_code C.
Proof.
  intros C HC. unfold prop_universe_code in HC. eapply set_mem_eq_r in HC; [| apply code_carrier_type_code].
  destruct HC as [P E]. exists P. exact E.
Qed.

(** The λ rule: [λ A M : Π{κd,κc} A B]. *)
Lemma set_rule_fn : forall Γ κd κc i A M B FA FS FB FB' FM, fn_kinds_unique -> set_ctx T γ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_fn A M : a_pi κd κc A B -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κd A :: Γ ->
    set_denotes T γ Γ A FA ->
    set_exp_eq_with T γ (ce_ass κd A :: Γ) (abs_kind_sort κc (a_typ i)) B B FS FB ->
    set_exp_eq_with T γ (ce_ass κd A :: Γ) B M M FB' FM ->
    set_exp_eq T γ Γ (a_pi κd κc A B) (a_fn A M) (a_fn A M).
Proof.
  intros * Hk HΓ HT Hc HA [HS HB _ HBm] [HB' HM _ HMm].
  exists (pi_denotation κd κc FA FB), (fn_denotation κd κc FA FM).
  constructor; [apply set_denotes_pi; assumption | eapply set_denotes_fn; eassumption .. |].
  intros ρ Hρ. pose proof (set_denotes_exists _ _ _ _ _ HA _ Hρ) as Ha.
  assert (Hx : forall x, set_mem x (code_carrier (FA ρ)) -> set_env_in T γ (ce_ass κd A :: Γ) (set_env_extend ρ (set_entry_term κd x)))
    by (intros x Hx; exact (set_env_in_extend_ass T γ Γ ρ κd A _ x Hρ Ha Hx)).
  assert (HMB : forall x, set_mem x (code_carrier (FA ρ)) -> set_mem (body_function κd FM ρ x) (code_carrier (body_function κd FB ρ x))).
  { intros x Hxa. unfold body_function. eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ HB' HB (Hx x Hxa)) |].
    apply HMm. exact (Hx x Hxa). }
  destruct κc; cbn [pi_denotation fn_denotation].
  - unfold pi_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
    apply graph_set_function_on; [| exact (body_function_respects _ _ _ _ _ _ _ HΓ HA HM Hρ) | exact HMB].
    intros x y Hxa E. apply code_carrier_resp. exact (body_function_respects _ _ _ _ _ _ _ HΓ HA HB Hρ _ _ Hxa E).
  - unfold forall_code. apply (proj2 (prop_true_prop_code _)). intros x Hxa.
    assert (HP : is_prop_code (body_function κd FB ρ x)).
    { apply is_prop_code_of_prop_universe. cbn [abs_kind_sort] in HS.
      eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ HS (set_denotes_prop T γ _) (Hx x Hxa)) |].
      apply HBm. exact (Hx x Hxa). }
    pose proof (HMB x Hxa) as Hm. unfold prop_true.
    eapply set_mem_eq_l; [exact (prop_code_carrier_empty _ _ HP Hm) | exact Hm].
  - unfold pi_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
    apply graph_set_function_on; [| exact (body_function_respects _ _ _ _ _ _ _ HΓ HA HM Hρ) | exact HMB].
    intros x y Hxa E. apply code_carrier_resp. exact (body_function_respects _ _ _ _ _ _ _ HΓ HA HB Hρ _ _ Hxa E).
Qed.

(** ** Applications *)

Lemma set_denotes_app : forall Γ M N FM FN, set_denotes T γ Γ M FM -> set_denotes T γ Γ N FN ->
    set_denotes T γ Γ (a_app M N) (fun ρ => set_apply (FM ρ) (FN ρ)).
Proof.
  intros * HM HN. constructor.
  - intros ρ Hρ. constructor; [apply (set_denotes_exists _ _ _ _ _ HM) | apply (set_denotes_exists _ _ _ _ _ HN)]; exact Hρ.
  - intros ρ ρ' v Hr Hv. inversion Hv; subst. apply set_apply_resp;
      [exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Hr ltac:(eassumption)) | exact (set_denotes_unique _ _ _ _ _ HN _ _ _ Hr ltac:(eassumption))].
Qed.

(** The application rule, at the codomain's instance [C], whose
    denotation is the codomain's at the argument. *)
Lemma set_rule_app : forall Γ κd κc i A B M N C FA FS FB FP FM FA' FN FC, set_ctx T γ Γ ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κd A :: Γ -> set_denotes T γ Γ A FA ->
    set_exp_eq_with T γ (ce_ass κd A :: Γ) (abs_kind_sort κc (a_typ i)) B B FS FB ->
    set_exp_eq_with T γ Γ (a_pi κd κc A B) M M FP FM ->
    set_exp_eq_with T γ Γ A N N FA' FN ->
    set_denotes T γ Γ C FC -> (forall ρ, set_env_in T γ Γ ρ -> set_eq (FC ρ) (body_function κd FB ρ (FN ρ))) ->
    set_exp_eq T γ Γ C (a_app M N) (a_app M N).
Proof.
  intros * HΓ Hc HA [HS HB _ HBm] [HP HM _ HMm] [HA' HN _ HNm] HC EC.
  exists FC, (fun ρ => set_apply (FM ρ) (FN ρ)).
  constructor; [exact HC | apply set_denotes_app; assumption .. |]. intros ρ Hρ.
  pose proof (set_denotes_agree _ _ _ _ _ HP (set_denotes_pi _ _ κc _ _ _ _ HΓ Hc HA HB) Hρ) as EP.
  assert (Hn : set_mem (FN ρ) (code_carrier (FA ρ)))
    by (eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ HA' HA Hρ) | apply HNm; exact Hρ]).
  pose proof (HMm ρ Hρ) as Hm. eapply set_mem_eq_r in Hm; [| apply code_carrier_resp; exact EP].
  eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact (EC ρ Hρ) |].
  destruct κc; cbn [pi_denotation] in Hm.
  - unfold pi_code in Hm. eapply set_mem_eq_r in Hm; [| apply code_carrier_type_code].
    apply (function_set_apply_on (FM ρ) (code_carrier (FA ρ)) (fun x => code_carrier (body_function κd FB ρ x)) (FN ρ));
      [| exact Hm | exact Hn].
    intros x y Hx E. apply code_carrier_resp. exact (body_function_respects _ _ _ _ _ _ _ HΓ HA HB Hρ _ _ Hx E).
  - unfold forall_code, prop_code in Hm. eapply set_mem_eq_r in Hm; [| apply code_carrier_type_code].
    apply set_mem_truth in Hm as [Hall Hm0].
    eapply set_mem_eq_l; [| exact (Hall _ Hn)].
    eapply set_eq_trans; [| apply set_eq_sym; apply set_apply_resp; [exact Hm0 | apply set_eq_refl]].
    apply set_eq_sym. apply set_apply_empty.
  - unfold pi_code in Hm. eapply set_mem_eq_r in Hm; [| apply code_carrier_type_code].
    apply (function_set_apply_on (FM ρ) (code_carrier (FA ρ)) (fun x => code_carrier (body_function κd FB ρ x)) (FN ρ));
      [| exact Hm | exact Hn].
    intros x y Hx E. apply code_carrier_resp. exact (body_function_respects _ _ _ _ _ _ _ HΓ HA HB Hρ _ _ Hx E).
Qed.

End Functions.
