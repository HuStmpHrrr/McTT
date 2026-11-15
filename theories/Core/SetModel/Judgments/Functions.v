(** * The Set Rules of Functions

    The denotations of [Π] types and of λs, from those of their parts,
    and the set judgments of the rules of functions.  A λ's kind is read
    off its typing: that two typings of one λ give it the same kinds is a
    hypothesis here ([fn_kinds_unique]), a consequence of the NbE
    theorems, discharged where the set fundamental theorem is proved. *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Judgments Require Export Props.
From Mctt.Core.SetModel.Interpretation Require Import Substitution.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
Import ListNotations.

Section Functions.
  (** The context the rules' premises are read at *)
  Variable Θ : gdeps.
  Variable Ξ : gstack.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** The function of a binder's body over its domain. *)
Definition body_function (κ : abs_kind) (F : set_env -> aczel_set) (ρ : set_env) : aczel_set -> aczel_set :=
  fun x => F (set_env_extend ρ (set_entry_term κ x)).

(** A body's function respects equality on its domain. *)
Lemma body_function_respects {GC : GCtx} : forall Γ κ A FA B FB ρ, set_ctx T γ Γ -> set_denotes T γ Γ A FA ->
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

Lemma set_denotes_pi {GC : GCtx} : forall Γ κd κc A B FA FB, set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κd A :: Γ ->
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

(** ** Sorts and Sizes *)


(** A type of levels is a member of every universe of sets. *)
Lemma is_level_type_code_mem : forall V C, grothendieck V -> is_level_type_code C -> set_mem C V.
Proof.
  intros V C HV H. induction H as [C n E | C dom F HF E Hd IHd Hc IHc].
  - eapply set_mem_eq_l; [apply set_eq_sym; exact E | apply grothendieck_level_type_code; exact HV].
  - eapply set_mem_eq_l; [apply set_eq_sym; exact E |]. apply grothendieck_pi_code; [exact HV | exact IHd | | exact IHc].
    intros x y _ Exy. apply HF. exact Exy.
Qed.

(** The value of the sort of the kind [κ] over the universe [U]. *)
Definition kind_sort_value (κ : abs_kind) (FU : set_env -> aczel_set) (ρ : set_env) : aczel_set :=
  match κ with
  | ak_relevant => FU ρ
  | ak_propositional => prop_universe_code
  | ak_level => level_sort_code (level_types_universe T)
  end.

Lemma set_denotes_level_sort {GC : GCtx} : forall Γ, set_denotes T γ Γ a_level_sort (fun _ => level_sort_code (level_types_universe T)).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

Lemma set_denotes_kind_sort {GC : GCtx} : forall Γ κ U FU, set_denotes T γ Γ U FU ->
    set_denotes T γ Γ (abs_kind_sort κ U) (kind_sort_value κ FU).
Proof. intros * HU. destruct κ; cbn [abs_kind_sort kind_sort_value]; [exact HU | apply set_denotes_prop | apply set_denotes_level_sort]. Qed.

(** A member of a sort's carrier is a member of the universe's sets. *)
Lemma kind_sort_value_mem : forall κ FU ρ V C, universe_shape FU ρ V -> set_mem C (code_carrier (kind_sort_value κ FU ρ)) ->
    set_mem C V.
Proof.
  intros κ FU ρ V C [HV [l EU]] HC. destruct κ; cbn [kind_sort_value] in HC.
  - eapply set_mem_eq_r in HC; [| apply code_carrier_resp; exact EU]. unfold universe_code in HC.
    eapply set_mem_eq_r in HC; [| apply code_carrier_type_code].
    apply set_mem_separation in HC as [HC _]; [exact HC | exact is_relevant_code_resp].
  - destruct (is_prop_code_of_prop_universe _ HC) as [P E]. eapply set_mem_eq_l; [apply set_eq_sym; exact E |].
    apply grothendieck_prop_code. exact HV.
  - unfold level_sort_code in HC. eapply set_mem_eq_r in HC; [| apply code_carrier_type_code].
    apply set_mem_separation in HC as [_ HC]; [| exact is_level_type_code_resp]. apply is_level_type_code_mem; assumption.
Qed.

(** A term keeps its value weakened past one more entry. *)
Lemma set_interp_shift {GC : GCtx} : forall Γ e ρ d M v, ⊢ gc_deps ⍮ gc_stack ⍮ e :: Γ -> set_interp T γ Γ ρ M v ->
    set_interp T γ (e :: Γ) (set_env_extend ρ d) (exp_wk M wk_shift) v.
Proof.
  intros * Hc HM. exact (set_interp_wk T γ _ _ _ _ HM nil Γ (e :: Γ) wk_shift _ eq_refl (wf_wk_shift _ _ _ _ Hc) (fun y => eq_refl)).
Qed.

(** The sort of a codomain, read under the domain, is the sort over the
    universe. *)
Lemma kind_sort_value_shift {GC : GCtx} : forall Γ κd A κc U FU FA FS ρ x, set_ctx T γ Γ -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κd A :: Γ ->
    set_denotes T γ Γ U FU -> set_denotes T γ Γ A FA -> set_denotes T γ (ce_ass κd A :: Γ) (exp_wk (abs_kind_sort κc U) wk_shift) FS ->
    set_env_in T γ Γ ρ -> set_mem x (code_carrier (FA ρ)) ->
    set_eq (FS (set_env_extend ρ (set_entry_term κd x))) (kind_sort_value κc FU ρ).
Proof.
  intros * HΓ Hc HU HA HS Hρ Hx.
  pose proof (set_env_in_extend_ass T γ Γ ρ κd A _ x Hρ (set_denotes_exists _ _ _ _ _ HA _ Hρ) Hx) as Hρx.
  destruct κc; cbn [abs_kind_sort kind_sort_value exp_wk] in HS |- *.
  - apply set_eq_sym. exact (set_denotes_unique _ _ _ _ _ HS _ _ _ Hρx (set_interp_shift _ _ _ _ _ _ Hc (set_denotes_exists _ _ _ _ _ HU _ Hρ))).
  - exact (set_denotes_agree _ _ _ _ _ _ _ HS (set_denotes_prop T γ _) Hρx).
  - exact (set_denotes_agree _ _ _ _ _ _ _ HS (set_denotes_level_sort _) Hρx).
Qed.


(** A term of an extension by [A], read in the extension by an equal
    [A'], keeps its denotation. *)
Lemma set_denotes_ctx_conv_ass {GC : GCtx} : forall Γ κ A A' M FA FA' FM, fn_kinds_unique ->
    (forall q, set_module_eq γ (global_module γ q) (global_module γ q)) -> set_ctx T γ Γ ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κ A :: Γ -> gc_deps ⍮ gc_stack ⍮ ce_ass κ A' :: Γ ⊢ˢ sb_id : ce_ass κ A :: Γ ->
    set_denotes T γ Γ A FA -> set_denotes T γ Γ A' FA' -> (forall ρ, set_env_in T γ Γ ρ -> set_eq (FA ρ) (FA' ρ)) ->
    set_denotes T γ (ce_ass κ A :: Γ) M FM -> set_denotes T γ (ce_ass κ A' :: Γ) M FM.
Proof.
  intros * Hfn Hmods HΓ Hc Hσ HA HA' EA HM. apply set_denotes_of_exists; [exact Hfn | exact Hmods | split; [exact HΓ | exists FA'; exact HA'] |].
  intros ρ [Ht (x & x' & a & [E1 E2 Ha Hx Ex])]. apply (set_interp_ctx_conv _ _ _ _ _ _ _ Hc Hσ).
  apply (set_denotes_exists _ _ _ _ _ HM). split; [exact Ht |]. exists x, x', (FA (set_env_tail ρ)). constructor; try assumption.
  - exact (set_denotes_exists _ _ _ _ _ HA _ Ht).
  - eapply set_mem_eq_r; [| exact Hx]. apply code_carrier_resp.
    eapply set_eq_trans; [exact (set_denotes_unique _ _ _ _ _ HA' _ _ _ Ht Ha) | apply set_eq_sym; apply EA; exact Ht].
Qed.


(** ** λs *)

(** The value of a λ of the kinds [κd], [κc]: a proof, or the graph of its
    body on the domain. *)
Definition fn_denotation (κd κc : abs_kind) (FA FM : set_env -> aczel_set) (ρ : set_env) : aczel_set :=
  match κc with
  | ak_propositional => empty_set
  | _ => graph_set (code_carrier (FA ρ)) (body_function κd FM ρ)
  end.

Lemma set_denotes_fn {GC : GCtx} : forall Γ κd κc A M C B FA FM, fn_kinds_unique -> set_ctx T γ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ a_fn A M : a_pi κd κc C B -> ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κd A :: Γ ->
    set_denotes T γ Γ A FA -> set_denotes T γ (ce_ass κd A :: Γ) M FM ->
    set_denotes T γ Γ (a_fn A M) (fn_denotation κd κc FA FM).
Proof.
  intros * Hk HΓ HT Hc HA HM. destruct (set_env_rel_per _ _ _ HΓ) as [Hsym Htrans]. constructor.
  - intros ρ Hρ. pose proof (set_denotes_exists _ _ _ _ _ HA _ Hρ) as Ha.
    destruct κc; cbn [fn_denotation]; [eapply set_interp_fn; [exact HT | discriminate | exact Hc | exact Ha | apply set_eq_refl |]
                                     | eapply set_interp_fn_proof; exact HT
                                     | eapply set_interp_fn; [exact HT | discriminate | exact Hc | exact Ha | apply set_eq_refl |]];
      intros x Hx; apply (set_denotes_exists _ _ _ _ _ HM); exact (set_env_in_extend_ass T γ Γ ρ κd A _ x Hρ Ha Hx).
  - intros ρ ρ' v Hr Hv.
    assert (Hρ : set_env_in T γ Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
    pose proof (set_denotes_exists _ _ _ _ _ HA _ Hρ) as Ha.
    inversion Hv as [ | | | | | | | | | | | | | | | | | | | | | | | ? ? ? ? κd' C' B' HT' | ? ? ? ? κd' κc' C' B' a' X' F' HT' Hκ' _ HA' EX' HM' | | | | | | | | | ];
      subst.
    + destruct (Hk _ _ _ _ _ _ _ _ _ _ _ HT HT') as [_ ->]. apply set_eq_refl.
    + destruct (Hk _ _ _ _ _ _ _ _ _ _ _ HT HT') as [<- <-].
      pose proof (set_denotes_unique _ _ _ _ _ HA _ _ _ Hr HA') as Ea.
      assert (Hacross : respects_across (code_carrier (FA ρ)) (body_function κd FM ρ) F').
      { intros x x' Hx E. unfold body_function. apply set_eq_sym.
        apply (set_denotes_unique _ _ _ _ _ HM _ _ _ (set_env_rel_extend_ass T γ Γ ρ ρ' κd A _ x x' Hr Ha Hx E)).
        apply HM'. eapply set_mem_eq_l; [exact E |]. eapply set_mem_eq_r; [apply code_carrier_resp; apply set_eq_sym; exact Ea | exact Hx]. }
      destruct κc; [| contradiction |]; cbn [fn_denotation]; apply set_eq_sym;
        (apply graph_set_resp_on; [eapply set_eq_trans; [apply code_carrier_resp; apply set_eq_sym; exact Ea | apply set_eq_sym; exact EX']
                                  | exact Hacross]).
Qed.

(** A λ's value is of its [Π]'s carrier: the graph of a body of the
    codomain at each argument, or a proof. *)
Lemma set_fn_value_mem {GC : GCtx} : forall Γ κd κc i A M B FA FS FB FB2 FB' FM FM2, set_ctx T γ Γ ->
    set_denotes T γ Γ A FA ->
    set_exp_eq_with T γ (ce_ass κd A :: Γ) (abs_kind_sort κc (a_typ i)) B B FS FB FB2 ->
    set_exp_eq_with T γ (ce_ass κd A :: Γ) B M M FB' FM FM2 ->
    forall ρ, set_env_in T γ Γ ρ -> set_mem (fn_denotation κd κc FA FM ρ) (code_carrier (pi_denotation κd κc FA FB ρ)).
Proof.
  intros * HΓ HA [HS HB _ _ HBm] [HB' HM _ _ HMm] ρ Hρ. pose proof (set_denotes_exists _ _ _ _ _ HA _ Hρ) as Ha.
  assert (Hx : forall x, set_mem x (code_carrier (FA ρ)) -> set_env_in T γ (ce_ass κd A :: Γ) (set_env_extend ρ (set_entry_term κd x)))
    by (intros x Hx; exact (set_env_in_extend_ass T γ Γ ρ κd A _ x Hρ Ha Hx)).
  assert (HMB : forall x, set_mem x (code_carrier (FA ρ)) -> set_mem (body_function κd FM ρ x) (code_carrier (body_function κd FB ρ x))).
  { intros x Hxa. unfold body_function. eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HB' HB (Hx x Hxa)) |].
    apply HMm. exact (Hx x Hxa). }
  destruct κc; cbn [pi_denotation fn_denotation].
  - unfold pi_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
    apply graph_set_function_on; [| exact (body_function_respects _ _ _ _ _ _ _ HΓ HA HM Hρ) | exact HMB].
    intros x y Hxa E. apply code_carrier_resp. exact (body_function_respects _ _ _ _ _ _ _ HΓ HA HB Hρ _ _ Hxa E).
  - unfold forall_code. apply (proj2 (prop_true_prop_code _)). intros x Hxa.
    assert (HP : is_prop_code (body_function κd FB ρ x)).
    { apply is_prop_code_of_prop_universe. cbn [abs_kind_sort] in HS.
      eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HS (set_denotes_prop T γ _) (Hx x Hxa)) |].
      apply HBm. exact (Hx x Hxa). }
    pose proof (HMB x Hxa) as Hm. unfold prop_true.
    eapply set_mem_eq_l; [exact (prop_code_carrier_empty _ _ HP Hm) | exact Hm].
  - unfold pi_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
    apply graph_set_function_on; [| exact (body_function_respects _ _ _ _ _ _ _ HΓ HA HM Hρ) | exact HMB].
    intros x y Hxa E. apply code_carrier_resp. exact (body_function_respects _ _ _ _ _ _ _ HΓ HA HB Hρ _ _ Hxa E).
Qed.



(** ** Applications *)

Lemma set_denotes_app {GC : GCtx} : forall Γ M N FM FN, set_denotes T γ Γ M FM -> set_denotes T γ Γ N FN ->
    set_denotes T γ Γ (a_app M N) (fun ρ => set_apply (FM ρ) (FN ρ)).
Proof.
  intros * HM HN. constructor.
  - intros ρ Hρ. constructor; [apply (set_denotes_exists _ _ _ _ _ HM) | apply (set_denotes_exists _ _ _ _ _ HN)]; exact Hρ.
  - intros ρ ρ' v Hr Hv. inversion Hv; subst. apply set_apply_resp;
      [exact (set_denotes_unique _ _ _ _ _ HM _ _ _ Hr ltac:(eassumption)) | exact (set_denotes_unique _ _ _ _ _ HN _ _ _ Hr ltac:(eassumption))].
Qed.

(** A function's value applied to an argument's is of the codomain's
    carrier at the argument. *)
Lemma set_apply_value_mem {GC : GCtx} : forall Γ κd κc i A B M M' N N' FA FS FB FB2 FP FM FM' FA' FN FN', set_ctx T γ Γ ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κd A :: Γ -> set_denotes T γ Γ A FA ->
    set_exp_eq_with T γ (ce_ass κd A :: Γ) (abs_kind_sort κc (a_typ i)) B B FS FB FB2 ->
    set_exp_eq_with T γ Γ (a_pi κd κc A B) M M' FP FM FM' ->
    set_exp_eq_with T γ Γ A N N' FA' FN FN' ->
    forall ρ, set_env_in T γ Γ ρ -> set_mem (set_apply (FM ρ) (FN ρ)) (code_carrier (body_function κd FB ρ (FN ρ))).
Proof.
  intros * HΓ Hc HA [HS HB _ _ HBm] [HP HM _ _ HMm] [HA' HN _ _ HNm] ρ Hρ.
  pose proof (set_denotes_agree _ _ _ _ _ _ _ HP (set_denotes_pi _ _ κc _ _ _ _ HΓ Hc HA HB) Hρ) as EP.
  assert (Hn : set_mem (FN ρ) (code_carrier (FA ρ)))
    by (eapply set_mem_eq_r; [apply code_carrier_resp; exact (set_denotes_agree _ _ _ _ _ _ _ HA' HA Hρ) | apply HNm; exact Hρ]).
  pose proof (HMm ρ Hρ) as Hm. eapply set_mem_eq_r in Hm; [| apply code_carrier_resp; exact EP].
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


(** ** η *)


(** ** β *)

(** A term of [Γ ▹{κ} A] denotes, with a term [N] of [A] substituted, its
    value at [N]'s. *)
Lemma set_denotes_single_sub {GC : GCtx} : forall Γ κ A N X FA FN FX, fn_kinds_unique ->
    (forall q, set_module_eq γ (global_module γ q) (global_module γ q)) -> set_ctx T γ Γ ->
    ⊢ gc_deps ⍮ gc_stack ⍮ ce_ass κ A :: Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp N) : ce_ass κ A :: Γ ->
    set_denotes T γ Γ A FA -> set_denotes T γ Γ N FN -> (forall ρ, set_env_in T γ Γ ρ -> set_mem (FN ρ) (code_carrier (FA ρ))) ->
    set_denotes T γ (ce_ass κ A :: Γ) X FX ->
    set_denotes T γ Γ (exp_sub X (sb_extend sb_id (se_exp N))) (fun ρ => body_function κ FX ρ (FN ρ)).
Proof.
  intros * Hfn Hmods HΓ Hc Hσ HA HN HNm HX. apply set_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ |]. intros ρ Hρ.
  apply (set_interp_single_sub T γ Γ ρ κ A N (FN ρ)); [exact Hc | exact Hσ | apply (set_denotes_exists _ _ _ _ _ HN); exact Hρ |].
  apply (set_denotes_exists _ _ _ _ _ HX).
  exact (set_env_in_extend_ass T γ Γ ρ κ A _ _ Hρ (set_denotes_exists _ _ _ _ _ HA _ Hρ) (HNm ρ Hρ)).
Qed.


(** ** The Application Rules *)



End Functions.
