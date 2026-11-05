(** * Inverting the Typing Rules

    Every term former is introduced by exactly one rule, so a typing derivation
    for a term whose head is known says exactly what that rule says — except that
    [wf_exp_subtyp] may have been applied any number of times afterwards, which
    replaces "the type is [A]" by "the type refines to [A]".  Each lemma below is
    that observation for one former, proved by induction on the derivation with
    only two cases: the introduction rule, where refinement is reflexivity, and
    [wf_exp_subtyp], where it is transitivity.

    Substitutions need no inversion lemmas:

    - [M[σ]] is not a term former, so there is nothing to invert;
    - [wf_sub] is a record, not an inductive family, so a derivation of
      [Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ] carries no information beyond its two fields;
      in particular [Θ ⍮ Ξ ⍮ Γ ⊢ˢ Id : Δ] is itself a context refinement. *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export SubEq.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf.
Import Syntax_Notations Wk_Notations.

Lemma wf_typ_inversion : forall {Θ Ξ Γ i A},
    Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@(S i) ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve.
Qed.

#[export]
Hint Resolve wf_typ_inversion : mctt.

Lemma wf_univ_inversion : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨succl M⟩ ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve.
Qed.

(** The level of a universe that is a type is a level of some sort: the only
    rule that gives a universe a type asks for it. *)
Lemma wf_univ_lvl_inversion : forall {Θ Ξ Γ M A},
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ : A ->
    exists n, Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n.
Proof.
  intros * H.
  dependent induction H; [ eexists; eassumption | apply (IHwf_exp1 _ eq_refl) ].
Qed.

#[export]
Hint Resolve wf_univ_inversion wf_univ_lvl_inversion : mctt.

(** The level forms.  A level is of type [Level] up to subtyping, and so is
    every argument of [succl] and [maxl]; the type of levels [Level@n] is of
    the types of levels ([LevelSort]) up to subtyping. *)
Lemma wf_level_inversion : forall Θ Ξ Γ A n,
    Θ ⍮ Ξ ⍮ Γ ⊢ Level@n : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ LevelSort ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_level_inversion : mctt.

Corollary wf_llit_inversion : forall Θ Ξ Γ A o,
    Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o : A ->
    exists n, Θ ⍮ Ξ ⍮ Γ ⊢ Level@n ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    [ eexists; mauto 3
    | specialize (IHwf_exp1 _ eq_refl) as (n & Hs); exists n; mauto 3 ].
Qed.

#[export]
Hint Resolve wf_llit_inversion : mctt.

(** The same with the bound of the sort the literal is typed at. *)
Corollary wf_llit_inversion_sort : forall Θ Ξ Γ A o,
    Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o : A ->
    exists n, fst o <= n /\ Θ ⍮ Ξ ⍮ Γ ⊢ Level@n ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    [ eexists; split; [ eassumption | mauto 3 ]
    | specialize (IHwf_exp1 _ eq_refl) as (n & Hn & Hs); exists n; split; [ exact Hn | mauto 3 ] ].
Qed.

Corollary wf_succl_inversion : forall Θ Ξ Γ A M,
    Θ ⍮ Ξ ⍮ Γ ⊢ succl M : A ->
    exists n, Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n /\ Θ ⍮ Ξ ⍮ Γ ⊢ Level@n ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    [ eexists; split; [ eassumption | mauto 3 ]
    | specialize (IHwf_exp1 _ eq_refl) as (n & HM & Hs);
      exists n; split; [ exact HM | mauto 3 ] ].
Qed.

#[export]
Hint Resolve wf_succl_inversion : mctt.

Corollary wf_maxl_inversion : forall Θ Ξ Γ A M N,
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl M N : A ->
    exists n, Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n /\ Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n /\ Θ ⍮ Ξ ⍮ Γ ⊢ Level@n ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    [ eexists; repeat split; [ eassumption | eassumption | mauto 3 ]
    | specialize (IHwf_exp1 _ _ eq_refl) as (n & HM & HN & Hs);
      exists n; repeat split; [ exact HM | exact HN | mauto 3 ] ].
Qed.

#[export]
Hint Resolve wf_maxl_inversion : mctt.

(** ** Propositions *)

(** [Prop] is a type of the least large universe, so refines itself. *)
Lemma wf_prop_large : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ Propₘ : Typeω@0.
Proof. intros * HΓ; eapply wf_exp_suniv_large; [ | mauto 3 ]; mauto 3. Qed.

Lemma wf_subtyp_prop_refl : forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ Propₘ ⊆ Propₘ.
Proof. intros * HΓ; exact (wf_subtyp_refl_large _ _ _ _ _ (wf_prop_large _ _ _ HΓ)). Qed.

#[export]
Hint Resolve wf_prop_large wf_subtyp_prop_refl : mctt.

(** The sort of the types of levels is a type of [Typeω@0], up to
    subtyping ([wf_level_sort]). *)
Lemma wf_level_sort_inversion : forall {Θ Ξ Γ A},
    Θ ⍮ Ξ ⍮ Γ ⊢ LevelSort : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

Lemma wf_prop_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ Propₘ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_prop_inversion : mctt.

Lemma wf_True_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Propₘ ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_True_inversion : mctt.

Lemma wf_False_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Propₘ ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_False_inversion : mctt.

(** What ex falso [efq M return C] is typed by. *)
#[warnings="-cannot-define-projection"]
Record absurd_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (M C A : typ) : Prop := mk_absurd_inv
  { (** The sort of the type it returns *)
    absurd_inv_sort : typ
    (** It is a sort *)
  ; absurd_inv_sort_ok : type_sort absurd_inv_sort
    (** The type it returns is of it *)
  ; absurd_inv_typ : Θ ⍮ Ξ ⍮ Γ ⊢ C : absurd_inv_sort
    (** The proof of [⊥] *)
  ; absurd_inv_proof : Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊥
    (** The type it returns is below [A] *)
  ; absurd_inv_sub : Θ ⍮ Ξ ⍮ Γ ⊢ C ⊆ A }.

Lemma wf_absurd_inversion : forall Θ Ξ Γ A M C,
    Θ ⍮ Ξ ⍮ Γ ⊢ efq M return C : A ->
    absurd_inv Θ Ξ Γ M C A.
Proof.
  intros * H.
  dependent induction H.
  - econstructor; [ eassumption | eassumption | eassumption | mautosolve 3 ].
  - destruct (IHwf_exp1 _ _ eq_refl) as [S HS HC HM Hs].
    econstructor; [ exact HS | exact HC | exact HM | eapply wf_subtyp_trans; eassumption ].
Qed.

#[export]
Hint Resolve wf_absurd_inversion : mctt.

(** What a [∀] over a domain of the kind [κ] is typed by. *)
#[warnings="-cannot-define-projection"]
Record all_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (κ : abs_kind) (A P C : typ) : Prop := mk_all_inv
  { (** The sort of the domain *)
    all_inv_sort : typ
    (** It is a sort of the domain's kind *)
  ; all_inv_sort_ok : sort_kind all_inv_sort κ
    (** The domain is of it *)
  ; all_inv_dom : Θ ⍮ Ξ ⍮ Γ ⊢ A : all_inv_sort
    (** The family is of propositions *)
  ; all_inv_cod : Θ ⍮ Ξ ⍮ Γ ▹{κ} A ⊢ P : Propₘ
    (** [Prop] is below [C] *)
  ; all_inv_sub : Θ ⍮ Ξ ⍮ Γ ⊢ Propₘ ⊆ C }.

(** The type of a term refines itself. *)
Lemma wf_subtyp_of_typed : forall {Θ Ξ Γ M A}, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A.
Proof.
  intros * H; destruct (presup_exp_typ H) as [S HS Hi].
  eapply wf_subtyp_refl; [ exact Hi | exact HS | apply wf_exp_eq_refl; exact Hi ].
Qed.

(** What a [Π] at the kinds [κd κc] is typed by: the premises of
    [wf_pi], and its sort below [C]. *)
#[warnings="-cannot-define-projection"]
Record pi_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (κd κc : abs_kind) (A B C : typ) : Prop := mk_pi_inv
  { (** The universe the sorts of the [Π]'s parts are next to *)
    pi_inv_univ : typ
    (** It is a universe *)
  ; pi_inv_univ_ok : Θ ⍮ Ξ ⍮ Γ ⊢ᵤ pi_inv_univ
    (** The domain is of the sort of its kind next to it *)
  ; pi_inv_dom : Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort κd pi_inv_univ
    (** The codomain is of the sort of its kind next to it *)
  ; pi_inv_cod : Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B : (abs_kind_sort κc pi_inv_univ)[↑]ʷ
    (** The kinds are those of a [Π] *)
  ; pi_inv_kinds : pi_kinds κd κc
    (** The [Π]'s sort is below [C] *)
  ; pi_inv_sub : Θ ⍮ Ξ ⍮ Γ ⊢ abs_kind_sort κc pi_inv_univ ⊆ C }.

(** A [Π] is typed by [wf_pi]. *)
Lemma wf_pi_inversion_at : forall {Θ Ξ Γ κd κc A B C},
    Θ ⍮ Ξ ⍮ Γ ⊢ a_pi κd κc A B : C ->
    pi_inv Θ Ξ Γ κd κc A B C.
Proof.
  intros * H.
  dependent induction H.
  - econstructor; [ eassumption | eassumption | eassumption | eassumption |].
    eapply wf_subtyp_of_typed; eapply wf_pi; eassumption.
  - destruct (IHwf_exp1 _ _ _ _ eq_refl) as [U HU HA HB Hk Hs].
    econstructor; [ exact HU | exact HA | exact HB | exact Hk | eapply wf_subtyp_trans; eassumption ].
Qed.

(** The tag of each parameter of a [Π] over a telescope, typed at any
    sort, may be abstracted at the [Π]'s tag ([pi_kinds]). *)
Lemma ctx_pi_at_pi_kinds : forall Θ Ξ r Δ Γ B S, all_assumptions Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi_at r Δ B : S ->
    forall Δ1 κ A Δ2, Δ = (Δ1 ++ ce_ass κ A :: Δ2)%list -> pi_kinds κ r.
Proof.
  intros Θ Ξ r Δ; induction Δ as [| e Δ0 IH] using List.rev_ind; intros * HΔ HB Δ1 κ A Δ2 Heq.
  - destruct Δ1; discriminate.
  - apply List.Forall_app in HΔ as [HΔ0 He]; inversion He as [| ? ? (κ0 & X & ->) _]; subst.
    rewrite ctx_pi_app in HB; cbn [ctx_pi_at] in HB.
    destruct (wf_pi_inversion_at HB) as [U _ _ HBc Hk _].
    destruct Δ2 as [| d Δ2 _] using List.rev_ind.
    + apply List.app_inj_tail in Heq as [_ [= <- _]]; exact Hk.
    + rewrite List.app_comm_cons, List.app_assoc in Heq; apply List.app_inj_tail in Heq as [Heq _].
      exact (IH _ _ _ HΔ0 HBc _ _ _ _ Heq).
Qed.

Lemma wf_all_inversion : forall Θ Ξ Γ κ A P C,
    Θ ⍮ Ξ ⍮ Γ ⊢ ∀ₚ{κ} A P : C ->
    all_inv Θ Ξ Γ κ A P C.
Proof.
  intros * H.
  destruct (wf_pi_inversion_at H) as [U HU HA HB _ Hs]; cbn [abs_kind_sort exp_wk] in HB, Hs.
  destruct (pi_domain_eq_sort HU HA HA ltac:(apply wf_exp_eq_refl; exact HA)) as (S & HS & HA0 & _ & _).
  econstructor; [ exact HS | exact HA0 | exact HB | exact Hs ].
Qed.

#[export]
Hint Resolve wf_all_inversion : mctt.

(** What a [Σₚ] is typed by. *)
#[warnings="-cannot-define-projection"]
Record and_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (P Q C : typ) : Prop := mk_and_inv
  { (** The first component is a proposition *)
    and_inv_left : Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ
    (** The second is one under the first *)
  ; and_inv_right : Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊢ Q : Propₘ
    (** [Prop] is below [C] *)
  ; and_inv_sub : Θ ⍮ Ξ ⍮ Γ ⊢ Propₘ ⊆ C }.

Lemma wf_and_inversion : forall Θ Ξ Γ P Q C,
    Θ ⍮ Ξ ⍮ Γ ⊢ Σₚ P Q : C ->
    and_inv Θ Ξ Γ P Q C.
Proof.
  intros * H.
  dependent induction H.
  - econstructor; [ eassumption | eassumption | mautosolve 3 ].
  - destruct (IHwf_exp1 _ _ eq_refl) as [HP HQ Hs].
    econstructor; [ exact HP | exact HQ | eapply wf_subtyp_trans; eassumption ].
Qed.

#[export]
Hint Resolve wf_and_inversion : mctt.

(** What a proof of the conjunction [Σₚ P Q] is typed by: its components'
    propositions and its components. *)
#[warnings="-cannot-define-projection"]
Record conj_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (P Q M N C : typ) : Prop := mk_conj_inv
  { (** The first component's proposition is one *)
    conj_inv_left_prop_wf : Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ
    (** So is the second's, under the first *)
  ; conj_inv_right_prop_wf : Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊢ Q : Propₘ
    (** The first component *)
  ; conj_inv_left : Θ ⍮ Ξ ⍮ Γ ⊢ M : P
    (** The second component, at the first *)
  ; conj_inv_right : Θ ⍮ Ξ ⍮ Γ ⊢ N : Q[Id,,M]
    (** The conjunction is below [C] *)
  ; conj_inv_sub : Θ ⍮ Ξ ⍮ Γ ⊢ Σₚ P Q ⊆ C }.

Lemma wf_conj_inversion : forall Θ Ξ Γ P Q M N C,
    Θ ⍮ Ξ ⍮ Γ ⊢ a_conj P Q M N : C ->
    conj_inv Θ Ξ Γ P Q M N C.
Proof.
  intros * H.
  dependent induction H.
  - econstructor; try eassumption; mautosolve 3.
  - destruct (IHwf_exp1 _ _ _ _ eq_refl) as [HP HQ HM HN Hs].
    econstructor; try eassumption; eapply wf_subtyp_trans; eassumption.
Qed.

#[export]
Hint Resolve wf_conj_inversion : mctt.

(** What a first projection of a proof of a conjunction is typed by. *)
#[warnings="-cannot-define-projection"]
Record left_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (M C : typ) : Prop := mk_left_inv
  { (** The first component's proposition *)
    left_inv_left_prop : typ
    (** The second's, under the first *)
  ; left_inv_right_prop : typ
    (** The first is a proposition *)
  ; left_inv_left_prop_wf : Θ ⍮ Ξ ⍮ Γ ⊢ left_inv_left_prop : Propₘ
    (** So is the second, under the first *)
  ; left_inv_right_prop_wf : Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} left_inv_left_prop ⊢ left_inv_right_prop : Propₘ
    (** The projected proof *)
  ; left_inv_arg : Θ ⍮ Ξ ⍮ Γ ⊢ M : Σₚ left_inv_left_prop left_inv_right_prop
    (** The first component's proposition is below [C] *)
  ; left_inv_sub : Θ ⍮ Ξ ⍮ Γ ⊢ left_inv_left_prop ⊆ C }.

Lemma wf_left_inversion : forall Θ Ξ Γ M C,
    Θ ⍮ Ξ ⍮ Γ ⊢ a_left M : C ->
    left_inv Θ Ξ Γ M C.
Proof.
  intros * H.
  dependent induction H.
  - econstructor; try eassumption; mautosolve 3.
  - destruct (IHwf_exp1 _ eq_refl) as [P Q HP HQ HM Hs].
    econstructor; try eassumption; eapply wf_subtyp_trans; eassumption.
Qed.

#[export]
Hint Resolve wf_left_inversion : mctt.

(** What a second projection is typed by: the same, at the first
    projection. *)
#[warnings="-cannot-define-projection"]
Record right_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (M C : typ) : Prop := mk_right_inv
  { (** The first component's proposition *)
    right_inv_left_prop : typ
    (** The second's, under the first *)
  ; right_inv_right_prop : typ
    (** The first is a proposition *)
  ; right_inv_left_prop_wf : Θ ⍮ Ξ ⍮ Γ ⊢ right_inv_left_prop : Propₘ
    (** So is the second, under the first *)
  ; right_inv_right_prop_wf : Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} right_inv_left_prop ⊢ right_inv_right_prop : Propₘ
    (** The projected proof *)
  ; right_inv_arg : Θ ⍮ Ξ ⍮ Γ ⊢ M : Σₚ right_inv_left_prop right_inv_right_prop
    (** The second at the first projection is below [C] *)
  ; right_inv_sub : Θ ⍮ Ξ ⍮ Γ ⊢ right_inv_right_prop[Id,,a_left M] ⊆ C }.

Lemma wf_right_inversion : forall Θ Ξ Γ M C,
    Θ ⍮ Ξ ⍮ Γ ⊢ a_right M : C ->
    right_inv Θ Ξ Γ M C.
Proof.
  intros * H.
  dependent induction H.
  - eapply mk_right_inv with (right_inv_left_prop := P) (right_inv_right_prop := Q); try eassumption; mautosolve 3.
  - destruct (IHwf_exp1 _ eq_refl) as [P Q HP HQ HM Hs].
    econstructor; try eassumption; eapply wf_subtyp_trans; eassumption.
Qed.

#[export]
Hint Resolve wf_right_inversion : mctt.

(** A [Π] into types of a universe, over a domain of the kind [κd], is in
    a large universe, or in a small one at a level, its domain of the sort
    of its kind next to that universe. *)
Lemma wf_pi_inversion : forall {Θ Ξ Γ κd A B C},
    Θ ⍮ Ξ ⍮ Γ ⊢ Π{κd} A B : C ->
    (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort κd Typeω@i /\
               Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i ⊆ C) \/
    (exists L n, Θ ⍮ Ξ ⍮ Γ ⊢ L : Level@n /\ Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort κd Type⟨L⟩ /\
               Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B : Type⟨L[↑]ʷ⟩ /\ Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨L⟩ ⊆ C).
Proof.
  intros * H.
  destruct (wf_pi_inversion_at H) as [U HU HA HB _ Hs]; cbn [abs_kind_sort] in HB, Hs.
  inversion HU; subst; cbn [exp_wk] in HB.
  - left; eexists; split; [ exact HA | split; eassumption ].
  - right; do 2 eexists; split; [ eassumption | split; [ exact HA | split; eassumption ] ].
Qed.

#[export]
Hint Resolve wf_pi_inversion : mctt.

(** The level the domain and the codomain are checked at can always be taken to
    be the level of the [Π]-type itself, the domain a type of that universe
    or a proposition.  Moving the refinement [Typeω@j ⊆ Typeω@i] from [Γ]
    into [Γ ▹ A] is a weakening, and it is the only step that needs any
    work: both sides are unchanged by it ([Typeω@j[↑]ʷ] is [Typeω@j]), but only by
    computation, so the step is taken by hand. *)
Corollary wf_pi_inversion' : forall {Θ Ξ Γ κd A B i},
    Θ ⍮ Ξ ⍮ Γ ⊢ Π{κd} A B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : abs_kind_sort κd Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B : Typeω@i.
Proof.
  intros * [(j & HA & HB & Hs) | (L & n & HL & HA & HB & Hs)]%wf_pi_inversion.
  - assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹{κd} A)
      by (eapply wf_ctx_extend_univ_kind; [ apply wf_is_univ_large; mauto 3 | exact HA ]).
    assert (Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ʷ ↑ : Γ) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ exp_wk Typeω@j ↑ ⊆ exp_wk Typeω@i ↑) as H'
      by (eapply wk_preserves_subtyp; eassumption).
    assert (Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ Typeω@j ⊆ Typeω@i) by exact H'.
    split; [ destruct κd; cbn [abs_kind_sort] in HA |- *; [ mauto 3 | exact HA | exact HA ] | mauto 3 ].
  - assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹{κd} A)
      by (eapply wf_ctx_extend_univ_kind; [ eapply wf_is_univ_small; exact HL | exact HA ]).
    assert (Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ʷ ↑ : Γ) by mauto 2.
    assert (Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ L[↑]ʷ : Level@n) by (eapply (wk_preserves_exp _ _ _ _ (Level@n)); eassumption).
    split; [ destruct κd; cbn [abs_kind_sort] in HA |- *; [ eapply wf_exp_suniv_large; eassumption | exact HA | exact HA ] |].
    eapply wf_exp_suniv_large; eassumption.
Qed.

#[export]
Hint Resolve wf_pi_inversion' : mctt.

(** A λ-abstraction is of a [Π] at some kinds: a function, a proof of a
    [∀], or a function between levels. *)
Corollary wf_fn_inversion : forall {Θ Ξ Γ A M C},
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M : C ->
    exists κd κc B, Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ M : B /\ Θ ⍮ Ξ ⍮ Γ ⊢ a_pi κd κc A B ⊆ C.
Proof.
  intros * H.
  dependent induction H.
  - do 3 eexists; split; [ eassumption |].
    eapply wf_subtyp_of_typed; eapply wf_fn; eassumption.
  - destruct (IHwf_exp1 _ _ eq_refl) as (κd & κc & B' & HM & Hs).
    do 3 eexists; split; [ exact HM | eapply wf_subtyp_trans; eassumption ].
Qed.

#[export]
Hint Resolve wf_fn_inversion : mctt.

(** What an application is typed by: a term of a [Π] at some kinds
    applied — a function, a proof of a [∀] or a function between levels. *)
#[warnings="-cannot-define-projection"]
Record app_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (M N C : typ) : Prop := mk_app_inv
  { (** The kind of the domain *)
    app_inv_dom_kind : abs_kind
    (** The kind of the codomain *)
  ; app_inv_cod_kind : abs_kind
    (** The domain *)
  ; app_inv_dom : typ
    (** The codomain *)
  ; app_inv_cod : typ
    (** The applied term is of the [Π] *)
  ; app_inv_fun : Θ ⍮ Ξ ⍮ Γ ⊢ M : a_pi app_inv_dom_kind app_inv_cod_kind app_inv_dom app_inv_cod
    (** The argument is in the domain *)
  ; app_inv_arg : Θ ⍮ Ξ ⍮ Γ ⊢ N : app_inv_dom
    (** The codomain at the argument is below [C] *)
  ; app_inv_sub : Θ ⍮ Ξ ⍮ Γ ⊢ app_inv_cod[Id,,N] ⊆ C }.

Lemma wf_app_inversion : forall {Θ Ξ Γ M N C},
    Θ ⍮ Ξ ⍮ Γ ⊢ M $ N : C ->
    app_inv Θ Ξ Γ M N C.
Proof.
  intros * H.
  dependent induction H.
  - match goal with HM : _ ⍮ _ ⍮ _ ⊢ _ : a_pi _ _ ?A0 _ |- _ =>
      econstructor; [ exact HM | eassumption | eapply wf_subtyp_of_typed; eapply wf_app with (A := A0); eassumption ]
    end.
  - destruct (IHwf_exp1 _ _ eq_refl) as [κd κc X Y HM HN Hs].
    econstructor; [ exact HM | exact HN | eapply wf_subtyp_trans; eassumption ].
Qed.

#[export]
Hint Resolve wf_app_inversion : mctt.

(** What a local definition is typed by: its annotation, of a sort, the
    definition of the annotation, and the body under the definition, at a
    type whose instance at the definition is below [T].  Every local
    definition is annotated. *)
#[warnings="-cannot-define-projection"]
Record let_ann_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (A M B T : typ) : Prop := mk_let_ann_inv
  { (** The annotation's sort *)
    let_ann_inv_sort : typ
    (** The body's type *)
  ; let_ann_inv_body_typ : typ
    (** The sort is a sort *)
  ; let_ann_inv_sort_ok : type_sort let_ann_inv_sort
    (** The annotation is of it *)
  ; let_ann_inv_typed : Θ ⍮ Ξ ⍮ Γ ⊢ A : let_ann_inv_sort
    (** The definition is of the annotation *)
  ; let_ann_inv_def : Θ ⍮ Ξ ⍮ Γ ⊢ M : A
    (** The body is typed under the definition *)
  ; let_ann_inv_body : Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : let_ann_inv_body_typ
    (** The body's type at the definition is below [T] *)
  ; let_ann_inv_sub : Θ ⍮ Ξ ⍮ Γ ⊢ let_ann_inv_body_typ[Id,,M] ⊆ T }.

Lemma wf_let_ann_inversion : forall {Θ Ξ Γ A M B T},
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B : T ->
    let_ann_inv Θ Ξ Γ A M B T.
Proof.
  intros * H.
  dependent induction H.
  - match goal with HB : _ ⍮ _ ⍮ _ ▸ _ ≔ _ ⊢ _ : ?C |- _ => destruct (presup_exp_typ HB) as [SC HSC HC] end.
    apply (mk_let_ann_inv _ _ _ _ _ _ _ Srt C); [ assumption .. |].
    eapply wf_subtyp_refl_typ; [ eapply sub_preserves_sort; [ eassumption | eassumption | mauto 3 ] | eassumption ].
  - destruct (IHwf_exp1 _ _ _ eq_refl) as [S Y HS HA HM HB Hs].
    econstructor; try eassumption; eapply wf_subtyp_trans; eassumption.
Qed.

#[export]
Hint Resolve wf_let_ann_inversion : mctt.

Lemma wf_let_mod_inversion : forall {Θ Ξ Γ U B T},
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B : T ->
    exists C, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U /\
         Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C /\ Θ ⍮ Ξ ⍮ Γ ⊢ C[Id ,,ₘ me_lit U] ⊆ T.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    eexists; repeat split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_let_mod_inversion : mctt.

Lemma wf_vlookup_inversion : forall {Θ Ξ Γ x A},
    Θ ⍮ Ξ ⍮ Γ ⊢ #x : A ->
    exists A', Γ ∋ #x : A' /\ Θ ⍮ Ξ ⍮ Γ ⊢ A' ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ eq_refl));
    destruct_conjs; gen_core_presups; eexists; split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_vlookup_inversion : mctt.

(** We omit [wf_exp_subtyp] as it does not give a useful inversion. *)

(** ** Inductive Types

    The type former, a constructor and the eliminator are each introduced by
    one rule; the inversion of an application of a head is
    [wf_apps_head]. *)

Lemma wf_apps_head : forall {Θ Ξ Γ} Ns M T, Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp M Ns : T -> exists T', Θ ⍮ Ξ ⍮ Γ ⊢ M : T'.
Proof.
  intros Θ Ξ Γ Ns; induction Ns as [| N Ns IH]; intros * H; cbn in H; [ eauto |].
  destruct (IH _ _ H) as (T' & HT'); destruct (wf_app_inversion HT') as [κd κc X Y HM _ _]; eauto.
Qed.

(** What the type former [a_ind p k] is typed by. *)
#[warnings="-cannot-define-projection"]
Record ind_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (p : qname) (k : nat) (T : typ) : Prop := mk_ind_inv
  { (** The group *)
    ind_inv_decl : ind_decl
    (** The member *)
  ; ind_inv_mem : imember
    (** The group is found at [p] *)
  ; ind_inv_lookup : ind_lookup Θ Ξ p = Some ind_inv_decl
    (** The member is the group's [k]-th *)
  ; ind_inv_member : ind_member ind_inv_decl k = Some ind_inv_mem
    (** It is a declared member *)
  ; ind_inv_lt : k < ind_ndecl ind_inv_decl
    (** The type former's type is below [T] *)
  ; ind_inv_sub : Θ ⍮ Ξ ⍮ Γ ⊢ ind_ty ind_inv_decl ind_inv_mem ⊆ T }.

Lemma wf_ind_inversion : forall {Θ Ξ Γ p k T}, Θ ⍮ Ξ ⍮ Γ ⊢ a_ind p k : T -> ind_inv Θ Ξ Γ p k T.
Proof.
  intros * H; dependent induction H.
  - econstructor; try eassumption; eapply wf_subtyp_of_typed; econstructor; eassumption.
  - destruct (IHwf_exp1 _ _ eq_refl) as [D Mk Hl Hk Hlt Hs].
    econstructor; try eassumption; eapply wf_subtyp_trans; eassumption.
Qed.

(** What the constructor [a_con p k c] is typed by. *)
#[warnings="-cannot-define-projection"]
Record con_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (p : qname) (k : nat) (c : String.string) (T : typ) : Prop :=
  mk_con_inv
  { (** The group *)
    con_inv_decl : ind_decl
    (** The member *)
  ; con_inv_mem : imember
    (** The constructor's arguments *)
  ; con_inv_args : list carg
    (** The group is found at [p] *)
  ; con_inv_lookup : ind_lookup Θ Ξ p = Some con_inv_decl
    (** The member is the group's [k]-th *)
  ; con_inv_member : ind_member con_inv_decl k = Some con_inv_mem
    (** [c] is one of its constructors *)
  ; con_inv_con : ind_con con_inv_mem c = Some con_inv_args
    (** The constructor's type is below [T] *)
  ; con_inv_sub : Θ ⍮ Ξ ⍮ Γ ⊢ con_ty p con_inv_decl k con_inv_mem con_inv_args ⊆ T }.

Lemma wf_con_inversion : forall {Θ Ξ Γ p k c T}, Θ ⍮ Ξ ⍮ Γ ⊢ a_con p k c : T -> con_inv Θ Ξ Γ p k c T.
Proof.
  intros * H; dependent induction H.
  - econstructor; try eassumption; eapply wf_subtyp_of_typed; econstructor; eassumption.
  - destruct (IHwf_exp1 _ _ _ eq_refl) as [D Mk gs Hl Hk Hc Hs].
    econstructor; try eassumption; eapply wf_subtyp_trans; eassumption.
Qed.

(** The head of a typed application along terms is typed. *)
Lemma wf_apps_exp_head : forall Θ Ξ Γ Ns M C, Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp M Ns : C -> exists T, Θ ⍮ Ξ ⍮ Γ ⊢ M : T.
Proof.
  intros Θ Ξ Γ; induction Ns as [| N Ns IH]; intros M C H; cbn [apps_exp] in H; [ eexists; exact H |].
  destruct (IH _ _ H) as [T HT].
  destruct (wf_app_inversion HT) as [κd κc X Y HM _ _]; eexists; exact HM.
Qed.

(** The equation of a record view's constructor and the tuple of its
    fields without the premise that the constructor is the view's: the
    typing premise gives it ([wf_con]). *)
Lemma wf_exp_eq_con_rview_any : forall Θ Ξ Γ p D j Mj qr Is fl c Us Ms A,
    ind_lookup Θ Ξ p = Some D -> ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
    List.length Us = ind_nu D -> List.length Ms = List.length fl ->
    Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp (a_con p j c) (Us ++ Ms) : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple (apps_exp (a_record qr) (im_pre Mj Us)) (List.combine fl Ms) : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp (a_con p j c) (Us ++ Ms) ≈ a_tuple (apps_exp (a_record qr) (im_pre Mj Us)) (List.combine fl Ms) : A.
Proof.
  intros * Hl HMj Hh HUl HMl HL HR.
  destruct (wf_apps_exp_head _ _ _ _ _ _ HL) as [T HT].
  destruct (wf_con_inversion HT) as [D' Mj' gs Hl' HMj' Hc _].
  rewrite Hl in Hl'; injection Hl' as <-; rewrite HMj in HMj'; injection HMj' as <-.
  eapply wf_exp_eq_con_rview; eassumption.
Qed.

(** What the eliminator [a_elim r pq Us m Bks M] is typed by: the premises
    of [wf_elim], and the type it gives below [T].  The stored uniform
    parameters are exactly those of the derivation ([elim_inv_ups]): convertible
    ones are reached only through the congruence rule. *)
#[warnings="-cannot-define-projection"]
Record elim_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (r : abs_kind) (pq : qname) (Us : list exp) (m : nat)
    (Bks : list eblock) (M T : typ) : Prop := mk_elim_inv
  { (** The group *)
    elim_inv_decl : ind_decl
    (** The scrutinee's member *)
  ; elim_inv_mem : imember
    (** That member's block *)
  ; elim_inv_block : eblock
    (** The scrutinee type's parameters, uniform then non-uniform *)
  ; elim_inv_params : list exp
    (** The level of the motives' sort, [abs_kind_sort r Typeω@_] *)
  ; elim_inv_level : nat
    (** The group is found at its path *)
  ; elim_inv_lookup : ind_lookup Θ Ξ pq = Some elim_inv_decl
    (** The member is the group's [m]-th *)
  ; elim_inv_member : ind_member elim_inv_decl m = Some elim_inv_mem
    (** Its block is the [m]-th *)
  ; elim_inv_nth : List.nth_error Bks m = Some elim_inv_block
    (** There are as many parameters as the member has *)
  ; elim_inv_params_length : List.length elim_inv_params = im_np elim_inv_decl elim_inv_mem
    (** Each parameter is typed at the member's telescope *)
  ; elim_inv_ps : forall k P T, List.nth_error elim_inv_params k = Some P ->
      List.nth_error (tele_insts (im_params elim_inv_decl elim_inv_mem) Id elim_inv_params) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P : T
    (** The scrutinee is of the member's type at the parameters *)
  ; elim_inv_scrut : Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty pq elim_inv_decl m (List.firstn (ind_nu elim_inv_decl) elim_inv_params)
                                 (List.skipn (ind_nu elim_inv_decl) elim_inv_params)
    (** The stored uniform parameters are the derivation's *)
  ; elim_inv_ups : Us = List.firstn (ind_nu elim_inv_decl) elim_inv_params
    (** The blocks are typed *)
  ; elim_inv_blocks : blocks_typed Θ Ξ Γ pq elim_inv_decl (List.firstn (ind_nu elim_inv_decl) elim_inv_params) Bks r elim_inv_level
    (** The block's motive at the non-uniform parameters and the scrutinee
        is below [T] *)
  ; elim_inv_sub : Θ ⍮ Ξ ⍮ Γ ⊢ (eb_motive elim_inv_block)[sb_of_list Id (List.skipn (ind_nu elim_inv_decl) elim_inv_params ++ M :: nil)] ⊆ T }.

Lemma wf_elim_inversion : forall {Θ Ξ Γ r pq Us m Bks M T}, Θ ⍮ Ξ ⍮ Γ ⊢ a_elim r pq Us m Bks M : T ->
    elim_inv Θ Ξ Γ r pq Us m Bks M T.
Proof.
  intros * H; dependent induction H.
  - econstructor; try eassumption; try reflexivity; [ constructor; eassumption |].
    eapply wf_subtyp_of_typed; eapply wf_elim; try eassumption; reflexivity.
  - destruct (IHwf_exp1 _ _ _ _ _ _ eq_refl) as [D Mm bm Ps i0 Hl Hm Hb HPl HPs HM HUs HBt Hs].
    econstructor; try eassumption; eapply wf_subtyp_trans; eassumption.
Qed.
