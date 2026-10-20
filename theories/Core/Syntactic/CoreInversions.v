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
    every argument of [succl] and [maxl]. *)
Lemma wf_level_inversion : forall Θ Ξ Γ A n,
    Θ ⍮ Ξ ⍮ Γ ⊢ Level@n : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@0 ⊆ A.
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

Lemma wf_True_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_True_inversion : mctt.

Corollary wf_true_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ ⋆ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp eq_refl); mautosolve 4.
Qed.

#[export]
Hint Resolve wf_true_inversion : mctt.

Lemma wf_False_inversion : forall Θ Ξ Γ A,
    Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type@0 ⊆ A.
Proof.
  intros * H.
  dependent induction H; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_False_inversion : mctt.

Lemma wf_exfalso_inversion : forall Θ Ξ Γ A M A',
    Θ ⍮ Ξ ⍮ Γ ⊢ efq M return A' : A ->
    (exists i, Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A' : Typeω@i) /\
    Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊥ /\
    Θ ⍮ Ξ ⍮ Γ ⊢ A'[Id,,M] ⊆ A.
Proof.
  intros * H.
  dependent induction H;
    try (specialize (IHwf_exp1 _ _ eq_refl));
    destruct_conjs; gen_core_presups; repeat split; mautosolve.
Qed.

#[export]
Hint Resolve wf_exfalso_inversion : mctt.

(** A [Π] is in a large universe, or in a small one at a level. *)
Lemma wf_pi_inversion : forall {Θ Ξ Γ A B C},
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : C ->
    (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i ⊆ C) \/
    (exists L n, Θ ⍮ Ξ ⍮ Γ ⊢ L : Level@n /\ Θ ⍮ Ξ ⍮ Γ ⊢ A : Type⟨L⟩ /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type⟨L[↑]ʷ⟩ /\
               Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨L⟩ ⊆ C).
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    try destruct IHwf_exp1 as [(j & ? & ? & ?) | (L' & n' & ? & ? & ? & ?)];
    repeat match goal with Hu : wf_is_univ _ _ _ _ |- _ => inversion Hu; subst; clear Hu end;
    cbn [exp_wk] in *; gen_core_presups.
  - left; eexists; mautosolve 4.
  - right; do 2 eexists; repeat split; try eassumption; mautosolve 4.
  - left; exists j; repeat split; try assumption; mautosolve 4.
  - right; exists L', n'; repeat split; try assumption; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_pi_inversion : mctt.

(** The level the domain and the codomain are checked at can always be taken to
    be the level of the [Π]-type itself.  Moving the refinement [Typeω@j ⊆ Typeω@i]
    from [Γ] into [Γ ▹ A] is a weakening, and it is the only step that needs any
    work: both sides are unchanged by it ([Typeω@j[↑]ʷ] is [Typeω@j]), but only by
    computation, so the step is taken by hand. *)
Corollary wf_pi_inversion' : forall {Θ Ξ Γ A B i},
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i.
Proof.
  intros * [[j [? []]] | [L [n [? [? []]]]]]%wf_pi_inversion.
  2:{ assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
      assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ʷ ↑ : Γ) by mauto 2.
      assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ L[↑]ʷ : Level@n) by (eapply (wk_preserves_exp _ _ _ _ (Level@n)); eassumption).
      split; eapply wf_exp_suniv_large; eassumption. }
  assert (⊢ Θ ⍮ Ξ ⍮ Γ ▹ A) by mauto 3.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ʷ ↑ : Γ) by mauto 2.
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ exp_wk Typeω@j ↑ ⊆ exp_wk Typeω@i ↑) as H'
      by (eapply wk_preserves_subtyp; eassumption).
  assert (Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ Typeω@j ⊆ Typeω@i) by exact H'.
  split; mauto 3.
Qed.

#[export]
Hint Resolve wf_pi_inversion' : mctt.

Corollary wf_fn_inversion : forall {Θ Ξ Γ A M C},
    Θ ⍮ Ξ ⍮ Γ ⊢ λ A M : C ->
    exists B, Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M : B /\ Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ⊆ C.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    eexists; split; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_fn_inversion : mctt.

Lemma wf_app_inversion : forall {Θ Ξ Γ M N C},
    Θ ⍮ Ξ ⍮ Γ ⊢ M $ N : C ->
    exists A B, Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B /\ Θ ⍮ Ξ ⍮ Γ ⊢ N : A /\ Θ ⍮ Ξ ⍮ Γ ⊢ B[Id,,N] ⊆ C.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs;
    do 2 eexists; repeat split; mautosolve 4.
Qed.

#[export]
Hint Resolve wf_app_inversion : mctt.

Lemma wf_let_inversion : forall {Θ Ξ Γ oA M B T},
    Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA M) B : T ->
    exists A i C, let_ann oA A /\ Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : A /\
           Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C /\ Θ ⍮ Ξ ⍮ Γ ⊢ C[Id,,M] ⊆ T.
Proof.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    do 3 eexists; repeat split; first [ solve [ eassumption ] | mautosolve 4 ].
Qed.

(** For an annotated definition, the type is the annotation. *)
Corollary wf_let_ann_inversion : forall {Θ Ξ Γ A M B T},
    Θ ⍮ Ξ ⍮ Γ ⊢ ℓ A ≔ M in B : T ->
    exists i C, Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : A /\
           Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C /\ Θ ⍮ Ξ ⍮ Γ ⊢ C[Id,,M] ⊆ T.
Proof.
  intros * H; destruct (wf_let_inversion H) as (A' & i & C & [[=] | [= <-]] & ?); eauto.
Qed.

#[export]
Hint Resolve wf_let_inversion : mctt.

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
  destruct (IH _ _ H) as (T' & HT'); destruct (wf_app_inversion HT') as (X & Y & HM & _); eauto.
Qed.

Lemma wf_subtyp_of_typed : forall {Θ Ξ Γ M A}, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A.
Proof.
  intros * H; destruct (presup_exp_typ H) as [i Hi].
  eapply wf_subtyp_refl; [ exact Hi | apply wf_exp_eq_refl; exact Hi ].
Qed.

(** What the type former [a_ind p k] is typed by. *)
#[warnings="-cannot-define-projection"]
Record ind_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (p : qname) (k : nat) (T : typ) : Prop := mk_ind_inv
  { ii_decl : ind_decl
  ; ii_mem : imember
  ; ii_lookup : ind_lookup Θ Ξ p = Some ii_decl
  ; ii_member : ind_member ii_decl k = Some ii_mem
  ; ii_lt : k < ind_ndecl ii_decl
  ; ii_sub : Θ ⍮ Ξ ⍮ Γ ⊢ ind_ty ii_decl ii_mem ⊆ T }.

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
  { ci_decl : ind_decl
  ; ci_mem : imember
  ; ci_args : list carg
  ; ci_lookup : ind_lookup Θ Ξ p = Some ci_decl
  ; ci_member : ind_member ci_decl k = Some ci_mem
  ; ci_con : ind_con ci_mem c = Some ci_args
  ; ci_sub : Θ ⍮ Ξ ⍮ Γ ⊢ con_ty p ci_decl k ci_mem ci_args ⊆ T }.

Lemma wf_con_inversion : forall {Θ Ξ Γ p k c T}, Θ ⍮ Ξ ⍮ Γ ⊢ a_con p k c : T -> con_inv Θ Ξ Γ p k c T.
Proof.
  intros * H; dependent induction H.
  - econstructor; try eassumption; eapply wf_subtyp_of_typed; econstructor; eassumption.
  - destruct (IHwf_exp1 _ _ _ eq_refl) as [D Mk gs Hl Hk Hc Hs].
    econstructor; try eassumption; eapply wf_subtyp_trans; eassumption.
Qed.

(** What the eliminator [a_elim oq oUs m Bks M] is typed by: the premises of
    [wf_elim], and the type it gives below [T].  The stored uniform
    parameters are exactly those of the derivation ([ei_ups]): convertible
    ones are reached only through the congruence rule. *)
#[warnings="-cannot-define-projection"]
Record elim_inv (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (oq : option qname) (oUs : option (list exp)) (m : nat)
    (Bks : list eblock) (M T : typ) : Prop := mk_elim_inv
  { ei_grp : qname
  ; ei_decl : ind_decl
  ; ei_mem : imember
  ; ei_block : eblock
  ; ei_params : list exp
  ; ei_lvl : nat
  ; ei_lookup : ind_lookup Θ Ξ ei_grp = Some ei_decl
  ; ei_elim_grp : elim_grp ei_decl oq ei_grp m
  ; ei_member : ind_member ei_decl m = Some ei_mem
  ; ei_nth : List.nth_error Bks m = Some ei_block
  ; ei_plen : List.length ei_params = im_np ei_decl ei_mem
  ; ei_ps : forall k P T, List.nth_error ei_params k = Some P ->
      List.nth_error (tele_insts (im_params ei_decl ei_mem) Id ei_params) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P : T
  ; ei_scrut : Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty ei_grp ei_decl m (List.firstn (ind_nu ei_decl) ei_params)
                                 (List.skipn (ind_nu ei_decl) ei_params)
  ; ei_ups : oUs = elim_ups ei_decl (List.firstn (ind_nu ei_decl) ei_params)
  ; ei_blocks : blocks_typed Θ Ξ Γ ei_grp ei_decl (List.firstn (ind_nu ei_decl) ei_params) Bks ei_lvl
  ; ei_sub : Θ ⍮ Ξ ⍮ Γ ⊢ (eb_motive ei_block)[sb_of_list Id (List.skipn (ind_nu ei_decl) ei_params ++ M :: nil)] ⊆ T }.

Lemma wf_elim_inversion : forall {Θ Ξ Γ oq oUs m Bks M T}, Θ ⍮ Ξ ⍮ Γ ⊢ a_elim oq oUs m Bks M : T ->
    elim_inv Θ Ξ Γ oq oUs m Bks M T.
Proof.
  intros * H; dependent induction H.
  - econstructor; try eassumption; try reflexivity; [ constructor; eassumption |].
    eapply wf_subtyp_of_typed; eapply wf_elim; try eassumption; reflexivity.
  - destruct (IHwf_exp1 _ _ _ _ _ eq_refl) as [p D Mm bm Ps i0 Hl Hg Hm Hb HPl HPs HM HUs HBt Hs].
    econstructor; try eassumption; eapply wf_subtyp_trans; eassumption.
Qed.
