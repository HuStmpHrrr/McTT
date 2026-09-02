(** * Fundamental Theorem: Π-Types

    Four of the old file's lemmas are gone.  [rel_exp_pi_sub], [rel_exp_fn_sub]
    and [rel_exp_app_sub] validated the rules that pushed a substitution under a
    Π, a λ and an application; all three are now *equations* of [exp_sub], holding
    by iota-conversion, so [(Π A B)[σ]] simply *is* [Π (A[σ]) (B[q σ])] and there
    is nothing left to validate.  With them goes [rel_exp_pi_core], which existed
    to share the evidence-indexed [out_rel] family between the congruence and the
    substitution rule; the canonical [per_pi] replaces it.

    What remains is organised around one lemma, [rel_typ_of_pi]: the type
    judgment of a Π, in the form a *stage* of [subtyp_under_ctx] asks for.  Its output is
    the same for all five rules below, because in every one of them the type of
    the judgment is a Π built from the same two premises — a domain judgment and a
    judgment in the extended context — and the element PER is therefore always the
    one canonical [per_pi].  The remaining work of each rule is then only about
    its own four values:

    - [rel_exp_pi_cong] has nothing more to do: the type judgment *is* the goal,
      read at [per_univ i] instead of at the element PER.
    - [rel_exp_fn_cong] applies [rel_exp_under_ctx_q], whose three obligations are
      exactly [per_pi]'s three links once [eval_app_fn] has stripped the λ.
    - [rel_exp_app_cong], [rel_exp_pi_beta] and [rel_exp_fn_eta] all read the
      canonical [per_pi] off a Π-typed judgment with [per_pi_iff], and differ only
      in what they then do with the [rel_mod_app] it hands over.

    The one place cumulativity is needed is the level: [per_univ_elem_pi_canonical]
    insists the domain and the codomain of a Π-value be related at *one* level,
    while the syntax types [A] and [B] at unrelated ones, so every rule whose
    codomain level comes from a presupposition lifts both to their maximum with
    [rel_exp_cumu_ge]. *)

From Stdlib Require Import Lia List Morphisms_Relations PeanoNat RelationClasses.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution.
From Mctt.Core.Completeness Require Import
  ContextCases LogicalRelation SubstitutionCases UniverseCases VariableCases.
Import Domain_Notations.
Import Wk_Notations.

(** ** The Type Judgment of a Π

    A stage of [subtyp_under_ctx] — a related pair of environments and a related
    pair of
    substitutions out of it — turned into the four Π-values it determines,
    together with the canonical element PER they all carry.  Both the four values
    and the PER are forced: [(Π A B)[σ]] is [Π (A[σ]) (B[q σ])] definitionally, so
    [eval_exp_pi] applies to the substituted head as it stands, and the [per_pi]
    is the one [per_univ_elem_pi_chain] produces.

    The domain's own four values are reported together with the *two* pairs a
    caller can need them at, exactly as [rel_typ_of_instance] reports [N]'s: the
    outer pair, which [per_env_extend_sub_intro] and every irrelevance step along
    [q σ] is stated at, and the inner one, which is what [per_pi_iff] must be
    applied with — the middle link of the type chain being
    [Π a2 ρσ B ≈ Π a3 ρ'σ' B']. *)
Lemma rel_typ_of_pi : forall {Γ A A' i B B'},
    Γ ⊨ A ≈ A' : Type@i ->
    Γ ▹ A ⊨ B ≈ B' : Type@i ->
    forall Γ' env_rel',
      EF Γ' ≈ Γ' ∈ per_ctx_env ↘ env_rel' ->
      forall σ σ' ρ ρ' ρσ ρ'σ',
        Γ' ⊨s σ ≈ σ' : Γ ->
        Dom ρ ≈ ρ' ∈ env_rel' ->
        ⟦ σ ⟧s ρ ↘ ρσ ->
        ⟦ σ' ⟧s ρ' ↘ ρ'σ' ->
        exists in_rel a1 a2 a3 a4,
          ⟦ A[σ] ⟧ ρ ↘ a1 /\
          ⟦ A ⟧ ρσ ↘ a2 /\
          ⟦ A' ⟧ ρ'σ' ↘ a3 /\
          ⟦ A'[σ'] ⟧ ρ' ↘ a4 /\
          DF a1 ≈ a4 ∈ per_univ_elem i ↘ in_rel /\
          DF a2 ≈ a3 ∈ per_univ_elem i ↘ in_rel /\
          rel_typ i (Π A B) σ ρ ρσ (Π A' B') σ' ρ' ρ'σ'
            (per_pi in_rel B ρσ B' ρ'σ').
Proof.
  intros * HA HB * HΓ' * Hσj Hρ Hev Hev'.
  pose proof (rel_exp_under_ctx_refl_left HA) as HAself.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ HAgen]].
  destruct (HAgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev')
    as [a1 a2 a3 a4 Ha1 Ha2 Ha3 Ha4 Hachain].
  (** The domain PER, named by weak functionality: both the outer pair the caller
      is owed and the inner one it needs alongside are then just links of the
      *same* chain, with no refinement step in between. *)
  functionalize_per_univ_chain Hachain in_rel.
  exists in_rel, a1, a2, a3, a4.
  do 4 (split; [ eassumption |]).
  do 2 (split; [ pairwise |]).
  apply (mk_rel_exp Πᵈ a1 ρ B[q σ] Πᵈ a2 ρσ B
                    Πᵈ a3 ρ'σ' B' Πᵈ a4 ρ' B'[q σ']);
    [ apply eval_exp_pi; exact Ha1 | apply eval_exp_pi; exact Ha2
    | apply eval_exp_pi; exact Ha3 | apply eval_exp_pi; exact Ha4 |].
  (** The three codomain obligations are, in order, the three [q]-obligations of
      [B] at an argument pair drawn from the domain PER. *)
  eapply per_univ_elem_pi_chain; [ exact Hachain | | |];
    intros c c' Hc;
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ Hρ Ha1
                  ltac:(pairwise) Hc) as Hpair;
    destruct (rel_exp_of_typ_under_ctx_q HΓ' Hσj HAself HB _ _ _ _ _ _ Hpair Hev Hev')
      as [O1 [O2 O3]];
    eassumption.
Qed.

(** ** Π-Congruence *)

Lemma rel_exp_pi_cong : forall {Γ A A' i B B'},
    Γ ⊨ A ≈ A' : Type@i ->
    Γ ▹ A ⊨ B ≈ B' : Type@i ->
    Γ ⊨ Π A B ≈ Π A' B' : Type@i.
Proof.
  intros * HA HB.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  eexists_rel_exp_of_typ.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_pi HA HB _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [in_rel [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter [Hmid Htyp]]]]]]]]]]].
  (** Forgetting the element PER is all that separates a type judgment from a
      judgment in the universe. *)
  eapply rel_typ_implies_rel_exp; eassumption.
Qed.

#[export]
Hint Resolve rel_exp_pi_cong : mctt.

(** ** λ-Congruence

    A λ evaluates to a closure with no premise at all ([eval_exp_fn]), so all four
    of the goal's values are known before anything is proved, and every link of
    the chain is an application of two closures — which [eval_app_fn] turns into
    evaluation of the two bodies in the two extended environments.  Those are
    precisely the three obligations of [rel_exp_under_ctx_q], and they land in
    precisely the [per_head] that [per_pi] asks for. *)
Lemma rel_exp_fn_cong : forall {Γ A A' i B M M'},
    Γ ⊨ A ≈ A' : Type@i ->
    Γ ▹ A ⊨ M ≈ M' : B ->
    Γ ⊨ λ A M ≈ λ A' M' : Π A B.
Proof.
  intros * HA HM.
  pose proof (rel_exp_under_ctx_refl_left HA) as HAself.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  pose proof (presup_rel_exp_under_ctx HM) as [j HB].
  pose proof (rel_exp_cumu_ge (Nat.le_max_l i j) HAself) as HAk.
  pose proof (rel_exp_cumu_ge (Nat.le_max_r i j) HB) as HBk.
  eexists_rel_exp_with (Nat.max i j).
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_pi HAk HBk _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [in_rel [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter [Hmid Htyp]]]]]]]]]]].
  exists (per_pi in_rel B ρσ B ρ'σ').
  split; [ exact Htyp |].
  apply (mk_rel_exp λᵈ ρ M[q σ] λᵈ ρσ M
                    λᵈ ρ'σ' M' λᵈ ρ' M'[q σ']);
    [ apply eval_exp_fn | apply eval_exp_fn | apply eval_exp_fn | apply eval_exp_fn |].
  apply rel_chain_4; hnf; intros c c' Hc;
    pose proof (per_env_extend_sub_intro HΓ' Hσj HAself _ _ _ _ _ _ _ _ Hρ Ha1 Houter Hc)
      as Hpair;
    destruct (rel_exp_under_ctx_q HΓ' Hσj HAself HM _ _ _ _ _ _ Hpair Hev Hev')
      as [[m1 [m2 [Hm1 [Hm2 Hm]]]]
            [[n1 [n2 [Hn1 [Hn2 Hn]]]] [p1 [p2 [Hp1 [Hp2 Hp]]]]]].
  - econstructor; [ apply eval_app_fn; exact Hm1 | apply eval_app_fn; exact Hm2 | exact Hm ].
  - econstructor; [ apply eval_app_fn; exact Hn1 | apply eval_app_fn; exact Hn2 | exact Hn ].
  - econstructor; [ apply eval_app_fn; exact Hp1 | apply eval_app_fn; exact Hp2 | exact Hp ].
Qed.

#[export]
Hint Resolve rel_exp_fn_cong : mctt.

(** ** Application Congruence

    The first of the two rules whose *type* is not a Π but an instantiated
    codomain, and so the first client of [rel_typ_of_instance]: everything the type
    [B[Id,,N]] costs — two instantiations of the codomain judgment, a bridge between
    them, two merges — is done there, once, for this rule and for β and for the
    ℕ-eliminator.  What is left here is the term side.

    The element PER is the canonical one: the head PER of [B] at the arguments the
    *type* names, [⟦N⟧ρσ] and [⟦N⟧ρ'σ']. Each link of [M]'s chain arrives at the
    head PER of its own pair of arguments instead, and [per_head_of_args] moves
    it. *)
Lemma rel_exp_app_cong : forall {Γ A i B M M' N N'},
    Γ ⊨ A ≈ A : Type@i ->
    Γ ▹ A ⊨ B ≈ B : Type@i ->
    Γ ⊨ M ≈ M' : Π A B ->
    Γ ⊨ N ≈ N' : A ->
    Γ ⊨ M $ N ≈ M' $ N' : B[Id ,, N].
Proof.
  intros * HA HB HM HN.
  (** The type mentions [N] on both sides, so it is the reflexive-left form of
      [HN] that the type judgment is built from; [HN] itself is only ever used for
      the term chain. *)
  pose proof (rel_exp_under_ctx_refl_left HN) as HNl.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  destruct HM as [? [? [k HMgen]]].
  destruct HN as [? [? [l HNgen]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  (** *** The Type

      Nothing about it is specific to this rule, so all of it — the type judgment,
      the argument's four values, and the codomain at an arbitrary related pair of
      arguments — comes from [rel_typ_of_instance]. *)
  destruct (rel_typ_of_instance HA HB HNl _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [l' [RN [a1 [a2 [a3 [a4 [p1 [p2 [p3 [p4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter
       [Hmid [Hp1 [Hp2 [Hp3 [Hp4 [Hpchain [Hcod Htyp]]]]]]]]]]]]]]]]]]]]]].
  exists (per_head B B (ρσ ↦ p2) (ρ'σ' ↦ p3)).
  split; [ exact Htyp |].
  (** *** The Argument

      The other instantiation of [N]'s judgment, the one about [N ≈ N'], and its
      chain identified with the reflexive one: the two agree on the values of [A] —
      the type is the same on both sides of both judgments — so [retype_rel_chain]
      puts both chains in one PER, and then they merge. *)
  destruct (HNgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RN2 [HNtyp HNexp]].
  destruct HNtyp as [b1 b2 b3 b4 Hb1 Hb2 Hb3 Hb4 Hbchain].
  destruct HNexp as [n1 n2 n3 n4 Hn1 Hn2 Hn3 Hn4 Hnchain].
  assert (b2 = a2) as -> by (eapply functional_eval_exp; [ exact Hb2 | exact Ha2 ]).
  assert (b3 = a3) as -> by (eapply functional_eval_exp; [ exact Hb3 | exact Ha3 ]).
  retype_rel_chain Hbchain Hmid Hnchain.
  assert (Hp1n1 : p1 = n1) by (eapply functional_eval_exp; [ exact Hp1 | exact Hn1 ]).
  assert (Hp2n2 : p2 = n2) by (eapply functional_eval_exp; [ exact Hp2 | exact Hn2 ]).
  subst p1 p2.
  assert (Hnall : rel_chain RN ([n1; n2; n3; n4; p3; p4]))
    by (merge_rel_chain Hnchain Hpchain n1).
  (** *** The Function

      Its type chain's middle link is a Π of the values of [A] and the syntactic
      [B], which identifies its element PER with the canonical [per_pi] — and then
      each link of its term chain is a function of an argument pair. *)
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RM [HMtyp HMexp]].
  destruct HMtyp as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  destruct HMexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (c2 = Πᵈ a2 ρσ B) as ->
    by (eapply functional_eval_exp; [ exact Hc2 | apply eval_exp_pi; exact Ha2 ]).
  assert (c3 = Πᵈ a3 ρ'σ' B) as ->
    by (eapply functional_eval_exp; [ exact Hc3 | apply eval_exp_pi; exact Ha3 ]).
  assert (HRMmid : DF Πᵈ a2 ρσ B ≈ Πᵈ a3 ρ'σ' B ∈ per_univ_elem k ↘ RM) by pairwise.
  rewrite (per_pi_iff Hmid HRMmid) in Hmchain.
  (** *** The Term Chain

      Three applications, at the three consecutive pairs of arguments; the middle
      value of each link is the same application as the first of the next, which is
      what makes the three [rel_mod_app]s one chain. *)
  assert (Hn12 : Dom n1 ≈ n2 ∈ RN) by pairwise.
  assert (Hn23 : Dom n2 ≈ n3 ∈ RN) by pairwise.
  assert (Hn34 : Dom n3 ≈ n4 ∈ RN) by pairwise.
  assert (Hn2p3 : Dom n2 ≈ p3 ∈ RN) by pairwise.
  assert (Hn22 : Dom n2 ≈ n2 ∈ RN) by pairwise.
  assert (Hn24 : Dom n2 ≈ n4 ∈ RN) by pairwise.
  assert (Hpi1 : per_pi RN B ρσ B ρ'σ' m1 m2)
    by (eapply rel_chain_4_commut_left; first [ eassumption | solve_chain_PER ]).
  assert (Hpi2 : per_pi RN B ρσ B ρ'σ' m2 m3)
    by (eapply rel_chain_4_related; first [ eassumption | solve_chain_PER ]).
  assert (Hpi3 : per_pi RN B ρσ B ρ'σ' m3 m4)
    by (eapply rel_chain_4_commut_right; first [ eassumption | solve_chain_PER ]).
  destruct (Hpi1 _ _ Hn12) as [r1 r2 Hr1 Hr2 Hr].
  destruct (Hpi2 _ _ Hn23) as [s1 s2 Hs1 Hs2 Hs].
  destruct (Hpi3 _ _ Hn34) as [u1 u2 Hu1 Hu2 Hu].
  assert (Hs1e : s1 = r2) by (eapply functional_eval_app; [ exact Hs1 | exact Hr2 ]).
  assert (Hu1e : u1 = s2) by (eapply functional_eval_app; [ exact Hu1 | exact Hs2 ]).
  subst s1 u1.
  apply (mk_rel_exp r1 r2 s2 u2);
    [ eapply eval_exp_app; [ exact Hm1 | exact Hn1 | exact Hr1 ]
    | eapply eval_exp_app; [ exact Hm2 | exact Hn2 | exact Hr2 ]
    | eapply eval_exp_app; [ exact Hm3 | exact Hn3 | exact Hs2 ]
    | eapply eval_exp_app; [ exact Hm4 | exact Hn4 | exact Hu2 ]
    |].
  apply rel_chain_4;
    [ apply (per_head_of_args Hcod n1 n2 n2 p3 Hn12 Hn2p3 Hn22); exact Hr
    | apply (per_head_of_args Hcod n2 n3 n2 p3 Hn23 Hn2p3 Hn23); exact Hs
    | apply (per_head_of_args Hcod n3 n4 n2 p3 Hn34 Hn2p3 Hn24); exact Hu ].
Qed.

#[export]
Hint Resolve rel_exp_app_cong : mctt.

(** ** β

    Its type is [B[Id,,N]] again, so [rel_typ_of_instance] settles that half,
    and what it reports alongside — [N]'s four values, the PER they live in, and the
    codomain at an arbitrary related pair — is exactly what the term half needs, so
    nothing here instantiates a *type* judgment at all.

    The four values of the term are
    [⟦M[q σ]⟧(ρ ↦ n1)], [⟦M⟧(ρσ ↦ n2)], [⟦M[Id,,N]⟧ρ'σ'] and [⟦M[Id,,N][σ']⟧ρ'].
    The first is so because [((λ A M) N)[σ]] *is* [(λ A[σ] M[q σ]) (N[σ])] and
    applying a closure evaluates its body in the extended environment
    ([eval_app_fn]) — which means the redex contributes no evaluation of its own:
    its value is the one [rel_exp_under_ctx_q]'s first obligation already produces,
    at the argument pair [n1 ≈ n2].  That obligation *is* the first link.

    The other two values need the same two instantiations of [M]'s judgment that
    the type needed of [B]'s — along [σ ,, N[σ]] for the outer one, along [Id ,, N]
    at the substituted environments for the inner — and the same bridge between
    them, which here is [M] itself read at the crossing pair of arguments. Three
    merges then select the goal's four values, all at the canonical head PER. *)
Lemma rel_exp_pi_beta : forall {Γ A i B M N},
    Γ ⊨ A ≈ A : Type@i ->
    Γ ▹ A ⊨ B ≈ B : Type@i ->
    Γ ▹ A ⊨ M ≈ M : B ->
    Γ ⊨ N ≈ N : A ->
    Γ ⊨ (λ A M) $ N ≈ M[Id,,N] : B[Id ,, N].
Proof.
  intros * HA HB HM HN.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  pose proof (rel_sub_under_ctx_extend_sub (rel_sub_id (ex_intro _ _ HΓ)) HN) as HidN.
  rewrite exp_sub_id in HidN.
  pose proof HM as [? [? [k HMgen]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_instance HA HB HN _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [j [RN [a1 [a2 [a3 [a4 [n1 [n2 [n3 [n4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter
       [Hmid [Hn1 [Hn2 [Hn3 [Hn4 [Hnchain [Hcod Htyp]]]]]]]]]]]]]]]]]]]]]].
  exists (per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3)).
  split; [ exact Htyp |].
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  (** The argument pairs the links are read at. *)
  assert (Hn12 : Dom n1 ≈ n2 ∈ RN) by pairwise.
  assert (Hn13 : Dom n1 ≈ n3 ∈ RN) by pairwise.
  assert (Hn14 : Dom n1 ≈ n4 ∈ RN) by pairwise.
  assert (Hn22 : Dom n2 ≈ n2 ∈ RN) by pairwise.
  assert (Hn23 : Dom n2 ≈ n3 ∈ RN) by pairwise.
  assert (Hn24 : Dom n2 ≈ n4 ∈ RN) by pairwise.
  (** *** The Redex

      [rel_exp_under_ctx_q] at the argument pair [n1 ≈ n2]. *)
  pose proof (per_env_extend_sub_intro HΓ' Hσj HA _ _ _ _ _ _ _ _ Hρ Ha1 Houter Hn12)
    as Hpair.
  destruct (rel_exp_under_ctx_q HΓ' Hσj HA HM _ _ _ _ _ _ Hpair Hev Hev')
    as [[v1 [v2 [Hv1 [Hv2 Hv]]]] _].
  assert (Hlink1 : Dom v1 ≈ v2 ∈ per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3))
    by (apply (per_head_of_args Hcod n1 n2 n2 n3 Hn12 Hn23 Hn22); exact Hv).
  apply rel_chain_of_pair in Hlink1.
  (** *** The Outer Instantiation

      Along [σ ,, N[σ] ≈ σ' ,, N[σ']], whose right-hand outer value is the goal's
      fourth once [exp_sub_extend_sub] has rewritten it. *)
  destruct (HMgen _ _ HΓ' _ _ (rel_sub_under_ctx_extend_sub Hσj HN) _ _ _ _ Hρ
                  (eval_sub_extend _ _ _ _ _ Hev Hn1)
                  (eval_sub_extend _ _ _ _ _ Hev' Hn4))
    as [RA [HAtyp HAexp]].
  destruct HAtyp as [cA1 cA2 cA3 cA4 HcA1 HcA2 HcA3 HcA4 HcAchain].
  destruct HAexp as [h1 h2 h3 h4 Hh1 Hh2 Hh3 Hh4 Hhchain].
  rewrite <- exp_sub_extend_sub in Hh4.
  destruct (per_head_anchor Hcod n1 n4 n2 n3 Hn14 Hn23 Hn24)
    as [e1 [e2 [He1 [He2 HanchorA]]]].
  assert (e1 = cA2) as -> by (eapply functional_eval_exp; [ exact He1 | exact HcA2 ]).
  assert (e2 = cA3) as -> by (eapply functional_eval_exp; [ exact He2 | exact HcA3 ]).
  retype_rel_chain HcAchain HanchorA Hhchain.
  (** *** The Inner Instantiation

      Along [Id ,, N ≈ Id ,, N] at the substituted environments: its second value
      is the goal's second and its right-hand outer value the goal's third. *)
  destruct (HMgen _ _ HΓ _ _ HidN _ _ _ _ Hρσ
                  (eval_sub_extend _ _ _ _ _ (eval_sub_id _) Hn2)
                  (eval_sub_extend _ _ _ _ _ (eval_sub_id _) Hn3))
    as [RB [HBtyp HBexp]].
  destruct HBtyp as [cB1 cB2 cB3 cB4 HcB1 HcB2 HcB3 HcB4 HcBchain].
  destruct HBexp as [g1 g2 g3 g4 Hg1 Hg2 Hg3 Hg4 Hgchain].
  destruct (per_head_anchor Hcod n2 n3 n2 n3 Hn23 Hn23 Hn23)
    as [f1 [f2 [Hf1 [Hf2 HanchorB]]]].
  assert (f1 = cB2) as -> by (eapply functional_eval_exp; [ exact Hf1 | exact HcB2 ]).
  assert (f2 = cB3) as -> by (eapply functional_eval_exp; [ exact Hf2 | exact HcB3 ]).
  retype_rel_chain HcBchain HanchorB Hgchain.
  (** The goal's second value is produced by this instantiation and by the redex
      alike. *)
  assert (v2 = g2) as -> by (eapply functional_eval_exp; [ exact Hv2 | exact Hg2 ]).
  (** *** The Bridge

      [M] at the pair of arguments that crosses from the one instantiation to the
      other. *)
  destruct (rel_exp_under_ctx_extend_simple HΓ HA HM _ _
              (per_env_extend_intro' Hρσ (per_head_of Ha2 Ha3 Hmid Hn13)))
    as [b1 [b2 [Hb1 [Hb2 Hb]]]].
  assert (b1 = h2) as -> by (eapply functional_eval_exp; [ exact Hb1 | exact Hh2 ]).
  assert (b2 = g3) as -> by (eapply functional_eval_exp; [ exact Hb2 | exact Hg3 ]).
  assert (Hbridge : Dom h2 ≈ g3 ∈ per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3))
    by (apply (per_head_of_args Hcod n1 n3 n2 n3 Hn13 Hn23 Hn23); exact Hb).
  apply rel_chain_of_pair in Hbridge.
  (** *** The Four Values *)
  assert (Hmerge1 : rel_chain (per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3))
                      ([h4; g3]))
    by (merge_rel_chain Hhchain Hbridge h2).
  assert (Hmerge2 : rel_chain (per_head B B (ρσ ↦ n2) (ρ'σ' ↦ n3))
                      ([g2; g4; h4]))
    by (merge_rel_chain Hmerge1 Hgchain g3).
  apply (mk_rel_exp v1 g2 g4 h4);
    [ eapply eval_exp_app;
      [ apply eval_exp_fn | exact Hn1 | apply eval_app_fn; exact Hv1 ]
    | eapply eval_exp_app;
      [ apply eval_exp_fn | exact Hn2 | apply eval_app_fn; exact Hg2 ]
    | exact Hg4
    | exact Hh4
    |].
  merge_rel_chain Hlink1 Hmerge2 g2.
Qed.

#[export]
Hint Resolve rel_exp_pi_beta : mctt.

(** ** η

    The one rule whose statement mentions a weakening rather than a
    substitution — and so the one place the difference between the two
    presentations bites.  With an explicit substitution [M[Wk]] was a *delayed*
    term and [eval_exp_sub] evaluated it in the shifted environment, which made
    this rule a three-liner.  Now [M⟨↑⟩] is a term of its own, and
    [⟦M⟨↑⟩⟧(ρ ↦ c)] is *not* [⟦M⟧ρ]: the two λ-cases are the closures
    [λ (ρ ↦ c) (N⟨wk_q ↑⟩)] and [λ ρ N], which are different values.  So the
    weakening has to be crossed semantically, by instantiating [M]'s own judgment
    along [Wk], which is what [rel_exp_under_ctx_shift_at] does.

    The type is [rel_typ_of_pi] unchanged, and the four values of the term are
    [⟦M[σ]⟧ρ], [⟦M⟧ρσ], [λ ρ'σ' (M⟨↑⟩ #0)] and [λ ρ' ((M⟨↑⟩ #0)[q σ'])], the last
    two by [eval_exp_fn] alone.  Of the three links,

    - the first is [M]'s own left commutation, so η contributes nothing to it;
    - the second *is* η: [M] and the closure of its own weakened body agree on
      every argument, which is [rel_exp_under_ctx_shift_at] at the substituted
      environments, read at the argument pair — the closure's application
      evaluates [M⟨↑⟩ #0] in [ρ'σ' ↦ c'], which is [eval_app_fn] followed by
      [eval_exp_app] on the weakened head and [#0];
    - the third is the right commutation of the closure, which is the third
      obligation of [rel_exp_under_ctx_q] for the *weakened* judgment
      [Γ ▹ A ⊨ M⟨↑⟩ ≈ M⟨↑⟩ : (Π A B)⟨↑⟩] — the value it produces on the right is
      [⟦M⟨↑⟩[q σ']⟧(ρ' ↦ c')], which is the closure body's, and the [per_head] of
      [(Π A B)⟨↑⟩] it produces it in is identified with [per_pi] by the *outer*
      pair of the same weakening instance.

    So both nontrivial links are read off one application of
    [rel_exp_under_ctx_shift_at], the second off its chain and the third off its
    type PER. *)
Lemma rel_exp_fn_eta : forall {Γ A i B M},
    Γ ⊨ A ≈ A : Type@i ->
    Γ ▹ A ⊨ B ≈ B : Type@i ->
    Γ ⊨ M ≈ M : Π A B ->
    Γ ⊨ M ≈ λ A M⟨↑⟩ $ #0 : Π A B.
Proof.
  intros * HA HB HM.
  pose proof (rel_exp_of_typ_inversion HA) as [env_relΓ [HΓ _]].
  pose proof (per_ctx_env_of_typ HΓ HA) as HΓA.
  pose proof (rel_exp_under_ctx_shift HΓA HM) as HMwk.
  pose proof HM as [? [? [k HMgen]]].
  eexists_rel_exp_with i.
  intros Γ' env_rel' HΓ' σ σ' Hσj ρ ρ' ρσ ρ'σ' Hρ Hev Hev'.
  destruct (rel_typ_of_pi HA HB _ _ HΓ' _ _ _ _ _ _ Hσj Hρ Hev Hev')
    as [in_rel [a1 [a2 [a3 [a4 [Ha1 [Ha2 [Ha3 [Ha4 [Houter [Hmid Htyp]]]]]]]]]]].
  exists (per_pi in_rel B ρσ B ρ'σ').
  split; [ exact Htyp |].
  (** [pairwise] needs [per_pi in_rel B ρσ B ρ'σ'] to be known a PER, and what
      makes it one is that it is an element PER — the middle link of the very type
      chain just handed over. *)
  destruct Htyp as [d1 d2 d3 d4 Hd1 Hd2 Hd3 Hd4 Hdchain].
  assert (Hanchor : DF d2 ≈ d3 ∈ per_univ_elem i ↘ (per_pi in_rel B ρσ B ρ'σ'))
    by pairwise.
  assert (Hρσ : Dom ρσ ≈ ρ'σ' ∈ env_relΓ)
    by (eapply (rel_sub_under_ctx_at' Hσj HΓ' HΓ); eassumption).
  (** [M]'s own chain, brought to the canonical [per_pi]. *)
  destruct (HMgen _ _ HΓ' _ _ Hσj _ _ _ _ Hρ Hev Hev') as [RM [HMtyp HMexp]].
  destruct HMtyp as [c1 c2 c3 c4 Hc1 Hc2 Hc3 Hc4 Hcchain].
  destruct HMexp as [m1 m2 m3 m4 Hm1 Hm2 Hm3 Hm4 Hmchain].
  assert (c2 = Πᵈ a2 ρσ B) as ->
    by (eapply functional_eval_exp; [ exact Hc2 | apply eval_exp_pi; exact Ha2 ]).
  assert (c3 = Πᵈ a3 ρ'σ' B) as ->
    by (eapply functional_eval_exp; [ exact Hc3 | apply eval_exp_pi; exact Ha3 ]).
  assert (HRMmid : DF Πᵈ a2 ρσ B ≈ Πᵈ a3 ρ'σ' B ∈ per_univ_elem k ↘ RM) by pairwise.
  rewrite (per_pi_iff Hmid HRMmid) in Hmchain.
  apply (mk_rel_exp m1 m2 λᵈ ρ'σ' (M⟨↑⟩ $ #0) λᵈ ρ' (M⟨↑⟩ $ #0)[q σ']);
    [ exact Hm1 | exact Hm2 | apply eval_exp_fn | apply eval_exp_fn |].
  (** The first link is [M]'s, the other two are read at an argument pair — and
      both from the same instance of [M]'s judgment along [Wk], at the substituted
      environments extended by that pair. *)
  apply rel_chain_4;
    [ pairwise | |];
    hnf; intros c c' Hc;
    pose proof (per_env_extend_intro' Hρσ (per_head_of Ha2 Ha3 Hmid Hc)) as Hpair;
    destruct (rel_exp_under_ctx_shift_at HΓ HA HM _ _ _ _ Hpair)
      as [j [R [b1 [b2 [b3 [b4 [w1 [w2 [w3 [w4 [Hb1 [Hb2 [Hb3 [Hb4 [Hbouter
         [Hbmid [Hw1 [Hw2 [Hw3 [Hw4 Hwchain]]]]]]]]]]]]]]]]]]]];
    assert (b2 = Πᵈ a2 ρσ B) as ->
      by (eapply functional_eval_exp; [ exact Hb2 | apply eval_exp_pi; exact Ha2 ]);
    assert (b3 = Πᵈ a3 ρ'σ' B) as ->
      by (eapply functional_eval_exp; [ exact Hb3 | apply eval_exp_pi; exact Ha3 ]);
    assert (HRpi : R <~> per_pi in_rel B ρσ B ρ'σ')
      by (eapply per_pi_iff; [ exact Hmid | exact Hbmid ]).
  - (** η itself: the instance's *inner* value on the left is [⟦M⟧ρσ], the goal's
        second, and its outer value on the right is [⟦M⟨↑⟩⟧(ρ'σ' ↦ c')], which is
        the head the closure applies. *)
    assert (w2 = m2) as ->
      by (eapply functional_eval_exp; [ exact Hw2 | exact Hm2 ]).
    rewrite HRpi in Hwchain.
    assert (Hlink : Dom m2 ≈ w4 ∈ per_pi in_rel B ρσ B ρ'σ') by pairwise.
    destruct (Hlink _ _ Hc) as [r r' Hr Hr' Hrr'].
    econstructor;
      [ exact Hr
      | apply eval_app_fn; eapply eval_exp_app;
        [ exact Hw4 | apply eval_exp_var | exact Hr' ]
      | exact Hrr' ].
  - (** The closure's own right commutation, from the weakened judgment along
        [q σ']; the weakening instance's *outer* type pair is what identifies the
        [per_head] of [(Π A B)⟨↑⟩] it arrives in with [per_pi]. *)
    pose proof (per_env_extend_sub_intro HΓ' Hσj HA _ _ _ _ _ _ _ _ Hρ Ha1 Houter Hc)
      as Hpair'.
    destruct (rel_exp_under_ctx_q HΓ' Hσj HA HMwk _ _ _ _ _ _ Hpair' Hev Hev')
      as [_ [_ [u [v [Hu [Hv Huv]]]]]].
    assert (HuvR : Dom u ≈ v ∈ R)
      by (eapply Huv; [ exact Hb1 | exact Hb4 | exact Hbouter ]).
    apply HRpi in HuvR.
    destruct (HuvR _ _ Hc) as [r r' Hr Hr' Hrr'].
    (** [(M⟨↑⟩ #0)[q σ']] *is* [(M⟨↑⟩[q σ']) #0], since [(#0)[q σ']] is [#0] by
        [sb_q_zero], so the head is the value [rel_exp_under_ctx_q] reports. *)
    econstructor;
      [ apply eval_app_fn; eapply eval_exp_app;
        [ exact Hu | apply eval_exp_var | exact Hr ]
      | apply eval_app_fn; eapply eval_exp_app;
        [ exact Hv | apply eval_exp_var | exact Hr' ]
      | exact Hrr' ].
Qed.

#[export]
Hint Resolve rel_exp_fn_eta : mctt.
