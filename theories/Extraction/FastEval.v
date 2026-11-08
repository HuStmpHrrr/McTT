(** * The Evaluation the Extracted Checker Runs

    A copy of the evaluation relations ([Core.Semantic.Evaluation]), at a
    mode ([SkipMode]).  With the skip on, one rule changes: the eliminator
    of a group of inductive types at a constructor computes the recursive
    result of a recursive argument only when the branch reads it, that is,
    when its variable is not fresh in the branch ([exp_freshb]); an unused
    entry is [𝕌ω@0] ([fast_eval_ihs_skip]), at the type the branch's
    telescope gives it.  With it off, the relations are Core's
    ([Extraction.FastEquiv]).

    The decision is syntactic and builds nothing.

    The values of the two evaluations agree except in the entries of
    environments that nothing reads: [Extraction.Simulation] makes this
    precise. *)
From Stdlib Require Import Lia List Morphisms PeanoNat Relations String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Records Fresh.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import Domain Evaluation Readback.
Import Domain_Notations.
Import Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.
#[local] Open Scope bool_scope.

(** ** Deciding Freshness

    [exp_freshb] and its list helpers are in [Core.Syntactic.Fresh], with
    soundness and completeness ([exp_freshb_iff]). *)

(** Whether a branch [B] reads none of the [k] recursive results of one
    argument, the entries [base] to [base + k - 1] of its environment.
    [None] stands for a computation every result of which is read: the
    recursive results of a record view's fields, which become those of the
    argument the view is at. *)
Definition ihs_skipb (oB : option exp) (base k : nat) : bool :=
  match oB with
  | Some B => List.forallb (fun i => exp_freshb (base + i) B) (List.seq 0 k)
  | None => false
  end.

(** A skipped argument's results are each unread. *)
Lemma ihs_skipb_sound : forall oB base k, ihs_skipb oB base k = true ->
    exists B, oB = Some B /\ forall i, i < k -> exp_fresh (base + i) B.
Proof.
  intros [B |] * H; cbn in H; [| discriminate ].
  exists B; split; [ reflexivity |]; intros i Hi.
  apply exp_freshb_sound; apply (proj1 (List.forallb_forall _ _) H), List.in_seq; lia.
Qed.

(** Whether the skip is on.  With it off, every recursive result is
    computed and the relations are those of [Core.Semantic.Evaluation]
    ([Extraction.FastEquiv]); the extracted normalizer runs with it on,
    and recomputes with it off where a normal form has a proof in it
    ([Extraction.NbE]). *)
Class SkipMode : Set := mk_skip_mode
  { (** The skip is on. *)
    skip_on : bool }.

(** The skip at a mode: on, and the branch reads none of the results. *)
Definition ihs_skip_at (sk : bool) (oB : option exp) (base k : nat) : bool := sk && ihs_skipb oB base k.

(** A skipped argument's results are each unread. *)
Lemma ihs_skip_at_sound : forall sk oB base k, ihs_skip_at sk oB base k = true ->
    sk = true /\ exists B, oB = Some B /\ forall i, i < k -> exp_fresh (base + i) B.
Proof.
  intros * H; unfold ihs_skip_at in H; apply andb_prop in H as [-> H].
  split; [ reflexivity | exact (ihs_skipb_sound _ _ _ H) ].
Qed.

(** With the skip off, nothing is skipped. *)
Lemma ihs_skip_at_off : forall oB base k, ihs_skip_at false oB base k = false.
Proof. reflexivity. Qed.

(** ** The Relations *)

Reserved Notation "'⟦' M '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, M at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'$ᶠ|' m '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦elimᶠ' m 'at' j 'of' p ups Bks '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, m at level 69, j at level 0, p at level 0, ups at level 0, Bks at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ihsᶠ' vs 'of' gs 'under' p ups Bks 'for' B '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, vs at level 69, gs at level 69, p at level 0, ups at level 0, Bks at level 0, B at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ihᶠ' v 'of' t 'under' p ups Bks '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, v at level 69, t at level 69, p at level 0, ups at level 0, Bks at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦mrefᶠ' j 'of' p ups '⟧ᶠ' Θ '⍮' Ξ '↘' r" (at level 70, j at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦shtyᶠ' t 'of' p ups '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, t at level 69, p at level 0, ups at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ihtyᶠ' v 'of' t 'at' p ups 'under' ρm As '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, v at level 69, t at level 69, p at level 0, ups at level 0, ρm at level 0, As at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦ihtysᶠ' vs 'of' gs 'at' p ups 'under' ρm As '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, vs at level 69, gs at level 69, p at level 0, ups at level 0, ρm at level 0, As at level 0, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦projsᶠ' fl 'of' v '⟧ᶠ' Θ '⍮' Ξ '↘' ws" (at level 70, fl at level 69, v at level 69, Θ at level 69, Ξ at level 69, ws at level 69).
Reserved Notation "'⟦' H '⟧ᵐᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, H at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦' Ms '⟧*ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' ms" (at level 70, Ms at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, ms at level 69).
Reserved Notation "'⟦' Φ '⟧ᵇᶠ' Θ '⍮' Ξ '⍮' ρ '↘' ρ'" (at level 70, Φ at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, ρ' at level 69).
Reserved Notation "'$*ᶠ|' m '&' ns '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, ns at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'$ᵐᶠ|' h '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, h at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'$ᵐ*ᶠ|' h '&' ns '|' Θ '⍮' Ξ '↘' r" (at level 70, h at level 69, ns at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦' Δ '⊢' D '⟧ᶜᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" (at level 70, Δ at level 69, D at level 69, Θ at level 69, Ξ at level 69, ρ at level 69, r at level 69).
Reserved Notation "h '·ₜᶠ' x Θ '⍮' Ξ '↘' r" (at level 70, x at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "h '·ₘᶠ' y Θ '⍮' Ξ '↘' r" (at level 70, y at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "h '·ₜ*ᶠ' ch Θ '⍮' Ξ '↘' r" (at level 70, ch at level 0, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "h '·ₘ*ᶠ' ch Θ '⍮' Ξ '↘' r" (at level 70, ch at level 0, Θ at level 69, Ξ at level 69, r at level 69).

Generalizable All Variables.

(** The rules of [Core.Semantic.Evaluation], one for one, but for the rules
    of a recursive argument's result: the recursive results of a
    constructor's arguments are computed for the branch that reads them. *)
Inductive fast_eval_exp {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : exp -> env -> domain -> Prop :=
(** A universe is its own value. *)
| fast_eval_exp_typ :
  `( ⟦ Typeω@i ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ 𝕌ω@i )
(** A small universe evaluates its level. *)
| fast_eval_exp_univ :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ l ->
     ⟦ Type⟨M⟩ ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ 𝕌@l )
(** [Level] is a value. *)
| fast_eval_exp_level :
  `( ⟦ Level@n ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ Levelᵈ@n )
(** So is the sort of the types of levels. *)
| fast_eval_exp_level_sort :
  `( ⟦ LevelSort ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ LevelSortᵈ )
(** A level literal is the flat level with that constant and no atom. *)
| fast_eval_exp_llit :
  `( ⟦ 𝕃ᵒ o ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ domain_level_lit o )
(** The successor of a level: the flat successor of its value. *)
| fast_eval_exp_succl :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ succl M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ domain_level_suc m )
(** The join of two levels: the flat join of their values. *)
| fast_eval_exp_maxl :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     ⟦ maxl M N ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ domain_level_max m n )
(** A variable is read off the environment. *)
| fast_eval_exp_var :
  `( ⟦ #x ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ x )
(** [Prop] is a value. *)
| fast_eval_exp_prop :
  `( ⟦ Propₘ ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ Propᵈ )
(** [⊤] is a value. *)
| fast_eval_exp_True :
  `( ⟦ ⊤ ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⊤ᵈ )
(** The introduction of [⊤] is a proof, kept as it is. *)
| fast_eval_exp_tt :
  `( ⟦ a_tt ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ⟨a_tt, ρ⟩ )
(** [⊥] is a value. *)
| fast_eval_exp_False :
  `( ⟦ ⊥ ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⊥ᵈ )
(** Ex falso is stuck at its type, on the proof kept as it is. *)
| fast_eval_exp_absurd :
  `( ⟦ C ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ c ->
     ⟦ efq M return C ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ c (efqᵈ ⋆ᵈ⟨M, ρ⟩ return c) )
(** A [Σₚ] evaluates its first component and closes over its second. *)
| fast_eval_exp_and :
  `( ⟦ P ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ p ->
     ⟦ Σₚ P Q ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ Σₚᵈ p ρ Q )
(** The proof of a conjunction is kept as it is. *)
| fast_eval_exp_conj :
  `( ⟦ a_conj P Q M N ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ⟨a_conj P Q M N, ρ⟩ )
(** So is the proof of its first component. *)
| fast_eval_exp_left :
  `( ⟦ a_left M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ⟨a_left M, ρ⟩ )
(** And that of its second. *)
| fast_eval_exp_right :
  `( ⟦ a_right M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ⟨a_right M, ρ⟩ )
(** The type former of a member is a value, with no argument yet. *)
| fast_eval_exp_indty :
  `( ⟦ a_ind p k ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_ind p k nil )
(** A constructor that is a value of its own before any argument. *)
| fast_eval_exp_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_starts D Mk = true ->
     ⟦ a_con p k c ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_con p k c nil )
(** A constructor of a view of a group with no uniform parameters: the
    container's, at the view's arguments. *)
| fast_eval_exp_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ind_nu D = 0 ->
     ⟦ Is ⟧*ᶠ Θ ⍮ Ξ ⍮ nil ↘ cups ->
     ⟦ a_con p j c ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_con qc k c cups )
(** The constructor of a record view with fields, waiting for them. *)
| fast_eval_exp_con_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     ind_nu D = 0 ->
     0 < List.length fl ->
     ⟦ a_con p j c ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_con p j c nil )
(** The constructor of a record view without fields: the empty tuple. *)
| fast_eval_exp_con_rview_empty :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is nil ->
     ind_nu D = 0 ->
     ⟦ a_con p j c ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_tuple nil )
(** The eliminator into types: evaluates its scrutinee and eliminates it. *)
| fast_eval_exp_elim :
  `( ⟦ Us ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ups ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦elimᶠ m at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ a_elim ak_relevant p Us j Bks M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** An eliminator into propositions is a proof, kept as it is. *)
| fast_eval_exp_elim_proof :
  `( ⟦ a_elim ak_propositional p Us j Bks M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⋆ᵈ⟨a_elim ak_propositional p Us j Bks M, ρ⟩ )
(** A [Π] evaluates its domain and closes over its codomain. *)
| fast_eval_exp_pi :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     ⟦ a_pi κd κc A B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_pi κd κc a ρ B )
(** A function evaluates its domain and closes over its body. *)
| fast_eval_exp_fn :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     ⟦ λ A M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ λᵈ a ρ M )
(** An application at an evaluated argument. *)
| fast_eval_exp_app :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     evaluated_kind (arg_kind Θ Ξ m) ->
     ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     $ᶠ| m & n | Θ ⍮ Ξ ↘ r ->
     ⟦ M $ N ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** An application at a proof: the proof kept as it is. *)
| fast_eval_exp_app_proof :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     arg_kind Θ Ξ m = ak_propositional ->
     $ᶠ| m & ⋆ᵈ⟨N, ρ⟩ | Θ ⍮ Ξ ↘ r ->
     ⟦ M $ N ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A local definition at a type of an evaluated kind. *)
| fast_eval_exp_let :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     evaluated_kind (domain_kind a) ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ m ⦂ entry_type_value a ↘ r ->
     ⟦ ℓ A ≔ M in B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A local definition at a proposition: its body kept as it is. *)
| fast_eval_exp_let_proof :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     domain_kind a = ak_propositional ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ ⋆ᵈ⟨M, ρ⟩ ⦂ entry_type_value a ↘ r ->
     ⟦ ℓ A ≔ M in B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A local module: the unit's closure, at the unit. *)
| fast_eval_exp_let_mod :
  `( ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ᵐ h ⦂ gu_mk Δ D ↘ r ->
     ⟦ ℓₘ (gu_mk Δ D) in B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A local definition with a module part: its body at its type, and the
    value of the unit's literal at the unit, as [eval_exp_let_dm] *)
| fast_eval_exp_let_dm :
  `( ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ me_lit U ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ᵈ m ⦂ entry_type_value a ‖ h ⦂ U ↘ r ->
     ⟦ ℓᵈ A ≔ M ‖ U in B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A member: read off the root of its module expression, then applied to
    the module's arguments. *)
| fast_eval_exp_mem :
  `( modexp_spine H = (R, args, pre) ->
     ⟦ R ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     h ·ₜ*ᶠ (pre ++ x :: nil) Θ ⍮ Ξ ↘ f ->
     ⟦ args ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ns ->
     $*ᶠ| f & ns | Θ ⍮ Ξ ↘ r ->
     ⟦ a_mem H x ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** A record's type former is a value, with no argument yet. *)
| fast_eval_exp_record :
  `( ⟦ a_record p ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_record p nil )
(** A record element: the tuple of its fields' values, by name. *)
| fast_eval_exp_tuple :
  `( ⟦ T ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_record p ns ->
     record_lookup Θ Ξ p = Some R ->
     fast_eval_field_vals Θ Ξ (record_field_kinds R) (List.map snd fs) ρ vs ->
     ⟦ a_tuple T fs ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_tuple (List.combine (List.map fst fs) vs) )
(** A field: the field of the value. *)
| fast_eval_exp_proj :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     fast_eval_proj Θ Ξ f m r ->
     ⟦ a_proj f M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
where "'⟦' e '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (fast_eval_exp Θ Ξ e ρ r)
(** The field [f] of a value, as [eval_proj] *)
with fast_eval_proj {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : string -> domain -> domain -> Prop :=
(** A tuple: its field *)
| fast_eval_proj_tuple :
  `( field_lookup vs f = Some r ->
     fast_eval_proj Θ Ξ f (d_tuple vs) r )
(** A neutral: its projection, at the field's type *)
| fast_eval_proj_neut :
  `( record_lookup Θ Ξ p = Some R ->
     field_index (record_fields R) f = Some k ->
     fast_eval_neutral_fields Θ Ξ m (env_tele nil (List.rev (record_params R)) ns) (List.firstn (S k) (record_fields R)) rs ->
     List.nth_error rs k = Some r ->
     fast_eval_proj Θ Ξ f (⇑ (d_record p ns) m) r )
(** The neutral projections of a neutral at fields, as
    [eval_neutral_fields] *)
with fast_eval_neutral_fields {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : domain_ne -> env -> list (string * exp) -> list domain -> Prop :=
(** No field left *)
| fast_eval_neutral_fields_nil :
  `( fast_eval_neutral_fields Θ Ξ m ρ nil nil )
(** The next field's projection, at its type, then the rest *)
| fast_eval_neutral_fields_cons :
  `( ⟦ T ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a ->
     fast_eval_neutral_fields Θ Ξ m (ρ ↦ ⇑ a (d_proj g m) ⦂ entry_type_closure T ρ) fl rs ->
     fast_eval_neutral_fields Θ Ξ m ρ ((g, T) :: fl) (⇑ a (d_proj g m) :: rs) )
(** The eliminator on a value, as [eval_elim]: on a constructor, the
    recursive results are computed for the branch ([Some B]). *)
with fast_eval_elim {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> nat -> domain -> domain -> Prop :=
(** On a saturated constructor: its branch *)
| fast_eval_elim_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_ref p j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     ind_con Mj c = Some gs ->
     List.length vs = (im_np Dq Mk + List.length gs)%nat ->
     List.nth_error Bks j = Some b ->
     brs_lookup (eb_brs b) c = Some (n, B) ->
     n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat ->
     leaves_coherent D ->
     ⟦ihsᶠ skipn (im_np Dq Mk) vs of gs under p ups Bks for (Some B) ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ env_extend_typed ρ (branch_entries D Mj p ups (blocks_motives Bks) ρ gs
                                     (skipn (ind_nu Dq) (firstn (im_np Dq Mk) vs)) (skipn (im_np Dq Mk) vs) ihs) ↘ r ->
     ⟦elimᶠ d_con pc k c vs at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** On a neutral: a stuck eliminator, at the motive's instance *)
| fast_eval_elim_neut :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_ref p j Mj = (pc, k) ->
     ind_lookup Θ Ξ pc = Some Dq ->
     ind_member Dq k = Some Mk ->
     List.length as' = im_np Dq Mk ->
     List.nth_error Bks j = Some b ->
     eb_binder_count b = S (im_nn Mk) ->
     ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pc, k, cups) ->
     ⟦ eb_motive b ⟧ᶠ Θ ⍮ Ξ ⍮ env_extend_typed ρ (motive_entries D Mj ups (List.skipn (ind_nu Dq) as')
                                           (d_ind pc k (cups ++ List.skipn (ind_nu Dq) as')) (⇑ (d_ind pc k as') m)) ↘ a ->
     ⟦elimᶠ ⇑ (d_ind pc k as') m at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ⇑ a (d_elim ρ Bks p ups j as' m) )
where "'⟦elimᶠ' m 'at' j 'of' p ups Bks '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (fast_eval_elim Θ Ξ ρ p ups Bks j m r)
(** The recursive results of the arguments [vs] of a constructor, for the
    branch [B] ([Some B]): those of a recursive argument, one per leaf
    path of its shape, are computed only when [B] reads one of them.  The
    results of the recursive argument at the head of [ca_rec t :: gs] are
    the variables [cargs_nrec D gs] on of [B], since the results of the
    recursive arguments after it come after it in [B]'s environment.
    [None] computes them all. *)
with fast_eval_ihs {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> option exp -> list carg -> list domain -> list domain -> Prop :=
(** No argument, no result *)
| fast_eval_ihs_nil :
  `( ⟦ihsᶠ nil of nil under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ nil )
(** A non-recursive argument has none *)
| fast_eval_ihs_arg :
  `( ⟦ihsᶠ vs of gs under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ihsᶠ v :: vs of ca_arg r T :: gs under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs )
(** The branch reads one of the recursive results: they are computed. *)
| fast_eval_ihs_rec :
  `( ind_lookup Θ Ξ p = Some D ->
     ihs_skip_at skip_on oB (cargs_nrec D gs) (List.length (shape_leaves (rview_leaves D) 0 t)) = false ->
     ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs1 ->
     ⟦ihsᶠ vs of gs under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ihsᶠ v :: vs of ca_rec t :: gs under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs1 ++ ihs )
(** It reads none: each entry is [𝕌ω@0], which nothing reads. *)
| fast_eval_ihs_skip :
  `( ind_lookup Θ Ξ p = Some D ->
     ihs_skip_at skip_on oB (cargs_nrec D gs) (List.length (shape_leaves (rview_leaves D) 0 t)) = true ->
     ⟦ihsᶠ vs of gs under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
     ⟦ihsᶠ v :: vs of ca_rec t :: gs under p ups Bks for oB ⟧ᶠ Θ ⍮ Ξ ⍮ ρ
       ↘ List.repeat 𝕌ω@0 (List.length (shape_leaves (rview_leaves D) 0 t)) ++ ihs )
where "'⟦ihsᶠ' vs 'of' gs 'under' p ups Bks 'for' oB '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (fast_eval_ihs Θ Ξ ρ p ups Bks oB gs vs r)
(** The recursive results of an argument of a shape, as [eval_ih] *)
with fast_eval_ih {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : env -> qname -> list domain -> list eblock -> ptyp -> domain -> list domain -> Prop :=
(** At a member with a block: the eliminator at it *)
| fast_eval_ih_self :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_is_rview Mj = false ->
     ⟦elimᶠ v at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r ->
     ⟦ihᶠ v of pt_self j Ps under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r :: nil )
(** At a record view: those of its fields at the projections *)
| fast_eval_ih_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws ->
     ⟦ihsᶠ ws of gs under p ups Bks for None ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     ⟦ihᶠ v of pt_self j Ps under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs )
(** At a function shape: the family of each recursive result of the rest *)
| fast_eval_ih_pi :
  `( ind_lookup Θ Ξ p = Some D ->
     ⟦ihᶠ v of pt_pi B t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ
       ↘ List.map (fun i => d_ihfn ρ Bks p ups t i v) (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t))) )
where "'⟦ihᶠ' v 'of' t 'under' p ups Bks '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (fast_eval_ih Θ Ξ ρ p ups Bks t v r)
(** The projections of a value at fields, in order *)
with fast_eval_projs {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : list string -> domain -> list domain -> Prop :=
(** No field *)
| fast_eval_projs_nil :
  `( ⟦projsᶠ nil of v ⟧ᶠ Θ ⍮ Ξ ↘ nil )
(** The first field's projection, then the rest *)
| fast_eval_projs_cons :
  `( fast_eval_proj Θ Ξ f v w ->
     ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws ->
     ⟦projsᶠ f :: fl of v ⟧ᶠ Θ ⍮ Ξ ↘ w :: ws )
where "'⟦projsᶠ' fl 'of' v '⟧ᶠ' Θ '⍮' Ξ '↘' ws" := (fast_eval_projs Θ Ξ fl v ws)
(** The declared member a member is, as [eval_mref] *)
with fast_eval_mref {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> nat -> (qname * nat * list domain) -> Prop :=
(** A declared member: itself *)
| fast_eval_mref_decl :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_decl pm ->
     ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (p, j, ups) )
(** A view: the container's member, at the view's arguments *)
| fast_eval_mref_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     ⟦ Is ⟧*ᶠ Θ ⍮ Ξ ⍮ decl_env D ups ↘ cups ->
     ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (qc, k, cups) )
where "'⟦mrefᶠ' j 'of' p ups '⟧ᶠ' Θ '⍮' Ξ '↘' r" := (fast_eval_mref Θ Ξ p ups j r)
(** The type of an argument of a shape, as [eval_shape_type] *)
with fast_eval_shape_type {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> ptyp -> domain -> Prop :=
(** At the end: the member's type former at the shape's parameters *)
| fast_eval_shape_type_self :
  `( ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ bs ->
     ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ (pc, k, pre) ->
     ⟦shtyᶠ pt_self j Ps of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_ind pc k (pre ++ bs) )
(** At the end, at a record view: the record type at the view's instance *)
| fast_eval_shape_type_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     ⟦ Is ⟧*ᶠ Θ ⍮ Ξ ⍮ decl_env D ups ↘ cups ->
     ⟦shtyᶠ pt_self j Ps of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ d_record qr cups )
(** At a domain: a [Π] over it, of the shape family *)
| fast_eval_shape_type_pi :
  `( ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     ⟦shtyᶠ pt_pi B t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ Πᵈ{ak_relevant} b (nil ↦ d_shfam p ups ρ B t ⦂ entry_type_none) fam_cod )
where "'⟦shtyᶠ' t 'of' p ups '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (fast_eval_shape_type Θ Ξ p ups ρ t r)
(** The types of the recursive results of an argument, as [eval_ihty] *)
with fast_eval_ihty {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> list exp -> env -> ptyp -> domain -> list domain -> Prop :=
(** At a member with a block: its motive at the shape's parameters and [v] *)
| fast_eval_ihty_self :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_is_rview Mj = false ->
     ⟦ Ps ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ bs ->
     ⟦ List.nth j As a_prop ⟧ᶠ Θ ⍮ Ξ ⍮
       env_extend_typed ρm (tele_entries (decl_env D ups) (List.rev (im_nparams Mj)) bs ++ (v, entry_type_shape p ups ρ (pt_self j Ps)) :: nil) ↘ a ->
     ⟦ihtyᶠ v of pt_self j Ps at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a :: nil )
(** At a record view: those of its fields at the projections *)
| fast_eval_ihty_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     im_cons Mj = (c, gs) :: nil ->
     ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws ->
     ⟦ihtysᶠ ws of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ decl_env D ups ↘ rs ->
     ⟦ihtyᶠ v of pt_self j Ps at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs )
(** At a domain: a [Π] over it, of each recursive result's family *)
| fast_eval_ihty_pi :
  `( ind_lookup Θ Ξ p = Some D ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ b ->
     ⟦ihtyᶠ v of pt_pi B t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ
       ↘ List.map (fun i => Πᵈ{ak_relevant} b (nil ↦ d_ihfam ρm As p ups ρ B t i v ⦂ entry_type_none) fam_cod)
           (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t))) )
where "'⟦ihtyᶠ' v 'of' t 'at' p ups 'under' ρm As '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (fast_eval_ihty Θ Ξ p ups ρm As ρ t v r)
(** The types of the recursive results of a record view's fields, as
    [eval_ihtys] *)
with fast_eval_ihtys {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : qname -> list domain -> env -> list exp -> env -> list carg -> list domain -> list domain -> Prop :=
(** No field, no result *)
| fast_eval_ihtys_nil :
  `( ⟦ihtysᶠ nil of nil at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ nil )
(** A non-recursive field has none, and extends the components' environment *)
| fast_eval_ihtys_arg :
  `( ⟦ihtysᶠ vs of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ v ⦂ entry_type_closure T ρ ↘ rs ->
     ⟦ihtysᶠ v :: vs of ca_arg r T :: gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs )
(** A recursive field has those of its shape *)
| fast_eval_ihtys_rec :
  `( ⟦ihtyᶠ v of t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs1 ->
     ⟦ihtysᶠ vs of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     ⟦ihtysᶠ v :: vs of ca_rec t :: gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs1 ++ rs )
where "'⟦ihtysᶠ' vs 'of' gs 'at' p ups 'under' ρm As '⟧ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (fast_eval_ihtys Θ Ξ p ups ρm As ρ gs vs r)
(** Semantic application, as [eval_app] *)
with fast_eval_app {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : domain -> domain -> domain -> Prop :=
(** A function's body, at the argument *)
| fast_eval_app_fn :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ n ⦂ entry_type_value a ↘ m ->
     $ᶠ| λᵈ a ρ M & n | Θ ⍮ Ξ ↘ m )
(** A neutral applied, at the codomain's instance *)
| fast_eval_app_neut :
  `( evaluated_kind κc ->
     ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ n ⦂ entry_type_value a ↘ b ->
     $ᶠ| ⇑ (d_pi κd κc a ρ B) m & n | Θ ⍮ Ξ ↘ ⇑ b (m $ᵈ ⇓ a n) )
(** The type former takes a parameter it still lacks *)
| fast_eval_app_indty :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     List.length as' < im_np D Mk ->
     $ᶠ| d_ind p k as' & n | Θ ⍮ Ξ ↘ d_ind p k (as' ++ n :: nil) )
(** So does a record's type former *)
| fast_eval_app_record :
  `( record_lookup Θ Ξ p = Some R ->
     List.length ns < List.length (record_params R) ->
     $ᶠ| d_record p ns & n | Θ ⍮ Ξ ↘ d_record p (ns ++ n :: nil) )
(** So does a constructor *)
| fast_eval_app_con :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some Mk ->
     im_head Mk = mh_decl pm ->
     ind_con Mk c = Some gs ->
     List.length vs < (im_np D Mk + List.length gs)%nat ->
     $ᶠ| d_con p k c vs & n | Θ ⍮ Ξ ↘ d_con p k c (vs ++ n :: nil) )
(** A constructor of a view takes the group's uniform parameters *)
| fast_eval_app_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     S (List.length vs) < ind_nu D ->
     $ᶠ| d_con p j c vs & n | Θ ⍮ Ξ ↘ d_con p j c (vs ++ n :: nil) )
(** At the last of them, the container's constructor at the view's
    arguments *)
| fast_eval_app_con_view_ups :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     S (List.length vs) = ind_nu D ->
     ⟦ Is ⟧*ᶠ Θ ⍮ Ξ ⍮ decl_env D (vs ++ n :: nil) ↘ cups ->
     $ᶠ| d_con p j c vs & n | Θ ⍮ Ξ ↘ d_con qc k c cups )
(** The constructor of a record view, before its last argument *)
| fast_eval_app_con_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     S (List.length vs) < ind_nu D + List.length fl ->
     $ᶠ| d_con p j c vs & n | Θ ⍮ Ξ ↘ d_con p j c (vs ++ n :: nil) )
(** At its last one, the tuple of the fields *)
| fast_eval_app_con_rview_full :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     S (List.length vs) = ind_nu D + List.length fl ->
     $ᶠ| d_con p j c vs & n | Θ ⍮ Ξ ↘ d_tuple (List.combine fl (List.skipn (ind_nu D) (vs ++ n :: nil))) )
(** A recursive result of a function shape, at the argument *)
| fast_eval_app_ihfn :
  `( $ᶠ| f & n | Θ ⍮ Ξ ↘ fn ->
     ⟦ihᶠ fn of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ rs ->
     List.nth_error rs i = Some r ->
     $ᶠ| d_ihfn ρ Bks p ups t i f & n | Θ ⍮ Ξ ↘ r )
(** The family of the type of an argument of a function shape *)
| fast_eval_app_shfam :
  `( ⟦shtyᶠ t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ n ⦂ entry_type_closure B ρ ↘ a ->
     $ᶠ| d_shfam p ups ρ B t & n | Θ ⍮ Ξ ↘ a )
(** The family of the type of a recursive result *)
| fast_eval_app_ihfam :
  `( $ᶠ| f & n | Θ ⍮ Ξ ↘ fn ->
     ⟦ihtyᶠ fn of t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↦ n ⦂ entry_type_closure B ρ ↘ as' ->
     List.nth_error as' i = Some a ->
     $ᶠ| d_ihfam ρm As p ups ρ B t i f & n | Θ ⍮ Ξ ↘ a )
(** A member closure takes the next argument of its module *)
| fast_eval_app_member :
  `( $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h' ->
     h' ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r ->
     $ᶠ| d_member h ch & n | Θ ⍮ Ξ ↘ r )
where "'$ᶠ|' m '&' n '|' Θ '⍮' Ξ '↘' r" := (fast_eval_app Θ Ξ m n r)
(** The values of terms, in order *)
with fast_eval_exps {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : list exp -> env -> list domain -> Prop :=
(** No terms *)
| fast_eval_exps_nil :
  `( ⟦ nil ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ nil )
(** A term, then the rest *)
| fast_eval_exps_cons :
  `( ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ms ->
     ⟦ M :: Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m :: ms )
where "'⟦' Ms '⟧*ᶠ' Θ '⍮' Ξ '⍮' ρ '↘' ms" := (fast_eval_exps Θ Ξ Ms ρ ms)
(** A function applied to terms, as [eval_app_args] *)
with fast_eval_app_args {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : domain -> list exp -> env -> domain -> Prop :=
(** No argument: the function itself *)
| fast_eval_app_args_nil :
  `( fast_eval_app_args Θ Ξ f nil ρ f )
(** An evaluated argument: its value applied, then the rest *)
| fast_eval_app_args_evaluated :
  `( evaluated_kind (arg_kind Θ Ξ f) ->
     ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     $ᶠ| f & n | Θ ⍮ Ξ ↘ g ->
     fast_eval_app_args Θ Ξ g Ns ρ r ->
     fast_eval_app_args Θ Ξ f (N :: Ns) ρ r )
(** A proof argument: kept as it is, then the rest *)
| fast_eval_app_args_proof :
  `( arg_kind Θ Ξ f = ak_propositional ->
     $ᶠ| f & ⋆ᵈ⟨N, ρ⟩ | Θ ⍮ Ξ ↘ g ->
     fast_eval_app_args Θ Ξ g Ns ρ r ->
     fast_eval_app_args Θ Ξ f (N :: Ns) ρ r )
(** The values of a record value's fields, as [eval_field_vals] *)
with fast_eval_field_vals {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : list abs_kind -> list exp -> env -> list domain -> Prop :=
(** No field *)
| fast_eval_field_vals_nil :
  `( fast_eval_field_vals Θ Ξ rs nil ρ nil )
(** An evaluated field: its value, then the rest *)
| fast_eval_field_vals_evaluated :
  `( evaluated_kind (List.hd ak_relevant rs) ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m ->
     fast_eval_field_vals Θ Ξ (List.tl rs) Ms ρ ms ->
     fast_eval_field_vals Θ Ξ rs (M :: Ms) ρ (m :: ms) )
(** A propositional field: the proof kept as it is, then the rest *)
| fast_eval_field_vals_proof :
  `( List.hd ak_relevant rs = ak_propositional ->
     fast_eval_field_vals Θ Ξ (List.tl rs) Ms ρ ms ->
     fast_eval_field_vals Θ Ξ rs (M :: Ms) ρ (⋆ᵈ⟨M, ρ⟩ :: ms) )
(** A value applied to values, outermost first *)
with fast_eval_apps {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : domain -> list domain -> domain -> Prop :=
(** No arguments *)
| fast_eval_apps_nil :
  `( $*ᶠ| m & nil | Θ ⍮ Ξ ↘ m )
(** The first argument, then the rest *)
| fast_eval_apps_cons :
  `( $ᶠ| m & n | Θ ⍮ Ξ ↘ m1 ->
     $*ᶠ| m1 & args | Θ ⍮ Ξ ↘ r ->
     $*ᶠ| m & n :: args | Θ ⍮ Ξ ↘ r )
where "'$*ᶠ|' m '&' ns '|' Θ '⍮' Ξ '↘' r" := (fast_eval_apps Θ Ξ m ns r)
(** Module expressions, as [eval_modexp] *)
with fast_eval_modexp {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : modexp -> env -> dmod -> Prop :=
(** A module slot is read off the environment *)
| fast_eval_me_var :
  `( ⟦ me_var x ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ env_mod ρ x )
(** A unit is a global body module, with no argument yet *)
| fast_eval_me_unit :
  `( ⟦ me_unit fp ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ dm_global (q_abs fp nil) nil )
(** A literal unit is its closure *)
| fast_eval_me_lit :
  `( ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ me_lit (gu_mk Δ D) ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h )
(** A submodule is selected from the module's value *)
| fast_eval_me_mem :
  `( ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     h ·ₘᶠ y Θ ⍮ Ξ ↘ r ->
     ⟦ me_mem H y ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
(** An application adds the argument's value to the module's *)
| fast_eval_me_app :
  `( ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ N ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ n ->
     $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r ->
     ⟦ me_app H N ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ r )
where "'⟦' H '⟧ᵐᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (fast_eval_modexp Θ Ξ H ρ r)
(** The closure of a unit's definition, as [eval_close] *)
with fast_eval_close {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : ctx -> moddef -> env -> dmod -> Prop :=
(** A body: the closure of its expansion *)
| fast_eval_close_body :
  `( ⟦ Δ ⊢ md_body sm Φ ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ dm_local Δ (md_body sm (gm_expand Φ)) ρ )
(** An alias still lacking a parameter: its closure *)
| fast_eval_close_alias :
  `( 0 < List.length Δ ->
     ⟦ Δ ⊢ md_alias E ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ dm_local Δ (md_alias E) ρ )
(** An alias lacking none: its target's value *)
| fast_eval_close_alias0 :
  `( ⟦ E ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h ->
     ⟦ nil ⊢ md_alias E ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ h )
where "'⟦' Δ '⊢' D '⟧ᶜᶠ' Θ '⍮' Ξ '⍮' ρ '↘' r" := (fast_eval_close Θ Ξ Δ D ρ r)
(** A module value applied to one more argument, as [eval_appm] *)
with fast_eval_appm {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : dmod -> domain -> dmod -> Prop :=
(** A global module records the argument *)
| fast_eval_appm_global :
  `( $ᵐᶠ| dm_global p args & n | Θ ⍮ Ξ ↘ dm_global p (args ++ n :: nil) )
(** A closure takes it as its outermost missing parameter *)
| fast_eval_appm_local :
  `( ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↦ n ⦂ entry_type_closure A ρ ↘ r ->
     $ᵐᶠ| dm_local (Δ ++ ce_ass κ A :: nil) D ρ & n | Θ ⍮ Ξ ↘ r )
(** A submodule closure passes it to the module, then selects again *)
| fast_eval_appm_member :
  `( $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h' ->
     h' ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r ->
     $ᵐᶠ| dm_member h ch & n | Θ ⍮ Ξ ↘ r )
where "'$ᵐᶠ|' h '&' n '|' Θ '⍮' Ξ '↘' r" := (fast_eval_appm Θ Ξ h n r)
(** A module value applied to arguments, outermost first *)
with fast_eval_appms {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : dmod -> list domain -> dmod -> Prop :=
(** No argument *)
| fast_eval_appms_nil :
  `( $ᵐ*ᶠ| h & nil | Θ ⍮ Ξ ↘ h )
(** The first argument, then the rest *)
| fast_eval_appms_cons :
  `( $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ h1 ->
     $ᵐ*ᶠ| h1 & ns | Θ ⍮ Ξ ↘ r ->
     $ᵐ*ᶠ| h & n :: ns | Θ ⍮ Ξ ↘ r )
where "'$ᵐ*ᶠ|' h '&' ns '|' Θ '⍮' Ξ '↘' r" := (fast_eval_appms Θ Ξ h ns r)
(** Selecting a term member, as [eval_sel] *)
with fast_eval_sel {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : dmod -> string -> domain -> Prop :=
(** A term part of a saturated global module, applied to its arguments *)
| fast_eval_sel_global :
  `( module_saturated Θ Ξ p args ->
     gc_term Θ Ξ (qname_app p (x :: nil)) = Some M ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ f ->
     $*ᶠ| f & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
(** An opaque definition or axiom of an evaluated kind: a neutral *)
| fast_eval_sel_global_neut :
  `( module_saturated Θ Ξ p args ->
     gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some (ge_def b pv κ A B) ->
     evaluated_kind κ ->
     b = false \/ B = None ->
     ⟦ A ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ a ->
     $*ᶠ| ⇑ a (d_glob (qname_app p (x :: nil))) & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
(** A definition tagged a proposition: a proof, kept as the selection *)
| fast_eval_sel_global_proof :
  `( gc_loc Θ Ξ p = Some (T, Φ) ->
     List.length args = List.length T ->
     gc_resolve Θ Ξ (qname_app p (x :: nil)) = Some (ge_def b pv ak_propositional A B) ->
     dm_global p args ·ₜᶠ x Θ ⍮ Ξ ↘ ⋆ᵈ⟨member_proof x, global_proof_env p T args⟩ )
(** The module of a member of a group, as a term: its type former *)
| fast_eval_sel_global_ind :
  `( module_saturated Θ Ξ p args ->
     gc_resolve Θ Ξ (qname_app p (x :: nil)) = None ->
     ind_mlookup Θ Ξ (qname_app p (x :: nil)) = Some (pq, k, D) ->
     $*ᶠ| d_ind pq k nil & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
(** A member of a global module lacking a parameter: a member closure *)
| fast_eval_sel_global_unsat :
  `( gc_loc Θ Ξ p = Some (T, Φ) ->
     List.length args < List.length T ->
     dm_global p args ·ₜᶠ x Θ ⍮ Ξ ↘ d_member (dm_global p args) (x :: nil) )
(** A member of a closure lacking a parameter: a member closure *)
| fast_eval_sel_unsat :
  `( 0 < List.length Δ ->
     dm_local Δ D ρ ·ₜᶠ x Θ ⍮ Ξ ↘ d_member (dm_local Δ D ρ) (x :: nil) )
(** A term part of a saturated body, of an evaluated kind *)
| fast_eval_sel_body :
  `( gm_prefix_upto (gm_expand Φ) x = Some (gm_ext Φ' x E) ->
     entry_tm E = Some (A, M) ->
     evaluated_kind (entry_kind E) ->
     ⟦ Φ' ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ' ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r ->
     dm_local nil (md_body sm Φ) ρ ·ₜᶠ x Θ ⍮ Ξ ↘ r )
(** A definition of a saturated body tagged a proposition: a proof *)
| fast_eval_sel_body_proof :
  `( gm_prefix_upto (gm_expand Φ) x = Some (gm_ext Φ' x E) ->
     entry_tm E = Some (A, M) ->
     entry_kind E = ak_propositional ->
     dm_local nil (md_body sm Φ) ρ ·ₜᶠ x Θ ⍮ Ξ ↘ ⋆ᵈ⟨member_proof x, ρ ↦ᵐ dm_local nil (md_body sm Φ) ρ ⦂ gu_mk nil (md_body sm Φ)⟩ )
(** A member of a submodule closure extends the chain *)
| fast_eval_sel_member :
  `( dm_member h ch ·ₜᶠ x Θ ⍮ Ξ ↘ d_member h (ch ++ x :: nil) )
(** A record type of a saturated global module, as a term *)
| fast_eval_sel_global_record :
  `( module_saturated Θ Ξ p args ->
     gc_resolve Θ Ξ (qname_app p (x :: nil)) = None ->
     record_lookup Θ Ξ (qname_app p (x :: nil)) = Some R ->
     $*ᶠ| d_record (qname_app p (x :: nil)) nil & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₜᶠ x Θ ⍮ Ξ ↘ r )
where "h '·ₜᶠ' x Θ '⍮' Ξ '↘' r" := (fast_eval_sel Θ Ξ h x r)
(** Selecting a submodule, as [eval_selm] *)
with fast_eval_selm {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : dmod -> string -> dmod -> Prop :=
(** A located submodule of a global module: a global module *)
| fast_eval_selm_global :
  `( gc_loc Θ Ξ (qname_app p (y :: nil)) = Some TΦ ->
     dm_global p args ·ₘᶠ y Θ ⍮ Ξ ↘ dm_global (qname_app p (y :: nil)) args )
(** An alias submodule of a global module: its closure, applied *)
| fast_eval_selm_global_alias :
  `( gc_module Θ Ξ (qname_app p (y :: nil)) = Some (mr_alias (gu_mk Δ D)) ->
     ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ nil ↘ h ->
     $ᵐ*ᶠ| h & args | Θ ⍮ Ξ ↘ r ->
     dm_global p args ·ₘᶠ y Θ ⍮ Ξ ↘ r )
(** A submodule of a closure lacking a parameter: a submodule closure *)
| fast_eval_selm_unsat :
  `( 0 < List.length Δ ->
     dm_local Δ D ρ ·ₘᶠ y Θ ⍮ Ξ ↘ dm_member (dm_local Δ D ρ) (y :: nil) )
(** A module part of a saturated body: its unit's closure *)
| fast_eval_selm_body :
  `( gm_prefix_upto (gm_expand Φ) y = Some (gm_ext Φ' y E) ->
     entry_unit E = Some (gu_mk Δy Dy) ->
     ⟦ Φ' ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ' ->
     ⟦ Δy ⊢ Dy ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r ->
     dm_local nil (md_body sm Φ) ρ ·ₘᶠ y Θ ⍮ Ξ ↘ r )
(** A submodule of a submodule closure extends the chain *)
| fast_eval_selm_member :
  `( dm_member h ch ·ₘᶠ y Θ ⍮ Ξ ↘ dm_member h (ch ++ y :: nil) )
where "h '·ₘᶠ' y Θ '⍮' Ξ '↘' r" := (fast_eval_selm Θ Ξ h y r)
(** Selecting along a chain: submodules, then a term member *)
with fast_eval_selc {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> domain -> Prop :=
(** The last selection is a term member *)
| fast_eval_selc_one :
  `( h ·ₜᶠ x Θ ⍮ Ξ ↘ r ->
     h ·ₜ*ᶠ (x :: nil) Θ ⍮ Ξ ↘ r )
(** The ones before it are submodules *)
| fast_eval_selc_cons :
  `( h ·ₘᶠ y Θ ⍮ Ξ ↘ h1 ->
     h1 ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r ->
     h ·ₜ*ᶠ (y :: ch) Θ ⍮ Ξ ↘ r )
where "h '·ₜ*ᶠ' ch Θ '⍮' Ξ '↘' r" := (fast_eval_selc Θ Ξ h ch r)
(** Selecting submodules along a chain *)
with fast_eval_selmc {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : dmod -> list string -> dmod -> Prop :=
(** The empty chain is the module itself *)
| fast_eval_selmc_nil :
  `( h ·ₘ*ᶠ nil Θ ⍮ Ξ ↘ h )
(** A submodule, then the rest of the chain *)
| fast_eval_selmc_cons :
  `( h ·ₘᶠ y Θ ⍮ Ξ ↘ h1 ->
     h1 ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r ->
     h ·ₘ*ᶠ (y :: ch) Θ ⍮ Ξ ↘ r )
where "h '·ₘ*ᶠ' ch Θ '⍮' Ξ '↘' r" := (fast_eval_selmc Θ Ξ h ch r)
(** The environment the members of a body see, as [eval_body_env] *)
with fast_eval_body_env {SM : SkipMode} (Θ : gdeps) (Ξ : gstack) : env -> gmod -> env -> Prop :=
(** The empty body adds nothing *)
| fast_eval_body_env_nil :
  `( ⟦ gm_nil ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ )
(** A definition tagged an evaluated kind adds its value *)
| fast_eval_body_env_def :
  `( evaluated_kind κ ->
     ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ1 ↘ m ->
     ⟦ gm_ext Φ y (ge_def b pv κ A (Some M)) ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ m ⦂ entry_type_closure A ρ1 )
(** A definition tagged a proposition adds it kept as it is *)
| fast_eval_body_env_def_proof :
  `( ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ gm_ext Φ y (ge_def b pv ak_propositional A (Some M)) ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ ⋆ᵈ⟨M, ρ1⟩ ⦂ entry_type_closure A ρ1 )
(** A submodule adds its unit's closure *)
| fast_eval_body_env_mod :
  `( ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ Δy ⊢ Dy ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ1 ↘ h ->
     ⟦ gm_ext Φ y (ge_mod pm (gu_mk Δy Dy)) ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ᵐ h ⦂ gu_mk Δy Dy )
(** A definition with a module part adds both parts *)
| fast_eval_body_env_dm :
  `( ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
     ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ1 ↘ m ->
     ⟦ Δy ⊢ Dy ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ1 ↘ h ->
     ⟦ gm_ext Φ y (ge_def_mod pv A M (gu_mk Δy Dy)) ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ↦ᵈ m ⦂ entry_type_closure A ρ1 ‖ h ⦂ gu_mk Δy Dy )
where "'⟦' Φ '⟧ᵇᶠ' Θ '⍮' Ξ '⍮' ρ '↘' ρ'" := (fast_eval_body_env Θ Ξ ρ Φ ρ').

Scheme fast_eval_exp_mut_ind := Induction for fast_eval_exp Sort Prop
with fast_eval_app_mut_ind := Induction for fast_eval_app Sort Prop
with fast_eval_exps_mut_ind := Induction for fast_eval_exps Sort Prop
with fast_eval_apps_mut_ind := Induction for fast_eval_apps Sort Prop
with fast_eval_modexp_mut_ind := Induction for fast_eval_modexp Sort Prop
with fast_eval_close_mut_ind := Induction for fast_eval_close Sort Prop
with fast_eval_appm_mut_ind := Induction for fast_eval_appm Sort Prop
with fast_eval_appms_mut_ind := Induction for fast_eval_appms Sort Prop
with fast_eval_sel_mut_ind := Induction for fast_eval_sel Sort Prop
with fast_eval_selm_mut_ind := Induction for fast_eval_selm Sort Prop
with fast_eval_selc_mut_ind := Induction for fast_eval_selc Sort Prop
with fast_eval_selmc_mut_ind := Induction for fast_eval_selmc Sort Prop
with fast_eval_body_env_mut_ind := Induction for fast_eval_body_env Sort Prop
with fast_eval_elim_mut_ind := Induction for fast_eval_elim Sort Prop
with fast_eval_ihs_mut_ind := Induction for fast_eval_ihs Sort Prop
with fast_eval_ih_mut_ind := Induction for fast_eval_ih Sort Prop
with fast_eval_mref_mut_ind := Induction for fast_eval_mref Sort Prop
with fast_eval_shape_type_mut_ind := Induction for fast_eval_shape_type Sort Prop
with fast_eval_ihty_mut_ind := Induction for fast_eval_ihty Sort Prop
with fast_eval_proj_mut_ind := Induction for fast_eval_proj Sort Prop
with fast_eval_neutral_fields_mut_ind := Induction for fast_eval_neutral_fields Sort Prop
with fast_eval_projs_mut_ind := Induction for fast_eval_projs Sort Prop
with fast_eval_ihtys_mut_ind := Induction for fast_eval_ihtys Sort Prop
with fast_eval_field_vals_mut_ind := Induction for fast_eval_field_vals Sort Prop
with fast_eval_app_args_mut_ind := Induction for fast_eval_app_args Sort Prop.
Combined Scheme fast_eval_mut_ind from
  fast_eval_exp_mut_ind,
  fast_eval_app_mut_ind,
  fast_eval_exps_mut_ind,
  fast_eval_apps_mut_ind,
  fast_eval_modexp_mut_ind,
  fast_eval_close_mut_ind,
  fast_eval_appm_mut_ind,
  fast_eval_appms_mut_ind,
  fast_eval_sel_mut_ind,
  fast_eval_selm_mut_ind,
  fast_eval_selc_mut_ind,
  fast_eval_selmc_mut_ind,
  fast_eval_body_env_mut_ind,
  fast_eval_elim_mut_ind,
  fast_eval_ihs_mut_ind,
  fast_eval_ih_mut_ind,
  fast_eval_mref_mut_ind,
  fast_eval_shape_type_mut_ind,
  fast_eval_ihty_mut_ind,
  fast_eval_proj_mut_ind,
  fast_eval_neutral_fields_mut_ind,
  fast_eval_projs_mut_ind,
  fast_eval_ihtys_mut_ind,
  fast_eval_field_vals_mut_ind,
  fast_eval_app_args_mut_ind.

#[export]
Hint Constructors fast_eval_exp fast_eval_proj fast_eval_neutral_fields fast_eval_projs fast_eval_elim fast_eval_ihs fast_eval_ih fast_eval_mref fast_eval_shape_type fast_eval_ihty fast_eval_ihtys fast_eval_app fast_eval_exps fast_eval_apps fast_eval_modexp fast_eval_close fast_eval_appm fast_eval_appms fast_eval_sel fast_eval_selm
  fast_eval_selc fast_eval_selmc fast_eval_body_env fast_eval_field_vals fast_eval_app_args : mctt.

(** ** Determinism *)

Section FastDeterminism.
  (** The mode the relations run at *)
  Context {SM : SkipMode}.

  Lemma functional_fast_eval : forall {Θ Ξ},
    (forall M ρ m1,
        ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m1 ->
        forall m2,
          ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m2 ->
          m1 = m2) /\
      (forall m n r1,
          $ᶠ| m & n | Θ ⍮ Ξ ↘ r1 ->
          forall r2,
            $ᶠ| m & n | Θ ⍮ Ξ ↘ r2 ->
            r1 = r2) /\
      (forall Ms ρ ms1, ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ms1 -> forall ms2, ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ms2 -> ms1 = ms2) /\
      (forall m args r1, $*ᶠ| m & args | Θ ⍮ Ξ ↘ r1 -> forall r2, $*ᶠ| m & args | Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall H ρ h1, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h1 -> forall h2, ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h2 -> h1 = h2) /\
      (forall Δ D ρ h1, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ h1 -> forall h2, ⟦ Δ ⊢ D ⟧ᶜᶠ Θ ⍮ Ξ ⍮ ρ ↘ h2 -> h1 = h2) /\
      (forall h n r1, $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r1 -> forall r2, $ᵐᶠ| h & n | Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h ns r1, $ᵐ*ᶠ| h & ns | Θ ⍮ Ξ ↘ r1 -> forall r2, $ᵐ*ᶠ| h & ns | Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h x r1, h ·ₜᶠ x Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₜᶠ x Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h y r1, h ·ₘᶠ y Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₘᶠ y Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h ch r1, h ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h ch r1, h ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall ρ Φ ρ1, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 -> forall ρ2, ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 -> ρ1 = ρ2) /\
      (forall ρ p ups Bks j m r1,
          ⟦elimᶠ m at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2, ⟦elimᶠ m at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall ρ p ups Bks B gs vs r1,
          ⟦ihsᶠ vs of gs under p ups Bks for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2, ⟦ihsᶠ vs of gs under p ups Bks for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall ρ p ups Bks t v r1,
          ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 -> forall r2, ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall p ups j r1, ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ r1 -> forall r2, ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall p ups ρ t a1, ⟦shtyᶠ t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a1 -> forall a2, ⟦shtyᶠ t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a2 -> a1 = a2) /\
      (forall p ups ρm As ρ t v a1, ⟦ihtyᶠ v of t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a1 ->
          forall a2, ⟦ihtyᶠ v of t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a2 -> a1 = a2) /\
      (forall f m r1, fast_eval_proj Θ Ξ f m r1 -> forall r2, fast_eval_proj Θ Ξ f m r2 -> r1 = r2) /\
      (forall m ρ fl rs1, fast_eval_neutral_fields Θ Ξ m ρ fl rs1 -> forall rs2, fast_eval_neutral_fields Θ Ξ m ρ fl rs2 -> rs1 = rs2) /\
      (forall fl v ws1, ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws1 -> forall ws2, ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws2 -> ws1 = ws2) /\
      (forall p ups ρm As ρ gs vs r1, ⟦ihtysᶠ vs of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2, ⟦ihtysᶠ vs of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall rs Ms ρ ms1, fast_eval_field_vals Θ Ξ rs Ms ρ ms1 -> forall ms2, fast_eval_field_vals Θ Ξ rs Ms ρ ms2 -> ms1 = ms2) /\
      (forall f Ms ρ r1, fast_eval_app_args Θ Ξ f Ms ρ r1 -> forall r2, fast_eval_app_args Θ Ξ f Ms ρ r2 -> r1 = r2).
  Proof.
    intros Θ Ξ; apply fast_eval_mut_ind; intros;
      (* invert the other evaluation, then use the hypotheses on its parts, as
         in [functional_eval] *)
      match goal with |- _ = ?r2 => match goal with H : context [r2] |- _ => inversion H; subst; clear H end end;
      repeat match goal with
        | H : gc_term Θ Ξ ?p = Some _ |- _ =>
            destruct (gc_term_inv _ _ _ _ H) as [(? & ? & ? & ? & ?) | (? & ? & ? & ?)]; clear H
        | H1 : entry_tm ?E = Some _, H2 : entry_tm ?E = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : entry_unit ?E = Some _, H2 : entry_unit ?E = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_resolve Θ Ξ ?p = Some _, H2 : Members.gc_resolve Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : gc_entry Θ Ξ ?p = Some _, H2 : gc_entry Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : gc_entry Θ Ξ ?p = Some (ge_def_mod _ _ _ _), H2 : Members.gc_resolve Θ Ξ ?p = Some _ |- _ =>
            exfalso; rewrite (gc_entry_def_mod _ _ _ _ _ _ _ H1) in H2; discriminate H2
        | H1 : ind_mlookup Θ Ξ ?p = Some _, H2 : gc_entry Θ Ξ ?p = Some (ge_def_mod _ _ _ _) |- _ =>
            exfalso; exact (ind_mlookup_not_def_mod _ _ _ _ _ _ _ _ H1 H2)
        | H1 : ind_mlookup Θ Ξ ?p = Some _, H2 : ind_mlookup Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : ind_lookup Θ Ξ ?p = Some _, H2 : ind_lookup Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : record_lookup Θ Ξ ?p = Some _, H2 : record_lookup Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : record_lookup Θ Ξ ?p = Some _, H2 : ind_mlookup Θ Ξ ?p = Some _ |- _ =>
            exfalso; rewrite (record_lookup_not_ind _ _ _ _ H1) in H2; discriminate H2
        | H1 : record_lookup Θ Ξ ?p = Some _, H2 : gc_entry Θ Ξ ?p = Some (ge_def_mod _ _ _ _) |- _ =>
            exfalso; exact (record_lookup_not_def_mod _ _ _ _ _ _ _ _ H1 H2)
        | H1 : field_index ?fl ?f = Some _, H2 : field_index ?fl ?f = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : field_lookup ?fl ?f = Some _, H2 : field_lookup ?fl ?f = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : ind_member ?D ?k = Some _, H2 : ind_member ?D ?k = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : im_head ?M = _, H2 : im_head ?M = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : im_starts _ ?M = true, H2 : im_head ?M = mh_view _ _ _ _ |- _ =>
            unfold im_starts, im_is_decl in H1; rewrite H2 in H1; cbn [orb] in H1; apply Nat.ltb_lt in H1
        | H1 : im_starts _ ?M = true, H2 : im_head ?M = mh_record _ _ _ |- _ =>
            unfold im_starts, im_is_decl in H1; rewrite H2 in H1; cbn [orb] in H1; apply Nat.ltb_lt in H1
        | H1 : im_is_rview ?M = false, H2 : im_head ?M = mh_record _ _ _ |- _ =>
            exfalso; unfold im_is_rview in H1; rewrite H2 in H1; discriminate H1
        | H : 0 < List.length nil |- _ => exfalso; cbn in H; lia
        | H1 : im_cons ?M = _, H2 : im_cons ?M = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : fast_eval_mref Θ Ξ ?p _ ?j _, H2 : ind_member _ ?j = Some ?M, H3 : im_head ?M = mh_record _ _ _ |- _ =>
            inversion H1; subst; clear H1
        | H1 : im_ref ?p ?j ?M = _, H2 : im_ref ?p ?j ?M = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : List.nth_error ?Bks ?j = Some _, H2 : List.nth_error ?Bks ?j = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : ind_con ?D ?c = Some _, H2 : ind_con ?D ?c = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : brs_lookup ?Bs ?c = Some _, H2 : brs_lookup ?Bs ?c = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some _, H2 : Members.gc_module Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some (Members.mr_alias _),
          H2 : forall U, Members.gc_module Θ Ξ ?p <> Some (Members.mr_alias U) |- _ =>
            exfalso; exact (H2 _ H1)
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_loc Θ Ξ ?p = Some _, H2 : Members.gc_module Θ Ξ ?p = Some (Members.mr_alias _) |- _ =>
            exfalso; exact (gc_loc_not_alias _ _ _ _ _ H1 H2)
        | H1 : module_saturated Θ Ξ ?p ?args, H2 : Members.gc_loc Θ Ξ ?p = Some (?T, ?Φ),
          H3 : List.length ?args < List.length ?T |- _ =>
            exfalso; specialize (H1 _ _ H2); lia
        | H1 : Members.gc_loc Θ Ξ ?p = Some (?T, ?Φ), H2 : Members.gc_loc Θ Ξ ?p = Some (?T', ?Φ') |- _ =>
            assert_fails (constr_eq H1 H2); rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H : _ ++ ce_ass _ _ :: nil = _ ++ ce_ass _ _ :: nil |- _ =>
            apply List.app_inj_tail in H as [? [= ?]]; subst
        | H : 0 < List.length (_ ++ _ :: nil) -> False |- _ =>
            exfalso; apply H; rewrite List.length_app; cbn; lia
        | H1 : modexp_spine ?H = _, H2 : modexp_spine ?H = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | IH : forall r, ?P r -> ?a = r, H : ?P ?b |- _ =>
            assert_fails (constr_eq a b); specialize (IH _ H); subst
        | H : d_neut _ _ = d_neut _ _ |- _ => injection H; intros; subst; clear H
        | H : d_record _ _ = d_record _ _ |- _ => injection H; intros; subst; clear H
        | H : (_, _, _) = (_, _, _) |- _ => injection H; intros; subst; clear H
        | H : fast_eval_selc _ _ _ nil _ |- _ => inversion H
        | H1 : evaluated_kind ?k, H2 : ?k = ak_propositional |- _ =>
            exfalso; exact (evaluated_kind_not_propositional _ H1 H2)
        | H : evaluated_kind ak_propositional |- _ =>
            exfalso; exact (evaluated_kind_not_propositional _ H eq_refl)
        end;
      cbn [gu_params List.length] in *; try congruence; try lia; intuition (try congruence; try lia).
  Qed.

  Corollary functional_fast_eval_exp : forall {Θ Ξ} M ρ m1 m2,
      ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m1 ->
      ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ m2 ->
      m1 = m2.
  Proof.
    intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ); firstorder.
  Qed.

  Corollary functional_fast_eval_app : forall {Θ Ξ} m n r1 r2,
      $ᶠ| m & n | Θ ⍮ Ξ ↘ r1 ->
      $ᶠ| m & n | Θ ⍮ Ξ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ); intuition.
  Qed.

  Corollary functional_fast_eval_modexp : forall {Θ Ξ} H ρ h1 h2,
      ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h1 ->
      ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ ↘ h2 ->
      h1 = h2.
  Proof.
    intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ); intuition.
  Qed.

  Corollary functional_fast_eval_elim : forall {Θ Ξ} ρ p ups Bks j m r1 r2,
      ⟦elimᶠ m at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      ⟦elimᶠ m at j of p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_fast_eval_ihs : forall {Θ Ξ} ρ p ups Bks B gs vs r1 r2,
      ⟦ihsᶠ vs of gs under p ups Bks for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      ⟦ihsᶠ vs of gs under p ups Bks for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_fast_eval_ih : forall {Θ Ξ} ρ p ups Bks t v r1 r2,
      ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 -> ⟦ihᶠ v of t under p ups Bks ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2.
  Proof. intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_fast_eval_mref : forall {Θ Ξ} p ups j r1 r2,
      ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ r1 -> ⟦mrefᶠ j of p ups ⟧ᶠ Θ ⍮ Ξ ↘ r2 -> r1 = r2.
  Proof. intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_fast_eval_shape_type : forall {Θ Ξ} p ups ρ t a1 a2,
      ⟦shtyᶠ t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a1 -> ⟦shtyᶠ t of p ups ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a2 -> a1 = a2.
  Proof. intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_fast_eval_ihty : forall {Θ Ξ} p ups ρm As ρ t v a1 a2,
      ⟦ihtyᶠ v of t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a1 -> ⟦ihtyᶠ v of t at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ a2 -> a1 = a2.
  Proof. intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_fast_eval_ihtys : forall {Θ Ξ} p ups ρm As ρ gs vs r1 r2,
      ⟦ihtysᶠ vs of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r1 -> ⟦ihtysᶠ vs of gs at p ups under ρm As ⟧ᶠ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2.
  Proof. intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_fast_eval_projs : forall {Θ Ξ} fl v ws1 ws2,
      ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws1 -> ⟦projsᶠ fl of v ⟧ᶠ Θ ⍮ Ξ ↘ ws2 -> ws1 = ws2.
  Proof. intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ); destruct_all; eauto. Qed.

  Corollary functional_fast_eval_exps : forall {Θ Ξ} Ms ρ ms1 ms2,
      ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ms1 -> ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ ↘ ms2 -> ms1 = ms2.
  Proof. intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ); firstorder. Qed.

  Corollary functional_fast_eval_body_env : forall {Θ Ξ} ρ Φ ρ1 ρ2,
      ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
      ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 ->
      ρ1 = ρ2.
  Proof.
    intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  (** A field of a value is one value. *)
  Corollary functional_fast_eval_proj : forall {Θ Ξ} f m r1 r2,
      fast_eval_proj Θ Ξ f m r1 -> fast_eval_proj Θ Ξ f m r2 -> r1 = r2.
  Proof. intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ) as H; destruct_all; eauto. Qed.

  (** So are the neutral projections of the fields of a neutral. *)
  Corollary functional_fast_eval_neutral_fields : forall {Θ Ξ} m ρ fl rs1 rs2,
      fast_eval_neutral_fields Θ Ξ m ρ fl rs1 -> fast_eval_neutral_fields Θ Ξ m ρ fl rs2 -> rs1 = rs2.
  Proof. intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ) as H; destruct_all; eauto. Qed.

  (** The values of a record value's fields are one list. *)
  Corollary functional_fast_eval_field_vals : forall {Θ Ξ} rs Ms ρ ms1 ms2,
      fast_eval_field_vals Θ Ξ rs Ms ρ ms1 -> fast_eval_field_vals Θ Ξ rs Ms ρ ms2 -> ms1 = ms2.
  Proof. intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ) as H; destruct_all; eauto. Qed.

  (** A function applied along terms has one value. *)
  Corollary functional_fast_eval_app_args : forall {Θ Ξ} f Ms ρ r1 r2,
      fast_eval_app_args Θ Ξ f Ms ρ r1 -> fast_eval_app_args Θ Ξ f Ms ρ r2 -> r1 = r2.
  Proof. intros Θ Ξ; pose proof (@functional_fast_eval Θ Ξ) as H; destruct_all; eauto. Qed.
End FastDeterminism.

#[export]
Hint Resolve functional_fast_eval_exp functional_fast_eval_elim functional_fast_eval_ihs functional_fast_eval_ih functional_fast_eval_mref
  functional_fast_eval_shape_type functional_fast_eval_ihty functional_fast_eval_ihtys functional_fast_eval_projs functional_fast_eval_app
  functional_fast_eval_modexp functional_fast_eval_proj functional_fast_eval_neutral_fields : mctt.

Ltac functional_fast_eval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_fast_eval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (⟦ ?M ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?m1), H2 : (⟦ ?M ⟧ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?m2) |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : ($ᶠ| ?m & ?n | ?T ⍮ ?X ↘ ?r1), H2 : ($ᶠ| ?m & ?n | ?T ⍮ ?X ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : fast_eval_elim ?T ?X ?ρ ?p ?o ?Bks ?j ?m ?r1, H2 : fast_eval_elim ?T ?X ?ρ ?p ?o ?Bks ?j ?m ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : fast_eval_ihs ?T ?X ?ρ ?p ?o ?Bks ?B ?gs ?vs ?r1, H2 : fast_eval_ihs ?T ?X ?ρ ?p ?o ?Bks ?B ?gs ?vs ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : fast_eval_ih ?T ?X ?ρ ?p ?o ?Bks ?t ?v ?r1, H2 : fast_eval_ih ?T ?X ?ρ ?p ?o ?Bks ?t ?v ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_fast_eval_ih; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : fast_eval_mref ?T ?X ?p ?ups ?j ?r1, H2 : fast_eval_mref ?T ?X ?p ?ups ?j ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_fast_eval_mref; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : fast_eval_shape_type ?T ?X ?p ?ups ?ρ ?t ?r1, H2 : fast_eval_shape_type ?T ?X ?p ?ups ?ρ ?t ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_fast_eval_shape_type; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : fast_eval_ihty ?T ?X ?p ?u ?ρm ?As ?ρ ?t ?v ?r1, H2 : fast_eval_ihty ?T ?X ?p ?u ?ρm ?As ?ρ ?t ?v ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_fast_eval_ihty; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : fast_eval_ihtys ?T ?X ?p ?u ?ρm ?As ?ρ ?gs ?vs ?r1, H2 : fast_eval_ihtys ?T ?X ?p ?u ?ρm ?As ?ρ ?gs ?vs ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_fast_eval_ihtys; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : fast_eval_projs ?T ?X ?fl ?v ?r1, H2 : fast_eval_projs ?T ?X ?fl ?v ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_fast_eval_projs; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : (⟦ ?Ps ⟧*ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?r1), H2 : (⟦ ?Ps ⟧*ᶠ ?T ⍮ ?X ⍮ ?ρ ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_fast_eval_exps; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : fast_eval_proj ?T ?X ?f ?m ?r1, H2 : fast_eval_proj ?T ?X ?f ?m ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_fast_eval_proj; eassumption] | tactic_error r2 r1]; clear H2
  | H1 : fast_eval_neutral_fields ?T ?X ?m ?ρ ?fl ?r1, H2 : fast_eval_neutral_fields ?T ?X ?m ?ρ ?fl ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [eapply functional_fast_eval_neutral_fields; eassumption] | tactic_error r2 r1]; clear H2
  end.
(** There is no [fast_eval_sub] case: there is no fast evaluation of
    substitutions. *)
Ltac functional_fast_eval_rewrite_clear := repeat functional_fast_eval_rewrite_clear1.
