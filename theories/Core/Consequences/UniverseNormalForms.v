(** * The Normal Forms of the Types of a Universe

    The normal form of a type of a universe, when it is not neutral, is a
    type constructor below the universe ([typ_nf_below_of_nbe]): small
    universes are ordered by the canonical levels of their level terms
    ([subtyp_suniv_bound]), and a small type's normal form is of the small
    tier ([small_typ_nf]). *)

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Consequences Require Import Inversions.
From Mctt.Core.Syntactic Require Import CoreInversions.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Semantic Require Import Realizability Levels.
From Mctt.Core.Completeness.LogicalRelation Require Import Lemmas.
From Mctt.Core.Completeness Require Import LogicalRelation.Universes LogicalRelation.Contexts LogicalRelation.Functions.
From Mctt.Core.Completeness.Consequences Require Import ContextEquality.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Cong.
Require Import Mctt.Core.Syntactic.Command.
From Mctt.Core.Syntactic Require Import Builtin NfRename.
Import Domain_Notations Fixed_Notations.
Import Wk_Notations.
#[local] Open Scope list_scope.

(** ** The Normal Forms of Small Types

    A small type's normal form is a type constructor of the small tier:
    [Prop], [Level], a [Π], or a small universe at a
    literal level below the one the type lives in.  It is never a large
    universe (the large tier is not below the small one), never a
    proposition (a proposition is in no universe), and never a small
    universe at a level with an atom: such a universe is in no small
    universe at a literal level, since an atom is unbounded under some
    assignment. *)
Inductive small_typ_nf (n : nat) : nf -> Prop :=
(** The universe of propositions *)
| small_typ_nf_prop : small_typ_nf n Propⁿ
(** A type of levels *)
| small_typ_nf_level : forall m, small_typ_nf n Levelⁿ@m
(** A [Π] into a universe, its domain of any tag *)
| small_typ_nf_pi : forall κ A B, small_typ_nf n (Πⁿ{κ} A B)
(** A small universe at a literal level below [n] *)
| small_typ_nf_univ : forall m, m < n -> small_typ_nf n Typeⁿ@m
(** An inductive type applied to its parameters.  Its sort is not
    recorded: the shape says only that it is an inductive type. *)
| small_typ_nf_indty : forall p k Ms, small_typ_nf n (nf_indty p k Ms)
(** A record type applied to its parameters; its sort is not recorded
    either. *)
| small_typ_nf_record : forall p Ms, small_typ_nf n (nf_record p Ms).
#[export]
Hint Constructors small_typ_nf : mctt.

(** ** The Normal Forms of the Types of a Universe

    The normal forms of the types of a universe [u], when they are not
    neutral: [Prop], the types of levels, their sort [LevelSort] (in a
    large universe), the [Π]s,
    the small universes whose successor level is below [u] (every small
    universe when [u] is large), and the large universes below [u].  A
    literal small universe's instance is [small_typ_nf]
    ([typ_nf_below_lit]); a large one's gives the type constructors
    ([typ_nf_below_large]). *)
Inductive typ_nf_below : universe_nf -> nf -> Prop :=
(** The universe of propositions *)
| typ_nf_below_prop : forall u, typ_nf_below u Propⁿ
(** A type of levels *)
| typ_nf_below_level : forall u m, typ_nf_below u Levelⁿ@m
(** The sort of the types of levels, in the large universes only
    ([wf_level_sort]) *)
| typ_nf_below_level_sort : forall i, typ_nf_below (universe_large i) LevelSortⁿ
(** A [Π] into a universe, its domain of any tag *)
| typ_nf_below_pi : forall u κ A B, typ_nf_below u (Πⁿ{κ} A B)
(** A small universe whose successor level is below [u] *)
| typ_nf_below_univ : forall u c xs,
    universe_nf_le (universe_small (lvl_suc (c, xs))) u ->
    typ_nf_below u (univⁿ c xs)
(** A large universe below [u] *)
| typ_nf_below_typ : forall i j, j < i -> typ_nf_below (universe_large i) Typeωⁿ@j
(** An inductive type at its parameters *)
| typ_nf_below_indty : forall u p k Ms, typ_nf_below u (nf_indty p k Ms)
(** A record type at its parameters *)
| typ_nf_below_record : forall u p Ms, typ_nf_below u (nf_record p Ms).
#[export]
Hint Constructors typ_nf_below : mctt.

(** Below the literal [Type@n], a universe has no atom (an atom is
    unbounded below a finite literal, [lvl_le_lit_closed]) and a finite
    level below [n]. *)
Lemma typ_nf_below_lit : forall n W,
    typ_nf_below (universe_small (lvl_lit (ordinal_of_nat n))) W ->
    small_typ_nf n W.
Proof.
  intros * H; inversion H as [| | | | ? c xs Hle | | |]; subst; try constructor.
  cbn [universe_nf_le] in Hle.
  pose proof (lvl_le_lit_closed _ _ Hle) as Hxs.
  destruct xs as [| [k s a] r]; cbn in Hxs; [| discriminate ].
  rewrite lvl_le_correct in Hle; specialize (Hle _ lvl_adm_zero).
  rewrite lvl_eval_suc in Hle; unfold lvl_eval, lvl_lit in Hle; cbn in Hle.
  destruct c as [a m]; assert (a = 0) as -> by ordinal_solve.
  constructor; ordinal_solve.
Qed.

(** Below a large universe, a type constructor that is not neutral. *)
Lemma typ_nf_below_large : forall i W,
    typ_nf_below (universe_large i) W ->
    is_typ_constr W /\ (forall κ V, W <> ⇑ⁿ{κ} V).
Proof.
  intros * H; inversion H; subst; (split; [ cbn; constructor | intros ? ? Heq; discriminate Heq ]).
Qed.

Section Small_Typ.
  Context {GC : GCtx}.

(** A small universe below another: the canonical level of its level term
    is below the other's.  Read off the semantic subtyping at the initial
    environment, where [per_subtyp_suniv] orders the readbacks. *)
Lemma subtyp_suniv_bound : forall {Γ M N L L'},
    Γ ⊢ Type⟨M⟩ ⊆ Type⟨N⟩ ->
    nbe_f Γ M Level (nf_lvl_of L) ->
    nbe_f Γ N Level (nf_lvl_of L') ->
    lvl_le L L'.
Proof.
  intros * Hs0 Hn Hn'.
  pose proof (proj1 (proj1 (proj1 (proj2 (proj2 (proj2 wf_scoped))) _ _ _ _ _ Hs0))) as HsΓ0.
  pose proof (completeness_fundamental_subtyp _ _ _ Hs0) as [R HR i Hg].
  destruct (per_ctx_then_per_env_initial_env HR HsΓ0 HsΓ0) as (ρ & ρ' & Hρ & Hρ' & Hrel).
  assert (ρ' = ρ) as -> by (eapply functional_initial_env; eassumption).
  assert (⊨ Γ ≈ Γ) as HsΓ by (eexists; exact HR).
  destruct (eval_sub_id_rel HR Hrel) as [Hid Hid'].
  destruct (Hg _ _ HR _ _ (rel_sub_id HsΓ) _ _ _ _ Hrel Hid Hid')
    as [aσ a a'σ' a' Ha1 Ha2 Ha3 Ha4 [Rl Hll] [Rr Hrr] Hsub].
  rewrite exp_sub_id in Ha1, Ha3.
  inversion Hn; subst.
  inversion Hn'; subst.
  directed_inversion_by_head eval_exp; subst.
  invert_nbe_term.
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  inversion Hsub; subst;
    (** universes are no propositions *)
    [| match goal with Hp : per_prop _ _ |- _ => destruct Hp; cbn in *; discriminate end ].
  match goal with Hl : per_sublvl _ _ |- _ =>
    destruct (Hl (length Γ)) as [L0 L1 HL0 HL1 Hle _ _] end.
  (** The values at the identity and at the retagged environment are
      related levels, so read back alike *)
  invert_per_univ_elem Hll; invert_per_univ_elem Hrr.
  repeat match goal with Hp : per_lvl _ _ |- _ =>
    let La := fresh "La" in let HW := fresh "HW" in let HW' := fresh "HW'" in
    destruct (per_lvl_reads _ _ Hp (length Γ)) as (La & HW & HW' & _); clear Hp end.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  repeat match goal with H : nf_lvl_of _ = nf_lvl_of _ |- _ => apply nf_lvl_of_inj in H; subst end.
  (** The readbacks the order is about are those NbE gives. *)
  exact Hle.
Qed.

(** The instance at a literal. *)
Corollary subtyp_suniv_lit_bound : forall {Γ M n L},
    Γ ⊢ Type⟨M⟩ ⊆ Type@n ->
    nbe_f Γ M Level (nf_lvl_of L) ->
    lvl_le L (lvl_lit (ordinal_of_nat n)).
Proof.
  intros * Hs Hn; eapply subtyp_suniv_bound; [ exact Hs | exact Hn |].
  inversion Hn; subst.
  eapply nbe_evaluated_intro; [ eassumption | eassumption | apply eval_exp_llit | | directed_inversion_by_head eval_exp; constructor ].
  directed_inversion_by_head eval_exp; subst; mauto 3.
Qed.

(** The normal form of a small universe is the universe at the normal form of
    its level. *)
Lemma nbe_ty_univ_level : forall {Γ t L n},
    nbe_ty_f Γ Type⟨t⟩ (nf_univ_of L) ->
    nbe_f Γ t Level@n (nf_lvl_of L).
Proof.
  intros * Hn.
  inversion Hn; subst.
  directed_inversion_by_head eval_exp; subst.
  directed_inversion_by_head read_typ; subst.
  match goal with H1 : fst ?L0 = fst L, H2 : snd ?L0 = snd L |- _ =>
    assert (L0 = L) as -> by (destruct L0, L; cbn in *; congruence) end.
  eapply nbe_evaluated_intro; [ eassumption | apply eval_exp_level | eassumption | eapply read_nf_level_sort; eassumption | constructor ].
Qed.

(** The normal form of a type that is a small universe holds no proof: the
    universe's level is related to itself ([per_lvl]), whose canonical
    forms hold none ([per_lvl_canon_proof_free]). *)
Lemma nbe_ty_univ_proof_free : forall {Γ A i c xs},
    Γ ⊢ A : Typeω@i -> nbe_ty_f Γ A (univⁿ c xs) -> nf_proof_free (univⁿ c xs).
Proof.
  intros * HA0 Hn.
  pose proof (completeness_fundamental_exp_eq _ _ _ _ (wf_exp_eq_refl HA0)) as H.
  destruct (rel_typ_under_ctx_at_initial_env (wf_ctx_scoped_exp_eq (wf_exp_eq_refl HA0)) H) as [ρ [a [a' [Hρ [Ha [Ha' [R HR]]]]]]].
  destruct Hn as [ρ0 a0 Hρ0 Ha0 HW].
  assert (ρ0 = ρ) as -> by (eapply functional_initial_env; eassumption).
  functional_eval_rewrite_clear.
  inversion HW; subst.
  invert_per_univ_elem HR.
  match goal with Hr : Rnf ⇓ Levelᵈ _ in _ ↘ nf_lvl_of _ |- _ => apply domain_level_canon_of_read in Hr as [_ [L' [Heq HL']]] end.
  apply nf_lvl_of_inj in Heq as <-.
  pose proof (per_lvl_canon_proof_free _ _ _ _ ltac:(eassumption) HL') as Hpf.
  destruct L; exact Hpf.
Qed.

(** The level of a small universe in normal form is a canonical level of a
    sort its level term has: its constant is of a tier at most that sort, and
    each atom is a level of its own sort ([soundness_lvl_well_scoped]). *)
Lemma univ_nf_well_scoped : forall {Γ c xs A},
    Γ ⊢ Type⟨lvl_exp_of c (List.map atom_exp xs)⟩ : A ->
    nbe_ty_f Γ Type⟨lvl_exp_of c (List.map atom_exp xs)⟩ (univⁿ c xs) ->
    exists n, Γ ⊢ lvl_exp_of c (List.map atom_exp xs) : Level@n /\ fst c <= n /\ @level_atoms_well_scoped gc_deps gc_stack n Γ xs.
Proof.
  intros * HA Hn.
  destruct (wf_univ_lvl_inversion HA) as [n Ht].
  pose proof (nbe_ty_univ_level (L := (c, xs)) (n := n) Hn) as Hl.
  pose proof (soundness_lvl_well_scoped Ht Hl) as Hws; cbn in Hws.
  exists n; split; [ exact Ht | exact Hws ].
Qed.

(** What the normal form [univⁿ c xs] of a small universe [Type⟨t⟩] says
    of its level term [t]. *)
#[warnings="-cannot-define-projection"]
Record univ_nf_level (Γ : ctx) (t : exp) (c : o2) (xs : list level_atom) : Prop := mk_univ_nf_level
  { (** A sort of the level *)
    univ_nf_level_sort : nat
    (** The level term is equal there to the canonical level *)
  ; univ_nf_level_eq : Γ ⊢ t ≈ lvl_exp_of c (List.map atom_exp xs) : Level@univ_nf_level_sort
    (** The constant is of a tier at most that sort *)
  ; univ_nf_level_constant : fst c <= univ_nf_level_sort
    (** Each atom is a level of its own sort, at most that sort *)
  ; univ_nf_level_well_scoped : @level_atoms_well_scoped gc_deps gc_stack univ_nf_level_sort Γ xs
    (** The atoms are atoms of the normal form of a typed level *)
  ; univ_nf_level_atoms : forall j s a, List.In (mk_level_atom j s a) xs -> nbe_level_atom Γ s a }.

(** A typed small universe whose normal form is [univⁿ c xs]: its level
    term's normal form is [nf_lvl c xs] ([nbe_ty_univ_level]), which
    soundness reads as [univ_nf_level]. *)
Lemma univ_nf_level_of_nbe : forall {Γ t c xs A},
    Γ ⊢ Type⟨t⟩ : A ->
    nbe_ty_f Γ Type⟨t⟩ (univⁿ c xs) ->
    univ_nf_level Γ t c xs.
Proof.
  intros * HA Hn.
  destruct (wf_univ_lvl_inversion HA) as [n Ht].
  pose proof (nbe_ty_univ_level (L := (c, xs)) (n := n) Hn) as Hl.
  pose proof (soundness_lvl_well_scoped Ht Hl) as [Hc Hws]; cbn in Hc, Hws.
  econstructor; [ exact (soundness' Ht Hl) | exact Hc | exact Hws | exact (nbe_level_atom_of_nbe Ht Hl) ].
Qed.

(** The atoms of the levels of two small universes in normal form are
    coherent together: they are atoms of normal forms of typed levels
    ([univ_nf_level_atoms]). *)
Lemma univ_nfs_coherent : forall {Γ t c xs A t' d ys B},
    Γ ⊢ Type⟨t⟩ : A ->
    nbe_ty_f Γ Type⟨t⟩ (univⁿ c xs) ->
    Γ ⊢ Type⟨t'⟩ : B ->
    nbe_ty_f Γ Type⟨t'⟩ (univⁿ d ys) ->
    @level_atoms_coherent gc_deps gc_stack Γ (xs ++ ys).
Proof.
  intros * HA Hn HB Hn'; apply level_atoms_coherent_of_nbe.
  intros j s a Hin; apply List.in_app_or in Hin as [Hin | Hin];
    [ exact (univ_nf_level_atoms _ _ _ _ (univ_nf_level_of_nbe HA Hn) _ _ _ Hin)
    | exact (univ_nf_level_atoms _ _ _ _ (univ_nf_level_of_nbe HB Hn') _ _ _ Hin) ].
Qed.

(** NbE at a small universe reads the term back as a type. *)
Lemma nbe_suniv_to_nbe_ty : forall {Γ M t W},
    nbe_f Γ M Type⟨t⟩ W ->
    nbe_ty_f Γ M W.
Proof.
  intros * Hn.
  inversion Hn; subst.
  directed_inversion_by_head eval_exp; subst.
  invert_nbe_term.
  match goal with Hr : Rnf ⇓ _ _ in _ ↘ _ |- _ => inversion Hr; subst; try (cbn in *; discriminate) end.
  econstructor; eassumption.
Qed.

(** A small universe at a literal level reads back as itself. *)
Lemma nbe_ty_suniv_lit : forall {Γ n W},
    nbe_ty_f Γ Type⟨𝕃ᵒ n⟩ W ->
    W = nf_univ n nil.
Proof.
  intros * Hn.
  directed_inversion_clear_by_head nbe_ty; directed_inversion_by_head eval_exp; subst.
  match goal with H : eval_exp _ _ (a_llit _) _ _ |- _ => inversion H; subst end.
  directed_inversion_by_head read_typ; subst.
  match goal with H : Rnf ⇓ Levelᵈ (domain_level_lit n) in _ ↘ _ |- _ =>
    pose proof (read_nf_domain_level_lit n (length Γ)) as Hk;
    assert (L = lvl_lit n) as -> by (apply nf_lvl_of_inj; eapply functional_read_nf; eassumption) end.
  reflexivity.
Qed.

(** The large universes are ordered by their indices. *)
Lemma subtyp_large_inv : forall {Γ i j},
    Γ ⊢ Typeω@i ⊆ Typeω@j ->
    i <= j.
Proof.
  intros * H.
  destruct (subtyp_at_initial_env H) as (ρ & a & a' & k & _ & Ha & Ha' & Hs).
  inversion Ha; subst; inversion Ha'; subst.
  inversion Hs; subst; try assumption.
  match goal with Hp : per_prop _ _ |- _ => destruct Hp as [Hp _ _]; cbn in Hp; discriminate end.
Qed.

(** The normal form of a universe term is a universe normal form: [Typeω@i]
    is its own, and [Type⟨t⟩]'s is the universe at the normal form of [t]. *)
Lemma nbe_ty_univ_term : forall {Γ T W},
    univ_term T ->
    nbe_ty_f Γ T W ->
    exists u, W = universe_nf_to_nf u.
Proof.
  intros * HT Hn; inversion HT; subst;
    directed_inversion_clear_by_head nbe_ty; directed_inversion_by_head eval_exp; subst;
    directed_inversion_by_head read_typ; subst.
  - exists (universe_large i); reflexivity.
  - exists (universe_small L); reflexivity.
Qed.

Lemma nbe_ty_typ_univ_nf : forall {Γ i u},
    nbe_ty_f Γ Typeω@i (universe_nf_to_nf u) ->
    u = universe_large i.
Proof.
  intros * Hn; directed_inversion_clear_by_head nbe_ty; directed_inversion_by_head eval_exp; subst.
  destruct u; cbn in *; match goal with H : Rtyp _ in _ ↘ _ |- _ => inversion H; subst end; congruence.
Qed.

Lemma nbe_ty_suniv_univ_nf : forall {Γ t u},
    nbe_ty_f Γ Type⟨t⟩ (universe_nf_to_nf u) ->
    exists L, u = universe_small L /\ nbe_f Γ t Level (nf_lvl_of L).
Proof.
  intros * Hn; destruct u as [L | i].
  - exists L; split; [ reflexivity | exact (nbe_ty_univ_level Hn) ].
  - exfalso; directed_inversion_clear_by_head nbe_ty; directed_inversion_by_head eval_exp; subst.
    cbn in *; match goal with H : Rtyp _ in _ ↘ _ |- _ => inversion H end.
Qed.

Lemma nbe_ty_lit_univ_nf : forall {Γ n u},
    nbe_ty_f Γ Type@n (universe_nf_to_nf u) ->
    u = universe_small (lvl_lit (ordinal_of_nat n)).
Proof.
  intros * Hn; apply nbe_ty_suniv_lit in Hn.
  destruct u as [[c xs] | i]; cbn in Hn; inversion Hn; reflexivity.
Qed.

(** NbE at a universe term reads the term back as a type. *)
Lemma nbe_univ_term_to_nbe_ty : forall {Γ T M W},
    univ_term T ->
    nbe_f Γ M T W ->
    nbe_ty_f Γ M W.
Proof. intros * [] Hn; [ eapply nbe_type_to_nbe_ty; exact Hn | eapply nbe_suniv_to_nbe_ty; exact Hn ]. Qed.

(** A type of a universe term is a type of a large universe. *)
Lemma univ_term_large : forall {Γ T M},
    univ_term T ->
    Γ ⊢ M : T ->
    exists k, Γ ⊢ M : Typeω@k.
Proof.
  intros * [i | t] HM; [ eauto |].
  assert (⊢ Γ) by (gen_presups; assumption).
  assert (exists C, Γ ⊢ Type⟨t⟩ : C) as [C Hk] by (gen_presups; eexists; eassumption).
  destruct (wf_univ_lvl_inversion Hk) as [n Ht].
  exists 0; eapply wf_exp_subtyp'; [ exact HM | eapply wf_subtyp_small_large; eassumption ].
Qed.

(** A universe term with a term is a type of a large universe. *)
Lemma univ_term_typed_large : forall {Γ T M},
    univ_term T ->
    Γ ⊢ M : T ->
    exists k, Γ ⊢ T : Typeω@k.
Proof.
  intros * [i | t] HM; assert (⊢ Γ) by (gen_presups; assumption).
  - exists (S i); apply wf_typ; assumption.
  - assert (exists C, Γ ⊢ Type⟨t⟩ : C) as [C Hk] by (gen_presups; eexists; eassumption).
    destruct (wf_univ_lvl_inversion Hk) as [n Ht].
    exists 0; eapply wf_univ_large_tm; eassumption.
Qed.

(** The shape of the normal form of a type of a universe term, when it is
    not neutral.  A large universe [Typeω@j] in [Typeω@i] has [j < i], and is
    in no small universe; a small universe [Type⟨l⟩] in [Type⟨t⟩] has the
    successor of [l] below the normal form of [t] ([subtyp_suniv_bound]). *)
Lemma typ_nf_below_of_nbe : forall {Γ M T u W},
    univ_term T ->
    Γ ⊢ M : T ->
    nbe_ty_f Γ T (universe_nf_to_nf u) ->
    nbe_f Γ M T W ->
    (forall κ V, W <> ⇑ⁿ{κ} V) ->
    typ_nf_below u W.
Proof.
  intros * HT HM HnT Hn Hne.
  assert (⊢ Γ) by (gen_presups; assumption).
  assert (HMW : Γ ⊢ M ≈ W : T) by (eapply soundness'; eassumption).
  assert (HW : Γ ⊢ W : T) by (gen_presups; assumption).
  destruct (univ_term_large HT HM) as [k HMl].
  destruct (univ_term_large HT HW) as [k' HWl].
  pose proof (nbe_univ_term_to_nbe_ty HT Hn) as Hty.
  (** The normal form of the normal form, equal to it up to proofs *)
  destruct (normalization_ty HWl) as (W'' & HW'').
  pose proof (idempotent_nbe_ty HMl Hty HW'') as HEW.
  inversion Hty; subst.
  match goal with Hr : Rtyp _ in _ ↘ W |- _ => inversion Hr; subst end.
  (** A [Π] by the kind of its codomain: into a universe, a proposition,
      or a type of levels *)
  all: try match goal with |- typ_nf_below _ (nf_pi _ ?κc _ _) => destruct κc end.
  all: try solve [ constructor | exfalso; eapply Hne; reflexivity ].
  (** A proposition is in no universe *)
  all: try solve [ exfalso; cbn [nf_to_exp] in HWl; eapply (typ_prop_absurd HWl), (prop_former_typed HWl); eauto 7 ].
  (** A type of levels is in no universe ([level_type_not_large]) *)
  all: try solve [ exfalso; cbn [nf_to_exp] in HWl; destruct (wf_pi_inversion_at HWl) as [U HU HA HB Hk _];
                   eapply level_type_not_large; [| exact HWl ];
                   change LevelSort with (abs_kind_sort ak_level U); eapply wf_pi; eassumption ].
  - destruct HT as [i0 | t].
    + apply nbe_ty_typ_univ_nf in HnT as ->.
      cbn in HW; apply wf_typ_inversion, subtyp_large_inv in HW.
      constructor; lia.
    + exfalso; cbn in HW; apply wf_typ_inversion in HW; eapply subtyp_large_small_absurd; exact HW.
  - destruct L as [c xs]; unfold nf_univ_of in *; cbn [fst snd] in *.
    constructor.
    destruct HT as [i | t].
    + apply nbe_ty_typ_univ_nf in HnT as ->; exact I.
    + destruct (nbe_ty_suniv_univ_nf HnT) as (L' & -> & HL').
      cbn [universe_nf_le nf_to_exp] in *.
      (** A small universe is its own normal form up to the proofs in
          its level's atoms: its level is canonical *)
      assert (HWW : exists xs2, nbe_ty_f Γ (univⁿ c xs) (univⁿ c xs2) /\ lvl_eq_upto_proofs (c, xs) (c, xs2)).
      { pose proof HW'' as HW0; destruct HW0 as [ρ2 a2 Hρ2 Ha2 Hr2].
        directed_inversion_by_head eval_exp; subst.
        inversion Hr2; subst.
        match goal with H3 : Rnf ⇓ Levelᵈ _ in _ ↘ nf_lvl_of ?L2 |- _ => destruct L2 as [c2 xs2] end.
        unfold nf_univ_of in *; cbn [fst snd] in HEW, HW''.
        assert (HEW' : lvl_eq_upto_proofs (c, xs) (c2, xs2))
          by (unfold nf_eq_upto_proofs in HEW; cbn in HEW; eqb_split; eqb_leaves; split; assumption).
        destruct HEW' as [Hc2 Hxs2]; cbn [fst] in Hc2; subst c2.
        exists xs2; split; [ exact HW'' | split; [ reflexivity | exact Hxs2 ] ]. }
      destruct HWW as (xs2 & HWW & Hxs2).
      set (E := lvl_exp_of c (List.map atom_exp xs)) in *.
      apply wf_univ_inversion in HW.
      assert (HL : nbe_f Γ E Level (nf_lvl_of (c, xs2))) by (apply (nbe_ty_univ_level (L := (c, xs2))); exact HWW).
      inversion HL; subst.
      directed_inversion_by_head eval_exp; subst.
      invert_nbe_term.
      match goal with Hr : Rnf ⇓ Levelᵈ ?l in _ ↘ _, HE : ⟦ E ⟧ _ ↘ ?l |- _ =>
        destruct (domain_level_canon_of_read _ _ _ Hr) as [Hsh [L0 [HL0 Hc]]] end.
      apply nf_lvl_of_inj in HL0; subst L0.
      (** The universe above has the successor level, whose canonical form
          is, up to proofs, the canonical successor of [(c, xs2)]. *)
      destruct (domain_level_canon_suc _ _ _ Hc) as (Ls & Hc' & ELs).
      assert (Hn' : nbe_f Γ (succl E) Level (nf_lvl_of Ls)).
      { eapply nbe_evaluated_intro; [ eassumption | eassumption | apply eval_exp_succl; eassumption
                                    | apply domain_level_canon_read; [ apply domain_level_shape_suc | exact Hc' ] | constructor ]. }
      pose proof (subtyp_suniv_bound HW Hn' HL') as Hle.
      rewrite lvl_le_correct in *; intros ν Hν; specialize (Hle ν Hν).
      rewrite (lvl_eval_upto ν _ _ Hν ELs), (lvl_canon_eval ν _ Hν), !lvl_eval_suc,
        <- (lvl_eval_upto ν _ _ Hν Hxs2) in Hle.
      rewrite !lvl_eval_suc; exact Hle.
  - (** [LevelSort] is of the large universes only *)
    destruct HT as [i | t].
    + apply nbe_ty_typ_univ_nf in HnT as ->; constructor.
    + exfalso; cbn in HW; exact (level_sort_untyped HW).
Qed.

End Small_Typ.
