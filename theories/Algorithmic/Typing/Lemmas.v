From Stdlib Require Import Wf_nat PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Typing Require Import Definitions.
From Mctt.Algorithmic.Typing Require Export Functional.
From Mctt.Algorithmic.Subtyping Require Export Lemmas.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import Consequences.Rules.
From Mctt.Core.Completeness.Modules Require Import ValidUnit.
From Mctt.Core.Consequences Require Import Consistency.
From Mctt.Core.Syntactic Require Import CoreInversions Corollaries Fresh.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong IndConv.
From Mctt.Core.Syntactic.Levels Require Levels.
From Mctt.Algorithmic Require Import Strengthening.
From Mctt.Core.Syntactic.System.Global Require Import Modules Paths DescTyping LookupSound MemberWf.
From Mctt.Core.Semantic Require Import MemberWf Avoid.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
Import Domain_Notations Fixed_Notations Wk_Notations.

(** The universe premise of a [Π] rule, as its two cases: a large universe,
    or a small one at a level. *)
#[local]
Ltac destruct_univ :=
  repeat match goal with
         | HU : wf_is_univ _ _ _ ?U |- _ => is_var U; inversion HU; subst; clear HU
         end;
  repeat match goal with
         | H : context [exp_wk (a_typ ?i) ?φ] |- _ => change (exp_wk (a_typ i) φ) with (a_typ i) in H
         | H : context [exp_wk (a_univ ?L) ?φ] |- _ => change (exp_wk (a_univ L) φ) with (a_univ (exp_wk L φ)) in H
         | |- context [exp_wk (a_typ ?i) ?φ] => change (exp_wk (a_typ i) φ) with (a_typ i)
         | |- context [exp_wk (a_univ ?L) ?φ] => change (exp_wk (a_univ L) φ) with (a_univ (exp_wk L φ))
         end.

Section Fixed_GCtx.
  Context {GC : GCtx}.

#[local]
Hint Resolve functional_alg_type_infer : mctt.

End Fixed_GCtx.

(** The global context is well formed: a hypothesis says so, or a
    judgment in one of its contexts presupposes it. *)
Ltac gctx_wf_tac :=
  lazymatch goal with
  | |- wf_gstack ?T ?X =>
      first [ assumption
            | match goal with H : wf_ctx T X _ |- _ => exact (ctx_wf_gctx _ _ _ H) end
            | match goal with H : wf_exp T X _ _ _ |- _ => exact (ctx_wf_gctx _ _ _ (presup_exp_ctx H)) end
            | match goal with H : wf_modexp_eq T X _ _ _ |- _ => exact (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx H)) end
            | match goal with H : exists i, wf_exp T X _ _ _ |- _ =>
                let i := fresh "i" in let Hi := fresh "Hi" in
                destruct H as [i Hi]; exact (ctx_wf_gctx _ _ _ (presup_exp_ctx Hi)) end
            | match goal with H : wf_type T X _ _ |- _ =>
                let Hi := fresh "Hi" in
                destruct H as [? ? Hi]; exact (ctx_wf_gctx _ _ _ (presup_exp_ctx Hi)) end
            | solve [ mauto 3 ] ]
  end.

Ltac functional_alg_type_infer_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_alg_type_infer equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (?Γ ⊢a ?M ⟹ ?A1), H2 : (?Γ ⊢a ?M ⟹ ?A2) |- _ =>
      clean replace A2 with A1
        by first [ solve [ eapply functional_alg_type_infer; [| exact H1 | exact H2 ]; gctx_wf_tac ]
                 | solve [ eapply functional_alg_type_infer; [| exact H2 | exact H1 ]; gctx_wf_tac ]
                 | solve [ mauto 2 using functional_alg_type_infer ]
                 | tactic_error A2 A1 ];
      clear H2
  end.
Ltac functional_alg_type_infer_rewrite_clear := repeat functional_alg_type_infer_rewrite_clear1.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Moving Levels Up the Sorts

    A level of a sort is a level of every larger sort ([wf_subtyp_level]). *)
Lemma wf_exp_level_up : forall {Γ M m n},
    m <= n ->
    Γ ⊢ M : Level@m ->
    Γ ⊢ M : Level@n.
Proof.
  intros * Hmn HM; assert (⊢ Γ) by (gen_presups; assumption).
  eapply wf_exp_subtyp'; [ exact HM | apply wf_subtyp_level; assumption ].
Qed.

Lemma wf_exp_eq_level_up : forall {Γ M M' m n},
    m <= n ->
    Γ ⊢ M ≈ M' : Level@m ->
    Γ ⊢ M ≈ M' : Level@n.
Proof.
  intros * Hmn HM; assert (⊢ Γ) by (gen_presups; assumption).
  eapply wf_exp_eq_subtyp'; [ exact HM | apply wf_subtyp_level; assumption ].
Qed.

(** ** Universe Normal Forms as Types

    A universe normal form, as a term, is a universe. *)
Lemma univ_term_universe_nf_tm : forall u, univ_term (universe_nf_tm u).
Proof. intros [L | n]; constructor. Qed.

(** A goal [exists k, Γ ⊢ U : Typeω@k] at a universe [U] that a hypothesis
    (or a presupposition of one) types a term at: a universe is of a large
    one ([univ_term_typed_large]), as a proposition is not. *)
Ltac univ_large :=
  let univ_term_tac := first [ apply univ_term_universe_nf_tm | constructor ] in
  lazymatch goal with
  | |- exists _, wf_exp _ _ ?Γ _ ?U =>
      first [ match goal with H : wf_exp _ _ Γ _ _ |- _ => refine (univ_term_typed_large _ H); univ_term_tac end
            | gen_presups;
              match goal with H : wf_exp _ _ Γ _ _ |- _ => refine (univ_term_typed_large _ H); univ_term_tac end ]
  end.

(**

    The universe a type infers is a universe normal form [u]; as a term it is
    [universe_nf_tm u], which is a small universe at a level term or a large one.
    The declarative rules ask for a large universe, which a small one is below
    ([wf_subtyp_small_large]): this is the cumulativity the algorithmic layer
    relies on. *)
Lemma wf_exp_universe_nf_large_index : forall {Γ A} {u : universe_nf},
    Γ ⊢ A : universe_nf_tm u ->
    Γ ⊢ A : Typeω@(universe_nf_large_index u).
Proof.
  intros * HA; destruct u as [L | n]; cbn in *; [| exact HA ].
  destruct (presup_exp_typ_sorted HA ltac:(discriminate)) as (Sk & _ & Hk).
  assert (⊢ Γ) by (gen_presups; assumption).
  destruct (wf_univ_lvl_inversion Hk) as [n Hn].
  eapply wf_exp_subtyp'; [ exact HA | eapply wf_subtyp_small_large; eassumption ].
Qed.

(** The normal form of a type, when it holds no proof, is its own normal
    form: normalisation is idempotent up to proofs ([idempotent_nbe_ty]),
    and only itself is equal up to proofs to a normal form without proofs
    ([nf_ne_proof_free_eq]). *)
Lemma nbe_ty_self : forall {Γ i A B},
    Γ ⊢ A : Typeω@i ->
    nbe_ty_f Γ A B ->
    nf_proof_free B ->
    nbe_ty_f Γ B B.
Proof.
  intros * HA Hn Hpf.
  assert (Γ ⊢ A ≈ B : Typeω@i) by (eapply soundness_ty'; eassumption).
  assert (HB : Γ ⊢ B : Typeω@i) by (gen_presups; assumption).
  destruct (soundness_ty HB) as (C & HC & _).
  pose proof (proj1 nf_ne_proof_free_eq B Hpf C (idempotent_nbe_ty HA Hn HC)) as <-.
  exact HC.
Qed.

(** A universe normal form whose level is a canonical level of a sort its
    level term has, each atom a level of its own sort and holding no proof:
    what the normal form of a universe is ([univ_nf_well_scoped],
    [nbe_ty_univ_proof_free]). *)
Definition universe_nf_well_scoped (Γ : ctx) (u : universe_nf) : Prop :=
  match u with
  | universe_small L => (exists n, Γ ⊢ lvl_exp_of (fst L) (List.map atom_exp (snd L)) : Level@n /\
                    fst (fst L) <= n /\ @level_atoms_well_scoped gc_deps gc_stack n Γ (snd L)) /\
                    all_list (fun a => ne_proof_free (atom_level a)) (snd L)
  | universe_large _ => True
  end.

Lemma universe_nf_well_scoped_of_nbe : forall {Γ u i},
    Γ ⊢ universe_nf_tm u : Typeω@i ->
    nbe_ty_f Γ (universe_nf_tm u) (universe_nf_to_nf u) ->
    universe_nf_well_scoped Γ u.
Proof.
  intros * Hu Hn; destruct u as [[c xs] | j]; cbn in *; [| exact I ].
  split; [ exact (univ_nf_well_scoped Hu Hn) | exact (nbe_ty_univ_proof_free Hu Hn) ].
Qed.

(** A property of the elements of a list that follows from two others and
    the motive the nested induction gives them holds of the list. *)
Lemma list_all_combine {A : Set} (Q : A -> Type) (P1 P2 P3 : A -> Prop) : forall l,
    Base.list_all A Q l -> (forall x, Q x -> P1 x -> P2 x -> P3 x) -> all_list P1 l -> all_list P2 l -> all_list P3 l.
Proof. intros l Hl Hf; induction Hl; cbn; [ auto | intros [] []; split; auto ]. Qed.

(** A normal form that holds no proof and avoids a variable outside its
    proofs avoids it ([nf_fresh_outside_proofs], the freshness readback
    gives under a weakening). *)
Lemma nf_ne_fresh_of_outside_proofs :
  (forall W, nf_proof_free W -> forall k, nf_fresh_outside_proofs k W -> nf_fresh k W) /\
  (forall M, ne_proof_free M -> forall k, ne_fresh_outside_proofs k M -> ne_fresh k M).
Proof.
  apply nf_ne_ind; intros; cbn [nf_proof_free ne_proof_free nf_fresh_outside_proofs ne_fresh_outside_proofs nf_fresh ne_fresh] in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; try contradiction; try tauto; try solve [ split; auto ].
  all: repeat split; try assumption; try solve [ auto ].
  all: match goal with
       | Hl : Base.list_all _ _ ?l, Hp : all_list ?P1 ?l, Hf : all_list ?P2 ?l |- all_list _ ?l =>
           lazymatch P1 with context [ nf_proof_free ] => idtac | context [ ne_proof_free ] => idtac end;
           lazymatch P2 with context [ nf_fresh_outside_proofs ] => idtac | context [ ne_fresh_outside_proofs ] => idtac end;
           apply (list_all_combine _ P1 P2 _ l Hl); [| exact Hp | exact Hf ]
       end.
  all: intros x Hx Hp Hf; cbn in *; try solve [ auto ].
  (** a block: its scrutinee type, motive and branches *)
  all: destruct Hx; unfold normal_block_forall in *; cbn in *; auto.
  destruct Hp as (Hp1 & Hp2 & Hp3); destruct Hf as (Hf1 & Hf2 & Hf3).
  split; [ auto | split; [ auto |] ].
  eapply list_all_combine; [ eassumption | | exact Hp3 | exact Hf3 ].
  intros x Hb Hpb Hfb; destruct Hb; cbn in *; auto.
Qed.

(** The list of a list of terms mapped is checked by the check of its
    elements mapped. *)
Lemma forallb_map_eq_list_all : forall {X : Set} (P : X -> Type) (f : X -> bool) (g : X -> X) l,
    list_all X P l -> (forall x, P x -> f (g x) = f x) -> List.forallb f (List.map g l) = List.forallb f l.
Proof. intros * Hl Hf; induction Hl as [| x Hx l Hl IH]; cbn; [ reflexivity | rewrite (Hf _ Hx), IH; reflexivity ]. Qed.

(** Un-weakening moves variables only: it keeps proof-freedom. *)
Lemma nf_ne_unwk_proof_freeb :
  (forall W k, nf_proof_freeb (nf_unwk k W) = nf_proof_freeb W) /\
  (forall u k, ne_proof_freeb (ne_unwk k u) = ne_proof_freeb u).
Proof.
  apply nf_ne_ind; intros; cbn [nf_unwk ne_unwk nf_proof_freeb ne_proof_freeb]; try reflexivity;
    repeat match goal with H : forall k, _ = _ |- _ => rewrite H end; try reflexivity.
  all: repeat match goal with H : list_all _ _ ?l |- context [ ListDef.map ?g ?l ] =>
                erewrite (forallb_map_eq_list_all _ _ _ _ H) end.
  all: try reflexivity.
  all: intros x Hx; first [ solve [ eauto ] | destruct Hx; cbn; solve [ eauto ] | idtac ].
  all: destruct Hx as [ar Z HZ M HM brs Hbrs]; unfold normal_block_forallb, map_normal_block;
    cbn [block_arity block_scrutinee_type block_motive block_branches]; rewrite HZ, HM.
  all: erewrite (forallb_map_eq_list_all _ _ _ _ Hbrs); [ reflexivity | intros br Hbr; destruct Hbr; cbn; eauto ].
Qed.

Lemma ne_unwk_proof_free : forall k u, ne_proof_free u -> ne_proof_free (ne_unwk k u).
Proof.
  intros * H; apply (proj2 nf_proof_freeb_iff); rewrite (proj2 nf_ne_unwk_proof_freeb); apply (proj2 nf_proof_freeb_iff); exact H.
Qed.

(** The bound of a level without proofs under a binder ([lvl_bound]) holds
    none. *)
Lemma level_atoms_unwk_fresh_proof_free : forall k c xs, all_list (fun a => ne_proof_free (atom_level a)) xs ->
    nf_proof_free (nf_lvl c (List.map (map_level_atom (ne_unwk k)) (level_atoms_fresh_part k xs))).
Proof.
  intros k c xs; cbn [nf_proof_free]; induction xs as [| [j s a] r IH]; cbn; [ intros; exact I |].
  intros [Ha Hr]; destruct (ne_freshb k a); cbn; [ split; [ exact (ne_unwk_proof_free _ _ Ha) | exact (IH Hr) ] | exact (IH Hr) ].
Qed.

(** The fresh part of a level's atoms is a part of them. *)
Lemma level_atoms_fresh_part_In : forall k xs j s a, List.In (mk_level_atom j s a) (level_atoms_fresh_part k xs) -> List.In (mk_level_atom j s a) xs.
Proof.
  intros k xs; induction xs as [| [j0 s0 a0] r IH]; cbn; [ auto |].
  intros * Hin; destruct (ne_freshb k a0); [ destruct Hin as [-> | Hin]; [ left; reflexivity | right; eauto ] | right; eauto ].
Qed.

(** Atoms of their sorts without proofs are coherent: two of them equal up
    to proofs are the same ([ne_proof_free_eq]). *)
Lemma level_atoms_coherent_proof_free : forall Γ n xs, @level_atoms_well_scoped gc_deps gc_stack n Γ xs ->
    all_list (fun a => ne_proof_free (atom_level a)) xs -> @level_atoms_coherent gc_deps gc_stack Γ xs.
Proof.
  intros * Hw Hp j s a j' b Ha Hb Hab.
  assert (Hpa : ne_proof_free a).
  { clear - Hp Ha; induction xs as [| x r IH]; [ destruct Ha |]; destruct Hp as [Hx Hr]; destruct Ha as [-> | Ha]; [ exact Hx | exact (IH Hr Ha) ]. }
  pose proof (ne_proof_free_eq _ _ Hpa Hab) as <-.
  exact (wf_exp_eq_refl (level_atoms_well_scoped_In _ _ _ _ _ _ Hw Ha)).
Qed.

(** The domain of a [Π] the algorithm counts in the universe [u]: a type
    of the sort at its kind next to [u], where [u] (for a proposition or a
    type of levels the least small universe, [is_sort_nf_prop],
    [is_sort_nf_level]) is a type. *)
Definition pi_domain_ok (Γ : ctx) (A : typ) (κd : abs_kind) (u : universe_nf) : Prop :=
  Γ ⊢ A : abs_kind_sort κd (universe_nf_tm u) /\ exists k, Γ ⊢ universe_nf_tm u : Typeω@k.

(** A type of a sort normal form [UA] ([is_sort_nf]) is of its sort: a
    large universe, [Prop] or [LevelSort]. *)
Lemma sort_typed_of_is_sort_nf : forall {Γ A} {UA : nf} {r u},
    Γ ⊢ A : UA -> is_sort_nf UA r u -> Γ ⊢ A : abs_kind_sort r Typeω@(universe_nf_large_index u).
Proof.
  intros * HA Hs; destruct Hs as [W u' Hu | |]; cbn [abs_kind_sort]; [| exact HA | exact HA ].
  rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HA.
  exact (wf_exp_universe_nf_large_index HA).
Qed.

(** The sort above is a sort. *)
Lemma type_sort_kind_universe : forall r i, type_sort (abs_kind_sort r Typeω@i).
Proof. intros; apply type_sort_abs_kind; constructor. Qed.

(** It is a type ([⊢ᵗ]): a large universe or [Prop] of the next universe,
    [LevelSort] the sort of the types of levels. *)
Lemma kind_sort_universe_wf_type : forall Γ r i, ⊢ Γ -> Γ ⊢ᵗ abs_kind_sort r Typeω@i.
Proof.
  intros * HΓ; destruct r; cbn [abs_kind_sort];
    [ eapply wf_type_of_sort; [ apply (type_sort_universe (S i)) | apply wf_typ, HΓ ]
    | eapply wf_type_of_sort; [ apply (type_sort_universe 0) | eapply wf_prop_large; exact HΓ ]
    | apply wf_type_level_sort, HΓ ].
Qed.

(** The sort of a motive's kind is of the next universe: a large universe
    or [Prop], never [LevelSort] ([motive_kind]). *)
Lemma motive_kind_sort_typed : forall Γ r i, motive_kind r -> ⊢ Γ -> Γ ⊢ abs_kind_sort r Typeω@i : Typeω@(S i).
Proof. intros * [] HΓ; cbn [abs_kind_sort]; [ apply wf_typ, HΓ | eapply wf_prop_large; exact HΓ ]. Qed.

(** An application spine headed by a term other than [LevelSort] is not
    [LevelSort]. *)
Lemma apps_exp_not_level_sort : forall l M, M <> LevelSort -> apps_exp M l <> LevelSort.
Proof. induction l as [| N l IH]; intros M HM; cbn; [ exact HM | apply IH; discriminate ]. Qed.

(** A type of a sort normal form is a [Π] domain at its kind and
    universe. *)
Lemma pi_domain_ok_of_is_sort_nf : forall {Γ A} {UA : nf} {r u},
    Γ ⊢ A : UA -> is_sort_nf UA r u -> pi_domain_ok Γ A r u.
Proof.
  intros * HA Hs.
  assert (⊢ Γ) by (gen_presups; assumption).
  destruct Hs as [W u' Hu | |].
  - rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HA; split; [ exact HA |].
    exact (univ_term_typed_large (univ_term_universe_nf_tm _) HA).
  - split; [ exact HA |].
    exists 0; cbn; eapply (wf_univ_large_tm (n := 0)); [ assumption | apply wf_llit; [ cbn; lia | assumption ] ].
  - split; [ exact HA |].
    exists 0; cbn; eapply (wf_univ_large_tm (n := 0)); [ assumption | apply wf_llit; [ cbn; lia | assumption ] ].
Qed.

(** The universe of a [Π] ([universe_nf_pi_tm]).  Two small universes join in the
    small tier, the codomain's level bounded under the binder
    ([lvl_bound]): the bound, weakened back, is above the codomain's level
    ([lvl_bound_above]) and mentions no bound variable, so it is the weakening
    of a level of [Γ] ([level_nf_strengthen]); both parts are moved up to the
    join.  Otherwise the [Π] is at the large join. *)
Lemma wf_pi_universe_nf_pi : forall {Γ κd A B} {u v : universe_nf},
    pi_domain_ok Γ A κd u ->
    Γ ▹{κd} A ⊢ B : universe_nf_tm v ->
    universe_nf_well_scoped (Γ ▹{κd} A) v ->
    Γ ⊢ Π{κd} A B : universe_nf_pi_tm u v.
Proof.
  intros * [HA HUk] HB Hv.
  assert (⊢ Γ) by (gen_presups; assumption).
  assert (HAl : Γ ⊢ A : abs_kind_sort κd Typeω@(universe_nf_large_index u))
    by (destruct κd; cbn [abs_kind_sort] in HA |- *; [ apply wf_exp_universe_nf_large_index; exact HA | exact HA | exact HA ]).
  assert (HBl : Γ ▹{κd} A ⊢ B : Typeω@(universe_nf_large_index v)) by (apply wf_exp_universe_nf_large_index; exact HB).
  assert (HΓA : ⊢ Γ ▹{κd} A) by (eapply wf_ctx_extend; [ exact HAl | apply sort_kind_abs_kind_sort ]).
  (** The domain moved up a large universe: a type of a universe is lifted,
      a proposition or a type of levels stays. *)
  assert (HAup : forall k, universe_nf_large_index u <= k -> Γ ⊢ A : abs_kind_sort κd Typeω@k)
    by (intros k Hk; destruct κd; cbn [abs_kind_sort] in HAl |- *; [ eapply lift_exp_ge; [| exact HAl ]; exact Hk | exact HAl | exact HAl ]).
  destruct u as [[c xs] | i], v as [[d ys] | j]; cbn [universe_nf_pi_tm universe_nf_max universe_nf_tm universe_nf_large_index fst snd] in *;
    (** A large join: the domain lifted to it. *)
    [| (try (destruct xs); try (destruct ys); cbn [universe_nf_tm universe_nf_max universe_nf_large_index] in *;
        match goal with |- _ ⊢ _ : Typeω@?K =>
          change (Typeω@K) with (abs_kind_sort ak_relevant Typeω@K);
          eapply wf_pi; [ apply wf_is_univ_large; assumption | apply HAup; lia | eapply lift_exp_ge; [| exact HBl ]; lia
                        | apply pi_kinds_relevant ]
        end) .. ].
  - (** The small join. *)
    destruct Hv as [(nB & HLB0 & Hd & Hys) Hpfv]; cbn [fst snd] in *.
    unfold lvl_bound; cbn [fst snd].
    set (LA := lvl_exp_of c (List.map atom_exp xs)) in *.
    set (cb := ordinal_max d (level_atoms_open_bound 0 ys)) in *.
    set (fp := level_atoms_fresh_part 0 ys) in *.
    set (LBs := lvl_exp_of cb (List.map atom_exp (List.map (map_level_atom (ne_unwk 0)) fp))).
    assert (exists nA, Γ ⊢ LA : Level@nA) as [nA HLA0]
      by (destruct HUk as [k Hk]; eapply wf_univ_lvl_inversion; exact Hk).
    set (N := S (Nat.max nA nB)).
    assert (Hcb : fst cb <= N)
      by (subst cb N; apply ordinal_max_fst_le;
          [ lia | eapply Nat.le_trans; [ apply level_atoms_open_bound_fst; eapply level_atoms_well_scoped_sorts; exact Hys | lia ] ]).
    assert (HysN : @level_atoms_well_scoped gc_deps gc_stack N (Γ ▹{κd} A) ys) by (eapply level_atoms_well_scoped_mono; [| exact Hys ]; lia).
    assert (HfpN : @level_atoms_well_scoped gc_deps gc_stack N (Γ ▹{κd} A) fp) by (apply level_atoms_well_scoped_fresh_part; exact HysN).
    assert (HLB : Γ ▹{κd} A ⊢ lvl_exp_of d (List.map atom_exp ys) : Level@N) by (eapply wf_exp_level_up; [| exact HLB0 ]; lia).
    (** The bound, weakened back, is the level of its fresh atoms. *)
    assert (Hfresh : lvl_exp_of cb (List.map atom_exp fp) = LBs[↑]ʷ)
      by exact (nf_fresh_unwk 0 (nf_lvl cb fp) (level_atoms_fresh_part_fresh 0 ys)).
    assert (HLBl : Γ ▹{κd} A ⊢ LBs[↑]ʷ : Level@N)
      by (rewrite <- Hfresh; apply lvl_exp_of_wf; [ exact Hcb | exact HΓA | apply level_atoms_well_scoped_wf; exact HfpN ]).
    assert (Habove : Γ ▹{κd} A ⊢ maxl (lvl_exp_of d (List.map atom_exp ys)) LBs[↑]ʷ ≈ LBs[↑]ʷ : Level@N).
    { rewrite <- Hfresh.
      apply lvl_exp_of_le; [ lia | exact Hcb | exact HΓA | exact HysN | exact HfpN | |].
      - (** the atoms, of the codomain's level and of its fresh part, hold no proof *)
        eapply (level_atoms_coherent_incl ys); [| exact (level_atoms_coherent_proof_free _ _ _ HysN Hpfv) ].
        intros j s a Hin; exists j; apply List.in_app_or in Hin as [Hin | Hin]; [ exact Hin | exact (level_atoms_fresh_part_In _ _ _ _ _ Hin) ].
      - exact (lvl_bound_above 0 (d, ys)). }
    assert (HLA : Γ ⊢ LA : Level@N) by (eapply wf_exp_level_up; [| exact HLA0 ]; lia).
    (** The bound holds no proof, the codomain's level holding none: it is
        the weakening of a level of [Γ] ([level_nf_strengthen]). *)
    assert (HLBs : Γ ⊢ LBs : Level@N)
      by exact (level_nf_strengthen Γ κd A _ (nf_lvl cb (List.map (map_level_atom (ne_unwk 0)) fp))
                  (level_atoms_unwk_fresh_proof_free 0 cb ys Hpfv) HΓA HLBl).
    assert (Ht : Γ ⊢ maxl LA LBs : Level@N) by mauto 3.
    assert (Hw : Γ ▹{κd} A ⊢ʷ ↑ : Γ) by mauto 2.
    change (Type⟨maxl LA LBs⟩) with (abs_kind_sort ak_relevant Type⟨maxl LA LBs⟩).
    eapply wf_pi; [ eapply wf_is_univ_small, Ht | | | apply pi_kinds_relevant ].
    + destruct κd; cbn [abs_kind_sort] in HA |- *; [| exact HA | exact HA ].
      eapply wf_exp_subtyp'; [ exact HA |].
      eapply wf_subtyp_suniv; [ assumption | exact HLA | exact Ht | apply lvl_sub_maxl_l; assumption ].
    + cbn [abs_kind_sort exp_wk]; eapply wf_exp_subtyp'; [ exact HB |].
      assert (Hsub : Γ ⊢ Type⟨LBs⟩ ⊆ Type⟨maxl LA LBs⟩)
        by (eapply wf_subtyp_suniv; [ assumption | exact HLBs | exact Ht | apply lvl_sub_maxl_r; assumption ]).
      etransitivity; [| exact (wk_preserves_subtyp _ _ _ _ _ _ _ Hsub Hw) ].
      eapply wf_subtyp_suniv; [ exact HΓA | exact HLB | exact HLBl | exact Habove ].
Qed.

(** The universe of a [Π] is a type. *)
Lemma wf_universe_nf_pi_tm : forall {Γ κd A B} {u v : universe_nf},
    pi_domain_ok Γ A κd u ->
    Γ ▹{κd} A ⊢ B : universe_nf_tm v ->
    universe_nf_well_scoped (Γ ▹{κd} A) v ->
    exists k, Γ ⊢ universe_nf_pi_tm u v : Typeω@k.
Proof.
  intros * HA HB Hv.
  refine (univ_term_typed_large _ (wf_pi_universe_nf_pi HA HB Hv)).
  destruct u as [[] |], v as [[] |]; cbn; constructor.
Qed.

(** A premise [⟹ UA] with [is_univ_nf UA u] is sound as a typing at
    [universe_nf_tm u], while the declarative rules ask for a large universe: such a
    hypothesis is lifted to [Typeω@(universe_nf_large_index u)] ([wf_exp_universe_nf_large_index]).
    [is_univ_nf_eq] turns the side condition into the shape of [UA]. *)
#[local] Tactic Notation "lift_univ_at" constr(Δ) constr(A) constr(u) :=
  repeat match goal with Hi : is_univ_nf ?UA u |- _ =>
    assert_fails (constr_eq UA (universe_nf_to_nf u));
    rewrite (is_univ_nf_eq _ _ Hi) in * end;
  assert (Δ ⊢ A : universe_nf_tm u)
    by (rewrite <- nf_to_exp_univ_nf; mauto 2);
  assert (Δ ⊢ A : a_typ (universe_nf_large_index u))
    by (apply wf_exp_universe_nf_large_index; eassumption).

(** Terms with, position by position, the normal forms of terms at the
    instances of a telescope are, position by position, equal to them. *)
Lemma nfs_agree_sound : forall Δ Γ0 Γ σ σ' Ms Rs,
    all_assumptions Δ -> ⊢ (Δ ++ Γ0)%list -> Γ ⊢ˢ σ ≈ σ' : Γ0 ->
    List.length Ms = List.length Δ -> List.length Rs = List.length Δ ->
    (forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ σ Ms) j = Some T -> Γ ⊢ N : T) ->
    (forall j N T, List.nth_error Rs j = Some N -> List.nth_error (tele_insts Δ σ' Rs) j = Some T -> Γ ⊢ N : T) ->
    nfs_agree Γ Ms Rs (tele_insts Δ σ Ms) ->
    forall j N R T, List.nth_error Ms j = Some N -> List.nth_error Rs j = Some R ->
      List.nth_error (tele_insts Δ σ Ms) j = Some T -> Γ ⊢ N ≈ R : T.
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ HMl HRl HMs HRs Hag j N R T HN HR HT.
  - destruct Ms; [ destruct j; discriminate | discriminate ].
  - unfold all_assumptions in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [(κ0 & A0 & ->) _].
    rewrite List.length_app in HMl, HRl; cbn in HMl, HRl.
    destruct Ms as [| M0 Ms]; [ cbn in HMl; lia |]; destruct Rs as [| R0 Rs]; [ cbn in HRl; lia |].
    rewrite tele_insts_snoc in HMs, HRs, Hag, HT.
    rewrite <- List.app_assoc in HΔ; cbn [List.app] in HΔ.
    destruct (ctx_decomp_kind (ctx_app_wf_tail _ _ _ _ HΔ)) as (S0 & HS0k & HA0).
    pose proof (sort_kind_type_sort _ _ HS0k) as HS0.
    inversion Hag as [| ? ? ? W W' ? ? ? HMW HRW HWW Hag']; subst.
    assert (HM0 : Γ ⊢ M0 : A0[σ]) by (apply (HMs 0); reflexivity).
    assert (HR0' : Γ ⊢ R0 : A0[σ']) by (apply (HRs 0); reflexivity).
    assert (HAA : Γ ⊢ A0[σ] ≈ A0[σ'] : S0) by (eapply sub_eq_preserves_sort; [ exact HA0 | exact HS0 | exact Hσ ]).
    assert (HR0 : Γ ⊢ R0 : A0[σ]) by (exact (exp_conv_sort HS0 ltac:(symmetry; exact HAA) HR0')).
    assert (HMR : Γ ⊢ M0 ≈ R0 : A0[σ])
      by (eapply soundness_upto_proofs; [ exact HM0 | exact HR0 | eassumption | eassumption | eassumption ]).
    destruct j as [| j]; cbn in HN, HR, HT.
    + injection HN as <-; injection HR as <-; injection HT as <-; exact HMR.
    + eapply (IH _ _ _ _ Ms Rs); [ exact Hass | exact HΔ | | cbn in HMl; lia | cbn in HRl; lia | | | exact Hag' | exact HN | exact HR | exact HT ].
      * eapply wf_sub_eq_extend; [ exact Hσ | exact HA0 | exact HS0k | exact HM0 | exact HR0' | exact HMR ].
      * intros j' N' T' HN' HT'; apply (HMs (S j')); [ exact HN' | exact HT' ].
      * intros j' N' T' HN' HT'; apply (HRs (S j')); [ exact HN' | exact HT' ].
Qed.

(** The eliminator: its uniform parameters are typed, and the uniform
    arguments of its member's type at them are equal to those of the type
    its scrutinee infers ([nfs_agree_sound]), so the scrutinee is of the
    member's type ([mty_params_conv]); the blocks are typed at the uniform
    parameters, by the induction hypotheses.  The eliminator is of the
    motive's instance, before that is normalised. *)
Lemma alg_elim_typed : forall Γ M pc k Rs p D m Mm Dq Mk bm Bks Us Ns r i,
    ⊢ Γ -> Γ ⊢ M : apps (a_ind pc k) (List.map nf_to_exp Rs) ->
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm ->
    im_ref p m Mm = (pc, k) -> ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk ->
    List.length (List.map nf_to_exp Rs) = im_np Dq Mk ->
    List.nth_error Bks m = Some bm -> List.length Bks = ind_nblk D ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
       ⊢ Γ -> forall Srt, type_sort Srt -> Γ ⊢ T : Srt -> Γ ⊢ U : T) ->
    nfs_agree Γ (im_pre Mm Us) (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) ->
    Ns = List.skipn (ind_nu Dq) (List.map nf_to_exp Rs) ->
    blocks_binder_count_ok D Bks ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ⊢ (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list -> forall Srt, type_sort Srt ->
       (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢ Typeω@i : Srt ->
       (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢ eb_scrutinee_type b : Typeω@i) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) (eb_scrutinee_type b)
         (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ⊢ (elim_mctx p D j Mj Us ++ Γ)%list -> forall Srt, type_sort Srt ->
       (elim_mctx p D j Mj Us ++ Γ)%list ⊢ abs_kind_sort r Typeω@i : Srt ->
       (elim_mctx p D j Mj Us ++ Γ)%list ⊢ eb_motive b : abs_kind_sort r Typeω@i) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b)) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       ⊢ (elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ)%list -> forall Srt, type_sort Srt ->
       (elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ)%list ⊢ elim_branch_type p D j Mj c gs (eb_motive b) Us : Srt ->
       (elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ)%list ⊢ B : elim_branch_type p D j Mj c gs (eb_motive b) Us) ->
    motive_kind r ->
    Γ ⊢ a_elim r p Us m Bks M : (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)].
Proof.
  intros * HΓ HM Hl Hm Hr Hlq Hk HRl Hb HBl HUl HUs Hag -> HBnm HZt HZc HAt HBn HBa HBt Hmk.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hgw; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
  pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ HD)) as Hsuf.
  pose proof (block_member_not_rview _ _ _ _ _ Hsuf HBl Hm Hb) as Hnr.
  (** The uniform parameters. *)
  assert (HUt : forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T).
  { eapply tele_insts_typed_all; [ exact (decl_closed_ass _ Hc) | exact (wf_uparams_app _ _ _ HD Hc _ HΓ) | apply wf_sub_id, HΓ |].
    intros j U X HU HX (SX & HSX & HXt); exact (HUs _ _ _ HU HX HΓ _ HSX HXt). }
  (** The scrutinee, of the member's type. *)
  destruct (presup_exp_typ_sorted HM (apps_exp_not_level_sort (List.map nf_to_exp Rs) (a_ind pc k) ltac:(discriminate)))
    as (Skk & _ & Hkk).
  pose proof (wf_ind_apps_inv _ _ _ _ _ _ _ Hlq Hk Hkk HRl) as HRt.
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hnr Hr Hlq HUl HUt) as [HPl HPt].
  destruct (params_typed_split _ _ Dq Hcq _ _ _ _ Hk HRl HRt) as [HRu _].
  assert (HRl' : List.length (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) = ind_nu Dq)
    by (rewrite List.length_firstn; unfold im_np in HRl; lia).
  assert (HPR : forall j N R X, List.nth_error (im_pre Mm Us) j = Some N -> List.nth_error (List.map nf_to_exp Rs) j = Some R ->
             List.nth_error (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) j = Some X -> Γ ⊢ N ≈ R : X).
  { intros j N R X HN HR HX.
    assert (Hj : j < ind_nu Dq) by (rewrite <- HPl; apply List.nth_error_Some; congruence).
    eapply (nfs_agree_sound (ind_uparams Dq) Γ Γ Id Id); [ exact (decl_closed_ass _ Hcq) | exact (wf_uparams_app _ _ _ HDq Hcq _ HΓ)
           | apply wf_sub_eq_refl, wf_sub_id, HΓ | rewrite HPl; reflexivity | rewrite HRl'; reflexivity
           | exact HPt | exact HRu | exact Hag | exact HN | | exact HX ].
    rewrite List.nth_error_firstn; destruct (Nat.ltb_spec j (ind_nu Dq)); [ exact HR | lia ]. }
  destruct (mty_params_conv _ _ _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hnr Hr Hlq Hk HUl HUt HRl HRt HPR) as [HNl HNt [iE HE]].
  assert (HM' : Γ ⊢ M : ind_mty p D m Us (List.skipn (ind_nu Dq) (List.map nf_to_exp Rs))) by (eapply wf_conv'; [ exact HM | exact HE ]).
  clear HPR HRu HPt HRt Hkk Skk HE Hag HUs HRl' HPl HM.
  set (Ns := List.skipn (ind_nu Dq) (List.map nf_to_exp Rs)) in *.
  (** The blocks. *)
  assert (HUt' : forall j Mj, ind_member D j = Some Mj -> ⊢ (elim_mctx p D j Mj Us ++ Γ)%list)
    by (intros; eapply elim_mctx_wf; eassumption).
  assert (HBmot : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             (elim_mctx p D j Mj Us ++ Γ)%list ⊢ eb_motive b : abs_kind_sort r Typeω@i)
    by (intros j Mj b Hj Hb0;
        exact (HAt _ _ _ Hj Hb0 (HUt' _ _ Hj) _ (type_sort_universe _) (motive_kind_sort_typed _ r i Hmk (HUt' _ _ Hj)))).
  assert (HAs : motives_typed gc_deps gc_stack Γ p D Us (blocks_motives Bks) r i).
  { intros j Mj Hj Hjr; destruct (blocks_nth _ _ _ _ Hsuf HBl Hj Hjr) as [b Hb0].
    rewrite (blocks_motives_nth _ _ _ Hb0); exact (HBmot _ _ _ Hj Hb0). }
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUt) as Hσ.
  assert (HBts : blocks_typed gc_deps gc_stack Γ p D Us Bks r i).
  { constructor; [ exact HBl | exact HBnm | | exact HBmot | | exact HBn | | exact HBa | | exact Hmk ].
    - (** The scrutinee type, of [Typeω@i], has the member's type's normal
          form, which is of a universe too ([ctx_decomp_kind]): they are
          equal ([exp_eq_of_nbe_ty_same]). *)
      intros j Mj b Hj Hb0.
      pose proof (HUt' _ _ Hj) as HC; unfold elim_mctx in HC; cbn [List.app] in HC.
      pose proof (ctx_decomp_left HC) as HΨ; destruct (ctx_decomp_kind HC) as (SH & HSH & HH).
      destruct (sort_kind_abs_kind_sort_inv _ _ HSH) as [jH ->]; cbn [abs_kind_sort] in HH.
      pose proof (HZt _ _ _ Hj Hb0 HΨ _ (type_sort_universe _) (wf_typ _ _ _ _ HΨ)) as HZi.
      destruct (HZc _ _ _ Hj Hb0) as (W & W' & HZW & HHW & HWW).
      assert (HZH : (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list
                      ⊢ eb_scrutinee_type b ≈ ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj))
                      : Typeω@(max i jH))
        by (eapply exp_eq_of_nbe_ty_same; [ apply type_sort_universe | eapply lift_exp_max_left; exact HZi
                                           | eapply lift_exp_max_right; exact HH | exact HZW | exact HHW | exact HWW ]).
      unfold elim_mctx.
      assert (Hext : gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ tele_sub (im_nparams Mj) (sb_of_list Id Us)
                                                ≈ tele_sub (im_nparams Mj) (sb_of_list Id Us))
        by (apply ctx_ext_refl; [ apply all_assumptions_sub; exact (decl_closed_nparams_ass _ Hc _ _ Hj) | exact HΨ ]).
      eapply wf_ext_eq_ass_eq; [ exact Hext | eapply lift_exp_max_left; exact HZi | constructor | exact HZH
                               | eapply lift_exp_max_right; exact HH | eapply lift_exp_max_right; exact HH ].
    - intros j Mj Hj; apply ctx_ext_refl; [ exact (elim_mctx_ass _ _ _ _ _ Hc Hj) | exact (HUt' _ _ Hj) ].
    - intros j Mj c gs Hj Hcon; apply ctx_ext_refl; [ exact (elim_bctx_ass _ _ _ _ _ _ _ _ Hc Hj) |].
      eapply elim_bctx_wf; [ exact Hgw | exact HDs | exact Hl | exact Hj | exact HΓ | exact HUl | exact Hσ | exact HUt'
                           | exact HAs | exact Hmk | exact Hcon ].
    - intros j Mj b c gs n B Hj Hb0 Hcon Hin.
      pose proof (wf_branch_type_sub _ _ _ _ _ _ _ _ _ _ _ _ _ Hgw HDs Hl Hj (block_member_not_rview _ _ _ _ _ Hsuf HBl Hj Hb0)
                    HΓ HUl HUt HUt' HAs Hmk Hcon) as Hbs.
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ (HBmot _ _ _ Hj Hb0) Hbs) as HBty.
      rewrite abs_kind_sort_sub in HBty; cbn [exp_sub] in HBty.
      eapply HBt; [ exact Hj | exact Hb0 | exact Hcon | exact Hin
                  | eapply elim_bctx_wf; [ exact Hgw | exact HDs | exact Hl | exact Hj | exact HΓ | exact HUl | exact Hσ | exact HUt'
                                         | exact HAs | exact Hmk | exact Hcon ]
                  | exact (type_sort_kind_universe r i) | exact HBty ]. }
  exact (wf_elim_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl Hm Hb HBts HUl HUt HNl HNt HM').
Qed.

(** The eliminator is of the normal form of the motive's instance. *)
Lemma alg_elim_sound : forall Γ M pc k Rs p D m Mm Dq Mk bm Bks Us Ns r i T,
    ⊢ Γ -> Γ ⊢ M : apps (a_ind pc k) (List.map nf_to_exp Rs) ->
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm ->
    im_ref p m Mm = (pc, k) -> ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk ->
    List.length (List.map nf_to_exp Rs) = im_np Dq Mk ->
    List.nth_error Bks m = Some bm -> List.length Bks = ind_nblk D ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
       ⊢ Γ -> forall Srt, type_sort Srt -> Γ ⊢ T : Srt -> Γ ⊢ U : T) ->
    nfs_agree Γ (im_pre Mm Us) (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) ->
    Ns = List.skipn (ind_nu Dq) (List.map nf_to_exp Rs) ->
    blocks_binder_count_ok D Bks ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ⊢ (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list -> forall Srt, type_sort Srt ->
       (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢ Typeω@i : Srt ->
       (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢ eb_scrutinee_type b : Typeω@i) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) (eb_scrutinee_type b)
         (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ⊢ (elim_mctx p D j Mj Us ++ Γ)%list -> forall Srt, type_sort Srt ->
       (elim_mctx p D j Mj Us ++ Γ)%list ⊢ abs_kind_sort r Typeω@i : Srt ->
       (elim_mctx p D j Mj Us ++ Γ)%list ⊢ eb_motive b : abs_kind_sort r Typeω@i) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b)) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       ⊢ (elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ)%list -> forall Srt, type_sort Srt ->
       (elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ)%list ⊢ elim_branch_type p D j Mj c gs (eb_motive b) Us : Srt ->
       (elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ Γ)%list ⊢ B : elim_branch_type p D j Mj c gs (eb_motive b) Us) ->
    motive_kind r ->
    nbe_ty_f Γ (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)] T ->
    Γ ⊢ a_elim r p Us m Bks M : T /\ exists Srt, type_sort Srt /\ Γ ⊢ (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)] : Srt.
Proof.
  intros * HΓ HM Hl Hm Hr Hlq Hk HRl Hb HBl HUl HUs Hag HNs HBnm HZt HZc HAt HBn HBa HBt Hmk HT.
  pose proof (alg_elim_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΓ HM Hl Hm Hr Hlq Hk HRl Hb HBl HUl HUs Hag HNs
                HBnm HZt HZc HAt HBn HBa HBt Hmk) as Hel.
  (** an eliminator is no type of levels *)
  assert (exists Sj, type_sort Sj /\ Γ ⊢ (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)] : Sj) as (Sj & HSj & Hj).
  { pose proof (presup_exp_typ_cases Hel) as Hp; inversion Hp; [ eexists; split; eassumption |].
    match goal with H : level_type_former _ |- _ => inversion H end. }
  split; [ exact (exp_conv_sort HSj (soundness_ty_at_sort HSj Hj HT) Hel) | exists Sj; split; assumption ].
Qed.

(** What a checked body is: the body, read in an extension [Ψ] of [Γ0], is
    its expansion, which extends [Ψ], and the targets of its opens are
    well-formed modules where they stand. *)
Record alg_body_ok (Γ0 Ψ Γ : ctx) (Φ Φx : gmod) : Prop := mk_alg_body_ok
  { (** The body's expansion is [Φx] *)
    alg_body_ok_xp : body_xp gc_deps gc_stack Γ Φ Φx
    (** The expansion extends [Ψ] over [Γ0] *)
  ; alg_body_ok_ext : gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx Φx ++ Ψ ≈ body_ctx Φx ++ Ψ
    (** The targets of the opens are modules where they stand *)
  ; alg_body_ok_opens : forall k Ψo H, List.nth_error (body_opens Φ Φx) k = Some (Ψo, H) -> gc_deps ⍮ gc_stack ⍮ Ψo ++ Γ ⊢ᵐ H ≈ H
    (** The targets of the opens are no modules still being defined *)
  ; alg_body_ok_frame_free : forall k Ψo H, List.nth_error (body_opens Φ Φx) k = Some (Ψo, H) ->
      frame_free_target gc_deps gc_stack (Ψo ++ Γ) H
    (** The term parts of the expansion are of the sorts at their tags *)
  ; alg_body_ok_tags : exists L, body_tags Γ Φx L }.

Definition alg_body_sound (Γ : ctx) (Φ Φx : gmod) : Prop :=
  forall Γ0 Ψ, Γ = Ψ ++ Γ0 -> ⊢ Γ0 -> gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ Ψ ≈ Ψ -> alg_body_ok Γ0 Ψ Γ Φ Φx.

Lemma alg_body_nil_sound : forall Γ, alg_body_sound Γ gm_nil gm_nil.
Proof.
  intros Γ Γ0 Ψ -> HΓ0 HΨ; constructor; [ constructor | exact HΨ | | | exists 0; apply body_tags_nil ];
    intros [| k] * Hk; discriminate.
Qed.

(** A definition, of the sort at its tag. *)
Lemma alg_body_def_sound : forall Γ Φ Φx x b pv r A M i,
    alg_body_sound Γ Φ Φx ->
    (⊢ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢ A : abs_kind_sort r Typeω@i) ->
    (⊢ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢ M : A) ->
    alg_body_sound Γ (gm_ext Φ x (ge_def b pv r A (Some M))) (gm_ext Φx x (ge_def b pv r A (Some M))).
Proof.
  intros * IH HA HM Γ0 Ψ -> HΓ0 HΨ.
  destruct (IH _ _ eq_refl HΓ0 HΨ) as [Hbx HX Ho Hof [L HL]].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  specialize (HA HC); specialize (HM HC).
  constructor; [ constructor; exact Hbx | | exact Ho | exact Hof |].
  - rewrite List.app_assoc in HA, HM; cbn [body_ctx List.app].
    eapply wf_ext_eq_def_same; [ exact HX | exact HA | apply type_sort_kind_universe | exact HA | exact HM | exact HM ].
  - exists (max L i); apply body_tags_ext; [ exact (body_tags_mono _ _ _ _ HL (Nat.le_max_l L i)) |].
    intros A' M' HE; cbn [entry_tm entry_kind] in HE |- *; injection HE as <- <-.
    destruct r; cbn [abs_kind_sort] in HA |- *; [ eapply lift_exp_ge; [| exact HA ]; lia | exact HA | exact HA ].
Qed.

Lemma alg_body_mod_sound : forall Γ Φ Φx x pm U,
    alg_body_sound Γ Φ Φx ->
    (⊢ body_ctx Φx ++ Γ -> gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Γ ⊢ᵘ U ≈ U) ->
    alg_body_sound Γ (gm_ext Φ x (ge_mod pm U)) (gm_ext Φx x (ge_mod pm U)).
Proof.
  intros * IH HU Γ0 Ψ -> HΓ0 HΨ.
  destruct (IH _ _ eq_refl HΓ0 HΨ) as [Hbx HX Ho Hof [L HL]].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  specialize (HU HC); rewrite List.app_assoc in HU.
  constructor; [ constructor; exact Hbx | | exact Ho | exact Hof |].
  - cbn [body_ctx List.app]; apply wf_ext_eq_mod; [ exact HX | exact HU | exact HU ].
  - exists L; apply body_tags_ext; [ exact HL | intros * [=] ].
Qed.

(** A definition with a module part: as a definition and as a submodule. *)
Lemma alg_body_dm_sound : forall Γ Φ Φx x pv A M U i,
    alg_body_sound Γ Φ Φx ->
    (⊢ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢ A : Typeω@i) ->
    (⊢ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢ M : A) ->
    (⊢ body_ctx Φx ++ Γ -> gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Γ ⊢ᵘ U ≈ U) ->
    alg_body_sound Γ (gm_ext Φ x (ge_def_mod pv A M U)) (gm_ext Φx x (ge_def_mod pv A M U)).
Proof.
  intros * IH HA HM HU Γ0 Ψ -> HΓ0 HΨ.
  destruct (IH _ _ eq_refl HΓ0 HΨ) as [Hbx HX Ho Hof [L HL]].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  specialize (HA HC); specialize (HM HC); specialize (HU HC).
  constructor; [ constructor; exact Hbx | | exact Ho | exact Hof |].
  - rewrite List.app_assoc in HA, HM, HU; cbn [body_ctx List.app].
    eapply wf_ext_eq_dm; [ exact HX | exact HA | apply wf_exp_eq_refl; exact HA | exact HM | apply wf_exp_eq_refl; exact HM
                         | exact HA | exact HM | exact HU | exact HU ].
  - exists (max L i); apply body_tags_ext; [ exact (body_tags_mono _ _ _ _ HL (Nat.le_max_l L i)) |].
    intros A' M' HE; cbn [entry_tm entry_kind abs_kind_sort] in HE |- *; injection HE as <- <-.
    eapply lift_exp_ge; [| exact HA ]; lia.
Qed.

Lemma alg_body_open_sound : forall Γ Φ Φx H R Rm its gs Φg,
    alg_body_sound Γ Φ Φx ->
    (⊢ body_ctx Φx ++ Γ -> gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Γ ⊢ᵐ H ≈ H) ->
    mdenote gc_deps gc_stack (body_ctx Φx ++ Γ) H R ->
    mdesc_mod R = Some Rm ->
    frame_free_target gc_deps gc_stack (body_ctx Φx ++ Γ) H ->
    items_gen gc_deps gc_stack (body_ctx Φx ++ Γ) H its gs ->
    items_ok its ->
    Φg = gens_body gs ->
    alg_body_sound Γ (gm_open Φ H its Φg) (gens_append Φx 0 gs).
Proof.
  intros * IH HH HR HRm HRf Hg Hok -> Γ0 Ψ -> HΓ0 HΨ.
  destruct (IH _ _ eq_refl HΓ0 HΨ) as [Hbx HX Ho Hof [L HL]].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  specialize (HH HC).
  pose proof (gens_ext_wf _ _ _ _ _ _ Hg HH HRf HX) as HXg.
  constructor; [ econstructor; [ eassumption .. | reflexivity ] | exact HXg | | |].
  - cbn [body_opens]; rewrite <- (items_gen_length _ _ _ _ _ _ Hg), gm_dropn_gens_append.
    intros [| k] * Hk; cbn in Hk; [ injection Hk as <- <-; exact HH | exact (Ho _ _ _ Hk) ].
  - cbn [body_opens]; rewrite <- (items_gen_length _ _ _ _ _ _ Hg), gm_dropn_gens_append.
    intros [| k] * Hk; cbn in Hk; [ injection Hk as <- <-; exact HRf | exact (Hof _ _ _ Hk) ].
  - pose proof (ext_eq_ctx_left _ _ _ _ _ HXg) as HCg; rewrite <- List.app_assoc in HCg.
    exact (body_tags_gens _ _ _ _ Hg _ _ eq_refl HH Φx nil L eq_refl HCg HL).
Qed.

(** The parameters [Δ] over [Γ], each, in the context of those outside
    it, a type of the universe at [l] or a type of levels, as its kind
    says: what the algorithmic parameters are ([alg_params_ass],
    [alg_params_level]). *)
Definition params_kinded (Γ Δ : ctx) (l : nat) : Prop :=
  forall Δ1 κ T Δ2, Δ = (Δ1 ++ ce_ass κ T :: Δ2)%list ->
    (κ = ak_relevant /\ (Δ2 ++ Γ)%list ⊢ T : Typeω@l) \/ (κ = ak_level /\ (Δ2 ++ Γ)%list ⊢ T : LevelSort).

Lemma params_kinded_nil : forall Γ l, params_kinded Γ nil l.
Proof. intros * Δ1 κ T Δ2 E; destruct Δ1; discriminate. Qed.

(** One more parameter, at a level the others are lifted to. *)
Lemma params_kinded_snoc : forall Γ Δ κ T l j,
    params_kinded Γ Δ l ->
    (κ = ak_relevant /\ (Δ ++ Γ)%list ⊢ T : Typeω@j) \/ (κ = ak_level /\ (Δ ++ Γ)%list ⊢ T : LevelSort) ->
    params_kinded Γ (ce_ass κ T :: Δ) (max j l).
Proof.
  intros * Hl HT Δ1 κ' T' Δ2 E.
  destruct Δ1 as [| e Δ1]; cbn in E.
  - injection E as -> -> ->.
    destruct HT as [[-> HT] | [-> HT]]; [ left; split; [ reflexivity | eapply lift_exp_ge; [| exact HT ]; lia ] | right; split; [ reflexivity | exact HT ] ].
  - injection E as <- E.
    destruct (Hl _ _ _ _ E) as [[-> HT'] | [-> HT']]; [ left; split; [ reflexivity | eapply lift_exp_ge; [| exact HT' ]; lia ] | right; split; [ reflexivity | exact HT' ] ].
Qed.

(** The sort of the parameter at position [k] from the outermost: of the
    universe at [l], or [LevelSort] for a parameter of levels. *)
Definition param_sort_at (Δ : ctx) (l : nat) (k : nat) : exp :=
  match List.nth_error (List.rev Δ) k with Some (ce_ass ak_level _) => LevelSort | _ => Typeω@l end.

Lemma param_sort_at_parameter_sort : forall Δ l k, parameter_sort l (param_sort_at Δ l k).
Proof.
  intros; unfold param_sort_at.
  repeat match goal with |- context [ match ?x with _ => _ end ] => destruct x end; constructor.
Qed.

Lemma params_kinded_sorts : forall Γ Δ l, params_kinded Γ Δ l ->
    forall Δ1 κ T Δ2, Δ = (Δ1 ++ ce_ass κ T :: Δ2)%list -> (Δ2 ++ Γ)%list ⊢ T : param_sort_at Δ l (List.length Δ2).
Proof.
  intros * Hl * E.
  assert (Hn : List.nth_error (List.rev Δ) (List.length Δ2) = Some (ce_ass κ T)).
  { rewrite E, List.rev_app_distr; cbn [List.rev]; rewrite <- List.app_assoc; cbn [List.app].
    rewrite List.nth_error_app2 by (rewrite List.length_rev; lia).
    rewrite List.length_rev, Nat.sub_diag; reflexivity. }
  unfold param_sort_at; rewrite Hn.
  destruct (Hl _ _ _ _ E) as [[-> HT] | [-> HT]]; exact HT.
Qed.

(** A body: its parameters, of their kinds at a level, its expansion, the
    targets of its opens, and its definitions at the sorts of their tags,
    filled in ([wf_gm_fill]), so it is a unit ([unit_full_body]). *)
Lemma alg_unit_body_sound : forall Γ Δ Φ Φx,
    (⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ /\ exists l, params_kinded Γ Δ l) ->
    all_assumptions Δ -> alg_body_sound (Δ ++ Γ) Φ Φx ->
    body_shape Φ Φ -> body_shape Φx Φx -> List.NoDup (gm_names Φ) ->
    levels_abstractable gc_deps gc_stack Γ Δ (me_lit (gu_open nil Φ)) ->
    ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ Φ.
Proof.
  intros * HΔ Ht HB Hs Hsx Hn Habs HΓ.
  destruct (HΔ HΓ) as [HΔe [l Hl]].
  (** The flag, read off the abstractability: all parameters of levels,
      or what the body denotes has no member of a type of levels *)
  assert (exists lv Rt, levels_flag gc_deps gc_stack Γ Δ (me_lit (gu_open nil Φ)) lv Rt) as (lv & Rt & Hflag).
  { destruct Habs as [Hsorted | (R & HR & Hnl)].
    - exists true, (mdesc_term ak_relevant a_prop None); constructor; [ intros _; exact Hsorted | discriminate | discriminate ].
    - exists false, R; constructor; [ discriminate | intros _; exact HR | intros _; exact Hnl ]. }
  destruct (HB _ _ eq_refl HΓ HΔe) as [Hbx HX Ho Hof [L HL]].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  (** The sort of each name: its entry's tag, at [L]. *)
  set (es := fun y => abs_kind_sort match gm_prefix_upto Φx y with
                                      | Some (gm_ext _ _ E) => entry_kind E
                                      | _ => ak_relevant
                                      end Typeω@L).
  apply unit_eq_of_full;
    eapply (unit_full_body _ _ _ _ _ _ Hbx HC Ho Ht Hs Hsx Hn l (param_sort_at Δ l) (param_sort_at_parameter_sort Δ l)
              (params_kinded_sorts _ _ _ Hl) es); [| | | exact Hflag | exact Hof ].
  - intros y; apply type_sort_kind_universe.
  - intros * Hp HE; unfold es; cbv beta; rewrite Hp; apply sort_kind_abs_kind_sort.
  - intros * Hp HE Hf; unfold es; cbv beta; rewrite Hp.
    pose proof (HL _ _ _ _ _ Hp HE) as HA.
    pose proof (wf_gm_fill _ _ _ _ _ (presup_exp_ctx HA) Hf) as Hσ.
    pose proof (sub_preserves_sort _ _ _ _ _ _ _ HA (type_sort_kind_universe _ _) Hσ) as HAσ.
    exact HAσ.
Qed.

(** A tuple whose annotation normalises to a record type at [Rs], its
    fields checked at their types at [Rs]: of that normal form. *)
Lemma alg_tuple_sound : forall Γ T (fs : list (String.string * exp)) p Rs R i,
    ⊢ Γ -> Γ ⊢ T : Typeω@i -> nbe_ty_f Γ T (nf_record p Rs) -> record_lookup gc_deps gc_stack p = Some R ->
    List.map fst fs = List.map fst (record_fields R) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       ⊢ Γ -> forall Srt, type_sort Srt -> Γ ⊢ U[sb_of_list Id (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs))] : Srt ->
       Γ ⊢ M : U[sb_of_list Id (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs))]) ->
    Γ ⊢ a_tuple T fs : nf_record p Rs.
Proof.
  intros * HΓ HT Hn Hl Hfs HMs.
  assert (HTR : Γ ⊢ T ≈ nf_record p Rs : Typeω@i) by (eapply soundness_ty'; eassumption).
  cbn [nf_to_exp] in HTR |- *.
  assert (HRa : Γ ⊢ apps (a_record p) (List.map nf_to_exp Rs) : Typeω@i) by (gen_presups; assumption).
  pose proof (wf_record_apps_len _ _ _ _ _ Hl HRa) as HRl.
  pose proof (wf_record_apps_inv _ _ _ _ _ Hl HRa HRl) as HRt.
  destruct (record_former_typed _ _ _ HΓ Hl) as [j [Hrt _]].
  pose proof (tuple_fields_typed_seq _ _ _ _ _ Hrt Hl HRl Hfs HRt
                ltac:(intros * Hk Hfk (S' & HS' & Hi'); exact (HMs _ _ _ _ Hk Hfk HΓ _ HS' Hi'))) as HFt.
  eapply wf_conv'; [ eapply wf_tuple; [ exact HT | exact HTR | exact Hrt | exact Hl | exact HRl | exact HRt | exact Hfs | exact HFt ]
                   | exact HTR ].
Qed.

(** A projection of an element of a record type at [Rs]: of its field's
    type at [Rs] and the projections before it, which is a type. *)
Lemma alg_proj_typed : forall Γ M p Rs R f k U,
    ⊢ Γ -> Γ ⊢ M : nf_record p Rs -> record_lookup gc_deps gc_stack p = Some R ->
    List.nth_error (record_fields R) k = Some (f, U) ->
    exists m, Γ ⊢ U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)] : abs_kind_sort (record_field_kind R k) Typeω@m /\
      Γ ⊢ a_proj f M : U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)].
Proof.
  intros * HΓ HM Hl Hfk; cbn [nf_to_exp] in HM.
  (** A record type is of a large universe, never a proposition. *)
  assert (exists i, Γ ⊢ apps (a_record p) (List.map nf_to_exp Rs) : Typeω@i) as [i HRa]
    by (destruct (presup_exp_typ_sorted HM (apps_exp_not_level_sort (List.map nf_to_exp Rs) (a_record p) ltac:(discriminate)))
          as (SR & HSR & HRS); destruct HSR as [iR | |];
        [ exists iR; exact HRS | exfalso; exact (typ_prop_record_absurd HRS) | exfalso; exact (record_type_not_level HRS) ]).
  pose proof (wf_record_apps_len _ _ _ _ _ Hl HRa) as HRl.
  pose proof (wf_record_apps_inv _ _ _ _ _ Hl HRa HRl) as HRt.
  destruct (record_former_typed _ _ _ HΓ Hl) as [j [Hrt _]].
  destruct (record_sort_large _ _ _ _ _ _ Hrt Hl HRl HRt) as [m Hm].
  destruct (record_proj_cong_at _ _ _ M M p R _ m k f U (wf_exp_eq_refl HM) Hrt Hl HRl HRt Hm Hfk) as [HUU Hpp].
  exists m; split; gen_presups; assumption.
Qed.

(** So it is of the normal form of that type. *)
Lemma alg_proj_sound : forall Γ M p Rs R f k U W,
    ⊢ Γ -> Γ ⊢ M : nf_record p Rs -> record_lookup gc_deps gc_stack p = Some R ->
    List.nth_error (record_fields R) k = Some (f, U) ->
    nbe_ty_f Γ U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)] W ->
    Γ ⊢ a_proj f M : W.
Proof.
  intros * HΓ HM Hl Hfk Hn.
  destruct (alg_proj_typed _ _ _ _ _ _ _ _ HΓ HM Hl Hfk) as (m & HUt & Hp).
  pose proof (type_sort_kind_universe (record_field_kind R k) m) as HS.
  exact (exp_conv_sort HS (soundness_ty_at_sort HS HUt Hn) Hp).
Qed.

(** A type whose type [UB] normalises to a universe normal form [v] is of
    [v], whose level's atoms are of the sorts they carry: [UB] is of a
    large universe, as a universe normal form is no proposition's normal
    form ([nbe_ty_prop_not_univ_pi]). *)
Lemma typed_at_univ_nf : forall Δ B (UB UB' : nf) v,
    Δ ⊢ B : UB -> nbe_ty_f Δ UB UB' -> is_univ_nf UB' v ->
    Δ ⊢ B : universe_nf_tm v /\ universe_nf_well_scoped Δ v.
Proof.
  intros * HBU HnB Hv.
  assert (exists k, Δ ⊢ (UB : exp) : Typeω@k) as [kB HUB].
  { destruct (presup_exp_typ_cases HBU) as [? SB HSB HUB0 | ? Hlf].
    - destruct HSB as [kB | |]; [ exists kB; exact HUB0 | |].
      + exfalso; pose proof (nbe_ty_prop_not_univ_pi _ _ _ HUB0 HnB) as Hnu.
        rewrite (is_univ_nf_eq _ _ Hv) in Hnu; destruct v as [[] |]; cbn in Hnu; exact Hnu.
      + (** a type of levels normalises to a type of levels, of [LevelSort]
            ([level_sort_typed_former]), and no universe is one *)
        exfalso; pose proof (soundness_ty_at_sort type_sort_level HUB0 HnB) as HE.
        rewrite (is_univ_nf_eq _ _ Hv), nf_to_exp_univ_nf in HE.
        pose proof (level_sort_typed_former (presup_exp_eq_right HE)) as Hf.
        destruct v; inversion Hf.
    - (** [LevelSort] normalises to itself, no universe *)
      exfalso; destruct HnB as [ρ a Hρ Ha HW]; inversion Ha; subst; inversion HW; subst; inversion Hv. }
  assert (HUBe : Δ ⊢ (UB : exp) ≈ UB' : Typeω@kB) by (eapply soundness_ty'; eassumption).
  assert (Hpf : nf_proof_free UB')
    by (rewrite (is_univ_nf_eq _ _ Hv) in HnB |- *; destruct v as [[c xs] | j]; [ exact (nbe_ty_univ_proof_free HUB HnB) | exact I ]).
  pose proof (nbe_ty_self HUB HnB Hpf) as HnB'.
  rewrite (is_univ_nf_eq _ _ Hv) in HUBe, HnB'.
  assert (HB' : Δ ⊢ B : universe_nf_tm v) by (rewrite <- nf_to_exp_univ_nf; eapply wf_conv'; [ exact HBU | exact HUBe ]).
  split; [ exact HB' |].
  eapply universe_nf_well_scoped_of_nbe; [ rewrite <- nf_to_exp_univ_nf; gen_presups; eassumption
                                         | rewrite <- nf_to_exp_univ_nf; exact HnB' ].
Qed.

(** A type whose type [UB] normalises to [Prop] or to [LevelSort]
    ([is_sort_nf] at a kind other than the relevant one) is of that sort.
    A type [UB] of a sort is equal to its normal form, and [LevelSort],
    of no sort, is not one; [UB] itself [LevelSort] normalises to
    [LevelSortⁿ]. *)
Lemma typed_at_sort_nf_irrelevant : forall Δ B (UB UB' : nf) κ v,
    Δ ⊢ B : UB -> nbe_ty_f Δ UB UB' -> is_sort_nf UB' κ v -> κ <> ak_relevant ->
    Δ ⊢ B : abs_kind_sort κ Typeω@0.
Proof.
  intros * HBU HnB Hs Hκ.
  destruct Hs as [W u Hu | |]; [ contradiction (Hκ eq_refl) | |]; cbn [abs_kind_sort].
  - destruct (presup_exp_typ_cases HBU) as [? SB HSB HUB0 | ? Hlf].
    + pose proof (soundness_ty_at_sort HSB HUB0 HnB) as HE; cbn [nf_to_exp] in HE.
      exact (exp_conv_sort HSB HE HBU).
    + exfalso; destruct HnB as [ρ a Hρ Ha HW]; inversion Ha; subst; inversion HW.
  - destruct (presup_exp_typ_cases HBU) as [? SB HSB HUB0 | ? Hlf].
    + exfalso; pose proof (soundness_ty_at_sort HSB HUB0 HnB) as HE; cbn [nf_to_exp] in HE.
      exact (level_sort_untyped (presup_exp_eq_right HE)).
    + exact HBU.
Qed.

(** The parts of a typed [Π] at the kinds [κd] and [κc]: the domain of a
    sort, the codomain of the sort at [κc] at a large universe
    ([wf_pi_parts]). *)
Lemma wf_pi_parts_large : forall Γ κd κc A B C,
    Γ ⊢ a_pi κd κc A B : C ->
    exists Sd k, type_sort Sd /\ Γ ⊢ A : Sd /\ Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@k.
Proof.
  intros * H.
  destruct (wf_pi_parts H) as (_ & (Sd & HSd & HA) & (k & HB)).
  exists Sd, k; repeat split; [ exact (sort_kind_type_sort _ _ HSd) | exact HA | exact HB ].
Qed.

(** A type of a sort, of the kind [r] its value says, is of the sort [r]
    names ([typed_at_sort_of_initial_kind]). *)
Lemma typed_at_relevance_of_nbe : forall {Γ A S r},
    type_sort S -> Γ ⊢ A : S -> nbe_ty_kind Γ A r ->
    exists k : nat, Γ ⊢ A : abs_kind_sort r Typeω@k.
Proof.
  intros * HS HA (ρ & a & Hρ & Ha & <-).
  exact (typed_at_sort_of_initial_kind HS HA Hρ Ha).
Qed.

(** Conversely, a type of the sort [r] names is of the kind [r]: its
    value at the initial environment is of the sort's kind
    ([typed_at_sort_of_initial_kind]), and no type is of two sorts of
    different kinds ([subtyp_same_kind]). *)
Lemma nbe_ty_kind_of_typed : forall {Γ A r} {i : nat},
    Γ ⊢ A : abs_kind_sort r Typeω@i -> nbe_ty_kind Γ A r.
Proof.
  intros * HA.
  pose proof (type_sort_kind_universe r i) as HS.
  destruct (nbe_ty_exists_sort HS HA) as [W [ρ a Hρ Ha _]].
  exists ρ, a; split; [ exact Hρ | split; [ exact Ha |] ].
  destruct (typed_at_sort_of_initial_kind HS HA Hρ Ha) as [k Hk].
  assert (Hs : Γ ⊢ A ⊆ A) by (eapply wf_subtyp_refl; [ exact HA | exact HS | apply wf_exp_eq_refl; exact HA ]).
  exact (eq_sym (subtyp_same_kind _ _ _ r (domain_kind a) i k Hs HA Hk)).
Qed.

(** A λ whose body's type [B] is no [LevelSort] and of the kind [κc] is of
    the [Π] of its annotation's normal form: [B] is of a sort
    ([presup_exp_typ_sorted]), so of the sort of [κc]
    ([typed_at_relevance_of_nbe]); both parts are moved to one universe, at
    which the [Π] is congruent in its domain. *)
Lemma fn_typed_at_nf : forall {Γ κd κc A M} {B C : nf} {l},
    Γ ⊢ A : abs_kind_sort κd Typeω@l -> Γ ▹{κd} A ⊢ M : B -> nf_to_exp B <> LevelSort ->
    nbe_ty_kind (Γ ▹{κd} A) B κc -> pi_kinds κd κc -> nbe_ty_f Γ A C ->
    Γ ⊢ λ A M : nf_pi κd κc C B.
Proof.
  intros * HA HM HnL Hr Hk Hn.
  assert (⊢ Γ) by (gen_presups; assumption).
  destruct (presup_exp_typ_sorted HM HnL) as [SB [HSB HB0]].
  destruct (typed_at_relevance_of_nbe HSB HB0 Hr) as [kB HBs].
  pose proof (abs_kind_sort_lift _ _ _ _ _ HA (Nat.le_max_l l kB)) as HAj.
  pose proof (abs_kind_sort_lift _ _ _ _ _ HBs (Nat.le_max_r l kB)) as HBj.
  pose proof (soundness_ty_at_sort (type_sort_kind_universe κd (Nat.max l kB)) HAj Hn) as HAC.
  assert (Hfn : Γ ⊢ λ A M : a_pi κd κc A B)
    by (eapply wf_fn; [ exact HA | apply sort_kind_abs_kind_sort | exact HBs | exact Hk | exact HM ]).
  assert (Heq : Γ ⊢ a_pi κd κc A B ≈ a_pi κd κc C B : abs_kind_sort κc Typeω@(Nat.max l kB)).
  { eapply wf_exp_eq_pi_cong; [ apply wf_is_univ_large; assumption | exact HAj | exact HAC | | exact Hk ].
    rewrite abs_kind_sort_wk; exact (wf_exp_eq_refl HBj). }
  cbn [nf_to_exp]; exact (exp_conv_sort (type_sort_kind_universe κc _) Heq Hfn).
Qed.

(** A body's type [C] that is no [LevelSort] and of the kind [κC] is of
    the sort of [κC] at a large universe ([presup_exp_typ_sorted],
    [typed_at_relevance_of_nbe]). *)
Lemma typed_at_kind_of_nbe : forall {Δ B} {C : nf} {κC},
    Δ ⊢ B : C -> nf_to_exp C <> LevelSort -> nbe_ty_kind Δ C κC ->
    exists k, Δ ⊢ C : abs_kind_sort κC Typeω@k.
Proof.
  intros * HB HnL Hr.
  destruct (presup_exp_typ_sorted HB HnL) as [SC [HSC HC]].
  exact (typed_at_relevance_of_nbe HSC HC Hr).
Qed.

(** A [let] of a definition of the kind [r], whose body's type [C] is no
    [LevelSort] and of a kind [κC] the definition may build (a type of
    levels only under a level), is of the normal form of [C]
    instantiated ([wf_let]). *)
Lemma let_typed_at_nf : forall {Γ A M B r l} {C D : nf} {κC},
    Γ ⊢ A : abs_kind_sort r Typeω@l -> Γ ⊢ M : A -> Γ ▸ A ≔ M ⊢ B : C ->
    nf_to_exp C <> LevelSort -> nbe_ty_kind (Γ ▸ A ≔ M) C κC -> (κC = ak_level -> r = ak_level) ->
    nbe_ty_f Γ (nf_to_exp C)[Id,,M] D ->
    Γ ⊢ ℓ A ≔ M in B : D.
Proof.
  intros * HA HM HB HnL Hr Hlc Hn.
  pose proof (type_sort_kind_universe r l) as HSA.
  destruct (typed_at_kind_of_nbe HB HnL Hr) as [k HC].
  pose proof (type_sort_kind_universe κC k) as HSC.
  assert (Hcl : level_closed_sort (abs_kind_sort r Typeω@l) (abs_kind_sort κC Typeω@k))
    by (destruct κC; cbn [abs_kind_sort]; [ constructor | constructor | rewrite (Hlc eq_refl); constructor ]).
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HC HSC (wf_sub_single_def _ _ _ _ _ _ HA HSA HM)) as HCs.
  exact (exp_conv_sort HSC (soundness_ty_at_sort HSC HCs Hn) (wf_let _ _ _ _ _ _ _ _ _ HA HSA HM HC Hcl HB)).
Qed.

(** A module [let] whose body's type [C] is no [LevelSort] and no type of
    levels is of the normal form of [C] instantiated ([wf_let_mod]). *)
Lemma let_mod_typed_at_nf : forall {Γ U B} {C D : nf} {κC},
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> Γ ▹ₘ U ⊢ B : C ->
    nf_to_exp C <> LevelSort -> nbe_ty_kind (Γ ▹ₘ U) C κC -> κC <> ak_level ->
    nbe_ty_f Γ (nf_to_exp C)[Id ,,ₘ me_lit U] D ->
    Γ ⊢ ℓₘ U in B : D.
Proof.
  intros * HU HB HnL Hr Hlc Hn.
  destruct (typed_at_kind_of_nbe HB HnL Hr) as [k HC].
  pose proof (type_sort_kind_universe κC k) as HSC.
  assert (Hms : module_body_sort (abs_kind_sort κC Typeω@k))
    by (destruct κC; cbn [abs_kind_sort]; [ constructor | constructor | contradiction (Hlc eq_refl) ]).
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HC HSC (wf_sub_single_mod _ _ _ _ HU)) as HCs.
  exact (exp_conv_sort HSC (soundness_ty_at_sort HSC HCs Hn) (wf_let_mod _ _ _ _ _ _ _ HU HC HSC Hms HB)).
Qed.

(** The type of a proof of a conjunction is a proposition: it is of a
    sort, being no [LevelSort] ([presup_exp_typ_sorted]), and a
    conjunction of a sort is one of [Prop] ([prop_former_typed]). *)
Lemma and_typed_of_proof : forall {Γ M P Q},
    Γ ⊢ M : Σₚ P Q -> Γ ⊢ Σₚ P Q : Propₘ.
Proof.
  intros * HM.
  destruct (presup_exp_typ_sorted HM ltac:(discriminate)) as [S [_ HPQ]].
  exact (prop_former_typed HPQ ltac:(eauto 6)).
Qed.

Lemma alg_type_sound :
  (forall {Γ A M}, Γ ⊢a M ⟸ A -> ⊢ Γ -> forall Srt, type_sort Srt -> Γ ⊢ A : Srt -> Γ ⊢ M : A) /\
    (forall {Γ A M}, Γ ⊢a M ⟹ A -> ⊢ Γ -> Γ ⊢ M : A) /\
    (forall {Γ Ψ}, Γ ⊢aˣ Ψ -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ) /\
    (forall {Γ Δ}, Γ ⊢aᵖ Δ -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ /\ exists l, params_kinded Γ Δ l) /\
    (forall {Γ U}, Γ ⊢aᵘ U -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U) /\
    (forall {Γ Φ Φx}, Γ ⊢aᵇ Φ ⇝ Φx -> alg_body_sound Γ Φ Φx) /\
    (forall {Γ H}, Γ ⊢aᵐ H -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H).
Proof.
  apply alg_type_mut_ind; intros.
  (** ** Checking: by the inferred type, below the checked one *)
  - match goal with
    | IH : ⊢ ?G -> ?G ⊢ ?M : ?A, HG : ⊢ ?G, Hs : ?G ⊢a ?A ⊆ ?B, HS : type_sort ?S, HB : ?G ⊢ ?B : ?S |- _ =>
        pose proof (IH HG) as HM; destruct (presup_exp_typ_cases HM) as [? SA HSA HA | ? Hlf];
        [ eapply wf_exp_subtyp; [ exact HM | exact HB | exact HS | exact (alg_subtyping_sound_sort _ _ _ _ _ HSA HS Hs HA HB) ]
        | (** inferred [LevelSort], below only itself, of no sort *)
          exfalso; destruct Hs as [A' B' HA' HB' Hsub];
          inversion HA' as [ρ a1 Hρ Ha HW]; subst; inversion Ha; subst; inversion HW; subst;
          inversion Hsub; subst;
          match goal with HE : nf_eq_upto_proofs LevelSortⁿ ?B |- _ => destruct B; cbn in HE; try discriminate end;
          pose proof (soundness_ty_at_sort HS HB HB') as HE'; cbn [nf_to_exp] in HE';
          eapply level_sort_untyped; eapply presup_exp_eq_right; exact HE' ]
    end.
  (** ** Inference *)
  (** The universes, the levels and [Prop] *)
  - apply wf_typ; assumption.
  - match goal with
    | IH : ⊢ ?G -> ?G ⊢ ?M : _, Hn : nbe_ty_f _ (a_univ (succl ?M)) ?W, HG : ⊢ ?G |- _ =>
        pose proof (IH HG) as HMl; cbn [nf_to_exp] in HMl;
        assert (HSU : G ⊢ Type⟨succl M⟩ : Typeω@0) by (eapply wf_univ_large_tm; [ assumption | eapply wf_succl; exact HMl ]);
        eapply wf_conv'; [ eapply wf_univ; exact HMl | eapply soundness_ty'; [ exact HSU | exact Hn ] ]
    end.
  - apply wf_level; assumption.
  - apply wf_llit; [ lia | assumption ].
  - match goal with IH : ⊢ ?G -> ?G ⊢ ?M : _, HG : ⊢ ?G |- _ => pose proof (IH HG) as HMl end.
    cbn [nf_to_exp] in *; apply wf_succl; assumption.
  - match goal with
    | HM : ⊢ ?G -> ?G ⊢ ?M : _, HN : ⊢ ?G -> ?G ⊢ ?N : _, HG : ⊢ ?G |- ?G ⊢ maxl ?M ?N : _ =>
        pose proof (HM HG) as HMl; pose proof (HN HG) as HNl; cbn [nf_to_exp] in HMl, HNl |- *;
        match type of HMl with _ ⊢ _ : Level@?m => match type of HNl with _ ⊢ _ : Level@?n =>
          apply wf_maxl; [ apply (wf_exp_level_up (m := m)); [ lia | exact HMl ]
                         | apply (wf_exp_level_up (m := n)); [ lia | exact HNl ] ] end end
    end.
  - apply wf_prop; assumption.
  (** The propositions [⊤], [⊥], the proof [⋆] and the introduction of [⊤] *)
  - apply wf_True; assumption.
  - apply wf_tt; assumption.
  - apply wf_False; assumption.
  (** Ex falso: the target at its sort, the proof at [⊥] *)
  - match goal with
    | IHC : ⊢ ?G -> ?G ⊢ ?C : (nf_to_exp ?UC), Hs : is_sort_nf ?UC ?r ?u, Hr : ?r <> ak_level,
      IHM : ⊢ ?G -> forall Srt, _ -> ?G ⊢ ⊥ : Srt -> ?G ⊢ ?M : ⊥,
      Hn : nbe_ty_f ?G ?C ?W, HG : ⊢ ?G |- _ =>
        pose proof (sort_typed_of_is_sort_nf (IHC HG) Hs) as HCs;
        pose proof (type_sort_kind_universe r (universe_nf_large_index u)) as HS;
        pose proof (IHM HG _ type_sort_prop (wf_False _ _ _ HG)) as HM0;
        assert (HL : level_closed_sort Propₘ (abs_kind_sort r Typeω@(universe_nf_large_index u)))
          by (destruct r; [ constructor | constructor | congruence ]);
        exact (exp_conv_sort HS (soundness_ty_at_sort HS HCs Hn) (wf_absurd _ _ _ _ _ _ HCs HS HL HM0))
    end.
  (** A conjunction of propositions *)
  - match goal with
    | IHP : ⊢ ?G -> ?G ⊢ ?P : (nf_to_exp Propⁿ), IHQ : ⊢ ?G ▹{ak_propositional} ?P -> ?G ▹{ak_propositional} ?P ⊢ ?Q : (nf_to_exp Propⁿ), HG : ⊢ ?G |- _ =>
        pose proof (IHP HG) as HP; cbn [nf_to_exp] in HP;
        assert (HGP : ⊢ G ▹{ak_propositional} P) by (eapply wf_ctx_extend; [ exact HP | constructor ]);
        pose proof (IHQ HGP) as HQ; cbn [nf_to_exp] in HQ;
        apply wf_and; assumption
    end.
  (** A proof of a conjunction: at its annotation, normalised *)
  - match goal with
    | IHP : ⊢ ?G -> ?G ⊢ ?P : (nf_to_exp Propⁿ),
      IHQ : ⊢ ?G ▹{ak_propositional} ?P -> ?G ▹{ak_propositional} ?P ⊢ ?Q : (nf_to_exp Propⁿ),
      IHM : ⊢ ?G -> forall Srt, _ -> ?G ⊢ ?P : Srt -> ?G ⊢ ?M : _,
      IHN : ⊢ ?G -> forall Srt, _ -> ?G ⊢ ?Q[Id,,?M] : Srt -> ?G ⊢ ?N : _,
      Hn : nbe_ty_f ?G (Σₚ ?P ?Q) ?W, HG : ⊢ ?G |- _ =>
        pose proof (IHP HG) as HP; cbn [nf_to_exp] in HP;
        assert (HGP : ⊢ G ▹{ak_propositional} P) by (eapply wf_ctx_extend; [ exact HP | constructor ]);
        pose proof (IHQ HGP) as HQ; cbn [nf_to_exp] in HQ;
        pose proof (IHM HG _ type_sort_prop HP) as HM;
        assert (HQM : G ⊢ Q[Id,,M] : Propₘ)
          by (exact (sub_preserves_sort _ _ _ _ _ _ _ HQ type_sort_prop (wf_sub_single _ _ _ _ _ _ _ HP ltac:(constructor) HM)));
        pose proof (IHN HG _ type_sort_prop HQM) as HN;
        assert (HT : G ⊢ Σₚ P Q : Propₘ) by (apply wf_and; assumption);
        exact (exp_conv_sort type_sort_prop (soundness_ty_at_sort type_sort_prop HT Hn) (wf_conj _ _ _ _ _ _ _ HP HQ HM HN))
    end.
  (** The components of a proof of a conjunction *)
  - match goal with
    | IH : ⊢ ?G -> ?G ⊢ ?M : (nf_to_exp (Σₚⁿ ?P ?Q)), HG : ⊢ ?G |- _ =>
        pose proof (IH HG) as HM; cbn [nf_to_exp] in HM;
        pose proof (and_typed_of_proof HM) as HPQ;
        destruct (wf_and_inversion _ _ _ _ _ _ HPQ) as [HP HQ _];
        eapply wf_left; eassumption
    end.
  - match goal with
    | IH : ⊢ ?G -> ?G ⊢ ?M : (nf_to_exp (Σₚⁿ ?P ?Q)), Hn : nbe_ty_f ?G (nf_to_exp ?Q)[Id,,a_left ?M] ?W, HG : ⊢ ?G |- _ =>
        pose proof (IH HG) as HM; cbn [nf_to_exp] in HM;
        pose proof (and_typed_of_proof HM) as HPQ;
        destruct (wf_and_inversion _ _ _ _ _ _ HPQ) as [HP HQ _];
        assert (HL : G ⊢ a_left M : nf_to_exp P) by (eapply wf_left; eassumption);
        assert (HQL : G ⊢ (nf_to_exp Q)[Id,,a_left M] : Propₘ)
          by (exact (sub_preserves_sort _ _ _ _ _ _ _ HQ type_sort_prop (wf_sub_single _ _ _ _ _ _ _ HP ltac:(constructor) HL)));
        exact (exp_conv_sort type_sort_prop (soundness_ty_at_sort type_sort_prop HQL Hn)
                 (wf_right _ _ _ _ _ _ HP HQ HM HQL))
    end.
  (** The type former, a constructor and the eliminator *)
  - match goal with Hl : ind_lookup _ _ _ = Some ?D, Hk : ind_member ?D _ = Some _, HΓ : ⊢ ?G |- _ =>
      destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc];
      destruct (ind_ty_typed _ _ _ _ _ _ HD Hc Hk HΓ) as [j Hj];
      eapply wf_conv'; [ eapply wf_ind; eassumption | eapply soundness_ty'; eassumption ] end.
  - match goal with Hl : ind_lookup _ _ _ = Some ?D, Hk : ind_member ?D _ = Some _, Hcon : ind_con _ _ = Some ?gs,
                    HΓ : ⊢ ?G |- _ =>
      destruct (con_ty_typed _ _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) (decls_of_ctx _ _ _ HΓ) Hl Hk Hcon HΓ) as [j Hj];
      eapply wf_conv'; [ eapply wf_con_closed; eassumption | eapply soundness_ty'; eassumption ] end.
  - match goal with
    | HM : ⊢ ?G -> ?G ⊢ ?M : _, HΓ : ⊢ ?G, Hl : ind_lookup _ _ ?p = Some ?D |- ?G ⊢ a_elim ?r ?p _ ?m _ ?M : _ =>
        eapply proj1; eapply (alg_elim_sound G M _ _ _ p D m); first [ exact HΓ | exact (HM HΓ) | eassumption ]
    end.
  (** A [Π]: the domain of either sort, counted in its universe, the
      codomain at the normal form of its universe, whose level's atoms are
      of the sorts they carry; at the normal form of the join *)
  - match goal with
    | IHA : ⊢ ?G -> ?G ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?κd ?u,
      IHB : ⊢ ?G ▹{?κd} ?A -> ?G ▹{?κd} ?A ⊢ ?B : (nf_to_exp ?UB),
      HnB : nbe_ty_f (?G ▹{?κd} ?A) (nf_to_exp ?UB) ?UB', Hv : is_sort_nf ?UB' ?κc ?v, Hk : pi_kinds ?κd ?κc,
      HnW : nbe_ty_f ?G (abs_kind_sort ?κc (universe_nf_pi_tm ?u ?v)) ?W, HG : ⊢ ?G |- _ =>
        pose proof (IHA HG) as HA0;
        pose proof (sort_typed_of_is_sort_nf HA0 Hs) as HAs;
        assert (HGA : ⊢ G ▹{κd} A) by (eapply wf_ctx_extend; [ exact HAs | apply sort_kind_abs_kind_sort ]);
        pose proof (IHB HGA) as HB0;
        destruct Hv as [UB0 v0 Hv | |]; cbn [abs_kind_sort] in HnW
    end.
    + (** Into a universe: at the normal form of the join *)
      match goal with
      | HB0 : ?G ▹{?κd} ?A ⊢ ?B : (nf_to_exp ?UB), HnB : nbe_ty_f _ (nf_to_exp ?UB) ?UB', Hv : is_univ_nf ?UB' ?v,
        HA0 : ?G ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?κd ?u |- _ =>
          destruct (typed_at_univ_nf _ _ _ _ _ HB0 HnB Hv) as [HB' Hvw];
          pose proof (pi_domain_ok_of_is_sort_nf HA0 Hs) as HAd;
          pose proof (wf_pi_universe_nf_pi HAd HB' Hvw) as HPi;
          destruct (wf_universe_nf_pi_tm HAd HB' Hvw) as [k Hk];
          eapply wf_exp_subtyp'; [ exact HPi | eapply wf_subtyp_refl'; eapply soundness_ty'; eassumption ]
      end.
    + (** A universal proposition: in [Prop], whatever the universe *)
      match goal with
      | HB0 : ?G ▹{?κd} ?A ⊢ ?B : (nf_to_exp ?UB), HnB : nbe_ty_f _ (nf_to_exp ?UB) Propⁿ,
        HAs : ?G ⊢ ?A : abs_kind_sort ?κd Typeω@?l, HnW : nbe_ty_f ?G Propₘ ?W, Hk : pi_kinds _ _, HG : ⊢ ?G |- _ =>
          pose proof (typed_at_sort_nf_irrelevant _ _ _ _ _ _ HB0 HnB is_sort_nf_prop ltac:(discriminate)) as HB;
          cbn [abs_kind_sort] in HB;
          destruct HnW as [ρ a1 Hρ Ha HWr]; inversion Ha; subst; inversion HWr; subst;
          change (Propⁿ : exp) with (abs_kind_sort ak_propositional Typeω@l);
          eapply wf_pi; [ apply wf_is_univ_large; exact HG | exact HAs | exact HB | exact Hk ]
      end.
    + (** A type of functions between levels: in [LevelSort] *)
      match goal with
      | HB0 : ?G ▹{?κd} ?A ⊢ ?B : (nf_to_exp ?UB), HnB : nbe_ty_f _ (nf_to_exp ?UB) LevelSortⁿ,
        HAs : ?G ⊢ ?A : abs_kind_sort ?κd Typeω@?l, HnW : nbe_ty_f ?G LevelSort ?W, Hk : pi_kinds _ _, HG : ⊢ ?G |- _ =>
          pose proof (typed_at_sort_nf_irrelevant _ _ _ _ _ _ HB0 HnB is_sort_nf_level ltac:(discriminate)) as HB;
          cbn [abs_kind_sort] in HB;
          destruct HnW as [ρ a1 Hρ Ha HWr]; inversion Ha; subst; inversion HWr; subst;
          change (LevelSortⁿ : exp) with (abs_kind_sort ak_level Typeω@l);
          eapply wf_pi; [ apply wf_is_univ_large; exact HG | exact HAs | exact HB | exact Hk ]
      end.
  (** [λ]: the annotation of either sort, the body at its type of the sort
      [r]; the function is of the [Π] of the annotation's normal form *)
  - match goal with
    | IHA : ⊢ ?G -> ?G ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?κd ?u,
      IHM : ⊢ ?G ▹{?κd} ?A -> ?G ▹{?κd} ?A ⊢ ?M : (nf_to_exp ?B), HnL : nf_to_exp ?B <> LevelSort,
      Hr : nbe_ty_kind (?G ▹{?κd} ?A) (nf_to_exp ?B) ?κc, Hk : pi_kinds ?κd ?κc, Hn : nbe_ty_f ?G ?A ?C, HG : ⊢ ?G |- _ =>
        pose proof (sort_typed_of_is_sort_nf (IHA HG) Hs) as HAs;
        assert (HGA : ⊢ G ▹{κd} A) by (eapply wf_ctx_extend; [ exact HAs | apply sort_kind_abs_kind_sort ]);
        exact (fn_typed_at_nf HAs (IHM HGA) HnL Hr Hk Hn)
    end.
  (** An application: at the codomain instantiated, normalised *)
  - match goal with
    | IHM : ⊢ ?G -> ?G ⊢ ?M : (nf_to_exp (nf_pi ?κd ?κc ?A ?B)), IHN : ⊢ ?G -> forall Srt, _ -> ?G ⊢ (nf_to_exp ?A) : Srt -> ?G ⊢ ?N : _,
      Hn : nbe_ty_f ?G (nf_to_exp ?B)[Id,,?N] ?C, HG : ⊢ ?G |- _ =>
        pose proof (IHM HG) as HM; cbn [nf_to_exp] in HM;
        assert (exists Spi, G ⊢ a_pi κd κc (nf_to_exp A) (nf_to_exp B) : Spi) as [Spi HPi]
          by (let S00 := fresh "S00" in let H00 := fresh "H00" in
              destruct (presup_exp_typ_sorted HM ltac:(discriminate)) as [S00 [_ H00]]; eauto);
        destruct (wf_pi_parts HPi) as (Hκ & (SA & HSAk & HA) & (iU & HBr));
        pose proof (sort_kind_type_sort _ _ HSAk) as HSA;
        pose proof (IHN HG _ HSA HA) as HN;
        pose proof (type_sort_kind_universe κc iU) as HSB;
        assert (HBN : G ⊢ (nf_to_exp B)[Id,,N] : abs_kind_sort κc Typeω@iU)
          by (exact (sub_preserves_sort _ _ _ _ _ _ _ HBr HSB (wf_sub_single _ _ _ _ _ _ _ HA HSAk HN)));
        refine (exp_conv_sort HSB (soundness_ty_at_sort HSB HBN Hn) _);
        eapply wf_app; [ exact HA | exact HSAk | exact HBr | exact Hκ | exact HM | exact HN ]
    end.
  (** A local definition: its type of the sort [r], an annotation checked
      against, without one a type of a universe; the body's type, of a
      sort, instantiated, normalised *)
  - match goal with
    | IHA : ⊢ ?G -> ?G ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?r ?u,
      IHM : ⊢ ?G -> forall Srt, _ -> ?G ⊢ ?A : Srt -> ?G ⊢ ?M : ?A, IHB : ⊢ ?G ▸ ?A ≔ ?M -> _ ⊢ ?B : (nf_to_exp ?C),
      HnL : nf_to_exp ?C <> LevelSort, Hr : nbe_ty_kind _ (nf_to_exp ?C) ?κC, Hlc : ?κC = ak_level -> ?r = ak_level,
      Hn : nbe_ty_f ?G (nf_to_exp ?C)[Id,,?M] ?D, HG : ⊢ ?G |- _ =>
        pose proof (sort_typed_of_is_sort_nf (IHA HG) Hs) as HAs;
        pose proof (type_sort_kind_universe r (universe_nf_large_index u)) as HSA;
        pose proof (IHM HG _ HSA HAs) as HM;
        assert (HGd : ⊢ G ▸ A ≔ M) by (eapply wf_ctx_extend_def; [ exact HAs | exact HSA | exact HM ]);
        exact (let_typed_at_nf HAs HM (IHB HGd) HnL Hr Hlc Hn)
    end.
  (** A module [let] *)
  - match goal with
    | IHU : ⊢ ?G -> gc_deps ⍮ gc_stack ⍮ ?G ⊢ᵘ ?U ≈ ?U, IHB : ⊢ ?G ▹ₘ ?U -> _ ⊢ ?B : (nf_to_exp ?C),
      HnL : nf_to_exp ?C <> LevelSort, Hr : nbe_ty_kind _ (nf_to_exp ?C) ?κC, Hlc : ?κC <> ak_level,
      Hn : nbe_ty_f ?G (nf_to_exp ?C)[Id ,,ₘ me_lit ?U] ?D, HG : ⊢ ?G |- _ =>
        pose proof (IHU HG) as HU;
        assert (HGU : ⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU);
        exact (let_mod_typed_at_nf HU (IHB HGU) HnL Hr Hlc Hn)
    end.
  (** A member, at the normal form of the type its module's description
      reads *)
  - match goal with
    | IHH : ⊢ ?G -> gc_deps ⍮ gc_stack ⍮ ?G ⊢ᵐ ?H0 ≈ ?H0, Hm : mdenote _ _ _ (me_mem ?H0 ?x0) _, Ht : mdesc_type _ = Some ?A0,
      Hn : nbe_ty_f ?G ?A0 ?B, HG : ⊢ ?G |- _ =>
        destruct (member_wf _ _ _ _ _ (IHH HG) Hm Ht) as ((SA & HSA & HA) & _ & HMt);
        exact (exp_conv_sort HSA (soundness_ty_at_sort HSA HA Hn) HMt)
    end.
  (** A variable, at the normal form of its type *)
  - match goal with
    | Hl : ?G ∋ #?x : ?A, Hn : nbe_ty_f ?G ?A ?B, HG : ⊢ ?G |- _ =>
        assert (Hx : G ⊢ #x : A) by (apply wf_vlookup; assumption);
        destruct (ctx_lookup_wf_sorted _ _ _ _ _ HG Hl) as (SA & HSA & HA);
        exact (exp_conv_sort HSA (soundness_ty_at_sort HSA HA Hn) Hx)
    end.
  (** A record's type former, a tuple and a projection *)
  - match goal with Hl : record_lookup _ _ _ = Some _, HΓ : ⊢ ?G |- _ =>
      let j := fresh "j" in let Hrt := fresh "Hrt" in let Hj := fresh "Hj" in
      destruct (record_former_typed _ _ _ HΓ Hl) as [j [Hrt Hj]];
      eapply wf_conv'; [ exact Hrt | eapply soundness_ty'; eassumption ] end.
  - match goal with
    | IHT : ⊢ ?G -> ?G ⊢ ?T : (nf_to_exp ?UT), Hu : is_univ_nf ?UT ?u, HΓ : ⊢ ?G |- _ =>
        pose proof (IHT HΓ) as HT0; rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HT0;
        pose proof (wf_exp_universe_nf_large_index HT0) as HT;
        eapply alg_tuple_sound; [ exact HΓ | exact HT | eassumption | eassumption | eassumption | intros; eauto ]
    end.
  - match goal with HM : ⊢ ?G -> ?G ⊢ ?M : _, HΓ : ⊢ ?G, Hfk : List.nth_error (record_fields _) _ = Some _ |- _ ⊢ a_proj _ ?M : _ =>
      eapply alg_proj_sound; [ exact HΓ | exact (HM HΓ) | eassumption | exact Hfk | eassumption ] end.
  (** ** Extensions, entry by entry *)
  - apply wf_ext_eq_nil; assumption.
  - match goal with
    | IHX : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P, IHA : ⊢ ?P ++ ?G -> ?P ++ ?G ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?r ?u, HG : ⊢ ?G |- _ =>
        pose proof (IHX HG) as HX; pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HP;
        pose proof (sort_typed_of_is_sort_nf (IHA HP) Hs) as HAs;
        eapply wf_ext_eq_ass_same; [ exact HX | exact HAs | apply sort_kind_abs_kind_sort | exact HAs ]
    end.
  - match goal with
    | IHX : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P, IHA : ⊢ ?P ++ ?G -> ?P ++ ?G ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?r ?u,
      IHM : ⊢ ?P ++ ?G -> forall Srt, _ -> ?P ++ ?G ⊢ ?A : Srt -> ?P ++ ?G ⊢ ?M : ?A, HG : ⊢ ?G |- _ =>
        pose proof (IHX HG) as HX; pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HP;
        pose proof (sort_typed_of_is_sort_nf (IHA HP) Hs) as HAs;
        pose proof (IHM HP _ (type_sort_kind_universe _ _) HAs) as HM;
        eapply wf_ext_eq_def_same; [ exact HX | exact HAs | apply type_sort_kind_universe | exact HAs | exact HM | exact HM ]
    end.
  - match goal with
    | IHX : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P, IHU : ⊢ ?P ++ ?G -> wf_unit_eq _ _ _ ?U ?U, HG : ⊢ ?G |- _ =>
        pose proof (IHX HG) as HX; pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HP;
        eapply wf_ext_eq_mod; [ exact HX | exact (IHU HP) | exact (IHU HP) ]
    end.
  - match goal with
    | IHX : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P, IHA : ⊢ ?P ++ ?G -> ?P ++ ?G ⊢ ?A : (nf_to_exp ?UA), Hu : is_univ_nf ?UA ?u,
      IHM : ⊢ ?P ++ ?G -> forall Srt, _ -> ?P ++ ?G ⊢ ?A : Srt -> ?P ++ ?G ⊢ ?M : ?A,
      IHU : ⊢ ?P ++ ?G -> wf_unit_eq _ _ _ ?U ?U, HG : ⊢ ?G |- _ =>
        pose proof (IHX HG) as HX; pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HP;
        pose proof (IHA HP) as HA0; rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HA0;
        pose proof (wf_exp_universe_nf_large_index HA0) as HA;
        pose proof (IHM HP _ (type_sort_universe _) HA) as HM;
        eapply wf_ext_eq_dm; [ exact HX | exact HA | apply wf_exp_eq_refl; exact HA | exact HM | apply wf_exp_eq_refl; exact HM
                             | exact HA | exact HM | exact (IHU HP) | exact (IHU HP) ]
    end.
  (** ** Parameters: each of a universe or of levels, all at one level *)
  - split; [ apply wf_ext_eq_nil; assumption | exists 0; apply params_kinded_nil ].
  - match goal with
    | IHX : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P /\ _, IHA : ⊢ ?P ++ ?G -> ?P ++ ?G ⊢ ?A : (nf_to_exp ?UA), Hu : is_univ_nf ?UA ?u, HG : ⊢ ?G |- _ =>
        destruct (IHX HG) as [HX [l Hl]]; pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HP;
        pose proof (IHA HP) as HA0; rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HA0;
        pose proof (wf_exp_universe_nf_large_index HA0) as HA;
        split; [ eapply wf_ext_eq_ass_same; [ exact HX | exact HA | constructor | exact HA ] |];
        exists (max (universe_nf_large_index u) l);
        apply params_kinded_snoc; [ exact Hl | left; split; [ reflexivity | exact HA ] ]
    end.
  - (** A parameter of levels *)
    match goal with
    | IHX : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P /\ _, IHA : ⊢ ?P ++ ?G -> ?P ++ ?G ⊢ ?A : _, HG : ⊢ ?G |- _ =>
        destruct (IHX HG) as [HX [l Hl]]; pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HP;
        pose proof (IHA HP) as HA; cbn [nf_to_exp] in HA;
        split; [ eapply wf_ext_eq_ass_same; [ exact HX | exact HA | constructor | exact HA ] |];
        exists (max 0 l);
        apply params_kinded_snoc; [ exact Hl | right; split; [ reflexivity | exact HA ] ]
    end.
  (** ** Units *)
  - eapply alg_unit_body_sound; eassumption.
  - (** An alias: the parameters' sorts by position ([param_sort_at]), and
        the flag read off the abstractability, as for a body *)
    match goal with
    | IHX : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P /\ _, IHE : ⊢ ?P ++ ?G -> wf_modexp_eq _ _ _ ?E ?E, Ha : all_assumptions ?P,
      Habs : levels_abstractable _ _ ?G ?P ?E, HG : ⊢ ?G |- _ =>
        let lp := fresh "lp" in
        destruct (IHX HG) as [HX [lp Hl]]; pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HP;
        destruct Habs as [Hsorted | (R & HR & Hnl)];
        [ eapply wf_unit_eq_alias with (param_level := lp) (param_sorts := param_sort_at P lp) (lv := true) (lv' := true)
                                         (Rt := mdesc_term ak_relevant a_prop None) (Rt' := mdesc_term ak_relevant a_prop None)
        | eapply wf_unit_eq_alias with (param_level := lp) (param_sorts := param_sort_at P lp) (lv := false) (lv' := false)
                                         (Rt := R) (Rt' := R) ];
        first [ exact HX | exact Ha | exact (IHE HP) | apply param_sort_at_parameter_sort | exact (params_kinded_sorts _ _ _ Hl)
              | intros _; assumption | discriminate | assumption ]
    end.
  (** ** Bodies, by their own lemmas *)
  - apply alg_body_nil_sound.
  - match goal with
    | IH : alg_body_sound _ _ _, HA : ⊢ _ -> _ ⊢ ?A : (nf_to_exp ?UA), Hs : is_sort_nf ?UA ?r ?u,
      HM : ⊢ _ -> forall Srt, _ -> _ ⊢ ?A : Srt -> _ ⊢ ?M : ?A |- _ =>
        eapply (alg_body_def_sound _ _ _ _ _ _ _ _ _ (universe_nf_large_index u));
          [ exact IH | intros HC; exact (sort_typed_of_is_sort_nf (HA HC) Hs)
          | intros HC; exact (HM HC _ (type_sort_kind_universe _ _) (sort_typed_of_is_sort_nf (HA HC) Hs)) ]
    end.
  - eapply alg_body_mod_sound; eassumption.
  - match goal with
    | IH : alg_body_sound _ _ _, HA : ⊢ _ -> _ ⊢ ?A : (nf_to_exp ?UA), Hu : is_univ_nf ?UA ?u,
      HM : ⊢ _ -> forall Srt, _ -> _ ⊢ ?A : Srt -> _ ⊢ ?M : ?A, HU : ⊢ _ -> wf_unit_eq _ _ _ ?U ?U |- _ =>
        assert (HA' : ⊢ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢ A : Typeω@(universe_nf_large_index u))
          by (intros HC; apply wf_exp_universe_nf_large_index; rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu);
              exact (HA HC));
        eapply (alg_body_dm_sound _ _ _ _ _ _ _ _ (universe_nf_large_index u));
          [ exact IH | exact HA' | intros HC; exact (HM HC _ (type_sort_universe _) (HA' HC)) | exact HU ]
    end.
  - eapply alg_body_open_sound; eassumption.
  (** ** Module expressions *)
  - match goal with Hm : mdenote _ _ _ (me_unit _) _ |- wf_modexp_eq _ _ _ _ _ =>
      let Hu := fresh "Hu" in
      destruct (mdenote_unit_inv _ _ ltac:(eapply ctx_wf_gctx; eassumption) _ _ _ Hm) as (? & ? & Hu & _);
      eapply wf_me_unit; [ eauto | exact Hu ] end.
  - mautosolve 4.
  - mautosolve 4.
  - match goal with Hm : mdenote _ _ _ (me_mem ?H0 _) _, Htl : mdesc_mod_tele _ = Some _, IHH : ⊢ ?G -> _, HG : ⊢ ?G |- _ =>
      pose proof (IHH HG) as HH; eapply wf_me_mem; eassumption end.
  - match goal with
    | Hm : mdenote _ _ _ ?H0 _, Htl : mdesc_mod_tele _ = Some _, Hv : tele_view _ = Some _,
      IHH : ⊢ ?G -> wf_modexp_eq _ _ _ ?H0 ?H0, IHN : ⊢ ?G -> forall Srt, _ -> ?G ⊢ ?B : Srt -> ?G ⊢ ?N : ?B, HG : ⊢ ?G
      |- wf_modexp_eq _ _ _ (me_app _ _) _ =>
        pose proof (IHH HG) as HH;
        destruct (mtele_head_wf _ _ _ _ _ _ HH Hm Htl Hv) as (Sb & HSb & HB);
        pose proof (IHN HG _ (evaluated_sort_type_sort _ HSb) HB) as HN;
        eapply wf_me_app; eauto using wf_exp_eq_refl
    end.
Qed.

Lemma alg_type_check_sound : forall {Γ i A M},
    Γ ⊢a M ⟸ A ->
    ⊢ Γ ->
    Γ ⊢ A : Typeω@i ->
    Γ ⊢ M : A.
Proof.
  intros; eapply (proj1 alg_type_sound); [ eassumption | eassumption | apply type_sort_universe | eassumption ].
Qed.

(** The same at a type of any sort. *)
Lemma alg_type_check_sound_sort : forall {Γ Srt A M},
    Γ ⊢a M ⟸ A ->
    ⊢ Γ ->
    type_sort Srt ->
    Γ ⊢ A : Srt ->
    Γ ⊢ M : A.
Proof.
  intros; eapply (proj1 alg_type_sound); eassumption.
Qed.

Lemma alg_type_infer_sound : forall {Γ A M},
    Γ ⊢a M ⟹ A -> ⊢ Γ -> Γ ⊢ M : A.
Proof.
  intros; eapply (proj1 (proj2 alg_type_sound)); eassumption.
Qed.

Lemma alg_ext_sound : forall {Γ Ψ}, Γ ⊢aˣ Ψ -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ.
Proof. intros; eapply (proj1 (proj2 (proj2 alg_type_sound))); eassumption. Qed.

(** Checked parameters are an extension, each a type of a universe, all
    at one level ((R) of the unit rules). *)
Lemma alg_params_sound : forall {Γ Δ}, Γ ⊢aᵖ Δ -> ⊢ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ /\ exists l, params_kinded Γ Δ l.
Proof. intros; eapply (proj1 (proj2 (proj2 (proj2 alg_type_sound)))); eassumption. Qed.

Lemma alg_unit_sound : forall {Γ U}, Γ ⊢aᵘ U -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U.
Proof. intros; eapply (proj1 (proj2 (proj2 (proj2 (proj2 alg_type_sound))))); eassumption. Qed.

Lemma alg_modexp_sound : forall {Γ H}, Γ ⊢aᵐ H -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros; eapply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 alg_type_sound)))))); eassumption. Qed.

(** A checked body is read in a well-formed context, past its expansion. *)
Lemma alg_body_ctx : forall {Γ Φ Φx}, ⊢ Γ -> Γ ⊢aᵇ Φ ⇝ Φx -> ⊢ body_ctx Φx ++ Γ.
Proof.
  intros * HΓ HB.
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 alg_type_sound))))) _ _ _ HB Γ nil eq_refl HΓ
              ltac:(apply wf_ext_eq_nil; exact HΓ)) as [_ HX _ _].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite List.app_nil_r in HC; exact HC.
Qed.

(** A body checks to one expansion. *)
Lemma alg_body_functional : forall {Γ Φ Φx Φx'}, ⊢ᵍ gc_deps ⍮ gc_stack ->
    Γ ⊢aᵇ Φ ⇝ Φx -> Γ ⊢aᵇ Φ ⇝ Φx' -> Φx = Φx'.
Proof.
  intros * Hg Hb1; revert Φx'; induction Hb1; intros Φx' Hb2; inversion Hb2; subst;
    try match goal with IH : forall Φx', _ ⊢aᵇ ?Φ ⇝ Φx' -> _ = Φx', Hb : _ ⊢aᵇ ?Φ ⇝ ?Y |- _ =>
      pose proof (IH _ Hb); subst Y end; try reflexivity.
  f_equal; eapply (proj2 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg))))); eassumption.
Qed.

(** The parts of a [Π] the algorithm infers: the domain at its universe, the
    codomain at the normal form of its universe, whose level's atoms are of
    the sorts they carry. *)
Lemma alg_pi_parts_sound : forall {Γ A B UA UB UB' κd u v},
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    is_sort_nf UA κd u ->
    Γ ▹{κd} A ⊢a B ⟹ UB ->
    nbe_ty_f (Γ ▹{κd} A) UB UB' ->
    is_univ_nf UB' v ->
    pi_domain_ok Γ A κd u /\ Γ ▹{κd} A ⊢ B : universe_nf_tm v /\ universe_nf_well_scoped (Γ ▹{κd} A) v.
Proof.
  intros * HΓ HAi Hs HBi HnB Hv.
  pose proof (alg_type_infer_sound HAi HΓ) as HA0.
  pose proof (sort_typed_of_is_sort_nf HA0 Hs) as HAs.
  assert (HGA : ⊢ Γ ▹{κd} A) by (eapply wf_ctx_extend; [ exact HAs | apply sort_kind_abs_kind_sort ]).
  split; [ exact (pi_domain_ok_of_is_sort_nf HA0 Hs) |].
  exact (typed_at_univ_nf _ _ _ _ _ (alg_type_infer_sound HBi HGA) HnB Hv).
Qed.

(** A normal form [W] of a type [T] of a sort normalises to itself. *)
Ltac normal_of_typed HS HT Hn Hnbe :=
  eapply idempotent_nbe_ty_sort; [ | exact HT | exact Hn | exact Hnbe ]; exact HS.

(** An inferred type is a normal form: most rules infer the normal form of
    a type of a sort, which normalises to itself; a [λ] the [Π] of its
    domain's normal form and of its body's type, normal by induction; a
    projection of a conjunction a part of a normal form.  All up to
    proofs: the normal form of a normal form is equal to it up to the
    proofs it keeps ([idempotent_nbe_ty_sort]). *)
Lemma alg_type_infer_normal : forall {Γ A A' M},
    ⊢ Γ ->
    Γ ⊢a M ⟹ A ->
    nbe_ty_f Γ A A' ->
    nf_eq_upto_proofs A A'.
Proof.
  intros Γ A A0 M HΓ0 Hinfer Hnbe0; revert A0 HΓ0 Hnbe0; induction Hinfer; intros A' HΓ0 Hnbe;
    try (rewrite (nbe_ty_suniv_lit Hnbe); reflexivity);
    try (directed_inversion_clear_by_head nbe_ty;
         directed_inversion_by_head eval_exp; subst;
         directed_inversion_by_head read_typ; subst;
         reflexivity).
  all: lazymatch goal with
  (** A small universe: the normal form of [Type⟨succl M⟩] *)
  | HMi : ?G ⊢a ?M ⟹ Levelⁿ@?k, Hn : nbe_ty_f _ (a_univ (succl ?M)) _ |- _ =>
      pose proof (alg_type_infer_sound HMi HΓ0) as HMl;
      assert (HT : G ⊢ Type⟨succl M⟩ : Typeω@0) by (eapply wf_univ_large_tm; [ assumption | eapply wf_succl; exact HMl ]);
      normal_of_typed (type_sort_universe 0) HT Hn Hnbe
  (** Ex falso: the normal form of its target *)
  | HCi : ?G ⊢a ?C ⟹ ?UC, Hs : is_sort_nf ?UC ?r ?u, HMc : alg_type_check ?G ⊥ _, Hn : nbe_ty_f ?G ?C _ |- _ =>
      normal_of_typed (type_sort_kind_universe r (universe_nf_large_index u))
        (sort_typed_of_is_sort_nf (alg_type_infer_sound HCi HΓ0) Hs) Hn Hnbe
  (** A proof of a conjunction: the normal form of the conjunction *)
  | HPi : ?G ⊢a ?P ⟹ Propⁿ, HQi : ?G ▹{ak_propositional} ?P ⊢a ?Q ⟹ Propⁿ, Hn : nbe_ty_f ?G (Σₚ ?P ?Q) _ |- _ =>
      pose proof (alg_type_infer_sound HPi HΓ0) as HP; cbn [nf_to_exp] in HP;
      assert (HGP : ⊢ G ▹{ak_propositional} P) by (eapply wf_ctx_extend; [ exact HP | exact sort_kind_prop ]);
      pose proof (alg_type_infer_sound HQi HGP) as HQ; cbn [nf_to_exp] in HQ;
      normal_of_typed type_sort_prop (wf_and _ _ _ _ _ HP HQ) Hn Hnbe
  (** The first component of a proof of a conjunction: the first part of a
      normal form *)
  | HMi : ?G ⊢a ?M ⟹ Σₚⁿ ?P ?Q, IH : forall A0, ⊢ ?G -> nbe_ty_f ?G _ A0 -> nf_eq_upto_proofs _ A0 |- nf_eq_upto_proofs ?P _ =>
      pose proof (alg_type_infer_sound HMi HΓ0) as HM;
      cbn [nf_to_exp] in HM; pose proof (and_typed_of_proof HM) as HPQ;
      destruct (nbe_ty_exists_sort type_sort_prop HPQ) as [WPQ HWPQ];
      pose proof (IH _ HΓ0 HWPQ) as E;
      cbn [nf_to_exp] in HWPQ; destruct (nbe_ty_and_inv _ _ _ _ HWPQ) as (WP & WQ & -> & HWP & _);
      functional_nbe_rewrite_clear;
      unfold nf_eq_upto_proofs in E; cbn in E; apply andb_prop in E as [E _]; exact E
  (** The second: the normal form of its type *)
  | HMi : ?G ⊢a ?M ⟹ Σₚⁿ ?P ?Q, Hn : nbe_ty_f ?G (nf_to_exp ?Q)[Id,,a_left ?M] _ |- _ =>
      pose proof (alg_type_infer_sound (alg_type_infer_right _ _ _ _ _ HMi Hn) HΓ0) as HR;
      pose proof (alg_type_infer_sound HMi HΓ0) as HM; cbn [nf_to_exp] in HM;
      pose proof (and_typed_of_proof HM) as HPQ;
      destruct (wf_and_inversion _ _ _ _ _ _ HPQ) as [HP HQ _];
      assert (HL : G ⊢ a_left M : nf_to_exp P) by (eapply wf_left; eassumption);
      normal_of_typed type_sort_prop
        (sub_preserves_sort _ _ _ _ _ _ _ HQ type_sort_prop (wf_sub_single _ _ _ _ _ _ _ HP ltac:(constructor) HL)) Hn Hnbe
  (** The type former and a constructor: the normal forms of closed types *)
  | Hl : ind_lookup _ _ _ = Some ?D, Hk : ind_member ?D _ = Some _, Hlt : _ < ind_ndecl ?D, Hn : nbe_ty_f _ (ind_ty _ _) _ |- _ =>
      destruct (decl_of_lookup _ _ _ _ _ HΓ0 Hl) as [HD Hc];
      destruct (ind_ty_typed _ _ _ _ _ _ HD Hc Hk HΓ0) as [j Hj];
      normal_of_typed (type_sort_universe j) Hj Hn Hnbe
  | Hl : ind_lookup _ _ _ = Some ?D, Hk : ind_member ?D _ = Some _, Hcon : ind_con _ _ = Some _, Hn : nbe_ty_f _ (con_ty _ _ _ _ _) _ |- _ =>
      destruct (con_ty_typed _ _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓ0) (decls_of_ctx _ _ _ HΓ0) Hl Hk Hcon HΓ0) as [j Hj];
      normal_of_typed (type_sort_universe j) Hj Hn Hnbe
  (** The eliminator: the normal form of the motive's instance *)
  | HMi : ?G ⊢a ?N ⟹ nf_indty _ _ _, Hn : nbe_ty_f ?G (eb_motive ?bm)[sb_of_list Id (?Ns ++ ?N :: nil)] _,
    Hb : List.nth_error ?Bks ?m = Some ?bm, HBl : List.length ?Bks = ind_nblk ?D,
    Hl : ind_lookup _ _ ?p = Some ?D |- _ =>
      let Sm := fresh "Sm" in let HSm := fresh "HSm" in let Hm := fresh "Hm" in
      assert (exists Srt, type_sort Srt /\ G ⊢ (eb_motive bm)[sb_of_list Id (Ns ++ N :: nil)] : Srt) as (Sm & HSm & Hm)
        by (eapply proj2; eapply (alg_elim_sound G N _ _ _ p D m);
            first [ exact HΓ0 | exact (alg_type_infer_sound HMi HΓ0) | eassumption
                  | intros; eapply alg_type_check_sound_sort; eauto ]);
      normal_of_typed HSm Hm Hn Hnbe
  (** A [Π]: the normal form of the join of its parts' universes *)
  | HAi : ?G ⊢a ?A ⟹ ?UA, Hs : is_sort_nf ?UA ?κd _, HBi : ?G ▹{?κd} ?A ⊢a ?B ⟹ ?UB,
    HnB : nbe_ty_f (?G ▹{?κd} ?A) (nf_to_exp ?UB) ?UB', Hv : is_sort_nf ?UB' _ _,
    Hn : nbe_ty_f ?G (abs_kind_sort _ (universe_nf_pi_tm _ _)) _ |- _ =>
      destruct Hv as [UB0 v0 Hv | |]; cbn [abs_kind_sort] in Hn;
      [ destruct (alg_pi_parts_sound HΓ0 HAi Hs HBi HnB Hv) as (HA' & HB' & Hvw);
        destruct (wf_universe_nf_pi_tm HA' HB' Hvw) as [k Hk];
        normal_of_typed (type_sort_universe k) Hk Hn Hnbe
      | normal_of_typed (type_sort_universe 1) (motive_kind_sort_typed _ ak_propositional 0 ltac:(constructor) HΓ0) Hn Hnbe
      | destruct Hn as [ρ a1 Hρ Ha HWr]; inversion Ha; subst; inversion HWr; subst;
        directed_inversion_clear_by_head nbe_ty; directed_inversion_by_head eval_exp; subst;
        directed_inversion_by_head read_typ; subst; reflexivity ]
  (** A [λ]: the [Π] of its domain's normal form, normal, and of its
      body's type, normal by induction, in the context the domain's normal
      form extends, semantically the context the domain extends *)
  | HAi : ?G ⊢a ?A ⟹ ?UA, Hs : is_sort_nf ?UA ?κd ?u, HMi : ?G ▹{?κd} ?A ⊢a ?M ⟹ ?B, HnL : nf_to_exp ?B <> LevelSort,
    Hr : nbe_ty_kind (?G ▹{?κd} ?A) (nf_to_exp ?B) ?κc, Hn : nbe_ty_f ?G ?A ?C,
    IH : forall A0, ⊢ ?G ▹{?κd} ?A -> nbe_ty_f (?G ▹{?κd} ?A) (nf_to_exp ?B) A0 -> nf_eq_upto_proofs ?B A0 |- _ =>
      pose proof (sort_typed_of_is_sort_nf (alg_type_infer_sound HAi HΓ0) Hs) as HAs;
      pose proof (type_sort_kind_universe κd (universe_nf_large_index u)) as HSA;
      assert (HGA : ⊢ G ▹{κd} A) by (eapply wf_ctx_extend; [ exact HAs | apply sort_kind_abs_kind_sort ]);
      let kB := fresh "kB" in let HBs := fresh "HBs" in
      destruct (typed_at_kind_of_nbe (alg_type_infer_sound HMi HGA) HnL Hr) as [kB HBs];
      pose proof (soundness_ty_at_sort HSA HAs Hn) as HAC;
      cbn [nf_to_exp] in Hnbe; destruct (nbe_ty_pi_inv _ _ _ _ _ _ Hnbe) as (WC & WB & -> & HWC & HWB);
      pose proof (idempotent_nbe_ty_sort HSA HAs Hn HWC) as HCW;
      assert (HBC : G ▹{κd} nf_to_exp C ⊢ nf_to_exp B : abs_kind_sort κc Typeω@kB)
        by (eapply ctxsub_exp; [ exact (sub_id_extend_of_exp_eq (sort_kind_abs_kind_sort _ _) (wf_exp_eq_sym _ _ _ _ _ _ HAC)) | exact HBs ]);
      let WB' := fresh "WB'" in let HWB' := fresh "HWB'" in
      destruct (nbe_ty_exists_sort (type_sort_kind_universe _ _) HBs) as [WB' HWB'];
      pose proof (ctxeq_nbe_ty_eq_sort (type_sort_kind_universe _ _) HBC
                    (ctx_extend_sem_eq HSA (wf_exp_eq_sym _ _ _ _ _ _ HAC)) ltac:(eapply wf_ctx_scoped; exact HGA) HWB HWB') as HBB;
      exact (nf_pi_upto_proofs _ _ _ _ _ _ HCW (transitivity (IH _ HGA HWB') (symmetry HBB)))
  (** An application: the normal form of the codomain instantiated *)
  | HMi : ?G ⊢a ?M ⟹ nf_pi ?κd ?κc ?A ?B, HNc : alg_type_check ?G (nf_to_exp ?A) ?N, Hn : nbe_ty_f ?G (nf_to_exp ?B)[Id,,?N] _ |- _ =>
      pose proof (alg_type_infer_sound HMi HΓ0) as HM; cbn [nf_to_exp] in HM;
      let Spi := fresh "Spi" in let HPi := fresh "HPi" in
      assert (exists Spi, G ⊢ a_pi κd κc (nf_to_exp A) (nf_to_exp B) : Spi) as [Spi HPi]
        by (let S00 := fresh "S00" in let H00 := fresh "H00" in
            destruct (presup_exp_typ_sorted HM ltac:(discriminate)) as [S00 [_ H00]]; eauto);
      let Hκ := fresh "Hκ" in let SA := fresh "SA" in let HSAk := fresh "HSAk" in let HA := fresh "HA" in
      let iU := fresh "iU" in let HBr := fresh "HBr" in
      destruct (wf_pi_parts HPi) as (Hκ & (SA & HSAk & HA) & (iU & HBr));
      pose proof (alg_type_check_sound_sort HNc HΓ0 (sort_kind_type_sort _ _ HSAk) HA) as HN;
      normal_of_typed (type_sort_kind_universe κc iU)
        (sub_preserves_sort _ _ _ _ _ _ _ HBr (type_sort_kind_universe _ _) (wf_sub_single _ _ _ _ _ _ _ HA HSAk HN)) Hn Hnbe
  (** A local definition: the normal form of its body's type instantiated *)
  | HAi : ?G ⊢a ?A ⟹ ?UA, Hs : is_sort_nf ?UA ?r ?u, HMc : alg_type_check ?G ?A ?M,
    HBi : ?G ▸ ?A ≔ ?M ⊢a ?B ⟹ ?C, HnL : nf_to_exp ?C <> LevelSort, Hr : nbe_ty_kind _ (nf_to_exp ?C) ?κC,
    Hn : nbe_ty_f ?G (nf_to_exp ?C)[Id,,?M] _ |- _ =>
      pose proof (sort_typed_of_is_sort_nf (alg_type_infer_sound HAi HΓ0) Hs) as HAs;
      pose proof (type_sort_kind_universe r (universe_nf_large_index u)) as HSA;
      pose proof (alg_type_check_sound_sort HMc HΓ0 HSA HAs) as HM;
      assert (HGd : ⊢ G ▸ A ≔ M) by (eapply wf_ctx_extend_def; [ exact HAs | exact HSA | exact HM ]);
      let kC := fresh "kC" in let HC := fresh "HC" in
      destruct (typed_at_kind_of_nbe (alg_type_infer_sound HBi HGd) HnL Hr) as [kC HC];
      normal_of_typed (type_sort_kind_universe κC kC)
        (sub_preserves_sort _ _ _ _ _ _ _ HC (type_sort_kind_universe κC kC) (wf_sub_single_def _ _ _ _ _ _ HAs HSA HM)) Hn Hnbe
  (** A module [let]: the same *)
  | HUi : ?G ⊢aᵘ ?U, HBi : ?G ▹ₘ ?U ⊢a ?B ⟹ ?C, HnL : nf_to_exp ?C <> LevelSort, Hr : nbe_ty_kind _ (nf_to_exp ?C) ?κC,
    Hn : nbe_ty_f ?G (nf_to_exp ?C)[Id ,,ₘ me_lit ?U] _ |- _ =>
      pose proof (alg_unit_sound HUi HΓ0) as HU;
      assert (HGU : ⊢ G ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU);
      let kC := fresh "kC" in let HC := fresh "HC" in
      destruct (typed_at_kind_of_nbe (alg_type_infer_sound HBi HGU) HnL Hr) as [kC HC];
      normal_of_typed (type_sort_kind_universe κC kC)
        (sub_preserves_sort _ _ _ _ _ _ _ HC (type_sort_kind_universe κC kC) (wf_sub_single_mod _ _ _ _ HU)) Hn Hnbe
  (** A member: the normal form of the type its module's description reads *)
  | HHi : ?G ⊢aᵐ ?H0, Hm : mdenote _ _ _ (me_mem _ _) _, Ht : mdesc_type _ = Some ?A0, Hn : nbe_ty_f _ ?A0 _ |- _ =>
      let SA := fresh "SA" in let HSA := fresh "HSA" in let HA := fresh "HA" in
      destruct (member_wf _ _ _ _ _ (alg_modexp_sound HHi HΓ0) Hm Ht) as ((SA & HSA & HA) & _);
      normal_of_typed HSA HA Hn Hnbe
  (** A variable: the normal form of its type *)
  | Hl : ?G ∋ #?x : ?A, Hn : nbe_ty_f ?G ?A _ |- _ =>
      let SA := fresh "SA" in let HSA := fresh "HSA" in let HA := fresh "HA" in
      destruct (ctx_lookup_wf_sorted _ _ _ _ _ HΓ0 Hl) as (SA & HSA & HA);
      normal_of_typed HSA HA Hn Hnbe
  (** A record's type former, a tuple and a projection *)
  | Hl : record_lookup _ _ _ = Some _, Hn : nbe_ty_f _ (record_ty _) _ |- _ =>
      let j := fresh "j" in let Hj := fresh "Hj" in
      destruct (record_former_typed _ _ _ HΓ0 Hl) as [j [_ Hj]];
      normal_of_typed (type_sort_universe j) Hj Hn Hnbe
  | HTi : ?G ⊢a ?T ⟹ ?UT, Hu : is_univ_nf ?UT ?u, Hn : nbe_ty_f ?G ?T (nf_record _ _) |- _ =>
      pose proof (alg_type_infer_sound HTi HΓ0) as HT0; rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in HT0;
      normal_of_typed (type_sort_universe (universe_nf_large_index u)) (wf_exp_universe_nf_large_index HT0) Hn Hnbe
  | HMi : ?G ⊢a ?N ⟹ nf_record _ _, Hfk : List.nth_error (record_fields _) _ = Some (_, ?U), Hn : nbe_ty_f _ (?U[_]) _ |- _ =>
      let m := fresh "m" in let HUt := fresh "HUt" in
      destruct (alg_proj_typed _ _ _ _ _ _ _ _ HΓ0 (alg_type_infer_sound HMi HΓ0) ltac:(eassumption) Hfk) as (m & HUt & _);
      eapply idempotent_nbe_ty_sort; [ apply type_sort_kind_universe | exact HUt | exact Hn | exact Hnbe ]
  end.
Qed.

Hint Resolve alg_type_infer_normal : mctt.

(** A type ([⊢ᵗ]) has a normal form: one of a sort by normalization,
    [LevelSort] its own, read at the initial environment of the context
    (which the normal form of a universe gives). *)
Lemma nbe_ty_exists_wf_type : forall {Γ A}, Γ ⊢ᵗ A -> exists W, nbe_ty_f Γ A W.
Proof.
  intros * [? S HS HA | HΓ]; [ exact (nbe_ty_exists_sort HS HA) |].
  destruct (nbe_ty_exists_sort (type_sort_universe 1) ltac:(apply wf_typ; exact HΓ)) as [W [ρ a Hρ _ _]].
  exists LevelSortⁿ; econstructor; [ exact Hρ | econstructor | econstructor ].
Qed.

(** [Prop] and [LevelSort] are their own normal forms. *)
Lemma nbe_ty_prop_self : forall {Γ}, ⊢ Γ -> nbe_ty_f Γ Propₘ Propⁿ.
Proof.
  intros * HΓ.
  destruct (nbe_ty_exists_sort (type_sort_universe 1) (motive_kind_sort_typed _ ak_propositional 0 ltac:(constructor) HΓ)) as [W HW].
  assert (W = Propⁿ) as -> by (inversion HW; subst; directed_inversion_by_head eval_exp; subst;
                                directed_inversion_by_head read_typ; subst; reflexivity).
  exact HW.
Qed.

Lemma nbe_ty_level_sort_self : forall {Γ}, ⊢ Γ -> nbe_ty_f Γ LevelSort LevelSortⁿ.
Proof.
  intros * HΓ.
  destruct (nbe_ty_exists_wf_type (wf_type_level_sort HΓ)) as [W HW].
  assert (W = LevelSortⁿ) as -> by (inversion HW; subst; directed_inversion_by_head eval_exp; subst;
                                     directed_inversion_by_head read_typ; subst; reflexivity).
  exact HW.
Qed.

(** An inferred type has a normal form equal to it up to proofs
    ([alg_type_infer_normal]). *)
Lemma alg_type_infer_self_upto : forall {Γ A M},
    ⊢ Γ ->
    Γ ⊢a M ⟹ A ->
    exists A', nbe_ty_f Γ A A' /\ nf_eq_upto_proofs A A'.
Proof.
  intros * HΓ Hi.
  destruct (nbe_ty_exists_wf_type (presup_exp_typ (alg_type_infer_sound Hi HΓ))) as (C & HC).
  exists C; split; [ exact HC | exact (alg_type_infer_normal HΓ Hi HC) ].
Qed.

(** An inferred type that holds no proof is its own normal form: equal up
    to proofs to it, it is it ([nf_ne_proof_free_eq]). *)
Lemma alg_type_infer_self : forall {Γ A M},
    ⊢ Γ ->
    Γ ⊢a M ⟹ A ->
    nf_proof_free A ->
    nbe_ty_f Γ A A.
Proof.
  intros * HΓ Hi Hpf.
  destruct (alg_type_infer_self_upto HΓ Hi) as (C & HC & E).
  rewrite <- (proj1 nf_ne_proof_free_eq _ Hpf _ E) in HC; exact HC.
Qed.

(** An inferred small universe holds no proof: its normal form, equal to
    it up to proofs, is the normal form of a type of a large universe,
    whose atoms hold none ([nbe_ty_univ_proof_free]). *)
Lemma alg_type_infer_univ_proof_free : forall {Γ M c xs},
    ⊢ Γ -> Γ ⊢a M ⟹ univⁿ c xs -> nf_proof_free (univⁿ c xs).
Proof.
  intros * HΓ Hi.
  destruct (alg_type_infer_self_upto HΓ Hi) as (C & HC & E).
  pose proof (alg_type_infer_sound Hi HΓ) as HM; cbn [nf_to_exp] in HM.
  assert (exists k, Γ ⊢ Type⟨lvl_exp_of c (List.map atom_exp xs)⟩ : Typeω@k) as [k Hk] by univ_large.
  pose proof E as E0; symmetry in E0.
  destruct C; unfold nf_eq_upto_proofs in E; cbn in E; try discriminate.
  pose proof (nbe_ty_univ_proof_free Hk HC) as Hpf.
  rewrite <- (proj1 nf_ne_proof_free_eq _ Hpf _ E0); exact Hpf.
Qed.

(** A checked term infers a type below the normal form of the checked
    one: the inferred type is equal up to proofs to its normal form
    ([alg_type_infer_normal]). *)
Lemma alg_type_check_infer_below : forall {Γ M B},
    ⊢ Γ -> Γ ⊢a M ⟸ B -> exists A W, Γ ⊢a M ⟹ A /\ nbe_ty_f Γ B W /\ ⊢anf A ⊆ W.
Proof.
  intros * HΓ Hc; inversion Hc as [? A ? ? Hi [A' W Hn1 Hn2 Hs]]; subst.
  exists A, W; split; [ exact Hi | split; [ exact Hn2 |] ].
  eapply alg_subtyping_nf_trans; [ apply alg_subtyping_nf_of_upto_proofs; exact (alg_type_infer_normal HΓ Hi Hn1) | exact Hs ].
Qed.

(** The type a term infers below a type of a sort is of a sort: it is no
    [LevelSort], which is below only itself, of no sort. *)
Lemma alg_infer_below_sorted : forall {Γ M A B S},
    ⊢ Γ -> type_sort S -> Γ ⊢ B : S -> Γ ⊢a M ⟹ A -> Γ ⊢a A ⊆ B -> exists SA, type_sort SA /\ Γ ⊢ A : SA.
Proof.
  intros * HΓ HS HB Hi Hs.
  pose proof (alg_type_infer_sound Hi HΓ) as HM.
  destruct (presup_exp_typ_cases HM) as [? SA HSA HA | ? Hlf]; [ eauto |].
  exfalso; destruct Hs as [A' B' HA' HB' Hsub].
  inversion HA' as [ρ a1 Hρ Ha HW]; subst; inversion Ha; subst; inversion HW; subst.
  inversion Hsub; subst.
  match goal with HE : nf_eq_upto_proofs LevelSortⁿ ?X |- _ => destruct X; cbn in HE; try discriminate end.
  pose proof (soundness_ty_at_sort HS HB HB') as HE'; cbn [nf_to_exp] in HE'.
  eapply level_sort_untyped; eapply presup_exp_eq_right; exact HE'.
Qed.

(** The case of [alg_subtyping_nf] at normal forms of no universe or [Π]
    case is impossible below a universe or a type of levels: the two
    would be equal up to proofs. *)
Ltac refl_case_absurd :=
  match goal with Hn : not_univ_pi ?X, E : nf_eq_upto_proofs ?X _ |- _ =>
    destruct X; cbn in Hn; try contradiction; unfold nf_eq_upto_proofs in E; cbn in E; discriminate end.

(** A former of a type of levels is no application spine: an
    application is neither [Level@n] nor a [Π]. *)
Lemma apps_exp_level_former : forall l M, level_type_former (apps_exp M l) -> l = nil /\ level_type_former M.
Proof.
  induction l as [| N l IH]; intros M H; cbn in H; [ split; [ reflexivity | exact H ] |].
  apply IH in H as [_ H]; inversion H.
Qed.

(** A type former applied to its parameters is a type of a large
    universe: of a sort, it is no proposition, being below itself
    ([subtyp_prop_ind_absurd]), and no type of levels
    ([apps_exp_level_former]). *)
Lemma ind_apps_typed_large : forall {Γ p k X S},
    type_sort S -> Γ ⊢ apps (a_ind p k) X : S -> exists j, Γ ⊢ apps (a_ind p k) X : Typeω@j.
Proof.
  intros * HS HX.
  destruct HS as [j | |]; [ exists j; exact HX | exfalso | exfalso ].
  - eapply subtyp_prop_ind_absurd; [| exact HX ].
    eapply wf_subtyp_refl; [ exact HX | exact type_sort_prop | apply wf_exp_eq_refl; exact HX ].
  - pose proof (level_sort_typed_former HX) as Hf.
    apply apps_exp_level_former in Hf as [_ Hf]; inversion Hf.
Qed.

(** The same for a record type: no proposition
    ([typ_prop_record_absurd]), no type of levels. *)
Lemma record_apps_typed_large : forall {Γ p X S},
    type_sort S -> Γ ⊢ apps (a_record p) X : S -> exists j, Γ ⊢ apps (a_record p) X : Typeω@j.
Proof.
  intros * HS HX.
  destruct HS as [j | |]; [ exists j; exact HX | exfalso; exact (typ_prop_record_absurd HX) | exfalso ].
  pose proof (level_sort_typed_former HX) as Hf.
  apply apps_exp_level_former in Hf as [_ Hf]; inversion Hf.
Qed.

(** A type checked against a large universe infers a universe at an index
    below it: with the small tier that index need not be a large one. *)
Lemma alg_type_check_typ_implies_alg_type_infer_typ : forall {Γ A i},
    ⊢ Γ ->
    Γ ⊢a A ⟸ Typeω@i ->
    exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ universe_nf_le u (universe_large i).
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [A'' ? Hnbe1 Hnbe2 Hnfsub0]; subst.
  (** the inferred type is below its normal form, equal up to proofs *)
  pose proof (alg_subtyping_nf_trans _ _ _
                (alg_subtyping_nf_of_upto_proofs _ _ (alg_type_infer_normal H Hinfer Hnbe1)) Hnfsub0) as Hnfsub.
  inversion Hnbe2; subst.
  directed_inversion_by_head eval_exp; subst.
  directed_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst.
  - match goal with Hn : not_univ_pi ?X, E : nf_eq_upto_proofs ?X _ |- _ =>
      destruct X; cbn in Hn; try contradiction; unfold nf_eq_upto_proofs in E; cbn in E; discriminate end.
  - exists Typeωⁿ@i0, (universe_large i0); split; [ exact Hinfer | split; [ constructor | cbn; assumption ] ].
  - exists (univⁿ c xs), (universe_small (c, xs)); split; [ exact Hinfer | split; [ constructor | exact I ] ].
Qed.

Hint Resolve alg_type_check_typ_implies_alg_type_infer_typ : mctt.

(** A term checked against a [Π] at the kinds [κd] and [κc] infers a [Π]
    at those kinds: its domain equal to the [Π]'s, its codomain below the
    [Π]'s (equal to it up to proofs into [Prop], where subtyping is
    equality).  The inferred type is equal up to proofs to its normal
    form ([alg_type_infer_normal]), so below the [Π]'s normal form; its
    domain and the [Π]'s, of one kind, are at one sort
    ([sort_kind_common]), with normal forms equal up to proofs
    ([exp_eq_of_nbe_ty_same]). *)
Lemma alg_type_check_pi_implies_alg_type_infer_pi : forall {Γ M κd κc A B S},
    ⊢ Γ ->
    Γ ⊢ a_pi κd κc A B : S ->
    Γ ⊢a M ⟸ a_pi κd κc A B ->
    exists A' B' SA, sort_kind SA κd /\ Γ ⊢a M ⟹ nf_pi κd κc A' B' /\ Γ ⊢ A' ≈ A : SA /\ Γ ▹{κd} A ⊢a B' ⊆ B.
Proof.
  intros * HΓ HPi Hcheck.
  destruct (wf_pi_parts HPi) as (Hκ & (SA0 & HSAk0 & HA) & (k & HB)).
  inversion Hcheck as [? W ? ? Hinfer Hsub]; subst.
  destruct Hsub as [W1 W2 Hn1 Hn2 Hnf0].
  pose proof (alg_type_infer_normal HΓ Hinfer Hn1) as HW1.
  pose proof (alg_subtyping_nf_trans _ _ _ (alg_subtyping_nf_of_upto_proofs _ _ HW1) Hnf0) as Hnf.
  destruct (nbe_ty_pi_inv _ _ _ _ _ _ Hn2) as (WA & WB & -> & HnA & HnB).
  (** The inferred type is a [Π] at the kinds [κd] and [κc]. *)
  assert (exists WA' WB', W = nf_pi κd κc WA' WB' /\ nf_eq_upto_proofs WA' WA /\ ⊢anf WB' ⊆ WB)
    as (WA' & WB' & -> & HWA & HWB).
  { inversion Hnf; subst.
    - match goal with E : nf_eq_upto_proofs W _ |- _ =>
        destruct W; try (unfold nf_eq_upto_proofs in E; cbn in E; discriminate);
        apply nf_pi_upto_proofs_inv in E as (<- & <- & EA & EB) end.
      do 2 eexists; split; [ reflexivity | split; [ exact EA | apply alg_subtyping_nf_of_upto_proofs; exact EB ] ].
    - do 2 eexists; split; [ reflexivity | split; eassumption ]. }
  (** The inferred [Π] is typed; its domain and the [Π]'s at one sort. *)
  pose proof (alg_type_infer_sound Hinfer HΓ) as HM; cbn [nf_to_exp] in HM.
  destruct (presup_exp_typ_sorted HM ltac:(discriminate)) as (S' & _ & HPi').
  destruct (wf_pi_parts HPi') as (_ & (SA' & HSAk' & HA') & (k' & HB')).
  destruct (sort_kind_common HSAk' HSAk0 HA' HA) as (j & HA'j & HAj).
  pose proof (type_sort_kind_universe κd j) as HSj.
  destruct (nbe_ty_pi_inv _ _ _ _ _ _ Hn1) as (X & Y & -> & HnX & HnY).
  apply nf_pi_upto_proofs_inv in HW1 as (_ & _ & HWX & HWY).
  assert (HAA : Γ ⊢ WA' ≈ A : abs_kind_sort κd Typeω@j)
    by (eapply exp_eq_of_nbe_ty_same; [ exact HSj | exact HA'j | exact HAj | exact HnX | exact HnA
                                      | transitivity WA'; [ symmetry; exact HWX | exact HWA ] ]).
  exists WA', WB', (abs_kind_sort κd Typeω@j).
  split; [ apply sort_kind_abs_kind_sort | split; [ exact Hinfer | split; [ exact HAA |] ] ].
  (** The inferred codomain, read in the context [A] extends, is below the
      [Π]'s codomain's normal form. *)
  assert (HΓA : ⊢ Γ ▹{κd} A) by (gen_presups; assumption).
  assert (HB'A : Γ ▹{κd} A ⊢ WB' : abs_kind_sort κc Typeω@k')
    by (eapply ctxsub_exp; [ exact (sub_id_extend_of_exp_eq (sort_kind_abs_kind_sort κd j) (wf_exp_eq_sym _ _ _ _ _ _ HAA)) | exact HB' ]).
  destruct (nbe_ty_exists_sort (type_sort_kind_universe _ _) HB'A) as [Y' HnY'].
  assert (HYY : nf_eq_upto_proofs Y Y')
    by (eapply ctxeq_nbe_ty_eq_sort; [ apply type_sort_kind_universe | exact HB'
                                     | eapply ctx_extend_sem_eq; [ exact HSj | exact HAA ]
                                     | eapply wf_ctx_scoped; exact HΓA | exact HnY | exact HnY' ]).
  econstructor; [ exact HnY' | exact HnB |].
  eapply alg_subtyping_nf_trans; [ apply alg_subtyping_nf_of_upto_proofs | exact HWB ].
  transitivity Y; [ symmetry; exact HYY | symmetry; exact HWY ].
Qed.

Hint Resolve alg_type_check_pi_implies_alg_type_infer_pi : mctt.

Lemma alg_type_check_subtyp : forall {Γ A A' M},
    Γ ⊢a M ⟸ A ->
    Γ ⊢ A ⊆ A' ->
    Γ ⊢a M ⟸ A'.
Proof.
  intros * [] **.
  assert (Γ0 ⊢a B ⊆ A') by mauto 3 using alg_subtyping_complete.
  mauto 3 using alg_subtyping_trans.
Qed.

Hint Resolve alg_type_check_subtyp : mctt.

Corollary alg_type_check_conv : forall {Γ i A A' M},
    Γ ⊢a M ⟸ A ->
    Γ ⊢ A ≈ A' : Typeω@i ->
    Γ ⊢a M ⟸ A'.
Proof.
  mauto 3.
Qed.

Hint Resolve alg_type_check_conv : mctt.

(** A term that infers the normal form of a type of a sort checks against
    the type. *)
Lemma alg_type_check_of_infer_nbe : forall {Γ M A S},
    type_sort S ->
    Γ ⊢ A : S ->
    (forall W, nbe_ty_f Γ A W -> Γ ⊢a M ⟹ W) ->
    Γ ⊢a M ⟸ A.
Proof.
  intros * HS HA Hi.
  destruct (nbe_ty_exists_sort HS HA) as [W HW].
  pose proof (soundness_ty_at_sort HS HA HW) as HE.
  econstructor; [ exact (Hi _ HW) |].
  apply alg_subtyping_complete.
  exact (proj2 (wf_subtyp_of_exp_eq _ _ _ _ _ _ HA (presup_exp_eq_right HE) HS HE)).
Qed.

(** A term checked against a type [T] whose normal form [Tn] is of no
    universe or [Π] case and holds no proof infers [Tn]: subtyping below
    [Tn] is equality up to proofs ([alg_subtyping_nf_not_univ_pi_eq]), the
    inferred type is equal up to proofs to its normal form
    ([alg_type_infer_normal]), and a proof-free normal form is equal to
    what is equal to it up to proofs ([nf_ne_proof_free_eq]). *)
Lemma alg_type_check_infer_of_nf : forall {Γ A T} {Tn : nf},
    ⊢ Γ -> Γ ⊢a A ⟸ T -> (forall W, nbe_ty_f Γ T W -> W = Tn) -> not_univ_pi Tn -> nf_proof_free Tn ->
    Γ ⊢a A ⟹ Tn.
Proof.
  intros * HΓ Hc HT Hn Hpf.
  inversion Hc as [? W ? ? Hi [W1 W2 Hn1 Hn2 Hsub]]; subst.
  rewrite (HT _ Hn2) in Hsub.
  pose proof (alg_subtyping_nf_not_univ_pi_eq _ _ Hsub (or_intror Hn)) as E1.
  pose proof (transitivity (alg_type_infer_normal HΓ Hi Hn1) E1) as E.
  rewrite <- (proj1 nf_ne_proof_free_eq _ Hpf _ (symmetry E)) in Hi; exact Hi.
Qed.

(** A term checked against [Prop] infers [Prop]: subtyping at a
    proposition is equality up to proofs ([alg_subtyping_nf_not_univ_pi_eq]),
    and [Prop] holds none. *)
Lemma alg_type_check_prop_infer : forall {Γ A},
    ⊢ Γ ->
    Γ ⊢a A ⟸ Propₘ ->
    Γ ⊢a A ⟹ Propⁿ.
Proof.
  intros * HΓ Hc.
  eapply alg_type_check_infer_of_nf; [ exact HΓ | exact Hc | | exact I | exact I ].
  intros W Hn2; inversion Hn2; subst; directed_inversion_by_head eval_exp; subst;
    directed_inversion_by_head read_typ; subst; reflexivity.
Qed.

(** A term checked against [LevelSort] infers [LevelSort]: subtyping
    below it is equality. *)
Lemma alg_type_check_level_sort_infer : forall {Γ A},
    ⊢ Γ ->
    Γ ⊢a A ⟸ LevelSort ->
    Γ ⊢a A ⟹ LevelSortⁿ.
Proof.
  intros * HΓ Hc.
  eapply alg_type_check_infer_of_nf; [ exact HΓ | exact Hc | | exact I | exact I ].
  intros W Hn2; inversion Hn2; subst; directed_inversion_by_head eval_exp; subst;
    directed_inversion_by_head read_typ; subst; reflexivity.
Qed.

(** A term checked against a sort infers a sort. *)
Lemma alg_type_check_sort_infer : forall {Γ A S},
    ⊢ Γ ->
    type_sort S ->
    Γ ⊢a A ⟸ S ->
    exists UA r u, Γ ⊢a A ⟹ UA /\ is_sort_nf UA r u.
Proof.
  intros * HΓ [i | |] Hc.
  - destruct (alg_type_check_typ_implies_alg_type_infer_typ HΓ Hc) as (UA & u & Hi & Hu & _).
    exists UA, ak_relevant, u; split; [ exact Hi | constructor; exact Hu ].
  - exists Propⁿ, ak_propositional, (universe_small (ordinal_of_nat 0, nil)).
    split; [ exact (alg_type_check_prop_infer HΓ Hc) | constructor ].
  - exists LevelSortⁿ, ak_level, (universe_small (ordinal_of_nat 0, nil)).
    split; [ exact (alg_type_check_level_sort_infer HΓ Hc) | constructor ].
Qed.

(** ** Unannotated Definitions

    The number of unannotated [let]s in a term, the measure of the outer
    induction of completeness: the body of an unannotated [let] is checked in
    a context refined to the type its definiens infers, by a derivation which
    is not a subderivation, but whose subject has fewer of them.  The
    eliminators and the module expressions a term, a unit or a body reads are
    counted too: the motive and the branches of an eliminator are typed at the
    parameters the scrutinee infers, and a module expression is well-formed
    by a derivation that may go through its δ- and β-reducts, so its parts are
    reached by generation ([modexp_gen]), not as subderivations. *)
Fixpoint exp_lets (M : exp) : nat :=
  match M with
  | a_succl M | a_univ M => exp_lets M
  | a_maxl M N => exp_lets M + exp_lets N
  | a_absurd A M => exp_lets A + exp_lets M
  | a_and P Q => exp_lets P + exp_lets Q
  | a_conj P Q M N => exp_lets P + exp_lets Q + exp_lets M + exp_lets N
  | a_left M | a_right M => exp_lets M
  | a_elim _ _ Us _ Bks M =>
      S ((fix us_lets (Us : list exp) : nat :=
            match Us with
            | nil => 0
            | U :: Us' => exp_lets U + us_lets Us'
            end) Us +
         (fix blocks_lets (Bks : list eblock) : nat :=
            match Bks with
            | nil => 0
            | eb_mk _ Z A Bs :: Bks' =>
                exp_lets Z + exp_lets A +
                (fix brs_lets (Bs : list (String.string * nat * exp)) : nat :=
                   match Bs with
                   | nil => 0
                   | b :: Bs' => exp_lets (snd b) + brs_lets Bs'
                   end) Bs + blocks_lets Bks'
            end) Bks + exp_lets M)
  | a_pi _ _ A B => exp_lets A + exp_lets B
  | a_fn A M => exp_lets A + exp_lets M
  | a_app M N => exp_lets M + exp_lets N
  | a_let b B => binding_lets b + exp_lets B
  | a_mem H _ => S (modexp_lets H)
  | a_tuple T fs =>
      exp_lets T +
      (fix fields_lets (fs : list (String.string * exp)) : nat :=
         match fs with
         | nil => 0
         | f :: fs' => exp_lets (snd f) + fields_lets fs'
         end) fs
  | a_proj _ M => exp_lets M
  | _ => 0
  end
with modexp_lets (H : modexp) : nat :=
  match H with
  | me_mem H _ => modexp_lets H
  | me_app H N => modexp_lets H + exp_lets N
  | me_lit U => gunit_lets U
  | _ => 0
  end
with binding_lets (b : binding) : nat :=
  match b with
  | b_def A M => exp_lets A + exp_lets M
  | b_mod U => gunit_lets U
  end
with gunit_lets (U : gunit) : nat :=
  match U with
  | gu_mk Δ D =>
      (fix tele_lets (Δ : list centry) : nat :=
         match Δ with
         | nil => 0
         | e :: Δ' => centry_lets e + tele_lets Δ'
         end) Δ + moddef_lets D
  end
with moddef_lets (D : moddef) : nat :=
  match D with
  (** one more than its entries: each part of a unit has fewer [let]s
      than the unit, for the expanded side of [wf_unit_eq_expand] *)
  | md_body sm Φ => S (gmod_lets Φ)
  | md_alias E => S (modexp_lets E)
  end
with gmod_lets (Φ : gmod) : nat :=
  match Φ with
  | gm_nil => 0
  | gm_ext Φ _ E => gmod_lets Φ + gentry_lets E
  | gm_open Φ H _ _ => gmod_lets Φ + S (modexp_lets H)
  end
with gentry_lets (E : gentry) : nat :=
  match E with
  | ge_def _ _ _ A B => exp_lets A + match B with Some M => exp_lets M | None => 0 end
  | ge_mod _ U => gunit_lets U
  (** an inductive or a record stands in the body's context as an alias,
      of one module expression ([body_ctx]) *)
  | ge_ind _ _ _ _ Φ => S (gmod_lets Φ)
  | ge_def_mod _ A M U => exp_lets A + exp_lets M + gunit_lets U
  | ge_record _ _ _ Φ => S (gmod_lets Φ)
  end
with centry_lets (e : centry) : nat :=
  match e with
  | ce_ass _ A => exp_lets A
  | ce_def A M => exp_lets A + exp_lets M
  | ce_mod U => gunit_lets U
  | ce_dm A M U => exp_lets A + exp_lets M + gunit_lets U
  end.

Fixpoint ctx_lets (Γ : ctx) : nat :=
  match Γ with
  | nil => 0
  | e :: Γ' => centry_lets e + ctx_lets Γ'
  end.

Lemma gunit_lets_mk : forall Δ D, gunit_lets (gu_mk Δ D) = ctx_lets Δ + moddef_lets D.
Proof. intros; cbn; f_equal; induction Δ; cbn; congruence. Qed.

Lemma ctx_lets_app : forall Ψ Γ, ctx_lets (Ψ ++ Γ) = ctx_lets Ψ + ctx_lets Γ.
Proof. induction Ψ; intros; cbn; [| rewrite IHΨ ]; lia. Qed.

(** A chain of selections counts as its head. *)
Lemma modexp_lets_mems : forall pre H, modexp_lets (me_mems H pre) = modexp_lets H.
Proof. induction pre as [| y pre IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma body_ctx_lets : forall Φ, ctx_lets (body_ctx Φ) <= gmod_lets Φ.
Proof.
  induction Φ as [| Φ IH x [b pv r A [M |] | pm U | ? ? ? ? ? | ? ? ? ? | ? ? ? ?] | Φ IH H its Φo IHo ];
    cbn; unfold qname_mod; rewrite ?modexp_lets_mems; cbn; lia.
Qed.

Lemma exp_lets_apps : forall M args,
    exp_lets (apps M args) = exp_lets M + List.fold_right (fun N n => exp_lets N + n) 0 args.
Proof. intros M args; revert M; induction args; intros; cbn; [ lia | rewrite IHargs; cbn; lia ]. Qed.

Ltac lets_bound :=
  repeat first
    [ progress rewrite ?gunit_lets_mk, ?ctx_lets_app in *
    | progress cbn [exp_lets modexp_lets binding_lets moddef_lets gmod_lets
                    gentry_lets centry_lets ctx_lets] in * ];
  repeat match goal with
         | Φ : gmod |- _ =>
             lazymatch goal with
             | _ : ctx_lets (body_ctx Φ) <= gmod_lets Φ |- _ => fail
             | _ => pose proof (body_ctx_lets Φ)
             end
         end;
  lia.

(** A term that infers a universe checks against every universe above it: the
    algorithmic counterpart of the universe subtyping rules, against a large
    universe and against a small one at a literal level. *)
Lemma alg_type_check_typ_of : forall Γ A UA (u : universe_nf) i,
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    is_univ_nf UA u ->
    universe_nf_le u (universe_large i) ->
    Γ ⊢a A ⟸ Typeω@i.
Proof.
  intros * HΓ Hi Hu Hle.
  assert (HA : Γ ⊢ A : UA) by (eapply alg_type_infer_sound; eassumption).
  econstructor; [ exact Hi |].
  rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in *.
  apply alg_subtyping_complete.
  destruct u as [L | j]; cbn [universe_nf_tm universe_nf_le] in *.
  - assert (exists k, Γ ⊢ Type⟨lvl_exp_of (fst L) (List.map atom_exp (snd L))⟩ : Typeω@k) as [k Hk]
      by univ_large.
    destruct (wf_univ_lvl_inversion Hk) as [n Hn].
    eapply wf_subtyp_small_large; eassumption.
  - apply wf_subtyp_ge; [ assumption | lia ].
Qed.

Lemma alg_type_check_suniv : forall Γ A UA (u : universe_nf) m,
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    is_univ_nf UA u ->
    universe_nf_le u (universe_nf_lit m) ->
    Γ ⊢a A ⟸ Type⟨𝕃ᵒ m⟩.
Proof.
  intros * HΓ Hi Hu Hle.
  destruct u as [[c xs] | j]; cbn [universe_nf_le universe_nf_lit] in Hle; [| contradiction ].
  (** The inferred universe is a normal form, so its level's atoms are of the
      sorts they carry, below the literal's tier ([lvl_le_lit_sorts]). *)
  assert (HA : Γ ⊢ A : UA) by (eapply alg_type_infer_sound; eassumption).
  pose proof (is_univ_nf_eq _ _ Hu) as EU; cbn [universe_nf_to_nf nf_univ_of fst snd] in EU; subst UA.
  pose proof (alg_type_infer_univ_proof_free HΓ Hi) as Hpf.
  pose proof (alg_type_infer_self HΓ Hi Hpf) as HnA.
  cbn [nf_to_exp] in HA, HnA.
  assert (exists k, Γ ⊢ Type⟨lvl_exp_of c (List.map atom_exp xs)⟩ : Typeω@k) as [k Hk] by univ_large.
  destruct (univ_nf_well_scoped Hk HnA) as (nA & HLA & Hc & Hxs).
  set (N := Nat.max nA (fst m)).
  econstructor; [ exact Hi |].
  rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf.
  apply alg_subtyping_complete.
  cbn [universe_nf_tm fst snd].
  eapply (wf_subtyp_suniv _ _ _ N);
    [ exact HΓ | eapply wf_exp_level_up; [| exact HLA ]; subst N; lia
    | apply wf_llit; [ subst N; lia | exact HΓ ] |].
  assert (HcN : fst c <= N) by (subst N; lia).
  assert (HmN : fst m <= N) by (subst N; lia).
  assert (HxsN : @level_atoms_well_scoped gc_deps gc_stack N Γ xs) by (eapply level_atoms_well_scoped_mono; [| exact Hxs ]; subst N; lia).
  assert (Hcoh : @level_atoms_coherent gc_deps gc_stack Γ (xs ++ nil))
    by (rewrite List.app_nil_r; exact (level_atoms_coherent_proof_free _ _ _ HxsN Hpf)).
  exact (lvl_exp_of_le (n := N) c xs m nil HcN HmN HΓ HxsN I Hcoh Hle).
Qed.

(** A type checked against a small universe infers a small universe, at a canonical
    level below the one [Type⟨t⟩] normalizes to. *)
Lemma alg_type_check_suniv_tm_implies_alg_type_infer_univ : forall {Γ A t},
    ⊢ Γ ->
    Γ ⊢a A ⟸ Type⟨t⟩ ->
    exists L L', Γ ⊢a A ⟹ nf_univ_of L /\ nbe_ty_f Γ Type⟨t⟩ (nf_univ_of L') /\ lvl_le L L'.
Proof.
  intros * HΓ Hcheck.
  destruct (alg_type_check_infer_below HΓ Hcheck) as (A' & B' & Hinfer & Hnbe2 & Hnfsub).
  pose proof Hnbe2 as Hn.
  inversion Hn; subst.
  directed_inversion_by_head eval_exp; subst.
  directed_inversion_by_head read_typ; subst.
  destruct L as [d ys]; unfold nf_univ_of in *; cbn [fst snd] in *.
  inversion Hnfsub; subst; [ refl_case_absurd |].
  exists (c, xs), (d, ys); split; [ exact Hinfer | split; [ exact Hnbe2 | assumption ] ].
Qed.

(** A term checked against a type of levels infers a type of levels of a
    smaller sort: the only normal forms below [Levelⁿ@n] are the [Levelⁿ@m]
    with [m <= n]. *)
Lemma alg_type_check_level_infer : forall {Γ M n},
    ⊢ Γ ->
    Γ ⊢a M ⟸ Level@n ->
    exists m, Γ ⊢a M ⟹ Levelⁿ@m /\ m <= n.
Proof.
  intros * HΓ Hcheck.
  destruct (alg_type_check_infer_below HΓ Hcheck) as (A' & B' & Hinfer & Hnbe2 & Hnfsub).
  inversion Hnbe2; subst.
  directed_inversion_by_head eval_exp; subst.
  directed_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [ refl_case_absurd |].
  eexists; split; [ exact Hinfer | assumption ].
Qed.

(** Conversely, a term that infers a type of levels checks against every
    type of levels of a larger sort. *)
Lemma alg_type_check_level_of : forall {Γ M m n},
    ⊢ Γ ->
    Γ ⊢a M ⟹ Levelⁿ@m ->
    m <= n ->
    Γ ⊢a M ⟸ Level@n.
Proof.
  intros * HΓ Hi Hmn.
  econstructor; [ exact Hi |].
  apply alg_subtyping_complete; cbn [nf_to_exp].
  apply wf_subtyp_level; assumption.
Qed.

(** ** Completeness of the [Π] Rule

    A [Π] whose parts infer universes checks against every type its
    universe ([universe_nf_pi_tm]) is below. *)
Lemma alg_pi_check_of_infer : forall Γ A B UA UB κd (u v : universe_nf) T k,
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    Γ ▹{κd} A ⊢a B ⟹ UB ->
    is_sort_nf UA κd u ->
    is_univ_nf UB v ->
    Γ ⊢ T : Typeω@k ->
    Γ ⊢ universe_nf_pi_tm u v ⊆ T ->
    Γ ⊢a Π{κd} A B ⟸ T.
Proof.
  intros * HΓ HAi HBi Hu Hv HT Hsub.
  assert (HΓA : ⊢ Γ ▹{κd} A)
    by (eapply wf_ctx_extend; [ exact (sort_typed_of_is_sort_nf (alg_type_infer_sound HAi HΓ) Hu) | apply sort_kind_abs_kind_sort ]).
  assert (HnB : nbe_ty_f (Γ ▹{κd} A) UB UB).
  { eapply alg_type_infer_self; [ exact HΓA | eassumption |].
    rewrite (is_univ_nf_eq _ _ Hv) in HBi |- *.
    destruct v as [[c xs] | j]; cbn [universe_nf_to_nf nf_univ_of fst snd] in HBi |- *;
      [ exact (alg_type_infer_univ_proof_free HΓA HBi) | exact I ]. }
  destruct (alg_pi_parts_sound HΓ HAi Hu HBi HnB Hv) as (HA & HB & Hvws).
  destruct (wf_universe_nf_pi_tm HA HB Hvws) as [j Hj].
  destruct (soundness_ty Hj) as [W [HW HeqW]].
  econstructor; [ eapply alg_type_infer_pi; [ eassumption | eassumption | eassumption | exact HnB | constructor; exact Hv
                                            | apply pi_kinds_relevant | exact HW ] |].
  apply alg_subtyping_complete.
  etransitivity; [| exact Hsub ].
  eapply wf_subtyp_refl'; symmetry; exact HeqW.
Qed.

(** The universe of a [Π] of two types below a large universe is below it. *)
Lemma universe_nf_pi_tm_large : forall Γ (u v : universe_nf) i k,
    ⊢ Γ ->
    Γ ⊢ universe_nf_pi_tm u v : Typeω@k ->
    universe_nf_le u (universe_large i) ->
    universe_nf_le v (universe_large i) ->
    Γ ⊢ universe_nf_pi_tm u v ⊆ Typeω@i.
Proof.
  intros * HΓ Hk Hu Hv.
  destruct u as [[c xs] | i1], v as [[d ys] | j1]; cbn [universe_nf_pi_tm universe_nf_le fst snd] in *.
  - destruct (wf_univ_lvl_inversion Hk) as [? ?]; eapply wf_subtyp_small_large; eassumption.
  - destruct xs; cbn [universe_nf_max universe_nf_tm]; apply wf_subtyp_ge; [ exact HΓ | lia | exact HΓ | lia ].
  - destruct ys; cbn [universe_nf_max universe_nf_tm]; apply wf_subtyp_ge; [ exact HΓ | lia | exact HΓ | lia ].
  - cbn [universe_nf_max universe_nf_tm]; apply wf_subtyp_ge; [ exact HΓ | lia ].
Qed.

(** The small [Π] at a level term.  The codomain's universe is below the
    normal form of the weakened level, which is fresh ([nbe_ty_wk_fresh]), so
    the bound of the codomain's level under the binder is below it too
    ([lvl_le_bound_wk]), and the [Π] is at a level below [L]: the domain's is
    below [L] in [Γ], and the codomain's bound below [L[↑]ʷ] in [Γ ▹ A],
    which strengthens.  Every level here is a normal form or an inferred
    universe's level, so its atoms are of the sorts they carry
    ([univ_nf_well_scoped], [soundness_lvl_well_scoped]).  The domain
    infers a sort at the small universe [(c, xs)], with its level and
    atoms well formed: a small universe, or [Prop], at the least level. *)
Lemma alg_pi_small_complete_at : forall Γ L A B n UA κd c xs e zs,
    Γ ⊢ L : Level@n ->
    ⊢ Γ ▹{κd} A ->
    Γ ⊢a A ⟹ UA ->
    is_sort_nf UA κd (universe_small (c, xs)) ->
    nbe_ty_f Γ Type⟨L⟩ (nf_univ_of (e, zs)) ->
    lvl_le (c, xs) (e, zs) ->
    (exists nA, Γ ⊢ lvl_exp_of c (List.map atom_exp xs) : Level@nA /\ fst c <= nA /\
       @level_atoms_well_scoped gc_deps gc_stack nA Γ xs /\ all_list (fun a => ne_proof_free (atom_level a)) xs) ->
    Γ ▹{κd} A ⊢a B ⟸ Type⟨L[↑]ʷ⟩ ->
    Γ ⊢a Π{κd} A B ⟸ Type⟨L⟩.
Proof.
  intros * HL0 HΓA HAi Hs HnL HLA HAws HBc.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (alg_type_check_suniv_tm_implies_alg_type_infer_univ HΓA HBc) as (LB & L' & HBi & HnL' & HLB).
  destruct LB as [d ys], L' as [f ws]; cbn [fst snd] in *.
  (** The inferred universes and the normal forms of universes hold no
      proofs ([alg_type_infer_univ_proof_free], [nbe_ty_univ_proof_free]),
      so the weakened level's normal form avoids the bound variable
      ([nbe_ty_wk_fresh], [nf_ne_fresh_of_outside_proofs]). *)
  assert (HL1 : Γ ▹{κd} A ⊢ L[↑]ʷ : Level@n) by (eapply (wk_preserves_exp _ _ _ _ Level@n); [ exact HL0 | mauto 2 ]).
  pose proof (alg_type_infer_univ_proof_free HΓA HBi) as Hpys.
  assert (HTL : Γ ⊢ Type⟨L⟩ : Typeω@0) by (eapply wf_univ_large_tm; eassumption).
  assert (HTL1 : Γ ▹{κd} A ⊢ Type⟨L[↑]ʷ⟩ : Typeω@0) by (eapply wf_univ_large_tm; eassumption).
  pose proof (nbe_ty_univ_proof_free HTL HnL) as Hpzs.
  pose proof (nbe_ty_univ_proof_free HTL1 HnL') as Hpws.
  assert (HfL' : all_list (fun a => ne_fresh 0 (atom_level a)) ws)
    by exact (proj1 nf_ne_fresh_of_outside_proofs _ Hpws 0 (nbe_ty_wk_fresh _ _ Γ κd A Type⟨L⟩ _ HnL')).
  pose proof (lvl_le_bound_wk 0 (d, ys) (f, ws) Hpys HLB HfL') as HbLB.
  eapply (alg_pi_check_of_infer _ _ _ _ _ κd (universe_small (c, xs)) (universe_small (d, ys)) _ 0);
    [ exact HΓ | exact HAi | exact HBi | exact Hs | constructor | eapply wf_univ_large_tm; eassumption |].
  cbn [universe_nf_pi_tm fst snd]; unfold lvl_bound; cbn [fst snd].
  (** The levels and their atoms, each at its own sort. *)
  assert (HBi' : Γ ▹{κd} A ⊢ B : Type⟨lvl_exp_of d (List.map atom_exp ys)⟩) by (eapply alg_type_infer_sound in HBi; eassumption).
  assert (exists k, Γ ▹{κd} A ⊢ Type⟨lvl_exp_of d (List.map atom_exp ys)⟩ : Typeω@k) as [kB HkB] by univ_large.
  destruct HAws as (nA & HLAe0 & Hc & Hxs & Hpxs).
  destruct (univ_nf_well_scoped HkB (alg_type_infer_self HΓA HBi Hpys)) as (nB & HLBe0 & Hd & Hys).
  pose proof (soundness_lvl_well_scoped HL0 (nbe_ty_univ_level (L := (e, zs)) (n := n) HnL)) as [He Hzs].
  pose proof (soundness_lvl_well_scoped HL1 (nbe_ty_univ_level (L := (f, ws)) (n := n) HnL')) as [Hf Hws].
  cbn [fst snd] in He, Hzs, Hf, Hws.
  assert (HTt : Γ ⊢ Type⟨L⟩ ≈ (nf_univ_of (e, zs) : exp) : Typeω@0)
    by (eapply soundness_ty'; [ eapply wf_univ_large_tm; eassumption | exact HnL ]).
  assert (HTt' : Γ ▹{κd} A ⊢ Type⟨L[↑]ʷ⟩ ≈ (nf_univ_of (f, ws) : exp) : Typeω@0)
    by (eapply soundness_ty'; [ eapply wf_univ_large_tm; eassumption | exact HnL' ]).
  cbn [nf_to_exp nf_univ_of fst snd] in HTt, HTt'.
  apply exp_eq_suniv_tm_inj in HTt as [nT HTt0], HTt' as [nT' HTt'0].
  (** All of them move to the largest of the sorts, one above the
      codomain's, where the bound of its open atoms lives. *)
  set (cb := ordinal_max d (level_atoms_open_bound 0 ys)) in *.
  set (fp := level_atoms_fresh_part 0 ys) in *.
  set (N := S (Nat.max (Nat.max n (Nat.max nA nB)) (Nat.max nT nT'))).
  assert (Hcb : fst cb <= N)
    by (subst cb N; apply ordinal_max_fst_le;
        [ lia | eapply Nat.le_trans; [ apply level_atoms_open_bound_fst; eapply level_atoms_well_scoped_sorts; exact Hys | lia ] ]).
  assert (HxsN : @level_atoms_well_scoped gc_deps gc_stack N Γ xs) by (eapply level_atoms_well_scoped_mono; [| exact Hxs ]; subst N; lia).
  assert (HzsN : @level_atoms_well_scoped gc_deps gc_stack N Γ zs) by (eapply level_atoms_well_scoped_mono; [| exact Hzs ]; subst N; lia).
  assert (HwsN : @level_atoms_well_scoped gc_deps gc_stack N (Γ ▹{κd} A) ws) by (eapply level_atoms_well_scoped_mono; [| exact Hws ]; subst N; lia).
  assert (HysN : @level_atoms_well_scoped gc_deps gc_stack N (Γ ▹{κd} A) ys) by (eapply level_atoms_well_scoped_mono; [| exact Hys ]; subst N; lia).
  assert (HfpN : @level_atoms_well_scoped gc_deps gc_stack N (Γ ▹{κd} A) fp)
    by (apply level_atoms_well_scoped_fresh_part; exact HysN).
  assert (HL : Γ ⊢ L : Level@N) by (eapply wf_exp_level_up; [| exact HL0 ]; subst N; lia).
  assert (HLAe : Γ ⊢ lvl_exp_of c (List.map atom_exp xs) : Level@N) by (eapply wf_exp_level_up; [| exact HLAe0 ]; subst N; lia).
  assert (HTt : Γ ⊢ L ≈ lvl_exp_of e (List.map atom_exp zs) : Level@N) by (eapply wf_exp_eq_level_up; [| exact HTt0 ]; subst N; lia).
  assert (HTt' : Γ ▹{κd} A ⊢ L[↑]ʷ ≈ lvl_exp_of f (List.map atom_exp ws) : Level@N)
    by (eapply wf_exp_eq_level_up; [| exact HTt'0 ]; subst N; lia).
  clear HL0 HLAe0 HTt0 HTt'0.
  set (LAe := lvl_exp_of c (List.map atom_exp xs)) in *.
  set (LBs := lvl_exp_of cb (List.map atom_exp (List.map (map_level_atom (ne_unwk 0)) fp))).
  assert (Hfresh : lvl_exp_of cb (List.map atom_exp fp) = LBs[↑]ʷ)
    by exact (nf_fresh_unwk 0 (nf_lvl cb fp) (level_atoms_fresh_part_fresh 0 ys)).
  assert (HLBl : Γ ▹{κd} A ⊢ LBs[↑]ʷ : Level@N)
    by (rewrite <- Hfresh; apply lvl_exp_of_wf; [ exact Hcb | exact HΓA | apply level_atoms_well_scoped_wf; exact HfpN ]).
  (** The bound holds no proof, the codomain's universe holding none: it
      is the weakening of a level of [Γ] ([level_nf_strengthen]). *)
  assert (HLBs : Γ ⊢ LBs : Level@N)
    by exact (level_nf_strengthen Γ κd A N (nf_lvl cb (List.map (map_level_atom (ne_unwk 0)) fp))
                (level_atoms_unwk_fresh_proof_free 0 cb ys Hpys) HΓA HLBl).
  eapply wf_subtyp_suniv; [ exact HΓ | apply wf_maxl; eassumption | exact HL |].
  apply lvl_sub_maxl_lub; [ exact HLAe | exact HLBs | exact HL | |].
  - (** The domain's level is below [L]. *)
    unfold lvl_sub.
    assert (HcN : fst c <= N) by (subst N; lia).
    assert (HeN : fst e <= N) by (subst N; lia).
    (** the atoms of the two levels hold no proofs *)
    assert (Hcoh : @level_atoms_coherent gc_deps gc_stack Γ (xs ++ zs))
      by (eapply level_atoms_coherent_proof_free; [ apply level_atoms_well_scoped_app; [ exact HxsN | exact HzsN ]
                                                  | apply all_list_app; [ exact Hpxs | exact Hpzs ] ]).
    pose proof (lvl_exp_of_le (n := N) c xs e zs HcN HeN HΓ HxsN HzsN Hcoh HLA) as Hle.
    transitivity (maxl LAe (lvl_exp_of e (List.map atom_exp zs)));
      [ apply wf_exp_eq_maxl_cong; [ mauto 3 | exact HTt ] |].
    transitivity (lvl_exp_of e (List.map atom_exp zs)); [ exact Hle | symmetry; exact HTt ].
  - (** The codomain's bound, below [L[↑]ʷ] in [Γ ▹ A], strengthened. *)
    unfold lvl_sub.
    assert (HfN : fst f <= N) by (subst N; lia).
    (** the atoms of the bound are among the codomain's, which hold no
        proofs, as the weakened level's do not *)
    assert (Hcoh : @level_atoms_coherent gc_deps gc_stack (Γ ▹{κd} A) (fp ++ ws)).
    { eapply (level_atoms_coherent_incl (ys ++ ws));
        [| eapply level_atoms_coherent_proof_free; [ apply level_atoms_well_scoped_app; [ exact HysN | exact HwsN ]
                                                   | apply all_list_app; [ exact Hpys | exact Hpws ] ] ].
      intros j s a Hin; exists j; apply List.in_app_or in Hin as [Hin | Hin];
        apply List.in_or_app; [ left; exact (level_atoms_fresh_part_In _ _ _ _ _ Hin) | right; exact Hin ]. }
    pose proof (lvl_exp_of_le (n := N) cb fp f ws Hcb HfN HΓA HfpN HwsN Hcoh HbLB) as Hle.
    rewrite Hfresh in Hle.
    assert (Hlong : Γ ▹{κd} A ⊢ maxl LBs[↑]ʷ L[↑]ʷ ≈ L[↑]ʷ : Level@N).
    { transitivity (maxl LBs[↑]ʷ (lvl_exp_of f (List.map atom_exp ws)));
        [ apply wf_exp_eq_maxl_cong; [ mauto 3 | exact HTt' ] |].
      transitivity (lvl_exp_of f (List.map atom_exp ws)); [ exact Hle | symmetry; exact HTt' ]. }
    exact (exp_eq_strengthen nil Γ κd A (maxl LBs L) L Level@N ltac:(constructor) HΓA ltac:(mauto 3) HL Hlong).
Qed.

(** The small [Π] over a type of the kind [κd] at the small universe: a
    type of it, or a proposition or a type of levels, which count as the
    least small universe ([is_sort_nf_prop], [is_sort_nf_level]), below
    every level. *)
Lemma alg_pi_small_complete : forall Γ L A B n κd,
    Γ ⊢ L : Level@n ->
    Γ ⊢ A : abs_kind_sort κd Type⟨L⟩ ->
    Γ ⊢a A ⟸ abs_kind_sort κd Type⟨L⟩ ->
    Γ ▹{κd} A ⊢a B ⟸ Type⟨L[↑]ʷ⟩ ->
    Γ ⊢a Π{κd} A B ⟸ Type⟨L⟩.
Proof.
  intros * HL0 HA HAc HBc.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  assert (HT : Γ ⊢ Type⟨L⟩ : Typeω@0) by (eapply wf_univ_large_tm; [ exact HΓ | exact HL0 ]).
  (** the domain is at the sort of its kind at the least large universe *)
  assert (HAl : Γ ⊢ A : abs_kind_sort κd Typeω@0)
    by (destruct κd; cbn [abs_kind_sort] in HA |- *; [ eapply wf_exp_subtyp'; [ exact HA | eapply wf_subtyp_small_large; eassumption ]
                                                     | exact HA | exact HA ]).
  assert (HΓA : ⊢ Γ ▹{κd} A) by (eapply wf_ctx_extend; [ exact HAl | apply sort_kind_abs_kind_sort ]).
  destruct κd; cbn [abs_kind_sort] in HA, HAc.
  - (** a type of the small universe: below its level *)
    destruct (alg_type_check_suniv_tm_implies_alg_type_infer_univ HΓ HAc) as (LA & Lt & HAi & HnL & HLA).
    destruct LA as [c xs], Lt as [e zs].
    eapply alg_pi_small_complete_at; [ exact HL0 | exact HΓA | exact HAi | do 2 constructor | exact HnL | exact HLA | | exact HBc ].
    assert (HAi' : Γ ⊢ A : Type⟨lvl_exp_of c (List.map atom_exp xs)⟩) by (eapply alg_type_infer_sound in HAi; eassumption).
    assert (exists k, Γ ⊢ Type⟨lvl_exp_of c (List.map atom_exp xs)⟩ : Typeω@k) as [kA HkA] by univ_large.
    pose proof (alg_type_infer_univ_proof_free HΓ HAi) as Hpxs.
    destruct (univ_nf_well_scoped HkA (alg_type_infer_self HΓ HAi Hpxs)) as (nA & ? & ? & ?).
    exists nA; repeat split; assumption.
  (** a proposition or a type of levels: at the least small universe *)
  - destruct (nbe_ty_exists_sort (type_sort_universe 0) HT) as [W HW];
      destruct (nbe_ty_univ_term (univ_term_suniv _) HW) as [u ->];
      destruct (nbe_ty_suniv_univ_nf HW) as ([e zs] & -> & _).
    eapply alg_pi_small_complete_at;
      [ exact HL0 | exact HΓA | exact (alg_type_check_prop_infer HΓ HAc) | exact is_sort_nf_prop | exact HW
      | apply lvl_le_zero | | exact HBc ].
    exists 0; split; [ cbn; eapply wf_llit; [ cbn; lia | exact HΓ ] | split; [ cbn; lia | split; exact I ] ].
  - destruct (nbe_ty_exists_sort (type_sort_universe 0) HT) as [W HW];
      destruct (nbe_ty_univ_term (univ_term_suniv _) HW) as [u ->];
      destruct (nbe_ty_suniv_univ_nf HW) as ([e zs] & -> & _).
    eapply alg_pi_small_complete_at;
      [ exact HL0 | exact HΓA | exact (alg_type_check_level_sort_infer HΓ HAc) | exact is_sort_nf_level | exact HW
      | apply lvl_le_zero | | exact HBc ].
    exists 0; split; [ cbn; eapply wf_llit; [ cbn; lia | exact HΓ ] | split; [ cbn; lia | split; exact I ] ].
Qed.

(** Completeness, for terms and for the module judgments at once, since a
    unit's body holds terms and a term may hold a unit.  The global context is
    an index of the judgments, so it is fixed for the induction, as in
    [subtyp_spec]. *)
(** The parts of an eliminator have fewer [let]s than it. *)
Lemma elim_lets_parts : forall r p Us m Bks M,
    (forall U, List.In U Us -> exp_lets U < exp_lets (a_elim r p Us m Bks M)) /\
    (forall b, List.In b Bks -> exp_lets (eb_scrutinee_type b) < exp_lets (a_elim r p Us m Bks M)) /\
    (forall b, List.In b Bks -> exp_lets (eb_motive b) < exp_lets (a_elim r p Us m Bks M)) /\
    (forall b br, List.In b Bks -> List.In br (eb_brs b) -> exp_lets (snd br) < exp_lets (a_elim r p Us m Bks M)) /\
    exp_lets M < exp_lets (a_elim r p Us m Bks M).
Proof.
  intros; cbn [exp_lets].
  set (ul := (fix us_lets (Us : list exp) : nat :=
                match Us with nil => 0 | U :: Us' => exp_lets U + us_lets Us' end) Us).
  set (brl := fix brs_lets (Bs : list (String.string * nat * exp)) : nat :=
                match Bs with nil => 0 | b :: Bs' => exp_lets (snd b) + brs_lets Bs' end).
  set (bl := (fix blocks_lets (Bks : list eblock) : nat :=
                match Bks with
                | nil => 0
                | eb_mk _ Z A Bs :: Bks' => exp_lets Z + exp_lets A + brl Bs + blocks_lets Bks'
                end) Bks).
  assert (HU : forall U, List.In U Us -> exp_lets U <= ul).
  { unfold ul; clear; induction Us as [| U' Us IH]; intros U HU; cbn in HU |- *; [ contradiction |].
    destruct HU as [-> | HU]; [ lia | specialize (IH _ HU); lia ]. }
  assert (Hbr : forall Bs br, List.In br Bs -> exp_lets (snd br) <= brl Bs).
  { induction Bs as [| br' Bs IH]; intros br Hin; cbn in Hin |- *; [ contradiction |].
    destruct Hin as [-> | Hin]; [ lia | specialize (IH _ Hin); lia ]. }
  assert (HB : forall b, List.In b Bks ->
             exp_lets (eb_scrutinee_type b) + exp_lets (eb_motive b) + brl (eb_brs b) <= bl).
  { unfold bl; clear -Hbr; induction Bks as [| [nm Z A Bs] Bks IH]; intros b Hb; cbn in Hb |- *; [ contradiction |].
    destruct Hb as [<- | Hb]; cbn; [ lia | specialize (IH _ Hb); lia ]. }
  split; [ intros U HU'; specialize (HU _ HU'); lia | split; [| split; [| split ] ] ].
  - intros b Hb; specialize (HB _ Hb); lia.
  - intros b Hb; specialize (HB _ Hb); lia.
  - intros b br Hb Hbr'; specialize (HB _ Hb); specialize (Hbr _ _ Hbr'); lia.
  - lia.
Qed.

(** A monotone property with a witness below each [j < n] has one witness
    for them all. *)
Lemma nat_bound_upto : forall (Q : nat -> nat -> Prop) n,
    (forall j, j < n -> exists l, Q j l) -> (forall j l l', l <= l' -> Q j l -> Q j l') ->
    exists L, forall j, j < n -> Q j L.
Proof.
  intros Q n; induction n as [| n IH]; intros Hex Hmon; [ exists 0; intros; lia |].
  destruct IH as [L HL]; [ intros j Hj; apply Hex; lia | exact Hmon |].
  destruct (Hex n ltac:(lia)) as [l Hl].
  exists (max L l); intros j Hj.
  destruct (Nat.eq_dec j n) as [-> | Hne]; [ eapply Hmon; [| exact Hl ]; lia | eapply Hmon; [| apply HL; lia ]; lia ].
Qed.

(** Normal forms, position by position, give [nfs_agree]. *)
Lemma nfs_agree_of_nth : forall Γ Ms Rs Ts,
    List.length Ms = List.length Ts -> List.length Rs = List.length Ts ->
    (forall j M R T, List.nth_error Ms j = Some M -> List.nth_error Rs j = Some R -> List.nth_error Ts j = Some T ->
       exists W W', nbe_f Γ M T W /\ nbe_f Γ R T W' /\ nf_eq_upto_proofs W W') ->
    nfs_agree Γ Ms Rs Ts.
Proof.
  induction Ms as [| M Ms IH]; intros [| R Rs] [| T Ts] HMl HRl H; cbn in HMl, HRl; try discriminate; [ constructor |].
  destruct (H 0 M R T eq_refl eq_refl eq_refl) as (W & W' & HMW & HRW & E).
  econstructor; [ exact HMW | exact HRW | exact E |].
  apply IH; [ lia | lia | intros j M' R' T' HM' HR' HT'; exact (H (S j) M' R' T' HM' HR' HT') ].
Qed.

(** The eliminator, from the derivation's premises at the parameters [Ps]
    and the algorithm's for its parts: the scrutinee infers the type former
    the member's type is headed by, at parameters equal to the
    derivation's ([subtyp_ind_nf]), whose uniform ones the member's
    uniform arguments normalize to, and whose others are the member's
    non-uniform ones ([mty_params_conv], [mty_params_inj]); the scrutinee
    types and the motives are checked at one universe above them all
    ([nat_bound_upto]).  A scrutinee type is equal to its member's type
    ([blocks_typed_scrutinee_type]), at a large universe. *)
Lemma alg_elim_complete : forall Γ p D m Mm bm Bks Ps M r i,
    ind_lookup gc_deps gc_stack p = Some D -> ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm ->
    List.length Ps = im_np D Mm ->
    (forall j P T, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T -> Γ ⊢ P : T) ->
    Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Γ ⊢a M ⟸ ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    blocks_typed gc_deps gc_stack Γ p D (List.firstn (ind_nu D) Ps) Bks r i ->
    (forall j U T, List.nth_error (List.firstn (ind_nu D) Ps) j = Some U ->
       List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) j = Some T -> Γ ⊢a U ⟸ T) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       exists UZ u, tele_sub (im_nparams Mj) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ++ Γ ⊢a eb_scrutinee_type b ⟹ UZ /\
         is_sort_nf UZ ak_relevant u) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       elim_mctx p D j Mj (List.firstn (ind_nu D) Ps) ++ Γ ⊢a eb_motive b ⟸ abs_kind_sort r Typeω@i) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       elim_bctx r p D Mj gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ
         ⊢a B ⟸ elim_branch_type p D j Mj c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    Γ ⊢a a_elim r p (List.firstn (ind_nu D) Ps) m Bks M
       ⟸ (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros * Hl Hm Hb HPl HPt HMe HMc HBt HUc HZc HAc HBc.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hgw; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  set (Us := List.firstn (ind_nu D) Ps) in *; set (NsP := List.skipn (ind_nu D) Ps) in *.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNPl : List.length NsP = im_nn Mm) by (unfold NsP; rewrite List.length_skipn; unfold im_np in HPl; lia).
  destruct (params_typed_split _ _ D Hc _ _ _ Ps Hm HPl HPt) as [HUt HNPt]; fold Us NsP in HUt, HNPt.
  destruct (im_ref p m Mm) as [pc k] eqn:Hr.
  destruct (im_ref_lookup _ _ _ _ _ _ _ HΓ Hl Hm Hr) as [Dq Hlq].
  destruct (im_ref_member _ _ _ _ _ _ _ _ HΓ Hl Hm Hr Hlq) as [Mk Hk].
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
  pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ HD)) as Hsuf.
  pose proof (block_member_not_rview _ _ _ _ _ Hsuf (blocks_typed_len _ _ _ _ _ _ _ _ _ HBt) Hm Hb) as Hnr.
  assert (Emty : forall Us' Ns', ind_mty p D m Us' Ns' = apps (a_ind pc k) (im_pre Mm Us' ++ Ns'))
    by (intros; unfold ind_mty; rewrite Hm; unfold im_ty_at;
        destruct (im_head Mm) eqn:Hh0; [ rewrite Hr; reflexivity | rewrite Hr; reflexivity |];
        exfalso; unfold im_is_rview in Hnr; rewrite Hh0 in Hnr; discriminate).
  destruct (im_pre_params_typed _ _ _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hnr Hr Hlq Hk HUl HUt HNPl HNPt) as [HXl HXt].
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hnr Hr Hlq HUl HUt) as [HPrl HPrt].
  (** The scrutinee infers the type former at parameters equal to the
      derivation's. *)
  inversion HMc as [? W ? ? HMi HMs]; subst.
  pose proof (alg_type_infer_sound HMi HΓ) as HMW.
  destruct (presup_exp_typ_sorted HMe ltac:(rewrite Emty; apply apps_exp_not_level_sort; discriminate)) as (SP & HSP & HPs).
  destruct (alg_infer_below_sorted HΓ HSP HPs HMi HMs) as (SW & HSW & HWt).
  assert (HWs : Γ ⊢ (W : exp) ⊆ ind_mty p D m Us NsP) by exact (alg_subtyping_sound_sort _ _ _ _ _ HSW HSP HMs HWt HPs).
  rewrite Emty in HWs.
  (** The inferred type is equal up to proofs to its normal form, a type
      former at parameters, so it is one. *)
  destruct (alg_type_infer_self_upto HΓ HMi) as (W' & HWW & EW).
  destruct (subtyp_ind_nf HWs Hlq Hk HXl HXt HWW) as (Rs' & -> & HRl' & _).
  destruct W; try (unfold nf_eq_upto_proofs in EW; cbn in EW; discriminate).
  apply nf_indty_upto_proofs_inv in EW as (<- & <- & ERs).
  rename l into Rs.
  assert (HRl : List.length (List.map nf_to_exp Rs) = im_np Dq Mk)
    by (rewrite List.length_map, (nfs_eq_upto_proofs_length _ _ ERs); exact HRl').
  clear Rs' HRl' ERs HWW.
  cbn [nf_to_exp] in HWt, HWs, HMW.
  pose proof (wf_ind_apps_inv _ _ _ _ _ _ _ Hlq Hk HWt HRl) as HRt.
  (** The two type formers are equal, so their parameters are, position
      by position ([exp_eq_ind_apps_inv]). *)
  destruct (subtyp_ind_inv HWs) as (SR & HSR & HeqR0).
  destruct (ind_apps_typed_large HSW HWt) as [kW HWl].
  destruct (exp_eq_sort_large HSR HeqR0 (or_introl HWl)) as [kk HeqR1].
  destruct (exp_eq_ind_apps_inv _ _ _ _ _ _ _ _ Hlq Hk (wf_exp_eq_sym _ _ _ _ _ _ HeqR1) HXl HRl HXt HRt) as [_ HXR].
  assert (Hti : tele_insts (im_params Dq Mk) Id (im_pre Mm Us ++ NsP)
               = tele_insts (ind_uparams Dq) Id (im_pre Mm Us) ++ tele_insts (im_nparams Mk) (sb_of_list Id (im_pre Mm Us)) NsP)
    by (unfold im_params; apply tele_insts_app; [ exact (decl_closed_ass _ Hcq) | exact HPrl ]).
  assert (Hl1 : List.length (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) = ind_nu Dq)
    by (rewrite length_tele_insts by exact (decl_closed_ass _ Hcq); rewrite HPrl; unfold ind_nu in *; lia).
  assert (HPR : forall j N R T, List.nth_error (im_pre Mm Us) j = Some N -> List.nth_error (List.map nf_to_exp Rs) j = Some R ->
             List.nth_error (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) j = Some T -> Γ ⊢ N ≈ R : T).
  { intros j N R T HN HR HT.
    assert (Hj : j < ind_nu Dq) by (rewrite <- HPrl; apply List.nth_error_Some; congruence).
    apply (HXR j); [ rewrite List.nth_error_app1 by lia; exact HN | exact HR | rewrite Hti, List.nth_error_app1 by lia; exact HT ]. }
  assert (Hag : nfs_agree Γ (im_pre Mm Us) (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) (tele_insts (ind_uparams Dq) Id (im_pre Mm Us))).
  { apply nfs_agree_of_nth; [ lia | rewrite List.length_firstn; unfold im_np in HRl; lia |].
    intros j N R T HN HR HT.
    assert (Hj : j < ind_nu Dq) by (rewrite <- HPrl; apply List.nth_error_Some; congruence).
    rewrite List.nth_error_firstn in HR; destruct (Nat.ltb_spec j (ind_nu Dq)); [| discriminate ].
    exact (completeness (HPR _ _ _ _ HN HR HT)). }
  (** The rest of the inferred parameters are the member's non-uniform
      ones, equal to the derivation's. *)
  destruct (mty_params_conv _ _ _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hnr Hr Hlq Hk HUl HUt HRl HRt HPR) as [HNl HNt [iE HE]].
  set (Ns :=List.skipn (ind_nu Dq) (List.map nf_to_exp Rs)) in *.
  pose proof HeqR1 as HeqR; clear SR HSR HeqR0 HeqR1.
  rewrite <- Emty in HeqR.
  assert (HmE : Γ ⊢ ind_mty p D m Us NsP ≈ ind_mty p D m Us Ns : Typeω@(max kk iE))
    by (etransitivity; [ symmetry; eapply lift_exp_eq_max_left; exact HeqR | eapply lift_exp_eq_max_right; exact HE ]).
  pose proof (mty_params_inj _ _ _ _ _ _ _ _ _ Hl Hm HUl HUt HNPl HNl HNPt HNt HmE) as HNN.
  clear HmE HeqR HE HWs HMs HXR HPR Hti Hl1 HXt HXl HRt HMW HWt HPs.
  pose proof (params_typed_join _ _ D Hc _ _ _ Us Ns Hm HUl HUt HNt) as HPt'.
  assert (HPl' : List.length (Us ++ Ns) = im_np D Mm) by (rewrite List.length_app, HUl, HNl; unfold im_np; lia).
  assert (HPP : forall j P P' T, List.nth_error Ps j = Some P -> List.nth_error (Us ++ Ns) j = Some P' ->
             List.nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T -> Γ ⊢ P ≈ P' : T).
  { intros j P P' T HP HP' HT.
    assert (EPs : Ps = Us ++ NsP) by (unfold Us, NsP; symmetry; apply List.firstn_skipn).
    rewrite EPs in HP, HT.
    unfold im_params in HT; rewrite tele_insts_app in HT by (try exact (decl_closed_ass _ Hc); exact HUl).
    assert (Hl1 : List.length (tele_insts (ind_uparams D) Id Us) = ind_nu D)
      by (rewrite length_tele_insts by exact (decl_closed_ass _ Hc); rewrite HUl; unfold ind_nu in *; lia).
    destruct (Nat.lt_ge_cases j (ind_nu D)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HP, HP', HT by lia; rewrite HP in HP'; injection HP' as <-.
      apply wf_exp_eq_refl; exact (HUt _ _ _ HP HT).
    - rewrite List.nth_error_app2 in HP, HP', HT by lia; rewrite HUl in HP, HP'; rewrite Hl1 in HT.
      exact (HNN _ _ _ _ HP HP' HT). }
  (** So the motive's instance is the derivation's. *)
  destruct (wf_elim_params_conv _ _ _ _ _ _ _ _ _ _ r i Hl Hm Hb HPl HPt HPl' HPt' HPP HMe HBt) as (_ & _ & Hmot).
  rewrite skipn_app_len in Hmot by exact HUl; fold NsP in Hmot.
  clear HPP HPt' HNN.
  (** One universe for the scrutinee types and the motives. *)
  assert (HΨ : forall j Mj, ind_member D j = Some Mj -> ⊢ (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list).
  { intros j Mj Hj; pose proof (ext_eq_ctx_left _ _ _ _ _ (blocks_typed_mctx _ _ _ _ _ _ _ _ _ HBt _ _ Hj)) as HC.
    unfold elim_mctx in HC; cbn [List.app] in HC; exact (proj1 (ctx_decomp HC)). }
  assert (Hmono : forall Δ A l l', ⊢ Δ -> l <= l' -> Δ ⊢a A ⟸ Typeω@l -> Δ ⊢a A ⟸ Typeω@l').
  { intros Δ A l l' HΔ Hll HA; destruct (Nat.eq_dec l l') as [<- | Hne]; [ exact HA |].
    eapply alg_type_check_subtyp; [ exact HA | apply wf_subtyp_univ; [ exact HΔ | lia ] ]. }
  (** A scrutinee type is of a large universe and mutually below its
      member's type ([blocks_typed_scrutinee_type]). *)
  assert (HZh : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             ext_eq_ass_head gc_deps gc_stack Γ (tele_sub (im_nparams Mj) (sb_of_list Id Us))
               (tele_sub (im_nparams Mj) (sb_of_list Id Us)) ak_relevant (eb_scrutinee_type b)
               (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj))))
    by (intros j Mj b Hj Hbj; apply ext_eq_ass_inv; exact (blocks_typed_scrutinee_type _ _ _ _ _ _ _ _ _ HBt _ _ _ Hj Hbj)).
  destruct (nat_bound_upto (fun j l => forall Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
              (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢a eb_scrutinee_type b ⟸ Typeω@l)
              (List.length Bks)) as [L HL].
  { intros j _.
    destruct (ind_member D j) as [Mj |] eqn:Hj; [| exists 0; intros; discriminate ].
    destruct (List.nth_error Bks j) as [b |] eqn:Hbj; [| exists 0; intros; discriminate ].
    destruct (HZc _ _ _ Hj Hbj) as (UZ & u & HZi & Hs).
    inversion Hs as [? ? Hu | |]; subst.
    exists (universe_nf_large_index u); intros Mj' b' Hj' Hb'.
    assert (Mj' = Mj) as -> by congruence; assert (b' = b) as -> by congruence.
    eapply alg_type_check_typ_of; [ exact (HΨ _ _ Hj) | exact HZi | exact Hu | apply universe_nf_le_large ]. }
  { intros j l l' Hll HQ Mj b Hj Hbj; eapply Hmono; [ exact (HΨ _ _ Hj) | exact Hll | exact (HQ _ _ Hj Hbj) ]. }
  set (i' := max i L).
  (** The type, the normal form of the motive's instance. *)
  pose proof (type_sort_kind_universe r i) as HSr.
  assert (HTt : Γ ⊢ (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)] : abs_kind_sort r Typeω@i) by (gen_presups; assumption).
  destruct (nbe_ty_exists_sort HSr HTt) as (T & HnT).
  pose proof (soundness_ty_at_sort HSr HTt HnT) as HTe.
  econstructor.
  - eapply alg_type_infer_elim with (p := p) (D := D) (Mm := Mm) (Dq := Dq) (Mk := Mk) (bm := bm) (i := i'); try eassumption; try reflexivity.
    + exact (blocks_typed_len _ _ _ _ _ _ _ _ _ HBt).
    + exact (blocks_typed_binder_count _ _ _ _ _ _ _ _ _ HBt).
    + intros j Mj b Hj Hbj.
      assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence).
      eapply (Hmono _ _ L); [ exact (HΨ _ _ Hj) | unfold i'; lia | exact (HL j Hjl _ _ Hj Hbj) ].
    + intros j Mj b Hj Hbj.
      destruct (HZh _ _ _ Hj Hbj) as [_ _ _ _ _ _ _ HZH HHZ].
      exact (nbe_ty_of_mutual_subtyp HZH HHZ).
    + intros j Mj b Hj Hbj; destruct (blocks_typed_kind _ _ _ _ _ _ _ _ _ HBt); cbn [abs_kind_sort] in *;
        [| exact (HAc _ _ _ Hj Hbj) ].
      eapply (Hmono _ _ i);
        [ exact (ext_eq_ctx_left _ _ _ _ _ (blocks_typed_mctx _ _ _ _ _ _ _ _ _ HBt _ _ Hj)) | unfold i'; lia | exact (HAc _ _ _ Hj Hbj) ].
    + exact (blocks_typed_names _ _ _ _ _ _ _ _ _ HBt).
    + exact (blocks_typed_counts _ _ _ _ _ _ _ _ _ HBt).
    + exact (blocks_typed_kind _ _ _ _ _ _ _ _ _ HBt).
  - apply alg_subtyping_complete.
    assert (HE : Γ ⊢ T ≈ (eb_motive bm)[sb_of_list Id (NsP ++ M :: nil)] : abs_kind_sort r Typeω@i)
      by (etransitivity; [ symmetry; exact HTe | symmetry; exact Hmot ]).
    exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ (presup_exp_eq_left HE) (presup_exp_eq_right HE) HSr HE)).
Qed.

(** ** Extensions Entry by Entry

    Completeness for an extension is stated for each of its entries, under
    the bound on that entry's lets: a body's expansion has entries its local
    opens generate, whose types are the targets' member types, which the
    body's own lets do not bound; the algorithm does not check them again. *)

Definition alg_entry (Γ : ctx) (e : centry) : Prop :=
  match e with
  | ce_ass κ A => exists UA u, Γ ⊢a A ⟹ UA /\ is_sort_nf UA κ u
  | ce_def A M => (exists UA r u, Γ ⊢a A ⟹ UA /\ is_sort_nf UA r u) /\ Γ ⊢a M ⟸ A
  | ce_mod U => Γ ⊢aᵘ U
  | ce_dm A M U => ((exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ Γ ⊢a M ⟸ A) /\ Γ ⊢aᵘ U
  end.

Definition ext_entries (n : nat) (Γ Ψ : ctx) : Prop :=
  forall Ψ2 e Ψ1, Ψ = Ψ2 ++ e :: Ψ1 -> centry_lets e <= n -> alg_entry (Ψ1 ++ Γ) e.

Lemma ext_entries_nil : forall n Γ, ext_entries n Γ nil.
Proof. intros n Γ [| ? ?] * H; discriminate. Qed.

Lemma ext_entries_cons : forall n Γ Ψ e, ext_entries n Γ Ψ ->
    (centry_lets e <= n -> alg_entry (Ψ ++ Γ) e) -> ext_entries n Γ (e :: Ψ).
Proof.
  intros * Ht He [| e2 Ψ2] e' Ψ1 Heq Hle; cbn in Heq; injection Heq as -> Heq; [ subst; exact (He Hle) |].
  exact (Ht _ _ _ Heq Hle).
Qed.

Lemma ext_entries_app_r : forall n Γ Ψ2 Ψ, ext_entries n Γ (Ψ2 ++ Ψ) -> ext_entries n Γ Ψ.
Proof. intros * Hx Ψ3 e Ψ1 -> Hle; apply (Hx (Ψ2 ++ Ψ3)); [ rewrite <- List.app_assoc; reflexivity | exact Hle ]. Qed.

Lemma ext_entries_head : forall n Γ Ψ e, ext_entries n Γ (e :: Ψ) -> centry_lets e <= n -> alg_entry (Ψ ++ Γ) e.
Proof. intros * Hx Hle; exact (Hx nil e Ψ eq_refl Hle). Qed.

Lemma ext_entries_alg : forall n Γ Ψ, ext_entries n Γ Ψ -> ctx_lets Ψ <= n -> Γ ⊢aˣ Ψ.
Proof.
  intros n Γ; induction Ψ as [| e Ψ IH]; intros Hx Hl; [ constructor |]; cbn [ctx_lets] in Hl.
  pose proof (ext_entries_head _ _ _ _ Hx ltac:(lia)) as He.
  pose proof (IH (ext_entries_app_r _ _ (e :: nil) _ Hx) ltac:(lia)) as Ht.
  destruct e; cbn [alg_entry] in He; destruct_all;
    [ eapply alg_ext_ass | eapply alg_ext_def | eapply alg_ext_mod | eapply alg_ext_dm ]; eauto.
Qed.

(** [body_tagged Γ Φ]: the type of every term part of the body [Φ] over
    [Γ] is, in the context of the entries before it, of the sort its
    relevance tag says ([entry_kind]). *)
Definition body_tagged (Γ : ctx) (Φ : gmod) : Prop :=
  forall y Φ0 E A M, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
    exists i, (body_ctx Φ0 ++ Γ)%list ⊢ A : abs_kind_sort (entry_kind E) Typeω@i.

(** A name a body finds is one of its names. *)
Lemma gm_prefix_upto_in : forall Φ y Φ', gm_prefix_upto Φ y = Some Φ' -> List.In y (gm_names Φ).
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its Φg IHg]; intros y Φ' Hp; cbn in Hp |- *; [ discriminate | |].
  - destruct (String.eqb_spec y x) as [-> | _]; [ left; reflexivity | right; exact (IH _ _ Hp) ].
  - destruct (List.existsb _ _); [ discriminate | apply List.in_or_app; right; exact (IH _ _ Hp) ].
Qed.

(** Entries generated under names other than [y] do not hide what [y]
    names. *)
Lemma gm_prefix_upto_gens : forall gs Φ k y, ~ List.In y (List.map generated_item_name gs) ->
    gm_prefix_upto (gens_append Φ k gs) y = gm_prefix_upto Φ y.
Proof.
  induction gs as [| g gs IH]; intros Φ k y Hy; cbn [gens_append]; [ reflexivity |].
  cbn [List.map List.In] in Hy.
  unfold generated_item_name in Hy; destruct (generated_item_entry g) as [d E] eqn:Eg; cbn [fst] in Hy.
  rewrite IH by tauto; cbn [gm_prefix_upto].
  destruct (String.eqb_spec y d) as [-> | _]; [ tauto | reflexivity ].
Qed.

(** The tags of a body hold of its prefix before an entry of a fresh name. *)
Lemma body_tagged_ext_inv : forall Γ Φ x E, body_tagged Γ (gm_ext Φ x E) -> ~ List.In x (gm_names Φ) -> body_tagged Γ Φ.
Proof.
  intros * HT Hx y Φ0 E0 A M Hp HE; apply (HT y Φ0 E0 A M); [| exact HE ]; cbn [gm_prefix_upto].
  destruct (String.eqb_spec y x) as [-> | _]; [ exfalso; exact (Hx (gm_prefix_upto_in _ _ _ Hp)) | exact Hp ].
Qed.

(** The two parts of a list without repetition are disjoint. *)
Lemma nodup_app_disjoint : forall {X : Type} (l l' : list X) a, List.NoDup (l ++ l') -> List.In a l -> ~ List.In a l'.
Proof.
  induction l as [| x l IH]; intros l' a Hnd Hin Hin'; [ exact Hin |].
  cbn [List.app] in Hnd; apply List.NoDup_cons_iff in Hnd as [Hx Hnd].
  destruct Hin as [-> | Hin]; [ apply Hx, List.in_or_app; right; exact Hin' | exact (IH _ _ Hnd Hin Hin') ].
Qed.

(** The same before the entries an open generates, under fresh names. *)
Lemma body_tagged_gens_inv : forall Γ Φ gs, body_tagged Γ (gens_append Φ 0 gs) ->
    List.NoDup (gm_names (gens_append Φ 0 gs)) -> body_tagged Γ Φ.
Proof.
  intros * HT Hnd y Φ0 E A M Hp HE; apply (HT y Φ0 E A M); [| exact HE ].
  rewrite gm_prefix_upto_gens; [ exact Hp |].
  rewrite gens_append_names in Hnd.
  intros Hin; apply List.in_rev in Hin.
  exact (nodup_app_disjoint _ _ y Hnd Hin (gm_prefix_upto_in _ _ _ Hp)).
Qed.

(** A type of the sorts of two kinds is of one kind ([subtyp_same_kind]
    at the reflexive subtyping). *)
Lemma kind_sort_agree : forall Γ A r r' i j,
    Γ ⊢ A : abs_kind_sort r Typeω@i -> Γ ⊢ A : abs_kind_sort r' Typeω@j -> r = r'.
Proof.
  intros * H H'.
  assert (Hs : Γ ⊢ A ⊆ A)
    by (eapply wf_subtyp_refl; [ exact H | apply type_sort_kind_universe | apply wf_exp_eq_refl; exact H ]).
  exact (subtyp_same_kind _ _ _ r r' i j Hs H H').
Qed.

(** The entries of an expanded body are of their tagged sorts in the
    context the body before each makes, once each, filled in, is of the
    sort the tag names: the type is of a sort before it, which filling in
    keeps, and no type is of both sorts ([typ_prop_absurd]). *)
Lemma body_tagged_of_fill : forall Γ0 Φx (entry_sort : String.string -> exp),
    gm_nopens Φx = 0 -> body_shape Φx Φx -> ⊢ body_ctx Φx ++ Γ0 ->
    (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       sort_kind (entry_sort y) (entry_kind E)) ->
    (forall y Φ0 E A M σ, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_fill Φ0 = Some σ -> Γ0 ⊢ A[σ] : entry_sort y) ->
    body_tagged Γ0 Φx.
Proof.
  intros * Hn Hs HC Htag Hfill y Φ0 E A M Hp HE.
  destruct (sort_kind_abs_kind_sort_inv _ _ (Htag _ _ _ _ _ Hp HE)) as [i Hi].
  destruct (fill_prefix _ _ _ _ (proj1 (body_shape_fill _ _ Hn Hs)) Hp) as [σ Hσf].
  pose proof (Hfill _ _ _ _ _ _ Hp HE Hσf) as HAσ; rewrite Hi in HAσ.
  destruct (prefix_body_ctx _ _ _ Hn Hp) as [X HX].
  rewrite HX, <- List.app_assoc in HC.
  pose proof (ctx_app_wf_tail _ _ _ _ HC) as HC0.
  (** The entry's type is of a sort, in the context before it. *)
  assert (HAS : ⊢ body_ctx Φ0 ++ Γ0 /\ exists Srt, type_sort Srt /\ body_ctx Φ0 ++ Γ0 ⊢ A : Srt).
  { destruct E as [b pv r A' [M' |] | | | pv A' M' U |]; cbn in HE; try discriminate; injection HE as <- <-;
      cbn [body_ctx List.app] in HC0.
    - destruct (ctx_decomp_def HC0) as (HΓ & _ & _); split; [ exact HΓ | exact (ctx_decomp_def_sorted HC0) ].
    - destruct (ctx_decomp_dm HC0) as (HΓ & [k HA'] & _ & _); split; [ exact HΓ |].
      exists Typeω@k; split; [ constructor | exact HA' ]. }
  destruct HAS as (HΓ0 & Srt & HS & HA0).
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HA0 HS (wf_gm_fill _ _ _ _ _ HΓ0 Hσf)) as HAσ'.
  (** the sort is the sort of a kind, which the filled-in type fixes *)
  assert (exists κ j, Srt = abs_kind_sort κ Typeω@j) as (κ & j & ->)
    by (destruct HS as [j | |]; [ exists ak_relevant, j | exists ak_propositional, 0 | exists ak_level, 0 ]; reflexivity).
  pose proof (kind_sort_agree _ _ _ _ _ _ HAσ' HAσ) as ->.
  exists j; exact HA0.
Qed.

(** The same, read off the premises of a unit rule, which fill in an entry
    together with the entry of the same name on the other side. *)
Lemma body_tagged_of_fill_left : forall Γ0 Φx Φx' (entry_sort : String.string -> exp),
    gm_nopens Φx = 0 -> body_shape Φx Φx' -> ⊢ body_ctx Φx ++ Γ0 ->
    (forall y Φ0 E A M, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       sort_kind (entry_sort y) (entry_kind E)) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Γ0 ⊢ A[σ] : entry_sort y) ->
    body_tagged Γ0 Φx.
Proof.
  intros * Hn Hs HC Htag Hfill.
  destruct (body_shape_refl _ _ Hs) as (Hs1 & _ & _).
  apply (body_tagged_of_fill _ _ entry_sort Hn Hs1 HC Htag).
  intros y Φ0 E A M σ Hp HE Hσ.
  destruct (shape_prefix _ _ _ _ _ Hs Hp) as (Φ0' & E' & Hp' & Hs0 & HsE).
  destruct (entry_shape_tm _ _ _ _ HsE HE) as (A' & M' & HE').
  destruct (gm_fill Φ0') as [σ' |] eqn:Hσ'; [ exact (Hfill _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hσ Hσ') |].
  pose proof (prefix_nopens _ _ _ Hn Hp) as Hn0; cbn [gm_nopens] in Hn0.
  exfalso; exact (proj2 (body_shape_fill _ _ Hn0 Hs0) Hσ').
Qed.

(** The other side's. *)
Lemma body_tagged_of_fill_right : forall Γ0 Φx Φx' (entry_sort : String.string -> exp),
    gm_nopens Φx' = 0 -> body_shape Φx Φx' -> ⊢ body_ctx Φx' ++ Γ0 ->
    (forall y Φ0' E' A' M', gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       sort_kind (entry_sort y) (entry_kind E')) ->
    (forall y Φ0 E A M Φ0' E' A' M' σ σ',
       gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
       gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
       gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' -> Γ0 ⊢ A'[σ'] : entry_sort y) ->
    body_tagged Γ0 Φx'.
Proof.
  intros * Hn' Hs HC Htag Hfill.
  destruct (body_shape_refl _ _ Hs) as (_ & Hs2 & _).
  apply (body_tagged_of_fill _ _ entry_sort Hn' Hs2 HC Htag).
  intros y Φ0' E' A' M' σ' Hp' HE' Hσ'.
  destruct (shape_prefix _ _ _ _ _ (body_shape_sym _ _ Hs) Hp') as (Φ0 & E & Hp & Hs0 & HsE).
  destruct (entry_shape_tm _ _ _ _ HsE HE') as (A & M & HE).
  destruct (gm_fill Φ0) as [σ |] eqn:Hσ; [ exact (Hfill _ _ _ _ _ _ _ _ _ _ _ Hp HE Hp' HE' Hσ Hσ') |].
  pose proof (prefix_nopens _ _ _ Hn' Hp') as Hn0; cbn [gm_nopens] in Hn0.
  exfalso; exact (proj2 (body_shape_fill _ _ Hn0 Hs0) Hσ).
Qed.

(** A body checked from its expansion's entries: its own entries are
    bounded by its lets; those its opens generate are not looked at.  A
    definition is checked at the sort its tag says, which the entry's
    type has ([body_tagged]); the names are distinct, so each entry is
    the one its name finds. *)
Lemma alg_body_of_entries : forall n Γ0 Δ Φ Φx, body_xp gc_deps gc_stack (Δ ++ Γ0) Φ Φx ->
    ext_entries n Γ0 (body_ctx Φx ++ Δ) -> gmod_lets Φ <= n -> body_shape Φ Φ ->
    List.NoDup (gm_names Φx) -> body_tagged (Δ ++ Γ0) Φx ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> S (modexp_lets H) <= n -> Ψ ++ Δ ++ Γ0 ⊢aᵐ H) ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> frame_free_target gc_deps gc_stack (Ψ ++ Δ ++ Γ0) H) ->
    Δ ++ Γ0 ⊢aᵇ Φ ⇝ Φx.
Proof.
  intros * Hx; remember (Δ ++ Γ0) as G eqn:HG; revert HG.
  induction Hx as [G | G Φ Φx x E Hx IH | G Φ Φx H its Φg R Rm gs Hx IH HR HRm Hg Hok HΦg];
    intros -> HE Hl Hs Hnd Htg Ho Hof; cbn [gmod_lets] in Hl.
  - constructor.
  - cbn [body_shape] in Hs; destruct Hs as (Hs & _ & HsE).
    cbn [gm_names] in Hnd; apply List.NoDup_cons_iff in Hnd as [Hx' Hnd].
    assert (HEt : ext_entries n Γ0 (body_ctx Φx ++ Δ)).
    { destruct E as [? ? ? ? [] | | | | ]; cbn [body_ctx List.app] in HE; exact (ext_entries_app_r _ _ (_ :: nil) _ HE). }
    specialize (IH eq_refl HEt ltac:(lia) Hs Hnd (body_tagged_ext_inv _ _ _ _ Htg Hx') Ho Hof).
    destruct E as [b pv r A [M |] | pm U | ? ? ? ? ? | pv A M U | ? ? ? ?]; cbn in HsE; try contradiction.
    + pose proof (ext_entries_head _ _ _ _ HE) as He; cbn [body_ctx List.app gentry_lets centry_lets alg_entry] in He, Hl.
      rewrite <- List.app_assoc in He; destruct (He ltac:(lia)) as ((UA & r' & u & HA & Hu) & HM).
      (** The tag is the relevance of the type's sort. *)
      destruct (Htg x Φx _ A M ltac:(cbn [gm_prefix_upto]; rewrite String.eqb_refl; reflexivity) eq_refl) as [i HAt].
      cbn [entry_kind] in HAt.
      pose proof (sort_typed_of_is_sort_nf (alg_type_infer_sound HA (presup_exp_ctx HAt)) Hu) as HAs.
      pose proof (kind_sort_agree _ _ _ _ _ _ HAs HAt) as ->.
      econstructor; eassumption.
    + pose proof (ext_entries_head _ _ _ _ HE) as He; cbn [body_ctx List.app gentry_lets centry_lets alg_entry] in He, Hl.
      rewrite <- List.app_assoc in He; specialize (He ltac:(lia)).
      econstructor; eassumption.
    + (* a definition with a module part: both parts *)
      pose proof (ext_entries_head _ _ _ _ HE) as He; cbn [body_ctx List.app gentry_lets centry_lets alg_entry] in He, Hl.
      rewrite <- List.app_assoc in He; destruct (He ltac:(lia)) as (((UA & u & HA & Hu) & HM) & HU).
      econstructor; eassumption.
  - cbn [body_shape] in Hs; destruct Hs as [Hs _].
    cbn [body_opens] in Ho, Hof; rewrite <- (items_gen_length _ _ _ _ _ _ Hg), gm_dropn_gens_append in Ho, Hof.
    pose proof (body_tagged_gens_inv _ _ _ Htg Hnd) as Htg'.
    assert (Hnd' : List.NoDup (gm_names Φx))
      by (rewrite gens_append_names in Hnd; exact (List.NoDup_app_remove_l _ _ Hnd)).
    rewrite gens_body_ctx_base, <- List.app_assoc in HE.
    specialize (IH eq_refl (ext_entries_app_r _ _ _ _ HE) ltac:(lia) Hs Hnd' Htg' (fun k => Ho (S k)) (fun k => Hof (S k))).
    pose proof (Ho 0 _ _ eq_refl ltac:(lia)) as HH.
    (* the module opened is no module still being defined *)
    pose proof (Hof 0 _ _ eq_refl) as HHf.
    econstructor; eassumption.
Qed.

(** A well-formed module expression checks, given that its arguments and
    its literals do: they are reached by generation ([modexp_gen]), whatever
    reducts its derivation goes through. *)
Lemma alg_modexp_of_wf : forall n,
    (forall Γ A M, gc_deps ⍮ gc_stack ⍮ Γ ⊢ M : A -> exp_lets M <= n -> Γ ⊢a M ⟸ A) ->
    (forall Γ U, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> gunit_lets U <= n -> Γ ⊢aᵘ U) ->
    forall H Γ, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> modexp_lets H <= n -> Γ ⊢aᵐ H.
Proof.
  intros n HM HU; induction H as [fp | x | H IH y | H IH N | U]; intros Γ HH Hl;
    pose proof (proj1 (modexp_gen _ _ _ _ _ HH)) as Hgen; cbn [gen_m modexp_lets] in Hgen, Hl.
  - destruct (me_mtele _ _ _ HH) as (R & T & Hm & Ht); econstructor; eassumption.
  - destruct (me_denotes _ _ _ _ _ HH) as (R & _ & Hm & _).
    inversion Hm; subst; try (unfold gc_unit in *; cbn in *; discriminate).
    econstructor; eassumption.
  - destruct (me_mtele _ _ _ HH) as (R & T & Hm & Ht).
    eapply alg_modexp_mem; [ apply IH; [ exact Hgen | lia ] | exact Hm | exact Ht ].
  - destruct Hgen as (HH0 & R & T & B & T1 & i & Hm & Ht & Hv & HB & _ & HN).
    eapply alg_modexp_app; [ apply IH; [ exact HH0 | lia ] | exact Hm | exact Ht | exact Hv | apply HM; [ exact HN | lia ] ].
  - apply alg_modexp_lit, HU; [ exact (unit_eq_of_full _ _ _ _ Hgen) | exact Hl ].
Qed.

(** An extension of an extension is one extension. *)
Lemma alg_ext_app : forall Γ Δ Ψ, Γ ⊢aˣ Δ -> Δ ++ Γ ⊢aˣ Ψ -> Γ ⊢aˣ Ψ ++ Δ.
Proof.
  intros * HΔ HΨ; remember (Δ ++ Γ) as G eqn:HG; induction HΨ; subst; cbn [List.app];
    [ exact HΔ | .. ]; econstructor; rewrite <- ?List.app_assoc; eauto.
Qed.

(** The same for parameters. *)
Lemma alg_params_app : forall Γ Δ Ψ, Γ ⊢aᵖ Δ -> Δ ++ Γ ⊢aᵖ Ψ -> Γ ⊢aᵖ Ψ ++ Δ.
Proof.
  intros * HΔ HΨ; remember (Δ ++ Γ) as G eqn:HG; induction HΨ; subst; cbn [List.app];
    [ exact HΔ | .. ]; econstructor; rewrite <- ?List.app_assoc; eauto.
Qed.

(** A body abstractable over the outer parameters [Δ] as a literal over
    its own [Δ'], and over [Δ'], is abstractable over both: with [Δ] of
    levels, by the inner premise; otherwise the literal's description,
    with no member of a type of levels, is the body's under both
    telescopes ([no_level_open_shift]). *)
Lemma levels_abstractable_flatten_body : forall Γ Δ Δ' Φ,
    levels_abstractable gc_deps gc_stack Γ Δ (me_lit (gu_open Δ' Φ)) ->
    levels_abstractable gc_deps gc_stack (Δ ++ Γ) Δ' (me_lit (gu_open nil Φ)) ->
    levels_abstractable gc_deps gc_stack Γ (Δ' ++ Δ) (me_lit (gu_open nil Φ)).
Proof.
  intros * [Hs | (R & HR & HN)] Hin.
  - destruct Hin as [Hs' | (R' & HR' & HN')]; [ left; exact (level_sorted_app _ _ Hs' Hs) |].
    right; exists R'; rewrite <- List.app_assoc; split; assumption.
  - right; inversion HR; subst; try (unfold gc_unit, gc_loc in *; cbn in *; discriminate).
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu as [? ? ? ? ? Φx ? Hx HRb |]; subst end.
    cbn in HRb; injection HRb as <-.
    exists (mdesc_open nil Φ Φx); split.
    + constructor; econstructor; [ rewrite List.app_nil_l, <- List.app_assoc; exact Hx | reflexivity ].
    + eapply no_level_open_shift; [| exact HN ]; rewrite List.app_nil_l, List.app_assoc; reflexivity.
Qed.

(** The same for an alias: the literal denotes the target's module part
    abstracted over [Δ'] ([udenote_alias]), whose having no member of a
    type of levels is the target's under [Δ'] ([no_level_up_mod],
    [no_level_of_mod]). *)
Lemma levels_abstractable_flatten_alias : forall Γ Δ Δ' E,
    levels_abstractable gc_deps gc_stack Γ Δ (me_lit (gu_mk Δ' (md_alias E))) ->
    levels_abstractable gc_deps gc_stack (Δ ++ Γ) Δ' E ->
    levels_abstractable gc_deps gc_stack Γ (Δ' ++ Δ) E.
Proof.
  intros * [Hs | (R & HR & HN)] Hin.
  - destruct Hin as [Hs' | (R' & HR' & HN')]; [ left; exact (level_sorted_app _ _ Hs' Hs) |].
    right; exists R'; rewrite <- List.app_assoc; split; assumption.
  - right; inversion HR; subst; try (unfold gc_unit, gc_loc in *; cbn in *; discriminate).
    match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu as [| ? ? ? ? R0 R1 HE HR1]; subst end.
    pose proof (proj1 (no_level_up_mod _ _ _ _ _ (mdesc_mod_is_mod _ _ HR1)) HN) as HN1.
    exists R0; rewrite <- List.app_assoc; split; [ exact HE | exact (no_level_of_mod _ _ _ _ _ HR1 HN1) ].
Qed.

(** A unit under parameters [Δ] is the unit over its own parameters and
    [Δ], the algorithmic counterpart of [wf_unit_eq_flatten], given that
    the literal is abstractable over [Δ], as the rule's flag premise
    says. *)
Lemma alg_unit_flatten : forall Γ Δ Δ' D,
    Γ ⊢aᵖ Δ -> all_assumptions Δ -> Δ ++ Γ ⊢aᵘ gu_mk Δ' D ->
    levels_abstractable gc_deps gc_stack Γ Δ (me_lit (gu_mk Δ' D)) ->
    Γ ⊢aᵘ gu_mk (Δ' ++ Δ) D.
Proof.
  intros * HΔ Ha HU Habs; inversion HU; subst.
  - eapply alg_unit_body; [ eapply alg_params_app; eassumption | apply List.Forall_app; split; assumption
                       | rewrite <- List.app_assoc; eassumption | assumption .. |].
    eapply levels_abstractable_flatten_body; eassumption.
  - eapply alg_unit_alias; [ eapply alg_params_app; eassumption | apply List.Forall_app; split; assumption
                        | rewrite <- List.app_assoc; eassumption | | rewrite <- List.app_assoc; eassumption ].
    eapply levels_abstractable_flatten_alias; eassumption.
Qed.

(** Parameters of the sorts a unit rule gives them, each type checked as
    an entry, are checked parameters: a type of the universe at [l] infers
    a universe, a type of levels [LevelSort], as the kind of the entry
    is the kind of its sort ([kind_sort_agree]). *)
Lemma alg_params_of_entries : forall n Γ Δ l (param_sorts : nat -> exp), ⊢ Γ ->
    ext_entries n Γ Δ -> ctx_lets Δ <= n -> all_assumptions Δ ->
    (forall k, parameter_sort l (param_sorts k)) ->
    (forall Δ1 κ T Δ2, Δ = (Δ1 ++ ce_ass κ T :: Δ2)%list -> (Δ2 ++ Γ)%list ⊢ T : param_sorts (List.length Δ2)) ->
    Γ ⊢aᵖ Δ.
Proof.
  intros n Γ; induction Δ as [| e Δ IH]; intros l ps HΓ Hx Hl Ha Hps HR; [ constructor |]; cbn [ctx_lets] in Hl.
  apply List.Forall_cons_iff in Ha as [(κ & T & ->) Ha].
  cbn [centry_lets] in Hl.
  pose proof (ext_entries_head _ _ _ _ Hx ltac:(cbn [centry_lets]; lia)) as He; cbn [alg_entry] in He.
  destruct He as (UA & u & HT & Hs).
  pose proof (HR nil κ T Δ eq_refl) as HTl.
  pose proof (sort_typed_of_is_sort_nf (alg_type_infer_sound HT (presup_exp_ctx HTl)) Hs) as HTs.
  pose proof (IH l ps HΓ (ext_entries_app_r _ _ (_ :: nil) _ Hx) ltac:(lia) Ha Hps
                (fun Δ1 κ' T' Δ2 E => HR (ce_ass κ T :: Δ1) κ' T' Δ2 ltac:(rewrite E; reflexivity))) as HΔ.
  assert (HP : ps (List.length Δ) = Typeω@l \/ ps (List.length Δ) = LevelSort)
    by (destruct (Hps (List.length Δ)); auto).
  destruct HP as [EP | EP]; rewrite EP in HTl.
  - change (Typeω@l) with (abs_kind_sort ak_relevant Typeω@l) in HTl.
    pose proof (kind_sort_agree _ _ _ _ _ _ HTl HTs) as <-.
    inversion Hs; subst; eapply alg_params_ass; eassumption.
  - change LevelSort with (abs_kind_sort ak_level Typeω@0) in HTl.
    pose proof (kind_sort_agree _ _ _ _ _ _ HTl HTs) as <-.
    inversion Hs; subst; eapply alg_params_level; eassumption.
Qed.

(** ** Records, Algorithmically *)

(** A field of a tuple has at most the tuple's unannotated [let]s. *)
Lemma tuple_field_lets : forall T (fs : list (String.string * exp)) k f M,
    List.nth_error fs k = Some (f, M) -> exp_lets M <= exp_lets (a_tuple T fs).
Proof.
  intros T fs; cbn [exp_lets].
  enough (H : forall k f M, List.nth_error fs k = Some (f, M) ->
                exp_lets M <= (fix fields_lets (fs : list (String.string * exp)) : nat :=
                                 match fs with
                                 | nil => 0
                                 | f :: fs' => exp_lets (snd f) + fields_lets fs'
                                 end) fs) by (intros; pose proof (H _ _ _ ltac:(eassumption)); lia).
  induction fs as [| [g N] fs IH]; intros [| k] f M Hk; cbn in Hk |- *; try discriminate.
  - injection Hk as <- <-; lia.
  - pose proof (IH _ _ _ Hk); lia.
Qed.

(** A record's type former checks at its type. *)
Lemma alg_record_complete : forall Γ p R, ⊢ Γ -> record_lookup gc_deps gc_stack p = Some R ->
    Γ ⊢a a_record p ⟸ record_ty R.
Proof.
  intros * HΓ Hl.
  destruct (record_former_typed _ _ _ HΓ Hl) as [j [_ Hj]].
  destruct (soundness_ty Hj) as [W [HW HWe]].
  econstructor; [ eapply alg_type_infer_record; eassumption | apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe ].
Qed.

(** A tuple checks at its annotation: the annotation normalises to the
    record type at the normal forms [Rs] of its parameters
    ([subtyp_record_nf]), and each field's type at them is its type at the
    parameters, where the field checks. *)
Lemma alg_tuple_complete : forall Γ T (fs : list (String.string * exp)) p R Ns i,
    Γ ⊢ T : Typeω@i -> Γ ⊢a T ⟸ Typeω@i ->
    Γ ⊢ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
    Γ ⊢ a_record p : record_ty R -> record_lookup gc_deps gc_stack p = Some R ->
    List.length Ns = List.length (record_params R) ->
    (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A -> Γ ⊢ N : A) ->
    List.map fst fs = List.map fst (record_fields R) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       Γ ⊢a M ⟸ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
    Γ ⊢a a_tuple T fs ⟸ T.
Proof.
  intros * HTt HTc HTeq Hrt Hl Hn HNs Hfs HMt HMc.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HS HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
  destruct (alg_type_check_typ_implies_alg_type_infer_typ HΓ HTc) as (UT & u & HTi & Hu & _).
  destruct (soundness_ty HTt) as [W [HW HWe]].
  destruct (subtyp_record_nf (wf_subtyp_refl' _ _ _ _ _ _ HTeq) Hl Hn HNs HW) as (Rs & -> & HRl0 & _).
  (** the parameters of the normal form are, position by position, the
      annotation's ([exp_eq_record_apps_inv]) *)
  assert (HRl : List.length (List.map nf_to_exp Rs) = List.length (record_params R)) by (rewrite List.length_map; exact HRl0).
  assert (HE : Γ ⊢ apps_exp (a_record p) Ns ≈ apps_exp (a_record p) (List.map nf_to_exp Rs) : Typeω@i)
    by (etransitivity; [ symmetry; exact HTeq | exact HWe ]).
  pose proof (wf_record_apps_inv _ _ _ _ _ Hl (presup_exp_eq_right HE) HRl) as HRt.
  destruct (exp_eq_record_apps_inv _ _ _ _ _ _ Hl HE Hn HRl HNs HRt) as [_ HNR].
  assert (Hlf : List.length fs = List.length (record_fields R))
    by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
  econstructor; [| apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe ].
  eapply alg_type_infer_tuple; [ exact HTi | exact Hu | exact HW | exact Hl | exact Hfs |].
  intros k f M U Hk Hfk.
  assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
  pose proof (record_fields_insts_eq _ _ _ p R Ns (List.map nf_to_exp Rs) fs fs Hrt Hl Hn HRl HNR Hfs eq_refl
                ltac:(intros * HM HM' HU; rewrite HM in HM'; injection HM' as <-; apply wf_exp_eq_refl; eapply HMt; eassumption)
                k ltac:(lia)) as Hins.
  destruct (record_field_typ_cong _ _ _ R k f U (Ns ++ List.firstn k (List.map snd fs))
              (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs)) Hc Hass HF HΓ Hfk
              ltac:(rewrite ?List.length_app, ?List.length_firstn, ?List.length_map in *; lia)
              ltac:(rewrite ?List.length_app, ?List.length_firstn, ?List.length_map in *; lia) Hins) as (SU & HSU & HUU).
  eapply alg_type_check_subtyp; [ exact (HMc _ _ _ _ Hk Hfk) |].
  exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ (presup_exp_eq_left HUU) (presup_exp_eq_right HUU) HSU HUU)).
Qed.

(** A projection checks at its field's type at the parameters of the
    element's type: the element infers the record type at the normal forms
    of its parameters ([subtyp_record_nf]), at which the field's type is
    equal to that one. *)
Lemma alg_proj_complete : forall Γ M p R Ns k f U,
    Γ ⊢ M : apps_exp (a_record p) Ns -> Γ ⊢a M ⟸ apps_exp (a_record p) Ns ->
    Γ ⊢ a_record p : record_ty R -> record_lookup gc_deps gc_stack p = Some R ->
    List.length Ns = List.length (record_params R) ->
    (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A -> Γ ⊢ N : A) ->
    List.nth_error (record_fields R) k = Some (f, U) ->
    Γ ⊢a a_proj f M ⟸ U[sb_of_list Id (Ns ++ record_pre R k M)].
Proof.
  intros * HMt HMc Hrt Hl Hn HNs Hfk.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HS HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  inversion HMc as [? W ? ? HMi HMs]; subst.
  pose proof (alg_type_infer_sound HMi HΓ) as HMW.
  destruct (presup_exp_typ_sorted HMt ltac:(apply apps_exp_not_level_sort; discriminate)) as (SP & HSP & HPs).
  destruct (alg_infer_below_sorted HΓ HSP HPs HMi HMs) as (SW & HSW & HWt).
  assert (HWs : Γ ⊢ (W : exp) ⊆ apps_exp (a_record p) Ns) by exact (alg_subtyping_sound_sort _ _ _ _ _ HSW HSP HMs HWt HPs).
  (** The inferred type is equal up to proofs to its normal form, the
      record type at parameters, so it is one; its parameters are the
      element's type's ([exp_eq_record_apps_inv]). *)
  destruct (alg_type_infer_self_upto HΓ HMi) as (W' & HWW & EW).
  destruct (subtyp_record_nf HWs Hl Hn HNs HWW) as (Rs' & -> & HRl' & _).
  destruct W; try (unfold nf_eq_upto_proofs in EW; cbn in EW; discriminate).
  apply nf_record_upto_proofs_inv in EW as (-> & ERs).
  rename l into Rs.
  assert (HRl : List.length (List.map nf_to_exp Rs) = List.length (record_params R))
    by (rewrite List.length_map, (nfs_eq_upto_proofs_length _ _ ERs); exact HRl').
  clear Rs' HRl' ERs HWW.
  cbn [nf_to_exp] in HWt, HWs, HMW.
  destruct (record_apps_typed_large HSW HWt) as [kW HWl].
  destruct (subtyp_record_inv HWs) as (SR & HSR & HeqR0).
  destruct (exp_eq_sort_large HSR HeqR0 (or_introl HWl)) as [kk HeqR].
  pose proof (wf_record_apps_inv _ _ _ _ _ Hl HWt HRl) as HRt.
  destruct (exp_eq_record_apps_inv _ _ _ _ _ _ Hl (wf_exp_eq_sym _ _ _ _ _ _ HeqR) Hn HRl HNs HRt) as [_ HNR].
  destruct (alg_proj_typed _ _ _ _ _ _ _ _ HΓ HMW Hl Hfk) as (m & HUR & _).
  pose proof (type_sort_kind_universe (record_field_kind R k) m) as HSm.
  destruct (nbe_ty_exists_sort HSm HUR) as [V HV].
  pose proof (soundness_ty_at_sort HSm HUR HV) as HVe.
  destruct (record_sort_large _ _ _ _ _ _ Hrt Hl Hn HNs) as [n Hm].
  pose proof (record_field_params_cong _ _ _ M p R Ns (List.map nf_to_exp Rs) n k f U HMt Hrt Hl Hn HRl HNs HNR Hm Hfk) as HUU.
  econstructor; [ eapply alg_type_infer_proj; [ exact HMi | exact Hl | exact (field_index_nth_nodup _ _ _ _ Hnd Hfk) | exact Hfk | exact HV ] |].
  apply alg_subtyping_complete.
  destruct (exp_eq_trans_sort HSm (type_sort_kind_universe _ n) ltac:(symmetry; exact HVe) ltac:(symmetry; exact HUU))
    as (S0 & HS0 & HE).
  exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ (presup_exp_eq_left HE) (presup_exp_eq_right HE) HS0 HE)).
Qed.

(** ** Completeness of the Rules of Either Sort *)

(** Two types equal at a sort have normal forms equal up to proofs. *)
Lemma nbe_ty_of_exp_eq_sort : forall {Γ A B S W},
    type_sort S -> Γ ⊢ A ≈ B : S -> nbe_ty_f Γ A W -> exists W', nbe_ty_f Γ B W' /\ nf_eq_upto_proofs W W'.
Proof.
  intros * HS HE HW.
  destruct (completeness_ty_sort HS HE) as (W0 & W' & HW1 & HW2 & E).
  pose proof (functional_nbe_ty _ _ _ _ HW HW1) as <-; exists W'; split; assumption.
Qed.

(** A term that infers a type equal up to proofs to the normal form of
    another checks against it: the inferred type is equal up to proofs to
    its own normal form ([alg_type_infer_self_upto]). *)
Lemma alg_type_check_of_infer_upto : forall {Γ M A} {W0 W : nf},
    ⊢ Γ -> Γ ⊢a M ⟹ W0 -> nbe_ty_f Γ A W -> nf_eq_upto_proofs W0 W -> Γ ⊢a M ⟸ A.
Proof.
  intros * HΓ Hi HW E.
  destruct (alg_type_infer_self_upto HΓ Hi) as (W0' & Hn & E0).
  econstructor; [ exact Hi | econstructor; [ exact Hn | exact HW |] ].
  apply alg_subtyping_nf_of_upto_proofs; transitivity W0; [ symmetry; exact E0 | exact E ].
Qed.

(** The same, the inferred type below the normal form. *)
Lemma alg_type_check_of_infer_sub_nf : forall {Γ M A} {W0 W : nf},
    ⊢ Γ -> Γ ⊢a M ⟹ W0 -> nbe_ty_f Γ A W -> ⊢anf W0 ⊆ W -> Γ ⊢a M ⟸ A.
Proof.
  intros * HΓ Hi HW Hs.
  destruct (alg_type_infer_self_upto HΓ Hi) as (W0' & Hn & E0).
  econstructor; [ exact Hi | econstructor; [ exact Hn | exact HW |] ].
  eapply alg_subtyping_nf_trans; [ apply alg_subtyping_nf_of_upto_proofs; symmetry; exact E0 | exact Hs ].
Qed.

(** A conjunction is injective in its parts: their normal forms are the
    parts of its normal form, equal up to proofs ([exp_eq_of_nbe_ty_same]);
    the second part's, read in the context the other first part extends,
    semantically the same ([ctxeq_nbe_ty_eq_sort]). *)
Lemma exp_eq_and_inv : forall {Γ P Q P' Q'},
    Γ ⊢ Σₚ P Q ≈ Σₚ P' Q' : Propₘ -> Γ ⊢ P ≈ P' : Propₘ /\ Γ ▹{ak_propositional} P ⊢ Q ≈ Q' : Propₘ.
Proof.
  intros * H.
  destruct (wf_and_inversion _ _ _ _ _ _ (presup_exp_eq_left H)) as [HP HQ _].
  destruct (wf_and_inversion _ _ _ _ _ _ (presup_exp_eq_right H)) as [HP' HQ' _].
  destruct (completeness_ty_sort type_sort_prop H) as (W & W' & HW & HW' & E).
  destruct (nbe_ty_and_inv _ _ _ _ HW) as (WP & WQ & -> & HWP & HWQ).
  destruct (nbe_ty_and_inv _ _ _ _ HW') as (WP' & WQ' & -> & HWP' & HWQ').
  unfold nf_eq_upto_proofs in E; cbn in E; apply andb_prop in E as [EP EQ].
  pose proof (exp_eq_of_nbe_ty_same type_sort_prop HP HP' HWP HWP' EP) as HPP.
  split; [ exact HPP |].
  assert (HΓP : ⊢ Γ ▹{ak_propositional} P) by (gen_presups; assumption).
  assert (HQ'P : Γ ▹{ak_propositional} P ⊢ Q' : Propₘ)
    by (eapply ctxsub_exp; [ exact (sub_id_extend_of_exp_eq sort_kind_prop HPP) | exact HQ' ]).
  destruct (nbe_ty_exists_sort type_sort_prop HQ'P) as [Y HY].
  assert (HYQ : nf_eq_upto_proofs Y WQ')
    by (eapply ctxeq_nbe_ty_eq_sort; [ exact type_sort_prop | exact HQ'P | eapply ctx_extend_sem_eq; [ exact type_sort_prop | exact HPP ]
                                     | eapply wf_ctx_scoped; gen_presups; eassumption | exact HY | exact HWQ' ]).
  exact (exp_eq_of_nbe_ty_same type_sort_prop HQ HQ'P HWQ HY ltac:(transitivity WQ'; [ exact EQ | symmetry; exact HYQ ])).
Qed.

(** A term checked against a type checks against a type equal to it at a
    sort. *)
Lemma alg_type_check_conv_sort : forall {Γ A A' M S},
    Γ ⊢a M ⟸ A -> type_sort S -> Γ ⊢ A ≈ A' : S -> Γ ⊢a M ⟸ A'.
Proof.
  intros * Hc HS HE; eapply alg_type_check_subtyp; [ exact Hc |].
  exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ (presup_exp_eq_left HE) (presup_exp_eq_right HE) HS HE)).
Qed.

(** A term that infers [Prop] checks against it. *)
Lemma alg_type_check_prop_of : forall {Γ A}, ⊢ Γ -> Γ ⊢a A ⟹ Propⁿ -> Γ ⊢a A ⟸ Propₘ.
Proof.
  intros * HΓ Hi.
  apply (alg_type_check_of_infer_nbe (type_sort_universe 0) (wf_prop_large (i := 0) HΓ)); intros W HW.
  replace W with Propⁿ; [ exact Hi |].
  inversion HW; subst; directed_inversion_by_head eval_exp; subst; directed_inversion_by_head read_typ; subst; reflexivity.
Qed.

(** The introduction of [⊤] checks against [⊤]. *)
Lemma alg_tt_complete : forall Γ, ⊢ Γ -> Γ ⊢a a_tt ⟸ ⊤.
Proof.
  intros * HΓ.
  apply (alg_type_check_of_infer_nbe type_sort_prop (wf_True _ _ _ HΓ)); intros W HW.
  replace W with ⊤ⁿ; [ constructor |].
  inversion HW; subst; directed_inversion_by_head eval_exp; subst; directed_inversion_by_head read_typ; subst; reflexivity.
Qed.

(** Ex falso checks against its target, a type of a universe or a
    proposition ([level_closed_sort]): its type infers a sort of that
    kind, never [LevelSort]. *)
Lemma alg_absurd_complete : forall {Γ C M S},
    ⊢ Γ -> type_sort S -> level_closed_sort Propₘ S -> Γ ⊢ C : S -> Γ ⊢a C ⟸ S -> Γ ⊢a M ⟸ ⊥ ->
    Γ ⊢a efq M return C ⟸ C.
Proof.
  intros * HΓ HS Hlc HC HCc HMc.
  assert (exists UC r u, Γ ⊢a C ⟹ UC /\ is_sort_nf UC r u /\ r <> ak_level) as (UC & r & u & HCi & Hs & Hr).
  { inversion Hlc; subst.
    - destruct (alg_type_check_typ_implies_alg_type_infer_typ HΓ HCc) as (UC & u & Hi & Hu & _).
      exists UC, ak_relevant, u; split; [ exact Hi | split; [ constructor; exact Hu | discriminate ] ].
    - exists Propⁿ, ak_propositional, (universe_small (ordinal_of_nat 0, nil)).
      split; [ exact (alg_type_check_prop_infer HΓ HCc) | split; [ constructor | discriminate ] ]. }
  apply (alg_type_check_of_infer_nbe HS HC); intros W HW.
  eapply alg_type_infer_absurd; eassumption.
Qed.

(** A proof checked against a conjunction infers a conjunction whose parts
    are the checked one's: the inferred type is below its normal form,
    subtyping at a proposition is equality up to proofs, and conjunctions
    equal at [Prop] have equal parts ([exp_eq_and_inv]). *)
Lemma alg_type_check_and_infer : forall {Γ M P Q},
    ⊢ Γ -> Γ ⊢ Σₚ P Q : Propₘ -> Γ ⊢a M ⟸ Σₚ P Q ->
    exists WP WQ, Γ ⊢a M ⟹ Σₚⁿ WP WQ /\ Γ ⊢ WP ≈ P : Propₘ /\ Γ ▹{ak_propositional} WP ⊢ WQ ≈ Q : Propₘ.
Proof.
  intros * HΓ HPQ Hc.
  destruct (alg_type_check_infer_below HΓ Hc) as (W & W2 & Hi & Hn2 & Hsub).
  destruct (nbe_ty_and_inv _ _ _ _ Hn2) as (VP & VQ & -> & _ & _).
  pose proof (alg_subtyping_nf_not_univ_pi_eq _ _ Hsub ltac:(right; exact I)) as E.
  destruct W; try (unfold nf_eq_upto_proofs in E; cbn in E; discriminate).
  eexists _, _; split; [ exact Hi |].
  pose proof (alg_type_infer_sound Hi HΓ) as HM; cbn [nf_to_exp] in HM.
  pose proof (and_typed_of_proof HM) as HPQ'.
  destruct (alg_type_infer_self_upto HΓ Hi) as (X & HX & EX).
  pose proof (exp_eq_of_nbe_ty_same type_sort_prop HPQ' HPQ HX Hn2 ltac:(etransitivity; [ symmetry; exact EX | exact E ]))
    as HE.
  exact (exp_eq_and_inv HE).
Qed.

(** The first component of a proof of a conjunction. *)
Lemma alg_left_complete : forall {Γ M P Q},
    ⊢ Γ -> Γ ⊢ Σₚ P Q : Propₘ -> Γ ⊢a M ⟸ Σₚ P Q -> Γ ⊢a a_left M ⟸ P.
Proof.
  intros * HΓ HPQ Hc.
  destruct (alg_type_check_and_infer HΓ HPQ Hc) as (WP & WQ & Hi & HWP & _).
  econstructor; [ eapply alg_type_infer_left; exact Hi |].
  apply alg_subtyping_complete.
  exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ (presup_exp_eq_left HWP) (presup_exp_eq_right HWP) type_sort_prop HWP)).
Qed.

(** The second, at the first: the inferred second part instantiated at
    the first component is equal to the checked one's. *)
Lemma alg_right_complete : forall {Γ M P Q},
    ⊢ Γ -> Γ ⊢ Σₚ P Q : Propₘ -> Γ ⊢ M : Σₚ P Q -> Γ ⊢a M ⟸ Σₚ P Q ->
    Γ ⊢a a_right M ⟸ Q[Id,,a_left M].
Proof.
  intros * HΓ HPQ HM Hc.
  destruct (wf_and_inversion _ _ _ _ _ _ HPQ) as [HP HQ _].
  destruct (alg_type_check_and_infer HΓ HPQ Hc) as (WP & WQ & Hi & HWP & HWQ).
  pose proof (alg_type_infer_sound Hi HΓ) as HMW; cbn [nf_to_exp] in HMW.
  destruct (wf_and_inversion _ _ _ _ _ _ (and_typed_of_proof HMW)) as [HWPt HWQt _].
  assert (HL : Γ ⊢ a_left M : WP) by (eapply wf_left; eassumption).
  pose proof (wf_sub_single _ _ _ _ _ _ _ HWPt sort_kind_prop HL) as Hσ.
  pose proof (sub_preserves_sort_eq _ _ _ _ _ _ _ _ HWQ type_sort_prop Hσ) as HQσ.
  destruct (nbe_ty_exists_sort type_sort_prop (presup_exp_eq_left HQσ)) as [W HW].
  pose proof (soundness_ty_at_sort type_sort_prop (presup_exp_eq_left HQσ) HW) as HWe.
  econstructor; [ eapply alg_type_infer_right; [ exact Hi | exact HW ] |].
  apply alg_subtyping_complete.
  assert (HE : Γ ⊢ (W : exp) ≈ Q[Id,,a_left M] : Propₘ) by (etransitivity; [ symmetry; exact HWe | exact HQσ ]).
  exact (proj1 (wf_subtyp_of_exp_eq _ _ _ _ _ _ (presup_exp_eq_left HE) (presup_exp_eq_right HE) type_sort_prop HE)).
Qed.

(** A proof of a conjunction checks against the conjunction it
    annotates: its annotations are propositions, and the components check
    against their parts. *)
Lemma alg_conj_complete : forall {Γ P Q M N},
    ⊢ Γ -> Γ ⊢ P : Propₘ -> Γ ⊢a P ⟸ Propₘ -> Γ ▹{ak_propositional} P ⊢ Q : Propₘ ->
    Γ ▹{ak_propositional} P ⊢a Q ⟸ Propₘ ->
    Γ ⊢a M ⟸ P -> Γ ⊢a N ⟸ Q[Id,,M] -> Γ ⊢a a_conj P Q M N ⟸ Σₚ P Q.
Proof.
  intros * HΓ HP HPc HQ HQc HMc HNc.
  assert (HΓP : ⊢ Γ ▹{ak_propositional} P) by (gen_presups; assumption).
  apply (alg_type_check_of_infer_nbe type_sort_prop (wf_and _ _ _ _ _ HP HQ)); intros W HW.
  eapply alg_type_infer_conj;
    [ exact (alg_type_check_prop_infer HΓ HPc) | exact (alg_type_check_prop_infer HΓP HQc) | exact HMc | exact HNc | exact HW ].
Qed.

(** A term checked against a type of a sort infers a type of the kind of
    that sort, no [LevelSort], whose instance along a substitution
    normalises below the type's instance. *)
Lemma alg_type_check_nbe_sub : forall {Γ Δ σ B C κ j},
    ⊢ Δ -> Γ ⊢ˢ σ : Δ -> Δ ⊢ C : abs_kind_sort κ Typeω@j -> Δ ⊢a B ⟸ C ->
    exists C' W, Δ ⊢a B ⟹ C' /\ nf_to_exp C' <> LevelSort /\ nbe_ty_kind Δ C' κ /\
      nbe_ty_f Γ (nf_to_exp C')[σ] W /\ Γ ⊢a W ⊆ C[σ].
Proof.
  intros * HΔ Hσ HC Hc.
  pose proof (type_sort_kind_universe κ j) as HSC.
  inversion Hc as [? C' ? ? HBi HBs]; subst.
  pose proof (alg_type_infer_sound HBi HΔ) as HB'.
  destruct (alg_infer_below_sorted HΔ HSC HC HBi HBs) as (SC' & HSC' & HC').
  pose proof (alg_subtyping_sound_sort _ _ _ _ _ HSC' HSC HBs HC' HC) as HCC.
  (** the inferred type is of the checked one's kind ([subtyp_same_kind]) *)
  assert (exists k, Δ ⊢ (C' : exp) : abs_kind_sort κ Typeω@k) as [k HC'k].
  { assert (exists r' (j' : nat), SC' = abs_kind_sort r' Typeω@j') as (r' & j' & ->)
      by (destruct HSC' as [j' | |]; [ exists ak_relevant, j' | exists ak_propositional, 0 | exists ak_level, 0 ]; reflexivity).
    pose proof (subtyp_same_kind _ _ _ r' κ j' j HCC HC' HC) as <-; exists j'; exact HC'. }
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HC' HSC' Hσ) as HC'σ.
  destruct (nbe_ty_exists_sort HSC' HC'σ) as [W HW].
  pose proof (soundness_ty_at_sort HSC' HC'σ HW) as HE.
  exists C', W; split; [ exact HBi |].
  split; [ intros E; rewrite E in HC'k; exact (level_sort_untyped HC'k) |].
  split; [ exact (nbe_ty_kind_of_typed HC'k) |].
  split; [ exact HW |].
  apply alg_subtyping_complete.
  etransitivity; [| exact (sub_preserves_subtyp _ _ _ _ _ _ _ HCC Hσ) ].
  exact (proj2 (wf_subtyp_of_exp_eq _ _ _ _ _ _ HC'σ (presup_exp_eq_right HE) HSC' HE)).
Qed.

(** A local definition checks at its body's type instantiated: its
    annotation infers a sort of its kind; its body's inferred type is of
    the kind of the body's type's sort, a type of levels only under a
    level ([level_closed_sort]). *)
Lemma alg_let_complete : forall Γ A M B C Srt SrtC,
    ⊢ Γ -> Γ ⊢ A : Srt -> type_sort Srt -> Γ ⊢a A ⟸ Srt -> Γ ⊢ M : A -> Γ ⊢a M ⟸ A ->
    Γ ▸ A ≔ M ⊢ C : SrtC -> level_closed_sort Srt SrtC -> Γ ▸ A ≔ M ⊢a B ⟸ C ->
    Γ ⊢a ℓ A ≔ M in B ⟸ C[Id,,M].
Proof.
  intros * HΓ HA HS HAc HM HMc HC Hlc HBc.
  destruct (alg_type_check_sort_infer HΓ HS HAc) as (UA & r & u & HAi & Hs).
  (** the annotation's kind is its sort's *)
  assert (exists κ j, Srt = abs_kind_sort κ Typeω@j) as (κ & j & ->)
    by (destruct HS as [j | |]; [ exists ak_relevant, j | exists ak_propositional, 0 | exists ak_level, 0 ]; reflexivity).
  pose proof (kind_sort_agree _ _ _ _ _ _ (sort_typed_of_is_sort_nf (alg_type_infer_sound HAi HΓ) Hs) HA) as ->.
  assert (HGd : ⊢ Γ ▸ A ≔ M) by (eapply wf_ctx_extend_def; [ exact HA | exact HS | exact HM ]).
  assert (exists κC jC, SrtC = abs_kind_sort κC Typeω@jC /\ (κC = ak_level -> κ = ak_level)) as (κC & jC & -> & Hkl).
  { inversion Hlc as [? i | | E1]; subst.
    - exists ak_relevant, i; split; [ reflexivity | discriminate ].
    - exists ak_propositional, 0; split; [ reflexivity | discriminate ].
    - exists ak_level, 0; split; [ reflexivity | intros _ ].
      destruct κ; cbn [abs_kind_sort] in E1; congruence. }
  destruct (alg_type_check_nbe_sub HGd (wf_sub_single_def _ _ _ _ _ _ HA HS HM) HC HBc)
    as (C' & W & HBi & HnL & Hr & HW & Hsub).
  econstructor; [ eapply alg_type_infer_let; [ exact HAi | exact Hs | exact HMc | exact HBi | exact HnL | exact Hr | exact Hkl | exact HW ]
                | exact Hsub ].
Qed.

(** A module [let] checks at its body's type instantiated: the body's
    type is no type of levels ([module_body_sort]). *)
Lemma alg_let_mod_complete : forall Γ U B C Srt,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> Γ ⊢aᵘ U -> Γ ▹ₘ U ⊢ C : Srt -> module_body_sort Srt ->
    Γ ▹ₘ U ⊢a B ⟸ C -> Γ ⊢a ℓₘ U in B ⟸ C[Id ,,ₘ me_lit U].
Proof.
  intros * HU HUa HC Hms HBc.
  assert (HGU : ⊢ Γ ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU).
  assert (exists κC jC, Srt = abs_kind_sort κC Typeω@jC /\ κC <> ak_level) as (κC & jC & -> & Hkl)
    by (destruct Hms as [i |]; [ exists ak_relevant, i | exists ak_propositional, 0 ]; split; first [ reflexivity | discriminate ]).
  destruct (alg_type_check_nbe_sub HGU (wf_sub_single_mod _ _ _ _ HU) HC HBc) as (C' & W & HBi & HnL & Hr & HW & Hsub).
  econstructor; [ eapply alg_type_infer_let_mod; [ exact HUa | exact HBi | exact HnL | exact Hr | exact Hkl | exact HW ] | exact Hsub ].
Qed.

(** An application checks against the codomain instantiated: the function
    infers a [Π] whose codomain is below the [Π]'s ([alg_type_check_pi_implies_alg_type_infer_pi]). *)
Lemma alg_app_complete : forall {Γ A B M N κd κc},
    ⊢ Γ -> Γ ⊢ M : a_pi κd κc A B -> Γ ⊢a M ⟸ a_pi κd κc A B -> Γ ⊢ N : A -> Γ ⊢a N ⟸ A ->
    Γ ⊢a M $ N ⟸ B[Id,,N].
Proof.
  intros * HΓ HM HMc HN HNc.
  destruct (presup_exp_typ_sorted HM ltac:(discriminate)) as (Spi & _ & HPi).
  destruct (wf_pi_parts HPi) as (_ & (SA0 & HSAk0 & HA) & (i & HB)).
  destruct (alg_type_check_pi_implies_alg_type_infer_pi HΓ HPi HMc) as (A' & B' & SA & HSAk & HMi & HAA & HBB).
  pose proof (alg_type_check_conv_sort HNc (sort_kind_type_sort _ _ HSAk) (wf_exp_eq_sym _ _ _ _ _ _ HAA)) as HNc'.
  pose proof (alg_type_infer_sound HMi HΓ) as HM'; cbn [nf_to_exp] in HM'.
  destruct (presup_exp_typ_sorted HM' ltac:(discriminate)) as (S' & _ & HPi').
  destruct (wf_pi_parts HPi') as (_ & _ & (k & HB'k)).
  pose proof (ctxsub_exp _ _ _ _ _ _ (sub_id_extend_of_exp_eq HSAk (wf_exp_eq_sym _ _ _ _ _ _ HAA)) HB'k) as HB'A.
  pose proof (alg_subtyping_sound_sort _ _ _ _ _ (type_sort_kind_universe κc k) (type_sort_kind_universe κc i)
                HBB HB'A HB) as HBB'.
  pose proof (wf_sub_single _ _ _ _ _ _ _ HA HSAk0 HN) as Hσ.
  pose proof (sub_preserves_sort _ _ _ _ _ _ _ HB'A (type_sort_kind_universe κc k) Hσ) as HB'N.
  destruct (nbe_ty_exists_sort (type_sort_kind_universe κc k) HB'N) as [W HW].
  pose proof (soundness_ty_at_sort (type_sort_kind_universe κc k) HB'N HW) as HE.
  econstructor; [ eapply alg_type_infer_app; [ exact HMi | exact HNc' | exact HW ] |].
  apply alg_subtyping_complete.
  etransitivity; [| exact (sub_preserves_subtyp _ _ _ _ _ _ _ HBB' Hσ) ].
  exact (proj2 (wf_subtyp_of_exp_eq _ _ _ _ _ _ HB'N (presup_exp_eq_right HE) (type_sort_kind_universe κc k) HE)).
Qed.

(** A term checked against the sort of the kind [κ] at a large universe
    infers a sort of that kind, below the universe. *)
Lemma alg_type_check_kind_sort_infer : forall {Γ A κ i},
    ⊢ Γ -> Γ ⊢a A ⟸ abs_kind_sort κ Typeω@i ->
    exists UA u, Γ ⊢a A ⟹ UA /\ is_sort_nf UA κ u /\ universe_nf_le u (universe_large i).
Proof.
  intros * HΓ HAc; destruct κ; cbn [abs_kind_sort] in HAc.
  - destruct (alg_type_check_typ_implies_alg_type_infer_typ HΓ HAc) as (UA & u & HAi & Hu & Hle).
    exists UA, u; split; [ exact HAi | split; [ constructor; exact Hu | exact Hle ] ].
  - exists Propⁿ, (universe_small (ordinal_of_nat 0, nil)).
    split; [ exact (alg_type_check_prop_infer HΓ HAc) | split; [ constructor | cbn; exact I ] ].
  - exists LevelSortⁿ, (universe_small (ordinal_of_nat 0, nil)).
    split; [ exact (alg_type_check_level_sort_infer HΓ HAc) | split; [ constructor | cbn; exact I ] ].
Qed.

(** The same at a universe, small or large: a sort of the kind. *)
Lemma alg_type_check_kind_sort_univ_infer : forall {Γ A κ U},
    ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵤ U -> Γ ⊢a A ⟸ abs_kind_sort κ U -> exists UA u, Γ ⊢a A ⟹ UA /\ is_sort_nf UA κ u.
Proof.
  intros * HΓ HU HAc.
  inversion HU; subst.
  - destruct (alg_type_check_kind_sort_infer HΓ HAc) as (UA & u & HAi & Hs & _); eauto.
  - destruct κ; cbn [abs_kind_sort] in HAc.
    + destruct (alg_type_check_suniv_tm_implies_alg_type_infer_univ HΓ HAc) as ([c xs] & Lt & HAi & _ & _).
      exists (nf_univ_of (c, xs)), (universe_small (c, xs)); split; [ exact HAi | do 2 constructor ].
    + exists Propⁿ, (universe_small (ordinal_of_nat 0, nil)); split; [ exact (alg_type_check_prop_infer HΓ HAc) | constructor ].
    + exists LevelSortⁿ, (universe_small (ordinal_of_nat 0, nil)); split; [ exact (alg_type_check_level_sort_infer HΓ HAc) | constructor ].
Qed.

(** A [Π] into a universe at a large universe, over a type of any kind
    below it: the join of the two parts' universes is below it. *)
Lemma alg_pi_large_complete : forall {Γ A B κd i},
    ⊢ Γ -> Γ ⊢a A ⟸ abs_kind_sort κd Typeω@i -> Γ ▹{κd} A ⊢a B ⟸ Typeω@i ->
    Γ ⊢a Π{κd} A B ⟸ Typeω@i.
Proof.
  intros * HΓ HAc HBc.
  destruct (alg_type_check_kind_sort_infer HΓ HAc) as (UA & u & HAi & Hs & Hle).
  assert (HΓA : ⊢ Γ ▹{κd} A)
    by (eapply wf_ctx_extend; [ exact (sort_typed_of_is_sort_nf (alg_type_infer_sound HAi HΓ) Hs) | apply sort_kind_abs_kind_sort ]).
  destruct (alg_type_check_typ_implies_alg_type_infer_typ HΓA HBc) as (UB & v & HBi & Hv & Hle').
  pose proof (pi_domain_ok_of_is_sort_nf (alg_type_infer_sound HAi HΓ) Hs) as HAd.
  assert (HBv : Γ ▹{κd} A ⊢ B : universe_nf_tm v)
    by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hv); exact (alg_type_infer_sound HBi HΓA)).
  assert (Hvws : universe_nf_well_scoped (Γ ▹{κd} A) v).
  { assert (Hpf : nf_proof_free UB)
      by (rewrite (is_univ_nf_eq _ _ Hv) in HBi |- *; destruct v as [[c xs] | j];
          [ exact (alg_type_infer_univ_proof_free HΓA HBi) | exact I ]).
    pose proof (alg_type_infer_self HΓA HBi Hpf) as HnB; rewrite (is_univ_nf_eq _ _ Hv) in HnB.
    assert (exists k, Γ ▹{κd} A ⊢ universe_nf_tm v : Typeω@k) as [kv Hkv] by univ_large.
    eapply universe_nf_well_scoped_of_nbe; [ exact Hkv | rewrite <- nf_to_exp_univ_nf; exact HnB ]. }
  destruct (wf_universe_nf_pi_tm HAd HBv Hvws) as [k Hk].
  eapply (alg_pi_check_of_infer _ _ _ _ _ κd u v _ (Datatypes.S i));
    [ exact HΓ | exact HAi | exact HBi | exact Hs | exact Hv | apply wf_typ; exact HΓ |].
  eapply universe_nf_pi_tm_large; eassumption.
Qed.

(** A universal proposition or a type of functions between levels: the
    [Π] is of [Prop] or of [LevelSort], whatever the universe its parts
    are counted in. *)
Lemma alg_pi_irrelevant_complete : forall {Γ A B κd κc U},
    ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵤ U -> κc <> ak_relevant -> pi_kinds κd κc ->
    Γ ⊢a A ⟸ abs_kind_sort κd U -> Γ ▹{κd} A ⊢a B ⟸ abs_kind_sort κc U ->
    Γ ⊢a a_pi κd κc A B ⟸ abs_kind_sort κc U.
Proof.
  intros * HΓ HU Hκ Hk HAc HBc.
  destruct (alg_type_check_kind_sort_univ_infer HΓ HU HAc) as (UA & u & HAi & Hs).
  assert (HΓA : ⊢ Γ ▹{κd} A)
    by (eapply wf_ctx_extend; [ exact (sort_typed_of_is_sort_nf (alg_type_infer_sound HAi HΓ) Hs) | apply sort_kind_abs_kind_sort ]).
  destruct κc; [ contradiction (Hκ eq_refl) | |]; cbn [abs_kind_sort] in HBc |- *.
  - pose proof (alg_type_check_prop_infer HΓA HBc) as HBi.
    apply (alg_type_check_of_infer_nbe (type_sort_universe 1) (motive_kind_sort_typed _ ak_propositional 0 ltac:(constructor) HΓ));
      intros W HW.
    eapply alg_type_infer_pi; [ exact HAi | exact Hs | exact HBi | exact (nbe_ty_prop_self HΓA) | exact is_sort_nf_prop | exact Hk | exact HW ].
  - pose proof (alg_type_check_level_sort_infer HΓA HBc) as HBi.
    econstructor; [ eapply alg_type_infer_pi; [ exact HAi | exact Hs | exact HBi | exact (nbe_ty_level_sort_self HΓA)
                                              | exact is_sort_nf_level | exact Hk | exact (nbe_ty_level_sort_self HΓ) ] |].
    econstructor; [ exact (nbe_ty_level_sort_self HΓ) | exact (nbe_ty_level_sort_self HΓ) | apply alg_subtyping_nf_refl ].
Qed.

(** A [λ] checks against a [Π] of the sort its body's type is of: the
    body's inferred type is below the [Π]'s codomain, so of its sort
    ([subtyp_same_relevance]), and of that relevance
    ([nbe_ty_kind_of_typed]); the inferred [Π] is below the [Π],
    covariantly at [relevant], equal at [propositional]. *)
Lemma alg_fn_complete : forall {Γ A B M Srt κd κc} {i : nat},
    ⊢ Γ -> Γ ⊢ A : Srt -> sort_kind Srt κd -> Γ ⊢a A ⟸ Srt -> Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@i ->
    pi_kinds κd κc -> Γ ▹{κd} A ⊢a M ⟸ B ->
    Γ ⊢a λ A M ⟸ a_pi κd κc A B.
Proof.
  intros * HΓ HA HSk HAc HB Hk HMc.
  pose proof (sort_kind_type_sort _ _ HSk) as HS.
  destruct (alg_type_check_sort_infer HΓ HS HAc) as (UA & rA & u & HAi & Hs).
  (** the inferred sort is of the domain's kind *)
  pose proof (sort_typed_of_is_sort_nf (alg_type_infer_sound HAi HΓ) Hs) as HAr.
  destruct (sort_kind_abs_kind_sort_inv _ _ HSk) as [jA ->].
  pose proof (kind_sort_agree _ _ _ _ _ _ HAr HA) as ->.
  assert (HΓA : ⊢ Γ ▹{κd} A) by (eapply wf_ctx_extend; [ exact HA | exact HSk ]).
  inversion HMc as [? B' ? ? HMi HMs]; subst.
  destruct (alg_infer_below_sorted HΓA (type_sort_kind_universe κc i) HB HMi HMs) as (SB & HSB & HB').
  pose proof (alg_subtyping_sound_sort _ _ _ _ _ HSB (type_sort_kind_universe κc i) HMs HB' HB) as HBB.
  (** the body's inferred type is of the codomain's kind ([subtyp_same_kind]) *)
  assert (exists k : nat, Γ ▹{κd} A ⊢ B' : abs_kind_sort κc Typeω@k) as [k HBk].
  { assert (exists r' (j : nat), SB = abs_kind_sort r' Typeω@j) as (r' & j & ->)
      by (destruct HSB as [j | |]; [ exists ak_relevant, j | exists ak_propositional, 0 | exists ak_level, 0 ]; reflexivity).
    pose proof (subtyp_same_kind _ _ _ r' κc j i HBB HB' HB) as <-; exists j; exact HB'. }
  assert (HnL : nf_to_exp B' <> LevelSort)
    by (intros E; rewrite E in HBk; exact (level_sort_untyped HBk)).
  destruct (nbe_ty_exists_sort HS HA) as [C HC].
  assert (Hfi : Γ ⊢a λ A M ⟹ nf_pi κd κc C B')
    by (eapply alg_type_infer_fn; [ exact HAi | exact Hs | exact HMi | exact HnL | exact (nbe_ty_kind_of_typed HBk) | exact Hk | exact HC ]).
  destruct HMs as [B1 B2 Hn1 Hn2 Hsub].
  pose proof (alg_type_infer_normal HΓA HMi Hn1) as EB.
  apply (alg_type_check_of_infer_sub_nf HΓ Hfi (nbe_ty_pi_intro _ _ _ _ _ _ _ HC Hn2)).
  (** the inferred [Π] is below the [Π]: covariantly into an evaluated
      kind, equal up to proofs into [Prop] *)
  destruct κc.
  - apply alg_subtyping_nf_pi; [ constructor | reflexivity | eapply alg_subtyping_nf_trans; [ apply alg_subtyping_nf_of_upto_proofs; exact EB | exact Hsub ] ].
  - cbn [abs_kind_sort] in HB.
    pose proof (alg_subtyping_nf_not_univ_pi_eq _ _ Hsub ltac:(right; exact (nbe_ty_prop_not_univ_pi _ _ _ HB Hn2))) as E.
    apply alg_subtyping_nf_refl_case; [ exact I | apply nf_pi_upto_proofs; [ reflexivity | etransitivity; [ exact EB | exact E ] ] ].
  - apply alg_subtyping_nf_pi; [ constructor | reflexivity | eapply alg_subtyping_nf_trans; [ apply alg_subtyping_nf_of_upto_proofs; exact EB | exact Hsub ] ].
Qed.

(** A type checked against a sort of the kind [κ] infers a sort of that
    kind ([kind_sort_agree]): an assumption entry. *)
Lemma alg_entry_ass_of_check : forall Γ A Srt κ,
    ⊢ Γ -> Γ ⊢ A : Srt -> sort_kind Srt κ -> Γ ⊢a A ⟸ Srt -> exists UA u, Γ ⊢a A ⟹ UA /\ is_sort_nf UA κ u.
Proof.
  intros * HΓ HA HSk HAc.
  destruct (alg_type_check_sort_infer HΓ (sort_kind_type_sort _ _ HSk) HAc) as (UA & r & u & HAi & Hs).
  destruct (sort_kind_abs_kind_sort_inv _ _ HSk) as [j ->].
  pose proof (kind_sort_agree _ _ _ _ _ _ (sort_typed_of_is_sort_nf (alg_type_infer_sound HAi HΓ) Hs) HA) as ->.
  eauto.
Qed.

(** A [Π] checks against the sort of its codomain's kind at the universe
    its parts are counted in: into a universe at a large one
    ([alg_pi_large_complete]) or a small one ([alg_pi_small_complete]),
    or into [Prop] or [LevelSort] ([alg_pi_irrelevant_complete]). *)
Lemma alg_pi_complete : forall Γ U A B κd κc,
    ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵤ U -> Γ ⊢ A : abs_kind_sort κd U -> Γ ⊢a A ⟸ abs_kind_sort κd U ->
    Γ ▹{κd} A ⊢a B ⟸ (abs_kind_sort κc U)[↑]ʷ -> pi_kinds κd κc ->
    Γ ⊢a a_pi κd κc A B ⟸ abs_kind_sort κc U.
Proof.
  intros * HΓ HU HA HAc HBc Hk.
  rewrite abs_kind_sort_wk in HBc.
  destruct κc.
  - cbn [abs_kind_sort] in HBc |- *; inversion HU; subst; cbn [exp_wk] in HBc.
    + eapply alg_pi_large_complete; eassumption.
    + eapply alg_pi_small_complete; eassumption.
  - eapply alg_pi_irrelevant_complete; [ exact HΓ | exact HU | discriminate | exact Hk | exact HAc | cbn [abs_kind_sort] in *; exact HBc ].
  - eapply alg_pi_irrelevant_complete; [ exact HΓ | exact HU | discriminate | exact Hk | exact HAc | cbn [abs_kind_sort] in *; exact HBc ].
Qed.

(** The expanded side of [wf_unit_eq_expand], in the induction below: the
    expanded unit's parts, from its own derivation, by the outer
    induction at a smaller bound. *)
Ltac expand_case :=
  match goal with
  | IHn : forall m, m < ?n -> _, HmH : forall Γ' H0, _ -> modexp_lets H0 < ?n -> _,
    HU : _ ⍮ _ ⍮ ?G ⊢ᵘ gu_open ?Δ ?Φ ≈ _, Hb : gunit_lets (gu_open ?Δ (gm_expand ?Φ)) <= ?n |- _ =>
      destruct (proj1 (unit_full_of_eq _ _ _ _ _ HU)) as [Φx0 ? ? ? ? Hx0];
      pose proof (body_xp_result_noopen _ _ _ _ _ Hx0) as Hno; rewrite (body_xp_expand _ _ _ _ _ Hx0) in Hno;
      destruct (proj2 (unit_full_of_eq _ _ _ _ _ (wf_unit_eq_expand _ _ _ _ _ HU)))
        as [Φx es pl ps Hps Hx HC Hsorts Htags Hdefs Hopens Ha Hs Hsx Hnd HR lv Rt [Hf1 Hf2 Hf3] Hoff];
      pose proof (body_xp_noopen_id _ _ _ _ _ Hno Hx) as EΦx; subst Φx;
      rewrite gunit_lets_mk in Hb; cbn [moddef_lets] in Hb;
      destruct (IHn (n - 1) ltac:(lia)) as (_ & _ & _ & _ & _ & IHx & _ & _);
      assert (HXe : gc_deps ⍮ gc_stack ⍮ G ⊢ˣ body_ctx (gm_expand Φ) ++ Δ ≈ body_ctx (gm_expand Φ) ++ Δ)
        by (apply ext_of_ctx'; rewrite <- List.app_assoc; exact HC);
      pose proof (proj1 (IHx _ _ _ _ _ HXe eq_refl eq_refl)) as HXl;
      assert (HΓ : ⊢ G) by exact (ctx_app_wf_tail _ _ _ _ (ext_eq_ctx_left _ _ _ _ _ HXe));
      eapply alg_unit_body;
        [ eapply (alg_params_of_entries (n - 1)); [ exact HΓ | exact (ext_entries_app_r _ _ _ _ HXl) | lets_bound | exact Ha | exact Hps | exact HR ]
        | exact Ha | | exact Hs | exact Hsx | exact Hnd | exact (levels_abstractable_of_flag _ _ _ _ _ _ _ Hf1 Hf2 Hf3) ];
      eapply (alg_body_of_entries (n - 1));
        [ exact Hx | exact HXl | lets_bound | exact Hs | exact Hnd
        | exact (body_tagged_of_fill _ _ _ (body_xp_nopens _ _ _ _ _ Hx) Hsx HC Htags
                   (fun y Φ0 E A M σ Hp HE Hσ => proj1 (Hdefs y Φ0 E A M σ Hp HE Hσ)))
        | intros k Ψ0 H0' Hk Hle; apply HmH; [ exact (Hopens _ _ _ Hk) | lia ] | exact Hoff ]
  end.

(** The whole block, the universes included; [alg_type_complete_lets] below
    is the statement without them. *)
Lemma alg_type_complete_lets_all : forall n,
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> True) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> user_exp M ->
     exp_lets M <= n -> Γ ⊢a M ⟸ A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = gc_deps -> Ξ = gc_stack ->
     ext_entries n Γ Ψ /\ ext_entries n Γ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack ->
     (gunit_lets U <= n -> Γ ⊢aᵘ U) /\ (gunit_lets U' <= n -> Γ ⊢aᵘ U')) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> True).
Proof.
  intros n; induction n as [n IHn] using lt_wf_ind.
  (** A module expression, by generation, below the bound. *)
  assert (HmH : forall Γ' H0, gc_deps ⍮ gc_stack ⍮ Γ' ⊢ᵐ H0 ≈ H0 -> modexp_lets H0 < n -> Γ' ⊢aᵐ H0).
  { intros Γ' H0 HH0 Hlt; destruct (IHn _ Hlt) as (_ & IHt & _ & _ & _ & _ & IHu & _).
    eapply (alg_modexp_of_wf (modexp_lets H0)); [| | exact HH0 | lia ].
    - intros; eapply IHt; [ eassumption | reflexivity | reflexivity | apply user_exp_all | assumption ].
    - intros * HU0 HlU; exact (proj1 (IHu _ _ _ _ _ HU0 eq_refl eq_refl) HlU). }
  apply syntactic_wf_mut_ind; intros; try exact I; subst; destruct_univ;
    repeat match goal with IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl) end;
    repeat match goal with IH : user_exp ?M -> _ |- _ => specialize (IH (user_exp_all M)) end;
    try match goal with Hue : user_exp _ |- _ => clear Hue end;
    try match goal with |- (_ <= n -> _) /\ (_ <= n -> _) => split; intros end;
    repeat match goal with
           | IH : _ <= n -> _ |- _ => specialize (IH ltac:(lets_bound))
           | IH : (_ <= n -> ?P) /\ ?Q |- _ =>
               let H' := fresh in
               assert (H' : P /\ Q) by (split; [ apply (proj1 IH); lets_bound | exact (proj2 IH) ]);
               clear IH; rename H' into IH
           | IH : ?P /\ (_ <= n -> ?Q) |- _ =>
               let H' := fresh in
               assert (H' : P /\ Q) by (split; [ exact (proj1 IH) | apply (proj2 IH); lets_bound ]);
               clear IH; rename H' into IH
           end.
  (** The outer induction is needed only for the module expressions
      ([HmH]) and the expanded side of an expansion. *)
  all: try (lazymatch goal with |- _ ⊢aᵘ gu_open _ (gm_expand _) => fail | _ => clear IHn end).
  all: match goal with |- _ ⊢a a_elim _ _ _ _ _ ⟸ _ => idtac | |- _ ⊢a _ ⟸ _ =>
         gen_presups;
         (** A universe, [⊤] and [⊥] infer their own universe. *)
         try solve [ eapply alg_type_check_suniv;
                     [ assumption | mauto 3 | constructor | cbn; apply lvl_le_lit; lia ]
                   | eapply alg_type_check_typ_of;
                     [ assumption | mauto 3 | constructor | cbn; first [ exact I | lia ] ] ];
         (** A small universe at a level term infers the normal form of the
             universe above it. *)
         try match goal with
           | |- _ ⊢a a_univ ?M ⟸ a_univ (succl ?M) =>
               match goal with Hc : alg_type_check ?G (a_level _) M, HG : ⊢ ?G |- _ =>
                 destruct (alg_type_check_level_infer HG Hc) as (? & ? & ?) end;
               assert (HSU : Γ ⊢ Type⟨succl M⟩ : Typeω@0)
                 by (eapply wf_univ_large_tm; [ assumption | eapply wf_succl; eassumption ]);
               destruct (soundness_ty HSU) as [W [HW HWe]];
               econstructor; [ eapply alg_type_infer_suniv; eassumption |];
               apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe
           end;
         (** The level forms infer a type of levels below the one they are
             checked against. *)
         try solve [ lazymatch goal with
           | |- alg_type_check _ (a_level _) (a_llit _) =>
               eapply alg_type_check_level_of; [ assumption | constructor | lia ]
           | |- alg_type_check _ (a_level _) (a_succl ?M) =>
               match goal with Hc : alg_type_check ?G (a_level _) M, HG : ⊢ ?G |- _ =>
                 destruct (alg_type_check_level_infer HG Hc) as (? & ? & ?) end;
               eapply alg_type_check_level_of; [ assumption | constructor; eassumption | lia ]
           | |- alg_type_check _ (a_level _) (a_maxl ?M ?N) =>
               match goal with Hc : alg_type_check ?G (a_level _) M, HG : ⊢ ?G |- _ =>
                 destruct (alg_type_check_level_infer HG Hc) as (? & ? & ?) end;
               match goal with Hc : alg_type_check ?G (a_level _) N, HG : ⊢ ?G |- _ =>
                 destruct (alg_type_check_level_infer HG Hc) as (? & ? & ?) end;
               eapply alg_type_check_level_of; [ assumption | constructor; eassumption | lia ]
           end ];
         mauto 4 using alg_subtyping_complete, alg_type_check_subtyp | _ => idtac end.
  (** A record's type former, a projection and a tuple ([alg_record_complete],
      [alg_proj_complete], [alg_tuple_complete]); the fields of a tuple are
      below its bound on [let]s ([tuple_field_lets]). *)
  all: try solve [ eapply alg_record_complete; eassumption ].
  all: try solve [ eapply alg_proj_complete; eassumption ].
  all: try match goal with
    | HTt : _ ⊢ ?T : Typeω@?i, HTc : _ ⊢a ?T ⟸ Typeω@?i, HTe : _ ⊢ ?T ≈ apps_exp (a_record _) _ : _,
      HMs : forall k f M U, List.nth_error ?fs k = Some (f, M) -> _ -> _ = _ -> _ = _ -> user_exp M -> exp_lets M <= _ -> _ ⊢a M ⟸ _,
      Hbd : exp_lets (a_tuple ?T ?fs) <= _ |- _ ⊢a a_tuple ?T ?fs ⟸ _ =>
        eapply alg_tuple_complete; [ exact HTt | exact HTc | exact HTe | eassumption .. |];
        let k := fresh "k" in let f := fresh "f" in let M := fresh "M" in let U := fresh "U" in
        let Hk := fresh "Hk" in let Hfk := fresh "Hfk" in
        intros k f M U Hk Hfk; apply (HMs _ _ _ _ Hk Hfk eq_refl eq_refl (user_exp_all _));
        pose proof (tuple_field_lets T fs k f M Hk); lia
    end.
  (** A member, at the normal form of the type its module's description
      reads; the module, by generation. *)
  all: try match goal with
    | HH : _ ⍮ _ ⍮ ?G ⊢ᵐ ?H0 ≈ ?H0, Hm : mdenote _ _ ?G (me_mem ?H0 ?x0) _, Ht : mdesc_type _ = Some ?A0,
      HA : ?G ⊢ ?A0 : ?Srt, HS : type_sort ?Srt, Hb : exp_lets (a_mem ?H0 ?x0) <= _ |-?G ⊢a a_mem ?H0 ?x0 ⟸ ?A0 =>
        cbn [exp_lets] in Hb;
        let W := fresh "W" in let HW := fresh "HW" in
        apply (alg_type_check_of_infer_nbe HS HA); intros W HW;
        eapply alg_type_infer_mem; [ apply HmH; [ exact HH | lia ] | exact Hm | exact Ht | exact HW ]
    end.
  (** A type of levels at [LevelSort]: its own sort. *)
  - econstructor; [ apply alg_type_infer_level |].
    econstructor; [ exact (nbe_ty_level_sort_self H) | exact (nbe_ty_level_sort_self H) | apply alg_subtyping_nf_refl ].
  (** The introduction of [⊤] at [⊤]. *)
  - apply alg_tt_complete; assumption.
  (** Ex falso, conjunctions and their proofs. *)
  - match goal with H : ?G ⊢ ?C : ?Srt, Hs : type_sort ?Srt, Hl : level_closed_sort _ ?Srt |- ?G ⊢a efq _ return ?C ⟸ ?C =>
      eapply (alg_absurd_complete (S := Srt)); eassumption end.
  - match goal with HG : ⊢ ?G, HGP : ⊢ ?G ▹{ak_propositional} ?P |- ?G ⊢a Σₚ ?P ?Q ⟸ _ =>
      apply alg_type_check_prop_of; [ exact HG |];
      apply alg_type_infer_and; apply alg_type_check_prop_infer; assumption end.
  - eapply alg_conj_complete; eassumption.
  - match goal with HG : ⊢ ?G, HM : ?G ⊢ ?M : Σₚ ?P ?Q |- _ ⊢a a_left ?M ⟸ _ =>
      eapply (alg_left_complete HG (and_typed_of_proof HM)); eassumption end.
  - match goal with HG : ⊢ ?G, HM : ?G ⊢ ?M : Σₚ ?P ?Q |- _ ⊢a a_right ?M ⟸ _ =>
      eapply (alg_right_complete HG (and_typed_of_proof HM) HM); eassumption end.
  (** The type former and a constructor: at the normal forms of their
      types. *)
  - destruct (decl_of_lookup _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)) as [HD Hc].
    destruct (ind_ty_typed _ _ _ _ _ _ HD Hc ltac:(eassumption) ltac:(eassumption)) as [j Hj].
    destruct (soundness_ty Hj) as [W [HW HWe]].
    econstructor; [ eapply alg_type_infer_ind_case; eassumption | apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe ].
  - assert (HΓ1 : ⊢ Γ) by assumption.
    match goal with Hl : ind_lookup _ _ _ = Some _, Hk : ind_member _ _ = Some _, Hcon : ind_con _ _ = Some _ |- _ =>
      destruct (con_ty_typed _ _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓ1) (decls_of_ctx _ _ _ HΓ1) Hl Hk Hcon HΓ1) as [j Hj] end.
    destruct (soundness_ty Hj) as [W [HW HWe]].
    econstructor; [ eapply alg_type_infer_con; eassumption | apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe ].
  (** The eliminator ([alg_elim_complete]): its parts by the induction
      hypotheses, under the bound on [let]s ([elim_lets_parts]). *)
  - match goal with
    | Hl : ind_lookup _ _ ?p = Some ?D, Hm : ind_member ?D ?m = Some ?Mm,
      Hb : List.nth_error ?Bks ?m = Some ?bm, HPl : List.length ?Ps = im_np ?D ?Mm,
      Hbd : exp_lets (a_elim ?r ?p _ ?m ?Bks ?M) <= _,
      HAt : forall k Mk b, ind_member ?D k = Some Mk -> List.nth_error ?Bks k = Some b -> _ ⊢ eb_motive b : abs_kind_sort ?r Typeω@?i,
      HUs : forall k P T, List.nth_error ?Ps k = Some P -> List.nth_error (tele_insts (im_params ?D ?Mm) Id ?Ps) k = Some T ->
              _ = _ -> _ = _ -> user_exp P -> exp_lets P <= _ -> _ ⊢a P ⟸ T,
      HZs : forall k Mk b, ind_member ?D k = Some Mk -> List.nth_error ?Bks k = Some b ->
              _ = _ -> _ = _ -> ext_entries _ _ (_ ▹{ak_relevant} eb_scrutinee_type b) /\ _,
      HAs : forall k Mk b, ind_member ?D k = Some Mk -> List.nth_error ?Bks k = Some b -> _ = _ -> _ = _ ->
              user_exp (eb_motive b) -> exp_lets (eb_motive b) <= _ -> _ ⊢a eb_motive b ⟸ _,
      HBs : forall k Mk b c gs n0 B, ind_member ?D k = Some Mk -> List.nth_error ?Bks k = Some b -> ind_con Mk c = Some gs ->
              List.In (c, n0, B) (eb_brs b) -> _ = _ -> _ = _ -> user_exp B -> exp_lets B <= _ -> _ ⊢a B ⟸ _ |- _ =>
        destruct (elim_lets_parts r p (List.firstn (ind_nu D) Ps) m Bks M) as (HLu & HLz & HLa & HLb & _);
        assert (HΓe : ⊢ Γ) by (gen_presups; assumption);
        destruct (decl_of_lookup _ _ _ _ _ HΓe Hl) as [_ Hc];
        eapply (alg_elim_complete Γ p D m Mm bm Bks Ps M r i);
          [ exact Hl | exact Hm | exact Hb | exact HPl | eassumption | eassumption | eassumption
          | constructor; first [ assumption | unfold blocks_binder_count_ok; assumption ] | | | | ];
        [ intros j U T HU HT
        | intros j Mj b Hj Hbj; destruct (HZs _ _ _ Hj Hbj eq_refl eq_refl) as [HE _];
          apply (ext_entries_head _ _ _ _ HE); cbn [centry_lets];
          pose proof (HLz b (List.nth_error_In _ _ Hbj)); lia
        | intros j Mj b Hj Hbj; apply (HAs _ _ _ Hj Hbj eq_refl eq_refl (user_exp_all _));
          pose proof (HLa b (List.nth_error_In _ _ Hbj)); lia
        | intros j Mj b c gs n1 B Hj Hbj Hcon Hin; apply (HBs _ _ _ _ _ _ _ Hj Hbj Hcon Hin eq_refl eq_refl (user_exp_all _));
          pose proof (HLb b _ (List.nth_error_In _ _ Hbj) Hin); cbn [snd] in *; lia ];
        assert (Hj : j < ind_nu D)
          by (assert (j < List.length (List.firstn (ind_nu D) Ps)) by (apply List.nth_error_Some; congruence);
              rewrite List.length_firstn in *; lia);
        assert (HUP : List.nth_error Ps j = Some U)
          by (rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 by (rewrite List.length_firstn; unfold im_np in *; lia);
              exact HU);
        assert (HFl : List.length (List.firstn (ind_nu D) Ps) = List.length (ind_uparams D))
          by (rewrite List.length_firstn; change (List.length (ind_uparams D)) with (ind_nu D); unfold im_np in HPl; lia);
        assert (HTP : List.nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T)
          by (rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; unfold im_params;
              rewrite tele_insts_app by (try exact (decl_closed_ass _ Hc); exact HFl);
              rewrite List.nth_error_app1; [ exact HT | rewrite length_tele_insts by exact (decl_closed_ass _ Hc); unfold ind_nu in Hj; lia ]);
        apply (HUs j U T HUP HTP eq_refl eq_refl (user_exp_all _));
        pose proof (HLu U (List.nth_error_In _ _ HU)); lia
    end.
  (** [Π] at a large universe and at a small one ([alg_pi_complete]). *)
  - match goal with HG : ⊢ ?G, HAt : ?G ⊢ ?A : abs_kind_sort ?κd ?U |- ?G ⊢a a_pi ?κd _ ?A _ ⟸ _ =>
      eapply (alg_pi_complete _ U); [ exact HG | apply wf_is_univ_large; exact HG | exact HAt | eassumption .. ] end.
  - match goal with HG : ⊢ ?G, HL : ?G ⊢ ?L : Level@_, HAt : ?G ⊢ ?A : abs_kind_sort ?κd Type⟨?L⟩ |- ?G ⊢a a_pi ?κd _ ?A _ ⟸ _ =>
      eapply (alg_pi_complete _ Type⟨L⟩); [ exact HG | eapply wf_is_univ_small; exact HL | exact HAt | eassumption .. ] end.
  (** [λ] ([alg_fn_complete]) and an application ([alg_app_complete]). *)
  - match goal with HAt : ?G ⊢ ?A : ?Srt, HSk : sort_kind ?Srt _, HG : ⊢ ?G |- ?G ⊢a λ ?A _ ⟸ _ =>
      eapply (alg_fn_complete HG HAt HSk); eassumption end.
  - match goal with HG : ⊢ ?G, HM : ?G ⊢ ?M : a_pi _ _ _ _ |- ?G ⊢a ?M $ _ ⟸ _ =>
      eapply (alg_app_complete HG HM); eassumption end.
  (** A local definition ([alg_let_complete]) and a module [let]
      ([alg_let_mod_complete]). *)
  - match goal with
    | HAt : ?G ⊢ ?A : ?Srt, HS : type_sort ?Srt, HAc : ?G ⊢a ?A ⟸ ?Srt, HM : ?G ⊢ ?M : ?A, HMc : ?G ⊢a ?M ⟸ ?A,
      HC : ?G ▸ ?A ≔ ?M ⊢ ?C : ?SrtC, Hlc : level_closed_sort ?Srt ?SrtC,
      HBc : ?G ▸ ?A ≔ ?M ⊢a ?B ⟸ ?C, HG : ⊢ ?G |- ?G ⊢a ℓ ?A ≔ ?M in ?B ⟸ _ =>
        exact (alg_let_complete _ _ _ _ _ _ _ HG HAt HS HAc HM HMc HC Hlc HBc)
    end.
  - match goal with
    | HU : _ ⍮ _ ⍮ ?G ⊢ᵘ ?U ≈ ?U, HUa : ?G ⊢aᵘ ?U /\ _, HCt : ?G ▹ₘ ?U ⊢ ?C : ?Srt, Hms : module_body_sort ?Srt,
      HBc : ?G ▹ₘ ?U ⊢a ?B ⟸ ?C |- ?G ⊢a ℓₘ ?U in ?B ⟸ _ =>
        exact (alg_let_mod_complete _ _ _ _ _ HU (proj1 HUa) HCt Hms HBc)
    end.
  (** A variable, at the normal form of its type. *)
  - match goal with HA : ?G ⊢ ?A : ?S, HS : type_sort ?S |- ?G ⊢a #_ ⟸ ?A =>
      apply (alg_type_check_of_infer_nbe HS HA); intros W HW; eapply alg_type_infer_vlookup; eassumption end.
  (** Extensions, entry by entry. *)
  - split; apply ext_entries_nil.
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl HXr] end.
    split; apply ext_entries_cons; try assumption; intros Hle; cbn [centry_lets alg_entry] in *.
    + pose proof (ext_eq_ctx_left _ _ _ _ _ H) as HΨ.
      match goal with IHA : exp_lets A <= n -> _ ⊢a A ⟸ ?S, HSk : sort_kind ?S _, HA : _ ⊢ A : ?S |- _ =>
        exact (alg_entry_ass_of_check _ _ _ _ HΨ HA HSk (IHA Hle)) end.
    + pose proof (ext_eq_ctx_right _ _ _ _ _ H) as HΨ'.
      match goal with IHA : exp_lets A' <= n -> _ ⊢a A' ⟸ ?S, HSk : sort_kind ?S _, HA : _ ⊢ A' : ?S |- _ =>
        exact (alg_entry_ass_of_check _ _ _ _ HΨ' HA HSk (IHA Hle)) end.
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl HXr] end.
    split; apply ext_entries_cons; try assumption; intros Hle; cbn [centry_lets alg_entry] in *.
    + pose proof (ext_eq_ctx_left _ _ _ _ _ H) as HΨ.
      match goal with IHA : exp_lets A <= n -> _ ⊢a A ⟸ ?S, HS : type_sort ?S, IHM : exp_lets M <= n -> _ ⊢a M ⟸ _ |- _ =>
        destruct (alg_type_check_sort_infer HΨ HS (IHA ltac:(lia))) as (UA & r & u & Hj & Hs);
        split; [ eauto | exact (IHM ltac:(lia)) ] end.
    + pose proof (ext_eq_ctx_right _ _ _ _ _ H) as HΨ'.
      match goal with IHA : exp_lets A' <= n -> _ ⊢a A' ⟸ ?S, HS : type_sort ?S, IHM : exp_lets M' <= n -> _ ⊢a M' ⟸ _ |- _ =>
        destruct (alg_type_check_sort_infer HΨ' HS (IHA ltac:(lia))) as (UA & r & u & Hj & Hs);
        split; [ eauto | exact (IHM ltac:(lia)) ] end.
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl HXr] end.
    split; apply ext_entries_cons; try assumption; intros Hle; cbn [centry_lets alg_entry] in *.
    + match goal with IHU : (gunit_lets U <= n -> _ ⊢aᵘ U) /\ _ |- _ => exact (proj1 IHU Hle) end.
    + match goal with IHU : (gunit_lets U' <= n -> ?G ⊢aᵘ U') /\ _, _ : _ ⍮ _ ⍮ ?G ⊢ᵘ U' ≈ U' |- _ => exact (proj1 IHU Hle) end.
  - (** A definition with a module part: as a definition and as a slot. *)
    match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl HXr] end.
    split; apply ext_entries_cons; try assumption; intros Hle; cbn [centry_lets alg_entry] in *.
    + pose proof (ext_eq_ctx_left _ _ _ _ _ H) as HΨ.
      match goal with IHA : exp_lets A <= n -> _ ⊢a A ⟸ _, IHM : exp_lets M <= n -> _ ⊢a M ⟸ _,
                      IHU : (gunit_lets U <= n -> _ ⊢aᵘ U) /\ _ |- _ =>
        destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ (IHA ltac:(lia))) as [UA [u [Hj [Hu _]]]];
        split; [ split; [ eauto | exact (IHM ltac:(lia)) ] | exact (proj1 IHU ltac:(lia)) ] end.
    + pose proof (ext_eq_ctx_right _ _ _ _ _ H) as HΨ'.
      match goal with IHA : exp_lets A' <= n -> _ ⊢a A' ⟸ _, IHM : exp_lets M' <= n -> _ ⊢a M' ⟸ _,
                      IHU : (gunit_lets U' <= n -> ?G ⊢aᵘ U') /\ _, _ : _ ⍮ _ ⍮ ?G ⊢ᵘ U' ≈ U' |- _ =>
        destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ' (IHA ltac:(lia))) as [UA [u [Hj [Hu _]]]];
        split; [ split; [ eauto | exact (IHM ltac:(lia)) ] | exact (proj1 IHU ltac:(lia)) ] end.
  (** Units: the parameters, relevant, as checked parameters
      ([alg_params_of_entries]); a body from the entries of its expansion
      that are its own, each of the sort its tag says
      ([body_tagged_of_fill_left]), and the targets of its opens. *)
  - match goal with
    | HX : ext_entries _ _ (body_ctx Φx ++ Δ) /\ _ |- _ => destruct HX as [HXl _]
    end.
    match goal with
    | Hx : body_xp _ _ (Δ ++ Γ) Φ Φx, HXe : _ ⍮ _ ⍮ Γ ⊢ˣ body_ctx Φx ++ Δ ≈ _, HD : _ ⍮ _ ⍮ Γ ⊢ˣ Δ ≈ _,
      Hs : body_shape Φ Φ', Hsx : body_shape Φx Φx', Hnd : List.NoDup (gm_names Φ),
      Ho : forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> _ ⍮ _ ⍮ _ ⊢ᵐ H ≈ H,
      Hps : forall k, parameter_sort _ (?ps k),
      HR : forall Δ1 κ T Δ2, Δ = Δ1 ++ ce_ass κ T :: Δ2 -> _ ⊢ T : ?ps (List.length Δ2) |- _ =>
        destruct (body_shape_refl _ _ Hs) as (Hs1 & _ & _);
        destruct (body_shape_refl _ _ Hsx) as (Hsx1 & _ & _);
        pose proof (ext_eq_ctx_left _ _ _ _ _ HXe) as HCx; rewrite <- List.app_assoc in HCx;
        assert (HΓ : ⊢ Γ) by exact (ctx_app_wf_tail _ _ _ _ (ext_eq_ctx_left _ _ _ _ _ HD));
        rewrite gunit_lets_mk in *; cbn [moddef_lets] in *;
        eapply alg_unit_body;
          [ eapply (alg_params_of_entries n); [ exact HΓ | exact (ext_entries_app_r _ _ _ _ HXl) | lia | assumption | exact Hps | exact HR ]
          | assumption | | exact Hs1 | exact Hsx1 | exact Hnd | eapply levels_abstractable_of_flag; eassumption ];
        eapply alg_body_of_entries;
          [ eassumption | exact HXl | lia | exact Hs1 | rewrite (body_xp_names _ _ _ _ _ Hx); exact Hnd
          | eapply (body_tagged_of_fill_left _ _ Φx' _ (body_xp_nopens _ _ _ _ _ Hx) Hsx HCx); eassumption | | eassumption ];
        intros k Ψ0 H0' Hk Hle; apply HmH; [ exact (Ho _ _ _ Hk) | lia ]
    end.
  - match goal with
    | HX : ext_entries _ _ (body_ctx Φx' ++ Δ') /\ _ |- _ => destruct HX as [HXr _]
    end.
    match goal with
    | Hx : body_xp _ _ (Δ' ++ Γ) Φ' Φx', HXe : _ ⍮ _ ⍮ Γ ⊢ˣ body_ctx Φx' ++ Δ' ≈ _, HD : _ ⍮ _ ⍮ Γ ⊢ˣ Δ ≈ Δ',
      Hs : body_shape Φ Φ', Hsx : body_shape Φx Φx', Hnd : List.NoDup (gm_names Φ),
      Ho : forall k Ψ H, List.nth_error (body_opens Φ' Φx') k = Some (Ψ, H) -> _ ⍮ _ ⍮ _ ⊢ᵐ H ≈ H,
      Hps : forall k, parameter_sort _ (?ps k),
      HR : forall Δ1 κ T Δ2, Δ' = Δ1 ++ ce_ass κ T :: Δ2 -> _ ⊢ T : ?ps (List.length Δ2) |- _ =>
        destruct (body_shape_refl _ _ Hs) as (_ & Hs2 & Hn);
        destruct (body_shape_refl _ _ Hsx) as (_ & Hsx2 & _);
        pose proof (ext_eq_ctx_left _ _ _ _ _ HXe) as HCx; rewrite <- List.app_assoc in HCx;
        assert (HΓ : ⊢ Γ) by exact (ctx_app_wf_tail _ _ _ _ (ext_eq_ctx_left _ _ _ _ _ HD));
        rewrite gunit_lets_mk in *; cbn [moddef_lets] in *;
        eapply alg_unit_body;
          [ eapply (alg_params_of_entries n); [ exact HΓ | exact (ext_entries_app_r _ _ _ _ HXr) | lia | assumption | exact Hps | exact HR ]
          | assumption | | exact Hs2 | exact Hsx2 | rewrite <- Hn; exact Hnd | eapply levels_abstractable_of_flag; eassumption ];
        eapply alg_body_of_entries;
          [ eassumption | exact HXr | lia | exact Hs2 | rewrite (body_xp_names _ _ _ _ _ Hx), <- Hn; exact Hnd
          | eapply (body_tagged_of_fill_right _ Φx _ _ (body_xp_nopens _ _ _ _ _ Hx) Hsx HCx); eassumption | | eassumption ];
        intros k Ψ1 H1' Hk Hle; apply HmH; [ exact (Ho _ _ _ Hk) | lia ]
    end.
  (** An alias: its parameters, and its target, by generation. *)
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl _] end.
    rewrite gunit_lets_mk in *; cbn [moddef_lets] in *.
    match goal with HD : _ ⍮ _ ⍮ ?G ⊢ˣ _ ≈ _ |- ?G ⊢aᵘ _ => pose proof (ctx_app_wf_tail _ _ _ _ (ext_eq_ctx_left _ _ _ _ _ HD)) as HΓ end.
    econstructor; [ eapply (alg_params_of_entries n); [ exact HΓ | exact HXl | lia | assumption | eassumption | eassumption ]
                  | assumption | | eapply levels_abstractable_of_flag; eassumption | eassumption ].
    apply HmH; [ first [ eapply wf_modexp_eq_refl_left; eassumption | eassumption ] | lia ].
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [_ HXr] end.
    rewrite gunit_lets_mk in *; cbn [moddef_lets] in *.
    match goal with HD : _ ⍮ _ ⍮ ?G ⊢ˣ _ ≈ _ |- ?G ⊢aᵘ _ => pose proof (ctx_app_wf_tail _ _ _ _ (ext_eq_ctx_left _ _ _ _ _ HD)) as HΓ end.
    econstructor; [ eapply (alg_params_of_entries n); [ exact HΓ | exact HXr | lia | assumption | eassumption | eassumption ]
                  | assumption | | eapply levels_abstractable_of_flag; eassumption | eassumption ].
    apply HmH; [ first [ eapply wf_modexp_eq_refl_left; eassumption | eassumption ] | lia ].
  (** Flattening: the alias of the literal, and the unit over both
      telescopes. *)
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl _] end.
    rewrite gunit_lets_mk in *; cbn [moddef_lets] in *.
    match goal with HD : _ ⍮ _ ⍮ ?G ⊢ˣ _ ≈ _ |- ?G ⊢aᵘ _ => pose proof (ctx_app_wf_tail _ _ _ _ (ext_eq_ctx_left _ _ _ _ _ HD)) as HΓ end.
    match goal with HU : _ ⊢aᵘ _ /\ _ |- _ =>
      apply alg_unit_alias; [ eapply (alg_params_of_entries n); [ exact HΓ | exact HXl | lia | assumption | eassumption | eassumption ]
                            | assumption | apply alg_modexp_lit, (proj1 HU) | eapply levels_abstractable_of_flag; eassumption
                            | eassumption ] end.
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl _] end.
    rewrite gunit_lets_mk, ctx_lets_app in *.
    match goal with HD : _ ⍮ _ ⍮ ?G ⊢ˣ _ ≈ _ |- ?G ⊢aᵘ _ => pose proof (ctx_app_wf_tail _ _ _ _ (ext_eq_ctx_left _ _ _ _ _ HD)) as HΓ end.
    match goal with HU : _ ⊢aᵘ _ /\ _ |- _ =>
      eapply alg_unit_flatten; [ eapply (alg_params_of_entries n); [ exact HΓ | exact HXl | lia | assumption | eassumption | eassumption ]
                               | assumption | exact (proj1 HU) | eapply levels_abstractable_of_flag; eassumption ] end.
  (** The expansion of a body: its own side, and the expanded one.  The
      expanded unit's derivation is no subderivation; its parts, read off
      it ([unit_full_of_eq]), have fewer [let]s than it, so the outer
      induction checks them, as for a body. *)
  - first [ repeat match goal with H0 : _ /\ _ |- _ => destruct H0 end; solve [ auto ] | expand_case ].
  - first [ repeat match goal with H0 : _ /\ _ |- _ => destruct H0 end; solve [ auto ] | expand_case ].
  (** Symmetry and transitivity: the sides the induction hypotheses give. *)
  - repeat match goal with H0 : _ /\ _ |- _ => destruct H0 end; solve [ auto ].
  - repeat match goal with H0 : _ /\ _ |- _ => destruct H0 end; solve [ auto ].
  - repeat match goal with H0 : _ /\ _ |- _ => destruct H0 end; solve [ auto ].
  - repeat match goal with H0 : _ /\ _ |- _ => destruct H0 end; solve [ auto ].
Qed.

Lemma alg_type_complete_lets : forall n,
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> True) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> user_exp M ->
     exp_lets M <= n -> Γ ⊢a M ⟸ A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = gc_deps -> Ξ = gc_stack ->
     ext_entries n Γ Ψ /\ ext_entries n Γ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack ->
     (gunit_lets U <= n -> Γ ⊢aᵘ U) /\ (gunit_lets U' <= n -> Γ ⊢aᵘ U')) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = gc_deps -> Ξ = gc_stack ->
     (modexp_lets H <= n -> Γ ⊢aᵐ H) /\ (modexp_lets H' <= n -> Γ ⊢aᵐ H')).
Proof.
  intros n; destruct (alg_type_complete_lets_all n) as (H1 & H2 & H3 & H4 & _ & H5 & H6 & _).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 _)))))).
  (** A module expression and its other side, by generation. *)
  assert (Hm : forall Γ H, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> modexp_lets H <= n -> Γ ⊢aᵐ H).
  { intros Γ H HH Hl; eapply (alg_modexp_of_wf n); [| | exact HH | exact Hl ].
    - intros; eapply H2; [ eassumption | reflexivity | reflexivity | apply user_exp_all | assumption ].
    - intros * HU HlU; exact (proj1 (H6 _ _ _ _ _ HU eq_refl eq_refl) HlU). }
  intros * HH -> ->; split; intros Hl;
    [ exact (Hm _ _ (wf_modexp_eq_refl_left HH) Hl) | exact (Hm _ _ (wf_modexp_eq_refl_right HH) Hl) ].
Qed.

Lemma alg_type_complete_all :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> True) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> user_exp M -> Γ ⊢a M ⟸ A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aˣ Ψ /\ Γ ⊢aˣ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aᵘ U /\ Γ ⊢aᵘ U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aᵐ H /\ Γ ⊢aᵐ H').
Proof.
  repeat split; intros; try exact I.
  - eapply (alg_type_complete_lets (exp_lets M)); eauto.
  - eapply (ext_entries_alg (ctx_lets Ψ + ctx_lets Ψ'));
      [ exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (ctx_lets Ψ + ctx_lets Ψ')))))) _ _ _ _ _ H H0 H1)) | lia ].
  - eapply (ext_entries_alg (ctx_lets Ψ + ctx_lets Ψ'));
      [ exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (ctx_lets Ψ + ctx_lets Ψ')))))) _ _ _ _ _ H H0 H1)) | lia ].
  - eapply (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (gunit_lets U + gunit_lets U'))))))) _ _ _ _ _ H H0 H1)); lia.
  - eapply (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (gunit_lets U + gunit_lets U'))))))) _ _ _ _ _ H H0 H1)); lia.
  - eapply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (modexp_lets H + modexp_lets H'))))))) _ _ _ _ _ H0 H1 H2)); lia.
  - eapply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (modexp_lets H + modexp_lets H'))))))) _ _ _ _ _ H0 H1 H2)); lia.
Qed.

Lemma alg_type_check_complete : forall {Γ A M},
    user_exp M ->
    Γ ⊢ M : A ->
    Γ ⊢a M ⟸ A.
Proof.
  intros * Hue HM; exact (proj1 (proj2 alg_type_complete_all) _ _ _ _ _ HM eq_refl eq_refl Hue).
Qed.

Lemma alg_ext_complete : forall {Γ Ψ}, gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ -> Γ ⊢aˣ Ψ.
Proof. intros * HΨ; exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 alg_type_complete_all)))) _ _ _ _ _ HΨ eq_refl eq_refl)). Qed.

Lemma alg_unit_complete : forall {Γ U}, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> Γ ⊢aᵘ U.
Proof. intros * HU; exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 alg_type_complete_all))))) _ _ _ _ _ HU eq_refl eq_refl)). Qed.

Lemma alg_modexp_complete : forall {Γ H}, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> Γ ⊢aᵐ H.
Proof. intros * HH; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 alg_type_complete_all))))) _ _ _ _ _ HH eq_refl eq_refl)). Qed.



Hint Resolve alg_type_check_complete : mctt.

Corollary alg_type_infer_complete : forall {Γ A M},
    user_exp M ->
    Γ ⊢ M : A ->
    exists B, Γ ⊢a M ⟹ B /\ Γ ⊢a B ⊆ A.
Proof.
  intros.
  assert (Γ ⊢a M ⟸ A) as Hcheck by mauto 4 using alg_type_check_complete.
  inversion_clear Hcheck.
  firstorder.
Qed.

Hint Resolve alg_type_infer_complete : mctt.

(** The normal forms below a universe in the order on normal forms are the
    universes below it. *)
Lemma alg_subtyping_nf_univ_inv : forall W u,
    ⊢anf W ⊆ universe_nf_to_nf u ->
    exists v, W = universe_nf_to_nf v /\ universe_nf_le v u.
Proof.
  intros W [[d ys] | j] H; cbn in H; inversion H; subst; try refl_case_absurd.
  all: match goal with
       | |- exists v, univⁿ ?c ?xs = _ /\ _ => exists (universe_small (c, xs))
       | |- exists v, Typeωⁿ@?i = _ /\ _ => exists (universe_large i)
       end; split; [ reflexivity | cbn; first [ assumption | exact I ] ].
Qed.

(** Completeness at a universe: a type of a universe term [T] infers a
    universe below the normal form of [T].  The bound is the normal form of
    [T] and not [T]'s universe index read off syntactically: the sorts the
    atoms of a universe normal form carry are those of their types only in a
    normal form ([soundness_lvl_well_scoped]).  At [Typeω@i] this is
    [alg_type_infer_large_typ_complete], at [Type@n]
    [alg_type_infer_typ_complete_lit], at [Type⟨t⟩]
    [alg_type_infer_typ_complete_tm]. *)
Corollary alg_type_infer_typ_complete : forall {Γ T A},
    user_exp A ->
    univ_term T ->
    Γ ⊢ A : T ->
    exists u v, nbe_ty_f Γ T (universe_nf_to_nf u) /\ Γ ⊢a A ⟹ universe_nf_to_nf v /\ universe_nf_le v u.
Proof.
  intros * HA HT HAT.
  pose proof (alg_type_check_complete HA HAT) as Hcheck.
  assert (HΓ : ⊢ Γ) by exact (presup_exp_ctx HAT).
  destruct (alg_type_check_infer_below HΓ Hcheck) as (A' & B' & Hinfer & Hnbe2 & Hnfsub).
  destruct (nbe_ty_univ_term HT Hnbe2) as [u ->].
  destruct (alg_subtyping_nf_univ_inv _ _ Hnfsub) as (v & -> & Hle).
  exists u, v; split; [ exact Hnbe2 | split; [ exact Hinfer | exact Hle ] ].
Qed.

Corollary alg_type_infer_large_typ_complete : forall {Γ i A},
    user_exp A ->
    Γ ⊢ A : Typeω@i ->
    exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ universe_nf_le u (universe_large i).
Proof.
  intros * HA HAi.
  destruct (alg_type_infer_typ_complete HA (univ_term_typ i) HAi) as (u & v & Hu & Hinf & Hle).
  apply nbe_ty_typ_univ_nf in Hu as ->.
  exists (universe_nf_to_nf v), v; split; [ exact Hinf | split; [ apply is_univ_nf_univ_nf | exact Hle ] ].
Qed.

Hint Resolve alg_type_infer_large_typ_complete : mctt.

(** At a literal small universe, with the old precise shape: the inferred
    universe is a small universe at a literal level below [n] (an atom is
    never below a literal, [lvl_le_lit_closed]). *)
Corollary alg_type_infer_typ_complete_lit : forall {Γ n A},
    user_exp A ->
    Γ ⊢ A : Type@n ->
    exists m, Γ ⊢a A ⟹ Typeⁿ@m /\ m <= n.
Proof.
  intros * HA HAn.
  destruct (alg_type_infer_typ_complete HA (univ_term_suniv _) HAn) as (u & v & Hu & Hinf & Hle).
  apply nbe_ty_lit_univ_nf in Hu as ->.
  destruct v as [[c xs] | i]; cbn in Hle; [| contradiction].
  pose proof (lvl_le_lit_closed _ _ Hle) as Hxs; cbn in Hxs; subst xs.
  rewrite lvl_le_correct in Hle; specialize (Hle _ lvl_adm_zero); unfold lvl_eval, lvl_lit in Hle; cbn in Hle.
  destruct c as [a m]; assert (a = 0) as -> by ordinal_solve.
  exists m; split; [ exact Hinf | ordinal_solve ].
Qed.

(** At a level term [t]: the inferred universe is small, at a canonical
    level below the normal form of [t]. *)
Corollary alg_type_infer_typ_complete_tm : forall {Γ t A},
    user_exp A ->
    Γ ⊢ A : Type⟨t⟩ ->
    exists L L', Γ ⊢a A ⟹ nf_univ_of L /\ nbe_f Γ t Level (nf_lvl_of L') /\ lvl_le L L'.
Proof.
  intros * HA HAt.
  destruct (alg_type_infer_typ_complete HA (univ_term_suniv _) HAt) as (u & v & Hu & Hinf & Hle).
  destruct (nbe_ty_suniv_univ_nf Hu) as (L' & -> & HL').
  destruct v as [L | i]; cbn in Hle; [| contradiction].
  exists L, L'; split; [ exact Hinf | split; [ exact HL' | exact Hle ] ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve alg_type_infer_normal : mctt.
#[export]
Hint Resolve alg_type_check_typ_implies_alg_type_infer_typ : mctt.
#[export]
Hint Resolve alg_type_check_pi_implies_alg_type_infer_pi : mctt.
#[export]
Hint Resolve alg_type_check_subtyp : mctt.
#[export]
Hint Resolve alg_type_check_conv : mctt.
#[export]
Hint Resolve alg_type_check_complete : mctt.
#[export]
Hint Resolve alg_type_infer_complete : mctt.
#[export]
Hint Resolve alg_type_infer_large_typ_complete : mctt.
