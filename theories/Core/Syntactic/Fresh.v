(** * Freshness and Un-weakening

    A variable that does not occur can be dropped.  [exp_fresh k M] says that
    [#k] does not occur free in [M], and [unwk k] is the renaming that drops
    index [k]; together they invert [q^k ↑], the weakening that inserts a
    variable at position [k]:

    - [exp_unwk_wk]: dropping what was just inserted gives the term back,
      with no hypothesis;
    - [exp_unwk_spec]: inserting what was dropped gives the term back, when
      the dropped variable did not occur;
    - [exp_wk_fresh]: what [q^k ↑] produces never mentions [#k].

    Nothing here is a judgment: these are facts about terms and renamings.
    They are what the checker needs to turn a level that is typed in an
    extended context, and does not mention the new variable, into a level of
    the shorter one.  The same three facts are proved for normal and neutral
    forms, where the un-weakening has to produce a normal form again
    ([nf_unwk]) rather than go through [nf_to_exp]. *)
From Stdlib Require Import Arith Lia List PeanoNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Substitution.
From Mctt.Core.Syntactic.Levels Require Import Levels.
Import Syntax_Notations Wk_Notations.

(** ** Un-weakening

    [unwk k] fixes the indices below [k], sends [k] to itself (any value would
    do: a fresh term never looks at it) and decrements those above.  It is the
    renaming [q^k pred], so it acts on terms by [exp_wk] and needs no new
    recursion. *)
Definition unwk (k : nat) : wk := wk_qn k pred.

(** ** [#k] Does Not Occur

    One clause per syntactic sort, as for [exp_wk]: under [n] binders the
    index to avoid is [n + k].  A telescope shifts by its own length, and a
    module body by its binders, exactly as the weakenings do. *)
Fixpoint exp_fresh (k : nat) (M : exp) {struct M} : Prop :=
  match M with
  | a_typ _ | a_level _ | a_level_sort | a_llit _
  | a_prop | a_True | a_tt | a_False => True
  | a_univ M | a_succl M | a_left M | a_right M => exp_fresh k M
  | a_maxl M N | a_app M N | a_absurd M N => exp_fresh k M /\ exp_fresh k N
  | a_conj T M N => exp_fresh k T /\ exp_fresh k M /\ exp_fresh k N
  | a_ind _ _ | a_con _ _ _ | a_nlit _ | a_ntok => True
  | a_elim _ _ Us _ Bks M =>
      all_list (exp_fresh k) Us /\
      all_blocks (fun nm oZ A Bs => opt_all (exp_fresh (nm - 1 + k)) oZ /\ exp_fresh (nm + k) A /\
                                    all_brs (fun n B => exp_fresh (n + k) B) Bs) Bks /\ exp_fresh k M
  | a_pi _ A B | a_fn A B | a_and A B => exp_fresh k A /\ exp_fresh (S k) B
  | a_var x => x <> k
  | a_let b B => binding_fresh k b /\ exp_fresh (S k) B
  | a_mem H _ => modexp_fresh k H
  | a_record _ => True
  | a_tuple T fs => exp_fresh k T /\ all_list (fun f => exp_fresh k (snd f)) fs
  | a_proj _ M => exp_fresh k M
  end
with modexp_fresh (k : nat) (H : modexp) {struct H} : Prop :=
  match H with
  | me_unit _ => True
  | me_var x => x <> k
  | me_mem H _ => modexp_fresh k H
  | me_app H N => modexp_fresh k H /\ exp_fresh k N
  | me_lit U => gunit_fresh k U
  end
with binding_fresh (k : nat) (b : binding) {struct b} : Prop :=
  match b with
  | b_def A M => exp_fresh k A /\ exp_fresh k M
  | b_mod U => gunit_fresh k U
  end
with gunit_fresh (k : nat) (U : gunit) {struct U} : Prop :=
  match U with
  | gu_mk Δ D =>
      (fix tele_fresh (Δ : list centry) : Prop :=
         match Δ with
         | nil => True
         | cons e Δ' => centry_fresh (List.length Δ' + k) e /\ tele_fresh Δ'
         end) Δ
      /\ moddef_fresh (List.length Δ + k) D
  end
with moddef_fresh (k : nat) (D : moddef) {struct D} : Prop :=
  match D with
  | md_body sm Φ => gmod_fresh k Φ
  | md_alias E => modexp_fresh k E
  end
with gmod_fresh (k : nat) (Φ : gmod) {struct Φ} : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ _ E => gmod_fresh k Φ /\ gentry_fresh (gm_binders Φ + k) E
  | gm_open Φ H _ => gmod_fresh k Φ /\ modexp_fresh (gm_binders Φ + k) H
  end
with gentry_fresh (k : nat) (E : gentry) {struct E} : Prop :=
  match E with
  | ge_def _ _ _ A B => exp_fresh k A /\ match B with Some M => exp_fresh k M | None => True end
  | ge_mod _ U => gunit_fresh k U
  | ge_ind _ _ _ D Φ => gmod_fresh (ind_nu D + k) Φ
  | ge_def_mod _ A M U => exp_fresh k A /\ exp_fresh k M /\ gunit_fresh k U
  | ge_record _ _ R Φ => gmod_fresh (S (List.length (record_params R)) + k) Φ
  end
with centry_fresh (k : nat) (e : centry) {struct e} : Prop :=
  match e with
  | ce_ass A => exp_fresh k A
  | ce_def A M => exp_fresh k A /\ exp_fresh k M
  | ce_mod U => gunit_fresh k U
  | ce_dm A M U => exp_fresh k A /\ exp_fresh k M /\ gunit_fresh k U
  end.

(** The telescope clause of [gunit_fresh], as a definition of its own. *)
Fixpoint tele_fresh (k : nat) (Δ : list centry) : Prop :=
  match Δ with
  | nil => True
  | cons e Δ' => centry_fresh (List.length Δ' + k) e /\ tele_fresh k Δ'
  end.

(** The blocks clause of [exp_fresh], as a definition of its own. *)
Definition blocks_fresh (k : nat) (Bks : list eblock) : Prop :=
  all_blocks (fun nm oZ A Bs => opt_all (exp_fresh (nm - 1 + k)) oZ /\ exp_fresh (nm + k) A /\
                                all_brs (fun n B => exp_fresh (n + k) B) Bs) Bks.

(** ** Two Classes of Renaming

    A renaming that is the identity away from [k] fixes every term in which
    [#k] does not occur; a renaming that never hits [k] produces only such
    terms.  Both classes are closed under [q] and so under [q^n], at the index
    the binders shift it to. *)
Definition wk_id_away (k : nat) (χ : wk) : Prop := forall x, x <> k -> χ x = x.

Lemma wk_id_away_q : forall k χ, wk_id_away k χ -> wk_id_away (S k) (wk_q χ).
Proof. intros k χ H [|x] Hx; cbn; [ reflexivity | rewrite H by lia; reflexivity ]. Qed.

Lemma wk_id_away_qn : forall n k χ, wk_id_away k χ -> wk_id_away (n + k) (wk_qn n χ).
Proof. induction n; intros; cbn; [ assumption | apply wk_id_away_q; auto ]. Qed.

Definition wk_avoids (k : nat) (φ : wk) : Prop := forall x, φ x <> k.

Lemma wk_avoids_q : forall k φ, wk_avoids k φ -> wk_avoids (S k) (wk_q φ).
Proof. intros k φ H [|x]; cbn; [ lia | specialize (H x); lia ]. Qed.

Lemma wk_avoids_qn : forall n k φ, wk_avoids k φ -> wk_avoids (n + k) (wk_qn n φ).
Proof. induction n; intros; cbn; [ assumption | apply wk_avoids_q; auto ]. Qed.

#[local]
Hint Resolve wk_id_away_q wk_id_away_qn wk_avoids_q wk_avoids_qn : core.

(** One case of either mutual induction below: unfold the freshness and the
    weakening of the sort at hand, split the conjunctions, and apply the
    induction hypotheses. *)
#[local]
Ltac fresh_case :=
  intros; cbn [exp_fresh modexp_fresh binding_fresh gunit_fresh moddef_fresh gmod_fresh
               gentry_fresh centry_fresh exp_wk modexp_wk binding_wk gunit_wk moddef_wk
               gmod_wk gentry_wk centry_wk] in *;
  repeat match goal with
         | B : option exp |- _ => destruct B; cbn iota in *
         end;
  rewrite ?gunit_wk_mk;
  destruct_conjs;
  repeat split; f_equal;
  try match goal with |- Some _ = Some _ => f_equal end;
  eauto 6.

Lemma syn_fresh_id :
  (forall M k χ, exp_fresh k M -> wk_id_away k χ -> M[χ]ʷ = M) /\
  (forall H k χ, modexp_fresh k H -> wk_id_away k χ -> modexp_wk H χ = H) /\
  (forall b k χ, binding_fresh k b -> wk_id_away k χ -> binding_wk b χ = b) /\
  (forall U k χ, gunit_fresh k U -> wk_id_away k χ -> gunit_wk U χ = U) /\
  (forall D k χ, moddef_fresh k D -> wk_id_away k χ -> moddef_wk D χ = D) /\
  (forall Φ k χ, gmod_fresh k Φ -> wk_id_away k χ -> gmod_wk Φ χ = Φ) /\
  (forall E k χ, gentry_fresh k E -> wk_id_away k χ -> gentry_wk E χ = E) /\
  (forall e k χ, centry_fresh k e -> wk_id_away k χ -> centry_wk e χ = e).
Proof.
  syn_mut_ind; fresh_case;
    try solve [ match goal with H : wk_id_away _ _ |- _ => apply H; assumption end
              | match goal with H : forall A, Some ?X = Some A -> _ |- _ => eapply (H X); eauto end ].
  (** The blocks of an eliminator, and the telescope of a unit: their own
      inductions, over the [Forall] the principle carries. *)
  all: try ups_eq_case ltac:(fun H => eapply H; eassumption).
  all: try fields_eq_case ltac:(fun H => eapply H; eassumption).
  1: blocks_eq_case ltac:(fun H => eapply H; [ eassumption | auto ]).
  match goal with
  | HF : List.Forall _ _ |- _ => clear - HF H1 H2; induction HF; cbn in *; destruct_conjs; f_equal; eauto
  end.
Qed.

Lemma syn_wk_fresh :
  (forall M k φ, wk_avoids k φ -> exp_fresh k M[φ]ʷ) /\
  (forall H k φ, wk_avoids k φ -> modexp_fresh k (modexp_wk H φ)) /\
  (forall b k φ, wk_avoids k φ -> binding_fresh k (binding_wk b φ)) /\
  (forall U k φ, wk_avoids k φ -> gunit_fresh k (gunit_wk U φ)) /\
  (forall D k φ, wk_avoids k φ -> moddef_fresh k (moddef_wk D φ)) /\
  (forall Φ k φ, wk_avoids k φ -> gmod_fresh k (gmod_wk Φ φ)) /\
  (forall E k φ, wk_avoids k φ -> gentry_fresh k (gentry_wk E φ)) /\
  (forall e k φ, wk_avoids k φ -> centry_fresh k (centry_wk e φ)).
Proof.
  syn_mut_ind; fresh_case; rewrite ?gm_binders_wk, ?length_tele_wk; eauto;
    try solve [ match goal with H : forall A, Some ?X = Some A -> _ |- _ => eapply (H X); eauto end ].
  all: try ups_case ltac:(fun H => eapply H; eassumption).
  all: try fields_case ltac:(fun H => eapply H; eassumption).
  1: blocks_case ltac:(fun H => eapply H; auto).
  match goal with
  | HF : List.Forall _ _ |- _ =>
      clear - HF H1; induction HF; cbn in *; [ exact I | rewrite length_tele_wk; split; eauto ]
  end.
Qed.

(** A renaming that sends only [k] to [k'] keeps [#k'] out of what kept
    [#k] out. *)
Definition wk_reflects (k k' : nat) (φ : wk) : Prop := forall x, φ x = k' -> x = k.

Lemma wk_reflects_q : forall k k' φ, wk_reflects k k' φ -> wk_reflects (S k) (S k') (wk_q φ).
Proof. intros k k' φ H [|x] Hx; cbn in Hx; [ discriminate | injection Hx as Hx; rewrite (H _ Hx); reflexivity ]. Qed.

Lemma wk_reflects_qn : forall n k k' φ, wk_reflects k k' φ -> wk_reflects (n + k) (n + k') (wk_qn n φ).
Proof. induction n; intros; cbn; [ assumption | apply wk_reflects_q; auto ]. Qed.

#[local]
Hint Resolve wk_reflects_q wk_reflects_qn : core.

Lemma syn_fresh_wk :
  (forall M k k' φ, exp_fresh k M -> wk_reflects k k' φ -> exp_fresh k' M[φ]ʷ) /\
  (forall H k k' φ, modexp_fresh k H -> wk_reflects k k' φ -> modexp_fresh k' (modexp_wk H φ)) /\
  (forall b k k' φ, binding_fresh k b -> wk_reflects k k' φ -> binding_fresh k' (binding_wk b φ)) /\
  (forall U k k' φ, gunit_fresh k U -> wk_reflects k k' φ -> gunit_fresh k' (gunit_wk U φ)) /\
  (forall D k k' φ, moddef_fresh k D -> wk_reflects k k' φ -> moddef_fresh k' (moddef_wk D φ)) /\
  (forall Φ k k' φ, gmod_fresh k Φ -> wk_reflects k k' φ -> gmod_fresh k' (gmod_wk Φ φ)) /\
  (forall E k k' φ, gentry_fresh k E -> wk_reflects k k' φ -> gentry_fresh k' (gentry_wk E φ)) /\
  (forall e k k' φ, centry_fresh k e -> wk_reflects k k' φ -> centry_fresh k' (centry_wk e φ)).
Proof.
  syn_mut_ind; fresh_case; rewrite ?gm_binders_wk, ?length_tele_wk; eauto;
    try solve [ match goal with H : wk_reflects _ _ _ |- _ => intros Heq; apply H in Heq; contradiction end
              | match goal with H : forall A, Some ?X = Some A -> _ |- _ => eapply (H X); eauto end ].
  all: try ups_case ltac:(fun H => eapply H; eassumption).
  all: try fields_case ltac:(fun H => eapply H; eassumption).
  - blocks_case ltac:(fun H => eapply H; [ eassumption | apply wk_reflects_qn; assumption ]).
  - match goal with
    | HF : List.Forall _ ?Δ, Hf : _ ?Δ, Hw : wk_reflects _ _ _ |- _ =>
        clear - HF Hf Hw; induction HF as [| ? ? HB ? IH]; cbn in *; destruct_conjs; [ exact I | rewrite length_tele_wk; split ];
        [ eapply HB; [ eassumption | apply wk_reflects_qn; assumption ] | apply IH; assumption ]
    end.
Qed.

Corollary modexp_fresh_shiftn : forall H k n, modexp_fresh k H -> modexp_fresh (n + k) (modexp_wk H (wk_shiftn n)).
Proof.
  intros * Hf; eapply (proj1 (proj2 syn_fresh_wk)); [ exact Hf |].
  intros x Hx; cbn in Hx; lia.
Qed.

Corollary gentry_fresh_shiftn : forall E k n, gentry_fresh k E -> gentry_fresh (n + k) (gentry_wk E (wk_shiftn n)).
Proof.
  intros * Hf; eapply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 syn_fresh_wk))))))); [ exact Hf |].
  intros x Hx; cbn in Hx; lia.
Qed.

(** The term part of an entry avoids what the entry avoids. *)
Lemma entry_tm_fresh : forall E A M k, entry_tm E = Some (A, M) -> gentry_fresh k E -> exp_fresh k M.
Proof.
  intros [? ? ? ? [] | | | |] * He Hf; cbn in *; try discriminate;
    injection He as <- <-; tauto.
Qed.

(** The module part of an entry avoids what the entry avoids. *)
Lemma entry_unit_fresh : forall E U k, entry_unit E = Some U -> gentry_fresh k E -> gunit_fresh k U.
Proof.
  intros [| | | |] * He Hf; cbn in *; try discriminate;
    injection He as <-; tauto.
Qed.

(** ** [unwk k] Inverts [q^k ↑]

    One way round the composite is the identity away from [k], the other is
    the identity outright. *)
Lemma unwk_after_wk : forall k, wk_id_away k (unwk k ⊙ wk_qn k ↑).
Proof.
  intros k x Hx; unfold unwk; cbn.
  destruct (Compare_dec.lt_dec x k).
  - rewrite (wk_qn_lt _ _ x) by lia; rewrite wk_qn_lt by lia; reflexivity.
  - rewrite (wk_qn_ge k pred x) by lia; cbn; rewrite wk_qn_ge by lia; cbn; lia.
Qed.

Lemma wk_after_unwk : forall k, wk_eq (wk_qn k ↑ ⊙ unwk k) wk_id.
Proof.
  intros k x; unfold unwk; cbn.
  destruct (Compare_dec.lt_dec x k).
  - rewrite (wk_qn_lt _ _ x) by lia; rewrite wk_qn_lt by lia; reflexivity.
  - rewrite (wk_qn_ge k ↑ x) by lia; cbv [wk_shift]; rewrite wk_qn_ge by lia;
      rewrite Nat.add_sub; cbn [pred]; lia.
Qed.

Lemma wk_qn_shift_avoids : forall k, wk_avoids k (wk_qn k ↑).
Proof. intros k; rewrite <- (Nat.add_0_r k) at 1; apply wk_avoids_qn; intros x; cbn; lia. Qed.

Theorem exp_unwk_spec : forall k M, exp_fresh k M -> M = M[unwk k]ʷ[wk_qn k ↑]ʷ.
Proof.
  intros; rewrite (exp_wk_wk_ext _ _ _ (unwk k ⊙ wk_qn k ↑)) by reflexivity.
  symmetry; eapply (proj1 syn_fresh_id); eauto using unwk_after_wk.
Qed.

Theorem exp_unwk_wk : forall k M, M[wk_qn k ↑]ʷ[unwk k]ʷ = M.
Proof. intros; rewrite (exp_wk_wk_ext _ _ _ wk_id) by apply wk_after_unwk; apply exp_wk_id. Qed.

Theorem exp_wk_fresh : forall k M, exp_fresh k M[wk_qn k ↑]ʷ.
Proof. intros; apply (proj1 syn_wk_fresh), wk_qn_shift_avoids. Qed.

Corollary exp_shift_fresh : forall M, exp_fresh 0 M[↑]ʷ.
Proof. intros; exact (exp_wk_fresh 0 M). Qed.

(** ** Normal and Neutral Forms

    The checker drops a variable from a *normal form* and must get a normal
    form back, so freshness and un-weakening are defined again on [nf], [ne]
    and the atoms of a canonical level, and related to the versions on terms
    through [nf_to_exp].

    [nf_unwk] is a renaming of neutrals, so it preserves the shape of a
    normal form; it does **not** preserve canonicity of a level, since
    dropping a variable changes the order of the atoms.  The checker therefore
    re-canonicalises ([lvl_canon]) after un-weakening a level. *)
(** Freshness of an eliminator: of its uniform parameters, its blocks and
    its scrutinee. *)
Lemma exp_fresh_elim : forall k r oq Us m Bks M,
    exp_fresh k (a_elim r oq Us m Bks M) <->
      all_list (exp_fresh k) Us /\ blocks_fresh k Bks /\ exp_fresh k M.
Proof. reflexivity. Qed.

Lemma apps_exp_fresh : forall Ms M k,
    exp_fresh k M -> List.Forall (exp_fresh k) Ms -> exp_fresh k (apps_exp M Ms).
Proof. induction Ms; intros * HM HF; inversion HF; subst; cbn; [ assumption | apply IHMs; [ split |]; assumption ]. Qed.

(** ** Deciding Freshness *)

(** The boolean counterparts of [all_list], [opt_all], [all_brs] and
    [all_blocks]: structural recursions on the lists, so that a recursive
    function on terms may use them on an eliminator's parts. *)
Fixpoint all_listb {A : Set} (f : A -> bool) (l : list A) : bool :=
  match l with
  | nil => true
  | x :: l' => (f x && all_listb f l')%bool
  end.

(** An annotation, when there is one. *)
Definition opt_allb {A : Set} (f : A -> bool) (o : option A) : bool :=
  match o with Some a => f a | None => true end.

(** Every branch, under its binders. *)
Fixpoint all_brsb {A : Type} (f : nat -> A -> bool) (Bs : list (String.string * nat * A)) : bool :=
  match Bs with
  | nil => true
  | b :: Bs' => (f (snd (fst b)) (snd b) && all_brsb f Bs')%bool
  end.

(** Every block: its binder count, annotation, motive and branches. *)
Fixpoint all_blocksb {A : Set} (f : nat -> option A -> A -> list (String.string * nat * A) -> bool)
    (Bks : list (eblock_g A)) : bool :=
  match Bks with
  | nil => true
  | eb_mk nm oZ M Bs :: Bks' => (f nm oZ M Bs && all_blocksb f Bks')%bool
  end.

#[local] Open Scope bool_scope.

(** Freshness of a term is decided by a boolean function with the same
    clauses as [exp_fresh]: the extracted evaluation consults it, to skip a
    value that the term it evaluates next never reads, and the freshness of
    a kept proof in a normal form is decided by it ([nf_freshb]). *)
Fixpoint exp_freshb (k : nat) (M : exp) {struct M} : bool :=
  match M with
  | a_typ _ | a_level _ | a_level_sort | a_llit _
  | a_prop | a_True | a_tt | a_False => true
  | a_univ M | a_succl M | a_left M | a_right M => exp_freshb k M
  | a_maxl M N | a_app M N | a_absurd M N => exp_freshb k M && exp_freshb k N
  | a_conj T M N => exp_freshb k T && exp_freshb k M && exp_freshb k N
  | a_ind _ _ | a_con _ _ _ | a_nlit _ | a_ntok => true
  | a_elim _ _ Us _ Bks M =>
      all_listb (exp_freshb k) Us &&
      all_blocksb (fun nm oZ A Bs => opt_allb (exp_freshb (nm - 1 + k)) oZ && exp_freshb (nm + k) A &&
                                     all_brsb (fun n B => exp_freshb (n + k) B) Bs) Bks &&
      exp_freshb k M
  | a_pi _ A B | a_fn A B | a_and A B => exp_freshb k A && exp_freshb (S k) B
  | a_var x => negb (Nat.eqb x k)
  | a_let b B => binding_freshb k b && exp_freshb (S k) B
  | a_mem H _ => modexp_freshb k H
  | a_record _ => true
  | a_tuple T fs => exp_freshb k T && all_listb (fun f => exp_freshb k (snd f)) fs
  | a_proj _ M => exp_freshb k M
  end
with modexp_freshb (k : nat) (H : modexp) {struct H} : bool :=
  match H with
  | me_unit _ => true
  | me_var x => negb (Nat.eqb x k)
  | me_mem H _ => modexp_freshb k H
  | me_app H N => modexp_freshb k H && exp_freshb k N
  | me_lit U => gunit_freshb k U
  end
with binding_freshb (k : nat) (b : binding) {struct b} : bool :=
  match b with
  | b_def A M => exp_freshb k A && exp_freshb k M
  | b_mod U => gunit_freshb k U
  end
with gunit_freshb (k : nat) (U : gunit) {struct U} : bool :=
  match U with
  | gu_mk Δ D =>
      (fix tele_freshb (Δ : list centry) : bool :=
         match Δ with
         | nil => true
         | cons e Δ' => centry_freshb (List.length Δ' + k) e && tele_freshb Δ'
         end) Δ
      && moddef_freshb (List.length Δ + k) D
  end
with moddef_freshb (k : nat) (D : moddef) {struct D} : bool :=
  match D with
  | md_body sm Φ => gmod_freshb k Φ
  | md_alias E => modexp_freshb k E
  end
with gmod_freshb (k : nat) (Φ : gmod) {struct Φ} : bool :=
  match Φ with
  | gm_nil => true
  | gm_ext Φ _ E => gmod_freshb k Φ && gentry_freshb (gm_binders Φ + k) E
  | gm_open Φ H _ => gmod_freshb k Φ && modexp_freshb (gm_binders Φ + k) H
  end
with gentry_freshb (k : nat) (E : gentry) {struct E} : bool :=
  match E with
  | ge_def _ _ _ A B => exp_freshb k A && match B with Some M => exp_freshb k M | None => true end
  | ge_mod _ U => gunit_freshb k U
  | ge_ind _ _ _ D Φ => gmod_freshb (ind_nu D + k) Φ
  | ge_def_mod _ A M U => exp_freshb k A && exp_freshb k M && gunit_freshb k U
  | ge_record _ _ R Φ => gmod_freshb (S (List.length (record_params R)) + k) Φ
  end
with centry_freshb (k : nat) (e : centry) {struct e} : bool :=
  match e with
  | ce_ass A => exp_freshb k A
  | ce_def A M => exp_freshb k A && exp_freshb k M
  | ce_mod U => gunit_freshb k U
  | ce_dm A M U => exp_freshb k A && exp_freshb k M && gunit_freshb k U
  end.

(** The boolean list functions decide their counterparts, element by
    element. *)
Lemma all_listb_sound : forall {A : Set} (f : A -> bool) (P : A -> Prop) l,
    List.Forall (fun x => f x = true -> P x) l -> all_listb f l = true -> all_list P l.
Proof.
  induction 1 as [| x l Hx Hl IH]; cbn; [ trivial |].
  intros Hb; apply Bool.andb_true_iff in Hb as [H1 H2]; split; auto.
Qed.

Lemma all_brsb_sound : forall {A : Type} (f : nat -> A -> bool) (P : nat -> A -> Prop) Bs,
    List.Forall (fun b => f (snd (fst b)) (snd b) = true -> P (snd (fst b)) (snd b)) Bs ->
    all_brsb f Bs = true -> all_brs P Bs.
Proof.
  induction 1 as [| b Bs Hb HBs IH]; cbn; [ trivial |].
  intros H; apply Bool.andb_true_iff in H as [H1 H2]; split; auto.
Qed.

Lemma all_blocksb_sound : forall {A : Set} (f : nat -> option A -> A -> list (String.string * nat * A) -> bool)
    (P : nat -> option A -> A -> list (String.string * nat * A) -> Prop) Bks,
    List.Forall (fun b => f (eb_binder_count b) (eb_ann b) (eb_motive b) (eb_brs b) = true ->
                          P (eb_binder_count b) (eb_ann b) (eb_motive b) (eb_brs b)) Bks ->
    all_blocksb f Bks = true -> all_blocks P Bks.
Proof.
  induction 1 as [| [nm oZ M Bs] Bks Hb HBks IH]; cbn; [ trivial |].
  intros H; apply Bool.andb_true_iff in H as [H1 H2]; split; auto.
Qed.

(** And conversely. *)
Lemma all_listb_complete : forall {A : Set} (f : A -> bool) (P : A -> Prop) l,
    List.Forall (fun x => P x -> f x = true) l -> all_list P l -> all_listb f l = true.
Proof.
  induction 1 as [| x l Hx Hl IH]; cbn; [ trivial |].
  intros [H1 H2]; apply Bool.andb_true_iff; split; auto.
Qed.

Lemma all_brsb_complete : forall {A : Type} (f : nat -> A -> bool) (P : nat -> A -> Prop) Bs,
    List.Forall (fun b => P (snd (fst b)) (snd b) -> f (snd (fst b)) (snd b) = true) Bs ->
    all_brs P Bs -> all_brsb f Bs = true.
Proof.
  induction 1 as [| b Bs Hb HBs IH]; cbn; [ trivial |].
  intros [H1 H2]; apply Bool.andb_true_iff; split; auto.
Qed.

Lemma all_blocksb_complete : forall {A : Set} (f : nat -> option A -> A -> list (String.string * nat * A) -> bool)
    (P : nat -> option A -> A -> list (String.string * nat * A) -> Prop) Bks,
    List.Forall (fun b => P (eb_binder_count b) (eb_ann b) (eb_motive b) (eb_brs b) ->
                          f (eb_binder_count b) (eb_ann b) (eb_motive b) (eb_brs b) = true) Bks ->
    all_blocks P Bks -> all_blocksb f Bks = true.
Proof.
  induction 1 as [| [nm oZ M Bs] Bks Hb HBks IH]; cbn; [ trivial |].
  intros [H1 H2]; apply Bool.andb_true_iff; split; auto.
Qed.

Lemma freshb_sound :
  (forall M k, exp_freshb k M = true -> exp_fresh k M) /\
  (forall H k, modexp_freshb k H = true -> modexp_fresh k H) /\
  (forall b k, binding_freshb k b = true -> binding_fresh k b) /\
  (forall U k, gunit_freshb k U = true -> gunit_fresh k U) /\
  (forall D k, moddef_freshb k D = true -> moddef_fresh k D) /\
  (forall Φ k, gmod_freshb k Φ = true -> gmod_fresh k Φ) /\
  (forall E k, gentry_freshb k E = true -> gentry_fresh k E) /\
  (forall e k, centry_freshb k e = true -> centry_fresh k e).
Proof.
  apply (syn_mut_ind
           (fun M => forall k, exp_freshb k M = true -> exp_fresh k M)
           (fun H => forall k, modexp_freshb k H = true -> modexp_fresh k H)
           (fun b => forall k, binding_freshb k b = true -> binding_fresh k b)
           (fun U => forall k, gunit_freshb k U = true -> gunit_fresh k U)
           (fun D => forall k, moddef_freshb k D = true -> moddef_fresh k D)
           (fun Φ => forall k, gmod_freshb k Φ = true -> gmod_fresh k Φ)
           (fun E => forall k, gentry_freshb k E = true -> gentry_fresh k E)
           (fun e => forall k, centry_freshb k e = true -> centry_fresh k e)).
  (** An eliminator: its uniform parameters, then its blocks, part by
      part, then its scrutinee. *)
  all: try match goal with |- forall r oq Us m Bks M, _ -> _ -> _ -> forall k, exp_freshb k (a_elim r oq Us m Bks M) = true -> _ =>
        intros r oq Us m Bks M HUs HBks HM k Hb; cbn [exp_freshb] in Hb;
        apply Bool.andb_true_iff in Hb as [Hb HbM]; apply Bool.andb_true_iff in Hb as [HbU HbB];
        apply (proj2 (exp_fresh_elim k r oq Us m Bks M)); split; [| split; [| auto ] ];
        [ eapply all_listb_sound; [| exact HbU ];
          eapply List.Forall_impl; [| exact HUs ]; cbv beta; intros U HU; apply HU
        | eapply all_blocksb_sound; [| exact HbB ];
          eapply List.Forall_impl; [| exact HBks ]; cbv beta;
          intros [nm oZ A Bs] (HZ & HA & HBs) Hbk; cbn [eb_binder_count eb_ann eb_motive eb_brs] in *;
          apply Bool.andb_true_iff in Hbk as [Hbk Hbr]; apply Bool.andb_true_iff in Hbk as [HbZ HbA];
          split; [| split ];
          [ destruct oZ as [Z |]; cbn in *; [ apply (HZ Z eq_refl); exact HbZ | exact I ]
          | apply HA; exact HbA
          | eapply all_brsb_sound; [| exact Hbr ];
            eapply List.Forall_impl; [| exact HBs ]; cbv beta; intros br Hbr' Hbt; apply Hbr'; exact Hbt ] ] end.
  (** A record element: its type, then its fields. *)
  all: try match goal with |- forall T fs, _ -> _ -> forall k, exp_freshb k (a_tuple T fs) = true -> _ =>
         intros T fs HT Hfs k Hb; cbn [exp_freshb exp_fresh] in *; apply Bool.andb_true_iff in Hb as [HbT Hbf];
         split; [ auto
                | eapply all_listb_sound; [| exact Hbf ];
                  eapply List.Forall_impl; [| exact Hfs ]; cbv beta; intros f Hf; apply Hf ] end.
  all: intros; cbn in *; repeat rewrite Bool.andb_true_iff in *; destruct_conjs;
    try solve [ auto | split; auto | repeat split; auto
              | apply Bool.negb_true_iff, Nat.eqb_neq in H; assumption
              | apply Bool.negb_true_iff, Nat.eqb_neq in H0; assumption ].
  - (* a unit: its telescope, entry by entry *)
    split; [| auto ].
    clear H2 H0; induction H as [| e Δ' He HΔ' IHΔ]; cbn in *; [ exact I |].
    apply Bool.andb_true_iff in H1 as [H1 H1']; split; [ apply He; exact H1 | apply IHΔ; exact H1' ].
  - (* a global entry *) destruct B; split; eauto.
Qed.

Lemma freshb_complete :
  (forall M k, exp_fresh k M -> exp_freshb k M = true) /\
  (forall H k, modexp_fresh k H -> modexp_freshb k H = true) /\
  (forall b k, binding_fresh k b -> binding_freshb k b = true) /\
  (forall U k, gunit_fresh k U -> gunit_freshb k U = true) /\
  (forall D k, moddef_fresh k D -> moddef_freshb k D = true) /\
  (forall Φ k, gmod_fresh k Φ -> gmod_freshb k Φ = true) /\
  (forall E k, gentry_fresh k E -> gentry_freshb k E = true) /\
  (forall e k, centry_fresh k e -> centry_freshb k e = true).
Proof.
  apply (syn_mut_ind
           (fun M => forall k, exp_fresh k M -> exp_freshb k M = true)
           (fun H => forall k, modexp_fresh k H -> modexp_freshb k H = true)
           (fun b => forall k, binding_fresh k b -> binding_freshb k b = true)
           (fun U => forall k, gunit_fresh k U -> gunit_freshb k U = true)
           (fun D => forall k, moddef_fresh k D -> moddef_freshb k D = true)
           (fun Φ => forall k, gmod_fresh k Φ -> gmod_freshb k Φ = true)
           (fun E => forall k, gentry_fresh k E -> gentry_freshb k E = true)
           (fun e => forall k, centry_fresh k e -> centry_freshb k e = true)).
  (** An eliminator: its uniform parameters, then its blocks, part by
      part, then its scrutinee. *)
  all: try match goal with |- forall r oq Us m Bks M, _ -> _ -> _ -> forall k, exp_fresh k (a_elim r oq Us m Bks M) -> _ =>
        intros r oq Us m Bks M HUs HBks HM k Hf;
        apply (proj1 (exp_fresh_elim k r oq Us m Bks M)) in Hf as (HfU & HfB & HfM); cbn [exp_freshb];
        rewrite !Bool.andb_true_iff; split; [ split |];
        [ eapply all_listb_complete; [| exact HfU ];
          eapply List.Forall_impl; [| exact HUs ]; cbv beta; intros U HU; apply HU
        | eapply all_blocksb_complete; [| exact HfB ];
          eapply List.Forall_impl; [| exact HBks ]; cbv beta;
          intros [nm oZ A Bs] (HZ & HA & HBs) (HfZ & HfA & HfBs); cbn [eb_binder_count eb_ann eb_motive eb_brs] in *;
          rewrite !Bool.andb_true_iff; split; [ split |];
          [ destruct oZ as [Z |]; cbn in *; [ apply (HZ Z eq_refl); exact HfZ | reflexivity ]
          | apply HA; exact HfA
          | eapply all_brsb_complete; [| exact HfBs ];
            eapply List.Forall_impl; [| exact HBs ]; cbv beta; intros br Hbr' Hbt; apply Hbr'; exact Hbt ]
        | auto ] end.
  (** A record element: its type, then its fields. *)
  all: try match goal with |- forall T fs, _ -> _ -> forall k, exp_fresh k (a_tuple T fs) -> _ =>
         intros T fs HT Hfs k [HfT Hff]; cbn [exp_freshb]; apply Bool.andb_true_iff;
         split; [ auto
                | eapply all_listb_complete; [| exact Hff ];
                  eapply List.Forall_impl; [| exact Hfs ]; cbv beta; intros f Hf; apply Hf ] end.
  all: intros; cbn in *; rewrite ?Bool.andb_true_iff; destruct_conjs;
    try solve [ reflexivity | auto | split; auto | repeat split; auto
              | apply Bool.negb_true_iff, Nat.eqb_neq; assumption ].
  - (* a unit: its telescope, entry by entry *)
    split; [| auto ].
    clear H2 H0; induction H as [| e Δ' He HΔ' IHΔ]; cbn in *; [ reflexivity |].
    destruct H1 as [H1 H1']; apply Bool.andb_true_iff; split; [ apply He; exact H1 | apply IHΔ; exact H1' ].
  - (* a global entry *) destruct B; split; eauto.
Qed.

Lemma exp_freshb_sound : forall M k, exp_freshb k M = true -> exp_fresh k M.
Proof. exact (proj1 freshb_sound). Qed.

(** The boolean function decides freshness. *)
Lemma exp_freshb_iff : forall M k, exp_freshb k M = true <-> exp_fresh k M.
Proof. intros; split; [ apply exp_freshb_sound | apply (proj1 freshb_complete) ]. Qed.

#[local] Close Scope bool_scope.

(** [nf_fresh k W]: the variable [k] does not occur in the normal form
    [W]; mutually, in the neutral [u]. *)
Fixpoint nf_fresh (k : nat) (W : nf) {struct W} : Prop :=
  match W with
  | nf_typ _ | nf_level _ | nf_level_sort | nf_prop | nf_True | nf_False
  | nf_proof_erased => True
  | nf_proof M => exp_fresh k M
  | nf_univ _ xs | nf_lvl _ xs => all_list (fun a => ne_fresh k (atom_level a)) xs
  | nf_pi _ A B | nf_fn A B | nf_and A B => nf_fresh k A /\ nf_fresh (S k) B
  | nf_indty _ _ Ms | nf_con _ _ _ Ms => all_list (nf_fresh k) Ms
  | nf_neut u => ne_fresh k u
  | nf_record _ Ms => all_list (nf_fresh k) Ms
  | nf_tuple _ Ms _ Ns => all_list (nf_fresh k) Ms /\ all_list (nf_fresh k) Ns
  end
with ne_fresh (k : nat) (u : ne) {struct u} : Prop :=
  match u with
  | ne_absurd A M => nf_fresh k A /\ exp_fresh k M
  | ne_absurd_erased A => nf_fresh k A
  | ne_elim _ Us _ Bks u =>
      all_list (nf_fresh k) Us /\ all_list (normal_block_forall (fun n => nf_fresh (n + k))) Bks /\ ne_fresh k u
  | ne_app u W => ne_fresh k u /\ nf_fresh k W
  | ne_var x => x <> k
  | ne_glob _ => True
  | ne_proj _ u => ne_fresh k u
  end.

(** The normal form [W] with the variable [k] removed: the variables above
    it moved down by one; the inverse of the weakening at [k] when [k] is
    fresh in [W]. *)
Fixpoint nf_unwk (k : nat) (W : nf) {struct W} : nf :=
  match W with
  | nf_typ i => nf_typ i
  | nf_univ c xs => nf_univ c (List.map (map_level_atom (ne_unwk k)) xs)
  | nf_level n => nf_level n
  | nf_level_sort => nf_level_sort
  | nf_lvl c xs => nf_lvl c (List.map (map_level_atom (ne_unwk k)) xs)
  | nf_prop => nf_prop
  | nf_True => nf_True
  | nf_proof M => nf_proof M[unwk k]ʷ
  | nf_False => nf_False
  | nf_and P Q => nf_and (nf_unwk k P) (nf_unwk (S k) Q)
  | nf_proof_erased => nf_proof_erased
  | nf_pi r A B => nf_pi r (nf_unwk k A) (nf_unwk (S k) B)
  | nf_fn A M => nf_fn (nf_unwk k A) (nf_unwk (S k) M)
  | nf_indty p j Ms => nf_indty p j (List.map (nf_unwk k) Ms)
  | nf_con p j c Ms => nf_con p j c (List.map (nf_unwk k) Ms)
  | nf_neut u => nf_neut (ne_unwk k u)
  | nf_record p Ms => nf_record p (List.map (nf_unwk k) Ms)
  | nf_tuple p Ms fs Ns => nf_tuple p (List.map (nf_unwk k) Ms) fs (List.map (nf_unwk k) Ns)
  end
with ne_unwk (k : nat) (u : ne) {struct u} : ne :=
  match u with
  | ne_absurd A M => ne_absurd (nf_unwk k A) M[unwk k]ʷ
  | ne_absurd_erased A => ne_absurd_erased (nf_unwk k A)
  | ne_elim p Us m Bks u =>
      ne_elim p (List.map (nf_unwk k) Us) m (List.map (map_normal_block (fun n => nf_unwk (n + k))) Bks) (ne_unwk k u)
  | ne_app u W => ne_app (ne_unwk k u) (nf_unwk k W)
  | ne_var x => ne_var (unwk k x)
  | ne_glob p => ne_glob p
  | ne_proj f u => ne_proj f (ne_unwk k u)
  end.

(** Weakening of a level expression: [lvl_exp_of] builds a term out of a
    constant and a list of atoms, so a renaming goes through it, atom by
    atom. *)
Lemma succl_n_wk : forall j M φ, (succl_n j M)[φ]ʷ = succl_n j M[φ]ʷ.
Proof. induction j; intros; cbn; congruence. Qed.

Lemma lvl_fold_wk : forall xs hd φ,
    (lvl_fold hd xs)[φ]ʷ = lvl_fold hd[φ]ʷ (List.map (fun p => (fst p, (snd p)[φ]ʷ)) xs).
Proof.
  induction xs as [| [j a] r IH]; intros; cbn; [ reflexivity |].
  rewrite IH; cbn; rewrite succl_n_wk; reflexivity.
Qed.

Lemma lvl_exp_of_wk : forall c xs φ,
    (lvl_exp_of c xs)[φ]ʷ = lvl_exp_of c (List.map (fun p => (fst p, (snd p)[φ]ʷ)) xs).
Proof.
  intros c [| [j a] r] φ; destruct c as [[|] [|]]; cbn; try reflexivity;
    rewrite lvl_fold_wk; cbn; rewrite succl_n_wk; reflexivity.
Qed.

(** The same for freshness: a level expression is fresh exactly when each of
    its atoms is. *)
Lemma succl_n_fresh : forall j k M, exp_fresh k M -> exp_fresh k (succl_n j M).
Proof. induction j; intros; cbn; auto. Qed.

Lemma lvl_fold_fresh : forall xs k hd,
    exp_fresh k hd ->
    List.Forall (fun p => exp_fresh k (snd p)) xs ->
    exp_fresh k (lvl_fold hd xs).
Proof.
  induction xs as [| [j a] r IH]; intros * Hhd HF; cbn; [ assumption |].
  inversion HF as [| ? ? Ha HF']; subst; apply IH; [| assumption ].
  split; [ assumption | apply succl_n_fresh; exact Ha ].
Qed.

Lemma lvl_exp_of_fresh : forall c xs k,
    List.Forall (fun p => exp_fresh k (snd p)) xs ->
    exp_fresh k (lvl_exp_of c xs).
Proof.
  intros c [| [j a] r] k HF; destruct c as [[|] [|]]; cbn; try exact I;
    inversion HF as [| ? ? Ha HF']; subst;
    apply lvl_fold_fresh; first [ exact HF' | apply succl_n_fresh; exact Ha
                                | split; [ exact I | apply succl_n_fresh; exact Ha ] ].
Qed.

(** A global is closed: the term of a qualified name is a chain of selections
    from a unit, and a unit holds no local index.  So it is fresh at every
    index, and no renaming touches it. *)
Lemma me_mems_fresh : forall pre H k, modexp_fresh k H -> modexp_fresh k (me_mems H pre).
Proof. induction pre; intros; cbn; auto. Qed.

Lemma member_ref_fresh : forall ch H k, modexp_fresh k H -> exp_fresh k (member_ref H ch).
Proof.
  induction ch as [| x ch IH]; intros * HH; cbn; [ exact I |].
  destruct ch as [| y ch]; [ exact HH | apply IH; cbn; exact HH ].
Qed.

Lemma qname_term_fresh : forall p k, exp_fresh k (qname_term p).
Proof. intros [fp ch] k; apply member_ref_fresh; exact I. Qed.

Lemma me_mems_wk : forall pre H φ,
    modexp_wk H φ = H -> modexp_wk (me_mems H pre) φ = me_mems H pre.
Proof.
  induction pre as [| y pre IH]; intros * HH; cbn; [ exact HH |].
  apply IH; cbn; rewrite HH; reflexivity.
Qed.

Lemma member_ref_wk : forall ch H φ,
    modexp_wk H φ = H -> (member_ref H ch)[φ]ʷ = member_ref H ch.
Proof.
  induction ch as [| x ch IH]; intros * HH; cbn; [ reflexivity |].
  destruct ch as [| y ch]; [ cbn; rewrite HH; reflexivity |].
  apply IH; cbn; rewrite HH; reflexivity.
Qed.

Lemma qname_term_wk : forall p φ, (qname_term p)[φ]ʷ = qname_term p.
Proof. intros [fp ch] φ; apply member_ref_wk; reflexivity. Qed.

Lemma qname_mod_wk : forall p φ, modexp_wk (qname_mod p) φ = qname_mod p.
Proof. intros [fp ch] φ; apply me_mems_wk; reflexivity. Qed.

Lemma qname_mod_fresh : forall p k, modexp_fresh k (qname_mod p).
Proof. intros [fp ch] k; apply me_mems_fresh; exact I. Qed.

(** The fields of a tuple read back from its names and values: each as
    its value. *)
Lemma all_list_combine : forall (P : exp -> Prop) (fs : list String.string) Ms,
    List.Forall P Ms -> all_list (fun f => P (snd f)) (List.combine fs Ms).
Proof.
  intros P; induction fs as [| f fs IH]; intros [| M Ms] HF; cbn; try exact I.
  inversion HF; subst; split; [ assumption | apply IH; assumption ].
Qed.

(** Mapping the values of [combine] is mapping the second components. *)
Lemma combine_map_r : forall {A B C : Type} (g : B -> C) (xs : list A) (ys : list B),
    List.combine xs (List.map g ys) = List.map (fun p => (fst p, g (snd p))) (List.combine xs ys).
Proof. induction xs as [| x xs IH]; intros [| y ys]; cbn; f_equal; auto. Qed.

(** Freshness of a normal form is freshness of the term it denotes, and
    un-weakening agrees with the renaming on terms. *)
Lemma nf_fresh_to_exp :
  (forall W k, nf_fresh k W -> exp_fresh k (nf_to_exp W)) /\
  (forall u k, ne_fresh k u -> exp_fresh k (ne_to_exp u)).
Proof.
  apply nf_ne_ind; intros; cbn [nf_to_exp ne_to_exp nf_fresh ne_fresh exp_fresh] in *; destruct_conjs;
    (** The lists of terms a normal form spells, as [all_list]s over the
        lists it holds. *)
    rewrite ?exp_fresh_elim; unfold blocks_fresh;
    rewrite <- ?all_list_Forall, ?all_blocks_all_list, ?all_list_map;
    repeat split;
    first [ exact I | solve [ eauto ] | apply lvl_exp_of_fresh | apply apps_exp_fresh; [ exact I |] | apply all_list_combine
          | apply qname_term_fresh | idtac ];
    rewrite <- ?all_list_Forall, ?all_list_map; nested_elements; cbn in *; destruct_conjs;
    repeat split; eauto.
  (** A block: its motive, and its branches. *)
  all: unfold normal_block_forall in *; cbn in *; destruct_conjs; eauto.
  rewrite all_brs_all_list, all_list_map; nested_elements; cbn in *; eauto.
Qed.

(** Un-weakening at [k], under [n] binders, is un-weakening at [n + k]. *)
Lemma unwk_plus : forall n k, wk_qn n (unwk k) = unwk (n + k).
Proof. intros; unfold unwk; rewrite wk_qn_plus; reflexivity. Qed.

Lemma nf_unwk_to_exp :
  (forall W k, nf_to_exp (nf_unwk k W) = (nf_to_exp W)[unwk k]ʷ) /\
  (forall u k, ne_to_exp (ne_unwk k u) = (ne_to_exp u)[unwk k]ʷ).
Proof.
  apply nf_ne_ind; intros; cbn [nf_unwk ne_unwk nf_to_exp ne_to_exp exp_wk]; rewrite ?apps_exp_wk, ?lvl_exp_of_wk;
    (** A global is closed, so the renaming does not touch it. *)
    try solve [ symmetry; apply qname_term_wk ];
    repeat (f_equal; try solve [ eauto ]).
  (** A tuple: its values through [combine]. *)
  all: try match goal with
           | |- combine ?fs _ = List.map (fun f => (fst f, (snd f)[?φ]ʷ)) _ =>
               rewrite <- (combine_map_r (fun N => N[φ]ʷ)); f_equal
           end.
  all: nested_elements; cbn; rewrite ?unwk_plus; repeat (f_equal; try solve [ eauto ]).
  (** A block's branches. *)
  all: nested_elements; cbn; rewrite ?unwk_plus; f_equal; eauto.
Qed.

(** The three facts of un-weakening, on normal forms. *)
Theorem nf_fresh_unwk : forall k W, nf_fresh k W -> nf_to_exp W = (nf_to_exp (nf_unwk k W))[wk_qn k ↑]ʷ.
Proof.
  intros * HW.
  rewrite (proj1 nf_unwk_to_exp).
  apply exp_unwk_spec, (proj1 nf_fresh_to_exp), HW.
Qed.

(** Freshness of a normal form is decidable: it is a conjunction of
    disequalities of indices and of freshness of the kept proofs, so it is
    decided by a boolean function and reflection. *)
Fixpoint nf_freshb (k : nat) (W : nf) {struct W} : bool :=
  match W with
  | nf_typ _ | nf_level _ | nf_level_sort | nf_prop | nf_True | nf_False
  | nf_proof_erased => true
  | nf_proof M => exp_freshb k M
  | nf_univ _ xs | nf_lvl _ xs => List.forallb (fun a => ne_freshb k (atom_level a)) xs
  | nf_pi _ A B | nf_fn A B | nf_and A B => nf_freshb k A && nf_freshb (S k) B
  | nf_indty _ _ Ms | nf_con _ _ _ Ms => List.forallb (nf_freshb k) Ms
  | nf_neut u => ne_freshb k u
  | nf_record _ Ms => List.forallb (nf_freshb k) Ms
  | nf_tuple _ Ms _ Ns => List.forallb (nf_freshb k) Ms && List.forallb (nf_freshb k) Ns
  end
with ne_freshb (k : nat) (u : ne) {struct u} : bool :=
  match u with
  | ne_absurd A M => nf_freshb k A && exp_freshb k M
  | ne_absurd_erased A => nf_freshb k A
  | ne_elim _ Us _ Bks u =>
      List.forallb (nf_freshb k) Us && (List.forallb (normal_block_forallb (fun n => nf_freshb (n + k))) Bks
                                         && ne_freshb k u)
  | ne_app u W => ne_freshb k u && nf_freshb k W
  | ne_var x => negb (Nat.eqb x k)
  | ne_glob _ => true
  | ne_proj _ u => ne_freshb k u
  end.

Lemma nf_freshb_iff :
  (forall W k, nf_freshb k W = true <-> nf_fresh k W) /\
  (forall u k, ne_freshb k u = true <-> ne_fresh k u).
Proof.
  assert (Hand : forall A B C D : Prop, (A <-> B) -> (C <-> D) -> (A /\ C <-> B /\ D)) by tauto.
  apply nf_ne_ind; intros; cbn; rewrite ?Bool.andb_true_iff;
    repeat apply Hand;
    try solve [ split; [ intros _; exact I | reflexivity ]
              | rewrite Bool.negb_true_iff, Nat.eqb_neq; reflexivity
              | apply exp_freshb_iff
              | eauto ].
  (** The lists, element by element. *)
  all: (eapply list_all_forallb; [ eassumption |]); intros x Hx; try destruct Hx; cbn; try solve [ eauto ].
  (** A block: its motive and its branches. *)
  all: unfold normal_block_forallb, normal_block_forall; cbn; rewrite Bool.andb_true_iff; apply Hand; [ eauto |].
  all: (eapply list_all_forallb; [ eassumption |]); intros y Hy; destruct Hy; cbn; eauto.
Qed.

(** Erasure keeps a normal form fresh: it replaces proofs by the marker,
    which mentions no variable. *)
Lemma nf_ne_fresh_erase :
  (forall W k, nf_fresh k W -> nf_fresh k (nf_erase W)) /\ (forall u k, ne_fresh k u -> ne_fresh k (ne_erase u)).
Proof.
  apply nf_ne_ind; intros; cbn [nf_erase ne_erase nf_fresh ne_fresh exp_fresh] in *; intuition auto;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    rewrite ?all_list_map; try split; auto;
    try (eapply list_all_all_list_impl; [ eassumption | eassumption |]; cbn; intros x Hx Hy;
         first [ solve [ match type of Hx with normal_block_g_all _ _ _ =>
                         destruct Hx as [n' A HA brs Hbrs]; unfold normal_block_forall in *; cbn in *;
                         destruct Hy as [HyA Hybrs]; split; auto;
                         rewrite all_list_map; eapply list_all_all_list_impl; [ exact Hbrs | exact Hybrs |];
                         intros br Hbr Hy'; destruct Hbr; cbn in *; auto end ]
               | solve [ destruct Hx; cbn in *; auto ]
               | auto ]).
Qed.

Lemma ne_fresh_erase : forall k u, ne_fresh k u -> ne_fresh k (ne_erase u).
Proof. intros; apply nf_ne_fresh_erase; assumption. Qed.

(** ** Normal Forms Free of Proofs

    [nf_proof_free W]: the normal form [W] holds no kept proof
    ([nf_proof]) and no ex falso; mutually, [ne_proof_free u] for the
    neutral [u].  Normal forms are compared up to their proofs
    ([nf_erase]), so up to erasure a normal form that holds a proof no
    longer says which variables the proof used, and it cannot be
    strengthened past a variable it does not mention: with
    [f : ⊥ → Type@0], the normal form [f M], for a proof [M] of [⊥], is a
    type in [f ▹ (x : ⊥)], where [x] proves [⊥], but not in [f] alone.  The normal forms that are
    strengthened ([Algorithmic.Strengthening.nf_strengthen]) and the
    classification of an argument by its normal form ([classify_in_nf])
    ask for proof-free ones. *)
Fixpoint nf_proof_free (W : nf) {struct W} : Prop :=
  match W with
  | nf_proof _ | nf_proof_erased => False
  | nf_typ _ | nf_level _ | nf_level_sort | nf_prop | nf_True | nf_False => True
  | nf_univ _ xs | nf_lvl _ xs => all_list (fun a => ne_proof_free (atom_level a)) xs
  | nf_pi _ A B | nf_fn A B | nf_and A B => nf_proof_free A /\ nf_proof_free B
  | nf_indty _ _ Ms | nf_con _ _ _ Ms => all_list nf_proof_free Ms
  | nf_neut u => ne_proof_free u
  | nf_record _ Ms => all_list nf_proof_free Ms
  | nf_tuple _ Ms _ Ns => all_list nf_proof_free Ms /\ all_list nf_proof_free Ns
  end
with ne_proof_free (u : ne) {struct u} : Prop :=
  match u with
  | ne_absurd _ _ | ne_absurd_erased _ => False
  | ne_elim _ Us _ Bks u =>
      all_list nf_proof_free Us /\ all_list (normal_block_forall (fun _ => nf_proof_free)) Bks /\ ne_proof_free u
  | ne_app u W => ne_proof_free u /\ nf_proof_free W
  | ne_var _ | ne_glob _ => True
  | ne_proj _ u => ne_proof_free u
  end.

(** Proof-freedom is decided by a boolean function with the same clauses. *)
Fixpoint nf_proof_freeb (W : nf) {struct W} : bool :=
  match W with
  | nf_proof _ | nf_proof_erased => false
  | nf_typ _ | nf_level _ | nf_level_sort | nf_prop | nf_True | nf_False => true
  | nf_univ _ xs | nf_lvl _ xs => List.forallb (fun a => ne_proof_freeb (atom_level a)) xs
  | nf_pi _ A B | nf_fn A B | nf_and A B => nf_proof_freeb A && nf_proof_freeb B
  | nf_indty _ _ Ms | nf_con _ _ _ Ms => List.forallb nf_proof_freeb Ms
  | nf_neut u => ne_proof_freeb u
  | nf_record _ Ms => List.forallb nf_proof_freeb Ms
  | nf_tuple _ Ms _ Ns => List.forallb nf_proof_freeb Ms && List.forallb nf_proof_freeb Ns
  end
with ne_proof_freeb (u : ne) {struct u} : bool :=
  match u with
  | ne_absurd _ _ | ne_absurd_erased _ => false
  | ne_elim _ Us _ Bks u =>
      List.forallb nf_proof_freeb Us && (List.forallb (normal_block_forallb (fun _ => nf_proof_freeb)) Bks
                                         && ne_proof_freeb u)
  | ne_app u W => ne_proof_freeb u && nf_proof_freeb W
  | ne_var _ | ne_glob _ => true
  | ne_proj _ u => ne_proof_freeb u
  end.

Lemma nf_proof_freeb_iff :
  (forall W, nf_proof_freeb W = true <-> nf_proof_free W) /\
  (forall u, ne_proof_freeb u = true <-> ne_proof_free u).
Proof.
  assert (Hand : forall A B C D : Prop, (A <-> B) -> (C <-> D) -> (A /\ C <-> B /\ D)) by tauto.
  apply nf_ne_ind; intros; cbn; rewrite ?Bool.andb_true_iff;
    repeat apply Hand;
    try solve [ split; [ intros _; exact I | reflexivity ] | split; [ discriminate | contradiction ] | eauto ].
  (** The lists, element by element. *)
  all: (eapply list_all_forallb; [ eassumption |]); intros x Hx; try destruct Hx; cbn; try solve [ tauto | eauto ].
  (** A block: its motive and its branches. *)
  all: unfold normal_block_forallb, normal_block_forall; cbn; rewrite Bool.andb_true_iff; apply Hand; [ tauto |].
  all: (eapply list_all_forallb; [ eassumption |]); intros y Hy; destruct Hy; cbn; tauto.
Qed.

(** A level below a level fresh at [k] mentions [k] only in atoms that the
    larger one's constant absorbs: an atom of the smaller one that mentions
    [k] is not an atom of the larger, and the assignment that makes it alone
    large, at [ω·s + N] for its sort [s], is below the larger level only if
    that level's constant is at least [ω·(s+1)]. *)
(** An erased atom of a fresh list, up to erasure, is fresh.  Atoms are
    compared up to erasure ([level_atoms_In]), and an atom that holds a
    proof may mention a variable that its erasure does not; the atoms of a
    canonical level are erased ([lvl_canonical_erased],
    [level_atoms_erased]), and by the 𝕃 invariant (typed level normal forms
    hold no proofs) so are those of every typed level normal form. *)
Lemma level_atoms_fresh_In : forall k ys j s a, all_list (fun a => ne_fresh k (atom_level a)) ys -> level_atoms_In j s a ys ->
    ne_erase a = a -> ne_fresh k a.
Proof.
  induction ys as [| [j0 t b] r IH]; cbn; intros j s a Hf Hi Ha; [ contradiction |].
  destruct Hf as [Hb Hr]; destruct Hi as [(_ & _ & Hab) | Hi]; [| eapply IH; eassumption ].
  rewrite <- Ha, Hab; exact (ne_fresh_erase _ _ Hb).
Qed.

Lemma lvl_le_level_atoms_fresh : forall k l l', lvl_le l l' -> all_list (fun a => ne_fresh k (atom_level a)) (snd l') ->
    forall j s a, level_atoms_In j s a (snd l) -> ne_erase a = a -> ~ ne_fresh k a -> s < fst (fst l').
Proof.
  intros k [c xs] [d ys] Hle Hys j s a Hin Hea Ha; cbn [fst snd] in *.
  rewrite lvl_le_correct in Hle.
  destruct (Nat.lt_ge_cases s (fst d)) as [| Hs]; [ assumption | exfalso ].
  assert (Hn : level_atoms_lookup a s ys = None).
  { destruct (level_atoms_lookup a s ys) eqn:L; [| reflexivity ].
    apply level_atoms_lookup_In in L; exfalso; apply Ha; eapply level_atoms_fresh_In; eassumption. }
  set (N := S (snd d + level_atoms_max_offset ys)).
  specialize (Hle (ν_at a s N) (ν_at_adm _ _ _)).
  unfold lvl_eval in Hle; cbn [fst snd] in Hle.
  rewrite (level_atoms_eval_at_none _ _ _ _ Hn) in Hle.
  assert (Hge : ordinal_le (s, N) (level_atoms_eval (ν_at a s N) xs)).
  { clear Hle; induction xs as [| [j0 t b] r IH]; cbn in Hin |- *; [ contradiction |].
    destruct Hin as [(<- & <- & Hab) | Hin].
    - unfold ν_at at 1; rewrite (at_cmp_erase_eq_r a s b a s (eq_sym Hab)), at_cmp_refl.
      generalize (level_atoms_eval (ν_at a s N) r); intros; ordinal_solve.
    - specialize (IH Hin); revert IH; generalize (level_atoms_eval (ν_at a s N) r) (ν_at a s N b t); intros; ordinal_solve. }
  assert (HN1 : snd d < N) by (subst N; lia).
  assert (HN2 : level_atoms_max_offset ys < N) by (subst N; lia).
  clearbody N.
  revert Hle Hge Hs HN1 HN2; generalize (level_atoms_eval (ν_at a s N) xs) (level_atoms_max_offset ys); intros; ordinal_solve.
Qed.

(** Un-weakening commutes with erasure: the marker mentions no variable. *)
Lemma nf_ne_erase_unwk :
  (forall W k, nf_erase (nf_unwk k W) = nf_unwk k (nf_erase W)) /\
  (forall u k, ne_erase (ne_unwk k u) = ne_unwk k (ne_erase u)).
Proof.
  apply nf_ne_ind; intros; cbn [nf_erase ne_erase nf_unwk ne_unwk]; try solve [ f_equal; eauto ];
    f_equal; try solve [ eauto ]; rewrite ?List.map_map;
    (eapply list_all_map_ext; [ eassumption |]); intros x Hx;
    first [ apply Hx
          | solve [ destruct Hx; unfold map_level_atom; cbn; f_equal; eauto ]
          | destruct Hx as [n' A HA brs Hbrs]; unfold map_normal_block; cbn; f_equal; [ apply HA |];
            rewrite !List.map_map; eapply list_all_map_ext; [ exact Hbrs |];
            intros br Hbr; destruct Hbr; unfold map_normal_branch; cbn; f_equal; eauto ].
Qed.

(** ** The Bound of a Level Under a Binder

    The least level of the context that is above a level [l] of the context
    extended by a variable, for every value of the variable: an atom fresh
    at [k] stays, un-weakened, and an atom that mentions [k], of sort [s],
    ranges over the ordinals below [ω·(s+1)], which is the bound it
    contributes ([lvl_bound_le], [lvl_le_bound]). *)
Fixpoint level_atoms_fresh_part (k : nat) (xs : list level_atom) : list level_atom :=
  match xs with
  | nil => nil
  | mk_level_atom j s a :: r => if ne_freshb k a then mk_level_atom j s a :: level_atoms_fresh_part k r else level_atoms_fresh_part k r
  end.

Fixpoint level_atoms_open_bound (k : nat) (xs : list level_atom) : o2 :=
  match xs with
  | nil => ordinal_zero
  | mk_level_atom j s a :: r => if ne_freshb k a then level_atoms_open_bound k r else ordinal_max (S s, 0) (level_atoms_open_bound k r)
  end.

Definition lvl_bound (k : nat) (l : lvl) : lvl :=
  (ordinal_max (fst l) (level_atoms_open_bound k (snd l)), List.map (map_level_atom (ne_unwk k)) (level_atoms_fresh_part k (snd l))).

(** The bound, weakened back, is above the level: the fresh atoms are the
    same, and an atom of sort [s] is below [ω·(s+1)]. *)
Lemma lvl_bound_above : forall k l,
    lvl_le l (ordinal_max (fst l) (level_atoms_open_bound k (snd l)), level_atoms_fresh_part k (snd l)).
Proof.
  intros k [c xs]; apply lvl_le_correct; intros ν Hν; unfold lvl_eval; cbn [fst snd].
  enough (ordinal_le (level_atoms_eval ν xs) (ordinal_max (level_atoms_open_bound k xs) (level_atoms_eval ν (level_atoms_fresh_part k xs)))) as H
    by (revert H; generalize (level_atoms_eval ν xs) (level_atoms_open_bound k xs) (level_atoms_eval ν (level_atoms_fresh_part k xs)); intros; ordinal_solve).
  induction xs as [| [j s a] r IH]; cbn [level_atoms_eval level_atoms_open_bound level_atoms_fresh_part]; [ ordinal_solve |].
  pose proof (lvl_adm_sort _ Hν a s) as Hνa; clear Hν; rename Hνa into Hν.
  destruct (ne_freshb k a); cbn [level_atoms_eval].
  - revert IH; generalize (level_atoms_eval ν r) (level_atoms_open_bound k r) (level_atoms_eval ν (level_atoms_fresh_part k r)) (ν a s); intros; ordinal_solve.
  - revert IH Hν; generalize (level_atoms_eval ν r) (level_atoms_open_bound k r) (level_atoms_eval ν (level_atoms_fresh_part k r)) (ν a s); intros; ordinal_solve.
Qed.

(** The bound is below every level fresh at [k] above the level, un-weakened:
    so it is the least such level of the context. *)
Lemma level_atoms_eval_unwk : forall ν k xs,
    level_atoms_eval ν (List.map (map_level_atom (ne_unwk k)) xs) = level_atoms_eval (fun a s => ν (ne_unwk k a) s) xs.
Proof. intros ν k; induction xs as [| [j s a] r IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma level_atoms_eval_fresh_part : forall ν k xs, ordinal_le (level_atoms_eval ν (level_atoms_fresh_part k xs)) (level_atoms_eval ν xs).
Proof.
  intros ν k; induction xs as [| [j s a] r IH]; cbn [level_atoms_eval level_atoms_fresh_part]; [ ordinal_solve |].
  destruct (ne_freshb k a); cbn [level_atoms_eval];
    revert IH; generalize (level_atoms_eval ν r) (level_atoms_eval ν (level_atoms_fresh_part k r)) (ν a s); intros; ordinal_solve.
Qed.

Lemma level_atoms_open_bound_le : forall k xs d, level_atoms_erased xs ->
    (forall j s a, level_atoms_In j s a xs -> ne_erase a = a -> ~ ne_fresh k a -> s < fst d) ->
    ordinal_le (level_atoms_open_bound k xs) d.
Proof.
  intros k xs d; induction xs as [| [j s a] r IH]; cbn [level_atoms_open_bound]; intros HE H; [ apply ordinal_le_zero |].
  cbn [level_atoms_erased] in HE; destruct HE as [Ha Hr].
  assert (IH' : ordinal_le (level_atoms_open_bound k r) d) by (apply IH; [ exact Hr | intros; eapply H; [ right | |]; eassumption ]).
  destruct (ne_freshb k a) eqn:E; [ exact IH' |].
  assert (Hs : s < fst d).
  { eapply H; [ left; auto | exact Ha |]. intros Hf; apply (proj2 nf_freshb_iff) in Hf; congruence. }
  revert IH' Hs; generalize (level_atoms_open_bound k r); intros; ordinal_solve.
Qed.

Lemma lvl_le_bound : forall k l l', level_atoms_erased (snd l) -> lvl_le l l' -> all_list (fun a => ne_fresh k (atom_level a)) (snd l') ->
    lvl_le (lvl_bound k l) (fst l', List.map (map_level_atom (ne_unwk k)) (snd l')).
Proof.
  intros k [c xs] [d ys] HE Hle Hys; cbn [fst snd] in *.
  pose proof (lvl_le_level_atoms_fresh _ _ _ Hle Hys) as Hs; cbn [fst snd] in Hs.
  pose proof (level_atoms_open_bound_le k xs d HE Hs) as Hb.
  rewrite lvl_le_correct in Hle |- *; intros ν Hν.
  set (ν' := fun a s => ν (ne_unwk k a) s).
  assert (Hν' : lvl_adm ν').
  { constructor; intros a; [ intros s; apply (lvl_adm_sort _ Hν) |].
    intros b s Hab; apply (lvl_adm_erase _ Hν).
    rewrite !(proj2 nf_ne_erase_unwk), Hab; reflexivity. }
  specialize (Hle ν' Hν'); unfold lvl_bound, lvl_eval in *; cbn [fst snd] in *.
  rewrite !level_atoms_eval_unwk; fold ν'.
  pose proof (level_atoms_eval_fresh_part ν' k xs) as Hf.
  revert Hle Hb Hf; generalize (level_atoms_eval ν' xs) (level_atoms_eval ν' ys) (level_atoms_eval ν' (level_atoms_fresh_part k xs)) (level_atoms_open_bound k xs); intros; ordinal_solve.
Qed.

(** The fresh atoms are fresh and are atoms of the level; the bound of the
    others is of the tier just above their largest sort. *)
Lemma level_atoms_fresh_part_fresh : forall k xs, all_list (fun a => ne_fresh k (atom_level a)) (level_atoms_fresh_part k xs).
Proof.
  intros k; induction xs as [| [j s a] r IH]; cbn [level_atoms_fresh_part]; [ exact I |].
  destruct (ne_freshb k a) eqn:E; cbn; [| exact IH ].
  split; [ apply (proj2 nf_freshb_iff); exact E | exact IH ].
Qed.

Lemma level_atoms_open_bound_fst : forall k xs n,
    (forall j s a, level_atoms_In j s a xs -> s <= n) ->
    fst (level_atoms_open_bound k xs) <= S n.
Proof.
  intros k xs n; induction xs as [| [j s a] r IH]; cbn [level_atoms_open_bound]; intros H; [ cbn; lia |].
  assert (IH' : fst (level_atoms_open_bound k r) <= S n) by (apply IH; intros; eapply H; right; eassumption).
  assert (Hs : s <= n) by (eapply H; left; auto).
  destruct (ne_freshb k a); [ exact IH' |].
  apply ordinal_max_fst_le; [ cbn; lia | exact IH' ].
Qed.

(** The bound, weakened back, is below every level fresh at [k] above the
    level. *)
Lemma lvl_le_bound_wk : forall k l l', level_atoms_erased (snd l) -> lvl_le l l' -> all_list (fun a => ne_fresh k (atom_level a)) (snd l') ->
    lvl_le (ordinal_max (fst l) (level_atoms_open_bound k (snd l)), level_atoms_fresh_part k (snd l)) l'.
Proof.
  intros k [c xs] [d ys] HE Hle Hys; cbn [fst snd] in *.
  pose proof (lvl_le_level_atoms_fresh _ _ _ Hle Hys) as Hs; cbn [fst snd] in Hs.
  pose proof (level_atoms_open_bound_le k xs d HE Hs) as Hb.
  rewrite lvl_le_correct in Hle |- *; intros ν Hν.
  specialize (Hle ν Hν); unfold lvl_eval in *; cbn [fst snd] in *.
  pose proof (level_atoms_eval_fresh_part ν k xs) as Hf.
  revert Hle Hb Hf; generalize (level_atoms_eval ν xs) (level_atoms_eval ν ys) (level_atoms_eval ν (level_atoms_fresh_part k xs)) (level_atoms_open_bound k xs); intros; ordinal_solve.
Qed.

(** ** The Universe of a [Π]

    A [Π] of a small domain and a small codomain is small, at the join of the
    domain's level and the bound of the codomain's ([lvl_bound]): the
    codomain's level lives under the domain, and an atom of it that mentions
    the bound variable is bounded by its sort.  Any other [Π] is at the join
    of the universes of its parts ([universe_nf_max]).  This is the term the checker
    normalises: the join is not canonical, and normalising it is what makes
    the inferred universe a normal form. *)
Definition universe_nf_pi_tm (u v : universe_nf) : exp :=
  match u, v with
  | universe_small l, universe_small l' =>
      a_univ (a_maxl (lvl_exp_of (fst l) (List.map atom_exp (snd l)))
                     (lvl_exp_of (fst (lvl_bound 0 l')) (List.map atom_exp (snd (lvl_bound 0 l')))))
  | _, _ => universe_nf_tm (universe_nf_max u v)
  end.
