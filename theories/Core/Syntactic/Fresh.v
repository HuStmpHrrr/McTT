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
From Mctt.Core.Syntactic Require Import Levels.
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
  | a_typ _ | a_level | a_llit _ | a_nat | a_zero
  | a_True | a_true | a_False => True
  | a_univ M | a_succl M | a_succ M => exp_fresh k M
  | a_maxl M N | a_app M N => exp_fresh k M /\ exp_fresh k N
  | a_natrec A MZ MS M =>
      exp_fresh (S k) A /\ exp_fresh k MZ /\ exp_fresh (S (S k)) MS /\ exp_fresh k M
  | a_exfalso A M => exp_fresh (S k) A /\ exp_fresh k M
  | a_pi A B | a_fn A B => exp_fresh k A /\ exp_fresh (S k) B
  | a_var x => x <> k
  | a_let b B => bnd_fresh k b /\ exp_fresh (S k) B
  | a_mem H _ => modexp_fresh k H
  end
with modexp_fresh (k : nat) (H : modexp) {struct H} : Prop :=
  match H with
  | me_unit _ => True
  | me_var x => x <> k
  | me_mem H _ => modexp_fresh k H
  | me_app H N => modexp_fresh k H /\ exp_fresh k N
  | me_lit U => gunit_fresh k U
  end
with bnd_fresh (k : nat) (b : bnd) {struct b} : Prop :=
  match b with
  | b_def oA M => match oA with Some A => exp_fresh k A | None => True end /\ exp_fresh k M
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
  | md_body Φ => gmod_fresh k Φ
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
  | ge_def _ _ A B => exp_fresh k A /\ match B with Some M => exp_fresh k M | None => True end
  | ge_mod _ U => gunit_fresh k U
  end
with centry_fresh (k : nat) (e : centry) {struct e} : Prop :=
  match e with
  | ce_ass A => exp_fresh k A
  | ce_def A M => exp_fresh k A /\ exp_fresh k M
  | ce_mod U => gunit_fresh k U
  end.

(** The telescope clause of [gunit_fresh], as a definition of its own. *)
Fixpoint tele_fresh (k : nat) (Δ : list centry) : Prop :=
  match Δ with
  | nil => True
  | cons e Δ' => centry_fresh (List.length Δ' + k) e /\ tele_fresh k Δ'
  end.

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
  intros; cbn [exp_fresh modexp_fresh bnd_fresh gunit_fresh moddef_fresh gmod_fresh
               gentry_fresh centry_fresh exp_wk modexp_wk bnd_wk gunit_wk moddef_wk
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
  (forall b k χ, bnd_fresh k b -> wk_id_away k χ -> bnd_wk b χ = b) /\
  (forall U k χ, gunit_fresh k U -> wk_id_away k χ -> gunit_wk U χ = U) /\
  (forall D k χ, moddef_fresh k D -> wk_id_away k χ -> moddef_wk D χ = D) /\
  (forall Φ k χ, gmod_fresh k Φ -> wk_id_away k χ -> gmod_wk Φ χ = Φ) /\
  (forall E k χ, gentry_fresh k E -> wk_id_away k χ -> gentry_wk E χ = E) /\
  (forall e k χ, centry_fresh k e -> wk_id_away k χ -> centry_wk e χ = e).
Proof.
  syn_mut_ind; fresh_case;
    try solve [ match goal with H : wk_id_away _ _ |- _ => apply H; assumption end
              | match goal with H : forall A, Some ?X = Some A -> _ |- _ => eapply (H X); eauto end ].
  (** The telescope of a unit: its own induction, over the [Forall] the
      principle carries. *)
  match goal with
  | HF : List.Forall _ _ |- _ => clear - HF H1 H2; induction HF; cbn in *; destruct_conjs; f_equal; eauto
  end.
Qed.

Lemma syn_wk_fresh :
  (forall M k φ, wk_avoids k φ -> exp_fresh k M[φ]ʷ) /\
  (forall H k φ, wk_avoids k φ -> modexp_fresh k (modexp_wk H φ)) /\
  (forall b k φ, wk_avoids k φ -> bnd_fresh k (bnd_wk b φ)) /\
  (forall U k φ, wk_avoids k φ -> gunit_fresh k (gunit_wk U φ)) /\
  (forall D k φ, wk_avoids k φ -> moddef_fresh k (moddef_wk D φ)) /\
  (forall Φ k φ, wk_avoids k φ -> gmod_fresh k (gmod_wk Φ φ)) /\
  (forall E k φ, wk_avoids k φ -> gentry_fresh k (gentry_wk E φ)) /\
  (forall e k φ, wk_avoids k φ -> centry_fresh k (centry_wk e φ)).
Proof.
  syn_mut_ind; fresh_case; rewrite ?gm_binders_wk, ?length_tele_wk; eauto;
    try solve [ match goal with H : forall A, Some ?X = Some A -> _ |- _ => eapply (H X); eauto end ].
  match goal with
  | HF : List.Forall _ _ |- _ =>
      clear - HF H1; induction HF; cbn in *; [ exact I | rewrite length_tele_wk; split; eauto ]
  end.
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

(** The two forms the checker meets: a weakening by one at the front. *)
Corollary exp_unwk_shift : forall M, M[↑]ʷ[unwk 0]ʷ = M.
Proof. intros; exact (exp_unwk_wk 0 M). Qed.

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
Scheme nf_mind := Induction for nf Sort Prop
  with ne_mind := Induction for ne Sort Prop
  with la_mind := Induction for lvl_atoms Sort Prop.

Combined Scheme nf_mut_ind from nf_mind, ne_mind, la_mind.

Fixpoint nf_fresh (k : nat) (W : nf) {struct W} : Prop :=
  match W with
  | nf_typ _ | nf_level | nf_nat | nf_zero | nf_True | nf_true | nf_False => True
  | nf_univ _ xs | nf_lvl _ xs => la_fresh k xs
  | nf_succ W => nf_fresh k W
  | nf_pi A B | nf_fn A B => nf_fresh k A /\ nf_fresh (S k) B
  | nf_neut u => ne_fresh k u
  end
with ne_fresh (k : nat) (u : ne) {struct u} : Prop :=
  match u with
  | ne_natrec A MZ MS u =>
      nf_fresh (S k) A /\ nf_fresh k MZ /\ nf_fresh (S (S k)) MS /\ ne_fresh k u
  | ne_exfalso A u => nf_fresh (S k) A /\ ne_fresh k u
  | ne_app u W => ne_fresh k u /\ nf_fresh k W
  | ne_var x => x <> k
  | ne_glob _ => True
  end
with la_fresh (k : nat) (xs : lvl_atoms) {struct xs} : Prop :=
  match xs with
  | la_nil => True
  | la_cons _ u r => ne_fresh k u /\ la_fresh k r
  end.

Fixpoint nf_unwk (k : nat) (W : nf) {struct W} : nf :=
  match W with
  | nf_typ i => nf_typ i
  | nf_univ c xs => nf_univ c (la_unwk k xs)
  | nf_level => nf_level
  | nf_lvl c xs => nf_lvl c (la_unwk k xs)
  | nf_nat => nf_nat
  | nf_zero => nf_zero
  | nf_succ W => nf_succ (nf_unwk k W)
  | nf_True => nf_True
  | nf_true => nf_true
  | nf_False => nf_False
  | nf_pi A B => nf_pi (nf_unwk k A) (nf_unwk (S k) B)
  | nf_fn A M => nf_fn (nf_unwk k A) (nf_unwk (S k) M)
  | nf_neut u => nf_neut (ne_unwk k u)
  end
with ne_unwk (k : nat) (u : ne) {struct u} : ne :=
  match u with
  | ne_natrec A MZ MS u =>
      ne_natrec (nf_unwk (S k) A) (nf_unwk k MZ) (nf_unwk (S (S k)) MS) (ne_unwk k u)
  | ne_exfalso A u => ne_exfalso (nf_unwk (S k) A) (ne_unwk k u)
  | ne_app u W => ne_app (ne_unwk k u) (nf_unwk k W)
  | ne_var x => ne_var (unwk k x)
  | ne_glob p => ne_glob p
  end
with la_unwk (k : nat) (xs : lvl_atoms) {struct xs} : lvl_atoms :=
  match xs with
  | la_nil => la_nil
  | la_cons j u r => la_cons j (ne_unwk k u) (la_unwk k r)
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
  intros c [| [j a] r] φ; destruct c; cbn; try reflexivity;
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
  intros c [| [j a] r] k HF; destruct c; cbn; try exact I;
    inversion HF as [| ? ? Ha HF']; subst;
    apply lvl_fold_fresh; [ apply succl_n_fresh; exact Ha | exact HF'
                          | split; [ exact I | apply succl_n_fresh; exact Ha ] | exact HF' ].
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

(** Freshness of a normal form is freshness of the term it denotes, and
    un-weakening agrees with the renaming on terms. *)
Lemma nf_fresh_to_exp :
  (forall W k, nf_fresh k W -> exp_fresh k (nf_to_exp W)) /\
  (forall u k, ne_fresh k u -> exp_fresh k (ne_to_exp u)) /\
  (forall xs k, la_fresh k xs -> List.Forall (fun p => exp_fresh k (snd p)) (la_to_list xs)).
Proof.
  apply nf_mut_ind; intros; cbn in *; destruct_conjs;
    try exact I;
    try solve [ repeat split; eauto
              | apply lvl_exp_of_fresh; eauto
              | constructor; eauto ].
  (** A global never mentions a local variable. *)
  apply qname_term_fresh.
Qed.

Lemma nf_unwk_to_exp :
  (forall W k, nf_to_exp (nf_unwk k W) = (nf_to_exp W)[unwk k]ʷ) /\
  (forall u k, ne_to_exp (ne_unwk k u) = (ne_to_exp u)[unwk k]ʷ) /\
  (forall xs k, la_to_list (la_unwk k xs)
                = List.map (fun p => (fst p, (snd p)[unwk k]ʷ)) (la_to_list xs)).
Proof.
  apply nf_mut_ind; intros; cbn;
    try reflexivity;
    try solve [ (** A small universe and a level carry the same atom list, so
                    both go through [lvl_exp_of_wk]. *)
                f_equal; rewrite lvl_exp_of_wk; f_equal; eauto
              | rewrite lvl_exp_of_wk; f_equal; eauto
                (** A global is closed, so the renaming does not touch it. *)
              | symmetry; apply qname_term_wk
              | f_equal; eauto
              | match goal with
                | Hu : forall k, _ = _, Hr : forall k, _ = _ |- _ => rewrite Hu, Hr; reflexivity
                end ].
Qed.

(** The three facts of un-weakening, on normal forms. *)
Theorem nf_fresh_unwk : forall k W, nf_fresh k W -> nf_to_exp W = (nf_to_exp (nf_unwk k W))[wk_qn k ↑]ʷ.
Proof.
  intros * HW.
  rewrite (proj1 nf_unwk_to_exp).
  apply exp_unwk_spec, (proj1 nf_fresh_to_exp), HW.
Qed.

(** Freshness of a normal form is decidable: it is a conjunction of
    disequalities of indices, so it is decided by a boolean function and
    reflection. *)
Fixpoint nf_freshb (k : nat) (W : nf) {struct W} : bool :=
  match W with
  | nf_typ _ | nf_level | nf_nat | nf_zero | nf_True | nf_true | nf_False => true
  | nf_univ _ xs | nf_lvl _ xs => la_freshb k xs
  | nf_succ W => nf_freshb k W
  | nf_pi A B | nf_fn A B => nf_freshb k A && nf_freshb (S k) B
  | nf_neut u => ne_freshb k u
  end
with ne_freshb (k : nat) (u : ne) {struct u} : bool :=
  match u with
  | ne_natrec A MZ MS u =>
      nf_freshb (S k) A && nf_freshb k MZ && nf_freshb (S (S k)) MS && ne_freshb k u
  | ne_exfalso A u => nf_freshb (S k) A && ne_freshb k u
  | ne_app u W => ne_freshb k u && nf_freshb k W
  | ne_var x => negb (Nat.eqb x k)
  | ne_glob _ => true
  end
with la_freshb (k : nat) (xs : lvl_atoms) {struct xs} : bool :=
  match xs with
  | la_nil => true
  | la_cons _ u r => ne_freshb k u && la_freshb k r
  end.

Lemma nf_freshb_iff :
  (forall W k, nf_freshb k W = true <-> nf_fresh k W) /\
  (forall u k, ne_freshb k u = true <-> ne_fresh k u) /\
  (forall xs k, la_freshb k xs = true <-> la_fresh k xs).
Proof.
  apply nf_mut_ind; intros; cbn;
    repeat rewrite Bool.andb_true_iff;
    try solve [ split; [ intros _; exact I | reflexivity ]
              | rewrite Bool.negb_true_iff, Nat.eqb_neq; reflexivity
              | firstorder ].
Qed.

Definition nf_fresh_dec : forall k W, { nf_fresh k W } + { ~ nf_fresh k W }.
Proof.
  intros k W; destruct (nf_freshb k W) eqn:E;
    [ left; apply (proj1 nf_freshb_iff); exact E
    | right; intros H; apply (proj1 nf_freshb_iff) in H; congruence ].
Defined.

(** A level below a level fresh at [k] is fresh at [k]: an atom of the
    smaller one that mentions [k] is not an atom of the larger, and the
    assignment that makes it alone large separates the two. *)
Lemma la_fresh_In : forall k ys j a, la_fresh k ys -> la_In j a ys -> ne_fresh k a.
Proof.
  induction ys as [| j0 b r IH]; cbn; intros j a Hf Hi; [ contradiction |].
  destruct Hf as [Hb Hr]; destruct Hi as [[_ ->] | Hi]; [ exact Hb | eapply IH; eassumption ].
Qed.

Lemma lvl_le_la_fresh : forall k l l', lvl_le l l' -> la_fresh k (snd l') -> la_fresh k (snd l).
Proof.
  intros k [c xs] [d ys] Hle Hys; cbn in *.
  pose proof (proj1 (lvl_le_correct _ _) Hle) as Hev; clear Hle; rename Hev into Hle.
  revert c Hle; induction xs as [| j a r IH]; intros c Hle; cbn; [ exact I |].
  split.
  - destruct (ne_freshb k a) eqn:E; [ apply (proj1 (proj2 nf_freshb_iff)); exact E |].
    exfalso.
    assert (Hn : la_look a ys = None).
    { destruct (la_look a ys) eqn:L; [| reflexivity ].
      apply la_look_In in L.
      pose proof (la_fresh_In _ _ _ _ Hys L) as Hf.
      apply (proj1 (proj2 nf_freshb_iff)) in Hf; congruence. }
    specialize (Hle (ν_at a (S (Nat.max d (la_maxoff ys))))).
    unfold lvl_ev in Hle; cbn [fst snd la_ev] in Hle.
    rewrite (la_ev_at_none _ _ _ Hn) in Hle.
    unfold ν_at at 1 in Hle; rewrite ne_cmp_refl in Hle.
    lia.
  - apply (IH c); intros ν; specialize (Hle ν); unfold lvl_ev in *; cbn [fst snd la_ev] in *; lia.
Qed.

(** ** The Universe of a [Π]

    A [Π] of a small domain and a small codomain whose level does not mention
    the bound variable is small, at the join of the domain's level and the
    codomain's, un-weakened into the context of the [Π]; any other [Π] is at
    the join of the universes of its parts ([unf_max]), where a small
    universe at an open level falls back to the least large one.  This is the
    term the checker normalises: the join of two canonical levels, one of them
    un-weakened, is not canonical, and normalising it is what makes the
    inferred universe a normal form. *)
Definition unf_pi_tm (u v : unf) : exp :=
  match u, v with
  | uns l, uns l' =>
      if la_freshb 0 (snd l')
      then a_univ (a_maxl (lvl_exp_of (fst l) (la_to_list (snd l)))
                          (lvl_exp_of (fst l') (la_to_list (la_unwk 0 (snd l')))))
      else a_typ 0
  | _, _ => unf_tm (unf_max u v)
  end.
