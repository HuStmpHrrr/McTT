(** * Checking Privacy

    [refs_check] decides [acc_ok]: every table is computed, so a reference is
    checked by reading the entry it names, and a failure names the module
    that declares the private member and the member. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Stdlib Require Import Lia PeanoNat.
From Mctt.Core.Syntactic Require Import Command.
From Mctt.Core.Syntactic.System Require Import Definitions Privacy Command.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** A private member out of reach: declared in the module of a unit, or
    an entry of a local body, at the chain of submodules [ch] from the local
    module. *)
Inductive priv_err : Set :=
| pe_global : qname -> string -> priv_err
| pe_local : list string -> string -> priv_err.

Definition bn_err (nm : bname) (x : string) : priv_err :=
  match nm with
  | bn_glob p => pe_global p x
  | bn_local ch => pe_local ch x
  end.

Definition tab_check (t : ptab) (x : string) : { e : priv_err | ~ tab_ok t x } + { tab_ok t x }.
Proof.
  destruct t as [| fp ch | nm es | t]; cbn; try (right; exact I).
  destruct (option_map fst (tab_find x es)) as [[|] |] eqn:E.
  - left; exists (bn_err nm x); intros Hn; apply Hn; reflexivity.
  - right; discriminate.
  - right; discriminate.
Defined.

Section PrivacyImpl.
  Variables (Θ : gctx).

  Definition ref_check (r : (ptab * string)%type) :
      { e : priv_err | ~ ref_ok Θ r } + { ref_ok Θ r }.
  Proof.
    destruct r as [t x]; unfold ref_ok; cbn [fst snd].
    destruct t as [| fp ch | nm es | t]; try exact (tab_check _ x).
    destruct (gtab Θ fp ch) as [t |]; [ exact (tab_check t x) | right; exact I ].
  Defined.

  Definition refs_check : forall (l : list (ptab * string)%type),
      { e : priv_err | ~ acc_ok Θ l } + { acc_ok Θ l }.
  Proof.
    induction l as [| r l IH]; [ right; constructor |].
    destruct (ref_check r) as [[e Hr] | Hr]; [ left; exists e; intros Hall; inversion Hall; contradiction |].
    destruct IH as [[e Hl] | Hl]; [ left; exists e; intros Hall; inversion Hall; contradiction | right; constructor; assumption ].
  Defined.
End PrivacyImpl.

(** * The Tables of the Open Frames, Kept

    The scope of a command, [fctx_tabs], holds the self table of every open
    frame, which [btab] builds from the whole body so far.  The executable
    keeps it from one command to the next instead: a command changes only
    the innermost frame, by adding entries to its body ([gm_grows]), and the
    table of the longer body is the shorter one's with the new entries'
    added in front ([btab_from]), as [btab] itself adds them. *)

(** The entries of a body. *)
Fixpoint gm_len (Φ : gmod) : nat :=
  match Φ with
  | gm_nil => 0
  | gm_ext Φ _ _ | gm_open Φ _ _ _ => S (gm_len Φ)
  end.

(** The body without its [k] newest entries. *)
Fixpoint gm_drop (k : nat) (Φ : gmod) : gmod :=
  match k, Φ with
  | 0, _ => Φ
  | S k, gm_ext Φ _ _ | S k, gm_open Φ _ _ _ => gm_drop k Φ
  | S _, gm_nil => gm_nil
  end.

(** [btab nm S Φ], given the table [es] of the body without the [k] newest
    entries of [Φ]: those entries, as [btab] makes them, on top of [es]. *)
Fixpoint btab_from (nm : bname) (S : list ptab) (k : nat) (Φ : gmod) (es : list (string * bool * ptab)) :
    list (string * bool * ptab) :=
  match k, Φ with
  | 0, _ => es
  | Datatypes.S k, gm_ext Φ x E =>
      let es1 := btab_from nm S k Φ es in
      (x, ge_private E, etab (bn_sub nm x) (pt_self (pt_body nm es1) :: S) E) :: es1
  | Datatypes.S k, gm_open Φ H oz its =>
      let es1 := btab_from nm S k Φ es in
      let t := mtab (pt_self (pt_body nm es1) :: S) H in
      let es2 := match oz with Some z => (z, true, t) :: es1 | None => es1 end in
      rev (map (fun it => let '(n, d, pv) := it in (d, pv, tab_sel t n)) its) ++ es2
  | Datatypes.S _, gm_nil => es
  end.

Lemma btab_from_drop : forall nm S k Φ, btab_from nm S k Φ (btab nm S (gm_drop k Φ)) = btab nm S Φ.
Proof.
  intros nm S k; induction k as [| k IH]; intros Φ; [ reflexivity |].
  destruct Φ as [| Φ x E | Φ H oz its]; cbn [btab_from gm_drop btab]; rewrite ?IH; reflexivity.
Qed.

(** A body grows by entries added on top. *)
Inductive gm_grows (Φ : gmod) : gmod -> Prop :=
| gg_refl : gm_grows Φ Φ
| gg_ext : forall Φ' x E, gm_grows Φ Φ' -> gm_grows Φ (gm_ext Φ' x E)
| gg_open : forall Φ' H oz its, gm_grows Φ Φ' -> gm_grows Φ (gm_open Φ' H oz its).

Lemma gm_grows_trans : forall Φ1 Φ2 Φ3, gm_grows Φ1 Φ2 -> gm_grows Φ2 Φ3 -> gm_grows Φ1 Φ3.
Proof. intros * H12 H23; induction H23; [ exact H12 | constructor; auto .. ]. Qed.

Lemma gm_grows_drop : forall Φ Φ', gm_grows Φ Φ' -> gm_drop (gm_len Φ' - gm_len Φ) Φ' = Φ.
Proof.
  assert (Hle : forall Φ Φ', gm_grows Φ Φ' -> gm_len Φ <= gm_len Φ') by (induction 1; cbn; lia).
  induction 1 as [| Φ' x E Hg IH | Φ' H oz its Hg IH].
  - rewrite Nat.sub_diag; reflexivity.
  - pose proof (Hle _ _ Hg); cbn [gm_len]; replace (S (gm_len Φ') - gm_len Φ) with (S (gm_len Φ' - gm_len Φ)) by lia.
    exact IH.
  - pose proof (Hle _ _ Hg); cbn [gm_len]; replace (S (gm_len Φ') - gm_len Φ) with (S (gm_len Φ' - gm_len Φ)) by lia.
    exact IH.
Qed.

(** A frame grows when only its body does. *)
Definition fr_grows (f f' : frame) : Prop :=
  fr_chain f' = fr_chain f /\ fr_params f' = fr_params f /\ gm_grows (fr_body f) (fr_body f').

(** The tables of the frames [f' :: F], from the tables [S] of [f :: F]. *)
Definition tabs_next (f f' : frame) (S : list ptab) : list ptab :=
  match S with
  | pt_self (pt_body nm es) :: S0 =>
      pt_self (pt_body nm (btab_from nm S0 (gm_len (fr_body f') - gm_len (fr_body f)) (fr_body f') es)) :: S0
  | _ => S
  end.

Lemma tabs_next_ok : forall fp Γimp f f' F S,
    S = fctx_tabs fp Γimp (f :: F) -> fr_grows f f' -> tabs_next f f' S = fctx_tabs fp Γimp (f' :: F).
Proof.
  intros * -> (Ec & Ep & Hg); cbn [fctx_tabs tabs_next self_tab]; rewrite Ec, Ep.
  unfold self_tab; rewrite <- (btab_from_drop _ _ (gm_len (fr_body f') - gm_len (fr_body f)) (fr_body f')),
    (gm_grows_drop _ _ Hg); reflexivity.
Qed.

(** The tables of a new frame [f] on top. *)
Definition tabs_push (fp : path) (f : frame) (S : list ptab) : list ptab :=
  let S' := repeat pt_none (List.length (fr_params f)) ++ S in
  self_tab (bn_glob (q_abs fp (fr_chain f))) S' (fr_body f) :: S'.

Lemma tabs_push_ok : forall fp Γimp f F S,
    S = fctx_tabs fp Γimp F -> tabs_push fp f S = fctx_tabs fp Γimp (f :: F).
Proof. intros * ->; reflexivity. Qed.

Lemma fr_grows_refl : forall f, fr_grows f f.
Proof. intros f; split; [ reflexivity | split; [ reflexivity | constructor ] ]. Qed.

Lemma fr_grows_trans : forall f1 f2 f3, fr_grows f1 f2 -> fr_grows f2 f3 -> fr_grows f1 f3.
Proof.
  intros * (E1 & P1 & G1) (E2 & P2 & G2); split; [ congruence | split; [ congruence | eapply gm_grows_trans; eassumption ] ].
Qed.

Lemma fr_grows_add : forall x E f, fr_grows f (fr_add x E f).
Proof. intros; split; [ reflexivity | split; [ reflexivity | constructor; constructor ] ]. Qed.
