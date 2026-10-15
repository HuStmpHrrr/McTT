From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.

(** * What the Implementations Look Up

    The declarations the evaluator and readback keep ([lk_cache]), and the
    data a command computes once for the implementations it runs
    ([FCtx]). *)

Definition inspect {A} (a : A) : { b | a = b } := exist _ a eq_refl.

Definition qname_dec : forall (x y : qname), {x = y} + {x <> y}.
Proof. decide equality; apply list_eq_dec, string_dec. Defined.

(** ** Filed Units by Path

    A trie of the filed units, keyed by the components of their paths:
    looking a path up compares one component per level, with the components
    present at that level, rather than every path filed.  Strings are only
    compared for equality, as extraction makes that comparison native. *)
Inductive ptrie : Set := pnode : option gunit -> pkids -> ptrie
with pkids : Set :=
| pk_nil : pkids
| pk_cons : string -> ptrie -> pkids -> pkids.

Definition ptrie_empty : ptrie := pnode None pk_nil.

Fixpoint kid_find (ks : pkids) (x : string) : option ptrie :=
  match ks with
  | pk_nil => None
  | pk_cons y t ks' => if String.eqb x y then Some t else kid_find ks' x
  end.

(** [ks] with the subtrie at [x] replaced by its image under [f], the empty
    trie's if there is none. *)
Fixpoint kid_upd (ks : pkids) (x : string) (f : ptrie -> ptrie) : pkids :=
  match ks with
  | pk_nil => pk_cons x (f ptrie_empty) pk_nil
  | pk_cons y t ks' => if String.eqb x y then pk_cons y (f t) ks' else pk_cons y t (kid_upd ks' x f)
  end.

Fixpoint pt_find (t : ptrie) (fp : path) {struct fp} : option gunit :=
  match t with
  | pnode o ks =>
      match fp with
      | nil => o
      | x :: fp' =>
          match kid_find ks x with
          | Some t' => pt_find t' fp'
          | None => None
          end
      end
  end.

Fixpoint pt_add (fp : path) (U : gunit) (t : ptrie) {struct fp} : ptrie :=
  match t with
  | pnode o ks =>
      match fp with
      | nil => pnode (Some U) ks
      | x :: fp' => pnode o (kid_upd ks x (pt_add fp' U))
      end
  end.

Lemma kid_find_upd : forall ks x f y,
    kid_find (kid_upd ks x f) y =
    if String.eqb y x then Some (f (match kid_find ks x with Some t => t | None => ptrie_empty end))
    else kid_find ks y.
Proof.
  induction ks as [| z t ks IH]; intros; cbn [kid_find kid_upd].
  - destruct (String.eqb_spec y x); reflexivity.
  - destruct (String.eqb_spec x z) as [-> |]; cbn [kid_find].
    + destruct (String.eqb_spec y z); reflexivity.
    + destruct (String.eqb_spec y z) as [-> |]; rewrite ?IH.
      * destruct (String.eqb_spec z x); [ congruence | reflexivity ].
      * reflexivity.
Qed.

Lemma pt_find_empty : forall fp, pt_find ptrie_empty fp = None.
Proof. intros [|]; reflexivity. Qed.

Lemma pt_find_add : forall fp U t fq,
    pt_find (pt_add fp U t) fq = if path_eq_dec fq fp then Some U else pt_find t fq.
Proof.
  induction fp as [| x fp IH]; intros U [o ks] fq; cbn [pt_add pt_find].
  - destruct fq as [| y fq]; cbn [pt_find].
    + destruct (path_eq_dec nil nil); [ reflexivity | congruence ].
    + destruct (path_eq_dec (y :: fq) nil); [ discriminate | reflexivity ].
  - destruct fq as [| y fq]; cbn [pt_find].
    + destruct (path_eq_dec nil (x :: fp)); [ discriminate | reflexivity ].
    + rewrite kid_find_upd.
      destruct (String.eqb_spec y x) as [-> |].
      * rewrite IH.
        destruct (path_eq_dec fq fp) as [-> | Hn].
        -- destruct (path_eq_dec (x :: fp) (x :: fp)); [ reflexivity | congruence ].
        -- destruct (path_eq_dec (x :: fq) (x :: fp)) as [He | _]; [ injection He; congruence |].
           destruct (kid_find ks x); [ reflexivity | apply pt_find_empty ].
      * destruct (path_eq_dec (y :: fq) (x :: fp)) as [He | _]; [ injection He; congruence | reflexivity ].
Qed.

(** The trie of the filed units [Θ]: the newest entry of a path decides, as
    in [gds_lookup]. *)
Definition pt_of (Θ : gdeps) : ptrie :=
  fold_right (fun e t => pt_add (fst e) (snd e) t) ptrie_empty Θ.

Lemma pt_of_find : forall Θ fp, pt_find (pt_of Θ) fp = gds_lookup Θ fp.
Proof.
  induction Θ as [| [fq U] Θ IH]; intros fp; cbn [pt_of fold_right gds_lookup fst snd].
  - apply pt_find_empty.
  - fold (pt_of Θ); rewrite pt_find_add, <- IH; unfold path_beq.
    destruct (path_eq_dec fp fq); reflexivity.
Qed.

(** ** The Declarations Kept *)

Section Cache.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** A declaration looked up already: the eliminator keeps the one of the
      constructor it takes apart for the recursive results, whose arguments
      are of the same type, and compares names instead of looking up
      again. *)
  Definition lk_cache : Set := option {x : qname * ind_decl | ind_lookup Θ Ξ (fst x) = Some (snd x)}.
End Cache.

(** ** What a Command Looks Up Once

    The data the implementations look global names up in, computed once by
    the command that runs them ([Extraction.Command]) rather than once per
    lookup.  It is a class, so that the reference checker
    ([Reference.TypeCheck]) and the statements about the implementations
    ([Reference.Refinement]) get the default, [fctx_none], without naming
    it; any instance gives the same results, since every lookup it
    provides is proved equal to the one of the global context.

    - [fc_seed]: a declaration the evaluator and readback start from, as if
      they had looked it up already: the eliminator of the type bound as
      the natural numbers then looks nothing up;
    - [fc_units]: the filed units by path, [gds_lookup Θ] ([fc_units_ok]),
      computed from a trie ([pt_of]). *)
Class FCtx (Θ : gdeps) (Ξ : gstack) : Set := mk_fctx
  { fc_seed : lk_cache Θ Ξ
  ; fc_units : path -> option gunit
  ; fc_units_ok : forall fp, fc_units fp = gds_lookup Θ fp }.

Arguments mk_fctx {Θ Ξ}.
Arguments fc_seed {Θ Ξ}.
Arguments fc_units {Θ Ξ}.
Arguments fc_units_ok {Θ Ξ}.

#[global] Instance fctx_none Θ Ξ : FCtx Θ Ξ | 100 := mk_fctx None (gds_lookup Θ) (fun _ => eq_refl).

(** The lookups through the filed units of an [FCtx]. *)
Section Lookups.
  Variables (Θ : gdeps) (Ξ : gstack).
  Context {F : FCtx Θ Ξ}.

  Definition gc_entry_f p : { o | gc_entry Θ Ξ p = o } :=
    exist _ (gc_entry_u (fc_units F) Ξ p) (eq_sym (gc_entry_u_ok _ _ (fc_units_ok F) Ξ p)).
  Definition gc_module_f p : { o | gc_module Θ Ξ p = o } :=
    exist _ (gc_module_u (fc_units F) Ξ p) (eq_sym (gc_module_u_ok _ _ (fc_units_ok F) Ξ p)).
  Definition ind_lookup_f p : { o | ind_lookup Θ Ξ p = o } :=
    exist _ (ind_lookup_u (fc_units F) Ξ p) (eq_sym (ind_lookup_u_ok _ _ (fc_units_ok F) Ξ p)).

  Definition cache_lookup (ck : lk_cache Θ Ξ) (p : qname) : { o | ind_lookup Θ Ξ p = o } :=
    match ck with
    | Some (exist _ (pc, D) E) =>
        match qname_dec pc p with
        | left Hq => exist _ (Some D) (eq_rect pc (fun r => ind_lookup Θ Ξ r = Some D) E p Hq)
        | right _ => ind_lookup_f p
        end
    | None => ind_lookup_f p
    end.
End Lookups.

(** The data of a command at [Θ ⍮ Ξ]: the trie of [Θ], and the declaration
    at [op] looked up through it. *)
Definition fctx_at (Θ : gdeps) (Ξ : gstack) (op : option qname) : FCtx Θ Ξ :=
  let t := pt_of Θ in
  let uf := pt_find t in
  let Huf := pt_of_find Θ in
  mk_fctx
    match op with
    | Some p =>
        match exist (fun o => ind_lookup Θ Ξ p = o) (ind_lookup_u uf Ξ p) (eq_sym (ind_lookup_u_ok _ _ Huf Ξ p)) with
        | exist _ (Some D) E => Some (exist _ (p, D) E)
        | exist _ None _ => None
        end
    | None => None
    end
    uf Huf.
