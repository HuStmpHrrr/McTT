From Stdlib Require Import List String RelationClasses.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Extraction Require Export FastGlobal.

(** * The Fast Context

    The declarations the evaluator and readback keep ([lk_cache]), and the
    fast context the implementations run on ([FCtx]): the only run-time
    global context of the extracted code.  Its Core reading is in
    [Extraction.Decoding], its lookups in [Extraction.Lookup]. *)

Definition inspect {A} (a : A) : { b | a = b } := exist _ a eq_refl.

(** Equality of lists of names, one [String.compare] per component: once
    extracted (the directive of [Entrypoint]), a comparison of strings the
    compiler knows the type of.  [String.eqb] and [string_dec] extract to
    the generic [(=)], which here would be OCaml's polymorphic equality. *)
Fixpoint names_eqb (p q : list string) : bool :=
  match p, q with
  | nil, nil => true
  | x :: p', y :: q' => match String.compare x y with Eq => names_eqb p' q' | _ => false end
  | _, _ => false
  end.

Lemma names_eqb_eq : forall p q, names_eqb p q = true <-> p = q.
Proof.
  induction p as [| x p IH]; intros [| y q]; cbn [names_eqb]; try (split; congruence).
  destruct (str_compare_spec x y) as [-> | Hl | Hl].
  - rewrite IH; split; [ intros ->; reflexivity | intros E; injection E as ->; reflexivity ].
  - split; [ discriminate | intros E; injection E as -> _; elim (StrictOrder_Irreflexive _ Hl) ].
  - split; [ discriminate | intros E; injection E as -> _; elim (StrictOrder_Irreflexive _ Hl) ].
Qed.

(** Equality of qualified names: the chains first, which differ more
    often, then the units *)
Definition qname_eqb (x y : qname) : bool := names_eqb (q_chain x) (q_chain y) && names_eqb (q_unit x) (q_unit y).

Lemma qname_eqb_eq : forall x y, qname_eqb x y = true <-> x = y.
Proof.
  intros [ux cx] [uy cy]; unfold qname_eqb; cbn [q_chain q_unit]; rewrite Bool.andb_true_iff, (names_eqb_eq cx cy), (names_eqb_eq ux uy).
  split; [ intros [-> ->]; reflexivity | intros E; injection E as -> ->; split; reflexivity ].
Qed.

(** Equality of qualified names decided by [qname_eqb] *)
Definition qname_dec (x y : qname) : {x = y} + {x <> y} :=
  match qname_eqb x y as b return qname_eqb x y = b -> {x = y} + {x <> y} with
  | true => fun E => left (proj1 (qname_eqb_eq x y) E)
  | false => fun E => right (fun Exy => Bool.diff_false_true (eq_trans (eq_sym E) (proj2 (qname_eqb_eq x y) Exy)))
  end eq_refl.

(** ** The Declarations Kept *)

Section Cache.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** A declaration looked up already: the eliminator keeps the one of the
      constructor it takes apart for the recursive results, whose arguments
      are of the same type, and compares names instead of looking up
      again. *)
  Definition lk_cache : Set := option {x : qname * ind_decl | ind_lookup Θ Ξ (fst x) = Some (snd x)}.
End Cache.

(** ** The Fast Context

    What the implementations run on: the units the command's unit sees
    ([fc_view]), the open frames ([fc_frames]), and a declaration looked up
    already ([fc_seed_found], at the decoding of the view and the frames;
    [Extraction.Lookup.fc_seed] is the same, read at [fc_deps] and
    [fc_stack]).  The Core context it stands for, [fc_deps] and
    [fc_stack], is its decoding: it appears in types and proofs only, never
    at run time.  [fc_ok], a [Prop], says that the fast data is the
    translation of some Core context, which is what makes every fast lookup
    agree with the Core lookup of the decoding ([fc_entry_ok] and the
    like). *)

(** The fast data translates some canonical Core context. *)
#[warnings="-cannot-define-projection"]
Record fctx_ok (v : fview) (fs : fstack) : Prop := mk_fctx_ok
  { (** the filed units it translates *)
    fo_deps : gdeps
    (** the open frames it translates *)
  ; fo_stack : gstack
    (** the filed units are canonical *)
  ; fo_canon_deps : canon_deps fo_deps
    (** the frames are canonical *)
  ; fo_canon_stack : canon_stack fo_stack
    (** the units are those of [fo_deps] *)
  ; fo_units : units_rep (fv_units v) fo_deps
    (** the units seen are those filed at the imported paths *)
  ; fo_vis : vis_rep (fv_units v) (fv_dom v)
    (** the frames are those of [fo_stack] *)
  ; fo_frames : fs = fs_of fo_stack }.

(** A fast context: the units seen, the open frames, the proof that they
    translate a canonical Core context, and a declaration looked up
    already *)
Record FCtx : Type := mk_fctx
  { (** the units the unit being run sees *)
    fc_view : fview
    (** the open frames *)
  ; fc_frames : fstack
    (** they translate a Core context *)
  ; fc_ok : fctx_ok fc_view fc_frames
    (** a declaration the evaluator and readback start from, as if they
        had looked it up already *)
  ; fc_seed_found : lk_cache (view_deps fc_view) (dec_stack fc_frames) }.
