(** * Deciding a Record Declaration

    What [wf_gentry_record] asks of a record declaration, as
    [record_typed] collects it, decided premise by premise: its parameters
    are assumptions, no type of it has a free module variable, its sort is
    a universe over the parameters, its field names are distinct, and each
    field is a type of the sort over the fields before it.  A failing
    premise is reported, the first failing field by name. *)

From Stdlib Require Import Arith List ListDec String PeanoNat Bool Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Extraction Require Import Lookup TypeCheckBase GlobalCheck IndDecl.
Import Syntax_Notations GlobalCtx_Notations.

(** ** Module Variables *)

(** A record declaration without free module variables, computed. *)
Definition record_mvcb (R : record_decl) : bool :=
  forallb (centry_mvcb 0) (record_params R) && exp_mvcb 0 (record_sort R) &&
  forallb (fun fT => exp_mvcb 0 (snd fT)) (record_fields R).

Lemma record_mvcb_spec : forall R, record_mvcb R = true <-> record_mvc R.
Proof.
  destruct mvcb_spec as (He & _ & _ & _ & _ & _ & _ & Hc).
  intros R; unfold record_mvcb; rewrite !andb_true_iff.
  rewrite (forallb_Forall _ _ _ (fun e => Hc e 0)), He.
  rewrite (forallb_Forall _ (fun fT => exp_mvc 0 (snd fT))) by (intros; apply He).
  split.
  - intros [[H1 H2] H3]; constructor; [ exact H1 | exact H2 |].
    intros k f T Hk; exact (proj1 (List.Forall_forall _ _) H3 (f, T) (List.nth_error_In _ _ Hk)).
  - intros [H1 H2 H3]; split; [ split; assumption |].
    apply List.Forall_forall; intros [f T] Hin; apply List.In_nth_error in Hin as [k Hk]; exact (H3 k f T Hk).
Qed.

Definition record_mvc_dec (R : record_decl) : {record_mvc R} + {~ record_mvc R} :=
  match record_mvcb R as b return record_mvcb R = b -> _ with
  | true => fun E => left (proj1 (record_mvcb_spec R) E)
  | false => fun E => right (fun H => diff_false_true (eq_trans (eq_sym E) (proj2 (record_mvcb_spec R) H)))
  end eq_refl.

(** ** A Property at Every Position *)

(** A property of each element of a list and its position, the first
    position it fails at found. *)
Definition forall_nth_search {X : Type} (P : nat -> X -> Prop) (f : forall k x, {P k x} + {~ P k x}) :
  forall (l : list X),
    ((forall k x, List.nth_error l k = Some x -> P k x) + {k : nat & {x : X | List.nth_error l k = Some x /\ ~ P k x}})%type.
Proof.
  intros l; revert P f; induction l as [| x l IH]; intros P f.
  - left; intros [] ? [=].
  - destruct (f 0 x) as [Hx | Hx]; [| right; exists 0, x; split; [ reflexivity | exact Hx ] ].
    destruct (IH (fun k => P (S k)) (fun k => f (S k))) as [Hl | (k & y & Hy & Hn)].
    + left; intros [| k] y Hy; cbn in Hy; [ injection Hy as <-; exact Hx | exact (Hl _ _ Hy) ].
    + right; exists (S k), y; split; [ exact Hy | exact Hn ].
Defined.

(** ** The Declaration *)

Section RecordDecide.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.

  (** "Is [U] a universe in [Γ]?": a large universe in a well-formed
      context, or a small one at a level. *)
  Definition is_univ_dec (Γ : ctx) (U : typ) : {Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U} + {~ Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U}.
  Proof.
    destruct (check_ctx fctx_none Θ Ξ HΞ Γ) as [HΓ | HnΓ]; [| right; intros H; exact (HnΓ (presup_is_univ_ctx H)) ].
    destruct U as [i | L | | | | | | | | | | | | | | | | | | | | | |];
      try solve [ right; intros H; inversion H ].
    - left; constructor; exact HΓ.
    - destruct (check_level fctx_none Θ Ξ Γ HΓ L) as [[n Hn] | Hn];
        [ left; econstructor; exact Hn | right; intros H; inversion H; subst; eapply Hn; eassumption ].
  Defined.

  (** Each field of [R] a type of its sort over the fields before it, the
      first one that is not found. *)
  Definition record_fields_search (R : record_decl) :
    ((forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
       Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R ⊢ T : (record_sort R)[wk_shiftn k]ʷ)
    + {k : nat & {fT : string * typ | List.nth_error (record_fields R) k = Some fT /\
         ~ Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R ⊢ snd fT : (record_sort R)[wk_shiftn k]ʷ}})%type.
  Proof.
    destruct (forall_nth_search
                (fun k (fT : (string * typ)%type) => Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R ⊢ snd fT : (record_sort R)[wk_shiftn k]ʷ)
                (fun k fT => check_exp_at Θ Ξ HΞ (record_fctx R k ++ record_params R) ((record_sort R)[wk_shiftn k]ʷ) (snd fT))
                (record_fields R)) as [H | H].
    - left; intros k f T Hk; exact (H _ _ Hk).
    - right; exact H.
  Defined.

  (** Why a record declaration is not typed: the first premise of
      [record_typed] that fails. *)
  Inductive record_why : Set :=
  (** A parameter is no assumption *)
  | rw_params
  (** A type of the declaration has a free module variable *)
  | rw_mvc
  (** The sort is no universe over the parameters *)
  | rw_sort
  (** Two fields have the name *)
  | rw_dup
  (** The field is no type of the sort *)
  | rw_field (f : string).

  (** A record declaration typed, or why it is not. *)
  Definition record_typed_dec (R : record_decl) : (record_typed Θ Ξ R + {e : record_why | ~ record_typed Θ Ξ R})%type.
  Proof.
    destruct (tele_ass_dec (record_params R)) as [Ha | Hn]; [| right; exists rw_params; intros [H _ _ _ _]; exact (Hn H) ].
    destruct (record_mvc_dec R) as [Hm | Hn]; [| right; exists rw_mvc; intros [_ H _ _ _]; exact (Hn H) ].
    destruct (is_univ_dec (record_params R) (record_sort R)) as [Hs | Hn];
      [| right; exists rw_sort; intros [_ _ H _ _]; exact (Hn H) ].
    destruct (nodup_dec (List.map fst (record_fields R))) as [Hd | Hn]; [| right; exists rw_dup; intros [_ _ _ H _]; exact (Hn H) ].
    destruct (record_fields_search R) as [Hf | (k & [f T] & Hk & Hn)];
      [| right; exists (rw_field f); intros [_ _ _ _ H]; exact (Hn (H _ _ _ Hk)) ].
    left; constructor; assumption.
  Defined.
End RecordDecide.

(** A record checked with an empty module, from its typed declaration. *)
Lemma record_entry_of_typed : forall Θ Ξ mp pv Δ Srt fs,
    record_typed Θ Ξ (record_at Ξ Δ Srt fs) -> Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_record pv mp (record_at Ξ Δ Srt fs) ⋄.
Proof. intros * [Ha Hm Hs Hd Hf]; econstructor; [ reflexivity | exact Ha | exact Hm | exact Hs | exact Hd | exact Hf ]. Qed.
