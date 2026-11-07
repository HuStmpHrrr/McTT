(** * Deciding a Record Declaration

    What [wf_gentry_record] asks of a record declaration, decided premise
    by premise: its parameters are assumptions, no type of it has a free
    module variable, its sort is a universe over the parameters, its field
    names are distinct, each field is a type of the sort its kind says
    over the fields before it, each field's kind is one a field may have,
    and the parameters are types of a universe or of levels.  A failing
    premise is reported, the first failing field by name. *)

From Stdlib Require Import Arith List ListDec String PeanoNat Bool Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Core.Syntactic.System.Records Require Import RecordRuns.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Extraction Require Import Lookup LookupTwins TypeCheckBase TypeCheck GlobalCheck IndDecl.
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

(** Whether every kind of a list is one a field may have
    ([field_kind]). *)
Definition field_kinds_dec (rs : list abs_kind) : {forall k, field_kind (List.nth k rs ak_relevant)} + {~ forall k, field_kind (List.nth k rs ak_relevant)}.
Proof.
  induction rs as [| r rs IH].
  - left; intros [| k]; constructor.
  - destruct r; [ | | right; intros H; specialize (H 0); inversion H ].
    all: destruct IH as [IH | IH]; [ left; intros [| k]; [ constructor | apply IH ] | right; intros H; apply IH; intros k; exact (H (S k)) ].
Defined.

(** ** The Declaration *)

(** Why a record declaration is not checked: the first premise of
    [wf_gentry_record] that fails. *)
Inductive record_why : Set :=
(** A parameter is no assumption *)
| rw_params
(** A type of the declaration has a free module variable *)
| rw_mvc
(** The sort is no universe over the parameters *)
| rw_sort
(** Two fields have the name *)
| rw_dup
(** A field of a kind no field may have: a type of levels *)
| rw_field_kind
(** The field is no type of the sort its kind says *)
| rw_field (f : string)
(** A parameter of the record is no type of a universe or of levels (a
    proposition, say) *)
| rw_param_level.

Section RecordDecide.
  (** The fast context the decisions look names up in; the judgments are
      at the Core context it stands for. *)
  Variable F : FCtx.
  #[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  (** The decision of [levels_abstractable] the checker is given *)
  Variable levels_abstractable_dec : forall G Δ E, ⊢ Θ ⍮ Ξ ⍮ Δ ++ G -> Θ ⍮ Ξ ⍮ Δ ++ G ⊢ᵐ E ≈ E ->
      { levels_abstractable Θ Ξ G Δ E } + { ~ levels_abstractable Θ Ξ G Δ E }.
  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.

  (** "Is [U] a universe in [Γ]?": a large universe in a well-formed
      context, or a small one at a level. *)
  Definition is_univ_dec (Γ : ctx) (U : typ) : {Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U} + {~ Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U}.
  Proof.
    destruct (check_ctx F levels_abstractable_dec HΞ Γ) as [HΓ | HnΓ]; [| right; intros H; exact (HnΓ (presup_is_univ_ctx H)) ].
    destruct U; try solve [ right; intros H; inversion H ].
    - left; constructor; exact HΓ.
    - match goal with |- context [a_univ ?L] =>
        destruct (check_level F levels_abstractable_dec Γ HΓ L) as [[n Hn] | Hn];
          [ left; econstructor; exact Hn | right; intros H; inversion H; subst; eapply Hn; eassumption ]
      end.
  Defined.

  (** Each field of [R] a type of the sort of its kind over the fields
      before it, the first one that is not found. *)
  Definition record_fields_search (R : record_decl) :
    ((forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
       Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R ⊢ T : abs_kind_sort (record_field_kind R k) (record_sort R)[wk_shiftn k]ʷ)
    + {k : nat & {fT : string * typ | List.nth_error (record_fields R) k = Some fT /\
         ~ Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R
             ⊢ snd fT : abs_kind_sort (record_field_kind R k) (record_sort R)[wk_shiftn k]ʷ}})%type.
  Proof.
    destruct (forall_nth_search
                (fun k (fT : (string * typ)%type) => Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R
                   ⊢ snd fT : abs_kind_sort (record_field_kind R k) (record_sort R)[wk_shiftn k]ʷ)
                (fun k fT => check_exp_at F levels_abstractable_dec HΞ (record_fctx R k ++ record_params R)
                               (abs_kind_sort (record_field_kind R k) (record_sort R)[wk_shiftn k]ʷ) (snd fT))
                (record_fields R)) as [H | H].
    - left; intros k f T Hk; exact (H _ _ Hk).
    - right; exact H.
  Defined.

  (** A record declaration over the frames' parameters, with its own
      parameters [Δ], sort [S] and kinded fields [fs], checked with an
      empty module, or why it is not. *)
  Definition record_entry_dec (mp : qname) (pv : bool) (Δ : ctx) (S : typ) (fs : list (string * abs_kind * typ)) :
    ((Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_record pv mp (record_at Ξ Δ S fs) ⋄)
     + {e : record_why | ~ Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_record pv mp (record_at Ξ Δ S fs) ⋄})%type.
  Proof.
    assert (HP : record_params (record_at Ξ Δ S fs) = Δ ++ gs_tele Ξ) by reflexivity.
    assert (Hl : List.length (record_field_kinds (record_at Ξ Δ S fs)) = List.length (record_fields (record_at Ξ Δ S fs)))
      by (cbn; rewrite !List.length_map; reflexivity).
    (** The parameters, first: their sorts are read off [Δ] *)
    destruct (params_sorts_dec F levels_abstractable_dec HΞ (gs_tele Ξ) Δ) as [[[lP bs] [_ HPs]] | HnP];
      [| right; exists rw_param_level; intros H;
         destruct (record_nil_entry_params_evaluated _ _ _ _ _ _ _ _ H) as [l Hl']; exact (HnP _ Hl') ].
    cbn [fst snd] in HPs.
    (** The rest: by the typed declaration the entry gives *)
    assert (Hty : Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_record pv mp (record_at Ξ Δ S fs) ⋄ -> record_typed Θ Ξ (record_at Ξ Δ S fs))
      by (intros H; exact (proj1 wf_record_typed_all _ _ _ _ H _ _ _ _ eq_refl)).
    remember (record_at Ξ Δ S fs) as R eqn:ER; clear ER.
    destruct (all_assumptions_dec (record_params R)) as [Ha | Hn];
      [| right; exists rw_params; intros H; exact (Hn (typed_params_ass _ _ _ (Hty H))) ].
    destruct (record_mvc_dec R) as [Hm | Hn]; [| right; exists rw_mvc; intros H; exact (Hn (typed_mvc _ _ _ (Hty H))) ].
    destruct (is_univ_dec (record_params R) (record_sort R)) as [Hs | Hn];
      [| right; exists rw_sort; intros H; exact (Hn (typed_sort _ _ _ (Hty H))) ].
    destruct (nodup_dec (List.map fst (record_fields R))) as [Hd | Hn];
      [| right; exists rw_dup; intros H; exact (Hn (typed_nodup _ _ _ (Hty H))) ].
    destruct (record_fields_search R) as [Hf | (k & [f T] & Hk & Hn)];
      [| right; exists (rw_field f); intros H; exact (Hn (typed_fields _ _ _ (Hty H) _ _ _ Hk)) ].
    destruct (field_kinds_dec (record_field_kinds R)) as [Hk | Hn];
      [| right; exists rw_field_kind; intros H; apply Hn; exact (typed_field_kinds _ _ _ (Hty H)) ].
    left; eapply wf_gentry_record with (Δ := Δ) (param_level := lP)
                                        (param_sorts := fun k => param_bool_sort lP (List.nth k (List.rev bs) false));
      first [ exact HP | eassumption | intros k; apply param_bool_sort_ok | intros Δ1 κ T Δ2 E; exact (HPs _ _ _ _ E)
            | intros k; apply Hk ].
  Defined.
End RecordDecide.
