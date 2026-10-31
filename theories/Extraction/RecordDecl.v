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

(** ** The Declaration *)

(** A record declaration checked as [wf_gentry_record] asks, declared over
    the frames' parameters [Γt] with its own parameters [Δ], its sort [S],
    its fields [fs] and their sorts [rs].  The sorts are those the fields'
    types infer ([record_field_type_relevance]), so they are fixed by the
    rest ([record_checked_dec]). *)
Record record_checked (Θ : gdeps) (Ξ : gstack) (Γt Δ : ctx) (S : typ) (fs : list (string * typ)) (rs : list relevance) : Prop :=
  mk_record_checked
  { (** The declaration is typed *)
    checked_typed : record_typed Θ Ξ (mk_record_decl (Δ ++ Γt) S fs rs)
    (** The record's own parameters are types of a universe, at one level *)
  ; checked_param_level : exists l, params_relevant Θ Ξ Γt Δ l }.

Section RecordDecide.
  (** The fast context the decisions look names up in; the judgments are
      at the Core context it stands for. *)
  Variable F : FCtx.
  #[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.

  (** "Is [U] a universe in [Γ]?": a large universe in a well-formed
      context, or a small one at a level. *)
  Definition is_univ_dec (Γ : ctx) (U : typ) : {Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U} + {~ Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U}.
  Proof.
    destruct (check_ctx F HΞ Γ) as [HΓ | HnΓ]; [| right; intros H; exact (HnΓ (presup_is_univ_ctx H)) ].
    destruct U; try solve [ right; intros H; inversion H ].
    - left; constructor; exact HΓ.
    - match goal with |- context [a_univ ?L] =>
        destruct (check_level F Γ HΓ L) as [[n Hn] | Hn];
          [ left; econstructor; exact Hn | right; intros H; inversion H; subst; eapply Hn; eassumption ]
      end.
  Defined.

  (** Each field of [R] a type of its sort over the fields before it, the
      first one that is not found. *)
  Definition record_fields_search (R : record_decl) :
    ((forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
       Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R ⊢ T : relevance_sort (record_field_rel R k) (record_sort R)[wk_shiftn k]ʷ)
    + {k : nat & {fT : string * typ | List.nth_error (record_fields R) k = Some fT /\
         ~ Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R
             ⊢ snd fT : relevance_sort (record_field_rel R k) (record_sort R)[wk_shiftn k]ʷ}})%type.
  Proof.
    destruct (forall_nth_search
                (fun k (fT : (string * typ)%type) => Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R
                   ⊢ snd fT : relevance_sort (record_field_rel R k) (record_sort R)[wk_shiftn k]ʷ)
                (fun k fT => check_exp_at F HΞ (record_fctx R k ++ record_params R)
                               (relevance_sort (record_field_rel R k) (record_sort R)[wk_shiftn k]ʷ) (snd fT))
                (record_fields R)) as [H | H].
    - left; intros k f T Hk; exact (H _ _ Hk).
    - right; exact H.
  Defined.

  (** The relevance of the sort a type infers in a context ([type_relevance]),
      or none in a well-formed context. *)
  Definition field_relevance_dec (Γ : ctx) (T : typ) :
    { r | type_relevance Θ Ξ Γ T r } + { ⊢ Θ ⍮ Ξ ⍮ Γ -> forall r, ~ type_relevance Θ Ξ Γ T r }.
  Proof.
    destruct (check_ctx F HΞ Γ) as [HΓ | HnΓ]; [| right; intros HΓ; contradiction ].
    destruct (type_infer F Γ HΓ T ltac:(apply user_exp_to_type_infer_order, user_exp_all)) as [[U (HU & _)] | HnU];
      [| right; intros _ r (U' & u' & HU' & _); rewrite <- (fc_gctx_eta F) in HU'; exact (HnU _ HU') ].
    rewrite (fc_gctx_eta F) in HU.
    destruct (sort_nf_dec U) as [(r & u & Hs) | Hns]; [ left; exists r, U, u; split; assumption |].
    right; intros _ r (U' & u' & HU' & Hs').
    pose proof (@functional_alg_type_infer (gc_mk Θ Ξ) _ _ _ _ HΞ HU HU') as <-; exact (Hns _ _ Hs').
  Defined.

  (** "Is [A] a type of either sort?", with the relevance of its sort
      ([type_relevance]), as [run_cmd_def] asks: the sort its type infers,
      at which it is typed ([sort_typed_of_is_sort_nf]); none for no type,
      since a type checks against its sort and so infers one
      ([alg_type_check_sort_infer]). *)
  Definition check_type_relevance (Γ : ctx) (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) (A : typ) :
    { r & { i : nat | Θ ⍮ Ξ ⍮ Γ ⊢ A : relevance_sort r Typeω@i /\ type_relevance Θ Ξ Γ A r } } +
    { ~ Θ ⍮ Ξ ⍮ Γ ⊢ᵗ A }.
  Proof.
    (** a type checks against its sort, so infers one *)
    assert (Hinf : Θ ⍮ Ξ ⍮ Γ ⊢ᵗ A -> exists UA r u, @alg_type_infer (gc_mk Θ Ξ) Γ UA A /\ is_sort_nf UA r u).
    { intros [S HS HA].
      exact (@alg_type_check_sort_infer (gc_mk Θ Ξ) _ _ _ HΓ HS
               (@alg_type_check_complete (gc_mk Θ Ξ) _ _ _ (user_exp_all A) HA)). }
    destruct (type_infer F Γ HΓ A ltac:(apply user_exp_to_type_infer_order, user_exp_all)) as [[U (HU & _)] | HnU];
      [| right; intros HA; destruct (Hinf HA) as (UA & r & u & HUA & _);
         rewrite <- (fc_gctx_eta F) in HUA; exact (HnU _ HUA) ].
    rewrite (fc_gctx_eta F) in HU.
    destruct (sort_nf_dec U) as [(r & u & Hs) | Hns].
    - left; exists r, (universe_nf_large_index u); split; [| exists U, u; split; assumption ].
      exact (@sort_typed_of_is_sort_nf (gc_mk Θ Ξ) _ _ _ _ _ (@alg_type_infer_sound (gc_mk Θ Ξ) _ _ _ HU HΓ) Hs).
    - right; intros HA; destruct (Hinf HA) as (UA & r & u & HUA & Hs).
      pose proof (@functional_alg_type_infer (gc_mk Θ Ξ) _ _ _ _ HΞ HU HUA) as <-; exact (Hns _ _ Hs).
  Defined.

  (** The sorts of the fields [fs] of a record declared over [Γt] with the
      parameters [Δ] and the sort [S], each the relevance its type infers
      over the fields before it and the parameters; or the first field whose
      type infers none. *)
  Definition fields_relevance_search (Γt Δ : ctx) (S : typ) (fs : list (string * typ)) :
    ({ rs | List.length rs = List.length fs /\
            forall k f T, List.nth_error fs k = Some (f, T) ->
              type_relevance Θ Ξ (record_fctx (mk_record_decl (Δ ++ Γt) S fs nil) k ++ Δ ++ Γt) T (List.nth k rs relevant) }
     + { f : string & { k : nat & { T : typ | List.nth_error fs k = Some (f, T) /\
            (⊢ Θ ⍮ Ξ ⍮ record_fctx (mk_record_decl (Δ ++ Γt) S fs nil) k ++ Δ ++ Γt ->
             forall r, ~ type_relevance Θ Ξ (record_fctx (mk_record_decl (Δ ++ Γt) S fs nil) k ++ Δ ++ Γt) T r) } } })%type.
  Proof.
    pose (Γk := fun k => record_fctx (mk_record_decl (Δ ++ Γt) S fs nil) k ++ Δ ++ Γt).
    assert (go : forall n, n <= List.length fs ->
              ({ rs | List.length rs = n /\ forall k f T, k < n -> List.nth_error fs k = Some (f, T) ->
                        type_relevance Θ Ξ (Γk k) T (List.nth k rs relevant) }
               + { f : string & { k : nat & { T : typ | List.nth_error fs k = Some (f, T) /\
                     (⊢ Θ ⍮ Ξ ⍮ Γk k -> forall r, ~ type_relevance Θ Ξ (Γk k) T r) } } })%type).
    { induction n as [| n IH]; intros Hn.
      - left; exists nil; split; [ reflexivity | intros; lia ].
      - destruct (IH ltac:(lia)) as [[rs [Hl Hrs]] | e]; [| right; exact e ].
        destruct (List.nth_error fs n) as [[f T] |] eqn:Hf;
          [| exfalso; apply List.nth_error_None in Hf; lia ].
        destruct (field_relevance_dec (Γk n) T) as [[r Hr] | Hnr];
          [| right; exists f, n, T; split; [ exact Hf | exact Hnr ] ].
        left; exists (rs ++ r :: nil); split; [ rewrite List.length_app; cbn; lia |].
        intros k f' T' Hk Hk'.
        destruct (Nat.eq_dec k n) as [-> | Hne].
        + rewrite Hf in Hk'; injection Hk' as <- <-.
          rewrite List.app_nth2 by lia; rewrite Hl, Nat.sub_diag; exact Hr.
        + rewrite List.app_nth1 by lia; refine (Hrs _ _ _ _ Hk'); lia. }
    destruct (go (List.length fs) (le_n _)) as [[rs [Hl Hrs]] | e]; [| right; exact e ].
    left; exists rs; split; [ exact Hl |].
    intros k f T Hk; refine (Hrs _ _ _ _ Hk); apply List.nth_error_Some; congruence.
  Defined.

  (** Why a record declaration is not typed: the first premise of
      [record_checked] that fails. *)
  Inductive record_why : Set :=
  (** A parameter is no assumption *)
  | rw_params
  (** A type of the declaration has a free module variable *)
  | rw_mvc
  (** The sort is no universe over the parameters *)
  | rw_sort
  (** Two fields have the name *)
  | rw_dup
  (** The type of the field infers no sort: it is no type *)
  | rw_field_sort (f : string)
  (** The field is no type of the sort, nor a proposition *)
  | rw_field (f : string)
  (** A parameter of the record is no type of a universe (a proposition,
      say) *)
  | rw_param_level.

  (** A record declaration typed, or why it is not. *)
  Definition record_typed_dec (R : record_decl) : (record_typed Θ Ξ R + {e : record_why | ~ record_typed Θ Ξ R})%type.
  Proof.
    destruct (tele_ass_dec (record_params R)) as [Ha | Hn]; [| right; exists rw_params; intros [H _ _ _ _ _]; exact (Hn H) ].
    destruct (record_mvc_dec R) as [Hm | Hn]; [| right; exists rw_mvc; intros [_ H _ _ _ _]; exact (Hn H) ].
    destruct (is_univ_dec (record_params R) (record_sort R)) as [Hs | Hn];
      [| right; exists rw_sort; intros [_ _ H _ _ _]; exact (Hn H) ].
    destruct (nodup_dec (List.map fst (record_fields R))) as [Hd | Hn]; [| right; exists rw_dup; intros [_ _ _ H _ _]; exact (Hn H) ].
    destruct (record_fields_search R) as [Hf | (k & [f T] & Hk & Hn)];
      [| right; exists (rw_field f); intros [_ _ _ _ H _]; exact (Hn (H _ _ _ Hk)) ].
    destruct (Nat.eq_dec (List.length (record_field_relevance R)) (List.length (record_fields R))) as [Hl | Hn];
      [| right; exists rw_sort; intros [_ _ _ _ _ H]; exact (Hn H) ].
    left; constructor; assumption.
  Defined.

  (** A record declaration over [Γt] checked, at the sorts of its fields
      that the fields' types infer, or why it is not, at any sorts.  For
      example, [record P : Prop ≔ { a : ℕ, h : a = a }] is checked at the
      sorts [relevant, propositional]: [ℕ] infers a universe, [a = a]
      infers [Prop]. *)
  Definition record_checked_dec (Γt Δ : ctx) (S : typ) (fs : list (string * typ)) :
    ({ rs | record_checked Θ Ξ Γt Δ S fs rs } + { e : record_why | forall rs, ~ record_checked Θ Ξ Γt Δ S fs rs })%type.
  Proof.
    destruct (fields_relevance_search Γt Δ S fs) as [[rs [Hl Hrs]] | (f & k & T & Hk & Hnr)].
    2:{ right; exists (rw_field_sort f); intros rs [Ht _].
        assert (Hle : k <= List.length fs) by (apply Nat.lt_le_incl, List.nth_error_Some; congruence).
        exact (Hnr (record_typed_fctx_wf _ _ _ Ht k Hle) _ (record_field_type_relevance _ _ _ _ _ _ Ht Hk)). }
    destruct (record_typed_dec (mk_record_decl (Δ ++ Γt) S fs rs)) as [Ht | [e Hn]].
    2:{ right; exists e; intros rs' [Ht' _]; apply Hn.
        pose proof (typed_relevance_length _ _ _ Ht') as Hl'; cbn in Hl'.
        assert (rs' = rs) as <-; [| exact Ht' ].
        apply (List.nth_ext _ _ relevant relevant); [ congruence |].
        intros k Hk.
        destruct (List.nth_error fs k) as [[f T] |] eqn:Hf; [| apply List.nth_error_None in Hf; lia ].
        exact (type_relevance_functional _ _ _ _ _ _ HΞ (record_field_type_relevance _ _ _ _ _ _ Ht' Hf) (Hrs _ _ _ Hf)). }
    destruct (params_level_dec F HΞ Γt Δ) as [[l Hlv] | Hnl].
    - left; exists rs; constructor; [ exact Ht | exists l; exact Hlv ].
    - right; exists rw_param_level; intros rs' [_ [l Hl']]; exact (Hnl l Hl').
  Defined.
End RecordDecide.

(** A record checked with an empty module, from its checked declaration. *)
Lemma record_entry_of_checked : forall Θ Ξ mp pv Δ Srt fs rs,
    record_checked Θ Ξ (gs_tele Ξ) Δ Srt fs rs -> Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_record pv mp (record_at Ξ Δ Srt fs rs) ⋄.
Proof.
  intros * [[Ha Hm Hs Hd Hf Hl] [lP HP]];
    econstructor; [ reflexivity | exact Ha | exact Hm | exact Hs | exact Hd | exact Hf | exact Hl | exact HP ].
Qed.

(** A record checked with an empty module has its declaration checked. *)
Lemma record_checked_of_entry : forall Θ Ξ mp pv Δ Srt fs rs,
    Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_record pv mp (record_at Ξ Δ Srt fs rs) ⋄ -> record_checked Θ Ξ (gs_tele Ξ) Δ Srt fs rs.
Proof.
  intros * HE; constructor;
    [ exact (proj1 wf_record_typed_all _ _ _ _ HE _ _ _ _ eq_refl) | exact (record_nil_entry_params_relevant _ _ _ _ _ _ _ _ _ HE) ].
Qed.

(** A checked declaration stays checked along an embedding. *)
Lemma gctx_embedding_preserves_record_checked : forall Θ Ξ Θ2 Ξ2 Γt Δ S fs rs,
    gctx_embedding Θ Ξ Θ2 Ξ2 -> record_checked Θ Ξ Γt Δ S fs rs -> record_checked Θ2 Ξ2 Γt Δ S fs rs.
Proof.
  intros * He [Ht [l Hl]]; constructor; [ exact (gctx_embedding_preserves_record_typed _ _ _ _ _ He Ht) |].
  destruct (gctx_embedding_preserves_wf _ _ _ _ He) as (_ & Hte & _).
  exists l; intros Δ1 T Δ2 E; exact (Hte _ _ _ (Hl _ _ _ E)).
Qed.

(** A declaration is checked at one list of field sorts only: each sort
    is the one its field's type infers. *)
Lemma record_checked_relevance_functional : forall Θ Ξ Γt Δ S fs rs rs', ⊢ᵍ Θ ⍮ Ξ ->
    record_checked Θ Ξ Γt Δ S fs rs -> record_checked Θ Ξ Γt Δ S fs rs' -> rs = rs'.
Proof.
  intros * HΞ [Ht _] [Ht' _].
  pose proof (typed_relevance_length _ _ _ Ht) as Hl; pose proof (typed_relevance_length _ _ _ Ht') as Hl'; cbn in Hl, Hl'.
  apply (List.nth_ext _ _ relevant relevant); [ congruence |].
  intros k Hk.
  destruct (List.nth_error fs k) as [[f T] |] eqn:Hf; [| apply List.nth_error_None in Hf; lia ].
  exact (type_relevance_functional _ _ _ _ _ _ HΞ (record_field_type_relevance _ _ _ _ _ _ Ht Hf)
           (record_field_type_relevance _ _ _ _ _ _ Ht' Hf)).
Qed.
