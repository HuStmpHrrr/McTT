(** * Records

    A record type is declared by a [record_decl] and filed by [ge_record]
    at its path, which names it ([record_lookup]).  Its type former
    [a_record p] is of the [Π] over the parameters of the sort
    ([record_ty]).  Field [k]'s type is over the fields before it,
    innermost first, then the parameters ([record_fctx]); at parameters
    [Ns] and earlier field values [Ms], both outermost first, it is
    [T[sb_of_list Id (Ns ++ Ms)]].  A field is selected by name: the first
    one so named ([field_lookup]); the names of a well-formed record are
    distinct. *)

From Stdlib Require Import Lia List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Members.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** The type of a record's type former: the [Π] over its parameters of its
    sort. *)
Definition record_ty (R : record_decl) : typ := ctx_pi (record_params R) (record_sort R).

(** The context of the first [k] fields, innermost first. *)
Definition record_fctx (R : record_decl) (k : nat) : ctx :=
  List.rev (List.map (fun fT => ce_ass (snd fT)) (List.firstn k (record_fields R))).

(** The projections of [M] at the first [k] fields, outermost first: the
    values of the fields before field [k], at which its type is read. *)
Definition record_pre (R : record_decl) (k : nat) (M : exp) : list exp :=
  List.map (fun fT => a_proj (fst fT) M) (List.firstn k (record_fields R)).

(** The fields of the η-expansion of [M]: each field's projection of [M]. *)
Definition record_eta_fields (R : record_decl) (M : exp) : list (string * exp) :=
  List.map (fun fT => (fst fT, a_proj (fst fT) M)) (record_fields R).

(** The value of the first field named [f] among [fs]: projection by name,
    on terms and on values alike. *)
Fixpoint field_lookup {A : Type} (fs : list (string * A)) (f : string) : option A :=
  match fs with
  | nil => None
  | (g, v) :: fs' => if String.eqb f g then Some v else field_lookup fs' f
  end.

(** The position of the first field named [f] among [fs]. *)
Fixpoint field_index {A : Type} (fs : list (string * A)) (f : string) : option nat :=
  match fs with
  | nil => None
  | (g, _) :: fs' => if String.eqb f g then Some 0 else option_map S (field_index fs' f)
  end.

(** ** Lemmas *)

Lemma length_record_fctx : forall R k, k <= List.length (record_fields R) -> List.length (record_fctx R k) = k.
Proof.
  intros; unfold record_fctx; rewrite List.length_rev, List.length_map, List.length_firstn; lia.
Qed.

(** The first [k+1] elements: the first [k], then the [k]-th. *)
Lemma firstn_succ_nth : forall {A : Type} (l : list A) k x,
    List.nth_error l k = Some x -> List.firstn (S k) l = List.firstn k l ++ x :: nil.
Proof.
  induction l as [| y l IH]; intros [| k] x H; cbn in H; try discriminate;
    [ injection H as ->; reflexivity | ].
  change (y :: List.firstn (S k) l = (y :: List.firstn k l) ++ x :: nil); rewrite (IH _ _ H); reflexivity.
Qed.

(** The context of the first [k+1] fields: field [k]'s type on top of the
    first [k]. *)
Lemma record_fctx_succ : forall R k f T, List.nth_error (record_fields R) k = Some (f, T) ->
    record_fctx R (S k) = ce_ass T :: record_fctx R k.
Proof.
  intros R k f T Hk; unfold record_fctx.
  rewrite (firstn_succ_nth _ _ _ Hk), List.map_app, List.rev_app_distr; reflexivity.
Qed.

Lemma length_record_pre : forall R k M, k <= List.length (record_fields R) -> List.length (record_pre R k M) = k.
Proof. intros; unfold record_pre; rewrite List.length_map, List.length_firstn; lia. Qed.

(** The first field so named is one of the fields. *)
Lemma field_lookup_In : forall {A : Type} (fs : list (string * A)) f v,
    field_lookup fs f = Some v -> List.In (f, v) fs.
Proof.
  induction fs as [| [g w] fs IH]; intros * H; cbn in H; [ discriminate |].
  destruct (String.eqb_spec f g) as [-> | _]; [ injection H as <-; left; reflexivity | right; eauto ].
Qed.

(** With distinct names, the field at position [k] is the first one so
    named. *)
Lemma field_lookup_nth : forall {A : Type} (fs : list (string * A)) k f v,
    List.NoDup (List.map fst fs) -> List.nth_error fs k = Some (f, v) -> field_lookup fs f = Some v.
Proof.
  induction fs as [| [g w] fs IH]; intros [| k] * Hnd Hk; cbn in Hk |- *; try discriminate.
  - injection Hk as <- <-; rewrite String.eqb_refl; reflexivity.
  - inversion Hnd as [| ? ? Hg Hnd']; subst.
    destruct (String.eqb_spec f g) as [-> | _]; [| eauto ].
    exfalso; apply Hg; apply (List.in_map fst _ (g, v)), (List.nth_error_In _ _ Hk).
Qed.

(** Mapping the values of named terms keeps the first one so named. *)
Lemma field_lookup_map : forall {A B : Type} (g : A -> B) (fs : list (string * A)) f,
    field_lookup (List.map (fun p => (fst p, g (snd p))) fs) f = option_map g (field_lookup fs f).
Proof.
  intros A B g; induction fs as [| [h w] fs IH]; intros; cbn; [ reflexivity |].
  destruct (String.eqb f h); [ reflexivity | apply IH ].
Qed.

(** The names and values of a list of named terms, combined back. *)
Lemma combine_names_values : forall {A : Type} (fs : list (string * A)),
    List.combine (List.map fst fs) (List.map snd fs) = fs.
Proof. induction fs as [| [f v] fs IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(** Two lists of named entries with the same names have their entries at
    the same positions. *)
Lemma map_fst_nth : forall {A B : Type} (l1 : list (string * A)) (l2 : list (string * B)) k f a,
    List.map fst l1 = List.map fst l2 -> List.nth_error l1 k = Some (f, a) -> exists b, List.nth_error l2 k = Some (f, b).
Proof.
  intros * Heq Hk.
  assert (Hm : List.nth_error (List.map fst l2) k = Some f) by (rewrite <- Heq, List.nth_error_map, Hk; reflexivity).
  rewrite List.nth_error_map in Hm; destruct (List.nth_error l2 k) as [[g b] |]; cbn in Hm; [| discriminate ].
  injection Hm as ->; eauto.
Qed.

(** A property of every entry of a list of named entries, by position. *)
Lemma all_list_snd_of_nth : forall {A : Set} (P : A -> Prop) (fs : list (string * A)),
    (forall k f a, List.nth_error fs k = Some (f, a) -> P a) -> all_list (fun f => P (snd f)) fs.
Proof.
  intros A P; induction fs as [| [f a] fs IH]; intros H; cbn; [ exact I |].
  split; [ exact (H 0 _ _ eq_refl) | apply IH; intros k g b Hk; exact (H (S k) _ _ Hk) ].
Qed.