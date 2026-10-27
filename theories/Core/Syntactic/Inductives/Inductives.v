(** * Inductive Types: Reading a Group's Declaration

    A group's declaration ([ind_decl], in [Syntax]) is filed in the entry
    of each of its declared members ([ge_ind]), with the body of the
    member's module: its constructors (and the recursor).  The type former
    [a_ind pq k] and the constructors [a_con pq k c] name the member [k] of
    the group [pq], the path of the entry of its first member
    ([ind_lookup]); these are the counts and the types that typing,
    evaluation and readback read off it. *)

From Stdlib Require Import Lia List String PeanoNat.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Members.
From Mctt.Core.Syntactic.Inductives Require Export Group.
Import Syntax_Notations.
#[local] Open Scope list_scope.


(** The arguments of the constructor [c] of the member [M]. *)
Definition ind_con (M : imember) (c : string) : option (list carg) := cons_lookup (im_cons M) c.

(** The branch of the constructor [c]: the number of variables it binds,
    and its body. *)
Fixpoint brs_lookup (Bs : list (string * nat * exp)) (c : string) : option (nat * exp) :=
  match Bs with
  | nil => None
  | (c', n, B) :: Bs' => if String.eqb c c' then Some (n, B) else brs_lookup Bs' c
  end.

(** ** Leaf Paths

    A recursive argument has one recursive result per leaf path of its
    shape: the way from the argument to one of the elements of the group
    it holds, through the domains of its function shape and, at an end in
    a record view, through the projections of the view's recursive fields,
    on into their shapes.  A record view has no eliminator, so a path never
    ends in one: it goes through its fields instead.

    The components of a path (domains, parameters) are over the binders
    passed on the way to them: a domain adds one, a projection the
    projections of the non-recursive fields before the field, and then the
    context of the argument's shape. *)
Inductive leaf_path : Set :=
(** The end: the member [j] at the non-uniform parameters [Ps]. *)
| leaf_self : nat -> list exp -> leaf_path
(** Apply to an element of the domain [B], then the rest, under one more
    binder. *)
| leaf_pi : exp -> leaf_path -> leaf_path
(** [leaf_proj f ns l]: project the field [f] of a record view, then the
    rest, whose components are over the projections of the non-recursive
    fields [ns] before [f], in order. *)
| leaf_proj : string -> list string -> leaf_path -> leaf_path.

(** The member a leaf path ends in. *)
Fixpoint leaf_mem (l : leaf_path) : nat :=
  match l with
  | leaf_self j _ => j
  | leaf_pi _ l => leaf_mem l
  | leaf_proj _ _ l => leaf_mem l
  end.

(** The non-uniform parameters at which a leaf path ends. *)
Fixpoint leaf_ps (l : leaf_path) : list exp :=
  match l with
  | leaf_self _ Ps => Ps
  | leaf_pi _ l => leaf_ps l
  | leaf_proj _ _ l => leaf_ps l
  end.

(** A leaf path whose components are moved by [φ], under the binders the
    path passes. *)
Fixpoint leaf_wk (φ : wk) (l : leaf_path) : leaf_path :=
  match l with
  | leaf_self j Ps => leaf_self j (List.map (fun P => exp_wk P φ) Ps)
  | leaf_pi B l => leaf_pi (exp_wk B φ) (leaf_wk (wk_q φ) l)
  | leaf_proj f ns l => leaf_proj f ns (leaf_wk (wk_qn (List.length ns) φ) l)
  end.

Section Leaves.
  (** The leaf paths of the record views met so far, by member: [Some ls]
      at a record view, its paths over the group's uniform parameters,
      [None] at any other member. *)
  Variable (tbl : nat -> option (list leaf_path)).

  (** The leaf paths of a shape whose components are over [m] binders
      above the uniform parameters: through each domain, and at the end
      the member's own end, or, at a record view, the view's paths moved
      past the [m] binders. *)
  Fixpoint shape_leaves (m : nat) (t : ptyp) : list leaf_path :=
    match t with
    | pt_pi B t' => List.map (leaf_pi B) (shape_leaves (S m) t')
    | pt_self j Ps =>
        match tbl j with
        | Some ls => List.map (leaf_wk (wk_shiftn m)) ls
        | None => leaf_self j Ps :: nil
        end
    end.

  (** The leaf paths of the fields [fs] of a record view, after the
      non-recursive fields [ns]: none at a non-recursive field, which joins
      [ns]; those of a recursive field's shape, each through the field's
      projection. *)
  Fixpoint fields_leaves (ns : list string) (fs : list (string * carg)) : list leaf_path :=
    match fs with
    | nil => nil
    | (f, ca_arg _) :: fs' => fields_leaves (ns ++ f :: nil) fs'
    | (f, ca_rec t) :: fs' => List.map (leaf_proj f ns) (shape_leaves (List.length ns) t) ++ fields_leaves ns fs'
    end.
End Leaves.

(** The names of the non-recursive fields among [fs], in order: those a
    projection's leaf path is over ([fields_leaves]). *)
Fixpoint fields_args (fs : list (string * carg)) : list string :=
  match fs with
  | nil => nil
  | (f, ca_arg _) :: fs' => f :: fields_args fs'
  | (_, ca_rec _) :: fs' => fields_args fs'
  end.

(** A leaf path of fields goes through the projection of one of their
    recursive fields, over the non-recursive fields before it, on into the
    field's shape. *)
Lemma fields_leaves_in : forall tbl fs ns l, In l (fields_leaves tbl ns fs) ->
    exists fs1 f t fs2 l1, fs = fs1 ++ (f, ca_rec t) :: fs2 /\ l = leaf_proj f (ns ++ fields_args fs1) l1 /\
      In l1 (shape_leaves tbl (List.length (ns ++ fields_args fs1)) t).
Proof.
  intros tbl; induction fs as [| [f [A | t]] fs IH]; intros ns l Hin; cbn [fields_leaves] in Hin; [ destruct Hin | |].
  - destruct (IH _ _ Hin) as (fs1 & f' & t & fs2 & l1 & -> & -> & Hl1).
    exists ((f, ca_arg A) :: fs1), f', t, fs2, l1; cbn [fields_args List.app].
    rewrite <- List.app_assoc in Hl1 |- *; cbn [List.app] in Hl1 |- *; auto.
  - apply List.in_app_or in Hin as [Hin | Hin].
    + apply List.in_map_iff in Hin as (l1 & <- & Hl1).
      exists nil, f, t, fs, l1; cbn [fields_args List.app]; rewrite List.app_nil_r; auto.
    + destruct (IH _ _ Hin) as (fs1 & f' & t' & fs2 & l1 & -> & -> & Hl1).
      exists ((f, ca_rec t) :: fs1), f', t', fs2, l1; cbn [fields_args List.app]; auto.
Qed.

(** The leaf paths of a member, if it is a record view, given those of
    the members before it: its fields' ([fields_leaves]), its fields named
    as its head names them. *)
Definition member_leaves (tbl : nat -> option (list leaf_path)) (M : imember) : option (list leaf_path) :=
  match im_head M, im_cons M with
  | mh_record _ _ fl, (_, gs) :: nil => Some (fields_leaves tbl nil (List.combine fl gs))
  | _, _ => None
  end.

(** The table of the leaf paths of the record views, member by member:
    each from the table of the members before it.  The record views'
    fields end only in members before them ([rview_order_ok]), so the
    table is a fold, without a measure. *)
Fixpoint leaves_tbl_from (acc : list (option (list leaf_path))) (ms : list imember) : list (option (list leaf_path)) :=
  match ms with
  | nil => acc
  | M :: ms' => leaves_tbl_from (acc ++ member_leaves (fun j => List.nth j acc None) M :: nil) ms'
  end.

(** The leaf paths of the record view [j] of the group [D]. *)
Definition rv_leaves (D : ind_decl) (j : nat) : option (list leaf_path) :=
  List.nth j (leaves_tbl_from nil (ind_members D)) None.

(** The number of leaf paths of a shape does not depend on the binders
    its components are over. *)
Lemma length_shape_leaves : forall tbl t m m',
    List.length (shape_leaves tbl m t) = List.length (shape_leaves tbl m' t).
Proof.
  intros tbl t; induction t as [j Ps | B t IH]; intros m m'; cbn.
  - destruct (tbl j); rewrite ?List.length_map; reflexivity.
  - rewrite !List.length_map; apply IH.
Qed.

(** The record views' fields end only in record views before them: what
    makes the table a fold.  The core command lists the record views so
    (children before parents, after every other member). *)
Definition rview_order_ok (D : ind_decl) : Prop :=
  forall j Mj qr Is fl c gs gs1 t gs2 Mi,
    ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
    gs = gs1 ++ ca_rec t :: gs2 -> ind_member D (ptyp_mem t) = Some Mi -> im_is_rview Mi = true ->
    ptyp_mem t < j.

(** The table gives each record view the leaf paths of its fields, read
    off the table itself: the fact about the table that the semantics
    needs ([rview_order_ok] gives it, [leaves_coherent_of_order]). *)
Definition leaves_coherent (D : ind_decl) : Prop :=
  forall j Mj qr Is fl c gs, ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
    rv_leaves D j = Some (fields_leaves (rv_leaves D) nil (List.combine fl gs)).

(** The leaf paths of a shape read only the table's entry at the member
    the shape ends in. *)
Lemma shape_leaves_ext : forall tbl1 tbl2 t m, tbl1 (ptyp_mem t) = tbl2 (ptyp_mem t) ->
    shape_leaves tbl1 m t = shape_leaves tbl2 m t.
Proof.
  intros tbl1 tbl2 t; induction t as [j Ps | B t IH]; intros m H; cbn in *; [ rewrite H; reflexivity |].
  rewrite IH by exact H; reflexivity.
Qed.

Lemma fields_leaves_ext : forall tbl1 tbl2 fs ns,
    (forall f t, In (f, ca_rec t) fs -> tbl1 (ptyp_mem t) = tbl2 (ptyp_mem t)) ->
    fields_leaves tbl1 ns fs = fields_leaves tbl2 ns fs.
Proof.
  intros tbl1 tbl2; induction fs as [| [f [A | t]] fs IH]; intros ns H; cbn; [ reflexivity | |].
  - apply IH; intros; apply (H f0); right; assumption.
  - rewrite (shape_leaves_ext tbl1 tbl2) by (apply (H f); left; reflexivity).
    rewrite IH by (intros; apply (H f0); right; assumption); reflexivity.
Qed.

(** The table from [acc]: [acc], then one entry per member, each read off
    the table before it. *)
Lemma leaves_tbl_from_prefix : forall ms acc,
    List.length (leaves_tbl_from acc ms) = List.length acc + List.length ms /\
    List.firstn (List.length acc) (leaves_tbl_from acc ms) = acc.
Proof.
  induction ms as [| M ms IH]; intros acc; cbn; [ rewrite Nat.add_0_r, List.firstn_all; auto |].
  destruct (IH (acc ++ member_leaves (fun j => List.nth j acc None) M :: nil)) as [Hl Hf].
  rewrite List.length_app in Hl; cbn in Hl; split; [ lia |].
  set (acc' := acc ++ _ :: nil) in *.
  assert (E : List.firstn (List.length acc) (leaves_tbl_from acc' ms) =
              List.firstn (List.length acc) (List.firstn (List.length acc') (leaves_tbl_from acc' ms))).
  { rewrite List.firstn_firstn, Nat.min_l; [ reflexivity | unfold acc'; rewrite List.length_app; cbn; lia ]. }
  rewrite E, Hf; unfold acc'; rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; cbn; rewrite List.app_nil_r; reflexivity.
Qed.

(** The entry of the member [k] is its leaf paths read off the table
    before it. *)
Lemma leaves_tbl_from_nth : forall ms acc k M, List.nth_error ms k = Some M ->
    List.nth (List.length acc + k) (leaves_tbl_from acc ms) None =
      member_leaves (fun j => List.nth j (List.firstn (List.length acc + k) (leaves_tbl_from acc ms)) None) M.
Proof.
  induction ms as [| M0 ms IH]; intros acc k M H; [ destruct k; discriminate |].
  destruct k as [| k]; cbn in H |- *.
  - injection H as ->; rewrite Nat.add_0_r.
    set (acc' := acc ++ member_leaves (fun j => List.nth j acc None) M :: nil).
    destruct (leaves_tbl_from_prefix ms acc') as [_ Hf].
    assert (Hl : List.length acc' = S (List.length acc)) by (unfold acc'; rewrite List.length_app; cbn; lia).
    assert (Hp : List.firstn (List.length acc) (leaves_tbl_from acc' ms) = acc).
    { assert (E : List.firstn (List.length acc) (leaves_tbl_from acc' ms) =
              List.firstn (List.length acc) (List.firstn (List.length acc') (leaves_tbl_from acc' ms)))
        by (rewrite List.firstn_firstn, Nat.min_l; [ reflexivity | lia ]).
      rewrite E, Hf; unfold acc'; rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; cbn; rewrite List.app_nil_r; reflexivity. }
    assert (Hn : List.nth (List.length acc) (leaves_tbl_from acc' ms) None = List.nth (List.length acc) acc' None).
    { rewrite <- Hf at 2; rewrite List.nth_firstn, Hl.
      destruct (Nat.ltb_spec (List.length acc) (S (List.length acc))); [ reflexivity | lia ]. }
    rewrite Hn, Hp; unfold acc'; rewrite List.app_nth2, Nat.sub_diag by lia; reflexivity.
  - pose proof (IH (acc ++ member_leaves (fun j => List.nth j acc None) M0 :: nil) k M H) as E.
    rewrite List.length_app in E; cbn in E.
    replace (List.length acc + S k) with (List.length acc + 1 + k) by lia; exact E.
Qed.

(** A member's leaf paths read off two tables that agree everywhere. *)
Lemma member_leaves_ext : forall tbl1 tbl2 M, (forall j, tbl1 j = tbl2 j) -> member_leaves tbl1 M = member_leaves tbl2 M.
Proof.
  intros * H; unfold member_leaves.
  destruct (im_head M), (im_cons M) as [| [c gs] [|]]; try reflexivity.
  rewrite (fields_leaves_ext tbl1 tbl2) by (intros; apply H); reflexivity.
Qed.

(** The entry of the member [k] of a group, read off the entries before
    it. *)
Lemma rv_leaves_member : forall D k M, ind_member D k = Some M ->
    rv_leaves D k = member_leaves (fun j => if j <? k then rv_leaves D j else None) M.
Proof.
  intros * HM; unfold rv_leaves.
  pose proof (leaves_tbl_from_nth (ind_members D) nil k M HM) as E; cbn in E; rewrite E.
  apply member_leaves_ext; intros j.
  rewrite List.nth_firstn; destruct (Nat.ltb_spec j k); reflexivity.
Qed.

(** A member that is no record view has no entry. *)
Lemma rv_leaves_not_rview : forall D k M, ind_member D k = Some M -> im_is_rview M = false -> rv_leaves D k = None.
Proof.
  intros * HM Hr; rewrite (rv_leaves_member _ _ _ HM); unfold member_leaves, im_is_rview in *.
  destruct (im_head M); [ reflexivity | reflexivity | discriminate ].
Qed.

(** Nor has a position past the members. *)
Lemma rv_leaves_none : forall D k, ind_member D k = None -> rv_leaves D k = None.
Proof.
  intros * HM; unfold rv_leaves, ind_member in *.
  destruct (leaves_tbl_from_prefix (ind_members D) nil) as [Hl _]; cbn in Hl.
  apply List.nth_overflow; apply List.nth_error_None in HM; lia.
Qed.

(** The order of the record views makes the table coherent. *)
Lemma leaves_coherent_of_order : forall D, rview_order_ok D -> leaves_coherent D.
Proof.
  intros D Ho j Mj qr Is fl c gs HM Hh Hc.
  rewrite (rv_leaves_member _ _ _ HM); unfold member_leaves; rewrite Hh, Hc; f_equal.
  apply fields_leaves_ext; intros f t Hin.
  apply List.in_combine_r, List.in_split in Hin as (gs1 & gs2 & Egs).
  destruct (Nat.ltb_spec (ptyp_mem t) j) as [Hlt | Hge]; [ reflexivity |].
  destruct (ind_member D (ptyp_mem t)) as [Mi |] eqn:HMi; [| symmetry; exact (rv_leaves_none _ _ HMi) ].
  destruct (im_is_rview Mi) eqn:Hr.
  - exfalso; pose proof (Ho _ _ _ _ _ _ _ _ _ _ _ HM Hh Hc Egs HMi Hr); lia.
  - symmetry; exact (rv_leaves_not_rview _ _ _ HMi Hr).
Qed.

Fixpoint cargs_nrec (D : ind_decl) (gs : list carg) : nat :=
  match gs with
  | nil => 0
  | ca_arg _ :: gs' => cargs_nrec D gs'
  | ca_rec t :: gs' => List.length (shape_leaves (rv_leaves D) 0 t) + cargs_nrec D gs'
  end.

(** A record view's fields, named, have as many leaf paths as its
    constructor's arguments have recursive results. *)
Lemma length_fields_leaves_combine : forall D fl gs ns, List.length fl = List.length gs ->
    List.length (fields_leaves (rv_leaves D) ns (List.combine fl gs)) = cargs_nrec D gs.
Proof.
  intros D; induction fl as [| f fl IH]; intros [| [A | t] gs] ns Hl; cbn in *; try discriminate; [ reflexivity | |].
  - apply IH; lia.
  - rewrite List.length_app, List.length_map, IH, (length_shape_leaves _ _ _ 0) by lia; reflexivity.
Qed.

(** At a record view with a coherent table, the leaf paths of a shape
    ending in it are its fields'. *)
Lemma length_shape_leaves_rview : forall D j Mj qr Is fl c gs Ps m,
    leaves_coherent D -> ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
    List.length fl = List.length gs ->
    List.length (shape_leaves (rv_leaves D) m (pt_self j Ps)) = cargs_nrec D gs.
Proof.
  intros * Hc HM Hh Hcs Hl; cbn; rewrite (Hc _ _ _ _ _ _ _ HM Hh Hcs), List.length_map.
  exact (length_fields_leaves_combine D fl gs nil Hl).
Qed.

(** At a member with a block, one. *)
Lemma length_shape_leaves_self : forall D j Mj Ps m, ind_member D j = Some Mj -> im_is_rview Mj = false ->
    shape_leaves (rv_leaves D) m (pt_self j Ps) = leaf_self j Ps :: nil.
Proof. intros * HM Hr; cbn; rewrite (rv_leaves_not_rview _ _ _ HM Hr); reflexivity. Qed.

(** ** A Property of All the Members of a List

    The values of a constructor, an inductive type and their parameters are
    lists, of which evaluation and readback take segments; a property of all
    the members of the list holds of all the members of a segment. *)

Section AllIn.
  Context {A : Type} (P : A -> Prop).

  Lemma all_in_nil : forall a, In a nil -> P a.
  Proof. intros ? []. Qed.

  Lemma all_in_cons : forall x l, P x -> (forall a, In a l -> P a) -> forall a, In a (x :: l) -> P a.
  Proof. intros * Hx Hl a [<- | Ha]; auto. Qed.

  Lemma all_in_app : forall l l', (forall a, In a l -> P a) -> (forall a, In a l' -> P a) ->
                                  forall a, In a (l ++ l') -> P a.
  Proof. intros * Hl Hl' a Ha; apply in_app_or in Ha as [Ha | Ha]; auto. Qed.

  Lemma all_in_firstn : forall n l, (forall a, In a l -> P a) -> forall a, In a (firstn n l) -> P a.
  Proof.
    intros * Hl a Ha; apply Hl; rewrite <- (firstn_skipn n l); apply in_or_app; left; assumption.
  Qed.

  Lemma all_in_skipn : forall n l, (forall a, In a l -> P a) -> forall a, In a (skipn n l) -> P a.
  Proof.
    intros * Hl a Ha; apply Hl; rewrite <- (firstn_skipn n l); apply in_or_app; right; assumption.
  Qed.

  Lemma all_in_tail : forall x l, (forall a, In a (x :: l) -> P a) -> forall a, In a l -> P a.
  Proof. intros * H a Ha; apply H; right; assumption. Qed.

  Lemma all_in_head : forall x l, (forall a, In a (x :: l) -> P a) -> P x.
  Proof. intros * H; apply H; left; reflexivity. Qed.

End AllIn.

(** Splits a goal [forall a, In a l -> P a] along the segments [l] is
    built of, down to hypotheses about whole lists or their tails, and
    leaves the members added one by one ([P x]) to [tac]. *)
Ltac all_in_with tac :=
  repeat lazymatch goal with
  | |- forall a, In a _ -> _ =>
  first [ eassumption
               | apply all_in_nil
               | match goal with H : forall a, In a (cons _ ?l) -> _ |- forall a, In a ?l -> _ =>
                   exact (all_in_tail _ _ _ H) end
               | apply all_in_app
               | apply all_in_firstn
               | apply all_in_skipn
               | apply all_in_cons; [ tac |] ]
  end.

Lemma brs_lookup_in : forall Bs c n B, brs_lookup Bs c = Some (n, B) -> In (c, n, B) Bs.
Proof.
  induction Bs as [| [[c' n'] B'] Bs IH]; cbn; intros * H; [ discriminate |].
  destruct (String.eqb_spec c c') as [-> | _]; [ injection H as -> ->; left; reflexivity | right; auto ].
Qed.

(** The environment of a branch extends the eliminator's by the
    non-uniform parameters, the arguments and the recursive results; the
    environment of the motive's instance at a neutral, by the non-uniform
    parameters and the neutral. *)
Lemma ind_branch_args_length : forall {A} D M (gs : list carg) (vs ihs : list A),
    List.length vs = im_np D M + List.length gs ->
    List.length (skipn (ind_nu D) (firstn (im_np D M) vs) ++ skipn (im_np D M) vs ++ ihs) =
      im_nn M + List.length gs + List.length ihs.
Proof.
  intros * H; rewrite !length_app, !length_skipn, length_firstn, Nat.min_l by lia.
  unfold im_np in *; lia.
Qed.

Lemma ind_motive_args_length : forall {A} D M (as' : list A) x,
    List.length as' = im_np D M ->
    List.length (skipn (ind_nu D) as' ++ x :: nil) = S (im_nn M).
Proof. intros * H; rewrite length_app, length_skipn; cbn; unfold im_np in *; lia. Qed.

(** The telescope of the non-uniform parameters, outermost first. *)
Lemma im_nn_tele_length : forall M, List.length (List.rev (im_nparams M)) = im_nn M.
Proof. intros; rewrite length_rev; reflexivity. Qed.

(** ** The Types of a Declaration

    What typing reads off a group [D] at [pq]: the types of the type
    formers and of the constructors, the contexts of the motives and of the
    branches of the eliminator, and the instances of telescopes at lists
    of terms.  All are built once, by typing; evaluation and readback use
    the declaration directly.

    The parameters of a member, [im_params D M], are a closed context,
    innermost first: its non-uniform ones, [im_nn M] of them, are the
    innermost.  The sort is in the context of the uniform ones. *)

Import Sub_Notations Wk_Notations.

(** The member [j] of the group [pq] at the uniform parameters [Us] and
    its non-uniform parameters [Ns]. *)
Definition ind_mty (pq : qname) (D : ind_decl) (j : nat) (Us Ns : list exp) : typ :=
  match ind_member D j with
  | Some M => im_ty_at pq j M Us Ns
  | None => a_True
  end.

(** The parameters of the member [M], and the uniform ones, as variables,
    under [k] more binders. *)
Definition ind_pvars (D : ind_decl) (M : imember) (k : nat) : list exp := vars_from k (im_np D M).
(** The uniform parameters as variables, under [k] binders and the [nn]
    non-uniform parameters of a member. *)
Definition ind_uvars (D : ind_decl) (nn k : nat) : list exp := vars_from (k + nn) (ind_nu D).

(** The type of the type former of a member: a [Π] over its parameters
    of the sort. *)
Definition ind_ty (D : ind_decl) (M : imember) : typ := ctx_pi (im_params D M) (ind_sort D)[wk_shiftn (im_nn M)]ʷ.

(** The types of the non-recursive arguments of a constructor are in the
    context of the non-recursive arguments before them: a recursive argument
    is not a binder for them ([cargs_strat]).  [wk_pat pat] sends that
    context into the one of all the arguments before, where [pat] tells,
    innermost first, which of them are recursive. *)
Fixpoint cargs_strat (gs : list carg) : ctx :=
  match gs with
  | nil => nil
  | ca_arg A :: gs' => cargs_strat gs' ++ ce_ass A :: nil
  | ca_rec _ :: gs' => cargs_strat gs'
  end.

(** ** Shapes

    A shape [pt_pi B1 (pt_pi B2 … (pt_self j Ps))] is a function from its
    domains [B1], [B2], …, each over the ones before it, into the member [j]
    at the non-uniform parameters [Ps], over all its domains.  Its domains,
    outermost first, and as a telescope, innermost first. *)
Fixpoint ptyp_doms {E : Set} (t : ptyp_g E) : list E :=
  match t with
  | pt_pi A t => A :: ptyp_doms t
  | _ => nil
  end.

Definition doms_ctx (Bs : list exp) : ctx := List.rev (List.map ce_ass Bs).
Definition ptyp_tele (t : ptyp) : ctx := doms_ctx (ptyp_doms t).
Definition ptyp_depth (t : ptyp) : nat := List.length (ptyp_doms t).

(** The shape of each recursive argument among [gs] ends in a member of
    [D] at as many parameters as the member has non-uniform ones. *)
Definition cargs_plen (D : ind_decl) (gs : list carg) : Prop :=
  forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    exists Mj, ind_member D (ptyp_mem t) = Some Mj /\ List.length (ptyp_ps t) = im_nn Mj.

(** The leaf paths through the record views of [D] end at as many
    parameters as their members have non-uniform ones: each record view's
    fields do, and they end only in record views before it, so a walk down
    the fields stops.  Readback asks it of the group of a stuck eliminator
    ([read_ne_elim]), as it asks [blocks_nm_at]: the type of a recursive
    result along a path through a record view is its end member's motive,
    evaluated under the end's parameters, which must be as many as the
    motive binds.  Every declared group has it. *)
Record rview_leaf_arity (D : ind_decl) : Prop := mk_rview_leaf_arity
  { (** The shapes of a record view's fields end at as many parameters as
        their members have non-uniform ones *)
    rview_leaf_plen : forall k Mk c gs, ind_member D k = Some Mk -> im_is_rview Mk = true -> In (c, gs) (im_cons Mk) ->
      cargs_plen D gs
    (** A record view's fields end only in record views before it *)
  ; rview_leaf_order : rview_order_ok D }.

(** The rest of a shape after [n] of its domains. *)
Fixpoint ptyp_skip (n : nat) (t : ptyp) : ptyp :=
  match n, t with
  | S n, pt_pi _ t => ptyp_skip n t
  | _, _ => t
  end.

(** The context of the domains of a shape, each weakened past the arguments
    before it by the pattern [pat] extended by the domains before it:
    the context in which the type of a recursive argument binds them. *)
Fixpoint sh_ctx (pat : list bool) (Bs : list exp) : ctx :=
  match Bs with
  | nil => nil
  | B :: Bs => sh_ctx (false :: pat) Bs ++ ce_ass B[wk_pat pat]ʷ :: nil
  end.

(** The type of a recursive argument of shape [t], in the context of all
    the arguments before it and the parameters of a member with [nn]
    non-uniform parameters, its components over the non-recursive
    arguments before it ([pat], innermost first, tells which of those
    before it are recursive): the [Π] over the domains of the member the
    shape ends in at the uniform parameters and the shape's non-uniform
    ones.  Under a domain the components are over one more variable, which
    is no recursive argument. *)
Fixpoint ptyp_ty (pq : qname) (D : ind_decl) (nn : nat) (pat : list bool) (t : ptyp) : typ :=
  match t with
  | pt_pi A t => a_pi A[wk_pat pat]ʷ (ptyp_ty pq D nn (false :: pat) t)
  | pt_self j Ps => ind_mty pq D j (ind_uvars D nn (List.length pat)) (List.map (fun P => P[wk_pat pat]ʷ) Ps)
  end.

(** The arguments of a constructor as a context over the parameters,
    innermost first: a recursive one is of the type of its shape. *)
Fixpoint cargs_ctx_aux (pq : qname) (D : ind_decl) (nn : nat) (pat : list bool) (gs : list carg) : ctx :=
  match gs with
  | nil => nil
  | ca_arg A :: gs' => cargs_ctx_aux pq D nn (false :: pat) gs' ++ ce_ass A[wk_pat pat]ʷ :: nil
  | ca_rec t :: gs' => cargs_ctx_aux pq D nn (true :: pat) gs' ++ ce_ass (ptyp_ty pq D nn pat t) :: nil
  end.

(** The arguments of a constructor of the member [M] as a context over its
    parameters, from no argument before. *)
Definition cargs_ctx (pq : qname) (D : ind_decl) (M : imember) (gs : list carg) : ctx :=
  cargs_ctx_aux pq D (im_nn M) nil gs.

(** ** The Group's Members as Variables

    The equations of a group's views mention the group itself: a view's
    instance is at the group's own types.  Before the group is filed they
    are checked with its declared members as variables, [Self_j] for the
    declared member [j], each of the member's type over the group's
    uniform parameters, the [Self]s inside the uniform parameters
    ([grp_sctx]); [IsS] gives each view's instance there.  Once the group
    is filed at [pq], [grp_sb pq D] instantiates [Self_j] by the type former
    [a_ind pq j] at the uniform parameters, and the checked forms become
    the filed ones. *)
Definition self_ty (D : ind_decl) (M : imember) : typ := ctx_pi (im_nparams M) (ind_sort D)[wk_shiftn (im_nn M)]ʷ.

(** The variables [Self_j], [Self_(j+1)], … of the members [ms], innermost
    first, each of its member's type over the [Self]s before it. *)
Fixpoint grp_selfs_from (D : ind_decl) (j : nat) (ms : list imember) : ctx :=
  match ms with
  | nil => nil
  | M :: ms' => grp_selfs_from D (S j) ms' ++ ce_ass (self_ty D M)[wk_shiftn j]ʷ :: nil
  end.

(** The variables of the declared members, [Self_0] outermost. *)
Definition grp_selfs (D : ind_decl) : ctx := grp_selfs_from D 0 (List.firstn (ind_ndecl D) (ind_members D)).

(** The context a group's views are checked in: the [Self]s inside the
    uniform parameters. *)
Definition grp_sctx (D : ind_decl) : ctx := grp_selfs D ++ ind_uparams D.

(** The [Self]s instantiated by the type formers of the filed group at
    [pq], at the uniform parameters. *)
Definition grp_sb (pq : qname) (D : ind_decl) : sub :=
  sb_of_list sb_id (List.map (fun j => apps (a_ind pq j) (vars_from 0 (ind_nu D))) (List.seq 0 (ind_ndecl D))).

(** The group's own data, which never mentions the group, moved under the
    [Self]s: [k] binders above the uniform parameters. *)
Definition self_wk (D : ind_decl) (k : nat) : wk := wk_qn k (wk_shiftn (ind_ndecl D)).

(** The type of the member [j] with the members as variables, [d] binders
    above the [Self]s, at the non-uniform parameters [Ns]: [Self_j] at a
    declared member, the container's at the view's instance [IsS j] at a
    view, the record type at its instance [IsS j] at a record view. *)
Definition self_mty (D : ind_decl) (IsS : nat -> list exp) (j d : nat) (Ns : list exp) : typ :=
  match ind_member D j with
  | Some Mj =>
      match im_head Mj with
      | mh_decl _ => apps_exp (a_var (d + (ind_ndecl D - 1 - j))) Ns
      | mh_view qc kc _ _ => apps_exp (a_ind qc kc) (List.map (fun I => I[wk_shiftn d]ʷ) (IsS j) ++ Ns)
      | mh_record qr _ _ => apps_exp (a_record qr) (List.map (fun I => I[wk_shiftn d]ʷ) (IsS j) ++ Ns)
      end
  | None => a_True
  end.

(** [ptyp_ty] and [cargs_ctx] with the members as variables. *)
Fixpoint sptyp_ty (D : ind_decl) (IsS : nat -> list exp) (nn : nat) (pat : list bool) (t : ptyp) : typ :=
  match t with
  | pt_pi A t => a_pi A[wk_pat pat]ʷ[self_wk D (List.length pat + nn)]ʷ (sptyp_ty D IsS nn (false :: pat) t)
  | pt_self j Ps => self_mty D IsS j (List.length pat + nn)
                      (List.map (fun P => P[wk_pat pat]ʷ[self_wk D (List.length pat + nn)]ʷ) Ps)
  end.

(** [cargs_ctx_aux] with the members as variables. *)
Fixpoint scargs_ctx_aux (D : ind_decl) (IsS : nat -> list exp) (nn : nat) (pat : list bool) (gs : list carg) : ctx :=
  match gs with
  | nil => nil
  | ca_arg A :: gs' => scargs_ctx_aux D IsS nn (false :: pat) gs' ++ ce_ass A[wk_pat pat]ʷ[self_wk D (List.length pat + nn)]ʷ :: nil
  | ca_rec t :: gs' => scargs_ctx_aux D IsS nn (true :: pat) gs' ++ ce_ass (sptyp_ty D IsS nn pat t) :: nil
  end.

(** [cargs_ctx] with the members as variables. *)
Definition scargs_ctx (D : ind_decl) (IsS : nat -> list exp) (M : imember) (gs : list carg) : ctx :=
  scargs_ctx_aux D IsS (im_nn M) nil gs.

(** The type of a constructor of the member [k]: a [Π] over the
    parameters and the arguments of the member at the parameters.  (For a
    view, this is the type of the container's constructor at the view's
    uniform arguments, as the group sees it.) *)
Definition con_ty (pq : qname) (D : ind_decl) (k : nat) (M : imember) (gs : list carg) : typ :=
  ctx_pi (im_params D M)
    (ctx_pi (cargs_ctx pq D M gs)
       (ind_mty pq D k (ind_uvars D (im_nn M) (List.length gs)) (vars_from (List.length gs) (im_nn M)))).

(** The instances of the types of a telescope [Δ] (innermost first) at the
    terms [Ms] (outermost first), the others free variables sent as [σ]
    does. *)
Fixpoint tele_insts_aux (Δr : list centry) (σ : sub) (Ms : list exp) : list typ :=
  match Δr, Ms with
  | ce_ass A :: Δr', M :: Ms' => A[σ] :: tele_insts_aux Δr' (σ ,, M) Ms'
  | _, _ => nil
  end.

Definition tele_insts (Δ : ctx) (σ : sub) (Ms : list exp) : list typ := tele_insts_aux (List.rev Δ) σ Ms.

(** ** The Eliminator

    The motive of the block of the member [k] is in the context of the
    member's non-uniform parameters, at the group's uniform ones [Us], and
    of the scrutinee. *)
Definition elim_mctx (pq : qname) (D : ind_decl) (k : nat) (M : imember) (Us : list exp) : ctx :=
  ce_ass (ind_mty pq D k (List.map (fun U => U[wk_shiftn (im_nn M)]ʷ) Us) (vars_from 0 (im_nn M)))
  :: tele_sub (im_nparams M) (sb_of_list Id Us).

(** The type of an argument of shape [t], its components moved by [σ], at
    the uniform parameters [Us]: [ptyp_ty] at an instance of the parameters
    and the arguments before. *)
Fixpoint ptyp_ty_at (pq : qname) (D : ind_decl) (Us : list exp) (σ : sub) (t : ptyp) : typ :=
  match t with
  | pt_pi B t => a_pi B[σ] (ptyp_ty_at pq D (List.map (fun U => U[wk_shift]ʷ) Us) (sb_q σ) t)
  | pt_self j Ps => ind_mty pq D j Us (List.map (fun P => P[σ]) Ps)
  end.

(** A map on the second components of a list of pairs is a map on the
    list it is combined from: how the fields of a tuple move. *)
Lemma combine_map_snd : forall {A B C : Type} (f : B -> C) (xs : list A) (ys : list B),
    List.map (fun p => (fst p, f (snd p))) (List.combine xs ys) = List.combine xs (List.map f ys).
Proof. intros A B C f; induction xs as [| x xs IH]; intros [| y ys]; cbn; f_equal; auto. Qed.

(** The projections of [x] at the fields [ns], in order: what the
    components of a leaf path after a projection are over. *)
Definition projections_of (ns : list string) (x : exp) : list exp := List.map (fun g => a_proj g x) ns.

(** The type of the recursive result of an argument [x] along a leaf path
    [l]: the motive of the member the path ends in, among the motives [As],
    at the path's non-uniform parameters and [x] at the end of the path:
    [x] applied to the domains the path passes (a [Π] over each), and
    projected at the fields it passes.  The motives' context, the
    eliminator's, is moved by [β], the path's components by [σ], which a
    projection extends by the projections of the non-recursive fields
    before the field. *)
Fixpoint leaf_ihty (As : list exp) (β σ : sub) (x : exp) (l : leaf_path) : typ :=
  match l with
  | leaf_pi B l => a_pi B[σ] (leaf_ihty As (β ⨟ sb_of_wk wk_shift) (sb_q σ) (a_app x[wk_shift]ʷ (a_var 0)) l)
  | leaf_self j Ps => (List.nth j As a_True)[sb_of_list β (List.map (fun P => P[σ]) Ps ++ x :: nil)]
  | leaf_proj f ns l => leaf_ihty As β (sb_of_list σ (projections_of ns x)) (a_proj f x) l
  end.

(** The recursive results of a constructor's arguments: the motive of the
    member each leaf path of each recursive argument ends in, at the
    argument along the path.  [i] arguments of [gs] and [j] results come
    before; [na] is the number of all the arguments, [nn] that of the
    member's non-uniform parameters.  [ihs_sub] moves a shape's components
    from the context of the non-recursive arguments before it and the
    parameters to the branch's: past the recursive arguments before it, the
    uniform parameters instantiated by [Us], past the arguments after it
    and the results before it. *)
Definition ihs_sub (nn : nat) (Us : list exp) (na : nat) (pat : list bool) (j : nat) : sub :=
  (sb_of_wk (wk_pat pat) ⨟ sb_qn (List.length pat + nn) (sb_of_list Id Us))
    ⨟ sb_of_wk (wk_shiftn (na - List.length pat + j)).

(** The number of non-recursive arguments a pattern tells. *)
Fixpoint pat_nargs (pat : list bool) : nat :=
  match pat with
  | nil => 0
  | false :: pat' => S (pat_nargs pat')
  | true :: pat' => pat_nargs pat'
  end.

(** The recursive results of a recursive argument along its leaf paths
    [ls], after [j] results, as a context: one per path, of its motive's
    type ([leaf_ihty]); [pat] tells which arguments before the argument
    are recursive. *)
Fixpoint leaves_ctx (nn : nat) (As : list exp) (Us : list exp) (na : nat)
    (pat : list bool) (j : nat) (ls : list leaf_path) : ctx :=
  match ls with
  | nil => nil
  | l :: ls' =>
      leaves_ctx nn As Us na pat (S j) ls' ++
        ce_ass (leaf_ihty As (sb_of_wk (wk_shiftn (j + na + nn))) (ihs_sub nn Us na pat j)
                  (a_var (j + na - 1 - List.length pat)) l) :: nil
  end.

(** The recursive results of a branch, after [j] of them, as a context:
    one per leaf path of each recursive argument, of its motive's type;
    the leaf paths are read off the table [tbl] of the group's record
    views. *)
Fixpoint ihs_ctx_aux (tbl : nat -> option (list leaf_path)) (nn : nat) (As : list exp) (Us : list exp) (na : nat)
    (pat : list bool) (j : nat) (gs : list carg) : ctx :=
  match gs with
  | nil => nil
  | ca_arg _ :: gs' => ihs_ctx_aux tbl nn As Us na (false :: pat) j gs'
  | ca_rec t :: gs' =>
      let ls := shape_leaves tbl (pat_nargs pat + nn) t in
      ihs_ctx_aux tbl nn As Us na (true :: pat) (List.length ls + j) gs' ++
        leaves_ctx nn As Us na pat j ls
  end.

(** The context of the branch of a constructor with arguments [gs] of the
    member [M]: the non-uniform parameters, the arguments and the recursive
    results, the motives being [As]. *)
Definition elim_bctx (pq : qname) (D : ind_decl) (M : imember) (gs : list carg) (As : list exp) (Us : list exp) : ctx :=
  ihs_ctx_aux (rv_leaves D) (im_nn M) As Us (List.length gs) nil 0 gs ++
  tele_sub (cargs_ctx pq D M gs) (sb_qn (im_nn M) (sb_of_list Id Us)) ++
  tele_sub (im_nparams M) (sb_of_list Id Us).

(** The type of the branch: the motive [A] of the member [k] of [D] at the
    constructor applied to the parameters and the arguments. *)
Definition elim_bty (pq : qname) (D : ind_decl) (k : nat) (M : imember) (c : string) (gs : list carg) (A : exp) (Us : list exp) : typ :=
  let na := List.length gs in
  let nn := im_nn M in
  let n := (nn + na + cargs_nrec D gs)%nat in
  A[sb_of_list (sb_of_wk (wk_shiftn n))
      (vars_from (cargs_nrec D gs + na) nn ++
       apps_exp (a_con (fst (im_ref pq k M)) (snd (im_ref pq k M)) c)
         (im_pre M (List.map (fun U => U[wk_shiftn n]ʷ) Us) ++
          vars_from (cargs_nrec D gs + na) nn ++ vars_from (cargs_nrec D gs) na) :: nil)].

(** The branches under [φ], each under the binders it has: what
    weakening does to the branches of an eliminator. *)
Definition brs_wk (Bs : list (string * nat * exp)) (φ : wk) : list (string * nat * exp) :=
  List.map (fun b => (fst b, (snd b)[wk_qn (snd (fst b)) φ]ʷ)) Bs.

(** The blocks under [φ]: what weakening does to the blocks of an
    eliminator ([exp_wk] unfolds to it). *)
Definition blocks_wk (Bks : list eblock) (φ : wk) : list eblock :=
  List.map (fun b =>
    match b with
    | eb_mk nm oZ A Bs =>
        eb_mk nm (option_map (fun Z => exp_wk Z (wk_qn (nm - 1) φ)) oZ) (exp_wk A (wk_qn nm φ))
          (List.map (fun br => (fst br, exp_wk (snd br) (wk_qn (snd (fst br)) φ))) Bs)
    end) Bks.

Lemma exp_wk_elim : forall oq Us m Bks M φ,
    (a_elim oq Us m Bks M)[φ]ʷ = a_elim oq (List.map (fun U => U[φ]ʷ) Us) m (blocks_wk Bks φ) M[φ]ʷ.
Proof. reflexivity. Qed.

(** The motives of the blocks, in order. *)
Definition blocks_motives (Bks : list eblock) : list exp := List.map eb_motive Bks.

(** ** Reading an Eliminator at its Member

    An eliminator of a group at its member [m] is read, when stuck, as the
    eliminator of the group the member is at: the group itself at a
    declared member, the container's at a view (E1′).  The blocks it reads
    are those of the members of that group, each the block of the member
    of this group [elim_src] gives: itself at a declared member, the view
    [vm] lists at a view.  Nothing is built: a block is looked up. *)
Definition im_sel (M : imember) : option (list nat) :=
  match im_head M with
  | mh_view _ _ _ vm => Some vm
  | _ => None
  end.

(** The member of this group whose block the eliminator reads for the
    member [i] of the group it is read as. *)
Definition elim_src (sel : option (list nat)) (i : nat) : nat :=
  match sel with
  | None => i
  | Some vm => List.nth i vm 0
  end.

(** The motives of the members of the group read, in its order. *)
Definition motives_sel (sel : option (list nat)) (As : list exp) : list exp :=
  match sel with
  | None => As
  | Some vm => List.map (fun v => List.nth v As a_True) vm
  end.

(** The motive of each block read binds the non-uniform parameters of the
    member of the group read it is the block of, and the scrutinee. *)
Definition blocks_nm_at (Dq : ind_decl) (sel : option (list nat)) (Bks : list eblock) : Prop :=
  forall i Mi b, ind_member Dq i = Some Mi -> List.nth_error Bks (elim_src sel i) = Some b -> eb_nm b = S (im_nn Mi).

(** The eliminator a recursive result at the member [j] is, at the
    group's uniform parameters [Us]: for a group with views the group's,
    named; for one without, the eliminator itself. *)
Definition elim_at (pq : qname) (D : ind_decl) (oq : option qname) (Us : list exp) (Bks : list eblock) (j : nat) (M : exp) : exp :=
  a_elim (if ind_has_views D then Some pq else oq) Us j Bks M.

(** The recursive result of an argument [M] along a leaf path [l], as an
    elimination: under the domains the path passes, moved by [σ], the
    eliminator at [M] applied to them and projected at the fields the path
    passes; a projection extends [σ] by the projections of the
    non-recursive fields before the field. *)
Fixpoint leaf_ih (pq : qname) (D : ind_decl) (oq : option qname) (Us : list exp) (Bks : list eblock)
    (σ : sub) (M : exp) (l : leaf_path) : exp :=
  match l with
  | leaf_pi B l =>
      a_fn B[σ] (leaf_ih pq D oq (List.map (fun U => U[wk_shift]ʷ) Us) (blocks_wk Bks wk_shift) (sb_q σ)
                   (a_app M[wk_shift]ʷ (a_var 0)) l)
  | leaf_self j _ => elim_at pq D oq Us Bks j M
  | leaf_proj f ns l => leaf_ih pq D oq Us Bks (sb_of_list σ (projections_of ns M)) (a_proj f M) l
  end.

(** The recursive results of the arguments [As] of a constructor, as
    eliminations, one per leaf path of each recursive argument; [σ]
    instantiates the parameters and the non-recursive arguments before,
    [m] of them above the uniform parameters, which the shapes' components
    are over. *)
Fixpoint elim_ihs (pq : qname) (D : ind_decl) (oq : option qname) (Us : list exp) (Bks : list eblock)
    (σ : sub) (m : nat) (gs : list carg) (As : list exp) : list exp :=
  match gs, As with
  | ca_arg _ :: gs', N :: As' => elim_ihs pq D oq Us Bks (σ ,, N) (S m) gs' As'
  | ca_rec t :: gs', M :: As' =>
      List.map (leaf_ih pq D oq Us Bks σ M) (shape_leaves (rv_leaves D) m t) ++ elim_ihs pq D oq Us Bks σ m gs' As'
  | _, _ => nil
  end.

(** The branches are in the order of the constructors. *)
Definition brs_names (cs : list (string * list carg)) (Bs : list (string * nat * exp)) : Prop :=
  List.map fst cs = List.map (fun b => fst (fst b)) Bs.

(** The group of an eliminator: written, or that of the scrutinee's type,
    at a declared member. *)
Definition elim_grp (D : ind_decl) (oq : option qname) (pq : qname) (m : nat) : Prop :=
  oq = Some pq \/ (oq = None /\ m < ind_ndecl D).

(** The components of a recursive argument's shape as the type of the
    argument has them: the domain [d], under the arguments before it ([pat])
    and the domains before it, and the non-uniform parameters of the member
    the shape ends in, under all its domains ([ptyp_ty]). *)
Definition ptyp_dom_at (pat : list bool) (d : nat) (t : ptyp) : typ :=
  (List.nth d (ptyp_doms t) a_True)[wk_pat (List.repeat false d ++ pat)]ʷ.

(** The non-uniform parameters a shape ends in, under the arguments
    before ([pat]) and all its domains. *)
Definition ptyp_ps_at (pat : list bool) (t : ptyp) : list exp :=
  List.map (fun P => P[wk_pat (List.repeat false (ptyp_depth t) ++ pat)]ʷ) (ptyp_ps t).

(** The arguments [gs] of a view's constructor are those [gs'] of the
    container's at its arguments, as this group sees them: an argument
    recursive in the container is recursive in the view, at the view's
    member [vm] gives for the container's member, through as many domains;
    an argument the container takes as non-recursive may be either. *)
Fixpoint cargs_corr (vm : list nat) (gs' gs : list carg) : Prop :=
  match gs', gs with
  | nil, nil => True
  | ca_rec t' :: gs1', ca_rec t :: gs1 =>
      List.nth_error vm (ptyp_mem t') = Some (ptyp_mem t) /\ ptyp_depth t' = ptyp_depth t /\ cargs_corr vm gs1' gs1
  | ca_arg _ :: gs1', ca_arg _ :: gs1 => cargs_corr vm gs1' gs1
  | ca_arg _ :: gs1', ca_rec _ :: gs1 => cargs_corr vm gs1' gs1
  | _, _ => False
  end.

(** ** The Eliminator at a View, as the Container's

    The eliminator of a group at its view of the declared member [k'] of
    the container's group [D'] at [Is] is the container's eliminator at
    [k'] (E1′): each block of the container's for its member [i'] is the
    block of the view [vm] gives for [i'], each branch for a container's
    constructor binding the container's arguments and recursive results,
    its body the view's branch, whose recursive results are the
    container's where the argument is recursive in the container, and the
    eliminator of the group at the argument where it is recursive in the
    view only.  The recursive results go by leaf path: a path of the
    view's argument is one of the container's ([leaf_in]) when every field
    it projects is recursive in the container's record view too.
    [wrap_ihs D' D gs' gs ihs r' nr']: the recursive results of the view's
    branch, [ihs] the group's ones, [r'] container's ones before, [nr'] the
    container's in all. *)
Fixpoint leaf_in (D' : ind_decl) (t' : ptyp) (l : leaf_path) {struct l} : bool :=
  match t', l with
  | pt_pi _ t1', leaf_pi _ l1 => leaf_in D' t1' l1
  | pt_self j' _, leaf_self _ _ =>
      match ind_member D' j' with Some M' => negb (im_is_rview M') | None => false end
  | pt_self j' _, leaf_proj f _ l1 =>
      match ind_member D' j' with
      | Some M' =>
          match im_head M', im_cons M' with
          | mh_record _ _ fl, (_, gs') :: nil =>
              match List.find (fun fg => String.eqb (fst fg) f) (List.combine fl gs') with
              | Some (_, ca_rec t1') => leaf_in D' t1' l1
              | _ => false
              end
          | _, _ => false
          end
      | None => false
      end
  | _, _ => false
  end.

(** The arguments of a view's constructor that the view nests through end
    in members of rank below [r] ([rk]): a whole argument non-recursive in
    the container [gs'] and recursive in the view [gs], and, of an argument
    recursive in both, each leaf path of the view's ([D]'s table) that is
    not the container's [D'] ([leaf_in]).  The eliminator at a view reads
    back its branches with the eliminator at those members applied to fresh
    variables; the rank orders these readbacks. *)
Fixpoint cargs_nest_ok (D D' : ind_decl) (rk : nat -> nat) (r : nat) (gs' gs : list carg) : Prop :=
  match gs', gs with
  | ca_arg _ :: gs1', ca_rec t :: gs1 => rk (ptyp_mem t) < r /\ cargs_nest_ok D D' rk r gs1' gs1
  | ca_rec t' :: gs1', ca_rec t :: gs1 =>
      (forall l, In l (shape_leaves (rv_leaves D) 0 t) -> leaf_in D' t' l = false -> rk (leaf_mem l) < r) /\
      cargs_nest_ok D D' rk r gs1' gs1
  | _ :: gs1', _ :: gs1 => cargs_nest_ok D D' rk r gs1' gs1
  | _, _ => True
  end.

(** A whole argument nested through ends in a member of rank below [r]. *)
Lemma cargs_nest_ok_at : forall D D' rk r gs1' A' gs2' gs1 t gs2, List.length gs1' = List.length gs1 ->
    cargs_nest_ok D D' rk r (gs1' ++ ca_arg A' :: gs2') (gs1 ++ ca_rec t :: gs2) -> rk (ptyp_mem t) < r.
Proof.
  intros D D' rk r gs1'; induction gs1' as [| g' gs1' IH]; intros A' gs2' [| g gs1] t gs2 Hl H; cbn in Hl;
    try discriminate; cbn in H.
  - exact (proj1 H).
  - injection Hl as Hl; destruct g', g; cbn in H; first [ exact (IH _ _ _ _ _ Hl H) | exact (IH _ _ _ _ _ Hl (proj2 H)) ].
Qed.

(** So does each leaf path of an argument recursive in both that is not
    the container's. *)
Lemma cargs_nest_ok_leaf_at : forall D D' rk r gs1' t' gs2' gs1 t gs2 l, List.length gs1' = List.length gs1 ->
    cargs_nest_ok D D' rk r (gs1' ++ ca_rec t' :: gs2') (gs1 ++ ca_rec t :: gs2) ->
    In l (shape_leaves (rv_leaves D) 0 t) -> leaf_in D' t' l = false -> rk (leaf_mem l) < r.
Proof.
  intros D D' rk r gs1'; induction gs1' as [| g' gs1' IH]; intros t' gs2' [| g gs1] t gs2 l Hl H Hin Hn; cbn in Hl;
    try discriminate; cbn in H.
  - exact (proj1 H _ Hin Hn).
  - injection Hl as Hl; destruct g', g; cbn in H;
      first [ exact (IH _ _ _ _ _ _ Hl H Hin Hn) | exact (IH _ _ _ _ _ _ Hl (proj2 H) Hin Hn) ].
Qed.

(** Whether a path is the container's does not depend on its components. *)
Lemma leaf_in_wk : forall D' l t' φ, leaf_in D' t' (leaf_wk φ l) = leaf_in D' t' l.
Proof.
  intros D' l; induction l as [j Ps | B l IH | f ns l IH]; intros [j' Ps' | B' t'] φ; cbn [leaf_wk leaf_in]; auto.
  destruct (ind_member D' j') as [M' |]; [| reflexivity ].
  destruct (im_head M'), (im_cons M') as [| [? ?] [|]]; try reflexivity.
  destruct (List.find _ _) as [[? [] ] |]; try reflexivity; apply IH.
Qed.

(** A field found by its name among distinct names. *)
Lemma find_name_split : forall (pre post : list (String.string * carg)) f g,
    List.NoDup (List.map fst (pre ++ (f, g) :: post)) ->
    List.find (fun fg => String.eqb (fst fg) f) (pre ++ (f, g) :: post) = Some (f, g).
Proof.
  induction pre as [| [f0 g0] pre IH]; intros * Hnd; cbn [List.app List.find fst].
  - rewrite String.eqb_refl; reflexivity.
  - cbn [List.map List.app] in Hnd; inversion Hnd as [| ? ? Hn Hnd']; subst.
    destruct (String.eqb_spec f0 f) as [-> | _]; [| apply IH; exact Hnd' ].
    exfalso; apply Hn; rewrite List.map_app; apply List.in_app_iff; right; left; reflexivity.
Qed.

Lemma combine_fst_eq : forall {X Y : Type} (xs : list X) (ys : list Y), List.length xs = List.length ys ->
    List.map fst (List.combine xs ys) = xs.
Proof. induction xs as [| x xs IH]; intros [| y ys] H; cbn in *; try discriminate; [ reflexivity | rewrite IH; auto ]. Qed.

Lemma combine_snd_eq : forall {X Y : Type} (xs : list X) (ys : list Y), List.length xs = List.length ys ->
    List.map snd (List.combine xs ys) = ys.
Proof. induction xs as [| x xs IH]; intros [| y ys] H; cbn in *; try discriminate; [ reflexivity | rewrite IH; auto ]. Qed.

(** The fields of a record view after the fields [fs1]: their names and
    kinds. *)
Lemma combine_app_split : forall (fl : list String.string) (gs : list carg) fs1 fs2,
    List.length fl = List.length gs -> List.combine fl gs = fs1 ++ fs2 ->
    fl = List.map fst fs1 ++ List.map fst fs2 /\ gs = List.map snd fs1 ++ List.map snd fs2.
Proof.
  intros * Hl E; split.
  - rewrite <- List.map_app, <- E; symmetry; apply combine_fst_eq; exact Hl.
  - rewrite <- List.map_app, <- E; symmetry; apply combine_snd_eq; exact Hl.
Qed.

(** The number of steps of a leaf path. *)
Fixpoint leaf_size (l : leaf_path) : nat :=
  match l with
  | leaf_self _ _ => 0
  | leaf_pi _ l => S (leaf_size l)
  | leaf_proj _ _ l => S (leaf_size l)
  end.

Lemma leaf_size_wk : forall l φ, leaf_size (leaf_wk φ l) = leaf_size l.
Proof. induction l; intros; cbn; auto. Qed.

Lemma leaf_mem_wk : forall l φ, leaf_mem (leaf_wk φ l) = leaf_mem l.
Proof. induction l; intros; cbn; auto. Qed.

(** Every leaf path of a shape of a group is the group's own: read as its
    own container, a group has every recursive result of its own, when its
    table is coherent, its record views' fields are distinct and as many
    as their one constructor's arguments, and every shape ends in a
    member. *)
Lemma leaf_in_own : forall D, leaves_coherent D ->
    (forall j Mj qr Is fl, ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
       List.NoDup fl /\ exists c gs, im_cons Mj = (c, gs) :: nil /\ List.length fl = List.length gs) ->
    (forall j Mj qr Is fl c gs1 t gs2, ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
       im_cons Mj = (c, gs1 ++ ca_rec t :: gs2) :: nil -> exists M, ind_member D (ptyp_mem t) = Some M) ->
    forall t m l, (exists M, ind_member D (ptyp_mem t) = Some M) ->
      In l (shape_leaves (rv_leaves D) m t) -> leaf_in D t l = true.
Proof.
  intros D Hc Hrv Hfm.
  enough (H : forall n l, leaf_size l < n -> forall t m, (exists M, ind_member D (ptyp_mem t) = Some M) ->
                In l (shape_leaves (rv_leaves D) m t) -> leaf_in D t l = true)
    by (intros t m l HM Hin; exact (H (S (leaf_size l)) l ltac:(lia) t m HM Hin)).
  induction n as [| n IH]; intros l Hs t m [M HM] Hin; [ lia |].
  destruct t as [j Ps | B t1]; cbn [ptyp_mem] in HM; cbn [shape_leaves] in Hin.
  - destruct (rv_leaves D j) as [ls |] eqn:Hr.
    + (** A record view: a projection of one of its recursive fields. *)
      apply List.in_map_iff in Hin as (l0 & <- & Hl0).
      rewrite leaf_size_wk in Hs; rewrite leaf_in_wk.
      destruct (im_is_rview M) eqn:Hm; [| rewrite (rv_leaves_not_rview _ _ _ HM Hm) in Hr; discriminate Hr ].
      unfold im_is_rview in Hm; destruct (im_head M) as [| | qr Is fl] eqn:Hh; try discriminate Hm.
      destruct (Hrv _ _ _ _ _ HM Hh) as (Hnd & c & gs & Hcs & Hlen).
      rewrite (Hc _ _ _ _ _ _ _ HM Hh Hcs) in Hr; injection Hr as <-.
      destruct (fields_leaves_in _ _ _ _ Hl0) as (fs1 & f & t1 & fs2 & l1 & Hfs & -> & Hl1).
      cbn [leaf_in leaf_size] in Hs |- *; rewrite HM, Hh, Hcs, Hfs.
      rewrite find_name_split by (rewrite <- Hfs, combine_fst_eq by exact Hlen; exact Hnd).
      apply (IH l1 ltac:(lia) t1 (List.length (nil ++ fields_args fs1))); [| exact Hl1 ].
      assert (Hgs : gs = List.map snd fs1 ++ ca_rec t1 :: List.map snd fs2)
        by (rewrite <- (combine_snd_eq fl gs Hlen), Hfs, List.map_app; reflexivity).
      rewrite Hgs in Hcs; exact (Hfm _ _ _ _ _ _ _ _ _ HM Hh Hcs).
    + (** A member with a block. *)
      destruct Hin as [<- | []]; cbn [leaf_in]; rewrite HM.
      destruct (im_is_rview M) eqn:Hm; [| reflexivity ].
      unfold im_is_rview in Hm; destruct (im_head M) as [| | qr Is fl] eqn:Hh; try discriminate Hm.
      destruct (Hrv _ _ _ _ _ HM Hh) as (_ & c & gs & Hcs & _).
      rewrite (Hc _ _ _ _ _ _ _ HM Hh Hcs) in Hr; discriminate Hr.
  - apply List.in_map_iff in Hin as (l1 & <- & Hl1); cbn [leaf_in leaf_size] in Hs |- *.
    exact (IH l1 ltac:(lia) t1 _ (ex_intro _ M HM) Hl1).
Qed.

(** At rank [0] below [1], every argument may be nested through. *)
Lemma cargs_nest_ok_zero : forall D D' gs' gs, cargs_nest_ok D D' (fun _ => 0) 1 gs' gs.
Proof.
  intros D D'; induction gs' as [| g' gs' IH]; intros gs; [ destruct gs; cbn; auto |].
  destruct gs as [| g gs]; [ destruct g'; cbn; auto |].
  destruct g', g; cbn; auto.
Qed.

(** The recursive results along the leaf paths [ls] of an argument
    recursive in both: the next of the container's at a path of the
    container's, the group's eliminator [ih] at one nested through. *)
Fixpoint wrap_leaves (D' : ind_decl) (t' : ptyp) (ls : list leaf_path) (ihs : list exp) (r' nr' : nat) : list exp :=
  match ls, ihs with
  | l :: ls', ih :: ihs' =>
      if leaf_in D' t' l then a_var (nr' - 1 - r') :: wrap_leaves D' t' ls' ihs' (S r') nr'
      else ih :: wrap_leaves D' t' ls' ihs' r' nr'
  | _, _ => nil
  end.

(** The number of the leaf paths [ls] that are the container's. *)
Definition leaves_in_count (D' : ind_decl) (t' : ptyp) (ls : list leaf_path) : nat :=
  List.length (List.filter (leaf_in D' t') ls).

(** The number of the leaf paths of the arguments [gs] of the group [D]
    that are the container's [D'], whose constructor has the arguments
    [gs']: the recursive results a branch of the container's binds. *)
Fixpoint cargs_nin (D D' : ind_decl) (gs' gs : list carg) : nat :=
  match gs', gs with
  | ca_rec t' :: gs1', ca_rec t :: gs1 => leaves_in_count D' t' (shape_leaves (rv_leaves D) 0 t) + cargs_nin D D' gs1' gs1
  | _ :: gs1', _ :: gs1 => cargs_nin D D' gs1' gs1
  | _, _ => 0
  end.

Fixpoint wrap_ihs (D' D : ind_decl) (gs' gs : list carg) (ihs : list exp) (r' nr' : nat) : list exp :=
  match gs', gs with
  | ca_rec t' :: gs1', ca_rec t :: gs1 =>
      let ls := shape_leaves (rv_leaves D) 0 t in
      wrap_leaves D' t' ls (List.firstn (List.length ls) ihs) r' nr' ++
        wrap_ihs D' D gs1' gs1 (List.skipn (List.length ls) ihs) (leaves_in_count D' t' ls + r') nr'
  | ca_arg _ :: gs1', ca_rec t :: gs1 =>
      let n := List.length (shape_leaves (rv_leaves D) 0 t) in
      List.firstn n ihs ++ wrap_ihs D' D gs1' gs1 (List.skipn n ihs) r' nr'
  | _ :: gs1', ca_arg _ :: gs1 => wrap_ihs D' D gs1' gs1 ihs r' nr'
  | _, _ => nil
  end.

(** The branch of the container's constructor [c] with arguments [gs'], of
    the container's group [D'], the view's member [Mv] and its block's
    branches [Bs], under the context of the eliminator; [nn] non-uniform
    parameters. *)
Definition wrap_br (pq : qname) (D D' : ind_decl) (Us : list exp) (Bks : list eblock)
    (Mv : imember) (Bs : list (string * nat * exp)) (c : string) (gs' : list carg) : (string * nat * exp)%type :=
  let nn := im_nn Mv in
  let na := List.length gs' in
  let nr' := cargs_nrec D' gs' in
  let n' := (nn + na + nr')%nat in
  let gs := match ind_con Mv c with Some gs => gs | None => gs' end in
  let B := match brs_lookup Bs c with Some (_, B) => B | None => a_True end in
  let Us' := List.map (fun U => U[wk_shiftn n']ʷ) Us in
  let nvars := vars_from (nr' + na) nn in
  let avars := vars_from nr' na in
  let ihs := elim_ihs pq D (Some pq) Us' (blocks_wk Bks (wk_shiftn n')) (sb_of_list (sb_of_wk (wk_shiftn n')) (Us' ++ nvars)) nn gs avars in
  (c, n', B[sb_of_list (sb_of_wk (wk_shiftn n')) (nvars ++ avars ++ wrap_ihs D' D gs' gs ihs 0 nr')]).

(** The members [vm] lists of [D] are those of the container's group [D']
    at the view's arguments, as the group's declaration says: as many,
    each a member of [D], with as many non-uniform parameters, the same
    constructors, and the arguments of each as the container's, classified
    for [D]. *)
Record vwrap_ok (D D' : ind_decl) (vm : list nat) : Prop := mk_vwrap_ok
  { (** [vm] lists one member of [D] per member of the container's group. *)
    vwrap_ok_length : List.length vm = List.length (ind_members D')
  (** Each member [vm] lists is a member of [D] with as many non-uniform
      parameters as the container's, the same constructors, and arguments
      corresponding to the container's ([cargs_corr]). *)
  ; vwrap_ok_members : forall i' Mi' v, ind_member D' i' = Some Mi' -> List.nth_error vm i' = Some v ->
      exists Mv, ind_member D v = Some Mv /\ im_nn Mv = im_nn Mi' /\
        List.map fst (im_cons Mv) = List.map fst (im_cons Mi') /\
        (forall c gs' gs, In (c, gs') (im_cons Mi') -> ind_con Mv c = Some gs -> cargs_corr vm gs' gs) }.

(** The container's blocks: one per member of the container's group [D']
    that has a block. *)
Definition vwrap_block (pq : qname) (D D' : ind_decl) (vm : list nat) (Us : list exp) (Bks : list eblock)
    (i' : nat) (Mi' : imember) : eblock :=
  let v := List.nth i' vm 0 in
  match List.nth_error Bks v, ind_member D v with
  | Some (eb_mk nm _ A Bs), Some Mv =>
      eb_mk nm None A (List.map (fun cg => wrap_br pq D D' Us Bks Mv Bs (fst cg) (snd cg)) (im_cons Mi'))
  | _, _ => eb_mk 0 None a_True nil
  end.

(** The container's blocks for its members [ms], from the member [i'] on. *)
Fixpoint vwrap_from (pq : qname) (D D' : ind_decl) (vm : list nat) (Us : list exp) (Bks : list eblock)
    (i' : nat) (ms : list imember) : list eblock :=
  match ms with
  | nil => nil
  | Mi' :: ms' => vwrap_block pq D D' vm Us Bks i' Mi' :: vwrap_from pq D D' vm Us Bks (S i') ms'
  end.

(** The members of a group that have a block: all but the record views,
    which come last. *)
Definition ind_bmembers (D : ind_decl) : list imember := List.firstn (ind_nblk D) (ind_members D).

(** The blocks of the container's eliminator that the eliminator at a view
    reads as: one per member of the container's group [D'] that has a
    block. *)
Definition vwrap (pq : qname) (D D' : ind_decl) (vm : list nat) (Us : list exp) (Bks : list eblock) : list eblock :=
  vwrap_from pq D D' vm Us Bks 0 (ind_bmembers D').

(** There are at most as many members with a block as members. *)
Lemma ind_nblk_le : forall D, ind_nblk D <= List.length (ind_members D).
Proof. intros; unfold ind_nblk; apply List.filter_length_le. Qed.

(** A member with a block is a member. *)
Lemma ind_bmembers_member : forall D k M, List.nth_error (ind_bmembers D) k = Some M ->
    ind_member D k = Some M /\ k < ind_nblk D.
Proof.
  intros * H; unfold ind_bmembers, ind_member in *.
  rewrite List.nth_error_firstn in H; destruct (Nat.ltb_spec k (ind_nblk D)); [ split; [ exact H | lia ] | discriminate ].
Qed.

Lemma length_ind_bmembers : forall D, List.length (ind_bmembers D) = ind_nblk D.
Proof. intros; unfold ind_bmembers; rewrite List.length_firstn; pose proof (ind_nblk_le D); lia. Qed.

Lemma nth_error_vwrap_from : forall pq D D' vm Us Bks ms s k b,
    List.nth_error (vwrap_from pq D D' vm Us Bks s ms) k = Some b ->
    exists Mi', List.nth_error ms k = Some Mi' /\ b = vwrap_block pq D D' vm Us Bks (s + k) Mi'.
Proof.
  induction ms as [| M ms IH]; intros * H; [ destruct k; discriminate |].
  destruct k as [| k]; cbn in H.
  - injection H as <-; exists M; rewrite Nat.add_0_r; auto.
  - destruct (IH _ _ _ H) as (Mi' & HM & ->); exists Mi'; split; [ exact HM | f_equal; lia ].
Qed.

Lemma length_vwrap : forall pq D D' vm Us Bks, List.length (vwrap pq D D' vm Us Bks) = List.length (ind_bmembers D').
Proof.
  intros; unfold vwrap; generalize 0; induction (ind_bmembers D'); intros; cbn; [ reflexivity | f_equal; apply IHl ].
Qed.

(** The sort of a declaration is a universe. *)
Definition ind_sort_univ (S : typ) : Prop := (exists i, S = Typeω@i) \/ (exists t, S = Type⟨t⟩).

(** The level of a small sort, and a level of none for a large one. *)
Definition ind_sort_lvl (S : typ) : exp :=
  match S with
  | a_univ t => t
  | _ => a_llit (0, 0)
  end.

(** ** Module Variables

    [exp_mvc d M]: every module variable of [M] is bound by one of the [d]
    binders above it inside the term, not free.  The parameters of a
    declaration are a telescope of assumptions, so their types have no free
    module variable; the typing rule of a declaration says so, which is what
    lets their instances at variables and at terms of variables coincide. *)

(** Every module variable of a term is bound by one of the [n] binders
    above it. *)
Fixpoint exp_mvc (n : nat) (M : exp) : Prop :=
  match M with
  | a_typ _ | a_level _ | a_llit _ | a_True | a_true | a_False => True
  | a_succl M | a_univ M => exp_mvc n M
  | a_maxl M N => exp_mvc n M /\ exp_mvc n N
  | a_exfalso A M => exp_mvc (S n) A /\ exp_mvc n M
  | a_ind _ _ | a_con _ _ _ | a_nlit _ | a_ntok => True
  | a_elim _ Us _ Bks M =>
      all_list (exp_mvc n) Us /\
      all_blocks (fun nm oZ A Bs => opt_all (exp_mvc (nm - 1 + n)) oZ /\ exp_mvc (nm + n) A /\
                                    all_brs (fun k B => exp_mvc (k + n) B) Bs) Bks /\ exp_mvc n M
  | a_pi A B | a_fn A B => exp_mvc n A /\ exp_mvc (S n) B
  | a_app M N => exp_mvc n M /\ exp_mvc n N
  | a_var _ => True
  | a_let b B => bnd_mvc n b /\ exp_mvc (S n) B
  | a_mem H _ => modexp_mvc n H
  | a_record _ => True
  | a_tuple T fs => exp_mvc n T /\ all_list (fun f => exp_mvc n (snd f)) fs
  | a_proj _ M => exp_mvc n M
  end
with modexp_mvc (n : nat) (H : modexp) : Prop :=
  match H with
  | me_unit _ => True
  | me_var x => x < n
  | me_mem H _ => modexp_mvc n H
  | me_app H N => modexp_mvc n H /\ exp_mvc n N
  | me_lit U => gunit_mvc n U
  end
with bnd_mvc (n : nat) (b : bnd) : Prop :=
  match b with
  | b_def oA M => match oA with Some A => exp_mvc n A | None => True end /\ exp_mvc n M
  | b_mod U => gunit_mvc n U
  end
with gunit_mvc (n : nat) (U : gunit) : Prop :=
  match U with
  | gu_mk Δ D =>
      (fix tele_mvc (Δ : list centry) : Prop :=
         match Δ with
         | nil => True
         | e :: Δ' => centry_mvc (List.length Δ' + n) e /\ tele_mvc Δ'
         end) Δ /\
      moddef_mvc (List.length Δ + n) D
  end
with moddef_mvc (n : nat) (D : moddef) : Prop :=
  match D with
  | md_body sm Φ => gmod_mvc n Φ
  | md_alias E => modexp_mvc n E
  end
with gmod_mvc (n : nat) (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ _ E => gmod_mvc n Φ /\ gentry_mvc (gm_binders Φ + n) E
  | gm_open Φ H _ => gmod_mvc n Φ /\ modexp_mvc (gm_binders Φ + n) H
  end
with gentry_mvc (n : nat) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B => exp_mvc n A /\ match B with Some M => exp_mvc n M | None => True end
  | ge_mod _ U => gunit_mvc n U
  | ge_ind _ _ _ D Φ => gmod_mvc (ind_nu D + n) Φ
  | ge_def_mod _ A M U => exp_mvc n A /\ exp_mvc n M /\ gunit_mvc n U
  | ge_record _ _ R Φ => gmod_mvc (S (List.length (record_params R)) + n) Φ
  end
with centry_mvc (n : nat) (e : centry) : Prop :=
  match e with
  | ce_ass A => exp_mvc n A
  | ce_def A M => exp_mvc n A /\ exp_mvc n M
  | ce_mod U => gunit_mvc n U
  | ce_dm A M U => exp_mvc n A /\ exp_mvc n M /\ gunit_mvc n U
  end.

(** A telescope whose types have no free module variable. *)
Definition ctx_mvc (Δ : ctx) : Prop := List.Forall (centry_mvc 0) Δ.

(** A declaration whose parameters' types, sort, views' uniform arguments
    and constructors' argument types have no free module variable. *)
Definition carg_mvc (g : carg) : Prop :=
  match g with
  | ca_arg A => exp_mvc 0 A
  | ca_rec t => List.Forall (exp_mvc 0) (ptyp_doms t) /\ List.Forall (exp_mvc 0) (ptyp_ps t)
  end.

(** A view's uniform arguments, and a record view's instance, have no free
    module variable. *)
Definition mhead_mvc (h : mhead) : Prop :=
  match h with
  | mh_decl _ => True
  | mh_view _ _ Is _ => List.Forall (exp_mvc 0) Is
  | mh_record _ Is _ => List.Forall (exp_mvc 0) Is
  end.

(** No free module variable anywhere in a group. *)
Record decl_mvc (D : ind_decl) : Prop := mk_decl_mvc
  { (** In the uniform parameters' types. *)
    decl_mvc_uparams : ctx_mvc (ind_uparams D)
  (** In the sort. *)
  ; decl_mvc_sort : exp_mvc 0 (ind_sort D)
  (** In each member's non-uniform parameters, view arguments and
      constructor arguments. *)
  ; decl_mvc_members : forall k M, ind_member D k = Some M ->
      ctx_mvc (im_nparams M) /\ mhead_mvc (im_head M) /\
      (forall c gs, In (c, gs) (im_cons M) -> List.Forall carg_mvc gs) }.

(** No free module variable anywhere in a record declaration, as
    [decl_mvc] for a group: so its value's type, the type former at the
    parameters as variables, is a type over them ([record_self]). *)
Record record_mvc (R : record_decl) : Prop := mk_record_mvc
  { (** No parameter's type has a free module variable. *)
    params_mvc : ctx_mvc (record_params R)
  (** The sort has no free module variable. *)
  ; sort_mvc : exp_mvc 0 (record_sort R)
  (** No field's type has a free module variable. *)
  ; fields_mvc : forall k f T, List.nth_error (record_fields R) k = Some (f, T) -> exp_mvc 0 T }.

(** The types are read off a declaration once; [simpl] leaves them
    folded, and the lemmas below compute with them. *)
#[global] Arguments ind_ty : simpl never.
#[global] Arguments con_ty : simpl never.
#[global] Arguments cargs_ctx : simpl never.
#[global] Arguments tele_insts : simpl never.
#[global] Arguments vars_from : simpl never.
#[global] Arguments elim_mctx : simpl never.
#[global] Arguments elim_bctx : simpl never.
#[global] Arguments elim_bty : simpl never.
#[global] Arguments ihs_sub : simpl never.
#[global] Arguments ind_mty : simpl never.

(** ** Facts About the Types of a Declaration *)

Lemma cons_lookup_in : forall cs c gs, cons_lookup cs c = Some gs -> In (c, gs) cs.
Proof.
  induction cs as [| [c' gs'] cs IH]; cbn; intros c gs H; [ discriminate |].
  destruct (String.eqb_spec c c') as [-> | _]; [ injection H as ->; left; reflexivity | right; auto ].
Qed.

Lemma cons_lookup_of_in : forall cs c gs, In (c, gs) cs -> exists gs', cons_lookup cs c = Some gs'.
Proof.
  induction cs as [| [c' gs'] cs IH]; cbn; intros c gs H; [ destruct H |].
  destruct (String.eqb_spec c c') as [-> | Hne]; [ eauto |].
  destruct H as [H | H]; [ injection H as -> ->; contradiction | eauto ].
Qed.

Lemma brs_names_con : forall cs Bs c n B,
    brs_names cs Bs -> In (c, n, B) Bs -> exists gs, cons_lookup cs c = Some gs.
Proof.
  intros * Hn Hin.
  assert (Hc : In c (List.map fst cs)) by (rewrite Hn; apply List.in_map_iff; exists (c, n, B); auto).
  apply List.in_map_iff in Hc as ([c' gs] & Hc & Hin'); cbn in Hc; subst c'.
  exact (cons_lookup_of_in _ _ _ Hin').
Qed.

Lemma length_cargs_ctx_aux : forall pq D nn gs pat, List.length (cargs_ctx_aux pq D nn pat gs) = List.length gs.
Proof. induction gs as [| [] gs IH]; intros; cbn; rewrite ?length_app, ?IH; cbn; lia. Qed.

Lemma length_cargs_ctx : forall pq D M gs, List.length (cargs_ctx pq D M gs) = List.length gs.
Proof. intros; apply length_cargs_ctx_aux. Qed.

Lemma length_leaves_ctx : forall nn As Us na pat ls j,
    List.length (leaves_ctx nn As Us na pat j ls) = List.length ls.
Proof. induction ls as [| l ls IH]; intros; cbn; rewrite ?length_app, ?IH; cbn; lia. Qed.

Lemma length_ihs_ctx_aux : forall D nn As Us na gs pat j,
    List.length (ihs_ctx_aux (rv_leaves D) nn As Us na pat j gs) = cargs_nrec D gs.
Proof.
  induction gs as [| [] gs IH]; intros; cbn; rewrite ?length_app, ?IH, ?length_leaves_ctx; cbn; [ reflexivity | reflexivity |].
  rewrite (length_shape_leaves _ _ _ 0); lia.
Qed.

Lemma length_elim_mctx : forall pq D k M Us, List.length (elim_mctx pq D k M Us) = S (im_nn M).
Proof. intros; unfold elim_mctx; cbn; rewrite length_tele_sub; reflexivity. Qed.

Lemma length_elim_bctx : forall pq D M gs As Us,
    List.length (elim_bctx pq D M gs As Us) = (cargs_nrec D gs + List.length gs + im_nn M)%nat.
Proof.
  intros; unfold elim_bctx; rewrite !length_app, length_ihs_ctx_aux, !length_tele_sub, length_cargs_ctx.
  unfold im_nn; lia.
Qed.

Lemma length_elim_ihs : forall pq D oq Us Bks σ m gs As,
    List.length As = List.length gs -> List.length (elim_ihs pq D oq Us Bks σ m gs As) = cargs_nrec D gs.
Proof.
  intros pq D oq Us Bks σ m gs; revert σ m.
  induction gs as [| [] gs IH]; intros σ m [| N As] Hl; cbn in *; try discriminate; try reflexivity.
  - apply IH; lia.
  - rewrite length_app, length_map, (length_shape_leaves _ _ _ 0), IH by lia; reflexivity.
Qed.

Lemma length_vars_from : forall k n, List.length (vars_from k n) = n.
Proof. intros; unfold vars_from; rewrite length_map, length_rev, length_seq; reflexivity. Qed.

Lemma length_tele_insts_aux : forall Δr σ Ms,
    List.Forall (fun e => exists A, e = ce_ass A) Δr ->
    List.length (tele_insts_aux Δr σ Ms) = Nat.min (List.length Δr) (List.length Ms).
Proof.
  intros Δr σ Ms Hr; revert σ Ms.
  induction Hr as [| e Δr [A ->] Hr IH]; intros σ [| M Ms]; cbn; try reflexivity.
  rewrite IH; reflexivity.
Qed.

Lemma length_tele_insts : forall Δ σ Ms,
    List.Forall (fun e => exists A, e = ce_ass A) Δ ->
    List.length (tele_insts Δ σ Ms) = Nat.min (List.length Δ) (List.length Ms).
Proof.
  intros; unfold tele_insts; rewrite length_tele_insts_aux, length_rev; [ reflexivity |].
  apply Forall_rev; assumption.
Qed.

Lemma cargs_ctx_aux_ass : forall pq D nn gs pat, List.Forall (fun e => exists A, e = ce_ass A) (cargs_ctx_aux pq D nn pat gs).
Proof.
  induction gs as [| [] gs IH]; intros; cbn; [ constructor | |]; apply List.Forall_app; split; eauto.
Qed.
