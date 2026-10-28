From Stdlib Require Import List String Bool ZArith.
From Stdlib Require Import OrderedType OrderedTypeEx FMapAVL FMapFacts FSetAVL FSetFacts.
From Stdlib Require Orders OrdersEx OrdersAlt.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.System Require Import Command.
Import ListNotations.

(** * The Fast Global Context

    The global context the extracted checker runs on: the filed units in
    one balanced map keyed by their whole paths ([funits]), the open frames
    each with the trie of its body so far ([fstack]), and the module bodies
    in a fast copy of the module layer ([funit], [ftrie], [fentry]) whose
    members are found by name in a balanced map, one lookup per component
    of a path.

    Only the module layer is copied: terms, context entries, declarations
    and module expressions are Core's ([exp], [centry], [ind_decl],
    [record_decl], [modexp]).  Each body is stored once, as a trie; no Core
    [gmod] is kept next to it.

    The Core context is never built at run time.  It appears in types and
    proofs only:
    - [tr_unit] and the like translate Core data into fast data; the
      refinement [units_rep s Θ] says that [s] finds the translation of what
      [gds_lookup Θ] finds;
    - [dec_unit] and the like decode fast data back into Core data, in
      types only; on canonical data ([canon_unit]: no local open, no name
      declared twice) decoding undoes the translation ([dec_tr_unit]).

    Every lookup of [Core.Syntactic.Members] has a twin here over fast data
    with a lemma stating that, on a translation, it finds the translation of
    what the Core lookup finds ([ft_entry_ok], [fgc_entry_ok], …). *)

(** ** Balanced Maps *)

(** Maps keyed by member names, compared by [String.compare] (native once
    extracted, by the directive of [Entrypoint]). *)
Module SMap := FMapAVL.Make OrderedTypeEx.String_as_OT.
(** The plain trees of [SMap], which a nested inductive can hold *)
Module SRaw := SMap.Raw.
(** Their lemmas *)
Module SP := SRaw.Proofs.

(** [find] after [add], at a search tree. *)
Lemma sraw_find_add {A} (m : SRaw.tree A) x e y :
  SRaw.bst m -> SRaw.find y (SRaw.add x e m) = if String.eqb y x then Some e else SRaw.find y m.
Proof.
  intros Hb; rewrite SP.add_find by exact Hb.
  destruct (OrderedTypeEx.String_as_OT.compare y x) as [Hl | He | Hg]; cbn.
  - destruct (String.eqb_spec y x) as [-> |]; [ | reflexivity ].
    exfalso; exact (OrderedTypeEx.String_as_OT.lt_not_eq Hl eq_refl).
  - unfold OrderedTypeEx.String_as_OT.eq in He; subst; rewrite String.eqb_refl; reflexivity.
  - destruct (String.eqb_spec y x) as [-> |]; [ | reflexivity ].
    exfalso; exact (OrderedTypeEx.String_as_OT.lt_not_eq Hg eq_refl).
Qed.

(** Nothing is found in the empty tree. *)
Lemma sraw_find_leaf {A} y : SRaw.find y (SRaw.Leaf A) = None.
Proof. reflexivity. Qed.

(** The components of paths are compared by [String.compare], which runs
    natively once extracted (the directive of [Entrypoint]); it is the
    order of [OrdersEx.String_as_OT], whose lemmas the proofs use.
    [OrdersEx.String_as_OT.compare] itself is a definition of its own,
    which would extract to a walk over characters. *)
Lemma str_compare_eq : forall x y, String.compare x y = OrdersEx.String_as_OT.compare x y.
Proof. induction x as [| a x IH]; intros [| b y]; cbn; try reflexivity; rewrite IH; reflexivity. Qed.

Lemma str_compare_spec : forall x y, CompSpec eq OrdersEx.String_as_OT.lt x y (String.compare x y).
Proof. intros; rewrite str_compare_eq; apply OrdersEx.String_as_OT.compare_spec. Qed.

(** Paths, compared lexicographically, component by component. *)
Lemma str_cmp_refl : forall x, String.compare x x = Eq.
Proof.
  intros x; destruct (str_compare_spec x x) as [_ | H | H];
    [ reflexivity | elim (StrictOrder_Irreflexive _ H) | elim (StrictOrder_Irreflexive _ H) ].
Qed.

(** [SRaw.find], written directly: one [String.compare] per node, with no
    [OrderedType.Compare] built and matched. *)
Fixpoint sfind {A} (x : string) (m : SRaw.tree A) : option A :=
  match m with
  | SRaw.Leaf _ => None
  | SRaw.Node l y d r _ =>
      match String.compare x y with
      | Eq => Some d
      | Lt => sfind x l
      | Gt => sfind x r
      end
  end.

(** It is [SRaw.find]. *)
Lemma sfind_ok {A} x (m : SRaw.tree A) : sfind x m = SRaw.find x m.
Proof.
  induction m as [| l IHl y d r IHr h]; [ reflexivity |]; cbn [sfind SRaw.find].
  destruct (OrderedTypeEx.String_as_OT.compare x y) as [E | E | E].
  - apply OrderedTypeEx.String_as_OT.cmp_lt in E; change (String.compare x y = Lt) in E; rewrite E; exact IHl.
  - cbv [OrderedTypeEx.String_as_OT.eq] in E; subst; rewrite str_cmp_refl; reflexivity.
  - apply OrderedTypeEx.String_as_OT.cmp_lt in E; change (String.compare y x = Lt) in E.
    rewrite String.compare_antisym, E; exact IHr.
Qed.

(** The order of unit paths *)
Module PathOrd <: Orders.OrderedType.
  Definition t := list string.
  Definition eq := @Logic.eq t.
  #[global] Instance eq_equiv : Equivalence eq := _.

  (** Lexicographic: the first component that differs decides, and a
      proper prefix comes first. *)
  Fixpoint compare (p q : t) : comparison :=
    match p, q with
    | [], [] => Eq
    | [], _ :: _ => Lt
    | _ :: _, [] => Gt
    | x :: p', y :: q' =>
        match String.compare x y with
        | Eq => compare p' q'
        | c => c
        end
    end.

  (** [p] comes before [q] *)
  Definition lt (p q : t) : Prop := compare p q = Lt.

  (** A path is equal to itself. *)
  Lemma compare_refl : forall p, compare p p = Eq.
  Proof. induction p as [| x p IH]; cbn; [ reflexivity | rewrite str_cmp_refl; exact IH ]. Qed.

  (** Paths compared equal are equal. *)
  Lemma compare_eq : forall p q, compare p q = Eq -> p = q.
  Proof.
    induction p as [| x p IH]; intros [| y q]; cbn; try discriminate; [ reflexivity |].
    destruct (str_compare_spec x y) as [-> | _ | _]; try discriminate.
    intros H; f_equal; auto.
  Qed.

  (** Swapping the paths swaps the result. *)
  Lemma compare_antisym : forall p q, compare q p = CompOpp (compare p q).
  Proof.
    induction p as [| x p IH]; intros [| y q]; cbn; try reflexivity.
    destruct (str_compare_spec x y) as [-> | H | H].
    - rewrite str_cmp_refl; apply IH.
    - destruct (str_compare_spec y x) as [-> | H' | H'];
        [ elim (StrictOrder_Irreflexive _ H) | elim (StrictOrder_Irreflexive _ (transitivity H H')) | reflexivity ].
    - destruct (str_compare_spec y x) as [-> | H' | H'];
        [ elim (StrictOrder_Irreflexive _ H) | reflexivity | elim (StrictOrder_Irreflexive _ (transitivity H H')) ].
  Qed.

  (** The order is transitive. *)
  Lemma lt_trans : forall p q r, lt p q -> lt q r -> lt p r.
  Proof.
    unfold lt; induction p as [| x p IH]; intros [| y q] [| z r]; cbn; try discriminate; auto.
    destruct (str_compare_spec x y) as [-> | Hxy | Hxy]; try discriminate;
      destruct (str_compare_spec y z) as [-> | Hyz | Hyz]; try discriminate.
    - destruct (str_compare_spec z z) as [_ | H | H]; [ apply IH | elim (StrictOrder_Irreflexive _ H) .. ].
    - destruct (str_compare_spec y z) as [-> | H | H];
        [ elim (StrictOrder_Irreflexive _ Hyz) | reflexivity | elim (StrictOrder_Irreflexive _ (transitivity H Hyz)) ].
    - destruct (str_compare_spec x z) as [-> | H | H];
        [ elim (StrictOrder_Irreflexive _ Hxy) | reflexivity | elim (StrictOrder_Irreflexive _ (transitivity H Hxy)) ].
    - destruct (str_compare_spec x z) as [-> | H | H]; [| reflexivity |].
      + elim (StrictOrder_Irreflexive _ (transitivity Hxy Hyz)).
      + elim (StrictOrder_Irreflexive _ (transitivity (transitivity Hxy Hyz) H)).
  Qed.

  #[global] Instance lt_strorder : StrictOrder lt.
  Proof. split; [ intros p H; unfold lt in H; rewrite compare_refl in H; discriminate | exact lt_trans ]. Qed.

  #[global] Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. intros ? ? -> ? ? ->; reflexivity. Qed.

  (** [compare] decides the order. *)
  Lemma compare_spec : forall p q, CompSpec eq lt p q (compare p q).
  Proof.
    intros p q; destruct (compare p q) eqn:E; constructor.
    - exact (compare_eq _ _ E).
    - exact E.
    - unfold lt; rewrite compare_antisym, E; reflexivity.
  Qed.

  (** A path compared greater than another comes after it. *)
  Lemma compare_gt_lt : forall p q, compare p q = Gt -> lt q p.
  Proof. intros p q E; unfold lt; rewrite compare_antisym, E; reflexivity. Qed.

  Definition eq_dec : forall p q : t, {p = q} + {p <> q} := path_eq_dec.
End PathOrd.

(** The same order in the interface [FMapAVL] and [FSetAVL] take, written
    directly: its [compare] is one match on [PathOrd.compare], no generic
    wrapper (as [OrdersAlt.Backport_OT] would add) in the comparisons of
    the maps. *)
Module PathOT <: OrderedType.OrderedType.
  Definition t := list string.
  Definition eq := @Logic.eq t.
  Definition lt := PathOrd.lt.
  Definition eq_refl : forall x : t, eq x x := @Logic.eq_refl t.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := @Logic.eq_sym t.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := @Logic.eq_trans t.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z := PathOrd.lt_trans.

  (** A path does not come before itself. *)
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y H E; unfold eq in E; subst y; unfold lt, PathOrd.lt in H; rewrite PathOrd.compare_refl in H; discriminate.
  Qed.

  (** [PathOrd.compare], with its proof carried in the result *)
  Definition compare (x y : t) : OrderedType.Compare lt eq x y :=
    match PathOrd.compare x y as c return PathOrd.compare x y = c -> OrderedType.Compare lt eq x y with
    | Eq => fun E => OrderedType.EQ (PathOrd.compare_eq x y E)
    | Lt => fun E => OrderedType.LT E
    | Gt => fun E => OrderedType.GT (PathOrd.compare_gt_lt x y E)
    end Logic.eq_refl.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := path_eq_dec.
End PathOT.
(** Maps keyed by unit paths *)
Module PM := FMapAVL.Make PathOT.
(** Their facts *)
Module PMF := FMapFacts.WFacts_fun PathOT PM.

(** [find] after [add] in a map of paths. *)
Lemma pm_find_add : forall {A} (m : PM.t A) fp fq x,
    PM.find fq (PM.add fp x m) = if path_beq fq fp then Some x else PM.find fq m.
Proof.
  intros; rewrite PMF.add_o; destruct (PathOT.eq_dec fp fq) as [E | E]; unfold PathOT.eq, PathOrd.eq in E.
  - subst; rewrite path_beq_refl; reflexivity.
  - rewrite path_beq_false by congruence; reflexivity.
Qed.

(** [PM.find], written directly over the tree: one [PathOrd.compare] per
    node, with no [OrderedType.Compare] built and matched. *)
Fixpoint pfind {A} (x : path) (m : PM.Raw.tree A) : option A :=
  match m with
  | PM.Raw.Leaf _ => None
  | PM.Raw.Node l y d r _ =>
      match PathOrd.compare x y with
      | Eq => Some d
      | Lt => pfind x l
      | Gt => pfind x r
      end
  end.

(** It is [PM.find]. *)
Lemma pfind_ok {A} x (m : PM.t A) : pfind x (PM.this m) = PM.find x m.
Proof.
  unfold PM.find; generalize (PM.this m); clear m; intros m.
  induction m as [| l IHl y d r IHr h]; [ reflexivity |]; cbn [pfind PM.Raw.find].
  destruct (PathOT.compare x y) as [E | E | E].
  - change (PathOrd.compare x y = Lt) in E; rewrite E; exact IHl.
  - cbv [PathOT.eq] in E; subst; rewrite PathOrd.compare_refl; reflexivity.
  - change (PathOrd.compare y x = Lt) in E; rewrite PathOrd.compare_antisym, E; exact IHr.
Qed.

(** The key a path is filed under: the path reversed, so that two keys
    differ early (paths share their first components, [Prelude] and the
    like, much more often than their last). *)
Definition path_key (fp : path) : path := List.rev' fp.

(** Keys are equal exactly when paths are. *)
Lemma path_key_beq : forall fp fq, path_beq (path_key fq) (path_key fp) = path_beq fq fp.
Proof.
  intros fp fq; unfold path_key, List.rev'; rewrite <- (List.rev_alt fq), <- (List.rev_alt fp).
  destruct (path_beq fq fp) eqn:E.
  - apply path_beq_true in E as ->; apply path_beq_refl.
  - apply path_beq_false; intros Hr; apply (f_equal (@List.rev _)) in Hr.
    rewrite (List.rev_involutive fq), (List.rev_involutive fp) in Hr; subst.
    rewrite path_beq_refl in E; discriminate.
Qed.

(** A map of paths keyed by [path_key]: what it finds at [fp] *)
Definition pk_find {A} (fp : path) (m : PM.t A) : option A := pfind (path_key fp) (PM.this m).

(** Adding [x] at [fp] *)
Definition pk_add {A} (fp : path) (x : A) (m : PM.t A) : PM.t A := PM.add (path_key fp) x m.

(** [pk_find] after [pk_add] *)
Lemma pk_find_add : forall {A} (m : PM.t A) fp fq x,
    pk_find fq (pk_add fp x m) = if path_beq fq fp then Some x else pk_find fq m.
Proof.
  intros A m fp fq x; unfold pk_find, pk_add.
  rewrite (pfind_ok _ (PM.add _ _ m)), (pfind_ok _ m), pm_find_add, path_key_beq; reflexivity.
Qed.

(** Nothing is found in the empty map. *)
Lemma pk_find_empty : forall {A} fp, pk_find fp (PM.empty A) = None.
Proof. intros; unfold pk_find; rewrite pfind_ok; apply PMF.empty_o. Qed.

(** ** The Fast Module Layer *)

Inductive funit : Type :=
(** [fu_mk Δ D]: a unit with a closed body, as Core's
    [gu_mk Δ (md_body sm_closed …)]: its parameters and its body *)
| fu_mk : list centry -> fmoddef -> funit
(** Core's unit kept as it is: an alias ([gu_mk Δ (md_alias E)]), which
    has no body to look into, or a unit with an open body
    ([md_body sm_open]), which no filed unit or open frame has *)
| fu_core : gunit -> funit
with fmoddef : Type :=
(** A closed body, as a trie *)
| fmd_body : ftrie -> fmoddef
with ftrie : Type :=
(** [ft_mk m xs]: the members by name ([m]), and the order index [xs]: the
    names declared, newest first.  [xs] holds names only, never an
    entry. *)
| ft_mk : SRaw.tree fentry -> list string -> ftrie
with fentry : Type :=
(** Core's [ge_def b pv A oM] *)
| fe_def : bool -> bool -> exp -> option exp -> fentry
(** Core's [ge_mod pv U], the unit fast *)
| fe_mod : bool -> funit -> fentry
(** Core's [ge_ind pv pq k D Φ], the member's module a trie *)
| fe_ind : bool -> qname -> nat -> ind_decl -> ftrie -> fentry
(** Core's [ge_def_mod pv A M U], the unit fast *)
| fe_def_mod : bool -> exp -> exp -> funit -> fentry
(** Core's [ge_record pv p R Φ], the record's module a trie *)
| fe_record : bool -> qname -> record_decl -> ftrie -> fentry.

(** The members of a trie by name *)
Definition ft_map (t : ftrie) : SRaw.tree fentry := match t with ft_mk m _ => m end.
(** The order index of a trie: its names, newest first *)
Definition ft_names (t : ftrie) : list string := match t with ft_mk _ xs => xs end.

(** The empty body *)
Definition ft_empty : ftrie := ft_mk (SRaw.Leaf _) nil.

(** One more member: one [add] and one cons of its name. *)
Definition ft_ext (t : ftrie) (x : string) (e : fentry) : ftrie :=
  match t with ft_mk m xs => ft_mk (SRaw.add x e m) (x :: xs) end.

(** The member named [x]: the newest one of that name. *)
Definition ft_find (t : ftrie) (x : string) : option fentry := sfind x (ft_map t).

(** The body a path descends into through an entry, as [gm_entry] reads
    it: a submodule's body, an inductive type's or a record's module. *)
Definition fe_body (e : fentry) : option ftrie :=
  match e with
  | fe_mod _ (fu_mk _ (fmd_body t)) => Some t
  | fe_ind _ _ _ _ t => Some t
  | fe_record _ _ _ t => Some t
  | _ => None
  end.

(** The member at [ip]: one [find] per component, [gm_entry]'s twin. *)
Fixpoint ft_entry (t : ftrie) (ip : list string) {struct ip} : option fentry :=
  match ip with
  | nil => None
  | x :: ip' =>
      match ft_find t x with
      | None => None
      | Some e =>
          match ip' with
          | nil => Some e
          | _ :: _ => match fe_body e with Some t' => ft_entry t' ip' | None => None end
          end
      end
  end.

(** The parameters of a unit, [gu_params]'s twin *)
Definition fu_params (u : funit) : list centry :=
  match u with
  | fu_mk Δ _ => Δ
  | fu_core U => gu_params U
  end.

(** The body of a unit, the empty body for an alias, [gu_mod]'s twin *)
Definition fu_body (u : funit) : ftrie :=
  match u with
  | fu_mk _ (fmd_body t) => t
  | fu_core _ => ft_empty
  end.

(** Whether an entry is private, [ge_private]'s twin *)
Definition fe_private (e : fentry) : bool :=
  match e with
  | fe_def _ pv _ _ | fe_mod pv _ | fe_ind pv _ _ _ _ | fe_def_mod pv _ _ _ | fe_record pv _ _ _ => pv
  end.

(** ** Translation from Core

    The entries are added oldest first, so that the newest entry of a name
    is the one the map keeps, as in [gm_entry]; a local open adds nothing,
    as [gm_entry] skips it (and a filed or open-frame body has none). *)
Fixpoint tr_unit (U : gunit) : funit :=
  match U with
  | gu_mk Δ (md_body sm_closed Φ) => fu_mk Δ (fmd_body (tr_mod Φ))
  | _ => fu_core U
  end
with tr_mod (Φ : gmod) : ftrie :=
  match Φ with
  | gm_nil => ft_empty
  | gm_ext Φ' x E => ft_ext (tr_mod Φ') x (tr_entry E)
  | gm_open Φ' _ _ => tr_mod Φ'
  end
with tr_entry (E : gentry) : fentry :=
  match E with
  | ge_def b pv A oM => fe_def b pv A oM
  | ge_mod pv U => fe_mod pv (tr_unit U)
  | ge_ind pv pq k D Φ => fe_ind pv pq k D (tr_mod Φ)
  | ge_def_mod pv A M U => fe_def_mod pv A M (tr_unit U)
  | ge_record pv p R Φ => fe_record pv p R (tr_mod Φ)
  end.

(** ** Decoding to Core

    For types and statements only, never run: how a specification names
    the Core data that fast data stands for.  A trie's entries are decoded
    in place, then its body assembled along the order index. *)

(** The entries of a tree, decoded in place. *)
Fixpoint dec_tree_with (f : fentry -> gentry) (m : SRaw.tree fentry) : SRaw.tree gentry :=
  match m with
  | SRaw.Leaf _ => SRaw.Leaf _
  | SRaw.Node l k e r h => SRaw.Node (dec_tree_with f l) k (f e) (dec_tree_with f r) h
  end.

(** The body whose entries, newest first, are those of [dm] at the names
    [xs]. *)
Fixpoint assemble (dm : SRaw.tree gentry) (xs : list string) : gmod :=
  match xs with
  | nil => gm_nil
  | x :: xs' =>
      match SRaw.find x dm with
      | Some E => gm_ext (assemble dm xs') x E
      | None => assemble dm xs'
      end
  end.

(** The Core unit, body and entry fast data stand for *)
Fixpoint dec_unit (u : funit) : gunit :=
  match u with
  | fu_mk Δ (fmd_body t) => gu_mk Δ (md_body sm_closed (dec_mod t))
  | fu_core U => U
  end
with dec_mod (t : ftrie) : gmod :=
  match t with
  | ft_mk m xs =>
      assemble ((fix dec_tree (m : SRaw.tree fentry) : SRaw.tree gentry :=
                   match m with
                   | SRaw.Leaf _ => SRaw.Leaf _
                   | SRaw.Node l k e r h => SRaw.Node (dec_tree l) k (dec_entry e) (dec_tree r) h
                   end) m) xs
  end
with dec_entry (e : fentry) : gentry :=
  match e with
  | fe_def b pv A oM => ge_def b pv A oM
  | fe_mod pv u => ge_mod pv (dec_unit u)
  | fe_ind pv pq k D t => ge_ind pv pq k D (dec_mod t)
  | fe_def_mod pv A M u => ge_def_mod pv A M (dec_unit u)
  | fe_record pv p R t => ge_record pv p R (dec_mod t)
  end.

(** A body decodes by assembling its decoded tree. *)
Lemma dec_mod_unfold : forall m xs, dec_mod (ft_mk m xs) = assemble (dec_tree_with dec_entry m) xs.
Proof.
  intros m xs; cbn [dec_mod]; f_equal.
  induction m as [| l IHl k e r IHr h]; cbn; [ reflexivity | rewrite IHl, IHr; reflexivity ].
Qed.

(** ** Canonical Data

    What a filed unit and an open frame are, by well-formedness
    ([canon_of_wf]): every body a path descends into is closed, with no
    local open and no name declared twice.  On canonical data the fast
    lookups find what the Core ones find, translated, and decoding undoes
    the translation. *)
Fixpoint canon_unit (U : gunit) : Prop :=
  match U with
  | gu_mk _ (md_body sm_closed Φ) => canon_mod Φ
  | gu_mk _ (md_body sm_open _) => False
  | gu_mk _ (md_alias _) => True
  end
with canon_mod (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ' x E => ~ In x (gm_names Φ') /\ canon_mod Φ' /\ canon_entry E
  | gm_open _ _ _ => False
  end
with canon_entry (E : gentry) : Prop :=
  match E with
  | ge_def _ _ _ _ => True
  | ge_mod _ U => canon_unit U
  | ge_ind _ _ _ _ Φ => canon_mod Φ
  | ge_def_mod _ _ _ U => canon_unit U
  | ge_record _ _ _ Φ => canon_mod Φ
  end.

(** ** Member Lookup Is [gm_entry]'s *)

(** A translated body is a search tree. *)
Lemma tr_mod_bst : forall Φ, SRaw.bst (ft_map (tr_mod Φ)).
Proof.
  induction Φ as [| Φ IH x E | Φ IH H its]; cbn [tr_mod].
  - constructor.
  - destruct (tr_mod Φ) as [m xs] eqn:Et; cbn in *; apply SP.add_bst; exact IH.
  - exact IH.
Qed.

(** The newest entry of a name in a body. *)
Fixpoint gm_newest (Φ : gmod) (x : string) : option gentry :=
  match Φ with
  | gm_nil => None
  | gm_ext Φ' y E => if String.eqb x y then Some E else gm_newest Φ' x
  | gm_open Φ' _ _ => gm_newest Φ' x
  end.

(** A name finds the translation of its newest entry. *)
Lemma tr_mod_find : forall Φ x, ft_find (tr_mod Φ) x = option_map tr_entry (gm_newest Φ x).
Proof.
  intros Φ x; unfold ft_find; rewrite sfind_ok; revert x.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros x; cbn [tr_mod gm_newest].
  - reflexivity.
  - pose proof (tr_mod_bst Φ) as Hb.
    destruct (tr_mod Φ) as [m xs] eqn:Et; cbn [ft_ext ft_map] in *.
    rewrite sraw_find_add by exact Hb; destruct (String.eqb x y); [ reflexivity | apply IH ].
  - apply IH.
Qed.

(** The body a path descends into through a Core entry, as [gm_entry]
    reads it. *)
Definition entry_body (E : gentry) : option gmod :=
  match E with
  | ge_mod _ (gu_mk _ (md_body _ Φ)) => Some Φ
  | ge_ind _ _ _ _ Φ => Some Φ
  | ge_record _ _ _ Φ => Some Φ
  | _ => None
  end.

(** The body a canonical entry leads into, translated *)
Lemma fe_body_tr : forall E, canon_entry E -> fe_body (tr_entry E) = option_map tr_mod (entry_body E).
Proof. intros [| ? [? [[|] ?|] ] | | |] Hc; cbn in Hc; first [ contradiction | reflexivity ]. Qed.

(** The newest entry of a name in a canonical body is canonical. *)
Lemma canon_newest : forall Φ x E, canon_mod Φ -> gm_newest Φ x = Some E -> canon_entry E.
Proof.
  induction Φ as [| Φ IH y E' | Φ IH H its]; intros x E Hc Hn; cbn in *; [ discriminate | | contradiction ].
  destruct Hc as (_ & HΦ & HE); destruct (String.eqb x y); [ injection Hn as <-; exact HE | eauto ].
Qed.

(** The body a canonical entry leads into is canonical. *)
Lemma canon_entry_body : forall E Φ, canon_entry E -> entry_body E = Some Φ -> canon_mod Φ.
Proof.
  intros [| ? [? [[|] ?|] ] | | |] Φ Hc He; cbn in *; try discriminate; try contradiction; injection He as <-; exact Hc.
Qed.

(** [gm_entry] reads the newest entry of the first name. *)
Lemma gm_entry_newest : forall Φ x ip,
    gm_entry Φ (x :: ip) =
      match gm_newest Φ x with
      | None => None
      | Some E => match ip with
                  | nil => Some E
                  | _ :: _ => match entry_body E with Some Φ' => gm_entry Φ' ip | None => None end
                  end
      end.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros x ip; cbn [gm_entry gm_newest].
  - reflexivity.
  - destruct (String.eqb x y); [| apply IH ].
    destruct ip; [ reflexivity |].
    destruct E as [| ? [? [] ] | | |]; reflexivity.
  - apply IH.
Qed.

(** The trie finds the translation of what [gm_entry] finds. *)
Theorem ft_entry_ok : forall ip Φ, canon_mod Φ -> ft_entry (tr_mod Φ) ip = option_map tr_entry (gm_entry Φ ip).
Proof.
  induction ip as [| x ip IH]; intros Φ Hc; [ rewrite gm_entry_nil; reflexivity |].
  cbn [ft_entry]; rewrite tr_mod_find, gm_entry_newest.
  destruct (gm_newest Φ x) as [E |] eqn:En; cbn [option_map]; [| reflexivity ].
  pose proof (canon_newest _ _ _ Hc En) as HE.
  destruct ip as [| z ip']; [ reflexivity |].
  rewrite fe_body_tr by exact HE; destruct (entry_body E) eqn:Eb; cbn [option_map]; [| reflexivity ].
  apply IH, (canon_entry_body _ _ HE Eb).
Qed.

(** A translated unit's parameters *)
Lemma tr_unit_params : forall U, fu_params (tr_unit U) = gu_params U.
Proof. intros [Δ [[|] Φ | H]]; reflexivity. Qed.

(** A canonical translated unit's body *)
Lemma tr_unit_body : forall U, canon_unit U -> fu_body (tr_unit U) = tr_mod (gu_mod U).
Proof. intros [Δ [[|] Φ | H]] Hc; cbn in Hc; first [ contradiction | reflexivity ]. Qed.

(** A translated entry's privacy *)
Lemma tr_entry_private : forall E, fe_private (tr_entry E) = ge_private E.
Proof. intros []; reflexivity. Qed.

(** ** Decoding Undoes the Translation on Canonical Data *)

(** Finding in a decoded tree decodes what is found. *)
Lemma find_dec_tree : forall m x, SRaw.find x (dec_tree_with dec_entry m) = option_map dec_entry (SRaw.find x m).
Proof.
  induction m as [| l IHl k e r IHr h]; intros x; cbn; [ reflexivity |].
  destruct (OrderedTypeEx.String_as_OT.compare x k); auto.
Qed.

(** Assembling along names other than [x] ignores an [add] at [x]. *)
Lemma assemble_add : forall xs m x e, SRaw.bst m -> ~ In x xs ->
    assemble (dec_tree_with dec_entry (SRaw.add x e m)) xs = assemble (dec_tree_with dec_entry m) xs.
Proof.
  induction xs as [| y xs IH]; intros m x e Hb Hn; cbn [assemble]; [ reflexivity |].
  rewrite !find_dec_tree, sraw_find_add by exact Hb.
  destruct (String.eqb_spec y x) as [-> | _]; [ elim Hn; left; reflexivity |].
  rewrite IH by (auto || (intros Hi; apply Hn; right; exact Hi)); reflexivity.
Qed.

(** Decoding one more member: one more [gm_ext]. *)
Lemma dec_ext : forall t x e, SRaw.bst (ft_map t) -> ~ In x (ft_names t) ->
    dec_mod (ft_ext t x e) = gm_ext (dec_mod t) x (dec_entry e).
Proof.
  intros [m xs] x e Hb Hn; cbn [ft_ext ft_map ft_names] in *.
  rewrite !dec_mod_unfold; cbn [assemble].
  rewrite find_dec_tree, sraw_find_add, String.eqb_refl by exact Hb; cbn [option_map].
  rewrite assemble_add by assumption; reflexivity.
Qed.

(** The order index of a canonical body is its names. *)
Lemma tr_mod_names : forall Φ, canon_mod Φ -> ft_names (tr_mod Φ) = gm_names Φ.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros Hc; cbn in *; [ reflexivity | | contradiction ].
  destruct Hc as (_ & Hc & _); destruct (tr_mod Φ) as [m xs] eqn:Et; cbn in *; rewrite <- IH by exact Hc; reflexivity.
Qed.

(** Decoding undoes the translation of canonical data. *)
Fixpoint dec_tr_unit (U : gunit) {struct U} : canon_unit U -> dec_unit (tr_unit U) = U
with dec_tr_mod (Φ : gmod) {struct Φ} : canon_mod Φ -> dec_mod (tr_mod Φ) = Φ
with dec_tr_entry (E : gentry) {struct E} : canon_entry E -> dec_entry (tr_entry E) = E.
Proof.
  - destruct U as [Δ [[|] Φ | H]]; cbn; intros Hc; [ contradiction | rewrite (dec_tr_mod Φ Hc) |]; reflexivity.
  - destruct Φ as [| Φ x E | Φ H its]; cbn [tr_mod canon_mod]; intros Hc; [ reflexivity | | contradiction ].
    destruct Hc as (Hn & HcΦ & HcE).
    rewrite dec_ext by (apply tr_mod_bst || (rewrite tr_mod_names by exact HcΦ; exact Hn)).
    rewrite (dec_tr_mod Φ HcΦ), (dec_tr_entry E HcE); reflexivity.
  - destruct E as [b pv A oM | pv U | pv pq k D Φ | pv A M U | pv p R Φ]; cbn; intros Hc.
    + reflexivity.
    + rewrite (dec_tr_unit U Hc); reflexivity.
    + rewrite (dec_tr_mod Φ Hc); reflexivity.
    + rewrite (dec_tr_unit U Hc); reflexivity.
    + rewrite (dec_tr_mod Φ Hc); reflexivity.
Qed.

(** ** The Filed Units

    One balanced map from the whole path of a unit to the unit, and the
    filing order (paths only, newest first), which decoding reads.  Filing
    a unit is one [PM.add] and one cons.  Next to them, the units the unit
    being run sees, in a map of their own ([fus_vis]): it grows by one add
    per path that becomes imported ([fus_see]), is set aside while an
    imported unit runs ([fus_with_vis]), and is never rebuilt, so that a
    lookup is one search.  Both maps are keyed by [path_key]. *)
Record funits : Type := mk_funits
  { (** each filed unit, by its whole path *)
    fus_map : PM.t funit
    (** the paths, in filing order, newest first *)
  ; fus_order : list path
    (** the filed units the unit being run imported, by their whole paths
        ([vis_rep]) *)
  ; fus_vis : PM.t funit }.

(** Nothing filed *)
Definition funits_empty : funits := mk_funits (PM.empty _) nil (PM.empty _).

(** Filing the unit [u] at [fp]; the units seen are not changed. *)
Definition fus_file (fp : path) (u : funit) (s : funits) : funits :=
  mk_funits (pk_add fp u (fus_map s)) (fp :: fus_order s) (fus_vis s).

(** The unit filed at [fp] *)
Definition fus_find (s : funits) (fp : path) : option funit := pk_find fp (fus_map s).

(** The Core units [s] stands for, for types only. *)
Definition dec_units (s : funits) : gdeps :=
  flat_map (fun fp => match fus_find s fp with Some u => [(fp, dec_unit u)] | None => nil end) (fus_order s).

(** Canonical filed units: no path filed twice, every unit canonical. *)
Fixpoint canon_deps (Θ : gdeps) : Prop :=
  match Θ with
  | nil => True
  | (fp, U) :: Θ' => gds_lookup Θ' fp = None /\ canon_unit U /\ canon_deps Θ'
  end.

(** [s] refines [Θ]. *)
Record units_rep (s : funits) (Θ : gdeps) : Prop := mk_units_rep
  { (** a path finds the translation of what [gds_lookup] finds *)
    ur_find : forall fp, fus_find s fp = option_map tr_unit (gds_lookup Θ fp)
    (** the order index lists exactly [Θ]'s paths *)
  ; ur_order : fus_order s = map fst Θ }.

(** Nothing filed refines nothing filed. *)
Lemma units_rep_empty : units_rep funits_empty nil.
Proof. constructor; [ intros; apply pk_find_empty | reflexivity ]. Qed.

(** Filing one unit keeps the refinement. *)
Theorem units_rep_file : forall s Θ fp U,
    units_rep s Θ -> units_rep (fus_file fp (tr_unit U) s) ((fp, U) :: Θ).
Proof.
  intros s Θ fp U [Hf Ho]; unfold fus_file; constructor; cbn [fus_order map fst]; [| rewrite Ho; reflexivity ].
  intros fq; unfold fus_find; cbn [fus_map gds_lookup]; rewrite pk_find_add.
  destruct (path_beq fq fp); [ reflexivity | apply Hf ].
Qed.

(** A unit of canonical filed units is canonical. *)
Lemma canon_deps_lookup : forall Θ fp U, canon_deps Θ -> gds_lookup Θ fp = Some U -> canon_unit U.
Proof.
  induction Θ as [| [fq V] Θ IH]; intros fp U Hc Hl; cbn in *; [ discriminate |].
  destruct Hc as (_ & HV & Hc); destruct (path_beq fp fq); [ injection Hl as <-; exact HV | eauto ].
Qed.

(** Decoding gives a canonical [Θ] back. *)
Theorem dec_units_ok : forall Θ s, canon_deps Θ -> units_rep s Θ -> dec_units s = Θ.
Proof.
  intros Θ s Hc [Hf Ho]; unfold dec_units; rewrite Ho.
  assert (Hgen : forall Θ0, canon_deps Θ0 ->
    (forall fp, In fp (map fst Θ0) -> fus_find s fp = option_map tr_unit (gds_lookup Θ0 fp)) ->
    flat_map (fun fp => match fus_find s fp with Some u => [(fp, dec_unit u)] | None => nil end) (map fst Θ0) = Θ0).
  { induction Θ0 as [| [fp U] Θ0 IH]; intros HC HF; [ reflexivity |].
    destruct HC as (Hn & HU & HC); cbn [map fst flat_map].
    pose proof (HF fp (or_introl eq_refl)) as E; cbn [gds_lookup] in E.
    rewrite path_beq_refl in E; rewrite E; cbn [option_map app]; rewrite dec_tr_unit by exact HU.
    f_equal; apply IH; [ exact HC |]; intros fq Hq; rewrite (HF fq (or_intror Hq)); cbn [gds_lookup].
    destruct (path_beq fq fp) eqn:Eb; [| reflexivity ].
    apply path_beq_true in Eb as ->.
    exfalso; clear -Hn Hq; induction Θ0 as [| [fr V] Θ0 IH]; cbn in *; [ contradiction |].
    destruct (path_beq fp fr) eqn:Eb; [ discriminate |].
    destruct Hq as [-> | Hq]; [ rewrite path_beq_refl in Eb; discriminate | exact (IH Hn Hq) ]. }
  apply Hgen; [ exact Hc |]; intros; apply Hf.
Qed.

(** The decoded units find the decoding of what the map finds, for any
    [Θ] the map refines. *)
Lemma dec_units_lookup : forall s Θ, units_rep s Θ -> forall fp, gds_lookup (dec_units s) fp = option_map dec_unit (fus_find s fp).
Proof.
  intros s Θ [Hf Ho] fp; unfold dec_units; rewrite Ho.
  assert (Hgen : forall L, (forall q, In q L -> fus_find s q <> None) ->
    gds_lookup (flat_map (fun fp => match fus_find s fp with Some u => [(fp, dec_unit u)] | None => nil end) L) fp =
    if existsb (path_beq fp) L then option_map dec_unit (fus_find s fp) else None).
  { induction L as [| q L IH]; intros HL; [ reflexivity |]; cbn [flat_map existsb].
    destruct (fus_find s q) as [u |] eqn:Eq; [| exfalso; exact (HL q (or_introl eq_refl) Eq) ].
    cbn [app gds_lookup]; destruct (path_beq fp q) eqn:Eb; cbn [orb].
    - apply path_beq_true in Eb as ->; rewrite Eq; reflexivity.
    - apply IH; intros; apply HL; right; assumption. }
  rewrite Hgen.
  - destruct (existsb (path_beq fp) (map fst Θ)) eqn:Ex; [ reflexivity |].
    rewrite Hf.
    destruct (gds_lookup Θ fp) eqn:El; [| reflexivity ].
    exfalso; apply gds_lookup_in in El; apply (in_map fst) in El; cbn in El.
    apply existsb_path_beq in El; congruence.
  - intros q Hq; rewrite Hf; apply in_map_iff in Hq as ([q' U] & <- & Hin); cbn [fst].
    destruct (gds_lookup Θ q') eqn:El; [ discriminate |].
    apply gds_dom_none in El; elim El; unfold gds_dom; apply (in_map fst) in Hin; exact Hin.
Qed.

(** ** What a Unit Sees

    The unit being run sees what it imported: the units of [fus_vis], which
    are the filed units at the paths it imported ([vis_rep]).  The map
    grows by one [add] per path that becomes imported ([fus_see]); it is
    set aside, not rebuilt, while an imported unit runs ([fus_with_vis]).
    The restriction itself is never built. *)

(** The units seen at [s] are those filed at the paths of [D]. *)
Definition vis_rep (s : funits) (D : list path) : Prop :=
  forall fp, pk_find fp (fus_vis s) = if existsb (path_beq fp) D then fus_find s fp else None.

(** [s] with the units seen [m] *)
Definition fus_with_vis (s : funits) (m : PM.t funit) : funits := mk_funits (fus_map s) (fus_order s) m.

(** The paths [L] seen as well: one [add] each, of the unit filed there *)
Definition fus_see (L : list path) (s : funits) : funits :=
  fus_with_vis s (fold_left (fun m fp => match fus_find s fp with Some u => pk_add fp u m | None => m end) L (fus_vis s)).

(** Seeing nothing *)
Lemma vis_rep_nil : forall s, vis_rep (fus_with_vis s (PM.empty _)) nil.
Proof. intros s fp; apply pk_find_empty. Qed.

(** The same paths, in another list *)
Lemma vis_rep_ext : forall s D D', (forall x, In x D <-> In x D') -> vis_rep s D -> vis_rep s D'.
Proof.
  intros s D D' HD H fp; rewrite H.
  destruct (existsb (path_beq fp) D) eqn:E1, (existsb (path_beq fp) D') eqn:E2; try reflexivity.
  - apply existsb_path_beq in E1; apply HD, existsb_path_beq in E1; congruence.
  - apply existsb_path_beq in E2; apply HD, existsb_path_beq in E2; congruence.
Qed.

(** Seeing [L] as well *)
Lemma vis_rep_see : forall L s D, vis_rep s D -> vis_rep (fus_see L s) (D ++ L).
Proof.
  intros L s; unfold vis_rep, fus_see; cbn [fus_vis fus_with_vis]; generalize (fus_vis s) as m.
  induction L as [| q L IH]; intros m D H fp; cbn [fold_left].
  - rewrite app_nil_r; apply H.
  - replace (D ++ q :: L) with ((D ++ q :: nil) ++ L) by (rewrite <- app_assoc; reflexivity).
    apply (IH _ (D ++ q :: nil)); clear fp; intros fp.
    rewrite existsb_app; cbn [existsb]; rewrite Bool.orb_false_r.
    destruct (fus_find s q) as [u |] eqn:Eq; [ rewrite pk_find_add |];
      destruct (path_beq fp q) eqn:Eb; rewrite ?Bool.orb_true_r, ?Bool.orb_false_r.
    + apply path_beq_true in Eb as ->; rewrite Eq; reflexivity.
    + exact (H fp).
    + apply path_beq_true in Eb as ->; rewrite (H q), Eq; destruct (existsb _ _); reflexivity.
    + exact (H fp).
Qed.

(** Units filed meanwhile, at paths not seen: the units seen stay. *)
Lemma vis_rep_grow : forall s s' D, vis_rep s D -> (forall q, In q D -> fus_find s' q = fus_find s q) ->
    vis_rep (fus_with_vis s' (fus_vis s)) D.
Proof.
  intros s s' D H Hq fp; cbn [fus_vis fus_with_vis]; rewrite H.
  destruct (existsb (path_beq fp) D) eqn:E; [| reflexivity ].
  apply existsb_path_beq in E; symmetry; exact (Hq fp E).
Qed.

(** Changing the units seen changes no unit filed. *)
Lemma units_rep_with_vis : forall s m Θ, units_rep s Θ -> units_rep (fus_with_vis s m) Θ.
Proof. intros s m Θ [Hf Ho]; constructor; [ exact Hf | exact Ho ]. Qed.

Lemma units_rep_see : forall L s Θ, units_rep s Θ -> units_rep (fus_see L s) Θ.
Proof. intros; apply units_rep_with_vis; assumption. Qed.

(** What a unit sees: the units, and the paths it imported *)
Record fview : Type := mk_fview
  { (** every unit filed so far, with the units seen *)
    fv_units : funits
    (** the paths the unit being run imported *)
  ; fv_dom : list path }.

(** The unit at [fp], if it is imported: one search *)
Definition fv_find (v : fview) (fp : path) : option funit := pk_find fp (fus_vis (fv_units v)).

(** The Core units a view stands for, for types only: the restriction of
    the decoded units to the imported paths. *)
Definition view_deps (v : fview) : gdeps := gds_restrict (fv_dom v) (dec_units (fv_units v)).

(** The view finds the translation of what the restriction finds. *)
Theorem fv_find_ok : forall v Θ fp, units_rep (fv_units v) Θ -> vis_rep (fv_units v) (fv_dom v) ->
    fv_find v fp = option_map tr_unit (gds_lookup (gds_restrict (fv_dom v) Θ) fp).
Proof.
  intros [s D] Θ fp H Hv; unfold fv_find; cbn [fv_dom fv_units] in *; rewrite gds_lookup_restrict, Hv.
  destruct (existsb _ _); [ apply (ur_find _ _ H) | reflexivity ].
Qed.

(** The decoded view finds the decoding of what the view finds. *)
Theorem view_deps_lookup : forall v Θ fp, units_rep (fv_units v) Θ -> vis_rep (fv_units v) (fv_dom v) ->
    gds_lookup (view_deps v) fp = option_map dec_unit (fv_find v fp).
Proof.
  intros [s D] Θ fp H Hv; unfold view_deps, fv_find; cbn [fv_dom fv_units] in *.
  rewrite gds_lookup_restrict, Hv; destruct (existsb _ _); [ exact (dec_units_lookup _ _ H fp) | reflexivity ].
Qed.

(** ** Open Frames

    A frame as Core's ([qname * frame_kind * gunit]), its body a trie. *)
Record fframe : Type := mk_fframe
  { (** the frame's own module path *)
    ff_path : qname
    (** what the frame is the module of *)
  ; ff_kind : frame_kind
    (** its own parameters *)
  ; ff_params : ctx
    (** its members so far *)
  ; ff_body : ftrie }.

(** The open frames, innermost first *)
Definition fstack : Type := list fframe.

(** The fast frame of a Core one *)
Definition tr_frame (f : (qname * frame_kind * gunit)%type) : fframe :=
  let '(mp, K, U) := f in mk_fframe mp K (gu_params U) (tr_mod (gu_mod U)).

(** The fast frames of a Core stack *)
Definition fs_of (Ξ : gstack) : fstack := map tr_frame Ξ.

(** The Core frame a fast one stands for, for types only *)
Definition dec_frame (f : fframe) : (qname * frame_kind * gunit)%type :=
  (ff_path f, ff_kind f, gu_body (ff_params f) (dec_mod (ff_body f))).

(** The Core stack a fast one stands for, for types only *)
Definition dec_stack (fs : fstack) : gstack := map dec_frame fs.

(** A frame of a well-formed stack: a closed body. *)
Definition frame_closed (U : gunit) : Prop :=
  match U with
  | gu_mk _ (md_body sm_closed _) => True
  | _ => False
  end.

(** A canonical frame: a closed canonical body. *)
Definition canon_frame (U : gunit) : Prop :=
  match U with
  | gu_mk _ (md_body sm_closed Φ) => canon_mod Φ
  | _ => False
  end.

(** Every frame closed *)
Definition stack_closed (Ξ : gstack) : Prop := Forall (fun f => frame_closed (snd f)) Ξ.

(** Every frame canonical *)
Definition canon_stack (Ξ : gstack) : Prop := Forall (fun f => canon_frame (snd f)) Ξ.

(** A canonical stack's frames are closed bodies. *)
Lemma canon_stack_closed : forall Ξ, canon_stack Ξ -> stack_closed Ξ.
Proof.
  intros Ξ H; induction H as [| f Ξ Hf _ IH]; constructor; [| exact IH ].
  destruct f as [[mp K] [Δ [[|] Φ | E]]]; cbn in *; tauto.
Qed.

(** Decoding the fast frames of a canonical stack gives it back. *)
Theorem dec_stack_ok : forall Ξ, canon_stack Ξ -> dec_stack (fs_of Ξ) = Ξ.
Proof.
  unfold dec_stack, fs_of; intros Ξ H; induction H as [| f Ξ Hf _ IH]; [ reflexivity |].
  destruct f as [[mp K] [Δ [[|] Φ | E]]]; cbn in Hf; try contradiction.
  change (dec_frame (tr_frame (mp, K, gu_body Δ Φ)) :: map dec_frame (map tr_frame Ξ) = (mp, K, gu_body Δ Φ) :: Ξ).
  rewrite IH; unfold dec_frame, tr_frame; cbn [ff_path ff_kind ff_params ff_body gu_params gu_mod].
  rewrite dec_tr_mod by exact Hf; reflexivity.
Qed.

(** The parameters of all the frames, [gs_tele]'s twin *)
Fixpoint fs_tele (fs : fstack) : ctx :=
  match fs with
  | nil => nil
  | f :: fs' => ff_params f ++ fs_tele fs'
  end.

(** The telescope of the fast frames of a stack is its telescope. *)
Lemma fs_tele_of : forall Ξ, fs_tele (fs_of Ξ) = gs_tele Ξ.
Proof. unfold fs_of; induction Ξ as [| [[mp K] U] Ξ IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(** The telescope of a decoded stack is that of the fast frames. *)
Lemma fs_tele_dec : forall fs, gs_tele (dec_stack fs) = fs_tele fs.
Proof. unfold dec_stack; induction fs as [| f fs IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(** The innermost frame's path, [gs_path]'s twin *)
Definition fs_path (fs : fstack) : qname :=
  match fs with
  | f :: _ => ff_path f
  | nil => q_abs nil nil
  end.

(** The path of the innermost fast frame of a stack *)
Lemma fs_path_of : forall Ξ, fs_path (fs_of Ξ) = gs_path Ξ.
Proof. intros [| [[mp K] U] Ξ]; reflexivity. Qed.

(** The path of the innermost frame of a decoded stack *)
Lemma fs_path_dec : forall fs, gs_path (dec_stack fs) = fs_path fs.
Proof. intros [| f fs]; reflexivity. Qed.

(** One member more in the innermost frame, [gs_add]'s twin: one
    [ft_ext]. *)
Definition fs_add (x : string) (e : fentry) (fs : fstack) : fstack :=
  match fs with
  | f :: fs' => mk_fframe (ff_path f) (ff_kind f) (ff_params f) (ft_ext (ff_body f) x e) :: fs'
  | nil => nil
  end.

(** Adding a translated entry fast is adding it in Core. *)
Lemma fs_add_of : forall x E Ξ, fs_add x (tr_entry E) (fs_of Ξ) = fs_of (gs_add x E Ξ).
Proof. intros x E [| [[mp K] U] Ξ]; reflexivity. Qed.

(** A frame pushed, [gs_push]'s twin *)
Definition fs_push (mp : qname) (Δ : ctx) (fs : fstack) : fstack := mk_fframe mp fk_module Δ ft_empty :: fs.

(** Pushing a frame fast is pushing it in Core. *)
Lemma fs_push_of : forall mp Δ Ξ, fs_push mp Δ (fs_of Ξ) = fs_of (gs_push mp Δ Ξ).
Proof. reflexivity. Qed.

(** The frame of the module of a member of a group, [gs_push_ind]'s twin *)
Definition fs_push_ind (mp pq : qname) (k : nat) (D : ind_decl) (Δ : ctx) (fs : fstack) : fstack :=
  mk_fframe mp (fk_ind pq k D) Δ ft_empty :: fs.

(** Alike for a member's module *)
Lemma fs_push_ind_of : forall mp pq k D Δ Ξ, fs_push_ind mp pq k D Δ (fs_of Ξ) = fs_of (gs_push_ind mp pq k D Δ Ξ).
Proof. reflexivity. Qed.

(** The frame of the module of a record type, [gs_push_record]'s twin *)
Definition fs_push_record (mp : qname) (R : record_decl) (Δ : ctx) (fs : fstack) : fstack :=
  mk_fframe mp (fk_record R) (ce_ass (record_self mp R) :: Δ) ft_empty :: fs.

(** Alike for a record's module *)
Lemma fs_push_record_of : forall mp R Δ Ξ, fs_push_record mp R Δ (fs_of Ξ) = fs_of (gs_push_record mp R Δ Ξ).
Proof. reflexivity. Qed.

(** Whether [x] is fresh in the innermost frame, [gs_fresh]'s twin *)
Definition fs_fresh_dec (x : string) (fs : fstack) : bool :=
  match fs with
  | f :: _ => match ft_find (ff_body f) x with None => true | Some _ => false end
  | nil => false
  end.

(** A canonical body has a newest entry of a name exactly when it
    declares the name. *)
Lemma gm_newest_names : forall Φ x, canon_mod Φ -> (gm_newest Φ x = None <-> ~ In x (gm_names Φ)).
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros x Hc; cbn in *; [ tauto | | contradiction ].
  destruct Hc as (_ & Hc & _); destruct (String.eqb_spec x y) as [-> | Hne].
  - split; [ discriminate | intros Hn; elim Hn; left; reflexivity ].
  - rewrite (IH x Hc); split; [ intros Hn [-> | Hin]; [ exact (Hne eq_refl) | exact (Hn Hin) ] | intros Hn Hin; exact (Hn (or_intror Hin)) ].
Qed.

(** Freshness decided fast, on a canonical stack *)
Lemma fs_fresh_dec_of : forall x Ξ, canon_stack Ξ -> (fs_fresh_dec x (fs_of Ξ) = true <-> gs_fresh x Ξ).
Proof.
  intros x [| [[mp K] U] Ξ] Hc; cbn; [ split; [ discriminate | contradiction ] |].
  inversion Hc as [| ? ? HU _]; subst; cbn in HU.
  destruct U as [Δ [[|] Φ | E]]; try contradiction; cbn [gu_mod].
  rewrite tr_mod_find; unfold gm_fresh; rewrite <- (gm_newest_names Φ x HU).
  destruct (gm_newest Φ x); cbn [option_map]; split; congruence.
Qed.

(** ** The Lookups

    Each Core lookup of a global path, over a function [uf] giving the
    filed units fast and over the fast frames.  On the translation of a
    Core context it finds what the Core lookup finds, translated
    ([fgc_entry_ok] and the like). *)

(** A located body: its full telescope and its members, fast *)
Definition tr_loc (r : (ctx * gmod)%type) : (ctx * ftrie)%type := (fst r, tr_mod (snd r)).

(** The innermost frame [p] is in, with [p] read inside it, and the
    parameters of the frames outside it; [gs_find_tele]'s twin. *)
Fixpoint fs_find_tele (fs : fstack) (p : qname) : option (fframe * list string * ctx) :=
  match fs with
  | nil => None
  | f :: fs' =>
      match qname_strip (ff_path f) p with
      | Some ip => Some (f, ip, fs_tele fs')
      | None => fs_find_tele fs' p
      end
  end.

(** What a lookup reads of the frame found: its parameters and its body *)
Definition ff_view (r : (fframe * list string * ctx)%type) : (ctx * ftrie * list string * ctx)%type :=
  let '(f, ip, T) := r in (ff_params f, ff_body f, ip, T).

(** The same of a Core frame, translated *)
Definition gf_view (r : (gunit * list string * ctx)%type) : (ctx * ftrie * list string * ctx)%type :=
  let '(U, ip, T) := r in (gu_params U, tr_mod (gu_mod U), ip, T).

(** The frame found fast reads as the Core frame found. *)
Lemma fs_find_tele_of : forall Ξ p,
    option_map ff_view (fs_find_tele (fs_of Ξ) p) = option_map gf_view (gs_find_tele Ξ p).
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros p; cbn; [ reflexivity |].
  destruct (qname_strip mp p); [ cbn; rewrite fs_tele_of; reflexivity | apply IH ].
Qed.

(** The kind of the frame found, alike *)
Lemma fs_find_tele_kind : forall Ξ p f ip T,
    fs_find_tele (fs_of Ξ) p = Some (f, ip, T) ->
    exists mp U T', gs_find_tele Ξ p = Some (U, ip, T') /\ f = tr_frame (mp, ff_kind f, U).
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros * H; cbn in *; [ discriminate |].
  destruct (qname_strip mp p); [ injection H as <- <- <-; do 3 eexists; split; reflexivity | exact (IH _ _ _ _ H) ].
Qed.

(** The innermost frame [p] is in, [gs_find]'s twin, with the frame. *)
Fixpoint fs_find (fs : fstack) (p : qname) : option (fframe * list string) :=
  match fs with
  | nil => None
  | f :: fs' =>
      match qname_strip (ff_path f) p with
      | Some ip => Some (f, ip)
      | None => fs_find fs' p
      end
  end.

(** The member of a group whose module is the open frame at [p],
    [gs_find_ind]'s twin *)
Fixpoint fs_find_ind (fs : fstack) (p : qname) : option (qname * nat * ind_decl) :=
  match fs with
  | nil => None
  | f :: fs' =>
      match qname_strip (ff_path f) p with
      | Some nil =>
          match ff_kind f with
          | fk_ind pq k D => Some (pq, k, D)
          | fk_module | fk_record _ => None
          end
      | Some (_ :: _) => None
      | None => fs_find_ind fs' p
      end
  end.

(** The record type whose module is the open frame at [p],
    [gs_find_record]'s twin *)
Fixpoint fs_find_record (fs : fstack) (p : qname) : option record_decl :=
  match fs with
  | nil => None
  | f :: fs' =>
      match qname_strip (ff_path f) p with
      | Some nil =>
          match ff_kind f with
          | fk_record R => Some R
          | fk_module | fk_ind _ _ _ => None
          end
      | Some (_ :: _) => None
      | None => fs_find_record fs' p
      end
  end.

(** The body of the frame found and the path in it *)
Definition ff_find_view (r : (fframe * list string)%type) : (ftrie * list string)%type := (ff_body (fst r), snd r).

(** Alike for [gs_find] *)
Lemma fs_find_of : forall Ξ p,
    option_map ff_find_view (fs_find (fs_of Ξ) p) = option_map (fun r => (tr_mod (gu_mod (fst r)), snd r)) (gs_find Ξ p).
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros p; cbn; [ reflexivity |].
  destruct (qname_strip mp p); [ reflexivity | apply IH ].
Qed.

(** The member of the frame found fast is the Core one. *)
Lemma fs_find_ind_of : forall Ξ p, fs_find_ind (fs_of Ξ) p = gs_find_ind Ξ p.
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros p; cbn; [ reflexivity |].
  destruct (qname_strip mp p) as [[|] |]; [ reflexivity | reflexivity | apply IH ].
Qed.

(** The record of the frame found fast is the Core one. *)
Lemma fs_find_record_of : forall Ξ p, fs_find_record (fs_of Ξ) p = gs_find_record Ξ p.
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros p; cbn; [ reflexivity |].
  destruct (qname_strip mp p) as [[|] |]; [ reflexivity | reflexivity | apply IH ].
Qed.

(** *** Through a Body *)

(** [gm_resolve]'s twin: a definition only, read through body modules *)
Fixpoint ft_resolve (t : ftrie) (ip : list string) {struct ip} : option gentry :=
  match ip with
  | nil => None
  | x :: ip' =>
      match ft_find t x with
      | None => None
      | Some e =>
          match ip', e with
          | nil, fe_def b pv A oM => Some (ge_def b pv A oM)
          | _ :: _, _ => match fe_body e with Some t' => ft_resolve t' ip' | None => None end
          | nil, _ => None
          end
      end
  end.

(** [gm_resolve] reads the newest entry of the first name. *)
Lemma gm_resolve_newest : forall Φ x ip,
    gm_resolve Φ (x :: ip) =
      match gm_newest Φ x with
      | None => None
      | Some E => match ip, E with
                  | nil, ge_def _ _ _ _ => Some E
                  | _ :: _, _ => match entry_body E with Some Φ' => gm_resolve Φ' ip | None => None end
                  | nil, _ => None
                  end
      end.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros x ip; cbn [gm_resolve gm_newest].
  - reflexivity.
  - destruct (String.eqb x y); [| apply IH ].
    destruct ip; destruct E as [| ? [? [] ] | | |]; reflexivity.
  - apply IH.
Qed.

(** The trie resolves what [gm_resolve] resolves. *)
Theorem ft_resolve_ok : forall ip Φ, canon_mod Φ -> ft_resolve (tr_mod Φ) ip = gm_resolve Φ ip.
Proof.
  induction ip as [| x ip IH]; intros Φ Hc; [ rewrite gm_resolve_nil; reflexivity |].
  cbn [ft_resolve]; rewrite tr_mod_find, gm_resolve_newest.
  destruct (gm_newest Φ x) as [E |] eqn:En; cbn [option_map]; [| reflexivity ].
  pose proof (canon_newest _ _ _ Hc En) as HE.
  destruct ip as [| z ip'].
  - destruct E; reflexivity.
  - rewrite fe_body_tr by exact HE; destruct (entry_body E) eqn:Eb; cbn [option_map]; [| reflexivity ].
    apply IH, (canon_entry_body _ _ HE Eb).
Qed.

(** What the submodule [ip] is, through the entry [e] of a body of
    telescope [T]: [gm_submodule]'s step *)
Fixpoint fe_submodule (T : ctx) (e : fentry) (ip : list string) {struct ip} : option modres :=
  match e with
  | fe_mod _ (fu_mk Δ (fmd_body t')) =>
      match ip with
      | nil => Some (mr_body (Δ ++ T) None)
      | z :: ip' => match ft_find t' z with Some e' => fe_submodule (Δ ++ T) e' ip' | None => None end
      end
  | fe_mod _ (fu_core (gu_mk Δ (md_alias E'))) =>
      match ip with
      | nil => Some (mr_alias (gu_mk Δ (md_alias E')))
      | _ :: _ => None
      end
  | fe_ind _ pq k D t' =>
      match ip with
      | nil => Some (mr_body (ind_uparams D) (Some (pq, k, D)))
      | z :: ip' => match ft_find t' z with Some e' => fe_submodule (ind_uparams D) e' ip' | None => None end
      end
  | fe_def_mod _ _ _ (fu_core (gu_mk Δ (md_alias E'))) =>
      match ip with
      | nil => Some (mr_alias (gu_mk Δ (md_alias E')))
      | _ :: _ => None
      end
  | fe_record _ p R t' =>
      match ip with
      | nil => Some (mr_body (record_mod_tele p R) None)
      | z :: ip' => match ft_find t' z with Some e' => fe_submodule (record_mod_tele p R) e' ip' | None => None end
      end
  | _ => None
  end.

(** [gm_submodule]'s twin *)
Definition ft_submodule (T : ctx) (t : ftrie) (x : string) (ip : list string) : option modres :=
  match ft_find t x with
  | Some e => fe_submodule T e ip
  | None => None
  end.

(** [gm_submodule] reads the newest entry of the name. *)
Lemma gm_submodule_newest : forall Φ T x ip,
    gm_submodule T Φ x ip =
      match gm_newest Φ x with
      | Some E =>
          match E with
          | ge_mod _ (gu_mk Δ (md_body sm Φ')) =>
              match ip with
              | nil => Some (mr_body (Δ ++ T) None)
              | z :: ip' => gm_submodule (Δ ++ T) Φ' z ip'
              end
          | ge_mod _ (gu_mk Δ (md_alias E')) =>
              match ip with
              | nil => Some (mr_alias (gu_mk Δ (md_alias E')))
              | _ :: _ => None
              end
          | ge_ind _ pq k D Φ' =>
              match ip with
              | nil => Some (mr_body (ind_uparams D) (Some (pq, k, D)))
              | z :: ip' => gm_submodule (ind_uparams D) Φ' z ip'
              end
          | ge_def_mod _ _ _ (gu_mk Δ (md_alias E')) =>
              match ip with
              | nil => Some (mr_alias (gu_mk Δ (md_alias E')))
              | _ :: _ => None
              end
          | ge_def_mod _ _ _ (gu_mk _ (md_body _ _)) => None
          | ge_record _ p R Φ' =>
              match ip with
              | nil => Some (mr_body (record_mod_tele p R) None)
              | z :: ip' => gm_submodule (record_mod_tele p R) Φ' z ip'
              end
          | ge_def _ _ _ _ => None
          end
      | None => None
      end.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros T x ip; cbn [gm_submodule gm_newest].
  - reflexivity.
  - destruct (String.eqb x y); [ reflexivity | apply IH ].
  - apply IH.
Qed.

(** The trie finds the submodule [gm_submodule] finds. *)
Theorem ft_submodule_ok : forall ip Φ T x, canon_mod Φ -> ft_submodule T (tr_mod Φ) x ip = gm_submodule T Φ x ip.
Proof.
  induction ip as [| z ip IH]; intros Φ T x Hc; unfold ft_submodule; rewrite tr_mod_find, gm_submodule_newest;
    destruct (gm_newest Φ x) as [E |] eqn:En; cbn [option_map]; try reflexivity;
    pose proof (canon_newest _ _ _ Hc En) as HE;
    destruct E as [b pv A oM | pv [Δ [[|] Φ' | E']] | pv pq k D Φ' | pv A M [Δ [[|] Φ' | E']] | pv p R Φ'];
    cbn in HE; try contradiction; try reflexivity;
    cbn [tr_entry tr_unit fe_submodule]; rewrite <- IH by exact HE; reflexivity.
Qed.

(** [gm_module]'s twin *)
Definition ft_module (T : ctx) (oD : option indref) (t : ftrie) (ip : list string) : option modres :=
  match ip with
  | nil => Some (mr_body T oD)
  | x :: ip' => ft_submodule T t x ip'
  end.

(** The trie finds the module [gm_module] finds. *)
Lemma ft_module_ok : forall T oD Φ ip, canon_mod Φ -> ft_module T oD (tr_mod Φ) ip = gm_module T oD Φ ip.
Proof. intros T oD Φ [| x ip] Hc; [ reflexivity | apply ft_submodule_ok, Hc ]. Qed.

(** The body module [ip] through the entry [e], [gm_subbody]'s step *)
Fixpoint fe_subbody (T : ctx) (e : fentry) (ip : list string) {struct ip} : option (ctx * ftrie) :=
  match e with
  | fe_mod _ (fu_mk Δ (fmd_body t')) =>
      match ip with
      | nil => Some (Δ ++ T, t')
      | z :: ip' => match ft_find t' z with Some e' => fe_subbody (Δ ++ T) e' ip' | None => None end
      end
  | fe_ind _ _ _ D t' =>
      match ip with
      | nil => Some (ind_uparams D, t')
      | z :: ip' => match ft_find t' z with Some e' => fe_subbody (ind_uparams D) e' ip' | None => None end
      end
  | fe_record _ p R t' =>
      match ip with
      | nil => Some (record_mod_tele p R, t')
      | z :: ip' => match ft_find t' z with Some e' => fe_subbody (record_mod_tele p R) e' ip' | None => None end
      end
  | _ => None
  end.

(** [gm_subbody]'s twin *)
Definition ft_subbody (T : ctx) (t : ftrie) (x : string) (ip : list string) : option (ctx * ftrie) :=
  match ft_find t x with
  | Some e => fe_subbody T e ip
  | None => None
  end.

(** [gm_subbody] reads the newest entry of the name. *)
Lemma gm_subbody_newest : forall Φ T x ip,
    gm_subbody T Φ x ip =
      match gm_newest Φ x with
      | Some (ge_mod _ (gu_mk Δ (md_body sm Φ'))) =>
          match ip with
          | nil => Some (Δ ++ T, Φ')
          | z :: ip' => gm_subbody (Δ ++ T) Φ' z ip'
          end
      | Some (ge_ind _ _ _ D Φ') =>
          match ip with
          | nil => Some (ind_uparams D, Φ')
          | z :: ip' => gm_subbody (ind_uparams D) Φ' z ip'
          end
      | Some (ge_record _ p R Φ') =>
          match ip with
          | nil => Some (record_mod_tele p R, Φ')
          | z :: ip' => gm_subbody (record_mod_tele p R) Φ' z ip'
          end
      | _ => None
      end.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros T x ip; cbn [gm_subbody gm_newest].
  - reflexivity.
  - destruct (String.eqb x y); [ destruct E as [| ? [? [] ] | | |]; reflexivity | apply IH ].
  - apply IH.
Qed.

(** The trie finds the translation of the body [gm_subbody] finds. *)
Theorem ft_subbody_ok : forall ip Φ T x, canon_mod Φ -> ft_subbody T (tr_mod Φ) x ip = option_map tr_loc (gm_subbody T Φ x ip).
Proof.
  induction ip as [| z ip IH]; intros Φ T x Hc; unfold ft_subbody; rewrite tr_mod_find, gm_subbody_newest;
    destruct (gm_newest Φ x) as [E |] eqn:En; cbn [option_map]; try reflexivity;
    pose proof (canon_newest _ _ _ Hc En) as HE;
    destruct E as [b pv A oM | pv [Δ [[|] Φ' | E']] | pv pq k D Φ' | pv A M [Δ [[|] Φ' | E']] | pv p R Φ'];
    cbn in HE; try contradiction; try reflexivity;
    cbn [tr_entry tr_unit fe_subbody]; rewrite <- IH by exact HE; reflexivity.
Qed.

(** What [gm_subbody] finds in a canonical body is canonical. *)
Lemma canon_subbody : forall ip Φ T x T' Φ', canon_mod Φ -> gm_subbody T Φ x ip = Some (T', Φ') -> canon_mod Φ'.
Proof.
  induction ip as [| z ip IH]; intros Φ T x T' Φ' Hc Hs; rewrite gm_subbody_newest in Hs;
    destruct (gm_newest Φ x) as [E |] eqn:En; try discriminate;
    pose proof (canon_newest _ _ _ Hc En) as HE;
    destruct E as [b pv A oM | pv [Δ [[|] Φ1 | E']] | pv pq k D Φ1 | pv A M U | pv p R Φ1];
    cbn in HE; try contradiction; try discriminate;
    first [ injection Hs as _ <-; exact HE | exact (IH _ _ _ _ _ HE Hs) ].
Qed.

(** What [gm_entry] finds in a canonical body is canonical. *)
Lemma canon_gm_entry : forall ip Φ E, canon_mod Φ -> gm_entry Φ ip = Some E -> canon_entry E.
Proof.
  induction ip as [| x ip IH]; intros Φ E Hc He; [ rewrite gm_entry_nil in He; discriminate |].
  rewrite gm_entry_newest in He; destruct (gm_newest Φ x) as [E' |] eqn:En; [| discriminate ].
  pose proof (canon_newest _ _ _ Hc En) as HE'.
  destruct ip as [| z ip']; [ injection He as <-; exact HE' |].
  destruct (entry_body E') eqn:Eb; [| discriminate ]; exact (IH _ _ (canon_entry_body _ _ HE' Eb) He).
Qed.

(** [gm_body]'s twin *)
Definition ft_body (T : ctx) (t : ftrie) (ip : list string) : option (ctx * ftrie) :=
  match ip with
  | nil => Some (T, t)
  | x :: ip' => ft_subbody T t x ip'
  end.

(** Alike for [gm_body] *)
Lemma ft_body_ok : forall T Φ ip, canon_mod Φ -> ft_body T (tr_mod Φ) ip = option_map tr_loc (gm_body T Φ ip).
Proof. intros T Φ [| x ip] Hc; [ reflexivity | apply ft_subbody_ok, Hc ]. Qed.

(** What [gm_body] finds in a canonical body is canonical. *)
Lemma canon_body : forall ip Φ T T' Φ', canon_mod Φ -> gm_body T Φ ip = Some (T', Φ') -> canon_mod Φ'.
Proof. intros [| x ip] * Hc Hb; [ injection Hb as _ <-; exact Hc | exact (canon_subbody _ _ _ _ _ _ Hc Hb) ]. Qed.

(** *** Through the Context

    The units by a function [uf : path -> option funit], the frames fast. *)
Section Lookups.
  Variable uf : path -> option funit.

  (** [gc_resolve]'s twin *)
  Definition fgc_resolve (fs : fstack) (p : qname) : option gentry :=
    match fs_find fs p with
    | Some (f, ip) => ft_resolve (ff_body f) ip
    | None =>
        match uf (q_unit p) with
        | Some u => ft_resolve (fu_body u) (q_chain p)
        | None => None
        end
    end.

  (** [gc_module]'s twin *)
  Definition fgc_module (fs : fstack) (p : qname) : option modres :=
    match fs_find_tele fs p with
    | Some (f, nil, _) => None
    | Some (f, x :: ip, T) => ft_submodule (ff_params f ++ T) (ff_body f) x ip
    | None =>
        match uf (q_unit p) with
        | Some u => ft_module (fu_params u) None (fu_body u) (q_chain p)
        | None => None
        end
    end.

  (** [gc_body]'s twin *)
  Definition fgc_body (fs : fstack) (p : qname) : option (ctx * ftrie) :=
    match fs_find_tele fs p with
    | Some (f, nil, _) => None
    | Some (f, x :: ip, T) => ft_subbody (ff_params f ++ T) (ff_body f) x ip
    | None =>
        match uf (q_unit p) with
        | Some u => ft_body (fu_params u) (fu_body u) (q_chain p)
        | None => None
        end
    end.

  (** [gc_frame]'s twin: every fast frame is a closed body. *)
  Definition fgc_frame (fs : fstack) (p : qname) : option (ctx * ftrie) :=
    match fs_find_tele fs p with
    | Some (f, nil, T0) => Some (ff_params f ++ T0, ff_body f)
    | _ => None
    end.

  (** [gc_loc]'s twin *)
  Definition fgc_loc (fs : fstack) (p : qname) : option (ctx * ftrie) :=
    match fgc_frame fs p with
    | Some r => Some r
    | None => fgc_body fs p
    end.

  (** [ind_mlookup]'s twin *)
  Definition fgc_mlookup (fs : fstack) (p : qname) : option indref :=
    match fs_find_ind fs p with
    | Some r => Some r
    | None =>
        match fgc_module fs p with
        | Some (mr_body _ oD) => oD
        | _ => None
        end
    end.

  (** [ind_lookup]'s twin *)
  Definition fgc_ind (fs : fstack) (p : qname) : option ind_decl := ind_of_ref (fgc_mlookup fs p).

  (** [gc_entry]'s twin *)
  Definition fgc_entry (fs : fstack) (p : qname) : option fentry :=
    match fs_find fs p with
    | Some (f, ip) => ft_entry (ff_body f) ip
    | None =>
        match uf (q_unit p) with
        | Some u => ft_entry (fu_body u) (q_chain p)
        | None => None
        end
    end.

  (** [gc_term]'s twin *)
  Definition fgc_term (fs : fstack) (p : qname) : option exp :=
    match fgc_resolve fs p with
    | Some (ge_def true _ _ (Some M)) => Some M
    | _ =>
        match fgc_entry fs p with
        | Some (fe_def_mod _ _ M _) => Some M
        | _ => None
        end
    end.

  (** [record_lookup]'s twin *)
  Definition fgc_record (fs : fstack) (p : qname) : option record_decl :=
    match fs_find_record fs p with
    | Some R => Some R
    | None =>
        match fgc_entry fs p with
        | Some (fe_record _ _ R _) => Some R
        | _ => None
        end
    end.

  (** [gc_unit]'s twin *)
  Definition fgc_unit (fs : fstack) (H : modexp) : option (ctx * ftrie) :=
    match mod_qname H with
    | Some mp =>
        match fs_find_tele fs mp with
        | Some (f, nil, T0) =>
            match fs_find_ind fs mp, fs_find_record fs mp with
            | None, None => Some (ff_params f ++ T0, ff_body f)
            | _, _ => None
            end
        | Some _ => None
        | None =>
            match q_chain mp, uf (q_unit mp) with
            | nil, Some (fu_mk Δ (fmd_body t)) => Some (Δ, t)
            | _, _ => None
            end
        end
    | None => None
    end.
End Lookups.

(** The body of a canonical frame is canonical. *)
Lemma canon_frame_mod : forall U, canon_frame U -> canon_mod (gu_mod U).
Proof. intros [Δ [[|] Φ | E]] H; cbn in *; tauto. Qed.

(** The body of a canonical unit is canonical. *)
Lemma canon_unit_mod : forall U, canon_unit U -> canon_mod (gu_mod U).
Proof. intros [Δ [[|] Φ | E]] H; cbn in *; tauto. Qed.

(** The frame a path is in, in a canonical stack, is canonical. *)
Lemma canon_gs_find_tele : forall Ξ p U ip T, canon_stack Ξ -> gs_find_tele Ξ p = Some (U, ip, T) -> canon_frame U.
Proof.
  intros Ξ p U ip T H; induction H as [| [[mp K] U'] Ξ HU _ IH]; cbn; [ discriminate |].
  destruct (qname_strip mp p); [ intros [= <- _ _]; exact HU | exact IH ].
Qed.

(** Alike for [gs_find] *)
Lemma canon_gs_find : forall Ξ p U ip, canon_stack Ξ -> gs_find Ξ p = Some (U, ip) -> canon_frame U.
Proof.
  intros * Hc Hf; rewrite gs_find_tele_find in Hf.
  destruct (gs_find_tele Ξ p) as [[[U' ip'] T] |] eqn:E; cbn in Hf; [| discriminate ]; injection Hf as -> ->.
  exact (canon_gs_find_tele _ _ _ _ _ Hc E).
Qed.

(** Restricting canonical units keeps them canonical. *)
Lemma canon_restrict : forall S Θ, canon_deps Θ -> canon_deps (gds_restrict S Θ).
Proof.
  intros S; induction Θ as [| [fp U] Θ IH]; intros Hc; [ exact I |]; unfold gds_restrict in *; cbn [filter fst] in *.
  destruct Hc as (Hn & HU & Hc).
  destruct (existsb (path_beq fp) S); [ cbn; split; [| split; [ exact HU | exact (IH Hc) ] ] | exact (IH Hc) ].
  fold (gds_restrict S Θ); rewrite gds_lookup_restrict, Hn; destruct (existsb _ _); reflexivity.
Qed.

(** On the translation of a canonical Core context, the twins find what
    the Core lookups find, translated. *)
Section LookupsOk.
  Variables (uf : path -> option funit) (Θ : gdeps).
  Hypothesis Huf : forall fp, uf fp = option_map tr_unit (gds_lookup Θ fp).
  Hypothesis HcΘ : canon_deps Θ.

  (** A unit found is canonical. *)
  Lemma canon_found : forall fp U, gds_lookup Θ fp = Some U -> canon_mod (gu_mod U).
  Proof. intros * H; exact (canon_unit_mod _ (canon_deps_lookup _ _ _ HcΘ H)). Qed.

  Lemma fs_find_some : forall Ξ p,
      match fs_find (fs_of Ξ) p, gs_find Ξ p with
      | Some (f, ip), Some (U, ip') => ff_body f = tr_mod (gu_mod U) /\ ip = ip'
      | None, None => True
      | _, _ => False
      end.
  Proof.
    intros Ξ p; pose proof (fs_find_of Ξ p) as H.
    destruct (fs_find (fs_of Ξ) p) as [[f ip] |], (gs_find Ξ p) as [[U ip'] |]; cbn in H; try discriminate; auto.
    injection H as -> ->; auto.
  Qed.

  Lemma fs_find_tele_some : forall Ξ p,
      match fs_find_tele (fs_of Ξ) p, gs_find_tele Ξ p with
      | Some (f, ip, T), Some (U, ip', T') => ff_params f = gu_params U /\ ff_body f = tr_mod (gu_mod U) /\ ip = ip' /\ T = T'
      | None, None => True
      | _, _ => False
      end.
  Proof.
    intros Ξ p; pose proof (fs_find_tele_of Ξ p) as H.
    destruct (fs_find_tele (fs_of Ξ) p) as [[[f ip] T] |], (gs_find_tele Ξ p) as [[[U ip'] T'] |];
      cbn in H; try discriminate; auto.
    injection H as -> -> -> ->; auto.
  Qed.

  Theorem fgc_resolve_ok : forall Ξ p, canon_stack Ξ -> fgc_resolve uf (fs_of Ξ) p = gc_resolve Θ Ξ p.
  Proof.
    intros Ξ p HcΞ; unfold fgc_resolve, gc_resolve, gc_resolve_u.
    pose proof (fs_find_some Ξ p) as H.
    destruct (fs_find (fs_of Ξ) p) as [[f ip] |], (gs_find Ξ p) as [[U ip'] |] eqn:Eg; try contradiction.
    - destruct H as [-> ->]; apply ft_resolve_ok, canon_frame_mod, (canon_gs_find _ _ _ _ HcΞ Eg).
    - rewrite Huf; destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:El; cbn [option_map]; [| reflexivity ].
      rewrite tr_unit_body by exact (canon_deps_lookup _ _ _ HcΘ El); apply ft_resolve_ok, (canon_found _ _ El).
  Qed.

  Theorem fgc_module_ok : forall Ξ p, canon_stack Ξ -> fgc_module uf (fs_of Ξ) p = gc_module Θ Ξ p.
  Proof.
    intros Ξ p HcΞ; unfold fgc_module, gc_module, gc_module_u.
    pose proof (fs_find_tele_some Ξ p) as H.
    destruct (fs_find_tele (fs_of Ξ) p) as [[[f ip] T] |], (gs_find_tele Ξ p) as [[[U ip'] T'] |] eqn:Eg; try contradiction.
    - destruct H as (-> & -> & <- & <-); destruct ip; [ reflexivity |].
      apply ft_submodule_ok, canon_frame_mod, (canon_gs_find_tele _ _ _ _ _ HcΞ Eg).
    - rewrite Huf; destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:El; cbn [option_map]; [| reflexivity ].
      rewrite tr_unit_body, tr_unit_params by exact (canon_deps_lookup _ _ _ HcΘ El); apply ft_module_ok, (canon_found _ _ El).
  Qed.

  Theorem fgc_body_ok : forall Ξ p, canon_stack Ξ -> fgc_body uf (fs_of Ξ) p = option_map tr_loc (gc_body Θ Ξ p).
  Proof.
    intros Ξ p HcΞ; unfold fgc_body, gc_body.
    pose proof (fs_find_tele_some Ξ p) as H.
    destruct (fs_find_tele (fs_of Ξ) p) as [[[f ip] T] |], (gs_find_tele Ξ p) as [[[U ip'] T'] |] eqn:Eg; try contradiction.
    - destruct H as (-> & -> & <- & <-); destruct ip; [ reflexivity |].
      apply ft_subbody_ok, canon_frame_mod, (canon_gs_find_tele _ _ _ _ _ HcΞ Eg).
    - rewrite Huf; destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:El; cbn [option_map]; [| reflexivity ].
      rewrite tr_unit_body, tr_unit_params by exact (canon_deps_lookup _ _ _ HcΘ El); apply ft_body_ok, (canon_found _ _ El).
  Qed.

  Theorem fgc_frame_ok : forall Ξ p, stack_closed Ξ -> fgc_frame (fs_of Ξ) p = option_map tr_loc (gc_frame Ξ p).
  Proof.
    induction Ξ as [| [[mp K] U] Ξ IH]; intros p Hc; [ reflexivity |].
    inversion Hc as [| ? ? HU Hc']; subst; cbn in HU.
    unfold fgc_frame, gc_frame in *; cbn [fs_of map tr_frame fs_find_tele gs_find_tele ff_path].
    destruct (qname_strip mp p) as [[| x ip] |].
    - destruct U as [Δ [[|] Φ | E]]; cbn in HU |- *; try contradiction; rewrite fs_tele_of; reflexivity.
    - destruct U as [Δ [[|] Φ | E]]; reflexivity.
    - exact (IH p Hc').
  Qed.

  Theorem fgc_loc_ok : forall Ξ p, canon_stack Ξ -> fgc_loc uf (fs_of Ξ) p = option_map tr_loc (gc_loc Θ Ξ p).
  Proof.
    intros * Hc; unfold fgc_loc, gc_loc; rewrite fgc_frame_ok by exact (canon_stack_closed _ Hc).
    destruct (gc_frame Ξ p); [ reflexivity | apply fgc_body_ok, Hc ].
  Qed.

  Theorem fgc_mlookup_ok : forall Ξ p, canon_stack Ξ -> fgc_mlookup uf (fs_of Ξ) p = ind_mlookup Θ Ξ p.
  Proof.
    intros * Hc; unfold fgc_mlookup, ind_mlookup, ind_mlookup_u; rewrite fs_find_ind_of.
    destruct (gs_find_ind Ξ p); [ reflexivity |].
    rewrite fgc_module_ok by exact Hc; reflexivity.
  Qed.

  Theorem fgc_ind_ok : forall Ξ p, canon_stack Ξ -> fgc_ind uf (fs_of Ξ) p = ind_lookup Θ Ξ p.
  Proof. intros * Hc; unfold fgc_ind, ind_lookup, ind_lookup_u; rewrite fgc_mlookup_ok by exact Hc; reflexivity. Qed.

  Theorem fgc_entry_ok : forall Ξ p, canon_stack Ξ -> fgc_entry uf (fs_of Ξ) p = option_map tr_entry (gc_entry Θ Ξ p).
  Proof.
    intros Ξ p HcΞ; unfold fgc_entry, gc_entry, gc_entry_u.
    pose proof (fs_find_some Ξ p) as H.
    destruct (fs_find (fs_of Ξ) p) as [[f ip] |], (gs_find Ξ p) as [[U ip'] |] eqn:Eg; try contradiction.
    - destruct H as [-> ->]; apply ft_entry_ok, canon_frame_mod, (canon_gs_find _ _ _ _ HcΞ Eg).
    - rewrite Huf; destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:El; cbn [option_map]; [| reflexivity ].
      rewrite tr_unit_body by exact (canon_deps_lookup _ _ _ HcΘ El); apply ft_entry_ok, (canon_found _ _ El).
  Qed.

  Theorem fgc_term_ok : forall Ξ p, canon_stack Ξ -> fgc_term uf (fs_of Ξ) p = gc_term Θ Ξ p.
  Proof.
    intros * Hc; unfold fgc_term, gc_term; rewrite fgc_resolve_ok, fgc_entry_ok by exact Hc.
    destruct (gc_resolve Θ Ξ p) as [[[] ? ? [] | | | |] |];
      try (destruct (gc_entry Θ Ξ p) as [[| | | | ] |]; reflexivity); reflexivity.
  Qed.

  Theorem fgc_record_ok : forall Ξ p, canon_stack Ξ -> fgc_record uf (fs_of Ξ) p = record_lookup Θ Ξ p.
  Proof.
    intros * Hc; unfold fgc_record, record_lookup; rewrite fs_find_record_of, fgc_entry_ok by exact Hc.
    destruct (gs_find_record Ξ p); [ reflexivity |].
    destruct (gc_entry Θ Ξ p) as [[| | | | ] |]; reflexivity.
  Qed.

  Theorem fgc_unit_ok : forall Ξ H, canon_stack Ξ -> fgc_unit uf (fs_of Ξ) H = option_map tr_loc (gc_unit Θ Ξ H).
  Proof.
    intros * Hc0; pose proof (canon_stack_closed _ Hc0) as Hc; unfold fgc_unit, gc_unit.
    destruct (mod_qname H) as [mp |]; [| reflexivity ].
    rewrite fs_find_ind_of, fs_find_record_of.
    destruct (fs_find_tele (fs_of Ξ) mp) as [[[f ip] T] |] eqn:Ef.
    - destruct (fs_find_tele_kind _ _ _ _ _ Ef) as (mq & U & T' & Eg & ->).
      pose proof (fs_find_tele_some Ξ mp) as Hs; rewrite Ef, Eg in Hs.
      destruct Hs as (_ & _ & _ & ->); rewrite Eg.
      assert (HU : frame_closed U).
      { clear -Hc Eg; induction Hc as [| [[mp' K'] U'] Ξ HU' _ IH]; cbn in Eg; [ discriminate |].
        destruct (qname_strip mp' mp); [ injection Eg as -> _ _; exact HU' | exact (IH Eg) ]. }
      destruct ip as [| x ip]; [| reflexivity ].
      destruct U as [Δ [[|] Φ | E]]; cbn in HU; try contradiction; cbn [tr_frame ff_params ff_body gu_params gu_mod].
      destruct (gs_find_ind Ξ mp), (gs_find_record Ξ mp); reflexivity.
    - pose proof (fs_find_tele_some Ξ mp) as Hs; rewrite Ef in Hs.
      destruct (gs_find_tele Ξ mp) as [[[U ip] T] |]; [ contradiction |].
      rewrite Huf; destruct (q_chain mp); [| reflexivity ].
      destruct (gds_lookup Θ (q_unit mp)) as [[Δ [[|] Φ | E]] |]; reflexivity.
  Qed.
End LookupsOk.


(** ** Well-Formed Contexts Are Canonical

    Freshness ([wf_gmod_ext], [wf_gstack_file]) and the absence of local
    opens in global bodies make every filed unit and every open frame
    canonical, so decoding undoes the translation on them. *)
Lemma canon_of_wf_gmod :
  (forall Θ Ξ mp E, Θ ⍮ Ξ ⍮ mp ⊢ᵉ E -> canon_entry E) /\
  (forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> canon_mod Φ).
Proof.
  apply global_wf_mut_ind; intros; cbn; auto.
Qed.

(** A well-formed global context is canonical. *)
Theorem canon_of_wf : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> canon_deps Θ /\ canon_stack Ξ.
Proof.
  intros Θ Ξ H; induction H as [| Θ fp U H [IHΘ IHΞ] | Θ Ξ mp K Δ Φ H [IHΘ IHΞ] HΦ Hfr].
  - split; [ exact I | constructor ].
  - destruct (wf_gstack_file_inv Θ fp U (wf_gstack_file _ _ _ H)) as (_ & _ & Hn).
    inversion IHΞ as [| ? ? HU _]; subst.
    split; [ cbn; split; [ exact Hn | split; [| exact IHΘ ] ] | constructor ].
    destruct U as [Δ [[|] Φ | E]]; cbn in HU |- *; tauto.
  - split; [ exact IHΘ | constructor; [ exact (proj2 canon_of_wf_gmod _ _ _ _ _ _ HΦ) | exact IHΞ ] ].
Qed.

(** ** What Canonical Contexts Find Is Canonical *)

Section CanonLookups.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypotheses (HcΘ : canon_deps Θ) (HcΞ : canon_stack Ξ).

  (** An entry found *)
  Lemma canon_gc_entry : forall p E, gc_entry Θ Ξ p = Some E -> canon_entry E.
  Proof.
    intros * He; unfold gc_entry, gc_entry_u in He.
    destruct (gs_find Ξ p) as [[U ip] |] eqn:Eg.
    - exact (canon_gm_entry _ _ _ (canon_frame_mod _ (canon_gs_find _ _ _ _ HcΞ Eg)) He).
    - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:El; [| discriminate ].
      exact (canon_gm_entry _ _ _ (canon_unit_mod _ (canon_deps_lookup _ _ _ HcΘ El)) He).
  Qed.

  (** A body module found *)
  Lemma canon_gc_body : forall p T Φ, gc_body Θ Ξ p = Some (T, Φ) -> canon_mod Φ.
  Proof.
    intros * Hb; unfold gc_body in Hb.
    destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |] eqn:Eg; [ discriminate | |].
    - exact (canon_subbody _ _ _ _ _ _ (canon_frame_mod _ (canon_gs_find_tele _ _ _ _ _ HcΞ Eg)) Hb).
    - destruct (gds_lookup Θ (q_unit p)) as [U |] eqn:El; [| discriminate ].
      exact (canon_body _ _ _ _ _ (canon_unit_mod _ (canon_deps_lookup _ _ _ HcΘ El)) Hb).
  Qed.

  (** An open frame found *)
  Lemma canon_gc_frame : forall p T Φ, gc_frame Ξ p = Some (T, Φ) -> canon_mod Φ.
  Proof.
    intros * Hf; unfold gc_frame in Hf.
    destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ0 | E]] [| x ip]] T0] |] eqn:Eg; try discriminate.
    injection Hf as _ <-; exact (canon_frame_mod _ (canon_gs_find_tele _ _ _ _ _ HcΞ Eg)).
  Qed.

  (** Where a module is stored *)
  Lemma canon_gc_loc : forall p T Φ, gc_loc Θ Ξ p = Some (T, Φ) -> canon_mod Φ.
  Proof.
    intros * Hl; unfold gc_loc in Hl.
    destruct (gc_frame Ξ p) as [[T0 Φ0] |] eqn:Ef; [ injection Hl as _ <-; exact (canon_gc_frame _ _ _ Ef) |].
    exact (canon_gc_body _ _ _ Hl).
  Qed.

  (** A stored unit found *)
  Lemma canon_gc_unit : forall H T Φ, gc_unit Θ Ξ H = Some (T, Φ) -> canon_mod Φ.
  Proof.
    intros * Hu; unfold gc_unit in Hu.
    destruct (mod_qname H) as [mp |]; [| discriminate ].
    destruct (gs_find_tele Ξ mp) as [[[U [| x ip]] T0] |] eqn:Eg; try discriminate.
    - destruct U as [Δ [[|] Φ0 | E]], (gs_find_ind Ξ mp), (gs_find_record Ξ mp); try discriminate.
      injection Hu as _ <-; exact (canon_frame_mod _ (canon_gs_find_tele _ _ _ _ _ HcΞ Eg)).
    - destruct (q_chain mp); [| discriminate ].
      destruct (gds_lookup Θ (q_unit mp)) as [[Δ [[|] Φ0 | E]] |] eqn:El; try discriminate.
      injection Hu as _ <-; exact (canon_unit_mod _ (canon_deps_lookup _ _ _ HcΘ El)).
  Qed.
End CanonLookups.

(** A located body, decoded *)
Definition dec_loc (r : (ctx * ftrie)%type) : (ctx * gmod)%type := (fst r, dec_mod (snd r)).

(** Decoding undoes the translation of a canonical located body. *)
Lemma dec_tr_loc : forall r, canon_mod (snd r) -> dec_loc (tr_loc r) = r.
Proof. intros [T Φ] H; unfold dec_loc, tr_loc; cbn in *; rewrite dec_tr_mod by exact H; reflexivity. Qed.

