(** * Renaming Normal Forms

    A weakening [φ] acts on normal and neutral forms as it acts on terms: it
    renames the variables, and lifts itself under binders ([nf_wk]).  It
    commutes with [nf_to_exp] ([nf_wk_to_exp]).

    The point of this file is that an *order-preserving* renaming also
    commutes with the canonical form of a level ([lvl_canon_wk]): the order
    on atoms ([ne_cmp]) is lexicographic on a coding in which a variable is
    coded by its index, and an order-preserving renaming does not change the
    result of comparing two indices at the same binder depth
    ([ne_cmp_wk]).  So the renaming of a canonical level is canonical, and
    renaming a normal form gives a normal form.

    This is the syntactic half of the readback-shift lemma in
    [Core.Semantic.Rename]. *)
From Stdlib Require Import Arith Lia List PeanoNat.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Levels Require Import Levels.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Core.Semantic Require Import Domain.
Import Syntax_Notations.

(** A normal form renamed by the weakening [φ]; mutually, a neutral.  A
    block's motive and a branch's body are under their binders. *)
Fixpoint nf_wk (φ : wk) (W : nf) {struct W} : nf :=
  match W with
  | nf_typ i => nf_typ i
  | nf_univ c xs => nf_univ c (List.map (map_level_atom (ne_wk φ)) xs)
  | nf_level n => nf_level n
  | nf_lvl c xs => nf_lvl c (List.map (map_level_atom (ne_wk φ)) xs)
  | nf_True => nf_True
  | nf_true => nf_true
  | nf_False => nf_False
  | nf_pi A B => nf_pi (nf_wk φ A) (nf_wk (wk_q φ) B)
  | nf_fn A M => nf_fn (nf_wk φ A) (nf_wk (wk_q φ) M)
  | nf_indty p k Ms => nf_indty p k (List.map (nf_wk φ) Ms)
  | nf_con p k c Ms => nf_con p k c (List.map (nf_wk φ) Ms)
  | nf_neut u => nf_neut (ne_wk φ u)
  | nf_record p Ms => nf_record p (List.map (nf_wk φ) Ms)
  | nf_tuple p Ms fs Ns => nf_tuple p (List.map (nf_wk φ) Ms) fs (List.map (nf_wk φ) Ns)
  end
with ne_wk (φ : wk) (u : ne) {struct u} : ne :=
  match u with
  | ne_exfalso A u => ne_exfalso (nf_wk (wk_q φ) A) (ne_wk φ u)
  | ne_elim p Us m Bks u =>
      ne_elim p (List.map (nf_wk φ) Us) m (List.map (map_normal_block (fun n => nf_wk (wk_qn n φ))) Bks) (ne_wk φ u)
  | ne_app u W => ne_app (ne_wk φ u) (nf_wk φ W)
  | ne_var x => ne_var (φ x)
  | ne_glob p => ne_glob p
  | ne_proj f u => ne_proj f (ne_wk φ u)
  end.

Definition lvl_wk (φ : wk) (l : lvl) : lvl := (fst l, List.map (map_level_atom (ne_wk φ)) (snd l)).

Lemma nf_lvl_of_wk : forall φ l, nf_wk φ (nf_lvl_of l) = nf_lvl_of (lvl_wk φ l).
Proof. reflexivity. Qed.

Lemma nf_univ_of_wk : forall φ l, nf_wk φ (nf_univ_of l) = nf_univ_of (lvl_wk φ l).
Proof. reflexivity. Qed.

(** ** The Renaming of the Term a Normal Form Denotes *)

Lemma nf_wk_to_exp :
  (forall W φ, nf_to_exp (nf_wk φ W) = (nf_to_exp W)[φ]ʷ) /\
  (forall u φ, ne_to_exp (ne_wk φ u) = (ne_to_exp u)[φ]ʷ).
Proof.
  apply nf_ne_ind; intros; cbn [nf_wk ne_wk nf_to_exp ne_to_exp exp_wk]; rewrite ?apps_exp_wk, ?lvl_exp_of_wk;
    (** A global is closed, so the renaming does not touch it. *)
    try solve [ symmetry; apply qname_term_wk ];
    repeat (f_equal; try solve [ eauto ]).
  (** A tuple: its values through [combine]. *)
  all: try match goal with
           | |- combine ?fs _ = List.map (fun f => (fst f, (snd f)[?φ]ʷ)) _ =>
               rewrite <- (combine_map_r (fun N => N[φ]ʷ)); f_equal
           end.
  all: nested_elements; cbn; repeat (f_equal; try solve [ eauto ]).
  (** A block's branches. *)
  all: nested_elements; cbn; f_equal; eauto.
Qed.

(** ** Order-Preserving Renamings Preserve the Order on Atoms

    The coding of a normal form is a node whose sibling is the continuation
    [t], so comparing two codings compares the forms first and the
    continuations only if the forms are equal ([nf_code_cmp]).  The
    continuation of [list_code] sits at the end of its list, with the same
    effect ([list_code_cmp]). *)
Definition cmp_then (c c' : comparison) : comparison :=
  match c with Eq => c' | _ => c end.

(** The order on normal forms: of their codings. *)
Definition nf_cmp (M N : nf) : comparison := lt_cmp (nf_code M ltree_nil) (nf_code N ltree_nil).
(** The order on lists, each element coded by [f]: of their codings. *)
Definition list_cmp {A : Set} (f : A -> ltree) (l l' : list A) : comparison :=
  lt_cmp (list_code f l ltree_nil) (list_code f l' ltree_nil).

Lemma cmp_then_eq : forall c, cmp_then c Eq = c.
Proof. intros []; reflexivity. Qed.

Lemma lt_cmp_node : forall a c t b c' t',
    lt_cmp (ltree_node a c t) (ltree_node b c' t')
    = cmp_then (Nat.compare a b) (cmp_then (lt_cmp c c') (lt_cmp t t')).
Proof. intros; cbn; destruct (Nat.compare a b), (lt_cmp c c'); reflexivity. Qed.

Lemma lt_cmp_node_nil : forall a c t b c' t',
    lt_cmp (ltree_node a c t) (ltree_node b c' t')
    = cmp_then (lt_cmp (ltree_node a c ltree_nil) (ltree_node b c' ltree_nil)) (lt_cmp t t').
Proof.
  intros; rewrite !lt_cmp_node; cbn [lt_cmp].
  destruct (Nat.compare a b), (lt_cmp c c'); reflexivity.
Qed.

Lemma nf_code_node : forall M t, exists a c, nf_code M t = ltree_node a c t /\ nf_code M ltree_nil = ltree_node a c ltree_nil.
Proof. intros [] t; repeat match goal with p : o2 |- _ => destruct p end; cbn; eauto. Qed.

Lemma ne_code_node : forall m t, exists a c, ne_code m t = ltree_node a c t /\ ne_code m ltree_nil = ltree_node a c ltree_nil.
Proof. intros [] t; cbn; eauto. Qed.

Lemma nf_code_cmp : forall M N t t',
    lt_cmp (nf_code M t) (nf_code N t') = cmp_then (nf_cmp M N) (lt_cmp t t').
Proof.
  intros; unfold nf_cmp.
  destruct (nf_code_node M t) as (a & c & -> & ->), (nf_code_node N t') as (b & c' & -> & ->).
  apply lt_cmp_node_nil.
Qed.

Lemma ne_code_cmp : forall m n t t',
    lt_cmp (ne_code m t) (ne_code n t') = cmp_then (ne_cmp m n) (lt_cmp t t').
Proof.
  intros; unfold ne_cmp.
  destruct (ne_code_node m t) as (a & c & -> & ->), (ne_code_node n t') as (b & c' & -> & ->).
  apply lt_cmp_node_nil.
Qed.

Lemma cmp_then_assoc : forall a b c, cmp_then (cmp_then a b) c = cmp_then a (cmp_then b c).
Proof. intros [] [] []; reflexivity. Qed.

Lemma list_code_cmp {A : Set} (f : A -> ltree) : forall l l' t t',
    lt_cmp (list_code f l t) (list_code f l' t') = cmp_then (list_cmp f l l') (lt_cmp t t').
Proof.
  unfold list_cmp; induction l as [| x l IH]; intros [| y l'] t t'; cbn [list_code];
    rewrite ?lt_cmp_node; cbn [Nat.compare lt_cmp cmp_then]; try reflexivity.
  rewrite (IH l' t t'), (IH l' ltree_nil ltree_nil); cbn [lt_cmp]; rewrite !cmp_then_eq, !cmp_then_assoc; reflexivity.
Qed.

(** A map that preserves the order on the elements of a list preserves
    the order on the list. *)
Lemma list_cmp_map {A : Set} (P : A -> Set) (f : A -> ltree) (g : A -> A) : forall l,
    list_all A P l -> (forall x, P x -> forall y, lt_cmp (f (g x)) (f (g y)) = lt_cmp (f x) (f y)) ->
    forall l', list_cmp f (List.map g l) (List.map g l') = list_cmp f l l'.
Proof.
  unfold list_cmp; intros l Hl Hg; induction Hl as [| x Hx l Hl IH]; intros [| y l']; cbn [List.map list_code];
    rewrite ?lt_cmp_node; cbn [Nat.compare lt_cmp cmp_then]; try reflexivity.
  rewrite (Hg x Hx y), (IH l'); reflexivity.
Qed.

Lemma wk_mono_qn : forall n φ, wk_mono φ -> wk_mono (wk_qn n φ).
Proof. induction n; intros; cbn; [ assumption | apply wk_mono_q; auto ]. Qed.

(** Every coding is compared by [lt_cmp] of a node, so the comparisons
    reduce to [cmp_then] of the comparisons of the parts. *)
Ltac cmp_norm :=
  unfold nf_cmp, ne_cmp;
  cbn [nf_code ne_code nf_wk ne_wk];
  rewrite ?lt_cmp_node; cbn [lt_cmp];
  repeat first [ rewrite nf_code_cmp | rewrite ne_code_cmp | rewrite list_code_cmp
                 (** a node a coding continues with, as the uniform parameters of a
                     stuck eliminator are *)
               | rewrite lt_cmp_node ]; cbn [lt_cmp];
  rewrite ?cmp_then_eq.

Lemma compare_mono : forall φ, wk_mono φ -> forall x y, Nat.compare (φ x) (φ y) = Nat.compare x y.
Proof.
  intros φ Hφ x y.
  destruct (Nat.compare_spec x y) as [-> | Hl | Hl];
    [ apply Nat.compare_refl | apply Nat.compare_lt_iff | apply Nat.compare_gt_iff ];
    apply Hφ; assumption.
Qed.

(** The side condition of [list_cmp_map] at the elements of a normal form:
    a normal form, an atom, or a block (whose motive and branches are
    compared at equal binder counts only). *)
Ltac elem_cmp_wk :=
  let x := fresh "x" in let Hx := fresh "Hx" in let y := fresh "y" in
  intros x Hx y; cbv beta;
  match goal with Hφ : wk_mono ?φ |- _ =>
    first
      [ (** a normal form *)
        exact (Hx _ y Hφ)
      | (** an atom *)
        let a := fresh "a" in let Ha := fresh "Ha" in let b := fresh "b" in let E := fresh "E" in
        destruct Hx as [? ? a Ha]; destruct y as [? ? b];
        unfold atom_code, map_level_atom; cbn [atom_offset atom_sort atom_level]; rewrite !lt_cmp_node;
        pose proof (Ha φ b Hφ) as E; unfold ne_cmp in E; rewrite E; reflexivity
      | (** a block *)
        let n := fresh "n" in let A := fresh "A" in let HA := fresh "HA" in let brs := fresh "brs" in
        let Hbrs := fresh "Hbrs" in let n' := fresh "n" in let A' := fresh "A" in let E := fresh "E" in
        destruct Hx as [n A HA brs Hbrs]; destruct y as [n' A' ?];
        unfold block_code, map_normal_block; cbn [block_arity block_motive block_branches]; rewrite !lt_cmp_node;
        destruct (Nat.compare_spec n n') as [<- | ? | ?]; cbn [cmp_then]; [| reflexivity | reflexivity ];
        pose proof (HA (wk_qn n φ) A' (wk_mono_qn _ _ Hφ)) as E; unfold nf_cmp in E; rewrite E;
        rewrite !list_code_cmp; rewrite (list_cmp_map _ _ _ brs Hbrs); [ reflexivity |];
        let z := fresh "z" in let Hz := fresh "Hz" in let w := fresh "w" in
        let m := fresh "m" in let B := fresh "B" in let HB := fresh "HB" in let m' := fresh "m" in
        let B' := fresh "B" in let E' := fresh "E" in
        intros z Hz w; destruct Hz as [? m B HB]; destruct w as [? m' B'];
        unfold branch_code, map_normal_branch; cbn [branch_constructor branch_arity branch_body]; rewrite !lt_cmp_node;
        destruct (Nat.compare_spec m m') as [<- | ? | ?]; cbn [cmp_then]; [| reflexivity | reflexivity ];
        pose proof (HB (wk_qn m φ) B' (wk_mono_qn _ _ Hφ)) as E'; unfold nf_cmp in E'; rewrite E';
        reflexivity ]
  end.

Lemma nf_cmp_wk :
  (forall M φ N, wk_mono φ -> nf_cmp (nf_wk φ M) (nf_wk φ N) = nf_cmp M N) /\
  (forall m φ n, wk_mono φ -> ne_cmp (ne_wk φ m) (ne_wk φ n) = ne_cmp m n).
Proof.
  apply nf_ne_ind; intros;
    match goal with
    | |- nf_cmp _ (nf_wk _ ?N) = _ => destruct N
    | |- ne_cmp _ (ne_wk _ ?N) = _ => destruct N
    end;
    repeat match goal with p : o2 |- _ => destruct p end;
    cmp_norm; try reflexivity.
  (** The lists, element by element. *)
  all: repeat match goal with
         | Hl : list_all _ _ ?l |- context [ list_cmp ?f (List.map ?g ?l) (List.map ?g ?l') ] =>
             rewrite (list_cmp_map _ f g l Hl) by elem_cmp_wk
         end.
  all: repeat match goal with
         | IH : forall φ N, wk_mono φ -> ?cmp (?wk φ ?M) (?wk φ N) = _ |- context [ ?cmp (?wk ?ψ ?M) (?wk ?ψ ?N') ] =>
             rewrite (IH ψ N') by (repeat apply wk_mono_q; assumption)
         end; try reflexivity.
  (** A variable: an order-preserving renaming preserves the comparison. *)
  all: try (match goal with H : wk_mono ?φ |- context [Nat.compare (?φ _) (?φ _)] => rewrite (compare_mono φ H) end; reflexivity).
Qed.

Corollary ne_cmp_wk : forall φ m n, wk_mono φ -> ne_cmp (ne_wk φ m) (ne_wk φ n) = ne_cmp m n.
Proof. intros; apply (proj2 nf_cmp_wk); assumption. Qed.

(** ** Order-Preserving Renamings Commute with the Canonical Form *)

Lemma at_cmp_wk : forall φ a s b t, wk_mono φ -> at_cmp (ne_wk φ a) s (ne_wk φ b) t = at_cmp a s b t.
Proof. intros; unfold at_cmp; rewrite ne_cmp_wk by assumption; reflexivity. Qed.

Lemma level_atoms_insert_wk : forall φ, wk_mono φ ->
    forall k s a ys, List.map (map_level_atom (ne_wk φ)) (level_atoms_insert k s a ys)
                     = level_atoms_insert k s (ne_wk φ a) (List.map (map_level_atom (ne_wk φ)) ys).
Proof.
  intros φ Hφ k s a; induction ys as [| [k' t b] r IH]; cbn [level_atoms_insert List.map]; [ reflexivity |].
  unfold map_level_atom at 2; cbn [atom_offset atom_sort atom_level].
  rewrite at_cmp_wk by assumption.
  destruct (at_cmp a s b t); cbn [List.map]; rewrite ?IH; reflexivity.
Qed.

Lemma level_atoms_sort_wk : forall φ, wk_mono φ -> forall xs,
    List.map (map_level_atom (ne_wk φ)) (level_atoms_sort xs) = level_atoms_sort (List.map (map_level_atom (ne_wk φ)) xs).
Proof.
  intros φ Hφ; induction xs as [| [k s a] r IH]; cbn [level_atoms_sort List.map]; [ reflexivity |].
  rewrite level_atoms_insert_wk, IH by assumption; reflexivity.
Qed.

Lemma level_atoms_keep_wk : forall φ c xs,
    List.map (map_level_atom (ne_wk φ)) (level_atoms_keep c xs) = level_atoms_keep c (List.map (map_level_atom (ne_wk φ)) xs).
Proof.
  intros φ c; induction xs as [| [k s a] r IH]; cbn [level_atoms_keep List.map]; [ reflexivity |].
  unfold map_level_atom at 2; cbn [atom_offset atom_sort atom_level level_atoms_keep].
  destruct (fst c <=? s); cbn [List.map]; rewrite IH; reflexivity.
Qed.

Lemma level_atoms_max_offset_wk : forall φ xs, level_atoms_max_offset (List.map (map_level_atom (ne_wk φ)) xs) = level_atoms_max_offset xs.
Proof. intros φ; induction xs as [| [k s a] r IH]; cbn; congruence. Qed.

Theorem lvl_canon_wk : forall φ, wk_mono φ -> forall l, lvl_canon (lvl_wk φ l) = lvl_wk φ (lvl_canon l).
Proof.
  intros φ Hφ [c xs]; unfold lvl_canon, lvl_wk; cbn [fst snd].
  rewrite <- level_atoms_sort_wk, <- level_atoms_keep_wk, level_atoms_max_offset_wk by assumption; reflexivity.
Qed.

(** ** Freshness

    A renaming that never hits [k] produces normal forms fresh at [k]. *)

Lemma nf_wk_fresh :
  (forall W k φ, wk_avoids k φ -> nf_fresh k (nf_wk φ W)) /\
  (forall u k φ, wk_avoids k φ -> ne_fresh k (ne_wk φ u)).
Proof.
  apply nf_ne_ind; intros; cbn; rewrite ?all_list_map; repeat split; eauto 6 using wk_avoids_q, wk_avoids_qn.
  all: nested_elements; cbn; unfold normal_block_forall; cbn; rewrite ?all_list_map;
    repeat split; eauto 6 using wk_avoids_q, wk_avoids_qn.
  all: nested_elements; cbn; eauto 6 using wk_avoids_q, wk_avoids_qn.
Qed.

(** ** Injectivity

    An injective renaming is injective on normal forms. *)
Definition wk_inj (φ : wk) : Prop := forall x y, φ x = φ y -> x = y.

Lemma wk_inj_q : forall φ, wk_inj φ -> wk_inj (wk_q φ).
Proof. intros φ Hφ [| x] [| y]; cbn; intros H; try discriminate; [ reflexivity | f_equal; apply Hφ; lia ]. Qed.

Lemma wk_inj_shift : wk_inj wk_shift.
Proof. intros x y; cbn; lia. Qed.

Lemma wk_inj_qn : forall n φ, wk_inj φ -> wk_inj (wk_qn n φ).
Proof. induction n; intros; cbn; [ assumption | apply wk_inj_q; auto ]. Qed.

(** A map injective on the elements of a list is injective on the list. *)
Lemma list_all_map_inj {A B : Set} (P : A -> Set) (g : A -> B) : forall l,
    list_all A P l -> (forall x, P x -> forall y, g x = g y -> x = y) ->
    forall l', List.map g l = List.map g l' -> l = l'.
Proof.
  intros l Hl Hg; induction Hl as [| x Hx l Hl IH]; intros [| y l'] H; cbn in H; try discriminate; [ reflexivity |].
  injection H as Hxy Hr; f_equal; [ eapply Hg; eassumption | apply IH; exact Hr ].
Qed.

Lemma nf_wk_inj :
  (forall W φ W', wk_inj φ -> nf_wk φ W = nf_wk φ W' -> W = W') /\
  (forall u φ u', wk_inj φ -> ne_wk φ u = ne_wk φ u' -> u = u').
Proof.
  apply nf_ne_ind; intros;
    match goal with
    | H : nf_wk _ _ = nf_wk _ ?W' |- _ => destruct W'; cbn in H; inversion H; subst
    | H : ne_wk _ _ = ne_wk _ ?W' |- _ => destruct W'; cbn in H; inversion H; subst
    end;
    f_equal; eauto using wk_inj_q, wk_inj_qn.
  (** The lists, element by element. *)
  all: eapply list_all_map_inj; [ eassumption | | eassumption ].
  all: let x := fresh "x" in let Hx := fresh "Hx" in let y := fresh "y" in let Hy := fresh "Hy" in
       intros x Hx y Hy; try solve [ eauto ].
  (** An atom. *)
  all: try (destruct Hx; destruct y; unfold map_level_atom in Hy; cbn in Hy; injection Hy as -> -> Hy;
            f_equal; eauto).
  (** A block: its motive and its branches. *)
  all: destruct Hx as [n A HA brs Hbrs]; destruct y as [n' A' brs']; unfold map_normal_block in Hy; cbn in Hy;
    injection Hy as -> Hy Hy'; f_equal; [ eauto using wk_inj_qn |].
  all: eapply list_all_map_inj; [ exact Hbrs | | exact Hy' ].
  all: let z := fresh "z" in let Hz := fresh "Hz" in let w := fresh "w" in let Hw := fresh "Hw" in
       intros z Hz w Hw; destruct Hz; destruct w; unfold map_normal_branch in Hw; cbn in Hw;
       injection Hw as -> -> Hw; f_equal; eauto using wk_inj_qn.
Qed.
