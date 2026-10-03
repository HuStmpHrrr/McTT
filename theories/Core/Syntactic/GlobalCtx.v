From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Syntax.
Import Syntax_Notations Wk_Notations.

Generalizable All Variables.

(** * Global Contexts

    Names have two levels, spelled differently in the surface language and
    represented differently here.  [X::Y::Z] names a unit; units are not
    declared inside one another, so the [::] level is flat.  [X.W] names an
    internal module of one unit; internal modules nest, so the [.] level is a
    module.

    The [::] level is a list of dependency levels, most recent first: a unit is
    filed above exactly the levels it may depend on, which rules out cycles.

    A member is stored closed: [wf_gentry_def] generalizes its type and body
    over the parameters of every enclosing module, outermost first.  Nothing
    about a member depends on where it is read from, so resolving a path hands
    the stored entry back unchanged, and evaluation needs no syntactic
    operations. *)

(** ** Modules

    A module is a sequence of entries, in declaration order: definitions and
    nested modules (see [gentry] in [Syntax]).  A nested module of a filed
    unit is a body [ge_body Δ Φ], with [Δ] the parameters it adds to the ones
    it is already under, or an alias [ge_mod (gu_mk T (md_alias E))], with [T]
    its full telescope. *)

Module GlobalCtx_Notations.

  Notation "⋄" := gm_nil.
  Notation "Φ ⊳ x ↦ E" := (gm_ext Φ x E) (at level 50, x at level 0).

End GlobalCtx_Notations.

Import GlobalCtx_Notations.

(** The names [Φ] declares, outermost last, and a name not among them. *)
Fixpoint gm_names (Φ : gmod) : list string :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ' x _ => x :: gm_names Φ'
  | gm_check Φ' _ => gm_names Φ'
  end.

Definition gm_fresh (x : string) (Φ : gmod) : Prop :=
  ~ List.In x (gm_names Φ).

Lemma gm_fresh_ext : forall x Φ y E,
    gm_fresh x (gm_ext Φ y E) <-> x <> y /\ gm_fresh x Φ.
Proof.
  unfold gm_fresh; simpl; intros *; split; [ intuition | intuition congruence ].
Qed.

(** ** Resolution in a Module

    The newest entry of a name decides; names are fresh in a well-formed
    module, so there is no other.  Only a definition is handed back, and only
    through body modules: a path through an alias resolves to nothing here (see
    [gm_module]). *)
Fixpoint gm_resolve (Φ : gmod) (ip : list string) : option gentry :=
  match Φ with
  | gm_nil => None
  | gm_ext Φ y E =>
      match ip with
      | nil => None
      | x :: ip' =>
          if String.eqb x y
          then match ip', E with
               | nil, ge_def _ _ _ _ => Some E
               | _ :: _, ge_mod (gu_mk _ (md_body Φ')) => gm_resolve Φ' ip'
               | _, _ => None
               end
          else gm_resolve Φ ip
      end
  | gm_check Φ _ => gm_resolve Φ ip
  end.

Lemma gm_resolve_def : forall Φ ip E,
    gm_resolve Φ ip = Some E -> exists b pv A B, E = ge_def b pv A B.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] ip E0 H; cbn in H; [ discriminate | | eapply IH; exact H ].
  destruct ip as [| x ip']; [ discriminate |].
  destruct (String.eqb x y); [| eapply IH; exact H ].
  destruct ip' as [| z ip''], E as [b pv A B | [Δ' [Φ' | E']]]; try discriminate.
  - injection H as <-; eauto.
  - eapply IH; exact H.
Qed.

(** What resolves starts with a declared name. *)
Lemma gm_resolve_head : forall Φ ip E,
    gm_resolve Φ ip = Some E -> exists x ip', ip = x :: ip' /\ List.In x (gm_names Φ).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] ip E0 H; cbn in H; [ discriminate | | exact (IH _ _ _ H) ].
  destruct ip as [| x ip']; [ discriminate |].
  destruct (String.eqb_spec x y) as [-> |].
  - exists y, ip'; cbn; auto.
  - destruct (IH _ _ _ H) as (z & ip'' & [= -> ->] & Hin); exists z, ip''; cbn; auto.
Qed.

(** An entry with a fresh name shadows nothing. *)
Lemma gm_resolve_ext_fresh : forall Φ x E ip E0,
    gm_fresh x Φ ->
    gm_resolve Φ ip = Some E0 ->
    gm_resolve (Φ ⊳ x ↦ E) ip = Some E0.
Proof.
  intros * Hf Hr; cbn.
  destruct (gm_resolve_head _ _ _ Hr) as (z & ip' & -> & Hin).
  destruct (String.eqb_spec z x) as [-> |]; [ contradiction | assumption ].
Qed.

Lemma gm_resolve_nil : forall Φ, gm_resolve Φ nil = None.
Proof. induction Φ; cbn; auto. Qed.

Lemma gm_resolve_in : forall Φ x Δ' Φ' ip E0,
    gm_resolve Φ' ip = Some E0 ->
    gm_resolve (Φ ⊳ x ↦ ge_body Δ' Φ') (x :: ip) = Some E0.
Proof.
  intros * Hr; cbn; rewrite String.eqb_refl.
  destruct ip; [ rewrite gm_resolve_nil in Hr; discriminate | assumption ].
Qed.

(** ** Resolution of a Module

    What a module path denotes: a body module with its full telescope, or the
    first alias on the path, with the rest of the chain.  An alias is stored
    closed, over its full telescope, so the rest of the chain is read inside
    it. *)
Inductive modres : Set :=
| mr_body : ctx -> modres
| mr_alias : gunit -> list string -> modres.

(** The submodule [x :: ip] of [Φ], whose enclosing telescope is [T]. *)
Fixpoint gm_submodule (T : ctx) (Φ : gmod) (x : string) (ip : list string) : option modres :=
  match Φ with
  | gm_nil => None
  | gm_check Φ0 _ => gm_submodule T Φ0 x ip
  | gm_ext Φ0 y E =>
      if String.eqb x y then
        match E with
        | ge_mod (gu_mk Δ (md_body Φ')) =>
            match ip with
            | nil => Some (mr_body (Δ ++ T))
            | z :: ip' => gm_submodule (Δ ++ T) Φ' z ip'
            end
        | ge_mod (gu_mk Δ (md_alias E')) => Some (mr_alias (gu_mk Δ (md_alias E')) ip)
        | ge_def _ _ _ _ => None
        end
      else gm_submodule T Φ0 x ip
  end.

Definition gm_module (T : ctx) (Φ : gmod) (ip : list string) : option modres :=
  match ip with
  | nil => Some (mr_body T)
  | x :: ip' => gm_submodule T Φ x ip'
  end.

Lemma gm_submodule_head : forall Φ T x ip r,
    gm_submodule T Φ x ip = Some r -> List.In x (gm_names Φ).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H; [ discriminate | | exact (IH _ _ _ _ _ H) ].
  destruct (String.eqb_spec x y) as [-> |]; [ cbn; auto |].
  cbn; right; exact (IH _ _ _ _ _ H).
Qed.

Lemma gm_submodule_ext_fresh : forall Φ T x E y ip r,
    gm_fresh x Φ ->
    gm_submodule T Φ y ip = Some r ->
    gm_submodule T (Φ ⊳ x ↦ E) y ip = Some r.
Proof.
  intros * Hf Hr; cbn.
  pose proof (gm_submodule_head _ _ _ _ _ Hr).
  destruct (String.eqb_spec y x) as [-> |]; [ contradiction | assumption ].
Qed.

Lemma gm_submodule_in : forall Φ T x Δ' Φ' ip r,
    gm_module (Δ' ++ T) Φ' ip = Some r ->
    gm_submodule T (Φ ⊳ x ↦ ge_body Δ' Φ') x ip = Some r.
Proof.
  intros * Hr; cbn; rewrite String.eqb_refl.
  destruct ip; cbn in Hr; assumption.
Qed.

(** The body module [x :: ip] of [Φ], with its full telescope. *)
Fixpoint gm_subbody (T : ctx) (Φ : gmod) (x : string) (ip : list string) : option (ctx * gmod) :=
  match Φ with
  | gm_nil => None
  | gm_check Φ0 _ => gm_subbody T Φ0 x ip
  | gm_ext Φ0 y E =>
      if String.eqb x y then
        match E with
        | ge_mod (gu_mk Δ (md_body Φ')) =>
            match ip with
            | nil => Some (Δ ++ T, Φ')
            | z :: ip' => gm_subbody (Δ ++ T) Φ' z ip'
            end
        | _ => None
        end
      else gm_subbody T Φ0 x ip
  end.

Definition gm_body (T : ctx) (Φ : gmod) (ip : list string) : option (ctx * gmod) :=
  match ip with
  | nil => Some (T, Φ)
  | x :: ip' => gm_subbody T Φ x ip'
  end.

Lemma gm_subbody_head : forall Φ T x ip r, gm_subbody T Φ x ip = Some r -> List.In x (gm_names Φ).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H; [ discriminate | | exact (IH _ _ _ _ _ H) ].
  destruct (String.eqb_spec x y) as [-> |]; [ cbn; auto |].
  cbn; right; exact (IH _ _ _ _ _ H).
Qed.

Lemma gm_subbody_ext_fresh : forall Φ T x E y ip r,
    gm_fresh x Φ ->
    gm_subbody T Φ y ip = Some r ->
    gm_subbody T (Φ ⊳ x ↦ E) y ip = Some r.
Proof.
  intros * Hf Hr; cbn.
  pose proof (gm_subbody_head _ _ _ _ _ Hr).
  destruct (String.eqb_spec y x) as [-> |]; [ contradiction | assumption ].
Qed.

Lemma gm_subbody_in : forall Φ T x Δ' Φ' ip r,
    gm_body (Δ' ++ T) Φ' ip = Some r ->
    gm_subbody T (Φ ⊳ x ↦ ge_body Δ' Φ') x ip = Some r.
Proof.
  intros * Hr; cbn; rewrite String.eqb_refl.
  destruct ip; cbn in Hr; assumption.
Qed.

(** ** Units

    A unit is a parameterized module in full: the parameters it abstracts over,
    and the module it declares (see [gunit] in [Syntax]).  Units do not nest. *)

Definition path_eq_dec := List.list_eq_dec String.string_dec.

Definition path_beq (fp fq : list string) : bool :=
  if path_eq_dec fp fq then true else false.

Lemma path_beq_refl : forall fp, path_beq fp fp = true.
Proof. intros; unfold path_beq; destruct (path_eq_dec fp fp); congruence. Qed.

Lemma path_beq_true : forall fp fq, path_beq fp fq = true -> fp = fq.
Proof. intros * H; unfold path_beq in H; destruct (path_eq_dec fp fq); congruence. Qed.

Lemma path_beq_false : forall fp fq, fp <> fq -> path_beq fp fq = false.
Proof. intros * H; unfold path_beq; destruct (path_eq_dec fp fq); congruence. Qed.

(** ** Dependency Levels

    One [gdep] is the units of a single level, keyed by absolute path; [gdeps] is
    the levels, highest first. *)
Definition gdep : Set := list (list string * gunit).
Definition gdeps : Set := list gdep.

Definition gd_lookup (d : gdep) (fp : list string) : option gunit :=
  option_map snd (List.find (fun fU => path_beq fp (fst fU)) d).

(** Searching the levels in order is searching their concatenation. *)
Definition gds_lookup (Θ : gdeps) (fp : list string) : option gunit :=
  gd_lookup (List.concat Θ) fp.

(** One [gdeps] is below another when everything filed in it is filed, the
    same, in the other: what filing more units, or merging, preserves. *)
Definition gds_sub (Θ Θ' : gdeps) : Prop :=
  forall fp U, gds_lookup Θ fp = Some U -> gds_lookup Θ' fp = Some U.

Notation "Θ ⊑ Θ'" := (gds_sub Θ Θ') (at level 70) : type_scope.

Lemma gds_sub_refl : forall Θ, gds_sub Θ Θ.
Proof. intros ? ? ? H; exact H. Qed.

Lemma gds_sub_trans : forall Θ1 Θ2 Θ3, gds_sub Θ1 Θ2 -> gds_sub Θ2 Θ3 -> gds_sub Θ1 Θ3.
Proof. intros * H12 H23 ? ? H; apply H23, H12, H. Qed.

Definition gd_fresh (fp : list string) (d : gdep) : Prop :=
  ~ List.In fp (List.map fst d).

Definition gds_fresh (fp : list string) (Θ : gdeps) : Prop :=
  gd_fresh fp (List.concat Θ).

Lemma gd_lookup_in : forall d fp U,
    gd_lookup d fp = Some U ->
    List.In (fp, U) d.
Proof.
  unfold gd_lookup, path_beq; intros * Heq.
  destruct (List.find _ d) as [[fq V] |] eqn:Hf; [| discriminate ].
  injection Heq as <-; apply List.find_some in Hf as [Hin Hb]; simpl in Hb.
  destruct (path_eq_dec fp fq) as [<- |]; [ assumption | discriminate ].
Qed.

Lemma gds_lookup_in : forall Θ fp U,
    gds_lookup Θ fp = Some U ->
    exists d, List.In d Θ /\ List.In (fp, U) d.
Proof.
  unfold gds_lookup; intros * Heq.
  apply (proj1 (List.in_concat _ _)), gd_lookup_in, Heq.
Qed.

Lemma gd_lookup_app_inv : forall d d' fp U,
    gd_lookup (d ++ d') fp = Some U ->
    gd_lookup d fp = Some U \/ gd_lookup d' fp = Some U.
Proof.
  unfold gd_lookup; induction d as [| fV d IH]; simpl; intros * Heq;
    [ now right |].
  destruct (path_beq fp (fst fV)); [ now left | now apply IH ].
Qed.

Lemma gd_lookup_app_l : forall d d' fp U,
    gd_lookup d fp = Some U ->
    gd_lookup (d ++ d') fp = Some U.
Proof.
  unfold gd_lookup; induction d as [| fV d IH]; simpl; intros * Heq; [ discriminate |].
  destruct (path_beq fp (fst fV)); [ assumption | now apply IH ].
Qed.

Lemma gd_lookup_app_none : forall d d' fp,
    gd_lookup d fp = None ->
    gd_lookup (d ++ d') fp = gd_lookup d' fp.
Proof.
  unfold gd_lookup; induction d as [| fV d IH]; cbn; intros * H; [ reflexivity |].
  destruct (path_beq fp (fst fV)); [ discriminate | auto ].
Qed.

Lemma gd_fresh_no_lookup : forall fp d,
    gd_fresh fp d ->
    gd_lookup d fp = None.
Proof.
  unfold gd_fresh, gd_lookup, path_beq; intros * Hfresh.
  destruct (List.find _ d) as [[fq V] |] eqn:Hf; [| reflexivity ].
  exfalso; apply List.find_some in Hf as [Hin Hb]; simpl in Hb.
  destruct (path_eq_dec fp fq) as [<- |]; [| discriminate ].
  exact (Hfresh (List.in_map fst _ _ Hin)).
Qed.

Corollary gds_fresh_no_lookup : forall fp Θ,
    gds_fresh fp Θ ->
    gds_lookup Θ fp = None.
Proof.
  unfold gds_fresh, gds_lookup; auto using gd_fresh_no_lookup.
Qed.

(** Filing a level whose units are fresh below it changes nothing below. *)
Lemma gds_lookup_level : forall Θ d fp U,
    (forall fq V, List.In (fq, V) d -> gds_fresh fq Θ) ->
    gds_lookup Θ fp = Some U ->
    gds_lookup (d :: Θ) fp = Some U.
Proof.
  unfold gds_lookup; intros * Hfr Hl; cbn [List.concat].
  destruct (gd_lookup d fp) as [V |] eqn:Hd.
  - apply gd_lookup_in, Hfr, gds_fresh_no_lookup in Hd; unfold gds_lookup in Hd; congruence.
  - rewrite gd_lookup_app_none; assumption.
Qed.

(** ** The Definition Stack

    The modules open around the point being checked, innermost first, each
    recorded with its own (absolute) module path.  Their parameters are the
    local context members are checked in, [gs_tele]: the innermost frame's
    parameters are bound last, so they come first. *)
Definition gstack : Set := list (path * gunit).

Fixpoint gs_tele (Ξ : gstack) : ctx :=
  match Ξ with
  | nil => nil
  | (_, U) :: Ξ' => gu_params U ++ gs_tele Ξ'
  end.

(** ** Resolution of a Path

    [strip_prefix l m] is [m] with the prefix [l] removed, if it is one. *)
Fixpoint strip_prefix (l m : list string) : option (list string) :=
  match l, m with
  | nil, _ => Some m
  | x :: l', y :: m' => if String.eqb x y then strip_prefix l' m' else None
  | _ :: _, nil => None
  end.

Lemma strip_prefix_app : forall l r, strip_prefix l (l ++ r) = Some r.
Proof. induction l; intros; cbn; [ reflexivity | rewrite String.eqb_refl; auto ]. Qed.

Lemma strip_prefix_spec : forall l m r, strip_prefix l m = Some r -> m = l ++ r.
Proof.
  induction l as [| x l IH]; intros [| y m] r H; cbn in H; try discriminate;
    [ injection H as <-; reflexivity | injection H as <-; reflexivity |].
  destruct (String.eqb_spec x y) as [-> |]; [| discriminate ].
  cbn; f_equal; auto.
Qed.

Lemma strip_prefix_snoc : forall l x m r,
    strip_prefix (l ++ x :: nil) m = Some r -> strip_prefix l m = Some (x :: r).
Proof.
  intros * H; apply strip_prefix_spec in H; subst.
  rewrite <- List.app_assoc; apply strip_prefix_app.
Qed.

Lemma strip_prefix_snoc_none : forall l x m r,
    strip_prefix l m = Some (x :: r) -> strip_prefix (l ++ x :: nil) m = Some r.
Proof.
  intros * H; apply strip_prefix_spec in H; subst.
  replace (l ++ x :: r) with ((l ++ x :: nil) ++ r) by (rewrite <- List.app_assoc; reflexivity).
  apply strip_prefix_app.
Qed.

(** The member chain [ip] of the module [mp]. *)
Definition path_app (mp : path) (ip : list string) : path :=
  {| p_unit := p_unit mp ; p_mems := p_mems mp ++ ip |}.

(** The members of [p] inside the module [mp], if [p] is in it. *)
Definition path_strip (mp p : path) : option (list string) :=
  if path_beq (p_unit mp) (p_unit p) then strip_prefix (p_mems mp) (p_mems p) else None.

(** The innermost open frame [p] is in, with [p] read inside it. *)
Fixpoint gs_find (Ξ : gstack) (p : path) : option (gunit * list string) :=
  match Ξ with
  | nil => None
  | (mp, U) :: Ξ' =>
      match path_strip mp p with
      | Some ip => Some (U, ip)
      | None => gs_find Ξ' p
      end
  end.

(** The innermost open frame [p] is in, with the telescope of the frames
    outside it. *)
Fixpoint gs_find_tele (Ξ : gstack) (p : path) : option (gunit * list string * ctx) :=
  match Ξ with
  | nil => None
  | (mp, U) :: Ξ' =>
      match path_strip mp p with
      | Some ip => Some (U, ip, gs_tele Ξ')
      | None => gs_find_tele Ξ' p
      end
  end.

Lemma gs_find_tele_find : forall Ξ p,
    gs_find Ξ p = option_map (fun r => let '(U, ip, _) := r in (U, ip)) (gs_find_tele Ξ p).
Proof.
  induction Ξ as [| [mp U] Ξ IH]; intros; cbn; [ reflexivity |].
  destruct (path_strip mp p); [ reflexivity | apply IH ].
Qed.

(** A path inside an open frame is read there, and anything else in the filed
    unit it names.  Nothing is re-expressed: entries are closed and paths
    absolute. *)
Definition gc_resolve (Θ : gdeps) (Ξ : gstack) (p : path) : option gentry :=
  match gs_find Ξ p with
  | Some (U, ip) => gm_resolve (gu_mod U) ip
  | None =>
      match gds_lookup Θ (p_unit p) with
      | Some U => gm_resolve (gu_mod U) (p_mems p)
      | None => None
      end
  end.

(** A module path inside an open frame is read there, provided it names a
    closed module: the open frame itself is not a module yet.  The telescope of
    the frame is its own parameters on top of those of the frames outside. *)
Definition gc_module (Θ : gdeps) (Ξ : gstack) (p : path) : option modres :=
  match gs_find_tele Ξ p with
  | Some (U, nil, _) => None
  | Some (U, x :: ip, T) => gm_submodule (gu_params U ++ T) (gu_mod U) x ip
  | None =>
      match gds_lookup Θ (p_unit p) with
      | Some U => gm_module (gu_params U) (gu_mod U) (p_mems p)
      | None => None
      end
  end.

(** The body module at [p], with its full telescope. *)
Definition gc_body (Θ : gdeps) (Ξ : gstack) (p : path) : option (ctx * gmod) :=
  match gs_find_tele Ξ p with
  | Some (U, nil, _) => None
  | Some (U, x :: ip, T) => gm_subbody (gu_params U ++ T) (gu_mod U) x ip
  | None =>
      match gds_lookup Θ (p_unit p) with
      | Some U => gm_body (gu_params U) (gu_mod U) (p_mems p)
      | None => None
      end
  end.

Lemma gs_find_unit : forall Ξ p U ip, gs_find Ξ p = Some (U, ip) ->
    exists mp, List.In (mp, U) Ξ /\ p_unit mp = p_unit p.
Proof.
  induction Ξ as [| [mp V] Ξ IH]; intros * H; cbn in H; [ discriminate |].
  unfold path_strip in H.
  destruct (path_beq (p_unit mp) (p_unit p)) eqn:Hb.
  - destruct (strip_prefix (p_mems mp) (p_mems p)).
    + injection H as <- <-; exists mp; cbn; split; [ auto | apply path_beq_true; assumption ].
    + destruct (IH _ _ _ H) as (mq & ? & ?); exists mq; cbn; auto.
  - destruct (IH _ _ _ H) as (mq & ? & ?); exists mq; cbn; auto.
Qed.

Lemma gc_resolve_def : forall Θ Ξ p E,
    gc_resolve Θ Ξ p = Some E -> exists b pv A B, E = ge_def b pv A B.
Proof.
  unfold gc_resolve; intros * H.
  destruct (gs_find Ξ p) as [[U ip] |]; [ eapply gm_resolve_def; eassumption |].
  destruct (gds_lookup Θ (p_unit p)); [ eapply gm_resolve_def; eassumption | discriminate ].
Qed.

(** Where a resolved entry comes from: a frame of the stack or a filed unit. *)
Lemma gc_resolve_inv : forall Θ Ξ p E,
    gc_resolve Θ Ξ p = Some E ->
    (exists mp U ip, List.In (mp, U) Ξ /\ gm_resolve (gu_mod U) ip = Some E) \/
    (exists fp U, gds_lookup Θ fp = Some U /\ gm_resolve (gu_mod U) (p_mems p) = Some E).
Proof.
  unfold gc_resolve; intros * H.
  destruct (gs_find Ξ p) as [[U ip] |] eqn:Hf.
  - left; destruct (gs_find_unit _ _ _ _ Hf) as (mp & Hin & _).
    exists mp, U, ip; split; assumption.
  - right; destruct (gds_lookup Θ (p_unit p)) eqn:Hl; [ eauto | discriminate ].
Qed.

(** ** How Resolution Grows

    Every way a global context grows preserves what resolves, both definitions
    and modules: this is the whole of what moving a judgment from one global
    context to a bigger one needs. *)
Definition gc_dsub (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  forall p E, gc_resolve Θ1 Ξ1 p = Some E -> gc_resolve Θ2 Ξ2 p = Some E.

Definition gc_msub (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  forall p r, gc_module Θ1 Ξ1 p = Some r -> gc_module Θ2 Ξ2 p = Some r.

(** Growth never adds to a closed module: a body module keeps its body. *)
Definition gc_bsub (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  forall p r, gc_body Θ1 Ξ1 p = Some r -> gc_body Θ2 Ξ2 p = Some r.

Definition gc_sub (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  gc_dsub Θ1 Ξ1 Θ2 Ξ2 /\ gc_msub Θ1 Ξ1 Θ2 Ξ2 /\ gc_bsub Θ1 Ξ1 Θ2 Ξ2.

Lemma gc_sub_resolve : forall Θ1 Ξ1 Θ2 Ξ2 p E,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_resolve Θ1 Ξ1 p = Some E -> gc_resolve Θ2 Ξ2 p = Some E.
Proof. intros * [H _]; apply H. Qed.

Lemma gc_sub_module : forall Θ1 Ξ1 Θ2 Ξ2 p r,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_module Θ1 Ξ1 p = Some r -> gc_module Θ2 Ξ2 p = Some r.
Proof. intros * [_ [H _]]; apply H. Qed.

Lemma gc_sub_body : forall Θ1 Ξ1 Θ2 Ξ2 p r,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_body Θ1 Ξ1 p = Some r -> gc_body Θ2 Ξ2 p = Some r.
Proof. intros * [_ [_ H]]; apply H. Qed.

Lemma gc_sub_refl : forall Θ Ξ, gc_sub Θ Ξ Θ Ξ.
Proof. repeat split; intros ? ? H; exact H. Qed.

Lemma gc_sub_trans : forall Θ1 Ξ1 Θ2 Ξ2 Θ3 Ξ3,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_sub Θ2 Ξ2 Θ3 Ξ3 -> gc_sub Θ1 Ξ1 Θ3 Ξ3.
Proof.
  intros * [H12 [M12 B12]] [H23 [M23 B23]]; repeat split; intros ? ? H;
    [ apply H23, H12, H | apply M23, M12, H | apply B23, B12, H ].
Qed.

(** A frame may be pushed when its module path is fresh where it is pushed: a
    unit not filed below, named by its root path, or a member not yet declared
    in the enclosing frame.  The root condition makes every prefix of a path
    that resolves resolve as well. *)
Definition frame_fresh (Θ : gdeps) (Ξ : gstack) (mp : path) : Prop :=
  match Ξ with
  | nil => gds_fresh (p_unit mp) Θ /\ p_mems mp = nil
  | (mq, U) :: _ => exists x, mp = path_in mq x /\ gm_fresh x (gu_mod U)
  end.

Lemma gc_sub_push : forall Θ Ξ mp U,
    frame_fresh Θ Ξ mp ->
    gc_sub Θ Ξ Θ ((mp, U) :: Ξ).
Proof.
  intros * Hf; split; [| split ].
  - intros p E Hr; unfold gc_resolve in *; cbn.
    destruct (path_strip mp p) as [ip |] eqn:Hs; [| exact Hr ].
    exfalso; unfold path_strip in Hs.
    destruct (path_beq (p_unit mp) (p_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb.
    destruct Ξ as [| [mq V] Ξ']; cbn in Hf, Hr.
    + destruct Hf as [Hf _].
      rewrite <- Hb in Hr; rewrite (gds_fresh_no_lookup _ _ Hf) in Hr; discriminate.
    + destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
      pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
      unfold path_strip in Hr; rewrite Hb, path_beq_refl, Hs' in Hr.
      destruct (gm_resolve_head _ _ _ Hr) as (z & ip' & [= <- <-] & Hin); contradiction.
  - intros p r Hr; unfold gc_module in *; cbn.
    destruct (path_strip mp p) as [ip |] eqn:Hs; [| exact Hr ].
    exfalso; unfold path_strip in Hs.
    destruct (path_beq (p_unit mp) (p_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb.
    destruct Ξ as [| [mq V] Ξ']; cbn in Hf, Hr.
    + destruct Hf as [Hf _].
      rewrite <- Hb in Hr; rewrite (gds_fresh_no_lookup _ _ Hf) in Hr; discriminate.
    + destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
      pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
      unfold path_strip in Hr; rewrite Hb, path_beq_refl, Hs' in Hr.
      exact (Hx (gm_submodule_head _ _ _ _ _ Hr)).
  - intros p r Hr; unfold gc_body in *; cbn.
    destruct (path_strip mp p) as [ip |] eqn:Hs; [| exact Hr ].
    exfalso; unfold path_strip in Hs.
    destruct (path_beq (p_unit mp) (p_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb.
    destruct Ξ as [| [mq V] Ξ']; cbn in Hf, Hr.
    + destruct Hf as [Hf _].
      rewrite <- Hb in Hr; rewrite (gds_fresh_no_lookup _ _ Hf) in Hr; discriminate.
    + destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
      pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
      unfold path_strip in Hr; rewrite Hb, path_beq_refl, Hs' in Hr.
      exact (Hx (gm_subbody_head _ _ _ _ _ Hr)).
Qed.

Lemma gc_sub_grow : forall Θ Ξ mp Δ Φ x E,
    gm_fresh x Φ ->
    gc_sub Θ ((mp, gu_body Δ Φ) :: Ξ) Θ ((mp, gu_body Δ (Φ ⊳ x ↦ E)) :: Ξ).
Proof.
  intros * Hf; split; [| split ].
  - intros p E0 Hr; unfold gc_resolve in *; cbn in *.
    destruct (path_strip mp p); [ cbn in *; apply gm_resolve_ext_fresh; assumption | exact Hr ].
  - intros p r Hr; unfold gc_module in *; cbn in *.
    destruct (path_strip mp p) as [[| y ip] |]; [ discriminate | | exact Hr ].
    cbn in *; apply gm_submodule_ext_fresh; assumption.
  - intros p r Hr; unfold gc_body in *; cbn in *.
    destruct (path_strip mp p) as [[| y ip] |]; [ discriminate | | exact Hr ].
    cbn in *; apply gm_subbody_ext_fresh; assumption.
Qed.

(** Closing a nested module into its parent: its members are read through the
    parent exactly as they were read in the frame. *)
Lemma gc_sub_close : forall Θ Ξ mp Δ Φ x Δ' Φ',
    gm_fresh x Φ ->
    gc_sub Θ ((path_in mp x, gu_body Δ' Φ') :: (mp, gu_body Δ Φ) :: Ξ)
           Θ ((mp, gu_body Δ (Φ ⊳ x ↦ ge_body Δ' Φ')) :: Ξ).
Proof.
  intros * Hf; split; [| split ].
  - intros p E0 Hr; unfold gc_resolve in *; cbn in *.
    unfold path_strip in *; cbn in *.
    destruct (path_beq (p_unit mp) (p_unit p)) eqn:Hb; [| exact Hr ].
    destruct (strip_prefix (p_mems mp ++ x :: nil) (p_mems p)) as [ip |] eqn:Hs.
    + rewrite (strip_prefix_snoc _ _ _ _ Hs).
      exact (gm_resolve_in Φ x Δ' Φ' ip E0 Hr).
    + destruct (strip_prefix (p_mems mp) (p_mems p)) as [ip |] eqn:Hs'; [| exact Hr ].
      cbn in *; destruct (gm_resolve_head _ _ _ Hr) as (z & ip' & -> & Hin).
      destruct (String.eqb_spec z x) as [-> |].
      * rewrite (strip_prefix_snoc_none _ _ _ _ Hs') in Hs; discriminate.
      * cbn; destruct (String.eqb_spec z x); [ contradiction | exact Hr ].
  - intros p r Hr; unfold gc_module in *; cbn in *.
    unfold path_strip in *; cbn in *.
    destruct (path_beq (p_unit mp) (p_unit p)) eqn:Hb; [| exact Hr ].
    destruct (strip_prefix (p_mems mp ++ x :: nil) (p_mems p)) as [ip |] eqn:Hs.
    + rewrite (strip_prefix_snoc _ _ _ _ Hs).
      destruct ip as [| z ip]; [ discriminate |].
      apply gm_submodule_in; cbn; exact Hr.
    + destruct (strip_prefix (p_mems mp) (p_mems p)) as [ip |] eqn:Hs'; [| exact Hr ].
      destruct ip as [| z ip]; [ discriminate |].
      cbn in *.
      destruct (String.eqb_spec z x) as [-> |].
      * rewrite (strip_prefix_snoc_none _ _ _ _ Hs') in Hs; discriminate.
      * destruct (String.eqb_spec z x); [ contradiction | exact Hr ].
  - intros p r Hr; unfold gc_body in *; cbn in *.
    unfold path_strip in *; cbn in *.
    destruct (path_beq (p_unit mp) (p_unit p)) eqn:Hb; [| exact Hr ].
    destruct (strip_prefix (p_mems mp ++ x :: nil) (p_mems p)) as [ip |] eqn:Hs.
    + rewrite (strip_prefix_snoc _ _ _ _ Hs).
      destruct ip as [| z ip]; [ discriminate |].
      apply gm_subbody_in; cbn; exact Hr.
    + destruct (strip_prefix (p_mems mp) (p_mems p)) as [ip |] eqn:Hs'; [| exact Hr ].
      destruct ip as [| z ip]; [ discriminate |].
      cbn in *.
      destruct (String.eqb_spec z x) as [-> |].
      * rewrite (strip_prefix_snoc_none _ _ _ _ Hs') in Hs; discriminate.
      * destruct (String.eqb_spec z x); [ contradiction | exact Hr ].
Qed.

(** Filing a unit: what was read in its open frame is read in the level it is
    filed in. *)
Lemma gc_sub_file : forall Θ d fp U,
    gd_lookup d fp = Some U ->
    (forall fq V, List.In (fq, V) d -> gds_fresh fq Θ) ->
    gc_sub Θ ((p_abs fp nil, U) :: nil) (d :: Θ) nil.
Proof.
  intros * Hd Hfr; split; [| split ].
  - intros p E0 Hr; unfold gc_resolve in *; cbn [gs_find] in *.
    unfold path_strip in Hr; cbn [p_unit p_mems strip_prefix] in Hr.
    destruct (path_beq fp (p_unit p)) eqn:Hb.
    + apply path_beq_true in Hb; subst.
      unfold gds_lookup; cbn [List.concat]; rewrite (gd_lookup_app_l _ _ _ _ Hd); exact Hr.
    + destruct (gds_lookup Θ (p_unit p)) as [V |] eqn:Hl; [| discriminate ].
      erewrite gds_lookup_level; [ exact Hr | exact Hfr | exact Hl ].
  - intros p r Hr; unfold gc_module in *; cbn [gs_find_tele] in *.
    unfold path_strip in Hr; cbn [p_unit p_mems strip_prefix] in Hr.
    destruct (path_beq fp (p_unit p)) eqn:Hb.
    + apply path_beq_true in Hb; subst.
      destruct (p_mems p) as [| x ip] eqn:Hp; [ discriminate |].
      unfold gds_lookup; cbn [List.concat]; rewrite (gd_lookup_app_l _ _ _ _ Hd).
      cbn in *; rewrite List.app_nil_r in Hr; exact Hr.
    + destruct (gds_lookup Θ (p_unit p)) as [V |] eqn:Hl; [| discriminate ].
      erewrite gds_lookup_level; [ exact Hr | exact Hfr | exact Hl ].
  - intros p r Hr; unfold gc_body in *; cbn [gs_find_tele] in *.
    unfold path_strip in Hr; cbn [p_unit p_mems strip_prefix] in Hr.
    destruct (path_beq fp (p_unit p)) eqn:Hb.
    + apply path_beq_true in Hb; subst.
      destruct (p_mems p) as [| x ip] eqn:Hp; [ discriminate |].
      unfold gds_lookup; cbn [List.concat]; rewrite (gd_lookup_app_l _ _ _ _ Hd).
      cbn in *; rewrite List.app_nil_r in Hr; exact Hr.
    + destruct (gds_lookup Θ (p_unit p)) as [V |] eqn:Hl; [| discriminate ].
      erewrite gds_lookup_level; [ exact Hr | exact Hfr | exact Hl ].
Qed.

Lemma gc_sub_level : forall Θ d,
    (forall fq V, List.In (fq, V) d -> gds_fresh fq Θ) ->
    gc_sub Θ nil (d :: Θ) nil.
Proof.
  intros * Hfr; repeat split; intros p E0 Hr; unfold gc_resolve, gc_module, gc_body in *; cbn [gs_find gs_find_tele] in *;
    destruct (gds_lookup Θ (p_unit p)) as [V |] eqn:Hl; try discriminate;
    rewrite (gds_lookup_level _ _ _ _ Hfr Hl); exact Hr.
Qed.

(** Filing more units under the same stack. *)
Lemma gc_sub_levels : forall Θ Θ' Ξ, Θ ⊑ Θ' -> gc_sub Θ Ξ Θ' Ξ.
Proof.
  intros * Hs; split; [| split ].
  - intros p E Hr; unfold gc_resolve in *.
    destruct (gs_find Ξ p) as [[U ip] |]; [ exact Hr |].
    destruct (gds_lookup Θ (p_unit p)) as [V |] eqn:E1; [| discriminate ].
    rewrite (Hs _ _ E1); exact Hr.
  - intros p r Hr; unfold gc_module in *.
    destruct (gs_find_tele Ξ p) as [[[U ip] T] |]; [ exact Hr |].
    destruct (gds_lookup Θ (p_unit p)) as [V |] eqn:E1; [| discriminate ].
    rewrite (Hs _ _ E1); exact Hr.
  - intros p r Hr; unfold gc_body in *.
    destruct (gs_find_tele Ξ p) as [[[U ip] T] |]; [ exact Hr |].
    destruct (gds_lookup Θ (p_unit p)) as [V |] eqn:E1; [| discriminate ].
    rewrite (Hs _ _ E1); exact Hr.
Qed.

(** ** Transparent Global Contexts

    Every definition is transparent and has a body: then no global is a
    neutral, which is what canonicity and consistency need.  Parameters, being
    λ-variables, impose nothing. *)

Fixpoint ge_transparent (E : gentry) : Prop :=
  match E with
  | ge_def b _ _ B => b = true /\ B <> None
  | ge_mod (gu_mk _ (md_body Φ)) => gm_transparent Φ
  | ge_mod (gu_mk _ (md_alias _)) => True
  end
with gm_transparent (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ _ E => gm_transparent Φ /\ ge_transparent E
  | gm_check Φ _ => gm_transparent Φ
  end.

Definition gc_transparent (Θ : gdeps) (Ξ : gstack) : Prop :=
  (forall fp U, List.In (fp, U) (List.concat Θ) -> gm_transparent (gu_mod U)) /\
  (forall mp U, List.In (mp, U) Ξ -> gm_transparent (gu_mod U)).

Lemma gm_transparent_resolve : forall Φ ip E,
    gm_transparent Φ -> gm_resolve Φ ip = Some E -> ge_transparent E.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] ip E0 HΦ H; cbn in H, HΦ; [ discriminate | | eapply IH; eassumption ].
  destruct HΦ as [HΦ HE].
  destruct ip as [| x ip']; [ discriminate |].
  destruct (String.eqb x y); [| eapply IH; eassumption ].
  destruct ip' as [| z ip''], E as [b pv A B | [Δ' [Φ' | E']]]; try discriminate.
  - injection H as <-; exact HE.
  - eapply IH; [ exact HE | exact H ].
Qed.

Lemma gc_transparent_resolve : forall Θ Ξ p b pv A B,
    gc_transparent Θ Ξ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    b = true /\ B <> None.
Proof.
  intros * [HΘ HΞ] Hr.
  destruct (gc_resolve_inv _ _ _ _ Hr) as [(mp & U & ip & Hin & Hm) | (fp & U & Hl & Hm)].
  - exact (gm_transparent_resolve _ _ _ (HΞ _ _ Hin) Hm).
  - exact (gm_transparent_resolve _ _ _ (HΘ _ _ (gd_lookup_in _ _ _ Hl)) Hm).
Qed.

(** ** A Fixed Global Context

    The semantic model and the two metatheorems about NbE are stated for one
    global context at a time.  Found by instance resolution, it keeps their
    judgments in the short forms of [Core.Semantic.Fixed]. *)
Class GCtx : Set := gc_mk
  { gc_deps : gdeps
  ; gc_stack : gstack }.
