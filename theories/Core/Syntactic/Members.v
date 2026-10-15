(** * Resolution and Members of Modules

    What a path names in the global context is a lookup ([gc_resolve],
    [gc_module], [gc_body]).  A module has no signature: the type of a member is computed from the
    module, when it is needed, by the relation [member_type], and its
    δ-reduct by the function [member_unfold].  Both read syntax, context
    lookup and global resolution only, so they sit outside the mutual block of
    judgments, which uses them. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Substitution.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

(** ** Resolution in a Module

    A module is a sequence of entries, in declaration order: definitions and
    nested modules (see [gentry] in [Syntax]).  A nested module of a filed
    unit is a body [ge_body pv Δ Φ], with [Δ] the parameters it adds to the ones
    it is already under, or an alias [ge_mod pv (gu_mk T (md_alias E))], with [T]
    its full telescope.

    The newest entry of a name decides; names are fresh in a well-formed
    module, so there is no other.  Only a definition or the declaration of an
    inductive type is handed back, and only
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
               | _ :: _, ge_mod _ (gu_mk _ (md_body Φ')) => gm_resolve Φ' ip'
               | _ :: _, ge_ind _ _ Φ' => gm_resolve Φ' ip'
               | _, _ => None
               end
          else gm_resolve Φ ip
      end
  | gm_open Φ _ _ => gm_resolve Φ ip
  end.

(** What resolves starts with a declared name. *)
Lemma gm_resolve_head : forall Φ ip E,
    gm_resolve Φ ip = Some E -> exists x ip', ip = x :: ip' /\ List.In x (gm_names Φ).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] ip E0 H; cbn in H; [ discriminate | |
    destruct (IH _ _ _ H) as (z & ip'' & -> & Hin); exists z, ip''; split; [ reflexivity | cbn; apply List.in_or_app; right; exact Hin ] ].
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

(** ** Resolution of a Module

    What a module path denotes: a body module with its full telescope and,
    for the module of an inductive type, the type's declaration, or the
    first alias on the path, with the rest of the chain.  An alias is stored
    closed, over its full telescope, so the rest of the chain is read inside
    it. *)
Inductive modres : Set :=
| mr_body : ctx -> option ind_decl -> modres
| mr_alias : gunit -> list string -> modres.

(** The submodule [x :: ip] of [Φ], whose enclosing telescope is [T]. *)
Fixpoint gm_submodule (T : ctx) (Φ : gmod) (x : string) (ip : list string) : option modres :=
  match Φ with
  | gm_nil => None
  | gm_open Φ0 _ _ => gm_submodule T Φ0 x ip
  | gm_ext Φ0 y E =>
      if String.eqb x y then
        match E with
        | ge_mod _ (gu_mk Δ (md_body Φ')) =>
            match ip with
            | nil => Some (mr_body (Δ ++ T) None)
            | z :: ip' => gm_submodule (Δ ++ T) Φ' z ip'
            end
        | ge_mod _ (gu_mk Δ (md_alias E')) => Some (mr_alias (gu_mk Δ (md_alias E')) ip)
        | ge_ind _ D Φ' =>
            match ip with
            | nil => Some (mr_body (ind_uparams D) (Some D))
            | z :: ip' => gm_submodule (ind_uparams D) Φ' z ip'
            end
        (** As a module, an inductive alias is an alias, over its own
            telescope, of the module at its canonical path at its
            arguments. *)
        | ge_ind_alias _ Δ p Ns => Some (mr_alias (gu_mk Δ (md_alias (me_apps (qname_mod p) Ns))) ip)
        | ge_def _ _ _ _ => None
        end
      else gm_submodule T Φ0 x ip
  end.

(** The module [ip] of a body of telescope [T], the body being the module
    of the inductive type [oD] if it is [Some]. *)
Definition gm_module (T : ctx) (oD : option ind_decl) (Φ : gmod) (ip : list string) : option modres :=
  match ip with
  | nil => Some (mr_body T oD)
  | x :: ip' => gm_submodule T Φ x ip'
  end.

Lemma gm_submodule_head : forall Φ T x ip r,
    gm_submodule T Φ x ip = Some r -> List.In x (gm_names Φ).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H; [ discriminate | | cbn; apply List.in_or_app; right; exact (IH _ _ _ _ _ H) ].
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

(** The body module [x :: ip] of [Φ], with its full telescope. *)
Fixpoint gm_subbody (T : ctx) (Φ : gmod) (x : string) (ip : list string) : option (ctx * gmod) :=
  match Φ with
  | gm_nil => None
  | gm_open Φ0 _ _ => gm_subbody T Φ0 x ip
  | gm_ext Φ0 y E =>
      if String.eqb x y then
        match E with
        | ge_mod _ (gu_mk Δ (md_body Φ')) =>
            match ip with
            | nil => Some (Δ ++ T, Φ')
            | z :: ip' => gm_subbody (Δ ++ T) Φ' z ip'
            end
        | ge_ind _ D Φ' =>
            match ip with
            | nil => Some (ind_uparams D, Φ')
            | z :: ip' => gm_subbody (ind_uparams D) Φ' z ip'
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
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H; [ discriminate | | cbn; apply List.in_or_app; right; exact (IH _ _ _ _ _ H) ].
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

(** ** Resolution of a Path

    A path is read in the innermost open frame it is in, and otherwise in
    the filed unit it names. *)

(** The innermost open frame [p] is in, with [p] read inside it. *)
Fixpoint gs_find (Ξ : gstack) (p : qname) : option (gunit * list string) :=
  match Ξ with
  | nil => None
  | (mp, U) :: Ξ' =>
      match qname_strip mp p with
      | Some ip => Some (U, ip)
      | None => gs_find Ξ' p
      end
  end.

(** The innermost open frame [p] is in, with the telescope of the frames
    outside it. *)
Fixpoint gs_find_tele (Ξ : gstack) (p : qname) : option (gunit * list string * ctx) :=
  match Ξ with
  | nil => None
  | (mp, U) :: Ξ' =>
      match qname_strip mp p with
      | Some ip => Some (U, ip, gs_tele Ξ')
      | None => gs_find_tele Ξ' p
      end
  end.

Lemma gs_find_tele_find : forall Ξ p,
    gs_find Ξ p = option_map (fun r => let '(U, ip, _) := r in (U, ip)) (gs_find_tele Ξ p).
Proof.
  induction Ξ as [| [mp U] Ξ IH]; intros; cbn; [ reflexivity |].
  destruct (qname_strip mp p); [ reflexivity | apply IH ].
Qed.

(** A path inside an open frame is read there, and anything else in the filed
    unit it names.  Nothing is re-expressed: entries are closed and paths
    absolute. *)
Definition gc_resolve (Θ : gdeps) (Ξ : gstack) (p : qname) : option gentry :=
  match gs_find Ξ p with
  | Some (U, ip) => gm_resolve (gu_mod U) ip
  | None =>
      match gds_lookup Θ (q_unit p) with
      | Some U => gm_resolve (gu_mod U) (q_chain p)
      | None => None
      end
  end.

(** A module path inside an open frame is read there, provided it names a
    closed module: the open frame itself is not a module yet.  The telescope of
    the frame is its own parameters on top of those of the frames outside. *)
Definition gc_module (Θ : gdeps) (Ξ : gstack) (p : qname) : option modres :=
  match gs_find_tele Ξ p with
  | Some (U, nil, _) => None
  | Some (U, x :: ip, T) => gm_submodule (gu_params U ++ T) (gu_mod U) x ip
  | None =>
      match gds_lookup Θ (q_unit p) with
      | Some U => gm_module (gu_params U) None (gu_mod U) (q_chain p)
      | None => None
      end
  end.

(** The body module at [p], with its full telescope. *)
Definition gc_body (Θ : gdeps) (Ξ : gstack) (p : qname) : option (ctx * gmod) :=
  match gs_find_tele Ξ p with
  | Some (U, nil, _) => None
  | Some (U, x :: ip, T) => gm_subbody (gu_params U ++ T) (gu_mod U) x ip
  | None =>
      match gds_lookup Θ (q_unit p) with
      | Some U => gm_body (gu_params U) (gu_mod U) (q_chain p)
      | None => None
      end
  end.

(** The declaration of the inductive type whose module is at [p], read off
    the type's entry ([gm_submodule]). *)
Definition ind_lookup (Θ : gdeps) (Ξ : gstack) (p : qname) : option ind_decl :=
  match gc_module Θ Ξ p with
  | Some (mr_body _ oD) => oD
  | _ => None
  end.

Lemma ind_lookup_module : forall Θ Ξ p D,
    ind_lookup Θ Ξ p = Some D -> exists T, gc_module Θ Ξ p = Some (mr_body T (Some D)).
Proof.
  unfold ind_lookup; intros * H.
  destruct (gc_module Θ Ξ p) as [[T oD | U r] |]; try discriminate.
  subst; eauto.
Qed.

(** The module of an inductive type is no alias. *)
Lemma ind_lookup_not_alias : forall Θ Ξ p D U r,
    ind_lookup Θ Ξ p = Some D -> gc_module Θ Ξ p <> Some (mr_alias U r).
Proof. intros * H; destruct (ind_lookup_module _ _ _ _ H) as [T ->]; discriminate. Qed.

Lemma ind_lookup_body : forall Θ Ξ p T oD,
    gc_module Θ Ξ p = Some (mr_body T oD) -> ind_lookup Θ Ξ p = oD.
Proof. intros * H; unfold ind_lookup; rewrite H; reflexivity. Qed.

Lemma gs_find_unit : forall Ξ p U ip, gs_find Ξ p = Some (U, ip) ->
    exists mp, List.In (mp, U) Ξ /\ q_unit mp = q_unit p.
Proof.
  induction Ξ as [| [mp V] Ξ IH]; intros * H; cbn in H; [ discriminate |].
  unfold qname_strip in H.
  destruct (path_beq (q_unit mp) (q_unit p)) eqn:Hb.
  - destruct (strip_prefix (q_chain mp) (q_chain p)).
    + injection H as <- <-; exists mp; cbn; split; [ auto | apply path_beq_true; assumption ].
    + destruct (IH _ _ _ H) as (mq & ? & ?); exists mq; cbn; auto.
  - destruct (IH _ _ _ H) as (mq & ? & ?); exists mq; cbn; auto.
Qed.

(** Where a resolved entry comes from: a frame of the stack or a filed unit. *)
Lemma gc_resolve_inv : forall Θ Ξ p E,
    gc_resolve Θ Ξ p = Some E ->
    (exists mp U ip, List.In (mp, U) Ξ /\ gm_resolve (gu_mod U) ip = Some E) \/
    (exists fp U, gds_lookup Θ fp = Some U /\ gm_resolve (gu_mod U) (q_chain p) = Some E).
Proof.
  unfold gc_resolve; intros * H.
  destruct (gs_find Ξ p) as [[U ip] |] eqn:Hf.
  - left; destruct (gs_find_unit _ _ _ _ Hf) as (mp & Hin & _).
    exists mp, U, ip; split; assumption.
  - right; destruct (gds_lookup Θ (q_unit p)) eqn:Hl; [ eauto | discriminate ].
Qed.

(** ** Entries

    [gc_entry Θ Ξ p] is the entry a path names, a definition or a submodule,
    read through body modules as [gc_resolve] is: it carries the privacy flag
    of a submodule, which no other lookup reports. *)
Fixpoint gm_entry (Φ : gmod) (ip : list string) : option gentry :=
  match Φ with
  | gm_nil => None
  | gm_ext Φ y E =>
      match ip with
      | nil => None
      | x :: ip' =>
          if String.eqb x y
          then match ip', E with
               | nil, _ => Some E
               | _ :: _, ge_mod _ (gu_mk _ (md_body Φ')) => gm_entry Φ' ip'
               | _ :: _, ge_ind _ _ Φ' => gm_entry Φ' ip'
               | _, _ => None
               end
          else gm_entry Φ ip
      end
  | gm_open Φ _ _ => gm_entry Φ ip
  end.

Definition gc_entry (Θ : gdeps) (Ξ : gstack) (p : qname) : option gentry :=
  match gs_find Ξ p with
  | Some (U, ip) => gm_entry (gu_mod U) ip
  | None =>
      match gds_lookup Θ (q_unit p) with
      | Some U => gm_entry (gu_mod U) (q_chain p)
      | None => None
      end
  end.

(** Whether an entry is private. *)
Definition ge_private (E : gentry) : bool :=
  match E with
  | ge_def _ pv _ _ => pv
  | ge_mod pv _ => pv
  | ge_ind pv _ _ => pv
  | ge_ind_alias pv _ _ _ => pv
  end.

Lemma gm_entry_head : forall Φ ip E,
    gm_entry Φ ip = Some E -> exists x ip', ip = x :: ip' /\ List.In x (gm_names Φ).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] ip E0 H; cbn in H; [ discriminate | |
    destruct (IH _ _ _ H) as (z & ip'' & -> & Hin); exists z, ip''; split; [ reflexivity | cbn; apply List.in_or_app; right; exact Hin ] ].
  destruct ip as [| x ip']; [ discriminate |].
  destruct (String.eqb_spec x y) as [-> |].
  - exists y, ip'; cbn; auto.
  - destruct (IH _ _ _ H) as (z & ip'' & [= -> ->] & Hin); exists z, ip''; cbn; auto.
Qed.

Lemma gm_entry_ext_fresh : forall Φ x E ip E0,
    gm_fresh x Φ -> gm_entry Φ ip = Some E0 -> gm_entry (Φ ⊳ x ↦ E) ip = Some E0.
Proof.
  intros * Hf Hr; cbn.
  destruct (gm_entry_head _ _ _ Hr) as (z & ip' & -> & Hin).
  destruct (String.eqb_spec z x) as [-> |]; [ contradiction | assumption ].
Qed.

(** ** The Inductive Alias a Path Names

    [ind_alias_lookup Θ Ξ q]: the telescope, canonical path and arguments
    of the inductive alias at the path [q]. *)
Definition ind_alias_view : Type := (list centry * qname * list exp)%type.

Definition ge_ind_target (E : gentry) : option ind_alias_view :=
  match E with
  | ge_ind_alias _ Δ p Ns => Some (Δ, p, Ns)
  | _ => None
  end.

Definition gm_ind_target (Φ : gmod) (ip : list string) : option ind_alias_view :=
  match gm_entry Φ ip with
  | Some E => ge_ind_target E
  | None => None
  end.

Definition ind_alias_lookup (Θ : gdeps) (Ξ : gstack) (pq : qname) : option ind_alias_view :=
  match gs_find Ξ pq with
  | Some (U, ip) => gm_ind_target (gu_mod U) ip
  | None =>
      match gds_lookup Θ (q_unit pq) with
      | Some U => gm_ind_target (gu_mod U) (q_chain pq)
      | None => None
      end
  end.

(** The inductive type a path names, its own or through an inductive
    alias, as a view: no telescope and no argument for the type itself. *)
Definition ind_target (Θ : gdeps) (Ξ : gstack) (pq : qname) : option ind_alias_view :=
  match ind_lookup Θ Ξ pq with
  | Some _ => Some (nil, pq, nil)
  | None => ind_alias_lookup Θ Ξ pq
  end.

Lemma gm_ind_target_ext_fresh : forall Φ x E ip p,
    gm_fresh x Φ -> gm_ind_target Φ ip = Some p -> gm_ind_target (Φ ⊳ x ↦ E) ip = Some p.
Proof.
  intros * Hf H; unfold gm_ind_target in *.
  destruct (gm_entry Φ ip) as [E0 |] eqn:E1; [| discriminate ].
  rewrite (gm_entry_ext_fresh _ _ _ _ _ Hf E1); exact H.
Qed.

(** ** One Lookup for a Global

    The entry a path names ([gc_entry]) tells a global from the module of
    an inductive type in one pass, which [gc_resolve] and [ind_lookup] would
    each take. *)
Lemma gm_entry_resolve_def : forall Φ ip b pv A B,
    gm_entry Φ ip = Some (ge_def b pv A B) <-> gm_resolve Φ ip = Some (ge_def b pv A B).
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] [| x ip] *; cbn; try tauto; try exact (IH _ _ _ _ _ _).
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _) ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [Φ' | E']] | pv' D Φ' | pv' Δa pa Nsa]; cbn; try tauto;
    try (split; intros; discriminate); exact (IH _ _ _ _ _ _).
Qed.

Lemma gm_entry_ind_resolve : forall Φ ip pv D Φ',
    gm_entry Φ ip = Some (ge_ind pv D Φ') -> gm_resolve Φ ip = None.
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] [| x ip] *; cbn; try discriminate; intros He; try (eapply IH; exact He).
  destruct (String.eqb x y); [| eapply IH; exact He ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [Φ1 | E']] | pv' D' Φ1 | pv' Δ1 p1 Ns1]; cbn in He |- *; try discriminate;
    try reflexivity; eapply IH; exact He.
Qed.

Lemma gm_entry_submodule : forall Φ T x ip pv D Φ',
    gm_entry Φ (x :: ip) = Some (ge_ind pv D Φ') -> gm_submodule T Φ x ip = Some (mr_body (ind_uparams D) (Some D)).
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] T x ip *; cbn; try discriminate; intros He; try (eapply IH; exact He).
  destruct (String.eqb x y); [| eapply IH; exact He ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [Φ1 | E']] | pv' D' Φ1 | pv' Δ1 p1 Ns1]; cbn in He |- *; try discriminate;
    try (injection He as -> -> ->; reflexivity); eapply IH; exact He.
Qed.

Lemma gm_submodule_entry : forall Φ T x ip T' D,
    gm_submodule T Φ x ip = Some (mr_body T' (Some D)) -> exists pv Φ', gm_entry Φ (x :: ip) = Some (ge_ind pv D Φ').
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] T x ip *; cbn; try discriminate; intros He; try (eapply IH; exact He).
  destruct (String.eqb x y); [| eapply IH; exact He ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [Φ1 | E']] | pv' D' Φ1 | pv' Δ1 p1 Ns1]; cbn in He |- *; try discriminate;
    try (injection He as _ ->; eauto; fail); eapply IH; exact He.
Qed.

Lemma gm_entry_nil : forall Φ, gm_entry Φ nil = None.
Proof. induction Φ; cbn; auto. Qed.

Lemma gc_entry_def : forall Θ Ξ p b pv A B,
    gc_entry Θ Ξ p = Some (ge_def b pv A B) <-> gc_resolve Θ Ξ p = Some (ge_def b pv A B).
Proof.
  intros; unfold gc_entry, gc_resolve.
  destruct (gs_find Ξ p) as [[U ip] |]; [ apply gm_entry_resolve_def |].
  destruct (gds_lookup Θ (q_unit p)); [ apply gm_entry_resolve_def | tauto ].
Qed.

Lemma gc_entry_ind : forall Θ Ξ p pv D Φ,
    gc_entry Θ Ξ p = Some (ge_ind pv D Φ) -> gc_resolve Θ Ξ p = None /\ ind_lookup Θ Ξ p = Some D.
Proof.
  intros * He; unfold gc_entry, gc_resolve, ind_lookup, gc_module in *.
  rewrite gs_find_tele_find in *.
  destruct (gs_find_tele Ξ p) as [[[U ip] T] |]; cbn in He |- *.
  - split; [ eapply gm_entry_ind_resolve; exact He |].
    destruct ip as [| x ip]; [ rewrite gm_entry_nil in He; discriminate |].
    erewrite gm_entry_submodule by exact He; reflexivity.
  - destruct (gds_lookup Θ (q_unit p)) as [U |]; [| discriminate ].
    split; [ eapply gm_entry_ind_resolve; exact He |].
    destruct (q_chain p) as [| x ip]; [ rewrite gm_entry_nil in He; discriminate |].
    unfold gm_module; erewrite gm_entry_submodule by exact He; reflexivity.
Qed.

Lemma ind_lookup_entry : forall Θ Ξ p D,
    ind_lookup Θ Ξ p = Some D -> exists pv Φ, gc_entry Θ Ξ p = Some (ge_ind pv D Φ).
Proof.
  intros * Hl; unfold gc_entry, ind_lookup, gc_module in *.
  rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[U ip] T] |]; cbn in Hl |- *.
  - destruct ip as [| x ip]; [ discriminate |].
    destruct (gm_submodule _ _ _ _) as [[T' [D' |] | U' r] |] eqn:E; try discriminate.
    injection Hl as ->; eapply gm_submodule_entry; exact E.
  - destruct (gds_lookup Θ (q_unit p)) as [U |]; [| discriminate ].
    destruct (q_chain p) as [| x ip]; cbn in Hl; [ discriminate |].
    destruct (gm_submodule _ _ _ _) as [[T' [D' |] | U' r] |] eqn:E; try discriminate.
    injection Hl as ->; eapply gm_submodule_entry; exact E.
Qed.

Lemma ind_alias_lookup_entry : forall Θ Ξ pq,
    ind_alias_lookup Θ Ξ pq = match gc_entry Θ Ξ pq with Some E => ge_ind_target E | None => None end.
Proof.
  intros; unfold ind_alias_lookup, gc_entry, gm_ind_target.
  destruct (gs_find Ξ pq) as [[U ip] |]; [ reflexivity |].
  destruct (gds_lookup Θ (q_unit pq)); reflexivity.
Qed.

Lemma gm_entry_resolve_none : forall Φ ip E,
    gm_entry Φ ip = Some E -> (forall b pv A B, E <> ge_def b pv A B) -> gm_resolve Φ ip = None.
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] [| x ip] * He Hn; cbn in He |- *; try discriminate; try (eapply IH; eassumption).
  destruct (String.eqb x y); [| eapply IH; eassumption ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [Φ1 | E']] | pv' D' Φ1 | pv' Δ1 p1 Ns1]; cbn in He |- *;
    try reflexivity; try (eapply IH; eassumption).
  injection He as <-; exfalso; eapply Hn; reflexivity.
Qed.

Lemma gm_entry_ind_alias_submodule : forall Φ T x ip pv Δ p Ns,
    gm_entry Φ (x :: ip) = Some (ge_ind_alias pv Δ p Ns) ->
    gm_submodule T Φ x ip = Some (mr_alias (gu_mk Δ (md_alias (me_apps (qname_mod p) Ns))) nil).
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] T x ip *; cbn; try discriminate; intros He; try (eapply IH; exact He).
  destruct (String.eqb x y); [| eapply IH; exact He ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ0 [Φ1 | E']] | pv' D' Φ1 | pv' Δ1 p1 Ns1]; cbn in He |- *; try discriminate;
    try (injection He as -> -> -> ->; reflexivity); eapply IH; exact He.
Qed.

Lemma ind_alias_lookup_module : forall Θ Ξ pq Δ p Ns,
    ind_alias_lookup Θ Ξ pq = Some (Δ, p, Ns) ->
    gc_module Θ Ξ pq = Some (mr_alias (gu_mk Δ (md_alias (me_apps (qname_mod p) Ns))) nil).
Proof.
  intros * Hl; unfold ind_alias_lookup, gc_module, gm_ind_target in *.
  rewrite gs_find_tele_find in Hl.
  destruct (gs_find_tele Ξ pq) as [[[U ip] T] |]; cbn in Hl |- *.
  - destruct (gm_entry (gu_mod U) ip) as [E |] eqn:He; [| discriminate ].
    destruct E as [| | | pv Δ' p' Ns']; cbn in Hl; try discriminate; injection Hl as -> -> ->.
    destruct ip as [| x ip]; [ rewrite gm_entry_nil in He; discriminate |].
    eapply gm_entry_ind_alias_submodule; exact He.
  - destruct (gds_lookup Θ (q_unit pq)) as [U |]; [| discriminate ].
    destruct (gm_entry (gu_mod U) (q_chain pq)) as [E |] eqn:He; [| discriminate ].
    destruct E as [| | | pv Δ' p' Ns']; cbn in Hl; try discriminate; injection Hl as -> -> ->.
    destruct (q_chain pq) as [| x ip]; [ rewrite gm_entry_nil in He; discriminate |].
    unfold gm_module; eapply gm_entry_ind_alias_submodule; exact He.
Qed.

Lemma gc_entry_ind_alias : forall Θ Ξ pq pv Δ pt Ns,
    gc_entry Θ Ξ pq = Some (ge_ind_alias pv Δ pt Ns) ->
    gc_resolve Θ Ξ pq = None /\ ind_alias_lookup Θ Ξ pq = Some (Δ, pt, Ns).
Proof.
  intros * He; split; [| rewrite ind_alias_lookup_entry, He; reflexivity ].
  unfold gc_entry, gc_resolve in *.
  destruct (gs_find Ξ pq) as [[U ip] |]; [ eapply gm_entry_resolve_none; [ exact He | intros; discriminate ] |].
  destruct (gds_lookup Θ (q_unit pq)); [ eapply gm_entry_resolve_none; [ exact He | intros; discriminate ] | discriminate ].
Qed.

(** A path names an inductive type or an inductive alias, not both. *)
Lemma ind_lookup_not_ind_alias : forall Θ Ξ p D,
    ind_lookup Θ Ξ p = Some D -> ind_alias_lookup Θ Ξ p = None.
Proof.
  intros * H; destruct (ind_lookup_entry _ _ _ _ H) as (? & ? & He).
  rewrite ind_alias_lookup_entry, He; reflexivity.
Qed.

Lemma ind_lookup_not_ind_alias_rev : forall Θ Ξ p Δ pt Ns,
    ind_alias_lookup Θ Ξ p = Some (Δ, pt, Ns) -> ind_lookup Θ Ξ p = None.
Proof.
  intros * H; destruct (ind_lookup Θ Ξ p) as [D |] eqn:E; [| reflexivity ].
  rewrite (ind_lookup_not_ind_alias _ _ _ _ E) in H; discriminate.
Qed.

(** [gm_grows Φ Φ']: [Φ'] is [Φ] with more definitions, of fresh names,
    after it, and no more modules.  The body of the module of an inductive
    type grows so while its members are checked ([wf_gentry_ind_ext]). *)
Inductive gm_grows (Φ : gmod) : gmod -> Prop :=
| gmg_refl : gm_grows Φ Φ
| gmg_ext : forall Φ' x b pv A B, gm_grows Φ Φ' -> gm_fresh x Φ' -> gm_grows Φ (Φ' ⊳ x ↦ ge_def b pv A B).

#[export]
Hint Constructors gm_grows : mctt.

Lemma gm_grows_trans : forall Φ1 Φ2 Φ3, gm_grows Φ1 Φ2 -> gm_grows Φ2 Φ3 -> gm_grows Φ1 Φ3.
Proof. intros * H12 H23; induction H23; eauto with mctt. Qed.

(** ** How Resolution Grows

    Every way a global context grows preserves what resolves, both definitions
    and modules, and the declarations of inductive types: this is the whole of
    what moving a judgment from one global context to a bigger one needs.  A
    body module keeps its body, but for entries after it: only the module of
    an inductive type grows so, while its members are checked. *)
Definition gc_sub (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  (forall p E, gc_resolve Θ1 Ξ1 p = Some E -> gc_resolve Θ2 Ξ2 p = Some E) /\
  (forall p r, gc_module Θ1 Ξ1 p = Some r -> gc_module Θ2 Ξ2 p = Some r) /\
  (forall p T Φ, gc_body Θ1 Ξ1 p = Some (T, Φ) ->
     exists Φ', gc_body Θ2 Ξ2 p = Some (T, Φ') /\ gm_grows Φ Φ') /\
  (forall pq v, ind_alias_lookup Θ1 Ξ1 pq = Some v -> ind_alias_lookup Θ2 Ξ2 pq = Some v).

Lemma gc_sub_resolve : forall Θ1 Ξ1 Θ2 Ξ2 p E,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_resolve Θ1 Ξ1 p = Some E -> gc_resolve Θ2 Ξ2 p = Some E.
Proof. intros * [H _]; apply H. Qed.

Lemma gc_sub_module : forall Θ1 Ξ1 Θ2 Ξ2 p r,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_module Θ1 Ξ1 p = Some r -> gc_module Θ2 Ξ2 p = Some r.
Proof. intros * [_ [H _]]; apply H. Qed.

Lemma gc_sub_body : forall Θ1 Ξ1 Θ2 Ξ2 p T Φ,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_body Θ1 Ξ1 p = Some (T, Φ) ->
    exists Φ', gc_body Θ2 Ξ2 p = Some (T, Φ') /\ gm_grows Φ Φ'.
Proof. intros * [_ [_ [H _]]]; apply H. Qed.

Lemma gc_sub_ind_alias : forall Θ1 Ξ1 Θ2 Ξ2 pq v,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> ind_alias_lookup Θ1 Ξ1 pq = Some v -> ind_alias_lookup Θ2 Ξ2 pq = Some v.
Proof. intros * [_ [_ [_ H]]]; apply H. Qed.

Lemma gc_sub_refl : forall Θ Ξ, gc_sub Θ Ξ Θ Ξ.
Proof. repeat split; intros * H; eauto with mctt. Qed.

Lemma gc_sub_trans : forall Θ1 Ξ1 Θ2 Ξ2 Θ3 Ξ3,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_sub Θ2 Ξ2 Θ3 Ξ3 -> gc_sub Θ1 Ξ1 Θ3 Ξ3.
Proof.
  intros * [H12 [M12 [B12 I12]]] [H23 [M23 [B23 I23]]]; repeat split; intros * H;
    [ apply H23, H12, H | apply M23, M12, H | | apply I23, I12, H ].
  destruct (B12 _ _ _ H) as (Φ2 & H2 & G12); destruct (B23 _ _ _ H2) as (Φ3 & H3 & G23).
  exists Φ3; split; [ exact H3 | exact (gm_grows_trans _ _ _ G12 G23) ].
Qed.

Lemma ind_lookup_gc_sub : forall Θ1 Ξ1 Θ2 Ξ2 p D,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> ind_lookup Θ1 Ξ1 p = Some D -> ind_lookup Θ2 Ξ2 p = Some D.
Proof.
  intros * Hs H; destruct (ind_lookup_module _ _ _ _ H) as [T Hm].
  unfold ind_lookup; rewrite (gc_sub_module _ _ _ _ _ _ Hs Hm); reflexivity.
Qed.

(** A body growing keeps its modules and its bodies. *)
Lemma gm_grows_names : forall Φ Φ', gm_grows Φ Φ' -> forall z, List.In z (gm_names Φ) -> List.In z (gm_names Φ').
Proof. induction 1; intros z Hz; cbn; auto. Qed.

Lemma gm_grows_submodule : forall Φ Φ', gm_grows Φ Φ' ->
    forall T x ip, gm_submodule T Φ' x ip = gm_submodule T Φ x ip.
Proof.
  induction 1 as [| Φ' y b pv A B Hg IH Hf]; intros; [ reflexivity |].
  cbn; destruct (String.eqb_spec x y) as [-> |]; [| apply IH ].
  destruct (gm_submodule T Φ y ip) eqn:E; [| reflexivity ].
  exfalso; exact (Hf (gm_grows_names _ _ Hg _ (gm_submodule_head _ _ _ _ _ E))).
Qed.

Lemma gm_grows_subbody : forall Φ Φ', gm_grows Φ Φ' ->
    forall T x ip, gm_subbody T Φ' x ip = gm_subbody T Φ x ip.
Proof.
  induction 1 as [| Φ' y b pv A B Hg IH Hf]; intros; [ reflexivity |].
  cbn; destruct (String.eqb_spec x y) as [-> |]; [| apply IH ].
  destruct (gm_subbody T Φ y ip) eqn:E; [| reflexivity ].
  exfalso; exact (Hf (gm_grows_names _ _ Hg _ (gm_subbody_head _ _ _ _ _ E))).
Qed.

Lemma gm_grows_module : forall Φ Φ', gm_grows Φ Φ' ->
    forall T oD ch, gm_module T oD Φ' ch = gm_module T oD Φ ch.
Proof. intros * Hg T oD [| x ip]; cbn; [ reflexivity | apply gm_grows_submodule; exact Hg ]. Qed.

Lemma gm_grows_body : forall Φ Φ', gm_grows Φ Φ' ->
    forall T x ip, gm_body T Φ' (x :: ip) = gm_body T Φ (x :: ip).
Proof. intros * Hg T x ip; cbn; apply gm_grows_subbody; exact Hg. Qed.

(** One body growing into another, as [gc_sub] asks of the frame holding
    it. *)
Definition gm_sub (Φ1 Φ2 : gmod) : Prop :=
  (forall ip E, gm_resolve Φ1 ip = Some E -> gm_resolve Φ2 ip = Some E) /\
  (forall T z ip r, gm_submodule T Φ1 z ip = Some r -> gm_submodule T Φ2 z ip = Some r) /\
  (forall T z ip T' Φ, gm_subbody T Φ1 z ip = Some (T', Φ) ->
     exists Φ', gm_subbody T Φ2 z ip = Some (T', Φ') /\ gm_grows Φ Φ') /\
  (forall ip v, gm_ind_target Φ1 ip = Some v -> gm_ind_target Φ2 ip = Some v).

Lemma gm_sub_refl : forall Φ, gm_sub Φ Φ.
Proof. repeat split; intros * H; eauto with mctt. Qed.

Lemma gm_sub_trans : forall Φ1 Φ2 Φ3, gm_sub Φ1 Φ2 -> gm_sub Φ2 Φ3 -> gm_sub Φ1 Φ3.
Proof.
  intros * [H12 [M12 [B12 I12]]] [H23 [M23 [B23 I23]]]; repeat split; intros * H;
    [ apply H23, H12, H | apply M23, M12, H | | apply I23, I12, H ].
  destruct (B12 _ _ _ _ _ H) as (Φ2' & H2 & G12); destruct (B23 _ _ _ _ _ H2) as (Φ3' & H3 & G23).
  exists Φ3'; split; [ exact H3 | exact (gm_grows_trans _ _ _ G12 G23) ].
Qed.

(** An entry of a fresh name. *)
Lemma gm_sub_ext_fresh : forall Φ x E, gm_fresh x Φ -> gm_sub Φ (Φ ⊳ x ↦ E).
Proof.
  intros * Hf; repeat split; intros * H.
  - exact (gm_resolve_ext_fresh _ _ _ _ _ Hf H).
  - exact (gm_submodule_ext_fresh _ _ _ _ _ _ _ Hf H).
  - eexists; split; [ exact (gm_subbody_ext_fresh _ _ _ _ _ _ _ Hf H) | constructor ].
  - exact (gm_ind_target_ext_fresh _ _ _ _ _ Hf H).
Qed.

Lemma gm_sub_grows : forall Φ Φ', gm_grows Φ Φ' -> gm_sub Φ Φ'.
Proof.
  induction 1; [ apply gm_sub_refl |].
  eapply gm_sub_trans; [ eassumption | apply gm_sub_ext_fresh; assumption ].
Qed.

(** The module of an inductive type growing. *)
Lemma gm_sub_ind : forall Φ0 y pv D Φ Φ',
    gm_grows Φ Φ' -> gm_sub (Φ0 ⊳ y ↦ ge_ind pv D Φ) (Φ0 ⊳ y ↦ ge_ind pv D Φ').
Proof.
  intros * Hg; destruct (gm_sub_grows _ _ Hg) as [HR [HM [HB HI]]].
  repeat split; intros * H; unfold gm_ind_target in *; cbn in H |- *.
  - destruct ip as [| x ip]; [ discriminate |].
    destruct (String.eqb x y); [| exact H ].
    destruct ip; [ discriminate | apply HR; exact H ].
  - destruct (String.eqb z y); [| exact H ].
    destruct ip; [ exact H | apply HM; exact H ].
  - destruct (String.eqb z y); [| eexists; split; [ exact H | constructor ] ].
    destruct ip.
    + injection H as <- <-; eexists; split; [ reflexivity | exact Hg ].
    + apply HB; exact H.
  - destruct ip as [| x ip]; [ discriminate |].
    destruct (String.eqb x y); [| exact H ].
    destruct ip; [ exact H | apply HI; exact H ].
Qed.

(** A frame whose body grows. *)
Lemma gc_sub_frame : forall Θ Ξ mp Δ Φ1 Φ2,
    gm_sub Φ1 Φ2 ->
    gc_sub Θ ((mp, gu_body Δ Φ1) :: Ξ) Θ ((mp, gu_body Δ Φ2) :: Ξ).
Proof.
  intros * [HR [HM [HB HI]]]; repeat split.
  - intros p E0 Hr; unfold gc_resolve in *; cbn in *.
    destruct (qname_strip mp p); [ apply HR; exact Hr | exact Hr ].
  - intros p r Hr; unfold gc_module in *; cbn in *.
    destruct (qname_strip mp p) as [[| y ip] |]; [ discriminate | | exact Hr ].
    apply HM; exact Hr.
  - intros p T Φ Hr; unfold gc_body in *; cbn in *.
    destruct (qname_strip mp p) as [[| y ip] |]; [ discriminate | | eexists; split; [ exact Hr | constructor ] ].
    apply HB; exact Hr.
  - intros pq p Hr; unfold ind_alias_lookup in *; cbn in *.
    destruct (qname_strip mp pq); [ apply HI; exact Hr | exact Hr ].
Qed.

(** A frame may be pushed when its module path is fresh where it is pushed: a
    unit not filed below, named by its root path, or a member not yet declared
    in the enclosing frame.  The root condition makes every prefix of a path
    that resolves resolve as well. *)
Definition frame_fresh (Θ : gdeps) (Ξ : gstack) (mp : qname) : Prop :=
  match Ξ with
  | nil => gds_lookup Θ (q_unit mp) = None /\ q_chain mp = nil
  | (mq, U) :: _ => exists x, mp = qname_in mq x /\ gm_fresh x (gu_mod U)
  end.

Lemma gc_sub_push : forall Θ Ξ mp U,
    frame_fresh Θ Ξ mp ->
    gc_sub Θ Ξ Θ ((mp, U) :: Ξ).
Proof.
  intros * Hf; repeat split.
  - intros p E Hr; unfold gc_resolve in *; cbn.
    destruct (qname_strip mp p) as [ip |] eqn:Hs; [| exact Hr ].
    exfalso; unfold qname_strip in Hs.
    destruct (path_beq (q_unit mp) (q_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb.
    destruct Ξ as [| [mq V] Ξ']; cbn in Hf, Hr.
    + destruct Hf as [Hf _].
      rewrite <- Hb, Hf in Hr; discriminate.
    + destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
      pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
      unfold qname_strip in Hr; rewrite Hb, path_beq_refl, Hs' in Hr.
      destruct (gm_resolve_head _ _ _ Hr) as (z & ip' & [= <- <-] & Hin); contradiction.
  - intros p r Hr; unfold gc_module in *; cbn.
    destruct (qname_strip mp p) as [ip |] eqn:Hs; [| exact Hr ].
    exfalso; unfold qname_strip in Hs.
    destruct (path_beq (q_unit mp) (q_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb.
    destruct Ξ as [| [mq V] Ξ']; cbn in Hf, Hr.
    + destruct Hf as [Hf _].
      rewrite <- Hb, Hf in Hr; discriminate.
    + destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
      pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
      unfold qname_strip in Hr; rewrite Hb, path_beq_refl, Hs' in Hr.
      exact (Hx (gm_submodule_head _ _ _ _ _ Hr)).
  - intros p T Φ Hr; unfold gc_body in *; cbn.
    destruct (qname_strip mp p) as [ip |] eqn:Hs; [| eexists; split; [ exact Hr | constructor ] ].
    exfalso; unfold qname_strip in Hs.
    destruct (path_beq (q_unit mp) (q_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb.
    destruct Ξ as [| [mq V] Ξ']; cbn in Hf, Hr.
    + destruct Hf as [Hf _].
      rewrite <- Hb, Hf in Hr; discriminate.
    + destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
      pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
      unfold qname_strip in Hr; rewrite Hb, path_beq_refl, Hs' in Hr.
      exact (Hx (gm_subbody_head _ _ _ _ _ Hr)).
  - intros pq p0 Hr; unfold ind_alias_lookup, gm_ind_target in *; cbn.
    destruct (qname_strip mp pq) as [ip |] eqn:Hs; [| exact Hr ].
    exfalso; unfold qname_strip in Hs.
    destruct (path_beq (q_unit mp) (q_unit pq)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb.
    destruct Ξ as [| [mq V] Ξ']; cbn in Hf, Hr.
    + destruct Hf as [Hf _].
      rewrite <- Hb, Hf in Hr; discriminate.
    + destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
      pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
      unfold qname_strip in Hr; rewrite Hb, path_beq_refl, Hs' in Hr.
      destruct (gm_entry (gu_mod V) (x :: ip)) eqn:He; [| discriminate ].
      destruct (gm_entry_head _ _ _ He) as (z & ip' & [= <- <-] & Hin); contradiction.
Qed.

Lemma gc_sub_grow : forall Θ Ξ mp Δ Φ x E,
    gm_fresh x Φ ->
    gc_sub Θ ((mp, gu_body Δ Φ) :: Ξ) Θ ((mp, gu_body Δ (Φ ⊳ x ↦ E)) :: Ξ).
Proof. intros * Hf; apply gc_sub_frame, gm_sub_ext_fresh; exact Hf. Qed.

(** The module of an inductive type, an entry of the innermost frame,
    growing. *)
Lemma gc_sub_ind_grows : forall Θ Ξ mp Δ Φ0 y pv D Φ Φ',
    gm_grows Φ Φ' ->
    gc_sub Θ ((mp, gu_body Δ (Φ0 ⊳ y ↦ ge_ind pv D Φ)) :: Ξ) Θ ((mp, gu_body Δ (Φ0 ⊳ y ↦ ge_ind pv D Φ')) :: Ξ).
Proof. intros * Hg; apply gc_sub_frame, gm_sub_ind; exact Hg. Qed.

(** Filing a unit: what was read in its open frame is read in the filed
    unit. *)
Lemma gc_sub_file : forall Θ fp U,
    gds_lookup Θ fp = None ->
    gc_sub Θ ((q_abs fp nil, U) :: nil) ((fp, U) :: Θ) nil.
Proof.
  intros * Hn; repeat split.
  - intros p E0 Hr; unfold gc_resolve in *; cbn [gs_find] in *.
    unfold qname_strip in Hr; cbn [q_unit q_chain strip_prefix] in Hr; cbn [gds_lookup].
    destruct (path_beq fp (q_unit p)) eqn:Hb.
    + apply path_beq_true in Hb; subst; rewrite path_beq_refl; exact Hr.
    + destruct (path_beq (q_unit p) fp) eqn:Hb'; [ apply path_beq_true in Hb'; subst; rewrite path_beq_refl in Hb; discriminate | exact Hr ].
  - intros p r Hr; unfold gc_module in *; cbn [gs_find_tele] in *.
    unfold qname_strip in Hr; cbn [q_unit q_chain strip_prefix] in Hr; cbn [gds_lookup].
    destruct (path_beq fp (q_unit p)) eqn:Hb.
    + apply path_beq_true in Hb; subst; rewrite path_beq_refl.
      destruct (q_chain p) as [| x ip] eqn:Hp; [ discriminate |].
      cbn in *; rewrite List.app_nil_r in Hr; exact Hr.
    + destruct (path_beq (q_unit p) fp) eqn:Hb'; [ apply path_beq_true in Hb'; subst; rewrite path_beq_refl in Hb; discriminate | exact Hr ].
  - intros p T Φ Hr; exists Φ; split; [| constructor ]; unfold gc_body in *; cbn [gs_find_tele] in *.
    unfold qname_strip in Hr; cbn [q_unit q_chain strip_prefix] in Hr; cbn [gds_lookup].
    destruct (path_beq fp (q_unit p)) eqn:Hb.
    + apply path_beq_true in Hb; subst; rewrite path_beq_refl.
      destruct (q_chain p) as [| x ip] eqn:Hp; [ discriminate |].
      cbn in *; rewrite List.app_nil_r in Hr; exact Hr.
    + destruct (path_beq (q_unit p) fp) eqn:Hb'; [ apply path_beq_true in Hb'; subst; rewrite path_beq_refl in Hb; discriminate | exact Hr ].
  - intros pq p0 Hr; unfold ind_alias_lookup in *; cbn [gs_find] in *.
    unfold qname_strip in Hr; cbn [q_unit q_chain strip_prefix] in Hr; cbn [gds_lookup].
    destruct (path_beq fp (q_unit pq)) eqn:Hb.
    + apply path_beq_true in Hb; subst; rewrite path_beq_refl; exact Hr.
    + destruct (path_beq (q_unit pq) fp) eqn:Hb'; [ apply path_beq_true in Hb'; subst; rewrite path_beq_refl in Hb; discriminate | exact Hr ].
Qed.

(** A filed unit resolves as its closed frame did. *)
Lemma gc_resolve_file : forall Θ fp U p,
    gc_resolve ((fp, U) :: Θ) nil p = gc_resolve Θ ((q_abs fp nil, U) :: nil) p.
Proof.
  intros; unfold gc_resolve; cbn [gs_find gds_lookup]; unfold qname_strip; cbn [q_unit q_chain strip_prefix].
  destruct (path_beq fp (q_unit p)) eqn:Hb.
  - apply path_beq_true in Hb as ->; rewrite path_beq_refl; reflexivity.
  - destruct (path_beq (q_unit p) fp) eqn:Hb'; [| reflexivity ].
    apply path_beq_true in Hb'; rewrite Hb', path_beq_refl in Hb; discriminate.
Qed.

(** Filing more units under the same stack. *)
Lemma gc_sub_deps : forall Θ Θ' Ξ, Θ ⊑ Θ' -> gc_sub Θ Ξ Θ' Ξ.
Proof.
  intros * Hs; repeat split.
  - intros p E Hr; unfold gc_resolve in *.
    destruct (gs_find Ξ p) as [[U ip] |]; [ exact Hr |].
    destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:E1; [| discriminate ].
    rewrite (Hs _ _ E1); exact Hr.
  - intros p r Hr; unfold gc_module in *.
    destruct (gs_find_tele Ξ p) as [[[U ip] T] |]; [ exact Hr |].
    destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:E1; [| discriminate ].
    rewrite (Hs _ _ E1); exact Hr.
  - intros p T Φ Hr; exists Φ; split; [| constructor ]; unfold gc_body in *.
    destruct (gs_find_tele Ξ p) as [[[U ip] T'] |]; [ exact Hr |].
    destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:E1; [| discriminate ].
    rewrite (Hs _ _ E1); exact Hr.
  - intros pq p0 Hr; unfold ind_alias_lookup in *.
    destruct (gs_find Ξ pq) as [[U ip] |]; [ exact Hr |].
    destruct (gds_lookup Θ (q_unit pq)) as [V |] eqn:E1; [| discriminate ].
    rewrite (Hs _ _ E1); exact Hr.
Qed.

(** ** Growth Keeping Bodies

    [gc_subx]: growth that keeps every body module's body as it is.  Every
    way a well-formed global context is extended by a command or a frame
    is of this kind; only the module of an inductive type grows its body,
    while its members are checked. *)
Definition gc_subx (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  gc_sub Θ1 Ξ1 Θ2 Ξ2 /\ (forall p r, gc_body Θ1 Ξ1 p = Some r -> gc_body Θ2 Ξ2 p = Some r).

Lemma gc_subx_sub : forall Θ1 Ξ1 Θ2 Ξ2, gc_subx Θ1 Ξ1 Θ2 Ξ2 -> gc_sub Θ1 Ξ1 Θ2 Ξ2.
Proof. intros * [H _]; exact H. Qed.

Lemma gc_subx_body : forall Θ1 Ξ1 Θ2 Ξ2 p r,
    gc_subx Θ1 Ξ1 Θ2 Ξ2 -> gc_body Θ1 Ξ1 p = Some r -> gc_body Θ2 Ξ2 p = Some r.
Proof. intros * [_ H]; apply H. Qed.

Lemma gc_subx_refl : forall Θ Ξ, gc_subx Θ Ξ Θ Ξ.
Proof. split; [ apply gc_sub_refl | auto ]. Qed.

Lemma gc_subx_trans : forall Θ1 Ξ1 Θ2 Ξ2 Θ3 Ξ3,
    gc_subx Θ1 Ξ1 Θ2 Ξ2 -> gc_subx Θ2 Ξ2 Θ3 Ξ3 -> gc_subx Θ1 Ξ1 Θ3 Ξ3.
Proof.
  intros * [H12 B12] [H23 B23]; split; [ eapply gc_sub_trans; eassumption | auto ].
Qed.

Lemma gc_subx_push : forall Θ Ξ mp U, frame_fresh Θ Ξ mp -> gc_subx Θ Ξ Θ ((mp, U) :: Ξ).
Proof.
  intros * Hf; split; [ apply gc_sub_push; exact Hf |].
  intros p r Hr; unfold gc_body in *; cbn.
  destruct (qname_strip mp p) as [ip |] eqn:Hs; [| exact Hr ].
  exfalso; unfold qname_strip in Hs.
  destruct (path_beq (q_unit mp) (q_unit p)) eqn:Hb; [| discriminate ].
  apply path_beq_true in Hb.
  destruct Ξ as [| [mq V] Ξ']; cbn in Hf, Hr.
  - destruct Hf as [Hf _]; rewrite <- Hb, Hf in Hr; discriminate.
  - destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
    pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
    unfold qname_strip in Hr; rewrite Hb, path_beq_refl, Hs' in Hr.
    exact (Hx (gm_subbody_head _ _ _ _ _ Hr)).
Qed.

Lemma gc_subx_grow : forall Θ Ξ mp Δ Φ x E,
    gm_fresh x Φ ->
    gc_subx Θ ((mp, gu_body Δ Φ) :: Ξ) Θ ((mp, gu_body Δ (Φ ⊳ x ↦ E)) :: Ξ).
Proof.
  intros * Hf; split; [ apply gc_sub_grow; exact Hf |].
  intros p r Hr; unfold gc_body in *; cbn in *.
  destruct (qname_strip mp p) as [[| y ip] |]; [ discriminate | | exact Hr ].
  cbn in *; apply gm_subbody_ext_fresh; assumption.
Qed.

Lemma gc_subx_file : forall Θ fp U,
    gds_lookup Θ fp = None ->
    gc_subx Θ ((q_abs fp nil, U) :: nil) ((fp, U) :: Θ) nil.
Proof.
  intros * Hn; split; [ apply gc_sub_file; exact Hn |].
  intros p r Hr; unfold gc_body in *; cbn [gs_find_tele] in *.
  unfold qname_strip in Hr; cbn [q_unit q_chain strip_prefix] in Hr; cbn [gds_lookup].
  destruct (path_beq fp (q_unit p)) eqn:Hb.
  - apply path_beq_true in Hb; subst; rewrite path_beq_refl.
    destruct (q_chain p) as [| x ip] eqn:Hp; [ discriminate |].
    cbn in *; rewrite List.app_nil_r in Hr; exact Hr.
  - destruct (path_beq (q_unit p) fp) eqn:Hb'; [ apply path_beq_true in Hb'; subst; rewrite path_beq_refl in Hb; discriminate | exact Hr ].
Qed.

Lemma gc_subx_deps : forall Θ Θ' Ξ, Θ ⊑ Θ' -> gc_subx Θ Ξ Θ' Ξ.
Proof.
  intros * Hs; split; [ apply gc_sub_deps; exact Hs |].
  intros p r Hr; unfold gc_body in *.
  destruct (gs_find_tele Ξ p) as [[[U ip] T'] |]; [ exact Hr |].
  destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:E1; [| discriminate ].
  rewrite (Hs _ _ E1); exact Hr.
Qed.

(** ** Transparent Global Contexts

    Every definition is transparent and has a body: then no global is a
    neutral, which is what canonicity and consistency need.  Parameters, being
    λ-variables, impose nothing. *)

Fixpoint ge_transparent (E : gentry) : Prop :=
  match E with
  | ge_def b _ _ B => b = true /\ B <> None
  | ge_mod _ (gu_mk _ (md_body Φ)) => gm_transparent Φ
  | ge_mod _ (gu_mk _ (md_alias _)) => True
  | ge_ind _ _ Φ => gm_transparent Φ
  | ge_ind_alias _ _ _ _ => True
  end
with gm_transparent (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ _ E => gm_transparent Φ /\ ge_transparent E
  | gm_open Φ _ _ => gm_transparent Φ
  end.

Definition gc_transparent (Θ : gdeps) (Ξ : gstack) : Prop :=
  (forall fp U, List.In (fp, U) Θ -> gm_transparent (gu_mod U)) /\
  (forall mp U, List.In (mp, U) Ξ -> gm_transparent (gu_mod U)).

Lemma gm_transparent_resolve : forall Φ ip E,
    gm_transparent Φ -> gm_resolve Φ ip = Some E -> ge_transparent E.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] ip E0 HΦ H; cbn in H, HΦ; [ discriminate | | eapply IH; eassumption ].
  destruct HΦ as [HΦ HE].
  destruct ip as [| x ip']; [ discriminate |].
  destruct (String.eqb x y); [| eapply IH; eassumption ].
  destruct ip' as [| z ip''], E as [b pv A B | pm [Δ' [Φ' | E']] | pv D Φ' | pv Δa pa Nsa]; try discriminate.
  - injection H as <-; exact HE.
  - eapply IH; [ exact HE | exact H ].
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
  - exact (gm_transparent_resolve _ _ _ (HΘ _ _ (gds_lookup_in _ _ _ Hl)) Hm).
Qed.

(** ** Module Slots *)

Reserved Notation "Γ ∋ '#' x ⇒ₘ U" (at level 70, x constr at level 0, U at level 69).

(** The unit of a module slot, weakened to the use site. *)
Inductive ctx_lookup_mod : nat -> gunit -> ctx -> Prop :=
(** The innermost slot *)
| mod_here : `(Γ ▹ₘ U ∋ #0 ⇒ₘ gunit_wk U wk_shift)
(** A slot under one more entry *)
| mod_there : `(Γ ∋ #n ⇒ₘ U -> e :: Γ ∋ #(S n) ⇒ₘ gunit_wk U wk_shift)
where "Γ ∋ '#' x ⇒ₘ U" := (ctx_lookup_mod x U Γ) : type_scope.

#[export]
Hint Constructors ctx_lookup_mod : mctt.

Fixpoint ctx_find_mod (Γ : ctx) (x : nat) : option gunit :=
  match Γ with
  | nil => None
  | e :: Γ' =>
      match x with
      | 0 => match e with ce_mod U => Some (gunit_wk U wk_shift) | _ => None end
      | S y => option_map (fun U => gunit_wk U wk_shift) (ctx_find_mod Γ' y)
      end
  end.

Lemma ctx_find_mod_sound : forall Γ x U, ctx_find_mod Γ x = Some U -> Γ ∋ #x ⇒ₘ U.
Proof.
  induction Γ as [| e Γ IH]; intros [| y] U H; cbn in H; try discriminate.
  - destruct e; cbn in H; try discriminate; injection H as <-; constructor.
  - destruct (ctx_find_mod Γ y) eqn:E; cbn in H; [| discriminate ].
    injection H as <-; constructor; apply IH; assumption.
Qed.

Lemma ctx_find_mod_complete : forall Γ x U, Γ ∋ #x ⇒ₘ U -> ctx_find_mod Γ x = Some U.
Proof. induction 1; cbn; [ reflexivity | rewrite IHctx_lookup_mod; reflexivity ]. Qed.

Lemma ctx_find_mod_spec : forall Γ x U, ctx_find_mod Γ x = Some U <-> Γ ∋ #x ⇒ₘ U.
Proof. split; auto using ctx_find_mod_sound, ctx_find_mod_complete. Qed.

Lemma ctx_lookup_mod_functional : forall Γ x U U', Γ ∋ #x ⇒ₘ U -> Γ ∋ #x ⇒ₘ U' -> U = U'.
Proof. intros * H H'; apply ctx_find_mod_spec in H, H'; congruence. Qed.

(** ** Syntactic Helpers *)

(** The body up to and including the entry named [x]. *)
Fixpoint gm_prefix_upto (Φ : gmod) (x : string) : option gmod :=
  match Φ with
  | gm_nil => None
  | gm_ext Φ' y _ => if String.eqb x y then Some Φ else gm_prefix_upto Φ' x
  | gm_open Φ' _ _ => gm_prefix_upto Φ' x
  end.

(** [M] applied to [args], outermost first ([apps_exp]). *)
Abbreviation apps := apps_exp (only parsing).

(** The root of a module expression, its arguments, outermost first, and the
    chain of submodules selected.  Arguments and selections commute, since
    members are closed over the parameters they lie under. *)
Fixpoint modexp_spine (H : modexp) : (modexp * list exp * list string)%type :=
  match H with
  | me_mem H y => let '(R, args, pre) := modexp_spine H in (R, args, pre ++ y :: nil)
  | me_app H N => let '(R, args, pre) := modexp_spine H in (R, args ++ N :: nil, pre)
  | _ => (H, nil, nil)
  end.

(** A module expression with no argument. *)
Fixpoint me_noargs (H : modexp) : Prop :=
  match H with
  | me_mem H _ => me_noargs H
  | me_app _ _ => False
  | _ => True
  end.

(** The Π a type is, looking through local definitions and local modules. *)
Fixpoint pi_view (A : typ) : option (typ * typ)%type :=
  match A with
  | a_pi B C => Some (B, C)
  | a_let (b_def B N) T =>
      match pi_view T with
      | Some (B', C') => Some (B'[Id,,N], C'[q (Id,,N)])
      | None => None
      end
  | a_let (b_mod U) T =>
      match pi_view T with
      | Some (B', C') => Some (B'[Id ,,ₘ me_lit U], C'[q (Id ,,ₘ me_lit U)])
      | None => None
      end
  | _ => None
  end.

(** ** Arities

    A module's arity is the telescope of parameters it still takes, a [ctx]
    over the context of the module, innermost first.  Its entries may include
    local definitions and modules, from the bodies around the module; they
    are not parameters, and an argument goes to the outermost assumption,
    through them.

    [tele_view T] is that assumption's type and the rest of the telescope,
    over the context extended by it, the definitions and modules outside the
    assumption substituted away; [None] if [T] has no assumption left.  It is
    computed outermost first, on the reversed telescope, as [pi_view] is on a
    type: through a definition, the view inside it is moved out by
    substituting the definition. *)
Fixpoint tele_open (R : list centry) : option (typ * ctx)%type :=
  match R with
  | nil => None
  | ce_ass B :: R' => Some (B, rev R')
  | ce_def B N :: R' =>
      match tele_open R' with
      | Some (B', T') => Some (B'[Id,,N], tele_sub T' (q (Id,,N)))
      | None => None
      end
  | ce_mod U :: R' =>
      match tele_open R' with
      | Some (B', T') => Some (B'[Id ,,ₘ me_lit U], tele_sub T' (q (Id ,,ₘ me_lit U)))
      | None => None
      end
  end.

Definition tele_view (T : ctx) : option (typ * ctx)%type := tele_open (rev T).

(** The telescope left when the outermost parameter is instantiated with
    [N]: a module of arity [T], applied to [N], has arity [tele_inst T N]. *)
Definition tele_inst (T : ctx) (N : exp) : option ctx :=
  match tele_view T with
  | Some (_, T') => Some (tele_sub T' (Id,,N))
  | None => None
  end.

(** A module [F (A : Typeω@0) (f : forall (x : A) -> A)] takes [⋅ ▹ Typeω@0 ▹
    Π #0 #1]; applied to [ℕ], it takes [⋅ ▹ Π ℕ ℕ]. *)
Example tele_inst_example : tele_inst (⋅ ▹ Typeω@0 ▹ Π #0 #1) ℕ = Some (⋅ ▹ Π ℕ ℕ).
Proof. reflexivity. Qed.

(** ** Member Types

    [member_type Θ Ξ Γ H ch R] says that the chain [ch] of the module [H] is
    a definition of canonical type [A] ([R = mr_term A]), or a module that
    still takes the parameters [T] ([R = mr_mod T]).  A module is applied to
    an argument of the type of its outermost parameter, [tele_view]: it may be
    applied to fewer arguments than it has parameters, but not to more.

    A body member's type is its declared type, generalized over the unit's
    parameters and over the body before it, which become [ℓ]/[ℓₘ] binders; a
    module's arity is extended by them.  An alias member's type is its target
    member's type, instantiated with the alias's arguments and generalized over
    its parameters.  A chain from a unit is read off the global context;
    privacy is not a matter of typing (see [Command]). *)

(** The sort of a member. *)
Inductive mkind : Set :=
(** A definition *)
| mk_term
(** A module *)
| mk_mod.

(** The type of a member. *)
Inductive mres : Set :=
(** A definition, of this type. *)
| mr_term : typ -> mres
(** A module, with the parameters it still takes. *)
| mr_mod : ctx -> mres.

Definition mres_kind (R : mres) : mkind :=
  match R with
  | mr_term _ => mk_term
  | mr_mod _ => mk_mod
  end.

(** The parameters a module still takes. *)
Definition mres_tl (R : mres) : option ctx :=
  match R with
  | mr_mod T => Some T
  | mr_term _ => None
  end.

(** A member type as a type: a module's arity is the [Π] over its parameters,
    into [⊤].  The semantics reads member types through it. *)
Definition mres_ty (R : mres) : typ :=
  match R with
  | mr_term A => A
  | mr_mod T => ctx_pi T a_True
  end.

(** A member type generalized over a telescope it lives under. *)
Definition mres_gen (Δ : ctx) (R : mres) : mres :=
  match R with
  | mr_term A => mr_term (ctx_pi Δ A)
  | mr_mod T => mr_mod (T ++ Δ)
  end.

(** The type of a member of [H N], from the type [R] of the member of [H]:
    the outermost parameter of [R] instantiated with [N]. *)
Definition mres_app (R : mres) (N : exp) : option mres :=
  match R with
  | mr_term A =>
      match pi_view A with
      | Some (_, C) => Some (mr_term C[Id,,N])
      | None => None
      end
  | mr_mod T => option_map mr_mod (tele_inst T N)
  end.

Definition mres_wk (R : mres) (φ : wk) : mres :=
  match R with
  | mr_term A => mr_term A[φ]ʷ
  | mr_mod T => mr_mod (tele_wk T φ)
  end.

Definition mres_sub (R : mres) (σ : sub) : mres :=
  match R with
  | mr_term A => mr_term A[σ]
  | mr_mod T => mr_mod (tele_sub T σ)
  end.

Inductive member_type (Θ : gdeps) (Ξ : gstack) : ctx -> modexp -> list string -> mres -> Prop :=
(** A definition reached from a unit, of its declared type. *)
| mt_unit_def : forall Γ fp ch b pv A B,
    ch <> nil ->
    gc_resolve Θ Ξ (q_abs fp ch) = Some (ge_def b pv A B) ->
    member_type Θ Ξ Γ (me_unit fp) ch (mr_term A)
(** A body module reached from a unit, taking the parameters it is filed
    with; the module of an inductive type is one. *)
| mt_unit_mod : forall Γ fp ch T oD,
    gc_module Θ Ξ (q_abs fp ch) = Some (mr_body T oD) ->
    member_type Θ Ξ Γ (me_unit fp) ch (mr_mod T)
(** A chain through an alias reached from a unit, read in the alias, past it. *)
| mt_unit_alias : forall Γ fp ch U r R,
    (mres_kind R = mk_term -> r <> nil) ->
    gc_module Θ Ξ (q_abs fp ch) = Some (mr_alias U r) ->
    unit_member_type Θ Ξ nil U r R ->
    member_type Θ Ξ Γ (me_unit fp) ch R
(** A chain of a module slot, read in the unit it holds. *)
| mt_var : forall Γ x U ch R,
    Γ ∋ #x ⇒ₘ U ->
    unit_member_type Θ Ξ Γ U ch R ->
    member_type Θ Ξ Γ (me_var x) ch R
(** A chain of a literal module. *)
| mt_lit : forall Γ U ch R,
    unit_member_type Θ Ξ Γ U ch R ->
    member_type Θ Ξ Γ (me_lit U) ch R
(** A selection is read as a longer chain; a definition is not a module. *)
| mt_mem : forall Γ H y ch R,
    (mres_kind R = mk_term -> ch <> nil) ->
    member_type Θ Ξ Γ H (y :: ch) R ->
    member_type Θ Ξ Γ (me_mem H y) ch R
(** A member of an application: the member of the module, its outermost
    parameter instantiated with the argument. *)
| mt_app : forall Γ H N ch R R',
    member_type Θ Ξ Γ H ch R ->
    mres_app R N = Some R' ->
    member_type Θ Ξ Γ (me_app H N) ch R'
with unit_member_type (Θ : gdeps) (Ξ : gstack) : ctx -> gunit -> list string -> mres -> Prop :=
(** A body unit itself takes its parameters. *)
| umt_self : forall Γ Δ Φ,
    unit_member_type Θ Ξ Γ (gu_body Δ Φ) nil (mr_mod Δ)
(** A definition of the body, generalized over the parameters and the body
    before it. *)
| umt_def : forall Γ Δ Φ Φ' x b pv A B,
    gm_prefix_upto Φ x = Some (gm_ext Φ' x (ge_def b pv A B)) ->
    unit_member_type Θ Ξ Γ (gu_body Δ Φ) (x :: nil) (mr_term (ctx_pi (body_ctx Φ' ++ Δ) A))
(** A chain through a module of the body, read in it, generalized over the
    parameters and the body before it. *)
| umt_mod : forall Γ Δ Φ Φ' y pm Uy ch R,
    (mres_kind R = mk_term -> ch <> nil) ->
    gm_prefix_upto Φ y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
    unit_member_type Θ Ξ (body_ctx Φ' ++ Δ ++ Γ) Uy ch R ->
    unit_member_type Θ Ξ Γ (gu_body Δ Φ) (y :: ch) (mres_gen (body_ctx Φ' ++ Δ) R)
(** A chain of an alias, read in its target, generalized over the alias's
    parameters. *)
| umt_alias : forall Γ Δ E ch R,
    member_type Θ Ξ (Δ ++ Γ) E ch R ->
    unit_member_type Θ Ξ Γ (gu_mk Δ (md_alias E)) ch (mres_gen Δ R).

Scheme member_type_mut_ind := Induction for member_type Sort Prop
with unit_member_type_mut_ind := Induction for unit_member_type Sort Prop.
Combined Scheme member_type_both_ind from member_type_mut_ind, unit_member_type_mut_ind.

#[export]
Hint Constructors member_type unit_member_type : mctt.


(** ** Expansions and the δ-Reduct

    The expansion of a member of a unit is a term of the unit's context: a
    body member is its body under the unit's parameters and the body before
    it; an alias member is its target member under the alias's parameters.
    The δ-reduct of [H.x] makes one lookup: a definition reached from a unit
    is its own reduct, the global, which unfolds by its own rule; otherwise it
    is the expansion of a member of an alias, or of a member of a slot or a
    literal.  It never follows an alias chain. *)

Definition member_expansion (U : gunit) (ch : list string) : option exp :=
  match U, ch with
  | _, nil => None
  | gu_mk Δ (md_alias E), _ => Some (ctx_fn Δ (member_ref E ch))
  | gu_mk Δ (md_body Φ), x :: ch' =>
      match gm_prefix_upto Φ x, ch' with
      | Some (gm_ext Φ' y (ge_def b pv A B)), nil =>
          Some (ctx_fn (body_ctx (gm_ext Φ' y (ge_def b pv A B)) ++ Δ) (a_var 0))
      | Some (gm_ext Φ' y (ge_mod pm Uy)), _ :: _ =>
          Some (ctx_fn (body_ctx (gm_ext Φ' y (ge_mod pm Uy)) ++ Δ) (member_ref (me_var 0) ch'))
      | _, _ => None
      end
  end.

Fixpoint member_unfold_ch (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) (ch : list string) : option exp :=
  match H with
  | me_unit fp =>
      match gc_resolve Θ Ξ (q_abs fp ch) with
      | Some (ge_def _ _ _ _) => Some (member_ref (me_unit fp) ch)
      | _ =>
          match gc_module Θ Ξ (q_abs fp ch) with
          | Some (mr_alias U r) => member_expansion U r
          | _ => None
          end
      end
  | me_var x =>
      match ctx_find_mod Γ x with
      | Some U => member_expansion U ch
      | None => None
      end
  | me_lit U => member_expansion U ch
  | me_mem H y => member_unfold_ch Θ Ξ Γ H (y :: ch)
  | me_app H N => option_map (fun M => a_app M N) (member_unfold_ch Θ Ξ Γ H ch)
  end.

Definition member_unfold (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) (x : string) : option exp :=
  member_unfold_ch Θ Ξ Γ H (x :: nil).

(** ** The Module that Declares a Member

    [mdecl Θ Ξ H ch qd pv]: the member at the chain [ch] of the module
    expression [H], reached from a unit, a definition or a submodule, is
    declared in the module named [qd], with privacy [pv].  A chain through a
    global alias goes on in the alias's target, past its arguments. *)
Inductive mdecl (Θ : gdeps) (Ξ : gstack) : modexp -> list string -> qname -> bool -> Prop :=
(** A member reached through body modules, declared in the module the chain
    names before it. *)
| mdl_entry : forall fp ch E pv,
    gc_entry Θ Ξ (q_abs fp ch) = Some E ->
    ge_private E = pv ->
    mdecl Θ Ξ (me_unit fp) ch (q_abs fp (removelast ch)) pv
(** A chain past an alias goes on in the alias's target. *)
| mdl_alias : forall fp ch T E r qd pv,
    r <> nil ->
    gc_module Θ Ξ (q_abs fp ch) = Some (mr_alias (gu_mk T (md_alias E)) r) ->
    mdecl Θ Ξ E r qd pv ->
    mdecl Θ Ξ (me_unit fp) ch qd pv
(** A selection is read as a longer chain from its module. *)
| mdl_mem : forall H y ch qd pv,
    mdecl Θ Ξ H (y :: ch) qd pv ->
    mdecl Θ Ξ (me_mem H y) ch qd pv
(** Arguments do not change where a member is declared. *)
| mdl_app : forall H N ch qd pv,
    mdecl Θ Ξ H ch qd pv ->
    mdecl Θ Ξ (me_app H N) ch qd pv.

#[export]
Hint Constructors mdecl : mctt.
