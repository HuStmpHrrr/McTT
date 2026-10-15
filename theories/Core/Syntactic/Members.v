(** * Resolution and Members of Modules

    What a path names in the global context is a lookup ([gc_resolve],
    [gc_module], [gc_body]).  A module has no signature: the type of a member is computed from the
    module, when it is needed, by the relation [member_type], and its
    δ-reduct by the relation [member_unfold].  Both read syntax, context
    lookup and global resolution only, so they sit outside the mutual block of
    judgments, which uses them. *)

From Stdlib Require Import Lia List String Bool.

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

(** Each lookup of a global name is defined at a function [uf] finding the
    filed unit at a path (its [_u] version), and then at [gds_lookup Θ]: an
    implementation may find the filed units faster, and gets the same results
    when its function agrees with [gds_lookup Θ] ([gc_resolve_u_ok] and the
    like). *)

(** A path inside an open frame is read there, and anything else in the filed
    unit it names.  Nothing is re-expressed: entries are closed and paths
    absolute. *)
Definition gc_resolve_u (uf : path -> option gunit) (Ξ : gstack) (p : qname) : option gentry :=
  match gs_find Ξ p with
  | Some (U, ip) => gm_resolve (gu_mod U) ip
  | None =>
      match uf (q_unit p) with
      | Some U => gm_resolve (gu_mod U) (q_chain p)
      | None => None
      end
  end.

Definition gc_resolve (Θ : gdeps) (Ξ : gstack) (p : qname) : option gentry := gc_resolve_u (gds_lookup Θ) Ξ p.

(** A module path inside an open frame is read there, provided it names a
    closed module: the open frame itself is not a module yet.  The telescope of
    the frame is its own parameters on top of those of the frames outside. *)
Definition gc_module_u (uf : path -> option gunit) (Ξ : gstack) (p : qname) : option modres :=
  match gs_find_tele Ξ p with
  | Some (U, nil, _) => None
  | Some (U, x :: ip, T) => gm_submodule (gu_params U ++ T) (gu_mod U) x ip
  | None =>
      match uf (q_unit p) with
      | Some U => gm_module (gu_params U) None (gu_mod U) (q_chain p)
      | None => None
      end
  end.

Definition gc_module (Θ : gdeps) (Ξ : gstack) (p : qname) : option modres := gc_module_u (gds_lookup Θ) Ξ p.

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
Definition ind_lookup_u (uf : path -> option gunit) (Ξ : gstack) (p : qname) : option ind_decl :=
  match gc_module_u uf Ξ p with
  | Some (mr_body _ oD) => oD
  | _ => None
  end.

Definition ind_lookup (Θ : gdeps) (Ξ : gstack) (p : qname) : option ind_decl := ind_lookup_u (gds_lookup Θ) Ξ p.

Lemma ind_lookup_unfold : forall Θ Ξ p,
    ind_lookup Θ Ξ p = match gc_module Θ Ξ p with Some (mr_body _ oD) => oD | _ => None end.
Proof. reflexivity. Qed.

Lemma ind_lookup_module : forall Θ Ξ p D,
    ind_lookup Θ Ξ p = Some D -> exists T, gc_module Θ Ξ p = Some (mr_body T (Some D)).
Proof.
  intros * H; rewrite ind_lookup_unfold in H.
  destruct (gc_module Θ Ξ p) as [[T oD | U r] |]; try discriminate.
  subst; eauto.
Qed.

(** The module of an inductive type is no alias. *)
Lemma ind_lookup_not_alias : forall Θ Ξ p D U r,
    ind_lookup Θ Ξ p = Some D -> gc_module Θ Ξ p <> Some (mr_alias U r).
Proof. intros * H; destruct (ind_lookup_module _ _ _ _ H) as [T ->]; discriminate. Qed.

Lemma ind_lookup_body : forall Θ Ξ p T oD,
    gc_module Θ Ξ p = Some (mr_body T oD) -> ind_lookup Θ Ξ p = oD.
Proof. intros * H; rewrite ind_lookup_unfold, H; reflexivity. Qed.

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
  unfold gc_resolve, gc_resolve_u; intros * H.
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

Definition gc_entry_u (uf : path -> option gunit) (Ξ : gstack) (p : qname) : option gentry :=
  match gs_find Ξ p with
  | Some (U, ip) => gm_entry (gu_mod U) ip
  | None =>
      match uf (q_unit p) with
      | Some U => gm_entry (gu_mod U) (q_chain p)
      | None => None
      end
  end.

Definition gc_entry (Θ : gdeps) (Ξ : gstack) (p : qname) : option gentry := gc_entry_u (gds_lookup Θ) Ξ p.

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

Definition ind_alias_lookup_u (uf : path -> option gunit) (Ξ : gstack) (pq : qname) : option ind_alias_view :=
  match gs_find Ξ pq with
  | Some (U, ip) => gm_ind_target (gu_mod U) ip
  | None =>
      match uf (q_unit pq) with
      | Some U => gm_ind_target (gu_mod U) (q_chain pq)
      | None => None
      end
  end.

Definition ind_alias_lookup (Θ : gdeps) (Ξ : gstack) (pq : qname) : option ind_alias_view :=
  ind_alias_lookup_u (gds_lookup Θ) Ξ pq.

(** The inductive type a path names, its own or through an inductive
    alias, as a view: no telescope and no argument for the type itself. *)
Definition ind_target_u (uf : path -> option gunit) (Ξ : gstack) (pq : qname) : option ind_alias_view :=
  match ind_lookup_u uf Ξ pq with
  | Some _ => Some (nil, pq, nil)
  | None => ind_alias_lookup_u uf Ξ pq
  end.

Definition ind_target (Θ : gdeps) (Ξ : gstack) (pq : qname) : option ind_alias_view := ind_target_u (gds_lookup Θ) Ξ pq.

Lemma ind_target_unfold : forall Θ Ξ pq,
    ind_target Θ Ξ pq = match ind_lookup Θ Ξ pq with Some _ => Some (nil, pq, nil) | None => ind_alias_lookup Θ Ξ pq end.
Proof. reflexivity. Qed.

(** The lookups at a function agreeing with [gds_lookup Θ] are those at
    [Θ]. *)
Section UnitsOk.
  Variables (uf : path -> option gunit) (Θ : gdeps).
  Hypothesis Huf : forall fp, uf fp = gds_lookup Θ fp.

  Lemma gc_resolve_u_ok : forall Ξ p, gc_resolve_u uf Ξ p = gc_resolve Θ Ξ p.
  Proof. intros; unfold gc_resolve, gc_resolve_u; rewrite Huf; reflexivity. Qed.

  Lemma gc_module_u_ok : forall Ξ p, gc_module_u uf Ξ p = gc_module Θ Ξ p.
  Proof. intros; unfold gc_module, gc_module_u; rewrite Huf; reflexivity. Qed.

  Lemma ind_lookup_u_ok : forall Ξ p, ind_lookup_u uf Ξ p = ind_lookup Θ Ξ p.
  Proof. intros; unfold ind_lookup_u; rewrite gc_module_u_ok; reflexivity. Qed.

  Lemma gc_entry_u_ok : forall Ξ p, gc_entry_u uf Ξ p = gc_entry Θ Ξ p.
  Proof. intros; unfold gc_entry, gc_entry_u; rewrite Huf; reflexivity. Qed.

  Lemma ind_alias_lookup_u_ok : forall Ξ p, ind_alias_lookup_u uf Ξ p = ind_alias_lookup Θ Ξ p.
  Proof. intros; unfold ind_alias_lookup, ind_alias_lookup_u; rewrite Huf; reflexivity. Qed.
End UnitsOk.

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
  intros; unfold gc_entry, gc_entry_u, gc_resolve, gc_resolve_u.
  destruct (gs_find Ξ p) as [[U ip] |]; [ apply gm_entry_resolve_def |].
  destruct (gds_lookup Θ (q_unit p)); [ apply gm_entry_resolve_def | tauto ].
Qed.

Lemma gc_entry_ind : forall Θ Ξ p pv D Φ,
    gc_entry Θ Ξ p = Some (ge_ind pv D Φ) -> gc_resolve Θ Ξ p = None /\ ind_lookup Θ Ξ p = Some D.
Proof.
  intros * He; unfold gc_entry, gc_entry_u, gc_resolve, gc_resolve_u, ind_lookup, ind_lookup_u, gc_module, gc_module_u in *.
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
  intros * Hl; unfold gc_entry, gc_entry_u, ind_lookup, ind_lookup_u, gc_module, gc_module_u in *.
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
  intros; unfold ind_alias_lookup, ind_alias_lookup_u, gc_entry, gc_entry_u, gm_ind_target.
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
  intros * Hl; unfold ind_alias_lookup, ind_alias_lookup_u, gc_module, gc_module_u, gm_ind_target in *.
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
  unfold gc_entry, gc_entry_u, gc_resolve, gc_resolve_u in *.
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
  rewrite ind_lookup_unfold, (gc_sub_module _ _ _ _ _ _ Hs Hm); reflexivity.
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

Lemma gm_grows_module : forall Φ Φ', gm_grows Φ Φ' ->
    forall T oD ch, gm_module T oD Φ' ch = gm_module T oD Φ ch.
Proof. intros * Hg T oD [| x ip]; cbn; [ reflexivity | apply gm_grows_submodule; exact Hg ]. Qed.

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

(** A frame whose body grows. *)
Lemma gc_sub_frame : forall Θ Ξ mp Δ Φ1 Φ2,
    gm_sub Φ1 Φ2 ->
    gc_sub Θ ((mp, gu_body Δ Φ1) :: Ξ) Θ ((mp, gu_body Δ Φ2) :: Ξ).
Proof.
  intros * [HR [HM [HB HI]]]; repeat split.
  - intros p E0 Hr; unfold gc_resolve, gc_resolve_u in *; cbn in *.
    destruct (qname_strip mp p); [ apply HR; exact Hr | exact Hr ].
  - intros p r Hr; unfold gc_module, gc_module_u in *; cbn in *.
    destruct (qname_strip mp p) as [[| y ip] |]; [ discriminate | | exact Hr ].
    apply HM; exact Hr.
  - intros p T Φ Hr; unfold gc_body in *; cbn in *.
    destruct (qname_strip mp p) as [[| y ip] |]; [ discriminate | | eexists; split; [ exact Hr | constructor ] ].
    apply HB; exact Hr.
  - intros pq p Hr; unfold ind_alias_lookup, ind_alias_lookup_u in *; cbn in *.
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
  - intros p E Hr; unfold gc_resolve, gc_resolve_u in *; cbn.
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
  - intros p r Hr; unfold gc_module, gc_module_u in *; cbn.
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
  - intros pq p0 Hr; unfold ind_alias_lookup, ind_alias_lookup_u, gm_ind_target in *; cbn.
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

(** Filing a unit: what was read in its open frame is read in the filed
    unit. *)
Lemma gc_sub_file : forall Θ fp U,
    gds_lookup Θ fp = None ->
    gc_sub Θ ((q_abs fp nil, U) :: nil) ((fp, U) :: Θ) nil.
Proof.
  intros * Hn; repeat split.
  - intros p E0 Hr; unfold gc_resolve, gc_resolve_u in *; cbn [gs_find] in *.
    unfold qname_strip in Hr; cbn [q_unit q_chain strip_prefix] in Hr; cbn [gds_lookup].
    destruct (path_beq fp (q_unit p)) eqn:Hb.
    + apply path_beq_true in Hb; subst; rewrite path_beq_refl; exact Hr.
    + destruct (path_beq (q_unit p) fp) eqn:Hb'; [ apply path_beq_true in Hb'; subst; rewrite path_beq_refl in Hb; discriminate | exact Hr ].
  - intros p r Hr; unfold gc_module, gc_module_u in *; cbn [gs_find_tele] in *.
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
  - intros pq p0 Hr; unfold ind_alias_lookup, ind_alias_lookup_u in *; cbn [gs_find] in *.
    unfold qname_strip in Hr; cbn [q_unit q_chain strip_prefix] in Hr; cbn [gds_lookup].
    destruct (path_beq fp (q_unit pq)) eqn:Hb.
    + apply path_beq_true in Hb; subst; rewrite path_beq_refl; exact Hr.
    + destruct (path_beq (q_unit pq) fp) eqn:Hb'; [ apply path_beq_true in Hb'; subst; rewrite path_beq_refl in Hb; discriminate | exact Hr ].
Qed.

(** A filed unit resolves as its closed frame did. *)
Lemma gc_resolve_file : forall Θ fp U p,
    gc_resolve ((fp, U) :: Θ) nil p = gc_resolve Θ ((q_abs fp nil, U) :: nil) p.
Proof.
  intros; unfold gc_resolve, gc_resolve_u; cbn [gs_find gds_lookup]; unfold qname_strip; cbn [q_unit q_chain strip_prefix].
  destruct (path_beq fp (q_unit p)) eqn:Hb.
  - apply path_beq_true in Hb as ->; rewrite path_beq_refl; reflexivity.
  - destruct (path_beq (q_unit p) fp) eqn:Hb'; [| reflexivity ].
    apply path_beq_true in Hb'; rewrite Hb', path_beq_refl in Hb; discriminate.
Qed.

(** Filing more units under the same stack. *)
Lemma gc_sub_deps : forall Θ Θ' Ξ, Θ ⊑ Θ' -> gc_sub Θ Ξ Θ' Ξ.
Proof.
  intros * Hs; repeat split.
  - intros p E Hr; unfold gc_resolve, gc_resolve_u in *.
    destruct (gs_find Ξ p) as [[U ip] |]; [ exact Hr |].
    destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:E1; [| discriminate ].
    rewrite (Hs _ _ E1); exact Hr.
  - intros p r Hr; unfold gc_module, gc_module_u in *.
    destruct (gs_find_tele Ξ p) as [[[U ip] T] |]; [ exact Hr |].
    destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:E1; [| discriminate ].
    rewrite (Hs _ _ E1); exact Hr.
  - intros p T Φ Hr; exists Φ; split; [| constructor ]; unfold gc_body in *.
    destruct (gs_find_tele Ξ p) as [[[U ip] T'] |]; [ exact Hr |].
    destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:E1; [| discriminate ].
    rewrite (Hs _ _ E1); exact Hr.
  - intros pq p0 Hr; unfold ind_alias_lookup, ind_alias_lookup_u in *.
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

(** The items of an open up to and including the last one named [x], and
    that item. *)
Fixpoint items_upto (x : string) (its : list iitem) : option (list iitem * iitem) :=
  match its with
  | nil => None
  | it :: its' =>
      match items_upto x its' with
      | Some (its1, it1) => Some (it :: its1, it1)
      | None => if String.eqb x (iitem_name it) then Some (it :: nil, it) else None
      end
  end.

(** The chain an item of an open reads in its target, before [ch]. *)
Definition item_ch (it : iitem) (ch : list string) : list string :=
  match it with
  | (Some n, _, _) => n :: ch
  | (None, _, _) => ch
  end.

(** The body up to and including the entry named [x].  A name a local
    open declares is no entry, and shadows the entries before it. *)
Fixpoint gm_prefix_upto (Φ : gmod) (x : string) : option gmod :=
  match Φ with
  | gm_nil => None
  | gm_ext Φ' y _ => if String.eqb x y then Some Φ else gm_prefix_upto Φ' x
  | gm_open Φ' _ its => if existsb (String.eqb x) (map iitem_name its) then None else gm_prefix_upto Φ' x
  end.

(** The local open that declares [x]: the body before it, its target, the
    items up to and including [x]'s, and [x]'s item.  An entry named [x]
    after the open shadows it. *)
Fixpoint gm_item_upto (Φ : gmod) (x : string) : option (gmod * modexp * list iitem * iitem) :=
  match Φ with
  | gm_nil => None
  | gm_ext Φ' y _ => if String.eqb x y then None else gm_item_upto Φ' x
  | gm_open Φ' H its =>
      match items_upto x its with
      | Some (its1, it) => Some (Φ', H, its1, it)
      | None => gm_item_upto Φ' x
      end
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
    still takes the parameters [T]: the module of an inductive type, its own
    or through an inductive alias ([R = mr_indm T]), or any other
    ([R = mr_mod T]).  A module is applied to
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
(** A module that is no inductive type, with the parameters it still takes. *)
| mr_mod : ctx -> mres
(** The module of an inductive type, its own or through an inductive alias,
    with the parameters it still takes. *)
| mr_indm : ctx -> mres.

Definition mres_kind (R : mres) : mkind :=
  match R with
  | mr_term _ => mk_term
  | mr_mod _ | mr_indm _ => mk_mod
  end.

(** The parameters a module still takes. *)
Definition mres_tl (R : mres) : option ctx :=
  match R with
  | mr_mod T | mr_indm T => Some T
  | mr_term _ => None
  end.

(** A member type as a type: a module's arity is the [Π] over its parameters,
    into [⊤].  The semantics reads member types through it. *)
Definition mres_ty (R : mres) : typ :=
  match R with
  | mr_term A => A
  | mr_mod T | mr_indm T => ctx_pi T a_True
  end.

(** A member type generalized over a telescope it lives under. *)
Definition mres_gen (Δ : ctx) (R : mres) : mres :=
  match R with
  | mr_term A => mr_term (ctx_pi Δ A)
  | mr_mod T => mr_mod (T ++ Δ)
  | mr_indm T => mr_indm (T ++ Δ)
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
  | mr_indm T => option_map mr_indm (tele_inst T N)
  end.

Definition mres_wk (R : mres) (φ : wk) : mres :=
  match R with
  | mr_term A => mr_term A[φ]ʷ
  | mr_mod T => mr_mod (tele_wk T φ)
  | mr_indm T => mr_indm (tele_wk T φ)
  end.

Definition mres_sub (R : mres) (σ : sub) : mres :=
  match R with
  | mr_term A => mr_term A[σ]
  | mr_mod T => mr_mod (tele_sub T σ)
  | mr_indm T => mr_indm (tele_sub T σ)
  end.

(** A name an open declares is found by one lookup only. *)
Lemma items_upto_none : forall x its, existsb (String.eqb x) (map iitem_name its) = false -> items_upto x its = None.
Proof.
  induction its as [| it its IH]; intros H; cbn in *; [ reflexivity |].
  apply Bool.orb_false_iff in H as [H1 H2]; rewrite IH by assumption; rewrite H1; reflexivity.
Qed.

Lemma items_upto_some : forall x its r, items_upto x its = Some r -> existsb (String.eqb x) (map iitem_name its) = true.
Proof.
  induction its as [| it its IH]; intros r H; cbn in *; [ discriminate |].
  destruct (items_upto x its) eqn:E; [ rewrite (IH _ eq_refl); apply Bool.orb_true_r |].
  destruct (String.eqb x (iitem_name it)); [ reflexivity | discriminate ].
Qed.

Lemma gm_prefix_item_excl : forall Φ x Φ1, gm_prefix_upto Φ x = Some Φ1 -> gm_item_upto Φ x = None.
Proof.
  induction Φ as [| Φ IH y E | Φ IH H its]; intros * Hp; cbn in *; [ discriminate | |].
  - destruct (String.eqb x y); [ reflexivity | eauto ].
  - destruct (existsb _ _) eqn:Ee; [ discriminate |].
    rewrite (items_upto_none _ _ Ee); eauto.
Qed.

(** A body's entry named [x] and a name an open of the body declares for
    [x] exclude each other. *)
Ltac prefix_item_excl :=
  match goal with
  | Hp : gm_prefix_upto ?Φ ?x = Some _, Hi : gm_item_upto ?Φ ?x = Some _ |- _ =>
      rewrite (gm_prefix_item_excl _ _ _ Hp) in Hi; discriminate Hi
  end.

(** A path through an alias names no definition, and a path naming a module
    names no definition. *)
Lemma gm_submodule_resolve : forall Φ T x ip r,
    gm_submodule T Φ x ip = Some r -> gm_resolve Φ (x :: ip) = None.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H |- *; try discriminate; [| eapply IH; exact H ].
  destruct (String.eqb x y); [| eapply IH; exact H ].
  destruct E as [b pv A B | ? [Δ [Φ' | E']] | ? D Φ' | ? Δa pa Nsa]; try discriminate.
  - destruct ip as [| z ip']; [ reflexivity |].
    eapply IH; exact H.
  - destruct ip; reflexivity.
  - destruct ip as [| z ip']; [ reflexivity |].
    eapply IH; exact H.
  - destruct ip; reflexivity.
Qed.

Lemma gc_module_resolve : forall Θ Ξ p r,
    gc_module Θ Ξ p = Some r -> gc_resolve Θ Ξ p = None.
Proof.
  intros * H; unfold gc_module, gc_module_u, gc_resolve, gc_resolve_u in *; rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T] |]; cbn; [ discriminate | eapply gm_submodule_resolve; exact H |].
  destruct (gds_lookup Θ (q_unit p)); [| discriminate ].
  destruct (q_chain p) as [| x ip]; cbn in *; [ destruct (gu_mod g); reflexivity || apply gm_resolve_nil | eapply gm_submodule_resolve; exact H ].
Qed.

(** ** What an Open Generates

    [open E use (n)] declares [n] as a private definition equal to [E.n],
    [open E as y] declares [y] a private alias of [E], and, at the global
    level, an item naming an inductive type declares an inductive alias of
    it; a local open of one is rejected.  At the global level the generated
    entries are filed by the command ([rc_open]);
    in a local body the open stays, and every reader of the body reads it
    as its generated entries ([body_xp]).  The two share the generation
    relation [items_gen], which reads the kind of each member off its member
    type. *)

(** What an item declares, read in the context of the open. *)
Inductive igen : Set :=
(** [ig_def d pv A M]: the definition [d] of type [A] equal to [M] *)
| ig_def : string -> bool -> typ -> exp -> igen
(** [ig_alias d pv E]: the alias [d] of [E] *)
| ig_alias : string -> bool -> modexp -> igen
(** [ig_ind_alias d pv Δ p Ns]: the inductive alias [d], over [Δ], of the
    inductive type at the canonical path [p] at [Ns] *)
| ig_ind_alias : string -> bool -> list centry -> qname -> list exp -> igen.

(** The inductive type a member of a chain from a unit names, by its path
    ([ind_target] at the global level). *)
Definition ind_oracle : Type := qname -> option ind_alias_view.


(** A generated item as a body entry. *)
Definition ig_entry (g : igen) : (string * gentry)%type :=
  match g with
  | ig_def d pv A M => (d, ge_def true pv A (Some M))
  | ig_alias d pv E => (d, ge_mod pv (gu_mk nil (md_alias E)))
  | ig_ind_alias d pv Δ p Ns => (d, ge_ind_alias pv Δ p Ns)
  end.

Definition ig_name (g : igen) : string := fst (ig_entry g).

(** A generated item under a weakening and a substitution, as its entry
    is ([ig_entry_wk], [ig_entry_sub]): an inductive alias is closed. *)
Definition igen_wk (g : igen) (φ : wk) : igen :=
  match g with
  | ig_def d pv A M => ig_def d pv A[φ]ʷ M[φ]ʷ
  | ig_alias d pv E => ig_alias d pv (modexp_wk E φ)
  | ig_ind_alias _ _ _ _ _ => g
  end.

Definition igen_sub (g : igen) (σ : sub) : igen :=
  match g with
  | ig_def d pv A M => ig_def d pv A[σ] M[σ]
  | ig_alias d pv E => ig_alias d pv E[σ]ᵐ
  | ig_ind_alias _ _ _ _ _ => g
  end.

(** The generated entries appended to [Φ], in order.  All are read in the
    context of the open, so the [k]-th is weakened by the [k] before it. *)
Fixpoint gens_append (Φ : gmod) (k : nat) (gs : list igen) : gmod :=
  match gs with
  | nil => Φ
  | g :: gs' =>
      let '(d, E) := ig_entry g in
      gens_append (gm_ext Φ d (gentry_wk E (wk_shiftn k))) (S k) gs'
  end.

(** The first member named both by a private and by a public item. *)
Definition src_has (n : string) (pv : bool) (its : list iitem) : bool :=
  existsb (fun it => match it with
                     | (Some m, _, pv') => String.eqb n m && Bool.eqb pv pv'
                     | _ => false
                     end) its.

Definition both_dup (its : list iitem) : option string :=
  match find (fun it => match it with
                        | (Some n, _, pv) => src_has n (negb pv) its
                        | _ => false
                        end) its with
  | Some (Some n, _, _) => Some n
  | _ => None
  end.

(** The first name a list repeats. *)
Fixpoint name_dup (xs : list string) : option string :=
  match xs with
  | nil => None
  | x :: xs' => if existsb (String.eqb x) xs' then Some x else name_dup xs'
  end.

(** The open's own conditions on its items: no member both used and
    exported, and the declared names distinct. *)
Definition items_ok (its : list iitem) : Prop :=
  both_dup its = None /\ name_dup (List.map iitem_name its) = None.

(** A telescope of parameters has assumptions only: a module's arguments are
    terms.  A unit has members only under such parameters. *)
Definition tele_ass (Δ : ctx) : Prop := List.Forall (fun e => exists A, e = ce_ass A) Δ.

Lemma tele_ass_wk : forall Δ φ, tele_ass Δ -> tele_ass (tele_wk Δ φ).
Proof.
  induction 1 as [| e Δ [A ->] HΔ IH]; cbn; constructor; eauto.
Qed.

Lemma tele_ass_sub : forall Δ σ, tele_ass Δ -> tele_ass (tele_sub Δ σ).
Proof.
  induction 1 as [| e Δ [A ->] HΔ IH]; cbn; constructor; eauto.
Qed.

Inductive member_type (Θ : gdeps) (Ξ : gstack) : ctx -> modexp -> list string -> mres -> Prop :=
(** A definition reached from a unit, of its declared type. *)
| mt_unit_def : forall Γ fp ch b pv A B,
    ch <> nil ->
    gc_resolve Θ Ξ (q_abs fp ch) = Some (ge_def b pv A B) ->
    member_type Θ Ξ Γ (me_unit fp) ch (mr_term A)
(** A body module reached from a unit, taking the parameters it is filed
    with. *)
| mt_unit_mod : forall Γ fp ch T,
    gc_module Θ Ξ (q_abs fp ch) = Some (mr_body T None) ->
    member_type Θ Ξ Γ (me_unit fp) ch (mr_mod T)
(** The module of an inductive type reached from a unit, taking its
    uniform parameters. *)
| mt_unit_ind : forall Γ fp ch T D,
    gc_module Θ Ξ (q_abs fp ch) = Some (mr_body T (Some D)) ->
    member_type Θ Ξ Γ (me_unit fp) ch (mr_indm T)
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
| umt_def : forall Γ Δ Φ Φx Φ' x b pv A B,
    tele_ass Δ ->
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx ->
    gm_prefix_upto Φx x = Some (gm_ext Φ' x (ge_def b pv A B)) ->
    unit_member_type Θ Ξ Γ (gu_body Δ Φ) (x :: nil) (mr_term (ctx_pi (body_ctx Φ' ++ Δ) A))
(** A chain through a module of the body, read in it, generalized over the
    parameters and the body before it. *)
| umt_mod : forall Γ Δ Φ Φx Φ' y pm Uy ch R,
    (mres_kind R = mk_term -> ch <> nil) ->
    tele_ass Δ ->
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx ->
    gm_prefix_upto Φx y = Some (gm_ext Φ' y (ge_mod pm Uy)) ->
    unit_member_type Θ Ξ (body_ctx Φ' ++ Δ ++ Γ) Uy ch R ->
    unit_member_type Θ Ξ Γ (gu_body Δ Φ) (y :: ch) (mres_gen (body_ctx Φ' ++ Δ) R)
(** A chain of an alias, read in its target, generalized over the alias's
    parameters. *)
| umt_alias : forall Γ Δ E ch R,
    tele_ass Δ ->
    member_type Θ Ξ (Δ ++ Γ) E ch R ->
    unit_member_type Θ Ξ Γ (gu_mk Δ (md_alias E)) ch (mres_gen Δ R)
(** [body_xp Θ Ξ Γ Φ Φx]: the body [Φ], read in [Γ], is [Φx] with every
    local open replaced by the entries it generates ([items_gen]), in the
    context its own expanded prefix makes.  The entries themselves are not
    looked into. *)
with body_xp (Θ : gdeps) (Ξ : gstack) : ctx -> gmod -> gmod -> Prop :=
| bx_nil : forall Γ, body_xp Θ Ξ Γ gm_nil gm_nil
| bx_ext : forall Γ Φ Φx x E,
    body_xp Θ Ξ Γ Φ Φx ->
    body_xp Θ Ξ Γ (gm_ext Φ x E) (gm_ext Φx x E)
| bx_open : forall Γ Φ Φx H its R T gs,
    body_xp Θ Ξ Γ Φ Φx ->
    member_type Θ Ξ (body_ctx Φx ++ Γ) H nil R ->
    mres_tl R = Some T ->
    items_gen Θ Ξ None (body_ctx Φx ++ Γ) H its gs ->
    items_ok its ->
    body_xp Θ Ξ Γ (gm_open Φ H its) (gens_append Φx 0 gs)
(** [items_gen Θ Ξ io Γ H its gs]: what the items [its] of an open of [H]
    declare, all read in [Γ], by the kind of the member each names: a
    definition gives a definition of its member type, a module an alias;
    an item naming no member, the alias of [H] itself.  At the global level
    ([io = Some it]) an inductive type gives an inductive alias, read by its
    path ([it]), or an alias if the path names none.  A local open
    ([io = None]) has no case for an inductive type: a local open of one is
    rejected. *)
with items_gen (Θ : gdeps) (Ξ : gstack) : option ind_oracle -> ctx -> modexp -> list iitem -> list igen -> Prop :=
| ign_nil : forall io Γ H, items_gen Θ Ξ io Γ H nil nil
| ign_self : forall io Γ H d pv its gs,
    items_gen Θ Ξ io Γ H its gs ->
    items_gen Θ Ξ io Γ H ((None, d, pv) :: its) (ig_alias d pv H :: gs)
| ign_def : forall io Γ H n d pv A its gs,
    member_type Θ Ξ Γ H (n :: nil) (mr_term A) ->
    items_gen Θ Ξ io Γ H its gs ->
    items_gen Θ Ξ io Γ H ((Some n, d, pv) :: its) (ig_def d pv A (a_mem H n) :: gs)
| ign_mod : forall io Γ H n d pv T its gs,
    member_type Θ Ξ Γ H (n :: nil) (mr_mod T) ->
    items_gen Θ Ξ io Γ H its gs ->
    items_gen Θ Ξ io Γ H ((Some n, d, pv) :: its) (ig_alias d pv (me_mem H n) :: gs)
| ign_ind : forall it Γ H n d pv T mp Δ p Ns its gs,
    member_type Θ Ξ Γ H (n :: nil) (mr_indm T) ->
    mod_qname H = Some mp ->
    it (qname_app mp (n :: nil)) = Some (Δ, p, Ns) ->
    items_gen Θ Ξ (Some it) Γ H its gs ->
    items_gen Θ Ξ (Some it) Γ H ((Some n, d, pv) :: its) (ig_ind_alias d pv Δ p Ns :: gs)
| ign_ind_mod : forall it Γ H n d pv T its gs,
    member_type Θ Ξ Γ H (n :: nil) (mr_indm T) ->
    (forall mp, mod_qname H = Some mp -> it (qname_app mp (n :: nil)) = None) ->
    items_gen Θ Ξ (Some it) Γ H its gs ->
    items_gen Θ Ξ (Some it) Γ H ((Some n, d, pv) :: its) (ig_alias d pv (me_mem H n) :: gs).

Scheme member_type_mut_ind := Induction for member_type Sort Prop
with unit_member_type_mut_ind := Induction for unit_member_type Sort Prop
with body_xp_mut_ind := Induction for body_xp Sort Prop
with items_gen_mut_ind := Induction for items_gen Sort Prop.
Combined Scheme member_type_both_ind from member_type_mut_ind, unit_member_type_mut_ind, body_xp_mut_ind, items_gen_mut_ind.

#[export]
Hint Constructors member_type unit_member_type body_xp items_gen : mctt.

(** [open_gens Θ Ξ io Γ H its gs]: an open of [H] with items [its], in [Γ]:
    [H] is a module, and [gs] is what the items declare. *)
Definition open_gens (Θ : gdeps) (Ξ : gstack) (io : option ind_oracle) (Γ : ctx) (H : modexp) (its : list iitem) (gs : list igen) : Prop :=
  (exists R T, member_type Θ Ξ Γ H nil R /\ mres_tl R = Some T) /\ items_gen Θ Ξ io Γ H its gs /\ items_ok its.

(** A unit with its body expanded; an alias is its own. *)
Inductive unit_xp (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : gunit -> gunit -> Prop :=
| ux_body : forall Δ Φ Φx, body_xp Θ Ξ (Δ ++ Γ) Φ Φx -> unit_xp Θ Ξ Γ (gu_body Δ Φ) (gu_body Δ Φx)
| ux_alias : forall Δ E, unit_xp Θ Ξ Γ (gu_mk Δ (md_alias E)) (gu_mk Δ (md_alias E)).

#[export]
Hint Constructors unit_xp : mctt.

(** The targets of the local opens of [Φ], newest first, each with the
    context its expanded prefix makes, where [Φx] is the expansion of
    [Φ]. *)
Fixpoint gm_dropn (n : nat) (Φ : gmod) : gmod :=
  match n, Φ with
  | 0, _ => Φ
  | S n', gm_ext Φ' _ _ => gm_dropn n' Φ'
  | S _, _ => Φ
  end.

Fixpoint body_opens (Φ Φx : gmod) : list (ctx * modexp) :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ0 _ _ => body_opens Φ0 (gm_dropn 1 Φx)
  | gm_open Φ0 H its =>
      let Φ0x := gm_dropn (List.length its) Φx in
      (body_ctx Φ0x, H) :: body_opens Φ0 Φ0x
  end.

(** The number of local opens of a body. *)
Fixpoint gm_nopens (Φ : gmod) : nat :=
  match Φ with
  | gm_nil => 0
  | gm_ext Φ0 _ _ => gm_nopens Φ0
  | gm_open Φ0 _ _ => S (gm_nopens Φ0)
  end.

(** *** The Shape of an Expansion *)

Lemma items_gen_length : forall Θ Ξ io Γ H its gs, items_gen Θ Ξ io Γ H its gs -> List.length gs = List.length its.
Proof. induction 1; cbn; auto. Qed.

Lemma items_gen_names : forall Θ Ξ io Γ H its gs, items_gen Θ Ξ io Γ H its gs -> List.map ig_name gs = List.map iitem_name its.
Proof. induction 1; cbn; f_equal; auto. Qed.

(** The context an open's entries make, over the body before it. *)
Lemma gens_body_ctx_base : forall gs Φ k,
    body_ctx (gens_append Φ k gs) = body_ctx (gens_append gm_nil k gs) ++ body_ctx Φ.
Proof.
  induction gs as [| g gs IH]; intros; cbn [gens_append]; [ reflexivity |].
  destruct (ig_entry g) as [d E].
  rewrite IH, (IH (gm_ext gm_nil d _)), <- List.app_assoc.
  destruct E as [? ? ? [] | | |]; reflexivity.
Qed.

Lemma gens_append_binders : forall gs Φ k, gm_binders (gens_append Φ k gs) = List.length gs + gm_binders Φ.
Proof.
  induction gs as [| g gs IH]; intros; cbn; [ reflexivity |].
  destruct (ig_entry g) eqn:E; rewrite IH; cbn; lia.
Qed.

Lemma gm_dropn_add : forall a b Φ, gm_dropn (a + b) Φ = gm_dropn b (gm_dropn a Φ).
Proof.
  induction a as [| a IH]; intros b [| Φ x E | Φ H its]; cbn; auto; destruct b; reflexivity.
Qed.

Lemma gm_dropn_gens_append : forall gs Φ k, gm_dropn (List.length gs) (gens_append Φ k gs) = Φ.
Proof.
  induction gs as [| g gs IH]; intros; cbn [gens_append List.length]; [ destruct Φ; reflexivity |].
  destruct (ig_entry g) eqn:E.
  replace (S (List.length gs)) with (List.length gs + 1) by lia; rewrite gm_dropn_add, IH; reflexivity.
Qed.

Lemma body_xp_binders : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> gm_binders Φx = gm_binders Φ.
Proof.
  induction 1; cbn; auto.
  rewrite gens_append_binders; erewrite items_gen_length by eassumption; lia.
Qed.

Lemma gens_append_nopens : forall gs Φ k, gm_nopens (gens_append Φ k gs) = gm_nopens Φ.
Proof. induction gs as [| g gs IH]; intros; cbn; [ reflexivity |]; destruct (ig_entry g); rewrite IH; reflexivity. Qed.

(** An expansion has no open. *)
Lemma body_xp_nopens : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> gm_nopens Φx = 0.
Proof. induction 1; cbn; auto; rewrite gens_append_nopens; assumption. Qed.

Lemma body_opens_length : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> List.length (body_opens Φ Φx) = gm_nopens Φ.
Proof.
  induction 1; cbn; auto.
  erewrite <- items_gen_length by eassumption; rewrite gm_dropn_gens_append; f_equal; assumption.
Qed.

(** The opens of a body after an entry, or after an open, are those of the
    body before it, and that open. *)
Lemma body_opens_ext : forall Φ Φx x E y E', body_opens (gm_ext Φ x E) (gm_ext Φx y E') = body_opens Φ Φx.
Proof. reflexivity. Qed.

Lemma body_opens_open_len : forall Φ Φx H its gs, List.length gs = List.length its ->
    body_opens (gm_open Φ H its) (gens_append Φx 0 gs) = (body_ctx Φx, H) :: body_opens Φ Φx.
Proof. intros * Hl; cbn; rewrite <- Hl, gm_dropn_gens_append; reflexivity. Qed.

Lemma body_opens_open : forall Θ Ξ io Γ Φ Φx H its gs,
    items_gen Θ Ξ io Γ H its gs ->
    body_opens (gm_open Φ H its) (gens_append Φx 0 gs) = (body_ctx Φx, H) :: body_opens Φ Φx.
Proof.
  intros * Hg; cbn; erewrite <- items_gen_length by eassumption; rewrite gm_dropn_gens_append; reflexivity.
Qed.


(** The expansion of the body before the open that declares [x], read off
    the body [Φ] and its expansion [Φx]. *)
Fixpoint gm_item_xp (Φ Φx : gmod) (x : string) : gmod :=
  match Φ, Φx with
  | gm_ext Φ' _ _, gm_ext Φx' _ _ => gm_item_xp Φ' Φx' x
  | gm_open Φ' _ its, _ =>
      match items_upto x its with
      | Some _ => gm_dropn (List.length its) Φx
      | None => gm_item_xp Φ' (gm_dropn (List.length its) Φx) x
      end
  | _, _ => gm_nil
  end.

Lemma body_xp_item : forall Θ Ξ Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx ->
    forall x Φ0 H its1 it, gm_item_upto Φ x = Some (Φ0, H, its1, it) -> body_xp Θ Ξ Γ Φ0 (gm_item_xp Φ Φx x).
Proof.
  induction 1 as [Γ | Γ Φ Φx y E Hx IH | Γ Φ Φx H its R T gs Hx IH HR HT Hg Hok]; intros x Φ0 H0 its1 it Hi;
    cbn [gm_item_upto gm_item_xp] in *; try discriminate.
  - destruct (String.eqb x y); [ discriminate | eauto ].
  - rewrite <- (items_gen_length _ _ _ _ _ _ _ Hg), gm_dropn_gens_append.
    destruct (items_upto x its) as [[its1' it'] |]; [ injection Hi as <- <- <- <-; exact Hx | eauto ].
Qed.

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

(** The chain [ch] of [U] does not start with a name a local open of its
    body declares. *)
Definition unit_noitem (U : gunit) (ch : list string) : Prop :=
  match U, ch with
  | gu_mk _ (md_body Φ), x :: _ => gm_item_upto Φ x = None
  | _, _ => True
  end.

(** The δ-reduct of a chain of a unit read in [Γ]: the expansion of the
    entry the chain reaches; for a name a local open declares, the target's
    member it names, under the unit's parameters and the body before the
    open, as evaluation reads it. *)
Inductive unit_unfold (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : gunit -> list string -> exp -> Prop :=
| uu_entry : forall U Ux ch M,
    unit_xp Θ Ξ Γ U Ux ->
    unit_noitem U ch ->
    member_expansion Ux ch = Some M ->
    unit_unfold Θ Ξ Γ U ch M
| uu_item : forall Δ Φ x ch Φ0 H its1 it Φx0,
    gm_item_upto Φ x = Some (Φ0, H, its1, it) ->
    body_xp Θ Ξ (Δ ++ Γ) Φ0 Φx0 ->
    item_ch it ch <> nil ->
    unit_unfold Θ Ξ Γ (gu_body Δ Φ) (x :: ch) (ctx_fn (body_ctx Φx0 ++ Δ) (member_ref H (item_ch it ch))).

#[export]
Hint Constructors unit_unfold : mctt.

Inductive member_unfold_ch (Θ : gdeps) (Ξ : gstack) : ctx -> modexp -> list string -> exp -> Prop :=
| muc_unit_def : forall Γ fp ch b pv A B,
    gc_resolve Θ Ξ (q_abs fp ch) = Some (ge_def b pv A B) ->
    member_unfold_ch Θ Ξ Γ (me_unit fp) ch (member_ref (me_unit fp) ch)
| muc_unit_alias : forall Γ fp ch U r M,
    (forall b pv A B, gc_resolve Θ Ξ (q_abs fp ch) <> Some (ge_def b pv A B)) ->
    gc_module Θ Ξ (q_abs fp ch) = Some (mr_alias U r) ->
    member_expansion U r = Some M ->
    member_unfold_ch Θ Ξ Γ (me_unit fp) ch M
| muc_var : forall Γ x U ch M,
    ctx_find_mod Γ x = Some U ->
    unit_unfold Θ Ξ Γ U ch M ->
    member_unfold_ch Θ Ξ Γ (me_var x) ch M
| muc_lit : forall Γ U ch M,
    unit_unfold Θ Ξ Γ U ch M ->
    member_unfold_ch Θ Ξ Γ (me_lit U) ch M
| muc_mem : forall Γ H y ch M,
    member_unfold_ch Θ Ξ Γ H (y :: ch) M ->
    member_unfold_ch Θ Ξ Γ (me_mem H y) ch M
| muc_app : forall Γ H N ch M,
    member_unfold_ch Θ Ξ Γ H ch M ->
    member_unfold_ch Θ Ξ Γ (me_app H N) ch (a_app M N).

#[export]
Hint Constructors member_unfold_ch : mctt.

Definition member_unfold (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) (x : string) (M : exp) : Prop :=
  member_unfold_ch Θ Ξ Γ H (x :: nil) M.

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
