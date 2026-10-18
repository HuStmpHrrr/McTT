(** * Resolution and Members of Modules

    What a path names in the global context is a lookup ([gc_resolve],
    [gc_module], [gc_body]).  A module has no signature: what a module
    expression denotes, a description ([mdesc]), is computed from the
    module, when it is needed, by the relation [mdenote], one name at a
    time; the type and the δ-reduct of a member are read off its
    description.  The relations read syntax, context lookup and global
    resolution only, so they sit outside the mutual block of judgments,
    which uses them. *)

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
               | _ :: _, ge_mod _ (gu_mk _ (md_body sm Φ')) => gm_resolve Φ' ip'
               | _ :: _, ge_ind _ _ _ Φ' => gm_resolve Φ' ip'
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

    What a module path names: a body module with its full telescope and,
    for the module of an inductive type, the type's declaration, or an
    alias, stored closed over its full telescope.  A path does not go
    through an alias. *)
Inductive modres : Set :=
| mr_body : ctx -> option ind_decl -> modres
| mr_alias : gunit -> modres.

(** The submodule [x :: ip] of [Φ], whose enclosing telescope is [T]. *)
Fixpoint gm_submodule (T : ctx) (Φ : gmod) (x : string) (ip : list string) : option modres :=
  match Φ with
  | gm_nil => None
  | gm_open Φ0 _ _ => gm_submodule T Φ0 x ip
  | gm_ext Φ0 y E =>
      if String.eqb x y then
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
        | ge_ind _ _ D Φ' =>
            match ip with
            | nil => Some (mr_body (ind_uparams D) (Some D))
            | z :: ip' => gm_submodule (ind_uparams D) Φ' z ip'
            end
        (** As a module, an inductive alias is an alias, over its own
            telescope, of the module at its canonical path at its
            arguments. *)
        | ge_ind_alias _ Δ p Ns =>
            match ip with
            | nil => Some (mr_alias (gu_mk Δ (md_alias (me_apps (qname_mod p) Ns))))
            | _ :: _ => None
            end
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
        | ge_mod _ (gu_mk Δ (md_body sm Φ')) =>
            match ip with
            | nil => Some (Δ ++ T, Φ')
            | z :: ip' => gm_subbody (Δ ++ T) Φ' z ip'
            end
        | ge_ind _ _ D Φ' =>
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

(** The open frame at [p], with its full telescope: its own parameters, then
    those of the frames outside it. *)
Definition gc_frame (Ξ : gstack) (p : qname) : option (ctx * gmod) :=
  match gs_find_tele Ξ p with
  | Some (gu_mk Δ (md_body sm_closed Φ), nil, T0) => Some (Δ ++ T0, Φ)
  | _ => None
  end.

(** An open frame names no definition. *)
Lemma gc_frame_resolve : forall Θ Ξ p TΦ, gc_frame Ξ p = Some TΦ -> gc_resolve Θ Ξ p = None.
Proof.
  intros * H; unfold gc_frame, gc_resolve, gc_resolve_u in *; rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ0 | E]] [| x ip]] T0] |]; cbn in *; try discriminate; apply gm_resolve_nil.
Qed.

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
  destruct (gc_module Θ Ξ p) as [[T oD | U] |]; try discriminate.
  subst; eauto.
Qed.

(** The module of an inductive type is no alias. *)
Lemma ind_lookup_not_alias : forall Θ Ξ p D U,
    ind_lookup Θ Ξ p = Some D -> gc_module Θ Ξ p <> Some (mr_alias U).
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
               | _ :: _, ge_mod _ (gu_mk _ (md_body sm Φ')) => gm_entry Φ' ip'
               | _ :: _, ge_ind _ _ _ Φ' => gm_entry Φ' ip'
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
  | ge_ind pv _ _ _ => pv
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
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [? Φ' | E']] | pv' ? D Φ' | pv' Δa pa Nsa]; cbn; try tauto;
    try (split; intros; discriminate); exact (IH _ _ _ _ _ _).
Qed.

Lemma gm_entry_ind_resolve : forall Φ ip pv pq D Φ',
    gm_entry Φ ip = Some (ge_ind pv pq D Φ') -> gm_resolve Φ ip = None.
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] [| x ip] *; cbn; try discriminate; intros He; try (eapply IH; exact He).
  destruct (String.eqb x y); [| eapply IH; exact He ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [? Φ1 | E']] | pv' ? D' Φ1 | pv' Δ1 p1 Ns1]; cbn in He |- *; try discriminate;
    try reflexivity; eapply IH; exact He.
Qed.

Lemma gm_entry_submodule : forall Φ T x ip pv pq D Φ',
    gm_entry Φ (x :: ip) = Some (ge_ind pv pq D Φ') -> gm_submodule T Φ x ip = Some (mr_body (ind_uparams D) (Some D)).
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] T x ip *; cbn; try discriminate; intros He; try (eapply IH; exact He).
  destruct (String.eqb x y); [| eapply IH; exact He ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [? Φ1 | E']] | pv' ? D' Φ1 | pv' Δ1 p1 Ns1]; cbn in He |- *; try discriminate;
    try (injection He as -> -> ->; reflexivity); eapply IH; exact He.
Qed.

Lemma gm_submodule_entry : forall Φ T x ip T' D,
    gm_submodule T Φ x ip = Some (mr_body T' (Some D)) -> exists pv pq Φ', gm_entry Φ (x :: ip) = Some (ge_ind pv pq D Φ').
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] T x ip *; cbn; try discriminate; intros He; try (eapply IH; exact He).
  destruct (String.eqb x y); [| eapply IH; exact He ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [? Φ1 | E']] | pv' ? D' Φ1 | pv' Δ1 p1 Ns1]; cbn in He |- *; try discriminate;
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

Lemma gc_entry_ind : forall Θ Ξ p pv pq D Φ,
    gc_entry Θ Ξ p = Some (ge_ind pv pq D Φ) -> gc_resolve Θ Ξ p = None /\ ind_lookup Θ Ξ p = Some D.
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
    ind_lookup Θ Ξ p = Some D -> exists pv pq Φ, gc_entry Θ Ξ p = Some (ge_ind pv pq D Φ).
Proof.
  intros * Hl; unfold gc_entry, gc_entry_u, ind_lookup, ind_lookup_u, gc_module, gc_module_u in *.
  rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[U ip] T] |]; cbn in Hl |- *.
  - destruct ip as [| x ip]; [ discriminate |].
    destruct (gm_submodule _ _ _ _) as [[T' [D' |] | U'] |] eqn:E; try discriminate.
    injection Hl as ->; eapply gm_submodule_entry; exact E.
  - destruct (gds_lookup Θ (q_unit p)) as [U |]; [| discriminate ].
    destruct (q_chain p) as [| x ip]; cbn in Hl; [ discriminate |].
    destruct (gm_submodule _ _ _ _) as [[T' [D' |] | U'] |] eqn:E; try discriminate.
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
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [? Φ1 | E']] | pv' ? D' Φ1 | pv' Δ1 p1 Ns1]; cbn in He |- *;
    try reflexivity; try (eapply IH; eassumption).
  injection He as <-; exfalso; eapply Hn; reflexivity.
Qed.

Lemma gm_entry_ind_alias_submodule : forall Φ T x ip pv Δ p Ns,
    gm_entry Φ (x :: ip) = Some (ge_ind_alias pv Δ p Ns) ->
    gm_submodule T Φ x ip = Some (mr_alias (gu_mk Δ (md_alias (me_apps (qname_mod p) Ns)))).
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] T x ip *; cbn; try discriminate; intros He; try (eapply IH; exact He).
  destruct (String.eqb x y); [| eapply IH; exact He ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ0 [? Φ1 | E']] | pv' ? D' Φ1 | pv' Δ1 p1 Ns1]; cbn in He |- *; try discriminate;
    try (injection He as -> -> -> ->; reflexivity); eapply IH; exact He.
Qed.

Lemma ind_alias_lookup_module : forall Θ Ξ pq Δ p Ns,
    ind_alias_lookup Θ Ξ pq = Some (Δ, p, Ns) ->
    gc_module Θ Ξ pq = Some (mr_alias (gu_mk Δ (md_alias (me_apps (qname_mod p) Ns)))).
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
  intros * H; destruct (ind_lookup_entry _ _ _ _ H) as (? & ? & ? & He).
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
(** [entry_grows E1 E2]: the entry [E2] is [E1], but for the body of a
    module or of an inductive type, which may have grown. *)
Definition entry_grows (E1 E2 : gentry) : Prop :=
  match E1, E2 with
  | ge_mod pv (gu_mk Δ (md_body sm _)), ge_mod pv' (gu_mk Δ' (md_body sm' _)) => pv = pv' /\ Δ = Δ' /\ sm = sm'
  | ge_ind pv pq D _, ge_ind pv' pq' D' _ => pv = pv' /\ pq = pq' /\ D = D'
  | _, _ => E1 = E2
  end.

Lemma entry_grows_refl : forall E, entry_grows E E.
Proof. intros [| ? [? [? ?| ?]] | ? ? ? ? | ? ? ? ?]; cbn; auto. Qed.

Lemma entry_grows_trans : forall E1 E2 E3, entry_grows E1 E2 -> entry_grows E2 E3 -> entry_grows E1 E3.
Proof.
  intros [| ? [? [? ?| ?]] | ? ? ? ? | ? ? ? ?] [| ? [? [? ?| ?]] | ? ? ? ? | ? ? ? ?] [| ? [? [? ?| ?]] | ? ? ? ? | ? ? ? ?];
    cbn; intros; destruct_all; subst; try congruence; auto.
Qed.

(** [gc_sub Θ1 Ξ1 Θ2 Ξ2]: what [Θ1 ⍮ Ξ1] resolves, [Θ2 ⍮ Ξ2] resolves the
    same way, its bodies perhaps grown, its open frames perhaps closed. *)
Record gc_sub (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop := mk_gc_sub
  { gcs_resolve : forall p E, gc_resolve Θ1 Ξ1 p = Some E -> gc_resolve Θ2 Ξ2 p = Some E
  ; gcs_module : forall p r, gc_module Θ1 Ξ1 p = Some r -> gc_module Θ2 Ξ2 p = Some r
  ; gcs_body : forall p T Φ, gc_body Θ1 Ξ1 p = Some (T, Φ) ->
      exists Φ', gc_body Θ2 Ξ2 p = Some (T, Φ') /\ gm_grows Φ Φ'
  ; gcs_ind_alias : forall pq v, ind_alias_lookup Θ1 Ξ1 pq = Some v -> ind_alias_lookup Θ2 Ξ2 pq = Some v
  ; gcs_frame : forall p T Φ, gc_frame Ξ1 p = Some (T, Φ) ->
      exists Φ', gc_frame Ξ2 p = Some (T, Φ') \/
        (gc_body Θ2 Ξ2 p = Some (T, Φ') /\ gc_module Θ2 Ξ2 p = Some (mr_body T None))
  ; gcs_entry : forall p E, gc_entry Θ1 Ξ1 p = Some E -> exists E', gc_entry Θ2 Ξ2 p = Some E' /\ entry_grows E E' }.

Lemma gc_sub_resolve : forall Θ1 Ξ1 Θ2 Ξ2 p E,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_resolve Θ1 Ξ1 p = Some E -> gc_resolve Θ2 Ξ2 p = Some E.
Proof. intros * H; apply (gcs_resolve _ _ _ _ H). Qed.

Lemma gc_sub_module : forall Θ1 Ξ1 Θ2 Ξ2 p r,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_module Θ1 Ξ1 p = Some r -> gc_module Θ2 Ξ2 p = Some r.
Proof. intros * H; apply (gcs_module _ _ _ _ H). Qed.

Lemma gc_sub_body : forall Θ1 Ξ1 Θ2 Ξ2 p T Φ,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_body Θ1 Ξ1 p = Some (T, Φ) ->
    exists Φ', gc_body Θ2 Ξ2 p = Some (T, Φ') /\ gm_grows Φ Φ'.
Proof. intros * H; apply (gcs_body _ _ _ _ H). Qed.

Lemma gc_sub_ind_alias : forall Θ1 Ξ1 Θ2 Ξ2 pq v,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> ind_alias_lookup Θ1 Ξ1 pq = Some v -> ind_alias_lookup Θ2 Ξ2 pq = Some v.
Proof. intros * H; apply (gcs_ind_alias _ _ _ _ H). Qed.

(** An open frame is still one, or has been closed into a body module. *)
Lemma gc_sub_frame_loc : forall Θ1 Ξ1 Θ2 Ξ2 p T Φ,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_frame Ξ1 p = Some (T, Φ) ->
    exists Φ', gc_frame Ξ2 p = Some (T, Φ') \/
      (gc_body Θ2 Ξ2 p = Some (T, Φ') /\ gc_module Θ2 Ξ2 p = Some (mr_body T None)).
Proof. intros * H; apply (gcs_frame _ _ _ _ H). Qed.

(** What is stored at a path stays there, its bodies perhaps grown. *)
Lemma gc_sub_entry : forall Θ1 Ξ1 Θ2 Ξ2 p E,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_entry Θ1 Ξ1 p = Some E -> exists E', gc_entry Θ2 Ξ2 p = Some E' /\ entry_grows E E'.
Proof. intros * H; apply (gcs_entry _ _ _ _ H). Qed.

Lemma gc_sub_refl : forall Θ Ξ, gc_sub Θ Ξ Θ Ξ.
Proof. repeat split; intros * H; eauto using entry_grows_refl with mctt. Qed.

Lemma gc_sub_trans : forall Θ1 Ξ1 Θ2 Ξ2 Θ3 Ξ3,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_sub Θ2 Ξ2 Θ3 Ξ3 -> gc_sub Θ1 Ξ1 Θ3 Ξ3.
Proof.
  intros * [H12 M12 B12 I12 F12 E12] [H23 M23 B23 I23 F23 E23]; constructor; intros * H;
    [ apply H23, H12, H | apply M23, M12, H | | apply I23, I12, H | | ].
  - destruct (B12 _ _ _ H) as (Φ2 & H2 & G12); destruct (B23 _ _ _ H2) as (Φ3 & H3 & G23).
    exists Φ3; split; [ exact H3 | exact (gm_grows_trans _ _ _ G12 G23) ].
  - destruct (F12 _ _ _ H) as (Φ2 & [H2 | [H2 Hm2]]).
    + exact (F23 _ _ _ H2).
    + destruct (B23 _ _ _ H2) as (Φ3 & H3 & _); exists Φ3; right; split; [ exact H3 | exact (M23 _ _ Hm2) ].
  - destruct (E12 _ _ H) as (E2 & H2 & G12); destruct (E23 _ _ H2) as (E3 & H3 & G23).
    exists E3; split; [ exact H3 | exact (entry_grows_trans _ _ _ G12 G23) ].
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
Record gm_sub (Φ1 Φ2 : gmod) : Prop := mk_gm_sub
  { gms_resolve : forall ip E, gm_resolve Φ1 ip = Some E -> gm_resolve Φ2 ip = Some E
  ; gms_submodule : forall T z ip r, gm_submodule T Φ1 z ip = Some r -> gm_submodule T Φ2 z ip = Some r
  ; gms_subbody : forall T z ip T' Φ, gm_subbody T Φ1 z ip = Some (T', Φ) ->
      exists Φ', gm_subbody T Φ2 z ip = Some (T', Φ') /\ gm_grows Φ Φ'
  ; gms_ind_target : forall ip v, gm_ind_target Φ1 ip = Some v -> gm_ind_target Φ2 ip = Some v
  ; gms_entry : forall ip E, gm_entry Φ1 ip = Some E -> exists E', gm_entry Φ2 ip = Some E' /\ entry_grows E E' }.

Lemma gm_sub_refl : forall Φ, gm_sub Φ Φ.
Proof. repeat split; intros * H; eauto using entry_grows_refl with mctt. Qed.

Lemma gm_sub_trans : forall Φ1 Φ2 Φ3, gm_sub Φ1 Φ2 -> gm_sub Φ2 Φ3 -> gm_sub Φ1 Φ3.
Proof.
  intros * [H12 M12 B12 I12 E12] [H23 M23 B23 I23 E23]; constructor; intros * H;
    [ apply H23, H12, H | apply M23, M12, H | | apply I23, I12, H | ].
  - destruct (B12 _ _ _ _ _ H) as (Φ2' & H2 & G12); destruct (B23 _ _ _ _ _ H2) as (Φ3' & H3 & G23).
    exists Φ3'; split; [ exact H3 | exact (gm_grows_trans _ _ _ G12 G23) ].
  - destruct (E12 _ _ H) as (E2 & H2 & G12); destruct (E23 _ _ H2) as (E3 & H3 & G23).
    exists E3; split; [ exact H3 | exact (entry_grows_trans _ _ _ G12 G23) ].
Qed.

(** An entry of a fresh name. *)
Lemma gm_sub_ext_fresh : forall Φ x E, gm_fresh x Φ -> gm_sub Φ (Φ ⊳ x ↦ E).
Proof.
  intros * Hf; repeat split; intros * H.
  - exact (gm_resolve_ext_fresh _ _ _ _ _ Hf H).
  - exact (gm_submodule_ext_fresh _ _ _ _ _ _ _ Hf H).
  - eexists; split; [ exact (gm_subbody_ext_fresh _ _ _ _ _ _ _ Hf H) | constructor ].
  - exact (gm_ind_target_ext_fresh _ _ _ _ _ Hf H).
  - eexists; split; [ exact (gm_entry_ext_fresh _ _ _ _ _ Hf H) | apply entry_grows_refl ].
Qed.

(** A frame whose body grows. *)
Lemma gc_sub_frame : forall Θ Ξ mp Δ Φ1 Φ2,
    gm_sub Φ1 Φ2 ->
    gc_sub Θ ((mp, gu_body Δ Φ1) :: Ξ) Θ ((mp, gu_body Δ Φ2) :: Ξ).
Proof.
  intros * [HR HM HB HI HE]; constructor.
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
  - intros p T Φ Hr; unfold gc_frame in *; cbn in *.
    destruct (qname_strip mp p) as [[| y ip] |]; [ | discriminate | eexists; left; exact Hr ].
    injection Hr as <- <-; eexists; left; reflexivity.
  - intros p E0 Hr; unfold gc_entry, gc_entry_u in *; cbn in *.
    destruct (qname_strip mp p); [ apply HE; exact Hr | exists E0; split; [ exact Hr | apply entry_grows_refl ] ].
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
  - intros p T Φ Hr; exists Φ; left; unfold gc_frame in *; cbn.
    destruct (qname_strip mp p) as [ip |] eqn:Hs; [| exact Hr ].
    exfalso; unfold qname_strip in Hs.
    destruct (path_beq (q_unit mp) (q_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb.
    destruct Ξ as [| [mq V] Ξ']; cbn in Hf, Hr; [ discriminate |].
    destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
    pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
    unfold qname_strip in Hr; rewrite Hb, path_beq_refl, Hs' in Hr.
    destruct V as [? [[] ? | ?]]; cbn in Hr; discriminate.
  - intros p E Hr; exists E; split; [| apply entry_grows_refl ]; unfold gc_entry, gc_entry_u in *; cbn.
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
      destruct (gm_entry_head _ _ _ Hr) as (z & ip' & [= <- <-] & Hin); contradiction.
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
  - intros p T Φ Hr; exists Φ; right; unfold gc_frame, gc_body in *; cbn [gs_find_tele] in *.
    unfold qname_strip in Hr; cbn [q_unit q_chain strip_prefix] in Hr; cbn [gds_lookup].
    destruct (path_beq fp (q_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb; subst; rewrite path_beq_refl.
    destruct (q_chain p) as [| x ip] eqn:Hp; cbn in Hr; destruct U as [Δ [[] Φ0 | ?]]; cbn in Hr; try discriminate.
    injection Hr as <- <-; cbn; rewrite List.app_nil_r; split; [ reflexivity |].
    unfold gc_module, gc_module_u; cbn [gs_find_tele gds_lookup]; rewrite path_beq_refl, Hp; reflexivity.
  - intros p E0 Hr; exists E0; split; [| apply entry_grows_refl ]; unfold gc_entry, gc_entry_u in *; cbn [gs_find] in *.
    unfold qname_strip in Hr; cbn [q_unit q_chain strip_prefix] in Hr; cbn [gds_lookup].
    destruct (path_beq fp (q_unit p)) eqn:Hb.
    + apply path_beq_true in Hb; subst; rewrite path_beq_refl; exact Hr.
    + destruct (path_beq (q_unit p) fp) eqn:Hb'; [ apply path_beq_true in Hb'; subst; rewrite path_beq_refl in Hb; discriminate | exact Hr ].
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
  - intros p T Φ Hr; exists Φ; left; exact Hr.
  - intros p E Hr; exists E; split; [| apply entry_grows_refl ]; unfold gc_entry, gc_entry_u in *.
    destruct (gs_find Ξ p) as [[U ip] |]; [ exact Hr |].
    destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:E1; [| discriminate ].
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
  | ge_mod _ (gu_mk _ (md_body sm Φ)) => gm_transparent Φ
  | ge_mod _ (gu_mk _ (md_alias _)) => True
  | ge_ind _ _ _ Φ => gm_transparent Φ
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
  destruct ip' as [| z ip''], E as [b pv A B | pm [Δ' [? Φ' | E']] | pv ? D Φ' | pv Δa pa Nsa]; try discriminate.
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

Reserved Notation "Γ ∋ '#' x ≔ₘ U" (at level 70, x constr at level 0, U at level 69).

(** The unit of a module slot, weakened to the use site. *)
Inductive ctx_lookup_mod : nat -> gunit -> ctx -> Prop :=
(** The innermost slot *)
| mod_here : `(Γ ▹ₘ U ∋ #0 ≔ₘ gunit_wk U wk_shift)
(** A slot under one more entry *)
| mod_there : `(Γ ∋ #n ≔ₘ U -> e :: Γ ∋ #(S n) ≔ₘ gunit_wk U wk_shift)
where "Γ ∋ '#' x ≔ₘ U" := (ctx_lookup_mod x U Γ) : type_scope.

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

Lemma ctx_find_mod_sound : forall Γ x U, ctx_find_mod Γ x = Some U -> Γ ∋ #x ≔ₘ U.
Proof.
  induction Γ as [| e Γ IH]; intros [| y] U H; cbn in H; try discriminate.
  - destruct e; cbn in H; try discriminate; injection H as <-; constructor.
  - destruct (ctx_find_mod Γ y) eqn:E; cbn in H; [| discriminate ].
    injection H as <-; constructor; apply IH; assumption.
Qed.

Lemma ctx_find_mod_complete : forall Γ x U, Γ ∋ #x ≔ₘ U -> ctx_find_mod Γ x = Some U.
Proof. induction 1; cbn; [ reflexivity | rewrite IHctx_lookup_mod; reflexivity ]. Qed.

Lemma ctx_find_mod_spec : forall Γ x U, ctx_find_mod Γ x = Some U <-> Γ ∋ #x ≔ₘ U.
Proof. split; auto using ctx_find_mod_sound, ctx_find_mod_complete. Qed.

Lemma ctx_lookup_mod_functional : forall Γ x U U', Γ ∋ #x ≔ₘ U -> Γ ∋ #x ≔ₘ U' -> U = U'.
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

(** ** Descriptions

    A description says what a module expression denotes ([mdenote] below):
    a term of a type with its δ-reduct, if it has one ([ds_term]); an open
    (local) module, its parameters, its body as written and the body read
    through the entries its local opens generate ([ds_open Δ Φ Φx]: the
    module is the written body, its entries are read in the expansion); a closed module,
    stored at its canonical path [p] closed over its full telescope [T],
    given the arguments [Ns] and still abstracted over the parameters [Θ]
    that come from outside it ([ds_closed Θ p T Φ Ns]): the path is what
    identifies a filed module, two filed modules with equal bodies staying
    distinct; or the inductive type declared at [p], given the
    arguments [Ns] and still abstracted over [Θ] ([ds_ind Θ p Ns]).  The
    arguments are terms over the context extended by [Θ].  A description
    never contains an alias, and its entries are read where no local open
    is left.

    A lookup returns the whole description, and each rule takes the part it
    expects: the term part ([ds_ty], [ds_red]), the module part
    ([ds_mod]), or the inductive part, the description itself. *)

(** The sort of a member, as evaluation reads it. *)
Inductive mkind : Set :=
(** A definition *)
| mk_term
(** A module *)
| mk_mod.

Inductive mdesc : Set :=
| ds_term : typ -> option exp -> mdesc
| ds_open : ctx -> gmod -> gmod -> mdesc
| ds_closed : ctx -> qname -> ctx -> gmod -> list exp -> mdesc
| ds_ind : ctx -> qname -> list exp -> mdesc.

(** A description of a module, of either storage. *)
Definition ds_is_mod (R : mdesc) : Prop :=
  match R with
  | ds_open _ _ _ | ds_closed _ _ _ _ _ => True
  | _ => False
  end.

(** The description of a body module [Φ], read as [Φx] through the entries
    its local opens generate, by its storage: an open one is its parameters,
    its body and the expansion; a closed one, stored at the path [o] it is
    read at, is given no argument yet.  A closed body is a module only where
    it is stored: read anywhere else, it has no description. *)
Definition ds_body (o : option qname) (sm : smark) (Δ : ctx) (Φ Φx : gmod) : option mdesc :=
  match sm with
  | sm_open => Some (ds_open Δ Φ Φx)
  | sm_closed => option_map (fun pq => ds_closed nil pq Δ Φx nil) o
  end.

(** The term part: the type of a definition, or of the type former of an
    inductive type at its arguments, over the outside parameters. *)
Definition ds_ty (Θ : gdeps) (Ξ : gstack) (R : mdesc) : option typ :=
  match R with
  | ds_term A _ => Some A
  | ds_ind Θ' p Ns =>
      match ind_lookup Θ Ξ p with
      | Some D => Some (ctx_pi Θ' (ind_ty_at D Ns))
      | None => None
      end
  | _ => None
  end.

(** The δ-reduct of the term part: the body of a transparent definition, or
    the type former at its arguments; an axiom and an abstract definition
    have none. *)
Definition ds_red (R : mdesc) : option exp :=
  match R with
  | ds_term _ om => om
  | ds_ind Θ' p Ns => Some (ctx_fn Θ' (apps_exp (a_ind p) Ns))
  | _ => None
  end.

(** The module part: a module is its own, and an inductive type's is the
    stored module of its members, closed over its uniform parameters, at the
    same arguments. *)
Definition ds_mod (Θ : gdeps) (Ξ : gstack) (R : mdesc) : option mdesc :=
  match R with
  | ds_open _ _ _ | ds_closed _ _ _ _ _ => Some R
  | ds_ind Θ' p Ns =>
      match gc_body Θ Ξ p with
      | Some (T, Φ) => Some (ds_closed Θ' p T Φ Ns)
      | None => None
      end
  | ds_term _ _ => None
  end.

(** The telescope of parameters a module still takes: an open module's
    parameters; a closed one's outside parameters, then the rest of its
    telescope after the arguments given, instantiated by them. *)
Definition ds_tele (R : mdesc) : option ctx :=
  match R with
  | ds_open Δ _ _ => Some Δ
  | ds_closed Θ' _ T _ Ns =>
      if Nat.leb (List.length Ns) (List.length T)
      then Some (tele_sub (List.firstn (List.length T - List.length Ns) T) (sb_of_list Id Ns) ++ Θ')
      else None
  | _ => None
  end.

(** The telescope of the module part: what a module expression used as a
    module still takes. *)
Definition ds_mtele (Θ : gdeps) (Ξ : gstack) (R : mdesc) : option ctx :=
  match ds_mod Θ Ξ R with
  | Some Rm => ds_tele Rm
  | None => None
  end.

(** Abstraction: a description from inside an open body, the body's
    parameters and the entries before the member being [Θ'], re-expressed
    outside it.  [Π] and [λ] read a definition entry of [Θ'] as a [let]. *)
Definition ds_up (Θ' : ctx) (R : mdesc) : mdesc :=
  match R with
  | ds_term A om => ds_term (ctx_pi Θ' A) (option_map (ctx_fn Θ') om)
  | ds_open Δ Φ Φx => ds_open (Δ ++ Θ') Φ Φx
  | ds_closed Θ p T Φ Ns => ds_closed (Θ ++ Θ') p T Φ Ns
  | ds_ind Θ p Ns => ds_ind (Θ ++ Θ') p Ns
  end.

(** The [λ] a term is, looking through local definitions and local modules
    as [pi_view] does. *)
Fixpoint fn_view (M : exp) : option exp :=
  match M with
  | a_fn _ M' => Some M'
  | a_let (b_def _ N) T =>
      match fn_view T with
      | Some M' => Some M'[q (Id,,N)]
      | None => None
      end
  | a_let (b_mod U) T =>
      match fn_view T with
      | Some M' => Some M'[q (Id ,,ₘ me_lit U)]
      | None => None
      end
  | _ => None
  end.

(** The outermost assumption of a telescope, given outermost first: its
    type, the telescope inside it, and the substitution taking what lives
    under the whole telescope to what lives under the assumption and the
    rest, the definitions and modules outside it substituted away
    ([inl]); or, when there is no assumption, the substitution removing all
    of them ([inr]).  [tele_open] is its first two components. *)
Fixpoint tele_split (R : list centry) : ((typ * ctx * sub) + sub)%type :=
  match R with
  | nil => inr Id
  | ce_ass B :: R' => inl (B, rev R', Id)
  | ce_def B N :: R' =>
      match tele_split R' with
      | inl (B', T', τ) => inl (B'[Id,,N], tele_sub T' (q (Id,,N)), τ ⨟ sb_qn (S (List.length T')) (Id,,N))
      | inr τ => inr (τ ⨟ (Id,,N))
      end
  | ce_mod U :: R' =>
      match tele_split R' with
      | inl (B', T', τ) => inl (B'[Id ,,ₘ me_lit U], tele_sub T' (q (Id ,,ₘ me_lit U)), τ ⨟ sb_qn (S (List.length T')) (Id ,,ₘ me_lit U))
      | inr τ => inr (τ ⨟ (Id ,,ₘ me_lit U))
      end
  end.

(** Application "R at N": [N] is the next parameter.  A leading definition
    entry is substituted away first, in every form.  An open module
    substitutes [N] into its body; a closed one with outside parameters left
    fills the outermost of them, and with none records the argument, the
    stored module being read as it is; likewise for an inductive type. *)
Definition ds_at (R : mdesc) (N : exp) : option mdesc :=
  match R with
  | ds_term A om =>
      match pi_view A with
      | Some (_, C) =>
          match om with
          | None => Some (ds_term C[Id,,N] None)
          | Some M =>
              match fn_view M with
              | Some M' => Some (ds_term C[Id,,N] (Some M'[Id,,N]))
              | None => None
              end
          end
      | None => None
      end
  | ds_open Δ Φ Φx =>
      match tele_split (rev Δ) with
      | inl (_, Δ', τ) =>
          Some (ds_open (tele_sub Δ' (Id,,N)) (gmod_sub Φ (τ ⨟ sb_qn (List.length Δ') (Id,,N)))
                  (gmod_sub Φx (τ ⨟ sb_qn (List.length Δ') (Id,,N))))
      | inr _ => None
      end
  | ds_closed Θ p T Φ Ns =>
      match tele_split (rev Θ) with
      | inl (_, Θ', τ) =>
          Some (ds_closed (tele_sub Θ' (Id,,N)) p T Φ (List.map (fun M => M[τ ⨟ sb_qn (List.length Θ') (Id,,N)]) Ns))
      | inr τ => Some (ds_closed nil p T Φ (List.map (fun M => M[τ]) Ns ++ N :: nil))
      end
  | ds_ind Θ p Ns =>
      match tele_split (rev Θ) with
      | inl (_, Θ', τ) =>
          Some (ds_ind (tele_sub Θ' (Id,,N)) p (List.map (fun M => M[τ ⨟ sb_qn (List.length Θ') (Id,,N)]) Ns))
      | inr τ => Some (ds_ind nil p (List.map (fun M => M[τ]) Ns ++ N :: nil))
      end
  end.

(** "R at N₁ … Nₖ". *)
Fixpoint ds_ats (R : mdesc) (Ns : list exp) : option mdesc :=
  match Ns with
  | nil => Some R
  | N :: Ns' =>
      match ds_at R N with
      | Some R' => ds_ats R' Ns'
      | None => None
      end
  end.

(** How a member of a module description is read once its entry's
    description is known ([ds_read]). *)
Inductive reader : Set :=
| rd_open : ctx -> gmod -> reader
| rd_closed : ctx -> list exp -> exp -> reader.

(** A description under a substitution.  The parts of a description over
    the context are substituted; a closed module's stored unit is not, being
    closed. *)
Definition ds_sub (R : mdesc) (σ : sub) : mdesc :=
  match R with
  | ds_term A om => ds_term A[σ] (option_map (fun M => M[σ]) om)
  | ds_open Δ Φ Φx => ds_open (tele_sub Δ σ) (gmod_sub Φ (sb_qn (List.length Δ) σ)) (gmod_sub Φx (sb_qn (List.length Δ) σ))
  | ds_closed Θ p T Φ Ns => ds_closed (tele_sub Θ σ) p T Φ (List.map (fun M => M[sb_qn (List.length Θ) σ]) Ns)
  | ds_ind Θ p Ns => ds_ind (tele_sub Θ σ) p (List.map (fun M => M[sb_qn (List.length Θ) σ]) Ns)
  end.

(** The entries of a local body before a member, filled in: the
    substitution sending each of them to its value, a definition to its body
    and a module to its unit, the entries before it filled in.  An entry with
    no value (a definition without a body) cannot be filled in. *)
Fixpoint gm_fill (Φ : gmod) : option sub :=
  match Φ with
  | gm_nil => Some Id
  | gm_ext Φ' _ (ge_def _ _ _ (Some M)) => option_map (fun σ => σ ,, M[σ]) (gm_fill Φ')
  | gm_ext Φ' _ (ge_mod _ U) => option_map (fun σ => σ ,,ₘ me_lit U[σ]ᵘ) (gm_fill Φ')
  | _ => None
  end.

(** A term with no δ-reduct read as the name [M]: a filed axiom or abstract
    definition δ-reduces to its own name. *)
Definition ds_self (M : exp) (R : mdesc) : mdesc :=
  match R with
  | ds_term A None => ds_term A (Some M)
  | _ => R
  end.

(** A term of a closed body read at the outside parameters [Θ] and the
    arguments [Ns], as the name [M] there: with an outside parameter or an
    argument, one with no δ-reduct δ-reduces to its name; read bare, at
    neither, it is its own name already, and has no δ-reduct. *)
Definition ds_named (Θ : ctx) (Ns : list exp) (M : exp) (R : mdesc) : mdesc :=
  match Θ, Ns with
  | nil, nil => R
  | _, _ => ds_self M R
  end.
(** It is read through its lemmas, not unfolded. *)
Arguments ds_named : simpl never.

Lemma ds_named_nil : forall M R, ds_named nil nil M R = R.
Proof. reflexivity. Qed.

(** It reads only whether there are outside parameters or arguments. *)
Lemma ds_named_length : forall Θ Θ' Ns Ns', List.length Θ' = List.length Θ -> List.length Ns' = List.length Ns ->
    ds_named Θ' Ns' = ds_named Θ Ns.
Proof. intros [|] [|] [|] [|]; cbn; intros; first [ reflexivity | discriminate ]. Qed.

(** It is the description or its [ds_self]. *)
Lemma ds_named_cases : forall (P : mdesc -> Prop) Θ Ns M R, P R -> P (ds_self M R) -> P (ds_named Θ Ns M R).
Proof. intros P [|] [|] * H1 H2; exact H1 + exact H2. Qed.

(** What [ds_self] leaves as it is, it leaves as it is. *)
Lemma ds_named_fix : forall Θ Ns M R, ds_self M R = R -> ds_named Θ Ns M R = R.
Proof. intros [|] [|] * H; cbn; first [ reflexivity | exact H ]. Qed.

(** A term of no δ-reduct is read bare as itself, and otherwise as its
    name. *)
Lemma ds_named_term_none : forall Θ Ns M A,
    (ds_named Θ Ns M (ds_term A None) = ds_term A None /\ Θ = nil /\ Ns = nil) \/
    ds_named Θ Ns M (ds_term A None) = ds_term A (Some M).
Proof. intros [|] [|] *; cbn; auto. Qed.

(** Read at an outside parameter or an argument, it is [ds_self]. *)
Lemma ds_named_self : forall Θ Ns, (Θ <> nil \/ Ns <> nil) -> ds_named Θ Ns = ds_self.
Proof. intros [|] [|] H; cbn; try reflexivity; destruct H as [H | H]; contradiction H; reflexivity. Qed.

(** How an entry's description is read: one of an open body, the entries
    before it [Φ'] filled in, abstracted over the body's parameters [Δ]; one
    of a closed body, given the arguments recorded, a term with no δ-reduct
    being its name [M] there ([ds_named]), then abstracted over the outside
    parameters. *)
Definition ds_read (rd : reader) (R : mdesc) : option mdesc :=
  match rd with
  | rd_open Δ Φ' => option_map (fun σ => ds_up Δ (ds_sub R σ)) (gm_fill Φ')
  | rd_closed Θ Ns M => option_map (fun R1 => ds_up Θ (ds_named Θ Ns M R1)) (ds_ats R Ns)
  end.

(** A term read as a name is a term. *)
Lemma ds_named_term : forall Θ Ns M A om, exists om', ds_named Θ Ns M (ds_term A om) = ds_term A om'.
Proof. intros [|] [|] * ; destruct om; cbn; eexists; reflexivity. Qed.

Lemma ds_mod_named_term : forall Θs Ξs Δ Θ Ns M A om, ds_mod Θs Ξs (ds_up Δ (ds_named Θ Ns M (ds_term A om))) = None.
Proof. intros; destruct (ds_named_term Θ Ns M A om) as [om' ->]; reflexivity. Qed.

(** A stored closed entry read in a closed body of telescope [T]: as it is,
    except that a closed submodule, stored with its own parameters only,
    is read with its full telescope. *)
Definition ge_read (T : ctx) (E : gentry) : gentry :=
  match E with
  | ge_mod pv (gu_mk Δ (md_body sm_closed Φ)) => ge_mod pv (gu_mk (Δ ++ T) (md_body sm_closed Φ))
  | _ => E
  end.

(** [entry R y]: the entry [y] of the module described by [R], the context
    it is read in (over the module's context) and how its description is
    read; [None] for a term, or when [R] has no entry [y]. *)
Definition ds_entry (R : mdesc) (y : string) : option (ctx * gentry * reader) :=
  match R with
  | ds_open Δ _ Φx =>
      match gm_prefix_upto Φx y with
      | Some (gm_ext Φ' _ E) =>
          match E with
          (** Inductive types are global: an inductive entry of a local body
              is not read.  A transparent local definition is read; an
              abstract one, and one without a body, are not: they are used
              only inside the body, as its definitions there. *)
          | ge_ind _ _ _ _ | ge_ind_alias _ _ _ _ | ge_def _ _ _ None | ge_def false _ _ _ => None
          | _ => Some (body_ctx Φ' ++ Δ, E, rd_open Δ Φ')
          end
      | _ => None
      end
  | ds_closed Θ p T Φ Ns =>
      match gm_prefix_upto Φ y with
      | Some (gm_ext _ _ E) => Some (nil, ge_read T E, rd_closed Θ Ns (apps (a_mem (qname_mod p) y) Ns))
      | _ => None
      end
  | _ => None
  end.

(** The unit a module description stands for, [⌜R⌝]: a local body is its
    literal as written; a closed module with no outside parameter is the filed module at
    its arguments, and with outside parameters the alias of it over them.
    Anything else is no module, and stands for the empty body. *)
Definition ds_unit (R : mdesc) : modexp :=
  match R with
  | ds_open Δ Φ _ => me_lit (gu_mk Δ (md_body sm_open Φ))
  | ds_closed nil p _ _ Ns => me_apps (qname_mod p) Ns
  | ds_closed Θ' p _ _ Ns => me_lit (gu_mk Θ' (md_alias (me_apps (qname_mod p) Ns)))
  | _ => me_lit (gu_mk nil (md_body sm_open gm_nil))
  end.

(** The path an entry of a module is stored at: that of a closed module's
    entries; a local entry has none. *)
Definition ds_epath (R : mdesc) (y : string) : option qname :=
  match R with
  | ds_closed _ p _ _ _ => Some (qname_in p y)
  | _ => None
  end.

(** The stored unit a path [P] names when it is a loaded unit or an open
    frame, with its full telescope: an open frame's own parameters, then
    those of the frames outside it. *)
Definition gc_unit (Θ : gdeps) (Ξ : gstack) (H : modexp) : option (ctx * gmod) :=
  match mod_qname H with
  | Some mp =>
      match gs_find_tele Ξ mp with
      | Some (U, nil, T0) =>
          match U with
          | gu_mk Δ (md_body sm_closed Φ) => Some (Δ ++ T0, Φ)
          | _ => None
          end
      | Some _ => None
      | None =>
          match q_chain mp, gds_lookup Θ (q_unit mp) with
          | nil, Some (gu_mk Δ (md_body sm_closed Φ)) => Some (Δ, Φ)
          | _, _ => None
          end
      end
  | None => None
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
  destruct E as [b pv A B | ? [Δ [? Φ' | E']] | ? ? D Φ' | ? Δa pa Nsa]; try discriminate.
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

(** ** What a Module Expression Denotes

    [mdenote Θ Ξ Γ H R], [Γ ⊢ H ⇝ R]: one rule per former.  A loaded unit
    or an open frame denotes its stored closed unit, at its path, with no
    argument; a
    slot and a literal denote what their unit does; an application supplies
    the next parameter; and a selection finds the entry in the module part
    of the selected module's description and reads it there.

    [udenote Θ Ξ Γ o U R], [Γ ⊢ U ⇓ R]: what a module value denotes, [o]
    being the path it is stored at, if it is stored.  A body, read through
    the entries its local opens generate ([body_xp]), by its storage
    ([ds_body]): a closed body only at its path; an alias, the module part
    of what its target denotes, abstracted over the alias's parameters.
    Aliases are resolved here only.

    [edenote Θ Ξ Γ o E R], [Γ ⊢ E denotes R]: what an entry stored at [o]
    denotes, one rule per entry kind.  A definition is a term of its type, whose δ-reduct is
    its body when it is transparent; a module is what its unit denotes; an
    inductive type is its type former with no argument; an inductive alias,
    the type former at its arguments, over its telescope. *)
Inductive mdenote (Θ : gdeps) (Ξ : gstack) : ctx -> modexp -> mdesc -> Prop :=
| dn_unit : forall Γ H p T Φ,
    mod_qname H = Some p ->
    gc_unit Θ Ξ H = Some (T, Φ) ->
    mdenote Θ Ξ Γ H (ds_closed nil p T Φ nil)
| dn_slot : forall Γ x U R,
    Γ ∋ #x ≔ₘ U ->
    udenote Θ Ξ Γ None U R ->
    mdenote Θ Ξ Γ (me_var x) R
| dn_lit : forall Γ U R,
    udenote Θ Ξ Γ None U R ->
    mdenote Θ Ξ Γ (me_lit U) R
| dn_app : forall Γ H N R R',
    mdenote Θ Ξ Γ H R ->
    ds_at R N = Some R' ->
    mdenote Θ Ξ Γ (me_app H N) R'
| dn_mem : forall Γ H y R0 R0m Γy E rd R R',
    mdenote Θ Ξ Γ H R0 ->
    ds_mod Θ Ξ R0 = Some R0m ->
    ds_entry R0m y = Some (Γy, E, rd) ->
    edenote Θ Ξ (Γy ++ Γ) (ds_epath R0m y) E R ->
    ds_read rd R = Some R' ->
    mdenote Θ Ξ Γ (me_mem H y) R'
with udenote (Θ : gdeps) (Ξ : gstack) : ctx -> option qname -> gunit -> mdesc -> Prop :=
| un_body : forall Γ o Δ sm Φ Φx R,
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx ->
    ds_body o sm Δ Φ Φx = Some R ->
    udenote Θ Ξ Γ o (gu_mk Δ (md_body sm Φ)) R
| un_alias : forall Γ o Δ E R R',
    mdenote Θ Ξ (Δ ++ Γ) E R ->
    ds_mod Θ Ξ R = Some R' ->
    udenote Θ Ξ Γ o (gu_mk Δ (md_alias E)) (ds_up Δ R')
with edenote (Θ : gdeps) (Ξ : gstack) : ctx -> option qname -> gentry -> mdesc -> Prop :=
| en_def : forall Γ o b pv A oM,
    edenote Θ Ξ Γ o (ge_def b pv A oM) (ds_term A (if b then oM else None))
| en_mod : forall Γ o pv U R,
    udenote Θ Ξ Γ o U R ->
    edenote Θ Ξ Γ o (ge_mod pv U) R
| en_ind : forall Γ o pv p D Φ,
    edenote Θ Ξ Γ o (ge_ind pv p D Φ) (ds_ind nil p nil)
| en_ind_alias : forall Γ o pv Δ pq Ns,
    edenote Θ Ξ Γ o (ge_ind_alias pv Δ pq Ns) (ds_ind Δ pq Ns)
(** [body_xp Θ Ξ Γ Φ Φx]: the body [Φ], read in [Γ], is [Φx] with every
    local open replaced by the entries it generates ([items_gen]), in the
    context its own expanded prefix makes.  The entries themselves are not
    looked into. *)
with body_xp (Θ : gdeps) (Ξ : gstack) : ctx -> gmod -> gmod -> Prop :=
| bx_nil : forall Γ, body_xp Θ Ξ Γ gm_nil gm_nil
| bx_ext : forall Γ Φ Φx x E,
    body_xp Θ Ξ Γ Φ Φx ->
    body_xp Θ Ξ Γ (gm_ext Φ x E) (gm_ext Φx x E)
| bx_open : forall Γ Φ Φx H its R Rm gs,
    body_xp Θ Ξ Γ Φ Φx ->
    mdenote Θ Ξ (body_ctx Φx ++ Γ) H R ->
    ds_mod Θ Ξ R = Some Rm ->
    items_gen Θ Ξ false (body_ctx Φx ++ Γ) H its gs ->
    items_ok its ->
    body_xp Θ Ξ Γ (gm_open Φ H its) (gens_append Φx 0 gs)
(** [items_gen Θ Ξ g Γ H its gs]: what the items [its] of an open of [H]
    declare, all read in [Γ], by what the member each names denotes: a term
    gives a definition of its type, a module an alias, and, at the global
    level only ([g = true]), an inductive type an inductive alias of it over
    the parameters it is still abstracted over; an item naming no member,
    the alias of [H] itself.  A local open ([g = false]) has no case for an
    inductive type: a local open of one is rejected. *)
with items_gen (Θ : gdeps) (Ξ : gstack) : bool -> ctx -> modexp -> list iitem -> list igen -> Prop :=
| ign_nil : forall g Γ H, items_gen Θ Ξ g Γ H nil nil
| ign_self : forall g Γ H d pv its gs,
    items_gen Θ Ξ g Γ H its gs ->
    items_gen Θ Ξ g Γ H ((None, d, pv) :: its) (ig_alias d pv H :: gs)
| ign_def : forall g Γ H n d pv A om its gs,
    mdenote Θ Ξ Γ (me_mem H n) (ds_term A om) ->
    items_gen Θ Ξ g Γ H its gs ->
    items_gen Θ Ξ g Γ H ((Some n, d, pv) :: its) (ig_def d pv A (a_mem H n) :: gs)
| ign_mod : forall g Γ H n d pv R its gs,
    mdenote Θ Ξ Γ (me_mem H n) R ->
    ds_is_mod R ->
    items_gen Θ Ξ g Γ H its gs ->
    items_gen Θ Ξ g Γ H ((Some n, d, pv) :: its) (ig_alias d pv (me_mem H n) :: gs)
| ign_ind : forall Γ H n d pv Θ' p Ns its gs,
    mdenote Θ Ξ Γ (me_mem H n) (ds_ind Θ' p Ns) ->
    items_gen Θ Ξ true Γ H its gs ->
    items_gen Θ Ξ true Γ H ((Some n, d, pv) :: its) (ig_ind_alias d pv Θ' p Ns :: gs).

Scheme mdenote_mut_ind := Induction for mdenote Sort Prop
with udenote_mut_ind := Induction for udenote Sort Prop
with edenote_mut_ind := Induction for edenote Sort Prop
with body_xp_mut_ind := Induction for body_xp Sort Prop
with items_gen_mut_ind := Induction for items_gen Sort Prop.
Combined Scheme mdenote_all_ind from mdenote_mut_ind, udenote_mut_ind, edenote_mut_ind, body_xp_mut_ind, items_gen_mut_ind.

#[export]
Hint Constructors mdenote udenote edenote body_xp items_gen : mctt.


(** [open_gens Θ Ξ g Γ H its gs]: an open of [H] with items [its], in [Γ]:
    [H] is a module, and [gs] is what the items declare.  (Its witnesses
    are informative, so they have no projections.) *)
#[warnings="-cannot-define-projection"]
Record open_gens (Θ : gdeps) (Ξ : gstack) (g : bool) (Γ : ctx) (H : modexp) (its : list iitem) (gs : list igen) : Prop :=
  mk_open_gens
  { og_desc : mdesc
  ; og_mod : mdesc
  ; og_denote : mdenote Θ Ξ Γ H og_desc
  ; og_is_mod : ds_mod Θ Ξ og_desc = Some og_mod
  ; og_items : items_gen Θ Ξ g Γ H its gs
  ; og_ok : items_ok its }.

(** A unit with its body expanded; an alias is its own. *)
Inductive unit_xp (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : gunit -> gunit -> Prop :=
| ux_body : forall Δ sm Φ Φx, body_xp Θ Ξ (Δ ++ Γ) Φ Φx -> unit_xp Θ Ξ Γ (gu_mk Δ (md_body sm Φ)) (gu_mk Δ (md_body sm Φx))
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

(** The same, each target with the expanded prefix itself. *)
Fixpoint body_opens_at (Φ Φx : gmod) : list (gmod * modexp) :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ0 _ _ => body_opens_at Φ0 (gm_dropn 1 Φx)
  | gm_open Φ0 H its =>
      let Φ0x := gm_dropn (List.length its) Φx in
      (Φ0x, H) :: body_opens_at Φ0 Φ0x
  end.

Lemma body_opens_at_nth : forall Φ Φx k Φ0 H,
    nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) -> nth_error (body_opens Φ Φx) k = Some (body_ctx Φ0, H).
Proof.
  induction Φ as [| Φ IH x E | Φ IH H0 its]; intros * Hk; cbn in *; [ destruct k; discriminate | eauto |].
  destruct k as [| k]; cbn in *; [ injection Hk as <- <-; reflexivity | eauto ].
Qed.

Lemma body_opens_nth_at : forall Φ Φx k Ψ H,
    nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> exists Φ0, nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) /\ Ψ = body_ctx Φ0.
Proof.
  induction Φ as [| Φ IH x E | Φ IH H0 its]; intros * Hk; cbn in *; [ destruct k; discriminate | eauto |].
  destruct k as [| k]; cbn in *; [ injection Hk as <- <-; eauto | eauto ].
Qed.

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

Lemma body_opens_at_open_len : forall Φ Φx H its gs, List.length gs = List.length its ->
    body_opens_at (gm_open Φ H its) (gens_append Φx 0 gs) = (Φx, H) :: body_opens_at Φ Φx.
Proof. intros * Hl; cbn; rewrite <- Hl, gm_dropn_gens_append; reflexivity. Qed.

Lemma body_opens_at_open : forall Θ Ξ io Γ Φ Φx H its gs,
    items_gen Θ Ξ io Γ H its gs ->
    body_opens_at (gm_open Φ H its) (gens_append Φx 0 gs) = (Φx, H) :: body_opens_at Φ Φx.
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

(** ** The Module that Declares a Member

    [msite Θ Ξ H q]: the module expression [H], reached from a unit, is the
    module stored at [q], read step by step: a loaded unit or an open frame is
    stored at its own path, a body module (or the module of an inductive
    type) at its entry's path, an alias (or the module view of an inductive
    alias) where its target is, and arguments change nothing.  [mdecl Θ Ξ H y
    q pv]: the member [y] of [H] is the entry [y] of the module stored at
    [q], with privacy [pv]. *)

(** The body an entry stores, as a module. *)
Definition entry_is_body (E : gentry) : Prop :=
  match E with
  | ge_mod _ (gu_mk _ (md_body _ _)) | ge_ind _ _ _ _ => True
  | _ => False
  end.

(** The target of an alias entry, as a module: an inductive alias's module
    view. *)
Definition entry_alias (E : gentry) : option modexp :=
  match E with
  | ge_mod _ (gu_mk _ (md_alias E')) => Some E'
  | ge_ind_alias _ _ p Ns => Some (me_apps (qname_mod p) Ns)
  | _ => None
  end.

Inductive msite (Θ : gdeps) (Ξ : gstack) : modexp -> qname -> Prop :=
(** A loaded unit or an open frame *)
| ms_unit : forall H p T Φ,
    mod_qname H = Some p ->
    gc_unit Θ Ξ H = Some (T, Φ) ->
    msite Θ Ξ H p
(** A body module, at its entry *)
| ms_body : forall H pq z E,
    msite Θ Ξ H pq ->
    gc_entry Θ Ξ (qname_in pq z) = Some E ->
    entry_is_body E ->
    msite Θ Ξ (me_mem H z) (qname_in pq z)
(** An alias, where its target is *)
| ms_alias : forall H pq z E E' pq',
    msite Θ Ξ H pq ->
    gc_entry Θ Ξ (qname_in pq z) = Some E ->
    entry_alias E = Some E' ->
    msite Θ Ξ E' pq' ->
    msite Θ Ξ (me_mem H z) pq'
(** An application, where its module is *)
| ms_app : forall H N pq,
    msite Θ Ξ H pq ->
    msite Θ Ξ (me_app H N) pq.

Inductive mdecl (Θ : gdeps) (Ξ : gstack) (H : modexp) (y : string) : qname -> bool -> Prop :=
| mdl_intro : forall pq E,
    msite Θ Ξ H pq ->
    gc_entry Θ Ξ (qname_in pq y) = Some E ->
    mdecl Θ Ξ H y pq (ge_private E).

#[export]
Hint Constructors msite mdecl : mctt.

(** ** Stored Modules and Entries

    A unit is a filed module at arguments, [P N⃗] (a loaded unit, an open
    frame, or a body module stored at its path, given arguments), or a
    literal [(U)]. *)

(** Where a filed module is stored: an open frame, or a body module. *)
Definition gc_loc (Θ : gdeps) (Ξ : gstack) (p : qname) : option (ctx * gmod) :=
  match gc_frame Ξ p with
  | Some r => Some r
  | None => gc_body Θ Ξ p
  end.

Lemma gm_subbody_module : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') -> exists oD, gm_submodule T Φ x ip = Some (mr_body T' oD).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H) ].
  destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? D0 Φ0 | ? Δa pa Nsa]; try discriminate;
    destruct ip as [| z ip]; [ injection H as <- <-; eexists; reflexivity | exact (IH _ _ _ _ _ _ H) | injection H as <- <-; eexists; reflexivity | exact (IH _ _ _ _ _ _ H) ].
Qed.

Lemma gc_body_module : forall Θ Ξ p T Φ, gc_body Θ Ξ p = Some (T, Φ) -> exists oD, gc_module Θ Ξ p = Some (mr_body T oD).
Proof.
  intros * H; unfold gc_body, gc_module, gc_module_u in *.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T0] |]; [ discriminate | exact (gm_subbody_module _ _ _ _ _ _ H) |].
  destruct (gds_lookup Θ (q_unit p)) as [U |]; [| discriminate ].
  destruct (q_chain p) as [| x ip]; cbn in H |- *; [ injection H as <- <-; eexists; reflexivity | exact (gm_subbody_module _ _ _ _ _ _ H) ].
Qed.

(** What [gc_loc] finds is no alias. *)
Lemma gc_loc_not_alias : forall Θ Ξ p TΦ U, gc_loc Θ Ξ p = Some TΦ -> gc_module Θ Ξ p = Some (mr_alias U) -> False.
Proof.
  intros * Hl Hm; unfold gc_loc in Hl; destruct (gc_frame Ξ p) as [r |] eqn:Hf.
  - unfold gc_frame, gc_module, gc_module_u in *.
    destruct (gs_find_tele Ξ p) as [[[[Δ [[|] Φ0 | E]] [| x ip]] T0] |]; discriminate.
  - destruct TΦ as [T Φ]; destruct (gc_body_module _ _ _ _ _ Hl) as (oD & Hm'); rewrite Hm in Hm'; discriminate.
Qed.

(** What a stored term entry describes: a definition, a type former, or an
    inductive alias. *)
Definition entry_term (E : gentry) : option mdesc :=
  match E with
  | ge_def b _ A oM => Some (ds_term A (if b then oM else None))
  | ge_ind _ pq _ _ => Some (ds_ind nil pq nil)
  | ge_ind_alias _ Δ pq Ns => Some (ds_ind Δ pq Ns)
  | ge_mod _ _ => None
  end.

(** A stored alias entry as the alias unit it is, over its full telescope:
    an inductive alias as the alias of the module of its inductive type. *)
Definition entry_alias_unit (E : gentry) : option gunit :=
  match E with
  | ge_mod _ (gu_mk Ta (md_alias E')) => Some (gu_mk Ta (md_alias E'))
  | ge_ind_alias _ Δ pq Ns => Some (gu_mk Δ (md_alias (me_apps (qname_mod pq) Ns)))
  | _ => None
  end.

(** A unit of the context after a body's parameters, abstracted over them. *)
Definition gunit_abs (Δ : ctx) (U : gunit) : gunit :=
  match U with
  | gu_mk Δy D => gu_mk (Δy ++ Δ) D
  end.


