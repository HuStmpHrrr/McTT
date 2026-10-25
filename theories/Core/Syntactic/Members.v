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
From Mctt.Core.Syntactic.Inductives Require Import Group.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Generalizable All Variables.

(** ** Resolution in a Module

    A module is a sequence of entries, in declaration order: definitions and
    nested modules (see [gentry] in [Syntax]).  A definition with a module
    part ([ge_def_mod]) does not resolve here: as a module it is its alias
    ([gm_submodule]), and as a term evaluation reads it off its entry
    ([gc_entry]), as kinds see a module only.  A nested module of a filed
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
               | _ :: _, ge_ind _ _ _ _ Φ' => gm_resolve Φ' ip'
               | _ :: _, ge_record _ _ _ Φ' => gm_resolve Φ' ip'
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
    for the module of a member of a group of inductive types, the group's
    path, the member and the group's declaration ([indref]), or an alias,
    stored closed over its full telescope.  A path does not go through an
    alias. *)
Definition indref : Set := (qname * nat * ind_decl)%type.

(** The type of a value of the record [R] at [p], over the record's
    parameters: the type former at the parameters as variables.  It names
    the record, so it is a type only where the record is found: inside the
    record's own open frame ([fk_record]), or once the record is filed;
    never one frame out, where the record's module is declared. *)
Definition record_self (p : qname) (R : record_decl) : typ :=
  apps_exp (a_record p) (vars_from 0 (List.length (record_params R))).

(** The full telescope of the module of the record [R] at [p]: the
    record's parameters, then a value of the record at them, bound last.
    The generated field definitions and the with-area are over it, so a
    member is read at a value as [(R Ns e).f].  Its last binding is typed
    at the record's frame only ([record_self]; [frame_params]). *)
Definition record_mod_tele (p : qname) (R : record_decl) : ctx :=
  ce_ass (record_self p R) :: record_params R.

(** What a module path resolves to: a body, or an alias. *)
Inductive modres : Set :=
(** A module body, with its full telescope, and the member of a group of
    inductive types whose module it is, if it is one. *)
| mr_body : ctx -> option indref -> modres
(** A module alias, as the unit it stands for. *)
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
        | ge_ind _ pq k D Φ' =>
            match ip with
            | nil => Some (mr_body (ind_uparams D) (Some (pq, k, D)))
            | z :: ip' => gm_submodule (ind_uparams D) Φ' z ip'
            end
        (** As a module, a definition with a module part is its module
            part, an alias.  Its well-formedness makes the unit an alias,
            so the case of a body ([md_body]) is unreachable; it is none. *)
        | ge_def_mod _ _ _ (gu_mk Δ (md_alias E')) =>
            match ip with
            | nil => Some (mr_alias (gu_mk Δ (md_alias E')))
            | _ :: _ => None
            end
        | ge_def_mod _ _ _ (gu_mk _ (md_body _ _)) => None
        (** A record's module is a body module over the record's
            parameters and then a value of it ([record_mod_tele]). *)
        | ge_record _ p R Φ' =>
            match ip with
            | nil => Some (mr_body (record_mod_tele p R) None)
            | z :: ip' => gm_submodule (record_mod_tele p R) Φ' z ip'
            end
        | ge_def _ _ _ _ => None
        end
      else gm_submodule T Φ0 x ip
  end.

(** The module [ip] of a body of telescope [T], the body being the module
    of the member of a group [oD] if it is [Some]. *)
Definition gm_module (T : ctx) (oD : option indref) (Φ : gmod) (ip : list string) : option modres :=
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
        | ge_ind _ _ _ D Φ' =>
            match ip with
            | nil => Some (ind_uparams D, Φ')
            | z :: ip' => gm_subbody (ind_uparams D) Φ' z ip'
            end
        | ge_record _ p R Φ' =>
            match ip with
            | nil => Some (record_mod_tele p R, Φ')
            | z :: ip' => gm_subbody (record_mod_tele p R) Φ' z ip'
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
  | (mp, _, U) :: Ξ' =>
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
  | (mp, _, U) :: Ξ' =>
      match qname_strip mp p with
      | Some ip => Some (U, ip, gs_tele Ξ')
      | None => gs_find_tele Ξ' p
      end
  end.

(** The member of a group of inductive types whose module is the open
    frame at [p]: the kind of the frame [p] is read in ([gs_find_tele]),
    when [p] is that frame's own path.  The group's declaration is read off
    the frame while it is open, as the member is filed only when its frame
    closes. *)
Fixpoint gs_find_ind (Ξ : gstack) (p : qname) : option (qname * nat * ind_decl) :=
  match Ξ with
  | nil => None
  | (mp, K, _) :: Ξ' =>
      match qname_strip mp p with
      | Some nil =>
          match K with
          | fk_ind pq k D => Some (pq, k, D)
          | fk_module | fk_record _ => None
          end
      | Some (_ :: _) => None
      | None => gs_find_ind Ξ' p
      end
  end.

(** The record type whose module is the open frame at [p], when [p] is
    that frame's own path: its declaration is read off the frame while it
    is open, as the record is filed only when its frame closes. *)
Fixpoint gs_find_record (Ξ : gstack) (p : qname) : option record_decl :=
  match Ξ with
  | nil => None
  | (mp, K, _) :: Ξ' =>
      match qname_strip mp p with
      | Some nil =>
          match K with
          | fk_record R => Some R
          | fk_module | fk_ind _ _ _ => None
          end
      | Some (_ :: _) => None
      | None => gs_find_record Ξ' p
      end
  end.

Lemma gs_find_tele_find : forall Ξ p,
    gs_find Ξ p = option_map (fun r => let '(U, ip, _) := r in (U, ip)) (gs_find_tele Ξ p).
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros; cbn; [ reflexivity |].
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

(** Where a filed module is stored: an open frame, or a body module. *)
Definition gc_loc (Θ : gdeps) (Ξ : gstack) (p : qname) : option (ctx * gmod) :=
  match gc_frame Ξ p with
  | Some r => Some r
  | None => gc_body Θ Ξ p
  end.

(** The member of a group of inductive types whose module is at [p]: the
    group's path, the member, the group's declaration, read off the open
    frame at [p] while the member's module is open ([gs_find_ind]), and
    off the member's entry once it is filed ([gm_submodule]). *)
Definition ind_mlookup_u (uf : path -> option gunit) (Ξ : gstack) (p : qname) : option indref :=
  match gs_find_ind Ξ p with
  | Some r => Some r
  | None =>
      match gc_module_u uf Ξ p with
      | Some (mr_body _ oD) => oD
      | _ => None
      end
  end.

(** [ind_mlookup_u] at the filed units of [Θ]. *)
Definition ind_mlookup (Θ : gdeps) (Ξ : gstack) (p : qname) : option indref := ind_mlookup_u (gds_lookup Θ) Ξ p.

(** The declaration of the group at [p]: the group of the member whose
    module is at [p], the group's first member. *)
Definition ind_of_ref (r : option indref) : option ind_decl :=
  match r with
  | Some (_, 0, D) => Some D
  | _ => None
  end.

(** The group whose path is [p]: the group of the member at [p], when it
    is the group's first member. *)
Definition ind_lookup_u (uf : path -> option gunit) (Ξ : gstack) (p : qname) : option ind_decl :=
  ind_of_ref (ind_mlookup_u uf Ξ p).

Definition ind_lookup (Θ : gdeps) (Ξ : gstack) (p : qname) : option ind_decl := ind_lookup_u (gds_lookup Θ) Ξ p.

Lemma ind_mlookup_unfold : forall Θ Ξ p,
    ind_mlookup Θ Ξ p =
      match gs_find_ind Ξ p with
      | Some r => Some r
      | None => match gc_module Θ Ξ p with Some (mr_body _ oD) => oD | _ => None end
      end.
Proof. reflexivity. Qed.

Lemma ind_lookup_unfold : forall Θ Ξ p, ind_lookup Θ Ξ p = ind_of_ref (ind_mlookup Θ Ξ p).
Proof. reflexivity. Qed.

Lemma ind_of_ref_some : forall r D, ind_of_ref r = Some D -> exists pq, r = Some (pq, 0, D).
Proof. intros [[[pq [| k]] D'] |] D H; cbn in H; try discriminate; injection H as ->; eauto. Qed.

(** The open frame of a member's module is read at its own path. *)
Lemma gs_find_ind_tele : forall Ξ p r, gs_find_ind Ξ p = Some r -> exists U T, gs_find_tele Ξ p = Some (U, nil, T).
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros * H; cbn in H |- *; [ discriminate |].
  destruct (qname_strip mp p) as [[| ? ?] |]; [ eauto | discriminate | eauto ].
Qed.

(** [gs_find_ind] does not depend on the units of the frames. *)
Lemma gs_find_ind_unit : forall mp K U U' Ξ p, gs_find_ind ((mp, K, U) :: Ξ) p = gs_find_ind ((mp, K, U') :: Ξ) p.
Proof. reflexivity. Qed.

(** A module's frame is the module of no member. *)
Lemma gs_find_ind_module_frame : forall mp U Ξ p,
    gs_find_ind ((mp, fk_module, U) :: Ξ) p = match qname_strip mp p with Some _ => None | None => gs_find_ind Ξ p end.
Proof. intros; cbn; destruct (qname_strip mp p) as [[| ? ?] |]; reflexivity. Qed.

Lemma gs_find_ind_none : forall Ξ p, (forall U T, gs_find_tele Ξ p <> Some (U, nil, T)) -> gs_find_ind Ξ p = None.
Proof.
  intros * H; destruct (gs_find_ind Ξ p) as [r |] eqn:Hf; [| reflexivity ].
  destruct (gs_find_ind_tele _ _ _ Hf) as (U & T & HT); exfalso; exact (H _ _ HT).
Qed.

(** The open frame of a record's module is read at its own path. *)
Lemma gs_find_record_tele : forall Ξ p R, gs_find_record Ξ p = Some R -> exists U T, gs_find_tele Ξ p = Some (U, nil, T).
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros * H; cbn in H |- *; [ discriminate |].
  destruct (qname_strip mp p) as [[| ? ?] |]; [ eauto | discriminate | eauto ].
Qed.

(** [gs_find_record] does not depend on the units of the frames. *)
Lemma gs_find_record_unit : forall mp K U U' Ξ p, gs_find_record ((mp, K, U) :: Ξ) p = gs_find_record ((mp, K, U') :: Ξ) p.
Proof. reflexivity. Qed.

(** A frame is the module of a member or of a record type, not both. *)
Lemma gs_find_ind_not_record : forall Ξ p r, gs_find_ind Ξ p = Some r -> gs_find_record Ξ p = None.
Proof.
  induction Ξ as [| [[mp K] U] Ξ IH]; intros * H; cbn in H |- *; [ discriminate |].
  destruct (qname_strip mp p) as [[| ? ?] |]; [ destruct K; congruence | reflexivity | eauto ].
Qed.

Lemma gs_find_record_none : forall Ξ p, (forall U T, gs_find_tele Ξ p <> Some (U, nil, T)) -> gs_find_record Ξ p = None.
Proof.
  intros * H; destruct (gs_find_record Ξ p) as [R |] eqn:Hf; [| reflexivity ].
  destruct (gs_find_record_tele _ _ _ Hf) as (U & T & HT); exfalso; exact (H _ _ HT).
Qed.

(** An open frame is no module yet. *)
Lemma gc_module_frame_own : forall Θ Ξ p U T, gs_find_tele Ξ p = Some (U, nil, T) -> gc_module Θ Ξ p = None.
Proof. intros * H; unfold gc_module, gc_module_u; rewrite H; reflexivity. Qed.

Lemma gs_find_ind_module : forall Θ Ξ p r, gs_find_ind Ξ p = Some r -> gc_module Θ Ξ p = None.
Proof. intros * H; destruct (gs_find_ind_tele _ _ _ H) as (U & T & HT); exact (gc_module_frame_own _ _ _ _ _ HT). Qed.

(** Where the member a path names is read: its filed module, or its open
    frame. *)
Lemma ind_mlookup_module : forall Θ Ξ p r,
    ind_mlookup Θ Ξ p = Some r -> (exists T, gc_module Θ Ξ p = Some (mr_body T (Some r))) \/ gs_find_ind Ξ p = Some r.
Proof.
  intros * H; rewrite ind_mlookup_unfold in H.
  destruct (gs_find_ind Ξ p) as [r' |]; [ right; exact H | left ].
  destruct (gc_module Θ Ξ p) as [[T oD | U] |]; try discriminate.
  subst; eauto.
Qed.

Lemma ind_lookup_mlookup : forall Θ Ξ p D, ind_lookup Θ Ξ p = Some D -> exists pq, ind_mlookup Θ Ξ p = Some (pq, 0, D).
Proof. intros * H; rewrite ind_lookup_unfold in H; exact (ind_of_ref_some _ _ H). Qed.

Lemma ind_lookup_module : forall Θ Ξ p D,
    ind_lookup Θ Ξ p = Some D ->
    exists pq, (exists T, gc_module Θ Ξ p = Some (mr_body T (Some (pq, 0, D)))) \/ gs_find_ind Ξ p = Some (pq, 0, D).
Proof.
  intros * H; destruct (ind_lookup_mlookup _ _ _ _ H) as [pq Hm].
  exists pq; exact (ind_mlookup_module _ _ _ _ Hm).
Qed.

(** The module of an inductive type is no alias. *)
Lemma ind_mlookup_not_alias : forall Θ Ξ p r U,
    ind_mlookup Θ Ξ p = Some r -> gc_module Θ Ξ p <> Some (mr_alias U).
Proof.
  intros * H; destruct (ind_mlookup_module _ _ _ _ H) as [[T ->] | Hf]; [ discriminate |].
  rewrite (gs_find_ind_module Θ _ _ _ Hf); discriminate.
Qed.

Lemma ind_lookup_not_alias : forall Θ Ξ p D U,
    ind_lookup Θ Ξ p = Some D -> gc_module Θ Ξ p <> Some (mr_alias U).
Proof. intros * H; destruct (ind_lookup_mlookup _ _ _ _ H) as [pq Hm]; exact (ind_mlookup_not_alias _ _ _ _ _ Hm). Qed.

Lemma ind_mlookup_body : forall Θ Ξ p T oD,
    gc_module Θ Ξ p = Some (mr_body T oD) -> ind_mlookup Θ Ξ p = oD.
Proof.
  intros * H; rewrite ind_mlookup_unfold, H.
  destruct (gs_find_ind Ξ p) as [r |] eqn:Hf; [| reflexivity ].
  rewrite (gs_find_ind_module Θ _ _ _ Hf) in H; discriminate.
Qed.

Lemma ind_lookup_body : forall Θ Ξ p T oD,
    gc_module Θ Ξ p = Some (mr_body T oD) -> ind_lookup Θ Ξ p = ind_of_ref oD.
Proof. intros * H; rewrite ind_lookup_unfold, (ind_mlookup_body _ _ _ _ _ H); reflexivity. Qed.

(** The path of the module of the declared member [k] of [D]. *)
Definition ind_mpath (D : ind_decl) (k : nat) : option qname :=
  match ind_member D k with
  | Some M => im_path M
  | None => None
  end.

Lemma gs_find_unit : forall Ξ p U ip, gs_find Ξ p = Some (U, ip) ->
    exists mp K, List.In (mp, K, U) Ξ /\ q_unit mp = q_unit p.
Proof.
  induction Ξ as [| [[mp K] V] Ξ IH]; intros * H; cbn in H; [ discriminate |].
  unfold qname_strip in H.
  destruct (path_beq (q_unit mp) (q_unit p)) eqn:Hb.
  - destruct (strip_prefix (q_chain mp) (q_chain p)).
    + injection H as <- <-; exists mp, K; cbn; split; [ auto | apply path_beq_true; assumption ].
    + destruct (IH _ _ _ H) as (mq & K' & ? & ?); exists mq, K'; cbn; auto.
  - destruct (IH _ _ _ H) as (mq & K' & ? & ?); exists mq, K'; cbn; auto.
Qed.

(** Where a resolved entry comes from: a frame of the stack or a filed unit. *)
Lemma gc_resolve_inv : forall Θ Ξ p E,
    gc_resolve Θ Ξ p = Some E ->
    (exists mp K U ip, List.In (mp, K, U) Ξ /\ gm_resolve (gu_mod U) ip = Some E) \/
    (exists fp U, gds_lookup Θ fp = Some U /\ gm_resolve (gu_mod U) (q_chain p) = Some E).
Proof.
  unfold gc_resolve, gc_resolve_u; intros * H.
  destruct (gs_find Ξ p) as [[U ip] |] eqn:Hf.
  - left; destruct (gs_find_unit _ _ _ _ Hf) as (mp & K & Hin & _).
    exists mp, K, U, ip; split; assumption.
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
               | _ :: _, ge_ind _ _ _ _ Φ' => gm_entry Φ' ip'
               | _ :: _, ge_record _ _ _ Φ' => gm_entry Φ' ip'
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

(** The term part a global path is selected as, stored closed: the body of
    a transparent definition it resolves to, or the term of the definition
    with a module part stored there.  Resolution reads a definition with a
    module part as a module only (its alias), so its term is read off the
    entry. *)
Definition gc_term (Θ : gdeps) (Ξ : gstack) (p : qname) : option exp :=
  match gc_resolve Θ Ξ p with
  | Some (ge_def true _ _ (Some M)) => Some M
  | _ =>
      match gc_entry Θ Ξ p with
      | Some (ge_def_mod _ _ M _) => Some M
      | _ => None
      end
  end.

(** The record type at [p]: while its module's frame is open, the
    declaration the frame carries ([gs_find_record]); after, the
    declaration of the record entry the path names. *)
Definition record_lookup (Θ : gdeps) (Ξ : gstack) (p : qname) : option record_decl :=
  match gs_find_record Ξ p with
  | Some R => Some R
  | None =>
      match gc_entry Θ Ξ p with
      | Some (ge_record _ _ R _) => Some R
      | _ => None
      end
  end.

(** A global path naming a member with a term part and a module part: an
    inductive type or a record type, stored or with its module's frame
    open, or a definition with a module part. *)
Definition dm_path (Θ : gdeps) (Ξ : gstack) (p : qname) : Prop :=
  (exists r, ind_mlookup Θ Ξ p = Some r) \/
  (exists R, record_lookup Θ Ξ p = Some R) \/
  (exists pv A M U, gc_entry Θ Ξ p = Some (ge_def_mod pv A M U)).

(** The type of the type former of the record [R] applied to [Us], its
    outermost parameters: the [Π] over the others of its sort, at [Us]. *)
Definition record_ty_at (R : record_decl) (Us : list exp) : typ :=
  exp_sub (ctx_pi (List.firstn (List.length (record_params R) - List.length Us) (record_params R)) (record_sort R))
    (sb_of_list sb_id Us).

(** Whether an entry is private. *)
Definition ge_private (E : gentry) : bool :=
  match E with
  | ge_def _ pv _ _ => pv
  | ge_mod pv _ => pv
  | ge_ind pv _ _ _ _ => pv
  | ge_def_mod pv _ _ _ => pv
  | ge_record pv _ _ _ => pv
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

(** The lookups at a function agreeing with [gds_lookup Θ] are those at
    [Θ]. *)
Section UnitsOk.
  Variables (uf : path -> option gunit) (Θ : gdeps).
  Hypothesis Huf : forall fp, uf fp = gds_lookup Θ fp.

  Lemma gc_resolve_u_ok : forall Ξ p, gc_resolve_u uf Ξ p = gc_resolve Θ Ξ p.
  Proof. intros; unfold gc_resolve, gc_resolve_u; rewrite Huf; reflexivity. Qed.

  Lemma gc_module_u_ok : forall Ξ p, gc_module_u uf Ξ p = gc_module Θ Ξ p.
  Proof. intros; unfold gc_module, gc_module_u; rewrite Huf; reflexivity. Qed.

  Lemma ind_mlookup_u_ok : forall Ξ p, ind_mlookup_u uf Ξ p = ind_mlookup Θ Ξ p.
  Proof. intros; unfold ind_mlookup_u; rewrite gc_module_u_ok; reflexivity. Qed.

  Lemma ind_lookup_u_ok : forall Ξ p, ind_lookup_u uf Ξ p = ind_lookup Θ Ξ p.
  Proof. intros; unfold ind_lookup_u; rewrite ind_mlookup_u_ok; reflexivity. Qed.

  Lemma gc_entry_u_ok : forall Ξ p, gc_entry_u uf Ξ p = gc_entry Θ Ξ p.
  Proof. intros; unfold gc_entry, gc_entry_u; rewrite Huf; reflexivity. Qed.
End UnitsOk.

(** ** One Lookup for a Global

    The entry a path names ([gc_entry]) tells a global from the module of
    an inductive type in one pass, which [gc_resolve] and [ind_lookup] would
    each take. *)
Lemma gm_entry_resolve_def : forall Φ ip b pv A B,
    gm_entry Φ ip = Some (ge_def b pv A B) <-> gm_resolve Φ ip = Some (ge_def b pv A B).
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] [| x ip] *; cbn; try tauto; try exact (IH _ _ _ _ _ _).
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _) ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [? Φ' | E']] | pv' ? ? D Φ' | pv' A1 M1 U1 | pv' Rr Φ']; cbn; try tauto;
    try (split; intros; discriminate); exact (IH _ _ _ _ _ _).
Qed.

Lemma gm_entry_ind_resolve : forall Φ ip pv pq k D Φ',
    gm_entry Φ ip = Some (ge_ind pv pq k D Φ') -> gm_resolve Φ ip = None.
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] [| x ip] *; cbn; try discriminate; intros He; try (eapply IH; exact He).
  destruct (String.eqb x y); [| eapply IH; exact He ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [? Φ1 | E']] | pv' ? ? D' Φ1 | pv' A1 M1 [Δ1 [? Φ2 | E2]] | pv' Rr Φ1]; cbn in He |- *;
    try discriminate; try reflexivity; eapply IH; exact He.
Qed.

Lemma gm_entry_submodule : forall Φ T x ip pv pq k D Φ',
    gm_entry Φ (x :: ip) = Some (ge_ind pv pq k D Φ') ->
    gm_submodule T Φ x ip = Some (mr_body (ind_uparams D) (Some (pq, k, D))).
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] T x ip *; cbn; try discriminate; intros He; try (eapply IH; exact He).
  destruct (String.eqb x y); [| eapply IH; exact He ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [? Φ1 | E']] | pv' ? ? D' Φ1 | pv' A1 M1 [Δ1 [? Φ2 | E2]] | pv' Rr Φ1]; cbn in He |- *;
    try discriminate; try (injection He as -> -> -> -> ->; reflexivity); eapply IH; exact He.
Qed.

Lemma gm_submodule_entry : forall Φ T x ip T' pq k D,
    gm_submodule T Φ x ip = Some (mr_body T' (Some (pq, k, D))) ->
    exists pv Φ', gm_entry Φ (x :: ip) = Some (ge_ind pv pq k D Φ').
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] T x ip *; cbn; try discriminate; intros He; try (eapply IH; exact He).
  destruct (String.eqb x y); [| eapply IH; exact He ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [? Φ1 | E']] | pv' ? ? D' Φ1 | pv' A1 M1 [Δ1 [? Φ2 | E2]] | pv' Rr Φ1]; cbn in He |- *;
    try discriminate; try (injection He as _ -> -> ->; eauto; fail); eapply IH; exact He.
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

Lemma gc_entry_ind : forall Θ Ξ p pv pq k D Φ,
    gc_entry Θ Ξ p = Some (ge_ind pv pq k D Φ) -> gc_resolve Θ Ξ p = None /\ ind_mlookup Θ Ξ p = Some (pq, k, D).
Proof.
  intros * He; unfold gc_entry, gc_entry_u, gc_resolve, gc_resolve_u, ind_mlookup, ind_mlookup_u, gc_module, gc_module_u in *.
  rewrite gs_find_tele_find in *.
  destruct (gs_find_tele Ξ p) as [[[U ip] T] |] eqn:Ef; cbn in He |- *.
  - rewrite gs_find_ind_none
      by (destruct ip; [ rewrite gm_entry_nil in He; discriminate | intros ? ? Hc; rewrite Ef in Hc; congruence ]).
    split; [ eapply gm_entry_ind_resolve; exact He |].
    destruct ip as [| x ip]; [ rewrite gm_entry_nil in He; discriminate |].
    erewrite gm_entry_submodule by exact He; reflexivity.
  - rewrite gs_find_ind_none by (intros ? ? Hc; rewrite Ef in Hc; discriminate).
    destruct (gds_lookup Θ (q_unit p)) as [U |]; [| discriminate ].
    split; [ eapply gm_entry_ind_resolve; exact He |].
    destruct (q_chain p) as [| x ip]; [ rewrite gm_entry_nil in He; discriminate |].
    unfold gm_module; erewrite gm_entry_submodule by exact He; reflexivity.
Qed.

(** The member a path names is filed, or its module's frame is open. *)
Lemma ind_mlookup_entry : forall Θ Ξ p pq k D,
    ind_mlookup Θ Ξ p = Some (pq, k, D) ->
    (exists pv Φ, gc_entry Θ Ξ p = Some (ge_ind pv pq k D Φ)) \/ gs_find_ind Ξ p = Some (pq, k, D).
Proof.
  intros * Hl; destruct (gs_find_ind Ξ p) as [r |] eqn:Hf.
  { right; rewrite ind_mlookup_unfold, Hf in Hl; exact Hl. }
  left; unfold gc_entry, gc_entry_u, ind_mlookup, ind_mlookup_u, gc_module, gc_module_u in *; rewrite Hf in Hl.
  rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[U ip] T] |]; cbn in Hl |- *.
  - destruct ip as [| x ip]; [ discriminate |].
    destruct (gm_submodule _ _ _ _) as [[T' [r |] | U'] |] eqn:E; try discriminate.
    injection Hl as ->; eapply gm_submodule_entry; exact E.
  - destruct (gds_lookup Θ (q_unit p)) as [U |]; [| discriminate ].
    destruct (q_chain p) as [| x ip]; cbn in Hl; [ discriminate |].
    destruct (gm_submodule _ _ _ _) as [[T' [r |] | U'] |] eqn:E; try discriminate.
    injection Hl as ->; eapply gm_submodule_entry; exact E.
Qed.

Lemma ind_lookup_entry : forall Θ Ξ p D,
    ind_lookup Θ Ξ p = Some D ->
    exists pq, (exists pv Φ, gc_entry Θ Ξ p = Some (ge_ind pv pq 0 D Φ)) \/ gs_find_ind Ξ p = Some (pq, 0, D).
Proof.
  intros * Hl; destruct (ind_lookup_mlookup _ _ _ _ Hl) as [pq Hm].
  exists pq; exact (ind_mlookup_entry _ _ _ _ _ _ Hm).
Qed.

Lemma gm_entry_resolve_none : forall Φ ip E,
    gm_entry Φ ip = Some E -> (forall b pv A B, E <> ge_def b pv A B) -> gm_resolve Φ ip = None.
Proof.
  fix IH 1; intros [| Φ y E | Φ H its] [| x ip] * He Hn; cbn in He |- *; try discriminate; try (eapply IH; eassumption).
  destruct (String.eqb x y); [| eapply IH; eassumption ].
  destruct ip as [| z ip], E as [b' pv' A' B' | pm [Δ [? Φ1 | E']] | pv' ? ? D' Φ1 | pv' A1 M1 [Δ1 [? Φ2 | E2]] | pv' Rr Φ1]; cbn in He |- *;
    try reflexivity; try (eapply IH; eassumption).
  injection He as <-; exfalso; eapply Hn; reflexivity.
Qed.

(** A definition with a module part, as a module, is its module part. *)
Lemma gm_entry_def_mod_submodule : forall Φ T x ip pv A M Δ E,
    gm_entry Φ (x :: ip) = Some (ge_def_mod pv A M (gu_mk Δ (md_alias E))) ->
    gm_submodule T Φ x ip = Some (mr_alias (gu_mk Δ (md_alias E))).
Proof.
  fix IH 1; intros [| Φ y E0 | Φ H its] T x ip *; cbn; try discriminate; intros He; try (eapply IH; exact He).
  destruct (String.eqb x y); [| eapply IH; exact He ].
  destruct ip as [| z ip], E0 as [b' pv' A' B' | pm0 [Δ0 [? Φ1 | E']] | pv' ? ? D' Φ1 | pv' A1 M1 [Δ1 [? Φ1 | E1]] | pv' Rr Φ1];
    cbn in He |- *; try discriminate; try (injection He as -> -> -> -> ->; reflexivity); eapply IH; exact He.
Qed.

(** A stored definition with a module part resolves to no definition. *)
Lemma gc_entry_def_mod : forall Θ Ξ p pv A M U,
    gc_entry Θ Ξ p = Some (ge_def_mod pv A M U) -> gc_resolve Θ Ξ p = None.
Proof.
  intros * He; unfold gc_entry, gc_entry_u, gc_resolve, gc_resolve_u in *.
  rewrite gs_find_tele_find in *.
  destruct (gs_find_tele Ξ p) as [[[Uf ip] T] |]; cbn in He |- *.
  - eapply gm_entry_resolve_none; [ exact He | intros; discriminate ].
  - destruct (gds_lookup Θ (q_unit p)) as [Uf |]; [| discriminate ].
    eapply gm_entry_resolve_none; [ exact He | intros; discriminate ].
Qed.

(** As a module, a stored definition with a module part is its module part,
    an alias. *)
Lemma gc_entry_def_mod_alias : forall Θ Ξ p pv A M Δ E,
    gc_entry Θ Ξ p = Some (ge_def_mod pv A M (gu_mk Δ (md_alias E))) ->
    gc_module Θ Ξ p = Some (mr_alias (gu_mk Δ (md_alias E))).
Proof.
  intros * He; unfold gc_entry, gc_entry_u, gc_module, gc_module_u in *.
  rewrite gs_find_tele_find in *.
  destruct (gs_find_tele Ξ p) as [[[Uf ip] T] |]; cbn in He |- *.
  - destruct ip as [| x ip]; [ rewrite gm_entry_nil in He; discriminate |].
    eapply gm_entry_def_mod_submodule; exact He.
  - destruct (gds_lookup Θ (q_unit p)) as [Uf |]; [| discriminate ].
    destruct (q_chain p) as [| x ip]; [ rewrite gm_entry_nil in He; discriminate |].
    unfold gm_module; eapply gm_entry_def_mod_submodule; exact He.
Qed.

(** The path of an open frame names no entry. *)
Lemma gc_entry_tele_nil : forall Θ Ξ p U T, gs_find_tele Ξ p = Some (U, nil, T) -> gc_entry Θ Ξ p = None.
Proof.
  intros * HT; unfold gc_entry, gc_entry_u; rewrite gs_find_tele_find, HT; cbn; apply gm_entry_nil.
Qed.

(** A path names the module of a member of a group or a definition with a
    module part, not both; nor a record type and one. *)
Lemma ind_mlookup_not_def_mod : forall Θ Ξ p r pv A M U,
    ind_mlookup Θ Ξ p = Some r -> gc_entry Θ Ξ p = Some (ge_def_mod pv A M U) -> False.
Proof.
  intros * H He; destruct r as [[pq k] D]; destruct (ind_mlookup_entry _ _ _ _ _ _ H) as [(? & ? & He') | Hf].
  - rewrite He in He'; discriminate.
  - destruct (gs_find_ind_tele _ _ _ Hf) as (U' & T & HT).
    rewrite (gc_entry_tele_nil Θ _ _ _ _ HT) in He; discriminate.
Qed.

Lemma record_lookup_not_def_mod : forall Θ Ξ p R pv A M U,
    record_lookup Θ Ξ p = Some R -> gc_entry Θ Ξ p = Some (ge_def_mod pv A M U) -> False.
Proof.
  intros * H He; unfold record_lookup in H.
  destruct (gs_find_record Ξ p) as [R' |] eqn:Hf.
  - destruct (gs_find_record_tele _ _ _ Hf) as (U' & T & HT); rewrite (gc_entry_tele_nil Θ _ _ _ _ HT) in He; discriminate.
  - rewrite He in H; discriminate.
Qed.

(** A path names a record type or a member of a group, not both. *)
Lemma record_lookup_not_ind : forall Θ Ξ p R, record_lookup Θ Ξ p = Some R -> ind_mlookup Θ Ξ p = None.
Proof.
  intros * H; destruct (ind_mlookup Θ Ξ p) as [[[pq k] D] |] eqn:E; [| reflexivity ].
  exfalso; unfold record_lookup in H.
  destruct (ind_mlookup_entry _ _ _ _ _ _ E) as [(pv & Φ & He) | Hf].
  - destruct (gs_find_record Ξ p) as [R' |] eqn:Hf; [| rewrite He in H; discriminate ].
    destruct (gs_find_record_tele _ _ _ Hf) as (U & T & HT); rewrite (gc_entry_tele_nil Θ _ _ _ _ HT) in He; discriminate.
  - rewrite (gs_find_ind_not_record _ _ _ Hf) in H.
    destruct (gs_find_ind_tele _ _ _ Hf) as (U & T & HT).
    rewrite (gc_entry_tele_nil Θ _ _ _ _ HT) in H; discriminate.
Qed.

(** As a module, a definition with a module part is no body. *)
Lemma gm_entry_def_mod_not_body : forall Φ T x ip pv A M U T' oD,
    gm_entry Φ (x :: ip) = Some (ge_def_mod pv A M U) ->
    gm_submodule T Φ x ip = Some (mr_body T' oD) -> False.
Proof.
  fix IH 1; intros [| Φ y E0 | Φ H its] T x ip *; cbn; try discriminate; intros He Hs; try (eapply IH; eassumption).
  destruct (String.eqb x y); [| eapply IH; eassumption ].
  destruct ip as [| z ip], E0 as [b' pv' A' B' | pm0 [Δ0 [? Φ1 | E']] | pv' ? ? D' Φ1 | pv' A1 M1 [Δ1 [? Φ1 | E1]] | pv' Rr Φ1];
    cbn in He, Hs; try discriminate; eapply IH; eassumption.
Qed.

Lemma gc_entry_def_mod_not_body : forall Θ Ξ p pv A M U T oD,
    gc_entry Θ Ξ p = Some (ge_def_mod pv A M U) -> gc_module Θ Ξ p = Some (mr_body T oD) -> False.
Proof.
  intros * He Hm; unfold gc_entry, gc_entry_u, gc_module, gc_module_u in *.
  rewrite gs_find_tele_find in *.
  destruct (gs_find_tele Ξ p) as [[[Uf ip] T0] |]; cbn in He, Hm.
  - destruct ip as [| x ip]; [ discriminate |].
    eapply gm_entry_def_mod_not_body; eassumption.
  - destruct (gds_lookup Θ (q_unit p)) as [Uf |]; [| discriminate ].
    destruct (q_chain p) as [| x ip]; [ rewrite gm_entry_nil in He; discriminate |].
    unfold gm_module in Hm; eapply gm_entry_def_mod_not_body; eassumption.
Qed.

(** A path read as a module is no open frame, so the module of no member
    of a group and of no record type with its frame open. *)
Lemma gc_module_not_find_ind : forall Θ Ξ p r, gc_module Θ Ξ p = Some r -> gs_find_ind Ξ p = None.
Proof.
  intros * Hm; destruct (gs_find_ind Ξ p) as [r' |] eqn:Hf; [| reflexivity ].
  destruct (gs_find_ind_tele _ _ _ Hf) as (U & T & HT).
  unfold gc_module, gc_module_u in Hm; rewrite HT in Hm; discriminate.
Qed.

(** A body module that is the module of no member names no member with a
    term part and a module part, when it is no record type. *)
Lemma module_body_not_dm : forall Θ Ξ p T,
    gc_module Θ Ξ p = Some (mr_body T None) -> record_lookup Θ Ξ p = None -> ~ dm_path Θ Ξ p.
Proof.
  intros * Hm Hr [(r & Hl) | [(R & Hl) | (pv & A & M & U & He)]].
  - rewrite ind_mlookup_unfold, (gc_module_not_find_ind _ _ _ _ Hm), Hm in Hl; discriminate.
  - rewrite Hr in Hl; discriminate.
  - exact (gc_entry_def_mod_not_body _ _ _ _ _ _ _ _ _ He Hm).
Qed.

(** A module stored as a module entry is no record type. *)
Lemma module_entry_no_record : forall Θ Ξ p r pv U,
    gc_module Θ Ξ p = Some r -> gc_entry Θ Ξ p = Some (ge_mod pv U) -> record_lookup Θ Ξ p = None.
Proof.
  intros * Hm He; unfold record_lookup; destruct (gs_find_record Ξ p) as [R |] eqn:Hr.
  - destruct (gs_find_record_tele _ _ _ Hr) as (U0 & T & HT).
    unfold gc_module, gc_module_u in Hm; rewrite HT in Hm; discriminate.
  - rewrite He; reflexivity.
Qed.

(** An alias stored as a module entry names no member with a term part and
    a module part. *)
Lemma module_alias_not_dm : forall Θ Ξ p U pv U',
    gc_module Θ Ξ p = Some (mr_alias U) -> gc_entry Θ Ξ p = Some (ge_mod pv U') -> ~ dm_path Θ Ξ p.
Proof.
  intros * Hm He [(r & Hl) | [(R & Hl) | (pv0 & A & M & U0 & He')]].
  - rewrite ind_mlookup_unfold, (gc_module_not_find_ind _ _ _ _ Hm), Hm in Hl; discriminate.
  - rewrite (module_entry_no_record _ _ _ _ _ _ Hm He) in Hl; discriminate.
  - rewrite He in He'; discriminate.
Qed.

(** [gm_grows Φ Φ']: [Φ'] is [Φ] with more definitions, of fresh names,
    after it, and no more modules: the body of an open frame grows so as
    definitions are added to it. *)
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
  | ge_ind pv pq k D _, ge_ind pv' pq' k' D' _ => pv = pv' /\ pq = pq' /\ k = k' /\ D = D'
  | ge_record pv p R _, ge_record pv' p' R' _ => pv = pv' /\ p = p' /\ R = R'
  | _, _ => E1 = E2
  end.

Lemma entry_grows_refl : forall E, entry_grows E E.
Proof. intros [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? ? | ? ? ?]; cbn; auto. Qed.

Lemma entry_grows_trans : forall E1 E2 E3, entry_grows E1 E2 -> entry_grows E2 E3 -> entry_grows E1 E3.
Proof.
  intros [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? ? | ? ? ?] [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? ? | ? ? ?]
    [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? ? | ? ? ?];
    cbn; intros; destruct_all; subst; try congruence; auto.
Qed.

(** [gc_sub Θ1 Ξ1 Θ2 Ξ2]: what [Θ1 ⍮ Ξ1] resolves, [Θ2 ⍮ Ξ2] resolves the
    same way, its bodies perhaps grown, its open frames perhaps closed. *)
Record gc_sub (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop := mk_gc_sub
  { gcs_resolve : forall p E, gc_resolve Θ1 Ξ1 p = Some E -> gc_resolve Θ2 Ξ2 p = Some E
  ; gcs_module : forall p r, gc_module Θ1 Ξ1 p = Some r -> gc_module Θ2 Ξ2 p = Some r
  ; gcs_body : forall p T Φ, gc_body Θ1 Ξ1 p = Some (T, Φ) ->
      exists Φ', gc_body Θ2 Ξ2 p = Some (T, Φ') /\ gm_grows Φ Φ'
  ; gcs_frame : forall p T Φ, gc_frame Ξ1 p = Some (T, Φ) ->
      exists Φ', (gc_frame Ξ2 p = Some (T, Φ') /\ gs_find_ind Ξ2 p = gs_find_ind Ξ1 p /\
                  gs_find_record Ξ2 p = gs_find_record Ξ1 p) \/
        (gc_body Θ2 Ξ2 p = Some (T, Φ') /\ gc_module Θ2 Ξ2 p = Some (mr_body T (gs_find_ind Ξ1 p)) /\
         record_lookup Θ2 Ξ2 p = gs_find_record Ξ1 p)
  ; gcs_entry : forall p E, gc_entry Θ1 Ξ1 p = Some E -> exists E', gc_entry Θ2 Ξ2 p = Some E' /\ entry_grows E E'
    (** The member a type's open frame is the module of is still read
        there, open or filed *)
  ; gcs_frame_ind : forall p r, gs_find_ind Ξ1 p = Some r -> ind_mlookup Θ2 Ξ2 p = Some r
    (** The record type an open frame is the module of is still read
        there, open or filed *)
  ; gcs_frame_record : forall p R, gs_find_record Ξ1 p = Some R -> record_lookup Θ2 Ξ2 p = Some R }.

Lemma gc_sub_resolve : forall Θ1 Ξ1 Θ2 Ξ2 p E,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_resolve Θ1 Ξ1 p = Some E -> gc_resolve Θ2 Ξ2 p = Some E.
Proof. intros * H; apply (gcs_resolve _ _ _ _ H). Qed.

Lemma gc_sub_module : forall Θ1 Ξ1 Θ2 Ξ2 p r,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_module Θ1 Ξ1 p = Some r -> gc_module Θ2 Ξ2 p = Some r.
Proof. intros * H; apply (gcs_module _ _ _ _ H). Qed.

(** An open frame that is the module of no member and of no record type
    names no member with a term part and a module part in any global
    context it grows into: still an open frame there, or filed as a body
    module of the same kind. *)
Lemma frame_not_dm_sub : forall Θ1 Ξ1 Θ2 Ξ2 p T Φ, gc_sub Θ1 Ξ1 Θ2 Ξ2 ->
    gc_frame Ξ1 p = Some (T, Φ) -> gs_find_ind Ξ1 p = None -> gs_find_record Ξ1 p = None -> ~ dm_path Θ2 Ξ2 p.
Proof.
  intros * Hs Hf Hk Hr.
  destruct (gcs_frame _ _ _ _ Hs _ _ _ Hf) as (Φ' & [(Hf2 & Hk2 & Hr2) | (Hb2 & Hm2 & Hr2)]).
  - rewrite Hk in Hk2; rewrite Hr in Hr2.
    assert (HT : exists U0 T0, gs_find_tele Ξ2 p = Some (U0, nil, T0)).
    { unfold gc_frame in Hf2; destruct (gs_find_tele Ξ2 p) as [[[U0 [| ? ?]] T0] |];
        [ eauto | destruct U0 as [? [[|] ? | ?]]; discriminate | discriminate ]. }
    destruct HT as (U0 & T0 & HT).
    pose proof (gc_entry_tele_nil Θ2 _ _ _ _ HT) as He2.
    intros [(r & Hl) | [(R & Hl) | (pv & A & M & U & He)]].
    + rewrite ind_mlookup_unfold, Hk2 in Hl; unfold gc_module, gc_module_u in Hl; rewrite HT in Hl; discriminate.
    + unfold record_lookup in Hl; rewrite Hr2, He2 in Hl; discriminate.
    + rewrite He2 in He; discriminate.
  - rewrite Hk in Hm2; rewrite Hr in Hr2; exact (module_body_not_dm _ _ _ _ Hm2 Hr2).
Qed.

Lemma gc_sub_body : forall Θ1 Ξ1 Θ2 Ξ2 p T Φ,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_body Θ1 Ξ1 p = Some (T, Φ) ->
    exists Φ', gc_body Θ2 Ξ2 p = Some (T, Φ') /\ gm_grows Φ Φ'.
Proof. intros * H; apply (gcs_body _ _ _ _ H). Qed.

(** An open frame is still one, of the same kind, or has been closed into
    a body module, of the member of a group or the record type its kind
    names, if any. *)
Lemma gc_sub_frame_loc : forall Θ1 Ξ1 Θ2 Ξ2 p T Φ,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_frame Ξ1 p = Some (T, Φ) ->
    exists Φ', (gc_frame Ξ2 p = Some (T, Φ') /\ gs_find_ind Ξ2 p = gs_find_ind Ξ1 p /\
                gs_find_record Ξ2 p = gs_find_record Ξ1 p) \/
      (gc_body Θ2 Ξ2 p = Some (T, Φ') /\ gc_module Θ2 Ξ2 p = Some (mr_body T (gs_find_ind Ξ1 p)) /\
       record_lookup Θ2 Ξ2 p = gs_find_record Ξ1 p).
Proof. intros * H; apply (gcs_frame _ _ _ _ H). Qed.

Lemma gc_sub_frame_ind : forall Θ1 Ξ1 Θ2 Ξ2 p r,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gs_find_ind Ξ1 p = Some r -> ind_mlookup Θ2 Ξ2 p = Some r.
Proof. intros * H; apply (gcs_frame_ind _ _ _ _ H). Qed.

Lemma gc_sub_frame_record : forall Θ1 Ξ1 Θ2 Ξ2 p R,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gs_find_record Ξ1 p = Some R -> record_lookup Θ2 Ξ2 p = Some R.
Proof. intros * H; apply (gcs_frame_record _ _ _ _ H). Qed.

Lemma ind_mlookup_gc_sub : forall Θ1 Ξ1 Θ2 Ξ2 p r,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> ind_mlookup Θ1 Ξ1 p = Some r -> ind_mlookup Θ2 Ξ2 p = Some r.
Proof.
  intros * Hs H; destruct (ind_mlookup_module _ _ _ _ H) as [[T Hm] | Hf]; [| exact (gc_sub_frame_ind _ _ _ _ _ _ Hs Hf) ].
  exact (ind_mlookup_body _ _ _ _ _ (gc_sub_module _ _ _ _ _ _ Hs Hm)).
Qed.

(** What is stored at a path stays there, its bodies perhaps grown. *)
Lemma gc_sub_entry : forall Θ1 Ξ1 Θ2 Ξ2 p E,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_entry Θ1 Ξ1 p = Some E -> exists E', gc_entry Θ2 Ξ2 p = Some E' /\ entry_grows E E'.
Proof. intros * H; apply (gcs_entry _ _ _ _ H). Qed.

(** A path naming an entry is no open frame's own path, so no record's
    open frame. *)
Lemma gc_entry_record_frame_none : forall Θ Ξ p E, gc_entry Θ Ξ p = Some E -> gs_find_record Ξ p = None.
Proof.
  intros * H; apply gs_find_record_none; intros U T Ht.
  unfold gc_entry, gc_entry_u in H; rewrite gs_find_tele_find, Ht in H; cbn in H.
  rewrite gm_entry_nil in H; discriminate.
Qed.

(** A stored record type is the record type its path names. *)
Lemma gc_entry_record : forall Θ Ξ p pv pr R Φ,
    gc_entry Θ Ξ p = Some (ge_record pv pr R Φ) -> record_lookup Θ Ξ p = Some R.
Proof.
  intros * He; unfold record_lookup; rewrite (gc_entry_record_frame_none _ _ _ _ He), He; reflexivity.
Qed.

(** The record type a path names is a stored one, or its module's frame is
    open, where the path names no entry. *)
Lemma record_lookup_entry : forall Θ Ξ p R,
    record_lookup Θ Ξ p = Some R -> gc_entry Θ Ξ p = None \/ exists pv pr Φ, gc_entry Θ Ξ p = Some (ge_record pv pr R Φ).
Proof.
  intros * H; unfold record_lookup in H.
  destruct (gs_find_record Ξ p) as [R' |] eqn:Hf.
  - left; destruct (gs_find_record_tele _ _ _ Hf) as (U & T & HT); exact (gc_entry_tele_nil Θ _ _ _ _ HT).
  - right; destruct (gc_entry Θ Ξ p) as [[| | | | pv pr R0 Φ] |]; try discriminate; injection H as ->; eauto.
Qed.

(** A stored record type resolves to no definition. *)
Lemma gc_entry_record_resolve : forall Θ Ξ p pv pr R Φ, gc_entry Θ Ξ p = Some (ge_record pv pr R Φ) -> gc_resolve Θ Ξ p = None.
Proof.
  intros * He; unfold gc_entry, gc_entry_u, gc_resolve, gc_resolve_u in *.
  destruct (gs_find Ξ p) as [[U ip] |]; [ eapply gm_entry_resolve_none; [ exact He | intros; discriminate ] |].
  destruct (gds_lookup Θ (q_unit p)); [ eapply gm_entry_resolve_none; [ exact He | intros; discriminate ] | discriminate ].
Qed.

(** Nor does a record type a path names. *)
Lemma record_lookup_resolve : forall Θ Ξ p R, record_lookup Θ Ξ p = Some R -> gc_resolve Θ Ξ p = None.
Proof.
  intros * H; unfold record_lookup in H.
  destruct (gs_find_record Ξ p) as [R' |] eqn:Hf.
  - destruct (gs_find_record_tele _ _ _ Hf) as (U & T & HT).
    unfold gc_resolve, gc_resolve_u; rewrite gs_find_tele_find, HT; cbn; apply gm_resolve_nil.
  - destruct (gc_entry Θ Ξ p) as [[| | | | pv pr R0 Φ] |] eqn:He; try discriminate.
    exact (gc_entry_record_resolve _ _ _ _ _ _ _ He).
Qed.

(** A record type stays, with the same declaration, along a growth of the
    global context: an open frame's as [gcs_frame_record] says, a filed
    one's as its entry grows. *)
Lemma record_lookup_gc_sub : forall Θ1 Ξ1 Θ2 Ξ2 p R,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> record_lookup Θ1 Ξ1 p = Some R -> record_lookup Θ2 Ξ2 p = Some R.
Proof.
  intros * Hs H; unfold record_lookup in H.
  destruct (gs_find_record Ξ1 p) as [R0 |] eqn:Hf.
  - injection H as <-; exact (gc_sub_frame_record _ _ _ _ _ _ Hs Hf).
  - destruct (gc_entry Θ1 Ξ1 p) as [[| | | | pv pr R0 Φ] |] eqn:E; try discriminate; injection H as <-.
    destruct (gc_sub_entry _ _ _ _ _ _ Hs E) as ([| | | | pv' pr' R' Φ'] & HE' & Hg); cbn in Hg;
      try contradiction; try discriminate.
    destruct Hg as (_ & _ & ->); unfold record_lookup; rewrite (gc_entry_record_frame_none _ _ _ _ HE'), HE'; reflexivity.
Qed.

(** A body module names an entry along its path. *)
Lemma gm_subbody_entry_some : forall Φ T x ip T' Φ', gm_subbody T Φ x ip = Some (T', Φ') ->
    exists E, gm_entry Φ (x :: ip) = Some E.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H) ].
  destruct ip as [| z ip]; [ eauto |].
  destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? D Φ0 | ? ? ? ? | ? R Φ0]; try discriminate; exact (IH _ _ _ _ _ _ H).
Qed.

(** A path that names a body module, at the root of its unit, names no
    entry and no frame's record. *)
Lemma gc_body_root_record : forall Θ Ξ p T Φ, gc_body Θ Ξ p = Some (T, Φ) -> q_chain p = nil ->
    record_lookup Θ Ξ p = None.
Proof.
  intros * Hb Hc; unfold record_lookup.
  rewrite gs_find_record_none; [| intros U T0 Ht; unfold gc_body in Hb; rewrite Ht in Hb; discriminate ].
  unfold gc_entry, gc_entry_u; rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[U ip] T0] |] eqn:Ef; cbn.
  - destruct ip as [| x ip]; [ rewrite gm_entry_nil; reflexivity |].
    exfalso; clear Hb; induction Ξ as [| [[mf K] V] Ξ IH]; cbn in Ef; [ discriminate |].
    destruct (qname_strip mf p) as [r |] eqn:Hs; [| exact (IH Ef) ].
    injection Ef as _ -> _; unfold qname_strip in Hs.
    destruct (path_beq (q_unit mf) (q_unit p)); [| discriminate ].
    apply strip_prefix_spec in Hs; rewrite Hc in Hs; destruct (q_chain mf); discriminate.
  - destruct (gds_lookup Θ (q_unit p)); [ rewrite Hc, gm_entry_nil |]; reflexivity.
Qed.

(** A body module that is the module of no record type stays so along a
    growth of the global context: its entry grows into one of the same
    kind, and a unit's root is no record's. *)
Lemma record_lookup_none_gc_sub : forall Θ1 Ξ1 Θ2 Ξ2 p T Φ,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_body Θ1 Ξ1 p = Some (T, Φ) -> record_lookup Θ1 Ξ1 p = None ->
    record_lookup Θ2 Ξ2 p = None.
Proof.
  intros * Hs Hb Hr.
  destruct (gc_entry Θ1 Ξ1 p) as [E |] eqn:He.
  - destruct (gc_sub_entry _ _ _ _ _ _ Hs He) as (E' & He' & Hg).
    unfold record_lookup in Hr |- *; rewrite (gc_entry_record_frame_none _ _ _ _ He), He in Hr.
    rewrite (gc_entry_record_frame_none _ _ _ _ He'), He'.
    destruct E' as [| | | | pv' R' Φ']; try reflexivity; exfalso.
    destruct E as [| ? [? [? ?| ?]] | | | ]; cbn in Hg; try discriminate.
  - assert (Hc : q_chain p = nil).
    { unfold gc_body in Hb; unfold gc_entry, gc_entry_u in He; rewrite gs_find_tele_find in He.
      destruct (gs_find_tele Ξ1 p) as [[[U [| x ip]] T0] |]; cbn in He; [ discriminate | |].
      - destruct (gm_subbody_entry_some _ _ _ _ _ _ Hb) as (E & HE); rewrite HE in He; discriminate.
      - destruct (gds_lookup Θ1 (q_unit p)) as [U |]; [| discriminate ].
        destruct (q_chain p) as [| x ip]; [ reflexivity |].
        destruct (gm_subbody_entry_some _ _ _ _ _ _ Hb) as (E & HE); rewrite HE in He; discriminate. }
    destruct (gc_sub_body _ _ _ _ _ _ _ Hs Hb) as (Φ2 & Hb2 & _).
    exact (gc_body_root_record _ _ _ _ _ Hb2 Hc).
Qed.

Lemma gc_sub_refl : forall Θ Ξ, gc_sub Θ Ξ Θ Ξ.
Proof.
  constructor; intros * H; [ exact H | exact H | exists Φ; split; [ exact H | constructor ]
    | exists Φ; left; split; [ exact H | split; reflexivity ] | exists E; split; [ exact H | apply entry_grows_refl ]
    | rewrite ind_mlookup_unfold, H; reflexivity | unfold record_lookup; rewrite H; reflexivity ].
Qed.

Lemma gc_sub_trans : forall Θ1 Ξ1 Θ2 Ξ2 Θ3 Ξ3,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> gc_sub Θ2 Ξ2 Θ3 Ξ3 -> gc_sub Θ1 Ξ1 Θ3 Ξ3.
Proof.
  intros * Hs12 Hs23; pose proof Hs23 as Hs23'.
  destruct Hs12 as [H12 M12 B12 F12 E12 K12 R12], Hs23 as [H23 M23 B23 F23 E23 K23 R23]; constructor; intros * H;
    [ apply H23, H12, H | apply M23, M12, H | | | | | ].
  - destruct (B12 _ _ _ H) as (Φ2 & H2 & G12); destruct (B23 _ _ _ H2) as (Φ3 & H3 & G23).
    exists Φ3; split; [ exact H3 | exact (gm_grows_trans _ _ _ G12 G23) ].
  - destruct (F12 _ _ _ H) as (Φ2 & [(H2 & Hk2 & Hr2) | (H2 & Hm2 & Hr2)]).
    + rewrite <- Hk2, <- Hr2; exact (F23 _ _ _ H2).
    + destruct (B23 _ _ _ H2) as (Φ3 & H3 & _); exists Φ3; right; split; [ exact H3 | split; [ exact (M23 _ _ Hm2) |] ].
      destruct (gs_find_record Ξ1 p) as [R |] eqn:Hf.
      * exact (record_lookup_gc_sub _ _ _ _ _ _ Hs23' (R12 _ _ Hf)).
      * exact (record_lookup_none_gc_sub _ _ _ _ _ _ _ Hs23' H2 Hr2).
  - destruct (E12 _ _ H) as (E2 & H2 & G12); destruct (E23 _ _ H2) as (E3 & H3 & G23).
    exists E3; split; [ exact H3 | exact (entry_grows_trans _ _ _ G12 G23) ].
  - exact (ind_mlookup_gc_sub _ _ _ _ _ _ Hs23' (K12 _ _ H)).
  - exact (record_lookup_gc_sub _ _ _ _ _ _ Hs23' (R12 _ _ H)).
Qed.

Lemma ind_lookup_gc_sub : forall Θ1 Ξ1 Θ2 Ξ2 p D,
    gc_sub Θ1 Ξ1 Θ2 Ξ2 -> ind_lookup Θ1 Ξ1 p = Some D -> ind_lookup Θ2 Ξ2 p = Some D.
Proof.
  intros * Hs H; destruct (ind_lookup_mlookup _ _ _ _ H) as [pq Hm].
  rewrite ind_lookup_unfold, (ind_mlookup_gc_sub _ _ _ _ _ _ Hs Hm); reflexivity.
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
  ; gms_entry : forall ip E, gm_entry Φ1 ip = Some E -> exists E', gm_entry Φ2 ip = Some E' /\ entry_grows E E' }.

Lemma gm_sub_refl : forall Φ, gm_sub Φ Φ.
Proof. repeat split; intros * H; eauto using entry_grows_refl with mctt. Qed.

Lemma gm_sub_trans : forall Φ1 Φ2 Φ3, gm_sub Φ1 Φ2 -> gm_sub Φ2 Φ3 -> gm_sub Φ1 Φ3.
Proof.
  intros * [H12 M12 B12 E12] [H23 M23 B23 E23]; constructor; intros * H;
    [ apply H23, H12, H | apply M23, M12, H | | ].
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
  - eexists; split; [ exact (gm_entry_ext_fresh _ _ _ _ _ Hf H) | apply entry_grows_refl ].
Qed.

(** A frame whose body grows. *)
Lemma gc_sub_frame : forall Θ Ξ mp K Δ Φ1 Φ2,
    gm_sub Φ1 Φ2 ->
    gc_sub Θ ((mp, K, gu_body Δ Φ1) :: Ξ) Θ ((mp, K, gu_body Δ Φ2) :: Ξ).
Proof.
  intros * [HR HM HB HE]; constructor.
  - intros p E0 Hr; unfold gc_resolve, gc_resolve_u in *; cbn in *.
    destruct (qname_strip mp p); [ apply HR; exact Hr | exact Hr ].
  - intros p r Hr; unfold gc_module, gc_module_u in *; cbn in *.
    destruct (qname_strip mp p) as [[| y ip] |]; [ discriminate | | exact Hr ].
    apply HM; exact Hr.
  - intros p T Φ Hr; unfold gc_body in *; cbn in *.
    destruct (qname_strip mp p) as [[| y ip] |]; [ discriminate | | eexists; split; [ exact Hr | constructor ] ].
    apply HB; exact Hr.
  - intros p T Φ Hr; unfold gc_frame in *; cbn in *.
    destruct (qname_strip mp p) as [[| y ip] |]; [ | discriminate | eexists; left; split; [ exact Hr | split; reflexivity ] ].
    injection Hr as <- <-; eexists; left; split; [ reflexivity | split; reflexivity ].
  - intros p E0 Hr; unfold gc_entry, gc_entry_u in *; cbn in *.
    destruct (qname_strip mp p); [ apply HE; exact Hr | exists E0; split; [ exact Hr | apply entry_grows_refl ] ].
  - intros p r Hr; rewrite ind_mlookup_unfold, (gs_find_ind_unit _ _ _ (gu_body Δ Φ1)), Hr; reflexivity.
  - intros p R Hr; unfold record_lookup.
    replace (gs_find_record ((mp, K, gu_body Δ Φ2) :: Ξ) p) with (gs_find_record ((mp, K, gu_body Δ Φ1) :: Ξ) p)
      by reflexivity.
    rewrite Hr; reflexivity.
Qed.

(** A frame may be pushed when its module path is fresh where it is pushed: a
    unit not filed below, named by its root path, or a member not yet declared
    in the enclosing frame.  The root condition makes every prefix of a path
    that resolves resolve as well. *)
Definition frame_fresh (Θ : gdeps) (Ξ : gstack) (mp : qname) : Prop :=
  match Ξ with
  | nil => gds_lookup Θ (q_unit mp) = None /\ q_chain mp = nil
  | (mq, _, U) :: _ => exists x, mp = qname_in mq x /\ gm_fresh x (gu_mod U)
  end.

Lemma gc_sub_push : forall Θ Ξ mp K U,
    frame_fresh Θ Ξ mp ->
    gc_sub Θ Ξ Θ ((mp, K, U) :: Ξ).
Proof.
  intros * Hf; repeat split.
  - intros p E Hr; unfold gc_resolve, gc_resolve_u in *; cbn.
    destruct (qname_strip mp p) as [ip |] eqn:Hs; [| exact Hr ].
    exfalso; unfold qname_strip in Hs.
    destruct (path_beq (q_unit mp) (q_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb.
    destruct Ξ as [| [[mq K'] V] Ξ']; cbn in Hf, Hr.
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
    destruct Ξ as [| [[mq K'] V] Ξ']; cbn in Hf, Hr.
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
    destruct Ξ as [| [[mq K'] V] Ξ']; cbn in Hf, Hr.
    + destruct Hf as [Hf _].
      rewrite <- Hb, Hf in Hr; discriminate.
    + destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
      pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
      unfold qname_strip in Hr; rewrite Hb, path_beq_refl, Hs' in Hr.
      exact (Hx (gm_subbody_head _ _ _ _ _ Hr)).
  - intros p T Φ Hr; exists Φ; left; unfold gc_frame in *; cbn [gs_find_tele gs_find_ind gs_find_record].
    destruct (qname_strip mp p) as [ip |] eqn:Hs; [| split; [ exact Hr | split; reflexivity ] ].
    exfalso; unfold qname_strip in Hs.
    destruct (path_beq (q_unit mp) (q_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb.
    destruct Ξ as [| [[mq K'] V] Ξ']; cbn in Hf, Hr; [ discriminate |].
    destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
    pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
    unfold qname_strip in Hr; rewrite Hb, path_beq_refl, Hs' in Hr.
    destruct V as [? [[] ? | ?]]; cbn in Hr; discriminate.
  - intros p E Hr; exists E; split; [| apply entry_grows_refl ]; unfold gc_entry, gc_entry_u in *; cbn.
    destruct (qname_strip mp p) as [ip |] eqn:Hs; [| exact Hr ].
    exfalso; unfold qname_strip in Hs.
    destruct (path_beq (q_unit mp) (q_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb.
    destruct Ξ as [| [[mq K'] V] Ξ']; cbn in Hf, Hr.
    + destruct Hf as [Hf _].
      rewrite <- Hb, Hf in Hr; discriminate.
    + destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
      pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
      unfold qname_strip in Hr; rewrite Hb, path_beq_refl, Hs' in Hr.
      destruct (gm_entry_head _ _ _ Hr) as (z & ip' & [= <- <-] & Hin); contradiction.
  - intros p r Hr; rewrite ind_mlookup_unfold; cbn [gs_find_ind].
    destruct (qname_strip mp p) as [ip |] eqn:Hs; [| rewrite Hr; reflexivity ].
    exfalso; destruct (gs_find_ind_tele _ _ _ Hr) as (U' & T' & Ht).
    unfold qname_strip in Hs.
    destruct (path_beq (q_unit mp) (q_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb.
    destruct Ξ as [| [[mq K'] V] Ξ']; cbn in Hf, Ht; [ discriminate |].
    destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
    pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
    unfold qname_strip in Ht; rewrite Hb, path_beq_refl, Hs' in Ht; discriminate.
  - intros p R Hr; unfold record_lookup; cbn [gs_find_record].
    destruct (qname_strip mp p) as [ip |] eqn:Hs; [| rewrite Hr; reflexivity ].
    exfalso; destruct (gs_find_record_tele _ _ _ Hr) as (U' & T' & Ht).
    unfold qname_strip in Hs.
    destruct (path_beq (q_unit mp) (q_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb.
    destruct Ξ as [| [[mq K'] V] Ξ']; cbn in Hf, Ht; [ discriminate |].
    destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
    pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
    unfold qname_strip in Ht; rewrite Hb, path_beq_refl, Hs' in Ht; discriminate.
Qed.

Lemma gc_sub_grow : forall Θ Ξ mp K Δ Φ x E,
    gm_fresh x Φ ->
    gc_sub Θ ((mp, K, gu_body Δ Φ) :: Ξ) Θ ((mp, K, gu_body Δ (Φ ⊳ x ↦ E)) :: Ξ).
Proof. intros * Hf; apply gc_sub_frame, gm_sub_ext_fresh; exact Hf. Qed.

(** Filing a unit: what was read in its open frame is read in the filed
    unit. *)
Lemma gc_sub_file : forall Θ fp U,
    gds_lookup Θ fp = None ->
    gc_sub Θ ((q_abs fp nil, fk_module, U) :: nil) ((fp, U) :: Θ) nil.
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
  - intros p T Φ Hr; exists Φ; right; unfold gc_frame, gc_body in *; cbn [gs_find_tele] in *.
    unfold qname_strip in Hr; cbn [q_unit q_chain strip_prefix] in Hr; cbn [gds_lookup].
    destruct (path_beq fp (q_unit p)) eqn:Hb; [| discriminate ].
    apply path_beq_true in Hb; subst; rewrite path_beq_refl.
    destruct (q_chain p) as [| x ip] eqn:Hp; cbn in Hr; destruct U as [Δ [[] Φ0 | ?]]; cbn in Hr; try discriminate.
    injection Hr as <- <-.
    assert (Hb : gc_body ((q_unit p, gu_mk Δ (md_body sm_closed Φ0)) :: Θ) nil p = Some (Δ, Φ0))
      by (unfold gc_body; cbn [gs_find_tele gds_lookup]; rewrite path_beq_refl, Hp; reflexivity).
    pose proof (gc_body_root_record _ _ _ _ _ Hb Hp) as Hrl.
    split; [ cbn; rewrite List.app_nil_r; reflexivity | split ].
    + cbn; rewrite List.app_nil_r; unfold gc_module, gc_module_u; cbn [gs_find_tele gds_lookup].
      rewrite path_beq_refl, Hp; destruct (qname_strip _ _) as [[| ? ?] |]; reflexivity.
    + rewrite Hrl; cbn; destruct (qname_strip _ _) as [[| ? ?] |]; reflexivity.
  - intros p E0 Hr; exists E0; split; [| apply entry_grows_refl ]; unfold gc_entry, gc_entry_u in *; cbn [gs_find] in *.
    unfold qname_strip in Hr; cbn [q_unit q_chain strip_prefix] in Hr; cbn [gds_lookup].
    destruct (path_beq fp (q_unit p)) eqn:Hb.
    + apply path_beq_true in Hb; subst; rewrite path_beq_refl; exact Hr.
    + destruct (path_beq (q_unit p) fp) eqn:Hb'; [ apply path_beq_true in Hb'; subst; rewrite path_beq_refl in Hb; discriminate | exact Hr ].
  - intros p r Hr; rewrite gs_find_ind_module_frame in Hr; destruct (qname_strip _ p); discriminate.
  - intros p R Hr; cbn in Hr; destruct (qname_strip _ p) as [[| ? ?] |]; discriminate.
Qed.

(** A filed unit resolves as its closed frame did. *)
Lemma gc_resolve_file : forall Θ fp U p,
    gc_resolve ((fp, U) :: Θ) nil p = gc_resolve Θ ((q_abs fp nil, fk_module, U) :: nil) p.
Proof.
  intros; unfold gc_resolve, gc_resolve_u; cbn [gs_find gds_lookup]; unfold qname_strip; cbn [q_unit q_chain strip_prefix].
  destruct (path_beq fp (q_unit p)) eqn:Hb.
  - apply path_beq_true in Hb as ->; rewrite path_beq_refl; reflexivity.
  - destruct (path_beq (q_unit p) fp) eqn:Hb'; [| reflexivity ].
    apply path_beq_true in Hb'; rewrite Hb', path_beq_refl in Hb; discriminate.
Qed.

(** A filed unit stores the entries its closed frame did. *)
Lemma gc_entry_file : forall Θ fp U p,
    gc_entry ((fp, U) :: Θ) nil p = gc_entry Θ ((q_abs fp nil, fk_module, U) :: nil) p.
Proof.
  intros; unfold gc_entry, gc_entry_u; cbn [gs_find gds_lookup]; unfold qname_strip; cbn [q_unit q_chain strip_prefix].
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
  - intros p T Φ Hr; exists Φ; left; split; [ exact Hr | split; reflexivity ].
  - intros p E Hr; exists E; split; [| apply entry_grows_refl ]; unfold gc_entry, gc_entry_u in *.
    destruct (gs_find Ξ p) as [[U ip] |]; [ exact Hr |].
    destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:E1; [| discriminate ].
    rewrite (Hs _ _ E1); exact Hr.
  - intros p r Hr; rewrite ind_mlookup_unfold, Hr; reflexivity.
  - intros p R Hr; unfold record_lookup; rewrite Hr; reflexivity.
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

Lemma gc_subx_push : forall Θ Ξ mp K U, frame_fresh Θ Ξ mp -> gc_subx Θ Ξ Θ ((mp, K, U) :: Ξ).
Proof.
  intros * Hf; split; [ apply gc_sub_push; exact Hf |].
  intros p r Hr; unfold gc_body in *; cbn.
  destruct (qname_strip mp p) as [ip |] eqn:Hs; [| exact Hr ].
  exfalso; unfold qname_strip in Hs.
  destruct (path_beq (q_unit mp) (q_unit p)) eqn:Hb; [| discriminate ].
  apply path_beq_true in Hb.
  destruct Ξ as [| [[mq K'] V] Ξ']; cbn in Hf, Hr.
  - destruct Hf as [Hf _]; rewrite <- Hb, Hf in Hr; discriminate.
  - destruct Hf as (x & -> & Hx); cbn in Hs, Hb.
    pose proof (strip_prefix_snoc _ _ _ _ Hs) as Hs'.
    unfold qname_strip in Hr; rewrite Hb, path_beq_refl, Hs' in Hr.
    exact (Hx (gm_subbody_head _ _ _ _ _ Hr)).
Qed.

Lemma gc_subx_grow : forall Θ Ξ mp K Δ Φ x E,
    gm_fresh x Φ ->
    gc_subx Θ ((mp, K, gu_body Δ Φ) :: Ξ) Θ ((mp, K, gu_body Δ (Φ ⊳ x ↦ E)) :: Ξ).
Proof.
  intros * Hf; split; [ apply gc_sub_grow; exact Hf |].
  intros p r Hr; unfold gc_body in *; cbn in *.
  destruct (qname_strip mp p) as [[| y ip] |]; [ discriminate | | exact Hr ].
  cbn in *; apply gm_subbody_ext_fresh; assumption.
Qed.

Lemma gc_subx_file : forall Θ fp U,
    gds_lookup Θ fp = None ->
    gc_subx Θ ((q_abs fp nil, fk_module, U) :: nil) ((fp, U) :: Θ) nil.
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

(** [ge_transparent E]: every definition in the entry [E], down through its
    module and inductive bodies, is transparent and has a body; aliases
    impose nothing.  [gm_transparent Φ] is the same for every entry of a
    module body. *)
Fixpoint ge_transparent (E : gentry) : Prop :=
  match E with
  | ge_def b _ _ B => b = true /\ B <> None
  | ge_mod _ (gu_mk _ (md_body sm Φ)) => gm_transparent Φ
  | ge_mod _ (gu_mk _ (md_alias _)) => True
  | ge_ind _ _ _ _ Φ => gm_transparent Φ
  | ge_def_mod _ _ _ _ => True
  | ge_record _ _ _ Φ => gm_transparent Φ
  end
with gm_transparent (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ _ E => gm_transparent Φ /\ ge_transparent E
  | gm_open Φ _ _ => gm_transparent Φ
  end.

Definition gc_transparent (Θ : gdeps) (Ξ : gstack) : Prop :=
  (forall fp U, List.In (fp, U) Θ -> gm_transparent (gu_mod U)) /\
  (forall mp K U, List.In (mp, K, U) Ξ -> gm_transparent (gu_mod U)).

Lemma gm_transparent_resolve : forall Φ ip E,
    gm_transparent Φ -> gm_resolve Φ ip = Some E -> ge_transparent E.
Proof.
  fix IH 1; intros [| Φ y E | Φ c] ip E0 HΦ H; cbn in H, HΦ; [ discriminate | | eapply IH; eassumption ].
  destruct HΦ as [HΦ HE].
  destruct ip as [| x ip']; [ discriminate |].
  destruct (String.eqb x y); [| eapply IH; eassumption ].
  destruct ip' as [| z ip''], E as [b pv A B | pm [Δ' [? Φ' | E']] | pv ? ? D Φ' | pv Aa Ma [Δa [? Φa | Ea]] | pv Rr Φ']; try discriminate.
  - injection H as <-; exact HE.
  - eapply IH; [ exact HE | exact H ].
  - eapply IH; [ exact HE | exact H ].
  - eapply IH; [ exact HE | exact H ].
Qed.

Lemma gc_transparent_resolve : forall Θ Ξ p b pv A B,
    gc_transparent Θ Ξ ->
    gc_resolve Θ Ξ p = Some (ge_def b pv A B) ->
    b = true /\ B <> None.
Proof.
  intros * [HΘ HΞ] Hr.
  destruct (gc_resolve_inv _ _ _ _ Hr) as [(mp & K & U & ip & Hin & Hm) | (fp & U & Hl & Hm)].
  - exact (gm_transparent_resolve _ _ _ (HΞ _ _ _ Hin) Hm).
  - exact (gm_transparent_resolve _ _ _ (HΘ _ _ (gds_lookup_in _ _ _ Hl)) Hm).
Qed.

(** ** Module Slots *)

Reserved Notation "Γ ∋ '#' x ≔ₘ U" (at level 70, x constr at level 0, U at level 69).

(** The unit of a module slot, weakened to the use site. *)
Inductive ctx_lookup_mod : nat -> gunit -> ctx -> Prop :=
(** The innermost slot *)
| mod_here : `(Γ ▹ₘ U ∋ #0 ≔ₘ gunit_wk U wk_shift)
(** The innermost definition with a module part, as its module part *)
| mod_here_dm : `(Γ ▸ₘ A ≔ M ‖ U ∋ #0 ≔ₘ gunit_wk U wk_shift)
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
      | 0 => match e with ce_mod U | ce_dm _ _ U => Some (gunit_wk U wk_shift) | _ => None end
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
Proof. induction 1; cbn; [ reflexivity | reflexivity | rewrite IHctx_lookup_mod; reflexivity ]. Qed.

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

(** The [Π]s a normal type is written with and what they end in: the
    domains as a context, innermost first (the last [Π]'s domain at the
    head, the first one's at the end), and the codomain past them, in that
    context.  [Π (A : Typeω@0). A → Typeω@0] gives the context
    [ce_ass #0 :: ce_ass Typeω@0 :: nil] (the inner domain [A], bound
    second, at the head) and the codomain [Typeω@0]. *)
Fixpoint nf_pi_tele (W : nf) : (ctx * nf)%type :=
  match W with
  | nf_pi B C => let '(Ds, C') := nf_pi_tele C in (Ds ++ ce_ass (nf_to_exp B) :: nil, C')
  | _ => (nil, W)
  end.

(** A normal type that is a universe, large or small. *)
Definition nf_is_universe (W : nf) : Prop :=
  match W with
  | nf_typ _ | nf_univ _ _ => True
  | _ => False
  end.

(** [M] applied to the [n] innermost variables, outermost first, past
    them: [M], in [Γ], read in [Ds ++ Γ] for an [n]-entry [Ds], at the
    variables [Ds] binds. *)
Definition exp_applied_to_vars (M : exp) (n : nat) : exp := apps_exp M[wk_shiftn n]ʷ (vars_from 0 n).

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
  | ce_dm _ N U :: R' =>
      match tele_open R' with
      | Some (B', T') => Some (B'[Id ,,ᵈ N ‖ me_lit U], tele_sub T' (q (Id ,,ᵈ N ‖ me_lit U)))
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
    distinct; or a term part with a module part ([ds_dm Θ A M Rm]): a
    definition with a module part, or the type former of an inductive or
    a record type with its module ([ind_former_desc],
    [record_former_desc]).  The
    arguments are terms over the context extended by [Θ].  A description
    never contains an alias, and its entries are read where no local open
    is left.

    A lookup returns the whole description, and each rule takes the part it
    expects: the term part ([ds_ty], [ds_red]), the module part
    ([ds_mod]). *)

(** The sort of a member, as evaluation reads it. *)
Inductive mkind : Set :=
(** A definition *)
| mk_term
(** A module *)
| mk_mod
(** A member with a term part and a module part: an inductive type, a
    record type, or a definition with a module part *)
| mk_dm.

(** A member description: what a module expression or an entry denotes
    (see the section header above). *)
Inductive mdesc : Set :=
(** A term of the type, with its δ-reduct if it is transparent *)
| ds_term : typ -> option exp -> mdesc
(** An open body module: its parameters, its written body and its
    expansion *)
| ds_open : ctx -> gmod -> gmod -> mdesc
(** A closed module, at its canonical path, over its full telescope, given
    the arguments so far, abstracted over the outer parameters *)
| ds_closed : ctx -> qname -> ctx -> gmod -> list exp -> mdesc
(** [ds_dm Θd A M Rm]: what a definition with a module part
    ([ge_def_mod]) denotes, and the type former of an inductive or a
    record type with its module ([ind_former_desc],
    [record_former_desc]).  Its term part is read as a transparent
    definition's is: the term [M] of the type [A], both over the outer
    parameters [Θd], given the arguments so far as [ds_term A (Some M)] is
    ([ds_ats_read]); its module part is [Rm] *)
| ds_dm : ctx -> typ -> exp -> mdesc -> mdesc.

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

(** The term part: the type of a definition, or of a definition with a
    module part, over the outside parameters. *)
Definition ds_ty (R : mdesc) : option typ :=
  match R with
  | ds_term A _ => Some A
  (** A definition with a module part: its term part's type *)
  | ds_dm Θd A _ _ => Some (ctx_pi Θd A)
  | _ => None
  end.

(** The δ-reduct of the term part: the body of a transparent definition, or
    of a definition with a module part; an axiom and an abstract
    definition have none. *)
Definition ds_red (R : mdesc) : option exp :=
  match R with
  | ds_term _ om => om
  | ds_dm Θd _ M _ => Some (ctx_fn Θd M)
  | _ => None
  end.

(** The module part: a module is its own, and a definition with a module
    part's is that of its module part. *)
Fixpoint ds_mod (R : mdesc) : option mdesc :=
  match R with
  | ds_open _ _ _ | ds_closed _ _ _ _ _ => Some R
  (** A definition with a module part: the module of its module part, so
      that a module part is always read as a module *)
  | ds_dm _ _ _ Rm => ds_mod Rm
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
Definition ds_mtele (R : mdesc) : option ctx :=
  match ds_mod R with
  | Some Rm => ds_tele Rm
  | None => None
  end.

(** Abstraction: a description from inside an open body, the body's
    parameters and the entries before the member being [Θ'], re-expressed
    outside it.  [Π] and [λ] read a definition entry of [Θ'] as a [let]. *)
Fixpoint ds_up (Θ' : ctx) (R : mdesc) : mdesc :=
  match R with
  | ds_term A om => ds_term (ctx_pi Θ' A) (option_map (ctx_fn Θ') om)
  | ds_open Δ Φ Φx => ds_open (Δ ++ Θ') Φ Φx
  | ds_closed Θ p T Φ Ns => ds_closed (Θ ++ Θ') p T Φ Ns
  | ds_dm Θd A M Rm => ds_dm (Θd ++ Θ') A M (ds_up Θ' Rm)
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
  | ce_dm _ N U :: R' =>
      match tele_split R' with
      | inl (B', T', τ) => inl (B'[Id ,,ᵈ N ‖ me_lit U], tele_sub T' (q (Id ,,ᵈ N ‖ me_lit U)),
                                τ ⨟ sb_qn (S (List.length T')) (Id ,,ᵈ N ‖ me_lit U))
      | inr τ => inr (τ ⨟ (Id ,,ᵈ N ‖ me_lit U))
      end
  end.

(** Application "R at N": [N] is the next parameter.  A leading definition
    entry is substituted away first, in every form.  An open module
    substitutes [N] into its body; a closed one with outside parameters left
    fills the outermost of them, and with none records the argument, the
    stored module being read as it is; likewise for an inductive type.  A
    definition with a module part given its outside parameters fills them,
    in both its parts, as a closed module does; past them it is its module
    part applied: the term reading and the module reading of [K N] are
    separate, and an application is a module reading.  (Its term part takes
    only the arguments of the frames it is filed in, when it is read as a
    member of a closed module at them: [ds_read].) *)
Fixpoint ds_at (R : mdesc) (N : exp) : option mdesc :=
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
  | ds_dm Θ A M Rm =>
      match ds_at Rm N with
      | None => None
      | Some Rm' =>
          match tele_split (rev Θ) with
          | inl (_, Θ', τ) =>
              Some (ds_dm (tele_sub Θ' (Id,,N)) A[τ ⨟ sb_qn (List.length Θ') (Id,,N)] M[τ ⨟ sb_qn (List.length Θ') (Id,,N)] Rm')
          | inr _ => Some Rm'
          end
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
Fixpoint ds_sub (R : mdesc) (σ : sub) : mdesc :=
  match R with
  | ds_term A om => ds_term A[σ] (option_map (fun M => M[σ]) om)
  | ds_open Δ Φ Φx => ds_open (tele_sub Δ σ) (gmod_sub Φ (sb_qn (List.length Δ) σ)) (gmod_sub Φx (sb_qn (List.length Δ) σ))
  | ds_closed Θ p T Φ Ns => ds_closed (tele_sub Θ σ) p T Φ (List.map (fun M => M[sb_qn (List.length Θ) σ]) Ns)
  | ds_dm Θd A M Rm => ds_dm (tele_sub Θd σ) A[sb_qn (List.length Θd) σ] M[sb_qn (List.length Θd) σ] (ds_sub Rm σ)
  end.

(** The entries of a local body before a member, filled in: the
    substitution sending each of them to its value, a definition to its body,
    a module to its unit and a definition with a module part to both, the
    entries before it filled in.  An entry with no value (a definition
    without a body) cannot be filled in. *)
Fixpoint gm_fill (Φ : gmod) : option sub :=
  match Φ with
  | gm_nil => Some Id
  | gm_ext Φ' _ (ge_def _ _ _ (Some M)) => option_map (fun σ => σ ,, M[σ]) (gm_fill Φ')
  | gm_ext Φ' _ (ge_mod _ U) => option_map (fun σ => σ ,,ₘ me_lit U[σ]ᵘ) (gm_fill Φ')
  | gm_ext Φ' _ (ge_def_mod _ _ M U) => option_map (fun σ => σ ,,ᵈ M[σ] ‖ me_lit U[σ]ᵘ) (gm_fill Φ')
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

(** Whether a term is a type former, an inductive's or a record's,
    applied. *)
Fixpoint app_const (M : exp) : bool :=
  match M with
  | a_ind _ _ | a_record _ => true
  | a_app M _ => app_const M
  | _ => false
  end.

(** The term part of a description given the argument [N]: by [β] when
    its body is a [λ], as [ds_at]; a type former applied, applied to [N]
    (see [ds_ats_read]). *)
Definition ds_at_tm (R : mdesc) (N : exp) : option mdesc :=
  match R with
  | ds_term A (Some M) =>
      match pi_view A with
      | Some (_, C) =>
          match fn_view M with
          | Some M' => Some (ds_term C[Id,,N] (Some M'[Id,,N]))
          | None => if app_const M then Some (ds_term C[Id,,N] (Some (a_app M N))) else None
          end
      | None => None
      end
  | _ => ds_at R N
  end.

(** [ds_at_tm] at [N₁ … Nₖ]. *)
Fixpoint ds_ats_tm (R : mdesc) (Ns : list exp) : option mdesc :=
  match Ns with
  | nil => Some R
  | N :: Ns' =>
      match ds_at_tm R N with
      | Some R' => ds_ats_tm R' Ns'
      | None => None
      end
  end.

(** An entry's description given the arguments of the closed module it is
    a member of, which are those of the frames it is filed in: as applied
    ([ds_ats]), but a definition with a module part, or a type former,
    with no outside parameter is given them in both its parts: its term
    part as a transparent definition is ([ds_term A (Some M)]), its module
    part as a module is.  So [F 3 .K], for a def-mod [K] filed in
    [module F (n : ℕ)], is K's term at [3] as well as its module at [3];
    an application [K N] as a module, past the frames' arguments, is its
    module part only ([ds_at]).

    The term part is given each argument by [ds_at_tm]: as [ds_at] does,
    by [β], when its body is a [λ], and otherwise, when its body is a type
    former applied ([app_const]), by applying it to the argument.  The
    second step is stable: it runs only at a filed entry's frame
    arguments, where the entry's coherence ([gm_coh]) makes a definition's
    body a [ctx_fn] over the frames' parameters, and where a type former's
    term part ([ind_former_desc], [record_former_desc]) is the closed
    constant [a_ind pq k] or [a_record p], applied: no substitution makes
    it a [λ] ([app_const] is kept by substitution).  So [F 3 .K] is [K]'s
    body at [3], and [P ℕ .N], for an inductive [N] filed in
    [module P (A : Type@0)], is [N ℕ]. *)
Definition ds_ats_read (R : mdesc) (Ns : list exp) : option mdesc :=
  match R with
  | ds_dm nil A M Rm =>
      match ds_ats_tm (ds_term A (Some M)) Ns, ds_ats Rm Ns with
      | Some (ds_term B (Some M')), Some Rm' => Some (ds_dm nil B M' Rm')
      | _, _ => None
      end
  | _ => ds_ats R Ns
  end.

(** [H : (the [ds_dm nil] case of [ds_ats_read]) = Some R]: [R] is a
    [ds_dm nil] of the two parts given the arguments. *)
Ltac ds_dm_read_shape H :=
  match type of H with
  | context [ds_ats_tm ?R ?Ns] => destruct (ds_ats_tm R Ns) as [[? [?|] | | |] |]; cbn in H; try discriminate H
  end;
  match type of H with
  | context [ds_ats ?R ?Ns] => destruct (ds_ats R Ns); cbn in H; [ injection H as <- | discriminate H ]
  end.

(** [ds_ats_read] is [ds_ats], but on a definition with a module part and
    no outside parameter, given the arguments in both its parts. *)
Lemma ds_ats_read_inv : forall R Ns R', ds_ats_read R Ns = Some R' ->
    ds_ats R Ns = Some R' \/
    exists A M Rm B M' Rm', R = ds_dm nil A M Rm /\ R' = ds_dm nil B M' Rm' /\
      ds_ats_tm (ds_term A (Some M)) Ns = Some (ds_term B (Some M')) /\ ds_ats Rm Ns = Some Rm'.
Proof.
  intros [| | | [| e Θd] A M Rm] Ns R' Ha; cbn [ds_ats_read] in Ha; try (left; exact Ha).
  right; destruct (ds_ats_tm (ds_term A (Some M)) Ns) as [[B [M' |] | | |] |] eqn:Et; try discriminate.
  destruct (ds_ats Rm Ns) as [Rm' |] eqn:E; [| discriminate ]; injection Ha as <-.
  do 6 eexists; split; [ reflexivity | split; [ reflexivity | split; [ exact Et | exact E ] ] ].
Qed.

(** At no argument, [ds_ats_read] reads the description as it is. *)
Lemma ds_ats_read_nil : forall R, ds_ats_read R nil = Some R.
Proof. intros [| | | [| e Θd] A M Rm]; reflexivity. Qed.

(** On anything but a definition with a module part, [ds_ats_read] is
    [ds_ats]. *)
Lemma ds_ats_read_other : forall R Ns, (forall Θd A M Rm, R <> ds_dm Θd A M Rm) -> ds_ats_read R Ns = ds_ats R Ns.
Proof. intros [| | | Θd A M Rm] Ns Hn; try reflexivity; exfalso; eapply Hn; reflexivity. Qed.

(** On a module, [ds_ats_read] is [ds_ats]. *)
Lemma ds_ats_read_mod : forall R Ns, ds_is_mod R -> ds_ats_read R Ns = ds_ats R Ns.
Proof. intros [| | |] Ns Hm; cbn in Hm; first [ contradiction | reflexivity ]. Qed.

(** How an entry's description is read: one of an open body, the entries
    before it [Φ'] filled in, abstracted over the body's parameters [Δ]; one
    of a closed body, given the arguments recorded ([ds_ats_read]), a term
    with no δ-reduct being its name [M] there ([ds_named]), then abstracted
    over the outside parameters. *)
Definition ds_read (rd : reader) (R : mdesc) : option mdesc :=
  match rd with
  | rd_open Δ Φ' => option_map (fun σ => ds_up Δ (ds_sub R σ)) (gm_fill Φ')
  | rd_closed Θ Ns M => option_map (fun R1 => ds_up Θ (ds_named Θ Ns M R1)) (ds_ats_read R Ns)
  end.

(** A term read as a name is a term. *)
Lemma ds_named_term : forall Θ Ns M A om, exists om', ds_named Θ Ns M (ds_term A om) = ds_term A om'.
Proof. intros [|] [|] * ; destruct om; cbn; eexists; reflexivity. Qed.

Lemma ds_mod_named_term : forall Δ Θ Ns M A om, ds_mod (ds_up Δ (ds_named Θ Ns M (ds_term A om))) = None.
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
              is not read.  A transparent local definition is read, and so
              is a local definition with a module part; an abstract
              definition, and one without a body, are not: they are used
              only inside the body, as its definitions there. *)
          | ge_ind _ _ _ _ _ | ge_record _ _ _ _ | ge_def _ _ _ None | ge_def false _ _ _ => None
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

(** The type former of member [k] of the group [D] declared at [pq], of
    its type, with the module part [Rm]; read at the frames' arguments
    ([ds_ats_read]), it is the type former at them. *)
Definition ind_former_desc (pq : qname) (k : nat) (D : ind_decl) (Mk : imember) (Rm : mdesc) : mdesc :=
  ds_dm nil (ctx_pi (im_params D Mk) (exp_wk (ind_sort D) (wk_shiftn (im_nn Mk)))) (a_ind pq k) Rm.

(** The type former of the record type [R] declared at [p], of its type,
    with the module part [Rm]. *)
Definition record_former_desc (p : qname) (R : record_decl) (Rm : mdesc) : mdesc :=
  ds_dm nil (ctx_pi (record_params R) (record_sort R)) (a_record p) Rm.

(** The stored unit a path [P] names when it is a loaded unit or an open
    frame, with its full telescope: an open frame's own parameters, then
    those of the frames outside it.  The open frame of the module of a
    member of a group, or of a record type, is not one: its path names the
    member ([dn_ind_frame]) or the record type ([dn_record_frame]). *)
Definition gc_unit (Θ : gdeps) (Ξ : gstack) (H : modexp) : option (ctx * gmod) :=
  match mod_qname H with
  | Some mp =>
      match gs_find_tele Ξ mp with
      | Some (U, nil, T0) =>
          match U, gs_find_ind Ξ mp, gs_find_record Ξ mp with
          | gu_mk Δ (md_body sm_closed Φ), None, None => Some (Δ ++ T0, Φ)
          | _, _, _ => None
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
  destruct E as [b pv A B | ? [Δ [? Φ' | E']] | ? ? ? D Φ' | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr Φ']; try discriminate.
  - destruct ip as [| z ip']; [ reflexivity |].
    eapply IH; exact H.
  - destruct ip; reflexivity.
  - destruct ip as [| z ip']; [ reflexivity |].
    eapply IH; exact H.
  - destruct ip; reflexivity.
  - destruct ip as [| z ip']; [ reflexivity |].
    eapply IH; exact H.
Qed.

Lemma gc_module_resolve : forall Θ Ξ p r,
    gc_module Θ Ξ p = Some r -> gc_resolve Θ Ξ p = None.
Proof.
  intros * H; unfold gc_module, gc_module_u, gc_resolve, gc_resolve_u in *; rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[U [| x ip]] T] |]; cbn; [ discriminate | eapply gm_submodule_resolve; exact H |].
  destruct (gds_lookup Θ (q_unit p)); [| discriminate ].
  destruct (q_chain p) as [| x ip]; cbn in *; [ destruct (gu_mod g); reflexivity || apply gm_resolve_nil | eapply gm_submodule_resolve; exact H ].
Qed.

(** The path of a member's module, open or filed, names no definition. *)
Lemma ind_mlookup_resolve : forall Θ Ξ p r,
    ind_mlookup Θ Ξ p = Some r -> gc_resolve Θ Ξ p = None.
Proof.
  intros * H; destruct (ind_mlookup_module _ _ _ _ H) as [[T Hm] | Hk]; [ exact (gc_module_resolve _ _ _ _ Hm) |].
  destruct (gs_find_ind_tele _ _ _ Hk) as (U & T & Ht).
  unfold gc_resolve, gc_resolve_u; rewrite gs_find_tele_find, Ht; cbn; apply gm_resolve_nil.
Qed.

(** ** What an Open Generates

    [open E use (n)] declares [n] as a private definition equal to [E.n],
    [open E as y] declares [y] a private alias of [E], and, at the global
    level, an item naming a type former (an inductive or a record type),
    and [open E as y] of one, declares a definition with a module part of
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
(** [ig_def_mod d pv A M E]: the definition [d] of type [A] equal to [M],
    with the module part the alias of [E].  A global open files it at its
    inferred type ([gr_def_mod]) *)
| ig_def_mod : string -> bool -> typ -> exp -> modexp -> igen.

(** A generated item as a body entry. *)
Definition ig_entry (g : igen) : (string * gentry)%type :=
  match g with
  | ig_def d pv A M => (d, ge_def true pv A (Some M))
  | ig_alias d pv E => (d, ge_mod pv (gu_mk nil (md_alias E)))
  | ig_def_mod d pv A M E => (d, ge_def_mod pv A M (gu_mk nil (md_alias E)))
  end.

Definition ig_name (g : igen) : string := fst (ig_entry g).

(** A generated item under a weakening and a substitution, as its entry
    is ([ig_entry_wk], [ig_entry_sub]). *)
Definition igen_wk (g : igen) (φ : wk) : igen :=
  match g with
  | ig_def d pv A M => ig_def d pv A[φ]ʷ M[φ]ʷ
  | ig_alias d pv E => ig_alias d pv (modexp_wk E φ)
  | ig_def_mod d pv A M E => ig_def_mod d pv A[φ]ʷ M[φ]ʷ (modexp_wk E φ)
  end.

(** The substitution counterpart of [igen_wk]. *)
Definition igen_sub (g : igen) (σ : sub) : igen :=
  match g with
  | ig_def d pv A M => ig_def d pv A[σ] M[σ]
  | ig_alias d pv E => ig_alias d pv E[σ]ᵐ
  | ig_def_mod d pv A M E => ig_def_mod d pv A[σ] M[σ] E[σ]ᵐ
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

    [edenote Θ Ξ Γ o E R], [Γ ⊢ E denotes R]: what an entry stored at
    [o] denotes, one rule per entry kind.  A definition is a term of its
    type, whose δ-reduct is its body when it is transparent; a module is
    what its unit denotes; an inductive or a record type is its type
    former with its module; a definition with a module part, its term
    with what its unit denotes as its module part. *)
Inductive mdenote (Θ : gdeps) (Ξ : gstack) : ctx -> modexp -> mdesc -> Prop :=
(** A loaded unit or open frame: its stored closed unit, at its path *)
| dn_unit : forall Γ H p T Φ,
    mod_qname H = Some p ->
    gc_unit Θ Ξ H = Some (T, Φ) ->
    mdenote Θ Ξ Γ H (ds_closed nil p T Φ nil)
(** The open frame of the module of a member of a group of inductive
    types: the member's type former, as it is read once filed there
    ([en_ind]), of the declaration the frame carries, whose module part is
    the frame's body so far; the member is filed only when the frame
    closes, so it is denoted so nowhere else *)
| dn_ind_frame : forall Γ H p pq k D Mk Tm Φm,
    mod_qname H = Some p ->
    gs_find_ind Ξ p = Some (pq, k, D) ->
    ind_member D k = Some Mk ->
    gc_loc Θ Ξ p = Some (Tm, Φm) ->
    mdenote Θ Ξ Γ H (ind_former_desc pq k D Mk (ds_closed nil p Tm Φm nil))
(** A module slot: what its unit denotes *)
| dn_slot : forall Γ x U R,
    Γ ∋ #x ≔ₘ U ->
    udenote Θ Ξ Γ None U R ->
    mdenote Θ Ξ Γ (me_var x) R
(** A module literal: what its unit denotes *)
| dn_lit : forall Γ U R,
    udenote Θ Ξ Γ None U R ->
    mdenote Θ Ξ Γ (me_lit U) R
(** An application: the head's description given the next argument *)
| dn_app : forall Γ H N R R',
    mdenote Θ Ξ Γ H R ->
    ds_at R N = Some R' ->
    mdenote Θ Ξ Γ (me_app H N) R'
(** A selection: the entry found in the module part of the selected
    module's description, denoted and read there *)
| dn_mem : forall Γ H y R0 R0m Γy E rd R R',
    mdenote Θ Ξ Γ H R0 ->
    ds_mod R0 = Some R0m ->
    ds_entry R0m y = Some (Γy, E, rd) ->
    edenote Θ Ξ (Γy ++ Γ) (ds_epath R0m y) E R ->
    ds_read rd R = Some R' ->
    mdenote Θ Ξ Γ (me_mem H y) R'
(** The open frame of the module of a record type: the record's type
    former, as it is read once filed there ([en_record]), whose module
    part is the frame's body so far; the record is filed only when the
    frame closes, so it is denoted so nowhere else *)
| dn_record_frame : forall Γ H p R Tm Φm,
    mod_qname H = Some p ->
    gs_find_record Ξ p = Some R ->
    gc_loc Θ Ξ p = Some (Tm, Φm) ->
    mdenote Θ Ξ Γ H (record_former_desc p R (ds_closed nil p Tm Φm nil))
with udenote (Θ : gdeps) (Ξ : gstack) : ctx -> option qname -> gunit -> mdesc -> Prop :=
(** A body, read through the entries its local opens generate, by its
    storage *)
| un_body : forall Γ o Δ sm Φ Φx R,
    body_xp Θ Ξ (Δ ++ Γ) Φ Φx ->
    ds_body o sm Δ Φ Φx = Some R ->
    udenote Θ Ξ Γ o (gu_mk Δ (md_body sm Φ)) R
(** An alias: the module part of what its target denotes, abstracted over
    the alias's parameters *)
| un_alias : forall Γ o Δ E R R',
    mdenote Θ Ξ (Δ ++ Γ) E R ->
    ds_mod R = Some R' ->
    udenote Θ Ξ Γ o (gu_mk Δ (md_alias E)) (ds_up Δ R')
with edenote (Θ : gdeps) (Ξ : gstack) : ctx -> option qname -> gentry -> mdesc -> Prop :=
(** A definition: a term of its type, with its body as δ-reduct when it is
    transparent *)
| en_def : forall Γ o b pv A oM,
    edenote Θ Ξ Γ o (ge_def b pv A oM) (ds_term A (if b then oM else None))
(** A module: what its unit denotes *)
| en_mod : forall Γ o pv U R,
    udenote Θ Ξ Γ o U R ->
    edenote Θ Ξ Γ o (ge_mod pv U) R
(** An inductive member: its type former ([ind_former_desc]), whose module
    part is the member's module, stored at its path.  The declaration is
    the one the entry stores, not one looked up again by path; the two
    agree in a well-formed context. *)
| en_ind : forall Γ o pv pq k D Φ Mk pm Tm Φm,
    ind_member D k = Some Mk ->
    ind_mpath D k = Some pm ->
    gc_loc Θ Ξ pm = Some (Tm, Φm) ->
    edenote Θ Ξ Γ o (ge_ind pv pq k D Φ) (ind_former_desc pq k D Mk (ds_closed nil pm Tm Φm nil))
(** A definition with a module part: its term, a transparent
    definition's, with what its unit, an alias, denotes as its module
    part.  A module part that is no alias denotes nothing, as it is no
    module ([gm_submodule]). *)
| en_def_mod : forall Γ o pv A M Δ E Rm,
    udenote Θ Ξ Γ o (gu_mk Δ (md_alias E)) Rm ->
    edenote Θ Ξ Γ o (ge_def_mod pv A M (gu_mk Δ (md_alias E))) (ds_dm nil A M Rm)
(** A record type stored at [p]: its type former ([record_former_desc]),
    whose module part is its module, stored at [p].  It denotes only where
    it is stored, read at the path it is found at *)
| en_record : forall Γ p pv pr R Φ Tm Φm,
    gc_loc Θ Ξ p = Some (Tm, Φm) ->
    edenote Θ Ξ Γ (Some p) (ge_record pv pr R Φ) (record_former_desc p R (ds_closed nil p Tm Φm nil))
(** [body_xp Θ Ξ Γ Φ Φx]: the body [Φ], read in [Γ], is [Φx] with every
    local open replaced by the entries it generates ([items_gen]), in the
    context its own expanded prefix makes.  The entries themselves are not
    looked into. *)
with body_xp (Θ : gdeps) (Ξ : gstack) : ctx -> gmod -> gmod -> Prop :=
(** The empty body expands to itself *)
| bx_nil : forall Γ, body_xp Θ Ξ Γ gm_nil gm_nil
(** An entry is kept as it is *)
| bx_ext : forall Γ Φ Φx x E,
    body_xp Θ Ξ Γ Φ Φx ->
    body_xp Θ Ξ Γ (gm_ext Φ x E) (gm_ext Φx x E)
(** A local open of a module is replaced by the entries its items
    generate *)
| bx_open : forall Γ Φ Φx H its R Rm gs,
    body_xp Θ Ξ Γ Φ Φx ->
    mdenote Θ Ξ (body_ctx Φx ++ Γ) H R ->
    ds_mod R = Some Rm ->
    items_gen Θ Ξ (body_ctx Φx ++ Γ) H its gs ->
    items_ok its ->
    body_xp Θ Ξ Γ (gm_open Φ H its) (gens_append Φx 0 gs)
(** [items_gen Θ Ξ Γ H its gs]: what the items [its] of an open of [H]
    declare, all read in [Γ], by what the member each names denotes: a term
    gives a definition of its type, a module an alias, and a member with
    both a term part and a module part a definition with a module part; an
    item naming no member, the alias of [H] itself, whatever [H] is.  A
    global open and a local one generate alike. *)
with items_gen (Θ : gdeps) (Ξ : gstack) : ctx -> modexp -> list iitem -> list igen -> Prop :=
(** No item generates nothing *)
| ign_nil : forall Γ H, items_gen Θ Ξ Γ H nil nil
(** An item naming no member ([open E as y]): the alias of [H] itself,
    whatever [H] is *)
| ign_self : forall Γ H d pv its gs,
    items_gen Θ Ξ Γ H its gs ->
    items_gen Θ Ξ Γ H ((None, d, pv) :: its) (ig_alias d pv H :: gs)
(** An item naming a term: a definition of its type, by selection *)
| ign_def : forall Γ H n d pv A om its gs,
    mdenote Θ Ξ Γ (me_mem H n) (ds_term A om) ->
    items_gen Θ Ξ Γ H its gs ->
    items_gen Θ Ξ Γ H ((Some n, d, pv) :: its) (ig_def d pv A (a_mem H n) :: gs)
(** An item naming a module: an alias of the selection *)
| ign_mod : forall Γ H n d pv R its gs,
    mdenote Θ Ξ Γ (me_mem H n) R ->
    ds_is_mod R ->
    items_gen Θ Ξ Γ H its gs ->
    items_gen Θ Ξ Γ H ((Some n, d, pv) :: its) (ig_alias d pv (me_mem H n) :: gs)
(** An item naming a member with both a term part and a module part (a
    type former, or a definition with a module part): a definition with a
    module part of the term part's type, the selection as its term and the
    alias of the selection as its module *)
| ign_dm : forall Γ H n d pv R A Rm its gs,
    mdenote Θ Ξ Γ (me_mem H n) R ->
    ds_ty R = Some A ->
    ds_mod R = Some Rm ->
    items_gen Θ Ξ Γ H its gs ->
    items_gen Θ Ξ Γ H ((Some n, d, pv) :: its) (ig_def_mod d pv A (a_mem H n) (me_mem H n) :: gs).

Scheme mdenote_mut_ind := Induction for mdenote Sort Prop
with udenote_mut_ind := Induction for udenote Sort Prop
with edenote_mut_ind := Induction for edenote Sort Prop
with body_xp_mut_ind := Induction for body_xp Sort Prop
with items_gen_mut_ind := Induction for items_gen Sort Prop.
Combined Scheme mdenote_all_ind from mdenote_mut_ind, udenote_mut_ind, edenote_mut_ind, body_xp_mut_ind, items_gen_mut_ind.

#[export]
Hint Constructors mdenote udenote edenote body_xp items_gen : mctt.


(** [open_gens Θ Ξ Γ H its gs]: an open of [H] with items [its], in [Γ]:
    [H] is a module, and [gs] is what the items declare.  (Its witnesses
    are informative, so they have no projections.) *)
#[warnings="-cannot-define-projection"]
Record open_gens (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) (its : list iitem) (gs : list igen) : Prop :=
  mk_open_gens
  { og_desc : mdesc
  ; og_mod : mdesc
  ; og_denote : mdenote Θ Ξ Γ H og_desc
  ; og_is_mod : ds_mod og_desc = Some og_mod
  ; og_items : items_gen Θ Ξ Γ H its gs
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

Lemma items_gen_length : forall Θ Ξ Γ H its gs, items_gen Θ Ξ Γ H its gs -> List.length gs = List.length its.
Proof. induction 1; cbn; auto. Qed.

Lemma items_gen_names : forall Θ Ξ Γ H its gs, items_gen Θ Ξ Γ H its gs -> List.map ig_name gs = List.map iitem_name its.
Proof. induction 1; cbn; f_equal; auto. Qed.

(** The context an open's entries make, over the body before it. *)
Lemma gens_body_ctx_base : forall gs Φ k,
    body_ctx (gens_append Φ k gs) = body_ctx (gens_append gm_nil k gs) ++ body_ctx Φ.
Proof.
  induction gs as [| g gs IH]; intros; cbn [gens_append]; [ reflexivity |].
  destruct (ig_entry g) as [d E].
  rewrite IH, (IH (gm_ext gm_nil d _)), <- List.app_assoc.
  destruct E as [? ? ? [] | | | |]; reflexivity.
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

Lemma body_opens_open : forall Θ Ξ Γ Φ Φx H its gs,
    items_gen Θ Ξ Γ H its gs ->
    body_opens (gm_open Φ H its) (gens_append Φx 0 gs) = (body_ctx Φx, H) :: body_opens Φ Φx.
Proof.
  intros * Hg; cbn; erewrite <- items_gen_length by eassumption; rewrite gm_dropn_gens_append; reflexivity.
Qed.

Lemma body_opens_at_open_len : forall Φ Φx H its gs, List.length gs = List.length its ->
    body_opens_at (gm_open Φ H its) (gens_append Φx 0 gs) = (Φx, H) :: body_opens_at Φ Φx.
Proof. intros * Hl; cbn; rewrite <- Hl, gm_dropn_gens_append; reflexivity. Qed.

Lemma body_opens_at_open : forall Θ Ξ Γ Φ Φx H its gs,
    items_gen Θ Ξ Γ H its gs ->
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
  - rewrite <- (items_gen_length _ _ _ _ _ _ Hg), gm_dropn_gens_append.
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
  | ge_mod _ (gu_mk _ (md_body _ _)) | ge_ind _ _ _ _ _ | ge_record _ _ _ _ => True
  | _ => False
  end.

(** The target of an alias entry, as a module: that of a definition with a
    module part's alias. *)
Definition entry_alias (E : gentry) : option modexp :=
  match E with
  | ge_mod _ (gu_mk _ (md_alias E')) => Some E'
  | ge_def_mod _ _ _ (gu_mk _ (md_alias E')) => Some E'
  | _ => None
  end.

Inductive msite (Θ : gdeps) (Ξ : gstack) : modexp -> qname -> Prop :=
(** A loaded unit or an open frame *)
| ms_unit : forall H p T Φ,
    mod_qname H = Some p ->
    gc_unit Θ Ξ H = Some (T, Φ) ->
    msite Θ Ξ H p
(** The open frame of the module of a member of a group *)
| ms_ind_frame : forall H p r,
    mod_qname H = Some p ->
    gs_find_ind Ξ p = Some r ->
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
    msite Θ Ξ (me_app H N) pq
(** The open frame of the module of a record type *)
| ms_record_frame : forall H p R,
    mod_qname H = Some p ->
    gs_find_record Ξ p = Some R ->
    msite Θ Ξ H p.

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


Lemma gm_subbody_module : forall Φ T x ip T' Φ',
    gm_subbody T Φ x ip = Some (T', Φ') -> exists oD, gm_submodule T Φ x ip = Some (mr_body T' oD).
Proof.
  fix IH 1; intros [| Φ y E | Φ c] * H; cbn in H |- *; [ discriminate | | exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H) ].
  destruct E as [? ? ? ? | ? [Δ [? Φ0 | E0]] | ? ? ? D0 Φ0 | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr Φ0]; try discriminate;
    destruct ip as [| z ip]; first [ injection H as <- <-; eexists; reflexivity | exact (IH _ _ _ _ _ _ H) ].
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

(** An entry a path resolves to is the entry stored there. *)
Lemma gm_resolve_entry : forall ip Φ E, gm_resolve Φ ip = Some E -> gm_entry Φ ip = Some E.
Proof.
  induction ip as [| x ip IH]; intros Φ; induction Φ as [| Φ IHΦ y E0 | Φ IHΦ H its]; intros E Hr; cbn in *;
    try discriminate; try (apply IHΦ; exact Hr).
  destruct (String.eqb x y); [| apply IHΦ; exact Hr ].
  destruct ip as [| x' ip'];
    destruct E0 as [b pv A B | pv [Δ [sm Φ' | E']] | pv pq k D Φ' | pv A M U | pv pr R Φ'];
    try discriminate; try exact Hr; apply IH; exact Hr.
Qed.

Lemma gc_resolve_entry : forall Θ Ξ p E, gc_resolve Θ Ξ p = Some E -> gc_entry Θ Ξ p = Some E.
Proof.
  intros * Hr; unfold gc_resolve, gc_resolve_u, gc_entry, gc_entry_u in *.
  destruct (gs_find Ξ p) as [[U ip] |]; [ exact (gm_resolve_entry _ _ _ Hr) |].
  destruct (gds_lookup Θ (q_unit p)); [ exact (gm_resolve_entry _ _ _ Hr) | discriminate ].
Qed.

(** A path resolving to a definition names no member with a term part and
    a module part. *)
Lemma gc_resolve_def_not_dm : forall Θ Ξ p b pv A B, gc_resolve Θ Ξ p = Some (ge_def b pv A B) -> ~ dm_path Θ Ξ p.
Proof.
  intros * Hr [(r & Hi) | [(R & Hl) | (pv' & A' & M' & U & He)]].
  - destruct (ind_mlookup_module _ _ _ _ Hi) as [(T & Hm) | Hf].
    + rewrite (gc_module_resolve _ _ _ _ Hm) in Hr; discriminate.
    + destruct (gs_find_ind_tele _ _ _ Hf) as (U & T & Ht).
      unfold gc_resolve, gc_resolve_u in Hr; rewrite gs_find_tele_find, Ht in Hr; cbn in Hr.
      rewrite gm_resolve_nil in Hr; discriminate.
  - unfold record_lookup in Hl; destruct (gs_find_record Ξ p) as [R0 |] eqn:Hf.
    + destruct (gs_find_record_tele _ _ _ Hf) as (U & T & Ht).
      unfold gc_resolve, gc_resolve_u in Hr; rewrite gs_find_tele_find, Ht in Hr; cbn in Hr.
      rewrite gm_resolve_nil in Hr; discriminate.
    + rewrite (gc_resolve_entry _ _ _ _ Hr) in Hl; discriminate.
  - rewrite (gc_resolve_entry _ _ _ _ Hr) in He; discriminate.
Qed.

(** The term part a path is selected as: the body of a transparent
    definition it resolves to, or the term of a definition with a module
    part stored there, which resolves to nothing. *)
Lemma gc_term_inv : forall Θ Ξ p M, gc_term Θ Ξ p = Some M ->
    (exists pv A, gc_resolve Θ Ξ p = Some (ge_def true pv A (Some M))) \/
    (exists pv A U, gc_entry Θ Ξ p = Some (ge_def_mod pv A M U)).
Proof.
  intros * Ht; unfold gc_term in Ht.
  destruct (gc_resolve Θ Ξ p) as [E |] eqn:Er.
  - destruct E as [[] pv A [M' |] | | | |];
      try (injection Ht as <-; left; eauto; fail);
      rewrite (gc_resolve_entry _ _ _ _ Er) in Ht; cbn in Ht;
      first [ discriminate | injection Ht as <-; right; do 3 eexists; exact (gc_resolve_entry _ _ _ _ Er) ].
  - destruct (gc_entry Θ Ξ p) as [[| | | pv A M' U |] |]; try discriminate.
    injection Ht as <-; right; eauto.
Qed.

(** A path resolving to a transparent definition is selected as its body. *)
Lemma gc_term_of_resolve : forall Θ Ξ p pv A M,
    gc_resolve Θ Ξ p = Some (ge_def true pv A (Some M)) -> gc_term Θ Ξ p = Some M.
Proof. intros * Hr; unfold gc_term; rewrite Hr; reflexivity. Qed.

(** A path storing a definition with a module part is selected as its term. *)
Lemma gc_term_of_def_mod : forall Θ Ξ p pv A M U,
    gc_entry Θ Ξ p = Some (ge_def_mod pv A M U) -> gc_term Θ Ξ p = Some M.
Proof.
  intros * He; unfold gc_term.
  destruct (gc_resolve Θ Ξ p) as [E |] eqn:Hr; [| rewrite He; reflexivity ].
  destruct E as [[|] pv' A' [M' |] | | | |]; try (rewrite He; reflexivity).
  exfalso; apply (gc_resolve_def_not_dm _ _ _ _ _ _ _ Hr); right; right; do 4 eexists; exact He.
Qed.

(** What a term entry stored at [o] describes as a term: a definition; a
    type former, the term part of its [ind_former_desc] or
    [record_former_desc]; a definition with a module part, its term part,
    read as a transparent definition is.  A record entry stores no path,
    so it describes its type former only where it is stored. *)
Definition entry_term (o : option qname) (E : gentry) : option mdesc :=
  match E with
  | ge_def b _ A oM => Some (ds_term A (if b then oM else None))
  | ge_ind _ pq k D _ =>
      option_map (fun Mk => ds_term (ctx_pi (im_params D Mk) (exp_wk (ind_sort D) (wk_shiftn (im_nn Mk)))) (Some (a_ind pq k)))
        (ind_member D k)
  | ge_def_mod _ A M _ => Some (ds_term A (Some M))
  | ge_mod _ _ => None
  | ge_record _ _ R _ => option_map (fun p => ds_term (ctx_pi (record_params R) (record_sort R)) (Some (a_record p))) o
  end.

(** A stored alias entry as the alias unit it is, over its full telescope:
    a definition with a module part as its module part. *)
Definition entry_alias_unit (E : gentry) : option gunit :=
  match E with
  | ge_mod _ (gu_mk Ta (md_alias E')) => Some (gu_mk Ta (md_alias E'))
  | ge_def_mod _ _ _ (gu_mk Ta (md_alias E')) => Some (gu_mk Ta (md_alias E'))
  | _ => None
  end.

(** A unit of the context after a body's parameters, abstracted over them. *)
Definition gunit_abs (Δ : ctx) (U : gunit) : gunit :=
  match U with
  | gu_mk Δy D => gu_mk (Δy ++ Δ) D
  end.


