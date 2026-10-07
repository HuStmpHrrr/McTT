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
               | _ :: _, ge_mod _ (gu_mk _ (md_body Φ')) => gm_resolve Φ' ip'
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
  | gm_open Φ0 _ _ => gm_submodule T Φ0 x ip
  | gm_ext Φ0 y E =>
      if String.eqb x y then
        match E with
        | ge_mod _ (gu_mk Δ (md_body Φ')) =>
            match ip with
            | nil => Some (mr_body (Δ ++ T))
            | z :: ip' => gm_submodule (Δ ++ T) Φ' z ip'
            end
        | ge_mod _ (gu_mk Δ (md_alias E')) => Some (mr_alias (gu_mk Δ (md_alias E')) ip)
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
      | Some U => gm_module (gu_params U) (gu_mod U) (q_chain p)
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

(** ** How Resolution Grows

    Every way a global context grows preserves what resolves, both definitions
    and modules: this is the whole of what moving a judgment from one global
    context to a bigger one needs. *)
Definition gc_sub (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  (forall p E, gc_resolve Θ1 Ξ1 p = Some E -> gc_resolve Θ2 Ξ2 p = Some E) /\
  (forall p r, gc_module Θ1 Ξ1 p = Some r -> gc_module Θ2 Ξ2 p = Some r) /\
  (** Growth never adds to a closed module: a body module keeps its body. *)
  (forall p r, gc_body Θ1 Ξ1 p = Some r -> gc_body Θ2 Ξ2 p = Some r).

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
Definition frame_fresh (Θ : gdeps) (Ξ : gstack) (mp : qname) : Prop :=
  match Ξ with
  | nil => gds_lookup Θ (q_unit mp) = None /\ q_chain mp = nil
  | (mq, U) :: _ => exists x, mp = qname_in mq x /\ gm_fresh x (gu_mod U)
  end.

Lemma gc_sub_push : forall Θ Ξ mp U,
    frame_fresh Θ Ξ mp ->
    gc_sub Θ Ξ Θ ((mp, U) :: Ξ).
Proof.
  intros * Hf; split; [| split ].
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
  - intros p r Hr; unfold gc_body in *; cbn.
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
      exact (Hx (gm_subbody_head _ _ _ _ _ Hr)).
Qed.

Lemma gc_sub_grow : forall Θ Ξ mp Δ Φ x E,
    gm_fresh x Φ ->
    gc_sub Θ ((mp, gu_body Δ Φ) :: Ξ) Θ ((mp, gu_body Δ (Φ ⊳ x ↦ E)) :: Ξ).
Proof.
  intros * Hf; split; [| split ].
  - intros p E0 Hr; unfold gc_resolve in *; cbn in *.
    destruct (qname_strip mp p); [ cbn in *; apply gm_resolve_ext_fresh; assumption | exact Hr ].
  - intros p r Hr; unfold gc_module in *; cbn in *.
    destruct (qname_strip mp p) as [[| y ip] |]; [ discriminate | | exact Hr ].
    cbn in *; apply gm_submodule_ext_fresh; assumption.
  - intros p r Hr; unfold gc_body in *; cbn in *.
    destruct (qname_strip mp p) as [[| y ip] |]; [ discriminate | | exact Hr ].
    cbn in *; apply gm_subbody_ext_fresh; assumption.
Qed.

(** Filing a unit: what was read in its open frame is read in the filed
    unit. *)
Lemma gc_sub_file : forall Θ fp U,
    gds_lookup Θ fp = None ->
    gc_sub Θ ((q_abs fp nil, U) :: nil) ((fp, U) :: Θ) nil.
Proof.
  intros * Hn; split; [| split ].
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
  - intros p r Hr; unfold gc_body in *; cbn [gs_find_tele] in *.
    unfold qname_strip in Hr; cbn [q_unit q_chain strip_prefix] in Hr; cbn [gds_lookup].
    destruct (path_beq fp (q_unit p)) eqn:Hb.
    + apply path_beq_true in Hb; subst; rewrite path_beq_refl.
      destruct (q_chain p) as [| x ip] eqn:Hp; [ discriminate |].
      cbn in *; rewrite List.app_nil_r in Hr; exact Hr.
    + destruct (path_beq (q_unit p) fp) eqn:Hb'; [ apply path_beq_true in Hb'; subst; rewrite path_beq_refl in Hb; discriminate | exact Hr ].
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
  intros * Hs; split; [| split ].
  - intros p E Hr; unfold gc_resolve in *.
    destruct (gs_find Ξ p) as [[U ip] |]; [ exact Hr |].
    destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:E1; [| discriminate ].
    rewrite (Hs _ _ E1); exact Hr.
  - intros p r Hr; unfold gc_module in *.
    destruct (gs_find_tele Ξ p) as [[[U ip] T] |]; [ exact Hr |].
    destruct (gds_lookup Θ (q_unit p)) as [V |] eqn:E1; [| discriminate ].
    rewrite (Hs _ _ E1); exact Hr.
  - intros p r Hr; unfold gc_body in *.
    destruct (gs_find_tele Ξ p) as [[[U ip] T] |]; [ exact Hr |].
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
  destruct ip' as [| z ip''], E as [b pv A B | pm [Δ' [Φ' | E']]]; try discriminate.
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

(** [M] applied to [args], outermost first. *)
Fixpoint apps (M : exp) (args : list exp) : exp :=
  match args with
  | nil => M
  | N :: args' => apps (a_app M N) args'
  end.

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
    with. *)
| mt_unit_mod : forall Γ fp ch T,
    gc_module Θ Ξ (q_abs fp ch) = Some (mr_body T) ->
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
