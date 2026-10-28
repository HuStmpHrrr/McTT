(** * Computing Descriptions

    [mdenote_impl] decides [mdenote], together with what units and entries
    denote ([udenote], [edenote]), the expansion of bodies ([body_xp]) and
    what an open generates ([items_gen]), by recursion on a termination
    order ([mdenote_order]) that mirrors their recursion: a slot is read through
    the unit the context gives it, a selection through the entry the
    description of its module gives, and an open through its target in the
    context of the expanded body before it.  Wherever a lookup succeeds, the
    order asks for an order of what it found, so every module expression
    that denotes has an order ([mdenote_order_of_mdenote]); so does a selection
    from a well-formed module expression ([mdenote_order_mem_of_wf]), since the
    entries of the description of a well-formed module expression denote. *)

From Stdlib Require Import Lia List PeanoNat String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Paths DescTyping Presup.
From Mctt.Core.Syntactic.Inductives Require Import Group.
From Mctt.Extraction Require Import Lookup FastDesc.
Import Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Termination Order *)

Inductive mdenote_order (Θ : gdeps) (Ξ : gstack) : ctx -> modexp -> Prop :=
| mdenote_order_unit : forall Γ H TΦ,
    gc_unit Θ Ξ H = Some TΦ ->
    mdenote_order Θ Ξ Γ H
(** The open frame of a member's module, named by its path *)
| mdenote_order_ind_frame : forall Γ H p r,
    mod_qname H = Some p -> gs_find_ind Ξ p = Some r ->
    mdenote_order Θ Ξ Γ H
(** The open frame of a record type's module, named by its path *)
| mdenote_order_record_frame : forall Γ H p R,
    mod_qname H = Some p -> gs_find_record Ξ p = Some R ->
    mdenote_order Θ Ξ Γ H
| mdenote_order_path : forall Γ fp,
    mdenote_order Θ Ξ Γ (me_unit fp)
| mdenote_order_var : forall Γ x,
    (forall U, ctx_find_mod Γ x = Some U -> udenote_order Θ Ξ Γ U) ->
    mdenote_order Θ Ξ Γ (me_var x)
| mdenote_order_lit : forall Γ U,
    udenote_order Θ Ξ Γ U ->
    mdenote_order Θ Ξ Γ (me_lit U)
| mdenote_order_app : forall Γ H N,
    mdenote_order Θ Ξ Γ H ->
    mdenote_order Θ Ξ Γ (me_app H N)
| mdenote_order_mem_case : forall Γ H y,
    mdenote_order Θ Ξ Γ H ->
    (forall R0 R0m Γy E rd, mdenote Θ Ξ Γ H R0 -> ds_mod R0 = Some R0m ->
       ds_entry R0m y = Some (Γy, E, rd) -> edenote_order Θ Ξ (Γy ++ Γ) E) ->
    mdenote_order Θ Ξ Γ (me_mem H y)
with udenote_order (Θ : gdeps) (Ξ : gstack) : ctx -> gunit -> Prop :=
| udenote_order_body : forall Γ Δ sm Φ,
    body_xp_order Θ Ξ (Δ ++ Γ) Φ ->
    udenote_order Θ Ξ Γ (gu_mk Δ (md_body sm Φ))
| udenote_order_alias : forall Γ Δ E,
    mdenote_order Θ Ξ (Δ ++ Γ) E ->
    udenote_order Θ Ξ Γ (gu_mk Δ (md_alias E))
with edenote_order (Θ : gdeps) (Ξ : gstack) : ctx -> gentry -> Prop :=
| edenote_order_def : forall Γ b pv A oM, edenote_order Θ Ξ Γ (ge_def b pv A oM)
| edenote_order_mod : forall Γ pv U,
    udenote_order Θ Ξ Γ U ->
    edenote_order Θ Ξ Γ (ge_mod pv U)
| edenote_order_ind_case : forall Γ pv p k D Φ, edenote_order Θ Ξ Γ (ge_ind pv p k D Φ)
(** A definition with a module part: its module part's target, under its
    parameters *)
| edenote_order_def_mod : forall Γ pv A M Δ E,
    mdenote_order Θ Ξ (Δ ++ Γ) E ->
    edenote_order Θ Ξ Γ (ge_def_mod pv A M (gu_mk Δ (md_alias E)))
(** One whose module part is a body denotes nothing *)
| edenote_order_def_mod_body : forall Γ pv A M Δ sm Φ, edenote_order Θ Ξ Γ (ge_def_mod pv A M (gu_mk Δ (md_body sm Φ)))
(** A record entry: its type former, where it is stored *)
| edenote_order_record : forall Γ pv pr R Φ, edenote_order Θ Ξ Γ (ge_record pv pr R Φ)
with body_xp_order (Θ : gdeps) (Ξ : gstack) : ctx -> gmod -> Prop :=
| body_xp_order_nil : forall Γ, body_xp_order Θ Ξ Γ gm_nil
| body_xp_order_ext : forall Γ Φ x E,
    body_xp_order Θ Ξ Γ Φ ->
    body_xp_order Θ Ξ Γ (gm_ext Φ x E)
| body_xp_order_open : forall Γ Φ H its,
    body_xp_order Θ Ξ Γ Φ ->
    (forall Φx, body_xp Θ Ξ Γ Φ Φx -> mdenote_order Θ Ξ (body_ctx Φx ++ Γ) H) ->
    (forall Φx, body_xp Θ Ξ Γ Φ Φx -> items_gen_order Θ Ξ (body_ctx Φx ++ Γ) H its) ->
    body_xp_order Θ Ξ Γ (gm_open Φ H its)
with items_gen_order (Θ : gdeps) (Ξ : gstack) : ctx -> modexp -> list iitem -> Prop :=
| items_gen_order_nil : forall Γ H, items_gen_order Θ Ξ Γ H nil
| items_gen_order_self : forall Γ H d pv its,
    items_gen_order Θ Ξ Γ H its ->
    items_gen_order Θ Ξ Γ H ((None, d, pv) :: its)
| items_gen_order_name : forall Γ H n d pv its,
    mdenote_order Θ Ξ Γ (me_mem H n) ->
    items_gen_order Θ Ξ Γ H its ->
    items_gen_order Θ Ξ Γ H ((Some n, d, pv) :: its).

Scheme mdenote_order_mut_ind := Induction for mdenote_order Sort Prop
with udenote_order_mut_ind := Induction for udenote_order Sort Prop
with edenote_order_mut_ind := Induction for edenote_order Sort Prop
with body_xp_order_mut_ind := Induction for body_xp_order Sort Prop
with items_gen_order_mut_ind := Induction for items_gen_order Sort Prop.

(** ** The Decision Procedure *)

(** The conditions of an open on its own items, decided. *)
Definition items_ok_dec (its : list iitem) : { items_ok its } + { ~ items_ok its }.
Proof.
  unfold items_ok.
  destruct (both_dup its) as [n |]; [ right; intros [H _]; discriminate |].
  destruct (name_dup (List.map iitem_name its)) as [n |]; [ right; intros [_ H]; discriminate | left; split; reflexivity ].
Defined.

(** Equality of references to members of groups, decided. *)
Definition indref_eq_dec (x y : (qname * nat * ind_decl)%type) : {x = y} + {x <> y}.
Proof.
  destruct x as [[p1 k1] D1], y as [[p2 k2] D2].
  destruct (ind_decl_eq_dec_g exp_eq_dec centry_eq_dec D1 D2) as [<- | HD]; [| right; congruence ].
  destruct (Nat.eq_dec k1 k2) as [<- | Hk]; [| right; congruence ].
  destruct (qname_eq_dec p1 p2) as [<- | Hp]; [ left; reflexivity | right; congruence ].
Defined.

Lemma gc_unit_var : forall Θ Ξ x, gc_unit Θ Ξ (me_var x) = None.
Proof. reflexivity. Qed.

Lemma gc_unit_lit : forall Θ Ξ U, gc_unit Θ Ξ (me_lit U) = None.
Proof. reflexivity. Qed.

Lemma gc_unit_app : forall Θ Ξ H N, gc_unit Θ Ξ (me_app H N) = None.
Proof. reflexivity. Qed.

Lemma mod_qname_mem_in : forall H y p, mod_qname H = Some p -> mod_qname (me_mem H y) = Some (qname_in p y).
Proof. intros * Hq; cbn; rewrite Hq; reflexivity. Qed.

Lemma gc_unit_mem_qname : forall Θ Ξ H y r, gc_unit Θ Ξ (me_mem H y) = Some r -> mod_qname H = None -> False.
Proof. intros * Hu Hq; unfold gc_unit in Hu; cbn in Hu; rewrite Hq in Hu; discriminate. Qed.

(** The member whose module's open frame a module expression names, if
    any. *)
Definition frame_ind_of (Ξ : gstack) (H : modexp) : option (qname * nat * ind_decl) :=
  match mod_qname H with
  | Some p => gs_find_ind Ξ p
  | None => None
  end.

Lemma frame_ind_of_some : forall Ξ H r, frame_ind_of Ξ H = Some r -> exists p, mod_qname H = Some p /\ gs_find_ind Ξ p = Some r.
Proof. intros * Hf; unfold frame_ind_of in Hf; destruct (mod_qname H) as [p |]; [ eauto | discriminate ]. Qed.

Lemma frame_ind_of_none : forall Ξ H p r, frame_ind_of Ξ H = None -> mod_qname H = Some p -> gs_find_ind Ξ p = Some r -> False.
Proof. intros * Hf Hq Hk; unfold frame_ind_of in Hf; rewrite Hq, Hk in Hf; discriminate. Qed.

(** What the open frame of member [k] of the group [D] declared at [pq]
    that a module expression names denotes: the member's type former,
    with its module. *)
Definition frame_ind_desc (Θ : gdeps) (Ξ : gstack) (H : modexp) (pq : qname) (k : nat) (D : ind_decl) : option mdesc :=
  match mod_qname H with
  | Some p =>
      match ind_member D k, gc_loc Θ Ξ p with
      | Some Mk, Some (Tm, Φm) => Some (ind_former_desc pq k D Mk (ds_closed nil p Tm Φm nil))
      | _, _ => None
      end
  | None => None
  end.

Lemma dn_of_frame_ind : forall Θ Ξ Γ H pq k D R, frame_ind_of Ξ H = Some (pq, k, D) ->
    frame_ind_desc Θ Ξ H pq k D = Some R -> mdenote Θ Ξ Γ H R.
Proof.
  intros * Hf Hd; destruct (frame_ind_of_some _ _ _ Hf) as (p & Hq & Hk).
  unfold frame_ind_desc in Hd; rewrite Hq in Hd.
  destruct (ind_member D k) as [Mk |] eqn:HMk; [| discriminate ].
  destruct (gc_loc Θ Ξ p) as [[Tm Φm] |] eqn:Hl; [ injection Hd as <- | discriminate ].
  eapply mdenote_ind_frame; eassumption.
Qed.

(** In a well-formed global context, the open frame of a member denotes. *)
Lemma frame_ind_desc_some : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H pq k D,
    frame_ind_of Ξ H = Some (pq, k, D) -> frame_ind_desc Θ Ξ H pq k D = None -> False.
Proof.
  intros * Hg * Hf Hd; destruct (frame_ind_of_some _ _ _ Hf) as (p & Hq & Hk).
  destruct (frame_ind_loc _ _ Hg _ _ _ _ Hk) as (U & T0 & T & Φ & Mk & Ht & _ & Hl & HMk).
  unfold frame_ind_desc in Hd; rewrite Hq, HMk, Hl in Hd; discriminate.
Qed.

(** The record type whose module's open frame a module expression names,
    if any. *)
Definition frame_record_of (Ξ : gstack) (H : modexp) : option (qname * record_decl) :=
  match mod_qname H with
  | Some p => option_map (fun R => (p, R)) (gs_find_record Ξ p)
  | None => None
  end.

Lemma frame_record_of_some : forall Ξ H p R, frame_record_of Ξ H = Some (p, R) -> mod_qname H = Some p /\ gs_find_record Ξ p = Some R.
Proof.
  intros * Hf; unfold frame_record_of in Hf; destruct (mod_qname H) as [p' |]; [| discriminate ].
  destruct (gs_find_record Ξ p') as [R' |] eqn:E; cbn in Hf; [ injection Hf as <- <-; auto | discriminate ].
Qed.

Lemma frame_record_of_none : forall Ξ H p R, frame_record_of Ξ H = None -> mod_qname H = Some p -> gs_find_record Ξ p = Some R -> False.
Proof. intros * Hf Hq Hk; unfold frame_record_of in Hf; rewrite Hq, Hk in Hf; discriminate. Qed.

(** What the open frame of the record type [R] at [p] denotes: its type
    former, with its module. *)
Definition frame_record_desc (Θ : gdeps) (Ξ : gstack) (p : qname) (R : record_decl) : option mdesc :=
  match gc_loc Θ Ξ p with
  | Some (Tm, Φm) => Some (record_former_desc p R (ds_closed nil p Tm Φm nil))
  | None => None
  end.

Lemma dn_of_frame_record : forall Θ Ξ Γ H p R Rd, frame_record_of Ξ H = Some (p, R) ->
    frame_record_desc Θ Ξ p R = Some Rd -> mdenote Θ Ξ Γ H Rd.
Proof.
  intros * Hf Hd; destruct (frame_record_of_some _ _ _ _ Hf) as (Hq & Hk).
  unfold frame_record_desc in Hd.
  destruct (gc_loc Θ Ξ p) as [[Tm Φm] |] eqn:Hl; [ injection Hd as <- | discriminate ].
  eapply mdenote_record_frame; eassumption.
Qed.

(** In a well-formed global context, the open frame of a record type
    denotes. *)
Lemma frame_record_desc_some : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H p R,
    frame_record_of Ξ H = Some (p, R) -> frame_record_desc Θ Ξ p R = None -> False.
Proof.
  intros * Hg * Hf Hd; destruct (frame_record_of_some _ _ _ _ Hf) as (Hq & Hk).
  destruct (frame_record_loc _ _ Hg _ _ Hk) as (U & T0 & T & Φ & _ & _ & Hl).
  unfold frame_record_desc in Hd; rewrite Hl in Hd; discriminate.
Qed.

(** A fast entry whose unit is Core's own but holds a body is no
    translation of a canonical entry. *)
Lemma canon_fe_core_body : forall pv Δ sm Φ, canon_fentry (fe_mod pv (fu_core (gu_mk Δ (md_body sm Φ)))) -> False.
Proof.
  intros * (E & HE & Hc); destruct E as [| pv' [Δ' [[|] Φ' | E']] | | |]; cbn in HE, Hc; try discriminate; contradiction.
Qed.

(** The trie of a canonical closed submodule entry is canonical. *)
Lemma canon_fe_mod_trie : forall pv Δ t, canon_fentry (fe_mod pv (fu_mk Δ (fmd_body t))) -> canon_trie t.
Proof.
  intros * (E & HE & Hc); destruct E as [| pv' [Δ' [[|] Φ' | E']] | | |]; cbn in HE, Hc; try discriminate; try contradiction.
  injection HE as _ _ ->; exists Φ'; split; [ reflexivity | exact Hc ].
Qed.

(** A canonical body expands to itself. *)
Lemma body_xp_canon : forall Θ Ξ Γ Φ, canon_mod Φ -> body_xp Θ Ξ Γ Φ Φ.
Proof.
  intros Θ Ξ Γ; induction Φ as [| Φ IH x E | Φ IH H its]; intros Hc; cbn in Hc; [ constructor | | contradiction ].
  constructor; apply IH; tauto.
Qed.

(** A stored closed submodule, read at its path *)
Lemma edenote_fast_closed : forall Θ Ξ Γ pq pv Δ t, canon_trie t ->
    edenote Θ Ξ Γ (Some pq) (ge_mod pv (gu_mk Δ (md_body sm_closed (dec_mod t)))) (ds_closed nil pq Δ (dec_mod t) nil).
Proof.
  intros * (Φ & -> & Hc); rewrite dec_tr_mod by exact Hc.
  constructor; econstructor; [ apply body_xp_canon, Hc | reflexivity ].
Qed.

(** A selection, read through the fast descriptions *)
Lemma mdenote_mem_dec : forall Θ Ξ Γ H y R0 R0m Γy s rd R R',
    mdenote Θ Ξ Γ H (dec_desc R0) -> ds_mod (dec_desc R0) = Some (dec_desc R0m) ->
    ds_entry (dec_desc R0m) y = Some (Γy, dec_entry_source s, rd) ->
    edenote Θ Ξ (Γy ++ Γ) (fds_epath R0m y) (dec_entry_source s) (dec_desc R) ->
    ds_read rd (dec_desc R) = Some (dec_desc R') -> mdenote Θ Ξ Γ (me_mem H y) (dec_desc R').
Proof. intros * H1 H2 H3 H4 H5; econstructor; [ exact H1 | exact H2 | exact H3 | rewrite fds_epath_dec; exact H4 | exact H5 ]. Qed.

(** A closed submodule read at no path denotes nothing. *)
Lemma edenote_closed_none : forall Θ Ξ Γ pv Δ Φ R, ~ edenote Θ Ξ Γ None (ge_mod pv (gu_mk Δ (md_body sm_closed Φ))) R.
Proof. intros * He; inversion He; subst; match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end; discriminate. Qed.

(** A definition with a module part whose unit is a body denotes
    nothing. *)
Lemma edenote_dm_body : forall Θ Ξ Γ o pv A M Δ sm Φ R, ~ edenote Θ Ξ Γ o (ge_def_mod pv A M (gu_mk Δ (md_body sm Φ))) R.
Proof. intros * He; inversion He. Qed.

(** Where an entry of a description may be read: a local entry at no
    path, as [ds_epath] gives for a local body. *)
Definition entry_source_ok (o : option qname) (s : entry_source) : Prop :=
  match s with
  | entry_source_core _ => o = None
  | entry_source_fast _ _ _ => True
  end.

(** What the descriptions of [Θ ⍮ Ξ] are, computed through the fast
    context [F]: the descriptions are fast ([fmdesc]), and stand for the
    Core ones the relations name ([dec_desc]). *)
Section DenoteImpl.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** [frame_ind_of], fast *)
  Definition fast_frame_ind_of (H : modexp) : { o | frame_ind_of Ξ H = o } :=
    match mod_qname H as m return { o | match m with Some p => gs_find_ind Ξ p | None => None end = o } with
    | Some p => gs_find_ind_f F p
    | None => exist _ None eq_refl
    end.

  (** [frame_record_of], fast *)
  Definition fast_frame_record_of (H : modexp) : { o | frame_record_of Ξ H = o } :=
    match mod_qname H as m return { o | match m with Some p => option_map (fun R => (p, R)) (gs_find_record Ξ p) | None => None end = o } with
    | Some p => let (o, E) := gs_find_record_f F p in exist _ (option_map (fun R => (p, R)) o) (f_equal _ E)
    | None => exist _ None eq_refl
    end.

  (** [frame_ind_desc], fast *)
  Definition fast_frame_ind_desc (H : modexp) (pq : qname) (k : nat) (D : ind_decl) :
      { o | frame_ind_desc Θ Ξ H pq k D = option_map dec_desc o }.
  Proof.
    unfold frame_ind_desc; destruct (mod_qname H) as [p |]; [| exact (exist _ None eq_refl) ].
    destruct (ind_member D k) as [Mk |]; [| exact (exist _ None eq_refl) ].
    destruct (gc_loc_cf F p) as [[[Tm tm] |] [El Hc]].
    - refine (exist _ (Some (fast_ind_former_desc pq k D Mk (fds_closed nil p Tm tm (Hc _ _ eq_refl) nil))) _).
      rewrite El; reflexivity.
    - refine (exist _ None _); rewrite El; reflexivity.
  Defined.

  (** [frame_record_desc], fast *)
  Definition fast_frame_record_desc (p : qname) (R : record_decl) :
      { o | frame_record_desc Θ Ξ p R = option_map dec_desc o }.
  Proof.
    unfold frame_record_desc; destruct (gc_loc_cf F p) as [[[Tm tm] |] [El Hc]].
    - refine (exist _ (Some (fast_record_former_desc p R (fds_closed nil p Tm tm (Hc _ _ eq_refl) nil))) _).
      rewrite El; reflexivity.
    - refine (exist _ None _); rewrite El; reflexivity.
  Defined.

  (** The twins of the operations on descriptions, with their equations *)
  Definition fds_at_s R N : { o | ds_at (dec_desc R) N = option_map dec_desc o } := exist _ (fds_at R N) (fds_at_dec R N).
  Definition fds_mod_s R : { o | ds_mod (dec_desc R) = option_map dec_desc o } := exist _ (fds_mod R) (fds_mod_dec R).
  Definition fds_ty_s R : { o | ds_ty (dec_desc R) = o } := exist _ (fds_ty R) (fds_ty_dec R).
  Definition fds_read_s rd R : { o | ds_read rd (dec_desc R) = option_map dec_desc o } :=
    exist _ (fds_read rd R) (fds_read_dec rd R).
  Definition fds_entry_s R y :
      { o | ds_entry (dec_desc R) y = option_map (fun r => (fst (fst r), dec_entry_source (snd (fst r)), snd r)) o /\
            forall Γy s rd, o = Some (Γy, s, rd) -> entry_source_ok (fds_epath R y) s } :=
    exist _ (fds_entry R y)
      (conj (fds_entry_dec R y)
         (fun Γy s rd E => match s as s0 return entry_source_path s0 = fds_epath R y -> entry_source_ok (fds_epath R y) s0 with
                           | entry_source_core _ => fun Ep => eq_sym Ep
                           | entry_source_fast _ _ _ => fun _ => I
                           end (fds_entry_path R y Γy s rd E))).

  #[local]
  Ltac dn_close :=
    repeat match goal with
      | H1 : mdenote _ _ ?G ?H ?A1, H2 : mdenote _ _ ?G ?H ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          pose proof (proj1 (mdenote_functional_all _ _ Hg) _ _ _ H1 _ H2); subst; clear H2
      | H1 : udenote _ _ ?G ?o ?U ?A1, H2 : udenote _ _ ?G ?o ?U ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          pose proof (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : edenote _ _ ?G ?o ?E ?A1, H2 : edenote _ _ ?G ?o ?E ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          pose proof (proj1 (proj2 (proj2 (mdenote_functional_all _ _ Hg))) _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : body_xp _ _ ?G ?Φ ?A1, H2 : body_xp _ _ ?G ?Φ ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ H1 _ H2); subst; clear H2
      | H1 : items_gen _ _ ?b ?G ?H ?its ?A1, H2 : items_gen _ _ ?b ?G ?H ?its ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          pose proof (proj2 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : ?f = Some ?a, H2 : ?f = Some ?b |- _ =>
          assert_fails (constr_eq a b); rewrite H1 in H2; injection H2; clear H2; intros; subst
      | H1 : ?f = Some _, H2 : ?f = None |- _ =>
          rewrite H1 in H2; discriminate H2
      | Hl : _ ∋ # ?x ≔ₘ _ |- _ => apply ctx_find_mod_complete in Hl
      end.

  #[local]
  Ltac dn_finish :=
    first [ congruence
          | solve [ eapply frame_ind_of_none; eassumption ]
          | solve [ eapply frame_record_of_none; eassumption ]
          | match goal with Hq : mod_qname _ = Some _ |- _ => solve [ cbn in Hq; congruence ] end
          | match goal with HN : forall r, ~ _ |- _ => solve [ eapply HN; eassumption ] end
          | intuition congruence
          | solve [ cbn in *; discriminate ]
          | cbn in *; contradiction ].

  #[local]
  Ltac dn_neg_after :=
    rewrite ?gc_unit_var, ?gc_unit_lit, ?gc_unit_app in *; dn_close; rewrite ?fds_epath_dec in *; dn_close;
    (* the module part of a definition with a module part: its alias *)
    try (match goal with Hu : udenote _ _ _ _ (gu_mk _ (md_alias _)) _ |- _ => inversion Hu; subst; clear Hu end; dn_close);
    dn_finish.

  #[local]
  Ltac dn_neg :=
    match goal with
    | Hm : mdenote _ _ _ _ _ |- _ => inversion Hm; subst; clear Hm; dn_neg_after
    | Hm : udenote _ _ _ _ _ _ |- _ => inversion Hm; subst; clear Hm; dn_neg_after
    | Hm : edenote _ _ _ _ _ _ |- _ => inversion Hm; subst; clear Hm; dn_neg_after
    | Hm : body_xp _ _ _ _ _ |- _ => inversion Hm; subst; clear Hm; dn_neg_after
    | Hm : items_gen _ _ _ _ _ _ |- _ => inversion Hm; subst; clear Hm; dn_neg_after
    end.

  #[local]
  Ltac impl_obl_tac :=
    intros; cbv beta in *;
    cbn [option_map dec_desc dec_entry_source dec_entry dec_unit dec_loc fst snd entry_source_ok] in *;
    rewrite ?fds_epath_dec, ?fds_up_dec in *;
    repeat match goal with H : _ = _ /\ _ |- _ => destruct H end;
    repeat match goal with H : ?o = None |- _ => is_var o; subst o end;
    repeat match goal with
      | H : mdenote_order _ _ _ _ |- _ => progressive_invert H
      | H : udenote_order _ _ _ _ |- _ => progressive_invert H
      | H : edenote_order _ _ _ _ |- _ => progressive_invert H
      | H : body_xp_order _ _ _ _ |- _ => progressive_invert H
      | H : items_gen_order _ _ _ _ _ |- _ => progressive_invert H
      | Ho : mdenote_order _ _ _ (me_mem _ _), Eu : gc_unit _ _ (me_mem _ _) = None, Ek : frame_ind_of _ (me_mem _ _) = None,
        Erf : frame_record_of _ (me_mem _ _) = None |- _ =>
          inversion Ho; subst; clear Ho;
            [ congruence | exfalso; eapply frame_ind_of_none; eassumption | exfalso; eapply frame_record_of_none; eassumption |]
      (** The reference a member's path names, decided equal *)
      | Hr : ?r = (_, _, _) |- _ => is_var r; subst r
      end;
    rewrite ?gc_unit_var, ?gc_unit_lit, ?gc_unit_app in *;
    try solve [ congruence | eauto ];
    lazymatch goal with
    | |- False => dn_neg
    | |- ~ _ => let Hd := fresh "Hd" in intros Hd; dn_neg
    | |- forall _, ~ _ => let r := fresh "r" in let Hd := fresh "Hd" in intros r Hd; dn_neg
    | _ => try solve [ econstructor; eauto using ctx_find_mod_sound, udenote_alias; cbn; auto ]
    end.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations mdenote_impl Γ H (Ho : mdenote_order Θ Ξ Γ H) :
      { R : fmdesc | mdenote Θ Ξ Γ H (dec_desc R) } + { forall R, ~ mdenote Θ Ξ Γ H R } by struct Ho :=
  | Γ, me_unit fp, Ho with gc_unit_cf F (me_unit fp) := {
    | exist _ (Some (T, t)) Eu => inleft (exist _ (fds_closed nil (q_abs fp nil) T t (proj2 Eu T t eq_refl) nil) _)
    | exist _ None Eu with fast_frame_ind_of (me_unit fp) := {
      | exist _ (Some (pq, k, D)) Ek with fast_frame_ind_desc (me_unit fp) pq k D := {
        | exist _ (Some R) Ed => inleft (exist _ R (dn_of_frame_ind _ _ _ _ _ _ _ _ Ek Ed))
        | exist _ None Ed => False_rect _ (frame_ind_desc_some _ _ Hg _ _ _ _ Ek Ed) }
      | exist _ None Ek with fast_frame_record_of (me_unit fp) := {
        | exist _ (Some (p, R)) Er with fast_frame_record_desc p R := {
          | exist _ (Some Rd) Ed => inleft (exist _ Rd (dn_of_frame_record _ _ _ _ _ _ _ Er Ed))
          | exist _ None Ed => False_rect _ (frame_record_desc_some _ _ Hg _ _ _ Er Ed) }
        | exist _ None Er => inright _ } } }
  | Γ, me_var x, Ho with inspect (ctx_find_mod Γ x) := {
    | exist _ (Some U) Ef with udenote_impl Γ U _ := {
      | inleft (exist _ R HR) => inleft (exist _ R _)
      | inright HN => inright _ }
    | exist _ None Ef => inright _ }
  | Γ, me_lit U, Ho with udenote_impl Γ U _ := {
    | inleft (exist _ R HR) => inleft (exist _ R _)
    | inright HN => inright _ }
  | Γ, me_app H N, Ho with mdenote_impl Γ H _ := {
    | inleft (exist _ R HR) with fds_at_s R N := {
      | exist _ (Some R') Ea => inleft (exist _ R' _)
      | exist _ None Ea => inright _ }
    | inright HN => inright _ }
  | Γ, me_mem H y, Ho with gc_unit_cf F (me_mem H y) := {
    | exist _ (Some (T, t)) Eu with inspect (mod_qname H) := {
      | exist _ (Some p) Eqp =>
          inleft (exist _ (fds_closed nil (qname_in p y) T t (proj2 Eu T t eq_refl) nil)
                    (mdenote_unit _ _ _ _ _ _ _ (mod_qname_mem_in _ _ _ Eqp) (proj1 Eu)))
      | exist _ None Eqp => False_rect _ (gc_unit_mem_qname _ _ _ _ _ (proj1 Eu) Eqp) }
    | exist _ None Eu with fast_frame_ind_of (me_mem H y) := {
      | exist _ (Some (pq, k, D)) Ek with fast_frame_ind_desc (me_mem H y) pq k D := {
        | exist _ (Some R) Ed => inleft (exist _ R (dn_of_frame_ind _ _ _ _ _ _ _ _ Ek Ed))
        | exist _ None Ed => False_rect _ (frame_ind_desc_some _ _ Hg _ _ _ _ Ek Ed) }
      | exist _ None Ek with fast_frame_record_of (me_mem H y) := {
        | exist _ (Some (p, Rr)) Erf with fast_frame_record_desc p Rr := {
          | exist _ (Some Rd) Ed => inleft (exist _ Rd (dn_of_frame_record _ _ _ _ _ _ _ Erf Ed))
          | exist _ None Ed => False_rect _ (frame_record_desc_some _ _ Hg _ _ _ Erf Ed) }
        | exist _ None Erf with mdenote_impl Γ H _ := {
          | inright HN => inright _
          | inleft (exist _ R0 HR0) with fds_mod_s R0 := {
            | exist _ None Em => inright _
            | exist _ (Some R0m) Em with fds_entry_s R0m y := {
              | exist _ None Ee => inright _
              | exist _ (Some (Γy, s, rd)) Ee with edenote_impl (Γy ++ Γ) (fds_epath R0m y) s (proj2 Ee _ _ _ eq_refl) _ := {
                | inright HN => inright _
                | inleft (exist _ R HR) with fds_read_s rd R := {
                  | exist _ None Er => inright _
                  | exist _ (Some R') Er => inleft (exist _ R' (mdenote_mem_dec _ _ _ _ _ _ _ _ _ _ _ _ HR0 Em (proj1 Ee) HR Er)) } } } } } } } }

  (** A Core unit, read at no path: a local module *)
  with udenote_impl Γ U (Ho : udenote_order Θ Ξ Γ U) :
      { R : fmdesc | udenote Θ Ξ Γ None U (dec_desc R) } + { forall R, ~ udenote Θ Ξ Γ None U R } by struct Ho :=
  | Γ, gu_mk Δ (md_body sm_open Φ), Ho with body_xp_impl (Δ ++ Γ) Φ _ := {
    | inleft (exist _ Φx Hx) => inleft (exist _ (fds_open Δ Φ Φx) _)
    | inright HN => inright _ }
  | Γ, gu_mk Δ (md_body sm_closed Φ), Ho => inright _
  | Γ, gu_mk Δ (md_alias E), Ho with mdenote_impl (Δ ++ Γ) E _ := {
    | inright HN => inright _
    | inleft (exist _ R HR) with fds_mod_s R := {
      | exist _ (Some R') Em => inleft (exist _ (fds_up Δ R') _)
      | exist _ None Em => inright _ } }

  (** An entry, read at [o] *)
  with edenote_impl Γ o s (Hos : entry_source_ok o s) (Ho : edenote_order Θ Ξ Γ (dec_entry_source s)) :
      { R : fmdesc | edenote Θ Ξ Γ o (dec_entry_source s) (dec_desc R) } + { forall R, ~ edenote Θ Ξ Γ o (dec_entry_source s) R }
      by struct Ho :=
  (** A local entry, at no path *)
  | Γ, o, entry_source_core (ge_def b pv A oM), Hos, Ho => inleft (exist _ (fds_term A (if b then oM else None)) _)
  | Γ, o, entry_source_core (ge_mod pv U), Hos, Ho with udenote_impl Γ U _ := {
    | inleft (exist _ R HR) => inleft (exist _ R _)
    | inright HN => inright _ }
  | Γ, o, entry_source_core (ge_ind pv p k D Φ), Hos, Ho with inspect (ind_member D k) := {
    | exist _ None EMk => inright _
    | exist _ (Some Mk) EMk with inspect (ind_mpath D k) := {
      | exist _ None Ep => inright _
      | exist _ (Some pm) Ep with gc_loc_cf F pm := {
        | exist _ None El => inright _
        | exist _ (Some (Tm, tm)) El =>
            inleft (exist _ (fast_ind_former_desc p k D Mk (fds_closed nil pm Tm tm (proj2 El Tm tm eq_refl) nil)) _) } } }
  | Γ, o, entry_source_core (ge_def_mod pv A M (gu_mk Δ (md_alias E))), Hos, Ho with mdenote_impl (Δ ++ Γ) E _ := {
    | inright HN => inright _
    | inleft (exist _ R HR) with fds_mod_s R := {
      | exist _ (Some R') Em => inleft (exist _ (fds_dm nil A M (fds_up Δ R')) _)
      | exist _ None Em => inright _ } }
  | Γ, o, entry_source_core (ge_def_mod pv A M (gu_mk Δ (md_body sm Φ))), Hos, Ho => inright _
  | Γ, Some p, entry_source_core (ge_record pv pr R Φ), Hos, Ho with gc_loc_cf F p := {
    | exist _ None El => inright _
    | exist _ (Some (Tm, tm)) El =>
        inleft (exist _ (fast_record_former_desc p R (fds_closed nil p Tm tm (proj2 El Tm tm eq_refl) nil)) _) }
  | Γ, None, entry_source_core (ge_record pv pr R Φ), Hos, Ho => inright _
  (** A stored entry, at its path *)
  | Γ, o, entry_source_fast pe (fe_def b pv A oM) Hc, Hos, Ho => inleft (exist _ (fds_term A (if b then oM else None)) _)
  | Γ, None, entry_source_fast pe (fe_mod pv (fu_mk Δ (fmd_body t))) Hc, Hos, Ho =>
      inright (fun R => edenote_closed_none _ _ Γ pv Δ (dec_mod t) R)
  | Γ, Some pq, entry_source_fast pe (fe_mod pv (fu_mk Δ (fmd_body t))) Hc, Hos, Ho =>
      inleft (exist _ (fds_closed nil pq Δ t (canon_fe_mod_trie _ _ _ Hc) nil)
                (edenote_fast_closed _ _ Γ pq pv Δ t (canon_fe_mod_trie _ _ _ Hc)))
  | Γ, o, entry_source_fast pe (fe_mod pv (fu_core (gu_mk Δ (md_body sm Φ)))) Hc, Hos, Ho => False_rect _ (canon_fe_core_body _ _ _ _ Hc)
  | Γ, o, entry_source_fast pe (fe_mod pv (fu_core (gu_mk Δ (md_alias E)))) Hc, Hos, Ho with mdenote_impl (Δ ++ Γ) E _ := {
    | inright HN => inright _
    | inleft (exist _ R HR) with fds_mod_s R := {
      | exist _ (Some R') Em => inleft (exist _ (fds_up Δ R') _)
      | exist _ None Em => inright _ } }
  | Γ, o, entry_source_fast pe (fe_ind pv p k D t) Hc, Hos, Ho with inspect (ind_member D k) := {
    | exist _ None EMk => inright _
    | exist _ (Some Mk) EMk with inspect (ind_mpath D k) := {
      | exist _ None Ep => inright _
      | exist _ (Some pm) Ep with gc_loc_cf F pm := {
        | exist _ None El => inright _
        | exist _ (Some (Tm, tm)) El =>
            inleft (exist _ (fast_ind_former_desc p k D Mk (fds_closed nil pm Tm tm (proj2 El Tm tm eq_refl) nil)) _) } } }
  | Γ, o, entry_source_fast pe (fe_def_mod pv A M (fu_core (gu_mk Δ (md_alias E)))) Hc, Hos, Ho with mdenote_impl (Δ ++ Γ) E _ := {
    | inright HN => inright _
    | inleft (exist _ R HR) with fds_mod_s R := {
      | exist _ (Some R') Em => inleft (exist _ (fds_dm nil A M (fds_up Δ R')) _)
      | exist _ None Em => inright _ } }
  | Γ, o, entry_source_fast pe (fe_def_mod pv A M (fu_core (gu_mk Δ (md_body sm Φ)))) Hc, Hos, Ho =>
      inright (fun R => edenote_dm_body _ _ Γ o pv A M Δ sm Φ R)
  | Γ, o, entry_source_fast pe (fe_def_mod pv A M (fu_mk Δ (fmd_body t))) Hc, Hos, Ho =>
      inright (fun R => edenote_dm_body _ _ Γ o pv A M Δ sm_closed (dec_mod t) R)
  | Γ, Some p, entry_source_fast pe (fe_record pv pr R t) Hc, Hos, Ho with gc_loc_cf F p := {
    | exist _ None El => inright _
    | exist _ (Some (Tm, tm)) El =>
        inleft (exist _ (fast_record_former_desc p R (fds_closed nil p Tm tm (proj2 El Tm tm eq_refl) nil)) _) }
  | Γ, None, entry_source_fast pe (fe_record pv pr R t) Hc, Hos, Ho => inright _

  with body_xp_impl Γ Φ (Ho : body_xp_order Θ Ξ Γ Φ) :
      { Φx | body_xp Θ Ξ Γ Φ Φx } + { forall Φx, ~ body_xp Θ Ξ Γ Φ Φx } by struct Ho :=
  | Γ, gm_nil, Ho => inleft (exist _ gm_nil _)
  | Γ, gm_ext Φ x E, Ho with body_xp_impl Γ Φ _ := {
    | inleft (exist _ Φx Hx) => inleft (exist _ (gm_ext Φx x E) _)
    | inright HN => inright _ }
  | Γ, gm_open Φ H its, Ho with body_xp_impl Γ Φ _ := {
    | inright HN => inright _
    | inleft (exist _ Φx Hx) with mdenote_impl (body_ctx Φx ++ Γ) H _ := {
      | inright HN => inright _
      | inleft (exist _ R HR) with fds_mod_s R := {
        | exist _ None Em => inright _
        | exist _ (Some Rm) Em with items_gen_impl (body_ctx Φx ++ Γ) H its _ := {
          | inright HN => inright _
          | inleft (exist _ gs Hgs) with items_ok_dec its := {
            | left Hok => inleft (exist _ (gens_append Φx 0 gs) _)
            | right Hn => inright _ } } } } }

  with items_gen_impl Γ H its (Ho : items_gen_order Θ Ξ Γ H its) :
      { gs | items_gen Θ Ξ Γ H its gs } + { forall gs, ~ items_gen Θ Ξ Γ H its gs } by struct Ho :=
  | Γ, H, nil, Ho => inleft (exist _ nil _)
  | Γ, H, (None, d, pv) :: its, Ho with items_gen_impl Γ H its _ := {
    | inleft (exist _ gs Hgs) => inleft (exist _ (generated_item_alias d pv H :: gs) _)
    | inright HN => inright _ }
  | Γ, H, (Some n, d, pv) :: its, Ho with mdenote_impl Γ (me_mem H n) _ := {
    | inright HN => inright _
    | inleft (exist _ (fds_term A om) HR) with items_gen_impl Γ H its _ := {
      | inleft (exist _ gs Hgs) => inleft (exist _ (generated_item_def d pv A (a_mem H n) :: gs) _)
      | inright HN => inright _ }
    | inleft (exist _ (fds_open Δ Φ Φx) HR) with items_gen_impl Γ H its _ := {
      | inleft (exist _ gs Hgs) => inleft (exist _ (generated_item_alias d pv (me_mem H n) :: gs) _)
      | inright HN => inright _ }
    | inleft (exist _ (fds_closed Θ' pc T t Ht Ns) HR) with items_gen_impl Γ H its _ := {
      | inleft (exist _ gs Hgs) => inleft (exist _ (generated_item_alias d pv (me_mem H n) :: gs) _)
      | inright HN => inright _ }
    (** A member with a term part and a module part: a definition with a
        module part, globally and locally alike *)
    | inleft (exist _ R HR) with fds_ty_s R := {
      | exist _ None Et => inright _
      | exist _ (Some A) Et with fds_mod_s R := {
        | exist _ None Em => inright _
        | exist _ (Some Rm) Em with items_gen_impl Γ H its _ := {
          | inleft (exist _ gs Hgs) => inleft (exist _ (generated_item_def_mod d pv A (a_mem H n) (me_mem H n) :: gs) _)
          | inright HN => inright _ } } } }.
  Solve All Obligations with impl_obl_tac.
End DenoteImpl.

(** ** What Denotes Has an Order *)

Section Orders.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  Theorem order_of_denote :
    (forall Γ H R, mdenote Θ Ξ Γ H R -> mdenote_order Θ Ξ Γ H) /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R -> udenote_order Θ Ξ Γ U) /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R -> edenote_order Θ Ξ Γ E) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> body_xp_order Θ Ξ Γ Φ) /\
    (forall Γ H its gs, items_gen Θ Ξ Γ H its gs -> items_gen_order Θ Ξ Γ H its).
  Proof.
    pose proof (mdenote_functional_all _ _ Hg) as (Fm & Fu & Fe & Fb & Fi).
    apply mdenote_all_ind; intros.
    - eapply mdenote_order_unit; eassumption.
    - eapply mdenote_order_ind_frame; eassumption.
    - apply mdenote_order_var; intros U' Hf.
      match goal with Hl : _ ∋ # _ ≔ₘ _ |- _ => rewrite (ctx_find_mod_complete _ _ _ Hl) in Hf end.
      injection Hf as <-; assumption.
    - constructor; assumption.
    - constructor; assumption.
    - apply mdenote_order_mem_case; [ assumption |].
      intros R1 R1m Γy' E' rd' Hm1 Hd1 He1.
      match goal with Hm0 : mdenote _ _ _ H _ |- _ => rewrite <- (Fm _ _ _ Hm0 _ Hm1) in Hd1 end.
      match goal with Hd0 : ds_mod _ = Some _ |- _ => rewrite Hd0 in Hd1; injection Hd1 as <- end.
      match goal with He0 : ds_entry _ _ = Some _ |- _ => rewrite He0 in He1; injection He1 as <- <- <- end.
      assumption.
    - eapply mdenote_order_record_frame; eassumption.
    - constructor; assumption.
    - constructor; assumption.
    - constructor.
    - constructor; assumption.
    - constructor.
    - (* a definition with a module part: its module part's target *)
      match goal with Hu : udenote_order _ _ _ (gu_mk _ (md_alias _)) |- _ => inversion Hu; subst end.
      constructor; assumption.
    - constructor.
    - constructor.
    - constructor; assumption.
    - constructor; [ assumption | |];
        intros Φx' Hx';
        match goal with Hx : body_xp _ _ _ Φ ?Φx0 |- _ => rewrite (Fb _ _ _ Hx' _ Hx) end; assumption.
    - constructor.
    - constructor; assumption.
    - constructor; assumption.
    - constructor; assumption.
    - constructor; assumption.
  Qed.

  Lemma body_xp_order_noopen : forall Γ Φ, gm_noopen Φ -> body_xp_order Θ Ξ Γ Φ.
  Proof.
    intros Γ; induction Φ as [| Φ IH x E | Φ IH H its]; intros Hn; cbn in Hn; [ constructor | constructor; auto | contradiction ].
  Qed.

  (** The entries of a typed module description denote, hence have an
      order: those of an open one are slots of its well-formed extended
      context, and those of a closed one are stored, so valid. *)
  Lemma edenote_order_entry : forall Γ Rm y Γy E rd,
      desc_ok Θ Ξ Γ Rm -> ds_entry Rm y = Some (Γy, E, rd) -> edenote_order Θ Ξ (Γy ++ Γ) E.
  Proof.
    pose proof (gctx_valid_syn _ _ Hg) as Hv.
    intros * Hok He; destruct Rm as [A om | Δ Φw Φ | Θ' pc T Φ Ns | ]; cbn in He; try discriminate.
    - (* an open module: a slot of its extended context *)
      inversion Hok as [| ? ? ? ? HΓ Hno Hsub | |]; subst.
      destruct (gm_prefix_upto Φ y) as [[| Φ' x E0 | ? ? ?] |] eqn:Hp; try discriminate.
      destruct E0 as [[|] pv A [M |] | pv U | ? ? ? ? ? | pv A M U | ? ? ?]; try discriminate; injection He as <- <- <-;
        [ constructor | |].
      all: destruct (gm_prefix_body_ctx _ _ _ Hno Hp) as (Ψ & HΨ); rewrite HΨ in HΓ; cbn [body_ctx] in HΓ;
             rewrite <- !app_assoc in HΓ; apply ctx_app_wf_right in HΓ.
      + constructor.
        destruct (ctx_decomp_mod HΓ) as [_ HU].
        destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & (R & HR) & _).
        rewrite <- app_assoc; exact (proj1 (proj2 order_of_denote) _ _ _ _ HR).
      + (* a definition with a module part: its alias's target denotes *)
        destruct (ctx_decomp_dm HΓ) as (_ & _ & _ & HU).
        destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & (R & HR) & _).
        destruct U as [Δ' [sm Φy | E']]; [ constructor |].
        constructor; inversion HR; subst.
        rewrite <- !app_assoc; eapply (proj1 order_of_denote); rewrite ?app_assoc in *; eassumption.
    - (* a closed module: a stored entry *)
      inversion Hok as [| | ? ? ? ? ? Θ0 Ξ0 ? Hg0 Hsub Hloc HaT HsT HT HΘ' Hargs |]; subst.
      destruct (gm_prefix_upto Φ y) as [[| Φ' x E0 | ? ? ?] |] eqn:Hp; try discriminate.
      injection He as <- <- <-; cbn [List.app].
      pose proof (loc_closed _ _ Hg0 _ _ _ Hloc) as [_ HcΦ].
      pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn in HcE; destruct HcE as [_ HcE].
      destruct E0 as [b pv A oM | pv [Δ [sm Φy | E']] | ? ? ? ? ? | pvd Ad Md [Δ [sm Φy | E']] | ? ? ?]; cbn [ge_read];
        try solve [ constructor ].
      + (* a closed submodule: its body has no open *)
        destruct HcE as (-> & HsΔ & HcΦy); cbn [ge_read].
        constructor; constructor; apply body_xp_order_noopen, (body_closed_noopen _ _ HcΦy).
      + (* an alias: valid, so its target denotes *)
        assert (Hloc' : exists Φ', loc Θ Ξ pc T Φ').
        { destruct Hloc as [Hf | Hb].
          - destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hsub Hf) as (Φq & [[Hf' _] | [Hb' _]]); exists Φq; [ left | right ]; assumption.
          - destruct (gc_sub_body _ _ _ _ _ _ _ Hsub Hb) as (Φq & Hb' & _); exists Φq; right; exact Hb'. }
        destruct Hloc' as (Φ'' & Hloc').
        destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & Hent).
        pose proof (proj2 (loc_entry _ _ Hg0 _ _ _ Hloc _ _) Hent) as HeΘ0.
        destruct (gc_sub_entry _ _ _ _ _ _ Hsub HeΘ0) as (E1 & HeΘ & Hgr).
        cbn in Hgr; subst E1.
        pose proof (proj1 (loc_entry _ _ Hg _ _ _ Hloc' _ _) HeΘ) as Hent1.
        destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ (proj2 (loc_closed _ _ Hg _ _ _ Hloc'))) Hent1) as (Φ0' & Hp1).
        destruct (loc_valid _ _ _ _ _ Hv Hloc') as [_ HvΦ].
        pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ HvΦ Hp1) as HE0.
        cbn [ge_valid syn_V] in HE0; destruct HE0 as (_ & HΔ & Hcl).
        rewrite gunit_scoped_mk in HcE; destruct HcE as [HsΔ _].
        pose proof (closed_tele_wf _ _ _ _ HsΔ HΔ (ctx_app_wf_tail _ _ _ _ HΘ')) as HΔΓ.
        destruct (proj1 (Hcl _ HΔΓ)) as (R & HR).
        constructor; constructor; exact (proj1 order_of_denote _ _ _ HR).
      + (* a definition with a module part: valid, so its module part's
           target denotes *)
        assert (Hloc' : exists Φ', loc Θ Ξ pc T Φ').
        { destruct Hloc as [Hf | Hb].
          - destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hsub Hf) as (Φq & [[Hf' _] | [Hb' _]]); exists Φq; [ left | right ]; assumption.
          - destruct (gc_sub_body _ _ _ _ _ _ _ Hsub Hb) as (Φq & Hb' & _); exists Φq; right; exact Hb'. }
        destruct Hloc' as (Φ'' & Hloc').
        destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & Hent).
        pose proof (proj2 (loc_entry _ _ Hg0 _ _ _ Hloc _ _) Hent) as HeΘ0.
        destruct (gc_sub_entry _ _ _ _ _ _ Hsub HeΘ0) as (E1 & HeΘ & Hgr).
        cbn in Hgr; subst E1.
        pose proof (proj1 (loc_entry _ _ Hg _ _ _ Hloc' _ _) HeΘ) as Hent1.
        destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ (proj2 (loc_closed _ _ Hg _ _ _ Hloc'))) Hent1) as (Φ0' & Hp1).
        destruct (loc_valid _ _ _ _ _ Hv Hloc') as [_ HvΦ].
        pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ HvΦ Hp1) as HE0.
        cbn [ge_valid syn_V] in HE0; destruct HE0 as [(_ & HΔ & Hcl) _].
        destruct HcE as (_ & _ & HsU); rewrite gunit_scoped_mk in HsU; destruct HsU as [HsΔ _].
        pose proof (closed_tele_wf _ _ _ _ HsΔ HΔ (ctx_app_wf_tail _ _ _ _ HΘ')) as HΔΓ.
        destruct (proj1 (Hcl _ HΔΓ)) as (R & HR).
        constructor; exact (proj1 order_of_denote _ _ _ HR).
  Qed.

  (** A selection from a module expression whose descriptions are typed. *)
  Lemma mdenote_order_mem : forall Γ H y, mdenote_order Θ Ξ Γ H ->
      (forall R0, mdenote Θ Ξ Γ H R0 -> desc_ok Θ Ξ Γ R0) -> mdenote_order Θ Ξ Γ (me_mem H y).
  Proof.
    intros * Ho Hok; apply mdenote_order_mem_case; [ exact Ho |].
    intros * Hm Hd He; eapply edenote_order_entry; [| exact He ].
    exact (desc_ok_mod _ _ Hg _ _ _ (Hok _ Hm) Hd).
  Qed.

  Corollary mdenote_order_of_wf : forall Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote_order Θ Ξ Γ H.
  Proof.
    intros * HH.
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HH) as (_ & (R & _ & HR & _) & _).
    exact (proj1 order_of_denote _ _ _ HR).
  Qed.

  Corollary mdenote_order_mem_of_wf : forall Γ H H' y, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> mdenote_order Θ Ξ Γ (me_mem H y).
  Proof.
    intros * HH; apply mdenote_order_mem; [ exact (mdenote_order_of_wf _ _ _ HH) |].
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HH (gctx_valid_syn _ _ Hg)) as (_ & Hok & _).
    exact Hok.
  Qed.

  (** What an open of a well-formed module expression generates has an order. *)
  Corollary items_gen_order_of_wf : forall Γ H H' its, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> items_gen_order Θ Ξ Γ H its.
  Proof.
    intros * HH; induction its as [| [[[n |] d] pv] its IH]; constructor; auto.
    eapply mdenote_order_mem_of_wf; exact HH.
  Qed.
End Orders.
