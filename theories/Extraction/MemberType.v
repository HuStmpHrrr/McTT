(** * Computing Descriptions

    [mdenote_impl] decides [mdenote], together with what units and entries
    denote ([udenote], [edenote]), the expansion of bodies ([body_xp]) and
    what an open generates ([items_gen]), by recursion on a termination
    order ([dn_order]) that mirrors their recursion: a slot is read through
    the unit the context gives it, a selection through the entry the
    description of its module gives, and an open through its target in the
    context of the expanded body before it.  Wherever a lookup succeeds, the
    order asks for an order of what it found, so every module expression
    that denotes has an order ([dn_order_of_mdenote]); so does a selection
    from a well-formed module expression ([dn_order_mem_of_wf]), since the
    entries of the description of a well-formed module expression denote. *)

From Stdlib Require Import Lia List PeanoNat String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Paths DescTyping Presup.
Import Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Termination Order *)

Inductive dn_order (Θ : gdeps) (Ξ : gstack) : ctx -> modexp -> Prop :=
| dno_unit : forall Γ H TΦ,
    gc_unit Θ Ξ H = Some TΦ ->
    dn_order Θ Ξ Γ H
| dno_path : forall Γ fp,
    dn_order Θ Ξ Γ (me_unit fp)
| dno_var : forall Γ x,
    (forall U, ctx_find_mod Γ x = Some U -> un_order Θ Ξ Γ U) ->
    dn_order Θ Ξ Γ (me_var x)
| dno_lit : forall Γ U,
    un_order Θ Ξ Γ U ->
    dn_order Θ Ξ Γ (me_lit U)
| dno_app : forall Γ H N,
    dn_order Θ Ξ Γ H ->
    dn_order Θ Ξ Γ (me_app H N)
| dno_mem : forall Γ H y,
    dn_order Θ Ξ Γ H ->
    (forall R0 R0m Γy E rd, mdenote Θ Ξ Γ H R0 -> ds_mod Θ Ξ R0 = Some R0m ->
       ds_entry R0m y = Some (Γy, E, rd) -> en_order Θ Ξ (Γy ++ Γ) E) ->
    dn_order Θ Ξ Γ (me_mem H y)
with un_order (Θ : gdeps) (Ξ : gstack) : ctx -> gunit -> Prop :=
| uno_body : forall Γ Δ sm Φ,
    bx_order Θ Ξ (Δ ++ Γ) Φ ->
    un_order Θ Ξ Γ (gu_mk Δ (md_body sm Φ))
| uno_alias : forall Γ Δ E,
    dn_order Θ Ξ (Δ ++ Γ) E ->
    un_order Θ Ξ Γ (gu_mk Δ (md_alias E))
with en_order (Θ : gdeps) (Ξ : gstack) : ctx -> gentry -> Prop :=
| eno_def : forall Γ b pv A oM, en_order Θ Ξ Γ (ge_def b pv A oM)
| eno_mod : forall Γ pv U,
    un_order Θ Ξ Γ U ->
    en_order Θ Ξ Γ (ge_mod pv U)
| eno_ind : forall Γ pv p D Φ, en_order Θ Ξ Γ (ge_ind pv p D Φ)
| eno_ind_alias : forall Γ pv Δ pq Ns, en_order Θ Ξ Γ (ge_ind_alias pv Δ pq Ns)
with bx_order (Θ : gdeps) (Ξ : gstack) : ctx -> gmod -> Prop :=
| bxo_nil : forall Γ, bx_order Θ Ξ Γ gm_nil
| bxo_ext : forall Γ Φ x E,
    bx_order Θ Ξ Γ Φ ->
    bx_order Θ Ξ Γ (gm_ext Φ x E)
| bxo_open : forall Γ Φ H its,
    bx_order Θ Ξ Γ Φ ->
    (forall Φx, body_xp Θ Ξ Γ Φ Φx -> dn_order Θ Ξ (body_ctx Φx ++ Γ) H) ->
    (forall Φx, body_xp Θ Ξ Γ Φ Φx -> ig_order Θ Ξ (body_ctx Φx ++ Γ) H its) ->
    bx_order Θ Ξ Γ (gm_open Φ H its)
with ig_order (Θ : gdeps) (Ξ : gstack) : ctx -> modexp -> list iitem -> Prop :=
| igo_nil : forall Γ H, ig_order Θ Ξ Γ H nil
| igo_self : forall Γ H d pv its,
    ig_order Θ Ξ Γ H its ->
    ig_order Θ Ξ Γ H ((None, d, pv) :: its)
| igo_name : forall Γ H n d pv its,
    dn_order Θ Ξ Γ (me_mem H n) ->
    ig_order Θ Ξ Γ H its ->
    ig_order Θ Ξ Γ H ((Some n, d, pv) :: its).

Scheme dn_order_mut_ind := Induction for dn_order Sort Prop
with un_order_mut_ind := Induction for un_order Sort Prop
with en_order_mut_ind := Induction for en_order Sort Prop
with bx_order_mut_ind := Induction for bx_order Sort Prop
with ig_order_mut_ind := Induction for ig_order Sort Prop.

(** ** The Decision Procedure *)

(** The conditions of an open on its own items, decided. *)
Definition items_ok_dec (its : list iitem) : { items_ok its } + { ~ items_ok its }.
Proof.
  unfold items_ok.
  destruct (both_dup its) as [n |]; [ right; intros [H _]; discriminate |].
  destruct (name_dup (List.map iitem_name its)) as [n |]; [ right; intros [_ H]; discriminate | left; split; reflexivity ].
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

Section DenoteImpl.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  Definition inspect {A} (a : A) : { b | a = b } := exist _ a eq_refl.

  #[local]
  Ltac dn_close :=
    repeat match goal with
      | H1 : mdenote Θ Ξ ?G ?H ?A1, H2 : mdenote Θ Ξ ?G ?H ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          pose proof (proj1 (mdenote_functional_all _ _ Hg) _ _ _ H1 _ H2); subst; clear H2
      | H1 : udenote Θ Ξ ?G ?o ?U ?A1, H2 : udenote Θ Ξ ?G ?o ?U ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          pose proof (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : edenote Θ Ξ ?G ?o ?E ?A1, H2 : edenote Θ Ξ ?G ?o ?E ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          pose proof (proj1 (proj2 (proj2 (mdenote_functional_all _ _ Hg))) _ _ _ _ H1 _ H2); subst; clear H2
      | H1 : body_xp Θ Ξ ?G ?Φ ?A1, H2 : body_xp Θ Ξ ?G ?Φ ?A2 |- _ =>
          assert_fails (constr_eq A1 A2);
          pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ H1 _ H2); subst; clear H2
      | H1 : items_gen Θ Ξ ?b ?G ?H ?its ?A1, H2 : items_gen Θ Ξ ?b ?G ?H ?its ?A2 |- _ =>
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
          | match goal with HN : forall r, ~ _ |- _ => solve [ eapply HN; eassumption ] end
          | intuition congruence
          | cbn in *; contradiction ].

  #[local]
  Ltac dn_neg_after := rewrite ?gc_unit_var, ?gc_unit_lit, ?gc_unit_app in *; dn_close; dn_finish.

  #[local]
  Ltac dn_neg :=
    match goal with
    | Hm : mdenote _ _ _ _ _ |- _ => inversion Hm; subst; clear Hm; dn_neg_after
    | Hm : udenote _ _ _ _ _ _ |- _ => inversion Hm; subst; clear Hm; dn_neg_after
    | Hm : edenote _ _ _ _ _ _ |- _ => inversion Hm; subst; clear Hm; dn_neg_after
    | Hm : body_xp _ _ _ _ _ |- _ => inversion Hm; subst; clear Hm; dn_neg_after
    | Hm : items_gen _ _ _ _ _ _ _ |- _ => inversion Hm; subst; clear Hm; dn_neg_after
    end.

  #[local]
  Ltac impl_obl_tac :=
    intros; cbv beta in *;
    repeat match goal with
      | H : dn_order _ _ _ _ |- _ => progressive_invert H
      | H : un_order _ _ _ _ |- _ => progressive_invert H
      | H : en_order _ _ _ _ |- _ => progressive_invert H
      | H : bx_order _ _ _ _ |- _ => progressive_invert H
      | H : ig_order _ _ _ _ _ |- _ => progressive_invert H
      | Ho : dn_order _ _ _ (me_mem _ _), Eu : gc_unit _ _ (me_mem _ _) = None |- _ =>
          inversion Ho; subst; clear Ho; [ congruence |]
      end;
    rewrite ?gc_unit_var, ?gc_unit_lit, ?gc_unit_app in *;
    try solve [ congruence | eauto ];
    lazymatch goal with
    | |- False => dn_neg
    | |- ~ _ => let Hd := fresh "Hd" in intros Hd; dn_neg
    | |- forall _, ~ _ => let r := fresh "r" in let Hd := fresh "Hd" in intros r Hd; dn_neg
    | _ => try solve [ econstructor; eauto using ctx_find_mod_sound; cbn; auto ]
    end.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations mdenote_impl Γ H (Ho : dn_order Θ Ξ Γ H) :
      { R | mdenote Θ Ξ Γ H R } + { forall R, ~ mdenote Θ Ξ Γ H R } by struct Ho :=
  | Γ, me_unit fp, Ho with inspect (gc_unit Θ Ξ (me_unit fp)) := {
    | exist _ (Some (T, Φ)) Eu => inleft (exist _ (ds_closed nil (q_abs fp nil) T Φ nil) _)
    | exist _ None Eu => inright _ }
  | Γ, me_var x, Ho with inspect (ctx_find_mod Γ x) := {
    | exist _ (Some U) Ef with udenote_impl Γ None U _ := {
      | inleft (exist _ R HR) => inleft (exist _ R _)
      | inright HN => inright _ }
    | exist _ None Ef => inright _ }
  | Γ, me_lit U, Ho with udenote_impl Γ None U _ := {
    | inleft (exist _ R HR) => inleft (exist _ R _)
    | inright HN => inright _ }
  | Γ, me_app H N, Ho with mdenote_impl Γ H _ := {
    | inleft (exist _ R HR) with inspect (ds_at R N) := {
      | exist _ (Some R') Ea => inleft (exist _ R' _)
      | exist _ None Ea => inright _ }
    | inright HN => inright _ }
  | Γ, me_mem H y, Ho with inspect (gc_unit Θ Ξ (me_mem H y)) := {
    | exist _ (Some (T, Φ)) Eu with inspect (mod_qname H) := {
      | exist _ (Some p) Eqp =>
          inleft (exist _ (ds_closed nil (qname_in p y) T Φ nil) (dn_unit _ _ _ _ _ _ _ (mod_qname_mem_in _ _ _ Eqp) Eu))
      | exist _ None Eqp => False_rect _ (gc_unit_mem_qname _ _ _ _ _ Eu Eqp) }
    | exist _ None Eu with mdenote_impl Γ H _ := {
      | inright HN => inright _
      | inleft (exist _ R0 HR0) with inspect (ds_mod Θ Ξ R0) := {
        | exist _ None Em => inright _
        | exist _ (Some R0m) Em with inspect (ds_entry R0m y) := {
          | exist _ None Ee => inright _
          | exist _ (Some (Γy, E, rd)) Ee with edenote_impl (Γy ++ Γ) (ds_epath R0m y) E _ := {
            | inright HN => inright _
            | inleft (exist _ R HR) with inspect (ds_read rd R) := {
              | exist _ None Er => inright _
              | exist _ (Some R') Er => inleft (exist _ R' _) } } } } } }

  with udenote_impl Γ o U (Ho : un_order Θ Ξ Γ U) :
      { R | udenote Θ Ξ Γ o U R } + { forall R, ~ udenote Θ Ξ Γ o U R } by struct Ho :=
  | Γ, o, gu_mk Δ (md_body sm Φ), Ho with body_xp_impl (Δ ++ Γ) Φ _ := {
    | inleft (exist _ Φx Hx) with inspect (ds_body o sm Δ Φ Φx) := {
      | exist _ (Some R) Eb => inleft (exist _ R _)
      | exist _ None Eb => inright _ }
    | inright HN => inright _ }
  | Γ, o, gu_mk Δ (md_alias E), Ho with mdenote_impl (Δ ++ Γ) E _ := {
    | inright HN => inright _
    | inleft (exist _ R HR) with inspect (ds_mod Θ Ξ R) := {
      | exist _ (Some R') Em => inleft (exist _ (ds_up Δ R') _)
      | exist _ None Em => inright _ } }

  with edenote_impl Γ o E (Ho : en_order Θ Ξ Γ E) :
      { R | edenote Θ Ξ Γ o E R } + { forall R, ~ edenote Θ Ξ Γ o E R } by struct Ho :=
  | Γ, o, ge_def b pv A oM, Ho => inleft (exist _ (ds_term A (if b then oM else None)) _)
  | Γ, o, ge_mod pv U, Ho with udenote_impl Γ o U _ := {
    | inleft (exist _ R HR) => inleft (exist _ R _)
    | inright HN => inright _ }
  | Γ, o, ge_ind pv p D Φ, Ho => inleft (exist _ (ds_ind nil p nil) _)
  | Γ, o, ge_ind_alias pv Δ pq Ns, Ho => inleft (exist _ (ds_ind Δ pq Ns) _)

  with body_xp_impl Γ Φ (Ho : bx_order Θ Ξ Γ Φ) :
      { Φx | body_xp Θ Ξ Γ Φ Φx } + { forall Φx, ~ body_xp Θ Ξ Γ Φ Φx } by struct Ho :=
  | Γ, gm_nil, Ho => inleft (exist _ gm_nil _)
  | Γ, gm_ext Φ x E, Ho with body_xp_impl Γ Φ _ := {
    | inleft (exist _ Φx Hx) => inleft (exist _ (gm_ext Φx x E) _)
    | inright HN => inright _ }
  | Γ, gm_open Φ H its, Ho with body_xp_impl Γ Φ _ := {
    | inright HN => inright _
    | inleft (exist _ Φx Hx) with mdenote_impl (body_ctx Φx ++ Γ) H _ := {
      | inright HN => inright _
      | inleft (exist _ R HR) with inspect (ds_mod Θ Ξ R) := {
        | exist _ None Em => inright _
        | exist _ (Some Rm) Em with items_gen_impl false (body_ctx Φx ++ Γ) H its _ := {
          | inright HN => inright _
          | inleft (exist _ gs Hgs) with items_ok_dec its := {
            | left Hok => inleft (exist _ (gens_append Φx 0 gs) _)
            | right Hn => inright _ } } } } }

  with items_gen_impl g Γ H its (Ho : ig_order Θ Ξ Γ H its) :
      { gs | items_gen Θ Ξ g Γ H its gs } + { forall gs, ~ items_gen Θ Ξ g Γ H its gs } by struct Ho :=
  | g, Γ, H, nil, Ho => inleft (exist _ nil _)
  | g, Γ, H, (None, d, pv) :: its, Ho with items_gen_impl g Γ H its _ := {
    | inleft (exist _ gs Hgs) => inleft (exist _ (ig_alias d pv H :: gs) _)
    | inright HN => inright _ }
  | g, Γ, H, (Some n, d, pv) :: its, Ho with mdenote_impl Γ (me_mem H n) _ := {
    | inright HN => inright _
    | inleft (exist _ (ds_term A om) HR) with items_gen_impl g Γ H its _ := {
      | inleft (exist _ gs Hgs) => inleft (exist _ (ig_def d pv A (a_mem H n) :: gs) _)
      | inright HN => inright _ }
    | inleft (exist _ (ds_open Δ Φ Φx) HR) with items_gen_impl g Γ H its _ := {
      | inleft (exist _ gs Hgs) => inleft (exist _ (ig_alias d pv (me_mem H n) :: gs) _)
      | inright HN => inright _ }
    | inleft (exist _ (ds_closed Θ' pc T Φ Ns) HR) with items_gen_impl g Γ H its _ := {
      | inleft (exist _ gs Hgs) => inleft (exist _ (ig_alias d pv (me_mem H n) :: gs) _)
      | inright HN => inright _ }
    | inleft (exist _ (ds_ind Θ' p Ns) HR) with g := {
      | false => inright _
      | true with items_gen_impl true Γ H its _ := {
        | inleft (exist _ gs Hgs) => inleft (exist _ (ig_ind_alias d pv Θ' p Ns :: gs) _)
        | inright HN => inright _ } } }.
End DenoteImpl.

(** ** What Denotes Has an Order *)

Section Orders.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  Theorem order_of_denote :
    (forall Γ H R, mdenote Θ Ξ Γ H R -> dn_order Θ Ξ Γ H) /\
    (forall Γ o U R, udenote Θ Ξ Γ o U R -> un_order Θ Ξ Γ U) /\
    (forall Γ o E R, edenote Θ Ξ Γ o E R -> en_order Θ Ξ Γ E) /\
    (forall Γ Φ Φx, body_xp Θ Ξ Γ Φ Φx -> bx_order Θ Ξ Γ Φ) /\
    (forall g Γ H its gs, items_gen Θ Ξ g Γ H its gs -> ig_order Θ Ξ Γ H its).
  Proof.
    pose proof (mdenote_functional_all _ _ Hg) as (Fm & Fu & Fe & Fb & Fi).
    apply mdenote_all_ind; intros.
    - eapply dno_unit; eassumption.
    - apply dno_var; intros U' Hf.
      match goal with Hl : _ ∋ # _ ≔ₘ _ |- _ => rewrite (ctx_find_mod_complete _ _ _ Hl) in Hf end.
      injection Hf as <-; assumption.
    - constructor; assumption.
    - constructor; assumption.
    - apply dno_mem; [ assumption |].
      intros R1 R1m Γy' E' rd' Hm1 Hd1 He1.
      match goal with Hm0 : mdenote _ _ _ H _ |- _ => rewrite <- (Fm _ _ _ Hm0 _ Hm1) in Hd1 end.
      match goal with Hd0 : ds_mod _ _ _ = Some _ |- _ => rewrite Hd0 in Hd1; injection Hd1 as <- end.
      match goal with He0 : ds_entry _ _ = Some _ |- _ => rewrite He0 in He1; injection He1 as <- <- <- end.
      assumption.
    - constructor; assumption.
    - constructor; assumption.
    - constructor.
    - constructor; assumption.
    - constructor.
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

  Lemma bx_order_noopen : forall Γ Φ, gm_noopen Φ -> bx_order Θ Ξ Γ Φ.
  Proof.
    intros Γ; induction Φ as [| Φ IH x E | Φ IH H its]; intros Hn; cbn in Hn; [ constructor | constructor; auto | contradiction ].
  Qed.

  (** The entries of a typed module description denote, hence have an
      order: those of an open one are slots of its well-formed extended
      context, and those of a closed one are stored, so valid. *)
  Lemma en_order_entry : forall Γ Rm y Γy E rd,
      desc_ok Θ Ξ Γ Rm -> ds_entry Rm y = Some (Γy, E, rd) -> en_order Θ Ξ (Γy ++ Γ) E.
  Proof.
    pose proof (gctx_valid_syn _ _ Hg) as Hv.
    intros * Hok He; destruct Rm as [A om | Δ Φw Φ | Θ' pc T Φ Ns | Θ' p Ns]; cbn in He; try discriminate.
    - (* an open module: a slot of its extended context *)
      inversion Hok as [| | ? ? ? ? HΓ Hno Hsub |]; subst.
      destruct (gm_prefix_upto Φ y) as [[| Φ' x E0 | ? ? ?] |] eqn:Hp; try discriminate.
      destruct E0 as [[|] pv A [M |] | pv U | ? ? ? ? | ? ? ? ?]; try discriminate; injection He as <- <- <-;
        [ constructor |].
      constructor.
      destruct (gm_prefix_body_ctx _ _ _ Hno Hp) as (Ψ & HΨ); rewrite HΨ in HΓ; cbn [body_ctx] in HΓ.
      rewrite <- !app_assoc in HΓ; apply ctx_app_wf_right in HΓ.
      destruct (ctx_decomp_mod HΓ) as [_ HU].
      destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & (R & HR) & _).
      rewrite <- app_assoc; exact (proj1 (proj2 order_of_denote) _ _ _ _ HR).
    - (* a closed module: a stored entry *)
      inversion Hok as [| | | ? ? ? ? ? Θ0 Ξ0 ? Hg0 Hsub Hloc HaT HsT HT HΘ' Hargs]; subst.
      destruct (gm_prefix_upto Φ y) as [[| Φ' x E0 | ? ? ?] |] eqn:Hp; try discriminate.
      injection He as <- <- <-; cbn [List.app].
      pose proof (loc_closed _ _ Hg0 _ _ _ Hloc) as [_ HcΦ].
      pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn in HcE; destruct HcE as [_ HcE].
      destruct E0 as [b pv A oM | pv [Δ [sm Φy | E']] | ? ? ? ? | ? ? ? ?]; cbn [ge_read];
        try solve [ constructor ].
      + (* a closed submodule: its body has no open *)
        destruct HcE as (-> & HsΔ & HcΦy); cbn [ge_read].
        constructor; constructor; apply bx_order_noopen, (body_closed_noopen _ _ HcΦy).
      + (* an alias: valid, so its target denotes *)
        assert (Hloc' : exists Φ', loc Θ Ξ pc T Φ').
        { destruct Hloc as [Hf | Hb].
          - destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hsub Hf) as (Φq & [Hf' | [Hb' _]]); exists Φq; [ left | right ]; assumption.
          - destruct (gc_sub_body _ _ _ _ _ _ _ Hsub Hb) as (Φq & Hb' & _); exists Φq; right; exact Hb'. }
        destruct Hloc' as (Φ'' & Hloc').
        destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & Hent).
        pose proof (proj2 (loc_entry _ _ Hg0 _ _ _ Hloc _ _) Hent) as HeΘ0.
        destruct (gc_sub_entry _ _ _ _ _ _ Hsub HeΘ0) as (E1 & HeΘ & Hgr).
        cbn in Hgr; subst E1.
        pose proof (proj1 (loc_entry _ _ Hg _ _ _ Hloc' _ _) HeΘ) as Hent1.
        destruct (gm_entry_prefix _ _ _ (body_closed_noopen _ _ (proj2 (loc_closed _ _ Hg _ _ _ Hloc'))) Hent1) as (Φ0' & Hp1).
        destruct (loc_valid _ _ _ _ _ Hv Hloc') as [_ HvΦ].
        pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ HvΦ Hp1) as HE0.
        cbn [ge_valid syn_V] in HE0; destruct HE0 as (_ & HΔ & Hcl).
        rewrite gunit_scoped_mk in HcE; destruct HcE as [HsΔ _].
        pose proof (closed_tele_wf _ _ _ _ HsΔ HΔ (ctx_app_wf_tail _ _ _ _ HΘ')) as HΔΓ.
        destruct (proj1 (Hcl _ HΔΓ)) as (R & HR).
        constructor; constructor; exact (proj1 order_of_denote _ _ _ HR).
  Qed.

  (** A selection from a module expression whose descriptions are typed. *)
  Lemma dn_order_mem : forall Γ H y, dn_order Θ Ξ Γ H ->
      (forall R0, mdenote Θ Ξ Γ H R0 -> desc_ok Θ Ξ Γ R0) -> dn_order Θ Ξ Γ (me_mem H y).
  Proof.
    intros * Ho Hok; apply dno_mem; [ exact Ho |].
    intros * Hm Hd He; eapply en_order_entry; [| exact He ].
    exact (desc_ok_mod _ _ Hg _ _ _ (Hok _ Hm) Hd).
  Qed.

  Corollary dn_order_of_wf : forall Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> dn_order Θ Ξ Γ H.
  Proof.
    intros * HH.
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HH) as (_ & (R & _ & HR & _) & _).
    exact (proj1 order_of_denote _ _ _ HR).
  Qed.

  Corollary dn_order_mem_of_wf : forall Γ H H' y, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> dn_order Θ Ξ Γ (me_mem H y).
  Proof.
    intros * HH; apply dn_order_mem; [ exact (dn_order_of_wf _ _ _ HH) |].
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 desc_typed)))))) _ _ _ _ _ HH (gctx_valid_syn _ _ Hg)) as (_ & Hok & _).
    exact Hok.
  Qed.

  (** What an open of a well-formed module expression generates has an order. *)
  Corollary ig_order_of_wf : forall Γ H H' its, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> ig_order Θ Ξ Γ H its.
  Proof.
    intros * HH; induction its as [| [[[n |] d] pv] its IH]; constructor; auto.
    eapply dn_order_mem_of_wf; exact HH.
  Qed.
End Orders.
