(** * Checking Privacy

    [decl_impl] computes where a member reached from a unit is declared, by
    recursion on the order [mt_order] of member types, which follows aliases
    exactly as [mdecl] does.  [refs_check] decides [acc_ok], and names the
    first private member that is out of reach. *)

From Stdlib Require Import List String.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Paths DescTyping Presup.
From Mctt.Core.Syntactic.System Require Import Privacy.
From Mctt.Extraction Require Import Lookup FastDesc LookupTwins MemberType.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** ** Where a Module Is Stored, and What It Denotes

    A module expression stored at [pq] ([msite]) denotes a module read off
    what is stored there: a closed module stored at [pq], or a term part
    with a module part that is a closed module stored at [pq] ([site_desc]):
    a definition with a module part, or the type former of the member of an
    inductive group or of the record type stored at [pq]. *)

(** A closed module stored at [pq]. *)
Definition site_closed (Θ : gdeps) (Ξ : gstack) (pq : qname) (R : mdesc) : Prop :=
  exists Θ' T Φ Ns, R = ds_closed Θ' pq T Φ Ns /\ loc Θ Ξ pq T Φ.

(** Read off what is stored at [pq]: a closed module there, or a term part
    with such a module part. *)
Definition site_desc (Θ : gdeps) (Ξ : gstack) (pq : qname) (R : mdesc) : Prop :=
  site_closed Θ Ξ pq R \/
  (exists Θd A M Rm, R = ds_dm Θd A M Rm /\ site_closed Θ Ξ pq Rm).

Section SiteDesc.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  Lemma site_closed_at : forall pq R N R', site_closed Θ Ξ pq R -> ds_at R N = Some R' -> site_closed Θ Ξ pq R'.
  Proof.
    intros * (Θ' & T & Φ & Ns & -> & Hl) Ha; cbn in Ha.
    destruct (tele_split (rev Θ')) as [[[? ?] ?] | ?]; injection Ha as <-; do 4 eexists; (split; [ reflexivity | exact Hl ]).
  Qed.

  Lemma site_closed_ats : forall Ns pq R R', site_closed Θ Ξ pq R -> ds_ats R Ns = Some R' -> site_closed Θ Ξ pq R'.
  Proof.
    induction Ns as [| N Ns IH]; intros * Hs Ha; cbn in Ha; [ injection Ha as <-; exact Hs |].
    destruct (ds_at R N) as [R1 |] eqn:E; [| discriminate ].
    exact (IH _ _ _ (site_closed_at _ _ _ _ Hs E) Ha).
  Qed.

  Lemma site_closed_up : forall pq Θ' R, site_closed Θ Ξ pq R -> site_closed Θ Ξ pq (ds_up Θ' R).
  Proof. intros * (Θ0 & T & Φ & Ns & -> & Hl); cbn [ds_up]; do 4 eexists; split; [ reflexivity | exact Hl ]. Qed.

  Lemma site_closed_sub : forall pq R σ, site_closed Θ Ξ pq R -> site_closed Θ Ξ pq (ds_sub R σ).
  Proof. intros * (Θ0 & T & Φ & Ns & -> & Hl); cbn [ds_sub]; do 4 eexists; split; [ reflexivity | exact Hl ]. Qed.

  Lemma site_desc_at : forall pq R N R', site_desc Θ Ξ pq R -> ds_at R N = Some R' -> site_desc Θ Ξ pq R'.
  Proof.
    intros * [Hc | (Θd & A & M & Rm & -> & Hc)] Ha.
    - left; exact (site_closed_at _ _ _ _ Hc Ha).
    - (* a term part with a module part: its module part at [N] *)
      cbn in Ha; destruct (ds_at Rm N) as [Rm' |] eqn:E; [| discriminate ].
      pose proof (site_closed_at _ _ _ _ Hc E) as Hc'.
      destruct (tele_split (rev Θd)) as [[[? ?] ?] | ?]; injection Ha as <-; [ right; do 4 eexists; split; [ reflexivity | exact Hc' ] | left; exact Hc' ].
  Qed.

  Lemma site_desc_ats : forall Ns pq R R', site_desc Θ Ξ pq R -> ds_ats R Ns = Some R' -> site_desc Θ Ξ pq R'.
  Proof.
    induction Ns as [| N Ns IH]; intros * Hs Ha; cbn in Ha; [ injection Ha as <-; exact Hs |].
    destruct (ds_at R N) as [R1 |] eqn:E; [| discriminate ].
    exact (IH _ _ _ (site_desc_at _ _ _ _ Hs E) Ha).
  Qed.

  Lemma site_desc_up : forall pq Θ' R, site_desc Θ Ξ pq R -> site_desc Θ Ξ pq (ds_up Θ' R).
  Proof.
    intros * [Hc | (Θd & A & M & Rm & -> & Hc)]; cbn [ds_up].
    - left; exact (site_closed_up _ _ _ Hc).
    - right; do 4 eexists; split; [ reflexivity | exact (site_closed_up _ _ _ Hc) ].
  Qed.

  Lemma site_desc_sub : forall pq R σ, site_desc Θ Ξ pq R -> site_desc Θ Ξ pq (ds_sub R σ).
  Proof.
    intros * [Hc | (Θd & A & M & Rm & -> & Hc)]; cbn [ds_sub].
    - left; exact (site_closed_sub _ _ _ Hc).
    - right; do 4 eexists; split; [ reflexivity | exact (site_closed_sub _ _ _ Hc) ].
  Qed.

  Lemma site_desc_read : forall pq rd R R', site_desc Θ Ξ pq R -> ds_read rd R = Some R' -> site_desc Θ Ξ pq R'.
  Proof.
    intros * Hs Hr; destruct rd as [Θ' Φ' | Θ' Ns]; cbn [ds_read] in Hr.
    - destruct (gm_fill Φ') as [σ |]; cbn in Hr; [ injection Hr as <- | discriminate ].
      apply site_desc_up, site_desc_sub; exact Hs.
    - destruct (ds_ats_read R Ns) as [R1 |] eqn:E; cbn in Hr; [| discriminate ]; injection Hr as <-.
      apply site_desc_up.
      assert (Hs1 : site_desc Θ Ξ pq R1).
      { destruct (ds_ats_read_inv _ _ _ E) as [Ha | (A & M & Rm & B & M' & Rm' & -> & -> & _ & Ha)];
          [ exact (site_desc_ats _ _ _ _ Hs Ha) |].
        destruct Hs as [(? & ? & ? & ? & [=] & _) | (Θd & A1 & M1 & Rm1 & [= <- <- <- <-] & Hc)].
        right; do 4 eexists; split; [ reflexivity | exact (site_closed_ats _ _ _ _ Hc Ha) ]. }
      apply (ds_named_cases (site_desc Θ Ξ pq)); [ exact Hs1 |].
      destruct Hs1 as [(Θ0 & T & Φ & Ns0 & -> & Hl) | (Θd & A & M & Rm & -> & Hc)]; cbn [ds_self].
      + left; do 4 eexists; split; [ reflexivity | exact Hl ].
      + right; do 4 eexists; split; [ reflexivity | exact Hc ].
  Qed.

  (** The module part of a description read off storage is stored there. *)
  Lemma site_desc_mod : forall pq R Rm, site_desc Θ Ξ pq R -> ds_mod R = Some Rm ->
      exists Θ' T Φ Ns, Rm = ds_closed Θ' pq T Φ Ns /\ loc Θ Ξ pq T Φ.
  Proof.
    intros * [(Θ' & T & Φ & Ns & -> & Hl) | (Θd & A & M & Rm0 & -> & (Θ' & T & Φ & Ns' & -> & Hl))] Hm; cbn in Hm;
      injection Hm as <-; (do 4 eexists; split; [ reflexivity | exact Hl ]).
  Qed.

  Lemma mdenote_apps : forall Ns Γ H R R', mdenote Θ Ξ Γ H R -> ds_ats R Ns = Some R' -> mdenote Θ Ξ Γ (me_apps H Ns) R'.
  Proof.
    induction Ns as [| N Ns IH]; intros * Hm Ha; cbn in Ha |- *; [ injection Ha as <-; exact Hm |].
    destruct (ds_at R N) as [R1 |] eqn:E; [| discriminate ].
    apply (IH _ _ R1); [ eapply mdenote_app; eassumption | exact Ha ].
  Qed.

  (** An open frame, of either kind, named by its path, is stored there. *)
  Lemma site_of_frame : forall H p TΦ, mod_qname H = Some p -> gc_frame Ξ p = Some TΦ -> msite Θ Ξ H p.
  Proof.
    intros * Hq Hf; destruct TΦ as [T Φ].
    destruct (gs_find_ind Ξ p) as [r |] eqn:Hk; [ exact (ms_ind_frame _ _ _ _ _ Hq Hk) |].
    destruct (gs_find_record Ξ p) as [Rr |] eqn:Hr; [ exact (ms_record_frame _ _ _ _ _ Hq Hr) |].
    exact (ms_unit _ _ _ _ _ _ Hq (gc_unit_frame _ _ _ _ _ _ Hq Hf Hk Hr)).
  Qed.

  (** The member of a stored module expression that is the open frame of a
      member's module is no entry there. *)
  Lemma ind_frame_no_entry : forall H z pq E p r, msite Θ Ξ H pq -> gc_entry Θ Ξ (qname_in pq z) = Some E ->
      mod_qname (me_mem H z) = Some p -> gs_find_ind Ξ p = Some r -> False.
  Proof.
    intros * Hs He Hq Hk.
    cbn in Hq; destruct (mod_qname H) as [p0 |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
    change {| q_unit := q_unit p0; q_chain := q_chain p0 ++ z :: nil |} with (qname_in p0 z) in Hk.
    destruct (gs_find_ind_tele _ _ _ Hk) as (U & T0 & Ht).
    destruct (frame_parent _ _ Hg _ _ _ _ Ht) as (Tq & Φq & Hfq & _).
    pose proof (msite_functional _ _ Hg _ _ Hs _ (site_of_frame _ _ _ Hq0 Hfq)) as ->.
    rewrite (frame_gc_entry_none _ _ _ _ _ Ht) in He; discriminate.
  Qed.

  (** Nor is the open frame of a record type's module. *)
  Lemma record_frame_no_entry : forall H z pq E p Rr, msite Θ Ξ H pq -> gc_entry Θ Ξ (qname_in pq z) = Some E ->
      mod_qname (me_mem H z) = Some p -> gs_find_record Ξ p = Some Rr -> False.
  Proof.
    intros * Hs He Hq Hk.
    cbn in Hq; destruct (mod_qname H) as [p0 |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
    change {| q_unit := q_unit p0; q_chain := q_chain p0 ++ z :: nil |} with (qname_in p0 z) in Hk.
    destruct (gs_find_record_tele _ _ _ Hk) as (U & T0 & Ht).
    destruct (frame_parent _ _ Hg _ _ _ _ Ht) as (Tq & Φq & Hfq & _).
    pose proof (msite_functional _ _ Hg _ _ Hs _ (site_of_frame _ _ _ Hq0 Hfq)) as ->.
    rewrite (frame_gc_entry_none _ _ _ _ _ Ht) in He; discriminate.
  Qed.

  (** What a stored module expression denotes is read off its storage. *)
  Theorem msite_desc : forall H pq, msite Θ Ξ H pq -> forall Γ R, mdenote Θ Ξ Γ H R -> site_desc Θ Ξ pq R.
  Proof.
    induction 1 as [H p T Φ Hq Hu | H p r Hq Hk | H pq z E Hs IH He Hb | H pq z E E' pq' Hs IH He Ha Hs' IH' | H N pq Hs IH
                   | H p Rr Hq Hk];
      intros Γ R Hm.
    - (* a loaded unit or an open frame *)
      rewrite (unit_denote_unique _ _ Hg _ _ _ _ _ _ Hq Hu Hm).
      destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq' & Hl); rewrite Hq in Hq'; injection Hq' as <-.
      left; do 4 eexists; split; [ reflexivity | exact Hl ].
    - (* the open frame of a member's module: the member's type former,
         with its module stored there *)
      destruct r as [[pg k] D].
      destruct (frame_ind_loc _ _ Hg _ _ _ _ Hk) as (U & T0 & T & Φ & Mk & Ht & _ & Hl & HMk).
      rewrite (proj1 (proj2 (frame_denote_unique _ _ Hg _ _ _ _ Hq Hm)) _ _ _ _ _ _ Hk HMk Hl).
      right; do 4 eexists; split; [ reflexivity | do 4 eexists; split; [ reflexivity | exact (gc_loc_loc _ _ _ _ _ Hl) ] ].
    - (* a body module: stored at its own path, an inductive type, or a record type *)
      inversion Hm as [? ? ? ? ? ? Hu | ? ? ? ? ? ? ? ? ? Hq Hk | | | | ? ? ? R0 R0m Γy E0 rd R1 ? Hm0 Hd0 He0 Hed Hr
                      | ? ? ? ? ? ? Hq Hk]; subst.
      + destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq & Hl).
        rewrite (msite_unit _ _ Hg _ _ (ms_body _ _ _ _ _ _ Hs He Hb) _ Hq (or_introl (ex_intro _ _ Hu))).
        match goal with Hq1 : mod_qname _ = Some ?p0 |- _ =>
          assert_fails (constr_eq p0 mp); assert (mp = p0) by congruence; subst mp end.
        left; do 4 eexists; split; [ reflexivity | exact Hl ].
      + (* an open frame of a member's module is no entry *)
        exfalso; exact (ind_frame_no_entry _ _ _ _ _ _ Hs He Hq Hk).
      + destruct (site_desc_mod _ _ _ (IH _ _ Hm0) Hd0) as (Θ' & T & Φ & Ns & -> & Hl).
        cbn in He0; destruct (gm_prefix_upto Φ z) as [[| Φ0 x E1 | ? ? ?] |] eqn:Hp; try discriminate.
        injection He0 as <- <- <-.
        destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & Hent).
        pose proof (proj2 (loc_entry _ _ Hg _ _ _ Hl _ _) Hent) as He1; rewrite He in He1; injection He1 as <-.
        eapply site_desc_read; [| exact Hr ].
        pose proof (loc_closed _ _ Hg _ _ _ Hl) as [_ HcΦ].
        pose proof (body_closed_prefix _ _ _ _ HcΦ Hp) as HcE; cbn in HcE; destruct HcE as [_ HcE].
        destruct E as [| pv [Δ [sm Φy | ?]] | pv pq1 k D Φi | | pv Rr ΦR ]; cbn in Hb; try contradiction.
        * destruct HcE as (-> & HsΔ & HcΦy); cbn [ge_read] in Hed.
          inversion Hed; subst.
          match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
          match goal with Hx : body_xp _ _ _ Φy ?Φx |- _ =>
            pose proof (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ Hx _
                          (body_xp_noopen Θ Ξ _ _ (body_closed_noopen _ _ HcΦy))) as <- end.
          match goal with Hbd : ds_body _ _ _ _ _ = Some _ |- _ => cbn in Hbd; injection Hbd as <- end.
          left; do 4 eexists; split; [ reflexivity |].
          right; exact (proj1 (loc_child_mod _ _ Hg _ _ _ Hl _ _ _ _ _ Hent)).
        * (* an inductive type: its type former, with its module stored at
             its path *)
          cbn [ge_read] in Hed; inversion Hed as [| | ? ? ? ? ? ? ? Mk pm Tm Φm HMk Hpm Hlm | |]; subst.
          destruct (ind_mlookup_selfpath _ _ Hg _ _ _ _ (proj2 (gc_entry_ind _ _ _ _ _ _ _ _ He))) as [Hmp _ _].
          rewrite Hmp in Hpm; injection Hpm as <-.
          right; do 4 eexists; split; [ reflexivity | do 4 eexists; split; [ reflexivity | exact (gc_loc_loc _ _ _ _ _ Hlm) ] ].
        * (* a record type: its type former, with its module stored at its
             path *)
          cbn [ge_read] in Hed; inversion Hed as [| | | | ? ? ? ? ? ? Tm Φm Hlm]; subst.
          right; do 4 eexists; split; [ reflexivity | do 4 eexists; split; [ reflexivity | exact (gc_loc_loc _ _ _ _ _ Hlm) ] ].
      + (* an open frame of a record type's module is no entry *)
        exfalso; exact (record_frame_no_entry _ _ _ _ _ _ Hs He Hq Hk).
    - (* an alias: where its target is *)
      inversion Hm as [? ? ? ? ? ? Hu | ? ? ? ? ? ? ? ? ? Hq Hk | | | | ? ? ? R0 R0m Γy E0 rd R1 ? Hm0 Hd0 He0 Hed Hr
                      | ? ? ? ? ? ? Hq Hk]; subst.
      + destruct (gc_unit_loc _ _ _ _ _ Hu) as (mp & Hq & Hl).
        rewrite (msite_unit _ _ Hg _ _ (ms_alias _ _ _ _ _ _ _ _ Hs He Ha Hs') _ Hq (or_introl (ex_intro _ _ Hu))).
        match goal with Hq1 : mod_qname _ = Some ?p0 |- _ =>
          assert_fails (constr_eq p0 mp); assert (mp = p0) by congruence; subst mp end.
        left; do 4 eexists; split; [ reflexivity | exact Hl ].
      + exfalso; exact (ind_frame_no_entry _ _ _ _ _ _ Hs He Hq Hk).
      + destruct (site_desc_mod _ _ _ (IH _ _ Hm0) Hd0) as (Θ' & T & Φ & Ns & -> & Hl).
        cbn in He0; destruct (gm_prefix_upto Φ z) as [[| Φ0 x E1 | ? ? ?] |] eqn:Hp; try discriminate.
        injection He0 as <- <- <-.
        destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & Hent).
        pose proof (proj2 (loc_entry _ _ Hg _ _ _ Hl _ _) Hent) as He1; rewrite He in He1; injection He1 as <-.
        eapply site_desc_read; [| exact Hr ].
        destruct E as [| pv [Δ [sm Φy | E'']] | pv pq1 k D Φi | pv Ad Md [Δ [sm Φy | E'']] | pv Rr ΦR ]; cbn in Ha; try discriminate; injection Ha as <-.
        * cbn [ge_read] in Hed; inversion Hed; subst.
          match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
          apply site_desc_up.
          match goal with Hm1 : mdenote _ _ _ E'' ?R2, Hd : ds_mod ?R2 = Some _ |- _ =>
            destruct (site_desc_mod _ _ _ (IH' _ _ Hm1) Hd) as (Θ2 & T2 & Φ2 & Ns2 & -> & Hl2) end.
          left; do 4 eexists; split; [ reflexivity | exact Hl2 ].
        * (* a definition with a module part: its module part where its
             target is *)
          cbn [ge_read] in Hed; inversion Hed; subst.
          match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
          match goal with Hm1 : mdenote _ _ _ E'' ?R2, Hd : ds_mod ?R2 = Some _ |- _ =>
            destruct (site_desc_mod _ _ _ (IH' _ _ Hm1) Hd) as (Θ2 & T2 & Φ2 & Ns2 & -> & Hl2) end.
          right; do 4 eexists; split; [ reflexivity |].
          cbn [ds_up]; do 4 eexists; split; [ reflexivity | exact Hl2 ].
      + exfalso; exact (record_frame_no_entry _ _ _ _ _ _ Hs He Hq Hk).
    - (* an application *)
      inversion Hm as [? ? ? ? ? ? Hu | ? ? ? ? ? ? ? ? ? Hq _ | | | ? ? ? R0 ? Hm0 Ha0 | | ? ? ? ? ? ? Hq _]; subst;
        [ cbn in Hu; discriminate | cbn in Hq; discriminate | | cbn in Hq; discriminate ].
      exact (site_desc_at _ _ _ _ (IH _ _ Hm0) Ha0).
    - (* the open frame of a record type's module: its type former, with
         its module stored there *)
      destruct (frame_record_loc _ _ Hg _ _ Hk) as (U & T0 & T & Φ & Ht & _ & Hl).
      rewrite (proj2 (proj2 (frame_denote_unique _ _ Hg _ _ _ _ Hq Hm)) _ _ _ Hk Hl).
      right; do 4 eexists; split; [ reflexivity | do 4 eexists; split; [ reflexivity | exact (gc_loc_loc _ _ _ _ _ Hl) ] ].
  Qed.
End SiteDesc.

(** ** What Is Stored Below Stays Below

    Along an embedding, a module expression that denotes in the smaller
    context is stored where it was: lookups that succeed only in the
    bigger context are of entries the smaller one does not have, which the
    expression, denoting, never reads. *)

Lemma mod_qname_mem : forall H p y, mod_qname H = Some p -> mod_qname (me_mem H y) = Some (qname_in p y).
Proof. intros * Hq; cbn; rewrite Hq; reflexivity. Qed.

Lemma entry_grows_body : forall E1 E2, entry_grows E1 E2 -> entry_is_body E2 -> entry_is_body E1.
Proof.
  intros [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? ? | ? ? ?] [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? ? | ? ? ?] Hgr Hb; cbn in *;
    try contradiction; try discriminate; auto.
Qed.

Lemma entry_grows_alias : forall E1 E2 E', entry_grows E1 E2 -> entry_alias E2 = Some E' -> E1 = E2.
Proof.
  intros [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? ? | ? ? ?] [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? ? | ? ? ?] E' Hgr Ha; cbn in *;
    try discriminate; auto.
Qed.

Lemma gm_entry_alias_sub : forall Φ T x ip E E', gm_entry Φ (x :: ip) = Some E -> entry_alias E = Some E' ->
    exists Δ, gm_submodule T Φ x ip = Some (mr_alias (gu_mk Δ (md_alias E'))).
Proof.
  fix IH 1; intros [| Φ0 y E0 | Φ0 c its] T x ip E E' He Ha; cbn in He |- *; [ discriminate | | exact (IH _ _ _ _ _ _ He Ha) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ He Ha) ].
  destruct ip as [| z ip'].
  - injection He as <-; destruct E0 as [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? [? [? ?| ?]] | ? ? ?]; cbn in Ha; try discriminate;
      injection Ha as <-; eexists; reflexivity.
  - destruct E0 as [| ? [Δ [? Φ'| ?]] | ? ? ? D Φ' | ? ? ? ? | ? ? ?]; try discriminate; eapply IH; eassumption.
Qed.

Lemma gc_entry_alias_module : forall Θ Ξ p E E', gc_entry Θ Ξ p = Some E -> entry_alias E = Some E' ->
    exists Δ, gc_module Θ Ξ p = Some (mr_alias (gu_mk Δ (md_alias E'))).
Proof.
  intros * He Ha; unfold gc_entry, gc_entry_u in He; unfold gc_module, gc_module_u.
  rewrite gs_find_tele_find in He.
  destruct (gs_find_tele Ξ p) as [[[U ip] T0] |]; cbn in He.
  - destruct ip as [| x ip]; [ rewrite gm_entry_nil in He; discriminate | exact (gm_entry_alias_sub _ _ _ _ _ _ He Ha) ].
  - destruct (gds_lookup Θ (q_unit p)) as [U |]; [| discriminate ].
    destruct (q_chain p) as [| x ip]; cbn; [ rewrite gm_entry_nil in He; discriminate | exact (gm_entry_alias_sub _ _ _ _ _ _ He Ha) ].
Qed.

Section Below.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hg1 : ⊢ᵍ Θ1 ⍮ Ξ1.
  Hypothesis He : gctx_embedding_with_bodies Θ1 Ξ1 Θ2 Ξ2.

  Let Hg2 : ⊢ᵍ Θ2 ⍮ Ξ2 := gctx_embedding_with_bodies_wf _ _ _ _ He.
  Let Hs : gc_sub Θ1 Ξ1 Θ2 Ξ2 := gc_subx_sub _ _ _ _ (gctx_embedding_with_bodies_resolution _ _ _ _ He).

  (** A member is an open frame of the smaller context, or neither a unit
      nor the open frame of a member's module or of a record type's module
      there. *)
  Lemma mem_frame_cases : forall H z,
      (exists p1 TΦ, mod_qname (me_mem H z) = Some p1 /\ gc_frame Ξ1 p1 = Some TΦ) \/
      (gc_unit Θ1 Ξ1 (me_mem H z) = None /\ frame_ind_of Ξ1 (me_mem H z) = None /\
       frame_record_of Ξ1 (me_mem H z) = None).
  Proof.
    intros H z; destruct (mod_qname (me_mem H z)) as [p1 |] eqn:Hq1.
    - destruct (gc_frame Ξ1 p1) as [TΦ |] eqn:Hf1; [ left; eauto | right; split; [| split ] ].
      + destruct (gc_unit Θ1 Ξ1 (me_mem H z)) as [[T Φ] |] eqn:Hu; [ exfalso | reflexivity ].
        destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq & [Hf | (_ & Hc & _)]); rewrite Hq1 in Hq; injection Hq as <-;
          [ congruence |].
        cbn in Hq1; destruct (mod_qname H) as [p0 |]; [| discriminate ]; injection Hq1 as <-.
        cbn in Hc; destruct (q_chain p0); discriminate.
      + unfold frame_ind_of; rewrite Hq1; destruct (gs_find_ind Ξ1 p1) as [r |] eqn:Hk; [ exfalso | reflexivity ].
        destruct (gs_find_ind_tele _ _ _ Hk) as (U & T & Ht).
        destruct (gs_find_tele_body _ _ Hg1 _ _ _ _ Ht) as (Δ & Φ & ->).
        unfold gc_frame in Hf1; rewrite Ht in Hf1; discriminate.
      + unfold frame_record_of; rewrite Hq1; destruct (gs_find_record Ξ1 p1) as [Rr |] eqn:Hk; [ exfalso | reflexivity ].
        destruct (gs_find_record_tele _ _ _ Hk) as (U & T & Ht).
        destruct (gs_find_tele_body _ _ Hg1 _ _ _ _ Ht) as (Δ & Φ & ->).
        unfold gc_frame in Hf1; rewrite Ht in Hf1; discriminate.
    - right; split; [| split ]; [ unfold gc_unit | unfold frame_ind_of | unfold frame_record_of ]; rewrite Hq1; reflexivity.
  Qed.

  (** An open frame of the smaller context a member names is that member
      of where its parent is stored. *)
  Lemma frame_mem_site : forall H z p1 TΦ pq Γ0,
      mod_qname (me_mem H z) = Some p1 -> gc_frame Ξ1 p1 = Some TΦ ->
      (forall R, mdenote Θ1 Ξ1 Γ0 H R -> msite Θ1 Ξ1 H pq) -> p1 = qname_in pq z.
  Proof.
    intros * Hq Hf IH.
    cbn in Hq; destruct (mod_qname H) as [p0 |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
    change {| q_unit := q_unit p0; q_chain := q_chain p0 ++ z :: nil |} with (qname_in p0 z) in *.
    assert (Ht : exists U T0, gs_find_tele Ξ1 (qname_in p0 z) = Some (U, nil, T0)).
    { destruct TΦ as [T Φ]; unfold gc_frame in Hf; destruct (gs_find_tele Ξ1 (qname_in p0 z)) as [[[U [| ? ?]] T0] |];
        try (destruct U as [? [[|] ? | ?]]); try discriminate; eauto. }
    destruct Ht as (U & T0 & Ht).
    destruct (frame_parent _ _ Hg1 _ _ _ _ Ht) as (Tq & Φq & Hfq & _).
    destruct (mdenote_of_loc_any _ _ Hg1 _ _ _ _ Γ0 Hq0 (or_introl Hfq)) as (R & Hm & _ & _).
    pose proof (msite_functional _ _ Hg1 _ _ (IH _ Hm) _ (site_of_frame _ _ _ _ _ Hq0 Hfq)) as ->; reflexivity.
  Qed.

  (** An open frame of the bigger context, at a path denoting in the
      smaller one, is an open frame there, of the same kind. *)
  Lemma frame_below : forall H p T2 Φ2, mod_qname H = Some p -> gc_frame Ξ2 p = Some (T2, Φ2) ->
      forall Γ R, mdenote Θ1 Ξ1 Γ H R ->
      exists T1 Φ1, gc_frame Ξ1 p = Some (T1, Φ1) /\ gs_find_ind Ξ1 p = gs_find_ind Ξ2 p /\
                    gs_find_record Ξ1 p = gs_find_record Ξ2 p.
  Proof.
    (* a frame of the smaller context that is one of the bigger keeps its kind *)
    assert (Hkeep : forall p T1 Φ1 T2 Φ2, gc_frame Ξ1 p = Some (T1, Φ1) -> gc_frame Ξ2 p = Some (T2, Φ2) ->
              gs_find_ind Ξ1 p = gs_find_ind Ξ2 p /\ gs_find_record Ξ1 p = gs_find_record Ξ2 p).
    { intros * Hf1 Hf2; destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hs Hf1) as (Φ' & [[_ [Hk Hkr]] | [Hb _]]);
        [ split; symmetry; assumption |].
      rewrite (gc_body_not_frame _ _ _ _ Hb) in Hf2; discriminate. }
    induction H as [fp | x | H0 IH y | H0 IH N | U]; intros p T2 Φ2 Hq Hf2 Γ R Hm; cbn in Hq; try discriminate.
    - injection Hq as <-.
      destruct (mdenote_unit_inv _ _ Hg1 _ _ _ Hm) as (T & Φ & Hu & _).
      destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq & [Hf | (_ & _ & Hb & _)]); cbn in Hq; injection Hq as <-.
      + exists T, Φ; split; [ exact Hf | exact (Hkeep _ _ _ _ _ Hf Hf2) ].
      + exfalso; destruct (gc_sub_body _ _ _ _ _ _ _ Hs Hb) as (Φ' & Hb2 & _).
        rewrite (gc_body_not_frame _ _ _ _ Hb2) in Hf2; discriminate.
    - case_eq (mod_qname H0); [ intros p0 Hq0 | intros Hn; rewrite Hn in Hq; discriminate ].
      rewrite Hq0 in Hq; injection Hq as <-.
      change {| q_unit := q_unit p0; q_chain := q_chain p0 ++ y :: nil |} with (qname_in p0 y) in *.
      assert (Hq : mod_qname (me_mem H0 y) = Some (qname_in p0 y)) by (cbn; rewrite Hq0; reflexivity).
      inversion Hm as [? ? ? T Φ Hq' Hu | ? ? ? pq k D Mk Tm Φm Hq' Hk | | | | ? ? ? R0 R0m Γy E rd R1 ? Hm0 Hd0 He0 Hed Hr
                      | ? ? ? Rr Tm Φm Hq' Hk]; subst.
      + (* a unit there: an open frame *)
        destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq1 & [Hf | (_ & Hc & _)]); rewrite Hq in Hq1; injection Hq1 as <-.
        * exists T, Φ; split; [ exact Hf | exact (Hkeep _ _ _ _ _ Hf Hf2) ].
        * exfalso; cbn in Hc; destruct (q_chain p0); discriminate.
      + (* the open frame of a member's module there *)
        rewrite Hq in Hq'; injection Hq' as <-.
        destruct (frame_ind_loc _ _ Hg1 _ _ _ _ Hk) as (? & ? & T & Φ & ? & _ & Hf & _ & _).
        exists T, Φ; split; [ exact Hf | exact (Hkeep _ _ _ _ _ Hf Hf2) ].
      + (* a member there: its entry is no frame here *)
        exfalso.
        assert (Ht2 : exists U T0, gs_find_tele Ξ2 (qname_in p0 y) = Some (U, nil, T0)).
        { unfold gc_frame in Hf2; destruct (gs_find_tele Ξ2 (qname_in p0 y)) as [[[U [| ? ?]] T0] |];
            try (destruct U as [? [[|] ? | ?]]); try discriminate; eauto. }
        destruct Ht2 as (U & T0 & Ht2).
        destruct (frame_parent _ _ Hg2 _ _ _ _ Ht2) as (Tq2 & Φq2 & Hfq2 & _).
        destruct (IH _ _ _ Hq0 Hfq2 _ _ Hm0) as (Tq & Φq & Hfq & _).
        (* what the parent denotes is its frame *)
        assert (Hmd : R0m = ds_closed nil p0 Tq Φq nil).
        { destruct (frame_denote_unique _ _ Hg1 _ _ _ _ Hq0 Hm0) as [Hu0 [Hk0 Hr0]].
          destruct (gs_find_ind Ξ1 p0) as [[[pq k] D] |] eqn:Hk.
          - destruct (frame_ind_loc _ _ Hg1 _ _ _ _ Hk) as (U' & T0' & T' & Φ' & Mk' & Ht' & Hf' & Hl' & HMk').
            rewrite (Hk0 _ _ _ _ _ _ eq_refl HMk' Hl') in Hd0; cbn in Hd0.
            rewrite Hfq in Hf'; injection Hf' as <- <-; injection Hd0 as <-; reflexivity.
          - destruct (gs_find_record Ξ1 p0) as [Rr |] eqn:Hkr.
            + destruct (frame_record_loc _ _ Hg1 _ _ Hkr) as (U' & T0' & T' & Φ' & Ht' & Hf' & Hl').
              rewrite (Hr0 _ _ _ eq_refl Hl') in Hd0; cbn in Hd0.
              rewrite Hfq in Hf'; injection Hf' as <- <-; injection Hd0 as <-; reflexivity.
            + rewrite (Hu0 _ _ (gc_unit_frame _ _ _ _ _ _ Hq0 Hfq Hk Hkr)) in Hd0; cbn in Hd0; injection Hd0 as <-; reflexivity. }
        subst R0m; cbn in He0; destruct (gm_prefix_upto Φq y) as [[| Φ0 x E1 | ? ? ?] |] eqn:Hp; try discriminate.
        destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & Hent).
        pose proof (proj2 (loc_entry _ _ Hg1 _ _ _ (or_introl Hfq) _ _) Hent) as HE1.
        destruct (gc_sub_entry _ _ _ _ _ _ Hs HE1) as (E2 & HE2 & _).
        rewrite (gc_frame_entry_none _ _ _ _ Hf2) in HE2; discriminate.
      + (* the open frame of a record type's module there *)
        rewrite Hq in Hq'; injection Hq' as <-.
        destruct (frame_record_loc _ _ Hg1 _ _ Hk) as (? & ? & T & Φ & _ & Hf & _).
        exists T, Φ; split; [ exact Hf | exact (Hkeep _ _ _ _ _ Hf Hf2) ].
  Qed.

  (** An open frame of the smaller context is, in the bigger one, no alias. *)
  Lemma frame_not_alias : forall p TΦ E E', gc_frame Ξ1 p = Some TΦ -> gc_entry Θ2 Ξ2 p = Some E ->
      entry_alias E = Some E' -> False.
  Proof.
    intros * Hf HE Ha; destruct TΦ as [T Φ].
    destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hs Hf) as (Φ' & [[Hf' _] | [_ [Hm' _]]]).
    - rewrite (gc_frame_entry_none _ _ _ _ Hf') in HE; discriminate.
    - destruct (gc_entry_alias_module _ _ _ _ _ HE Ha) as (Δ & Hm); congruence.
  Qed.

  (** The entry an expression denoting in the smaller context selects from
      where it is stored is stored there too, unless it names an open frame. *)
  Lemma entry_below : forall Γ H z R pq,
      mdenote Θ1 Ξ1 Γ (me_mem H z) R -> msite Θ1 Ξ1 H pq ->
      gc_unit Θ1 Ξ1 (me_mem H z) = None -> frame_ind_of Ξ1 (me_mem H z) = None ->
      frame_record_of Ξ1 (me_mem H z) = None ->
      exists E1, gc_entry Θ1 Ξ1 (qname_in pq z) = Some E1.
  Proof.
    intros * Hm Hsi Hu Hk Hkr;
      inversion Hm as [? ? ? ? ? ? Hu' | ? ? ? ? ? ? ? ? ? Hq' Hk' | | | | ? ? ? R0 R0m Γy E0 rd R1 ? Hm0 Hd0 He0 Hed Hr
                      | ? ? ? ? ? ? Hq' Hk']; subst;
      [ congruence | exfalso; eapply frame_ind_of_none; eassumption | | exfalso; eapply frame_record_of_none; eassumption ].
    destruct (site_desc_mod _ _ _ _ _ (msite_desc _ _ Hg1 _ _ Hsi _ _ Hm0) Hd0) as (Θ' & T & Φ & Ns & -> & Hl).
    cbn in He0; destruct (gm_prefix_upto Φ z) as [[| Φ0 x E1 | ? ? ?] |] eqn:Hp; try discriminate.
    destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & Hent).
    exists E1; exact (proj2 (loc_entry _ _ Hg1 _ _ _ Hl _ _) Hent).
  Qed.

  (** A loaded unit or an open frame of the bigger context, at an expression
      denoting in the smaller one, is one there too. *)
  (** A loaded unit or an open frame of the bigger context, at an expression
      denoting in the smaller one, is one there too. *)
  Lemma unit_below : forall H T2 Φ2, gc_unit Θ2 Ξ2 H = Some (T2, Φ2) ->
      forall Γ R, mdenote Θ1 Ξ1 Γ H R -> exists T1 Φ1, gc_unit Θ1 Ξ1 H = Some (T1, Φ1).
  Proof.
    intros * Hu Γ R Hm.
    destruct (gc_unit_cases _ _ _ _ _ Hu) as (p & Hq & [Hf2 | (_ & Hc & _)]).
    - destruct (frame_below _ _ _ _ Hq Hf2 _ _ Hm) as (T1 & Φ1 & Hf1 & Hk & Hkr).
      exists T1, Φ1; apply (gc_unit_frame _ _ _ _ _ _ Hq Hf1).
      + rewrite Hk; exact (gc_unit_not_ind _ _ _ _ _ _ Hq Hu).
      + rewrite Hkr; exact (gc_unit_not_record _ _ _ _ _ _ Hq Hu).
    - (* a filed unit: a unit's path *)
      pose proof (mod_qname_inv _ _ Hq) as ->.
      destruct p as [fp ch]; cbn in Hc; subst ch; cbn [qname_mod me_mems] in Hm |- *.
      destruct (mdenote_unit_inv _ _ Hg1 _ _ _ Hm) as (T1 & Φ1 & Hu1 & _); eauto.
  Qed.

  (** A loaded unit or an open frame of the smaller context is, in the
      bigger one, no alias. *)
  Lemma unit_not_alias : forall H T1 Φ1 p E E', gc_unit Θ1 Ξ1 (me_mem H p) = Some (T1, Φ1) ->
      forall pq0, mod_qname (me_mem H p) = Some pq0 ->
      gc_entry Θ2 Ξ2 pq0 = Some E -> entry_alias E = Some E' -> False.
  Proof.
    intros * Hu pq0 Hq HE Ha.
    destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq' & [Hf | (_ & Hc & _)]); rewrite Hq in Hq'; injection Hq' as <-.
    - exact (frame_not_alias _ _ _ _ Hf HE Ha).
    - cbn in Hq; destruct (mod_qname H) as [q0 |]; [| discriminate ]; injection Hq as <-.
      cbn in Hc; destruct (q_chain q0); discriminate.
  Qed.

  Theorem msite_below : forall H pq, msite Θ2 Ξ2 H pq ->
      forall Γ R, mdenote Θ1 Ξ1 Γ H R -> msite Θ1 Ξ1 H pq.
  Proof.
    induction 1 as [H p T Φ Hq Hu | H p r Hq Hk | H pq z E Hsi IH HE Hb | H pq z E E' pq' Hsi IH HE Ha Hsi' IH' | H N pq Hsi IH
                   | H p Rr Hq Hk];
      intros Γ R Hm.
    - destruct (unit_below _ _ _ Hu _ _ Hm) as (T1 & Φ1 & Hu1); eapply ms_unit; eassumption.
    - (* the open frame of a member's module there: an open frame here *)
      destruct r as [[pg k] D].
      destruct (frame_ind_loc _ _ Hg2 _ _ _ _ Hk) as (? & ? & T2 & Φ2 & ? & _ & Hf2 & _ & _).
      destruct (frame_below _ _ _ _ Hq Hf2 _ _ Hm) as (T1 & Φ1 & Hf1 & _).
      exact (site_of_frame _ _ _ _ _ Hq Hf1).
    - destruct (mem_frame_cases H z) as [(p1 & TΦ & Hq1 & Hf1) | (Hu1 & Hk1 & Hkr1)].
      + (* an open frame there: stored at its own path *)
        pose proof (frame_mem_site _ _ _ _ _ Γ Hq1 Hf1 (IH Γ)) as ->.
        exact (site_of_frame _ _ _ _ _ Hq1 Hf1).
      + inversion Hm as [? ? ? ? ? ? Hu' | ? ? ? ? ? ? ? ? ? Hq' Hk' | | | | ? ? ? R0 R0m Γy E0 rd R1 ? Hm0 Hd0 He0 Hed Hr
                        | ? ? ? ? ? ? Hq' Hk']; subst;
          [ congruence | exfalso; eapply frame_ind_of_none; eassumption | | exfalso; eapply frame_record_of_none; eassumption ].
        pose proof (IH _ _ Hm0) as Hs1.
        destruct (entry_below _ _ _ _ _ Hm Hs1 Hu1 Hk1 Hkr1) as (E1 & HE1).
        destruct (gc_sub_entry _ _ _ _ _ _ Hs HE1) as (E2 & HE2 & Hgr); rewrite HE in HE2; injection HE2 as <-.
        eapply ms_body; [ exact Hs1 | exact HE1 | exact (entry_grows_body _ _ Hgr Hb) ].
    - destruct (mem_frame_cases H z) as [(p1 & TΦ & Hq1 & Hf1) | (Hu1 & Hk1 & Hkr1)].
      + (* an open frame there is no alias here *)
        exfalso.
        pose proof (frame_mem_site _ _ _ _ _ Γ Hq1 Hf1 (IH Γ)) as ->.
        exact (frame_not_alias _ _ _ _ Hf1 HE Ha).
      + inversion Hm as [? ? ? ? ? ? Hu' | ? ? ? ? ? ? ? ? ? Hq' Hk' | | | | ? ? ? R0 R0m Γy E0 rd R1 ? Hm0 Hd0 He0 Hed Hr
                        | ? ? ? ? ? ? Hq' Hk']; subst;
          [ congruence | exfalso; eapply frame_ind_of_none; eassumption | | exfalso; eapply frame_record_of_none; eassumption ].
        pose proof (IH _ _ Hm0) as Hs1.
        destruct (entry_below _ _ _ _ _ Hm Hs1 Hu1 Hk1 Hkr1) as (E1 & HE1).
        destruct (gc_sub_entry _ _ _ _ _ _ Hs HE1) as (E2 & HE2 & Hgr); rewrite HE in HE2; injection HE2 as <-.
        pose proof (entry_grows_alias _ _ _ Hgr Ha) as <-.
        eapply ms_alias; [ exact Hs1 | exact HE1 | exact Ha |].
        (* the target denotes there: it is what the entry denotes *)
        destruct (site_desc_mod _ _ _ _ _ (msite_desc _ _ Hg1 _ _ Hs1 _ _ Hm0) Hd0) as (Θ' & T & Φ & Ns & -> & Hl).
        cbn in He0; destruct (gm_prefix_upto Φ z) as [[| Φ0 x E0' | ? ? ?] |] eqn:Hp; try discriminate.
        injection He0 as <- <- <-.
        destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= <- -> <-] & Hent).
        pose proof (proj2 (loc_entry _ _ Hg1 _ _ _ Hl _ _) Hent) as He1; rewrite HE1 in He1; injection He1 as <-.
        destruct E1 as [| pv [Δ [sm Φy | E'']] | pv pq1 k D Φi | pv Ad Md [Δ [sm Φy | E'']] | pv Rr ΦR ]; cbn in Ha; try discriminate; injection Ha as <-.
        all: cbn [ge_read] in Hed; inversion Hed; subst.
        all: match goal with Hu : udenote _ _ _ _ _ _ |- _ => inversion Hu; subst end.
        all: match goal with Hm1 : mdenote _ _ _ _ _ |- _ => exact (IH' _ _ Hm1) end.
    - inversion Hm as [? ? ? ? ? ? Hu | ? ? ? ? ? ? ? ? ? Hq _ | | | ? ? ? R0 ? Hm0 Ha0 | | ? ? ? ? ? ? Hq _]; subst;
        [ cbn in Hu; discriminate | cbn in Hq; discriminate | | cbn in Hq; discriminate ].
      exact (ms_app _ _ _ _ _ (IH _ _ Hm0)).
    - (* the open frame of a record type's module there: an open frame here *)
      destruct (frame_record_loc _ _ Hg2 _ _ Hk) as (? & ? & T2 & Φ2 & _ & Hf2 & _).
      destruct (frame_below _ _ _ _ Hq Hf2 _ _ Hm) as (T1 & Φ1 & Hf1 & _).
      exact (site_of_frame _ _ _ _ _ Hq Hf1).
  Qed.
End Below.

(** ** The Order of Sites

    Finding where a module expression is stored follows its spine, and the
    aliases it meets: their targets are read in turn.  Every module
    expression has an order ([site_order_total]): an alias names modules
    that were there before it, which a global induction over well-formed
    global contexts makes precise. *)

Inductive site_order (Θ : gdeps) (Ξ : gstack) : modexp -> Prop :=
| site_order_unit : forall fp, site_order Θ Ξ (me_unit fp)
| site_order_var : forall x, site_order Θ Ξ (me_var x)
| site_order_lit : forall U, site_order Θ Ξ (me_lit U)
| site_order_app : forall H N, site_order Θ Ξ H -> site_order Θ Ξ (me_app H N)
| site_order_mem : forall H z,
    site_order Θ Ξ H ->
    (forall pq E E', msite Θ Ξ H pq -> gc_entry Θ Ξ (qname_in pq z) = Some E -> entry_alias E = Some E' ->
       site_order Θ Ξ E') ->
    site_order Θ Ξ (me_mem H z).

(** The aliases stored in [Θ1 ⍮ Ξ1] have an order in [Θ2 ⍮ Ξ2]. *)
Definition aliases_sited (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack) : Prop :=
  forall p E E', gc_entry Θ1 Ξ1 p = Some E -> entry_alias E = Some E' -> site_order Θ2 Ξ2 E'.

Section Sited.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hg1 : ⊢ᵍ Θ1 ⍮ Ξ1.
  Hypothesis He : gctx_embedding_with_bodies Θ1 Ξ1 Θ2 Ξ2.
  Hypothesis Ha : aliases_sited Θ1 Ξ1 Θ2 Ξ2.

  Let Hs : gc_sub Θ1 Ξ1 Θ2 Ξ2 := gc_subx_sub _ _ _ _ (gctx_embedding_with_bodies_resolution _ _ _ _ He).

  (** What denotes in the smaller context has an order in the bigger one. *)
  Lemma site_order_of_mdenote : forall H Γ R, mdenote Θ1 Ξ1 Γ H R -> site_order Θ2 Ξ2 H.
  Proof.
    induction H as [fp | x | H0 IH z | H0 IH N | U]; intros Γ R Hm; try solve [ constructor ].
    - assert (Hm0 : exists Γ0 R0, mdenote Θ1 Ξ1 Γ0 H0 R0).
      { (* the parent of an open frame is one, which denotes *)
        assert (Hpar : forall p U T0, mod_qname (me_mem H0 z) = Some p -> gs_find_tele Ξ1 p = Some (U, nil, T0) ->
                  exists Γ0 R0, mdenote Θ1 Ξ1 Γ0 H0 R0).
        { intros p U T0 Hq Ht.
          cbn in Hq; destruct (mod_qname H0) as [p0 |] eqn:Hq0; [| discriminate ]; injection Hq as <-.
          destruct (frame_parent _ _ Hg1 _ _ _ _ Ht) as (Tq & Φq & Hfq & _).
          destruct (mdenote_of_loc_any _ _ Hg1 _ _ _ _ Γ Hq0 (or_introl Hfq)) as (R0 & Hm0 & _ & _); eauto. }
        inversion Hm as [? ? ? ? ? Hq Hu | ? ? ? ? ? ? ? ? ? Hq Hk | | | | ? ? ? R0 R0m Γy E0 rd R1 ? Hm0 Hd0 He0 Hed Hr
                        | ? ? ? ? ? ? Hq Hk]; subst;
          [ | | eauto | ].
        - destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq' & [Hf | (_ & Hc & _)]); rewrite Hq in Hq'; injection Hq' as <-.
          + unfold gc_frame in Hf; destruct (gs_find_tele Ξ1 _) as [[[U [| ? ?]] T0] |] eqn:Ht;
              try (destruct U as [? [[|] ? | ?]]); try discriminate; eapply Hpar; eassumption.
          + exfalso; cbn in Hq; destruct (mod_qname H0) as [p0 |]; [| discriminate ]; injection Hq as <-.
            cbn in Hc; destruct (q_chain p0); discriminate.
        - destruct (gs_find_ind_tele _ _ _ Hk) as (? & ? & Ht); eapply Hpar; eassumption.
        - destruct (gs_find_record_tele _ _ _ Hk) as (? & ? & Ht); eapply Hpar; eassumption. }
      destruct Hm0 as (Γ0 & R0 & Hm0).
      apply site_order_mem; [ exact (IH _ _ Hm0) |].
      intros pq E E' Hs2 HE2 Hal.
      pose proof (msite_below _ _ _ _ Hg1 He _ _ Hs2 _ _ Hm0) as Hs1.
      destruct (mem_frame_cases _ _ Hg1 H0 z) as [(p1 & TΦ & Hq1 & Hf1) | (Hu1 & Hk1 & Hkr1)].
      + exfalso.
        assert (Ep : p1 = qname_in pq z)
          by (eapply frame_mem_site with (Γ0 := Γ0); [ exact Hg1 | exact Hq1 | exact Hf1 | intros R' Hm'; eapply msite_below; eassumption ]).
        subst p1; eapply frame_not_alias; eassumption.
      + destruct (entry_below _ _ Hg1 _ _ _ _ _ Hm Hs1 Hu1 Hk1 Hkr1) as (E1 & HE1).
        destruct (gc_sub_entry _ _ _ _ _ _ Hs HE1) as (E2 & HE2' & Hgr); rewrite HE2 in HE2'; injection HE2' as <-.
        pose proof (entry_grows_alias _ _ _ Hgr Hal) as <-.
        exact (Ha _ _ _ HE1 Hal).
    - inversion Hm as [? ? ? ? ? ? Hu | ? ? ? ? ? ? ? ? ? Hq _ | | | ? ? ? R0 ? Hm0 Ha0 | | ? ? ? ? ? ? Hq _]; subst;
        [ cbn in Hu; discriminate | cbn in Hq; discriminate | | cbn in Hq; discriminate ].
      exact (site_order_app _ _ _ _ (IH _ _ Hm0)).
  Qed.
End Sited.

Definition sited_V (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) (E : gentry) : Prop :=
  match E with
  | ge_mod _ (gu_mk _ (md_alias E')) => site_order Θ2 Ξ2 E'
  | _ => True
  end.

Definition sited_F (Θ2 : gdeps) (Ξ2 : gstack) (T : ctx) : Prop := True.

Definition sited_VD (Θ2 : gdeps) (Ξ2 : gstack) (D : ind_decl) : Prop := True.

Definition sited_VR (Θ2 : gdeps) (Ξ2 : gstack) (R : record_decl) : Prop := True.

(** Being sited does not depend on where it is read from. *)
Abbreviation sited_Vs := (fun (_ : gdeps) (_ : gstack) => sited_V).

Lemma good_sited : forall Θ Ξ Θs Ξs Θ2 Ξ2,
    gds_valid sited_Vs sited_F sited_VD sited_VR Θs Ξs Θ2 Ξ2 Θ -> gs_valid sited_Vs sited_F sited_VD sited_VR Θs Ξs Θ2 Ξ2 Ξ ->
    aliases_sited Θ Ξ Θ2 Ξ2.
Proof.
  intros * HΘ HΞ p E E' HE Hal.
  destruct (gc_entry_alias_module _ _ _ _ _ HE Hal) as (Δ & Hm).
  destruct (good_alias _ _ _ _ _ _ _ _ _ _ _ _ HΘ HΞ Hm) as (T & pv & HV); exact HV.
Qed.

Lemma sited_V_alias : forall Θ Ξ pv Δ E Θ2 Ξ2 (Θs : gdeps) (Ξs : gstack),
    tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    bodies_valid_along_embeddings sited_Vs sited_F sited_VD sited_VR Θ Ξ -> gctx_embedding_with_bodies Θ Ξ Θ2 Ξ2 -> gc_sub Θ Ξ Θs Ξs ->
    sited_V Θ2 Ξ2 (gs_tele Ξ) (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))).
Proof.
  intros * _ _ HE HG He _; cbn [sited_V].
  pose proof (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) as Hg.
  destruct (HG _ _ He _ _ (gc_sub_refl _ _)) as [HΘ HΞ].
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HE) as (_ & (R & _ & HR & _) & _).
  exact (site_order_of_mdenote _ _ _ _ Hg He (good_sited _ _ _ _ _ _ HΘ HΞ) _ _ _ HR).
Qed.

Theorem gctx_aliases_sited : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> aliases_sited Θ Ξ Θ Ξ.
Proof.
  intros * Hg.
  pose proof (global_valid sited_Vs sited_F sited_VD sited_VR
                ltac:(intros; exact I) ltac:(intros; exact I)
                sited_V_alias ltac:(intros; exact I) ltac:(intros; split; exact I)
                ltac:(intros; exact I) ltac:(intros; exact I) _ _ Hg) as HG.
  destruct (HG _ _ (gctx_embedding_with_bodies_refl _ _ Hg) _ _ (gc_sub_refl _ _)) as [HΘ HΞ].
  exact (good_sited _ _ _ _ _ _ HΘ HΞ).
Qed.

Theorem site_order_total : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H, site_order Θ Ξ H.
Proof.
  intros * Hg; pose proof (gctx_aliases_sited _ _ Hg) as Ha.
  induction H as [fp | x | H IH z | H IH N | U]; constructor; auto.
  intros pq E E' _ HE Hal; exact (Ha _ _ _ HE Hal).
Qed.

(** A private member out of reach: declared in the module of a unit, or
    an entry of a local body, at the chain of submodules [ch] from the local
    module. *)
Inductive priv_err : Set :=
| priv_err_global : qname -> string -> priv_err
| priv_err_local : list string -> string -> priv_err.

Definition entry_is_body_b (E : gentry) : bool :=
  match E with
  | ge_mod _ (gu_mk _ (md_body _ _)) | ge_ind _ _ _ _ _ | ge_record _ _ _ _ => true
  | _ => false
  end.

Lemma entry_is_body_b_spec : forall E, entry_is_body_b E = true <-> entry_is_body E.
Proof. intros [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? ? | ? ? ?]; cbn; split; intros; auto; try discriminate; contradiction. Qed.

(** The fast test is the test of the entry a fast one stands for. *)
Lemma fe_is_body_b_core : forall e, fe_is_body_b e = entry_is_body_b (dec_entry e).
Proof. intros [| pv [Δ [t] | [Δ [sm Φ | E]]] | | pv A M [Δ [t] | [Δ [sm Φ | E]]] |]; reflexivity. Qed.

Section PrivacyImpl.
  (** The fast context the sites are looked up in; the judgments are at
      the Core context it stands for. *)
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  Lemma gc_unit_qname : forall H T Φ, gc_unit Θ Ξ H = Some (T, Φ) -> mod_qname H = None -> False.
  Proof. intros * Hu Hq; unfold gc_unit in Hu; rewrite Hq in Hu; discriminate. Qed.

  Lemma site_of_frame_ind : forall H r p, frame_ind_of Ξ H = Some r -> mod_qname H = Some p -> msite Θ Ξ H p.
  Proof. intros * Hf Hq; unfold frame_ind_of in Hf; rewrite Hq in Hf; exact (ms_ind_frame _ _ _ _ _ Hq Hf). Qed.

  Lemma frame_ind_of_qname : forall H r, frame_ind_of Ξ H = Some r -> mod_qname H = None -> False.
  Proof. intros * Hf Hq; unfold frame_ind_of in Hf; rewrite Hq in Hf; discriminate. Qed.

  (** The open frame of a record type's module is stored at its own path. *)
  Lemma site_of_frame_record : forall H p Rr, frame_record_of Ξ H = Some (p, Rr) -> msite Θ Ξ H p.
  Proof. intros * Hf; destruct (frame_record_of_some _ _ _ _ Hf) as [Hq Hk]; exact (ms_record_frame _ _ _ _ _ Hq Hk). Qed.

  #[local]
  Ltac site_obl :=
    intros; cbv beta in *;
    (** the fast data found, read as the Core data it stands for, which is
        all the obligations are about *)
    cbn [option_map dec_loc] in *; rewrite ?fe_alias_dec, ?fe_is_body_b_core in *;
    repeat match goal with e : fentry |- _ =>
      let E := fresh "E" in set (E := dec_entry e) in *; clearbody E; clear e end;
    repeat match goal with t : ftrie |- _ =>
      let Φ := fresh "Φ" in set (Φ := dec_mod t) in *; clearbody Φ; clear t end;
    repeat match goal with
      | H : site_order _ _ (me_mem _ _) |- _ => progressive_invert H
      | H : site_order _ _ (me_app _ _) |- _ => progressive_invert H
      end;
    try solve [ eauto using ms_unit, ms_app ];
    try solve [ exfalso; eapply gc_unit_qname; eassumption ];
    try solve [ exfalso; eapply gc_unit_qname; [ eassumption | cbn; match goal with Eqm : mod_qname _ = None |- _ => rewrite Eqm end; reflexivity ] ];
    try solve [ eapply ms_unit; [ apply mod_qname_mem; eassumption | eassumption ] ];
    try solve [ eapply site_of_frame_ind; [ eassumption | first [ reflexivity | apply mod_qname_mem; eassumption ] ] ];
    try solve [ exfalso; eapply frame_ind_of_qname; [ eassumption | cbn; match goal with Eqm : mod_qname _ = None |- _ => rewrite Eqm end; reflexivity ] ];
    try solve [ eapply ms_body; [ eassumption | eassumption | apply entry_is_body_b_spec; assumption ] ];
    try solve [ eapply ms_alias; eassumption ];
    exfalso;
    match goal with
    | Hd : msite _ _ _ _ |- _ =>
        inversion Hd; subst;
        repeat match goal with
          | H1 : msite _ _ ?H ?a, H2 : msite _ _ ?H ?b |- _ =>
              assert_fails (constr_eq a b); pose proof (msite_functional _ _ Hg _ _ H1 _ H2); subst; clear H2
          | H1 : ?f = Some ?a, H2 : ?f = Some ?b |- _ =>
              assert_fails (constr_eq a b); rewrite H1 in H2; injection H2; clear H2; intros; subst
          | H1 : ?f = Some _, H2 : ?f = None |- _ => rewrite H1 in H2; discriminate H2
          end;
        first [ congruence
              | solve [ eapply frame_ind_of_none; eassumption ]
              | solve [ eapply frame_record_of_none; eassumption ]
              | match goal with HN : forall _, ~ msite _ _ _ _ |- _ => solve [ eapply HN; eassumption ] end
              | match goal with Hb : entry_is_body ?E, Hf : entry_is_body_b ?E = false |- _ =>
                  apply entry_is_body_b_spec in Hb; congruence end
              | match goal with Hb : entry_is_body ?E, Ha : entry_alias ?E = Some _ |- _ =>
                  destruct E as [| ? [? [? ?| ?]] | ? ? ? ? ? | ? ? ? ? | ? ? ?]; cbn in Hb, Ha; try contradiction; discriminate end
              | match goal with Hb : entry_is_body ?E, Ha : entry_alias ?E = None |- _ => fail end
              | cbn in *; congruence ]
    end.

  (** Where a module expression is stored, by its order. *)
  #[tactic="idtac",derive(equations=no,eliminator=no)]
  Equations site_impl H (Ho : site_order Θ Ξ H) : { pq | msite Θ Ξ H pq } + { forall pq, ~ msite Θ Ξ H pq }
      by struct Ho :=
  | me_unit fp, Ho with gc_unit_f F (me_unit fp) := {
    | exist _ (Some (T, t)) Eu => inleft (exist _ (q_abs fp nil) _)
    | exist _ None Eu with fast_frame_ind_of F (me_unit fp) := {
      | exist _ (Some r) Ek => inleft (exist _ (q_abs fp nil) _)
      | exist _ None Ek with fast_frame_record_of F (me_unit fp) := {
        | exist _ (Some (p, Rr)) Er => inleft (exist _ p (site_of_frame_record _ _ _ Er))
        | exist _ None Er => inright _ } } }
  | me_var x, Ho => inright _
  | me_lit U, Ho => inright _
  | me_app H N, Ho with site_impl H _ := {
    | inleft (exist _ pq Hs) => inleft (exist _ pq _)
    | inright HN => inright _ }
  | me_mem H z, Ho with gc_unit_f F (me_mem H z) := {
    | exist _ (Some (T, t)) Eu with inspect (mod_qname H) := {
      | exist _ (Some p0) Eqm => inleft (exist _ (qname_in p0 z) _)
      | exist _ None Eqm => False_rect _ _ }
    | exist _ None Eu with fast_frame_ind_of F (me_mem H z) := {
      (** The open frame of a member's module: stored at its own path *)
      | exist _ (Some r) Ek with inspect (mod_qname H) := {
        | exist _ (Some p0) Eqm => inleft (exist _ (qname_in p0 z) _)
        | exist _ None Eqm => False_rect _ _ }
      | exist _ None Ek with fast_frame_record_of F (me_mem H z) := {
        (** The open frame of a record type's module: stored at its own path *)
        | exist _ (Some (p, Rr)) Er => inleft (exist _ p (site_of_frame_record _ _ _ Er))
        | exist _ None Er with site_impl H _ := {
          | inright HN => inright _
          | inleft (exist _ pq Hs) with gc_entry_f F (qname_in pq z) := {
            | exist _ None Ee => inright _
            | exist _ (Some e) Ee with inspect (fe_alias e) := {
              | exist _ (Some E') Ea with site_impl E' _ := {
                | inleft (exist _ pq' Hs') => inleft (exist _ pq' _)
                | inright HN => inright _ }
              | exist _ None Ea with inspect (fe_is_body_b e) := {
                | exist _ true Eb => inleft (exist _ (qname_in pq z) _)
                | exist _ false Eb => inright _ } } } } } } }.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.
  Next Obligation. site_obl. Defined.

  (** Where a member is declared: an entry of the module its module is
      stored at. *)
  Definition decl_impl (H : modexp) (y : string) :
      { d : qname * bool | mdecl Θ Ξ H y (fst d) (snd d) } + { forall qd pv, ~ mdecl Θ Ξ H y qd pv }.
  Proof.
    destruct (site_impl H (site_order_total _ _ Hg H)) as [[pq Hs] | HN].
    - destruct (gc_entry_f F (qname_in pq y)) as [[e |] Ee]; cbn [option_map] in Ee.
      + left; exists (pq, fe_private e); cbn [fst snd]; rewrite fe_private_dec; exact (mdecl_intro _ _ _ _ _ _ Hs Ee).
      + right; intros qd pv Hd; inversion Hd as [pq' E' Hs' He']; subst.
        rewrite (msite_functional _ _ Hg _ _ Hs _ Hs') in Ee; congruence.
    - right; intros qd pv Hd; inversion Hd; subst; eapply HN; eassumption.
  Defined.

  (** Whether a module is an open frame or an ancestor of one. *)
  Definition open_anc_b (qd : qname) : bool :=
    existsb (fun f => andb (path_beq (q_unit (ff_path f)) (q_unit qd))
                        (match strip_prefix (q_chain qd) (q_chain (ff_path f)) with Some _ => true | None => false end))
      (fc_frames F).

  Lemma open_anc_b_spec : forall qd, open_anc_b qd = true <-> open_anc Ξ qd.
  Proof.
    intros qd.
    assert (E : open_anc_b qd =
                existsb (fun e => let '(mp, _, _) := e in
                                  andb (path_beq (q_unit mp) (q_unit qd))
                                    (match strip_prefix (q_chain qd) (q_chain mp) with Some _ => true | None => false end)) Ξ)
      by (rewrite fc_stack_frames; unfold open_anc_b, dec_stack;
          induction (fc_frames F) as [| f fs IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]).
    rewrite E, existsb_exists; clear E; split.
    - intros ([[mp K] U] & Hin & Hb); apply andb_prop in Hb as [H1 H2]; cbn in *.
      apply path_beq_true in H1.
      destruct (strip_prefix (q_chain qd) (q_chain mp)) as [suf |] eqn:E; [| discriminate ].
      exact (mk_open_anc _ _ mp K U suf Hin H1 (strip_prefix_spec _ _ _ E)).
    - intros [mp K U suf Hin H1 H2]; exists (mp, K, U); split; [ exact Hin |]; cbn.
      rewrite H1, path_beq_refl, H2, strip_prefix_app; reflexivity.
  Qed.

  (** A reference to a member is checked where the member is declared; a
      failure names that module and the member. *)
  Definition glob_check (H : modexp) (x : string) :
      { qx : qname * string | ~ glob_ok Θ Ξ H x } + { glob_ok Θ Ξ H x }.
  Proof.
    unfold glob_ok.
    destruct (decl_impl H x) as [[[qd [|]] Hd] | HN]; cbn [fst snd] in *.
    - destruct (open_anc_b qd) eqn:Eo.
      + right; intros qd' Hd'; destruct (mdecl_functional _ _ Hg _ _ _ _ Hd _ _ Hd') as [<- _].
        apply open_anc_b_spec; exact Eo.
      + left; exists (qd, x); intros Hok; specialize (Hok _ Hd).
        apply open_anc_b_spec in Hok; congruence.
    - right; intros qd' Hd'; destruct (mdecl_functional _ _ Hg _ _ _ _ Hd _ _ Hd') as [_ [=]].
    - right; intros qd' Hd'; exfalso; exact (HN _ _ Hd').
  Defined.

  Definition ref_check (r : (ptab * string)%type) :
      { e : priv_err | ~ ref_ok Θ Ξ r } + { ref_ok Θ Ξ r }.
  Proof.
    destruct r as [[| H | ch es] x]; unfold ref_ok; cbn [fst snd].
    - right; exact I.
    - destruct (glob_check H x) as [[qx Hq] | Hok]; [ left; exists (priv_err_global (fst qx) (snd qx)); exact Hq | right; exact Hok ].
    - destruct (option_map fst (tab_find x es)) as [[|] |] eqn:E.
      + left; exists (priv_err_local ch x); intros Hn; apply Hn; reflexivity.
      + right; discriminate.
      + right; discriminate.
  Defined.

  Definition refs_check : forall (l : list (ptab * string)%type),
      { e : priv_err | ~ acc_ok Θ Ξ l } + { acc_ok Θ Ξ l }.
  Proof.
    induction l as [| r l IH]; [ right; constructor |].
    destruct (ref_check r) as [[e Hr] | Hr]; [ left; exists e; intros Hall; inversion Hall; contradiction |].
    destruct IH as [[e Hl] | Hl]; [ left; exists e; intros Hall; inversion Hall; contradiction | right; constructor; assumption ].
  Defined.
End PrivacyImpl.

(** ** Where a Member is Declared

    [def_site F Hg H ch] is the qualified name of the member at the chain
    [ch] of [H] where it is declared: the module [mdecl] finds for the last
    name of [ch], from [H] selected along the others, following aliases,
    then the member's own name, all in the Core context the fast context
    [F] stands for.  The documentation generator links a use of a member
    to it.  The proof [Hg] that the context is well formed only bounds the
    recursion, and extraction erases it. *)
Definition def_site (F : FCtx) (Hg : ⊢ᵍ fc_deps F ⍮ fc_stack F) (H : modexp) (ch : list string) : option qname :=
  match ch with
  | nil => None
  | _ :: _ =>
      match decl_impl F Hg (me_mems H (removelast ch)) (List.last ch EmptyString) with
      | inleft (exist _ (qd, _) _) => Some (qname_in qd (List.last ch EmptyString))
      | inright _ => None
      end
  end.

Lemma def_site_spec : forall F Hg H ch qx,
    def_site F Hg H ch = Some qx <->
    ch <> nil /\ exists qd pv, mdecl (fc_deps F) (fc_stack F) (me_mems H (removelast ch)) (List.last ch EmptyString) qd pv /\
      qx = qname_in qd (List.last ch EmptyString).
Proof.
  intros *; unfold def_site.
  destruct ch as [| z ch']; [ split; [ discriminate | intros [Hn _]; contradiction ] |].
  destruct (decl_impl _ _ _ _) as [[[qd pv] Hd] | HN]; cbn [fst snd] in *; split.
  - intros [= <-]; split; [ discriminate |]; exists qd, pv; split; [ exact Hd | reflexivity ].
  - intros (_ & qd' & pv' & Hd' & ->); destruct (mdecl_functional _ _ Hg _ _ _ _ Hd _ _ Hd') as [<- _]; reflexivity.
  - discriminate.
  - intros (_ & qd' & pv' & Hd' & _); exfalso; exact (HN _ _ Hd').
Qed.

(** The name found is that of an entry. *)
Corollary def_site_entry : forall F Hg H ch qx, ch <> nil ->
    def_site F Hg H ch = Some qx -> exists E, gc_entry (fc_deps F) (fc_stack F) qx = Some E.
Proof.
  intros * _ Hq; apply def_site_spec in Hq as (_ & qd & pv & Hd & ->).
  destruct (mdecl_entry _ _ _ _ _ _ Hd) as (E & HE & _); exists E; exact HE.
Qed.

(** What resolves is reached through body modules. *)
Lemma gm_resolve_walk : forall Φ ch E, gm_resolve Φ ch = Some E ->
    forall pre y suf, ch = pre ++ y :: suf -> suf <> nil ->
    exists E0, gm_entry Φ (pre ++ y :: nil) = Some E0 /\ entry_is_body E0.
Proof.
  fix IH 1; intros [| Φ0 z E1 | Φ0 c its] ch E Hr pre y suf Hch Hsuf; cbn in Hr; [ discriminate | | exact (IH _ _ _ Hr _ _ _ Hch Hsuf) ].
  destruct ch as [| x ip]; [ discriminate |].
  destruct (String.eqb_spec x z) as [-> | Hne].
  - destruct ip as [| w ip']; [ destruct pre as [| ? [| ? ?]]; cbn in Hch; injection Hch; intros; subst; try contradiction; discriminate |].
    destruct E1 as [| pv [Δ [sm Φ' | ?]] | pv pq k D Φ' | ? ? ? ? | pv pr Rr Φ']; try discriminate.
    + destruct pre as [| x' pre']; cbn in Hch; injection Hch as <- Hip.
      * exists (ge_mod pv (gu_mk Δ (md_body sm Φ'))); cbn; rewrite String.eqb_refl; split; [ reflexivity | exact I ].
      * destruct (IH _ _ _ Hr _ _ _ Hip Hsuf) as (E0 & HE0 & Hb).
        exists E0; cbn; rewrite String.eqb_refl.
        destruct (pre' ++ y :: nil) as [| ? ?] eqn:Ep; [ destruct pre'; discriminate | exact (conj HE0 Hb) ].
    + destruct pre as [| x' pre']; cbn in Hch; injection Hch as <- Hip.
      * exists (ge_ind pv pq k D Φ'); cbn; rewrite String.eqb_refl; split; [ reflexivity | exact I ].
      * destruct (IH _ _ _ Hr _ _ _ Hip Hsuf) as (E0 & HE0 & Hb).
        exists E0; cbn; rewrite String.eqb_refl.
        destruct (pre' ++ y :: nil) as [| ? ?] eqn:Ep; [ destruct pre'; discriminate | exact (conj HE0 Hb) ].
    + destruct pre as [| x' pre']; cbn in Hch; injection Hch as <- Hip.
      * exists (ge_record pv pr Rr Φ'); cbn; rewrite String.eqb_refl; split; [ reflexivity | exact I ].
      * destruct (IH _ _ _ Hr _ _ _ Hip Hsuf) as (E0 & HE0 & Hb).
        exists E0; cbn; rewrite String.eqb_refl.
        destruct (pre' ++ y :: nil) as [| ? ?] eqn:Ep; [ destruct pre'; discriminate | exact (conj HE0 Hb) ].
  - destruct (IH _ _ _ Hr _ _ _ Hch Hsuf) as (E0 & HE0 & Hb); exists E0; split; [| exact Hb ].
    destruct pre as [| x' pre']; cbn in Hch |- *; injection Hch as <- _;
      apply String.eqb_neq in Hne; rewrite Hne; exact HE0.
Qed.

(** A loaded unit, selected along body modules, is stored at its path. *)
Lemma site_resolve : forall Θ fp U, ⊢ᵍ Θ ⍮ nil -> gds_lookup Θ fp = Some U ->
    forall pre, (forall pre' y suf, pre = pre' ++ y :: suf ->
                   exists E0, gm_entry (gu_mod U) (pre' ++ y :: nil) = Some E0 /\ entry_is_body E0) ->
    msite Θ nil (me_mems (me_unit fp) pre) (q_abs fp pre).
Proof.
  intros * Hg Hl pre; induction pre as [| y pre IH] using rev_ind; intros Hw.
  - destruct (wf_gds_body _ _ Hg _ _ Hl) as (Δ & Φ & ->).
    eapply ms_unit; [ reflexivity | unfold gc_unit; cbn; rewrite Hl; reflexivity ].
  - rewrite me_mems_app; cbn [me_mems].
    destruct (Hw pre y nil eq_refl) as (E0 & HE0 & Hb).
    replace (q_abs fp (pre ++ y :: nil)) with (qname_in (q_abs fp pre) y) by reflexivity.
    eapply ms_body; [ | | exact Hb ].
    + apply IH; intros pre' y' suf Hpre; apply (Hw pre' y' (suf ++ y :: nil)); rewrite Hpre, <- app_assoc; reflexivity.
    + unfold gc_entry, gc_entry_u; cbn; rewrite Hl; exact HE0.
Qed.

(** A definition reached through body modules is declared where it stands. *)
Corollary def_site_resolve : forall F Hg p E, fc_stack F = nil ->
    gc_resolve (fc_deps F) nil p = Some E -> def_site F Hg (me_unit (q_unit p)) (q_chain p) = Some p.
Proof.
  intros * Hnil Hr; apply def_site_spec; rewrite Hnil.
  assert (Hg' : ⊢ᵍ fc_deps F ⍮ nil) by (rewrite <- Hnil; exact Hg); clear Hg; rename Hg' into Hg.
  set (Θ := fc_deps F) in *; clearbody Θ.
  assert (Hch : q_chain p <> nil).
  { intros Hn; unfold gc_resolve, gc_resolve_u in Hr; cbn in Hr; rewrite Hn in Hr.
    destruct (gds_lookup Θ (q_unit p)); [ rewrite gm_resolve_nil in Hr |]; discriminate. }
  split; [ exact Hch |].
  destruct p as [fp c]; cbn [q_unit q_chain] in *.
  pose proof (gc_entry_resolve _ _ _ _ Hr) as HE.
  unfold gc_resolve, gc_resolve_u in Hr; cbn in Hr.
  destruct (gds_lookup Θ fp) as [U |] eqn:Hl; [| discriminate ].
  pose proof (List.app_removelast_last EmptyString Hch) as Ec.
  exists (q_abs fp (removelast c)), (ge_private E); split.
  - apply mdecl_intro; [ apply (site_resolve _ _ _ Hg Hl); intros pre' y suf Hpre |].
    + apply (gm_resolve_walk _ _ _ Hr pre' y (suf ++ List.last c EmptyString :: nil)).
      * rewrite Ec at 1; rewrite Hpre, <- app_assoc; reflexivity.
      * destruct suf; discriminate.
    + replace (qname_in (q_abs fp (removelast c)) (List.last c EmptyString)) with (q_abs fp c); [ exact HE |].
      unfold qname_in; cbn; rewrite <- Ec; reflexivity.
  - unfold qname_in; cbn; rewrite <- Ec; reflexivity.
Qed.
