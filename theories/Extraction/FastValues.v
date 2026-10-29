From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.System Require Import Definitions Command.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Global Require Import Paths.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import FastEval FastDomain FastEvalGrowth FastGlobal.
Import Domain_Notations.
#[local] Open Scope list_scope.

(** * The Values the Fast Data Stores

    A transparent definition a command adds is stored with the value its
    body has in the empty environment ([fe_def], [fe_def_mod]), so that a
    selection evaluates the body once, not at every use.  A stored value
    is right in a global context ([stored_value_ok]) when it is the fast
    evaluation of the stored term there, and is itself right
    ([fdomain_ok]).  Every value stored in a unit, a body or an entry is
    right ([funit_values_ok] and the like), and stays right as the global
    context grows ([funit_values_grow] and the like,
    [Extraction.FastEvalGrowth]).  A translation stores no value, so its
    values are right anywhere ([tr_unit_values]).

    The values of the open frames are right in the context of the frame
    and those below it ([frames_values_ok]); in a well-formed stack they
    are right in the whole stack ([frames_values_current]).  A lookup
    through the fast context finds an entry whose values are right
    ([fgc_entry_values]). *)

(** ** Every Element of a Tree *)

(** [P] holds of every element of the tree [m]. *)
Fixpoint sraw_all {A} (P : A -> Prop) (m : SRaw.tree A) : Prop :=
  match m with
  | SRaw.Leaf _ => True
  | SRaw.Node l _ e r _ => sraw_all P l /\ P e /\ sraw_all P r
  end.

(** What [sfind] finds in a tree [P] holds of every element of, [P]
    holds of. *)
Lemma sraw_all_find : forall {A} (P : A -> Prop) x m e, sraw_all P m -> sfind x m = Some e -> P e.
Proof.
  intros A P x; induction m as [| l IHl y d r IHr h]; intros e Hm Hf; cbn in Hf; [ discriminate |].
  destruct Hm as (Hl & Hd & Hr); destruct (String.compare x y); [ injection Hf as <-; exact Hd | eauto | eauto ].
Qed.

(** A tree [P] holds of every element of is the tree of the elements of
    a tree of elements with their proofs of [P]. *)
Lemma sraw_all_sig : forall {A} (P : A -> Prop) m, sraw_all P m ->
    exists m' : SRaw.tree {a | P a}, m = SRaw.map (@proj1_sig _ _) m'.
Proof.
  intros A P; induction m as [| l IHl y d r IHr h]; intros Hm.
  - exists (SRaw.Leaf _); reflexivity.
  - destruct Hm as (Hl & Hd & Hr); destruct (IHl Hl) as [l' ->]; destruct (IHr Hr) as [r' ->].
    exists (SRaw.Node l' y (exist _ d Hd) r' h); reflexivity.
Qed.

(** [P] holds of every element of a tree of elements with their proofs
    of [P]. *)
Lemma sig_sraw_all : forall {A} (P : A -> Prop) (m' : SRaw.tree {a | P a}), sraw_all P (SRaw.map (@proj1_sig _ _) m').
Proof.
  intros A P; induction m' as [| l IHl y [d Hd] r IHr h]; cbn; [ exact I | split; [ exact IHl | split; [ exact Hd | exact IHr ] ] ].
Qed.

(** One element more, which [P] holds of, keeps [P] of every element. *)
Lemma sraw_all_add : forall {A} (P : A -> Prop) x e m, sraw_all P m -> P e -> sraw_all P (SRaw.add x e m).
Proof.
  intros A P x e m Hm He; destruct (sraw_all_sig P m Hm) as [m' ->].
  change e with (proj1_sig (exist P e He)); rewrite <- sraw_map_add; apply sig_sraw_all.
Qed.

(** [P] of every element implies [Q] of every element when [P] implies
    [Q]. *)
Lemma sraw_all_impl : forall {A} (P Q : A -> Prop) m, (forall e, P e -> Q e) -> sraw_all P m -> sraw_all Q m.
Proof.
  intros A P Q m H; induction m as [| l IHl y d r IHr h]; cbn; [ auto |].
  intros (Hl & Hd & Hr); split; [ exact (IHl Hl) | split; [ exact (H _ Hd) | exact (IHr Hr) ] ].
Qed.

(** ** Right Stored Values *)

Section ValuesOk.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** A value right for a closed term: its fast evaluation in the empty
      environment, and right itself *)
  Record value_ok (M : exp) (v : fdomain) : Prop := mk_value_ok
    { (** the term evaluates to it, fast, in the empty environment *)
      value_ok_eval : ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ nil ↘ fdomain_erase v
      (** the value is right *)
    ; value_ok_domain : fdomain_ok Θ Ξ v }.

  (** A stored value right for the stored term: no value, or one right
      for the term, which is then present *)
  Definition stored_value_ok (oM : option exp) (ov : option fdomain) : Prop :=
    match ov, oM with
    | None, _ => True
    | Some v, Some M => value_ok M v
    | Some _, None => False
    end.

  (** Every value stored in a unit, a body or an entry, nested ones
      included, is right. *)
  Fixpoint funit_values_ok (u : funit) : Prop :=
    match u with
    | fu_mk _ D => fmoddef_values_ok D
    | fu_core _ => True
    end
  with fmoddef_values_ok (D : fmoddef) : Prop :=
    match D with
    | fmd_body t => ftrie_values_ok t
    end
  with ftrie_values_ok (t : ftrie) : Prop :=
    match t with
    | ft_mk m _ => sraw_all fentry_values_ok m
    end
  with fentry_values_ok (e : fentry) : Prop :=
    match e with
    | fe_def _ _ _ oM ov => stored_value_ok oM ov
    | fe_mod _ u => funit_values_ok u
    | fe_ind _ _ _ _ t => ftrie_values_ok t
    | fe_def_mod _ _ M u ov => stored_value_ok (Some M) ov /\ funit_values_ok u
    | fe_record _ _ _ t => ftrie_values_ok t
    end.

  (** *** What a Lookup Finds *)

  Lemma ft_find_values : forall t x e, ftrie_values_ok t -> ft_find t x = Some e -> fentry_values_ok e.
  Proof. intros [m xs] x e Ht Hf; exact (sraw_all_find _ _ _ _ Ht Hf). Qed.

  Lemma fe_body_values : forall e t, fentry_values_ok e -> fe_body e = Some t -> ftrie_values_ok t.
  Proof.
    intros [b pv A oM ov | pv [Δ [t'] | U] | pv pq k D t' | pv A M u ov | pv p R t'] t He Hb; cbn in Hb;
      try discriminate; injection Hb as <-; exact He.
  Qed.

  Lemma ft_entry_values : forall ip t e, ftrie_values_ok t -> ft_entry t ip = Some e -> fentry_values_ok e.
  Proof.
    induction ip as [| x ip IH]; intros t e Ht Hf; cbn [ft_entry] in Hf; [ discriminate |].
    destruct (ft_find t x) as [e' |] eqn:Ef; [| discriminate ].
    pose proof (ft_find_values _ _ _ Ht Ef) as He'.
    destruct ip as [| y ip']; [ injection Hf as <-; exact He' |].
    destruct (fe_body e') as [t' |] eqn:Eb; [| discriminate ].
    exact (IH _ _ (fe_body_values _ _ He' Eb) Hf).
  Qed.

  Lemma fu_body_values : forall u, funit_values_ok u -> ftrie_values_ok (fu_body u).
  Proof. intros [Δ [t] | U] Hu; [ exact Hu | exact I ]. Qed.

  (** One entry more, its values right, keeps the values of a body
      right. *)
  Lemma ft_ext_values : forall t x e, ftrie_values_ok t -> fentry_values_ok e -> ftrie_values_ok (ft_ext t x e).
  Proof. intros [m xs] x e Ht He; exact (sraw_all_add _ _ _ _ Ht He). Qed.

  Lemma ft_empty_values : ftrie_values_ok ft_empty.
  Proof. exact I. Qed.

  (** *** No Value Stored *)

  (** With every value dropped, every value is right. *)
  Fixpoint funit_drop_values (u : funit) : funit_values_ok (funit_drop u)
  with ftrie_drop_values (t : ftrie) : ftrie_values_ok (ftrie_drop t)
  with fentry_drop_values (e : fentry) : fentry_values_ok (fentry_drop e).
  Proof.
    - destruct u as [Δ [t] | U]; cbn [funit_drop fmoddef_drop funit_values_ok fmoddef_values_ok]; [ apply ftrie_drop_values | exact I ].
    - destruct t as [m xs]; cbn [ftrie_drop ftrie_values_ok].
      revert m; fix IHm 1; intros [| l k e r h]; cbn [SRaw.map sraw_all]; [ exact I |].
      exact (conj (IHm l) (conj (fentry_drop_values e) (IHm r))).
    - destruct e; cbn [fentry_drop fentry_values_ok stored_value_ok];
        try (exact I); try (apply funit_drop_values); try (apply ftrie_drop_values).
      split; [ exact I | apply funit_drop_values ].
  Qed.

  (** A translation stores no value. *)
  Lemma tr_unit_values : forall U, funit_values_ok (tr_unit U).
  Proof. intros U; rewrite <- tr_unit_drop; apply funit_drop_values. Qed.

  Lemma tr_mod_values : forall Φ, ftrie_values_ok (tr_mod Φ).
  Proof. intros Φ; rewrite <- tr_mod_drop; apply ftrie_drop_values. Qed.

  Lemma tr_entry_values : forall E, fentry_values_ok (tr_entry E).
  Proof. intros E; rewrite <- tr_entry_drop; apply fentry_drop_values. Qed.
End ValuesOk.

(** ** Along a Growth of the Global Context *)

Section ValuesGrow.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hs : gc_sub Θ1 Ξ1 Θ2 Ξ2.

  Lemma value_ok_grow : forall M v, value_ok Θ1 Ξ1 M v -> value_ok Θ2 Ξ2 M v.
  Proof.
    intros M v [He Hv]; constructor; [ exact (fast_eval_exp_grow _ _ _ _ Hs _ _ _ He) | exact (proj1 (fdomain_ok_grow _ _ _ _ Hs) _ Hv) ].
  Qed.

  Lemma stored_value_grow : forall oM ov, stored_value_ok Θ1 Ξ1 oM ov -> stored_value_ok Θ2 Ξ2 oM ov.
  Proof. intros [M |] [v |] H; cbn in *; auto using value_ok_grow. Qed.

  Fixpoint funit_values_grow (u : funit) : funit_values_ok Θ1 Ξ1 u -> funit_values_ok Θ2 Ξ2 u
  with ftrie_values_grow (t : ftrie) : ftrie_values_ok Θ1 Ξ1 t -> ftrie_values_ok Θ2 Ξ2 t
  with fentry_values_grow (e : fentry) : fentry_values_ok Θ1 Ξ1 e -> fentry_values_ok Θ2 Ξ2 e.
  Proof.
    - destruct u as [Δ [t] | U]; cbn [funit_values_ok fmoddef_values_ok]; [ apply ftrie_values_grow | auto ].
    - destruct t as [m xs]; cbn [ftrie_values_ok].
      revert m; fix IHm 1; intros [| l k e r h]; cbn [sraw_all]; [ auto |].
      intros (Hl & He & Hr); exact (conj (IHm l Hl) (conj (fentry_values_grow e He) (IHm r Hr))).
    - destruct e; cbn [fentry_values_ok]; try (apply stored_value_grow); try (apply funit_values_grow); try (apply ftrie_values_grow).
      intros [Hv Hu]; split; [ exact (stored_value_grow _ _ Hv) | exact (funit_values_grow _ Hu) ].
  Qed.
End ValuesGrow.

(** ** The Values of the Open Frames

    Each frame's values are right in the context of the frame and the
    frames below it, where they were computed: closing the innermost frame
    leaves the others' right. *)
Fixpoint frames_values_ok (Θ : gdeps) (fs : fstack) : Prop :=
  match fs with
  | nil => True
  | f :: fs' => ftrie_values_ok Θ (dec_stack fs) (ff_body f) /\ frames_values_ok Θ fs'
  end.

(** In a well-formed stack, every frame's values are right in the whole
    stack. *)
Lemma frames_values_current : forall Θ fs, ⊢ᵍ Θ ⍮ dec_stack fs -> frames_values_ok Θ fs ->
    Forall (fun f => ftrie_values_ok Θ (dec_stack fs) (ff_body f)) fs.
Proof.
  intros Θ; induction fs as [| f fs IH]; intros HΞ Hv; [ constructor |].
  destruct Hv as [Hf Hv].
  change (dec_stack (f :: fs)) with ((dec_frame f :: nil) ++ dec_stack fs) in HΞ |- *.
  destruct (wf_gstack_app_inv _ _ _ HΞ) as [HΞ' Hsub].
  constructor; [ exact Hf |].
  refine (Forall_impl _ _ (IH HΞ' Hv)); intros f' Hf'; exact (ftrie_values_grow _ _ _ _ Hsub _ Hf').
Qed.

(** The frames' values stay right as more units are filed or seen. *)
Lemma frames_values_deps : forall Θ Θ' fs, Θ ⊑ Θ' -> frames_values_ok Θ fs -> frames_values_ok Θ' fs.
Proof.
  intros Θ Θ' fs HΘ; induction fs as [| f fs IH]; cbn [frames_values_ok]; [ auto |].
  intros [Hf Hfs]; split; [ exact (ftrie_values_grow _ _ _ _ (gc_sub_deps _ _ _ HΘ) _ Hf) | exact (IH Hfs) ].
Qed.

(** A frame opened, empty *)
Lemma frames_values_push : forall Θ fs f, frames_values_ok Θ fs -> ff_body f = ft_empty -> frames_values_ok Θ (f :: fs).
Proof. intros * Hfs Ht; cbn [frames_values_ok]; rewrite Ht; split; [ exact (ft_empty_values _ _) | exact Hfs ]. Qed.

(** An entry added to the innermost frame, its values right there *)
Lemma frames_values_add : forall Θ fs x e E, ⊢ᵍ Θ ⍮ dec_stack fs -> ⊢ᵍ Θ ⍮ gs_add x E (dec_stack fs) -> frames_values_ok Θ fs ->
    dec_stack (fs_add x e fs) = gs_add x E (dec_stack fs) -> fentry_values_ok Θ (gs_add x E (dec_stack fs)) e ->
    frames_values_ok Θ (fs_add x e fs).
Proof.
  intros Θ [| f fs] x e E HΞ HΞ' Hv Ed He; [ exact I |].
  assert (Hfr : gs_fresh x (dec_stack (f :: fs))) by (destruct f as [mp Kf Δ t]; exact (wf_gstack_ext_fresh _ _ _ _ _ _ _ _ HΞ')).
  destruct Hv as [Hf Hfs].
  change (frames_values_ok Θ (fs_add x e (f :: fs))) with
    (ftrie_values_ok Θ (dec_stack (fs_add x e (f :: fs))) (ft_ext (ff_body f) x e) /\ frames_values_ok Θ fs).
  rewrite Ed; split; [| exact Hfs ].
  apply ft_ext_values; [ exact (ftrie_values_grow _ _ _ _ (gc_sub_add _ _ _ _ HΞ Hfr) _ Hf) | exact He ].
Qed.

(** Alike, the entry's values right before it is added *)
Lemma frames_values_add_before : forall Θ fs x e E, ⊢ᵍ Θ ⍮ dec_stack fs -> ⊢ᵍ Θ ⍮ gs_add x E (dec_stack fs) -> frames_values_ok Θ fs ->
    dec_stack (fs_add x e fs) = gs_add x E (dec_stack fs) -> fentry_values_ok Θ (dec_stack fs) e ->
    frames_values_ok Θ (fs_add x e fs).
Proof.
  intros Θ [| f fs] x e E HΞ HΞ' Hv Ed He; [ exact I |].
  assert (Hfr : gs_fresh x (dec_stack (f :: fs))) by (destruct f as [mp Kf Δ t]; exact (wf_gstack_ext_fresh _ _ _ _ _ _ _ _ HΞ')).
  exact (frames_values_add _ _ _ _ _ HΞ HΞ' Hv Ed (fentry_values_grow _ _ _ _ (gc_sub_add _ _ _ _ HΞ Hfr) _ He)).
Qed.

(** The innermost frame [f], closed into the entry [e] of the frame below
    it: [f]'s values were right with [f] open, and are where it is
    closed. *)
Lemma frames_values_close : forall Θ Θ' fs f x pv e, Θ ⊑ Θ' -> frames_values_ok Θ fs ->
    ftrie_values_ok Θ' (dec_frame f :: dec_stack fs) (ff_body f) ->
    ⊢ᵍ Θ' ⍮ dec_stack fs -> gs_fresh x (dec_stack fs) ->
    ⊢ᵍ Θ' ⍮ gs_add x (frame_entry pv (ff_path f) (ff_kind f) (ff_params f) (dec_mod (ff_body f))) (dec_stack fs) ->
    ff_path f = qname_in (gs_path (dec_stack fs)) x ->
    kind_tele (ff_path f) (ff_kind f) (ff_params f) (gs_tele (dec_stack fs)) ->
    (forall Θ0 Ξ0, ftrie_values_ok Θ0 Ξ0 (ff_body f) -> fentry_values_ok Θ0 Ξ0 e) ->
    dec_stack (fs_add x e fs) = gs_add x (frame_entry pv (ff_path f) (ff_kind f) (ff_params f) (dec_mod (ff_body f))) (dec_stack fs) ->
    frames_values_ok Θ' (fs_add x e fs).
Proof.
  intros * HΘ Hfs Hf HΞ Hfr HΞ' Hp HK He Ed.
  apply (frames_values_add _ _ _ _ _ HΞ HΞ' (frames_values_deps _ _ _ HΘ Hfs) Ed).
  apply He; destruct f as [mp Kf Δ t]; cbn [ff_path ff_kind ff_params ff_body dec_frame] in *; subst mp.
  exact (ftrie_values_grow _ _ _ _ (gc_sub_close _ _ _ pv _ _ _ HΞ Hfr HK) _ Hf).
Qed.

(** The frames of a translation store no value. *)
Lemma fs_of_values : forall Θ Ξ, frames_values_ok Θ (fs_of Ξ).
Proof.
  intros Θ; induction Ξ as [| [[mp K] U] Ξ IH]; cbn [fs_of frames_values_ok]; [ exact I |].
  split; [| exact IH ]; destruct U as [Δ [[|] Φ | H]]; cbn; first [ apply tr_mod_values | exact I ].
Qed.

(** Alike, in any context *)
Lemma fs_of_values_all : forall Θ Ξ' Ξ, Forall (fun f => ftrie_values_ok Θ Ξ' (ff_body f)) (fs_of Ξ).
Proof.
  intros Θ Ξ'; induction Ξ as [| [[mp K] U] Ξ IH]; cbn [fs_of]; constructor; [| exact IH ].
  destruct U as [Δ [[|] Φ | H]]; cbn; first [ apply tr_mod_values | exact I ].
Qed.

(** ** What a Lookup Finds *)

(** The frame [fs_find] finds is one of the stack's. *)
Lemma fs_find_in : forall fs p f ip, fs_find fs p = Some (f, ip) -> In f fs.
Proof.
  induction fs as [| f' fs IH]; intros p f ip H; cbn in H; [ discriminate |].
  destruct (qname_strip (ff_path f') p); [ injection H as <- _; left; reflexivity | right; exact (IH _ _ _ H) ].
Qed.

(** An entry looked up through units and frames whose values are right
    has right values. *)
Lemma fgc_entry_values : forall Θ Ξ (uf : path -> option funit) fs p e,
    (forall fp u, uf fp = Some u -> funit_values_ok Θ Ξ u) ->
    Forall (fun f => ftrie_values_ok Θ Ξ (ff_body f)) fs ->
    fgc_entry uf fs p = Some e -> fentry_values_ok Θ Ξ e.
Proof.
  intros * Hu Hfs He; unfold fgc_entry in He.
  destruct (fs_find fs p) as [[f ip] |] eqn:Ef.
  - pose proof (proj1 (Forall_forall _ _) Hfs _ (fs_find_in _ _ _ _ Ef)) as Hf.
    exact (ft_entry_values _ _ _ _ _ Hf He).
  - destruct (uf (q_unit p)) as [u |] eqn:Eu; [| discriminate ].
    exact (ft_entry_values _ _ _ _ _ (fu_body_values _ _ _ (Hu _ _ Eu)) He).
Qed.

(** ** The Units Seen *)

(** A unit seen after [fus_see] is one filed, or one seen before. *)
Lemma fus_see_vis : forall L s fp u, pk_find fp (fus_vis (fus_see L s)) = Some u ->
    fus_find s fp = Some u \/ pk_find fp (fus_vis s) = Some u.
Proof.
  intros L s fp u; unfold fus_see; cbn [fus_vis fus_with_vis].
  assert (H : forall m, (forall u', pk_find fp m = Some u' -> fus_find s fp = Some u' \/ pk_find fp (fus_vis s) = Some u') ->
    pk_find fp (fold_left (fun m fq => match fus_find s fq with Some u => pk_add fq u m | None => m end) L m) = Some u ->
    fus_find s fp = Some u \/ pk_find fp (fus_vis s) = Some u).
  { induction L as [| fq L IH]; intros m Hm; cbn [fold_left]; [ apply Hm |].
    apply IH; intros u' Hu'.
    destruct (fus_find s fq) as [w |] eqn:Ew; [| exact (Hm _ Hu') ].
    rewrite pk_find_add in Hu'; destruct (path_beq fp fq) eqn:Eb; [| exact (Hm _ Hu') ].
    apply path_beq_true in Eb as ->; injection Hu' as <-; left; exact Ew. }
  apply H; auto.
Qed.
