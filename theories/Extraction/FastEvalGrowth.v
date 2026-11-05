From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.System.Global Require Import Paths LookupSound.
From Mctt.Core.Semantic Require Import Evaluation.
From Mctt.Extraction Require Import FastEval FastDomain.
Import Domain_Notations.
#[local] Open Scope list_scope.

(** * The Fast Evaluation Along a Growth of the Global Context

    A global context grows ([gc_sub Θ1 Ξ1 Θ2 Ξ2]) as a run goes on: an
    entry is added to an open frame, a frame is opened or closed, a unit is
    filed or seen.  What [Θ1 ⍮ Ξ1] resolves, [Θ2 ⍮ Ξ2] resolves the same
    way.  So the kinds of members ([dmod_member_kind] and the relations
    mutual with it), every relation of the fast evaluation
    ([Extraction.FastEval]) and the rightness of a fast value
    ([fdomain_ok]) hold in [Θ2 ⍮ Ξ2] wherever they hold in [Θ1 ⍮ Ξ1].

    This is what lets a value computed once, when its definition is added,
    stand for the definition's body in every later context
    ([Extraction.Evaluation], [Extraction.Command]). *)

(** An alias module is an entry at its path: an alias submodule, or a
    definition with a module part, whose module part is the alias. *)
Lemma gm_submodule_alias_entry : forall Φ T x ip U, gm_submodule T Φ x ip = Some (mr_alias U) ->
    exists E, gm_entry Φ (x :: ip) = Some E /\ ((exists pv, E = ge_mod pv U) \/ (exists pv A M, E = ge_def_mod pv A M U)).
Proof.
  fix IH 1; intros [| Φ y E | Φ c its] * Hs; cbn in Hs |- *; [ discriminate | | exact (IH _ _ _ _ _ Hs) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ Hs) ].
  destruct E as [? ? ? ? | ? [Δ [? Φ' | E']] | ? ? ? D Φ' | ? Aa Ma [Δa [? Φa | Ea]] | ? Rr ΦR]; try discriminate;
    destruct ip as [| z ip]; try discriminate; try (exact (IH _ _ _ _ _ Hs)); injection Hs as <-; eauto 8.
Qed.

Lemma gc_module_alias_entry : forall Θ Ξ p U, gc_module Θ Ξ p = Some (mr_alias U) ->
    exists E, gc_entry Θ Ξ p = Some E /\ ((exists pv, E = ge_mod pv U) \/ (exists pv A M, E = ge_def_mod pv A M U)).
Proof.
  intros * H; unfold gc_module, gc_module_u, gc_entry, gc_entry_u in *; rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[V [| x ip]] T] |]; cbn; [ discriminate | eapply gm_submodule_alias_entry; exact H |].
  destruct (gds_lookup Θ (q_unit p)) as [V |]; [| discriminate ].
  unfold gm_module in H; destruct (q_chain p) as [| x ip]; [ discriminate | eapply gm_submodule_alias_entry; exact H ].
Qed.

(** ** Where a Member's Module Is Stored

    A selection from a saturated global module ([module_saturated]) reads
    the module's telescope off where the module is stored.  In a
    well-formed context, a module one of whose members is found is
    stored. *)

(** An entry below a body's member [x] is in the body [x] names. *)
Lemma gm_entry_snoc_inv : forall Φ T x ip y E, gm_entry Φ (x :: ip ++ y :: nil) = Some E ->
    exists T' Φ', gm_subbody T Φ x ip = Some (T', Φ') /\ gm_entry Φ' (y :: nil) = Some E.
Proof.
  fix IH 1; intros [| Φ z E0 | Φ H its] T x ip y E He; cbn in He |- *; [ discriminate | | exact (IH _ _ _ _ _ _ He) ].
  destruct (String.eqb x z); [| exact (IH _ _ _ _ _ _ He) ].
  destruct ip as [| w ip]; cbn in He.
  - destruct E0 as [? ? ? ? ? | ? [Δ [sm Φ' | E']] | ? ? ? D Φ' | ? ? ? ? | ? pr R Φ']; try discriminate; eauto.
  - destruct E0 as [? ? ? ? ? | ? [Δ [sm Φ' | E']] | ? ? ? D Φ' | ? ? ? ? | ? pr R Φ']; try discriminate; eapply IH; exact He.
Qed.

(** A module one of whose entries is found is stored: an open frame, or a
    body module. *)
Lemma entry_parent_loc : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p y E, gc_entry Θ Ξ (qname_in p y) = Some E ->
    exists T Φ, loc Θ Ξ p T Φ.
Proof.
  intros * Hg * He; unfold gc_entry, gc_entry_u in He; rewrite gs_find_tele_find in He.
  destruct (gs_find_tele Ξ (qname_in p y)) as [[[U ip] T0] |] eqn:Ef; cbn [option_map] in He.
  - destruct (gs_find_tele_body _ _ Hg _ _ _ _ Ef) as (ΔU & ΦU & ->); cbn [gu_mod] in He.
    destruct (gs_find_tele_found _ _ _ _ _ Ef) as (F & HF & HFf).
    apply qname_strip_app_inv in HF.
    destruct ip as [| w ip] using rev_ind; [ rewrite gm_entry_nil in He; discriminate |].
    clear IHip.
    assert (Hy : w = y /\ p = qname_app F ip).
    { destruct p as [fq cq], F as [ff cf]; unfold qname_in, qname_app in HF |- *; cbn in HF |- *.
      injection HF as -> Hc; rewrite List.app_assoc in Hc.
      apply List.app_inj_tail in Hc as [-> ->]; split; reflexivity. }
    destruct Hy as [-> ->].
    destruct ip as [| x ip].
    + exists (ΔU ++ T0), ΦU; left; unfold gc_frame; rewrite qname_app_nil, HFf; reflexivity.
    + cbn [app] in He.
      destruct (gm_entry_snoc_inv _ (ΔU ++ T0) _ _ _ _ He) as (Tq & Φq & Hsb & _).
      destruct (gs_find_tele_head _ _ Hg _ _ _ _ _ Ef (gm_subbody_head _ _ _ _ _ Hsb)) as (Fp & HFp & HFall).
      assert (Fp = F) as ->.
      { destruct F as [ff cf], Fp as [fp' cp']; unfold qname_app in HFp, HF; cbn in HFp, HF.
        rewrite HF in HFp; injection HFp as -> Hc.
        apply List.app_inv_tail in Hc as ->; reflexivity. }
      exists Tq, Φq; right; unfold gc_body; rewrite HFall; exact Hsb.
  - destruct (gds_lookup Θ (q_unit (qname_in p y))) as [Uf |] eqn:El; [| discriminate ].
    cbn [q_unit qname_in q_chain] in El, He.
    pose proof (gs_find_tele_filed _ _ Hg p _ El nil) as Ef0; rewrite qname_app_nil in Ef0.
    destruct (q_chain p) as [| x ip] eqn:Hc.
    + exists (gu_params Uf), (gu_mod Uf); right; unfold gc_body; rewrite Ef0, El, Hc; reflexivity.
    + cbn [app] in He.
      destruct (gm_entry_snoc_inv _ (gu_params Uf) _ _ _ _ He) as (Tq & Φq & Hsb & _).
      exists Tq, Φq; right; unfold gc_body; rewrite Ef0, El, Hc; exact Hsb.
Qed.

(** What a selection from a global module finds below it: a term part, a
    definition, the module of a member of a group or a record type. *)
Definition child_found (Θ : gdeps) (Ξ : gstack) (pc : qname) : Prop :=
  (exists E, gc_entry Θ Ξ pc = Some E) \/ (exists r, gs_find_ind Ξ pc = Some r) \/ (exists R, gs_find_record Ξ pc = Some R).

Lemma child_found_term : forall Θ Ξ pc M, gc_term Θ Ξ pc = Some M -> child_found Θ Ξ pc.
Proof.
  intros * H; left; unfold gc_term in H.
  destruct (gc_resolve Θ Ξ pc) as [E |] eqn:Er; [ exists E; exact (gc_resolve_entry _ _ _ _ Er) |].
  destruct (gc_entry Θ Ξ pc) as [E |]; [ eauto | discriminate ].
Qed.

Lemma child_found_resolve : forall Θ Ξ pc E, gc_resolve Θ Ξ pc = Some E -> child_found Θ Ξ pc.
Proof. intros * H; left; exists E; exact (gc_resolve_entry _ _ _ _ H). Qed.

Lemma child_found_ind : forall Θ Ξ pc r, ind_mlookup Θ Ξ pc = Some r -> child_found Θ Ξ pc.
Proof.
  intros Θ Ξ pc [[pq k] D] H; destruct (ind_mlookup_entry _ _ _ _ _ _ H) as [(pv & Φ & He) | Hf]; [ left | right; left ]; eauto.
Qed.

Lemma child_found_record : forall Θ Ξ pc R, record_lookup Θ Ξ pc = Some R -> child_found Θ Ξ pc.
Proof.
  intros * H; unfold record_lookup in H.
  destruct (gs_find_record Ξ pc) as [R' |] eqn:Hf; [ right; right; eauto |].
  destruct (gc_entry Θ Ξ pc) as [E |] eqn:He; [ left; eauto | discriminate ].
Qed.

(** A global module a member of which is found is stored. *)
Lemma child_found_parent_loc : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall p x, child_found Θ Ξ (qname_app p (x :: nil)) ->
    exists T Φ, gc_loc Θ Ξ p = Some (T, Φ).
Proof.
  intros * Hg * Hc; rewrite <- qname_in_app in Hc.
  assert (Hl : exists T Φ, loc Θ Ξ p T Φ).
  { destruct Hc as [(E & He) | [([[pq k] D] & Hf) | (R & Hf)]].
    - exact (entry_parent_loc _ _ Hg _ _ _ He).
    - destruct (frame_ind_loc _ _ Hg _ _ _ _ Hf) as (U & T0 & T & Φ & Mk & _ & Hfr & _ & _).
      exact (loc_parent _ _ Hg _ _ _ _ (or_introl Hfr)).
    - destruct (frame_record_loc _ _ Hg _ _ Hf) as (U & T0 & T & Φ & _ & Hfr & _).
      exact (loc_parent _ _ Hg _ _ _ _ (or_introl Hfr)). }
  destruct Hl as (T & Φ & Hl); exists T, Φ; exact (gc_loc_of_loc _ _ Hg _ _ _ Hl).
Qed.

Scheme fdomain_ok_mut_ind0 := Minimality for fdomain_ok Sort Prop
with fdomain_ne_ok_mut_ind0 := Minimality for fdomain_ne_ok Sort Prop
with fdomain_nf_ok_mut_ind0 := Minimality for fdomain_nf_ok Sort Prop
with fdmod_ok_mut_ind0 := Minimality for fdmod_ok Sort Prop
with fdentry_ok_mut_ind0 := Minimality for fdentry_ok Sort Prop
with fentry_type_ok_mut_ind0 := Minimality for fentry_type_ok Sort Prop.
(** What the scheme states of every element, as a [Forall] *)
Lemma Forall_all_Forall : forall A (P : A -> Prop) (R : A -> Prop) l (H : Forall P l),
    Forall_all A P (fun x _ => R x) l H -> Forall R l.
Proof. intros * Ha; induction Ha; constructor; assumption. Qed.

Combined Scheme fdomain_ok_mut_ind from fdomain_ok_mut_ind0, fdomain_ne_ok_mut_ind0, fdomain_nf_ok_mut_ind0, fdmod_ok_mut_ind0, fdentry_ok_mut_ind0,
  fentry_type_ok_mut_ind0.

Section Growth.
  Variables (Θ1 : gdeps) (Ξ1 : gstack) (Θ2 : gdeps) (Ξ2 : gstack).
  Hypothesis Hs : gc_sub Θ1 Ξ1 Θ2 Ξ2.

  (** ** The Lookups *)

  (** The term part of a definition stays: a transparent definition's
      body resolves alike, and a definition with a module part's entry
      grows into itself. *)
  Lemma gc_term_grows : forall p M, gc_term Θ1 Ξ1 p = Some M -> gc_term Θ2 Ξ2 p = Some M.
  Proof.
    intros * H; unfold gc_term in H |- *.
    destruct (gc_resolve Θ1 Ξ1 p) as [E |] eqn:Er.
    - destruct E as [[|] pv [| |] A [M' |] | | | |]; try discriminate;
        try (rewrite (gc_sub_resolve _ _ _ _ _ _ Hs Er); assumption).
      all: pose proof (gc_resolve_entry _ _ _ _ Er) as Ee; rewrite Ee in H; try discriminate.
      exfalso; rewrite (gc_entry_def_mod _ _ _ _ _ _ _ Ee) in Er; discriminate.
    - destruct (gc_entry Θ1 Ξ1 p) as [[| | | pv A M' U |] |] eqn:Ee; try discriminate; injection H as <-.
      destruct (gc_sub_entry _ _ _ _ _ _ Hs Ee) as (E' & He' & Hg); cbn in Hg; subst E'.
      rewrite (gc_entry_def_mod _ _ _ _ _ _ _ He'), He'; reflexivity.
  Qed.

  (** A location stays one, perhaps of a grown body: an open frame stays
      open or is filed, and a body grows. *)
  Lemma gc_loc_grows : forall p TΦ, gc_loc Θ1 Ξ1 p = Some TΦ -> exists TΦ', gc_loc Θ2 Ξ2 p = Some TΦ'.
  Proof.
    intros p [T Φ] H; unfold gc_loc in H |- *.
    destruct (gc_frame Ξ1 p) as [[T0 Φ0] |] eqn:Ef.
    - injection H as <- <-.
      destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hs Ef) as (Φ' & [(Hf2 & _ & _) | (Hb2 & _ & _)]).
      + rewrite Hf2; eauto.
      + destruct (gc_frame Ξ2 p); eauto.
    - destruct (gc_sub_body _ _ _ _ _ _ _ Hs H) as (Φ' & Hb2 & _).
      destruct (gc_frame Ξ2 p); eauto.
  Qed.

  (** A member with a term part and a module part stays one. *)
  Lemma dm_path_grows : forall p, dm_path Θ1 Ξ1 p -> dm_path Θ2 Ξ2 p.
  Proof.
    intros p [(r & Hl) | [(R & Hl) | (pv & A & M & U & He)]].
    - left; exists r; exact (ind_mlookup_gc_sub _ _ _ _ _ _ Hs Hl).
    - right; left; exists R; exact (record_lookup_gc_sub _ _ _ _ _ _ Hs Hl).
    - right; right; destruct (gc_sub_entry _ _ _ _ _ _ Hs He) as (E' & He' & Hg); cbn in Hg; subst E'; eauto 6.
  Qed.

  (** A definition names no member with a term part and a module part,
      before and after. *)
  Lemma not_dm_path_def_grows : forall p b pv r A B, gc_resolve Θ1 Ξ1 p = Some (ge_def b pv r A B) -> ~ dm_path Θ2 Ξ2 p.
  Proof. intros * H; exact (gc_resolve_def_not_dm _ _ _ _ _ _ _ _ (gc_sub_resolve _ _ _ _ _ _ Hs H)). Qed.

  (** A location that is no member with a term part and a module part
      stays none: a frame of no member's and no record type's module is
      filed as a plain body or stays open, and a plain body module stays
      one. *)
  Lemma not_dm_path_loc_grows : forall p TΦ, gc_loc Θ1 Ξ1 p = Some TΦ -> ~ dm_path Θ1 Ξ1 p -> ~ dm_path Θ2 Ξ2 p.
  Proof.
    intros p [T Φ] Hl Hn; unfold gc_loc in Hl.
    destruct (gc_frame Ξ1 p) as [[T0 Φ0] |] eqn:Ef.
    - injection Hl as <- <-.
      apply (frame_not_dm_sub _ _ _ _ _ _ _ Hs Ef).
      + destruct (gs_find_ind Ξ1 p) as [r |] eqn:Hk; [| reflexivity ].
        exfalso; apply Hn; left; exists r; exact (gc_sub_frame_ind _ _ _ _ _ _ (gc_sub_refl Θ1 Ξ1) Hk).
      + destruct (gs_find_record Ξ1 p) as [R |] eqn:Hk; [| reflexivity ].
        exfalso; apply Hn; right; left; exists R; exact (gc_sub_frame_record _ _ _ _ _ _ (gc_sub_refl Θ1 Ξ1) Hk).
    - destruct (gc_body_module _ _ _ _ _ Hl) as [oD Hm].
      destruct oD as [r |].
      { exfalso; apply Hn; left; exists r; rewrite (ind_mlookup_body _ _ _ _ _ Hm); reflexivity. }
      assert (Hr : record_lookup Θ1 Ξ1 p = None).
      { destruct (record_lookup Θ1 Ξ1 p) as [R |] eqn:Hr; [| reflexivity ].
        exfalso; apply Hn; right; left; eauto. }
      apply (module_body_not_dm _ _ _ T); [ exact (gc_sub_module _ _ _ _ _ _ Hs Hm) |].
      exact (record_lookup_none_gc_sub _ _ _ _ _ _ _ Hs Hl Hr).
  Qed.

  (** An alias that is no member with a term part and a module part stays
      none: its entry is an alias submodule, which stays itself. *)
  Lemma not_dm_path_alias_grows : forall p U, gc_module Θ1 Ξ1 p = Some (mr_alias U) -> ~ dm_path Θ1 Ξ1 p -> ~ dm_path Θ2 Ξ2 p.
  Proof.
    intros * Hm Hn.
    destruct (gc_module_alias_entry _ _ _ _ Hm) as (E & He & [(pv & ->) | (pv & A & M & ->)]);
      [| exfalso; apply Hn; right; right; eauto 6 ].
    destruct (gc_module_alias_unit _ _ _ _ Hm) as (Δ & E0 & ->).
    destruct (gc_sub_entry _ _ _ _ _ _ Hs He) as (E' & He' & Hg); cbn in Hg; subst E'.
    exact (module_alias_not_dm _ _ _ _ _ _ (gc_sub_module _ _ _ _ _ _ Hs Hm) He').
  Qed.

  (** ** The Kinds of Members *)

  Theorem kinds_grow :
    (forall h ch k, dmod_member_kind Θ1 Ξ1 h ch k -> dmod_member_kind Θ2 Ξ2 h ch k) /\
    (forall ρ U ch k, gunit_member_kind Θ1 Ξ1 ρ U ch k -> gunit_member_kind Θ2 Ξ2 ρ U ch k) /\
    (forall ρ H ch k, modexp_member_kind Θ1 Ξ1 ρ H ch k -> modexp_member_kind Θ2 Ξ2 ρ H ch k) /\
    (forall ρ Φ ρ1, kinds_env Θ1 Ξ1 ρ Φ ρ1 -> kinds_env Θ2 Ξ2 ρ Φ ρ1).
  Proof.
    apply kind_mut_ind; intros; try solve [ econstructor; eauto ].
    - eapply dmod_member_kind_global_here_def; eapply gc_sub_resolve; eassumption.
    - apply dmod_member_kind_global_here_mod; destruct o as [(T & oD & Hm) | ([T Φ] & Hf)].
      + left; exists T, oD; exact (gc_sub_module _ _ _ _ _ _ Hs Hm).
      + destruct (gc_sub_frame_loc _ _ _ _ _ _ _ Hs Hf) as (Φ' & [(Hf2 & _ & _) | (_ & Hm2 & _)]); eauto.
    - destruct (gc_loc_grows _ _ e) as (TΦ' & e').
      eapply dmod_member_kind_global_here_dm; [ exact (dm_path_grows _ d) | exact e' ].
    - eapply dmod_member_kind_global_alias_case; [ exact (gc_sub_module _ _ _ _ _ _ Hs e) | | exact H ].
      destruct o as [? | Hn]; [ left; assumption | right; exact (not_dm_path_alias_grows _ _ e Hn) ].
    - eapply dmod_member_kind_global_alias_dm; [ exact (gc_sub_module _ _ _ _ _ _ Hs e) | exact (dm_path_grows _ d) | exact H ].
    - apply dmod_member_kind_global_step; [ | | exact H ].
      + destruct o as [(TΦ & Hl) | (b & pv & r & A & B & Hr)].
        * left; exact (gc_loc_grows _ _ Hl).
        * right; exists b, pv, r, A, B; exact (gc_sub_resolve _ _ _ _ _ _ Hs Hr).
      + destruct o0 as [? | Hn]; [ left; assumption | right ].
        destruct o as [(TΦ & Hl) | (b & pv & r & A & B & Hr)].
        * exact (not_dm_path_loc_grows _ _ Hl Hn).
        * exact (not_dm_path_def_grows _ _ _ _ _ _ Hr).
  Qed.

  (** ** The Fast Evaluation

      Evaluation reads two things whose absence counts: the kind of a
      function's next argument ([arg_kind], relevant when the
      constructor's group is not found) and whether a global module lacks
      no parameter ([module_saturated], over where the module is stored).
      The first is read only of a function the evaluation then applies,
      which finds the group; the second only where a member of the module
      is found, so that the module is stored, with the same telescope in
      the bigger context, when both contexts are well-formed. *)

  Hypothesis Hg1 : ⊢ᵍ Θ1 ⍮ Ξ1.
  Hypothesis Hg2 : ⊢ᵍ Θ2 ⍮ Ξ2.

  (** A stored module keeps its telescope ([Paths.gc_loc_grow]). *)
  Lemma gc_loc_grows_tele : forall p T Φ, gc_loc Θ1 Ξ1 p = Some (T, Φ) -> exists Φ', gc_loc Θ2 Ξ2 p = Some (T, Φ').
  Proof. intros * H; destruct (gc_loc_grow _ _ _ _ Hg2 Hs _ _ _ H) as (Φ' & H' & _); eauto. Qed.

  (** A global module a member of which is found stays saturated. *)
  Lemma module_saturated_grows : forall p x args, child_found Θ1 Ξ1 (qname_app p (x :: nil)) ->
      module_saturated Θ1 Ξ1 p args -> module_saturated Θ2 Ξ2 p args.
  Proof.
    intros * Hc Hsat T Φ Hl2.
    destruct (child_found_parent_loc _ _ Hg1 _ _ Hc) as (T1 & Φ1 & Hl1).
    destruct (gc_loc_grows_tele _ _ _ Hl1) as (Φ' & Hl1').
    rewrite Hl2 in Hl1'; injection Hl1' as <- _; exact (Hsat _ _ Hl1).
  Qed.

  (** A function that is applied takes its next argument at a kind of the
      same case, evaluated or a proof: a type former, a record's or a
      constructor applied is of a declaration found, and a module member
      always takes an evaluated argument ([dmod_param_kind_evaluated]). *)
  Lemma arg_kind_grows : forall m n r, fast_eval_app Θ1 Ξ1 m n r ->
      (evaluated_kind (arg_kind Θ1 Ξ1 m) -> evaluated_kind (arg_kind Θ2 Ξ2 m)) /\
      (arg_kind Θ1 Ξ1 m = ak_propositional -> arg_kind Θ2 Ξ2 m = ak_propositional).
  Proof.
    intros * H; destruct m; try (split; intro; assumption).
    all: first
      [ (** a module member: always evaluated *)
        split; intro Hk; [ apply dmod_param_kind_evaluated |];
        exfalso; cbn [arg_kind] in Hk; pose proof (dmod_param_kind_evaluated Θ1 Ξ1 d) as He;
        rewrite Hk in He; inversion He
      | (** a type former or a constructor: of a declaration found *)
        inversion H; subst; cbn [arg_kind];
        match goal with
        | Hl : ind_lookup Θ1 Ξ1 _ = Some _ |- _ => rewrite Hl, (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hl)
        | Hl : record_lookup Θ1 Ξ1 _ = Some _ |- _ => rewrite Hl, (record_lookup_gc_sub _ _ _ _ _ _ Hs Hl)
        end;
        split; intro; assumption ].
  Qed.

  Theorem fast_eval_grow :
    (forall M ρ a, fast_eval_exp Θ1 Ξ1 M ρ a -> fast_eval_exp Θ2 Ξ2 M ρ a) /\
    (forall m n r, fast_eval_app Θ1 Ξ1 m n r -> fast_eval_app Θ2 Ξ2 m n r) /\
    (forall Ms ρ ms, fast_eval_exps Θ1 Ξ1 Ms ρ ms -> fast_eval_exps Θ2 Ξ2 Ms ρ ms) /\
    (forall m args r, fast_eval_apps Θ1 Ξ1 m args r -> fast_eval_apps Θ2 Ξ2 m args r) /\
    (forall H ρ h, fast_eval_modexp Θ1 Ξ1 H ρ h -> fast_eval_modexp Θ2 Ξ2 H ρ h) /\
    (forall Δ D ρ h, fast_eval_close Θ1 Ξ1 Δ D ρ h -> fast_eval_close Θ2 Ξ2 Δ D ρ h) /\
    (forall h n r, fast_eval_appm Θ1 Ξ1 h n r -> fast_eval_appm Θ2 Ξ2 h n r) /\
    (forall h ns r, fast_eval_appms Θ1 Ξ1 h ns r -> fast_eval_appms Θ2 Ξ2 h ns r) /\
    (forall h x r, fast_eval_sel Θ1 Ξ1 h x r -> fast_eval_sel Θ2 Ξ2 h x r) /\
    (forall h y r, fast_eval_selm Θ1 Ξ1 h y r -> fast_eval_selm Θ2 Ξ2 h y r) /\
    (forall h ch r, fast_eval_selc Θ1 Ξ1 h ch r -> fast_eval_selc Θ2 Ξ2 h ch r) /\
    (forall h ch r, fast_eval_selmc Θ1 Ξ1 h ch r -> fast_eval_selmc Θ2 Ξ2 h ch r) /\
    (forall ρ Φ ρ1, fast_eval_body_env Θ1 Ξ1 ρ Φ ρ1 -> fast_eval_body_env Θ2 Ξ2 ρ Φ ρ1) /\
    (forall ρ p ups Bks j m r, fast_eval_elim Θ1 Ξ1 ρ p ups Bks j m r -> fast_eval_elim Θ2 Ξ2 ρ p ups Bks j m r) /\
    (forall ρ p ups Bks oB gs vs r, fast_eval_ihs Θ1 Ξ1 ρ p ups Bks oB gs vs r -> fast_eval_ihs Θ2 Ξ2 ρ p ups Bks oB gs vs r) /\
    (forall ρ p ups Bks t v r, fast_eval_ih Θ1 Ξ1 ρ p ups Bks t v r -> fast_eval_ih Θ2 Ξ2 ρ p ups Bks t v r) /\
    (forall p ups j r, fast_eval_mref Θ1 Ξ1 p ups j r -> fast_eval_mref Θ2 Ξ2 p ups j r) /\
    (forall p ups ρ t a, fast_eval_shape_type Θ1 Ξ1 p ups ρ t a -> fast_eval_shape_type Θ2 Ξ2 p ups ρ t a) /\
    (forall p ups ρm As ρ t v a, fast_eval_ihty Θ1 Ξ1 p ups ρm As ρ t v a -> fast_eval_ihty Θ2 Ξ2 p ups ρm As ρ t v a) /\
    (forall f m r, fast_eval_proj Θ1 Ξ1 f m r -> fast_eval_proj Θ2 Ξ2 f m r) /\
    (forall m ρ fl rs, fast_eval_neutral_fields Θ1 Ξ1 m ρ fl rs -> fast_eval_neutral_fields Θ2 Ξ2 m ρ fl rs) /\
    (forall fl v ws, fast_eval_projs Θ1 Ξ1 fl v ws -> fast_eval_projs Θ2 Ξ2 fl v ws) /\
    (forall p ups ρm As ρ gs vs as', fast_eval_ihtys Θ1 Ξ1 p ups ρm As ρ gs vs as' -> fast_eval_ihtys Θ2 Ξ2 p ups ρm As ρ gs vs as') /\
    (forall rs Ms ρ ms, fast_eval_field_vals Θ1 Ξ1 rs Ms ρ ms -> fast_eval_field_vals Θ2 Ξ2 rs Ms ρ ms) /\
    (forall f Ms ρ r, fast_eval_app_args Θ1 Ξ1 f Ms ρ r -> fast_eval_app_args Θ2 Ξ2 f Ms ρ r).
  Proof.
    apply fast_eval_mut_ind; intros;
      (** the kind of an applied function's argument, and the saturation
          of a module a member of which is found *)
      repeat match goal with
        | H : evaluated_kind (arg_kind Θ1 Ξ1 ?m), Ha : fast_eval_app Θ1 Ξ1 ?m _ _ |- _ =>
            apply (proj1 (arg_kind_grows _ _ _ Ha)) in H
        | H : arg_kind Θ1 Ξ1 ?m = ak_propositional, Ha : fast_eval_app Θ1 Ξ1 ?m _ _ |- _ =>
            apply (proj2 (arg_kind_grows _ _ _ Ha)) in H
        | H : module_saturated Θ1 Ξ1 ?p ?args, Hc : gc_term Θ1 Ξ1 (qname_app ?p (?x :: nil)) = Some _ |- _ =>
            apply (module_saturated_grows _ _ _ (child_found_term _ _ _ _ Hc)) in H
        | H : module_saturated Θ1 Ξ1 ?p ?args, Hc : gc_resolve Θ1 Ξ1 (qname_app ?p (?x :: nil)) = Some _ |- _ =>
            apply (module_saturated_grows _ _ _ (child_found_resolve _ _ _ _ Hc)) in H
        | H : module_saturated Θ1 Ξ1 ?p ?args, Hc : ind_mlookup Θ1 Ξ1 (qname_app ?p (?x :: nil)) = Some _ |- _ =>
            apply (module_saturated_grows _ _ _ (child_found_ind _ _ _ _ Hc)) in H
        | H : module_saturated Θ1 Ξ1 ?p ?args, Hc : record_lookup Θ1 Ξ1 (qname_app ?p (?x :: nil)) = Some _ |- _ =>
            apply (module_saturated_grows _ _ _ (child_found_record _ _ _ _ Hc)) in H
        | H : gc_loc Θ1 Ξ1 ?p = Some (?T, _) |- fast_eval_sel _ _ _ _ _ =>
            let Φ' := fresh "Φ'" in destruct (gc_loc_grows_tele _ _ _ H) as (Φ' & ?); clear H
        end;
      try solve [ econstructor; eauto using ind_lookup_gc_sub, record_lookup_gc_sub, ind_mlookup_gc_sub, gc_sub_resolve, gc_sub_module, gc_term_grows ].
    (** The module of a member of a group, or a record type, as a term:
        still no definition, as it is still such a module *)
    - pose proof (ind_mlookup_gc_sub _ _ _ _ _ _ Hs e0) as e0'.
      eapply fast_eval_sel_global_ind; [ exact m | exact (ind_mlookup_resolve _ _ _ _ e0') | exact e0' | exact H ].
    - pose proof (record_lookup_gc_sub _ _ _ _ _ _ Hs e0) as e0'.
      eapply fast_eval_sel_global_record; [ exact m | exact (record_lookup_resolve _ _ _ _ e0') | exact e0' | exact H ].
    (** A submodule located in place: still located, perhaps grown *)
    - destruct (gc_loc_grows _ _ e) as (TΦ' & e'); eapply fast_eval_selm_global; exact e'.
  Qed.

  Corollary fast_eval_exp_grow : forall M ρ a, ⟦ M ⟧ᶠ Θ1 ⍮ Ξ1 ⍮ ρ ↘ a -> ⟦ M ⟧ᶠ Θ2 ⍮ Ξ2 ⍮ ρ ↘ a.
  Proof. exact (proj1 fast_eval_grow). Qed.

  (** ** Right Fast Values *)

  (** A declaration carried stays the one its group's name finds. *)
  Lemma decl_carried_ok_grows : forall p oD, decl_carried_ok Θ1 Ξ1 p oD -> decl_carried_ok Θ2 Ξ2 p oD.
  Proof. intros * H D E; exact (ind_lookup_gc_sub _ _ _ _ _ _ Hs (H D E)). Qed.

  Theorem fdomain_ok_grow :
    (forall d, fdomain_ok Θ1 Ξ1 d -> fdomain_ok Θ2 Ξ2 d) /\
    (forall m, fdomain_ne_ok Θ1 Ξ1 m -> fdomain_ne_ok Θ2 Ξ2 m) /\
    (forall n, fdomain_nf_ok Θ1 Ξ1 n -> fdomain_nf_ok Θ2 Ξ2 n) /\
    (forall h, fdmod_ok Θ1 Ξ1 h -> fdmod_ok Θ2 Ξ2 h) /\
    (forall e, fdentry_ok Θ1 Ξ1 e -> fdentry_ok Θ2 Ξ2 e) /\
    (forall t, fentry_type_ok Θ1 Ξ1 t -> fentry_type_ok Θ2 Ξ2 t).
  Proof.
    apply fdomain_ok_mut_ind; intros;
      repeat match goal with H : Forall_all _ _ _ _ _ |- _ => apply Forall_all_Forall in H end;
      econstructor; eauto using decl_carried_ok_grows, ind_lookup_gc_sub.
  Qed.
End Growth.
