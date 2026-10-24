(** * Record Types in the PER Model, Canonically

    The clause of [per_univ_elem_core] for a record type takes the
    relations of its fields as an argument.  Here they are fixed: the
    relation of a field, after the left values of the fields before it, is
    the head PER of its type there ([canon_fields_rel], on the diagonal),
    which the PER model determines.  [per_univ_elem_record_canon] builds the
    clause from the relatedness of the field types alone, and
    [record_rel_canon] states that every derivation of the clause relates
    the elements as the canonical relations do. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export PER Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  (** The type of the field [k] of [R], [⊤] if there is no such field. *)
  Definition nth_ftyp (R : record_decl) (k : nat) : typ :=
    match List.nth_error (record_fields R) k with Some (_, T) => T | None => a_True end.

  (** The relation of a field, after the values [vs] of the fields before
      it: the head PER of its type there, at the parameters [ns]. *)
  Definition canon_fields_rel (R : record_decl) (ns : list domain) : nat -> list domain -> relation domain :=
    fun k vs => per_head (nth_ftyp R k) (nth_ftyp R k) (env_args nil (ns ++ vs)) (env_args nil (ns ++ vs)).

  Lemma nth_ftyp_eq : forall R k f T, List.nth_error (record_fields R) k = Some (f, T) -> nth_ftyp R k = T.
  Proof. intros * H; unfold nth_ftyp; rewrite H; reflexivity. Qed.

  Section Canon.
    Variable (u : uidx) (p : qname) (R : record_decl) (ns ns' : list domain).
    Let fr := canon_fields_rel R ns.
    Hypothesis (Hl : record_lookup gc_deps gc_stack p = Some R)
      (Hnd : List.NoDup (List.map fst (record_fields R)))
      (Hn : List.length ns = List.length (record_params R)) (Hn' : List.length ns' = List.length (record_params R))
      (Hps : per_top_ps (List.rev (record_params R)) ns ns').

    (** The types of the fields at two related prefixes, at [ns] and at a
        second base [u2]: their values related. *)
    Definition fields_related (u2 : list domain) : Prop :=
      forall k f T vs vs', List.nth_error (record_fields R) k = Some (f, T) -> tele_prefix_rel fr k vs vs' ->
        exists a a', ⟦ T ⟧ env_args nil (ns ++ vs) ↘ a /\ ⟦ T ⟧ env_args nil (u2 ++ vs') ↘ a' /\ Dom a ≈ a' ∈ per_univ u.
    Hypothesis (Hf : fields_related ns').

    (** The evidence at a field, at the head PER. *)
    Lemma canon_fields_evals : fields_evals (per_univ_elem u) R ns ns' fr.
    Proof.
      intros k f T vs vs' Hk Hp; destruct (Hf _ _ _ _ _ Hk Hp) as (a & a' & Ea & Ea' & [R0 HR]).
      econstructor; [ exact Ea | exact Ea' |].
      unfold fr, canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ Hk); exact (per_head_diag Ea HR).
    Qed.

    Lemma canon_fields_per : fields_per R fr.
    Proof.
      intros k f T vs vs' Hk Hp; destruct (canon_fields_evals _ _ _ _ _ Hk Hp) as [a a' _ _ HR].
      eapply per_elem_PER; exact HR.
    Qed.

    (** Invariance, by induction on the position: the prefixes on the right
        are related to themselves, by the positions before. *)
    Lemma canon_fields_invariant_all : forall k, k <= List.length (record_fields R) ->
        (forall j vs vs', j < k -> tele_prefix_rel fr j vs vs' -> (fr j vs <~> fr j vs')).
    Proof.
      induction k as [| k IH]; intros Hk j vs vs' Hj Hp; [ lia |].
      destruct (Nat.lt_ge_cases j k) as [Hjk | Hjk]; [ apply IH; [ lia | exact Hjk | exact Hp ] |].
      assert (j = k) as -> by lia.
      destruct (nth_error_lt_some' (record_fields R) k ltac:(lia)) as [[f T] HT].
      assert (HP : forall j vs vs', j < k -> tele_prefix_rel fr j vs vs' -> PER (fr j vs))
        by (intros j0 ? ? Hj0 Hp0; exact (fields_per_lt R fr canon_fields_per j0 _ _ ltac:(lia) Hp0)).
      pose proof (tele_prefix_rel_refl_r k fr HP (IH ltac:(lia)) k vs vs' (le_n _) Hp) as Hp'.
      destruct (canon_fields_evals _ _ _ _ _ HT Hp) as [a a' Ea Ea' HR1].
      destruct (canon_fields_evals _ _ _ _ _ HT Hp') as [b b' Eb Eb' HR2].
      functional_eval_rewrite_clear.
      eapply per_univ_elem_left_irrel; [ exact HR1 | exact HR2 ].
    Qed.

    Lemma canon_fields_invariant : fields_inv R fr.
    Proof.
      intros k f T vs vs' Hk Hp; assert (Hkl : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
      exact (canon_fields_invariant_all _ (le_n _) k vs vs' Hkl Hp).
    Qed.

    (** The clause, at the canonical relations. *)
    Lemma per_univ_elem_record_canon :
        DF d_record p ns ≈ d_record p ns' ∈ per_univ_elem u ↘ record_rel R fr.
    Proof.
      basic_per_univ_elem_econstructor;
        [ exact Hl | exact Hnd | exact Hn | exact Hn' | exact Hps | exact canon_fields_per | exact canon_fields_evals
        | exact canon_fields_invariant | reflexivity ].
    Qed.
  End Canon.

  (** Every derivation of the clause relates the elements as the canonical
      relations do: its field relations are those of the field types along
      related prefixes. *)
  Lemma record_rel_canon : forall i p R ns ns' elem_rel,
      record_lookup gc_deps gc_stack p = Some R ->
      DF d_record p ns ≈ d_record p ns' ∈ per_univ_elem i ↘ elem_rel ->
      elem_rel <~> record_rel R (canon_fields_rel R ns).
  Proof.
    intros * Hl HR; basic_invert_per_univ_elem HR.
    match goal with Hl2 : record_lookup _ _ p = Some ?R2 |- _ => assert_fails constr_eq R2 R;
      rewrite Hl in Hl2; injection Hl2 as <- end.
    match goal with
    | HE : elem_rel <~> record_rel R ?fr, HfE : fields_evals _ R ns ns' ?fr |- _ =>
        assert (Hfr : forall k pa pb pc, k < List.length (record_fields R) -> tele_prefix_rel fr k pa pb ->
                  tele_prefix_rel (canon_fields_rel R ns) k pa pc -> (fr k pa <~> canon_fields_rel R ns k pa));
        [ intros k pa pb pc Hk Hp1 _;
          destruct (nth_error_lt_some' _ _ Hk) as [[f T] HT];
          destruct (HfE _ _ _ _ _ HT Hp1) as [a a' Ea Ea' Hper];
          unfold canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ HT);
          eapply per_univ_elem_right_irrel; [ exact Hper | exact (per_head_diag Ea Hper) ]
        | rewrite HE; intros v v'; split; apply record_rel_change; intros;
            [ eapply Hfr; eassumption | symmetry; eapply Hfr; eassumption ] ]
    end.
  Qed.
  (** The canonical relations at the two sides' parameters of a related
      pair of record types agree with the clause's along its related
      prefixes, so the prefixes on the diagonal of the right side's are on
      the diagonal of the left side's. *)
  Lemma record_canon_prefix_clause : forall i (Rel : relation domain -> domain -> domain -> Prop) R ns ns' fr,
      (forall Q x y, Rel Q x y -> DF x ≈ y ∈ per_univ_elem i ↘ Q) ->
      fields_per R fr -> fields_inv R fr -> fields_evals Rel R ns ns' fr ->
      forall k vs, k <= List.length (record_fields R) ->
      tele_prefix_rel (canon_fields_rel R ns') k vs vs ->
      tele_prefix_rel fr k vs vs /\ tele_prefix_rel (canon_fields_rel R ns) k vs vs.
  Proof.
    intros * HRel HfP HfI HfE.
    (** At related prefixes of the clause, the canonical relations at either
        side are the clause's. *)
    assert (Hag : forall k pa pb, k < List.length (record_fields R) -> tele_prefix_rel fr k pa pb ->
              (canon_fields_rel R ns k pa <~> fr k pa) /\ (canon_fields_rel R ns' k pb <~> fr k pa)).
    { intros k pa pb Hk Hp.
      destruct (nth_error_lt_some' _ _ Hk) as [[f T] HT].
      destruct (HfE _ _ _ _ _ HT Hp) as [a a' Ea Ea' Hper%HRel].
      unfold canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ HT); split;
        [ symmetry; eapply per_univ_elem_right_irrel; [ exact Hper | exact (per_head_diag Ea Hper) ]
        | pose proof (per_univ_sym _ _ _ _ Hper) as Hper';
          symmetry; eapply per_univ_elem_right_irrel; [ exact Hper' | exact (per_head_diag Ea' Hper') ] ]. }
    intros k vs Hk Hp.
    rewrite !tele_prefix_rel_full_iff in *.
    (** first onto the clause's relations, then onto the left side's *)
    assert (Hfr : tele_rel fr (List.repeat tt k) vs vs).
    { eapply tele_rel_map; [| exact Hp ].
      intros j pa pb x y Hj Hp1 Hp2 Hxy; rewrite List.repeat_length in Hj.
      pose proof (fields_prefix_refl_l R fr HfP HfI j pa pb ltac:(lia) Hp2) as Hpa.
      exact (proj1 (proj2 (Hag j pa pa ltac:(lia) Hpa) _ _) Hxy). }
    split; [ exact Hfr |].
    eapply tele_rel_map; [| exact Hfr ].
    intros j pa pb x y Hj Hp1 Hp2 Hxy; rewrite List.repeat_length in Hj.
    exact (proj2 (proj1 (Hag j pa pb ltac:(lia) Hp1) _ _) Hxy).
  Qed.

  (** On the diagonal of a clause, its related prefixes are the canonical
      relations' at the parameters. *)
  Lemma record_canon_prefix_iff_clause : forall i (Rel : relation domain -> domain -> domain -> Prop) R ns ns' fr,
      (forall Q x y, Rel Q x y -> DF x ≈ y ∈ per_univ_elem i ↘ Q) ->
      fields_evals Rel R ns ns' fr ->
      forall k pa pb, k <= List.length (record_fields R) ->
      (tele_prefix_rel (canon_fields_rel R ns) k pa pb <-> tele_prefix_rel fr k pa pb).
  Proof.
    intros * HRel HfE.
    assert (Hag : forall k pa pb, k < List.length (record_fields R) -> tele_prefix_rel fr k pa pb ->
              (canon_fields_rel R ns k pa <~> fr k pa)).
    { intros k pa pb Hk Hp.
      destruct (nth_error_lt_some' _ _ Hk) as [[f T] HT].
      destruct (HfE _ _ _ _ _ HT Hp) as [a a' Ea Ea' Hper%HRel].
      unfold canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ HT).
      symmetry; eapply per_univ_elem_right_irrel; [ exact Hper | exact (per_head_diag Ea Hper) ]. }
    intros k pa pb Hk; rewrite !tele_prefix_rel_full_iff; split; intros Hp.
    - eapply tele_rel_map; [| exact Hp ].
      intros j qa qb x y Hj _ Hp2 Hxy; rewrite List.repeat_length in Hj.
      exact (proj1 (Hag j qa qb ltac:(lia) Hp2 _ _) Hxy).
    - eapply tele_rel_map; [| exact Hp ].
      intros j qa qb x y Hj Hp1 _ Hxy; rewrite List.repeat_length in Hj.
      exact (proj2 (Hag j qa qb ltac:(lia) Hp1 _ _) Hxy).
  Qed.

  Lemma record_canon_prefix_move : forall i p R ns ns' elem_rel,
      record_lookup gc_deps gc_stack p = Some R ->
      DF d_record p ns ≈ d_record p ns' ∈ per_univ_elem i ↘ elem_rel ->
      forall k vs, k <= List.length (record_fields R) ->
      tele_prefix_rel (canon_fields_rel R ns') k vs vs -> tele_prefix_rel (canon_fields_rel R ns) k vs vs.
  Proof.
    intros * Hl HR; basic_invert_per_univ_elem HR.
    match goal with Hl2 : record_lookup _ _ p = Some ?R2 |- _ => assert_fails constr_eq R2 R;
      rewrite Hl in Hl2; injection Hl2 as <- end.
    intros k vs Hk Hp.
    match goal with
    | HfP : fields_per R ?fr, HfI : fields_inv R ?fr, HfE : fields_evals _ R ns ns' ?fr |- _ =>
        exact (proj2 (record_canon_prefix_clause _ _ R ns ns' fr (fun _ _ _ H => H) HfP HfI HfE k vs Hk Hp))
    end.
  Qed.

  (** What a related pair of record types gives, at the canonical
      relations: the conditions of the clause. *)
  #[warnings="-cannot-define-projection"]
  Record record_canon_facts (i : uidx) (R : record_decl) (ns ns' : list domain) (elem_rel : relation domain) : Prop :=
    mk_record_canon_facts
    { (** The field names are distinct *)
      record_canon_facts_nodup : List.NoDup (List.map fst (record_fields R))
      (** The left parameters, one per parameter *)
    ; record_canon_facts_length : List.length ns = List.length (record_params R)
      (** The right parameters, one per parameter *)
    ; record_canon_facts_length_right : List.length ns' = List.length (record_params R)
      (** The parameters read back alike *)
    ; record_canon_facts_top : per_top_ps (List.rev (record_params R)) ns ns'
      (** The canonical relations of the fields are PERs *)
    ; record_canon_facts_per : fields_per R (canon_fields_rel R ns)
      (** and invariant along related prefixes *)
    ; record_canon_facts_inv : fields_inv R (canon_fields_rel R ns)
      (** The fields' types at related prefixes are related, at them *)
    ; record_canon_facts_evals : fields_evals (per_univ_elem i) R ns ns' (canon_fields_rel R ns)
      (** The element relation is the canonical record relation *)
    ; record_canon_facts_elem : elem_rel <~> record_rel R (canon_fields_rel R ns) }.

  Lemma per_univ_elem_record_facts : forall i p R ns ns' elem_rel,
      record_lookup gc_deps gc_stack p = Some R ->
      DF d_record p ns ≈ d_record p ns' ∈ per_univ_elem i ↘ elem_rel ->
      record_canon_facts i R ns ns' elem_rel.
  Proof.
    intros * Hl HR.
    pose proof (record_rel_canon _ _ _ _ _ _ Hl HR) as HE.
    basic_invert_per_univ_elem HR.
    match goal with Hl2 : record_lookup _ _ p = Some ?R2 |- _ => assert_fails constr_eq R2 R;
      rewrite Hl in Hl2; injection Hl2 as <- end.
    match goal with
    | HfE : fields_evals _ R ns ns' ?fr |- _ =>
        assert (HcE : fields_evals (per_univ_elem i) R ns ns' (canon_fields_rel R ns));
        [ intros k f T vs vs' Hk Hp;
          assert (Hkl : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence);
          pose proof (proj1 (record_canon_prefix_iff_clause i _ R ns ns' fr (fun _ _ _ H => H) HfE k vs vs' ltac:(lia)) Hp) as Hp';
          destruct (HfE _ _ _ _ _ Hk Hp') as [a a' Ea Ea' Hper];
          refine (mk_rel_mod_eval a a' Ea Ea' (per_univ_elem_resp_iff Hper _));
          unfold canon_fields_rel; rewrite (nth_ftyp_eq _ _ _ _ Hk);
          eapply per_univ_elem_right_irrel; [ exact Hper | exact (per_head_diag Ea Hper) ]
        |]
    end.
    assert (Hrel : fields_related i R ns ns').
    { intros k f T vs vs' Hk Hp; destruct (HcE _ _ _ _ _ Hk Hp) as [a a' Ea Ea' Hper].
      exists a, a'; split; [ exact Ea | split; [ exact Ea' | eexists; exact Hper ] ]. }
    apply mk_record_canon_facts; try assumption;
      [ exact (canon_fields_per _ _ _ _ Hrel) | apply (canon_fields_invariant i R ns ns'); assumption ].
  Qed.

  (** ** The Projections of a Neutral and the Readback of Fields *)

  (** Each neutral projection is the projection of the neutral at the
      field's type, at the parameters and the projections before it. *)
  Lemma eval_nflds_nth : forall ns m fl pre rs, eval_nflds gc_deps gc_stack ns m fl pre rs ->
      forall j g T r, List.nth_error fl j = Some (g, T) -> List.nth_error rs j = Some r ->
      exists a, r = ⇑ a (d_proj g m) /\ ⟦ T ⟧ env_args nil (ns ++ pre ++ List.firstn j rs) ↘ a.
  Proof.
    induction 1 as [| T ns pre a m fl g rs Ea E IH]; intros [| j] g' T' r Hj Hr; cbn in Hj, Hr; try discriminate.
    - injection Hj as <- <-; injection Hr as <-; exists a; split; [ reflexivity |].
      cbn [List.firstn]; rewrite List.app_nil_r; exact Ea.
    - destruct (IH _ _ _ _ Hj Hr) as (a' & -> & Ea'); exists a'; split; [ reflexivity |].
      cbn [List.firstn]; rewrite <- List.app_assoc in Ea'; exact Ea'.
  Qed.

  (** The projections of a neutral of a record type: each the neutral
      projection at the field's type, at the parameters and the projections
      before it. *)
  Lemma record_projs_neut_nth : forall p R ns m vs, record_lookup gc_deps gc_stack p = Some R ->
      List.NoDup (List.map fst (record_fields R)) ->
      record_projs R (⇑ (d_record p ns) m) vs ->
      forall k f T r, List.nth_error (record_fields R) k = Some (f, T) -> List.nth_error vs k = Some r ->
      exists a, r = ⇑ a (d_proj f m) /\ ⟦ T ⟧ env_args nil (ns ++ List.firstn k vs) ↘ a.
  Proof.
    intros * Hl Hnd Hvs k f T r Hk Hr.
    pose proof (Forall2_nth_both _ _ _ _ _ _ Hvs Hk Hr) as Hp; cbn [fst] in Hp.
    inversion Hp as [| ? R0 ? k0 ? ? rs ? Hl0 Hi E Hrk]; subst.
    rewrite Hl in Hl0; injection Hl0 as <-.
    rewrite (field_index_nth_nodup _ _ _ _ Hnd Hk) in Hi; injection Hi as <-.
    assert (Hkf : List.nth_error (List.firstn (S k) (record_fields R)) k = Some (f, T))
      by (rewrite List.nth_error_firstn; destruct (Nat.ltb_spec k (S k)); [ exact Hk | lia ]).
    destruct (eval_nflds_nth _ _ _ _ _ E _ _ _ _ Hkf Hrk) as (a & -> & Ea); exists a; split; [ reflexivity |].
    cbn [List.app] in Ea.
    replace (List.firstn k vs) with (List.firstn k rs); [ exact Ea |].
    assert (Hlk : k < List.length (record_fields R)) by (apply List.nth_error_Some; congruence).
    pose proof (eval_nflds_length _ _ _ _ _ E) as Hrl; rewrite List.length_firstn in Hrl.
    pose proof (List.Forall2_length Hvs) as Hvl.
    apply List.nth_error_ext; intros j.
    rewrite !List.nth_error_firstn; destruct (Nat.ltb_spec j k) as [Hjk |]; [| reflexivity ].
    destruct (nth_error_lt_some' (record_fields R) j ltac:(lia)) as [[g U] Hj].
    destruct (nth_error_lt_some' vs j ltac:(lia)) as [v Hv].
    destruct (nth_error_lt_some' rs j ltac:(lia)) as [w Hw].
    rewrite Hv, Hw; f_equal.
    pose proof (Forall2_nth_both _ _ _ _ _ _ Hvs Hj Hv) as Hpv; cbn [fst] in Hpv.
    assert (Hpw : eval_proj gc_deps gc_stack g (⇑ (d_record p ns) m) w).
    { econstructor; [ exact Hl | exact (field_index_nth_nodup _ _ _ _ Hnd Hj) | |].
      - pose proof (eval_nflds_firstn _ _ _ _ _ E (S j)) as Ej.
        rewrite List.firstn_firstn, Nat.min_l in Ej by lia; exact Ej.
      - rewrite List.nth_error_firstn; destruct (Nat.ltb_spec j (S j)); [ exact Hw | lia ]. }
    exact (functional_eval_proj _ _ _ _ Hpw Hpv).
  Qed.

  (** The readback of the fields of a record value, one by one: the
      readback of each projection at the field's type, at the parameters
      and the projections before it. *)
  Lemma read_fields_nth : forall s ρ fl v Fs, Rflds v at fl in gc_deps ⍮ gc_stack ⍮ ρ ⍮ s ↘ Fs ->
      forall ns pre vs, ρ = env_args nil (ns ++ pre) ->
      List.Forall2 (fun fT r => eval_proj gc_deps gc_stack (fst fT) v r) fl vs ->
      List.length (List.map nf_to_exp Fs) = List.length fl /\
      forall j g T r, List.nth_error fl j = Some (g, T) -> List.nth_error vs j = Some r ->
        exists t F, ⟦ T ⟧ env_args nil (ns ++ pre ++ List.firstn j vs) ↘ t /\ Rnf ⇓ t r in gc_deps ⍮ gc_stack ⍮ s ↘ F /\
          List.nth_error (List.map nf_to_exp Fs) j = Some (nf_to_exp F).
  Proof.
    induction 1 as [| f v r T ρ t s F fl Fs Hp Et HF HFs IH]; intros ns pre vs -> Hvs.
    - inversion Hvs; subst; split; [ reflexivity |]; intros [| j]; discriminate.
    - inversion Hvs as [| ? r' ? vs' Hr' Hvs']; subst; cbn [fst] in Hr'.
      pose proof (functional_eval_proj _ _ _ _ Hp Hr') as <-.
      destruct (IH ns (pre ++ r :: nil) vs' ltac:(rewrite List.app_assoc, env_args_snoc; reflexivity) Hvs') as [Hl IHn].
      split; [ cbn; congruence |].
      intros [| j] g U r0 Hj Hr0; cbn in Hj, Hr0.
      + injection Hj as <- <-; injection Hr0 as <-; exists t, F; split; [| split; [ exact HF | reflexivity ] ].
        cbn [List.firstn]; rewrite List.app_nil_r; exact Et.
      + destruct (IHn _ _ _ _ Hj Hr0) as (t' & F' & Et' & HF' & HnF); exists t', F'; split; [| split; [ exact HF' | exact HnF ] ].
        cbn [List.firstn]; rewrite <- List.app_assoc in Et'; exact Et'.
  Qed.
End Fixed_GCtx.
