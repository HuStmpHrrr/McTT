(** * The Eliminator in the PER Model

    The eliminator of a group of inductive types relates related elements
    at a family of relations, given that its motives are related at
    related arguments and its branches at related arguments and recursive
    results.  This is the semantic content of the eliminator's rule; the
    cases of the fundamental theorem instantiate it.

    The elements are related at their own parameters ([ind_rel]): a
    recursive argument's index is admissible at the element's own prefix
    ([admissible_index_at]).  A stuck eliminator reads back its motives and branches
    under fresh variables of the telescopes of the group's own members at
    the uniform parameters the eliminator carries ([elim_ups_ok]; model
    P), admissible at the fresh variables ([adm_fresh]); a neutral needs
    no admissibility.  The fresh variables at two admissible bases are related
    through those at the type's base [ups], and the indices of recursive
    arguments made of them are admissible by the recursive-index field of
    [adm_fresh] and the type-level admissibility [Hcd].  A view's stuck
    eliminator is read as its container's (E1′): an argument the view
    nests through has the eliminator's recursive result, at a member of
    lower rank. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Export PER Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER ViewCoherence ViewCount.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  Lemma cons_lookup_nodup_in : forall cs c gs, List.NoDup (List.map fst cs) -> In (c, gs) cs -> cons_lookup cs c = Some gs.
  Proof.
    induction cs as [| [c' gs'] cs IH]; cbn; intros c gs Hnd H; [ destruct H |].
    inversion Hnd as [| ? ? Hni Hnd']; subst.
    destruct (String.eqb_spec c c') as [-> | Hne].
    - destruct H as [H | H]; [ injection H as ->; reflexivity |].
      exfalso; apply Hni; apply List.in_map_iff; exists (c', gs); auto.
    - destruct H as [H | H]; [ injection H as -> ->; contradiction | eauto ].
  Qed.

  Lemma brs_lookup_nodup_in : forall (Bs : list (String.string * nat * exp)) c n B,
      List.NoDup (List.map (fun b => fst (fst b)) Bs) -> In (c, n, B) Bs -> brs_lookup Bs c = Some (n, B).
  Proof.
    induction Bs as [| [[c' n'] B'] Bs IH]; cbn; intros c n B Hnd H; [ destruct H |].
    inversion Hnd as [| ? ? Hni Hnd']; subst.
    destruct (String.eqb_spec c c') as [-> | Hne].
    - destruct H as [H | H]; [ injection H as -> ->; reflexivity |].
      exfalso; apply Hni; apply List.in_map_iff; exists (c', n, B); auto.
    - destruct H as [H | H]; [ injection H as -> -> ->; contradiction | eauto ].
  Qed.

  Lemma per_bot_app : forall m m' n n', Dom m ≈ m' ∈ per_bot -> Dom n ≈ n' ∈ per_top -> Dom m $ᵈ n ≈ m' $ᵈ n' ∈ per_bot.
  Proof.
    intros * Hm Hn s; destruct (Hm s) as [M M' HM HM' HE]; destruct (Hn s) as [N N' HN HN' HE'].
    apply (mk_neutral_reads_alike _ _ _ (M $ⁿ N) (M' $ⁿ N')); [ constructor; assumption | constructor; assumption | cbn; congruence ].
  Qed.

  (** A declared member of a group is itself at the group's uniform
      parameters. *)
  Lemma mref_decl_inv : forall p D j Mj pm ups r, ind_lookup gc_deps gc_stack p = Some D ->
      ind_member D j = Some Mj -> im_head Mj = mh_decl pm ->
      ⟦mref j of p ups ⟧ gc_deps ⍮ gc_stack ↘ r -> r = (p, j, ups).
  Proof.
    intros * Hl HM Hh H; inversion H; subst; [ reflexivity |].
    match goal with H1 : ind_lookup _ _ p = Some _, H2 : ind_member _ j = Some _, H3 : im_head _ = mh_view _ _ _ _ |- _ =>
      rewrite Hl in H1; injection H1 as <-; rewrite HM in H2; injection H2 as <-; rewrite Hh in H3; discriminate end.
  Qed.

  Lemma eval_exps_length : forall Ms ρ vs, ⟦ Ms ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ vs -> List.length vs = List.length Ms.
  Proof. induction Ms as [| M Ms IH]; intros ρ vs H; inversion H; subst; cbn; [ reflexivity | f_equal; eauto ]. Qed.

  (** A view member of a group is the container's member at the view's
      arguments. *)
  Lemma mref_view_inv : forall pq Dq i Mi qv kv Is vm Y r, ind_lookup gc_deps gc_stack pq = Some Dq ->
      ind_member Dq i = Some Mi -> im_head Mi = mh_view qv kv Is vm ->
      ⟦mref i of pq Y ⟧ gc_deps ⍮ gc_stack ↘ r -> exists py, r = (qv, kv, py) /\ ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env Dq Y ↘ py.
  Proof.
    intros * Hq HM Hh H; inversion H; subst.
    - match goal with H1 : ind_lookup _ _ pq = Some _, H2 : ind_member _ i = Some _, H3 : im_head _ = mh_decl _ |- _ =>
        rewrite Hq in H1; injection H1 as <-; rewrite HM in H2; injection H2 as <-; rewrite Hh in H3; discriminate end.
    - match goal with H1 : ind_lookup _ _ pq = Some _, H2 : ind_member _ i = Some _, H3 : im_head _ = mh_view _ _ _ _ |- _ =>
        rewrite Hq in H1; injection H1 as <-; rewrite HM in H2; injection H2 as <-; rewrite Hh in H3; injection H3 as <- <- <- <- end.
      eexists; split; [ reflexivity | eassumption ].
  Qed.

  (** The codomain of the type of an argument of a function shape, at an
      argument, is the type of the rest of the shape. *)
  Lemma fam_cod_shfam_inv : forall p ups ρ B t x a tf tx,
      ⟦ fam_cod ⟧ nil ↦ d_shfam p ups ρ B t ⦂ tf ↦ x ⦂ tx ↘ a ->
      ⟦shty t of p ups ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↦ x ⦂ entry_type_closure B ρ ↘ a.
  Proof.
    intros * H; unfold fam_cod in H; inversion H; subst;
      match goal with H1 : ⟦ #1 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H1; subst end;
      try (match goal with Hr : arg_kind _ _ _ = ak_propositional |- _ => cbn in Hr; discriminate Hr end).
    all: match goal with H0 : ⟦ #0 ⟧ _ ⍮ _ ⍮ _ ↘ _ |- _ => inversion H0; subst end.
    all: match goal with Ha : $| _ & _ | _ ⍮ _ ↘ _ |- _ => cbn in Ha; inversion Ha; subst; assumption end.
  Qed.

  (** Applications that read back alike have arguments that do. *)
  Lemma per_bot_app_inv : forall m m' n n', Dom m $ᵈ n ≈ m' $ᵈ n' ∈ per_bot -> Dom n ≈ n' ∈ per_top.
  Proof.
    intros * H s; destruct (H s) as [M M' H1 H2 HE].
    inversion H1; subst; inversion H2; subst.
    cbn in HE; injection HE as _ HE.
    eapply mk_normal_reads_alike; eassumption.
  Qed.

  Lemma nth_blocks_motives : forall Bks j b, List.nth_error Bks j = Some b ->
      List.nth j (blocks_motives Bks) a_prop = eb_motive b.
  Proof.
    intros * H; unfold blocks_motives.
    apply List.nth_error_nth; rewrite List.nth_error_map, H; reflexivity.
  Qed.

  Lemma cargs_correspond_length : forall vm gs' gs, cargs_correspond vm gs' gs -> List.length gs' = List.length gs.
  Proof.
    induction gs' as [| [rA' A' | t'] gs' IH]; intros [| [rA A | t] gs] H; cbn in H |- *; try contradiction; try reflexivity.
    - f_equal; exact (IH _ (proj2 H)).
    - f_equal; exact (IH _ (proj2 H)).
    - f_equal; exact (IH _ (proj2 (proj2 H))).
  Qed.

  Lemma tele_rel_len : forall {X Y : Type} tr (T : list X) (T' : list Y) a b, List.length T = List.length T' ->
      tele_rel tr T a b -> tele_rel tr T' a b.
  Proof. intros * HT [Hl Hr]; split; [ congruence | exact Hr ]. Qed.

  Lemma cons_lookup_names : forall cs c, In c (List.map fst cs) -> exists gs, cons_lookup cs c = Some gs.
  Proof.
    induction cs as [| [c' gs'] cs IH]; cbn; intros c H; [ destruct H |].
    destruct (String.eqb_spec c c') as [-> | Hne]; [ eauto |].
    destruct H as [H | H]; [ congruence | exact (IH _ H) ].
  Qed.

  (** The kinds of a constructor's arguments in the group read ([gs']) and
      in the group of the eliminator ([gs]): non-recursive in both,
      recursive in both, or nested through (non-recursive in the group
      read only). *)
  Fixpoint cargs_same_kinds (gs' gs : list carg) : Prop :=
    match gs', gs with
    | nil, nil => True
    | ca_arg _ _ :: gs1', ca_arg _ _ :: gs1 => cargs_same_kinds gs1' gs1
    | ca_rec _ :: gs1', ca_rec _ :: gs1 => cargs_same_kinds gs1' gs1
    | ca_arg _ _ :: gs1', ca_rec _ :: gs1 => cargs_same_kinds gs1' gs1
    | _, _ => False
    end.

  Lemma cargs_same_kinds_refl : forall gs, cargs_same_kinds gs gs.
  Proof. induction gs as [| [rA A | t] gs IH]; cbn; auto. Qed.

  Lemma cargs_same_kinds_of_correspond : forall vm gs' gs, cargs_correspond vm gs' gs -> cargs_same_kinds gs' gs.
  Proof.
    induction gs' as [| [rA' A' | t'] gs' IH]; intros [| [rA A | t] gs] H; cbn in H |- *; try contradiction;
      [ exact I | exact (IH _ (proj2 H)) | exact (IH _ (proj2 H)) | exact (IH _ (proj2 (proj2 H))) ].
  Qed.

  Lemma cargs_same_kinds_length : forall gs' gs, cargs_same_kinds gs' gs -> List.length gs' = List.length gs.
  Proof.
    induction gs' as [| [rA' A' | t'] gs' IH]; intros [| [rA A | t] gs] H; cbn in H |- *; try contradiction; auto.
  Qed.

  (** The environment of a constructor's components up to a shape's
      domains, one domain value more, at the domain's type. *)
  Lemma components_env_shape_snoc : forall D u (Mm : imember) gs1 t0 (ns ws ys : list domain) B c,
      List.length ns = List.length (im_nparams Mm) -> List.length ws = List.length (cargs_nonrec gs1) ->
      List.nth_error (ptyp_doms t0) (List.length ys) = Some B ->
      components_env D u (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns ++ ws ++ ys ++ c :: nil)
      = components_env D u (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns ++ ws ++ ys)
          ↦ c ⦂ entry_type_closure B
            (components_env D u (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns ++ ws ++ ys)).
  Proof.
    intros * Hn Hw HB.
    replace (ns ++ ws ++ ys ++ c :: nil) with ((ns ++ ws ++ ys) ++ c :: nil) by (rewrite <- !List.app_assoc; reflexivity).
    apply components_env_snoc_nth with (κ := ak_relevant).
    rewrite !List.length_app, List.nth_error_app2 by (rewrite List.length_rev; lia).
    rewrite List.length_rev, List.nth_error_app2
      by (rewrite length_cargs_nonrec_tele; lia).
    rewrite length_cargs_nonrec_tele; unfold shape_doms_tele.
    replace (List.length ns + (List.length ws + List.length ys) - List.length (im_nparams Mm) - List.length (cargs_nonrec gs1))
      with (List.length ys) by lia.
    rewrite List.nth_error_map, HB; reflexivity.
  Qed.

  (** A term reads back at a type that evaluates to a type it reads back
      at. *)
  Lemma entry_readable_at_evaluated : forall v t a, eval_entry_type gc_deps gc_stack t a ->
      entry_readable (de_term v (entry_type_value a)) -> entry_readable (de_term v t).
  Proof.
    intros * Ht H s; destruct (H s) as [b Hb]; inversion Hb; subst.
    match goal with He : eval_entry_type _ _ (entry_type_value _) _ |- _ => inversion He; subst end.
    eexists; eapply read_entry_term; eassumption.
  Qed.

  (** What a term entry's readback at a length is made of: its type's
      value, read back as a type, and the term read back at it. *)
  Lemma entry_readable_term_at : forall v t s, entry_readable (de_term v t) ->
      exists a A W, eval_entry_type gc_deps gc_stack t a /\ Rtyp a in gc_deps ⍮ gc_stack ⍮ s ↘ A /\
        Rnf ⇓ a v in gc_deps ⍮ gc_stack ⍮ s ↘ W.
  Proof.
    intros * H; destruct (H s) as [b Hb]; inversion Hb; subst.
    do 3 eexists; split; [ eassumption | split; eassumption ].
  Qed.

  (** A list of pairs is its two projections combined. *)
  Lemma combine_map_fst_snd : forall {A B : Type} (l : list (A * B)), List.combine (List.map fst l) (List.map snd l) = l.
  Proof. induction l as [| [a b] l IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

  (** The values at a telescope read back at the types the telescope
      gives them, when each does in the environment of the values before
      it. *)
  Lemma tele_entries_readable : forall vs ρ T,
      (forall i e v, List.nth_error T i = Some e -> List.nth_error vs i = Some v ->
         exists A, centry_type e = Some A /\
           entry_readable (de_term v (entry_type_closure A (env_tele ρ T (List.firstn i vs))))) ->
      List.length vs <= List.length T ->
      List.Forall2 (fun v t => entry_readable (de_term v t)) vs (List.map snd (tele_entries ρ T vs)).
  Proof.
    induction vs as [| v vs IH]; intros ρ [| e T] H Hl; cbn in Hl |- *; try lia; constructor.
    - destruct (H 0 e v eq_refl eq_refl) as (A & HA & Hr); cbn [tele_head_type]; rewrite HA; exact Hr.
    - apply IH; [| lia ].
      intros i e0 v0 He Hv; exact (H (S i) e0 v0 He Hv).
  Qed.

  (** The values of a motive's entries: the non-uniform parameters and the
      scrutinee. *)
  Lemma motive_entries_values : forall D Mj ua ns a m, List.map fst (motive_entries D Mj ua ns a m) = ns ++ m :: nil.
  Proof. intros; unfold motive_entries; rewrite List.map_app, tele_entries_values; reflexivity. Qed.

  (** A motive's environment, as the values combined with their types. *)
  Lemma motive_entries_combine : forall D Mj ρ ua ns a m,
      env_extend_typed ρ (List.combine (ns ++ m :: nil) (List.map snd (motive_entries D Mj ua ns a m)))
      = env_extend_typed ρ (motive_entries D Mj ua ns a m).
  Proof.
    intros; rewrite <- (motive_entries_values D Mj ua ns a m) at 1; rewrite combine_map_fst_snd; reflexivity.
  Qed.

  (** A telescope's entries and one more, as the values combined with
      their types. *)
  Lemma combine_tele_entries_snoc : forall ρ T vs v t,
      List.combine (vs ++ v :: nil) (List.map snd (tele_entries ρ T vs ++ (v, t) :: nil)) = tele_entries ρ T vs ++ (v, t) :: nil.
  Proof.
    intros; replace (vs ++ v :: nil) with (List.map fst (tele_entries ρ T vs ++ (v, t) :: nil))
      by (rewrite List.map_app, tele_entries_values; reflexivity).
    apply combine_map_fst_snd.
  Qed.

  (** A member's non-uniform parameters, related at [nr] to those at the
      type's base [ups], read back at the types of the telescope over any
      base [ua] admissible beside it ([adm_nparam_types]). *)
  Lemma nparams_entries_readable_at_admissible_base : forall D ups nr ar dr ua j Mj ns ns',
      grp_tele_ass D -> adm_uparams D ups nr ar dr ua -> ind_member D j = Some Mj ->
      tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns' ->
      List.Forall2 (fun v t => entry_readable (de_term v t)) ns'
        (List.map snd (tele_entries (decl_env D ua) (List.rev (im_nparams Mj)) ns')).
  Proof.
    intros * Hass Ha HM Hn.
    pose proof (proj1 (tele_rel_iff _ _ _ _) Hn) as (Ll & Lr & Hr).
    assert (Hta : tele_ass (List.rev (im_nparams Mj)))
      by (apply List.Forall_rev; exact (grp_tele_ass_nparams _ Hass _ _ HM)).
    apply tele_entries_readable; [| lia ].
    intros i e v He Hv.
    destruct (proj1 (List.Forall_forall _ _) Hta e (List.nth_error_In _ _ He)) as (κ & A & ->).
    assert (Hi : i < List.length ns) by (rewrite Ll; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some' ns i Hi) as [x Hx].
    pose proof (tele_prefix_rel_of_full _ _ _ _ i Hn ltac:(lia)) as Hp.
    pose proof (adm_nparam_types _ _ _ _ _ _ Ha j Mj i κ A _ _ HM He Hp) as Hc.
    exists A; split; [ reflexivity | exact (component_elem_readable_at_admissible_base _ _ _ _ _ _ Hc (Hr _ _ _ Hx Hv)) ].
  Qed.

  (** ** The Members the Leaf Paths End In *)

  (** The members the leaf paths of a shape [t] of the group [D] end in. *)
  Definition shape_mems (D : ind_decl) (t : ptyp) : list nat := List.map leaf_mem (shape_leaves (rview_leaves D) 0 t).

  (** Those of the recursive arguments among [gs], in order. *)
  Fixpoint cargs_mems (D : ind_decl) (gs : list carg) : list nat :=
    match gs with
    | nil => nil
    | ca_arg _ _ :: gs' => cargs_mems D gs'
    | ca_rec t :: gs' => shape_mems D t ++ cargs_mems D gs'
    end.

  Lemma map_leaf_mem_shape : forall tbl t m m',
      List.map leaf_mem (shape_leaves tbl m t) = List.map leaf_mem (shape_leaves tbl m' t).
  Proof.
    intros tbl; induction t as [j Ps | B t IH]; intros m m'; cbn [shape_leaves].
    - destruct (tbl j) as [ls |]; [| reflexivity ].
      rewrite !List.map_map; apply List.map_ext; intros l; rewrite !leaf_mem_wk; reflexivity.
    - rewrite !List.map_map; cbn [leaf_mem]; exact (IH (S m) (S m')).
  Qed.

  Lemma length_shape_mems : forall D t, List.length (shape_mems D t) = List.length (shape_leaves (rview_leaves D) 0 t).
  Proof. intros; unfold shape_mems; apply List.length_map. Qed.

  Lemma shape_mems_pi : forall D B t, shape_mems D (pt_pi B t) = shape_mems D t.
  Proof. intros; unfold shape_mems; cbn [shape_leaves]; rewrite List.map_map; cbn [leaf_mem]; apply map_leaf_mem_shape. Qed.

  Lemma shape_mems_self : forall D j Mj Ps, ind_member D j = Some Mj -> im_is_rview Mj = false ->
      shape_mems D (pt_self j Ps) = j :: nil.
  Proof. intros * HM Hr; unfold shape_mems; rewrite (length_shape_leaves_self _ _ _ _ 0 HM Hr); reflexivity. Qed.

  Lemma fields_mems : forall D fl gs ns, List.length fl = List.length gs ->
      List.map leaf_mem (fields_leaves (rview_leaves D) ns (List.combine fl gs)) = cargs_mems D gs.
  Proof.
    intros D; induction fl as [| f fl IH]; intros [| [rA A | t] gs] ns Hl; cbn in Hl |- *; try discriminate; [ reflexivity | |].
    - apply IH; lia.
    - rewrite List.map_app, List.map_map; cbn [leaf_mem]; rewrite IH by lia; f_equal.
      unfold shape_mems; apply map_leaf_mem_shape.
  Qed.

  (** At a record view with a coherent table: its fields'. *)
  Lemma shape_mems_rview : forall D j Mj qr Is fl c gs Ps, leaves_coherent D ->
      ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
      List.length fl = List.length gs -> shape_mems D (pt_self j Ps) = cargs_mems D gs.
  Proof.
    intros * Hc HM Hh Hcs Hl; unfold shape_mems; cbn [shape_leaves]; rewrite (Hc _ _ _ _ _ _ _ HM Hh Hcs).
    rewrite List.map_map; erewrite List.map_ext by (intros; apply leaf_mem_wk).
    exact (fields_mems D fl gs nil Hl).
  Qed.

  (** Flags of the leaf paths, [true] at a path whose recursive result is a
      fresh variable, [false] at one whose result is the eliminator's: [P]
      holds of the member each [false] path ends in. *)
  Inductive leaf_flags_ok (P : nat -> Prop) : list bool -> list nat -> Prop :=
  (** No path *)
  | leaf_flags_ok_nil : leaf_flags_ok P nil nil
  (** A fresh variable's path *)
  | leaf_flags_ok_fresh : forall bs m ms, leaf_flags_ok P bs ms -> leaf_flags_ok P (true :: bs) (m :: ms)
  (** An eliminator's path, at a member [P] holds of *)
  | leaf_flags_ok_nest : forall bs m ms, P m -> leaf_flags_ok P bs ms -> leaf_flags_ok P (false :: bs) (m :: ms).

  Lemma leaf_flags_ok_length : forall P bs ms, leaf_flags_ok P bs ms -> List.length bs = List.length ms.
  Proof. induction 1; cbn; congruence. Qed.

  Lemma leaf_flags_ok_app : forall P ms1 ms2 bs, leaf_flags_ok P bs (ms1 ++ ms2) ->
      exists bs1 bs2, bs = bs1 ++ bs2 /\ leaf_flags_ok P bs1 ms1 /\ leaf_flags_ok P bs2 ms2.
  Proof.
    intros P; induction ms1 as [| m ms1 IH]; intros ms2 bs H; cbn in H.
    - exists nil, bs; split; [ reflexivity | split; [ constructor | exact H ] ].
    - inversion H as [| bs0 ? ? H0 | bs0 ? ? Hm H0]; subst;
        destruct (IH _ _ H0) as (bs1 & bs2 & -> & H1 & H2);
        [ exists (true :: bs1), bs2 | exists (false :: bs1), bs2 ]; split; auto; split; auto; constructor; auto.
  Qed.

  (** Recursive results along leaf paths, flagged [bs], from two sources on
      each side: a fresh neutral of the types [as1] and [as2] where the
      flag is [true], two neutrals that read back alike; the eliminator's
      results [rs1] and [rs2] where it is [false]. *)
  Inductive leaf_results : list bool -> list domain -> list domain -> list domain -> list domain ->
      list domain -> list domain -> Prop :=
  (** No path *)
  | leaf_results_nil : leaf_results nil nil nil nil nil nil nil
  (** A fresh neutral on each side, a neutral proof at a proposition *)
  | leaf_results_fresh : forall bs a a' as1 as2 r r' rs1 rs2 e e' out out', Dom e ≈ e' ∈ per_bot ->
      leaf_results bs as1 as2 rs1 rs2 out out' ->
      leaf_results (true :: bs) (a :: as1) (a' :: as2) (r :: rs1) (r' :: rs2) (⇑ a e :: out) (⇑ a' e' :: out')
  (** The eliminator's result on each side *)
  | leaf_results_nest : forall bs a a' as1 as2 r r' rs1 rs2 out out',
      leaf_results bs as1 as2 rs1 rs2 out out' ->
      leaf_results (false :: bs) (a :: as1) (a' :: as2) (r :: rs1) (r' :: rs2) (r :: out) (r' :: out').

  Lemma leaf_results_app_inv : forall bs1 bs2 A1 A2 A1' A2' R1 R2 R1' R2' out out',
      leaf_results (bs1 ++ bs2) (A1 ++ A2) (A1' ++ A2') (R1 ++ R2) (R1' ++ R2') out out' ->
      List.length A1 = List.length bs1 -> List.length A1' = List.length bs1 ->
      List.length R1 = List.length bs1 -> List.length R1' = List.length bs1 ->
      exists o1 o2 o1' o2', out = o1 ++ o2 /\ out' = o1' ++ o2' /\
        leaf_results bs1 A1 A1' R1 R1' o1 o1' /\ leaf_results bs2 A2 A2' R2 R2' o2 o2'.
  Proof.
    induction bs1 as [| b bs1 IH]; intros * H L1 L2 L3 L4.
    - destruct A1, A1', R1, R1'; cbn in L1, L2, L3, L4; try discriminate.
      exists nil, out, nil, out'; split; [ reflexivity | split; [ reflexivity | split; [ constructor | exact H ] ] ].
    - destruct A1 as [| a A1], A1' as [| a' A1'], R1 as [| r R1], R1' as [| r' R1']; cbn in L1, L2, L3, L4; try discriminate.
      inversion H as [| ? ? ? ? ? ? ? ? ? e e' o o' He H0 | ? ? ? ? ? ? ? ? ? o o' H0]; subst;
        destruct (IH _ _ _ _ _ _ _ _ _ _ _ H0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (o1 & o2 & o1' & o2' & -> & -> & H1 & H2).
      + exists (⇑ a e :: o1), o2, (⇑ a' e' :: o1'), o2'; split; [ reflexivity | split; [ reflexivity | split; [ constructor; assumption | exact H2 ] ] ].
      + exists (r :: o1), o2, (r' :: o1'), o2'; split; [ reflexivity | split; [ reflexivity | split; [ constructor; assumption | exact H2 ] ] ].
  Qed.

  Lemma leaf_results_length : forall bs as1 as2 rs1 rs2 out out', leaf_results bs as1 as2 rs1 rs2 out out' ->
      List.length out = List.length bs /\ List.length out' = List.length bs.
  Proof. induction 1; cbn; [ auto | destruct IHleaf_results; auto | destruct IHleaf_results; auto ]. Qed.

  Lemma map_nth_seq_all : forall {A : Type} (l : list A) d, List.map (fun i => List.nth i l d) (List.seq 0 (List.length l)) = l.
  Proof.
    intros A l d.
    enough (H : forall pre, List.map (fun i => List.nth i (pre ++ l) d) (List.seq (List.length pre) (List.length l)) = l)
      by exact (H nil).
    induction l as [| x l IH]; intros pre; cbn [List.length List.seq List.map]; [ reflexivity |].
    rewrite List.app_nth2, Nat.sub_diag by lia; cbn [List.nth]; f_equal.
    specialize (IH (pre ++ x :: nil)); rewrite <- List.app_assoc, List.length_app in IH; cbn in IH.
    rewrite Nat.add_1_r in IH; exact IH.
  Qed.

  (** A list related pointwise to the values of [f] at its positions. *)
  Lemma forall2_map_seq : forall {A B : Type} (P : A -> B -> Prop) (l : list A) (f : nat -> B) k,
      (forall i x, List.nth_error l i = Some x -> P x (f (k + i))) -> List.Forall2 P l (List.map f (List.seq k (List.length l))).
  Proof.
    intros A B P l f; induction l as [| x l IH]; intros k H; cbn; constructor.
    - specialize (H 0 x eq_refl); rewrite Nat.add_0_r in H; exact H.
    - apply IH; intros i y Hy; replace (S k + i) with (k + S i) by lia; exact (H (S i) y Hy).
  Qed.

  (** The partner of an element of a list related pointwise to another. *)
  Lemma forall2_nth_left : forall {A B : Type} (P : A -> B -> Prop) l l' i x, List.Forall2 P l l' ->
      List.nth_error l i = Some x -> exists y, List.nth_error l' i = Some y /\ P x y.
  Proof.
    intros A B P l l' i x H; revert i; induction H as [| a b l l' Hab H IH]; intros [| i] Hi; cbn in Hi |- *; try discriminate.
    - injection Hi as <-; exists b; auto.
    - exact (IH i Hi).
  Qed.

  (** A neutral: what evaluation builds at a neutral, a neutral proof at a
      proposition. *)
  Definition is_neut (v : domain) : Prop := exists a e, v = ⇑ a e.

  Lemma is_neut_app : forall f c r, $| f & c | gc_deps ⍮ gc_stack ↘ r -> is_neut f -> is_neut r.
  Proof. intros * E (a & e & ->); inversion E; subst; eexists _, _; reflexivity. Qed.

  Lemma is_neut_neutral_fields : forall m ρ fl rs, eval_neutral_fields gc_deps gc_stack m ρ fl rs -> List.Forall is_neut rs.
  Proof. induction 1; constructor; [ eexists _, _; reflexivity | assumption ]. Qed.

  Lemma is_neut_projs : forall fl v ws, ⟦projs fl of v ⟧ gc_deps ⍮ gc_stack ↘ ws -> is_neut v -> List.Forall is_neut ws.
  Proof.
    induction 1 as [| f v w fl ws Ep Eps IH]; intros Hv; constructor; [| exact (IH Hv) ].
    destruct Hv as (a & e & ->); inversion Ep; subst.
    match goal with Hn : eval_neutral_fields _ _ _ _ _ ?rs, Hk : List.nth_error ?rs _ = Some w |- _ =>
      exact (proj1 (List.Forall_forall _ _) (is_neut_neutral_fields _ _ _ _ Hn) _ (List.nth_error_In _ _ Hk)) end.
  Qed.

  (** Flags by a test of the paths: [P] of the members of those it fails. *)
  Lemma leaf_flags_of_in : forall (P : nat -> Prop) (f : leaf_path -> bool) ls,
      (forall l, In l ls -> f l = false -> P (leaf_mem l)) -> leaf_flags_ok P (List.map f ls) (List.map leaf_mem ls).
  Proof.
    intros P f; induction ls as [| l ls IH]; intros H; cbn; [ constructor |].
    assert (IH' : leaf_flags_ok P (List.map f ls) (List.map leaf_mem ls))
      by (apply IH; intros l0 Hl0; apply H; right; exact Hl0).
    destruct (f l) eqn:Hf; [ apply leaf_flags_ok_fresh; exact IH' |].
    apply leaf_flags_ok_nest; [ apply H; [ left; reflexivity | exact Hf ] | exact IH' ].
  Qed.

  (** All the eliminator's: the results are its. *)
  Lemma leaf_results_all_nest : forall (ls : list leaf_path) as1 as2 rs1 rs2,
      List.length as1 = List.length ls -> List.length as2 = List.length ls ->
      List.length rs1 = List.length ls -> List.length rs2 = List.length ls ->
      leaf_results (List.map (fun _ => false) ls) as1 as2 rs1 rs2 rs1 rs2.
  Proof.
    induction ls as [| l ls IH]; intros [| a as1] [| a' as2] [| r rs1] [| r' rs2] L1 L2 L3 L4; cbn in *; try discriminate;
      constructor; apply IH; lia.
  Qed.

  (** Fresh variables along the paths flagged [true], from [s] on, and the
      results along all paths from them and the eliminator's. *)
  Lemma fresh_wrap_results : forall bs as1 as2 rs1 rs2 s,
      List.length as1 = List.length bs -> List.length as2 = List.length bs ->
      List.length rs1 = List.length bs -> List.length rs2 = List.length bs ->
      exists ihs1 ihs2 out out', fresh_leaf_vars bs as1 s ihs1 /\ fresh_leaf_vars bs as2 s ihs2 /\
        List.length ihs1 = List.length ihs2 /\
        (forall X, wrap_leaf_vals bs rs1 (ihs1 ++ X) X out) /\ (forall Y, wrap_leaf_vals bs rs2 (ihs2 ++ Y) Y out') /\
        leaf_results bs as1 as2 rs1 rs2 out out'.
  Proof.
    induction bs as [| b bs IH]; intros [| a as1] [| a' as2] [| r rs1] [| r' rs2] s L1 L2 L3 L4; cbn in *; try discriminate.
    - exists nil, nil, nil, nil; repeat split; constructor.
    - destruct b.
      + destruct (IH as1 as2 rs1 rs2 (S s) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as (ihs1 & ihs2 & out & out' & F1 & F2 & Li & W1 & W2 & Hr).
        exists (⇑! a s :: ihs1), (⇑! a' s :: ihs2), (⇑! a s :: out), (⇑! a' s :: out').
        split; [ constructor; exact F1 | split; [ constructor; exact F2 | split; [ cbn; congruence | split; [| split ] ] ] ].
        * intros X; cbn; constructor; apply W1.
        * intros Y; cbn; constructor; apply W2.
        * constructor; [ exact var_per_bot | exact Hr ].
      + destruct (IH as1 as2 rs1 rs2 s ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as (ihs1 & ihs2 & out & out' & F1 & F2 & Li & W1 & W2 & Hr).
        exists ihs1, ihs2, (r :: out), (r' :: out').
        split; [ constructor; exact F1 | split; [ constructor; exact F2 | split; [ exact Li | split; [| split ] ] ] ].
        * intros X; constructor; apply W1.
        * intros Y; constructor; apply W2.
        * constructor; exact Hr.
  Qed.

  (** ** Fresh Variables of a Group *)
  Section ElimGroup.
    #[local] Set Default Proof Using "All".
    Variable (p : qname) (D : ind_decl) (ups : list domain).
    Variable (nr : nat -> nat -> list domain -> relation domain).
    Variable (ar : nat -> list domain -> String.string -> nat -> list domain -> relation domain).
    Variable (dr : nat -> list domain -> list centry -> exp -> relation domain).
    Hypothesis (Hl : ind_lookup gc_deps gc_stack p = Some D) (Hass : grp_tele_ass D).
    Hypothesis (HnP : nparams_per D nr) (HnI : nparams_inv D nr).
    Hypothesis (HaP : args_per D nr ar) (HaI : args_inv D nr ar).
    Hypothesis (HdP : doms_per D nr ar dr) (HdI : doms_inv D nr ar dr).
    (** The type's uniform parameters, admissible beside themselves at every
        related prefix. *)
    Hypothesis (Hcd : adm_uparams D ups nr ar dr ups).
    (** The record views' table is coherent. *)
    Let Hrs := grp_tele_ass_record_struct _ Hass.
    Let Hlc : leaves_coherent D := leaves_coherent_of_order D (rview_struct_order _ _ _ Hrs).

    (** Every leaf path of a shape of the group is its own ([leaf_in]). *)
    Lemma own_leaves : forall t m l, (exists M, ind_member D (ptyp_mem t) = Some M) ->
        In l (shape_leaves (rview_leaves D) m t) -> leaf_in D t l = true.
    Proof.
      apply (leaf_in_own D Hlc).
      - intros * HM Hh.
        destruct (rview_struct_record _ _ _ Hrs _ _ _ _ _ HM Hh) as [R HR].
        destruct (rview_struct_con _ _ _ Hrs _ _ _ _ _ HM Hh) as (gs & Hcs & Hlen).
        split; [ exact (rview_record_nodup _ _ _ _ _ _ HR) | exists rview_con, gs; split; [ exact Hcs | lia ] ].
      - intros * HM Hh Hcs.
        destruct (grp_tele_ass_params_length _ Hass _ _ _ _ HM ltac:(rewrite Hcs; left; reflexivity) gs1 t gs2 eq_refl) as (M & HM' & _).
        exists M; exact HM'.
    Qed.

    (** Read as its own container, every leaf path of a constructor's
        argument is the group's: as many as its branch binds. *)
    Lemma cargs_container_count_own : forall gs, cargs_params_length D gs -> cargs_container_count D D gs gs = cargs_nrec D gs.
    Proof. exact (cargs_container_count_own_of_ass D Hass). Qed.

    (** Read as its own container, a constructor of the group nests
        through nothing. *)
    Lemma cargs_nest_ok_own : forall rk r k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        cargs_nest_ok D D rk r gs gs.
    Proof.
      intros * HM Hc.
      pose proof (grp_tele_ass_params_length _ Hass _ _ _ _ HM (cons_lookup_in _ _ _ Hc)) as Hpl.
      enough (H : forall gs2 gs1, gs = gs1 ++ gs2 -> cargs_nest_ok D D rk r gs2 gs2) by exact (H gs nil eq_refl).
      induction gs2 as [| [rA A | t] gs2 IH]; intros gs1 Heq; cbn; [ exact I | |].
      - apply (IH (gs1 ++ ca_arg rA A :: nil)); rewrite Heq, <- List.app_assoc; reflexivity.
      - split; [| apply (IH (gs1 ++ ca_rec t :: nil)); rewrite Heq, <- List.app_assoc; reflexivity ].
        intros l Hin Hn; exfalso.
        destruct (Hpl gs1 t gs2 Heq) as (M & HM' & _).
        rewrite (own_leaves t 0 l (ex_intro _ M HM') Hin) in Hn; discriminate Hn.
    Qed.

    (** A leaf path of a shape ends in a member of rank at most the
        shape's: a record view's rank is above its fields'. *)
    Lemma leaf_mem_rank : forall rk, view_rank_ok gc_deps gc_stack D rk ->
        forall t m l, In l (shape_leaves (rview_leaves D) m t) -> rk (leaf_mem l) <= rk (ptyp_mem t).
    Proof.
      intros rk Hrk.
      enough (H : forall n l, leaf_size l < n -> forall t m, In l (shape_leaves (rview_leaves D) m t) ->
                    rk (leaf_mem l) <= rk (ptyp_mem t))
        by (intros t m l Hin; exact (H (S (leaf_size l)) l ltac:(lia) t m Hin)).
      induction n as [| n IH]; intros l Hs t m Hin; [ lia |].
      destruct t as [j Ps | B t1]; cbn [ptyp_mem]; cbn [shape_leaves] in Hin.
      - destruct (rview_leaves D j) as [ls |] eqn:Hr; [| destruct Hin as [<- | []]; reflexivity ].
        apply List.in_map_iff in Hin as (l0 & <- & Hl0).
        rewrite leaf_size_wk in Hs; rewrite leaf_mem_wk.
        destruct (ind_member D j) as [M |] eqn:HM; [| rewrite (rview_leaves_none _ _ HM) in Hr; discriminate Hr ].
        destruct (im_is_rview M) eqn:Hm; [| rewrite (rview_leaves_not_rview _ _ _ HM Hm) in Hr; discriminate Hr ].
        unfold im_is_rview in Hm; destruct (im_head M) as [| | qr Is fl] eqn:Hh; try discriminate Hm.
        destruct (rview_struct_con _ _ _ Hrs _ _ _ _ _ HM Hh) as (gs & Hcs & Hlen).
        rewrite (Hlc _ _ _ _ _ _ _ HM Hh Hcs) in Hr; injection Hr as <-.
        destruct (fields_leaves_in _ _ _ _ Hl0) as (fs1 & f & t1 & fs2 & l1 & Hfs & -> & Hl1).
        cbn [leaf_mem leaf_size] in Hs |- *.
        assert (Hgs : gs = List.map snd fs1 ++ ca_rec t1 :: List.map snd fs2)
          by (rewrite <- (combine_snd_eq fl gs ltac:(lia)), Hfs, List.map_app; reflexivity).
        pose proof (view_rank_ok_rview _ _ _ _ Hrk _ _ _ _ _ _ _ _ _ _ HM Hh ltac:(rewrite Hcs; left; reflexivity) Hgs) as Hlt.
        pose proof (IH l1 ltac:(lia) t1 _ Hl1); lia.
      - apply List.in_map_iff in Hin as (l1 & <- & Hl1); cbn [leaf_mem leaf_size] in Hs |- *.
        exact (IH l1 ltac:(lia) t1 _ Hl1).
    Qed.

    (** *** The Ends of Shapes

        A neutral's type at the end of a shape: a member's type of the
        group, its uniform parameters admissible for the member. *)
    #[warnings="-cannot-define-projection"]
    Record end_adm (j : nat) (hd : qname) (k : nat) (py : list domain) : Prop := mk_end_adm
      { (** The member the shape ends in *)
        end_adm_Mj : imember
        (** It is the group's [j]-th *)
      ; end_adm_member : ind_member D j = Some end_adm_Mj
        (** It is the declared member [k] of the group at [hd] *)
      ; end_adm_ref : im_ref p j end_adm_Mj = (hd, k)
        (** [py] has as many entries as its own uniform parameters *)
      ; end_adm_len : List.length py = im_unu D end_adm_Mj
        (** It is not a record view *)
      ; end_adm_rv : im_is_rview end_adm_Mj = false }.

    Lemma mref_at_end_adm : forall X, List.length X = ind_nu D ->
        forall j hd k py, mref_at p X j hd k py -> end_adm j hd k py.
    Proof.
      intros X LX j hd k py Hm; inversion Hm as [p0 D0 j0 Mj pm X0 Hl0 HMj Hh | p0 D0 j0 Mj qc kc Is vm X0 cups Hl0 HMj Hh E]; subst.
      - rewrite Hl in Hl0; injection Hl0 as <-.
        exists Mj; [ exact HMj | unfold im_ref; rewrite Hh; reflexivity | unfold im_unu; rewrite Hh; exact LX
                   | unfold im_is_rview; rewrite Hh; reflexivity ].
      - rewrite Hl in Hl0; injection Hl0 as <-.
        exists Mj; [ exact HMj | unfold im_ref; rewrite Hh; reflexivity
                   | unfold im_unu; rewrite Hh; exact (eval_exps_length _ _ _ E) | unfold im_is_rview; rewrite Hh; reflexivity ].
    Qed.

    (** The type of an argument of a shape after related domains, at a base
        whose fresh variables are related to those at [ups]: it is defined. *)
    (** The type of the member [j] at the uniform parameters [X] is
        defined: at a member with a block, its declared member's at the
        uniform parameters (a declared member's always, a view's when its
        instance evaluates at [X]); at a record view, the record at its
        instance, when the instance evaluates at [X]. *)
    Definition end_ok (X : list domain) (j : nat) : Prop :=
      forall Mj, ind_member D j = Some Mj ->
        (im_is_rview Mj = false -> exists r, ⟦mref j of p X ⟧ gc_deps ⍮ gc_stack ↘ r) /\
        (forall qr Is fl, im_head Mj = mh_record qr Is fl -> exists cups, ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D X ↘ cups).

    Lemma shape_type_exists : forall ua m Mm c gs1 t0 gs2 nsu ns wsu ws,
        ind_member D m = Some Mm -> ind_con Mm c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        end_ok ua (ptyp_mem t0) ->
        (forall ys ys', tele_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) (ptyp_doms t0) ys ys' ->
           rel_evals (ptyp_ps t0) (components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (nsu ++ wsu ++ ys)) (components_env D ua (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns ++ ws ++ ys'))
             (nparams_tele_rel D nr (ptyp_mem t0))) ->
        (forall j B ys ys', List.nth_error (ptyp_doms t0) j = Some B ->
           tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) j ys ys' ->
           rel_dom_apps B (components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (nsu ++ wsu ++ ys)) (components_env D ua (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns ++ ws ++ ys'))
             (dr m (nsu ++ wsu ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t0)) B)) ->
        forall k ysu ys, k <= List.length (ptyp_doms t0) ->
          tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) k ysu ys ->
          exists a, ⟦shty ptyp_skip k t0 of p ua ⟧ gc_deps ⍮ gc_stack ⍮ components_env D ua (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns ++ ws ++ ys) ↘ a.
    Proof.
      intros * HM Hc Hend HR HD k ysu ys Hk Hy.
      destruct (Nat.eq_dec k (List.length (ptyp_doms t0))) as [-> | Hne].
      - rewrite ptyp_skip_end.
        assert (Hyf : tele_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) (ptyp_doms t0) ysu ys)
          by (destruct Hy as [Hyl Hya]; split; [ exact Hyl | exact Hya ]).
        destruct (HR _ _ Hyf) as [bs bs' _ E' Rb].
        destruct (nparams_tele_rel_member p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ Rb) as (Mj & HMj & _).
        destruct (Hend _ HMj) as [Hm Hr].
        destruct (im_is_rview Mj) eqn:Hrv.
        + unfold im_is_rview in Hrv; destruct (im_head Mj) as [| | qr Is fl] eqn:Hh; try discriminate Hrv.
          destruct (Hr _ _ _ eq_refl) as [cups Ec].
          eexists; eapply eval_shape_type_rview; [ exact Hl | exact HMj | exact Hh | exact Ec ].
        + destruct (Hm eq_refl) as [[[pc km] pre] Em].
          eexists; econstructor; [ exact E' | exact Em ].
      - destruct (ptyp_skip_lt k t0 ltac:(lia)) as (B & HB & Hs); rewrite Hs.
        destruct (HD _ _ _ _ HB Hy) as [b b' _ Eb' _].
        eexists; econstructor; exact Eb'.
    Qed.

    (** A neutral of the type of an argument of a shape, at two bases
        admissible at the fresh variables, after fresh prefixes [ns1 ++ ws1]
        and [ns2 ++ ws2] related to the ones at [ups] ([nsu ++ wsu]) and
        related domains [ys1] and [ys2]: related by the shape, each side at
        its own base.  At the end of the shape, the index is admissible at
        the element's own prefix ([admissible_index_at]): through the index at [ups]'s
        fresh prefix, by the recursive-index field of the fresh
        admissibility ([HR1], [HR2]), and from there to [ups] at the
        element's prefix by [Hcd]. *)
    Lemma shape_neut : forall ua1 ua2 m Mm c gs1 t0 gs2 nsu ns1 ns2 wsu ws1 ws2,
        adm_fresh p D ups nr ar dr ua1 -> adm_fresh p D ups nr ar dr ua2 ->
        List.length ua1 = ind_nu D -> List.length ua2 = ind_nu D ->
        ind_member D m = Some Mm -> ind_con Mm c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        end_ok ua1 (ptyp_mem t0) -> end_ok ua2 (ptyp_mem t0) ->
        (** At a record view, neutrals of the record at the instance at the
            two bases are related by the record clause *)
        (forall Mj qr Is fl cups1 cups2 e e', ind_member D (ptyp_mem t0) = Some Mj -> im_head Mj = mh_record qr Is fl ->
           ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ua1 ↘ cups1 -> ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ua2 ↘ cups2 ->
           Dom e ≈ e' ∈ per_bot ->
           ind_rel p D (admissible_index_at D ups nr) nr ar dr (ptyp_mem t0) ua1 ua2 nil nil (⇑ (d_record qr cups1) e) (⇑ (d_record qr cups2) e')) ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) nsu ns1 -> tele_rel (nr m) (List.rev (im_nparams Mm)) nsu ns2 ->
        tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu ws1 ->
        tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu ws2 ->
        (forall ys ys', tele_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) (ptyp_doms t0) ys ys' ->
           rel_evals (ptyp_ps t0) (components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (nsu ++ wsu ++ ys)) (components_env D ua1 (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns1 ++ ws1 ++ ys'))
             (nparams_tele_rel D nr (ptyp_mem t0))) ->
        (forall ys ys', tele_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) (ptyp_doms t0) ys ys' ->
           rel_evals (ptyp_ps t0) (components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (nsu ++ wsu ++ ys)) (components_env D ua2 (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns2 ++ ws2 ++ ys'))
             (nparams_tele_rel D nr (ptyp_mem t0))) ->
        (forall j B ys ys', List.nth_error (ptyp_doms t0) j = Some B ->
           tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) j ys ys' ->
           rel_dom_apps B (components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (nsu ++ wsu ++ ys)) (components_env D ua1 (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns1 ++ ws1 ++ ys'))
             (dr m (nsu ++ wsu ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t0)) B)) ->
        (forall j B ys ys', List.nth_error (ptyp_doms t0) j = Some B ->
           tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) j ys ys' ->
           rel_dom_apps B (components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (nsu ++ wsu ++ ys)) (components_env D ua2 (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns2 ++ ws2 ++ ys'))
             (dr m (nsu ++ wsu ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t0)) B)) ->
        forall n k ysu ys1 ys2 a1 a2 e e', k + n = List.length (ptyp_doms t0) ->
          tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) k ysu ys1 ->
          tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) k ysu ys2 ->
          ⟦shty ptyp_skip k t0 of p ua1 ⟧ gc_deps ⍮ gc_stack ⍮ components_env D ua1 (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns1 ++ ws1 ++ ys1) ↘ a1 ->
          ⟦shty ptyp_skip k t0 of p ua2 ⟧ gc_deps ⍮ gc_stack ⍮ components_env D ua2 (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns2 ++ ws2 ++ ys2) ↘ a2 ->
          Dom e ≈ e' ∈ per_bot ->
          rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr m ua1 ua2
            (ns1 ++ ws1 ++ ys1) (ns2 ++ ws2 ++ ys2)
            (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t0)) (ptyp_skip k t0) (⇑ a1 e) (⇑ a2 e').
    Proof.
      intros ua1 ua2 m Mm c gs1 t0 gs2 nsu ns1 ns2 wsu ws1 ws2 Ha1 Ha2 L1 L2 HM Hc Hme1 Hme2 Hrn
        Hn1 Hn2 Hw1 Hw2 HR1 HR2 HD1 HD2.
      pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
      pose proof (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as ttrans.
      pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl.
      pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl_r.
      pose proof (nparams_tele_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as ntsym.
      pose proof (nparams_tele_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as nttrans.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (trefl _ _ HM _ _ Hn1) as Huu.
      pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM nsu c _ Huu Hc _ _ _ HK Hw1)
        as Hwuu.
      (** A side's prefix seen from that side: its relation to [ups]'s, in
          the other direction. *)
      assert (Hside : forall nsi wsi ysi k, tele_rel (nr m) (List.rev (im_nparams Mm)) nsu nsi ->
                 tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu wsi ->
                 k <= List.length (ptyp_doms t0) ->
                 forall ysu, tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) k ysu ysi ->
                 tele_rel (nr m) (List.rev (im_nparams Mm)) nsi nsu /\
                 tele_prefix_rel (ar m nsi c) (List.length (cargs_nonrec gs1)) wsi wsu /\
                 tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsi wsi t0) k ysi ysu).
      { intros nsi wsi ysi k Hni Hwi Hk ysu Hyi.
        pose proof (tsym _ _ HM _ _ Hni) as Hin.
        assert (Hwi' : tele_prefix_rel (ar m nsi c) (List.length (cargs_nonrec gs1)) wsi wsu).
        { eapply (args_prefix_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM); [ exact Hni | exact Hc | exact HK |].
          eapply (args_prefix_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM); [ exact Huu | exact Hc | exact HK | exact Hwi ]. }
        split; [ exact Hin | split; [ exact Hwi' |] ].
        eapply (doms_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM); [ exact Hni | exact Hc | reflexivity | exact Hwi | exact Hk |].
        eapply (doms_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM nsu c _ gs1 t0 gs2 wsu Huu Hc eq_refl Hwuu);
          [ exact Hk | exact Hyi ]. }
      induction n as [| n IH]; intros k ysu ys1 ys2 a1 a2 e e' Hkn Hy1 Hy2 E1 E2 He.
      - destruct (ptyp_skip k t0) as [j Ps | B t] eqn:Hs.
        + (** The end of the shape. *)
          destruct (ptyp_skip_self _ _ _ _ Hs) as (Hkd & Hj & HPs).
          inversion E1; subst.
          2: { (** A record view: neutrals of the record at the instance,
                   related by its record clause. *)
               match goal with H1 : ind_lookup _ _ p = Some ?D1, H2 : ind_member ?D1 _ = Some ?M1,
                               H3 : im_head ?M1 = mh_record _ _ _, H4 : ⟦ _ ⟧* _ ⍮ _ ⍮ decl_env _ ua1 ↘ _ |- _ =>
                 rewrite Hl in H1; injection H1 as <-; rename H2 into HMj; rename H3 into Hh; rename H4 into Ec1 end.
               inversion E2; subst.
               { exfalso; match goal with Hm : ⟦mref _ of _ ua2 ⟧ _ ⍮ _ ↘ _ |- _ =>
                   destruct (mref_at_end_adm ua2 L2 _ _ _ _ Hm) as [Mj' HMj' _ _ Hrv'] end.
                 rewrite HMj in HMj'; injection HMj' as <-; exact (not_rview_record _ _ _ _ Hrv' Hh). }
               match goal with H1 : ind_lookup _ _ p = Some ?D1, H2 : ind_member ?D1 _ = Some ?M1,
                               H3 : im_head ?M1 = mh_record _ _ _, H4 : ⟦ _ ⟧* _ ⍮ _ ⍮ decl_env _ ua2 ↘ _ |- _ =>
                 rewrite Hl in H1; injection H1 as <-; rewrite HMj in H2; injection H2 as <-; rewrite Hh in H3;
                 injection H3 as <- <- <-; rename H4 into Ec2 end.
               destruct (grp_tele_ass_params_length _ Hass _ _ _ _ HM (cons_lookup_in _ _ _ Hc) gs1 t0 gs2 eq_refl) as (Mj' & HMj' & HlPs).
               rewrite HMj in HMj'; injection HMj' as <-.
               pose proof (rview_struct_nparams _ _ _ Hrs _ _ _ _ _ HMj Hh) as Hnp.
               assert (HP0 : ptyp_ps t0 = nil) by (unfold im_nn in HlPs; rewrite Hnp in HlPs; destruct (ptyp_ps t0); [ reflexivity | discriminate HlPs ]).
               rewrite HP0 in *.
               assert (Hok : forall pre Ts, admissible_index_at D ups nr (ptyp_mem t0) pre Ts nil nil)
                 by (intros; exists nil; [ constructor | unfold nparams_tele_rel; rewrite HMj, Hnp; split; reflexivity + exact I ]).
               eapply rec_arg_self; [ constructor | constructor | exact (Hok _ _) | exact (Hok _ _) |].
               exact (Hrn _ _ _ _ _ _ e e' HMj Hh Ec1 Ec2 He). }
          match goal with H0 : ⟦ _ ⟧* _ ⍮ _ ⍮ components_env D ua1 _ _ ↘ _ |- _ => rename H0 into Ebs1 end.
          match goal with Hm : ⟦mref _ of _ ua1 ⟧ _ ⍮ _ ↘ _ |- _ => rename Hm into Em1 end.
          inversion E2; subst.
          2: { exfalso; destruct (mref_at_end_adm ua1 L1 _ _ _ _ Em1) as [Mj0 HMj0 _ _ Hrv0].
               match goal with H1 : ind_lookup _ _ p = Some ?D1, H2 : ind_member ?D1 _ = Some ?M1, H3 : im_head ?M1 = mh_record _ _ _ |- _ =>
                 rewrite Hl in H1; injection H1 as <-; rewrite HMj0 in H2; injection H2 as <-;
                 exact (not_rview_record _ _ _ _ Hrv0 H3) end. }
          match goal with H0 : ⟦ _ ⟧* _ ⍮ _ ⍮ components_env D ua2 _ _ ↘ _ |- _ => rename H0 into Ebs2 end.
          match goal with Hm : ⟦mref _ of _ ua2 ⟧ _ ⍮ _ ↘ _ |- _ => rename Hm into Em2 end.
          destruct (mref_at_end_adm ua1 L1 _ _ _ _ Em1) as [Mj HMj Href1 Hlen1 Hrvj].
          destruct (mref_at_end_adm ua2 L2 _ _ _ _ Em2) as [Mj' HMj' Href2 Hlen2 _].
          rewrite HMj in HMj'; injection HMj' as <-; rewrite Href1 in Href2; injection Href2 as <- <-.
          assert (Hyf1 : tele_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) (ptyp_doms t0) ysu ys1)
            by (destruct Hy1 as [Hyl Hya]; split; [ lia | exact Hya ]).
          assert (Hyf2 : tele_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) (ptyp_doms t0) ysu ys2)
            by (destruct Hy2 as [Hyl Hya]; split; [ lia | exact Hya ]).
          destruct (HR1 _ _ Hyf1) as [b0 b1 F0 F1 R1].
          destruct (HR2 _ _ Hyf2) as [b0' b2 F0' F2 R2].
          pose proof (functional_eval_exps' _ _ _ _ F0 F0') as <-.
          pose proof (functional_eval_exps' _ _ _ _ F1 Ebs1) as <-.
          pose proof (functional_eval_exps' _ _ _ _ F2 Ebs2) as <-.
          (** Each index admissible at its element's own prefix. *)
          assert (Hokr : forall nsi wsi ysi bsi, tele_rel (nr m) (List.rev (im_nparams Mm)) nsu nsi ->
                     tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu wsi ->
                     tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) k ysu ysi ->
                     nparams_tele_rel D nr (ptyp_mem t0) b0 bsi ->
                     admissible_index_at D ups nr (ptyp_mem t0) (nsi ++ wsi ++ ysi)
                       (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ptyp_ps t0) bsi).
          { intros nsi wsi ysi bsi Hni Hwi Hyi Rb.
            destruct (Hside nsi wsi ysi k Hni Hwi ltac:(lia) ysu Hyi) as (Hin & Hwi' & Hyi').
            assert (Hyif : tele_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsi wsi t0) (ptyp_doms t0) ysi ysu)
              by (destruct Hyi' as [Hyl Hya]; split; [ lia | exact Hya ]).
            destruct (adm_rec_params _ _ _ _ _ _ Hcd m Mm nsi nsu c _ gs1 t0 gs2 wsi wsu ysi ysu HM Hin Hc eq_refl Hwi' Hyif)
              as [i1 i0 G1 G0 Ri].
            pose proof (functional_eval_exps' _ _ _ _ G0 F0) as ->.
            exists i1; [ exact G1 | exact (nttrans _ _ _ _ Ri Rb) ]. }
          pose proof (nttrans _ _ _ _ (ntsym _ _ _ R1) R2) as R12.
          destruct (nparams_tele_rel_member p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ R12) as (Mj' & HMj' & H12).
          rewrite HMj in HMj'; injection HMj' as <-.
          pose proof H12 as Hl12; rewrite tele_rel_iff in Hl12; destruct Hl12 as (Lb1 & Lb2 & _).
          rewrite List.length_rev in Lb1, Lb2.
          (** At the end of the shape, the telescope is all of its domains. *)
          rewrite shape_doms_tele_firstn_all by lia.
          econstructor; [ exact Ebs1 | exact Ebs2 | exact (Hokr _ _ _ _ Hn1 Hw1 Hy1 R1) | exact (Hokr _ _ _ _ Hn2 Hw2 Hy2 R2) |].
          eapply ind_rel_neut; [ exact HMj | exact Hrvj | exact Href1 | exact H12 | | | | | exact He ].
          * rewrite List.length_app, Hlen1; unfold im_np, im_nn; lia.
          * rewrite List.length_app, Hlen2; unfold im_np, im_nn; lia.
          * rewrite skipn_app_exact by exact Hlen1; exact (trefl _ _ HMj _ _ H12).
          * rewrite skipn_app_exact by exact Hlen2; exact (trefl_r _ _ HMj _ _ H12).
        + destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB _].
          assert (k < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence); lia.
      - destruct (ptyp_skip k t0) as [j Ps | B t] eqn:Hs.
        + destruct (ptyp_skip_self _ _ _ _ Hs) as (Hkd & _ & _); lia.
        + destruct (ptyp_skip_pi _ _ _ _ Hs) as [HB Hs'].
          assert (Hkl : k < List.length (ptyp_doms t0)) by (apply List.nth_error_Some; congruence).
          inversion E1 as [| | B0 ρ0 b1 t1 ? ? Eb1]; subst.
          inversion E2 as [| | B0 ρ0 b2 t1 ? ? Eb2]; subst.
          destruct (HD1 _ _ _ _ HB Hy1) as [bu b1' Ebu Eb1' Htop1 _ Hrel1 _ _].
          destruct (HD2 _ _ _ _ HB Hy2) as [bu' b2' Ebu' Eb2' Htop2 _ Hrel2 _ _].
          pose proof (functional_eval_exp _ _ _ _ Ebu Ebu') as <-.
          pose proof (functional_eval_exp _ _ _ _ Eb1 Eb1') as <-.
          pose proof (functional_eval_exp _ _ _ _ Eb2 Eb2') as <-.
          pose proof (doms_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM nsu c _ gs1 t0 gs2 wsu Huu Hc eq_refl
                        Hwuu k ysu ys1 ltac:(lia) Hy1) as Hyuu.
          pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Huu Hc eq_refl Hwuu HB Hyuu) as HPd.
          pose proof (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hn1 Hc eq_refl Hw1 HB Hy1) as HI1.
          constructor; [| exact Hrel1 | exact Hrel2 ]; intros c0 c0' Hcc.
          (** The argument of the domain, at [ups]'s prefix. *)
          apply (proj2 (HI1 _ _)) in Hcc.
          assert (Hcc0 : dr m (nsu ++ wsu ++ ysu) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t0)) B c0 c0)
            by (etransitivity; [ exact Hcc | symmetry; exact Hcc ]).
          assert (Hy1' : tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) (S k) (ysu ++ c0 :: nil) (ys1 ++ c0 :: nil))
            by (apply tele_prefix_rel_snoc; [ exact Hy1 | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc0 ]).
          assert (Hy2' : tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) (S k) (ysu ++ c0 :: nil) (ys2 ++ c0' :: nil))
            by (apply tele_prefix_rel_snoc; [ exact Hy2 | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hcc ]).
          destruct (shape_type_exists ua1 m Mm c gs1 t0 gs2 nsu ns1 wsu ws1 HM Hc Hme1 HR1 HD1 (S k) _ _ ltac:(lia) Hy1')
            as [a1' Ea1'].
          destruct (shape_type_exists ua2 m Mm c gs1 t0 gs2 nsu ns2 wsu ws2 HM Hc Hme2 HR2 HD2 (S k) _ _ ltac:(lia) Hy2')
            as [a2' Ea2'].
          (** The lengths of the prefixes, to extend their environments. *)
          pose proof (proj1 (tele_rel_iff _ _ _ _) Hn1) as (_ & Ln1 & _); rewrite List.length_rev in Ln1.
          pose proof (proj1 (tele_rel_iff _ _ _ _) Hn2) as (_ & Ln2 & _); rewrite List.length_rev in Ln2.
          pose proof (proj1 (tele_prefix_rel_iff _ _ _ _) Hw1) as (_ & Lw1 & _).
          pose proof (proj1 (tele_prefix_rel_iff _ _ _ _) Hw2) as (_ & Lw2 & _).
          pose proof (proj1 (tele_prefix_rel_iff _ _ _ _) Hy1) as (_ & Ly1 & _).
          pose proof (proj1 (tele_prefix_rel_iff _ _ _ _) Hy2) as (_ & Ly2 & _).
          econstructor;
            [ eapply eval_app_neut; [ constructor | eapply eval_fam_cod_shfam ];
              rewrite <- (components_env_shape_snoc _ _ _ _ _ _ _ _ _ _ Ln1 Lw1 ltac:(rewrite Ly1; exact HB)); exact Ea1'
            | eapply eval_app_neut; [ constructor | eapply eval_fam_cod_shfam ];
              rewrite <- (components_env_shape_snoc _ _ _ _ _ _ _ _ _ _ Ln2 Lw2 ltac:(rewrite Ly2; exact HB)); exact Ea2' |].
          replace ((ns1 ++ ws1 ++ ys1) ++ c0 :: nil) with (ns1 ++ ws1 ++ (ys1 ++ c0 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
          replace ((ns2 ++ ws2 ++ ys2) ++ c0' :: nil) with (ns2 ++ ws2 ++ (ys2 ++ c0' :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
          rewrite (prefix_tele_snoc_dom _ _ _ _ _ HB).
          apply (IH (S k) _ _ _ _ _ _ _ ltac:(lia) Hy1' Hy2'); [ exact Ea1' | exact Ea2' |].
          apply per_bot_app; [ exact He |].
          exact (per_top_trans' _ _ _ (per_top_sym' _ _ (Htop1 _ _ Hcc0)) (Htop2 _ _ Hcc)).
    Qed.

    (** The members' types at the uniform parameters [X] are defined. *)
    Definition mrefs_ok (X : list domain) : Prop := forall j, end_ok X j.

    (** The domains of a shape [t] of the member [k], after the components
        [pre] and [pre'] on each side, at the uniform parameters [X] and
        [Y]: each domain is defined on each side, and at related arguments
        its two values read back alike, and so on for the rest after
        them. *)
    Inductive shape_doms_ok (X Y : list domain) (k : nat) : list domain -> list domain -> list centry -> ptyp -> Prop :=
    (** At the end: the parameters at [X] and at [Y] are defined and
        admissible, as an element's at any admissible base are: so an
        element at another base reads back at the end's type at [X] and
        [Y], at indices related to its own ([elim_ups_ok]) *)
    | shape_doms_ok_self : forall pre pre' Ts j Ps bsX bsY,
        ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D X Ts pre ↘ bsX ->
        ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D Y Ts pre' ↘ bsY ->
        admissible_index_at D ups nr j pre Ts Ps bsX -> admissible_index_at D ups nr j pre' Ts Ps bsY ->
        shape_doms_ok X Y k pre pre' Ts (pt_self j Ps)
    (** At a domain: defined on each side, in the environment of the
        components before it, of the telescope [Ts]; related arguments read
        back alike, and the rest after them; the domain's two values are
        relevant types, as a shape's domain, a type of a universe, is *)
    | shape_doms_ok_pi : forall pre pre' Ts B t b b',
        ⟦ B ⟧ gc_deps ⍮ gc_stack ⍮ components_env D X Ts pre ↘ b ->
        ⟦ B ⟧ gc_deps ⍮ gc_stack ⍮ components_env D Y Ts pre' ↘ b' ->
        (forall c c', dr k pre Ts B c c' -> Dom ⇓ b c ≈ ⇓ b' c' ∈ per_top) ->
        (forall c c', dr k pre Ts B c c' -> shape_doms_ok X Y k (pre ++ c :: nil) (pre' ++ c' :: nil) (Ts ++ ce_ass ak_relevant B :: nil) t) ->
        domain_kind b = ak_relevant -> domain_kind b' = ak_relevant ->
        (** the two values read back alike as types *)
        Dom b ≈ b' ∈ per_top_typ ->
        (** and their variables are related: the arguments η-directed
            readback applies a function of the shape to *)
        (forall s, dr k pre Ts B (⇑! b s) (⇑! b' s)) ->
        shape_doms_ok X Y k pre pre' Ts (pt_pi B t).

    (** The parameters at the end of a shape of an argument, among
        components at an admissible base [X] related to those at [ups]:
        defined and admissible ([adm_rec_params] at the components
        themselves). *)
    Lemma shape_end_admissible : forall X m Mm c gs1 t0 gs2 nsu ns wsu ws ysu ys,
        adm_uparams D ups nr ar dr X ->
        ind_member D m = Some Mm -> ind_con Mm c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) nsu ns ->
        tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu ws ->
        tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0)
          (List.length (ptyp_doms t0)) ysu ys ->
        exists bs, ⟦ ptyp_ps t0 ⟧* gc_deps ⍮ gc_stack ⍮
            components_env D X (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns ++ ws ++ ys) ↘ bs /\
          admissible_index_at D ups nr (ptyp_mem t0) (ns ++ ws ++ ys)
            (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ptyp_ps t0) bs.
    Proof.
      intros * HaX HM Hc Hn Hw Hy.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM _ _ Hn) as Hnn.
      pose proof (args_prefix_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM _ _ c _ _ _ _ Hn Hc HK Hw) as Hww.
      pose proof (doms_rel_refl_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM _ _ c _ gs1 t0 gs2 _ _ _ _ _
                    Hn Hc eq_refl Hw (le_n _) Hy) as Hyy.
      destruct (adm_rec_params _ _ _ _ _ _ HaX m Mm ns ns c _ gs1 t0 gs2 ws ws ys ys HM Hnn Hc eq_refl Hww
                  (tele_rel_of_pre _ _ _ _ Hyy)) as [base bs Eu EX Hr].
      exists bs; split; [ exact EX | exact (mk_admissible_index_at _ _ _ _ _ _ _ _ base Eu Hr) ].
    Qed.

    (** The domains of a shape of an argument at two bases, after prefixes
        related to the ones at [ups], as [shape_neut] has them. *)
    Lemma shape_doms_fresh : forall ua1 ua2 m Mm c gs1 t0 gs2 nsu ns1 ns2 wsu ws1 ws2,
        adm_uparams D ups nr ar dr ua1 -> adm_uparams D ups nr ar dr ua2 ->
        ind_member D m = Some Mm -> ind_con Mm c = Some (gs1 ++ ca_rec t0 :: gs2) ->
        tele_rel (nr m) (List.rev (im_nparams Mm)) nsu ns1 -> tele_rel (nr m) (List.rev (im_nparams Mm)) nsu ns2 ->
        tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu ws1 ->
        tele_prefix_rel (ar m nsu c) (List.length (cargs_nonrec gs1)) wsu ws2 ->
        (forall j B ys ys', List.nth_error (ptyp_doms t0) j = Some B ->
           tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) j ys ys' ->
           rel_dom_apps B (components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (nsu ++ wsu ++ ys)) (components_env D ua1 (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns1 ++ ws1 ++ ys'))
             (dr m (nsu ++ wsu ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t0)) B)) ->
        (forall j B ys ys', List.nth_error (ptyp_doms t0) j = Some B ->
           tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) j ys ys' ->
           rel_dom_apps B (components_env D ups (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (nsu ++ wsu ++ ys)) (components_env D ua2 (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ shape_doms_tele t0) (ns2 ++ ws2 ++ ys'))
             (dr m (nsu ++ wsu ++ ys) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn j (shape_doms_tele t0)) B)) ->
        forall n k ysu ys1 ys2, k + n = List.length (ptyp_doms t0) ->
          tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) k ysu ys1 ->
          tele_prefix_rel (shape_doms_rel (dr m) (List.rev (im_nparams Mm)) (cargs_nonrec_tele gs1) nsu wsu t0) k ysu ys2 ->
          shape_doms_ok ua1 ua2 m (ns1 ++ ws1 ++ ys1) (ns2 ++ ws2 ++ ys2)
            (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t0)) (ptyp_skip k t0).
    Proof.
      intros ua1 ua2 m Mm c gs1 t0 gs2 nsu ns1 ns2 wsu ws1 ws2 Ha1 Ha2 HM Hc Hn1 Hn2 Hw1 Hw2 HD1 HD2.
      pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl.
      assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t0 :: gs2)))
        by (rewrite cargs_nonrec_app, List.length_app; lia).
      pose proof (trefl _ _ HM _ _ Hn1) as Huu.
      pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM nsu c _ Huu Hc _ _ _ HK Hw1)
        as Hwuu.
      induction n as [| n IH]; intros k ysu ys1 ys2 Hkn Hy1 Hy2.
      - rewrite Nat.add_0_r in Hkn; subst k; rewrite ptyp_skip_end, shape_doms_tele_firstn_all by lia.
        destruct (shape_end_admissible ua1 m Mm c gs1 t0 gs2 nsu ns1 wsu ws1 ysu ys1 Ha1 HM Hc Hn1 Hw1 Hy1) as (bs1 & E1 & A1).
        destruct (shape_end_admissible ua2 m Mm c gs1 t0 gs2 nsu ns2 wsu ws2 ysu ys2 Ha2 HM Hc Hn2 Hw2 Hy2) as (bs2 & E2 & A2).
        econstructor; [ exact E1 | exact E2 | exact A1 | exact A2 ].
      - destruct (ptyp_skip_lt k t0 ltac:(lia)) as (B & HB & Hs); rewrite Hs.
        destruct (HD1 _ _ _ _ HB Hy1) as [bu b1 Ebu Eb1 Htop1 _ Hb1r Ty1 V1].
        destruct (HD2 _ _ _ _ HB Hy2) as [bu' b2 Ebu' Eb2 Htop2 _ Hb2r Ty2 V2].
        pose proof (functional_eval_exp _ _ _ _ Ebu Ebu') as <-.
        pose proof (doms_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI m Mm HM nsu c _ gs1 t0 gs2 wsu Huu Hc eq_refl
                      Hwuu k ysu ys1 ltac:(lia) Hy1) as Hyuu.
        pose proof (HdP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Huu Hc eq_refl Hwuu HB Hyuu) as HPd.
        pose proof (HdI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hn1 Hc eq_refl Hw1 HB Hy1) as HI1.
        assert (Hcc0 : forall c0 c0',
                   dr m (ns1 ++ ws1 ++ ys1) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t0)) B c0 c0' ->
                   dr m (nsu ++ wsu ++ ysu) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t0)) B c0 c0' /\
                   dr m (nsu ++ wsu ++ ysu) (List.rev (im_nparams Mm) ++ cargs_nonrec_tele gs1 ++ List.firstn k (shape_doms_tele t0)) B c0 c0).
        { intros c0 c0' Hcc; apply (proj2 (HI1 _ _)) in Hcc; split; [ exact Hcc |].
          etransitivity; [ exact Hcc | symmetry; exact Hcc ]. }
        (** The domain reads only the components before it. *)
        pose proof (proj1 (tele_rel_iff _ _ _ _) Hn1) as (_ & Ln1 & _); rewrite List.length_rev in Ln1.
        pose proof (proj1 (tele_rel_iff _ _ _ _) Hn2) as (_ & Ln2 & _); rewrite List.length_rev in Ln2.
        pose proof (proj1 (tele_prefix_rel_iff _ _ _ _) Hw1) as (_ & Lw1 & _).
        pose proof (proj1 (tele_prefix_rel_iff _ _ _ _) Hw2) as (_ & Lw2 & _).
        pose proof (proj1 (tele_prefix_rel_iff _ _ _ _) Hy1) as (_ & Ly1 & _).
        pose proof (proj1 (tele_prefix_rel_iff _ _ _ _) Hy2) as (_ & Ly2 & _).
        rewrite components_env_shape_prefix, Ly1 in Eb1 by lia.
        rewrite components_env_shape_prefix, Ly2 in Eb2 by lia.
        econstructor; [ exact Eb1 | exact Eb2 | | | exact Hb1r | exact Hb2r
                      | exact (per_top_typ_trans' _ _ _ (per_top_typ_sym' _ _ Ty1) Ty2) |].
        3: intros s0; apply (proj1 (HI1 _ _)); etransitivity; [ symmetry; exact (V1 s0) | exact (V2 s0) ].
        + intros c0 c0' Hcc; destruct (Hcc0 _ _ Hcc) as [Hu Huu0].
          exact (per_top_trans' _ _ _ (per_top_sym' _ _ (Htop1 _ _ Huu0)) (Htop2 _ _ Hu)).
        + intros c0 c0' Hcc; destruct (Hcc0 _ _ Hcc) as [Hu Huu0].
          replace ((ns1 ++ ws1 ++ ys1) ++ c0 :: nil) with (ns1 ++ ws1 ++ (ys1 ++ c0 :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
          replace ((ns2 ++ ws2 ++ ys2) ++ c0' :: nil) with (ns2 ++ ws2 ++ (ys2 ++ c0' :: nil)) by (rewrite <- !List.app_assoc; reflexivity).
          rewrite (prefix_tele_snoc_dom _ _ _ _ _ HB).
          apply (IH (S k) (ysu ++ c0 :: nil) _ (ys2 ++ c0' :: nil) ltac:(lia));
            [ apply tele_prefix_rel_snoc; [ exact Hy1 | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Huu0 ]
            | apply tele_prefix_rel_snoc; [ exact Hy2 | unfold shape_doms_rel; rewrite (List.nth_error_nth _ _ _ HB); exact Hu ] ].
    Qed.

    (** The domains of the shapes of the arguments [vs] and [vs'] of kinds
        [gs] of the member [k], after [pre] and [pre'], each extended by
        the non-recursive arguments ([shape_doms_ok]). *)
    Inductive cargs_doms_ok (X Y : list domain) (k : nat) :
        list domain -> list domain -> list centry -> list carg -> list domain -> list domain -> Prop :=
    (** No argument *)
    | cargs_doms_ok_nil : forall pre pre' Ts, cargs_doms_ok X Y k pre pre' Ts nil nil nil
    (** A non-recursive argument joins the prefixes, at its type *)
    | cargs_doms_ok_arg : forall pre pre' Ts rA A gs v v' vs vs',
        cargs_doms_ok X Y k (pre ++ v :: nil) (pre' ++ v' :: nil) (Ts ++ ce_ass rA A :: nil) gs vs vs' ->
        cargs_doms_ok X Y k pre pre' Ts (ca_arg rA A :: gs) (v :: vs) (v' :: vs')
    (** A recursive argument's shape *)
    | cargs_doms_ok_rec : forall pre pre' Ts t gs v v' vs vs',
        shape_doms_ok X Y k pre pre' Ts t -> cargs_doms_ok X Y k pre pre' Ts gs vs vs' ->
        cargs_doms_ok X Y k pre pre' Ts (ca_rec t :: gs) (v :: vs) (v' :: vs').

    (** The fields of a record view, at two lists whose non-recursive ones
        are related: the domains of their shapes at two admissible uniform
        parameters ([adm_shape_doms] at the view's constructor). *)
    Lemma rview_cargs_doms : forall ua1 ua2, adm_uparams D ups nr ar dr ua1 -> adm_uparams D ups nr ar dr ua2 ->
        forall k Mk qr Is fl c gs, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl -> im_cons Mk = (c, gs) :: nil ->
        forall gs2 gs1 pre pre' vs vs', gs = gs1 ++ gs2 -> List.length vs = List.length gs2 -> List.length vs' = List.length gs2 ->
          tele_prefix_rel (ar k nil c) (List.length (cargs_nonrec gs1)) pre pre' ->
          tele_rel_from (ar k nil c) (List.length (cargs_nonrec gs1)) pre (nonrec_arg_vals gs2 vs) (nonrec_arg_vals gs2 vs') ->
          cargs_doms_ok ua1 ua2 k pre pre' (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) gs2 vs vs'.
    Proof.
      intros ua1 ua2 Ha1 Ha2 k Mk qr Is fl c gs HM Hh Hcs.
      pose proof (ind_con_single _ _ _ Hcs) as Hc.
      pose proof (rview_struct_nparams _ _ _ Hrs _ _ _ _ _ HM Hh) as Hnp.
      assert (Hnil : tele_rel (nr k) (List.rev (im_nparams Mk)) nil nil) by (rewrite Hnp; split; [ reflexivity | exact I ]).
      induction gs2 as [| [rA A | t] gs2 IH]; intros gs1 pre pre' [| v vs] [| v' vs'] Heq L1 L2 Hp Hr; cbn in L1, L2;
        try discriminate; [ constructor | |].
      - cbn [nonrec_arg_vals tele_rel_from] in Hr; destruct Hr as [Hv Hr].
        apply cargs_doms_ok_arg; rewrite (prefix_tele_snoc_arg _ _ rA).
        apply (IH (gs1 ++ ca_arg rA A :: nil)); [ rewrite Heq, <- List.app_assoc; reflexivity | lia | lia | |];
          rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_1_r;
          [ apply tele_prefix_rel_snoc; [ exact Hp | exact Hv ] | exact Hr ].
      - cbn [nonrec_arg_vals] in Hr.
        assert (Hn1 : List.length (cargs_nonrec (gs1 ++ ca_rec t :: nil)) = List.length (cargs_nonrec gs1))
          by (rewrite cargs_nonrec_app, List.length_app; cbn; lia).
        constructor; [| rewrite (prefix_tele_snoc_rec _ _ t);
                        apply (IH (gs1 ++ ca_rec t :: nil)); [ rewrite Heq, <- List.app_assoc; reflexivity | lia | lia
                                                              | rewrite Hn1; exact Hp | rewrite Hn1; exact Hr ] ].
        rewrite Heq in Hc.
        assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t :: gs2)))
          by (rewrite cargs_nonrec_app, List.length_app; lia).
        pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HM nil c _ Hnil Hc _ _ _ HK Hp)
          as Hpp.
        pose proof (shape_doms_fresh ua1 ua2 k Mk c gs1 t gs2 nil nil nil pre pre pre' Ha1 Ha2 HM Hc Hnil Hnil Hpp Hp
                      (fun j B ys ys' HB Hy => adm_shape_doms _ _ _ _ _ _ Ha1 k Mk nil nil c _ gs1 t gs2 pre pre j B ys ys'
                                                 HM Hnil Hc eq_refl Hpp HB Hy)
                      (fun j B ys ys' HB Hy => adm_shape_doms _ _ _ _ _ _ Ha2 k Mk nil nil c _ gs1 t gs2 pre pre' j B ys ys'
                                                 HM Hnil Hc eq_refl Hp HB Hy)
                      (List.length (ptyp_doms t)) 0 nil nil nil eq_refl (tele_prefix_rel_nil _) (tele_prefix_rel_nil _)) as H.
        cbn [ptyp_skip List.app List.firstn] in H; rewrite !List.app_nil_r in H; exact H.
    Qed.

    (** At related fields, from the start. *)
    Corollary rview_fields_doms : forall ua1 ua2, adm_uparams D ups nr ar dr ua1 -> adm_uparams D ups nr ar dr ua2 ->
        forall k Mk qr Is fl c gs vs vs', ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl -> im_cons Mk = (c, gs) :: nil ->
          List.length vs = List.length gs -> List.length vs' = List.length gs ->
          tele_rel (ar k nil c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
          cargs_doms_ok ua1 ua2 k nil nil nil gs vs vs'.
    Proof.
      intros * Ha1 Ha2 * HM Hh Hcs L1 L2 [_ Hr].
      pose proof (rview_cargs_doms ua1 ua2 Ha1 Ha2 k Mk qr Is fl c gs HM Hh Hcs gs nil nil nil vs vs' eq_refl L1 L2
                    (tele_prefix_rel_nil _) Hr) as H.
      rewrite (rview_struct_nparams _ _ _ Hrs _ _ _ _ _ HM Hh) in H; exact H.
    Qed.

    (** The arguments of a constructor of any member, after related
        non-uniform parameters [ns] and [ns'] and related non-recursive
        arguments: the domains of their shapes at two admissible uniform
        parameters ([adm_shape_doms]). *)
    Lemma cargs_doms_adm : forall ua1 ua2, adm_uparams D ups nr ar dr ua1 -> adm_uparams D ups nr ar dr ua2 ->
        forall k Mk c gs ns ns', ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns' ->
        forall gs2 gs1 pre pre' vs vs', gs = gs1 ++ gs2 -> List.length vs = List.length gs2 -> List.length vs' = List.length gs2 ->
          tele_prefix_rel (ar k ns c) (List.length (cargs_nonrec gs1)) pre pre' ->
          tele_rel_from (ar k ns c) (List.length (cargs_nonrec gs1)) pre (nonrec_arg_vals gs2 vs) (nonrec_arg_vals gs2 vs') ->
          cargs_doms_ok ua1 ua2 k (ns ++ pre) (ns' ++ pre') (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) gs2 vs vs'.
    Proof.
      intros ua1 ua2 Ha1 Ha2 k Mk c gs ns ns' HM Hc Hn.
      pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HM _ _ Hn) as Hnn.
      induction gs2 as [| [rA A | t] gs2 IH]; intros gs1 pre pre' [| v vs] [| v' vs'] Heq L1 L2 Hp Hr; cbn in L1, L2;
        try discriminate; [ constructor | |].
      - cbn [nonrec_arg_vals tele_rel_from] in Hr; destruct Hr as [Hv Hr].
        apply cargs_doms_ok_arg; rewrite (prefix_tele_snoc_arg _ _ rA), <- !List.app_assoc.
        apply (IH (gs1 ++ ca_arg rA A :: nil)); [ rewrite Heq, <- List.app_assoc; reflexivity | lia | lia | |];
          rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_1_r;
          [ apply tele_prefix_rel_snoc; [ exact Hp | exact Hv ] | exact Hr ].
      - cbn [nonrec_arg_vals] in Hr.
        assert (Hn1 : List.length (cargs_nonrec (gs1 ++ ca_rec t :: nil)) = List.length (cargs_nonrec gs1))
          by (rewrite cargs_nonrec_app, List.length_app; cbn; lia).
        constructor; [| rewrite (prefix_tele_snoc_rec _ _ t);
                        apply (IH (gs1 ++ ca_rec t :: nil)); [ rewrite Heq, <- List.app_assoc; reflexivity | lia | lia
                                                              | rewrite Hn1; exact Hp | rewrite Hn1; exact Hr ] ].
        rewrite Heq in Hc.
        assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec (gs1 ++ ca_rec t :: gs2)))
          by (rewrite cargs_nonrec_app, List.length_app; lia).
        pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HM ns c _ Hnn Hc _ _ _ HK Hp)
          as Hpp.
        pose proof (shape_doms_fresh ua1 ua2 k Mk c gs1 t gs2 ns ns ns' pre pre pre' Ha1 Ha2 HM Hc Hnn Hn Hpp Hp
                      (fun j B ys ys' HB Hy => adm_shape_doms _ _ _ _ _ _ Ha1 k Mk ns ns c _ gs1 t gs2 pre pre j B ys ys'
                                                 HM Hnn Hc eq_refl Hpp HB Hy)
                      (fun j B ys ys' HB Hy => adm_shape_doms _ _ _ _ _ _ Ha2 k Mk ns ns' c _ gs1 t gs2 pre pre' j B ys ys'
                                                 HM Hn Hc eq_refl Hp HB Hy)
                      (List.length (ptyp_doms t)) 0 nil nil nil eq_refl (tele_prefix_rel_nil _) (tele_prefix_rel_nil _)) as H.
        cbn [ptyp_skip List.app List.firstn] in H; rewrite !List.app_nil_r in H; exact H.
    Qed.

    (** ** The Eliminator at Related Elements

        Two eliminators of the group, their blocks [Bksa] and [Bksb]
        closures in [ρa] and [ρb], the family [Rel j] of each member's
        motives, the uniform parameters [ua] and [ub] they carry.  Their
        motives are related at related elements, and their branches at
        related constructors and related recursive results.

        The uniform parameters of the eliminators, as the blocks are read
        at them: admissible beside [ups], each member's type defined at
        them, and the uniform parameters of the member's container (its own
        group's at a declared member) reading back alike, as the read
        eliminator carries them. *)
    Record elim_ups_ok (ua ub : list domain) : Prop := mk_elim_ups_ok
      { (** [ua] has one entry per uniform parameter *)
        elim_ups_ok_len_a : List.length ua = ind_nu D
        (** So has [ub] *)
      ; elim_ups_ok_len_b : List.length ub = ind_nu D
        (** [ua] is admissible beside [ups] *)
      ; elim_ups_ok_adm_a : adm_uparams D ups nr ar dr ua
        (** So is [ub] *)
      ; elim_ups_ok_adm_b : adm_uparams D ups nr ar dr ub
        (** Each member's type is defined at [ua] *)
      ; elim_ups_ok_mref_a : mrefs_ok ua
        (** And at [ub] *)
      ; elim_ups_ok_mref_b : mrefs_ok ub
        (** The containers' uniform parameters at [ua] and [ub] read back
            alike *)
      ; elim_ups_ok_container_uparams : forall j Mj hd k pa pb Dq, ind_member D j = Some Mj ->
          ⟦mref j of p ua ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pa) -> ⟦mref j of p ub ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pb) ->
          ind_lookup gc_deps gc_stack hd = Some Dq ->
          per_top_ps (List.rev (ind_uparams Dq)) pa pb
        (** The left one of two elements of a member at any bases [u] and
            [u'] admissible beside [ups] reads back at the member's type at
            [ua], at any indices related to its own: the type a motive's
            scrutinee is stored at, a stuck eliminator's
            ([eval_elim_neut]), a recursive argument's ([eval_ihty_self])
            and a branch's constructor's (readback), and the type a branch
            stores a recursive argument at, at the end of its shape
            ([eval_shape_type_self]).  The bases and the indices differ
            from [ua]'s: for [Vec (A : Type) : ℕ → Type] with
            [cons (n : ℕ) (x : A) (xs : Vec A n)] eliminated at [ua],
            [cons n x xs] comes at the scrutinee type's bases, and its
            branch stores [xs] at [Vec] at [ua] and at [n] evaluated among
            [ua]'s components, related to, not equal to, [xs]'s own index.
            At a view, the type is the container's member's, which the
            group's elements are elements of only by the views' clauses,
            so it is asked for.  A record view's elements are never a
            motive's scrutinee (it has no block; its recursive results are
            its fields', [eval_ih_rview], [eval_ihty_rview]), but they are
            a branch's recursive arguments, at the record type: the last
            two fields *)
      ; elim_ups_ok_member_elements_readable_at_ua : forall j Mj hd k pa u u' bs bs' bs2 v v',
          ind_member D j = Some Mj -> im_is_rview Mj = false ->
          adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' ->
          ⟦mref j of p ua ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pa) -> grp_rel p D ups nr ar dr j u u' bs bs' v v' ->
          tele_rel (nr j) (List.rev (im_nparams Mj)) bs bs2 ->
          entry_readable (de_term v (entry_type_value (d_ind hd k (pa ++ bs2))))
        (** And the right one at [ub] *)
      ; elim_ups_ok_member_elements_readable_at_ub : forall j Mj hd k pb u u' bs bs' bs2 v v',
          ind_member D j = Some Mj -> im_is_rview Mj = false ->
          adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' ->
          ⟦mref j of p ub ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pb) -> grp_rel p D ups nr ar dr j u u' bs bs' v v' ->
          tele_rel (nr j) (List.rev (im_nparams Mj)) bs' bs2 ->
          entry_readable (de_term v' (entry_type_value (d_ind hd k (pb ++ bs2))))
        (** The left one of two elements of a record view at any bases [u]
            and [u'] admissible beside [ups] reads back at the record type
            at the view's instance at [ua]: the type a branch stores a
            recursive argument of a shape ending at the view at
            ([eval_shape_type_rview]).  For [T ≔ node (r : R)] with the
            record view [R ≔ { f : T }] in [T]'s group, the branch of
            [node] binds [r] at the record type [R] at [ua], where it reads
            back through its field [f], at [T]'s type *)
      ; elim_ups_ok_rview_elements_readable_at_ua : forall j Mj qr Is fl cups u u' v v', ind_member D j = Some Mj ->
          im_head Mj = mh_record qr Is fl -> adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' ->
          ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ua ↘ cups ->
          grp_rel p D ups nr ar dr j u u' nil nil v v' -> entry_readable (de_term v (entry_type_value (d_record qr cups)))
        (** And the right one at [ub] *)
      ; elim_ups_ok_rview_elements_readable_at_ub : forall j Mj qr Is fl cups u u' v v', ind_member D j = Some Mj ->
          im_head Mj = mh_record qr Is fl -> adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' ->
          ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ub ↘ cups ->
          grp_rel p D ups nr ar dr j u u' nil nil v v' -> entry_readable (de_term v' (entry_type_value (d_record qr cups)))
        (** A member's types at [ua] and at [ub], at related non-uniform
            parameters, read back alike: the scrutinee type a block is
            read back at.  For [Vec (A : Type) : ℕ → Type] at [ua] and
            [ub] the same [A], [Vec A n] and [Vec A n'] read back alike for
            related [n] and [n'] *)
      ; elim_ups_ok_member_types_alike : forall j Mj hd k pa pb bs bs', ind_member D j = Some Mj -> im_is_rview Mj = false ->
          ⟦mref j of p ua ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pa) -> ⟦mref j of p ub ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, pb) ->
          tele_rel (nr j) (List.rev (im_nparams Mj)) bs bs' ->
          Dom d_ind hd k (pa ++ bs) ≈ d_ind hd k (pb ++ bs') ∈ per_top_typ }.

    Section ElimRel.
      Variable (i : universe_index) (ρa ρb : env) (Bksa Bksb : list eblock) (ua ub : list domain).
      Hypothesis (Hups : elim_ups_ok ua ub).
      Variable (Rel : nat -> list domain -> domain -> list domain -> domain -> relation domain).
      (** A block for each member but the record views *)
      Hypothesis (HbA : forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false -> exists b, List.nth_error Bksa j = Some b)
        (HbB : forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false -> exists b, List.nth_error Bksb j = Some b).
      Hypothesis (HnmA : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bksa j = Some b -> eb_binder_count b = S (im_nn Mj))
        (HnmB : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bksb j = Some b -> eb_binder_count b = S (im_nn Mj)).
      Hypothesis (HnaA : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bksa j = Some b -> brs_names (im_cons Mj) (eb_brs b))
        (HnaB : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bksb j = Some b -> brs_names (im_cons Mj) (eb_brs b)).
      Hypothesis (HarA : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bksa j = Some b ->
                    ind_con Mj c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat)
        (HarB : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bksb j = Some b ->
                    ind_con Mj c = Some gs -> In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat).
      Hypothesis (Hnd : forall j Mj, ind_member D j = Some Mj -> List.NoDup (List.map fst (im_cons Mj))).
      (** The motives, at the two sides' indices of related elements, the
          indices and the elements stored at any types they read back at:
          the motive's environment is in its context's PER whatever the
          stored types are, as long as its entries read back. *)
      Hypothesis (Hmot : forall j Mj ba bb u u' ns ns' m m' ts ts', ind_member D j = Some Mj -> im_is_rview Mj = false ->
                    List.nth_error Bksa j = Some ba -> List.nth_error Bksb j = Some bb ->
                    grp_rel p D ups nr ar dr j u u' ns ns' m m' ->
                    List.Forall2 (fun v t => entry_readable (de_term v t)) (ns ++ m :: nil) ts ->
                    List.Forall2 (fun v t => entry_readable (de_term v t)) (ns' ++ m' :: nil) ts' ->
                    exists a a', ⟦ eb_motive ba ⟧ env_extend_typed ρa (List.combine (ns ++ m :: nil) ts) ↘ a /\
                      ⟦ eb_motive bb ⟧ env_extend_typed ρb (List.combine (ns' ++ m' :: nil) ts') ↘ a' /\
                      DF a ≈ a' ∈ per_univ_elem i ↘ Rel j ns m ns' m').
      (** Related indices and elements read back at some types, on each
          side (the model gives them their types in the motive's context). *)
      Hypothesis (Hidx : forall j Mj u u' ns ns' m m', ind_member D j = Some Mj -> im_is_rview Mj = false ->
                    grp_rel p D ups nr ar dr j u u' ns ns' m m' ->
                    (exists ts, List.Forall2 (fun v t => entry_readable (de_term v t)) (ns ++ m :: nil) ts) /\
                    (exists ts', List.Forall2 (fun v t => entry_readable (de_term v t)) (ns' ++ m' :: nil) ts')).
      (** Neutrals of a record view's record, at its instances at [ua] and
          [ub], are related by its record clause: their projections are
          related as its fields (S1-V's counterpart of the record shape;
          the model gives it, [rview_end_rel]). *)
      Hypothesis (Hrneut : forall j Mj qr Is fl cups1 cups2 e e', ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
                    ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ua ↘ cups1 -> ⟦ Is ⟧* gc_deps ⍮ gc_stack ⍮ decl_env D ub ↘ cups2 ->
                    Dom e ≈ e' ∈ per_bot ->
                    grp_rel p D ups nr ar dr j ua ub nil nil (⇑ (d_record qr cups1) e) (⇑ (d_record qr cups2) e')).

      (** The recursive results [rs] and [rs'] of recursive arguments [v]
          and [v'] of shape [t] of the member [k], one per leaf path of the
          shape, after the values [pre] and [pre'] of the shape's
          components on each side, the bases [u] and [u'] apart: at the end
          at a member with a block, related at [Rel] at the parameters the
          shape evaluates to on each side; at a record view, those of its
          fields at the projections; and at a domain, pointwise. *)
      Inductive rec_result_rel (k : nat) (u u' : list domain) :
          list domain -> list domain -> list centry -> ptyp -> domain -> domain -> list domain -> list domain -> Prop :=
      (** At the end, at a member with a block: related at [Rel] of the
          member [j], the parameters evaluated in the environment of the
          components, of the telescope [Ts] *)
      | rec_result_self : forall pre pre' Ts j Mj Ps bs bs' v v' ih ih',
          ind_member D j = Some Mj -> im_is_rview Mj = false ->
          ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D u Ts pre ↘ bs ->
          ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ components_env D u' Ts pre' ↘ bs' ->
          Rel j bs v bs' v' ih ih' ->
          rec_result_rel k u u' pre pre' Ts (pt_self j Ps) v v' (ih :: nil) (ih' :: nil)
      (** At the end, at a record view: the results of its fields at the
          projections *)
      | rec_result_rview : forall pre pre' Ts j Mj qr Is fl c gs Ps v v' ws ws' rs rs',
          ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
          ⟦projs fl of v ⟧ gc_deps ⍮ gc_stack ↘ ws -> ⟦projs fl of v' ⟧ gc_deps ⍮ gc_stack ↘ ws' ->
          rec_results_rel j u u' nil nil nil gs ws ws' rs rs' ->
          rec_result_rel k u u' pre pre' Ts (pt_self j Ps) v v' rs rs'
      (** At a domain: pointwise at related arguments, the results taking
          relevant arguments, as the elements of a [Π] over the domain, a
          type of a universe, do *)
      | rec_result_pi : forall pre pre' Ts B t v v' rs rs',
          (forall c c', dr k pre Ts B c c' ->
             rec_result_app_rel k u u' (pre ++ c :: nil) (pre' ++ c' :: nil) (Ts ++ ce_ass ak_relevant B :: nil) t v c v' c' rs rs') ->
          List.Forall (fun r => arg_kind gc_deps gc_stack r = ak_relevant) rs ->
          List.Forall (fun r => arg_kind gc_deps gc_stack r = ak_relevant) rs' ->
          rec_result_rel k u u' pre pre' Ts (pt_pi B t) v v' rs rs'
      with rec_result_app_rel (k : nat) (u u' : list domain) :
          list domain -> list domain -> list centry -> ptyp -> domain -> domain -> domain -> domain -> list domain -> list domain -> Prop :=
      (** The arguments and each result applied, related at the rest *)
      | rec_result_app_mk : forall pre pre' Ts t v c v' c' rs rs' fc fc' rcs rcs',
          $| v & c | gc_deps ⍮ gc_stack ↘ fc -> $| v' & c' | gc_deps ⍮ gc_stack ↘ fc' ->
          List.Forall2 (fun f r => $| f & c | gc_deps ⍮ gc_stack ↘ r) rs rcs ->
          List.Forall2 (fun f r => $| f & c' | gc_deps ⍮ gc_stack ↘ r) rs' rcs' ->
          rec_result_rel k u u' pre pre' Ts t fc fc' rcs rcs' ->
          rec_result_app_rel k u u' pre pre' Ts t v c v' c' rs rs'
      (** The recursive results of related arguments, after the values
          [pre] and [pre'] of the non-uniform parameters and the
          non-recursive arguments before them on each side, of the
          telescope [Ts]. *)
      with rec_results_rel (k : nat) (u u' : list domain) :
          list domain -> list domain -> list centry -> list carg -> list domain -> list domain -> list domain -> list domain -> Prop :=
      (** No argument *)
      | rec_results_nil : forall pre pre' Ts, rec_results_rel k u u' pre pre' Ts nil nil nil nil nil
      (** A non-recursive argument joins the prefixes, at its type *)
      | rec_results_arg : forall pre pre' Ts rA A gs v v' vs vs' ihs ihs',
          rec_results_rel k u u' (pre ++ v :: nil) (pre' ++ v' :: nil) (Ts ++ ce_ass rA A :: nil) gs vs vs' ihs ihs' ->
          rec_results_rel k u u' pre pre' Ts (ca_arg rA A :: gs) (v :: vs) (v' :: vs') ihs ihs'
      (** A recursive argument's results, one per leaf path, are related *)
      | rec_results_rec : forall pre pre' Ts t gs v v' vs vs' rs rs' ihs ihs',
          List.length rs = List.length (shape_leaves (rview_leaves D) 0 t) ->
          List.length rs' = List.length (shape_leaves (rview_leaves D) 0 t) ->
          rec_result_rel k u u' pre pre' Ts t v v' rs rs' ->
          rec_results_rel k u u' pre pre' Ts gs vs vs' ihs ihs' ->
          rec_results_rel k u u' pre pre' Ts (ca_rec t :: gs) (v :: vs) (v' :: vs') (rs ++ ihs) (rs' ++ ihs').

      (** What the eliminators give two related elements of the member [j]:
          at a member with a block, the eliminators' values, related at
          [Rel]; at a record view, the recursive results of its fields at
          the projections. *)
      Inductive member_results (j : nat) (u u' ns ns' : list domain) (m m' : domain) : Prop :=
      (** A member with a block: the eliminators *)
      | member_results_elim : forall Mj r r', ind_member D j = Some Mj -> im_is_rview Mj = false ->
          ⟦elim m at j of p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ r -> ⟦elim m' at j of p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ r' ->
          Rel j ns m ns' m' r r' -> member_results j u u' ns ns' m m'
      (** A record view: its fields' recursive results *)
      | member_results_rview : forall Mj qr Is fl c gs ws ws' rs rs',
          ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl -> im_cons Mj = (c, gs) :: nil ->
          ⟦projs fl of m ⟧ gc_deps ⍮ gc_stack ↘ ws -> ⟦projs fl of m' ⟧ gc_deps ⍮ gc_stack ↘ ws' ->
          ⟦ihs ws of gs under p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ rs ->
          ⟦ihs ws' of gs under p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ rs' ->
          rec_results_rel j u u' nil nil nil gs ws ws' rs rs' -> member_results j u u' ns ns' m m'.

      (** The branches, at two related constructors and related recursive
          results. *)
      Hypothesis (Hbr : forall j Mj ba bb c gs n Ba Bb u u' bs bs' vs vs' ihs ihs' hd k' ts ts', ind_member D j = Some Mj ->
                    im_is_rview Mj = false -> List.nth_error Bksa j = Some ba -> List.nth_error Bksb j = Some bb -> ind_con Mj c = Some gs ->
                    brs_lookup (eb_brs ba) c = Some (n, Ba) -> brs_lookup (eb_brs bb) c = Some (n, Bb) ->
                    grp_rel p D ups nr ar dr j u u' (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs')
                      (d_con hd k' c (bs ++ vs)) (d_con hd k' c (bs' ++ vs')) ->
                    rec_results_rel j u u'
                      (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') (List.rev (im_nparams Mj)) gs vs vs' ihs ihs' ->
                    (** The branch's variables stored at any types they read back at *)
                    List.Forall2 (fun v t => entry_readable (de_term v t)) (List.skipn (im_unu D Mj) bs ++ vs ++ ihs) ts ->
                    List.Forall2 (fun v t => entry_readable (de_term v t)) (List.skipn (im_unu D Mj) bs' ++ vs' ++ ihs') ts' ->
                    exists r r', ⟦ Ba ⟧ env_extend_typed ρa (List.combine (List.skipn (im_unu D Mj) bs ++ vs ++ ihs) ts) ↘ r /\
                      ⟦ Bb ⟧ env_extend_typed ρb (List.combine (List.skipn (im_unu D Mj) bs' ++ vs' ++ ihs') ts') ↘ r' /\
                      Rel j (List.skipn (im_unu D Mj) bs) (d_con hd k' c (bs ++ vs))
                        (List.skipn (im_unu D Mj) bs') (d_con hd k' c (bs' ++ vs')) r r').

      (** *** The Family Is Invariant *)
      Lemma motive_rel_right : forall j Mj u1 u1' u2 u2' ns m ns1 m1 ns2 m2, ind_member D j = Some Mj -> im_is_rview Mj = false ->
          grp_rel p D ups nr ar dr j u1 u1' ns ns1 m m1 -> grp_rel p D ups nr ar dr j u2 u2' ns ns2 m m2 ->
          (Rel j ns m ns1 m1 <~> Rel j ns m ns2 m2).
      Proof.
        intros * HM Hrv Hm1 Hm2.
        destruct (HbA _ _ HM Hrv) as [ba Ha]; destruct (HbB _ _ HM Hrv) as [bb Hb].
        (** Each side's motive at types its indices read back at. *)
        destruct (Hidx _ _ _ _ _ _ _ _ HM Hrv Hm1) as [(ts1 & T1) (ts1' & T1')].
        destruct (Hidx _ _ _ _ _ _ _ _ HM Hrv Hm2) as [_ (ts2' & T2')].
        destruct (Hmot _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Ha Hb Hm1 T1 T1') as (a & a1 & Ea & Ea1 & HR1).
        destruct (Hmot _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Ha Hb Hm2 T1 T2') as (b & a2 & Eb & Ea2 & HR2).
        pose proof (functional_eval_exp _ _ _ _ Ea Eb) as <-.
        eapply per_univ_elem_right_irrel; eassumption.
      Qed.

      Lemma motive_rel_left : forall j Mj u1 u1' u2 u2' ns1 m1 ns2 m2 ns' m', ind_member D j = Some Mj -> im_is_rview Mj = false ->
          grp_rel p D ups nr ar dr j u1 u1' ns1 ns' m1 m' -> grp_rel p D ups nr ar dr j u2 u2' ns2 ns' m2 m' ->
          (Rel j ns1 m1 ns' m' <~> Rel j ns2 m2 ns' m').
      Proof.
        intros * HM Hrv Hm1 Hm2.
        destruct (HbA _ _ HM Hrv) as [ba Ha]; destruct (HbB _ _ HM Hrv) as [bb Hb].
        destruct (Hidx _ _ _ _ _ _ _ _ HM Hrv Hm1) as [(ts1 & T1) (ts1' & T1')].
        destruct (Hidx _ _ _ _ _ _ _ _ HM Hrv Hm2) as [(ts2 & T2) _].
        destruct (Hmot _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Ha Hb Hm1 T1 T1') as (a1 & a & Ea1 & Ea & HR1).
        destruct (Hmot _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Ha Hb Hm2 T2 T1') as (a2 & b & Ea2 & Eb & HR2).
        pose proof (functional_eval_exp _ _ _ _ Ea Eb) as <-.
        eapply per_univ_elem_left_irrel; eassumption.
      Qed.

      (** The family at related elements does not depend on the indices. *)
      Lemma motive_rel_move : forall j Mj u u' ns ns' m m' ns1 ns1', ind_member D j = Some Mj -> im_is_rview Mj = false ->
          grp_rel p D ups nr ar dr j u u' ns ns' m m' ->
          tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns1 -> tele_rel (nr j) (List.rev (im_nparams Mj)) ns' ns1' ->
          (Rel j ns m ns' m' <~> Rel j ns1 m ns1' m').
      Proof.
        intros * HM Hrv Hm H1 H1'.
        pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ H1) as H0.
        pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HM Hm H0 H1') as Hmid.
        pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HM Hm H1 H1') as Hm1.
        etransitivity; [ exact (motive_rel_right _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Hm Hmid)
                       | exact (motive_rel_left _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Hmid Hm1) ].
      Qed.

      (** The member of a group a member is at: the member itself, or the
          container's at a view. *)
      Lemma im_ref_target : forall j Mj hd k', ind_member D j = Some Mj -> im_ref p j Mj = (hd, k') ->
          exists Dq Mk, ind_lookup gc_deps gc_stack hd = Some Dq /\ ind_member Dq k' = Some Mk /\
            im_nn Mk = im_nn Mj /\ ind_nu Dq = im_unu D Mj.
      Proof.
        intros * HM Hr; unfold im_ref in Hr; destruct (im_head Mj) as [pm | qc kc Is vm | qr Is fl] eqn:Hh; injection Hr as <- <-.
        - exists D, Mj; unfold im_unu; rewrite Hh; auto.
        - destruct (grp_tele_ass_views _ Hass j Mj qc kc Is vm HM Hh) as (Dq & Mc & Hq & HMc & Hnn & HIs).
          exists Dq, Mc; unfold im_unu; rewrite Hh; auto.
        - exists D, Mj; unfold im_unu; rewrite Hh; auto.
      Qed.

      (** A member but a record view has its type, the one [im_ref] names,
          at uniform parameters where the members' types are defined. *)
      Lemma mref_at_ref : forall X j Mj hd k', mrefs_ok X -> ind_member D j = Some Mj -> im_is_rview Mj = false ->
          im_ref p j Mj = (hd, k') -> exists cups, ⟦mref j of p X ⟧ gc_deps ⍮ gc_stack ↘ (hd, k', cups).
      Proof.
        intros * Hok HM Hrv Hr.
        destruct (proj1 (Hok j Mj HM) Hrv) as [r Hr'].
        unfold im_ref in Hr; destruct (im_head Mj) as [pm | qc kc Is vm | qr Is fl] eqn:Hh; injection Hr as <- <-.
        - rewrite (mref_decl_inv _ _ _ _ _ _ _ Hl HM Hh Hr') in Hr'; eexists; exact Hr'.
        - destruct (mref_view_inv _ _ _ _ _ _ _ _ _ _ Hl HM Hh Hr') as (py & -> & _); eexists; exact Hr'.
        - unfold im_is_rview in Hrv; rewrite Hh in Hrv; discriminate.
      Qed.

      (** The entries of the motive at the end of a shape, as [eval_ihty_self]
          types it at uniform parameters [X] admissible beside [ups]: the
          shape's parameters, related to an index at the type's base, and
          an element [v] of the member at the shape's type, read back when
          [v] does at the member's type at [X]. *)
      Lemma motive_self_entries_readable : forall X ρ j Mj Ps bs base hd k' v,
          adm_uparams D ups nr ar dr X -> mrefs_ok X ->
          (forall pa, ⟦mref j of p X ⟧ gc_deps ⍮ gc_stack ↘ (hd, k', pa) ->
             entry_readable (de_term v (entry_type_value (d_ind hd k' (pa ++ bs))))) ->
          ind_member D j = Some Mj -> im_is_rview Mj = false -> im_ref p j Mj = (hd, k') ->
          ⟦ Ps ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ bs -> tele_rel (nr j) (List.rev (im_nparams Mj)) base bs ->
          List.Forall2 (fun v t => entry_readable (de_term v t)) (bs ++ v :: nil)
            (List.map snd (tele_entries (decl_env D X) (List.rev (im_nparams Mj)) bs
                             ++ (v, entry_type_shape p X ρ (pt_self j Ps)) :: nil)).
      Proof.
        intros * Ha Hok Hrd HM Hrv Hr Eb Hn.
        destruct (mref_at_ref _ _ _ _ _ Hok HM Hrv Hr) as [cups Hc].
        rewrite List.map_app; apply List.Forall2_app;
          [ exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ Hass Ha HM Hn) | constructor; [| constructor ] ].
        eapply entry_readable_at_evaluated; [ apply eval_entry_type_shape; econstructor; [ exact Eb | exact Hc ] |].
        exact (Hrd _ Hc).
      Qed.

      (** A neutral of a member but a record view is one at any bases: the
          bases constrain recursive arguments only. *)
      Lemma grp_rel_neut_rebase : forall j Mj u u' w w' ns ns' hd k' as1 as2 e e',
          ind_member D j = Some Mj -> im_is_rview Mj = false ->
          grp_rel p D ups nr ar dr j u u' ns ns' (⇑ (d_ind hd k' as1) e) (⇑ (d_ind hd k' as2) e') ->
          grp_rel p D ups nr ar dr j w w' ns ns' (⇑ (d_ind hd k' as1) e) (⇑ (d_ind hd k' as2) e').
      Proof.
        intros * HM Hrv H; inversion H; subst; [ eapply ind_rel_neut; eassumption | no_rview_rel ].
      Qed.

      (** Stuck eliminators at related neutrals of a member are defined,
          their motives, at the types they store the neutrals at, related
          at [Rel] at the neutrals' own non-uniform parameters. *)
      Lemma neut_elim_motive : forall j Mj u u' ns ns' hd k' as1 as2 e e', ind_member D j = Some Mj -> im_is_rview Mj = false ->
          grp_rel p D ups nr ar dr j u u' ns ns' (⇑ (d_ind hd k' as1) e) (⇑ (d_ind hd k' as2) e') ->
          exists a a', ⟦elim ⇑ (d_ind hd k' as1) e at j of p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ ⇑ a (d_elim ρa Bksa p ua j as1 e) /\
            ⟦elim ⇑ (d_ind hd k' as2) e' at j of p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ ⇑ a' (d_elim ρb Bksb p ub j as2 e') /\
            DF a ≈ a' ∈ per_univ_elem i ↘ Rel j (List.skipn (im_unu D Mj) as1) (⇑ (d_ind hd k' as1) e)
                                                (List.skipn (im_unu D Mj) as2) (⇑ (d_ind hd k' as2) e').
      Proof.
        intros * HM Hrv Hm.
        pose proof Hm as Hm0.
        inversion Hm0 as [| j0 Mj0 hd0 k0 ns0 ns0' as1' as2' e0 e0' u0 u0' HM0 Hrv0 Hr Hn L1 L2 Hs1 Hs2 He |]; subst;
          [| no_rview_rel ].
        rewrite HM in HM0; injection HM0 as <-.
        destruct (im_ref_target _ _ _ _ HM Hr) as (Dq & Mk & Hq & HMk & Hnn & Hnu).
        destruct (HbA _ _ HM Hrv) as [ba Ha]; destruct (HbB _ _ HM Hrv) as [bb Hb'].
        pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HM Hm Hs1 Hs2) as Hm1.
        destruct Hups as [La Lb Aa Ab Ma Mb _ Ra Rb _ _ _].
        destruct (mref_at_ref _ _ _ _ _ Ma HM Hrv Hr) as [cupsa Hca].
        destruct (mref_at_ref _ _ _ _ _ Mb HM Hrv Hr) as [cupsb Hcb].
        pose proof (grp_rel_neut_rebase _ _ _ _ ua ub _ _ _ _ _ _ _ _ HM Hrv Hm1) as Hm2.
        (** The motives' entries at the types the neutrals are stored at
            read back: the non-uniform parameters by admissibility, the
            neutrals by [elim_ups_ok]. *)
        assert (Hra : List.Forall2 (fun v t => entry_readable (de_term v t))
                        (List.skipn (im_unu D Mj) as1 ++ ⇑ (d_ind hd k' as1) e :: nil)
                        (List.map snd (motive_entries D Mj ua (List.skipn (im_unu D Mj) as1)
                                         (d_ind hd k' (cupsa ++ List.skipn (im_unu D Mj) as1)) (⇑ (d_ind hd k' as1) e)))).
        { unfold motive_entries; rewrite List.map_app; apply List.Forall2_app;
            [ exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ Hass Aa HM Hs1)
            | constructor; [ exact (Ra _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Aa Ab Hca Hm2
                                       (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI j Mj HM _ _ Hs1))
                           | constructor ] ]. }
        assert (Hrb : List.Forall2 (fun v t => entry_readable (de_term v t))
                        (List.skipn (im_unu D Mj) as2 ++ ⇑ (d_ind hd k' as2) e' :: nil)
                        (List.map snd (motive_entries D Mj ub (List.skipn (im_unu D Mj) as2)
                                         (d_ind hd k' (cupsb ++ List.skipn (im_unu D Mj) as2)) (⇑ (d_ind hd k' as2) e')))).
        { unfold motive_entries; rewrite List.map_app; apply List.Forall2_app;
            [ exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ Hass Ab HM Hs2)
            | constructor; [ exact (Rb _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Aa Ab Hcb Hm2
                                       (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI j Mj HM _ _ Hs2))
                           | constructor ] ]. }
        destruct (Hmot _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Ha Hb' Hm1 Hra Hrb) as (a & a' & Ea & Ea' & HR).
        rewrite motive_entries_combine in Ea, Ea'.
        exists a, a'; split; [| split ]; [| | exact HR ].
        - eapply eval_elim_neut; [ exact Hl | exact HM | exact Hr | exact Hq | exact HMk | | exact Ha
                                 | rewrite (HnmA _ _ _ HM Ha), Hnn; reflexivity | exact Hca | rewrite Hnu; exact Ea ].
          rewrite L1; unfold im_np; lia.
        - eapply eval_elim_neut; [ exact Hl | exact HM | exact Hr | exact Hq | exact HMk | | exact Hb'
                                 | rewrite (HnmB _ _ _ HM Hb'), Hnn; reflexivity | exact Hcb | rewrite Hnu; exact Ea' ].
          rewrite L2; unfold im_np; lia.
      Qed.

      (** A stuck eliminator at related neutrals of a member, when the stuck
          eliminators read back alike: related at the motive. *)
      Lemma neut_elim_rel : forall j Mj u u' ns ns' hd k' as1 as2 e e', ind_member D j = Some Mj -> im_is_rview Mj = false ->
          grp_rel p D ups nr ar dr j u u' ns ns' (⇑ (d_ind hd k' as1) e) (⇑ (d_ind hd k' as2) e') ->
          Dom d_elim ρa Bksa p ua j as1 e ≈ d_elim ρb Bksb p ub j as2 e' ∈ per_bot ->
          exists r r', ⟦elim ⇑ (d_ind hd k' as1) e at j of p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ r /\
            ⟦elim ⇑ (d_ind hd k' as2) e' at j of p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ r' /\
            Rel j ns (⇑ (d_ind hd k' as1) e) ns' (⇑ (d_ind hd k' as2) e') r r'.
      Proof.
        intros * HM Hrv Hm Hb.
        destruct (neut_elim_motive _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Hm) as (a & a' & Ea & Ea' & HR).
        exists (⇑ a (d_elim ρa Bksa p ua j as1 e)), (⇑ a' (d_elim ρb Bksb p ub j as2 e')); split; [ exact Ea | split; [ exact Ea' |] ].
        pose proof Hm as Hm0.
        inversion Hm0 as [| j0 Mj0 hd0 k0 ns0 ns0' as1' as2' e0 e0' u0 u0' HM0 Hrv0 Hr Hn L1 L2 Hs1 Hs2 He |]; subst;
          [| no_rview_rel ].
        rewrite HM in HM0; injection HM0 as <-.
        apply (motive_rel_move _ _ _ _ _ _ _ _ _ _ HM Hrv Hm Hs1 Hs2).
        exact (per_bot_then_per_elem HR Hb).
      Qed.

      (** A stuck eliminator at neutrals of a member is defined. *)
      Lemma neut_elim_eval : forall j Mj u u' ns ns' hd k' as1 as2 e e', ind_member D j = Some Mj -> im_is_rview Mj = false ->
          grp_rel p D ups nr ar dr j u u' ns ns' (⇑ (d_ind hd k' as1) e) (⇑ (d_ind hd k' as2) e') ->
          exists r r', ⟦elim ⇑ (d_ind hd k' as1) e at j of p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ r /\
            ⟦elim ⇑ (d_ind hd k' as2) e' at j of p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ r'.
      Proof.
        intros * HM Hrv Hm.
        destruct (neut_elim_motive _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Hm) as (a & a' & Ea & Ea' & _).
        eexists; eexists; split; [ exact Ea | exact Ea' ].
      Qed.

      (** *** The Recursive Results along the Leaf Paths

          A stuck eliminator at a neutral reaches its recursive arguments
          as neutrals, through applications and projections.  The
          recursive results of a neutral recursive argument along its leaf
          paths: their types ([ihty]) and the eliminator's results ([ih])
          are defined on each side, and results taken from either, path by
          path ([leaf_results]), are related: a fresh neutral of the type,
          or the eliminator's result where the stuck eliminator at the
          member the path ends in reads back alike ([elim_bot]). *)
      Definition elim_bot (j : nat) : Prop :=
        forall Mj hd k' as1 as2 e1 e1' w w' ns ns', ind_member D j = Some Mj -> im_is_rview Mj = false ->
          grp_rel p D ups nr ar dr j w w' ns ns' (⇑ (d_ind hd k' as1) e1) (⇑ (d_ind hd k' as2) e1') ->
          Dom d_elim ρa Bksa p ua j as1 e1 ≈ d_elim ρb Bksb p ub j as2 e1' ∈ per_bot.

      (** The recursive results of the arguments [v] and [v'] of shape
          [t], its components in [ρ1] and [ρ2], along paths flagged [bs]:
          the types and the eliminator's results on each side, and results
          taken from either related by [R]. *)
      #[warnings="-cannot-define-projection"]
      Record ih_pair (t : ptyp) (v v' : domain) (ρ1 ρ2 : env) (bs : list bool)
          (R : list domain -> list domain -> Prop) : Prop := mk_ih_pair
        { (** The types of the results, left *)
          ih_pair_tya : list domain
          (** The types of the results, right *)
        ; ih_pair_tyb : list domain
          (** The eliminator's results, left *)
        ; ih_pair_resa : list domain
          (** The eliminator's results, right *)
        ; ih_pair_resb : list domain
          (** The left types *)
        ; ih_pair_Ta : ⟦ihty v of t at p ua under ρa (blocks_motives Bksa) ⟧ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ ih_pair_tya
          (** The right types *)
        ; ih_pair_Tb : ⟦ihty v' of t at p ub under ρb (blocks_motives Bksb) ⟧ gc_deps ⍮ gc_stack ⍮ ρ2 ↘ ih_pair_tyb
          (** The left results *)
        ; ih_pair_Ra : ⟦ih v of t under p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ ih_pair_resa
          (** The right results *)
        ; ih_pair_Rb : ⟦ih v' of t under p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ ih_pair_resb
          (** One left type per path *)
        ; ih_pair_lta : List.length ih_pair_tya = List.length bs
          (** One right type per path *)
        ; ih_pair_ltb : List.length ih_pair_tyb = List.length bs
          (** One left result per path *)
        ; ih_pair_lra : List.length ih_pair_resa = List.length bs
          (** One right result per path *)
        ; ih_pair_lrb : List.length ih_pair_resb = List.length bs
          (** Results taken from either are related *)
        ; ih_pair_rel : forall out out', leaf_results bs ih_pair_tya ih_pair_tyb ih_pair_resa ih_pair_resb out out' ->
            R out out' }.

      (** Likewise of the arguments [vs] and [vs'] of kinds [gs]. *)
      #[warnings="-cannot-define-projection"]
      Record ihs_pair (gs : list carg) (vs vs' : list domain) (ρ1 ρ2 : env) (bs : list bool)
          (R : list domain -> list domain -> Prop) : Prop := mk_ihs_pair
        { (** The types of the results, left *)
          ihs_pair_tya : list domain
          (** The types of the results, right *)
        ; ihs_pair_tyb : list domain
          (** The eliminator's results, left *)
        ; ihs_pair_resa : list domain
          (** The eliminator's results, right *)
        ; ihs_pair_resb : list domain
          (** The left types *)
        ; ihs_pair_Ta : ⟦ihtys vs of gs at p ua under ρa (blocks_motives Bksa) ⟧ gc_deps ⍮ gc_stack ⍮ ρ1 ↘ ihs_pair_tya
          (** The right types *)
        ; ihs_pair_Tb : ⟦ihtys vs' of gs at p ub under ρb (blocks_motives Bksb) ⟧ gc_deps ⍮ gc_stack ⍮ ρ2 ↘ ihs_pair_tyb
          (** The left results *)
        ; ihs_pair_Ra : ⟦ihs vs of gs under p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ ihs_pair_resa
          (** The right results *)
        ; ihs_pair_Rb : ⟦ihs vs' of gs under p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ ihs_pair_resb
          (** One left type per path *)
        ; ihs_pair_lta : List.length ihs_pair_tya = List.length bs
          (** One right type per path *)
        ; ihs_pair_ltb : List.length ihs_pair_tyb = List.length bs
          (** One left result per path *)
        ; ihs_pair_lra : List.length ihs_pair_resa = List.length bs
          (** One right result per path *)
        ; ihs_pair_lrb : List.length ihs_pair_resb = List.length bs
          (** Results taken from either are related *)
        ; ihs_pair_rel : forall out out', leaf_results bs ihs_pair_tya ihs_pair_tyb ihs_pair_resa ihs_pair_resb out out' ->
            R out out' }.

      (** The results of a function shape along its paths at relevant
          domains take relevant arguments: a fresh neutral of a [Π] over
          the domain, or the eliminator's result function. *)
      Lemma leaf_results_pi_relevant : forall (l : list nat) bs out out' b b' f f' ρ ρ' B t,
          leaf_results bs
            (List.map (fun i => Πᵈ{ak_relevant} b (nil ↦ d_ihfam ρa (blocks_motives Bksa) p ua ρ B t i f ⦂ entry_type_none) fam_cod) l)
            (List.map (fun i => Πᵈ{ak_relevant} b' (nil ↦ d_ihfam ρb (blocks_motives Bksb) p ub ρ' B t i f' ⦂ entry_type_none) fam_cod) l)
            (List.map (fun i => d_ihfn ρa Bksa p ua t i f) l) (List.map (fun i => d_ihfn ρb Bksb p ub t i f') l) out out' ->
          domain_kind b = ak_relevant -> domain_kind b' = ak_relevant ->
          List.Forall (fun r => arg_kind gc_deps gc_stack r = ak_relevant) out /\
          List.Forall (fun r => arg_kind gc_deps gc_stack r = ak_relevant) out'.
      Proof.
        induction l as [| x l IH]; intros * H Hb Hb'; cbn [List.map] in H.
        - inversion H; subst; split; constructor.
        - inversion H as [| bs0 ? ? ? ? ? ? ? ? e e' o o' He H0 | bs0 ? ? ? ? ? ? ? ? o o' H0]; subst;
            destruct (IH _ _ _ _ _ _ _ _ _ _ _ H0 Hb Hb') as [F1 F2]; (split; constructor; [| exact F1 | | exact F2 ]);
            try reflexivity.
          + cbn [domain_kind arg_kind]; exact Hb.
          + cbn [domain_kind arg_kind]; exact Hb'.
      Qed.

      (** The results of a function shape along its paths, applied to
          related arguments: from the same source as before, those of the
          rest at the function's values there. *)
      Lemma leaf_results_apply : forall (l : list nat) bs out out' b b' f f' fc fc' c c' ρ ρ' B t tc tc' rc rc',
          leaf_results bs
            (List.map (fun i => Πᵈ{ak_relevant} b (nil ↦ d_ihfam ρa (blocks_motives Bksa) p ua ρ B t i f ⦂ entry_type_none) fam_cod) l)
            (List.map (fun i => Πᵈ{ak_relevant} b' (nil ↦ d_ihfam ρb (blocks_motives Bksb) p ub ρ' B t i f' ⦂ entry_type_none) fam_cod) l)
            (List.map (fun i => d_ihfn ρa Bksa p ua t i f) l) (List.map (fun i => d_ihfn ρb Bksb p ub t i f') l) out out' ->
          $| f & c | gc_deps ⍮ gc_stack ↘ fc -> $| f' & c' | gc_deps ⍮ gc_stack ↘ fc' ->
          ⟦ihty fc of t at p ua under ρa (blocks_motives Bksa) ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↦ c ⦂ entry_type_closure B ρ ↘ tc ->
          ⟦ihty fc' of t at p ub under ρb (blocks_motives Bksb) ⟧ gc_deps ⍮ gc_stack ⍮ ρ' ↦ c' ⦂ entry_type_closure B ρ' ↘ tc' ->
          ⟦ih fc of t under p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ rc -> ⟦ih fc' of t under p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ rc' ->
          (forall i, In i l -> i < List.length tc /\ i < List.length tc' /\ i < List.length rc /\ i < List.length rc') ->
          Dom ⇓ b c ≈ ⇓ b' c' ∈ per_top ->
          exists outc outc', List.Forall2 (fun g x => $| g & c | gc_deps ⍮ gc_stack ↘ x) out outc /\
            List.Forall2 (fun g x => $| g & c' | gc_deps ⍮ gc_stack ↘ x) out' outc' /\
            leaf_results bs (List.map (fun i => List.nth i tc d_True) l) (List.map (fun i => List.nth i tc' d_True) l)
              (List.map (fun i => List.nth i rc d_True) l) (List.map (fun i => List.nth i rc' d_True) l) outc outc'.
      Proof.
        induction l as [| x l IH]; intros * H Ef Ef' Tc Tc' Rc Rc' Hi Htop; cbn [List.map] in H |- *.
        - inversion H; subst; exists nil, nil; split; [ constructor | split; constructor ].
        - destruct (Hi x ltac:(left; reflexivity)) as (L1 & L2 & L3 & L4).
          inversion H as [| bs0 ? ? ? ? ? ? ? ? e e' o o' He H0 | bs0 ? ? ? ? ? ? ? ? o o' H0]; subst;
            destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 Ef Ef' Tc Tc' Rc Rc'
                        ltac:(intros i0 Hi0; apply Hi; right; exact Hi0) Htop) as (oc & oc' & F1 & F2 & Hr).
          + exists (⇑ (List.nth x tc d_True) (e $ᵈ ⇓ b c) :: oc), (⇑ (List.nth x tc' d_True) (e' $ᵈ ⇓ b' c') :: oc').
            split; [| split ]; [ constructor; [| exact F1 ] | constructor; [| exact F2 ] | constructor; [| exact Hr ] ].
            * apply eval_app_neut; [ constructor |]; eapply eval_fam_cod_ihfam; [ exact Ef | exact Tc | apply List.nth_error_nth'; exact L1 ].
            * apply eval_app_neut; [ constructor |]; eapply eval_fam_cod_ihfam; [ exact Ef' | exact Tc' | apply List.nth_error_nth'; exact L2 ].
            * exact (per_bot_app _ _ _ _ He Htop).
          + exists (List.nth x rc d_True :: oc), (List.nth x rc' d_True :: oc').
            split; [| split ]; [ constructor; [| exact F1 ] | constructor; [| exact F2 ] | constructor; exact Hr ].
            * eapply eval_app_ihfn; [ exact Ef | exact Rc | apply List.nth_error_nth'; exact L3 ].
            * eapply eval_app_ihfn; [ exact Ef' | exact Rc' | apply List.nth_error_nth'; exact L4 ].
      Qed.

      Lemma con_args_rel_length : forall okr k u u' pre pre' Ts gs vs vs',
          con_args_rel p D okr nr ar dr k u u' pre pre' Ts gs vs vs' ->
          List.length vs = List.length gs /\ List.length vs' = List.length gs.
      Proof.
        intros * H; induction H; cbn; try (destruct IHcon_args_rel; split; f_equal; assumption); split; reflexivity.
      Qed.

      (** The recursive results along the leaf paths of neutral recursive
          arguments, by induction on their relation: at a record view
          through its fields' projections, at a domain through the
          applications to related arguments. *)
      Lemma ih_leaves_all :
        (forall k u u' ns ns' v v', grp_rel p D ups nr ar dr k u u' ns ns' v v' ->
           u = ua -> u' = ub -> is_neut v -> is_neut v' ->
           forall Mk qr Is fl c gs ws ws', ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
           im_cons Mk = (c, gs) :: nil ->
           ⟦projs fl of v ⟧ gc_deps ⍮ gc_stack ↘ ws -> ⟦projs fl of v' ⟧ gc_deps ⍮ gc_stack ↘ ws' ->
           forall bs, leaf_flags_ok elim_bot bs (cargs_mems D gs) ->
           ihs_pair gs ws ws' (decl_env D ua) (decl_env D ub) bs (rec_results_rel k ua ub nil nil nil gs ws ws')) /\
        (forall k u u' pre pre' Ts gs vs vs', con_args_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts gs vs vs' ->
           u = ua -> u' = ub -> List.length pre = List.length Ts -> List.length pre' = List.length Ts ->
           List.Forall is_neut vs -> List.Forall is_neut vs' -> cargs_doms_ok ua ub k pre pre' Ts gs vs vs' ->
           forall bs, leaf_flags_ok elim_bot bs (cargs_mems D gs) ->
           ihs_pair gs vs vs' (components_env D ua Ts pre) (components_env D ub Ts pre') bs
             (rec_results_rel k ua ub pre pre' Ts gs vs vs')) /\
        (forall k u u' pre pre' Ts t v v', rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts t v v' ->
           u = ua -> u' = ub -> List.length pre = List.length Ts -> List.length pre' = List.length Ts ->
           is_neut v -> is_neut v' -> shape_doms_ok ua ub k pre pre' Ts t ->
           forall bs, leaf_flags_ok elim_bot bs (shape_mems D t) ->
           ih_pair t v v' (components_env D ua Ts pre) (components_env D ub Ts pre') bs (rec_result_rel k ua ub pre pre' Ts t v v')) /\
        (forall k u u' pre pre' Ts t f c f' c', rec_arg_app_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts t f c f' c' ->
           forall fc fc', $| f & c | gc_deps ⍮ gc_stack ↘ fc -> $| f' & c' | gc_deps ⍮ gc_stack ↘ fc' ->
           u = ua -> u' = ub -> List.length pre = List.length Ts -> List.length pre' = List.length Ts ->
           is_neut f -> is_neut f' -> shape_doms_ok ua ub k pre pre' Ts t ->
           forall bs, leaf_flags_ok elim_bot bs (shape_mems D t) ->
           ih_pair t fc fc' (components_env D ua Ts pre) (components_env D ub Ts pre') bs (rec_result_rel k ua ub pre pre' Ts t fc fc')).
      Proof.
        unfold grp_rel; apply ind_rel_mut_ind_all.
        - (** A constructor: no record view. *)
          intros k Mk hd k' ns ns' c gs bs bs' vs vs' u u' HM Hrv; intros;
            match goal with H1 : ind_member D k = Some ?M, H2 : im_head ?M = mh_record _ _ _ |- _ =>
              rewrite HM in H1; injection H1 as <-; exfalso; exact (not_rview_record _ _ _ _ Hrv H2) end.
        - (** A neutral of a member with a block: no record view. *)
          intros k Mk hd k' ns ns' as1 as2 m m' u u' HM Hrv; intros;
            match goal with H1 : ind_member D k = Some ?M, H2 : im_head ?M = mh_record _ _ _ |- _ =>
              rewrite HM in H1; injection H1 as <-; exfalso; exact (not_rview_record _ _ _ _ Hrv H2) end.
        - (** A record view: its fields, at the projections. *)
          intros k Mk qr Is fl c gs v vs v' vs' u u' HM Hh Hnp Hcs Ep Ep' Hn Hc IH -> -> Hv Hv' Mk' qr' Is' fl' c' gs' ws ws'
            HM' Hh' Hcs' Ew Ew' bs Hbs.
          rewrite HM in HM'; injection HM' as <-; rewrite Hh in Hh'; injection Hh' as <- <- <-.
          rewrite Hcs in Hcs'; injection Hcs' as <- <-.
          pose proof (functional_eval_projs _ _ _ _ Ep Ew) as <-; pose proof (functional_eval_projs _ _ _ _ Ep' Ew') as <-.
          destruct (con_args_rel_length _ _ _ _ _ _ _ _ _ _ Hc) as [L1 L2].
          destruct Hups as [_ _ Ca Cb _ _ _ _ _ _ _ _].
          pose proof (rview_fields_doms ua ub Ca Cb k Mk qr Is fl c gs vs vs' HM Hh Hcs L1 L2 Hn) as Hd.
          exact (IH eq_refl eq_refl eq_refl eq_refl (is_neut_projs _ _ _ Ep Hv) (is_neut_projs _ _ _ Ep' Hv') Hd bs Hbs).
        - (** No argument. *)
          intros * -> -> _ _ _ _ _ bs Hbs; cbn [cargs_mems] in Hbs; inversion Hbs; subst.
          refine (mk_ihs_pair _ _ _ _ _ _ _ nil nil nil nil _ _ _ _ _ _ _ _ _); try reflexivity; try constructor.
          intros out out' Ho; inversion Ho; subst; constructor.
        - (** A non-recursive argument joins the prefixes. *)
          intros * Hc IH -> -> Lp Lp' Hv Hv' Hd bs Hbs.
          inversion Hv; inversion Hv'; inversion Hd; subst.
          destruct (IH eq_refl eq_refl ltac:(rewrite !List.length_app; cbn; lia) ltac:(rewrite !List.length_app; cbn; lia)
                      ltac:(assumption) ltac:(assumption) ltac:(assumption) bs Hbs)
            as [tya tyb resa resb Ta Tb Ra Rb La Lb Lc Ld Hr].
          rewrite (components_env_snoc _ _ _ _ _ _ _ Lp) in Ta; rewrite (components_env_snoc _ _ _ _ _ _ _ Lp') in Tb.
          refine (mk_ihs_pair _ _ _ _ _ _ _ tya tyb resa resb _ _ _ _ La Lb Lc Ld _);
            [ constructor; exact Ta | constructor; exact Tb | constructor; exact Ra | constructor; exact Rb |].
          intros out out' Ho; constructor; exact (Hr _ _ Ho).
        - (** A recursive argument: its paths, then the rest's. *)
          intros * Hr IH1 Hc IH2 -> -> Lp Lp' Hv Hv' Hd bs Hbs.
          inversion Hv as [| ? ? Hv0 Hvs]; inversion Hv' as [| ? ? Hv0' Hvs']; inversion Hd as [| | ? ? ? ? ? ? ? ? ? Hd1 Hd2]; subst.
          cbn [cargs_mems] in Hbs; destruct (leaf_flags_ok_app _ _ _ _ Hbs) as (bs1 & bs2 & -> & Hb1 & Hb2).
          destruct (IH1 eq_refl eq_refl Lp Lp' Hv0 Hv0' Hd1 bs1 Hb1) as [tya1 tyb1 resa1 resb1 Ta1 Tb1 Ra1 Rb1 La1 Lb1 Lc1 Ld1 Hr1].
          destruct (IH2 eq_refl eq_refl Lp Lp' Hvs Hvs' Hd2 bs2 Hb2) as [tya2 tyb2 resa2 resb2 Ta2 Tb2 Ra2 Rb2 La2 Lb2 Lc2 Ld2 Hr2].
          refine (mk_ihs_pair _ _ _ _ _ _ _ (tya1 ++ tya2) (tyb1 ++ tyb2) (resa1 ++ resa2) (resb1 ++ resb2) _ _ _ _ _ _ _ _ _);
            [ econstructor; eassumption | econstructor; eassumption | econstructor; eassumption | econstructor; eassumption
            | rewrite !List.length_app; lia | rewrite !List.length_app; lia | rewrite !List.length_app; lia
            | rewrite !List.length_app; lia |].
          intros out out' Ho.
          destruct (leaf_results_app_inv _ _ _ _ _ _ _ _ _ _ _ _ Ho La1 Lb1 Lc1 Ld1) as (o1 & o2 & o1' & o2' & -> & -> & Ho1 & Ho2).
          pose proof (leaf_flags_ok_length _ _ _ Hb1) as Lb1'; rewrite length_shape_mems in Lb1'.
          destruct (leaf_results_length _ _ _ _ _ _ _ Ho1) as [Lo1 Lo1'].
          econstructor; [ lia | lia | exact (Hr1 _ _ Ho1) | exact (Hr2 _ _ Ho2) ].
        - (** The end of a shape. *)
          intros Ps u Ts pre bs0 u' pre' bs0' j v v' k Eb Eb' Hk Hk' Hi IH -> -> _ _ Hv Hv' _ bs Hbs.
          pose proof Hi as Hi0.
          inversion Hi0 as [? Mj ? ? ? ? c gs ? ? vs vs' ? ? HM Hrv Href Hn Hc L1 L2 Hs1 Hs2 Ha Hca
                           | ? Mj hd k' ? ? as1 as2 e e' ? ? HM Hrv Href Hn L1 L2 Hs1 Hs2 He
                           | ? Mj qr Is fl c gs ? ws ? ws' ? ? HM Hh Hnp Hcs Ew Ew' Hn Hca]; subst.
          + exfalso; destruct Hv as (? & ? & Hv); discriminate Hv.
          + (** A member with a block: the motive, or the eliminator.  The
                motive's entries, the shape's parameters and the neutral
                at the shape's type, read back. *)
            rewrite (shape_mems_self _ _ _ _ HM Hrv) in Hbs.
            pose proof Hups as Hups0; destruct Hups0 as [_ _ Aa Ab Ma Mb _ Ra Rb _ _].
            pose proof Hk as [basea _ Hka]; pose proof Hk' as [baseb _ Hkb].
            unfold nparams_tele_rel in Hka, Hkb; rewrite HM in Hka, Hkb.
            pose proof (motive_self_entries_readable ua (components_env D ua Ts pre) j Mj Ps bs0 basea hd k' _ Aa Ma
                          (fun pa Hc => Ra j Mj hd k' pa _ _ _ _ _ _ _ HM Hrv Aa Ab Hc Hi
                                          (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI j Mj HM _ _ Hka))
                          HM Hrv Href Eb Hka) as Hra.
            pose proof (motive_self_entries_readable ub (components_env D ub Ts pre') j Mj Ps bs0' baseb hd k' _ Ab Mb
                          (fun pa Hc => Rb j Mj hd k' pa _ _ _ _ _ _ _ HM Hrv Aa Ab Hc Hi
                                          (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI j Mj HM _ _ Hkb))
                          HM Hrv Href Eb' Hkb) as Hrb.
            inversion Hbs as [| ? ? ? Hb0 | ? ? ? Hbot Hb0]; subst; inversion Hb0; subst;
            destruct (HbA _ _ HM Hrv) as [ba Ha]; destruct (HbB _ _ HM Hrv) as [bb Hb];
            destruct (Hmot _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Ha Hb Hi Hra Hrb) as (a & a' & Ea & Ea' & HR);
            rewrite combine_tele_entries_snoc in Ea, Ea';
            destruct (neut_elim_eval _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Hi) as (r & r' & Er & Er');
            (refine (mk_ih_pair _ _ _ _ _ _ _ (a :: nil) (a' :: nil) (r :: nil) (r' :: nil) _ _ _ _ _ _ _ _ _);
             [ .. | reflexivity | reflexivity | reflexivity | reflexivity |];
             [ eapply eval_ihty_self; [ exact Hl | exact HM | exact Hrv | exact Eb | rewrite (nth_blocks_motives _ _ _ Ha); exact Ea ]
             | eapply eval_ihty_self; [ exact Hl | exact HM | exact Hrv | exact Eb' | rewrite (nth_blocks_motives _ _ _ Hb); exact Ea' ]
             | eapply eval_ih_self; [ exact Hl | exact HM | exact Hrv | exact Er ]
             | eapply eval_ih_self; [ exact Hl | exact HM | exact Hrv | exact Er' ] |]);
            intros out out' Hout; inversion Hout as [| ? ? ? ? ? ? ? ? ? e2 e2' o o' He2 Ho0 | ? ? ? ? ? ? ? ? ? o o' Ho0]; subst;
              inversion Ho0; subst.
            * eapply rec_result_self; [ exact HM | exact Hrv | exact Eb | exact Eb' |].
              exact (per_bot_then_per_elem HR He2).
            * destruct (neut_elim_rel _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Hi (Hbot _ _ _ _ _ _ _ _ _ _ _ HM Hrv Hi))
                as (r0 & r0' & Er0 & Er0' & HR0).
              pose proof (functional_eval_elim _ _ _ _ _ _ _ _ Er Er0) as <-.
              pose proof (functional_eval_elim _ _ _ _ _ _ _ _ Er' Er0') as <-.
              eapply rec_result_self; [ exact HM | exact Hrv | exact Eb | exact Eb' | exact HR0 ].
          + (** A record view: its fields' results, at the projections. *)
            destruct (rview_struct_con _ _ _ Hrs _ _ _ _ _ HM Hh) as (gs0 & Hcs0 & Lfl).
            rewrite Hcs in Hcs0; injection Hcs0 as _ <-.
            rewrite (shape_mems_rview _ _ _ _ _ _ _ _ _ Hlc HM Hh Hcs ltac:(lia)) in Hbs.
            destruct (IH eq_refl eq_refl Hv Hv' _ _ _ _ _ _ _ _ HM Hh Hcs Ew Ew' bs Hbs)
              as [tya tyb resa resb Ta Tb Ra Rb La Lb Lc Ld Hr].
            refine (mk_ih_pair _ _ _ _ _ _ _ tya tyb resa resb _ _ _ _ La Lb Lc Ld _);
              [ eapply eval_ihty_rview; eassumption | eapply eval_ihty_rview; eassumption
              | eapply eval_ih_rview; eassumption | eapply eval_ih_rview; eassumption |].
            intros out out' Ho; eapply rec_result_rview; [ exact HM | exact Hh | exact Hcs | exact Ew | exact Ew' | exact (Hr _ _ Ho) ].
        - (** A domain: at related arguments. *)
          intros k pre Ts B u u' pre' t f f' Hr IH _ _ -> -> Lp Lp' Hf Hf' Hd bs Hbs.
          inversion Hd as [| ? ? ? ? ? b b' Eb Eb' Htop Hrest Hdr Hdr' _ _]; subst.
          rewrite shape_mems_pi in Hbs.
          pose proof (leaf_flags_ok_length _ _ _ Hbs) as Lbs; rewrite length_shape_mems in Lbs.
          set (N := List.length (shape_leaves (rview_leaves D) 0 t)) in *.
          refine (mk_ih_pair _ _ _ _ _ _ _
                    (List.map (fun i => Πᵈ{ak_relevant} b (nil ↦ d_ihfam ρa (blocks_motives Bksa) p ua (components_env D ua Ts pre) B t i f
                                                 ⦂ entry_type_none) fam_cod)
                       (List.seq 0 N))
                    (List.map (fun i => Πᵈ{ak_relevant} b' (nil ↦ d_ihfam ρb (blocks_motives Bksb) p ub (components_env D ub Ts pre') B t i f'
                                                  ⦂ entry_type_none) fam_cod)
                       (List.seq 0 N))
                    (List.map (fun i => d_ihfn ρa Bksa p ua t i f) (List.seq 0 N))
                    (List.map (fun i => d_ihfn ρb Bksb p ub t i f') (List.seq 0 N)) _ _ _ _ _ _ _ _ _);
            [ eapply eval_ihty_pi; [ exact Hl | exact Eb ] | eapply eval_ihty_pi; [ exact Hl | exact Eb' ]
            | eapply eval_ih_pi; exact Hl | eapply eval_ih_pi; exact Hl
            | rewrite List.length_map, List.length_seq; lia | rewrite List.length_map, List.length_seq; lia
            | rewrite List.length_map, List.length_seq; lia | rewrite List.length_map, List.length_seq; lia |].
          intros out out' Ho.
          destruct (leaf_results_pi_relevant _ _ _ _ _ _ _ _ _ _ _ _ Ho Hdr Hdr') as [Fo Fo'].
          constructor; [| exact Fo | exact Fo' ].
          intros c c' Hcc.
          pose proof (Hr c c' Hcc) as Ha; inversion Ha as [? ? fc ? ? fc' ? ? ? ? ? ? ? Ef Ef' Hfc]; subst.
          destruct (IH c c' Hcc fc fc' Ef Ef' eq_refl eq_refl ltac:(rewrite !List.length_app; cbn; lia)
                      ltac:(rewrite !List.length_app; cbn; lia) Hf Hf' (Hrest c c' Hcc) bs Hbs)
            as [tyc tyc' rc rc' Tc Tc' Rc Rc' Lc1 Lc2 Lc3 Lc4 Hrc].
          rewrite (components_env_snoc _ _ _ _ _ _ _ Lp) in Tc; rewrite (components_env_snoc _ _ _ _ _ _ _ Lp') in Tc'.
          destruct (leaf_results_apply (List.seq 0 N) bs out out' b b' f f' fc fc' c c' _ _ B t tyc tyc' rc rc' Ho Ef Ef'
                      Tc Tc' Rc Rc' ltac:(intros x Hx; apply List.in_seq in Hx; lia) (Htop c c' Hcc))
            as (oc & oc' & F1 & F2 & Hoc).
          replace N with (List.length tyc) in Hoc at 1 by lia.
          rewrite map_nth_seq_all in Hoc.
          replace N with (List.length tyc') in Hoc at 1 by lia.
          rewrite map_nth_seq_all in Hoc.
          replace N with (List.length rc) in Hoc at 1 by lia.
          rewrite map_nth_seq_all in Hoc.
          replace N with (List.length rc') in Hoc at 1 by lia.
          rewrite map_nth_seq_all in Hoc.
          econstructor; [ exact Ef | exact Ef' | exact F1 | exact F2 | exact (Hrc _ _ Hoc) ].
        - (** An application: the rest at the function's values. *)
          intros * Ef Ef' Hr IH fc fc' Ec Ec' -> -> Lp Lp' Hf Hf' Hd bs Hbs.
          pose proof (functional_eval_app _ _ _ _ Ef Ec) as <-; pose proof (functional_eval_app _ _ _ _ Ef' Ec') as <-.
          exact (IH eq_refl eq_refl Lp Lp' (is_neut_app _ _ _ Ef Hf) (is_neut_app _ _ _ Ef' Hf') Hd bs Hbs).
      Qed.

      (** *** The Readback of the Entries a Branch Binds

          A branch binds its constructor's recursive arguments at their
          shapes' types and their recursive results at their types
          ([branch_entries]), and its environment's entries read back
          there.  At a function shape the readback is η-directed: for
          [W (A : Type) (B : A → Type)] with [sup (a : A) (f : B a → W A B)],
          the branch of [sup] binds [f] at [Π (B a) (W A B)], where [f]
          reads back as [λ x. f x], [f x] read at [W A B]: an element
          again, as the fresh variable [x] of the domain is related to
          itself ([shape_doms_ok], from [rel_dom_apps_vars]), and the
          domain reads back as a type ([rel_dom_apps_types]).  At the end of
          a shape an element reads back at its member's type
          ([elim_ups_ok]), and a recursive result at its motive's instance,
          whose relation it is an element of ([Hmot]). *)

      (** The member of two related elements. *)
      Lemma grp_rel_member : forall j u u' ns ns' v v', grp_rel p D ups nr ar dr j u u' ns ns' v v' ->
          exists Mj, ind_member D j = Some Mj.
      Proof using. intros * H; inversion H; subst; eexists; eassumption. Qed.

      (** A record view's elements have no non-uniform parameters. *)
      Lemma grp_rel_rview_nil : forall j Mj qr Is fl u u' ns ns' v v', ind_member D j = Some Mj -> im_head Mj = mh_record qr Is fl ->
          grp_rel p D ups nr ar dr j u u' ns ns' v v' -> ns = nil /\ ns' = nil.
      Proof using.
        intros * HM Hh H; inversion H; subst; [ no_rview_rel | no_rview_rel | split; reflexivity ].
      Qed.

      (** The arguments of a function shape, applied. *)
      Lemma rec_arg_rel_pi_inv : forall k u u' pre pre' Ts B t f f',
          rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts (pt_pi B t) f f' ->
          forall c c', dr k pre Ts B c c' -> exists r r', $| f & c | gc_deps ⍮ gc_stack ↘ r /\ $| f' & c' | gc_deps ⍮ gc_stack ↘ r' /\
            rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr k u u' (pre ++ c :: nil) (pre' ++ c' :: nil) (Ts ++ ce_ass ak_relevant B :: nil) t r r'.
      Proof using.
        intros * H c c' Hc; inversion H as [| ? ? ? ? ? ? ? ? ? ? Hf _ _]; subst.
        destruct (Hf c c' Hc) as [? ? r ? ? r' ? ? ? ? ? ? ? Er Er' Hr]; exists r, r'; auto.
      Qed.

      (** A function of a shape and an argument, applied. *)
      Lemma rec_arg_app_rel_inv : forall k u u' pre pre' Ts t f c f' c',
          rec_arg_app_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts t f c f' c' ->
          exists r r', $| f & c | gc_deps ⍮ gc_stack ↘ r /\ $| f' & c' | gc_deps ⍮ gc_stack ↘ r' /\
            rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts t r r'.
      Proof using. intros * H; destruct H as [? ? r ? ? r' ? ? ? ? ? ? ? Er Er' Hr]; exists r, r'; auto. Qed.

      (** A non-recursive argument joins the prefixes. *)
      Lemma con_args_rel_arg_inv : forall k u u' pre pre' Ts r A gs v v' vs vs',
          con_args_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts (ca_arg r A :: gs) (v :: vs) (v' :: vs') ->
          con_args_rel p D (admissible_index_at D ups nr) nr ar dr k u u' (pre ++ v :: nil) (pre' ++ v' :: nil) (Ts ++ ce_ass r A :: nil) gs vs vs'.
      Proof using. intros * H; inversion H; subst; assumption. Qed.

      (** A recursive argument, by its shape, then the rest. *)
      Lemma con_args_rel_rec_inv : forall k u u' pre pre' Ts t gs v v' vs vs',
          con_args_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts (ca_rec t :: gs) (v :: vs) (v' :: vs') ->
          rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts t v v' /\
          con_args_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts gs vs vs'.
      Proof using. intros * H; inversion H; subst; split; assumption. Qed.

      (** Likewise of the domains. *)
      Lemma cargs_doms_ok_arg_inv : forall X Y k pre pre' Ts r A gs v v' vs vs',
          cargs_doms_ok X Y k pre pre' Ts (ca_arg r A :: gs) (v :: vs) (v' :: vs') ->
          cargs_doms_ok X Y k (pre ++ v :: nil) (pre' ++ v' :: nil) (Ts ++ ce_ass r A :: nil) gs vs vs'.
      Proof using. intros * H; inversion H; subst; assumption. Qed.

      Lemma cargs_doms_ok_rec_inv : forall X Y k pre pre' Ts t gs v v' vs vs',
          cargs_doms_ok X Y k pre pre' Ts (ca_rec t :: gs) (v :: vs) (v' :: vs') ->
          shape_doms_ok X Y k pre pre' Ts t /\ cargs_doms_ok X Y k pre pre' Ts gs vs vs'.
      Proof using. intros * H; inversion H; subst; split; assumption. Qed.

      (** The domain of a function shape. *)
      Lemma shape_doms_ok_pi_inv : forall X Y k pre pre' Ts B t, shape_doms_ok X Y k pre pre' Ts (pt_pi B t) ->
          exists b b', ⟦ B ⟧ gc_deps ⍮ gc_stack ⍮ components_env D X Ts pre ↘ b /\
            ⟦ B ⟧ gc_deps ⍮ gc_stack ⍮ components_env D Y Ts pre' ↘ b' /\
            (forall c c', dr k pre Ts B c c' -> shape_doms_ok X Y k (pre ++ c :: nil) (pre' ++ c' :: nil) (Ts ++ ce_ass ak_relevant B :: nil) t) /\
            Dom b ≈ b' ∈ per_top_typ /\ (forall s, dr k pre Ts B (⇑! b s) (⇑! b' s)).
      Proof using.
        intros * H; inversion H as [| ? ? ? ? ? b b' Eb Eb' _ Hrest _ _ Hty Hvar]; subst.
        exists b, b'; auto.
      Qed.

      (** Related arguments of a shape at the bases [ua] and [ub] read back
          at the shape's types there. *)
      (** Two admissible indices at the same components are related. *)
      Lemma admissible_indices_rel : forall j Mj pre Ts Ps bs1 bs2, ind_member D j = Some Mj ->
          admissible_index_at D ups nr j pre Ts Ps bs1 -> admissible_index_at D ups nr j pre Ts Ps bs2 ->
          tele_rel (nr j) (List.rev (im_nparams Mj)) bs1 bs2.
      Proof using p Hass HnP HnI HaP HaI HdP HdI.
        intros * HM [b1 E1 R1] [b2 E2 R2].
        pose proof (functional_eval_exps' _ _ _ _ E1 E2) as <-.
        unfold nparams_tele_rel in R1, R2; rewrite HM in R1, R2.
        exact (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI j Mj HM _ _ _
                 (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI j Mj HM _ _ R1) R2).
      Qed.

      (** Related arguments of a shape at any admissible bases [u] and
          [u'] read back at the shape's types at [ua] and [ub]. *)
      Lemma shape_elements_readable : forall t k u u' pre pre' Ts v v',
          adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' ->
          List.length pre = List.length Ts -> List.length pre' = List.length Ts ->
          rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts t v v' ->
          shape_doms_ok ua ub k pre pre' Ts t ->
          entry_readable (de_term v (entry_type_shape p ua (components_env D ua Ts pre) t)) /\
          entry_readable (de_term v' (entry_type_shape p ub (components_env D ub Ts pre') t)).
      Proof using Hl Hass HnP HnI HaP HaI HdP HdI Hups.
        induction t as [j Ps | B t IH]; intros * Hau Hau' Lp Lp' Hr Hd.
        - inversion Hr as [? ? ? ? bs ? ? bs' ? ? ? ? _ _ Hk Hk' Hi |]; subst.
          inversion Hd as [? ? ? ? ? bsX bsY EX EY AX AY |]; subst.
          pose proof Hups as [_ _ _ _ Ma Mb _ Ra Rb Va Vb _].
          destruct (grp_rel_member _ _ _ _ _ _ _ Hi) as [Mj HM].
          destruct (im_head Mj) as [pm | qc kc Is vm | qr Is fl] eqn:Hh.
          1-2: assert (Hrv : im_is_rview Mj = false) by (unfold im_is_rview; rewrite Hh; reflexivity);
            destruct (proj1 (Ma j Mj HM) Hrv) as [[[hd k0] pa] Hma];
            destruct (proj1 (Mb j Mj HM) Hrv) as [[[hd' k0'] pb] Hmb];
            pose proof (admissible_indices_rel _ _ _ _ _ _ _ HM Hk AX) as HbX;
            pose proof (admissible_indices_rel _ _ _ _ _ _ _ HM Hk' AY) as HbY;
            split; [ eapply entry_readable_at_evaluated;
                     [ apply eval_entry_type_shape; eapply eval_shape_type_self; [ exact EX | exact Hma ]
                     | exact (Ra _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Hau Hau' Hma Hi HbX) ]
                   | eapply entry_readable_at_evaluated;
                     [ apply eval_entry_type_shape; eapply eval_shape_type_self; [ exact EY | exact Hmb ]
                     | exact (Rb _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Hau Hau' Hmb Hi HbY) ] ].
          destruct (proj2 (Ma j Mj HM) _ _ _ Hh) as [cupsa Hca].
          destruct (proj2 (Mb j Mj HM) _ _ _ Hh) as [cupsb Hcb].
          destruct (grp_rel_rview_nil _ _ _ _ _ _ _ _ _ _ _ HM Hh Hi) as [-> ->].
          split; eapply entry_readable_at_evaluated.
          + apply eval_entry_type_shape; eapply eval_shape_type_rview; [ exact Hl | exact HM | exact Hh | exact Hca ].
          + exact (Va _ _ _ _ _ _ _ _ _ _ HM Hh Hau Hau' Hca Hi).
          + apply eval_entry_type_shape; eapply eval_shape_type_rview; [ exact Hl | exact HM | exact Hh | exact Hcb ].
          + exact (Vb _ _ _ _ _ _ _ _ _ _ HM Hh Hau Hau' Hcb Hi).
        - destruct (shape_doms_ok_pi_inv _ _ _ _ _ _ _ _ Hd) as (b & b' & Eb & Eb' & Hrest & Hty & Hvar).
          assert (Hext : forall s, exists r r',
                     $| v & ⇑! b s | gc_deps ⍮ gc_stack ↘ r /\ $| v' & ⇑! b' s | gc_deps ⍮ gc_stack ↘ r' /\
                     entry_readable (de_term r (entry_type_shape p ua (components_env D ua Ts pre ↦ ⇑! b s ⦂
                                                  entry_type_closure B (components_env D ua Ts pre)) t)) /\
                     entry_readable (de_term r' (entry_type_shape p ub (components_env D ub Ts pre' ↦ ⇑! b' s ⦂
                                                  entry_type_closure B (components_env D ub Ts pre')) t))).
          { intros s.
            destruct (rec_arg_rel_pi_inv _ _ _ _ _ _ _ _ _ _ Hr _ _ (Hvar s)) as (r & r' & Er & Er' & Hr').
            assert (L1 : List.length (pre ++ ⇑! b s :: nil) = List.length (Ts ++ ce_ass ak_relevant B :: nil))
              by (rewrite !List.length_app, Lp; reflexivity).
            assert (L2 : List.length (pre' ++ ⇑! b' s :: nil) = List.length (Ts ++ ce_ass ak_relevant B :: nil))
              by (rewrite !List.length_app, Lp'; reflexivity).
            destruct (IH _ _ _ _ _ _ _ _ Hau Hau' L1 L2 Hr' (Hrest _ _ (Hvar s))) as [IHa IHb].
            rewrite (components_env_snoc _ _ _ _ _ _ _ Lp) in IHa; rewrite (components_env_snoc _ _ _ _ _ _ _ Lp') in IHb.
            exists r, r'; split; [ exact Er | split; [ exact Er' | split; [ exact IHa | exact IHb ] ] ]. }
          split; intros s; destruct (Hext s) as (r & r' & Er & Er' & Ra & Rb);
            destruct (Hty s) as [A A' RA RA' _].
          + destruct (entry_readable_term_at _ _ (S s) Ra) as (c & C & W & Ec & RC & RW); inversion Ec; subst.
            eexists; eapply read_entry_term;
              [ apply eval_entry_type_shape, eval_shape_type_pi; exact Eb
              | eapply read_typ_pi; [ exact RA | eapply eval_fam_cod_shfam; eassumption | exact RC ]
              | eapply read_nf_fn; [ constructor | exact RA | exact Er | eapply eval_fam_cod_shfam; eassumption | exact RW ] ].
          + destruct (entry_readable_term_at _ _ (S s) Rb) as (c & C & W & Ec & RC & RW); inversion Ec; subst.
            eexists; eapply read_entry_term;
              [ apply eval_entry_type_shape, eval_shape_type_pi; exact Eb'
              | eapply read_typ_pi; [ exact RA' | eapply eval_fam_cod_shfam; eassumption | exact RC ]
              | eapply read_nf_fn; [ constructor | exact RA' | exact Er' | eapply eval_fam_cod_shfam; eassumption | exact RW ] ].
      Qed.

      Scheme rec_result_rel_readable_ind := Minimality for rec_result_rel Sort Prop
      with rec_result_app_rel_readable_ind := Minimality for rec_result_app_rel Sort Prop
      with rec_results_rel_readable_ind := Minimality for rec_results_rel Sort Prop.
      Combined Scheme rec_result_rel_readable_ind_all
        from rec_result_rel_readable_ind, rec_result_app_rel_readable_ind, rec_results_rel_readable_ind.

      (** Related recursive results of related arguments at the bases [ua]
          and [ub] read back at their types ([eval_ihty], [eval_ihtys]),
          which are defined: at the end of a shape the motive's instance,
          at a function shape a [Π] over the domain, whose η-directed
          readback applies them to a fresh variable of the domain, as for
          [f : B a → W A B] above, read at the motive's instance at [f x]. *)
      Lemma ih_results_readable_all : forall k u u',
        (forall pre pre' Ts t v v' rs rs', rec_result_rel k u u' pre pre' Ts t v v' rs rs' ->
           adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' ->
           List.length pre = List.length Ts -> List.length pre' = List.length Ts ->
           rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts t v v' ->
           shape_doms_ok ua ub k pre pre' Ts t ->
           exists as1 as2,
             ⟦ihty v of t at p ua under ρa (blocks_motives Bksa) ⟧ gc_deps ⍮ gc_stack ⍮ components_env D ua Ts pre ↘ as1 /\
             ⟦ihty v' of t at p ub under ρb (blocks_motives Bksb) ⟧ gc_deps ⍮ gc_stack ⍮ components_env D ub Ts pre' ↘ as2 /\
             List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) rs as1 /\
             List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) rs' as2) /\
        (forall pre pre' Ts t v c v' c' rs rs', rec_result_app_rel k u u' pre pre' Ts t v c v' c' rs rs' ->
           adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' ->
           List.length pre = List.length Ts -> List.length pre' = List.length Ts ->
           rec_arg_app_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts t v c v' c' ->
           shape_doms_ok ua ub k pre pre' Ts t ->
           exists fc fc' rcs rcs' as1 as2, $| v & c | gc_deps ⍮ gc_stack ↘ fc /\ $| v' & c' | gc_deps ⍮ gc_stack ↘ fc' /\
             List.Forall2 (fun f r => $| f & c | gc_deps ⍮ gc_stack ↘ r) rs rcs /\
             List.Forall2 (fun f r => $| f & c' | gc_deps ⍮ gc_stack ↘ r) rs' rcs' /\
             ⟦ihty fc of t at p ua under ρa (blocks_motives Bksa) ⟧ gc_deps ⍮ gc_stack ⍮ components_env D ua Ts pre ↘ as1 /\
             ⟦ihty fc' of t at p ub under ρb (blocks_motives Bksb) ⟧ gc_deps ⍮ gc_stack ⍮ components_env D ub Ts pre' ↘ as2 /\
             List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) rcs as1 /\
             List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) rcs' as2) /\
        (forall pre pre' Ts gs vs vs' ihs ihs', rec_results_rel k u u' pre pre' Ts gs vs vs' ihs ihs' ->
           adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' ->
           List.length pre = List.length Ts -> List.length pre' = List.length Ts ->
           con_args_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts gs vs vs' ->
           cargs_doms_ok ua ub k pre pre' Ts gs vs vs' ->
           exists as1 as2,
             ⟦ihtys vs of gs at p ua under ρa (blocks_motives Bksa) ⟧ gc_deps ⍮ gc_stack ⍮ components_env D ua Ts pre ↘ as1 /\
             ⟦ihtys vs' of gs at p ub under ρb (blocks_motives Bksb) ⟧ gc_deps ⍮ gc_stack ⍮ components_env D ub Ts pre' ↘ as2 /\
             List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) ihs as1 /\
             List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) ihs' as2).
      Proof.
        intros k0 u0 u0'; revert k0 u0 u0'.
        match goal with
        | |- forall k u u',
             (forall p1 p1' T1 t1 x1 x1' r1 r1', rec_result_rel _ _ _ _ _ _ _ _ _ _ _ -> @?Q k u u' p1 p1' T1 t1 x1 x1' r1 r1') /\
             (forall p2 p2' T2 t2 x2 c2 x2' c2' r2 r2', rec_result_app_rel _ _ _ _ _ _ _ _ _ _ _ _ _ ->
                @?Q0 k u u' p2 p2' T2 t2 x2 c2 x2' c2' r2 r2') /\
             (forall p3 p3' T3 g3 x3 x3' i3 i3', rec_results_rel _ _ _ _ _ _ _ _ _ _ _ -> @?Q1 k u u' p3 p3' T3 g3 x3 x3' i3 i3') =>
            intros k u u'; apply (rec_result_rel_readable_ind_all Q Q0 Q1)
        end.
        - (** At the end, at a member with a block: the motive's instance. *)
          intros k u u' pre pre' Ts j Mj Ps bs bs' v v' ih ih' HM Hrv Eb Eb' HR Hau Hau' Lp Lp' Hr Hd.
          inversion Hr as [? ? ? ? bs0 ? ? bs0' ? ? ? ? Eb0 Eb0' Hk Hk' Hi |]; subst.
          pose proof (functional_eval_exps' _ _ _ _ Eb Eb0) as <-; pose proof (functional_eval_exps' _ _ _ _ Eb' Eb0') as <-.
          inversion Hd as [? ? ? ? ? bsX bsY EX EY AX AY |]; subst.
          pose proof Hups as [_ _ Aa Ab _ _ _ _ _ _ _ _].
          (** The motive is at the parameters at [ua] and [ub], related to
              the element's own. *)
          pose proof (admissible_indices_rel _ _ _ _ _ _ _ HM Hk AX) as HbX.
          pose proof (admissible_indices_rel _ _ _ _ _ _ _ HM Hk' AY) as HbY.
          pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HM Hi HbX HbY) as HiX.
          pose proof AX as [basea _ Hka]; pose proof AY as [baseb _ Hkb].
          unfold nparams_tele_rel in Hka, Hkb; rewrite HM in Hka, Hkb.
          destruct (shape_elements_readable (pt_self j Ps) _ _ _ _ _ _ _ _ Hau Hau' Lp Lp' Hr Hd) as [Rva Rvb].
          assert (Hra : List.Forall2 (fun v t => entry_readable (de_term v t)) (bsX ++ v :: nil)
                          (List.map snd (tele_entries (decl_env D ua) (List.rev (im_nparams Mj)) bsX
                                           ++ (v, entry_type_shape p ua (components_env D ua Ts pre) (pt_self j Ps)) :: nil)))
            by (rewrite List.map_app; apply List.Forall2_app;
                [ exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ Hass Aa HM Hka) | constructor; [ exact Rva | constructor ] ]).
          assert (Hrb : List.Forall2 (fun v t => entry_readable (de_term v t)) (bsY ++ v' :: nil)
                          (List.map snd (tele_entries (decl_env D ub) (List.rev (im_nparams Mj)) bsY
                                           ++ (v', entry_type_shape p ub (components_env D ub Ts pre') (pt_self j Ps)) :: nil)))
            by (rewrite List.map_app; apply List.Forall2_app;
                [ exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ Hass Ab HM Hkb) | constructor; [ exact Rvb | constructor ] ]).
          destruct (HbA _ _ HM Hrv) as [ba Ha]; destruct (HbB _ _ HM Hrv) as [bb Hb].
          destruct (Hmot _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Ha Hb HiX Hra Hrb) as (a & a' & Ea & Ea' & HRa).
          rewrite combine_tele_entries_snoc in Ea, Ea'.
          pose proof (proj1 (motive_rel_move _ _ _ _ _ _ _ _ _ _ HM Hrv Hi HbX HbY _ _) HR) as HRX.
          exists (a :: nil), (a' :: nil); split; [| split; [| split ] ].
          + eapply eval_ihty_self; [ exact Hl | exact HM | exact Hrv | exact EX | rewrite (nth_blocks_motives _ _ _ Ha); exact Ea ].
          + eapply eval_ihty_self; [ exact Hl | exact HM | exact Hrv | exact EY | rewrite (nth_blocks_motives _ _ _ Hb); exact Ea' ].
          + constructor; [ exact (proj1 (entry_readable_of_elem HRa HRX)) | constructor ].
          + constructor; [ exact (proj2 (entry_readable_of_elem HRa HRX)) | constructor ].
        - (** At the end, at a record view: its fields'. *)
          intros k u u' pre pre' Ts j Mj qr Is fl c gs Ps v v' ws ws' rs rs' HM Hh Hcs Ew Ew' _ IH Hau Hau' Lp Lp' Hr Hd.
          inversion Hr as [? ? ? ? bs0 ? ? bs0' ? ? ? ? _ _ _ _ Hi |]; subst.
          destruct (grp_rel_rview_nil _ _ _ _ _ _ _ _ _ _ _ HM Hh Hi) as [-> ->].
          inversion Hi as [| | ? Mj0 qr0 Is0 fl0 c0 gs0 ? ws0 ? ws0' ? ? HM0 Hh0 Hnp Hcs0 Ew0 Ew0' Hn Hca];
            subst; [ no_rview_rel | no_rview_rel |].
          rewrite HM in HM0; injection HM0 as <-; rewrite Hh in Hh0; injection Hh0 as <- <- <-.
          rewrite Hcs in Hcs0; injection Hcs0 as <- <-.
          pose proof (functional_eval_projs _ _ _ _ Ew Ew0) as <-; pose proof (functional_eval_projs _ _ _ _ Ew' Ew0') as <-.
          destruct (con_args_rel_length _ _ _ _ _ _ _ _ _ _ Hca) as [L1 L2].
          pose proof Hups as [_ _ Ca Cb _ _ _ _ _ _ _ _].
          pose proof (rview_fields_doms ua ub Ca Cb j Mj qr Is fl c gs ws ws' HM Hh Hcs L1 L2 Hn) as Hds.
          destruct (IH Hau Hau' eq_refl eq_refl Hca Hds) as (as1 & as2 & T1 & T2 & R1 & R2).
          exists as1, as2; split; [| split; [| split; assumption ] ].
          + eapply eval_ihty_rview; [ exact Hl | exact HM | exact Hh | exact Hcs | exact Ew | exact T1 ].
          + eapply eval_ihty_rview; [ exact Hl | exact HM | exact Hh | exact Hcs | exact Ew' | exact T2 ].
        - (** At a domain: a [Π] over it of each recursive result's
              family, read at a fresh variable of the domain. *)
          intros k u u' pre pre' Ts B t v v' rs rs' Happ IH _ _ Hau Hau' Lp Lp' Hr Hd.
          destruct (shape_doms_ok_pi_inv _ _ _ _ _ _ _ _ Hd) as (b & b' & Eb & Eb' & Hrest & Hty & Hvar).
          assert (Hf : forall c c', dr k pre Ts B c c' ->
                     rec_arg_app_rel p D (admissible_index_at D ups nr) nr ar dr k u u' (pre ++ c :: nil) (pre' ++ c' :: nil)
                       (Ts ++ ce_ass ak_relevant B :: nil) t v c v' c').
          { intros c c' Hc; destruct (rec_arg_rel_pi_inv _ _ _ _ _ _ _ _ _ _ Hr _ _ Hc) as (r & r' & Er & Er' & Hr').
            econstructor; [ exact Er | exact Er' | exact Hr' ]. }
          assert (Hext : forall s, exists fc fc' rcs rcs' as1 as2,
                     $| v & ⇑! b s | gc_deps ⍮ gc_stack ↘ fc /\ $| v' & ⇑! b' s | gc_deps ⍮ gc_stack ↘ fc' /\
                     List.Forall2 (fun f r => $| f & ⇑! b s | gc_deps ⍮ gc_stack ↘ r) rs rcs /\
                     List.Forall2 (fun f r => $| f & ⇑! b' s | gc_deps ⍮ gc_stack ↘ r) rs' rcs' /\
                     ⟦ihty fc of t at p ua under ρa (blocks_motives Bksa) ⟧ gc_deps ⍮ gc_stack ⍮
                       components_env D ua Ts pre ↦ ⇑! b s ⦂ entry_type_closure B (components_env D ua Ts pre) ↘ as1 /\
                     ⟦ihty fc' of t at p ub under ρb (blocks_motives Bksb) ⟧ gc_deps ⍮ gc_stack ⍮
                       components_env D ub Ts pre' ↦ ⇑! b' s ⦂ entry_type_closure B (components_env D ub Ts pre') ↘ as2 /\
                     List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) rcs as1 /\
                     List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) rcs' as2).
          { intros s.
            assert (L1 : List.length (pre ++ ⇑! b s :: nil) = List.length (Ts ++ ce_ass ak_relevant B :: nil))
              by (rewrite !List.length_app, Lp; reflexivity).
            assert (L2 : List.length (pre' ++ ⇑! b' s :: nil) = List.length (Ts ++ ce_ass ak_relevant B :: nil))
              by (rewrite !List.length_app, Lp'; reflexivity).
            destruct (IH _ _ (Hvar s) Hau Hau' L1 L2 (Hf _ _ (Hvar s)) (Hrest _ _ (Hvar s)))
              as (fc & fc' & rcs & rcs' & as1 & as2 & Ef & Ef' & F1 & F2 & T1 & T2 & R1 & R2).
            rewrite (components_env_snoc _ _ _ _ _ _ _ Lp) in T1; rewrite (components_env_snoc _ _ _ _ _ _ _ Lp') in T2.
            exists fc, fc', rcs, rcs', as1, as2; repeat split; assumption. }
          set (N := List.length (shape_leaves (rview_leaves D) 0 t)).
          assert (LN : List.length rs = N /\ List.length rs' = N).
          { destruct (Hext 0) as (fc & fc' & rcs & rcs' & as1 & as2 & _ & _ & F1 & F2 & T1 & T2 & R1 & R2).
            pose proof (proj1 eval_ihty_length_all _ _ _ _ _ _ _ _ T1 D Hl Hlc).
            pose proof (proj1 eval_ihty_length_all _ _ _ _ _ _ _ _ T2 D Hl Hlc).
            pose proof (List.Forall2_length F1); pose proof (List.Forall2_length F2);
              pose proof (List.Forall2_length R1); pose proof (List.Forall2_length R2).
            unfold N; split; congruence. }
          destruct LN as [LN LN'].
          exists (List.map (fun i => Πᵈ{ak_relevant} b (nil ↦ d_ihfam ρa (blocks_motives Bksa) p ua (components_env D ua Ts pre) B t i v
                                             ⦂ entry_type_none) fam_cod) (List.seq 0 N)),
                 (List.map (fun i => Πᵈ{ak_relevant} b' (nil ↦ d_ihfam ρb (blocks_motives Bksb) p ub (components_env D ub Ts pre') B t i v'
                                             ⦂ entry_type_none) fam_cod) (List.seq 0 N)).
          split; [ eapply eval_ihty_pi; [ exact Hl | exact Eb ] | split; [ eapply eval_ihty_pi; [ exact Hl | exact Eb' ] | split ] ].
          + rewrite <- LN; apply forall2_map_seq; intros n r Hri s; cbn [Nat.add].
            destruct (Hext s) as (fc & fc' & rcs & rcs' & as1 & as2 & Ef & _ & F1 & _ & T1 & _ & R1 & _).
            destruct (forall2_nth_left _ _ _ _ _ F1 Hri) as (rc & Hrc & Erc).
            destruct (forall2_nth_left _ _ _ _ _ R1 Hrc) as (ai & Hai & Rai).
            destruct (entry_readable_term_at _ _ (S s) Rai) as (a0 & C & W & Ev & RC & RW); inversion Ev; subst.
            destruct (Hty s) as [A A' RA RA' _].
            eexists; eapply read_entry_term;
              [ apply eval_entry_type_value
              | eapply read_typ_pi; [ exact RA | eapply eval_fam_cod_ihfam; [ exact Ef | exact T1 | exact Hai ] | exact RC ]
              | eapply read_nf_fn; [ constructor | exact RA | exact Erc | eapply eval_fam_cod_ihfam; [ exact Ef | exact T1 | exact Hai ] | exact RW ] ].
          + rewrite <- LN'; apply forall2_map_seq; intros n r Hri s; cbn [Nat.add].
            destruct (Hext s) as (fc & fc' & rcs & rcs' & as1 & as2 & _ & Ef & _ & F2 & _ & T2 & _ & R2).
            destruct (forall2_nth_left _ _ _ _ _ F2 Hri) as (rc & Hrc & Erc).
            destruct (forall2_nth_left _ _ _ _ _ R2 Hrc) as (ai & Hai & Rai).
            destruct (entry_readable_term_at _ _ (S s) Rai) as (a0 & C & W & Ev & RC & RW); inversion Ev; subst.
            destruct (Hty s) as [A A' RA RA' _].
            eexists; eapply read_entry_term;
              [ apply eval_entry_type_value
              | eapply read_typ_pi; [ exact RA' | eapply eval_fam_cod_ihfam; [ exact Ef | exact T2 | exact Hai ] | exact RC ]
              | eapply read_nf_fn; [ constructor | exact RA' | exact Erc | eapply eval_fam_cod_ihfam; [ exact Ef | exact T2 | exact Hai ] | exact RW ] ].
        - (** An application: the rest at the function's values. *)
          intros k u u' pre pre' Ts t v c v' c' rs rs' fc fc' rcs rcs' Ev Ev' F1 F2 Hres IH Hau Hau' Lp Lp' Ha Hd.
          destruct (rec_arg_app_rel_inv _ _ _ _ _ _ _ _ _ _ _ Ha) as (r & r' & Er & Er' & Hr).
          pose proof (functional_eval_app _ _ _ _ Ev Er) as <-; pose proof (functional_eval_app _ _ _ _ Ev' Er') as <-.
          destruct (IH Hau Hau' Lp Lp' Hr Hd) as (as1 & as2 & T1 & T2 & R1 & R2).
          exists fc, fc', rcs, rcs', as1, as2; repeat split; assumption.
        - (** No argument. *)
          intros; exists nil, nil; split; [ constructor | split; [ constructor | split; constructor ] ].
        - (** A non-recursive argument joins the prefixes. *)
          intros k u u' pre pre' Ts rA A gs v v' vs vs' ihs ihs' _ IH Hau Hau' Lp Lp' Hc Hd.
          assert (L1 : List.length (pre ++ v :: nil) = List.length (Ts ++ ce_ass rA A :: nil))
            by (rewrite !List.length_app, Lp; reflexivity).
          assert (L2 : List.length (pre' ++ v' :: nil) = List.length (Ts ++ ce_ass rA A :: nil))
            by (rewrite !List.length_app, Lp'; reflexivity).
          destruct (IH Hau Hau' L1 L2 (con_args_rel_arg_inv _ _ _ _ _ _ _ _ _ _ _ _ _ Hc)
                      (cargs_doms_ok_arg_inv _ _ _ _ _ _ _ _ _ _ _ _ _ Hd)) as (as1 & as2 & T1 & T2 & R1 & R2).
          rewrite (components_env_snoc _ _ _ _ _ _ _ Lp) in T1; rewrite (components_env_snoc _ _ _ _ _ _ _ Lp') in T2.
          exists as1, as2; split; [ constructor; exact T1 | split; [ constructor; exact T2 | split; assumption ] ].
        - (** A recursive argument: its results, then the rest's. *)
          intros k u u' pre pre' Ts t gs v v' vs vs' rs rs' ihs ihs' _ _ _ IHr _ IHrs Hau Hau' Lp Lp' Hc Hd.
          destruct (con_args_rel_rec_inv _ _ _ _ _ _ _ _ _ _ _ _ Hc) as [Hc1 Hc2].
          destruct (cargs_doms_ok_rec_inv _ _ _ _ _ _ _ _ _ _ _ _ Hd) as [Hd1 Hd2].
          destruct (IHr Hau Hau' Lp Lp' Hc1 Hd1) as (as1 & as2 & T1 & T2 & R1 & R2).
          destruct (IHrs Hau Hau' Lp Lp' Hc2 Hd2) as (bs1 & bs2 & U1 & U2 & Q1 & Q2).
          exists (as1 ++ bs1), (as2 ++ bs2); split; [ eapply eval_ihtys_rec; [ exact T1 | exact U1 ] | split; [ eapply eval_ihtys_rec; [ exact T2 | exact U2 ] |] ].
          split; apply List.Forall2_app; assumption.
      Qed.

      (** The types of the recursive results a branch binds evaluate to
          the values [eval_ihtys] gives. *)
      Lemma ihs_types_eval : forall ρm As X ρ gs vs as1,
          ⟦ihtys vs of gs at p X under ρm As ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ as1 ->
          List.Forall2 (fun t a => eval_entry_type gc_deps gc_stack t a) (ihs_types D p X ρm As ρ gs vs) as1.
      Proof using Hl Hass.
        intros ρm As X ρ gs; revert ρ; induction gs as [| [r A | t] gs IH]; intros ρ [| v vs] as1 H;
          inversion H; subst; cbn [ihs_types].
        - constructor.
        - exact (IH _ _ _ ltac:(eassumption)).
        - apply List.Forall2_app; [| exact (IH _ _ _ ltac:(eassumption)) ].
          erewrite <- (proj1 (eval_ihty_length_all (Θ := gc_deps) (Ξ := gc_stack)) _ _ _ _ _ _ _ _ ltac:(eassumption) D Hl Hlc).
          apply List.Forall2_flip, forall2_map_seq; intros n0 a Ha; cbn [Nat.add].
          eapply eval_entry_type_induction_hypothesis; [ eassumption | exact Ha ].
      Qed.

      (** The values a branch binds, in order. *)
      Lemma pair_values_with_types_values : forall vs ts, List.map fst (pair_values_with_types vs ts) = vs.
      Proof. induction vs as [| v vs IH]; intros ts; cbn; [ reflexivity | f_equal; apply IH ]. Qed.

      Lemma pair_values_with_types_types : forall vs ts, List.length vs = List.length ts ->
          List.map snd (pair_values_with_types vs ts) = ts.
      Proof using. induction vs as [| v vs IH]; intros [| t ts] Lv; cbn in Lv |- *; try discriminate; [ reflexivity | f_equal; auto ]. Qed.

      Lemma branch_entries_values : forall Mj X As ρm gs ns vs ihs,
          List.map fst (branch_entries D Mj p X As ρm gs ns vs ihs) = ns ++ vs ++ ihs.
      Proof.
        intros; unfold branch_entries; rewrite !List.map_app, tele_entries_values, cargs_entries_values,
          pair_values_with_types_values; reflexivity.
      Qed.

      (** A branch's environment, as its values combined with their types. *)
      Lemma branch_env_combine : forall ρ Mj X As ρm gs ns vs ihs,
          env_extend_typed ρ (List.combine (ns ++ vs ++ ihs) (List.map snd (branch_entries D Mj p X As ρm gs ns vs ihs)))
          = env_extend_typed ρ (branch_entries D Mj p X As ρm gs ns vs ihs).
      Proof. intros; rewrite <- (branch_entries_values Mj X As ρm gs ns vs ihs) at 1; rewrite combine_map_fst_snd; reflexivity. Qed.

      (** The non-recursive argument after [gs1]. *)
      Lemma cargs_nonrec_nth_arg : forall gs1 r A gs2,
          List.nth_error (cargs_nonrec (gs1 ++ ca_arg r A :: gs2)) (List.length (cargs_nonrec gs1)) = Some A.
      Proof using. intros; rewrite cargs_nonrec_app, List.nth_error_app2, Nat.sub_diag by lia; reflexivity. Qed.


      (** The arguments of a constructor at any admissible bases read back
          at the types the branch binds them at, at [ua] and [ub]: a
          non-recursive one at its declared type ([adm_arg_types]), a
          recursive one at its shape's ([shape_elements_readable]). *)
      Lemma cargs_entries_readable : forall k Mk c gs u u' ns ns',
          adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' ->
          ind_member D k = Some Mk -> ind_con Mk c = Some gs -> tele_rel (nr k) (List.rev (im_nparams Mk)) ns ns' ->
          forall gs2 gs1 pre pre' vs vs', gs = gs1 ++ gs2 ->
          tele_prefix_rel (ar k ns c) (List.length (cargs_nonrec gs1)) pre pre' ->
          tele_rel_from (ar k ns c) (List.length (cargs_nonrec gs1)) pre (nonrec_arg_vals gs2 vs) (nonrec_arg_vals gs2 vs') ->
          con_args_rel p D (admissible_index_at D ups nr) nr ar dr k u u' (ns ++ pre) (ns' ++ pre')
            (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) gs2 vs vs' ->
          cargs_doms_ok ua ub k (ns ++ pre) (ns' ++ pre') (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) gs2 vs vs' ->
          List.Forall2 (fun v t => entry_readable (de_term v t)) vs
            (List.map snd (cargs_entries p ua (components_env D ua (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) (ns ++ pre)) gs2 vs)) /\
          List.Forall2 (fun v t => entry_readable (de_term v t)) vs'
            (List.map snd (cargs_entries p ub (components_env D ub (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) (ns' ++ pre')) gs2 vs')).
      Proof using Hl Hass HnP HnI HaP HaI HdP HdI Hups.
        intros k Mk c gs u u' ns ns' Hau Hau' HM Hc Hn.
        pose proof Hups as [_ _ Aa Ab _ _ _ _ _ _ _ _].
        pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HM _ _ Hn) as Hnn.
        pose proof (proj1 (tele_rel_iff _ _ _ _) Hn) as (Ln & Ln' & _).
        induction gs2 as [| [rA A | t] gs2 IH]; intros gs1 pre pre' [| v vs] [| v' vs'] Heq Hp Hr Hc' Hd;
          try (inversion Hc'; fail); [ split; constructor | |].
        - cbn [nonrec_arg_vals tele_rel_from] in Hr; destruct Hr as [Hv Hr].
          pose proof (proj1 (tele_prefix_rel_iff _ _ _ _) Hp) as (Lp & Lp' & _).
          assert (HK : List.length (cargs_nonrec gs1) <= List.length (cargs_nonrec gs))
            by (rewrite Heq, cargs_nonrec_app, List.length_app; lia).
          assert (Hk : List.nth_error (cargs_nonrec gs) (List.length (cargs_nonrec gs1)) = Some A)
            by (rewrite Heq; apply cargs_nonrec_nth_arg).
          pose proof (args_rel_pre_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI k Mk HM ns c gs Hnn Hc _ _ _ HK Hp) as Hpp.
          pose proof (adm_arg_types _ _ _ _ _ _ Aa k Mk ns ns c gs _ A pre pre HM Hnn Hc Hk Hpp) as RA.
          pose proof (adm_arg_types _ _ _ _ _ _ Ab k Mk ns ns' c gs _ A pre pre' HM Hn Hc Hk Hp) as RB.
          pose proof (HaP _ _ _ _ _ _ _ _ _ _ HM Hnn Hc Hk Hpp) as HPa.
          assert (Hvv : ar k ns c (List.length (cargs_nonrec gs1)) pre v v) by (etransitivity; [ exact Hv | symmetry; exact Hv ]).
          (** The type is read among the components before the argument. *)
          assert (LT : List.length (ns ++ pre) = List.length (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1))
            by (rewrite !List.length_app, length_cargs_nonrec_tele; lia).
          assert (LT' : List.length (ns' ++ pre') = List.length (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1))
            by (rewrite !List.length_app, length_cargs_nonrec_tele; lia).
          assert (HTs : List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs
                        = (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1) ++ cargs_nonrec_tele (ca_arg rA A :: gs2))
            by (rewrite Heq, cargs_nonrec_tele_app, List.app_assoc; reflexivity).
          pose proof (component_elem_readable_at_admissible_base _ _ _ _ _ _ RA Hvv) as Rv.
          pose proof (component_elem_readable_at_admissible_base _ _ _ _ _ _ RB Hv) as Rv'.
          rewrite HTs, components_env_prefix in Rv, Rv' by assumption.
          destruct (IH (gs1 ++ ca_arg rA A :: nil) (pre ++ v :: nil) (pre' ++ v' :: nil) vs vs')
            as [IHa IHb]; [ rewrite Heq, <- List.app_assoc; reflexivity | | | | |].
          1-2: rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_1_r.
          + apply tele_prefix_rel_snoc; [ exact Hp | exact Hv ].
          + exact Hr.
          + rewrite <- prefix_tele_snoc_arg, !List.app_assoc; exact (con_args_rel_arg_inv _ _ _ _ _ _ _ _ _ _ _ _ _ Hc').
          + rewrite <- prefix_tele_snoc_arg, !List.app_assoc; exact (cargs_doms_ok_arg_inv _ _ _ _ _ _ _ _ _ _ _ _ _ Hd).
          + rewrite <- prefix_tele_snoc_arg, !List.app_assoc, (components_env_snoc _ _ _ _ _ _ _ LT) in IHa.
            rewrite <- prefix_tele_snoc_arg, !List.app_assoc, (components_env_snoc _ _ _ _ _ _ _ LT') in IHb.
            split; cbn [cargs_entries List.map snd]; constructor; assumption.
        - cbn [nonrec_arg_vals] in Hr.
          pose proof (proj1 (tele_prefix_rel_iff _ _ _ _) Hp) as (Lp & Lp' & _).
          assert (Hn1 : List.length (cargs_nonrec (gs1 ++ ca_rec t :: nil)) = List.length (cargs_nonrec gs1))
            by (rewrite cargs_nonrec_app, List.length_app; cbn; lia).
          assert (LT : List.length (ns ++ pre) = List.length (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1))
            by (rewrite !List.length_app, length_cargs_nonrec_tele; lia).
          assert (LT' : List.length (ns' ++ pre') = List.length (List.rev (im_nparams Mk) ++ cargs_nonrec_tele gs1))
            by (rewrite !List.length_app, length_cargs_nonrec_tele; lia).
          destruct (con_args_rel_rec_inv _ _ _ _ _ _ _ _ _ _ _ _ Hc') as [Hra Hc2].
          destruct (cargs_doms_ok_rec_inv _ _ _ _ _ _ _ _ _ _ _ _ Hd) as [Hd1 Hd2].
          destruct (shape_elements_readable t _ _ _ _ _ _ _ _ Hau Hau' LT LT' Hra Hd1) as [Rv Rv'].
          destruct (IH (gs1 ++ ca_rec t :: nil) pre pre' vs vs') as [IHa IHb];
            [ rewrite Heq, <- List.app_assoc; reflexivity | rewrite Hn1; exact Hp | rewrite Hn1; exact Hr
            | rewrite <- prefix_tele_snoc_rec; exact Hc2 | rewrite <- prefix_tele_snoc_rec; exact Hd2 |].
          rewrite <- prefix_tele_snoc_rec in IHa, IHb.
          split; cbn [cargs_entries List.map snd]; constructor; assumption.
      Qed.

      (** The entries of a branch at related constructors at any
          admissible bases read back: the non-uniform parameters by
          admissibility, the arguments as above, the recursive results at
          their types ([ih_results_readable_all], [ihs_types_eval]). *)
      Lemma branch_entries_readable : forall v Mv c gs u u' ns ns' vs vs' ihs ihs',
          adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' ->
          ind_member D v = Some Mv -> ind_con Mv c = Some gs -> tele_rel (nr v) (List.rev (im_nparams Mv)) ns ns' ->
          tele_rel (ar v ns c) (cargs_nonrec gs) (nonrec_arg_vals gs vs) (nonrec_arg_vals gs vs') ->
          con_args_rel p D (admissible_index_at D ups nr) nr ar dr v u u' ns ns' (List.rev (im_nparams Mv)) gs vs vs' ->
          rec_results_rel v u u' ns ns' (List.rev (im_nparams Mv)) gs vs vs' ihs ihs' ->
          List.Forall2 (fun v t => entry_readable (de_term v t)) (ns ++ vs ++ ihs)
            (List.map snd (branch_entries D Mv p ua (blocks_motives Bksa) ρa gs ns vs ihs)) /\
          List.Forall2 (fun v t => entry_readable (de_term v t)) (ns' ++ vs' ++ ihs')
            (List.map snd (branch_entries D Mv p ub (blocks_motives Bksb) ρb gs ns' vs' ihs')).
      Proof.
        intros * Hau Hau' HM Hc Hn Hr Hca Hrr.
        pose proof Hups as [_ _ Aa Ab _ _ _ _ _ _ _ _].
        pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HM _ _ Hn) as Hnn.
        pose proof (proj1 (tele_rel_iff _ _ _ _) Hn) as (Ln & Ln' & _).
        destruct (con_args_rel_length _ _ _ _ _ _ _ _ _ _ Hca) as [Lv Lv'].
        destruct Hr as [_ Hr].
        pose proof (cargs_doms_adm ua ub Aa Ab v Mv c gs ns ns' HM Hc Hn gs nil nil nil vs vs' eq_refl Lv Lv'
                      (tele_prefix_rel_nil _) Hr) as Hd.
        rewrite ?List.app_nil_r in Hd; cbn [cargs_nonrec_tele cargs_nonrec List.map] in Hd; rewrite ?List.app_nil_r in Hd.
        pose proof (cargs_entries_readable v Mv c gs u u' ns ns' Hau Hau' HM Hc Hn gs nil nil nil vs vs' eq_refl
                      (tele_prefix_rel_nil _) Hr) as Hargs.
        cbn [cargs_nonrec_tele cargs_nonrec List.map] in Hargs; rewrite ?List.app_nil_r in Hargs.
        destruct (Hargs Hca Hd) as [Ra Rb].
        destruct (proj2 (proj2 (ih_results_readable_all v u u')) _ _ _ _ _ _ _ _ Hrr Hau Hau' Ln Ln' Hca Hd) as (as1 & as2 & T1 & T2 & R1 & R2).
        pose proof (ihs_types_eval _ _ _ _ _ _ _ T1) as E1; pose proof (ihs_types_eval _ _ _ _ _ _ _ T2) as E2.
        assert (Hit : forall ihs0 as0 ts, List.Forall2 (fun r a => entry_readable (de_term r (entry_type_value a))) ihs0 as0 ->
                   List.Forall2 (fun t a => eval_entry_type gc_deps gc_stack t a) ts as0 ->
                   List.Forall2 (fun v t => entry_readable (de_term v t)) ihs0 ts /\ List.length ihs0 = List.length ts).
        { intros ihs0 as0 ts H1 H2; revert ts H2; induction H1 as [| r a ihs0 as0 Hra H1 IH1]; intros ts H2;
            inversion H2 as [| t a' ts' as0' Ht H2']; subst; [ split; [ constructor | reflexivity ] |].
          destruct (IH1 _ H2') as [F L]; split; [ constructor; [ exact (entry_readable_at_evaluated _ _ _ Ht Hra) | exact F ] | cbn; f_equal; exact L ]. }
        destruct (Hit _ _ _ R1 E1) as [I1 L1]; destruct (Hit _ _ _ R2 E2) as [I2 L2].
        unfold branch_entries; rewrite !List.map_app, !pair_values_with_types_types by assumption.
        split; apply List.Forall2_app; [ exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ Hass Aa HM Hnn)
                                       | apply List.Forall2_app; [ exact Ra | exact I1 ]
                                       | exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ Hass Ab HM Hn)
                                       | apply List.Forall2_app; [ exact Rb | exact I2 ] ].
      Qed.

      (** *** Reading the Blocks of a Stuck Eliminator

          What the two readbacks of a stuck eliminator need of a branch:
          the constructor [c] of the member [Mi] of the group read (kinds
          [gs']), the branch's member [v] of this group (kinds [gs]), its
          fresh arguments of [v]'s telescopes at the uniform parameters
          [ua] and [ub], and its recursive results, on each side, the
          constructor at them related at [v], with related recursive
          results. *)
      #[warnings="-cannot-define-projection"]
      Record brs_pair (s : nat) (v : nat) (Mv Mi : imember)
          (hd : qname) (Dh : ind_decl) (k : nat) (prea preb nsa nsb : list domain) (c : String.string) (gs' gs : list carg) : Prop :=
        mk_brs_pair
        { (** The fresh arguments, left *)
          brs_pair_vsa : list domain
          (** The fresh arguments, right *)
        ; brs_pair_vsb : list domain
          (** The fresh recursive results, left *)
        ; brs_pair_ihsa : list domain
          (** The fresh recursive results, right *)
        ; brs_pair_ihsb : list domain
          (** The recursive results the branch is read under, left *)
        ; brs_pair_wa : list domain
          (** The recursive results the branch is read under, right *)
        ; brs_pair_wb : list domain
          (** The left arguments are the fresh ones at [ua] *)
        ; brs_pair_Fa : Fcargs gs of p ua in gc_deps ⍮ gc_stack ⍮ components_env D ua (List.rev (im_nparams Mv)) nsa
            ⍮ (s + im_nn Mi)%nat ↘ brs_pair_vsa
          (** The right arguments are the fresh ones at [ub] *)
        ; brs_pair_Fb : Fcargs gs of p ub in gc_deps ⍮ gc_stack ⍮ components_env D ub (List.rev (im_nparams Mv)) nsb
            ⍮ (s + im_nn Mi)%nat ↘ brs_pair_vsb
          (** The left fresh recursive results *)
        ; brs_pair_Ia : Fihs brs_pair_vsa at gs' gs of Dh under ρa (blocks_motives Bksa) at p ua
            in gc_deps ⍮ gc_stack ⍮ components_env D ua (List.rev (im_nparams Mv)) nsa ⍮ (s + im_nn Mi + List.length gs')%nat
            ↘ brs_pair_ihsa
          (** The right fresh recursive results *)
        ; brs_pair_Ib : Fihs brs_pair_vsb at gs' gs of Dh under ρb (blocks_motives Bksb) at p ub
            in gc_deps ⍮ gc_stack ⍮ components_env D ub (List.rev (im_nparams Mv)) nsb ⍮ (s + im_nn Mi + List.length gs')%nat
            ↘ brs_pair_ihsb
          (** The left results, the nested-through ones by the eliminator *)
        ; brs_pair_Wa : ⟦wihs brs_pair_vsa of gs' gs of Dh with brs_pair_ihsa under p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ brs_pair_wa
          (** The right results, likewise *)
        ; brs_pair_Wb : ⟦wihs brs_pair_vsb of gs' gs of Dh with brs_pair_ihsb under p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ brs_pair_wb
          (** The constructors at the fresh arguments are related at [v] *)
        ; brs_pair_rel : grp_rel p D ups nr ar dr v ua ub nsa nsb (d_con hd k c (prea ++ nsa ++ brs_pair_vsa)) (d_con hd k c (preb ++ nsb ++ brs_pair_vsb))
          (** The recursive results are related *)
        ; brs_pair_recs : rec_results_rel v ua ub nsa nsb (List.rev (im_nparams Mv)) gs
            brs_pair_vsa brs_pair_vsb brs_pair_wa brs_pair_wb }.

      (** What two related constructors of a member with a block are made
          of, at their uniform parameters [bs] and [bs'] of the member's
          own count and arguments [vs] and [vs']. *)
      #[warnings="-cannot-define-projection"]
      Record con_rel_parts (j : nat) (Mj : imember) (u u' ns ns' : list domain) (c : String.string)
          (bs bs' vs vs' : list domain) : Prop := mk_con_rel_parts
        { (** The constructor's argument kinds *)
          con_rel_parts_kinds : list carg
          (** It is a constructor of the member *)
        ; con_rel_parts_con : ind_con Mj c = Some con_rel_parts_kinds
          (** The indices are related *)
        ; con_rel_parts_indices : tele_rel (nr j) (List.rev (im_nparams Mj)) ns ns'
          (** The left one's own non-uniform parameters are related to them *)
        ; con_rel_parts_left : tele_rel (nr j) (List.rev (im_nparams Mj)) ns (List.skipn (im_unu D Mj) bs)
          (** And the right one's *)
        ; con_rel_parts_right : tele_rel (nr j) (List.rev (im_nparams Mj)) ns' (List.skipn (im_unu D Mj) bs')
          (** The non-recursive arguments are related *)
        ; con_rel_parts_nonrec : tele_rel (ar j (List.skipn (im_unu D Mj) bs) c) (cargs_nonrec con_rel_parts_kinds)
            (nonrec_arg_vals con_rel_parts_kinds vs) (nonrec_arg_vals con_rel_parts_kinds vs')
          (** And all the arguments, by their kinds *)
        ; con_rel_parts_args : con_args_rel p D (admissible_index_at D ups nr) nr ar dr j u u'
            (List.skipn (im_unu D Mj) bs) (List.skipn (im_unu D Mj) bs') (List.rev (im_nparams Mj)) con_rel_parts_kinds vs vs' }.

      Lemma grp_rel_con_parts : forall j Mj u u' ns ns' hd k c bs bs' vs vs',
          ind_member D j = Some Mj -> im_is_rview Mj = false ->
          List.length bs = (im_unu D Mj + im_nn Mj)%nat -> List.length bs' = (im_unu D Mj + im_nn Mj)%nat ->
          grp_rel p D ups nr ar dr j u u' ns ns' (d_con hd k c (bs ++ vs)) (d_con hd k c (bs' ++ vs')) ->
          con_rel_parts j Mj u u' ns ns' c bs bs' vs vs'.
      Proof.
        intros * HM Hrv L L' H; inversion H; subst; [| no_rview_rel ].
        (** The two splittings of the constructors' values agree, by the
            uniform parameters' count. *)
        match goal with
        | H0 : ind_member D j = Some ?M0, E1 : ?b0 ++ ?v0 = bs ++ vs, E2 : ?b0' ++ ?v0' = bs' ++ vs',
          L0 : length ?b0 = _, L0' : length ?b0' = _ |- _ =>
          rewrite HM in H0; injection H0 as <-;
          assert (b0 = bs) as -> by (rewrite <- (firstn_app_exact b0 v0 _ L0), E1; exact (firstn_app_exact bs vs _ L));
          apply List.app_inv_head in E1; subst v0;
          assert (b0' = bs') as -> by (rewrite <- (firstn_app_exact b0' v0' _ L0'), E2; exact (firstn_app_exact bs' vs' _ L'));
          apply List.app_inv_head in E2; subst v0'
        end.
        econstructor; eassumption.
      Qed.

      Lemma read_brs_rel : forall s v Mv Mi hd Dh k prea preb nsa nsb ba bb,
          ind_member D v = Some Mv -> im_is_rview Mv = false ->
          List.nth_error Bksa v = Some ba -> List.nth_error Bksb v = Some bb -> im_nn Mv = im_nn Mi ->
          List.length prea = im_unu D Mv -> List.length preb = im_unu D Mv ->
          ⟦mref v of p ua ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, prea) -> ⟦mref v of p ub ⟧ gc_deps ⍮ gc_stack ↘ (hd, k, preb) ->
          Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ua ⍮ s ↘ nsa ->
          Ftele List.rev (im_nparams Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ub ⍮ s ↘ nsb ->
          forall cs Bs1 Bs2,
          (forall c gs', List.In (c, gs') cs ->
             exists gs, ind_con Mv c = Some gs /\ cargs_params_length D gs /\ cargs_container_count D Dh gs' gs = cargs_nrec Dh gs' /\
               List.length gs = List.length gs' /\ brs_pair s v Mv Mi hd Dh k prea preb nsa nsb c gs' gs) ->
          (forall c n B, List.In (c, n, B) Bs1 -> brs_lookup (eb_brs ba) c = Some (n, B) /\ List.In (c, n, B) (eb_brs ba)) ->
          (forall c n B, List.In (c, n, B) Bs2 -> brs_lookup (eb_brs bb) c = Some (n, B) /\ List.In (c, n, B) (eb_brs bb)) ->
          brs_names cs Bs1 -> brs_names cs Bs2 ->
          exists Bs' Bs'', Rbrs Bs1 at cs of Mi (hd, k, prea) of Dh from p ua Bksa Mv (eb_motive ba)
                        in gc_deps ⍮ gc_stack ⍮ ρa ⍮ s ↘ Bs' /\
            Rbrs Bs2 at cs of Mi (hd, k, preb) of Dh from p ub Bksb Mv (eb_motive bb)
              in gc_deps ⍮ gc_stack ⍮ ρb ⍮ s ↘ Bs'' /\
            List.map (map_normal_branch (fun _ => nf_erase)) Bs' = List.map (map_normal_branch (fun _ => nf_erase)) Bs''.
      Proof.
        intros s v Mv Mi hd Dh k prea preb nsa nsb ba bb HM Hrv Ha Hb Hnn La Lb Hra Hrb Fa Fb.
        pose proof Hups as [_ _ Aa Ab _ _ _ Ra Rb _ _ _].
        pose proof (fresh_tele_length _ _ _ _ Fa) as Lna; pose proof (fresh_tele_length _ _ _ _ Fb) as Lnb.
        rewrite List.length_rev in Lna, Lnb.
        induction cs as [| [c gs'] cs IH]; intros [| [[c1 n1] B1] Bs1] [| [[c2 n2] B2] Bs2] Hcs HB1 HB2 Hn1 Hn2;
          cbn in Hn1, Hn2; try discriminate.
        - exists nil, nil; split; [ constructor | split; [ constructor | reflexivity ] ].
        - injection Hn1 as <- Hn1; injection Hn2 as <- Hn2.
          destruct (Hcs c gs' ltac:(left; reflexivity)) as (gs & Hc & Hpl & Hcnt & Lg & BP).
          destruct (HB1 c n1 B1 ltac:(left; reflexivity)) as [HL1 HI1].
          destruct (HB2 c n2 B2 ltac:(left; reflexivity)) as [HL2 HI2].
          pose proof (HarA _ _ _ _ _ _ _ HM Ha Hc HI1) as Hn1e; pose proof (HarB _ _ _ _ _ _ _ HM Hb Hc HI2) as Hn2e.
          assert (n2 = n1) as -> by lia.
          destruct BP as [vsa vsb ihsa ihsb wa wb Ca Cb Ia Ib Wa Wb Rel0 Recs].
          pose proof Rel0 as Rel1; rewrite !List.app_assoc in Rel1.
          (** The branch's and the motive's entries read back. *)
          assert (Lpa : List.length (prea ++ nsa) = (im_unu D Mv + im_nn Mv)%nat)
            by (rewrite List.length_app, La, Lna; unfold im_nn; reflexivity).
          assert (Lpb : List.length (preb ++ nsb) = (im_unu D Mv + im_nn Mv)%nat)
            by (rewrite List.length_app, Lb, Lnb; unfold im_nn; reflexivity).
          destruct (grp_rel_con_parts _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Lpa Lpb Rel1) as [gs0 Hc0 Hn Hsa Hsb Hnr Hca].
          rewrite Hc in Hc0; injection Hc0 as <-.
          rewrite (skipn_app_exact prea nsa _ La) in Hnr, Hca; rewrite (skipn_app_exact preb nsb _ Lb) in Hca.
          destruct (branch_entries_readable v Mv c gs ua ub nsa nsb vsa vsb wa wb Aa Ab HM Hc Hn Hnr Hca Recs) as [Ba1 Ba2].
          pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HM _ _ Hn) as Hnna.
          pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI v Mv HM _ _ Hn) as Hnnb.
          pose proof (Hbr v Mv ba bb c gs n1 B1 B2 ua ub (prea ++ nsa) (preb ++ nsb) vsa vsb wa wb hd k
                        (List.map snd (branch_entries D Mv p ua (blocks_motives Bksa) ρa gs nsa vsa wa))
                        (List.map snd (branch_entries D Mv p ub (blocks_motives Bksb) ρb gs nsb vsb wb))
                        HM Hrv Ha Hb Hc HL1 HL2) as HB.
          rewrite !skipn_app_exact in HB by assumption.
          destruct (HB Rel1 Recs Ba1 Ba2) as (r1 & r2 & Er1 & Er2 & Hrr).
          rewrite !branch_env_combine in Er1, Er2.
          assert (Ma1 : List.Forall2 (fun v t => entry_readable (de_term v t)) (nsa ++ d_con hd k c (prea ++ nsa ++ vsa) :: nil)
                          (List.map snd (motive_entries D Mv ua nsa (d_ind hd k (prea ++ nsa)) (d_con hd k c (prea ++ nsa ++ vsa)))))
            by (unfold motive_entries; rewrite List.map_app; apply List.Forall2_app;
                [ exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ Hass Aa HM Hnna)
                | constructor; [ exact (Ra _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Aa Ab Hra Rel0 Hnna) | constructor ] ]).
          assert (Ma2 : List.Forall2 (fun v t => entry_readable (de_term v t)) (nsb ++ d_con hd k c (preb ++ nsb ++ vsb) :: nil)
                          (List.map snd (motive_entries D Mv ub nsb (d_ind hd k (preb ++ nsb)) (d_con hd k c (preb ++ nsb ++ vsb)))))
            by (unfold motive_entries; rewrite List.map_app; apply List.Forall2_app;
                [ exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ Hass Ab HM Hn)
                | constructor; [ exact (Rb _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Aa Ab Hrb Rel0 Hnnb) | constructor ] ]).
          destruct (Hmot _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Ha Hb Rel0 Ma1 Ma2) as (t1 & t2 & T1 & T2 & HR).
          unfold motive_entries in T1, T2; rewrite combine_tele_entries_snoc in T1, T2.
          rewrite <- !List.app_assoc in Hrr.
          destruct (per_elem_then_per_top HR Hrr (s + (im_nn Mi + List.length gs' + cargs_nrec Dh gs'))) as [B' B'' RB1 RB2 HE].
          destruct (IH Bs1 Bs2) as (Bs' & Bs'' & RBs1 & RBs2 & HEs).
          { intros c' gs0 Hin; apply Hcs; right; exact Hin. }
          { intros c' n' Bx Hin; apply HB1; right; exact Hin. }
          { intros c' n' Bx Hin; apply HB2; right; exact Hin. }
          { exact Hn1. }
          { exact Hn2. }
          exists (cons (mk_normal_branch c (im_nn Mi + List.length gs' + cargs_nrec Dh gs') B') Bs'),
                 (cons (mk_normal_branch c (im_nn Mi + List.length gs' + cargs_nrec Dh gs') B'') Bs''); split; [| split ].
          + eapply read_brs_cons; [ exact Hc | exact Hl | lia | reflexivity | exact Hcnt | exact Hpl | exact Fa | exact Ca
                                  | exact Ia | exact Wa | exact Er1 | exact T1 | exact RB1 | exact RBs1 ].
          + eapply read_brs_cons; [ exact Hc | exact Hl | lia | reflexivity | exact Hcnt | exact Hpl | exact Fb | exact Cb
                                  | exact Ib | exact Wb | exact Er2 | exact T2 | exact RB2 | exact RBs2 ].
          + exact (f_equal2 (fun b l => b :: l) (f_equal (mk_normal_branch c _) HE) HEs).
      Qed.

      (** What the two readbacks need of a block: the one of the member
          [Mi] of the group read, the block of the member [elim_src sel i]
          of this group: its type at the uniform parameters [ua] and [ub],
          the fresh variables of its non-uniform parameters, the neutral at
          them related at the block's member, and each branch. *)
      #[warnings="-cannot-define-projection"]
      Record member_pair (s : nat) (Dc : ind_decl) (sel : option (list nat)) (i : nat) (Mi : imember) : Prop :=
        mk_member_pair
        { (** The block's member of this group *)
          member_pair_Mv : imember
          (** It is the member [elim_src sel i] *)
        ; member_pair_member : ind_member D (elim_src sel i) = Some member_pair_Mv
          (** It is no record view: it has a block *)
        ; member_pair_rv : im_is_rview member_pair_Mv = false
          (** It has as many non-uniform parameters as [Mi] *)
        ; member_pair_nn : im_nn member_pair_Mv = im_nn Mi
          (** The group of its type's declared member *)
        ; member_pair_hd : qname
          (** That declared member *)
        ; member_pair_k : nat
          (** Its type's uniform parameters at [ua] *)
        ; member_pair_prea : list domain
          (** Its type's uniform parameters at [ub] *)
        ; member_pair_preb : list domain
          (** Its type at [ua] *)
        ; member_pair_refa : ⟦mref elim_src sel i of p ua ⟧ gc_deps ⍮ gc_stack ↘ (member_pair_hd, member_pair_k, member_pair_prea)
          (** Its type at [ub] *)
        ; member_pair_refb : ⟦mref elim_src sel i of p ub ⟧ gc_deps ⍮ gc_stack ↘ (member_pair_hd, member_pair_k, member_pair_preb)
          (** [member_pair_prea] has the member's own uniform parameter count *)
        ; member_pair_lena : List.length member_pair_prea = im_unu D member_pair_Mv
          (** So has [member_pair_preb] *)
        ; member_pair_lenb : List.length member_pair_preb = im_unu D member_pair_Mv
          (** The fresh non-uniform parameters, left *)
        ; member_pair_nsa : list domain
          (** The fresh non-uniform parameters, right *)
        ; member_pair_nsb : list domain
          (** The left ones are fresh at [ua] *)
        ; member_pair_Fa : Ftele List.rev (im_nparams member_pair_Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ua ⍮ s ↘ member_pair_nsa
          (** The right ones are fresh at [ub] *)
        ; member_pair_Fb : Ftele List.rev (im_nparams member_pair_Mv) in gc_deps ⍮ gc_stack ⍮ decl_env D ub ⍮ s ↘ member_pair_nsb
          (** The fresh scrutinees are related at the block's member *)
        ; member_pair_neut : grp_rel p D ups nr ar dr (elim_src sel i) ua ub member_pair_nsa member_pair_nsb
            (⇑! (d_ind member_pair_hd member_pair_k (member_pair_prea ++ member_pair_nsa)) ((s + im_nn Mi)%nat))
            (⇑! (d_ind member_pair_hd member_pair_k (member_pair_preb ++ member_pair_nsb)) ((s + im_nn Mi)%nat))
          (** [Mi] and the block's member have the same constructor names *)
        ; member_pair_names : List.map fst (im_cons Mi) = List.map fst (im_cons member_pair_Mv)
          (** Each branch is a [brs_pair] *)
        ; member_pair_brs : forall c gs', List.In (c, gs') (im_cons Mi) ->
            exists gs, ind_con member_pair_Mv c = Some gs /\ cargs_params_length D gs /\ cargs_container_count D Dc gs' gs = cargs_nrec Dc gs' /\
              List.length gs = List.length gs' /\
              brs_pair s (elim_src sel i) member_pair_Mv Mi member_pair_hd Dc member_pair_k member_pair_prea
                member_pair_preb member_pair_nsa member_pair_nsb c gs' gs }.

      Lemma read_blocks_rel : forall s Dc sel Ms i,
          (forall n Mi, List.nth_error Ms n = Some Mi -> member_pair s Dc sel (i + n) Mi) ->
          exists NBks NBks', Rblks i Ms of Dc from p ua Bksa sel in gc_deps ⍮ gc_stack ⍮ ρa ⍮ s ↘ NBks /\
            Rblks i Ms of Dc from p ub Bksb sel in gc_deps ⍮ gc_stack ⍮ ρb ⍮ s ↘ NBks' /\
            List.map (map_normal_block (fun _ => nf_erase)) NBks = List.map (map_normal_block (fun _ => nf_erase)) NBks'.
      Proof.
        intros s Dc sel Ms; induction Ms as [| Mi Ms IH]; intros i0 HMs.
        - exists nil, nil; split; [ constructor | split; [ constructor | reflexivity ] ].
        - destruct (HMs 0 Mi eq_refl) as [Mv HM Hrv Hnn hd k prea preb Ra Rb La Lb nsa nsb Fa Fb Hne Hnames Hbrs].
          rewrite Nat.add_0_r in *.
          destruct (HbA _ _ HM Hrv) as [ba Ha]; destruct (HbB _ _ HM Hrv) as [bb Hb].
          (** The motive's entries, the fresh parameters and the fresh
              neutral at the member's type, read back. *)
          pose proof Hups as [_ _ Aa Ab _ _ _ Rda Rdb _ _ Tya].
          assert (Hnn0 : tele_rel (nr (elim_src sel i0)) (List.rev (im_nparams Mv)) nsa nsb)
            by (inversion Hne; subst;
                [ match goal with H0 : ind_member D _ = Some ?M0 |- _ => rewrite HM in H0; injection H0 as <- end; assumption
                | no_rview_rel ]).
          pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ Mv HM _ _ Hnn0) as Hnna.
          pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ Mv HM _ _ Hnn0) as Hnnb.
          assert (Ma1 : List.Forall2 (fun v t => entry_readable (de_term v t))
                          (nsa ++ ⇑! (d_ind hd k (prea ++ nsa)) (s + im_nn Mi) :: nil)
                          (List.map snd (motive_entries D Mv ua nsa (d_ind hd k (prea ++ nsa))
                                           (⇑! (d_ind hd k (prea ++ nsa)) (s + im_nn Mi)))))
            by (unfold motive_entries; rewrite List.map_app; apply List.Forall2_app;
                [ exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ Hass Aa HM Hnna)
                | constructor; [ exact (Rda _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Aa Ab Ra Hne Hnna) | constructor ] ]).
          assert (Ma2 : List.Forall2 (fun v t => entry_readable (de_term v t))
                          (nsb ++ ⇑! (d_ind hd k (preb ++ nsb)) (s + im_nn Mi) :: nil)
                          (List.map snd (motive_entries D Mv ub nsb (d_ind hd k (preb ++ nsb))
                                           (⇑! (d_ind hd k (preb ++ nsb)) (s + im_nn Mi)))))
            by (unfold motive_entries; rewrite List.map_app; apply List.Forall2_app;
                [ exact (nparams_entries_readable_at_admissible_base _ _ _ _ _ _ _ _ _ _ Hass Ab HM Hnn0)
                | constructor; [ exact (Rdb _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Aa Ab Rb Hne Hnnb) | constructor ] ]).
          destruct (Hmot _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv Ha Hb Hne Ma1 Ma2) as (a1 & a2 & Ea1 & Ea2 & HR).
          unfold motive_entries in Ea1, Ea2; rewrite combine_tele_entries_snoc in Ea1, Ea2.
          destruct (per_univ_then_per_top_typ HR (S (s + im_nn Mi))) as [A' A'' RA1 RA2 HEA].
          assert (Hnd' : List.NoDup (List.map (fun b0 => fst (fst b0)) (eb_brs ba)))
            by (rewrite <- (HnaA _ _ _ HM Ha); exact (Hnd _ _ HM)).
          assert (Hnd'' : List.NoDup (List.map (fun b0 => fst (fst b0)) (eb_brs bb)))
            by (rewrite <- (HnaB _ _ _ HM Hb); exact (Hnd _ _ HM)).
          destruct (read_brs_rel s _ Mv Mi hd Dc k prea preb nsa nsb ba bb HM Hrv Ha Hb Hnn La Lb Ra Rb Fa Fb
                      (im_cons Mi) (eb_brs ba) (eb_brs bb) Hbrs) as (Bs' & Bs'' & RB1 & RB2 & HEb).
          { intros c n B Hin; split; [ apply brs_lookup_nodup_in; assumption | exact Hin ]. }
          { intros c n B Hin; split; [ apply brs_lookup_nodup_in; assumption | exact Hin ]. }
          { unfold brs_names; rewrite Hnames; exact (HnaA _ _ _ HM Ha). }
          { unfold brs_names; rewrite Hnames; exact (HnaB _ _ _ HM Hb). }
          destruct (IH (S i0)) as (NBks & NBks' & RN1 & RN2 & HEn).
          { intros n Mi' Hn; replace (S i0 + n) with (i0 + S n) by lia; exact (HMs (S n) Mi' Hn). }
          (** The block's scrutinee type: the member's type at the fresh
              parameters, read back alike on the two sides. *)
          destruct (Tya _ _ _ _ _ _ _ _ HM Hrv Ra Rb Hnn0 (s + im_nn Mi)) as [Z' Z'' RZ1 RZ2 HEZ].
          exists (cons (mk_normal_block (S (im_nn Mi)) Z' A' Bs') NBks), (cons (mk_normal_block (S (im_nn Mi)) Z'' A'' Bs'') NBks');
            split; [| split ].
          + eapply read_blocks_cons; [ exact Hl | exact HM | exact Ha | rewrite (HnmA _ _ _ HM Ha), Hnn; reflexivity
                                     | exact Ra | exact Fa | exact RZ1 | exact Ea1 | exact RA1 | exact RB1 | exact RN1 ].
          + eapply read_blocks_cons; [ exact Hl | exact HM | exact Hb | rewrite (HnmB _ _ _ HM Hb), Hnn; reflexivity
                                     | exact Rb | exact Fb | exact RZ2 | exact Ea2 | exact RA2 | exact RB2 | exact RN2 ].
          + cbn [List.map]; f_equal; [ unfold map_normal_block; cbn; f_equal; assumption | exact HEn ].
      Qed.

      (** *** The Fresh Arguments of a Branch

          A stuck eliminator reads a branch under fresh arguments of its
          member's constructor at the uniform parameters [ua] and [ub], the
          fresh variables of each telescope at them related to those at
          [ups], and fresh recursive results where the group read has the
          argument recursive.  An argument the view nests through, or a
          leaf path of one the container has as a non-recursive field, has
          the eliminator's recursive result, stuck at a member of lower rank
          ([elim_bot]). *)

      (** What the readbacks need of the arguments [gs] (kinds [gs'] in the
          group read) after the fresh non-uniform parameters [nsa] and
          [nsb] and the fresh non-recursive arguments [wsa] and [wsb]
          before them: their fresh variables and recursive results on each
          side, the non-recursive ones related after the reference [args_pair_wfu],
          the arguments related by the shapes, with related recursive
          results. *)
      #[warnings="-cannot-define-projection"]
      Record args_pair (v : nat) (nsu : list domain) (c : String.string) (gsf : list carg) (Dh : ind_decl) (Ts : list centry)
          (nsa nsb wsa wsb : list domain) (gs' gs : list carg) (s s2 : nat) : Prop := mk_args_pair
        { (** The fresh arguments, left *)
          args_pair_vsa : list domain
          (** The fresh arguments, right *)
        ; args_pair_vsb : list domain
          (** The fresh recursive results, left *)
        ; args_pair_ihsa : list domain
          (** The fresh recursive results, right *)
        ; args_pair_ihsb : list domain
          (** The recursive results the branch is read under, left *)
        ; args_pair_wa : list domain
          (** The recursive results the branch is read under, right *)
        ; args_pair_wb : list domain
          (** The reference non-recursive arguments both sides are related
              to *)
        ; args_pair_wfu : list domain
          (** The left arguments are the fresh ones at [ua] *)
        ; args_pair_Fa : Fcargs gs of p ua in gc_deps ⍮ gc_stack ⍮ components_env D ua Ts (nsa ++ wsa) ⍮ s ↘ args_pair_vsa
          (** The right arguments are the fresh ones at [ub] *)
        ; args_pair_Fb : Fcargs gs of p ub in gc_deps ⍮ gc_stack ⍮ components_env D ub Ts (nsb ++ wsb) ⍮ s ↘ args_pair_vsb
          (** The left fresh recursive results *)
        ; args_pair_Ia : Fihs args_pair_vsa at gs' gs of Dh under ρa (blocks_motives Bksa) at p ua
            in gc_deps ⍮ gc_stack ⍮ components_env D ua Ts (nsa ++ wsa) ⍮ s2 ↘ args_pair_ihsa
          (** The right fresh recursive results *)
        ; args_pair_Ib : Fihs args_pair_vsb at gs' gs of Dh under ρb (blocks_motives Bksb) at p ub
            in gc_deps ⍮ gc_stack ⍮ components_env D ub Ts (nsb ++ wsb) ⍮ s2 ↘ args_pair_ihsb
          (** The left results, the nested-through ones by the eliminator *)
        ; args_pair_Wa : ⟦wihs args_pair_vsa of gs' gs of Dh with args_pair_ihsa under p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ args_pair_wa
          (** The right results, likewise *)
        ; args_pair_Wb : ⟦wihs args_pair_vsb of gs' gs of Dh with args_pair_ihsb under p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ args_pair_wb
          (** The left non-recursive arguments are related to the
              reference *)
        ; args_pair_Pa : tele_prefix_rel (ar v nsu c) (List.length (cargs_nonrec gsf)) args_pair_wfu (wsa ++ nonrec_arg_vals gs args_pair_vsa)
          (** So are the right ones *)
        ; args_pair_Pb : tele_prefix_rel (ar v nsu c) (List.length (cargs_nonrec gsf)) args_pair_wfu (wsb ++ nonrec_arg_vals gs args_pair_vsb)
          (** The arguments are related by the shapes *)
        ; args_pair_args : con_args_rel p D (admissible_index_at D ups nr) nr ar dr v ua ub
            (nsa ++ wsa) (nsb ++ wsb) Ts gs args_pair_vsa args_pair_vsb
          (** The recursive results are related *)
        ; args_pair_recs : rec_results_rel v ua ub (nsa ++ wsa) (nsb ++ wsb) Ts gs args_pair_vsa args_pair_vsb args_pair_wa args_pair_wb }.

      (** A telescope after the components' environment. *)
      Lemma components_env_tele : forall X T1 T2 vs1 vs2, List.length vs1 = List.length T1 ->
          env_tele (components_env D X T1 vs1) T2 vs2 = components_env D X (T1 ++ T2) (vs1 ++ vs2).
      Proof. intros * Lv; unfold components_env; symmetry; apply env_tele_app; exact Lv. Qed.

      (** The lengths of a prefix of fresh variables and its telescope. *)
      Local Ltac fresh_args_len :=
        rewrite ?List.app_nil_r; repeat rewrite List.length_app in *; cbn [List.length List.firstn] in *;
        rewrite ?length_cargs_nonrec_tele, ?List.length_map, ?List.length_rev in *; lia.

      Lemma fresh_args : forall v Mv c gsf nsu nsa nsb Dh (rk : nat -> nat) r,
          adm_fresh p D ups nr ar dr ua -> adm_fresh p D ups nr ar dr ub ->
          List.length ua = ind_nu D -> List.length ub = ind_nu D -> mrefs_ok ua -> mrefs_ok ub ->
          ind_member D v = Some Mv -> ind_con Mv c = Some gsf -> cargs_params_length D gsf ->
          tele_rel (nr v) (List.rev (im_nparams Mv)) nsu nsa -> tele_rel (nr v) (List.rev (im_nparams Mv)) nsu nsb ->
          view_rank_ok gc_deps gc_stack D rk -> (forall j, rk j < r -> elim_bot j) ->
          forall gs' gs gs1 wsu wsa wsb s s2, gsf = gs1 ++ gs ->
          cargs_same_kinds gs' gs -> cargs_nest_ok D Dh rk r gs' gs ->
          fresh_cargs_rel D nr (ar v nsu c) (dr v) (List.rev (im_nparams Mv)) nsu nsa (List.length (cargs_nonrec gs1))
            (cargs_nonrec_tele gs1) wsu wsa
            (components_env D ups (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1) (nsu ++ wsu))
            (components_env D ua (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1) (nsa ++ wsa)) s gs ->
          fresh_cargs_rel D nr (ar v nsu c) (dr v) (List.rev (im_nparams Mv)) nsu nsb (List.length (cargs_nonrec gs1))
            (cargs_nonrec_tele gs1) wsu wsb
            (components_env D ups (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1) (nsu ++ wsu))
            (components_env D ub (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1) (nsb ++ wsb)) s gs ->
          tele_prefix_rel (ar v nsu c) (List.length (cargs_nonrec gs1)) wsu wsa ->
          tele_prefix_rel (ar v nsu c) (List.length (cargs_nonrec gs1)) wsu wsb ->
          args_pair v nsu c gsf Dh (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1) nsa nsb wsa wsb gs' gs s s2.
      Proof.
        intros v Mv c gsf nsu nsa nsb Dh rk r Ha Hb La Lb Hma Hmb HM Hc Hpl Hn1 Hn2 Hrk HIH.
        pose proof Hups as [_ _ HAa HAb _ _ _ _ _ _ _ _].
        pose proof (proj1 (tele_rel_iff _ _ _ _) Hn1) as (Lnu & Ln1 & _).
        pose proof (proj1 (tele_rel_iff _ _ _ _) Hn2) as (_ & Ln2 & _).
        induction gs' as [| g' gs' IH]; intros [| g gs] gs1 wsu wsa wsb s s2 Heq Hk Hno C1 C2 Hw1 Hw2;
          cbn in Hk; try contradiction; try (destruct g' as [? | ?]; cbn in Hk; contradiction).
        - rewrite Heq, List.app_nil_r.
          refine (mk_args_pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ nil nil nil nil nil nil wsu _ _ _ _ _ _ _ _ _ _);
            cbn [nonrec_arg_vals]; rewrite ?List.app_nil_r;
            first [ exact Hw1 | exact Hw2 | constructor | econstructor; eassumption ].
        - pose proof (proj1 (tele_prefix_rel_iff _ _ _ _) Hw1) as (Lwu & Lw1 & _).
          pose proof (proj1 (tele_prefix_rel_iff _ _ _ _) Hw2) as (_ & Lw2 & _).
          assert (LTu : List.length (nsu ++ wsu) = List.length (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1))
            by (rewrite !List.length_app, length_cargs_nonrec_tele; lia).
          assert (LT1 : List.length (nsa ++ wsa) = List.length (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1))
            by (rewrite !List.length_app, length_cargs_nonrec_tele; lia).
          assert (LT2 : List.length (nsb ++ wsb) = List.length (List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1))
            by (rewrite !List.length_app, length_cargs_nonrec_tele; lia).
          destruct g' as [rA' A' | t']; destruct g as [rA A | t]; cbn in Hk; try contradiction.
          + (** Non-recursive in both. *)
            inversion C1 as [| k0 Ta0 ws0 ws0' ρ0 ρ0' s0 r0 A0 gs0 a0 a1 E0 E1 R1 C1' |]; subst.
            inversion C2 as [| k0 Ta0 ws0 ws0' ρ0 ρ0' s0 r0 A0 gs0 a0' a2 E0' E2 R2 C2' |]; subst.
            pose proof (functional_eval_exp _ _ _ _ E0 E0') as <-.
            assert (Hk1 : List.length (cargs_nonrec (gs1 ++ ca_arg rA A :: nil)) = S (List.length (cargs_nonrec gs1)))
              by (rewrite cargs_nonrec_app, List.length_app; cbn; lia).
            destruct (IH gs (gs1 ++ ca_arg rA A :: nil) (wsu ++ ⇑! a0 s :: nil)
                        (wsa ++ ⇑! a1 s :: nil) (wsb ++ ⇑! a2 s :: nil) (S s) s2)
              as [vsa vsb ihsa ihsb wa wb wfu F1 F2 I1 I2 W1 W2 P1 P2 Hia Hir].
            { rewrite <- List.app_assoc; reflexivity. }
            { exact Hk. }
            { exact Hno. }
            { rewrite Hk1, cargs_nonrec_tele_snoc_arg, !List.app_assoc, (components_env_snoc _ _ _ _ _ _ _ LTu),
                (components_env_snoc _ _ _ _ _ _ _ LT1); exact C1'. }
            { rewrite Hk1, cargs_nonrec_tele_snoc_arg, !List.app_assoc, (components_env_snoc _ _ _ _ _ _ _ LTu),
                (components_env_snoc _ _ _ _ _ _ _ LT2); exact C2'. }
            { rewrite Hk1; apply tele_prefix_rel_snoc; assumption. }
            { rewrite Hk1; apply tele_prefix_rel_snoc; assumption. }
            rewrite <- !List.app_assoc in P1, P2; cbn in P1, P2.
            (** The telescope and the prefixes, one argument more. *)
            replace (List.rev (im_nparams Mv) ++ cargs_nonrec_tele (gs1 ++ ca_arg rA A :: nil))
              with ((List.rev (im_nparams Mv) ++ cargs_nonrec_tele gs1) ++ ce_ass rA A :: nil) in F1, F2, I1, I2, Hia, Hir
              by (rewrite cargs_nonrec_tele_snoc_arg, List.app_assoc; reflexivity).
            replace (nsa ++ wsa ++ ⇑! a1 s :: nil) with ((nsa ++ wsa) ++ ⇑! a1 s :: nil) in F1, I1, Hia, Hir
              by (rewrite List.app_assoc; reflexivity).
            replace (nsb ++ wsb ++ ⇑! a2 s :: nil) with ((nsb ++ wsb) ++ ⇑! a2 s :: nil) in F2, I2, Hia, Hir
              by (rewrite List.app_assoc; reflexivity).
            rewrite (components_env_snoc _ _ _ _ _ _ _ LT1) in F1, I1; rewrite (components_env_snoc _ _ _ _ _ _ _ LT2) in F2, I2.
            refine (mk_args_pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ (⇑! a1 s :: vsa) (⇑! a2 s :: vsb)
                      ihsa ihsb wa wb wfu
                      _ _ _ _ _ _ _ _ _ _).
            * econstructor; [ exact E1 | exact F1 ].
            * econstructor; [ exact E2 | exact F2 ].
            * constructor; exact I1.
            * constructor; exact I2.
            * eapply wrap_ihs_eval_arg; exact W1.
            * eapply wrap_ihs_eval_arg; exact W2.
            * exact P1.
            * exact P2.
            * constructor; exact Hia.
            * constructor; exact Hir.
          + (** Nested through: the eliminator's recursive result at the
                fresh variable. *)
            destruct Hno as [Hlt Hno].
            inversion C1 as [| | k0 Ta0 ws0 ws0' ρ0 ρ0' s0 t0 gs0 HR1 HD1 C1']; subst.
            inversion C2 as [| | k0 Ta0 ws0 ws0' ρ0 ρ0' s0 t0 gs0 HR2 HD2 C2']; subst.
            (** The shape's components' environments, as one telescope. *)
            pose proof (fun X T2 vs2 => components_env_tele X _ T2 _ vs2 LTu) as CEu.
            pose proof (fun X T2 vs2 => components_env_tele X _ T2 _ vs2 LT1) as CE1.
            pose proof (fun X T2 vs2 => components_env_tele X _ T2 _ vs2 LT2) as CE2.
            setoid_rewrite CEu in HR1; setoid_rewrite CE1 in HR1; setoid_rewrite <- List.app_assoc in HR1.
            setoid_rewrite CEu in HD1; setoid_rewrite CE1 in HD1; setoid_rewrite <- List.app_assoc in HD1.
            setoid_rewrite CEu in HR2; setoid_rewrite CE2 in HR2; setoid_rewrite <- List.app_assoc in HR2.
            setoid_rewrite CEu in HD2; setoid_rewrite CE2 in HD2; setoid_rewrite <- List.app_assoc in HD2.
            assert (Hc' : ind_con Mv c = Some (gs1 ++ ca_rec t :: gs)) by exact Hc.
            pose proof (Hma (ptyp_mem t)) as Me1; pose proof (Hmb (ptyp_mem t)) as Me2.
            destruct (shape_type_exists ua v Mv c gs1 t gs nsu nsa wsu wsa HM Hc' Me1 HR1 HD1 0 nil nil ltac:(lia)
                        (tele_prefix_rel_nil _)) as [a1 Ea1].
            destruct (shape_type_exists ub v Mv c gs1 t gs nsu nsb wsu wsb HM Hc' Me2 HR2 HD2 0 nil nil ltac:(lia)
                        (tele_prefix_rel_nil _)) as [a2 Ea2].
            pose proof (shape_neut ua ub v Mv c gs1 t gs nsu nsa nsb wsu wsa wsb Ha Hb La Lb HM Hc' Me1 Me2
                          (fun Mj qr Is fl cups1 cups2 e e' => Hrneut (ptyp_mem t) Mj qr Is fl cups1 cups2 e e')
                          Hn1 Hn2 Hw1 Hw2 HR1 HR2 HD1 HD2 (List.length (ptyp_doms t)) 0 nil nil nil a1 a2 (d_var s) (d_var s)
                          eq_refl (tele_prefix_rel_nil _) (tele_prefix_rel_nil _) Ea1 Ea2 var_per_bot) as Hsh.
            pose proof (shape_doms_fresh ua ub v Mv c gs1 t gs nsu nsa nsb wsu wsa wsb HAa HAb HM Hc' Hn1 Hn2 Hw1 Hw2 HD1 HD2
                          (List.length (ptyp_doms t)) 0 nil nil nil eq_refl (tele_prefix_rel_nil _) (tele_prefix_rel_nil _))
              as Hds.
            cbn [ptyp_skip] in Ea1, Ea2, Hsh, Hds.
            rewrite !List.app_nil_r in Ea1, Ea2; repeat rewrite List.app_nil_r in Hsh; repeat rewrite List.app_nil_r in Hds.
            rewrite List.app_assoc, (components_env_prefix _ _ _ _ _ LT1) in Ea1.
            rewrite List.app_assoc, (components_env_prefix _ _ _ _ _ LT2) in Ea2.
            (** Every path's result is the eliminator's, at a member of rank
                at most the argument's, below [r]. *)
            assert (Hfl : leaf_flags_ok elim_bot (List.map (fun _ => false) (shape_leaves (rview_leaves D) 0 t)) (shape_mems D t)).
            { apply leaf_flags_of_in; intros l Hin _; apply HIH.
              pose proof (leaf_mem_rank rk Hrk t 0 l Hin); lia. }
            destruct (proj1 (proj2 (proj2 ih_leaves_all)) _ _ _ _ _ _ _ _ _ Hsh eq_refl eq_refl ltac:(fresh_args_len) ltac:(fresh_args_len)
                        (ex_intro _ _ (ex_intro _ _ eq_refl)) (ex_intro _ _ (ex_intro _ _ eq_refl)) Hds _ Hfl)
              as [tya tyb ih ih' _ _ J1 J2 La1 Lb1 Lc1 Ld1 Hres].
            rewrite List.length_map in La1, Lb1, Lc1, Ld1.
            pose proof (Hres _ _ (leaf_results_all_nest _ _ _ _ _ La1 Lb1 Lc1 Ld1)) as Hres'.
            destruct (IH gs (gs1 ++ ca_rec t :: nil) wsu wsa wsb (S s) s2)
              as [vsa vsb ihsa ihsb wa wb wfu F1 F2 I1 I2 W1 W2 P1 P2 Hia Hir].
            { rewrite <- List.app_assoc; reflexivity. }
            { exact Hk. }
            { exact Hno. }
            { rewrite cargs_nonrec_tele_snoc_rec, cargs_nonrec_app, List.length_app; cbn [List.length cargs_nonrec];
              rewrite Nat.add_0_r; exact C1'. }
            { rewrite cargs_nonrec_tele_snoc_rec, cargs_nonrec_app, List.length_app; cbn [List.length cargs_nonrec];
              rewrite Nat.add_0_r; exact C2'. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact Hw1. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact Hw2. }
            rewrite cargs_nonrec_tele_snoc_rec in F1, F2, I1, I2, Hia, Hir.
            refine (mk_args_pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ (⇑! a1 s :: vsa) (⇑! a2 s :: vsb) ihsa ihsb (ih ++ wa) (ih' ++ wb) wfu
                      _ _ _ _ _ _ _ _ _ _).
            * econstructor; eassumption.
            * econstructor; eassumption.
            * apply fresh_ihs_nest; exact I1.
            * apply fresh_ihs_nest; exact I2.
            * eapply wrap_ihs_eval_nest; [ exact J1 | exact W1 ].
            * eapply wrap_ihs_eval_nest; [ exact J2 | exact W2 ].
            * exact P1.
            * exact P2.
            * eapply con_args_rec; [ exact Hsh | exact Hia ].
            * eapply rec_results_rec; [ exact Lc1 | exact Ld1 | exact Hres' | exact Hir ].
          + (** Recursive in both: along each path, a fresh recursive
                result where the path is the container's, the
                eliminator's where it is not. *)
            destruct Hno as [Hlv Hno].
            inversion C1 as [| | k0 Ta0 ws0 ws0' ρ0 ρ0' s0 t0 gs0 HR1 HD1 C1']; subst.
            inversion C2 as [| | k0 Ta0 ws0 ws0' ρ0 ρ0' s0 t0 gs0 HR2 HD2 C2']; subst.
            (** The shape's components' environments, as one telescope. *)
            pose proof (fun X T2 vs2 => components_env_tele X _ T2 _ vs2 LTu) as CEu.
            pose proof (fun X T2 vs2 => components_env_tele X _ T2 _ vs2 LT1) as CE1.
            pose proof (fun X T2 vs2 => components_env_tele X _ T2 _ vs2 LT2) as CE2.
            setoid_rewrite CEu in HR1; setoid_rewrite CE1 in HR1; setoid_rewrite <- List.app_assoc in HR1.
            setoid_rewrite CEu in HD1; setoid_rewrite CE1 in HD1; setoid_rewrite <- List.app_assoc in HD1.
            setoid_rewrite CEu in HR2; setoid_rewrite CE2 in HR2; setoid_rewrite <- List.app_assoc in HR2.
            setoid_rewrite CEu in HD2; setoid_rewrite CE2 in HD2; setoid_rewrite <- List.app_assoc in HD2.
            assert (Hc' : ind_con Mv c = Some (gs1 ++ ca_rec t :: gs)) by exact Hc.
            pose proof (Hma (ptyp_mem t)) as Me1; pose proof (Hmb (ptyp_mem t)) as Me2.
            destruct (shape_type_exists ua v Mv c gs1 t gs nsu nsa wsu wsa HM Hc' Me1 HR1 HD1 0 nil nil ltac:(lia)
                        (tele_prefix_rel_nil _)) as [a1 Ea1].
            destruct (shape_type_exists ub v Mv c gs1 t gs nsu nsb wsu wsb HM Hc' Me2 HR2 HD2 0 nil nil ltac:(lia)
                        (tele_prefix_rel_nil _)) as [a2 Ea2].
            pose proof (shape_neut ua ub v Mv c gs1 t gs nsu nsa nsb wsu wsa wsb Ha Hb La Lb HM Hc' Me1 Me2
                          (fun Mj qr Is fl cups1 cups2 e e' => Hrneut (ptyp_mem t) Mj qr Is fl cups1 cups2 e e')
                          Hn1 Hn2 Hw1 Hw2 HR1 HR2 HD1 HD2 (List.length (ptyp_doms t)) 0 nil nil nil a1 a2 (d_var s) (d_var s)
                          eq_refl (tele_prefix_rel_nil _) (tele_prefix_rel_nil _) Ea1 Ea2 var_per_bot) as Hsh.
            pose proof (shape_doms_fresh ua ub v Mv c gs1 t gs nsu nsa nsb wsu wsa wsb HAa HAb HM Hc' Hn1 Hn2 Hw1 Hw2 HD1 HD2
                          (List.length (ptyp_doms t)) 0 nil nil nil eq_refl (tele_prefix_rel_nil _) (tele_prefix_rel_nil _))
              as Hds.
            cbn [ptyp_skip] in Ea1, Ea2, Hsh, Hds.
            rewrite !List.app_nil_r in Ea1, Ea2; repeat rewrite List.app_nil_r in Hsh; repeat rewrite List.app_nil_r in Hds.
            rewrite List.app_assoc, (components_env_prefix _ _ _ _ _ LT1) in Ea1.
            rewrite List.app_assoc, (components_env_prefix _ _ _ _ _ LT2) in Ea2.
            set (bs := List.map (leaf_in Dh t') (shape_leaves (rview_leaves D) 0 t)).
            assert (Hfl : leaf_flags_ok elim_bot bs (shape_mems D t))
              by (apply leaf_flags_of_in; intros l Hin Hn; apply HIH; exact (Hlv l Hin Hn)).
            destruct (proj1 (proj2 (proj2 ih_leaves_all)) _ _ _ _ _ _ _ _ _ Hsh eq_refl eq_refl ltac:(fresh_args_len) ltac:(fresh_args_len)
                        (ex_intro _ _ (ex_intro _ _ eq_refl)) (ex_intro _ _ (ex_intro _ _ eq_refl)) Hds bs Hfl)
              as [tya tyb resa resb G1 G2 J1 J2 La1 Lb1 Lc1 Ld1 Hres].
            destruct (fresh_wrap_results bs tya tyb resa resb s2 La1 Lb1 Lc1 Ld1)
              as (ihs1 & ihs2 & out & out' & V1 & V2 & Li & X1 & X2 & Ho).
            destruct (IH gs (gs1 ++ ca_rec t :: nil) wsu wsa wsb (S s) (List.length ihs1 + s2))
              as [vsa vsb ihsa ihsb wa wb wfu F1 F2 I1 I2 W1 W2 P1 P2 Hia Hir].
            { rewrite <- List.app_assoc; reflexivity. }
            { exact Hk. }
            { exact Hno. }
            { rewrite cargs_nonrec_tele_snoc_rec, cargs_nonrec_app, List.length_app; cbn [List.length cargs_nonrec];
              rewrite Nat.add_0_r; exact C1'. }
            { rewrite cargs_nonrec_tele_snoc_rec, cargs_nonrec_app, List.length_app; cbn [List.length cargs_nonrec];
              rewrite Nat.add_0_r; exact C2'. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact Hw1. }
            { rewrite cargs_nonrec_app, List.length_app; cbn; rewrite Nat.add_0_r; exact Hw2. }
            rewrite cargs_nonrec_tele_snoc_rec in F1, F2, I1, I2, Hia, Hir.
            refine (mk_args_pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ (⇑! a1 s :: vsa) (⇑! a2 s :: vsb) (ihs1 ++ ihsa) (ihs2 ++ ihsb)
                      (out ++ wa) (out' ++ wb) wfu _ _ _ _ _ _ _ _ _ _).
            * econstructor; eassumption.
            * econstructor; eassumption.
            * eapply fresh_ihs_rec; [ exact Hl | exact G1 | exact V1 | exact I1 ].
            * eapply fresh_ihs_rec; [ exact Hl | exact G2 | exact V2 | rewrite <- Li; exact I2 ].
            * eapply wrap_ihs_eval_rec; [ exact Hl | exact J1 | apply X1 | exact W1 ].
            * eapply wrap_ihs_eval_rec; [ exact Hl | exact J2 | apply X2 | exact W2 ].
            * exact P1.
            * exact P2.
            * eapply con_args_rec; [ exact Hsh | exact Hia ].
            * destruct (leaf_results_length _ _ _ _ _ _ _ Ho) as [Lo Lo'].
              unfold bs in Lo, Lo'; rewrite List.length_map in Lo, Lo'.
              econstructor; [ exact Lo | exact Lo' | exact (Hres _ _ Ho) | exact Hir ].
      Qed.

      (** What a constructor of the member read, of arguments [gs'], asks of
          this group's constructor of arguments [gs] it is read as: kinds
          compatible, the fresh recursive results as many as the branch
          read binds, and the paths nested through ending at members of
          rank below [r]. *)
      Record member_pair_con (Dc : ind_decl) (rk : nat -> nat) (r : nat) (gs' gs : list carg) : Prop :=
        mk_member_pair_con
        { (** The arguments' kinds are compatible *)
          member_pair_con_kinds : cargs_same_kinds gs' gs
          (** The group's leaf paths [Dc] has are as many as [Dc]'s branch
              binds *)
        ; member_pair_con_count : cargs_container_count D Dc gs' gs = cargs_nrec Dc gs'
          (** The paths nested through end at members of rank below [r] *)
        ; member_pair_con_nest : cargs_nest_ok D Dc rk r gs' gs }.

      (** *** The Blocks

          Each block of a stuck eliminator: the one of the member [Mi] of
          the group read, the block of the member [Mv] of this group
          [elim_src sel i0] gives, at admissible uniform parameters [ua] and
          [ub], when [Mv]'s constructors are [Mi]'s and their arguments of
          compatible kinds, and the eliminator's results at the members
          the arguments nested through end in are related. *)
      Lemma member_pair_of : forall s Dc sel i0 Mi Mv (rk : nat -> nat) r,
          adm_fresh p D ups nr ar dr ua -> adm_fresh p D ups nr ar dr ub ->
          List.length ua = ind_nu D -> List.length ub = ind_nu D -> mrefs_ok ua -> mrefs_ok ub ->
          ind_member D (elim_src sel i0) = Some Mv -> im_is_rview Mv = false -> im_nn Mv = im_nn Mi ->
          List.map fst (im_cons Mi) = List.map fst (im_cons Mv) ->
          (forall c gs' gs, List.In (c, gs') (im_cons Mi) -> ind_con Mv c = Some gs -> member_pair_con Dc rk r gs' gs) ->
          view_rank_ok gc_deps gc_stack D rk -> (forall j, rk j < r -> elim_bot j) ->
          member_pair s Dc sel i0 Mi.
      Proof.
        intros s Dc sel i0 Mi Mv rk r Ha Hb La Lb Hma Hmb HM Hrv Hnn Hnames Hcs Hrk HIH.
        pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
        pose proof (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as ttrans.
        pose proof (nparams_rel_refl_l p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl.
        pose proof (nparams_rel_refl_r p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as trefl_r.
        destruct (proj1 (Hma _ _ HM) Hrv) as [[[hd1 k1] pre1] R1].
        destruct (proj1 (Hmb _ _ HM) Hrv) as [[[hd2 k2] pre2] R2].
        destruct (mref_at_end_adm _ La _ _ _ _ R1) as [Mj HMj Href1 Hlen1 _].
        rewrite HM in HMj; injection HMj as <-.
        destruct (mref_at_end_adm _ Lb _ _ _ _ R2) as [Mj HMj Href2 Hlen2 _].
        rewrite HM in HMj; injection HMj as <-.
        rewrite Href1 in Href2; injection Href2 as <- <-.
        destruct (fresh_tele_rel_ftele _ _ _ _ _ _ _ _ (adm_fresh_nparams _ _ _ _ _ _ _ Ha _ Mv s HM)) as [nsu nsa Fu Fa Lu Hua].
        destruct (fresh_tele_rel_ftele _ _ _ _ _ _ _ _ (adm_fresh_nparams _ _ _ _ _ _ _ Hb _ Mv s HM)) as [nsu' nsb Fu' Fb _ Hub].
        rewrite ?List.app_nil_r in Fu, Fa, Fu', Fb.
        pose proof (functional_fresh_tele' _ _ _ _ _ Fu Fu') as <-.
        assert (Hn1 : tele_rel (nr (elim_src sel i0)) (List.rev (im_nparams Mv)) nsu nsa) by (split; assumption).
        assert (Hn2 : tele_rel (nr (elim_src sel i0)) (List.rev (im_nparams Mv)) nsu nsb) by (split; assumption).
        pose proof (ttrans _ _ HM _ _ _ (tsym _ _ HM _ _ Hn1) Hn2) as Hab.
        pose proof Hab as Lab; rewrite tele_rel_iff in Lab; destruct Lab as (Lna & Lnb & _).
        rewrite List.length_rev in Lna, Lnb.
        refine (mk_member_pair s Dc sel i0 Mi Mv HM Hrv Hnn hd1 k1 pre1 pre2 R1 R2 Hlen1 Hlen2 nsa nsb Fa Fb _ Hnames _).
        - eapply ind_rel_neut; [ exact HM | exact Hrv | exact Href1 | exact Hab | | | | | exact var_per_bot ].
          + rewrite List.length_app, Hlen1; unfold im_nn in *; lia.
          + rewrite List.length_app, Hlen2; unfold im_nn in *; lia.
          + rewrite skipn_app_exact by exact Hlen1; exact (trefl _ _ HM _ _ Hab).
          + rewrite skipn_app_exact by exact Hlen2; exact (trefl_r _ _ HM _ _ Hab).
        - intros c gs' Hin.
          assert (HinN : List.In c (List.map fst (im_cons Mv)))
            by (rewrite <- Hnames; apply List.in_map_iff; exists (c, gs'); split; [ reflexivity | exact Hin ]).
          destruct (cons_lookup_names _ _ HinN) as [gs Hc].
          destruct (Hcs c gs' gs Hin Hc) as [Hk Hcnt Hno].
          pose proof (grp_tele_ass_params_length _ Hass _ _ _ _ HM (cons_lookup_in _ _ _ Hc)) as Hpl.
          exists gs; split; [ exact Hc | split; [ exact Hpl | split; [ exact Hcnt | split; [ symmetry; exact (cargs_same_kinds_length _ _ Hk) |] ] ] ].
          pose proof (adm_fresh_args _ _ _ _ _ _ _ Ha _ Mv c gs s nsu nsa HM Hc Fu Fa) as C1.
          pose proof (adm_fresh_args _ _ _ _ _ _ _ Hb _ Mv c gs s nsu nsb HM Hc Fu Fb) as C2.
          destruct (fresh_args _ Mv c gs nsu nsa nsb Dc rk r Ha Hb La Lb Hma Hmb HM Hc Hpl Hn1 Hn2 Hrk HIH
                      gs' gs nil nil nil nil (s + im_nn Mv) (s + im_nn Mv + List.length gs') eq_refl Hk Hno
                      ltac:(cbn [cargs_nonrec_tele cargs_nonrec List.map]; rewrite ?List.app_nil_r; exact C1)
                      ltac:(cbn [cargs_nonrec_tele cargs_nonrec List.map]; rewrite ?List.app_nil_r; exact C2)
                      (tele_prefix_rel_nil _) (tele_prefix_rel_nil _))
            as [vsa vsb ihsa ihsb wa wb wfu F1 F2 I1 I2 W1 W2 P1 P2 Hia Hir].
          cbn [cargs_nonrec_tele cargs_nonrec List.map] in F1, F2, I1, I2, Hia, Hir.
          rewrite ?List.app_nil_r in F1, F2, I1, I2.
          repeat rewrite List.app_nil_r in Hia; repeat rewrite List.app_nil_r in Hir.
          cbn [List.app] in P1, P2.
          rewrite Hnn in F1, F2, I1, I2.
          refine (mk_brs_pair s _ Mv Mi hd1 Dc k1 pre1 pre2 nsa nsb c gs' gs vsa vsb ihsa ihsb wa wb F1 F2 I1 I2 W1 W2 _ Hir).
          rewrite !List.app_assoc; eapply ind_rel_con; [ exact HM | exact Hrv | exact Href1 | exact Hab | exact Hc | | | | | |].
          + rewrite List.length_app, Hlen1; unfold im_nn in *; lia.
          + rewrite List.length_app, Hlen2; unfold im_nn in *; lia.
          + rewrite skipn_app_exact by exact Hlen1; exact (trefl _ _ HM _ _ Hab).
          + rewrite skipn_app_exact by exact Hlen2; exact (trefl_r _ _ HM _ _ Hab).
          + rewrite skipn_app_exact by exact Hlen1.
            pose proof (trefl _ _ HM _ _ Hn1) as Huu.
            destruct P1 as [Lw1 Rw1]; destruct P2 as [Lw2 Rw2].
            assert (Q1 : tele_rel (ar (elim_src sel i0) nsu c) (cargs_nonrec gs) wfu (nonrec_arg_vals gs vsa)) by (split; assumption).
            assert (Q2 : tele_rel (ar (elim_src sel i0) nsu c) (cargs_nonrec gs) wfu (nonrec_arg_vals gs vsb)) by (split; assumption).
            apply (args_rel_inst p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ Mv HM nsu nsa c gs _ _ Hn1 Hc).
            exact (args_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ Mv HM nsu c gs Huu Hc _ _ _
                     (args_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ Mv HM nsu c gs Huu Hc _ _ Q1) Q2).
          + rewrite !skipn_app_exact by assumption; exact Hia.
      Qed.

      (** *** The Stuck Eliminator at a Member

          Read as the eliminator of the group its member is at (E1′: the
          container's, at a view), under fresh variables of this group's
          members' telescopes at the uniform parameters it carries (model
          P), when the stuck eliminators at the members of lower rank read
          back alike; with the container's uniform parameters at them. *)
      Lemma per_bot_elim_rank :
          forall j Mj rk u u' ns ns' hd k' as1 as2 e e', ind_member D j = Some Mj -> im_is_rview Mj = false ->
          view_rank_ok gc_deps gc_stack D rk -> (forall j', rk j' < rk j -> elim_bot j') ->
          grp_rel p D ups nr ar dr j u u' ns ns' (⇑ (d_ind hd k' as1) e) (⇑ (d_ind hd k' as2) e') ->
          Dom d_elim ρa Bksa p ua j as1 e ≈ d_elim ρb Bksb p ub j as2 e' ∈ per_bot.
      Proof.
        intros * HM Hrvj Hrk HIH Hm.
        destruct Hups as [La Lb Ca Cb Ma Mb Hcu _ _ _ _ _].
        pose proof (adm_fresh_of_uparams p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ua Ca) as Ha.
        pose proof (adm_fresh_of_uparams p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI ub Cb) as Hb.
        inversion Hm as [| j0 Mj0 hd0 k0 ns0 ns0' as1' as2' e0 e0' u0 u0' HM0 Hrv0 Hr Hn L1 L2 Hs1 Hs2 He |]; subst;
          [| no_rview_rel ].
        rewrite HM in HM0; injection HM0 as <-.
        destruct (im_ref_target _ _ _ _ HM Hr) as (Dq & Mk & Hq & HMk & Hnnq & Hnuq).
        (** The blocks: one per member of the group read that has one, the
            block of the member of this group the view takes it to. *)
        assert (HMP : forall s n Mi, List.nth_error (ind_block_members Dq) n = Some Mi -> member_pair s Dq (im_sel Mj) n Mi).
        { intros s n Mi Hb0; destruct (ind_block_members_member _ _ _ Hb0) as [Hn0 Hlt].
          destruct (im_head Mj) as [pm | qc kc Is vm | qr Is fl] eqn:Hh;
            [| | exfalso; exact (not_rview_record _ _ _ _ Hrvj Hh) ].
          - unfold im_ref in Hr; rewrite Hh in Hr; injection Hr as <- <-.
            rewrite Hl in Hq; injection Hq as <-.
            assert (Hsel : im_sel Mj = None) by (unfold im_sel; rewrite Hh; reflexivity); rewrite Hsel.
            assert (Hrvi : im_is_rview Mi = false)
              by (destruct (im_is_rview Mi) eqn:E; [ apply (rview_struct_suffix _ _ _ Hrs _ _ Hn0) in E; lia | reflexivity ]).
            apply (member_pair_of s D None n Mi Mi rk (rk j) Ha Hb La Lb Ma Mb Hn0 Hrvi eq_refl eq_refl); [| exact Hrk | exact HIH ].
            intros c gs' gs Hin Hc.
            assert (gs = gs') as ->
              by (pose proof (cons_lookup_nodup_in _ _ _ (Hnd _ _ Hn0) Hin) as Hc0; unfold ind_con in Hc; congruence).
            constructor; [ apply cargs_same_kinds_refl | | exact (cargs_nest_ok_own rk (rk j) _ _ _ _ Hn0 Hc) ].
            exact (cargs_container_count_own _ (grp_tele_ass_params_length _ Hass _ _ _ _ Hn0 (cons_lookup_in _ _ _ Hc))).
          - unfold im_ref in Hr; rewrite Hh in Hr; injection Hr as <- <-.
            assert (Hsel : im_sel Mj = Some vm) by (unfold im_sel; rewrite Hh; reflexivity); rewrite Hsel.
            destruct (grp_tele_ass_vm _ Hass j Mj qc kc Is vm Dq n Mi HM Hh Hq Hn0) as [v Mv Hvm HMv Hnn Hhm].
            destruct (grp_tele_ass_view_wrap _ Hass j Mj qc kc Is vm HM Hh) as (D' & Hq' & Hvw).
            rewrite Hq in Hq'; injection Hq' as <-.
            destruct (view_wrap_ok_members _ _ _ Hvw n Mi v Hn0 Hvm) as (Mv' & HMv' & _ & Hnames & Hcorr).
            rewrite HMv in HMv'; injection HMv' as <-.
            (** The container's member has a block, so is no record view,
                nor is its image. *)
            assert (Hrvi : im_is_rview Mi = false)
              by (destruct (im_is_rview Mi) eqn:E;
                  [ apply (grp_tele_ass_csuffix _ Hass _ _ _ _ _ _ _ HM Hh Hq _ _ Hn0) in E; lia | reflexivity ]).
            assert (Hrvv : im_is_rview Mv = false).
            { unfold im_is_rview in Hrvi |- *; destruct (im_head Mi) eqn:Hhi; try discriminate Hrvi.
              - destruct Hhm as [vm' ->]; reflexivity.
              - destruct Hhm as (Is' & vm' & -> & _); reflexivity. }
            assert (Hsrc : elim_src (Some vm) n = v) by (cbn; apply List.nth_error_nth; exact Hvm).
            apply (member_pair_of s Dq (Some vm) n Mi Mv rk (rk j) Ha Hb La Lb Ma Mb
                     ltac:(rewrite Hsrc; exact HMv) Hrvv Hnn (eq_sym Hnames)); [| exact Hrk | exact HIH ].
            intros c gs' gs Hin Hc.
            assert (Hc' : ind_con Mi c = Some gs')
              by (apply cons_lookup_nodup_in; [ rewrite <- Hnames; exact (Hnd _ _ HMv) | exact Hin ]).
            constructor; [ exact (cargs_same_kinds_of_correspond _ _ _ (Hcorr c gs' gs Hin Hc)) | |].
            (** as many of the group's paths are the container's as the
                container's branch binds *)
            { pose proof (grp_tele_ass_crstruct _ Hass _ _ _ _ _ _ _ HM Hh Hq) as HrsQ.
              exact (cargs_container_count_view p qc D Dq vm Hlc (leaves_coherent_of_order Dq (rview_struct_order _ _ _ HrsQ)) Hrs HrsQ
                       (view_members_of_ass p D j Mj qc kc Is vm Dq Hass HM Hh Hq) gs' gs (Hcorr c gs' gs Hin Hc)). }
            exact (view_rank_ok_nest _ _ _ _ Hrk j Mj qc kc Is vm Dq n Mi v Mv c gs' gs HM Hh Hq Hn0 Hvm HMv Hc' Hc). }
        assert (Hnm : forall Bks, (forall j1 Mj1 b, ind_member D j1 = Some Mj1 -> List.nth_error Bks j1 = Some b ->
                                     eb_binder_count b = S (im_nn Mj1)) ->
                   blocks_binder_count_at D None Bks) by (intros Bks HB i0 Mi b HMi Hb0; exact (HB _ _ _ HMi Hb0)).
        assert (Lq : List.length as1 = im_np Dq Mk /\ List.length as2 = im_np Dq Mk) by (unfold im_np; split; lia).
        intros s; destruct (He s) as [M M' RM1 RM2 HEM].
        destruct (read_blocks_rel s Dq (im_sel Mj) (ind_block_members Dq) 0) as (NBks & NBks' & RB1 & RB2 & HEB).
        { intros n Mi Hn0; exact (HMP s (0 + n) Mi Hn0). }
        destruct (proj1 (Ma _ _ HM) Hrvj) as [[[hd1 k1] pa] Ra]; destruct (proj1 (Mb _ _ HM) Hrvj) as [[[hd2 k2] pb] Rb].
        destruct (mref_at_end_adm _ La _ _ _ _ Ra) as [Mj1 HMj1 Hr1 _ _].
        rewrite HM in HMj1; injection HMj1 as <-; rewrite Hr in Hr1; injection Hr1 as <- <-.
        destruct (mref_at_end_adm _ Lb _ _ _ _ Rb) as [Mj1 HMj1 Hr1 _ _].
        rewrite HM in HMj1; injection HMj1 as <-; rewrite Hr in Hr1; injection Hr1 as <- <-.
        destruct (Hcu j Mj hd k' pa pb Dq HM Ra Rb Hq s) as [Us Us' RU1 RU2 HEU].
        apply (mk_neutral_reads_alike _ _ _ (ne_elim hd Us k' NBks M) (ne_elim hd Us' k' NBks' M')).
        - eapply read_ne_elim; [ exact Hl | exact HM | exact Hr | exact Hq | exact HMk | exact (proj1 Lq)
                               | exact (Hnm _ HnmA) | exact (grp_tele_ass_leaf_arity _ Hass) | exact Ra | exact RU1 | exact RB1
                               | exact RM1 ].
        - eapply read_ne_elim; [ exact Hl | exact HM | exact Hr | exact Hq | exact HMk | exact (proj2 Lq)
                               | exact (Hnm _ HnmB) | exact (grp_tele_ass_leaf_arity _ Hass) | exact Rb | exact RU2 | exact RB2
                               | exact RM2 ].
        - cbn [ne_erase]; rewrite HEU, HEB, HEM; reflexivity.
      Qed.

      (** ** The Stuck Eliminator

          By strong induction on the rank: a view's readback reads the
          eliminator at members of lower rank at the positions it nests
          through. *)
      Theorem per_bot_elim : forall j, elim_bot j.
      Proof.
        destruct (grp_tele_ass_rank _ Hass) as [rk Hrk].
        assert (H : forall r j, rk j < r -> elim_bot j).
        { induction r as [| r IH]; intros j Hj; [ lia |].
          intros Mj hd k' as1 as2 e1 e1' w w' ns ns' HM Hrv Hm.
          apply (per_bot_elim_rank j Mj rk w w' ns ns' hd k' as1 as2 e1 e1' HM Hrv Hrk); [| exact Hm ].
          intros j' Hj'; apply IH; lia. }
        intros j; exact (H (S (rk j)) j ltac:(lia)).
      Qed.

      (** The recursive results of a function shape, applied: those of the
          rest at the function's value. *)
      Lemma ihfn_apps : forall ρ Bks u t f c fc rcs, $| f & c | gc_deps ⍮ gc_stack ↘ fc ->
          ⟦ih fc of t under p u Bks ⟧ gc_deps ⍮ gc_stack ⍮ ρ ↘ rcs ->
          List.Forall2 (fun g r => $| g & c | gc_deps ⍮ gc_stack ↘ r)
            (List.map (fun i => d_ihfn ρ Bks p u t i f) (List.seq 0 (List.length rcs))) rcs.
      Proof.
        intros * Ef Eh.
        apply Forall2_of_nth; [ rewrite List.length_map, List.length_seq; reflexivity |].
        intros x g r Hg Hr.
        rewrite List.nth_error_map in Hg.
        assert (Hi : x < List.length rcs) by (apply List.nth_error_Some; congruence).
        rewrite List.nth_error_seq in Hg; apply Nat.ltb_lt in Hi; rewrite Hi in Hg; cbn in Hg; injection Hg as <-.
        eapply eval_app_ihfn; [ exact Ef | exact Eh | exact Hr ].
      Qed.

      (** ** Related Elements Eliminate to Related Values

          At any bases [u] and [u'] admissible beside [ups]: a branch's
          entries are read back at [ua]'s and [ub]'s types, which the
          elements at those bases are elements of ([elim_ups_ok]).  For
          [Vec] eliminated at [w1] and a scrutinee [cons n x xs] at the
          type's bases, the branch binds [xs] at [Vec] at [w1]: it reads
          back there because the type's bases are admissible. *)
      Theorem per_ind_elim_all :
        (forall j u u' ns ns' m m', grp_rel p D ups nr ar dr j u u' ns ns' m m' ->
           adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' -> member_results j u u' ns ns' m m') /\
        (forall k u u' pre pre' Ts gs vs vs',
           con_args_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts gs vs vs' ->
           adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' ->
           exists ihs ihs', ⟦ihs vs of gs under p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ ihs /\
             ⟦ihs vs' of gs under p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ ihs' /\
             rec_results_rel k u u' pre pre' Ts gs vs vs' ihs ihs') /\
        (forall k u u' pre pre' Ts t v v',
           rec_arg_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts t v v' ->
           adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' ->
           exists rs rs', ⟦ih v of t under p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ rs /\
             ⟦ih v' of t under p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ rs' /\
             rec_result_rel k u u' pre pre' Ts t v v' rs rs') /\
        (forall k u u' pre pre' Ts t f c f' c',
           rec_arg_app_rel p D (admissible_index_at D ups nr) nr ar dr k u u' pre pre' Ts t f c f' c' ->
           adm_uparams D ups nr ar dr u -> adm_uparams D ups nr ar dr u' ->
           exists fc fc' rcs rcs', $| f & c | gc_deps ⍮ gc_stack ↘ fc /\ $| f' & c' | gc_deps ⍮ gc_stack ↘ fc' /\
             ⟦ih fc of t under p ua Bksa ⟧ gc_deps ⍮ gc_stack ⍮ ρa ↘ rcs /\
             ⟦ih fc' of t under p ub Bksb ⟧ gc_deps ⍮ gc_stack ⍮ ρb ↘ rcs' /\
             rec_result_rel k u u' pre pre' Ts t fc fc' rcs rcs').
      Proof.
        pose proof (nparams_rel_sym p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI) as tsym.
        apply ind_rel_mut_ind_all.
        - (** A constructor: its branch, at its own parameters, moved to
              the indices. *)
          intros * HM Hrv Href Hn Hc Lb Lb' Hs Hs' Ha Hia IH Hau Hau'.
          destruct (IH Hau Hau') as (ihs & ihs' & Ei & Ei' & Hir).
          destruct (HbA _ _ HM Hrv) as [ba HBka]; destruct (HbB _ _ HM Hrv) as [bb HBkb].
          destruct (brs_names_lookup _ _ _ _ (HnaA _ _ _ HM HBka) Hc) as (n & Ba & HBa & HinA).
          destruct (brs_names_lookup _ _ _ _ (HnaB _ _ _ HM HBkb) Hc) as (n' & Bb & HBb & HinB).
          pose proof (HarA _ _ _ _ _ _ _ HM HBka Hc HinA) as Hn0; pose proof (HarB _ _ _ _ _ _ _ HM HBkb Hc HinB) as Hn0'.
          assert (n' = n) as -> by lia.
          destruct (im_ref_target _ _ _ _ HM Href) as (Dq & Mq & Hq & HMq & Hnnq & Hnuq).
          destruct (con_args_rel_length _ _ _ _ _ _ _ _ _ _ Hia) as [Lv Lv'].
          match goal with |- member_results _ _ _ _ _ (d_con _ _ _ (?bs ++ ?vs)) (d_con _ _ _ (?bs' ++ ?vs')) =>
            assert (Hcur : grp_rel p D ups nr ar dr _ _ _ _ _ (d_con _ _ _ (bs ++ vs)) (d_con _ _ _ (bs' ++ vs')))
              by (eapply ind_rel_con; [ exact HM | exact Hrv | exact Href | exact Hn | exact Hc | exact Lb | exact Lb' | exact Hs | exact Hs'
                                     | exact Ha | exact Hia ]) end.
          pose proof (ind_rel_idx p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ _ _ _ _ _ _ _ _ _ HM Hcur Hs Hs') as Hm.
          (** The branch's entries read back at the types it binds them at. *)
          pose proof (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ _
                        (tsym _ _ HM _ _ Hs) (nparams_rel_trans p D ups nr ar dr Hass HnP HnI HaP HaI HdP HdI _ _ HM _ _ _ Hn Hs'))
            as Hss.
          destruct (branch_entries_readable _ _ _ _ _ _ _ _ _ _ _ _ Hau Hau' HM Hc Hss Ha Hia Hir) as [Ba1 Ba2].
          destruct (Hbr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hrv HBka HBkb Hc HBa HBb Hm Hir Ba1 Ba2)
            as (r & r' & Er & Er' & Hrr).
          rewrite branch_env_combine in Er, Er'.
          apply (member_results_elim _ _ _ _ _ _ _ Mk r r' HM Hrv).
          + eapply eval_elim_con; [ exact Hl | exact HM | exact Href | exact Hq | exact HMq | exact Hc
                                  | rewrite List.length_app; unfold im_np; lia | exact HBka | exact HBa | rewrite Hnnq; exact Hn0 | exact Hlc | |].
            * rewrite skipn_app_exact by (unfold im_np; lia); exact Ei.
            * rewrite firstn_app_exact, skipn_app_exact, Hnuq by (unfold im_np; lia); exact Er.
          + eapply eval_elim_con; [ exact Hl | exact HM | exact Href | exact Hq | exact HMq | exact Hc
                                  | rewrite List.length_app; unfold im_np; lia | exact HBkb | exact HBb | rewrite Hnnq; exact Hn0 | exact Hlc | |].
            * rewrite skipn_app_exact by (unfold im_np; lia); exact Ei'.
            * rewrite firstn_app_exact, skipn_app_exact, Hnuq by (unfold im_np; lia); exact Er'.
          + apply (motive_rel_move _ _ _ _ _ _ _ _ _ _ HM Hrv Hm (tsym _ _ HM _ _ Hs) (tsym _ _ HM _ _ Hs')); exact Hrr.
        - (** A neutral: stuck, its readbacks agree. *)
          intros k Mk hd k' ns ns' as1 as2 m m' u0 u0' HM Hrv Href Hn L1 L2 Hs1 Hs2 He _ _.
          assert (Hm : grp_rel p D ups nr ar dr _ u0 u0' _ _ _ _)
            by (eapply ind_rel_neut; [ exact HM | exact Hrv | exact Href | exact Hn | exact L1 | exact L2 | exact Hs1
                                     | exact Hs2 | exact He ]).
          destruct (neut_elim_rel _ _ u0 u0' _ _ _ _ _ _ _ _ HM Hrv Hm (per_bot_elim _ _ _ _ _ _ _ _ u0 u0' _ _ HM Hrv Hm))
            as (r & r' & Er & Er' & Hrr).
          exact (member_results_elim _ _ _ _ _ _ _ Mk r r' HM Hrv Er Er' Hrr).
        - (** A record view: its fields' recursive results. *)
          intros * HM Hh Hnp Hcs Hp Hp' Ha Hia IH Hau Hau'; destruct (IH Hau Hau') as (ihs & ihs' & Ei & Ei' & Hir).
          exact (member_results_rview _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM Hh Hcs Hp Hp' Ei Ei' Hir).
        - intros; exists nil, nil; split; [ constructor | split; [ constructor | constructor ] ].
        - intros * Hia IH Hau Hau'; destruct (IH Hau Hau') as (ihs & ihs' & Ei & Ei' & Hir).
          exists ihs, ihs'; split; [ constructor; exact Ei | split; [ constructor; exact Ei' | constructor; exact Hir ] ].
        - intros * Hsh IHs Hia IH Hau Hau'.
          destruct (IHs Hau Hau') as (rs & rs' & Eh & Eh' & Hhh); destruct (IH Hau Hau') as (ihs & ihs' & Ei & Ei' & Hir).
          exists (rs ++ ihs), (rs' ++ ihs'); split; [ econstructor; eassumption | split; [ econstructor; eassumption |] ].
          pose proof (proj1 (proj2 (eval_ih_length_all (Θ := gc_deps) (Ξ := gc_stack))) _ _ _ _ _ _ _ Eh _ Hl Hlc) as Lr.
          pose proof (proj1 (proj2 (eval_ih_length_all (Θ := gc_deps) (Ξ := gc_stack))) _ _ _ _ _ _ _ Eh' _ Hl Hlc) as Lr'.
          econstructor; eassumption.
        - (** The end of a shape: the eliminator at a member with a block, the
              fields' results at a record view. *)
          intros * Hb Hb' Ok Ok' Hr IHr Hau Hau'.
          destruct (IHr Hau Hau') as [Mj r r' HMj Hrv Er Er' Hrr | Mj qr Is fl c gs ws ws' rs rs' HMj Hh Hcs Hp Hp' Ei Ei' Hir].
          + exists (r :: nil), (r' :: nil); split; [ eapply eval_ih_self; eassumption | split; [ eapply eval_ih_self; eassumption |] ].
            eapply rec_result_self; [ exact HMj | exact Hrv | exact Hb | exact Hb' | exact Hrr ].
          + exists rs, rs'; split; [ eapply eval_ih_rview; eassumption | split; [ eapply eval_ih_rview; eassumption |] ].
            eapply rec_result_rview; eassumption.
        - (** A function shape: the families, at each leaf path. *)
          intros * Hf IH _ _ Hau Hau'.
          match goal with |- exists rs rs', ⟦ih ?f of pt_pi _ ?t under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ rs /\
                                            ⟦ih ?f' of _ under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ rs' /\ _ =>
            exists (List.map (fun i => d_ihfn ρa Bksa p ua t i f) (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t)))),
                   (List.map (fun i => d_ihfn ρb Bksb p ub t i f') (List.seq 0 (List.length (shape_leaves (rview_leaves D) 0 t)))) end.
          split; [ eapply eval_ih_pi; exact Hl | split; [ eapply eval_ih_pi; exact Hl |] ].
          constructor;
            [| apply List.Forall_forall; intros r0 Hr0; apply List.in_map_iff in Hr0 as (i0 & <- & _); reflexivity
             | apply List.Forall_forall; intros r0 Hr0; apply List.in_map_iff in Hr0 as (i0 & <- & _); reflexivity ].
          intros c c' Hcc.
          destruct (IH c c' Hcc Hau Hau') as (fc & fc' & rcs & rcs' & Ef & Ef' & Er & Er' & Hrr).
          pose proof (proj1 (proj2 (eval_ih_length_all (Θ := gc_deps) (Ξ := gc_stack))) _ _ _ _ _ _ _ Er _ Hl Hlc) as Lr.
          pose proof (proj1 (proj2 (eval_ih_length_all (Θ := gc_deps) (Ξ := gc_stack))) _ _ _ _ _ _ _ Er' _ Hl Hlc) as Lr'.
          econstructor; [ exact Ef | exact Ef' | | | exact Hrr ].
          + rewrite <- Lr; exact (ihfn_apps _ _ _ _ _ _ _ _ Ef Er).
          + rewrite <- Lr'; exact (ihfn_apps _ _ _ _ _ _ _ _ Ef' Er').
        - intros * Ef Ef' Hsh IH Hau Hau'; destruct (IH Hau Hau') as (rs & rs' & Eh & Eh' & Hhh).
          do 4 eexists; split; [ exact Ef | split; [ exact Ef' | split; [ exact Eh | split; [ exact Eh' | exact Hhh ] ] ] ].
      Qed.
    End ElimRel.
  End ElimGroup.
End Fixed_GCtx.

Scheme rec_result_rel_mut_ind := Induction for rec_result_rel Sort Prop
with rec_result_app_rel_mut_ind := Induction for rec_result_app_rel Sort Prop
with rec_results_rel_mut_ind := Induction for rec_results_rel Sort Prop.
Combined Scheme rec_result_rel_mut_ind_all from rec_result_rel_mut_ind, rec_result_app_rel_mut_ind, rec_results_rel_mut_ind.
