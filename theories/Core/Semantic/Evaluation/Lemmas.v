From Stdlib Require Import Lia PeanoNat Relations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members Records.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic.Evaluation Require Import Definitions.
Import Domain_Notations.
#[local] Open Scope list_scope.

  (** Kinds are unique: a definition is no module, and a body's entry is
      found by one lookup. *)
  Lemma functional_kind : forall {Θ Ξ},
    (forall h ch k1, dmod_member_kind Θ Ξ h ch k1 -> forall k2, dmod_member_kind Θ Ξ h ch k2 -> k1 = k2) /\
    (forall ρ U ch k1, gunit_member_kind Θ Ξ ρ U ch k1 -> forall k2, gunit_member_kind Θ Ξ ρ U ch k2 -> k1 = k2) /\
    (forall ρ H ch k1, modexp_member_kind Θ Ξ ρ H ch k1 -> forall k2, modexp_member_kind Θ Ξ ρ H ch k2 -> k1 = k2) /\
    (forall ρ Φ ρ1, kinds_env Θ Ξ ρ Φ ρ1 -> forall ρ2, kinds_env Θ Ξ ρ Φ ρ2 -> ρ1 = ρ2) /\
    (forall ρ0 H k ρ its ρ1, kinds_items_env Θ Ξ ρ0 H k ρ its ρ1 -> forall ρ2, kinds_items_env Θ Ξ ρ0 H k ρ its ρ2 -> ρ1 = ρ2).
  Proof.
    intros Θ Ξ; apply kind_mut_ind; intros;
      match goal with |- _ = ?r2 => match goal with H : context [r2] |- _ => inversion H; subst; clear H end end;
      repeat match goal with
        | H1 : Members.gc_module Θ Ξ ?p = Some _, H2 : Members.gc_module Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some _, H2 : Members.gc_resolve Θ Ξ ?p = Some _ |- _ =>
            rewrite (gc_module_resolve _ _ _ _ H1) in H2; discriminate H2
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
            rewrite (gm_prefix_item_exclusive _ _ _ H1) in H2; discriminate H2
        | H1 : gm_item_upto ?Φ ?x = Some _, H2 : gm_item_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some (Members.mr_alias _),
          H2 : (exists TΦ, Members.gc_loc Θ Ξ ?p = Some TΦ) \/ (exists b pv ra A B, Members.gc_resolve Θ Ξ ?p = Some (ge_def b pv ra A B)) |- _ =>
            exfalso; destruct H2 as [(? & H2) | (? & ? & ? & ? & ? & H2)];
            [ exact (gc_loc_not_alias _ _ _ _ _ H2 H1) | rewrite (gc_module_resolve _ _ _ _ H1) in H2; discriminate H2 ]
        | H1 : Members.gc_resolve Θ Ξ ?p = Some (ge_def _ _ _ _ _),
          H2 : forall b pv ra A B, Members.gc_resolve Θ Ξ ?p <> Some (ge_def b pv ra A B) |- _ =>
            exfalso; exact (H2 _ _ _ _ _ H1)
        | H1 : Members.dm_path Θ Ξ ?p, H2 : ~ Members.dm_path Θ Ξ ?p |- _ => exfalso; exact (H2 H1)
        | H1 : Members.gc_loc Θ Ξ ?p = Some _, H2 : Members.gc_module Θ Ξ ?p = Some (Members.mr_alias _) |- _ =>
            exfalso; exact (gc_loc_not_alias _ _ _ _ _ H1 H2)
        | H1 : Members.gc_resolve Θ Ξ ?p = Some (ge_def _ _ _ _ _), H2 : Members.dm_path Θ Ξ ?p |- _ =>
            exfalso; exact (gc_resolve_def_not_dm _ _ _ _ _ _ _ _ H1 H2)
        | H : (@nil ?T) <> nil \/ _ |- _ => destruct H as [H | H]; [ exfalso; exact (H eq_refl) |]
        | H : (@nil ?T) <> nil |- _ => exfalso; exact (H eq_refl)
        | H : context [?l ++ nil] |- _ => rewrite List.app_nil_r in H
        | H : dmod_member_kind Θ Ξ (dm_global _ _) nil _ |- _ => inversion H; subst; clear H
        | H1 : Members.gc_resolve Θ Ξ ?p = Some (ge_def _ _ _ _ _),
          H2 : (exists T oD, Members.gc_module Θ Ξ ?p = Some (Members.mr_body T oD)) \/ (exists TΦ, gc_frame Ξ ?p = Some TΦ) |- _ =>
            exfalso; destruct H2 as [(? & ? & H2) | (? & H2)];
            [ rewrite (gc_module_resolve _ _ _ _ H2) in H1 | rewrite (gc_frame_resolve _ _ _ _ H2) in H1 ]; discriminate H1
        | IH : forall r, ?P r -> ?a = r, H : ?P ?b |- _ =>
            assert_fails (constr_eq a b); specialize (IH _ H); subst
        end; try congruence.
  Qed.

  Lemma functional_eval : forall {Θ Ξ},
    (forall M ρ m1,
        ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m1 ->
        forall m2,
          ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m2 ->
          m1 = m2) /\
      (forall m n r1,
          $| m & n | Θ ⍮ Ξ ↘ r1 ->
          forall r2,
            $| m & n | Θ ⍮ Ξ ↘ r2 ->
            r1 = r2) /\
      (forall Ms ρ ms1, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms1 -> forall ms2, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms2 -> ms1 = ms2) /\
      (forall m args r1, $*| m & args | Θ ⍮ Ξ ↘ r1 -> forall r2, $*| m & args | Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall H ρ h1, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h1 -> forall h2, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h2 -> h1 = h2) /\
      (forall Δ D ρ h1, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h1 -> forall h2, ⟦ Δ ⊢ D ⟧ᶜ Θ ⍮ Ξ ⍮ ρ ↘ h2 -> h1 = h2) /\
      (forall h n r1, $ᵐ| h & n | Θ ⍮ Ξ ↘ r1 -> forall r2, $ᵐ| h & n | Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h ns r1, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r1 -> forall r2, $ᵐ*| h & ns | Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h x r1, h ·ₜ x Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₜ x Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h y r1, h ·ₘ y Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₘ y Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h ch r1, h ·ₜ* ch Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₜ* ch Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall h ch r1, h ·ₘ* ch Θ ⍮ Ξ ↘ r1 -> forall r2, h ·ₘ* ch Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall ρ Φ ρ1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 -> forall ρ2, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 -> ρ1 = ρ2) /\
      (forall ρ p ups Bks j m r1,
          ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2, ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall ρ p ups Bks gs vs r1,
          ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2, ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall ρ p ups Bks t v r1,
          ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 -> forall r2, ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall p ups j r1, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r1 -> forall r2, ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r2 -> r1 = r2) /\
      (forall p ups ρ t a1, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a1 -> forall a2, ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a2 -> a1 = a2) /\
      (forall p ups ρm As ρ t v a1, ⟦ihty v of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a1 ->
          forall a2, ⟦ihty v of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a2 -> a1 = a2) /\
      (forall f m r1, eval_proj Θ Ξ f m r1 -> forall r2, eval_proj Θ Ξ f m r2 -> r1 = r2) /\
      (forall m ρ fl rs1, eval_neutral_fields Θ Ξ m ρ fl rs1 -> forall rs2, eval_neutral_fields Θ Ξ m ρ fl rs2 -> rs1 = rs2) /\
      (forall fl v ws1, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws1 -> forall ws2, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws2 -> ws1 = ws2) /\
      (forall p ups ρm As ρ gs vs r1, ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
          forall r2, ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2) /\
      (forall rs Ms ρ ms1, eval_field_vals Θ Ξ rs Ms ρ ms1 -> forall ms2, eval_field_vals Θ Ξ rs Ms ρ ms2 -> ms1 = ms2) /\
      (forall f Ms ρ r1, eval_app_args Θ Ξ f Ms ρ r1 -> forall r2, eval_app_args Θ Ξ f Ms ρ r2 -> r1 = r2).
  Proof.
    intros Θ Ξ; apply eval_mut_ind; intros;
      (* invert the other evaluation, then use the hypotheses on its parts; the
         two resolutions of a global or a module agree, and two neutral
         scrutinees of [efq] that are equal have equal parts; an induction
         hypothesis is never spent on the premise it is about *)
      match goal with |- _ = ?r2 => match goal with H : context [r2] |- _ => inversion H; subst; clear H end end;
      repeat match goal with
        | H : gc_term Θ Ξ ?p = Some _ |- _ =>
            destruct (gc_term_inv _ _ _ _ H) as [(? & ? & ?) | (? & ? & ? & ?)]; clear H
        | H1 : entry_tm ?E = Some _, H2 : entry_tm ?E = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : entry_unit ?E = Some _, H2 : entry_unit ?E = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_resolve Θ Ξ ?p = Some _, H2 : Members.gc_resolve Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : gc_entry Θ Ξ ?p = Some _, H2 : gc_entry Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : gc_entry Θ Ξ ?p = Some (ge_def_mod _ _ _ _), H2 : Members.gc_resolve Θ Ξ ?p = Some _ |- _ =>
            exfalso; rewrite (gc_entry_def_mod _ _ _ _ _ _ _ H1) in H2; discriminate H2
        | H1 : ind_mlookup Θ Ξ ?p = Some _, H2 : gc_entry Θ Ξ ?p = Some (ge_def_mod _ _ _ _) |- _ =>
            exfalso; exact (ind_mlookup_not_def_mod _ _ _ _ _ _ _ _ H1 H2)
        | H1 : ind_mlookup Θ Ξ ?p = Some _, H2 : ind_mlookup Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : ind_lookup Θ Ξ ?p = Some _, H2 : ind_lookup Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : record_lookup Θ Ξ ?p = Some _, H2 : record_lookup Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : record_lookup Θ Ξ ?p = Some _, H2 : ind_mlookup Θ Ξ ?p = Some _ |- _ =>
            exfalso; rewrite (record_lookup_not_ind _ _ _ _ H1) in H2; discriminate H2
        | H1 : record_lookup Θ Ξ ?p = Some _, H2 : gc_entry Θ Ξ ?p = Some (ge_def_mod _ _ _ _) |- _ =>
            exfalso; exact (record_lookup_not_def_mod _ _ _ _ _ _ _ _ H1 H2)
        | H1 : field_index ?fl ?f = Some _, H2 : field_index ?fl ?f = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : field_lookup ?fl ?f = Some _, H2 : field_lookup ?fl ?f = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : ind_member ?D ?k = Some _, H2 : ind_member ?D ?k = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : im_head ?M = _, H2 : im_head ?M = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : im_starts _ ?M = true, H2 : im_head ?M = mh_view _ _ _ _ |- _ =>
            unfold im_starts, im_is_decl in H1; rewrite H2 in H1; cbn [orb] in H1; apply Nat.ltb_lt in H1
        | H1 : im_starts _ ?M = true, H2 : im_head ?M = mh_record _ _ _ |- _ =>
            unfold im_starts, im_is_decl in H1; rewrite H2 in H1; cbn [orb] in H1; apply Nat.ltb_lt in H1
        | H1 : im_is_rview ?M = false, H2 : im_head ?M = mh_record _ _ _ |- _ =>
            exfalso; unfold im_is_rview in H1; rewrite H2 in H1; discriminate H1
        | H : 0 < List.length nil |- _ => exfalso; cbn in H; lia
        | H1 : im_cons ?M = _, H2 : im_cons ?M = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : eval_mref Θ Ξ ?p _ ?j _, H2 : ind_member _ ?j = Some ?M, H3 : im_head ?M = mh_record _ _ _ |- _ =>
            inversion H1; subst; clear H1
        | H1 : im_ref ?p ?j ?M = _, H2 : im_ref ?p ?j ?M = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : List.nth_error ?Bks ?j = Some _, H2 : List.nth_error ?Bks ?j = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : ind_con ?D ?c = Some _, H2 : ind_con ?D ?c = Some _ |- _ =>
            rewrite H1 in H2; injection H2 as ?; subst; clear H2
        | H1 : brs_lookup ?Bs ?c = Some _, H2 : brs_lookup ?Bs ?c = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some _, H2 : Members.gc_module Θ Ξ ?p = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_module Θ Ξ ?p = Some (Members.mr_alias _),
          H2 : forall U, Members.gc_module Θ Ξ ?p <> Some (Members.mr_alias U) |- _ =>
            exfalso; exact (H2 _ H1)
        | H1 : gm_prefix_upto ?Φ ?x = Some _, H2 : gm_prefix_upto ?Φ ?x = Some _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H1 : Members.gc_loc Θ Ξ ?p = Some _, H2 : Members.gc_module Θ Ξ ?p = Some (Members.mr_alias _) |- _ =>
            exfalso; exact (gc_loc_not_alias _ _ _ _ _ H1 H2)
        | H1 : module_saturated Θ Ξ ?p ?args, H2 : Members.gc_loc Θ Ξ ?p = Some (?T, ?Φ),
          H3 : List.length ?args < List.length ?T |- _ =>
            exfalso; specialize (H1 _ _ H2); lia
        | H1 : Members.gc_loc Θ Ξ ?p = Some (?T, ?Φ), H2 : Members.gc_loc Θ Ξ ?p = Some (?T', ?Φ') |- _ =>
            assert_fails (constr_eq H1 H2); rewrite H1 in H2; injection H2; intros; subst; clear H2
        | H : _ ++ ce_ass _ :: nil = _ ++ ce_ass _ :: nil |- _ =>
            apply List.app_inj_tail in H as [? [= ?]]; subst
        | H : 0 < List.length (_ ++ _ :: nil) -> False |- _ =>
            exfalso; apply H; rewrite List.length_app; cbn; lia
        | H1 : modexp_spine ?H = _, H2 : modexp_spine ?H = _ |- _ =>
            rewrite H1 in H2; injection H2; intros; subst; clear H2
        | IH : forall r, ?P r -> ?a = r, H : ?P ?b |- _ =>
            assert_fails (constr_eq a b); specialize (IH _ H); subst
        | H : d_neut _ _ = d_neut _ _ |- _ => injection H; intros; subst; clear H
        | H : d_record _ _ = d_record _ _ |- _ => injection H; intros; subst; clear H
        | H : (_, _, _) = (_, _, _) |- _ => injection H; intros; subst; clear H
        | H : eval_selc _ _ _ nil _ |- _ => inversion H
        end;
      cbn [gu_params List.length] in *; try congruence; try lia; intuition (try congruence; try lia).
  Qed.

  Corollary functional_eval_exp : forall {Θ Ξ} M ρ m1 m2,
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m1 ->
      ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m2 ->
      m1 = m2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ); firstorder.
  Qed.

  Corollary functional_eval_app : forall {Θ Ξ} m n r1 r2,
      $| m & n | Θ ⍮ Ξ ↘ r1 ->
      $| m & n | Θ ⍮ Ξ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ); intuition.
  Qed.

  (** A function applied along terms, each evaluated or the proof by the
      sort it is taken at, has one value. *)
  Corollary functional_eval_app_args : forall {Θ Ξ} f Ms ρ r1 r2,
      eval_app_args Θ Ξ f Ms ρ r1 ->
      eval_app_args Θ Ξ f Ms ρ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ * E1 E2; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_eval_elim : forall {Θ Ξ} ρ p ups Bks j m r1 r2,
      ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      ⟦elim m at j of p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_eval_ihs : forall {Θ Ξ} ρ p ups Bks gs vs r1 r2,
      ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 ->
      ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 ->
      r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_eval_ih : forall {Θ Ξ} ρ p ups Bks t v r1 r2,
      ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 -> ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_eval_mref : forall {Θ Ξ} p ups j r1 r2,
      ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r1 -> ⟦mref j of p ups ⟧ Θ ⍮ Ξ ↘ r2 -> r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_eval_shape_type : forall {Θ Ξ} p ups ρ t a1 a2,
      ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a1 -> ⟦shty t of p ups ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a2 -> a1 = a2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  Corollary functional_eval_ihty : forall {Θ Ξ} p ups ρm As ρ t v a1 a2,
      ⟦ihty v of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a1 -> ⟦ihty v of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ a2 -> a1 = a2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  (** The projections of a value at its fields are one list. *)
  Corollary functional_eval_projs : forall {Θ Ξ} fl v ws1 ws2,
      ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws1 -> ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws2 -> ws1 = ws2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  (** So are the types of the recursive results of a record view's
      fields. *)
  Corollary functional_eval_ihtys : forall {Θ Ξ} p ups ρm As ρ gs vs r1 r2,
      ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r1 -> ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r2 -> r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  (** A field of a value is one value. *)
  Corollary functional_eval_proj : forall {Θ Ξ} f m r1 r2,
      eval_proj Θ Ξ f m r1 -> eval_proj Θ Ξ f m r2 -> r1 = r2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  (** So are the neutral projections of the fields of a neutral. *)
  Corollary functional_eval_neutral_fields : forall {Θ Ξ} m ρ fl rs1 rs2,
      eval_neutral_fields Θ Ξ m ρ fl rs1 -> eval_neutral_fields Θ Ξ m ρ fl rs2 -> rs1 = rs2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  (** An evaluated substitution is determined pointwise. *)
  Corollary functional_eval_modexp : forall {Θ Ξ} H ρ h1 h2,
      ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h1 ->
      ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h2 ->
      h1 = h2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ); intuition.
  Qed.

  Corollary functional_eval_body_env : forall {Θ Ξ} ρ Φ ρ1 ρ2,
      ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 ->
      ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ2 ->
      ρ1 = ρ2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  (** Equality of values is decidable: they are first-order data. *)
  Fixpoint domain_eq_dec (a b : domain) {struct a} : {a = b} + {a <> b}
  with domain_ne_eq_dec (a b : domain_ne) {struct a} : {a = b} + {a <> b}
  with domain_nf_eq_dec (a b : domain_nf) {struct a} : {a = b} + {a <> b}
  with dmod_eq_dec (a b : dmod) {struct a} : {a = b} + {a <> b}
  with dentry_eq_dec (a b : dentry) {struct a} : {a = b} + {a <> b}
  with entry_type_eq_dec (a b : entry_type) {struct a} : {a = b} + {a <> b}.
  Proof.
    all: decide equality;
      first [ apply Nat.eq_dec | apply String.string_dec | apply qname_eq_dec | apply o2_eq_dec
            | apply relevance_eq_dec | apply exp_eq_dec | apply moddef_eq_dec | apply gunit_eq_dec
            | apply (List.list_eq_dec dentry_eq_dec) | apply (List.list_eq_dec domain_eq_dec)
            | apply (List.list_eq_dec exp_eq_dec) | apply (List.list_eq_dec centry_eq_dec)
            | apply (List.list_eq_dec String.string_dec)
            | apply (eblocks_eq_dec_g exp_eq_dec) | apply (ptyp_eq_dec_g exp_eq_dec)
            | apply List.list_eq_dec; intros; repeat (decide equality || apply domain_eq_dec || apply domain_ne_eq_dec
                                                        || apply Nat.eq_dec || apply String.string_dec)
            | idtac ].
  Defined.

  Corollary functional_eval_field_vals : forall {Θ Ξ} rs Ms ρ ms1 ms2,
      eval_field_vals Θ Ξ rs Ms ρ ms1 ->
      eval_field_vals Θ Ξ rs Ms ρ ms2 ->
      ms1 = ms2.
  Proof.
    intros Θ Ξ; pose proof (@functional_eval Θ Ξ) as H; destruct_all; eauto.
  Qed.

  (** Whether an entry is a proposition depends only on the substitution
      and its source environment, so two evaluations agree on it. *)
  (** A substitution entry denotes one entry. *)
  Corollary functional_eval_sentry : forall {Θ Ξ} t U e ρ d1 d2,
      eval_sentry Θ Ξ t U e ρ d1 ->
      eval_sentry Θ Ξ t U e ρ d2 ->
      d1 = d2.
  Proof.
    intros * H1 H2; destruct e; cbn in H1, H2.
    - congruence.
    - destruct H1 as (m1 & -> & H1), H2 as (m2 & -> & H2); f_equal; eapply functional_eval_exp; eassumption.
    - destruct H1 as (m1 & -> & H1), H2 as (m2 & -> & H2); f_equal; eapply functional_eval_modexp; eassumption.
    - destruct H1 as (n1 & m1 & -> & Hn1 & H1), H2 as (n2 & m2 & -> & Hn2 & H2); f_equal;
        [ eapply functional_eval_exp | eapply functional_eval_modexp ]; eassumption.
  Qed.

  (** So does a substitution entry at a proposition. *)
  Lemma functional_eval_sentry_proof : forall t U e ρ d1 d2,
      eval_sentry_proof t U e ρ d1 -> eval_sentry_proof t U e ρ d2 -> d1 = d2.
  Proof. intros * H1 H2; destruct e; cbn in H1, H2; subst; tauto. Qed.

  (** Whether the head entry is a proposition depends only on the tail, on
      the entries of the context. *)
  Lemma entry_propositional_zero_tail : forall {Θ Ξ} e Δ ρσ1 ρσ2,
      env_agree_upto (List.length Δ) (drop_env ρσ1) (drop_env ρσ2) ->
      entry_propositional Θ Ξ (e :: Δ) ρσ1 0 -> entry_propositional Θ Ξ (e :: Δ) ρσ2 0.
  Proof.
    intros * Ht [T HT E HE v Ev Hv]; econstructor; [ exact HT | | exact Ev | exact Hv ].
    intros y Hy; rewrite (HE y Hy), !env_entry_skipn; cbn [Nat.add].
    rewrite <- !env_entry_drop; apply Ht; exact Hy.
  Qed.

  (** Whether an entry is a proposition depends only on the entries after
      it, so two evaluations of a substitution agree on the entries of its
      target, entry by entry from the last; values are decidably equal, so
      no case analysis on a proposition is needed.  Past the target they
      may differ. *)
  Corollary functional_eval_sub : forall {Θ Ξ} Δ σ ρ ρσ1 ρσ2,
      ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ1 ->
      ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ2 ->
      env_agree_upto (List.length Δ) ρσ1 ρσ2.
  Proof.
    intros Θ Ξ Δ; induction Δ as [| e Δ IH]; intros σ ρ ρσ1 ρσ2 H1 H2.
    - intros x Hx; cbn in Hx; lia.
    - assert (Ht : env_agree_upto (List.length Δ) (drop_env ρσ1) (drop_env ρσ2))
        by (eapply IH; eapply eval_sub_shift_pre; eassumption).
      intros [| x] Hx; [| rewrite <- !env_entry_drop; apply Ht; cbn in Hx; lia ].
      destruct (dentry_eq_dec (env_entry ρσ1 0) (env_entry ρσ2 0)) as [| Hne]; [ assumption | exfalso ].
      assert (Ht' : env_agree_upto (List.length Δ) (drop_env ρσ2) (drop_env ρσ1)) by (symmetry; exact Ht).
      assert (Etag : ctx_entry_tag (e :: Δ) 0 ρσ2 = ctx_entry_tag (e :: Δ) 0 ρσ1)
        by (rewrite !ctx_entry_tag_head; unfold centry_tag; rewrite (env_upto_agree _ _ _ Ht'); reflexivity).
      destruct (H1 0 Hx) as [Hp1 Hn1'], (H2 0 Hx) as [Hp2 Hn2']; rewrite Etag in Hp2, Hn2'.
      assert (Hn1 : ~ entry_propositional Θ Ξ (e :: Δ) ρσ1 0).
      { intros Hp; apply Hne.
        eapply functional_eval_sentry_proof;
          [ exact (Hp1 Hp) | exact (Hp2 (entry_propositional_zero_tail _ _ _ _ Ht Hp)) ]. }
      assert (Hn2 : ~ entry_propositional Θ Ξ (e :: Δ) ρσ2 0)
        by (intros Hp; apply Hn1, (entry_propositional_zero_tail _ _ _ _ Ht' Hp)).
      apply Hne; eapply functional_eval_sentry; [ apply (Hn1' Hn1) | apply (Hn2' Hn2) ].
  Qed.

  (** The entries a substitution entry denotes are stored at the tag and
      unit it is evaluated at. *)
  Lemma eval_sentry_tagged : forall {Θ Ξ} t U e ρ d, eval_sentry Θ Ξ t U e ρ d -> retag_entry t U d = d.
  Proof.
    intros * H; destruct e; cbn in H; destruct_all; subst; [ apply retag_entry_twice | reflexivity .. ].
  Qed.

  Lemma eval_sentry_proof_tagged : forall t U e ρ d, eval_sentry_proof t U e ρ d -> retag_entry t U d = d.
  Proof. intros * H; destruct e; cbn in H; subst; [ apply retag_entry_twice | reflexivity | contradiction .. ]. Qed.

  (** So are the entries of an evaluated substitution, at the declarations
      of its target; no case analysis on a proposition is needed, as
      entries are decidably equal. *)
  Lemma eval_sub_entry_tagged : forall {Θ Ξ} Δ σ ρ ρσ,
      ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ ->
      forall x, x < List.length Δ ->
        retag_entry (ctx_entry_tag Δ x ρσ) (ctx_entry_unit Δ x) (env_entry ρσ x) = env_entry ρσ x.
  Proof.
    intros * H x Hx.
    destruct (dentry_eq_dec (retag_entry (ctx_entry_tag Δ x ρσ) (ctx_entry_unit Δ x) (env_entry ρσ x)) (env_entry ρσ x))
      as [| Hne]; [ assumption | exfalso ].
    destruct (H x Hx) as [Hp Hn].
    apply (fun Hnp : ~ entry_propositional Θ Ξ Δ ρσ x => Hne (eval_sentry_tagged _ _ _ _ _ (Hn Hnp))).
    intros Hpp; exact (Hne (eval_sentry_proof_tagged _ _ _ _ _ (Hp Hpp))).
  Qed.

  (** The tags of an environment of [Δ] read it on the entries of [Δ]
      only. *)
  Lemma ctx_entry_tag_agree : forall Δ x ρ ρ',
      env_agree_upto (List.length Δ) ρ ρ' -> ctx_entry_tag Δ x ρ = ctx_entry_tag Δ x ρ'.
  Proof.
    intros * H; unfold ctx_entry_tag; destruct (ctx_entry_type Δ x); [| reflexivity ].
    f_equal; apply env_upto_agree; intros y Hy; rewrite !env_entry_skipn; apply H.
    rewrite List.length_skipn in Hy; lia.
  Qed.

  (** An environment stored at the declarations of [Δ] already is its own
      retagging, on the entries of [Δ]. *)
  Lemma ctx_retag_agree : forall Δ ρ,
      (forall x, x < List.length Δ -> retag_entry (ctx_entry_tag Δ x ρ) (ctx_entry_unit Δ x) (env_entry ρ x) = env_entry ρ x) ->
      env_agree_upto (List.length Δ) (ctx_retag Δ ρ) ρ.
  Proof.
    induction Δ as [| e Δ IH]; intros ρ H x Hx; cbn [List.length] in Hx; [ lia |].
    assert (IH' : env_agree_upto (List.length Δ) (ctx_retag Δ ρ↯) ρ↯).
    { apply IH; intros y Hy; rewrite (ctx_entry_tag_drop e), env_entry_drop; exact (H (S y) ltac:(cbn; lia)). }
    destruct x as [| x].
    - rewrite env_entry_ctx_retag by (cbn; lia).
      rewrite <- (H 0) at 2 by (cbn; lia).
      f_equal; rewrite !ctx_entry_tag_head; cbn [ctx_retag drop_env List.tl] in IH' |- *; unfold centry_tag.
      rewrite (env_upto_agree _ _ _ IH'); reflexivity.
    - change (env_entry (ctx_retag Δ ρ↯) x = env_entry ρ (S x)); rewrite (IH' x ltac:(lia)), env_entry_drop; reflexivity.
  Qed.

  (** The head an extension by a term stores: a term entry at its
      declared type, its value or the term kept. *)
  Lemma eval_sub_head_exp : forall {Θ Ξ} e Δ σ ρ ρτ N,
      ⟦ σ : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρτ -> σ 0 = se_exp N ->
      env_entry ρτ 0 = de_term (ρτ 0) (ctx_entry_tag (e :: Δ) 0 ρτ).
  Proof.
    intros * H HN.
    destruct (dentry_eq_dec (env_entry ρτ 0) (de_term (ρτ 0) (ctx_entry_tag (e :: Δ) 0 ρτ))) as [| Hne]; [ assumption | exfalso ].
    destruct (H 0 ltac:(cbn; lia)) as [Hp Hn]; rewrite HN in Hp, Hn; cbn [eval_sentry eval_sentry_proof] in Hp, Hn.
    assert (Hnp : ~ entry_propositional Θ Ξ (e :: Δ) ρτ 0).
    { intros Hpp; apply Hne; unfold env_var; rewrite (Hp Hpp); reflexivity. }
    destruct (Hn Hnp) as (m & Em & _); apply Hne; unfold env_var; rewrite Em; reflexivity.
  Qed.

  (** An evaluated substitution agrees with its retagging on the target. *)
  Corollary eval_sub_agree_retag : forall {Θ Ξ} Δ σ ρ ρσ,
      ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ -> env_agree_upto (List.length Δ) ρσ (ctx_retag Δ ρσ).
  Proof. intros * H; symmetry; apply ctx_retag_agree, (eval_sub_entry_tagged _ _ _ _ H). Qed.

  #[local] Transparent eval_sub.
  (** The result of an evaluation of a substitution may be replaced by an
      environment agreeing with it on the target. *)
  Lemma eval_sub_resp_agree : forall {Θ Ξ} Δ σ ρ ρσ ρσ',
      ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ -> env_agree_upto (List.length Δ) ρσ ρσ' -> ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ'.
  Proof.
    intros * H Ha x Hx.
    assert (Ha' : env_agree_upto (List.length Δ) ρσ' ρσ) by (symmetry; exact Ha).
    rewrite <- (Ha x Hx), <- (ctx_entry_tag_agree _ x _ _ Ha); split.
    - intros Hp; apply (H x Hx); exact (entry_propositional_resp_agree _ _ _ _ Ha' Hp).
    - intros Hn; apply (H x Hx); intros Hp; exact (Hn (entry_propositional_resp_agree _ _ _ _ Ha Hp)).
  Qed.
  #[local] Opaque eval_sub.

  Corollary eval_sub_retag : forall {Θ Ξ} Δ σ ρ ρσ,
      ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ -> ⟦ σ : Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ctx_retag Δ ρσ.
  Proof. intros * H; exact (eval_sub_resp_agree _ _ _ _ _ H (eval_sub_agree_retag _ _ _ _ H)). Qed.

  (** At an environment an evaluated substitution yields, [Wk] evaluates to
      the tail itself: its entries are stored at their declarations
      already. *)
  Corollary eval_sub_shift_of_eval : forall {Θ Ξ} e Δ σ ρ ρσ,
      ⟦ σ : e :: Δ ⟧s Θ ⍮ Ξ ⍮ ρ ↘ ρσ -> ⟦ Wk : Δ ⟧s Θ ⍮ Ξ ⍮ ρσ ↘ ρσ↯.
  Proof.
    intros * H.
    apply (eval_sub_resp_agree _ _ _ _ _ (eval_sub_shift Δ ρσ)).
    apply ctx_retag_agree; intros x Hx.
    rewrite (ctx_entry_tag_drop e), env_entry_drop.
    exact (eval_sub_entry_tagged _ _ _ _ H (S x) ltac:(cbn; lia)).
  Qed.

#[export]
Hint Resolve functional_eval_exp functional_eval_elim functional_eval_ihs functional_eval_ih functional_eval_mref functional_eval_shape_type functional_eval_ihty functional_eval_app functional_eval_modexp functional_eval_sub functional_eval_proj functional_eval_neutral_fields functional_eval_projs functional_eval_ihtys : mctt.



Ltac functional_eval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_eval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (⟦ ?M ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?m1), H2 : (⟦ ?M ⟧ ?T ⍮ ?X ⍮ ?ρ ↘ ?m2) |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : ($| ?m & ?n | ?T ⍮ ?X ↘ ?r1), H2 : ($| ?m & ?n | ?T ⍮ ?X ↘ ?r2) |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : (⟦ ?H ⟧ᵐ ?T ⍮ ?X ⍮ ?ρ ↘ ?h1), H2 : (⟦ ?H ⟧ᵐ ?T ⍮ ?X ⍮ ?ρ ↘ ?h2) |- _ =>
      clean replace h2 with h1 by first [solve [mauto 2] | tactic_error h2 h1]; clear H2
  | H1 : eval_elim ?T ?X ?ρ ?p ?o ?Bks ?j ?m ?r1, H2 : eval_elim ?T ?X ?ρ ?p ?o ?Bks ?j ?m ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : eval_ihs ?T ?X ?ρ ?p ?o ?Bks ?gs ?vs ?r1, H2 : eval_ihs ?T ?X ?ρ ?p ?o ?Bks ?gs ?vs ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : eval_ih ?T ?X ?ρ ?p ?o ?Bks ?t ?v ?r1, H2 : eval_ih ?T ?X ?ρ ?p ?o ?Bks ?t ?v ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : eval_mref ?T ?X ?p ?ups ?j ?r1, H2 : eval_mref ?T ?X ?p ?ups ?j ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : eval_shape_type ?T ?X ?p ?ups ?ρ ?t ?r1, H2 : eval_shape_type ?T ?X ?p ?ups ?ρ ?t ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : eval_ihty ?T ?X ?p ?ups ?ρm ?As ?ρ ?t ?v ?r1, H2 : eval_ihty ?T ?X ?p ?ups ?ρm ?As ?ρ ?t ?v ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : eval_ihtys ?T ?X ?p ?ups ?ρm ?As ?ρ ?gs ?vs ?r1, H2 : eval_ihtys ?T ?X ?p ?ups ?ρm ?As ?ρ ?gs ?vs ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : eval_projs ?T ?X ?fl ?v ?r1, H2 : eval_projs ?T ?X ?fl ?v ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : eval_proj ?T ?X ?f ?m ?r1, H2 : eval_proj ?T ?X ?f ?m ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  | H1 : eval_neutral_fields ?T ?X ?ns ?m ?fl ?pre ?r1, H2 : eval_neutral_fields ?T ?X ?ns ?m ?fl ?pre ?r2 |- _ =>
      clean replace r2 with r1 by first [solve [mauto 2] | tactic_error r2 r1]; clear H2
  end.
(** There is no [eval_sub] case: [functional_eval_sub] gives only pointwise
    equality, so there is nothing to [replace]. *)
Ltac functional_eval_rewrite_clear := repeat functional_eval_rewrite_clear1.

(** The universe at an index evaluates to its value, at either tier. *)
Lemma eval_universe_index_term : forall Θ Ξ u ρ, ⟦ universe_index_term u ⟧ Θ ⍮ Ξ ⍮ ρ ↘ universe_index_value u.
Proof. intros ? ? [] ?; cbn; repeat econstructor. Qed.

#[export]
Hint Resolve eval_universe_index_term : mctt.

(** One recursive result per leaf path of each recursive argument, of an
    argument of a shape per leaf path of the shape, and one projection per
    field, when the group's table is coherent. *)
Lemma eval_ih_length_all : forall {Θ Ξ},
    (forall ρ p ups Bks gs vs ihs,
        ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
        forall D, ind_lookup Θ Ξ p = Some D -> leaves_coherent D ->
        List.length vs = List.length gs /\ List.length ihs = cargs_nrec D gs) /\
    (forall ρ p ups Bks t v r,
        ⟦ih v of t under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
        forall D, ind_lookup Θ Ξ p = Some D -> leaves_coherent D ->
        List.length r = List.length (shape_leaves (rview_leaves D) 0 t)) /\
    (forall fl v ws, ⟦projs fl of v ⟧ Θ ⍮ Ξ ↘ ws -> List.length ws = List.length fl).
Proof.
  intros Θ Ξ.
  pose proof (eval_mut_ind Θ Ξ
             (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True)
             (fun _ _ _ _ => True) (fun _ _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True)
             (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True)
             (fun _ _ _ _ => True)
             (fun _ _ _ _ _ _ _ _ => True)
             (fun ρ p ups Bks gs vs ihs _ => forall D, ind_lookup Θ Ξ p = Some D -> leaves_coherent D ->
                List.length vs = List.length gs /\ List.length ihs = cargs_nrec D gs)
             (fun ρ p ups Bks t v r _ => forall D, ind_lookup Θ Ξ p = Some D -> leaves_coherent D ->
                List.length r = List.length (shape_leaves (rview_leaves D) 0 t))
             (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ _ _ => True)
             (fun _ _ _ _ => True) (fun _ _ _ _ _ => True)
             (fun fl v ws _ => List.length ws = List.length fl)
             (fun _ _ _ _ _ _ _ _ _ => True)
             (fun _ _ _ _ _ => True) (fun _ _ _ _ _ => True)) as H.
  edestruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hihs & Hih & _ & _ & _ & _ & _ & Hp & _ & _ & _);
    clear H; [ .. | split; [ exact Hihs | split; [ exact Hih | exact Hp ] ] ]; intros; try exact I.
  - (* no argument *) cbn; auto.
  - (* a non-recursive argument *)
    match goal with IH : forall D, _ -> _ -> _ /\ _, HD : ind_lookup _ _ _ = Some ?D, Hc : leaves_coherent ?D |- _ =>
      destruct (IH _ HD Hc) as [? ?] end; cbn; auto.
  - (* a recursive argument *)
    match goal with
    | IH1 : forall D, _ -> _ -> List.length ?ih = _, IH2 : forall D, _ -> _ -> _ /\ _,
      HD : ind_lookup _ _ _ = Some ?D, Hc : leaves_coherent ?D |- _ =>
        pose proof (IH1 _ HD Hc); destruct (IH2 _ HD Hc) as [? ?]
    end; cbn; rewrite List.length_app; auto.
  - (* at a member with a block *)
    match goal with HD : ind_lookup _ _ _ = Some ?D, HD' : ind_lookup _ _ _ = Some ?D' |- _ =>
      rewrite HD in HD'; injection HD' as <- end.
    erewrite length_shape_leaves_self by eassumption; reflexivity.
  - (* at a record view *)
    match goal with HD : ind_lookup _ _ _ = Some ?D, HD' : ind_lookup _ _ _ = Some ?D' |- _ =>
      rewrite HD in HD'; injection HD' as <- end.
    match goal with IH : forall D, _ -> _ -> _ /\ _, HD : ind_lookup _ _ _ = Some ?D, Hc : leaves_coherent ?D |- _ =>
      destruct (IH _ HD Hc) as [Hlw Hlr] end.
    erewrite length_shape_leaves_rview by (eauto; congruence); exact Hlr.
  - (* at a function shape *)
    match goal with HD : ind_lookup _ _ _ = Some ?D, HD' : ind_lookup _ _ _ = Some ?D' |- _ =>
      rewrite HD in HD'; injection HD' as <- end.
    cbn; rewrite List.length_map, List.length_seq, List.length_map; apply length_shape_leaves.
  - (* no field *) reflexivity.
  - (* a field *) cbn; congruence.
Qed.

(** One type per leaf path, likewise. *)
Lemma eval_ihty_length_all : forall {Θ Ξ},
    (forall p ups ρm As ρ t v r,
        ⟦ihty v of t at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
        forall D, ind_lookup Θ Ξ p = Some D -> leaves_coherent D ->
        List.length r = List.length (shape_leaves (rview_leaves D) 0 t)) /\
    (forall p ups ρm As ρ gs vs r,
        ⟦ihtys vs of gs at p ups under ρm As ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
        forall D, ind_lookup Θ Ξ p = Some D -> leaves_coherent D ->
        List.length vs = List.length gs /\ List.length r = cargs_nrec D gs).
Proof.
  intros Θ Ξ.
  pose proof (eval_mut_ind Θ Ξ
             (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True)
             (fun _ _ _ _ => True) (fun _ _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True)
             (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True)
             (fun _ _ _ _ => True)
             (fun _ _ _ _ _ _ _ _ => True)
             (fun _ _ _ _ _ _ _ _ => True)
             (fun _ _ _ _ _ _ _ _ => True)
             (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
             (fun p ups ρm As ρ t v r _ => forall D, ind_lookup Θ Ξ p = Some D -> leaves_coherent D ->
                List.length r = List.length (shape_leaves (rview_leaves D) 0 t))
             (fun _ _ _ _ => True) (fun _ _ _ _ _ => True)
             (fun fl v ws _ => List.length ws = List.length fl)
             (fun p ups ρm As ρ gs vs r _ => forall D, ind_lookup Θ Ξ p = Some D -> leaves_coherent D ->
                List.length vs = List.length gs /\ List.length r = cargs_nrec D gs)
             (fun _ _ _ _ _ => True) (fun _ _ _ _ _ => True)) as H.
  edestruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hty & _ & _ & _ & Htys & _ & _);
    clear H; [ .. | split; [ exact Hty | exact Htys ] ]; intros; try exact I.
  - (* at a member with a block *)
    match goal with HD : ind_lookup _ _ _ = Some ?D, HD' : ind_lookup _ _ _ = Some ?D' |- _ =>
      rewrite HD in HD'; injection HD' as <- end.
    erewrite length_shape_leaves_self by eassumption; reflexivity.
  - (* at a record view *)
    match goal with HD : ind_lookup _ _ _ = Some ?D, HD' : ind_lookup _ _ _ = Some ?D' |- _ =>
      rewrite HD in HD'; injection HD' as <- end.
    match goal with IH : forall D, _ -> _ -> _ /\ _, HD : ind_lookup _ _ _ = Some ?D, Hc : leaves_coherent ?D |- _ =>
      destruct (IH _ HD Hc) as [Hlw Hlr] end.
    erewrite length_shape_leaves_rview by (eauto; congruence); exact Hlr.
  - (* at a function shape *)
    match goal with HD : ind_lookup _ _ _ = Some ?D, HD' : ind_lookup _ _ _ = Some ?D' |- _ =>
      rewrite HD in HD'; injection HD' as <- end.
    cbn; rewrite List.length_map, List.length_seq, List.length_map; apply length_shape_leaves.
  - (* no field *) reflexivity.
  - (* a field *) cbn; congruence.
  - (* no argument *) cbn; auto.
  - (* a non-recursive argument *)
    match goal with IH : forall D, _ -> _ -> _ /\ _, HD : ind_lookup _ _ _ = Some ?D, Hc : leaves_coherent ?D |- _ =>
      destruct (IH _ HD Hc) as [? ?] end; cbn; auto.
  - (* a recursive argument *)
    match goal with
    | IH1 : forall D, _ -> _ -> List.length ?ih = _, IH2 : forall D, _ -> _ -> _ /\ _,
      HD : ind_lookup _ _ _ = Some ?D, Hc : leaves_coherent ?D |- _ =>
        pose proof (IH1 _ HD Hc); destruct (IH2 _ HD Hc) as [? ?]
    end; cbn; rewrite List.length_app; auto.
Qed.

Lemma eval_ihs_length : forall {Θ Ξ} ρ p ups Bks gs vs ihs D,
    ind_lookup Θ Ξ p = Some D -> leaves_coherent D ->
    ⟦ihs vs of gs under p ups Bks ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs ->
    List.length vs = List.length gs /\ List.length ihs = cargs_nrec D gs.
Proof. intros * HD Hc H; exact (proj1 (@eval_ih_length_all Θ Ξ) _ _ _ _ _ _ _ H _ HD Hc). Qed.

(** The projections of a value at the fields [fl]: one per field. *)
Lemma eval_projs_length : forall {Θ Ξ} fl m ws, ⟦projs fl of m ⟧ Θ ⍮ Ξ ↘ ws -> List.length ws = List.length fl.
Proof. induction 1; cbn; congruence. Qed.

(** The projections of a value at the fields [fs], [f] and more: the one
    after [fs] is that of [f]. *)
Lemma eval_projs_at : forall {Θ Ξ} (fs : list String.string) f fl' m ws, ⟦projs fs ++ f :: fl' of m ⟧ Θ ⍮ Ξ ↘ ws ->
    exists w, List.nth_error ws (List.length fs) = Some w /\ eval_proj Θ Ξ f m w.
Proof.
  intros Θ Ξ; induction fs as [| g fs IH]; intros * Hps; cbn [List.app] in Hps; inversion Hps; subst;
    [ eexists; split; [ reflexivity | eassumption ] |].
  destruct (IH _ _ _ _ ltac:(eassumption)) as (w' & Hw & Hp); exists w'; split; [ exact Hw | exact Hp ].
Qed.

(** A constructor has no projection: its projections are at no field. *)
Lemma projs_con : forall {Θ Ξ} fl hd k' c xs ws, ⟦projs fl of d_con hd k' c xs ⟧ Θ ⍮ Ξ ↘ ws -> fl = nil /\ ws = nil.
Proof.
  intros * H; inversion H as [| f0 v0 w0 fl0 ws0 Ep]; subst; [ split; reflexivity |].
  inversion Ep.
Qed.
