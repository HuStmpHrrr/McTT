From Stdlib Require Import Bool Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Members Command.
From Mctt.Frontend Require Import Elaborator ElabSpec.

Import Syntax_Notations.
Open Scope list_scope.

(** * The Elaborator Meets Its Specification

    [elaborate_core] computes exactly [elab_spec] ([elaborate_core_sound],
    [elaborate_core_complete]), so the specification is functional
    ([elab_spec_functional]).  Both work on the same scope of entries, so
    each function is proved against its relation by an [iff], by induction
    on the syntax; no invariant on the scope is needed, since a name denotes
    its innermost entry. *)

(** ** Results *)

Lemma elab_bind_elab_success : forall {A B} (m : elab_result A) (f : A -> elab_result B) b,
    elab_bind m f = elab_success b <-> exists a, m = elab_success a /\ f a = elab_success b.
Proof.
  intros; destruct m; cbn; split; intros H.
  - eauto.
  - destruct H as (? & [=<-] & ?); assumption.
  - discriminate.
  - destruct H as (? & ? & _); discriminate.
Qed.

Lemma elab_check_elab_success : forall b e u, elab_check b e = elab_success u <-> b = true.
Proof. intros [] ? []; cbn; split; congruence. Qed.

Ltac inv_elab_success :=
  repeat match goal with
    | H : elab_success _ = elab_success _ |- _ => injection H as H; subst
    | H : Some _ = Some _ |- _ => injection H as H; subst
    end.

Ltac dest_elab_success :=
  repeat match goal with
    | H : elab_bind _ _ = elab_success _ |- _ => apply elab_bind_elab_success in H as (? & ? & H); cbv beta in H
    | H : elab_check _ _ = elab_success _ |- _ => apply elab_check_elab_success in H
    | H : elab_success _ = elab_success _ |- _ => injection H as H; subst
    | H : (_, _) = (_, _) |- _ => injection H as H; subst
    | H : elab_failure _ = elab_success _ |- _ => discriminate H
    end.

(** ** Names *)

Lemma mem_b_iff : forall x l, mem_b x l = true <-> In x l.
Proof.
  intros; unfold mem_b; rewrite existsb_exists; split.
  - intros (y & Hin & Hb); apply String.eqb_eq in Hb; subst; assumption.
  - intros Hin; exists x; split; [ assumption | apply String.eqb_refl ].
Qed.

Lemma binds_b_iff : forall x e, binds_b x e = true <-> scope_entry_name e = Some x.
Proof.
  intros x []; cbn; rewrite ?String.eqb_eq; split; congruence.
Qed.

Lemma names_cons : forall e S,
    names (e :: S) = match scope_entry_name e with Some x => x :: nil | None => nil end ++ names S.
Proof. reflexivity. Qed.

Lemma names_app : forall S1 S2, names (S1 ++ S2) = names S1 ++ names S2.
Proof. intros; unfold names; apply flat_map_app. Qed.

Lemma lookup_iff : forall x S k e, lookup x S = Some (k, e) <-> bound S x k e.
Proof.
  intros x. induction S as [| e0 S IH]; intros k e; cbn [lookup].
  - split; [ discriminate | intros [[] ? [=] _ _ _] ].
  - destruct (binds_b x e0) eqn:E; split.
    + intros [=<- <-]. apply binds_b_iff in E. apply (mk_bound _ _ _ _ nil S); cbn; tauto.
    + intros [[| e1 S1] S2 Heq Hx Hn ->]; cbn in Heq.
      * injection Heq as <- <-; reflexivity.
      * injection Heq as <- ->. exfalso; apply Hn. rewrite names_cons. apply binds_b_iff in E. rewrite E. left; reflexivity.
    + case_eq (lookup x S); [ intros [k' e'] El | intros _ ]; cbn; [| discriminate ].
      intros [=<- <-]. apply IH in El as [S1 S2 -> Hx Hn ->].
      apply (mk_bound _ _ _ _ (e0 :: S1) S2); cbn; try reflexivity; try assumption.
      change (flat_map _ S1) with (names S1). intros Hin. apply in_app_or in Hin as [Hin | Hin]; [| contradiction ].
      destruct (scope_entry_name e0) as [y |] eqn:Ey; [| contradiction ].
      destruct Hin as [-> | []]. apply (proj2 (binds_b_iff _ _)) in Ey. congruence.
    + intros [[| e1 S1] S2 Heq Hx Hn ->]; cbn in Heq.
      * injection Heq as <- <-. apply (proj2 (binds_b_iff _ _)) in Hx. congruence.
      * injection Heq as <- ->. rewrite names_cons in Hn.
        rewrite (proj2 (IH _ _))
          by (apply (mk_bound _ _ _ _ S1 S2); auto; intros Hin; apply Hn, in_or_app; auto).
        reflexivity.
Qed.

Lemma bound_in : forall S x k e, bound S x k e -> In x (names S).
Proof.
  intros * [S1 S2 -> Hx _ _]. rewrite names_app, names_cons, Hx. apply in_or_app; right; left; reflexivity.
Qed.

Lemma lookup_none : forall x S, lookup x S = None <-> ~ In x (names S).
Proof.
  intros x; induction S as [| e S IH]; cbn [lookup]; [ cbn; tauto |].
  rewrite names_cons, in_app_iff.
  destruct (binds_b x e) eqn:E.
  - apply binds_b_iff in E; rewrite E. split; [ discriminate | intros H; exfalso; apply H; left; left; reflexivity ].
  - assert (Hn : ~ In x (match scope_entry_name e with Some y => y :: nil | None => nil end)).
    { destruct (scope_entry_name e) eqn:Ey; cbn; [| tauto ]. intros [<- | []]. apply (proj2 (binds_b_iff _ _)) in Ey. congruence. }
    case_eq (lookup x S); [ intros [k e'] El | intros El ]; cbn; split; intros H; try discriminate.
    + exfalso; apply H; right. eapply bound_in, lookup_iff, El.
    + intros [? | Hin]; [ contradiction | apply IH in El; contradiction ].
    + reflexivity.
Qed.

Lemma entry_to_term_iff : forall k e M, entry_to_term k e = elab_success M <-> entry_denotes_term k e M.
Proof.
  intros * ; destruct e as [| | | | ? ? []]; cbn; split; intros H; inversion H; subst; constructor || reflexivity.
Qed.

Lemma entry_to_mod_iff : forall k e H, entry_to_mod k e = elab_success H <-> entry_denotes_mod k e H.
Proof. intros * ; destruct e; cbn; split; intros H'; inversion H'; subst; constructor || reflexivity. Qed.

Lemma check_fresh_ok : forall x P u, check_fresh x P = elab_success u <-> fresh x P.
Proof.
  intros x P []; unfold check_fresh, fresh; rewrite elab_check_elab_success, negb_true_iff, <- not_true_iff_false, mem_b_iff.
  reflexivity.
Qed.

Lemma check_fresh_all_ok : forall xs P u, check_fresh_all xs P = elab_success u <-> Forall (fun d => fresh d P) xs.
Proof.
  induction xs as [| x xs IH]; intros P []; cbn [check_fresh_all].
  - split; constructor.
  - rewrite elab_bind_elab_success, Forall_cons_iff, <- (IH P tt), <- (check_fresh_ok x P tt).
    split; [ intros ([] & ? & ?); auto | intros []; eauto ].
Qed.

Lemma first_dup_none : forall xs, first_dup xs = None <-> NoDup xs.
Proof.
  induction xs as [| x xs IH]; cbn; [ split; constructor |].
  destruct (mem_b x xs) eqn:E.
  - apply mem_b_iff in E. split; [ discriminate | intros Hnd; inversion Hnd; contradiction ].
  - rewrite IH. split; [ intros Hnd; constructor; [ intros Hin; apply mem_b_iff in Hin; congruence | assumption ] |].
    intros Hnd; inversion Hnd; assumption.
Qed.

Lemma check_params_ok : forall ps u, check_params ps = elab_success u <-> NoDup (map fst ps).
Proof.
  intros ps []; unfold check_params; rewrite <- first_dup_none.
  destruct (first_dup (map fst ps)); split; congruence.
Qed.

Lemma unit_in_b_iff : forall fq S, unit_in_b fq S = true <-> In (scope_entry_unit fq) S.
Proof.
  intros; unfold unit_in_b; rewrite existsb_exists; split.
  - intros ([] & Hin & Hb); try discriminate. apply path_beq_true in Hb; subst; assumption.
  - intros Hin; eexists; split; [ eassumption | apply path_beq_refl ].
Qed.

(** ** Open Targets *)

(** A projection chain is a module expression's spine of [me_mem]s. *)
Lemma spec_modexp_proj_chain : forall S ip o E,
    spec_modexp S (fold_left Cst.proj ip o) E <-> exists H, spec_modexp S o H /\ E = fold_left me_mem ip H.
Proof.
  intros S; induction ip as [| y ip IH]; intros o E; cbn [fold_left].
  - split; [ eauto | intros (H & HH & ->); assumption ].
  - rewrite IH; split.
    + intros (H' & Hs & ->); inversion Hs; subst; eauto.
    + intros (H & Hs & ->); exists (me_mem H y); split; [ constructor; assumption | reflexivity ].
Qed.

(** And the arguments of a module are its spine of [me_app]s. *)
Lemma spec_modexp_app_chain : forall S args o E,
    spec_modexp S (fold_left Cst.app args o) E <->
    exists H Ns, spec_modexp S o H /\ Forall2 (spec_exp S) args Ns /\ E = mapps H Ns.
Proof.
  intros S; induction args as [| a args IH]; intros o E; cbn [fold_left].
  - split; [ intros; exists E, nil; auto | intros (H & Ns & HH & HN & ->); inversion HN; subst; assumption ].
  - rewrite IH; split.
    + intros (H' & Ns & Hs & HN & ->); inversion Hs; subst.
      do 2 eexists; split; [ eassumption | split; [ constructor; eassumption | reflexivity ] ].
    + intros (H & Ns & Hs & HN & ->); inversion HN; subst.
      exists (me_app H y), l'; split; [ constructor; assumption | split; [ assumption | reflexivity ] ].
Qed.

(** A name in module position, as [elab_mod] reads it. *)
Lemma name_mod_iff : forall S x H,
    match lookup x S with
    | Some (k, e) => entry_to_mod k e
    | None => unit_mod x S
    end = elab_success H <-> spec_modexp S (Cst.var x) H.
Proof.
  intros; case_eq (lookup x S); [ intros [k e] El | intros El ]; split.
  - intros Hd; econstructor; [ apply lookup_iff; eassumption | apply entry_to_mod_iff; assumption ].
  - intros Hs; inversion Hs; subst.
    + match goal with Hb : bound _ _ _ _ |- _ => apply lookup_iff in Hb; rewrite Hb in El; inv_elab_success end.
      apply entry_to_mod_iff; assumption.
    + exfalso; match goal with Hn : ~ In x (names S) |- _ => apply Hn end.
      eapply bound_in, lookup_iff, El.
  - unfold unit_mod; destruct (unit_in_b (x :: nil) S) eqn:Eu; [| discriminate ].
    intros [= <-]; apply spec_modexp_unit1; [ apply lookup_none; exact El | apply unit_in_b_iff; exact Eu ].
  - intros Hs; inversion Hs; subst.
    + match goal with Hb : bound _ _ _ _ |- _ => apply lookup_iff in Hb; congruence end.
    + unfold unit_mod; match goal with Hu : In (scope_entry_unit _) S |- _ => apply unit_in_b_iff in Hu; rewrite Hu end; reflexivity.
Qed.

Lemma ihead_iff : forall S fq ip H,
    elab_ihead S fq ip = elab_success H <-> exists o, ihead fq ip = Some o /\ spec_modexp S o H.
Proof.
  intros. destruct fq as [| f fq]; [ destruct ip as [| x ip] |]; cbn [elab_ihead ihead].
  - split; [ discriminate | intros (? & [=] & _) ].
  - rewrite elab_bind_elab_success; split.
    + intros (H' & Hx & [=<-]). eexists; split; [ reflexivity |].
      apply spec_modexp_proj_chain; exists H'; split; [ apply name_mod_iff; assumption | reflexivity ].
    + intros (o & [=<-] & Hs). apply spec_modexp_proj_chain in Hs as (H' & Hs & ->).
      exists H'; split; [ apply name_mod_iff; assumption | reflexivity ].
  - rewrite elab_bind_elab_success; split.
    + intros ([] & Hu & [=<-]); apply elab_check_elab_success, unit_in_b_iff in Hu.
      eexists; split; [ reflexivity |]. apply spec_modexp_proj_chain; eexists; split; [ constructor; eassumption | reflexivity ].
    + intros (o & [=<-] & Hs). apply spec_modexp_proj_chain in Hs as (H' & Hs & ->). inversion Hs; subst.
      exists tt; split; [ apply elab_check_elab_success, unit_in_b_iff; assumption | reflexivity ].
Qed.

(** ** Objects *)

(** The loop of [elab_mdef], stated on its own. *)
Fixpoint elab_body (S : list scope_entry) (Φ : gmod) (cs : list Cst.cmd) : elab_result gmod :=
  match cs with
  | nil => elab_success Φ
  | Cst.c_def m x oA oM :: cs' =>
      let* A := elab S oA in
      let* M := elab S oM in
      elab_body (scope_entry_var x :: S) (gm_ext Φ x (ge_def (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M))) cs'
  | Cst.c_mod pv x ps md' :: cs' =>
      let* _ := check_params ps in
      let* tys := elab_params_with elab S ps in
      let* D := elab_mdef (param_scope_entries ps ++ S) md' in
      elab_body (scope_entry_var x :: S) (gm_ext Φ x (ge_mod pv (gu_mk (ptele tys) D))) cs'
  | Cst.c_open fq ip args its :: cs' =>
      let* E := elab_target_with elab S fq ip args in
      elab_body (item_scope_entries its ++ S) (gm_open Φ E its) cs'
  | Cst.c_axiom _ _ :: _ => elab_failure "axioms are not allowed in a local module"
  | Cst.c_import _ :: _ => elab_failure "import is not allowed in a local module; use open"
  | Cst.c_error e :: _ => elab_failure e
  | Cst.c_eval _ _ :: _ => elab_failure "eval is not allowed in a local module"
  | Cst.c_ind _ _ _ _ :: _ => elab_failure "an inductive type is not allowed in a local module"
  | Cst.c_mdef _ _ _ :: _ => elab_failure "a mutual definition is not allowed in a local module"
  | Cst.c_builtin _ _ :: _ => elab_failure "builtin is not allowed in a local module"
  | Cst.c_ind_alias _ x ps oE :: _ => elab_failure (local_alias_error "an inductive alias" x ps oE)
  | Cst.c_record_alias _ x ps oE :: _ => elab_failure (local_alias_error "a record alias" x ps oE)
  | Cst.c_record _ _ _ _ _ _ :: _ => elab_failure "a record type is not allowed in a local module"
  end.

Lemma elab_mdef_where : forall S cs, elab_mdef S (Cst.md_where cs) = let* Φ := elab_body S gm_nil cs in elab_success (md_body sm_open Φ).
Proof. reflexivity. Qed.

Definition Pterm (o : Cst.expression) : Prop := forall S M, elab S o = elab_success M <-> spec_exp S o M.
Definition Pmod (o : Cst.expression) : Prop := forall S H, elab_mod S o = elab_success H <-> spec_modexp S o H.
Definition Pmdef (md : Cst.mdef) : Prop := forall S D, elab_mdef S md = elab_success D <-> spec_def S md D.
Definition Pbody (cs : list Cst.cmd) : Prop := forall S Φ Φ', elab_body S Φ cs = elab_success Φ' <-> spec_body S Φ cs Φ'.
Definition Pbcmd (c : Cst.cmd) : Prop := forall cs, Pbody cs -> Pbody (c :: cs).

(** Turn the elaborator's results into the specification's premises, and
    back, by the [iff]s at hand. *)
Ltac to_spec :=
  repeat match goal with
    | H : elab ?S ?o = elab_success _, IH : forall S M, elab S ?o = elab_success M <-> _ |- _ => apply IH in H
    | H : elab_mod ?S ?o = elab_success _, IH : forall S H, elab_mod S ?o = elab_success H <-> _ |- _ => apply IH in H
    | H : elab_mdef ?S ?o = elab_success _, IH : forall S D, elab_mdef S ?o = elab_success D <-> _ |- _ => apply IH in H
    | H : elab_body _ _ ?cs = elab_success _, IH : forall S Φ Φ', elab_body S Φ ?cs = elab_success Φ' <-> _ |- _ => apply IH in H
    | H : elab_params_with elab _ _ = elab_success _, IH : forall S tys, elab_params_with elab S ?ps = elab_success tys <-> _ |- _ =>
        apply IH in H
    | H : check_params _ = elab_success _ |- _ => apply check_params_ok in H
    | H : check_fresh _ _ = elab_success _ |- _ => apply check_fresh_ok in H
    end.

Ltac to_elab :=
  repeat match goal with
    | H : spec_exp ?S ?o _, IH : forall S M, elab S ?o = elab_success M <-> _ |- _ => apply IH in H
    | H : spec_modexp ?S ?o _, IH : forall S H, elab_mod S ?o = elab_success H <-> _ |- _ => apply IH in H
    | H : spec_def ?S ?o _, IH : forall S D, elab_mdef S ?o = elab_success D <-> _ |- _ => apply IH in H
    | H : spec_body _ _ ?cs _, IH : forall S Φ Φ', elab_body S Φ ?cs = elab_success Φ' <-> _ |- _ => apply IH in H
    | H : spec_params _ ?ps _, IH : forall S tys, elab_params_with elab S ?ps = elab_success tys <-> _ |- _ => apply IH in H
    | H : NoDup (map fst ?ps) |- _ => apply (check_params_ok ps tt) in H
    | H : fresh ?x ?F |- _ => apply (check_fresh_ok x F tt) in H
    end;
  repeat match goal with
    | H : ?e = elab_success _ |- context [?e] => rewrite H; cbn [elab_bind]
    end.

Ltac iff_case :=
  let Hg := fresh "Hg" in
  split; intros Hg;
  [ dest_elab_success; to_spec; econstructor; eassumption
  | inversion Hg; subst; to_elab; reflexivity ].

Lemma params_iff : forall ps, Forall (fun p => Pterm (snd p)) ps ->
    forall S tys, elab_params_with elab S ps = elab_success tys <-> spec_params S ps tys.
Proof.
  induction 1 as [| [x oA] ps HA Hps IH]; intros S tys; cbn [elab_params_with].
  - split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
  - unfold Pterm in HA; cbn [snd] in HA. iff_case.
Qed.

Lemma args_iff : forall args, Forall Pterm args ->
    forall S Ns, elab_args_with elab S args = elab_success Ns <-> Forall2 (spec_exp S) args Ns.
Proof.
  induction 1 as [| o args Ho Hargs IH]; intros S Ns; cbn [elab_args_with].
  - split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
  - unfold Pterm in Ho. rewrite elab_bind_elab_success; split.
    + intros (N & HN & H); apply elab_bind_elab_success in H as (Ns' & HNs & [=<-]).
      constructor; [ apply Ho | apply IH ]; assumption.
    + intros H; inversion H; subst. eexists; split; [ apply Ho; eassumption |].
      rewrite (proj2 (IH _ _)) by eassumption. reflexivity.
Qed.

(** The target of an open, as [elab_mod] would read it. *)
Lemma target_iff : forall S fq ip args E, Forall Pterm args ->
    elab_target_with elab S fq ip args = elab_success E <-> exists o, itarget fq ip args = Some o /\ spec_modexp S o E.
Proof.
  intros * Hargs. unfold elab_target_with, itarget. rewrite elab_bind_elab_success. split.
  - intros (H & Hh & HE); apply elab_bind_elab_success in HE as (Ns & HNs & [=<-]).
    apply ihead_iff in Hh as (o & Ho & Hs). rewrite Ho; cbn [option_map].
    eexists; split; [ reflexivity |]. apply spec_modexp_app_chain; exists H, Ns; repeat split; try assumption.
    apply (args_iff _ Hargs); assumption.
  - intros (o' & Ho' & Hs). destruct (ihead fq ip) as [o |] eqn:Ho; [| discriminate ]. injection Ho' as <-.
    apply spec_modexp_app_chain in Hs as (H & Ns & Hs & HNs & ->).
    exists H; split; [ apply ihead_iff; eauto |].
    rewrite (proj2 (args_iff _ Hargs _ _)) by eassumption. reflexivity.
Qed.

Lemma brs_iff : forall bs, Forall (fun b => Pterm (snd b)) bs ->
    forall S Bs, elab_brs_with elab S bs = elab_success Bs <-> spec_branches S bs Bs.
Proof.
  induction 1 as [| [[c ys] oB] bs HB Hbs IH]; intros S Bs; cbn [elab_brs_with].
  - split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
  - unfold Pterm in HB; cbn [snd] in HB. split.
    + intros H; dest_elab_success. constructor; [ apply HB | apply IH ]; assumption.
    + intros H; inversion H; subst.
      rewrite (proj2 (HB _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (IH _ _)) by eassumption. reflexivity.
Qed.

(** The binders of a block, as [elab_binders_with] reads them. *)
Lemma binders_iff : forall xs, Forall (fun x => match snd x with Some A => Pterm A /\ Pmod A | None => True end) xs ->
    forall S pre oZ, elab_binders_with elab S pre xs = elab_success oZ <-> spec_binders S pre xs oZ.
Proof.
  induction 1 as [| [x oo] xs Hx Hxs IH]; intros S pre oZ; cbn [elab_binders_with].
  - split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
  - cbn [snd] in Hx; destruct xs as [| y xs'], oo as [o |].
    + destruct Hx as [Ho _]; unfold Pterm in Ho; split.
      * intros H; dest_elab_success; constructor; apply Ho; assumption.
      * intros H; inversion H; subst; rewrite (proj2 (Ho _ _)) by eassumption; reflexivity.
    + split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
    + split; [ discriminate | intros H; inversion H ].
    + rewrite IH; split; [ intros H; constructor; exact H | intros H; inversion H; subst; assumption ].
Qed.

Lemma blocks_iff : forall bks,
    Forall (fun bk => Forall (fun x => match snd x with Some A => Pterm A /\ Pmod A | None => True end) (snd (fst (fst bk))) /\
                      (Pterm (snd (fst bk)) /\ Pmod (snd (fst bk))) /\
                      Forall (fun b => Pterm (snd b) /\ Pmod (snd b)) (snd bk)) bks ->
    forall S Bks, elab_blocks_with elab S bks = elab_success Bks <-> spec_blocks S bks Bks.
Proof.
  induction 1 as [| [[[k xs] oA] bs] bks [Hxs [[HA _] Hbs]] _ IH]; intros S Bks; cbn [elab_blocks_with].
  - split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
  - cbn [fst snd] in *.
    pose proof (binders_iff _ Hxs) as Hxi.
    assert (Hb : forall S Bs, elab_brs_with elab S bs = elab_success Bs <-> spec_branches S bs Bs)
      by (apply brs_iff; eapply Forall_impl; [| exact Hbs ]; intros ? []; assumption).
    unfold Pterm in HA; split.
    + intros H; apply elab_bind_elab_success in H as (oZ & HZ & H); apply elab_bind_elab_success in H as (A & HA' & H).
      apply elab_bind_elab_success in H as (Bs & HBs & H); apply elab_bind_elab_success in H as (Bks' & HBks & H); inv_elab_success.
      constructor; [ apply Hxi; exact HZ | apply HA; exact HA' | apply Hb; exact HBs | apply IH; exact HBks ].
    + intros H; inversion H; subst.
      rewrite (proj2 (Hxi _ _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (HA _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (Hb _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (IH _ _)) by eassumption; reflexivity.
Qed.

(** The fields of a record value, as [elab_tfields_with] reads them. *)
Lemma tfields_iff : forall fs, Forall (fun f => Pterm (snd f)) fs ->
    forall S Ms, elab_tfields_with elab S fs = elab_success Ms <-> spec_tuple_fields S fs Ms.
Proof.
  induction 1 as [| [y oM] fs HM Hfs IH]; intros S Ms; cbn [elab_tfields_with].
  - split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
  - unfold Pterm in HM; cbn [snd] in HM. split.
    + intros H; dest_elab_success. constructor; [ apply HM | apply IH ]; assumption.
    + intros H; inversion H; subst.
      rewrite (proj2 (HM _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (IH _ _)) by eassumption. reflexivity.
Qed.

Lemma Pterm_params : forall ps : list (string * Cst.expression),
    Forall (fun p => Pterm (snd p) /\ Pmod (snd p)) ps -> Forall (fun p => Pterm (snd p)) ps.
Proof. intros ps; apply Forall_impl; intros ? []; assumption. Qed.

(** A local module, as [elab] and [elab_body] build it. *)
Lemma spec_unit_iff : forall S ps md U,
    Forall (fun p => Pterm (snd p)) ps -> Pmdef md ->
    (let* _ := check_params ps in
     let* tys := elab_params_with elab S ps in
     let* D := elab_mdef (param_scope_entries ps ++ S) md in
     elab_success (gu_mk (ptele tys) D)) = elab_success U <-> spec_unit S ps md U.
Proof.
  intros * Hps Hmd. pose proof (params_iff _ Hps) as IHps. unfold Pmdef in Hmd. iff_case.
Qed.

(** The hypothesis [Cst.cst_ind] gives about the blocks of an eliminator,
    in the form [blocks_iff] takes. *)
Lemma blocks_all_Forall : forall (P : Cst.expression -> Prop)
    (bks : list (bool * list (string * option Cst.expression) * Cst.expression * list (string * list string * Cst.expression))),
    list_all _ (prod_all _ (prod_all _ (prod_all bool (fun _ => unit) _
                  (list_all _ (prod_all string (fun _ => unit) (option Cst.expression) (option_all Cst.expression P))))
                  Cst.expression P) _ (list_all _ (prod_all (string * list string)%type (fun _ => unit) Cst.expression P))) bks ->
    Forall (fun bk => Forall (fun x => match snd x with Some A => P A | None => True end) (snd (fst (fst bk))) /\
                      P (snd (fst bk)) /\ Forall (fun b => P (snd b)) (snd bk)) bks.
Proof.
  intros P bks; apply list_all_Forall_impl.
  intros bk Hbk; destruct Hbk as [kxA HkxA bs Hbs]; destruct HkxA as [kx Hkx A HA]; destruct Hkx as [k _ xs Hxs].
  cbn [fst snd]; split; [| split; [ exact HA | exact (list_all_snd _ _ _ _ Hbs) ] ].
  refine (list_all_Forall_impl _ _ _ xs _ Hxs).
  intros x Hx; destruct Hx as [y _ o Ho]; exact (option_all_match _ _ _ Ho).
Qed.

Lemma expressions_iff :
  (forall o, Pterm o /\ Pmod o) /\
  (forall d, forall ob, Pterm ob -> forall S M,
      elab S (Cst.letb d ob) = elab_success M <-> spec_exp S (Cst.letb d ob) M) /\
  (forall md, Pmdef md) /\ (forall c, Pbcmd c).
Proof.
  apply Cst.cst_ind; unfold Pterm, Pmod, Pmdef, Pbcmd, Pbody.
  all: try (intros; repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
            split; intros S M; cbn [elab elab_mod];
            solve [ iff_case | let Hg := fresh "Hg" in split; [ discriminate | intros Hg; inversion Hg ] ]).
  - (* var *)
    intros x; split; [| intros S M; apply name_mod_iff ].
    intros S M; cbn [elab];
      (case_eq (lookup x S); [ intros [k e] El | intros El ]; split;
       [ intros H | intros Hs; inversion Hs; subst | discriminate | intros Hs; inversion Hs; subst ]).
    + econstructor; [ apply lookup_iff; eassumption | apply entry_to_term_iff; assumption ].
    + match goal with Hb : bound _ _ _ _ |- _ => apply lookup_iff in Hb; rewrite Hb in El; inv_elab_success end.
      apply entry_to_term_iff; assumption.
    + match goal with Hb : bound _ _ _ _ |- _ => apply lookup_iff in Hb; congruence end.
  - (* glob *)
    intros fq; split; intros S M; cbn [elab elab_mod]; split; intros H.
    + discriminate.
    + inversion H.
    + dest_elab_success; constructor; apply unit_in_b_iff; assumption.
    + inversion H; subst. rewrite (proj2 (unit_in_b_iff _ _)) by assumption. reflexivity.
  - (* proj: a member of a path's module, or of a term's, let-bound *)
    intros o [IHt IHm] x; split; intros S M; cbn [elab elab_mod].
    + destruct (expression_path o) eqn:Ep; split; intros Hg.
      * apply elab_bind_elab_success in Hg as (H & HH & Hg); inv_elab_success; constructor; [ exact Ep | apply IHm; exact HH ].
      * inversion Hg; subst; [ rewrite (proj2 (IHm _ _)) by eassumption; reflexivity | congruence ].
      * apply elab_bind_elab_success in Hg as (M' & HM & Hg); inv_elab_success; apply spec_exp_proj_let; [ exact Ep | apply IHt; exact HM ].
      * inversion Hg; subst; [ congruence | rewrite (proj2 (IHt _ _)) by eassumption; reflexivity ].
    + split; intros Hg.
      * apply elab_bind_elab_success in Hg as (H & HH & Hg); inv_elab_success; constructor; apply IHm; exact HH.
      * inversion Hg; subst; rewrite (proj2 (IHm _ _)) by eassumption; reflexivity.
  - (* letb *)
    intros d IHd o [IH _]; split; [ apply IHd, IH |].
    intros S M; destruct d; cbn [elab_mod]; split; intros H; try discriminate; inversion H.
  - (* elim *)
    intros om [IHm _] bks Hbks.
    pose proof (blocks_iff _ (blocks_all_Forall _ _ Hbks)) as Hb.
    split; intros S M; cbn [elab elab_mod].
    + split; intros Hg.
      * apply elab_bind_elab_success in Hg as (M' & HM & Hg); apply elab_bind_elab_success in Hg as (Bks & HB & Hg).
        destruct (elim_at _) as [m |] eqn:Ea; [ inv_elab_success | discriminate ].
        econstructor; [ apply IHm; exact HM | apply Hb; exact HB | exact Ea ].
      * inversion Hg; subst.
        rewrite (proj2 (IHm _ _)) by eassumption; cbn [elab_bind].
        rewrite (proj2 (Hb _ _)) by eassumption; cbn [elab_bind].
        match goal with Ea : elim_at _ = Some _ |- _ => rewrite Ea end; reflexivity.
    + split; [ discriminate | intros Hg; inversion Hg ].
  - (* tuple *)
    intros oT [IHT _] fs Hfs; apply list_all_snd in Hfs.
    assert (Hf : forall S Ms, elab_tfields_with elab S fs = elab_success Ms <-> spec_tuple_fields S fs Ms)
      by (apply tfields_iff; eapply Forall_impl; [| exact Hfs ]; intros ? []; assumption).
    split; intros S M; cbn [elab elab_mod].
    + split; intros Hg.
      * apply elab_bind_elab_success in Hg as (T & HT & Hg); apply elab_bind_elab_success in Hg as (Ms & HMs & Hg); inv_elab_success.
        constructor; [ apply IHT; exact HT | apply Hf; exact HMs ].
      * inversion Hg; subst.
        rewrite (proj2 (IHT _ _)) by eassumption; cbn [elab_bind].
        rewrite (proj2 (Hf _ _)) by eassumption; reflexivity.
    + split; [ discriminate | intros Hg; inversion Hg ].
  - (* d_def *)
    intros x [o1 |] HA o2 [IH2 _] ob IHb S M; [ apply option_all_match in HA; destruct HA as [IH1 _] |]; cbn [elab]; iff_case.
  - (* d_mod *)
    intros x ps Hps md Hmd ob IHb S M. apply list_all_snd, Pterm_params in Hps.
    pose proof (spec_unit_iff S ps md) as Hu. cbn [elab]; split; intros Hg.
    + dest_elab_success. econstructor; [ apply Hu; [ assumption | exact Hmd |] | apply IHb; eassumption ].
      to_elab; reflexivity.
    + inversion Hg; subst. match goal with Hs : spec_unit _ _ _ _ |- _ => apply Hu in Hs; [| assumption | exact Hmd ] end.
      dest_elab_success. to_elab. reflexivity.
  - (* md_where *)
    intros cs Hcs S D. apply list_all_Forall in Hcs. rewrite elab_mdef_where, elab_bind_elab_success.
    assert (Hb : forall S Φ Φ', elab_body S Φ cs = elab_success Φ' <-> spec_body S Φ cs Φ').
    { induction Hcs as [| c cs Hc Hcs IH]; intros S' Φ Φ'.
      - cbn; split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
      - apply Hc; intros; apply IH. }
    split.
    + intros (Φ & HΦ & H); inv_elab_success. constructor; apply Hb; assumption.
    + intros H; inversion H; subst. eexists; split; [ apply Hb; eassumption | reflexivity ].
  - (* md_alias *)
    intros o [_ IHm] S D; cbn [elab_mdef]. iff_case.
  - (* c_mod *)
    intros pv x ps Hps md Hmd cs Hcs S Φ Φ'. apply list_all_snd, Pterm_params in Hps.
    pose proof (spec_unit_iff S ps md) as Hu. cbn [elab_body].
    split; intros Hg.
    + dest_elab_success. econstructor; [ apply Hu; [ assumption | exact Hmd |] | apply Hcs; eassumption ].
      to_elab; reflexivity.
    + inversion Hg; subst. match goal with Hs : spec_unit _ _ _ _ |- _ => apply Hu in Hs; [| assumption | exact Hmd ] end.
      dest_elab_success. to_elab. reflexivity.
  - (* c_def *)
    intros m x o1 [IH1 _] o2 [IH2 _] cs Hcs S Φ Φ'; cbn [elab_body].
    split; intros Hg.
    + dest_elab_success. to_spec. econstructor; eassumption.
    + inversion Hg; subst. to_elab. reflexivity.
  - (* c_axiom *)
    intros x o _ cs Hcs S Φ Φ'; cbn [elab_body]. split; [ discriminate | intros H; inversion H ].
  - (* c_import *)
    intros fq cs Hcs S Φ Φ'; cbn [elab_body]. split; [ discriminate | intros H; inversion H ].
  - (* c_open *)
    intros fq ip args Hargs its cs Hcs S Φ Φ'; apply list_all_Forall in Hargs; cbn [elab_body].
    assert (Ha : Forall Pterm args) by (eapply Forall_impl; [| exact Hargs ]; intros ? []; assumption).
    split; intros Hg.
    + apply elab_bind_elab_success in Hg as (E & HE & Hg). apply (target_iff _ _ _ _ _ Ha) in HE as (o & Ho & Hs).
      econstructor; [ eassumption | eassumption | apply Hcs; eassumption ].
    + inversion Hg; subst.
      rewrite (proj2 (target_iff _ _ _ _ _ Ha)) by eauto; cbn [elab_bind].
      apply Hcs; assumption.
  - (* c_error *)
    intros e cs Hcs S Φ Φ'; cbn [elab_body]. split; [ discriminate | intros H; inversion H ].
  - (* c_eval *)
    intros o _ oA _ cs Hcs S Φ Φ'; cbn [elab_body]. split; [ discriminate | intros H; inversion H ].
  - (* c_ind *)
    intros pv wr ps _ ms _ cs Hcs S Φ Φ'; cbn [elab_body]. split; [ discriminate | intros H; inversion H ].
  - (* c_mdef *)
    intros m ps _ fs _ cs Hcs S Φ Φ'; cbn [elab_body]. split; [ discriminate | intros H; inversion H ].
  - (* c_builtin *)
    intros k o _ cs Hcs S Φ Φ'; cbn [elab_body]. split; [ discriminate | intros H; inversion H ].
  - (* c_ind_alias *)
    intros pv x ps _ o _ cs Hcs S Φ Φ'; cbn [elab_body]. split; [ discriminate | intros H; inversion H ].
  - (* c_record_alias *)
    intros pv x ps _ o _ cs Hcs S Φ Φ'; cbn [elab_body]. split; [ discriminate | intros H; inversion H ].
  - (* c_record *)
    intros pv x ps _ o _ fs _ cs' _ cs Hcs S Φ Φ'; cbn [elab_body]. split; [ discriminate | intros H; inversion H ].
Qed.

Lemma elab_iff : forall S o M, elab S o = elab_success M <-> spec_exp S o M.
Proof. intros; apply (proj1 (proj1 expressions_iff o)). Qed.

Lemma elab_mod_iff : forall S o H, elab_mod S o = elab_success H <-> spec_modexp S o H.
Proof. intros; apply (proj2 (proj1 expressions_iff o)). Qed.

Lemma elab_params_iff : forall S ps tys, elab_params S ps = elab_success tys <-> spec_params S ps tys.
Proof.
  intros; apply params_iff, Forall_forall; intros ? _ ? ?; apply elab_iff.
Qed.

Lemma elab_target_iff : forall S fq ip args E,
    elab_target_with elab S fq ip args = elab_success E <-> exists o, itarget fq ip args = Some o /\ spec_modexp S o E.
Proof.
  intros; apply target_iff, Forall_forall; intros ? _ ? ?; apply elab_iff.
Qed.

Lemma elab_args_iff : forall S os Ns, elab_args_with elab S os = elab_success Ns <-> Forall2 (spec_exp S) os Ns.
Proof. intros; apply args_iff, Forall_forall; intros ? _ ? ?; apply elab_iff. Qed.

Lemma elab_brs_iff : forall S bs Bs, elab_brs_with elab S bs = elab_success Bs <-> spec_branches S bs Bs.
Proof. intros; apply brs_iff, Forall_forall; intros ? _ ? ?; apply elab_iff. Qed.

Lemma elab_rargs_iff : forall args S args', elab_rargs S args = elab_success args' <-> spec_constructor_args S args args'.
Proof.
  induction args as [| [y oA] args IH]; intros S args'; cbn [elab_rargs].
  - split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
  - split.
    + intros H; apply elab_bind_elab_success in H as (A & HA & H); apply elab_bind_elab_success in H as (r & Hr & H); inv_elab_success.
      constructor; [ apply elab_iff; exact HA | apply IH; exact Hr ].
    + intros H; inversion H; subst.
      rewrite (proj2 (elab_iff _ _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (IH _ _)) by eassumption. reflexivity.
Qed.

Lemma elab_rcons_iff : forall S cs cs', elab_rcons S cs = elab_success cs' <-> spec_constructors S cs cs'.
Proof.
  intros S; induction cs as [| [c args] cs IH]; intros cs'; cbn [elab_rcons].
  - split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
  - split.
    + intros H; apply elab_bind_elab_success in H as (a & Ha & H); apply elab_bind_elab_success in H as (cs'' & Hcs & H); inv_elab_success.
      constructor; [ apply elab_rargs_iff; exact Ha | apply IH; exact Hcs ].
    + intros H; inversion H; subst.
      rewrite (proj2 (elab_rargs_iff _ _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (IH _)) by eassumption. reflexivity.
Qed.

Lemma elab_members_iff : forall ms S ups xs rms, elab_members S ups xs ms = elab_success rms <-> spec_members S ups xs ms rms.
Proof.
  induction ms as [| [[x oT] cs] ms IH]; intros S ups xs rms; cbn [elab_members].
  - split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
  - destruct (split_pis oT) as [nps oS] eqn:Es; split.
    + intros H; apply elab_bind_elab_success in H as ([] & Hp & H); apply elab_bind_elab_success in H as (ntys & Hn & H).
      apply elab_bind_elab_success in H as (A & HA & H); apply elab_bind_elab_success in H as (cs' & Hc & H).
      apply elab_bind_elab_success in H as (rms' & Hr & H); inv_elab_success.
      econstructor; [ exact Es | apply (check_params_ok _ tt); exact Hp | apply elab_params_iff; exact Hn
                    | apply elab_iff; exact HA | apply elab_rcons_iff; exact Hc | apply IH; exact Hr ].
    + intros H; inversion H; subst.
      match goal with H : split_pis oT = _ |- _ => rewrite Es in H; injection H as <- <- end.
      rewrite (proj2 (check_params_ok _ tt)) by assumption; cbn [elab_bind].
      rewrite (proj2 (elab_params_iff _ _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (elab_iff _ _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (elab_rcons_iff _ _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (IH _ _ _ _)) by eassumption; reflexivity.
Qed.

Lemma elab_funs_iff : forall fs S rfs, elab_funs S fs = elab_success rfs <-> spec_functions S fs rfs.
Proof.
  induction fs as [| [[[f ps] oA] bs] fs IH]; intros S rfs; cbn [elab_funs].
  - split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
  - split.
    + destruct (rev ps) as [| [z oZ] rys] eqn:Er; [ discriminate |].
      assert (Eps : ps = rev rys ++ (z, oZ) :: nil) by (rewrite <- (rev_involutive ps), Er; reflexivity).
      intros H; apply elab_bind_elab_success in H as ([] & Hp & H); apply elab_bind_elab_success in H as (ytys & Hy & H).
      apply elab_bind_elab_success in H as (Z & HZ & H); apply elab_bind_elab_success in H as (A & HA & H).
      apply elab_bind_elab_success in H as (Bs & HBs & H); apply elab_bind_elab_success in H as (rfs' & Hr & H); inv_elab_success.
      econstructor; [ apply (check_params_ok _ tt); exact Hp | apply elab_params_iff; exact Hy
                    | apply elab_iff; exact HZ | apply elab_iff; exact HA | apply elab_brs_iff; exact HBs | apply IH; exact Hr ].
    + intros H; inversion H; subst.
      rewrite rev_unit, rev_involutive; cbn [elab_bind].
      rewrite (proj2 (check_params_ok _ tt)) by assumption; cbn [elab_bind].
      rewrite (proj2 (elab_params_iff _ _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (elab_iff _ _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (elab_iff _ _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (elab_brs_iff _ _ _)) by eassumption; cbn [elab_bind].
      rewrite (proj2 (IH _ _)) by eassumption; reflexivity.
Qed.

Lemma check_distinct_ok : forall w xs u, check_distinct w xs = elab_success u <-> NoDup xs.
Proof.
  intros w xs []; unfold check_distinct; rewrite <- first_dup_none.
  destruct (first_dup xs); split; congruence.
Qed.

Lemma check_no_field_ok : forall x fs cs u,
    check_no_field x fs cs = elab_success u <-> Forall (fun y => ~ In y fs) (flat_map cmd_decls cs).
Proof.
  intros x fs cs []; unfold check_no_field; rewrite Forall_forall.
  destruct (find (fun y => mem_b y fs) (flat_map cmd_decls cs)) as [f |] eqn:E; split; try discriminate.
  - intros H; apply find_some in E as [Hin Hm]; apply mem_b_iff in Hm; exfalso; exact (H _ Hin Hm).
  - intros _ y Hin Hy; apply (find_none _ _ E) in Hin; apply (proj2 (mem_b_iff _ _)) in Hy; congruence.
  - intros _; reflexivity.
Qed.

(** ** Binders of a Scope

    A frame's members, units and open items are no binders, so a command
    keeps the binders of its scope, and the elaborator counts them once
    per frame. *)

(** The binders of two scopes, one inside the other, add up. *)
Lemma binders_app : forall S1 S2, binders (S1 ++ S2) = binders S1 + binders S2.
Proof.
  intros S1 S2; induction S1 as [| e S1 IH]; [ reflexivity |].
  change (binders ((e :: S1) ++ S2)) with (scope_entry_binders e + binders (S1 ++ S2)).
  change (binders (e :: S1)) with (scope_entry_binders e + binders S1).
  rewrite IH; lia.
Qed.

(** A member's entry is no binder. *)
Lemma binders_mem : forall x p m S, binders (scope_entry_mem x p m :: S) = binders S.
Proof. reflexivity. Qed.

(** Entries made one per item, each no binder, are no binders together. *)
Lemma binders_mems : forall {A} (f : A -> scope_entry) xs, (forall x, scope_entry_binders (f x) = 0) -> binders (rev (map f xs)) = 0.
Proof.
  intros A f xs Hf; induction xs as [| x xs IH]; cbn [map rev]; [ reflexivity |].
  rewrite binders_app, IH; cbn; rewrite Hf; reflexivity.
Qed.

(** The members an open declares in a frame are no binders. *)
Lemma binders_item_mems : forall fp ch n its, binders (item_mems fp ch n its) = 0.
Proof. intros; apply binders_mems; reflexivity. Qed.

(** Nor are the members a group or a mutual definition declares. *)
Lemma binders_filed_mems : forall fp ch n xs, binders (filed_mems fp ch n xs) = 0.
Proof. intros; apply binders_mems; reflexivity. Qed.

(** A record's frame binds its value and its parameters; its fields are
    members. *)
Lemma binders_record_scope_entries : forall fp ch n x ps fs,
    binders (record_scope_entries fp ch n x ps fs) = binders (scope_entry_self :: param_scope_entries ps).
Proof. intros; unfold record_scope_entries; rewrite binders_app, binders_filed_mems; reflexivity. Qed.

(** ** Commands

    A command is read in one scope, the frame's entries so far followed by
    everything outside the frame, onto whose front its declarations are
    pushed.  Every object a command reads is thus read in the same list as
    when the frame's entries and the outer scope were kept apart and
    concatenated for each read: a module body in [param_scope_entries ps ++ S], a
    record's with-area in [record_scope_entries … ++ scope_entry_mem x … :: S], the unit's
    frame in [param_scope_entries ps ++ L]. *)

Section Commands.
  Variable fp : path.

  (** A command keeps the binders of its scope. *)
  Lemma spec_cmd_binders : forall ch P S c S' c', spec_cmd fp ch P S c S' c' -> binders S' = binders S.
  Proof.
    intros * H; destruct H; rewrite ?binders_app, ?binders_mem, ?binders_item_mems, ?binders_filed_mems; reflexivity.
  Qed.

  (** [nb] is the count of the scope's binders the elaborator carries. *)
  Definition Pcmd (c : Cst.cmd) : Prop :=
    forall ch P nb S S' cs', nb = binders S -> (elab_cmd fp ch P nb S c = elab_success (S', cs') <-> spec_cmd fp ch P S c S' cs').
  Definition Pcmds (cs : list Cst.cmd) : Prop :=
    forall ch P nb S ccs, nb = binders S -> (elab_cmds fp ch P nb S cs = elab_success ccs <-> spec_cmds fp ch P S cs ccs).

  Lemma cmds_iff : forall cs, Forall Pcmd cs -> Pcmds cs.
  Proof.
    induction 1 as [| c cs Hc Hcs IH]; intros ch P nb S ccs ->; cbn.
    - split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
    - split.
      + intros H; apply elab_bind_elab_success in H as ([S' c'] & H1 & H); apply elab_bind_elab_success in H as (ccs' & H2 & H); inv_elab_success.
        cbn [fst snd] in *. apply (Hc _ _ _ _ _ _ eq_refl) in H1.
        econstructor; [ exact H1 |].
        refine (proj1 (IH _ _ _ _ _ _) H2). rewrite (spec_cmd_binders _ _ _ _ _ _ H1); reflexivity.
      + intros H; inversion H; subst.
        rewrite (proj2 (Hc _ _ _ _ _ _ eq_refl)) by eassumption; cbn [elab_bind fst snd].
        change (elab_cmds_with (elab_cmd fp) ch P (binders S) S' cs) with (elab_cmds fp ch P (binders S) S' cs).
        rewrite (proj2 (IH _ _ _ _ _ (eq_sym (spec_cmd_binders _ _ _ _ _ _ ltac:(eassumption))))) by eassumption.
        reflexivity.
  Qed.

  (** The count the elaborator passes to a nested frame is its scope's. *)
  Ltac binders_eq := rewrite ?binders_app, ?binders_mem, ?binders_record_scope_entries; reflexivity.

  Ltac cmd_spec :=
    repeat match goal with
      | H : elab _ _ = elab_success _ |- _ => apply elab_iff in H
      | H : elab_mod _ _ = elab_success _ |- _ => apply elab_mod_iff in H
      | H : elab_params _ _ = elab_success _ |- _ => apply elab_params_iff in H
      | H : elab_cmds_with (elab_cmd fp) _ _ _ _ ?cs = elab_success _, IH : Pcmds ?cs |- _ =>
          apply IH in H; [| binders_eq ]
      | H : check_params _ = elab_success _ |- _ => apply check_params_ok in H
      | H : check_fresh _ _ = elab_success _ |- _ => apply check_fresh_ok in H
      end.

  Ltac cmd_elab :=
    repeat match goal with
      | H : spec_exp _ _ _ |- _ => apply elab_iff in H
      | H : spec_modexp _ _ _ |- _ => apply elab_mod_iff in H
      | H : spec_params _ _ _ |- _ => apply elab_params_iff in H
      | H : spec_cmds fp _ _ ?S ?cs _, IH : Pcmds ?cs |- _ =>
          apply (proj2 (IH _ _ _ _ _ eq_refl)) in H; rewrite ?binders_app, ?binders_mem, ?binders_record_scope_entries in H
      | H : NoDup (map fst ?ps) |- _ => apply (check_params_ok ps tt) in H
      | H : fresh ?x ?F |- _ => apply (check_fresh_ok x F tt) in H
      end;
    unfold elab_cmds in *;
    repeat match goal with
      | H : ?e = elab_success _ |- context [?e] => rewrite H; cbn [elab_bind fst snd]
      end.

  Lemma commands_iff : forall c, Pcmd c.
  Proof.
    apply (fun H : (forall o : Cst.expression, True) /\ (forall d : Cst.decl, True) /\
                   (forall md, forall body, md = Cst.md_where body -> Pcmds body) /\ (forall c, Pcmd c) =>
             proj2 (proj2 (proj2 H))).
    apply Cst.cst_ind; try easy.
    - intros cs Hcs body [=<-]. apply cmds_iff, list_all_Forall, Hcs.
    - intros pv x ps _ [body | oE] Hmd ch P nb S S' c' ->;
        cbn [elab_cmd]; [ specialize (Hmd body eq_refl) |].
      all: split; intros Hg; [ dest_elab_success; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - intros m x o1 _ o2 _ ch P nb S S' c' ->; cbn [elab_cmd].
      split; intros Hg; [ dest_elab_success; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - intros x o _ ch P nb S S' c' ->; cbn [elab_cmd].
      split; intros Hg; [ dest_elab_success; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - intros fq ch P nb S S' c' ->; cbn [elab_cmd].
      split; [ intros H; inv_elab_success; constructor | intros H; inversion H; subst; reflexivity ].
    - intros fq ip args _ its ch P nb S S' c' ->; cbn [elab_cmd]. split.
      + intros H; apply elab_bind_elab_success in H as (E & HE & H); apply elab_bind_elab_success in H as ([] & Hf & H); inv_elab_success.
        apply elab_target_iff in HE as (o & Ho & Hs).
        econstructor; [ eassumption | eassumption | apply (check_fresh_all_ok _ _ tt); assumption ].
      + intros H; inversion H; subst.
        rewrite (proj2 (elab_target_iff _ _ _ _ _)) by eauto; cbn [elab_bind].
        rewrite (proj2 (check_fresh_all_ok _ _ tt)) by assumption. reflexivity.
    - intros o _ [oA |] _ ch P nb S S' c' ->; cbn [elab_cmd].
      all: split; intros Hg; [ dest_elab_success; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - intros pv wr ups _ ms _ ch P nb S S' c' ->; cbn [elab_cmd]; split.
      + intros Hg; apply elab_bind_elab_success in Hg as ([] & Hd & Hg); apply elab_bind_elab_success in Hg as ([] & Hf & Hg).
        apply elab_bind_elab_success in Hg as (tys & Ht & Hg); apply elab_bind_elab_success in Hg as (rms & Hm & Hg); inv_elab_success.
        econstructor; [ exact (proj1 (check_distinct_ok _ _ tt) Hd) | apply (check_fresh_all_ok _ _ tt); exact Hf
                      | apply elab_params_iff; exact Ht | apply elab_members_iff; exact Hm ].
      + intros Hg; inversion Hg; subst.
        rewrite (proj2 (check_distinct_ok "a group" _ tt)) by assumption; cbn [elab_bind].
        rewrite (proj2 (check_fresh_all_ok _ _ tt)) by assumption; cbn [elab_bind].
        rewrite (proj2 (elab_params_iff _ _ _)) by eassumption; cbn [elab_bind].
        rewrite (proj2 (elab_members_iff _ _ _ _ _)) by eassumption; reflexivity.
    - intros m ps _ fs _ ch P nb S S' c' ->; cbn [elab_cmd]; split.
      + intros Hg; apply elab_bind_elab_success in Hg as ([] & Hp & Hg); apply elab_bind_elab_success in Hg as ([] & Hd & Hg).
        apply elab_bind_elab_success in Hg as ([] & Hf & Hg); apply elab_bind_elab_success in Hg as (tys & Ht & Hg).
        apply elab_bind_elab_success in Hg as (rfs & Hr & Hg); inv_elab_success.
        econstructor; [ apply (check_params_ok _ tt); exact Hp | exact (proj1 (check_distinct_ok _ _ tt) Hd)
                      | apply (check_fresh_all_ok _ _ tt); exact Hf | apply elab_params_iff; exact Ht
                      | apply elab_funs_iff; exact Hr ].
      + intros Hg; inversion Hg; subst.
        rewrite (proj2 (check_params_ok _ tt)) by assumption; cbn [elab_bind].
        rewrite (proj2 (check_distinct_ok "a mutual definition" _ tt)) by assumption; cbn [elab_bind].
        rewrite (proj2 (check_fresh_all_ok _ _ tt)) by assumption; cbn [elab_bind].
        rewrite (proj2 (elab_params_iff _ _ _)) by eassumption; cbn [elab_bind].
        rewrite (proj2 (elab_funs_iff _ _ _)) by eassumption; reflexivity.
    - intros k o _ ch P nb S S' c' ->; cbn [elab_cmd]. split.
      + intros Hg; apply elab_bind_elab_success in Hg as (H & HH & Hg); inv_elab_success.
        econstructor; apply elab_mod_iff; exact HH.
      + intros Hg; inversion Hg; subst.
        rewrite (proj2 (elab_mod_iff _ _ _)) by eassumption; reflexivity.
    - intros pv x ps _ o _ ch P nb S S' c' ->; cbn [elab_cmd].
      split; intros Hg; [ dest_elab_success; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - (* a record alias, as an inductive alias *)
      intros pv x ps _ o _ ch P nb S S' c' ->; cbn [elab_cmd].
      split; intros Hg; [ dest_elab_success; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - (* a record type: its with-area by the commands' induction *)
      intros pv x ps _ o _ fs _ cs Hcs ch P nb S S' c' ->.
      apply list_all_Forall, cmds_iff in Hcs; cbn [elab_cmd]; split.
      + intros Hg; apply elab_bind_elab_success in Hg as ([] & Hf & Hg); apply elab_bind_elab_success in Hg as ([] & Hp & Hg).
        apply elab_bind_elab_success in Hg as (tys & Ht & Hg); apply elab_bind_elab_success in Hg as (Srt & HS & Hg).
        apply elab_bind_elab_success in Hg as (fs' & Hr & Hg); apply elab_bind_elab_success in Hg as ([] & Hn & Hg).
        apply elab_bind_elab_success in Hg as (bcs & Hb & Hg); dest_elab_success.
        econstructor; [ apply (check_fresh_ok _ _ tt); exact Hf | apply (check_params_ok _ tt); exact Hp
                      | apply elab_params_iff; exact Ht | apply elab_iff; exact HS | apply elab_rargs_iff; exact Hr
                      | apply (check_no_field_ok x _ _ tt); exact Hn | refine (proj1 (Hcs _ _ _ _ _ _) Hb); binders_eq ].
      + intros Hg; inversion Hg; subst.
        rewrite (proj2 (check_fresh_ok _ _ tt)) by assumption; cbn [elab_bind].
        rewrite (proj2 (check_params_ok _ tt)) by assumption; cbn [elab_bind].
        rewrite (proj2 (elab_params_iff _ _ _)) by eassumption; cbn [elab_bind].
        rewrite (proj2 (elab_iff _ _ _)) by eassumption; cbn [elab_bind].
        rewrite (proj2 (elab_rargs_iff _ _ _)) by eassumption; cbn [elab_bind].
        rewrite (proj2 (check_no_field_ok _ _ _ tt)) by assumption; cbn [elab_bind].
        change (elab_cmds_with (elab_cmd fp)) with (elab_cmds fp).
        match goal with Hb : spec_cmds fp _ _ _ cs _ |- _ => apply (proj2 (Hcs _ _ _ _ _ eq_refl)) in Hb;
          rewrite binders_app, binders_mem, binders_record_scope_entries in Hb; rewrite Hb end.
        reflexivity.
  Qed.

  Corollary elab_cmds_iff : forall ch P S cs ccs,
      elab_cmds fp ch P (binders S) S cs = elab_success ccs <-> spec_cmds fp ch P S cs ccs.
  Proof. intros; apply cmds_iff; [ apply Forall_forall; intros; apply commands_iff | reflexivity ]. Qed.
End Commands.

(** ** Member Counts

    A member's entry records the binders outside it when it is declared
    ([scope_entry_mem]).  The count stays right: a scope only grows at its front, so
    in every scope a command reads, each member's count is the number of
    binders outside its entry, which is what [vars_desc] needs. *)

(** In [S], each member's count is the binders outside its entry. *)
Definition mems_counted (S : list scope_entry) : Prop :=
  forall S1 x p m S2, S = S1 ++ scope_entry_mem x p m :: S2 -> m = binders S2.

(** Entries pushed on a counted scope [S] keep it counted when they are no
    binders and each member among them counts [binders S]. *)
Lemma counted_app : forall L S,
    mems_counted S ->
    Forall (fun e => scope_entry_binders e = 0 /\ forall x p m, e = scope_entry_mem x p m -> m = binders S) L ->
    mems_counted (L ++ S).
Proof.
  intros L S HS HL S1 x p m S2 Heq.
  apply app_eq_app in Heq as (l & [[-> Hl] | [-> Hl]]).
  - destruct l as [| e l]; cbn in Hl.
    + subst S; exact (HS nil x p m S2 eq_refl).
    + injection Hl as <- ->.
      apply Forall_app in HL as [_ HL]; inversion HL as [| ? ? [_ Hm] Hl']; subst.
      rewrite binders_app, (Hm x p m eq_refl).
      assert (H0 : binders l = 0).
      { clear - Hl'; induction Hl' as [| e l [He _] _ IH]; [ reflexivity |].
        change (binders (e :: l)) with (scope_entry_binders e + binders l); rewrite He, IH; reflexivity. }
      rewrite H0; reflexivity.
  - exact (HS l x p m S2 Hl).
Qed.

(** A scope with no member is counted. *)
Lemma counted_no_mem : forall S, (forall x p m, ~ In (scope_entry_mem x p m) S) -> mems_counted S.
Proof.
  intros S Hn S1 x p m S2 ->; exfalso; apply (Hn x p m), in_or_app; right; left; reflexivity.
Qed.

(** Entries that are no members, binders or not, pushed on a counted
    scope keep it counted: a member's count is about what lies outside
    it. *)
Lemma counted_push : forall L S, mems_counted S -> (forall x p m, ~ In (scope_entry_mem x p m) L) -> mems_counted (L ++ S).
Proof.
  intros L S HS Hn S1 x p m S2 Heq.
  apply app_eq_app in Heq as (l & [[-> Hl] | [-> Hl]]).
  - destruct l as [| e l]; cbn in Hl.
    + subst S; exact (HS nil x p m S2 eq_refl).
    + injection Hl as <- ->. exfalso; apply (Hn x p m), in_or_app; right; left; reflexivity.
  - exact (HS l x p m S2 Hl).
Qed.

(** The new entries of a command, as [counted_app] needs them *)
Lemma mems_fresh : forall {A} (f : A -> string) (g : A -> qname) n S xs,
    n = binders S ->
    Forall (fun e => scope_entry_binders e = 0 /\ forall x p m, e = scope_entry_mem x p m -> m = binders S)
      (rev (map (fun a => scope_entry_mem (f a) (g a) n) xs)).
Proof.
  intros A f g n S xs ->; apply Forall_rev, Forall_map, Forall_forall; intros a _.
  split; [ reflexivity | intros x p m [=]; congruence ].
Qed.

Section Counts.
  Variable fp : path.

  (** A command keeps its scope counted. *)
  Lemma spec_cmd_mems_counted : forall ch P S c S' c',
      spec_cmd fp ch P S c S' c' -> mems_counted S -> mems_counted S'.
  Proof.
    intros * H HS; destruct H; try exact HS.
    all: first
      [ change (scope_entry_mem ?y ?qy ?n :: S) with ((scope_entry_mem y qy n :: nil) ++ S);
        apply counted_app; [ exact HS | constructor; [ split; [ reflexivity | intros ? ? ? [=]; congruence ] | constructor ] ]
      | change (scope_entry_unit ?fq :: S) with ((scope_entry_unit fq :: nil) ++ S);
        apply counted_app; [ exact HS | constructor; [ split; [ reflexivity | intros ? ? ? [=] ] | constructor ] ]
      | apply counted_app; [ exact HS | apply mems_fresh; reflexivity ] ].
  Qed.

  (** So does a run of commands: each command [c] of a frame, after the
      commands [cs0], reads a counted scope. *)
  Lemma spec_cmds_mems_counted : forall ch P cs0 c cs1 S ccs,
      spec_cmds fp ch P S (cs0 ++ c :: cs1) ccs -> mems_counted S ->
      exists S1 S1' c', spec_cmd fp ch P S1 c S1' c' /\ mems_counted S1.
  Proof.
    intros ch P cs0; induction cs0 as [| c0 cs0 IH]; intros c cs1 S ccs H HS; inversion H; subst.
    - do 3 eexists; split; eassumption.
    - eapply IH; [ eassumption | eapply spec_cmd_mems_counted; eassumption ].
  Qed.

  (** A nested module's scope is counted when its enclosing one is: its
      parameters are no members. *)
  Lemma mod_scope_counted : forall ps S, mems_counted S -> mems_counted (param_scope_entries ps ++ S).
  Proof.
    intros ps S HS; apply counted_push; [ exact HS |].
    intros x p m Hin; unfold param_scope_entries in Hin; apply in_rev, in_map_iff in Hin as (? & [=] & _).
  Qed.

  (** So is a record's with-area's scope: its value and parameters are no
      members, and the record and its fields count the binders outside
      them. *)
  Lemma record_scope_counted : forall ch n x ps fs S,
      n = binders S -> mems_counted S ->
      mems_counted (record_scope_entries fp ch n x ps fs ++ scope_entry_mem x (q_abs fp (ch ++ x :: nil)) n :: S).
  Proof.
    intros * -> HS. unfold record_scope_entries. rewrite <- app_assoc.
    apply counted_app.
    - change (scope_entry_self :: param_scope_entries ps ++ scope_entry_mem x (q_abs fp (ch ++ x :: nil)) (binders S) :: S)
        with ((scope_entry_self :: param_scope_entries ps) ++ (scope_entry_mem x (q_abs fp (ch ++ x :: nil)) (binders S) :: nil) ++ S).
      apply counted_push; [ apply (counted_app (_ :: nil) S); [ exact HS | constructor; [ split; [ reflexivity | intros ? ? ? [=]; congruence ] | constructor ] ] |].
      intros y p m [Hin | Hin]; [ discriminate |]; unfold param_scope_entries in Hin; apply in_rev, in_map_iff in Hin as (? & [=] & _).
    - unfold filed_mems; apply mems_fresh. rewrite (binders_app (scope_entry_self :: param_scope_entries ps)), binders_mem. reflexivity.
  Qed.
End Counts.

(** A member a name denotes, in a counted scope, is generalized over
    exactly the binders outside its entry. *)
Corollary bound_mem_counted : forall S x k y p m,
    mems_counted S -> bound S x k (scope_entry_mem y p m) ->
    exists S1 S2, S = S1 ++ scope_entry_mem y p m :: S2 /\ k = binders S1 /\ m = binders S2.
Proof.
  intros * HS [S1 S2 Heq _ _ Hk]; exists S1, S2; split; [ exact Heq | split; [ exact Hk | exact (HS _ _ _ _ _ Heq) ] ].
Qed.

(** The leading scope has no member, so a unit's frame starts counted. *)
Lemma spec_lead_no_mem : forall L cs L' lds,
    spec_lead L cs L' lds -> (forall x p m, ~ In (scope_entry_mem x p m) L) -> forall x p m, ~ In (scope_entry_mem x p m) L'.
Proof.
  induction 1 as [| L fq cs L' lds _ IH | L fq ip args its o E cs L' lds _ _ _ IH]; intros Hn; [ exact Hn | |].
  - apply IH; intros x p m [[=] | Hin]; exact (Hn x p m Hin).
  - apply IH; intros x p m Hin; apply in_app_or in Hin as [Hin | Hin]; [| exact (Hn x p m Hin) ].
    unfold open_scope_entries in Hin; apply in_rev, in_map_iff in Hin as (? & [=] & _).
Qed.

(** The scope a unit's frame starts in, its parameters over the leading
    scope ([elab_spec_intro]), is counted. *)
Lemma elab_spec_frame_counted : forall leads ps L lds,
    spec_lead nil leads L lds -> mems_counted (param_scope_entries ps ++ L).
Proof.
  intros * Hl; apply counted_no_mem; intros x p m Hin; apply in_app_or in Hin as [Hin | Hin].
  - unfold param_scope_entries in Hin; apply in_rev, in_map_iff in Hin as (? & [=] & _).
  - exact (spec_lead_no_mem _ _ _ _ Hl (fun _ _ _ H => H) x p m Hin).
Qed.

(** ** Units *)

Lemma lead_iff : forall cs L L' lds, elab_lead L cs = elab_success (L', lds) <-> spec_lead L cs L' lds.
Proof.
  induction cs as [| c cs IH]; intros L L' lds; cbn [elab_lead].
  - split; [ intros H; inv_elab_success; constructor | intros H; inversion H; reflexivity ].
  - destruct c; try (split; [ discriminate | intros H; inversion H ]); rewrite elab_bind_elab_success; split.
    + intros ([L1 l1] & H & E); cbn [fst snd] in E; inv_elab_success. constructor; apply IH; exact H.
    + intros H; inversion H; subst. exists (L', lds0); split; [ apply IH; assumption | reflexivity ].
    + intros (E & HE & H). apply elab_target_iff in HE as (o & Ho & Hs).
      econstructor; [ eassumption | eassumption | apply IH; exact H ].
    + intros H; inversion H; subst. exists E; split; [ apply elab_target_iff; eauto | apply IH; assumption ].
Qed.

Theorem elaborate_core_iff : forall prg u, elaborate_core prg = elab_success u <-> elab_spec prg u.
Proof.
  intros [leads [[fp ps] cs]] u. unfold elaborate_core. split.
  - intros H; apply elab_bind_elab_success in H as ([L lds] & Hl & H); apply elab_bind_elab_success in H as ([] & Hp & H).
    apply elab_bind_elab_success in H as (tys & Ht & H); apply elab_bind_elab_success in H as (ccs & Hc & H); inv_elab_success.
    apply lead_iff in Hl. apply check_params_ok in Hp. apply elab_params_iff in Ht. apply elab_cmds_iff in Hc.
    econstructor; eassumption.
  - intros Hs; inversion Hs; subst.
    rewrite (proj2 (lead_iff _ _ _ _)) by eassumption; cbn [elab_bind].
    rewrite (proj2 (check_params_ok _ tt)) by assumption; cbn [elab_bind].
    rewrite (proj2 (elab_params_iff _ _ _)) by eassumption; cbn [elab_bind].
    rewrite (proj2 (elab_cmds_iff _ _ _ _ _ _)) by eassumption. reflexivity.
Qed.

(** Soundness: whatever the elaborator produces, the specification relates. *)
Corollary elaborate_core_sound : forall prg u, elaborate_core prg = elab_success u -> elab_spec prg u.
Proof. intros; apply elaborate_core_iff; assumption. Qed.

(** Completeness: whatever the specification relates, the elaborator produces. *)
Corollary elaborate_core_complete : forall prg u, elab_spec prg u -> elaborate_core prg = elab_success u.
Proof. intros; apply elaborate_core_iff; assumption. Qed.

(** The specification is functional. *)
Corollary elab_spec_functional : forall prg u1 u2, elab_spec prg u1 -> elab_spec prg u2 -> u1 = u2.
Proof.
  intros * H1 H2. apply elaborate_core_complete in H1, H2. rewrite H1 in H2. inversion H2; reflexivity.
Qed.

(** The elaborator fails exactly on the programs the specification relates
    to nothing. *)
Corollary elaborate_core_fails : forall prg,
    (exists e, elaborate_core prg = elab_failure e) <-> forall u, ~ elab_spec prg u.
Proof.
  intros; split.
  - intros (e & He) u Hs. apply elaborate_core_complete in Hs. congruence.
  - intros Hn. destruct (elaborate_core prg) as [u | e] eqn:E; [| eauto ].
    exfalso; apply (Hn u), elaborate_core_sound, E.
Qed.

(** The elaborator's units are written: no generated command in them
    ([elab_spec_written]). *)
Corollary to_core_written : forall prg u, to_core prg = Some u -> unit_written u.
Proof.
  intros * H; unfold to_core in H; destruct (elaborate_core prg) eqn:E; [| discriminate ].
  injection H as <-; exact (elab_spec_written _ _ (elaborate_core_sound _ _ E)).
Qed.
