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

Lemma ebind_eok : forall {A B} (m : eres A) (f : A -> eres B) b,
    ebind m f = eok b <-> exists a, m = eok a /\ f a = eok b.
Proof.
  intros; destruct m; cbn; split; intros H.
  - eauto.
  - destruct H as (? & [=<-] & ?); assumption.
  - discriminate.
  - destruct H as (? & ? & _); discriminate.
Qed.

Lemma echeck_eok : forall b e u, echeck b e = eok u <-> b = true.
Proof. intros [] ? []; cbn; split; congruence. Qed.

Ltac inv_eok :=
  repeat match goal with
    | H : eok _ = eok _ |- _ => injection H as H; subst
    | H : Some _ = Some _ |- _ => injection H as H; subst
    end.

Ltac dest_eok :=
  repeat match goal with
    | H : ebind _ _ = eok _ |- _ => apply ebind_eok in H as (? & ? & H); cbv beta in H
    | H : echeck _ _ = eok _ |- _ => apply echeck_eok in H
    | H : eok _ = eok _ |- _ => injection H as H; subst
    | H : (_, _) = (_, _) |- _ => injection H as H; subst
    | H : eerr _ = eok _ |- _ => discriminate H
    end.

(** ** Names *)

Lemma mem_b_iff : forall x l, mem_b x l = true <-> In x l.
Proof.
  intros; unfold mem_b; rewrite existsb_exists; split.
  - intros (y & Hin & Hb); apply String.eqb_eq in Hb; subst; assumption.
  - intros Hin; exists x; split; [ assumption | apply String.eqb_refl ].
Qed.

Lemma binds_b_iff : forall x e, binds_b x e = true <-> ent_name e = Some x.
Proof.
  intros x []; cbn; rewrite ?String.eqb_eq; split; congruence.
Qed.

Lemma names_cons : forall e S,
    names (e :: S) = match ent_name e with Some x => x :: nil | None => nil end ++ names S.
Proof. reflexivity. Qed.

Lemma names_app : forall S1 S2, names (S1 ++ S2) = names S1 ++ names S2.
Proof. intros; unfold names; apply flat_map_app. Qed.

Lemma lookup_iff : forall x S k e n, lookup x S = Some (k, e, n) <-> bound S x k e n.
Proof.
  intros x. induction S as [| e0 S IH]; intros k e n; cbn [lookup].
  - split; [ discriminate | intros [[] ? [=] _ _ _ _] ].
  - destruct (binds_b x e0) eqn:E; split.
    + intros [=<- <- <-]. apply binds_b_iff in E. apply (mk_bound _ _ _ _ _ nil S); cbn; tauto.
    + intros [[| e1 S1] S2 Heq Hx Hn -> ->]; cbn in Heq.
      * injection Heq as <- <-; reflexivity.
      * injection Heq as <- ->. exfalso; apply Hn. rewrite names_cons. apply binds_b_iff in E. rewrite E. left; reflexivity.
    + case_eq (lookup x S); [ intros [[k' e'] n'] El | intros _ ]; cbn; [| discriminate ].
      intros [=<- <- <-]. apply IH in El as [S1 S2 -> Hx Hn -> ->].
      apply (mk_bound _ _ _ _ _ (e0 :: S1) S2); cbn; try reflexivity; try assumption.
      change (flat_map _ S1) with (names S1). intros Hin. apply in_app_or in Hin as [Hin | Hin]; [| contradiction ].
      destruct (ent_name e0) as [y |] eqn:Ey; [| contradiction ].
      destruct Hin as [-> | []]. apply (proj2 (binds_b_iff _ _)) in Ey. congruence.
    + intros [[| e1 S1] S2 Heq Hx Hn -> ->]; cbn in Heq.
      * injection Heq as <- <-. apply (proj2 (binds_b_iff _ _)) in Hx. congruence.
      * injection Heq as <- ->. rewrite names_cons in Hn.
        rewrite (proj2 (IH _ _ _))
          by (apply (mk_bound _ _ _ _ _ S1 S2); auto; intros Hin; apply Hn, in_or_app; auto).
        reflexivity.
Qed.

Lemma bound_in : forall S x k e n, bound S x k e n -> In x (names S).
Proof.
  intros * [S1 S2 -> Hx _ _ _]. rewrite names_app, names_cons, Hx. apply in_or_app; right; left; reflexivity.
Qed.

Lemma lookup_none : forall x S, lookup x S = None <-> ~ In x (names S).
Proof.
  intros x; induction S as [| e S IH]; cbn [lookup]; [ cbn; tauto |].
  rewrite names_cons, in_app_iff.
  destruct (binds_b x e) eqn:E.
  - apply binds_b_iff in E; rewrite E. split; [ discriminate | intros H; exfalso; apply H; left; left; reflexivity ].
  - assert (Hn : ~ In x (match ent_name e with Some y => y :: nil | None => nil end)).
    { destruct (ent_name e) eqn:Ey; cbn; [| tauto ]. intros [<- | []]. apply (proj2 (binds_b_iff _ _)) in Ey. congruence. }
    case_eq (lookup x S); [ intros [[k e'] n] El | intros El ]; cbn; split; intros H; try discriminate.
    + exfalso; apply H; right. eapply bound_in, lookup_iff, El.
    + intros [? | Hin]; [ contradiction | apply IH in El; contradiction ].
    + reflexivity.
Qed.

Lemma den_to_term_iff : forall k n e M, den_to_term k n e = eok M <-> den_term k n e M.
Proof.
  intros * ; destruct e as [| | | | ? ? []]; cbn; split; intros H; inversion H; subst; constructor || reflexivity.
Qed.

Lemma den_to_mod_iff : forall k n e H, den_to_mod k n e = eok H <-> den_mod k n e H.
Proof. intros * ; destruct e; cbn; split; intros H'; inversion H'; subst; constructor || reflexivity. Qed.

Lemma check_fresh_ok : forall x F u, check_fresh x F = eok u <-> fresh x F.
Proof.
  intros x F []; unfold check_fresh, fresh; rewrite echeck_eok, negb_true_iff, <- not_true_iff_false, mem_b_iff.
  reflexivity.
Qed.

Lemma check_fresh_all_ok : forall xs F u, check_fresh_all xs F = eok u <-> Forall (fun d => fresh d F) xs.
Proof.
  induction xs as [| x xs IH]; intros F []; cbn [check_fresh_all].
  - split; constructor.
  - rewrite ebind_eok, Forall_cons_iff, <- (IH F tt), <- (check_fresh_ok x F tt).
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

Lemma check_params_ok : forall ps u, check_params ps = eok u <-> NoDup (map fst ps).
Proof.
  intros ps []; unfold check_params; rewrite <- first_dup_none.
  destruct (first_dup (map fst ps)); split; congruence.
Qed.

Lemma unit_in_b_iff : forall fq S, unit_in_b fq S = true <-> In (en_unit fq) S.
Proof.
  intros; unfold unit_in_b; rewrite existsb_exists; split.
  - intros ([] & Hin & Hb); try discriminate. apply path_beq_true in Hb; subst; assumption.
  - intros Hin; eexists; split; [ eassumption | apply path_beq_refl ].
Qed.

(** ** Open Targets *)

(** A projection chain is a module expression's spine of [me_mem]s. *)
Lemma selm_proj_chain : forall S ip o E,
    selm S (fold_left Cst.proj ip o) E <-> exists H, selm S o H /\ E = fold_left me_mem ip H.
Proof.
  intros S; induction ip as [| y ip IH]; intros o E; cbn [fold_left].
  - split; [ eauto | intros (H & HH & ->); assumption ].
  - rewrite IH; split.
    + intros (H' & Hs & ->); inversion Hs; subst; eauto.
    + intros (H & Hs & ->); exists (me_mem H y); split; [ constructor; assumption | reflexivity ].
Qed.

(** And the arguments of a module are its spine of [me_app]s. *)
Lemma selm_app_chain : forall S args o E,
    selm S (fold_left Cst.app args o) E <->
    exists H Ns, selm S o H /\ Forall2 (sel S) args Ns /\ E = mapps H Ns.
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
    | Some (k, e, n) => den_to_mod k n e
    | None => unit_mod x S
    end = eok H <-> selm S (Cst.var x) H.
Proof.
  intros; case_eq (lookup x S); [ intros [[k e] n] El | intros El ]; split.
  - intros Hd; econstructor; [ apply lookup_iff; eassumption | apply den_to_mod_iff; assumption ].
  - intros Hs; inversion Hs; subst.
    + match goal with Hb : bound _ _ _ _ _ |- _ => apply lookup_iff in Hb; rewrite Hb in El; inv_eok end.
      apply den_to_mod_iff; assumption.
    + exfalso; match goal with Hn : ~ In x (names S) |- _ => apply Hn end.
      eapply bound_in, lookup_iff, El.
  - unfold unit_mod; destruct (unit_in_b (x :: nil) S) eqn:Eu; [| discriminate ].
    intros [= <-]; apply selm_unit1; [ apply lookup_none; exact El | apply unit_in_b_iff; exact Eu ].
  - intros Hs; inversion Hs; subst.
    + match goal with Hb : bound _ _ _ _ _ |- _ => apply lookup_iff in Hb; congruence end.
    + unfold unit_mod; match goal with Hu : In (en_unit _) S |- _ => apply unit_in_b_iff in Hu; rewrite Hu end; reflexivity.
Qed.

Lemma ihead_iff : forall S fq ip H,
    elab_ihead S fq ip = eok H <-> exists o, ihead fq ip = Some o /\ selm S o H.
Proof.
  intros. destruct fq as [| f fq]; [ destruct ip as [| x ip] |]; cbn [elab_ihead ihead].
  - split; [ discriminate | intros (? & [=] & _) ].
  - rewrite ebind_eok; split.
    + intros (H' & Hx & [=<-]). eexists; split; [ reflexivity |].
      apply selm_proj_chain; exists H'; split; [ apply name_mod_iff; assumption | reflexivity ].
    + intros (o & [=<-] & Hs). apply selm_proj_chain in Hs as (H' & Hs & ->).
      exists H'; split; [ apply name_mod_iff; assumption | reflexivity ].
  - rewrite ebind_eok; split.
    + intros ([] & Hu & [=<-]); apply echeck_eok, unit_in_b_iff in Hu.
      eexists; split; [ reflexivity |]. apply selm_proj_chain; eexists; split; [ constructor; eassumption | reflexivity ].
    + intros (o & [=<-] & Hs). apply selm_proj_chain in Hs as (H' & Hs & ->). inversion Hs; subst.
      exists tt; split; [ apply echeck_eok, unit_in_b_iff; assumption | reflexivity ].
Qed.

(** ** Objects *)

(** The loop of [elab_mdef], stated on its own. *)
Fixpoint elab_body (S : list ent) (Φ : gmod) (cs : list Cst.cmd) : eres gmod :=
  match cs with
  | nil => eok Φ
  | Cst.c_def m x oA oM :: cs' =>
      let* A := elab S oA in
      let* M := elab S oM in
      elab_body (en_var x :: S) (gm_ext Φ x (ge_def (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M))) cs'
  | Cst.c_mod pv x ps md' :: cs' =>
      let* _ := check_params ps in
      let* tys := elab_params_with elab S ps in
      let* D := elab_mdef (pents ps ++ S) md' in
      elab_body (en_var x :: S) (gm_ext Φ x (ge_mod pv (gu_mk (ptele tys) D))) cs'
  | Cst.c_open fq ip args its :: cs' =>
      let* E := elab_target_with elab S fq ip args in
      elab_body (item_ents its ++ S) (gm_open Φ E its) cs'
  | Cst.c_axiom _ _ :: _ => eerr "axioms are not allowed in a local module"
  | Cst.c_import _ :: _ => eerr "import is not allowed in a local module; use open"
  | Cst.c_error e :: _ => eerr e
  | Cst.c_eval _ _ :: _ => eerr "eval is not allowed in a local module"
  | Cst.c_ind _ _ _ _ :: _ => eerr "an inductive type is not allowed in a local module"
  | Cst.c_mdef _ _ _ :: _ => eerr "a mutual definition is not allowed in a local module"
  | Cst.c_builtin _ _ :: _ => eerr "builtin is not allowed in a local module"
  | Cst.c_ind_alias _ x ps oE :: _ => eerr (local_alias_error "an inductive alias" x ps oE)
  | Cst.c_record_alias _ x ps oE :: _ => eerr (local_alias_error "a record alias" x ps oE)
  | Cst.c_record _ _ _ _ _ _ :: _ => eerr "a record type is not allowed in a local module"
  end.

Lemma elab_mdef_where : forall S cs, elab_mdef S (Cst.md_where cs) = let* Φ := elab_body S gm_nil cs in eok (md_body sm_open Φ).
Proof. reflexivity. Qed.

Definition Pterm (o : Cst.obj) : Prop := forall S M, elab S o = eok M <-> sel S o M.
Definition Pmod (o : Cst.obj) : Prop := forall S H, elab_mod S o = eok H <-> selm S o H.
Definition Pmdef (md : Cst.mdef) : Prop := forall S D, elab_mdef S md = eok D <-> sdef S md D.
Definition Pbody (cs : list Cst.cmd) : Prop := forall S Φ Φ', elab_body S Φ cs = eok Φ' <-> sbody S Φ cs Φ'.
Definition Pbcmd (c : Cst.cmd) : Prop := forall cs, Pbody cs -> Pbody (c :: cs).

(** Turn the elaborator's results into the specification's premises, and
    back, by the [iff]s at hand. *)
Ltac to_spec :=
  repeat match goal with
    | H : elab ?S ?o = eok _, IH : forall S M, elab S ?o = eok M <-> _ |- _ => apply IH in H
    | H : elab_mod ?S ?o = eok _, IH : forall S H, elab_mod S ?o = eok H <-> _ |- _ => apply IH in H
    | H : elab_mdef ?S ?o = eok _, IH : forall S D, elab_mdef S ?o = eok D <-> _ |- _ => apply IH in H
    | H : elab_body _ _ ?cs = eok _, IH : forall S Φ Φ', elab_body S Φ ?cs = eok Φ' <-> _ |- _ => apply IH in H
    | H : elab_params_with elab _ _ = eok _, IH : forall S tys, elab_params_with elab S ?ps = eok tys <-> _ |- _ =>
        apply IH in H
    | H : check_params _ = eok _ |- _ => apply check_params_ok in H
    | H : check_fresh _ _ = eok _ |- _ => apply check_fresh_ok in H
    end.

Ltac to_elab :=
  repeat match goal with
    | H : sel ?S ?o _, IH : forall S M, elab S ?o = eok M <-> _ |- _ => apply IH in H
    | H : selm ?S ?o _, IH : forall S H, elab_mod S ?o = eok H <-> _ |- _ => apply IH in H
    | H : sdef ?S ?o _, IH : forall S D, elab_mdef S ?o = eok D <-> _ |- _ => apply IH in H
    | H : sbody _ _ ?cs _, IH : forall S Φ Φ', elab_body S Φ ?cs = eok Φ' <-> _ |- _ => apply IH in H
    | H : sparams _ ?ps _, IH : forall S tys, elab_params_with elab S ?ps = eok tys <-> _ |- _ => apply IH in H
    | H : NoDup (map fst ?ps) |- _ => apply (check_params_ok ps tt) in H
    | H : fresh ?x ?F |- _ => apply (check_fresh_ok x F tt) in H
    end;
  repeat match goal with
    | H : ?e = eok _ |- context [?e] => rewrite H; cbn [ebind]
    end.

Ltac iff_case :=
  let Hg := fresh "Hg" in
  split; intros Hg;
  [ dest_eok; to_spec; econstructor; eassumption
  | inversion Hg; subst; to_elab; reflexivity ].

Lemma params_iff : forall ps, Forall (fun p => Pterm (snd p)) ps ->
    forall S tys, elab_params_with elab S ps = eok tys <-> sparams S ps tys.
Proof.
  induction 1 as [| [x oA] ps HA Hps IH]; intros S tys; cbn [elab_params_with].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - unfold Pterm in HA; cbn [snd] in HA. iff_case.
Qed.

Lemma args_iff : forall args, Forall Pterm args ->
    forall S Ns, elab_args_with elab S args = eok Ns <-> Forall2 (sel S) args Ns.
Proof.
  induction 1 as [| o args Ho Hargs IH]; intros S Ns; cbn [elab_args_with].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - unfold Pterm in Ho. rewrite ebind_eok; split.
    + intros (N & HN & H); apply ebind_eok in H as (Ns' & HNs & [=<-]).
      constructor; [ apply Ho | apply IH ]; assumption.
    + intros H; inversion H; subst. eexists; split; [ apply Ho; eassumption |].
      rewrite (proj2 (IH _ _)) by eassumption. reflexivity.
Qed.

(** The target of an open, as [elab_mod] would read it. *)
Lemma target_iff : forall S fq ip args E, Forall Pterm args ->
    elab_target_with elab S fq ip args = eok E <-> exists o, itarget fq ip args = Some o /\ selm S o E.
Proof.
  intros * Hargs. unfold elab_target_with, itarget. rewrite ebind_eok. split.
  - intros (H & Hh & HE); apply ebind_eok in HE as (Ns & HNs & [=<-]).
    apply ihead_iff in Hh as (o & Ho & Hs). rewrite Ho; cbn [option_map].
    eexists; split; [ reflexivity |]. apply selm_app_chain; exists H, Ns; repeat split; try assumption.
    apply (args_iff _ Hargs); assumption.
  - intros (o' & Ho' & Hs). destruct (ihead fq ip) as [o |] eqn:Ho; [| discriminate ]. injection Ho' as <-.
    apply selm_app_chain in Hs as (H & Ns & Hs & HNs & ->).
    exists H; split; [ apply ihead_iff; eauto |].
    rewrite (proj2 (args_iff _ Hargs _ _)) by eassumption. reflexivity.
Qed.

Lemma brs_iff : forall bs, Forall (fun b => Pterm (snd b)) bs ->
    forall S Bs, elab_brs_with elab S bs = eok Bs <-> sbrs S bs Bs.
Proof.
  induction 1 as [| [[c ys] oB] bs HB Hbs IH]; intros S Bs; cbn [elab_brs_with].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - unfold Pterm in HB; cbn [snd] in HB. split.
    + intros H; dest_eok. constructor; [ apply HB | apply IH ]; assumption.
    + intros H; inversion H; subst.
      rewrite (proj2 (HB _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (IH _ _)) by eassumption. reflexivity.
Qed.

(** The binders of a block, as [elab_binders_with] reads them. *)
Lemma binders_iff : forall xs, Forall (fun x => match snd x with Some A => Pterm A /\ Pmod A | None => True end) xs ->
    forall S pre oZ, elab_binders_with elab S pre xs = eok oZ <-> sbinders S pre xs oZ.
Proof.
  induction 1 as [| [x oo] xs Hx Hxs IH]; intros S pre oZ; cbn [elab_binders_with].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - cbn [snd] in Hx; destruct xs as [| y xs'], oo as [o |].
    + destruct Hx as [Ho _]; unfold Pterm in Ho; split.
      * intros H; dest_eok; constructor; apply Ho; assumption.
      * intros H; inversion H; subst; rewrite (proj2 (Ho _ _)) by eassumption; reflexivity.
    + split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
    + split; [ discriminate | intros H; inversion H ].
    + rewrite IH; split; [ intros H; constructor; exact H | intros H; inversion H; subst; assumption ].
Qed.

Lemma blocks_iff : forall bks,
    Forall (fun bk => Forall (fun x => match snd x with Some A => Pterm A /\ Pmod A | None => True end) (snd (fst (fst bk))) /\
                      (Pterm (snd (fst bk)) /\ Pmod (snd (fst bk))) /\
                      Forall (fun b => Pterm (snd b) /\ Pmod (snd b)) (snd bk)) bks ->
    forall S Bks, elab_blocks_with elab S bks = eok Bks <-> sblocks S bks Bks.
Proof.
  induction 1 as [| [[[k xs] oA] bs] bks [Hxs [[HA _] Hbs]] _ IH]; intros S Bks; cbn [elab_blocks_with].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - cbn [fst snd] in *.
    pose proof (binders_iff _ Hxs) as Hxi.
    assert (Hb : forall S Bs, elab_brs_with elab S bs = eok Bs <-> sbrs S bs Bs)
      by (apply brs_iff; eapply Forall_impl; [| exact Hbs ]; intros ? []; assumption).
    unfold Pterm in HA; split.
    + intros H; apply ebind_eok in H as (oZ & HZ & H); apply ebind_eok in H as (A & HA' & H).
      apply ebind_eok in H as (Bs & HBs & H); apply ebind_eok in H as (Bks' & HBks & H); inv_eok.
      constructor; [ apply Hxi; exact HZ | apply HA; exact HA' | apply Hb; exact HBs | apply IH; exact HBks ].
    + intros H; inversion H; subst.
      rewrite (proj2 (Hxi _ _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (HA _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (Hb _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (IH _ _)) by eassumption; reflexivity.
Qed.

(** The fields of a record value, as [elab_tfields_with] reads them. *)
Lemma tfields_iff : forall fs, Forall (fun f => Pterm (snd f)) fs ->
    forall S Ms, elab_tfields_with elab S fs = eok Ms <-> stfields S fs Ms.
Proof.
  induction 1 as [| [y oM] fs HM Hfs IH]; intros S Ms; cbn [elab_tfields_with].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - unfold Pterm in HM; cbn [snd] in HM. split.
    + intros H; dest_eok. constructor; [ apply HM | apply IH ]; assumption.
    + intros H; inversion H; subst.
      rewrite (proj2 (HM _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (IH _ _)) by eassumption. reflexivity.
Qed.

Lemma Pterm_params : forall ps : list (string * Cst.obj),
    Forall (fun p => Pterm (snd p) /\ Pmod (snd p)) ps -> Forall (fun p => Pterm (snd p)) ps.
Proof. intros ps; apply Forall_impl; intros ? []; assumption. Qed.

(** A local module, as [elab] and [elab_body] build it. *)
Lemma sunit_iff : forall S ps md U,
    Forall (fun p => Pterm (snd p)) ps -> Pmdef md ->
    (let* _ := check_params ps in
     let* tys := elab_params_with elab S ps in
     let* D := elab_mdef (pents ps ++ S) md in
     eok (gu_mk (ptele tys) D)) = eok U <-> sunit S ps md U.
Proof.
  intros * Hps Hmd. pose proof (params_iff _ Hps) as IHps. unfold Pmdef in Hmd. iff_case.
Qed.

(** The hypothesis [Cst.cst_ind] gives about the blocks of an eliminator,
    in the form [blocks_iff] takes. *)
Lemma blocks_all_Forall : forall (P : Cst.obj -> Prop)
    (bks : list (bool * list (string * option Cst.obj) * Cst.obj * list (string * list string * Cst.obj))),
    list_all _ (prod_all _ (prod_all _ (prod_all bool (fun _ => unit) _
                  (list_all _ (prod_all string (fun _ => unit) (option Cst.obj) (option_all Cst.obj P))))
                  Cst.obj P) _ (list_all _ (prod_all (string * list string)%type (fun _ => unit) Cst.obj P))) bks ->
    Forall (fun bk => Forall (fun x => match snd x with Some A => P A | None => True end) (snd (fst (fst bk))) /\
                      P (snd (fst bk)) /\ Forall (fun b => P (snd b)) (snd bk)) bks.
Proof.
  intros P bks; apply list_all_Forall_impl.
  intros bk Hbk; destruct Hbk as [kxA HkxA bs Hbs]; destruct HkxA as [kx Hkx A HA]; destruct Hkx as [k _ xs Hxs].
  cbn [fst snd]; split; [| split; [ exact HA | exact (list_all_snd _ _ _ _ Hbs) ] ].
  refine (list_all_Forall_impl _ _ _ xs _ Hxs).
  intros x Hx; destruct Hx as [y _ o Ho]; exact (option_all_match _ _ _ Ho).
Qed.

Lemma objects_iff :
  (forall o, Pterm o /\ Pmod o) /\
  (forall d, forall ob, Pterm ob -> forall S M,
      elab S (Cst.letb d ob) = eok M <-> sel S (Cst.letb d ob) M) /\
  (forall md, Pmdef md) /\ (forall c, Pbcmd c).
Proof.
  apply Cst.cst_ind; unfold Pterm, Pmod, Pmdef, Pbcmd, Pbody.
  all: try (intros; repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
            split; intros S M; cbn [elab elab_mod];
            solve [ iff_case | let Hg := fresh "Hg" in split; [ discriminate | intros Hg; inversion Hg ] ]).
  - (* var *)
    intros x; split; [| intros S M; apply name_mod_iff ].
    intros S M; cbn [elab];
      (case_eq (lookup x S); [ intros [[k e] n] El | intros El ]; split;
       [ intros H | intros Hs; inversion Hs; subst | discriminate | intros Hs; inversion Hs; subst ]).
    + econstructor; [ apply lookup_iff; eassumption | apply den_to_term_iff; assumption ].
    + match goal with Hb : bound _ _ _ _ _ |- _ => apply lookup_iff in Hb; rewrite Hb in El; inv_eok end.
      apply den_to_term_iff; assumption.
    + match goal with Hb : bound _ _ _ _ _ |- _ => apply lookup_iff in Hb; congruence end.
  - (* glob *)
    intros fq; split; intros S M; cbn [elab elab_mod]; split; intros H.
    + discriminate.
    + inversion H.
    + dest_eok; constructor; apply unit_in_b_iff; assumption.
    + inversion H; subst. rewrite (proj2 (unit_in_b_iff _ _)) by assumption. reflexivity.
  - (* proj: a member of a path's module, or of a term's, let-bound *)
    intros o [IHt IHm] x; split; intros S M; cbn [elab elab_mod].
    + destruct (obj_path o) eqn:Ep; split; intros Hg.
      * apply ebind_eok in Hg as (H & HH & Hg); inv_eok; constructor; [ exact Ep | apply IHm; exact HH ].
      * inversion Hg; subst; [ rewrite (proj2 (IHm _ _)) by eassumption; reflexivity | congruence ].
      * apply ebind_eok in Hg as (M' & HM & Hg); inv_eok; apply sel_proj_let; [ exact Ep | apply IHt; exact HM ].
      * inversion Hg; subst; [ congruence | rewrite (proj2 (IHt _ _)) by eassumption; reflexivity ].
    + split; intros Hg.
      * apply ebind_eok in Hg as (H & HH & Hg); inv_eok; constructor; apply IHm; exact HH.
      * inversion Hg; subst; rewrite (proj2 (IHm _ _)) by eassumption; reflexivity.
  - (* letb *)
    intros d IHd o [IH _]; split; [ apply IHd, IH |].
    intros S M; destruct d; cbn [elab_mod]; split; intros H; try discriminate; inversion H.
  - (* elim *)
    intros om [IHm _] bks Hbks.
    pose proof (blocks_iff _ (blocks_all_Forall _ _ Hbks)) as Hb.
    split; intros S M; cbn [elab elab_mod].
    + split; intros Hg.
      * apply ebind_eok in Hg as (M' & HM & Hg); apply ebind_eok in Hg as (Bks & HB & Hg).
        destruct (elim_at _) as [m |] eqn:Ea; [ inv_eok | discriminate ].
        econstructor; [ apply IHm; exact HM | apply Hb; exact HB | exact Ea ].
      * inversion Hg; subst.
        rewrite (proj2 (IHm _ _)) by eassumption; cbn [ebind].
        rewrite (proj2 (Hb _ _)) by eassumption; cbn [ebind].
        match goal with Ea : elim_at _ = Some _ |- _ => rewrite Ea end; reflexivity.
    + split; [ discriminate | intros Hg; inversion Hg ].
  - (* tuple *)
    intros oT [IHT _] fs Hfs; apply list_all_snd in Hfs.
    assert (Hf : forall S Ms, elab_tfields_with elab S fs = eok Ms <-> stfields S fs Ms)
      by (apply tfields_iff; eapply Forall_impl; [| exact Hfs ]; intros ? []; assumption).
    split; intros S M; cbn [elab elab_mod].
    + split; intros Hg.
      * apply ebind_eok in Hg as (T & HT & Hg); apply ebind_eok in Hg as (Ms & HMs & Hg); inv_eok.
        constructor; [ apply IHT; exact HT | apply Hf; exact HMs ].
      * inversion Hg; subst.
        rewrite (proj2 (IHT _ _)) by eassumption; cbn [ebind].
        rewrite (proj2 (Hf _ _)) by eassumption; reflexivity.
    + split; [ discriminate | intros Hg; inversion Hg ].
  - (* d_def *)
    intros x [o1 |] HA o2 [IH2 _] ob IHb S M; [ apply option_all_match in HA; destruct HA as [IH1 _] |]; cbn [elab]; iff_case.
  - (* d_mod *)
    intros x ps Hps md Hmd ob IHb S M. apply list_all_snd, Pterm_params in Hps.
    pose proof (sunit_iff S ps md) as Hu. cbn [elab]; split; intros Hg.
    + dest_eok. econstructor; [ apply Hu; [ assumption | exact Hmd |] | apply IHb; eassumption ].
      to_elab; reflexivity.
    + inversion Hg; subst. match goal with Hs : sunit _ _ _ _ |- _ => apply Hu in Hs; [| assumption | exact Hmd ] end.
      dest_eok. to_elab. reflexivity.
  - (* md_where *)
    intros cs Hcs S D. apply list_all_Forall in Hcs. rewrite elab_mdef_where, ebind_eok.
    assert (Hb : forall S Φ Φ', elab_body S Φ cs = eok Φ' <-> sbody S Φ cs Φ').
    { induction Hcs as [| c cs Hc Hcs IH]; intros S' Φ Φ'.
      - cbn; split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
      - apply Hc; intros; apply IH. }
    split.
    + intros (Φ & HΦ & H); inv_eok. constructor; apply Hb; assumption.
    + intros H; inversion H; subst. eexists; split; [ apply Hb; eassumption | reflexivity ].
  - (* md_alias *)
    intros o [_ IHm] S D; cbn [elab_mdef]. iff_case.
  - (* c_mod *)
    intros pv x ps Hps md Hmd cs Hcs S Φ Φ'. apply list_all_snd, Pterm_params in Hps.
    pose proof (sunit_iff S ps md) as Hu. cbn [elab_body].
    split; intros Hg.
    + dest_eok. econstructor; [ apply Hu; [ assumption | exact Hmd |] | apply Hcs; eassumption ].
      to_elab; reflexivity.
    + inversion Hg; subst. match goal with Hs : sunit _ _ _ _ |- _ => apply Hu in Hs; [| assumption | exact Hmd ] end.
      dest_eok. to_elab. reflexivity.
  - (* c_def *)
    intros m x o1 [IH1 _] o2 [IH2 _] cs Hcs S Φ Φ'; cbn [elab_body].
    split; intros Hg.
    + dest_eok. to_spec. econstructor; eassumption.
    + inversion Hg; subst. to_elab. reflexivity.
  - (* c_axiom *)
    intros x o _ cs Hcs S Φ Φ'; cbn [elab_body]. split; [ discriminate | intros H; inversion H ].
  - (* c_import *)
    intros fq cs Hcs S Φ Φ'; cbn [elab_body]. split; [ discriminate | intros H; inversion H ].
  - (* c_open *)
    intros fq ip args Hargs its cs Hcs S Φ Φ'; apply list_all_Forall in Hargs; cbn [elab_body].
    assert (Ha : Forall Pterm args) by (eapply Forall_impl; [| exact Hargs ]; intros ? []; assumption).
    split; intros Hg.
    + apply ebind_eok in Hg as (E & HE & Hg). apply (target_iff _ _ _ _ _ Ha) in HE as (o & Ho & Hs).
      econstructor; [ eassumption | eassumption | apply Hcs; eassumption ].
    + inversion Hg; subst.
      rewrite (proj2 (target_iff _ _ _ _ _ Ha)) by eauto; cbn [ebind].
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

Lemma elab_iff : forall S o M, elab S o = eok M <-> sel S o M.
Proof. intros; apply (proj1 (proj1 objects_iff o)). Qed.

Lemma elab_mod_iff : forall S o H, elab_mod S o = eok H <-> selm S o H.
Proof. intros; apply (proj2 (proj1 objects_iff o)). Qed.

Lemma elab_params_iff : forall S ps tys, elab_params S ps = eok tys <-> sparams S ps tys.
Proof.
  intros; apply params_iff, Forall_forall; intros ? _ ? ?; apply elab_iff.
Qed.

Lemma elab_target_iff : forall S fq ip args E,
    elab_target_with elab S fq ip args = eok E <-> exists o, itarget fq ip args = Some o /\ selm S o E.
Proof.
  intros; apply target_iff, Forall_forall; intros ? _ ? ?; apply elab_iff.
Qed.

Lemma elab_args_iff : forall S os Ns, elab_args_with elab S os = eok Ns <-> Forall2 (sel S) os Ns.
Proof. intros; apply args_iff, Forall_forall; intros ? _ ? ?; apply elab_iff. Qed.

Lemma elab_brs_iff : forall S bs Bs, elab_brs_with elab S bs = eok Bs <-> sbrs S bs Bs.
Proof. intros; apply brs_iff, Forall_forall; intros ? _ ? ?; apply elab_iff. Qed.

Lemma elab_rargs_iff : forall args S args', elab_rargs S args = eok args' <-> srargs S args args'.
Proof.
  induction args as [| [y oA] args IH]; intros S args'; cbn [elab_rargs].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - split.
    + intros H; apply ebind_eok in H as (A & HA & H); apply ebind_eok in H as (r & Hr & H); inv_eok.
      constructor; [ apply elab_iff; exact HA | apply IH; exact Hr ].
    + intros H; inversion H; subst.
      rewrite (proj2 (elab_iff _ _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (IH _ _)) by eassumption. reflexivity.
Qed.

Lemma elab_rcons_iff : forall S cs cs', elab_rcons S cs = eok cs' <-> srcons S cs cs'.
Proof.
  intros S; induction cs as [| [c args] cs IH]; intros cs'; cbn [elab_rcons].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - split.
    + intros H; apply ebind_eok in H as (a & Ha & H); apply ebind_eok in H as (cs'' & Hcs & H); inv_eok.
      constructor; [ apply elab_rargs_iff; exact Ha | apply IH; exact Hcs ].
    + intros H; inversion H; subst.
      rewrite (proj2 (elab_rargs_iff _ _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (IH _)) by eassumption. reflexivity.
Qed.

Lemma elab_members_iff : forall ms S ups xs rms, elab_members S ups xs ms = eok rms <-> smembers S ups xs ms rms.
Proof.
  induction ms as [| [[x oT] cs] ms IH]; intros S ups xs rms; cbn [elab_members].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - destruct (split_pis oT) as [nps oS] eqn:Es; split.
    + intros H; apply ebind_eok in H as ([] & Hp & H); apply ebind_eok in H as (ntys & Hn & H).
      apply ebind_eok in H as (A & HA & H); apply ebind_eok in H as (cs' & Hc & H).
      apply ebind_eok in H as (rms' & Hr & H); inv_eok.
      econstructor; [ exact Es | apply (check_params_ok _ tt); exact Hp | apply elab_params_iff; exact Hn
                    | apply elab_iff; exact HA | apply elab_rcons_iff; exact Hc | apply IH; exact Hr ].
    + intros H; inversion H; subst.
      match goal with H : split_pis oT = _ |- _ => rewrite Es in H; injection H as <- <- end.
      rewrite (proj2 (check_params_ok _ tt)) by assumption; cbn [ebind].
      rewrite (proj2 (elab_params_iff _ _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (elab_iff _ _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (elab_rcons_iff _ _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (IH _ _ _ _)) by eassumption; reflexivity.
Qed.

Lemma elab_funs_iff : forall fs S rfs, elab_funs S fs = eok rfs <-> sfuns S fs rfs.
Proof.
  induction fs as [| [[[f ps] oA] bs] fs IH]; intros S rfs; cbn [elab_funs].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - split.
    + destruct (rev ps) as [| [z oZ] rys] eqn:Er; [ discriminate |].
      assert (Eps : ps = rev rys ++ (z, oZ) :: nil) by (rewrite <- (rev_involutive ps), Er; reflexivity).
      intros H; apply ebind_eok in H as ([] & Hp & H); apply ebind_eok in H as (ytys & Hy & H).
      apply ebind_eok in H as (Z & HZ & H); apply ebind_eok in H as (A & HA & H).
      apply ebind_eok in H as (Bs & HBs & H); apply ebind_eok in H as (rfs' & Hr & H); inv_eok.
      econstructor; [ apply (check_params_ok _ tt); exact Hp | apply elab_params_iff; exact Hy
                    | apply elab_iff; exact HZ | apply elab_iff; exact HA | apply elab_brs_iff; exact HBs | apply IH; exact Hr ].
    + intros H; inversion H; subst.
      rewrite rev_unit, rev_involutive; cbn [ebind].
      rewrite (proj2 (check_params_ok _ tt)) by assumption; cbn [ebind].
      rewrite (proj2 (elab_params_iff _ _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (elab_iff _ _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (elab_iff _ _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (elab_brs_iff _ _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (IH _ _)) by eassumption; reflexivity.
Qed.

Lemma check_distinct_ok : forall w xs u, check_distinct w xs = eok u <-> NoDup xs.
Proof.
  intros w xs []; unfold check_distinct; rewrite <- first_dup_none.
  destruct (first_dup xs); split; congruence.
Qed.

Lemma check_no_field_ok : forall x fs cs u,
    check_no_field x fs cs = eok u <-> Forall (fun y => ~ In y fs) (flat_map cmd_decls cs).
Proof.
  intros x fs cs []; unfold check_no_field; rewrite Forall_forall.
  destruct (find (fun y => mem_b y fs) (flat_map cmd_decls cs)) as [f |] eqn:E; split; try discriminate.
  - intros H; apply find_some in E as [Hin Hm]; apply mem_b_iff in Hm; exfalso; exact (H _ Hin Hm).
  - intros _ y Hin Hy; apply (find_none _ _ E) in Hin; apply (proj2 (mem_b_iff _ _)) in Hy; congruence.
  - intros _; reflexivity.
Qed.

(** ** Commands *)

Section Commands.
  Variable fp : path.

  Definition Pcmd (c : Cst.cmd) : Prop :=
    forall ch O F F' cs', elab_cmd fp ch O F c = eok (F', cs') <-> scmd fp ch O F c F' cs'.
  Definition Pcmds (cs : list Cst.cmd) : Prop :=
    forall ch O F ccs, elab_cmds fp ch O F cs = eok ccs <-> scmds fp ch O F cs ccs.

  Lemma cmds_iff : forall cs, Forall Pcmd cs -> Pcmds cs.
  Proof.
    induction 1 as [| c cs Hc Hcs IH]; intros ch O F ccs; cbn.
    - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
    - split.
      + intros H; dest_eok. destruct x as [F' c']; cbn [fst snd] in *.
        econstructor; [ apply Hc | apply IH ]; eassumption.
      + intros H; inversion H; subst.
        rewrite (proj2 (Hc _ _ _ _ _)) by eassumption; cbn [ebind fst snd].
        change (elab_cmds_with (elab_cmd fp) ch O F' cs) with (elab_cmds fp ch O F' cs).
        rewrite (proj2 (IH _ _ _ _)) by eassumption. reflexivity.
  Qed.

  Ltac cmd_spec :=
    repeat match goal with
      | H : elab _ _ = eok _ |- _ => apply elab_iff in H
      | H : elab_mod _ _ = eok _ |- _ => apply elab_mod_iff in H
      | H : elab_params _ _ = eok _ |- _ => apply elab_params_iff in H
      | H : elab_cmds_with (elab_cmd fp) _ _ _ ?cs = eok _, IH : Pcmds ?cs |- _ => apply IH in H
      | H : check_params _ = eok _ |- _ => apply check_params_ok in H
      | H : check_fresh _ _ = eok _ |- _ => apply check_fresh_ok in H
      end.

  Ltac cmd_elab :=
    repeat match goal with
      | H : sel _ _ _ |- _ => apply elab_iff in H
      | H : selm _ _ _ |- _ => apply elab_mod_iff in H
      | H : sparams _ _ _ |- _ => apply elab_params_iff in H
      | H : scmds fp _ _ _ ?cs _, IH : Pcmds ?cs |- _ => apply IH in H
      | H : NoDup (map fst ?ps) |- _ => apply (check_params_ok ps tt) in H
      | H : fresh ?x ?F |- _ => apply (check_fresh_ok x F tt) in H
      end;
    unfold elab_cmds in *;
    repeat match goal with
      | H : ?e = eok _ |- context [?e] => rewrite H; cbn [ebind fst snd]
      end.

  Lemma commands_iff : forall c, Pcmd c.
  Proof.
    apply (fun H : (forall o : Cst.obj, True) /\ (forall d : Cst.decl, True) /\
                   (forall md, forall body, md = Cst.md_where body -> Pcmds body) /\ (forall c, Pcmd c) =>
             proj2 (proj2 (proj2 H))).
    apply Cst.cst_ind; try easy.
    - intros cs Hcs body [=<-]. apply cmds_iff, list_all_Forall, Hcs.
    - intros pv x ps _ [body | oE] Hmd ch O F F' c'; cbn [elab_cmd]; [ specialize (Hmd body eq_refl) |].
      all: split; intros Hg; [ dest_eok; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - intros m x o1 _ o2 _ ch O F F' c'; cbn [elab_cmd].
      split; intros Hg; [ dest_eok; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - intros x o _ ch O F F' c'; cbn [elab_cmd].
      split; intros Hg; [ dest_eok; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - intros fq ch O F F' c'; cbn [elab_cmd].
      split; [ intros H; inv_eok; constructor | intros H; inversion H; subst; reflexivity ].
    - intros fq ip args _ its ch O F F' c'; cbn [elab_cmd]. split.
      + intros H; apply ebind_eok in H as (E & HE & H); apply ebind_eok in H as ([] & Hf & H); inv_eok.
        apply elab_target_iff in HE as (o & Ho & Hs).
        econstructor; [ eassumption | eassumption | apply (check_fresh_all_ok _ _ tt); assumption ].
      + intros H; inversion H; subst.
        rewrite (proj2 (elab_target_iff _ _ _ _ _)) by eauto; cbn [ebind].
        rewrite (proj2 (check_fresh_all_ok _ _ tt)) by assumption. reflexivity.
    - intros o _ [oA |] _ ch O F F' c'; cbn [elab_cmd].
      all: split; intros Hg; [ dest_eok; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - intros pv wr ups _ ms _ ch O F F' c'; cbn [elab_cmd]; split.
      + intros Hg; apply ebind_eok in Hg as ([] & Hd & Hg); apply ebind_eok in Hg as ([] & Hf & Hg).
        apply ebind_eok in Hg as (tys & Ht & Hg); apply ebind_eok in Hg as (rms & Hm & Hg); inv_eok.
        econstructor; [ exact (proj1 (check_distinct_ok _ _ tt) Hd) | apply (check_fresh_all_ok _ _ tt); exact Hf
                      | apply elab_params_iff; exact Ht | apply elab_members_iff; exact Hm ].
      + intros Hg; inversion Hg; subst.
        rewrite (proj2 (check_distinct_ok "a group" _ tt)) by assumption; cbn [ebind].
        rewrite (proj2 (check_fresh_all_ok _ _ tt)) by assumption; cbn [ebind].
        rewrite (proj2 (elab_params_iff _ _ _)) by eassumption; cbn [ebind].
        rewrite (proj2 (elab_members_iff _ _ _ _ _)) by eassumption; reflexivity.
    - intros m ps _ fs _ ch O F F' c'; cbn [elab_cmd]; split.
      + intros Hg; apply ebind_eok in Hg as ([] & Hp & Hg); apply ebind_eok in Hg as ([] & Hd & Hg).
        apply ebind_eok in Hg as ([] & Hf & Hg); apply ebind_eok in Hg as (tys & Ht & Hg).
        apply ebind_eok in Hg as (rfs & Hr & Hg); inv_eok.
        econstructor; [ apply (check_params_ok _ tt); exact Hp | exact (proj1 (check_distinct_ok _ _ tt) Hd)
                      | apply (check_fresh_all_ok _ _ tt); exact Hf | apply elab_params_iff; exact Ht
                      | apply elab_funs_iff; exact Hr ].
      + intros Hg; inversion Hg; subst.
        rewrite (proj2 (check_params_ok _ tt)) by assumption; cbn [ebind].
        rewrite (proj2 (check_distinct_ok "a mutual definition" _ tt)) by assumption; cbn [ebind].
        rewrite (proj2 (check_fresh_all_ok _ _ tt)) by assumption; cbn [ebind].
        rewrite (proj2 (elab_params_iff _ _ _)) by eassumption; cbn [ebind].
        rewrite (proj2 (elab_funs_iff _ _ _)) by eassumption; reflexivity.
    - intros k o _ ch O F F' c'; cbn [elab_cmd]. split.
      + intros Hg; apply ebind_eok in Hg as (H & HH & Hg); inv_eok.
        econstructor; apply elab_mod_iff; exact HH.
      + intros Hg; inversion Hg; subst.
        rewrite (proj2 (elab_mod_iff _ _ _)) by eassumption; reflexivity.
    - intros pv x ps _ o _ ch O F F' c'; cbn [elab_cmd].
      split; intros Hg; [ dest_eok; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - (* a record alias, as an inductive alias *)
      intros pv x ps _ o _ ch O F F' c'; cbn [elab_cmd].
      split; intros Hg; [ dest_eok; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - (* a record type: its with-area by the commands' induction *)
      intros pv x ps _ o _ fs _ cs Hcs ch O F F' c'; apply list_all_Forall, cmds_iff in Hcs; cbn [elab_cmd]; split.
      + intros Hg; apply ebind_eok in Hg as ([] & Hf & Hg); apply ebind_eok in Hg as ([] & Hp & Hg).
        apply ebind_eok in Hg as (tys & Ht & Hg); apply ebind_eok in Hg as (Srt & HS & Hg).
        apply ebind_eok in Hg as (fs' & Hr & Hg); apply ebind_eok in Hg as ([] & Hn & Hg).
        apply ebind_eok in Hg as (bcs & Hb & Hg); dest_eok.
        econstructor; [ apply (check_fresh_ok _ _ tt); exact Hf | apply (check_params_ok _ tt); exact Hp
                      | apply elab_params_iff; exact Ht | apply elab_iff; exact HS | apply elab_rargs_iff; exact Hr
                      | apply (check_no_field_ok x _ _ tt); exact Hn | apply Hcs; exact Hb ].
      + intros Hg; inversion Hg; subst.
        rewrite (proj2 (check_fresh_ok _ _ tt)) by assumption; cbn [ebind].
        rewrite (proj2 (check_params_ok _ tt)) by assumption; cbn [ebind].
        rewrite (proj2 (elab_params_iff _ _ _)) by eassumption; cbn [ebind].
        rewrite (proj2 (elab_iff _ _ _)) by eassumption; cbn [ebind].
        rewrite (proj2 (elab_rargs_iff _ _ _)) by eassumption; cbn [ebind].
        rewrite (proj2 (check_no_field_ok _ _ _ tt)) by assumption; cbn [ebind].
        change (elab_cmds_with (elab_cmd fp)) with (elab_cmds fp).
        rewrite (proj2 (Hcs _ _ _ _)) by eassumption; reflexivity.
  Qed.

  Corollary elab_cmds_iff : forall ch O F cs ccs, elab_cmds fp ch O F cs = eok ccs <-> scmds fp ch O F cs ccs.
  Proof. intros; apply cmds_iff, Forall_forall; intros; apply commands_iff. Qed.
End Commands.

(** ** Units *)

Lemma lead_iff : forall cs L L' lds, elab_lead L cs = eok (L', lds) <-> slead L cs L' lds.
Proof.
  induction cs as [| c cs IH]; intros L L' lds; cbn [elab_lead].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - destruct c; try (split; [ discriminate | intros H; inversion H ]); rewrite ebind_eok; split.
    + intros ([L1 l1] & H & E); cbn [fst snd] in E; inv_eok. constructor; apply IH; exact H.
    + intros H; inversion H; subst. exists (L', lds0); split; [ apply IH; assumption | reflexivity ].
    + intros (E & HE & H). apply elab_target_iff in HE as (o & Ho & Hs).
      econstructor; [ eassumption | eassumption | apply IH; exact H ].
    + intros H; inversion H; subst. exists E; split; [ apply elab_target_iff; eauto | apply IH; assumption ].
Qed.

Theorem elaborate_core_iff : forall prg u, elaborate_core prg = eok u <-> elab_spec prg u.
Proof.
  intros [leads [[fp ps] cs]] u. unfold elaborate_core. split.
  - intros H; apply ebind_eok in H as ([L lds] & Hl & H); apply ebind_eok in H as ([] & Hp & H).
    apply ebind_eok in H as (tys & Ht & H); apply ebind_eok in H as (ccs & Hc & H); inv_eok.
    apply lead_iff in Hl. apply check_params_ok in Hp. apply elab_params_iff in Ht. apply elab_cmds_iff in Hc.
    econstructor; eassumption.
  - intros Hs; inversion Hs; subst.
    rewrite (proj2 (lead_iff _ _ _ _)) by eassumption; cbn [ebind].
    rewrite (proj2 (check_params_ok _ tt)) by assumption; cbn [ebind].
    rewrite (proj2 (elab_params_iff _ _ _)) by eassumption; cbn [ebind].
    rewrite (proj2 (elab_cmds_iff _ _ _ _ _ _)) by eassumption. reflexivity.
Qed.

(** Soundness: whatever the elaborator produces, the specification relates. *)
Corollary elaborate_core_sound : forall prg u, elaborate_core prg = eok u -> elab_spec prg u.
Proof. intros; apply elaborate_core_iff; assumption. Qed.

(** Completeness: whatever the specification relates, the elaborator produces. *)
Corollary elaborate_core_complete : forall prg u, elab_spec prg u -> elaborate_core prg = eok u.
Proof. intros; apply elaborate_core_iff; assumption. Qed.

(** The specification is functional. *)
Corollary elab_spec_functional : forall prg u1 u2, elab_spec prg u1 -> elab_spec prg u2 -> u1 = u2.
Proof.
  intros * H1 H2. apply elaborate_core_complete in H1, H2. rewrite H1 in H2. inversion H2; reflexivity.
Qed.

(** The elaborator fails exactly on the programs the specification relates
    to nothing. *)
Corollary elaborate_core_fails : forall prg,
    (exists e, elaborate_core prg = eerr e) <-> forall u, ~ elab_spec prg u.
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
