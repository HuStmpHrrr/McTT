From Stdlib Require Import Bool Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Members GlobalCtx Command.
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
  - split; [ discriminate | intros ([] & ? & [=] & _) ].
  - destruct (binds_b x e0) eqn:E; split.
    + intros [=<- <- <-]. exists nil, S. apply binds_b_iff in E. cbn; tauto.
    + intros ([| e1 S1] & S2 & Heq & Hx & Hn & -> & ->); cbn in Heq.
      * injection Heq as <- <-; reflexivity.
      * injection Heq as <- ->. exfalso; apply Hn. rewrite names_cons. apply binds_b_iff in E. rewrite E. left; reflexivity.
    + case_eq (lookup x S); [ intros [[k' e'] n'] El | intros _ ]; cbn; [| discriminate ].
      intros [=<- <- <-]. apply IH in El as (S1 & S2 & -> & Hx & Hn & -> & ->).
      exists (e0 :: S1), S2; cbn; repeat split; try assumption.
      change (flat_map _ S1) with (names S1). intros Hin. apply in_app_or in Hin as [Hin | Hin]; [| contradiction ].
      destruct (ent_name e0) as [y |] eqn:Ey; [| contradiction ].
      destruct Hin as [-> | []]. apply (proj2 (binds_b_iff _ _)) in Ey. congruence.
    + intros ([| e1 S1] & S2 & Heq & Hx & Hn & -> & ->); cbn in Heq.
      * injection Heq as <- <-. apply (proj2 (binds_b_iff _ _)) in Hx. congruence.
      * injection Heq as <- ->. rewrite names_cons in Hn.
        rewrite (proj2 (IH _ _ _)) by (exists S1, S2; repeat split; auto; intros Hin; apply Hn, in_or_app; auto).
        reflexivity.
Qed.

Lemma bound_in : forall S x k e n, bound S x k e n -> In x (names S).
Proof.
  intros * (S1 & S2 & -> & Hx & _). rewrite names_app, names_cons, Hx. apply in_or_app; right; left; reflexivity.
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
Proof. intros * ; destruct e; cbn; split; intros H; inversion H; subst; constructor || reflexivity. Qed.

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

(** ** Import Targets *)

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
    | None => eerr ("unbound name " ++ x)
    end = eok H <-> selm S (Cst.var x) H.
Proof.
  intros; case_eq (lookup x S); [ intros [[k e] n] El | intros El ]; split.
  - intros Hd; econstructor; [ apply lookup_iff; eassumption | apply den_to_mod_iff; assumption ].
  - intros Hs; inversion Hs; subst.
    match goal with Hb : bound _ _ _ _ _ |- _ => apply lookup_iff in Hb; rewrite Hb in El; inv_eok end.
    apply den_to_mod_iff; assumption.
  - discriminate.
  - intros Hs; inversion Hs; subst.
    match goal with Hb : bound _ _ _ _ _ |- _ => apply lookup_iff in Hb; congruence end.
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
  | Cst.c_import fq ip args spec :: cs' =>
      let* E := elab_target_with elab S fq ip args in
      elab_body (item_ents (ispec_items spec) ++ S) (gm_import Φ E (ispec_items spec)) cs'
  | Cst.c_eval _ _ :: _ => eerr "eval is not allowed in a local module"
  end.

Lemma elab_mdef_where : forall S cs, elab_mdef S (Cst.md_where cs) = let* Φ := elab_body S gm_nil cs in eok (md_body Φ).
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

(** The target of an import, as [elab_mod] would read it. *)
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

Lemma objects_iff :
  (forall o, Pterm o /\ Pmod o) /\
  (forall d, forall ob, Pterm ob -> forall S M,
      elab S (Cst.letb d ob) = eok M <-> sel S (Cst.letb d ob) M) /\
  (forall md, Pmdef md) /\ (forall c, Pbcmd c).
Proof.
  apply Cst.cst_mut_ind; unfold Pterm, Pmod, Pmdef, Pbcmd, Pbody.
  all: try (intros; repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
            split; intros S M; cbn [elab elab_mod];
            solve [ iff_case | let Hg := fresh "Hg" in split; [ discriminate | intros Hg; inversion Hg ] ]).
  - (* var *)
    intros x; split; intros S M; cbn [elab elab_mod];
      (case_eq (lookup x S); [ intros [[k e] n] El | intros El ]; split;
       [ intros H | intros Hs; inversion Hs; subst | discriminate | intros Hs; inversion Hs; subst ]).
    + econstructor; [ apply lookup_iff; eassumption | apply den_to_term_iff; assumption ].
    + match goal with Hb : bound _ _ _ _ _ |- _ => apply lookup_iff in Hb; rewrite Hb in El; inv_eok end.
      apply den_to_term_iff; assumption.
    + match goal with Hb : bound _ _ _ _ _ |- _ => apply lookup_iff in Hb; congruence end.
    + econstructor; [ apply lookup_iff; eassumption | apply den_to_mod_iff; assumption ].
    + match goal with Hb : bound _ _ _ _ _ |- _ => apply lookup_iff in Hb; rewrite Hb in El; inv_eok end.
      apply den_to_mod_iff; assumption.
    + match goal with Hb : bound _ _ _ _ _ |- _ => apply lookup_iff in Hb; congruence end.
  - (* glob *)
    intros fq; split; intros S M; cbn [elab elab_mod]; split; intros H.
    + discriminate.
    + inversion H.
    + dest_eok; constructor; apply unit_in_b_iff; assumption.
    + inversion H; subst. rewrite (proj2 (unit_in_b_iff _ _)) by assumption. reflexivity.
  - (* letb *)
    intros d o IHd [IH _]; split; [ apply IHd, IH |].
    intros S M; destruct d; cbn [elab_mod]; split; intros H; try discriminate; inversion H.
  - (* d_def *)
    intros x [o1 |] o2 HA [IH2 _] ob IHb S M; [ destruct HA as [IH1 _] |]; cbn [elab]; iff_case.
  - (* d_mod *)
    intros x ps md Hps Hmd ob IHb S M. apply Pterm_params in Hps.
    pose proof (sunit_iff S ps md) as Hu. cbn [elab]; split; intros Hg.
    + dest_eok. econstructor; [ apply Hu; [ assumption | exact Hmd |] | apply IHb; eassumption ].
      to_elab; reflexivity.
    + inversion Hg; subst. match goal with Hs : sunit _ _ _ _ |- _ => apply Hu in Hs; [| assumption | exact Hmd ] end.
      dest_eok. to_elab. reflexivity.
  - (* md_where *)
    intros cs Hcs S D. rewrite elab_mdef_where, ebind_eok.
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
    intros pv x ps md Hps Hmd cs Hcs S Φ Φ'. apply Pterm_params in Hps.
    pose proof (sunit_iff S ps md) as Hu. cbn [elab_body].
    split; intros Hg.
    + dest_eok. econstructor; [ apply Hu; [ assumption | exact Hmd |] | apply Hcs; eassumption ].
      to_elab; reflexivity.
    + inversion Hg; subst. match goal with Hs : sunit _ _ _ _ |- _ => apply Hu in Hs; [| assumption | exact Hmd ] end.
      dest_eok. to_elab. reflexivity.
  - (* c_def *)
    intros m x o1 o2 [IH1 _] [IH2 _] cs Hcs S Φ Φ'; cbn [elab_body].
    split; intros Hg.
    + dest_eok. to_spec. econstructor; eassumption.
    + inversion Hg; subst. to_elab. reflexivity.
  - (* c_import *)
    intros fq ip args spec Hargs cs Hcs S Φ Φ'; cbn [elab_body].
    assert (Ha : Forall Pterm args) by (eapply Forall_impl; [| exact Hargs ]; intros ? []; assumption).
    split; intros Hg.
    + apply ebind_eok in Hg as (E & HE & Hg). apply (target_iff _ _ _ _ _ Ha) in HE as (o & Ho & Hs).
      econstructor; [ eassumption | eassumption | apply Hcs; eassumption ].
    + inversion Hg; subst.
      rewrite (proj2 (target_iff _ _ _ _ _ Ha)) by eauto; cbn [ebind].
      apply Hcs; assumption.
  - (* c_eval *)
    intros o oA _ _ cs Hcs S Φ Φ'; cbn [elab_body]. split; [ discriminate | intros H; inversion H ].
Qed.

Lemma elab_iff : forall S o M, elab S o = eok M <-> sel S o M.
Proof. intros; apply (proj1 (proj1 objects_iff o)). Qed.

Lemma elab_mod_iff : forall S o H, elab_mod S o = eok H <-> selm S o H.
Proof. intros; apply (proj2 (proj1 objects_iff o)). Qed.

Lemma elab_params_iff : forall S ps tys, elab_params S ps = eok tys <-> sparams S ps tys.
Proof.
  intros; apply params_iff, Forall_forall; intros ? _ ? ?; apply elab_iff.
Qed.

(** ** Imports *)

Lemma elab_target_iff : forall S fq ip args E,
    elab_target_with elab S fq ip args = eok E <-> exists o, itarget fq ip args = Some o /\ selm S o E.
Proof.
  intros; apply target_iff, Forall_forall; intros ? _ ? ?; apply elab_iff.
Qed.

Lemma import_iff : forall fp ch O F fq ip args spec F' ls c,
    elab_import fp ch O F fq ip args spec = eok (F', ls, c) <->
    simport fp ch O F (Cst.c_import fq ip args spec) F' ls c.
Proof.
  intros; unfold elab_import. split.
  - intros H; apply ebind_eok in H as (E & HE & H); apply ebind_eok in H as ([] & Hf & H); inv_eok.
    apply elab_target_iff in HE as (o & Ho & Hs).
    econstructor; [ eassumption | eassumption | apply (check_fresh_all_ok _ _ tt); assumption ].
  - intros H; inversion H; subst.
    rewrite (proj2 (elab_target_iff _ _ _ _ _)) by eauto; cbn [ebind].
    rewrite (proj2 (check_fresh_all_ok _ _ tt)) by assumption. reflexivity.
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
      | H : elab_import _ _ _ _ _ _ _ _ = eok (_, _, _) |- _ => apply import_iff in H
      end.

  Ltac cmd_elab :=
    repeat match goal with
      | H : sel _ _ _ |- _ => apply elab_iff in H
      | H : selm _ _ _ |- _ => apply elab_mod_iff in H
      | H : sparams _ _ _ |- _ => apply elab_params_iff in H
      | H : scmds fp _ _ _ ?cs _, IH : Pcmds ?cs |- _ => apply IH in H
      | H : NoDup (map fst ?ps) |- _ => apply (check_params_ok ps tt) in H
      | H : fresh ?x ?F |- _ => apply (check_fresh_ok x F tt) in H
      | H : simport _ _ _ _ (Cst.c_import _ _ _ _) _ _ _ |- _ => apply import_iff in H
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
    apply Cst.cst_mut_ind; try easy.
    - intros cs Hcs body [=<-]. apply cmds_iff, Hcs.
    - intros pv x ps [body | oE] _ Hmd ch O F F' c'; cbn [elab_cmd]; [ specialize (Hmd body eq_refl) |].
      all: split; intros Hg; [ dest_eok; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - intros m x o1 o2 _ _ ch O F F' c'; cbn [elab_cmd].
      split; intros Hg; [ dest_eok; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
    - intros fq ip args spec _ ch O F F' c'; cbn [elab_cmd]. split.
      + intros H; apply ebind_eok in H as ([[F1 ls] ci] & H & E); injection E as <- <-.
        constructor; apply import_iff, H.
      + intros H; inversion H; subst.
        match goal with Hs : simport _ _ _ _ _ _ _ _ |- _ => apply import_iff in Hs; rewrite Hs end; reflexivity.
    - intros o [oA |] _ _ ch O F F' c'; cbn [elab_cmd].
      all: split; intros Hg; [ dest_eok; cmd_spec; econstructor; eassumption | inversion Hg; subst; cmd_elab; reflexivity ].
  Qed.

  Corollary elab_cmds_iff : forall ch O F cs ccs, elab_cmds fp ch O F cs = eok ccs <-> scmds fp ch O F cs ccs.
  Proof. intros; apply cmds_iff, Forall_forall; intros; apply commands_iff. Qed.
End Commands.

(** ** Units *)

Lemma imports_iff : forall fp O cs F F' lds imps,
    elab_imports fp O F cs = eok (F', lds, imps) <-> simports fp O F cs F' lds imps.
Proof.
  intros fp O; induction cs as [| c cs IH]; intros F F' lds imps; cbn [elab_imports].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - destruct c as [| | fq ip args spec |]; try (split; [ discriminate | intros H; inversion H ]).
    split.
    + intros H; apply ebind_eok in H as ([[F1 ls] ci] & H1 & H); apply ebind_eok in H as ([[F2 lds'] is] & H2 & E).
      injection E as <- <- <-.
      econstructor; [ apply import_iff | apply IH ]; eassumption.
    + intros H; inversion H; subst.
      rewrite (proj2 (import_iff _ _ _ _ _ _ _ _ _ _ _)) by eassumption; cbn [ebind].
      rewrite (proj2 (IH _ _ _ _)) by eassumption. reflexivity.
Qed.

Theorem elaborate_core_iff : forall prg u, elaborate_core prg = eok u <-> elab_spec prg u.
Proof.
  intros [imports [[fp ps] cs]] u. unfold elaborate_core. split.
  - intros H; apply ebind_eok in H as ([] & Hp & H); apply ebind_eok in H as (tys & Ht & H).
    apply ebind_eok in H as ([[F lds] imps] & Hi & H); apply ebind_eok in H as (ccs & Hc & H); inv_eok.
    apply check_params_ok in Hp. apply elab_params_iff in Ht. apply imports_iff in Hi. apply elab_cmds_iff in Hc.
    econstructor; eassumption.
  - intros Hs; inversion Hs; subst.
    rewrite (proj2 (check_params_ok _ tt)) by assumption; cbn [ebind].
    rewrite (proj2 (elab_params_iff _ _ _)) by eassumption; cbn [ebind].
    rewrite (proj2 (imports_iff _ _ _ _ _ _ _)) by eassumption; cbn [ebind].
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
