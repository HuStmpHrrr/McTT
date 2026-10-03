From Stdlib Require Import Bool Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax Members GlobalCtx Command.
From Mctt.Frontend Require Import Resolve Elaborator ElabSpec.

Import Syntax_Notations.
Open Scope list_scope.

(** * The Elaborator Meets Its Specification

    [elaborate_core] computes exactly [elab_spec] ([elaborate_core_sound],
    [elaborate_core_complete]), so the specification is functional
    ([elab_spec_functional]).  Both work on the same frames and scopes, so
    each layer is an [iff] between the elaborator succeeding and the
    specification relating, by induction on the syntax. *)

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

Lemma ebind_echeck : forall {B} b e (f : unit -> eres B) r,
    ebind (echeck b e) f = eok r <-> b = true /\ f tt = eok r.
Proof.
  intros; rewrite ebind_eok; split.
  - intros ([] & H1 & H2); apply echeck_eok in H1; auto.
  - intros [H1 H2]; exists tt; rewrite echeck_eok; auto.
Qed.

Ltac inv_eok :=
  repeat match goal with
    | H : eok _ = eok _ |- _ => injection H as H; subst
    | H : Some _ = Some _ |- _ => injection H as H; subst
    end.

(** ** Lists of Names *)

Lemma mem_b_iff : forall x l, mem_b x l = true <-> In x l.
Proof.
  intros; unfold mem_b; rewrite existsb_exists; split.
  - intros (y & Hin & Hb); apply String.eqb_eq in Hb; subst; assumption.
  - intros Hin; exists x; split; [ assumption | apply String.eqb_refl ].
Qed.

Lemma index_of_split : forall x l k,
    index_of x l = Some k -> exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l1 /\ k = List.length l1.
Proof.
  induction l as [| a l IH]; cbn; [ discriminate |]; intros k.
  destruct (String.eqb_spec x a) as [<- | Hne].
  - intros [=<-]; exists nil, l; cbn; auto.
  - destruct (index_of x l) eqn:E; cbn; [| discriminate ].
    intros [=<-]. destruct (IH _ eq_refl) as (l1 & l2 & -> & Hn & ->).
    exists (a :: l1), l2; cbn; repeat split; auto.
    intros [? | ?]; [ congruence | auto ].
Qed.

Lemma index_of_app : forall x l1 l2, ~ In x l1 -> index_of x (l1 ++ x :: l2) = Some (List.length l1).
Proof.
  induction l1 as [| a l1 IH]; cbn; intros.
  - rewrite String.eqb_refl; reflexivity.
  - destruct (String.eqb_spec x a); [ exfalso; auto |]. rewrite IH; auto.
Qed.

Lemma index_of_none : forall x l, index_of x l = None <-> ~ In x l.
Proof.
  induction l as [| a l IH]; cbn; [ tauto |].
  destruct (String.eqb_spec x a) as [<- | Hne].
  - split; [ discriminate | intros H; exfalso; auto ].
  - destruct (index_of x l) eqn:E; cbn.
    + split; [ discriminate |]. intros H; exfalso; apply H; right.
      destruct (index_of_split _ _ _ E) as (l1 & l2 & -> & _).
      apply in_or_app; right; left; reflexivity.
    + split; intros _; [| reflexivity ].
      intros [? | Hin]; [ congruence | apply (proj1 IH eq_refl Hin) ].
Qed.

Lemma param_index_some : forall x (ps : list (string * typ)) k,
    index_of x (rev (map fst ps)) = Some k ->
    exists ps1 A ps2, ps = ps1 ++ (x, A) :: ps2 /\ ~ In x (map fst ps2) /\ k = List.length ps2.
Proof.
  intros * H. destruct (index_of_split _ _ _ H) as (l1 & l2 & E & Hn & ->).
  apply (f_equal (@rev _)) in E. rewrite rev_involutive, rev_app_distr in E. cbn in E.
  rewrite <- app_assoc in E. cbn in E.
  apply map_eq_app in E as (ps1 & ps' & -> & E1 & E2).
  apply map_eq_cons in E2 as ([y A] & ps2 & -> & Ey & E2). cbn in Ey; subst y.
  exists ps1, A, ps2; repeat split.
  - rewrite E2, <- in_rev; assumption.
  - rewrite <- (length_map fst), E2, length_rev; reflexivity.
Qed.

Lemma param_index_split : forall x (A : typ) (ps1 ps2 : list (string * typ)),
    ~ In x (map fst ps2) ->
    index_of x (rev (map fst (ps1 ++ (x, A) :: ps2))) = Some (List.length ps2).
Proof.
  intros. rewrite map_app, rev_app_distr. cbn. rewrite <- app_assoc. cbn.
  rewrite index_of_app.
  - rewrite length_rev, length_map; reflexivity.
  - rewrite <- in_rev; assumption.
Qed.

Lemma param_index_none : forall x (ps : list (string * typ)), index_of x (rev (map fst ps)) = None <-> ~ In x (map fst ps).
Proof. intros; rewrite index_of_none, <- in_rev; reflexivity. Qed.

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

Lemma NoDup_app_disj : forall (l1 l2 : list string) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [| a l1 IH]; cbn; intros l2 x Hnd H1 H2; [ assumption |].
  inversion Hnd; subst. destruct H1 as [<- | H1]; [| eauto ].
  match goal with Hn : ~ In _ _ |- _ => apply Hn, in_or_app; right; assumption end.
Qed.

Lemma in_decl_names : forall cs x, In x (decl_names cs) <-> declares cs x.
Proof.
  intros; unfold decl_names, declares; rewrite in_flat_map. split.
  - intros (c & Hin & Hx). exists c; split; [ assumption |].
    destruct (cc_name c); cbn in Hx; [ destruct Hx as [<- | []]; reflexivity | destruct Hx ].
  - intros (c & Hin & Hx). exists c; split; [ assumption |]. rewrite Hx; left; reflexivity.
Qed.

(** ** Pre-application *)

Lemma tele_cons : forall F Fs, tele (F :: Fs) = List.length (sf_params F) + tele Fs.
Proof. reflexivity. Qed.

Lemma map_seq_add : forall (f : nat -> exp) b a s,
    map f (seq (b + s) a) = map (fun j => f (b + j)) (seq s a).
Proof.
  induction a; intros; cbn; [ reflexivity |].
  f_equal. rewrite <- Nat.add_succ_r. apply IHa.
Qed.

Lemma vars_desc_add : forall off a b, vars_desc off (a + b) = vars_desc (off + a) b ++ vars_desc off a.
Proof.
  intros; unfold vars_desc. rewrite (Nat.add_comm a b), seq_app, map_app. f_equal.
  - apply map_ext_in. intros i Hi. apply in_seq in Hi. f_equal. lia.
  - replace (0 + b) with (b + 0) by lia. rewrite map_seq_add.
    apply map_ext_in. intros i Hi. apply in_seq in Hi. f_equal. lia.
Qed.

Lemma preapp_iff : forall Fs off vs, preapp off Fs vs <-> vs = vars_desc off (tele Fs).
Proof.
  induction Fs as [| F Fs IH]; intros; split.
  - inversion 1; reflexivity.
  - intros ->; constructor.
  - inversion 1 as [| ? ? ? ? Hp]; subst. apply IH in Hp; subst.
    rewrite tele_cons, vars_desc_add. reflexivity.
  - intros ->. rewrite tele_cons, vars_desc_add. constructor. apply IH. reflexivity.
Qed.

(** ** Aliases *)

Lemma alias_lookup_none : forall x al, alias_lookup x al = None <-> ~ In x (map fst al).
Proof.
  induction al as [| [y t] al IH]; cbn; [ tauto |].
  destruct (String.eqb_spec x y) as [<- | Hne]; [ split; [ discriminate | intros H; exfalso; auto ] |].
  rewrite IH; split; [ intros H [? | ?]; [ congruence | auto ] | auto ].
Qed.

Lemma alias_lookup_some : forall x al t, alias_lookup x al = Some t -> In (x, t) al.
Proof.
  induction al as [| [y t'] al IH]; cbn; intros t H; [ discriminate |].
  destruct (String.eqb_spec x y) as [<- | Hne]; [ inv_eok; left; reflexivity | right; auto ].
Qed.

Lemma alias_lookup_in : forall x al t, NoDup (map fst al) -> In (x, t) al -> alias_lookup x al = Some t.
Proof.
  induction al as [| [y t'] al IH]; cbn; intros t Hnd Hin; [ contradiction |].
  inversion Hnd as [| ? ? Hy Hnd']; subst.
  destruct (String.eqb_spec x y) as [<- | Hne].
  - destruct Hin as [[=<-] | Hin]; [ reflexivity |].
    exfalso; apply Hy, in_map_iff; exists (x, t); auto.
  - destruct Hin as [[=] | Hin]; [ congruence | auto ].
Qed.

(** ** Frames *)

Lemma wf_aliases : forall F, sf_wf F -> NoDup (map fst (ss_alias (sf_scope F))).
Proof. intros F Hw; exact (NoDup_app_remove_r _ _ Hw). Qed.

Lemma wf_member_free : forall F x, sf_wf F -> declares (sf_cmds F) x -> ss_free (sf_scope F) x.
Proof.
  intros * Hw Hm Hin. apply in_decl_names in Hm.
  eapply NoDup_app_disj; [ exact Hw | exact Hin | apply in_or_app; left; exact Hm ].
Qed.

Lemma wf_param : forall F x A ps1 ps2,
    sf_wf F -> sf_params F = ps1 ++ (x, A) :: ps2 ->
    ss_free (sf_scope F) x /\ ~ declares (sf_cmds F) x /\ ~ In x (map fst ps2).
Proof.
  intros * Hw Hp. unfold sf_wf, sf_names, sf_taken in Hw. rewrite Hp, map_app in Hw.
  assert (Hx : In x (map fst ps1 ++ map fst ((x, A) :: ps2))) by (apply in_or_app; right; left; reflexivity).
  repeat split.
  - intros Hin. eapply NoDup_app_disj; [ exact Hw | exact Hin | apply in_or_app; right; exact Hx ].
  - intros Hd. apply in_decl_names in Hd.
    apply NoDup_app_remove_l in Hw.
    eapply NoDup_app_disj; [ exact Hw | exact Hd | exact Hx ].
  - intros Hin. do 2 apply NoDup_app_remove_l in Hw. cbn in Hw. apply NoDup_remove_2 in Hw. apply Hw, in_or_app; right; exact Hin.
Qed.

Lemma not_binds : forall F x,
    ss_free (sf_scope F) x -> ~ declares (sf_cmds F) x -> ~ In x (map fst (sf_params F)) -> ~ sf_binds F x.
Proof.
  unfold sf_binds, sf_names, sf_taken. intros * Ha Hd Hp Hin.
  apply in_app_or in Hin as [Hin | Hin]; [ exact (Ha Hin) |].
  apply in_app_or in Hin as [Hin | Hin]; [ apply Hd, in_decl_names, Hin | exact (Hp Hin) ].
Qed.

Lemma binds_not : forall F x,
    ~ sf_binds F x -> ss_free (sf_scope F) x /\ ~ declares (sf_cmds F) x /\ ~ In x (map fst (sf_params F)).
Proof.
  unfold sf_binds, sf_names, sf_taken. intros * Hn; repeat split; intros Hin; apply Hn.
  - apply in_or_app; left; assumption.
  - apply in_or_app; right; apply in_or_app; left; apply in_decl_names; assumption.
  - apply in_or_app; right; apply in_or_app; right; assumption.
Qed.

Lemma sf_fresh_b_iff : forall F x, sf_fresh_b F x = true <-> sf_fresh F x.
Proof.
  intros; unfold sf_fresh_b, sf_fresh, sf_binds; rewrite negb_true_iff, <- mem_b_iff.
  destruct (mem_b x (sf_names F)); split; congruence.
Qed.

Section Lookup.
  Variable (fp : fpath) (O : sscope).
  Hypothesis (HO : ss_wf O).

  Lemma fr_lookup_iff : forall Fs off x d,
      Forall sf_wf Fs ->
      fr_lookup fp O off x Fs = Some d <-> fbind fp O off Fs x d.
  Proof.
    induction Fs as [| F Fs IH]; intros off x d HFs; cbn [fr_lookup]; split.
    - intros H. destruct (alias_lookup x (ss_alias O)) as [t |] eqn:E; [| discriminate ]. inv_eok.
      apply fb_outer, alias_lookup_some, E.
    - intros Hf. inversion Hf; subst.
      rewrite (alias_lookup_in _ _ _ HO ltac:(eassumption)); reflexivity.
    - inversion HFs as [| ? ? HF HFs']; subst.
      intros H. destruct (alias_lookup x (ss_alias (sf_scope F))) as [t |] eqn:Ea.
      + inv_eok. apply fb_here, fr_alias, alias_lookup_some, Ea.
      + apply alias_lookup_none in Ea.
        destruct (mem_b x (decl_names (sf_cmds F))) eqn:Em.
        * inv_eok. apply mem_b_iff, in_decl_names in Em.
          apply fb_here, fr_mem; [ exact Em | apply preapp_iff; reflexivity ].
        * assert (Hd : ~ declares (sf_cmds F) x)
            by (intros Hd; apply in_decl_names, mem_b_iff in Hd; congruence).
          destruct (index_of x (rev (map fst (sf_params F)))) as [k |] eqn:Ei.
          -- apply param_index_some in Ei as (ps1 & A & ps2 & Hps & Hn & ->). inv_eok.
             eapply fb_here, fr_param; eassumption.
          -- apply param_index_none in Ei.
             apply fb_next; [ apply not_binds; assumption | apply IH; assumption ].
    - inversion HFs as [| ? ? HF HFs']; subst.
      intros Hf. inversion Hf as [? ? ? ? ? Hb | ? ? ? ? ? Hn Hnext |]; subst.
      + inversion Hb; subst.
        * rewrite (alias_lookup_in _ _ _ (wf_aliases _ HF) ltac:(eassumption)); reflexivity.
        * rewrite (proj2 (alias_lookup_none _ _) (wf_member_free _ _ HF ltac:(eassumption))).
          match goal with Hd : declares _ _ |- _ => apply in_decl_names, mem_b_iff in Hd; rewrite Hd end.
          match goal with Hp : preapp _ _ _ |- _ => apply preapp_iff in Hp; subst end.
          reflexivity.
        * match goal with Hp : sf_params _ = _ |- _ =>
            destruct (wf_param _ _ _ _ _ HF Hp) as (Ha & Hd & Hn2); rewrite Hp end.
          rewrite (proj2 (alias_lookup_none _ _) Ha).
          assert (Hm : mem_b x (decl_names (sf_cmds F)) = false)
            by (destruct (mem_b x (decl_names (sf_cmds F))) eqn:E; [ apply mem_b_iff, in_decl_names in E; contradiction | reflexivity ]).
          rewrite Hm, param_index_split by assumption. reflexivity.
      + destruct (binds_not _ _ Hn) as (Ha & Hd & Hp).
        rewrite (proj2 (alias_lookup_none _ _) Ha).
        assert (Hm : mem_b x (decl_names (sf_cmds F)) = false)
          by (destruct (mem_b x (decl_names (sf_cmds F))) eqn:E; [ apply mem_b_iff, in_decl_names in E; contradiction | reflexivity ]).
        rewrite Hm, (proj2 (param_index_none _ _) Hp).
        apply IH; assumption.
  Qed.
End Lookup.

(** ** Local Bindings *)


Lemma nbinders_cons : forall b L, nbinders (b :: L) = lb_binders b + nbinders L.
Proof. reflexivity. Qed.

Lemma lb_lookup_some : forall L k x d,
    lb_lookup k x L = Some d ->
    exists L1 b L2, L = L1 ++ b :: L2 /\ lb_name b = x /\ ~ In x (map lb_name L1) /\ d = ldenote (nbinders L1 + k) b.
Proof.
  induction L as [| b L IH]; intros k x d; cbn [lb_lookup]; [ discriminate |].
  destruct (String.eqb_spec x (lb_name b)) as [-> | Hne].
  - intros H; inv_eok. exists nil, b, L; cbn; auto.
  - intros H. apply IH in H as (L1 & b' & L2 & -> & Hb & Hn & ->).
    exists (b :: L1), b', L2; cbn [map app]; repeat split; auto.
    + intros [? | ?]; [ congruence | auto ].
    + rewrite nbinders_cons; f_equal; lia.
Qed.

Lemma lbound_lb_lookup : forall L x k b k0, lbound L x k b -> lb_lookup k0 x L = Some (ldenote (k + k0) b).
Proof.
  intros * (L1 & L2 & -> & Hb & Hn & ->). revert k0.
  induction L1 as [| b1 L1 IH]; intros k0; cbn [app lb_lookup].
  - rewrite <- Hb, String.eqb_refl; reflexivity.
  - destruct (String.eqb_spec x (lb_name b1)) as [E | _]; [ exfalso; apply Hn; left; auto |].
    rewrite IH by (intros Hin; apply Hn; right; assumption).
    rewrite nbinders_cons; f_equal; f_equal; lia.
Qed.

Lemma lb_lookup_none : forall L k x, lb_lookup k x L = None <-> ~ In x (map lb_name L).
Proof.
  induction L as [| b L IH]; cbn; intros; [ tauto |].
  destruct (String.eqb_spec x (lb_name b)) as [-> | Hne].
  - split; [ discriminate | intros H; exfalso; auto ].
  - rewrite IH; split; [ intros H [? | ?]; [ congruence | auto ] | auto ].
Qed.

Lemma lbound_in : forall L x k b, lbound L x k b -> In x (map lb_name L).
Proof.
  intros * (L1 & L2 & -> & Hb & _ & _). rewrite map_app; apply in_or_app; right; left; assumption.
Qed.

(** ** Denotations *)

Lemma den_to_term_iff : forall d M, den_to_term d = eok M <-> den_term d M.
Proof.
  intros [p vs | k | [E | E n]] M; cbn; split; intros H; inv_eok;
    try discriminate; try constructor; inversion H; reflexivity.
Qed.

Lemma den_to_mod_iff : forall d H, den_to_mod d = H <-> den_mod d H.
Proof.
  intros [p vs | k | [E | E n]] H; cbn; split; intros Hd; subst; try constructor; inversion Hd; reflexivity.
Qed.

Lemma existsb_path_beq : forall fq l, existsb (path_beq fq) l = true <-> In fq l.
Proof.
  intros; rewrite existsb_exists; split.
  - intros (y & Hin & Hb); apply path_beq_true in Hb; subst; assumption.
  - intros Hin; exists fq; split; [ assumption | apply path_beq_refl ].
Qed.

Lemma unit_reachable_iff : forall fq O Fs, unit_reachable O Fs fq = true <-> unit_in fq O Fs.
Proof.
  intros; unfold unit_reachable, unit_in.
  rewrite orb_true_iff, existsb_path_beq, existsb_exists.
  split; intros [H | (F & Hin & Hf)]; auto; right; exists F; split; try assumption.
  - apply existsb_path_beq; assumption.
  - apply existsb_path_beq; assumption.
Qed.

Lemma libinds_iff : forall fp O Fs E spec L L', libinds fp O Fs E spec L L' <-> L' = libinds_of E spec L.
Proof.
  intros; split; [ intros H; inversion H; reflexivity |].
  intros ->; destruct spec; constructor.
Qed.

(** ** Objects *)

Ltac dest_eok :=
  repeat match goal with
    | H : ebind _ _ = eok _ |- _ => apply ebind_eok in H as (? & ? & H); cbv beta in H
    | H : echeck _ _ = eok _ |- _ => apply echeck_eok in H
    | H : eok _ = eok _ |- _ => injection H as H; subst
    | H : eerr _ = eok _ |- _ => discriminate H
    end.

(** The loops of [elab_mdef], stated on their own. *)
Section Loops.
  Variable (fp : fpath) (O : sscope) (Fs : list sframe).

  Definition elab_path_unit (L : list lbind) (ps : list (string * Cst.obj)) (md : Cst.mdef)
    : list string -> eres (string * gunit)%type :=
    fix path_unit (p : list string) : eres (string * gunit)%type :=
      match p with
      | nil => eerr "empty module name"
      | x :: nil =>
          let* _ := check_params ps in
          let* tys := elab_params_with (elab fp O Fs) L ps in
          let* D := elab_mdef fp O Fs (lparams ps ++ L) md in
          eok (x, gu_mk (ptele tys) D)
      | x :: p' =>
          let* yU := path_unit p' in
          eok (x, gu_mk ⋅ (md_body (gm_ext gm_nil (fst yU) (ge_mod (snd yU)))))
      end.

  Fixpoint elab_body (L : list lbind) (Φ : gmod) (cs : list Cst.cmd) : eres gmod :=
    match cs with
    | nil => eok Φ
    | c :: cs' =>
        match c with
        | Cst.c_def m x oA oM =>
            let* A := elab fp O Fs L oA in
            let* M := elab fp O Fs L oM in
            elab_body (lb_var x :: L)
              (gm_ext Φ x (ge_def (negb (Cst.md_abstract m)) (Cst.md_private m) A (Some M))) cs'
        | Cst.c_mod p ps md' =>
            let* U := elab_path_unit L ps md' p in
            elab_body (lb_var (fst U) :: L) (gm_ext Φ (fst U) (ge_mod (snd U))) cs'
        | Cst.c_import fq ip spec =>
            let* E :=
              match fq, ip with
              | nil, x :: ip' => elab_dotted fp O Fs L x ip'
              | nil, nil => eerr "nothing to import"
              | _, _ => eok (me_path (p_abs fq ip))
              end in
            elab_body (libinds_of E spec L) (gm_check Φ (bc_import E (ispec_names spec))) cs'
        | Cst.c_eval oM oA =>
            let* M := elab fp O Fs L oM in
            match oA with
            | None => elab_body L (gm_check Φ (bc_eval M None)) cs'
            | Some oA =>
                let* A := elab fp O Fs L oA in
                elab_body L (gm_check Φ (bc_eval M (Some A))) cs'
            end
        end
    end.

  (** The cases of the mutual definition that call another of its
      functions, which [cbn] does not fold back. *)
  Lemma elab_mod_app : forall L o1 o2,
      elab_mod fp O Fs L (Cst.app o1 o2) =
        let* H := elab_mod fp O Fs L o1 in let* N := elab fp O Fs L o2 in eok (me_app H N).
  Proof. reflexivity. Qed.

  Lemma elab_proj : forall L o x,
      elab fp O Fs L (Cst.proj o x) = let* H := elab_mod fp O Fs L o in eok (a_mem H x).
  Proof. reflexivity. Qed.

  Lemma elab_mdef_alias : forall L oE,
      elab_mdef fp O Fs L (Cst.md_alias oE) = let* E := elab_mod fp O Fs L oE in eok (md_alias E).
  Proof. reflexivity. Qed.

  Lemma elab_let_mod : forall L x ps md ob,
      elab fp O Fs L (Cst.letb (Cst.d_mod x ps md) ob) =
        let* _ := check_params ps in
        let* tys := elab_params_with (elab fp O Fs) L ps in
        let* D := elab_mdef fp O Fs (lparams ps ++ L) md in
        let* B := elab fp O Fs (lb_var x :: L) ob in
        eok (ℓₘ (gu_mk (ptele tys) D) in B).
  Proof. reflexivity. Qed.

  Lemma elab_mdef_where : forall L cs,
      elab_mdef fp O Fs L (Cst.md_where cs) = let* Φ := elab_body L gm_nil cs in eok (md_body Φ).
  Proof. reflexivity. Qed.
End Loops.

Section Objects.
  Variable (fp : fpath) (O : sscope) (Fs : list sframe).
  Hypotheses (HO : ss_wf O) (HFs : Forall sf_wf Fs).

  Lemma lookup_char : forall (P : sden -> Prop) L x,
      ((exists k b, lbound L x k b /\ P (ldenote k b)) \/
       (~ In x (map lb_name L) /\ exists d, fbind fp O (nbinders L) Fs x d /\ P d)) <->
      exists d, lookup fp O Fs L x = Some d /\ P d.
  Proof.
    intros; unfold lookup; split.
    - intros [(k & b & Hb & HP) | (Hn & d & Hf & HP)].
      + rewrite (lbound_lb_lookup _ _ _ _ 0 Hb), Nat.add_0_r; eauto.
      + rewrite (proj2 (lb_lookup_none _ _ _) Hn), (proj2 (fr_lookup_iff fp O HO _ _ _ _ HFs) Hf); eauto.
    - intros (d & Hl & HP). destruct (lb_lookup 0 x L) as [d' |] eqn:E.
      + inv_eok. apply lb_lookup_some in E as (L1 & b & L2 & -> & Hb & Hn & ->).
        left; exists (nbinders L1 + 0), b; split; [ exists L1, L2; repeat split; auto; lia | assumption ].
      + right; split; [ apply lb_lookup_none in E; assumption |].
        exists d; split; [ apply (fr_lookup_iff fp O HO); assumption | assumption ].
  Qed.

  Lemma var_sel : forall L x M,
      sel fp O Fs L (Cst.var x) M <-> exists d, lookup fp O Fs L x = Some d /\ den_term d M.
  Proof.
    intros; rewrite <- lookup_char; split.
    - intros Hs; inversion Hs; subst; eauto 6.
    - intros [(k & b & ? & ?) | (? & d & ? & ?)]; [ eapply sel_local | eapply sel_frame ]; eassumption.
  Qed.

  Lemma var_selm : forall L x H,
      selm fp O Fs L (Cst.var x) H <-> exists d, lookup fp O Fs L x = Some d /\ den_mod d H.
  Proof.
    intros; rewrite <- lookup_char; split.
    - intros Hs; inversion Hs; subst; eauto 6.
    - intros [(k & b & ? & ?) | (? & d & ? & ?)]; [ eapply selm_local | eapply selm_frame ]; eassumption.
  Qed.

  Lemma dotted_selm : forall L x ip E,
      selm fp O Fs L (fold_left Cst.proj ip (Cst.var x)) E <->
      exists d, lookup fp O Fs L x = Some d /\ E = fold_left me_mem ip (den_to_mod d).
  Proof.
    intros L x ip; induction ip as [| ip y IH] using rev_ind; intros E; cbn [fold_left].
    - rewrite var_selm; split; intros (d & Hl & Hd); exists d; split; try assumption.
      + symmetry; apply den_to_mod_iff; assumption.
      + apply den_to_mod_iff; symmetry; assumption.
    - rewrite !fold_left_app; cbn [fold_left]. split.
      + intros Hs; inversion Hs; subst.
        match goal with Hm : selm _ _ _ _ (fold_left _ _ _) _ |- _ => apply IH in Hm as (d & Hl & ->) end.
        exists d; split; [ assumption | rewrite fold_left_app; reflexivity ].
      + intros (d & Hl & ->). rewrite fold_left_app. constructor. apply IH; eauto.
  Qed.

  Lemma elab_dotted_iff : forall L x ip E,
      elab_dotted fp O Fs L x ip = eok E <-> selm fp O Fs L (fold_left Cst.proj ip (Cst.var x)) E.
  Proof.
    intros; rewrite dotted_selm; unfold elab_dotted.
    destruct (lookup fp O Fs L x) as [d |]; split.
    - intros H; inv_eok; eauto.
    - intros (? & [=<-] & ->); reflexivity.
    - discriminate.
    - intros (? & [=] & _).
  Qed.

  Definition Pterm (o : Cst.obj) : Prop := forall L M, elab fp O Fs L o = eok M <-> sel fp O Fs L o M.
  Definition Pmod (o : Cst.obj) : Prop := forall L H, elab_mod fp O Fs L o = eok H <-> selm fp O Fs L o H.
  Definition Pmdef (md : Cst.mdef) : Prop := forall L D, elab_mdef fp O Fs L md = eok D <-> sdef fp O Fs L md D.

  Lemma params_iff : forall ps, Forall (fun p => Pterm (snd p)) ps ->
      forall L tys, elab_params_with (elab fp O Fs) L ps = eok tys <-> sparams fp O Fs L ps tys.
  Proof.
    induction 1 as [| [x oA] ps HA Hps IH]; intros L tys; cbn [elab_params_with].
    - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
    - unfold Pterm in HA; cbn [snd] in HA. split.
      + intros H; dest_eok. constructor; [ apply HA | apply IH ]; assumption.
      + intros Hs; inversion Hs; subst.
        match goal with H1 : sel _ _ _ _ _ _, H2 : sparams _ _ _ _ _ _ |- _ =>
          apply HA in H1; apply IH in H2; rewrite H1; cbn [ebind]; rewrite H2 end.
        reflexivity.
  Qed.

  Lemma sunit_iff : forall L ps md U,
      Forall (fun p => Pterm (snd p)) ps -> Pmdef md ->
      (let* _ := check_params ps in
       let* tys := elab_params_with (elab fp O Fs) L ps in
       let* D := elab_mdef fp O Fs (lparams ps ++ L) md in
       eok (gu_mk (ptele tys) D)) = eok U <-> sunit fp O Fs L ps md U.
  Proof.
    intros * Hps Hmd. split.
    - intros H; dest_eok.
      constructor; [ eapply (proj1 (check_params_ok _ _)) | apply params_iff | apply Hmd ]; eassumption.
    - intros Hs; inversion Hs; subst.
      match goal with Hn : NoDup _, H1 : sparams _ _ _ _ _ _, H2 : sdef _ _ _ _ _ _ |- _ =>
        rewrite (proj2 (check_params_ok ps tt) Hn); cbn [ebind];
        rewrite (proj2 (params_iff ps Hps _ _) H1); cbn [ebind];
        rewrite (proj2 (Hmd _ _) H2) end.
      reflexivity.
  Qed.

  (** The units [module p (ps) md] declares, named by the head of [p]. *)
  Inductive spath (L : list lbind) (ps : list (string * Cst.obj)) (md : Cst.mdef)
    : list string -> (string * gunit)%type -> Prop :=
  | spath_one : forall x U, sunit fp O Fs L ps md U -> spath L ps md (x :: nil) (x, U)
  | spath_more : forall x p U,
      p <> nil -> sunit fp O Fs L nil (Cst.md_where (Cst.c_mod p ps md :: nil)) U ->
      spath L ps md (x :: p) (x, U).

  Lemma sbody_c_mod : forall L Φ p ps md cs Φ',
      sbody fp O Fs L Φ (Cst.c_mod p ps md :: cs) Φ' <->
      exists yU, spath L ps md p yU /\ sbody fp O Fs (lb_var (fst yU) :: L) (gm_ext Φ (fst yU) (ge_mod (snd yU))) cs Φ'.
  Proof.
    intros; split.
    - intros Hs; inversion Hs; subst.
      + eexists (_, _); split; [ constructor |]; eassumption.
      + eexists (_, _); split; [ constructor |]; eassumption.
    - intros ([y U] & Hp & Hs); inversion Hp; subst; cbn in Hs.
      + eapply sb_mod; eassumption.
      + eapply sb_mod_path; eassumption.
  Qed.

  Lemma path_unit_iff : forall ps md, Forall (fun p => Pterm (snd p)) ps -> Pmdef md ->
      forall p L yU, elab_path_unit fp O Fs L ps md p = eok yU <-> spath L ps md p yU.
  Proof.
    intros ps md Hps Hmd p; induction p as [| x [| z p] IH]; intros L [y U].
    - split; [ discriminate | intros H; inversion H ].
    - cbn [elab_path_unit]. split.
      + intros H. dest_eok. constructor. apply sunit_iff; [ assumption .. |].
        repeat match goal with Hx : ?e = eok _ |- context [?e] => rewrite Hx; cbn [ebind] end.
        reflexivity.
      + intros Hs; inversion Hs as [? ? Hu | ? ? ? Hn]; subst; [| congruence ].
        apply sunit_iff in Hu; [| assumption .. ].
        dest_eok.
        repeat match goal with Hx : ?e = eok _ |- context [?e] => rewrite Hx; cbn [ebind] end.
        reflexivity.
    - change (elab_path_unit fp O Fs L ps md (x :: z :: p)) with
        (let* yU := elab_path_unit fp O Fs L ps md (z :: p) in
         eok (x, gu_mk ⋅ (md_body (gm_ext gm_nil (fst yU) (ge_mod (snd yU)))))).
      rewrite ebind_eok. split.
      + intros (yU & Hp & H); inv_eok. apply IH in Hp.
        constructor; [ discriminate |].
        change ⋅ with (ptele nil). constructor; [ constructor | constructor |].
        constructor. apply sbody_c_mod. exists yU; split; [ assumption | constructor ].
      + intros Hs; inversion Hs as [| ? ? ? Hn Hu]; subst.
        inversion Hu as [? ? ? tys D Hnd Hp Hd]; subst.
        inversion Hp; subst. inversion Hd; subst.
        match goal with Hb : sbody _ _ _ _ _ _ _ |- _ => apply sbody_c_mod in Hb as (yU & Hpu & Hnil) end.
        inversion Hnil; subst.
        exists yU; split; [ apply IH; assumption | reflexivity ].
  Qed.

  Definition Pcmd (c : Cst.cmd) : Prop :=
    forall cs Φ', (forall L Φ, elab_body fp O Fs L Φ cs = eok Φ' <-> sbody fp O Fs L Φ cs Φ') ->
    forall L Φ, elab_body fp O Fs L Φ (c :: cs) = eok Φ' <-> sbody fp O Fs L Φ (c :: cs) Φ'.

  Lemma ltarget_iff : forall L fq ip E,
      match fq, ip with
      | nil, x :: ip' => elab_dotted fp O Fs L x ip'
      | nil, nil => eerr "nothing to import"
      | _, _ => eok (me_path (p_abs fq ip))
      end = eok E <-> ltarget fp O Fs L fq ip E.
  Proof.
    intros. destruct fq as [| f fq]; [ destruct ip as [| x ip] |]; split.
    - discriminate.
    - intros H; inversion H; congruence.
    - intros H; apply lt_local, elab_dotted_iff, H.
    - intros H; inversion H; subst; [ apply elab_dotted_iff; assumption | congruence ].
    - intros H; inv_eok; constructor; discriminate.
    - intros H; inversion H; subst; reflexivity.
  Qed.

  (** Apply the induction hypotheses to the premises of a rule, and
      rewrite with the results. *)
  Ltac to_spec :=
    repeat match goal with
      | IH : forall L M, elab _ _ _ L ?o = eok M <-> _, H : elab _ _ _ ?L ?o = eok ?M |- _ => apply IH in H
      | IH : forall L M, elab_mod _ _ _ L ?o = eok M <-> _, H : elab_mod _ _ _ ?L ?o = eok ?M |- _ => apply IH in H
      | IH : forall L Φ, elab_body _ _ _ L Φ ?cs = eok ?Φ' <-> _, H : elab_body _ _ _ ?L ?Φ ?cs = eok ?Φ' |- _ =>
          apply IH in H
      end.

  Ltac to_elab :=
    repeat match goal with
      | IH : forall L M, elab _ _ _ L ?o = eok M <-> _, H : sel _ _ _ ?L ?o ?M |- _ => apply IH in H
      | IH : forall L M, elab_mod _ _ _ L ?o = eok M <-> _, H : selm _ _ _ ?L ?o ?M |- _ => apply IH in H
      | IH : forall L Φ, elab_body _ _ _ L Φ ?cs = eok ?Φ' <-> _, H : sbody _ _ _ ?L ?Φ ?cs ?Φ' |- _ =>
          apply IH in H
      end;
    repeat match goal with
      | H : ?e = eok _ |- context [?e] => rewrite H; cbn [ebind]
      end.

  Ltac obj_case :=
    let Hg := fresh "Hg" in
    split; intros Hg;
    [ dest_eok; to_spec; econstructor; eassumption
    | inversion Hg; subst; to_elab; reflexivity ].

  Lemma objects_iff :
    (forall o, Pterm o /\ Pmod o) /\
    (forall d, forall ob, Pterm ob -> forall L M,
        elab fp O Fs L (Cst.letb d ob) = eok M <-> sel fp O Fs L (Cst.letb d ob) M) /\
    (forall md, Pmdef md) /\ (forall c, Pcmd c).
  Proof.
    apply Cst.cst_mut_ind; unfold Pterm, Pmod, Pmdef, Pcmd.
    all: try (intros; repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
              split; intros L M; rewrite ?elab_mod_app, ?elab_proj; cbn [elab elab_mod];
              solve [ obj_case | let Hg := fresh "Hg" in split; [ discriminate | intros Hg; inversion Hg ] ]).
    - (* var *)
      intros x; split; intros L M; cbn [elab elab_mod].
      + rewrite var_sel. destruct (lookup fp O Fs L x) as [d |]; split.
        * intros H; exists d; split; [ reflexivity | apply den_to_term_iff, H ].
        * intros (d' & [=<-] & H); apply den_to_term_iff, H.
        * discriminate.
        * intros (? & [=] & _).
      + rewrite var_selm. destruct (lookup fp O Fs L x) as [d |]; split.
        * intros H; inv_eok; exists d; split; [ reflexivity | apply den_to_mod_iff; reflexivity ].
        * intros (d' & [=<-] & H); f_equal; apply den_to_mod_iff, H.
        * discriminate.
        * intros (? & [=] & _).
    - (* glob *)
      intros fq; split; intros L M; cbn [elab elab_mod]; split; intros H.
      + discriminate.
      + inversion H.
      + dest_eok; constructor; apply unit_reachable_iff; assumption.
      + inversion H; subst.
        match goal with Hu : unit_in _ _ _ |- _ => apply unit_reachable_iff in Hu; rewrite Hu end.
        reflexivity.
    - (* letb *)
      intros d o IHd [IH _]; split; [ apply IHd, IH |].
      intros L M; destruct d; cbn [elab_mod]; split; intros H; try discriminate; inversion H.
    - (* d_def *)
      intros x o1 o2 [IH1 _] [IH2 _] ob IHb L M; cbn [elab]. obj_case.
    - (* d_mod *)
      intros x ps md Hps Hmd ob IHb L M.
      assert (Hps' : Forall (fun p => Pterm (snd p)) ps)
        by (eapply Forall_impl; [| exact Hps ]; intros ? []; assumption).
      rewrite elab_let_mod; split.
      + intros Hg; dest_eok. constructor; [| apply IHb; assumption ].
        apply sunit_iff; [ assumption .. |].
        repeat match goal with Hx : ?e = eok _ |- context [?e] => rewrite Hx; cbn [ebind] end.
        reflexivity.
      + intros Hg; inversion Hg; subst.
        match goal with Hu : sunit _ _ _ _ _ _ _ |- _ => inversion Hu; subst end.
        match goal with Hn : NoDup _, H1 : sparams _ _ _ _ _ _, H2 : sdef _ _ _ _ _ _, H3 : sel _ _ _ _ ob _ |- _ =>
          rewrite (proj2 (check_params_ok ps tt) Hn); cbn [ebind];
          rewrite (proj2 (params_iff ps Hps' _ _) H1); cbn [ebind];
          rewrite (proj2 (Hmd _ _) H2); cbn [ebind];
          rewrite (proj2 (IHb _ _) H3) end.
        reflexivity.
    - (* md_where *)
      intros cs Hcs L D. rewrite elab_mdef_where, ebind_eok.
      assert (Hb : forall L Φ Φ', elab_body fp O Fs L Φ cs = eok Φ' <-> sbody fp O Fs L Φ cs Φ').
      { induction Hcs as [| c cs Hc Hcs IH]; intros L' Φ Φ'.
        - cbn; split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
        - apply Hc; intros; apply IH. }
      split.
      + intros (Φ & HΦ & H); inv_eok. constructor; apply Hb; assumption.
      + intros H; inversion H; subst. exists Φ; split; [ apply Hb; assumption | reflexivity ].
    - (* md_alias *)
      intros o [_ IHm] L D; rewrite elab_mdef_alias, ebind_eok; split.
      + intros (E & HE & H); inv_eok; constructor; apply IHm; assumption.
      + intros H; inversion H; subst; exists E; split; [ apply IHm; assumption | reflexivity ].
    - (* c_mod *)
      intros p ps md Hps Hmd cs Φ' Hcs L Φ.
      assert (Hps' : Forall (fun p => Pterm (snd p)) ps)
        by (eapply Forall_impl; [| exact Hps ]; intros ? []; assumption).
      change (elab_body fp O Fs L Φ (Cst.c_mod p ps md :: cs)) with
        (let* U := elab_path_unit fp O Fs L ps md p in
         elab_body fp O Fs (lb_var (fst U) :: L) (gm_ext Φ (fst U) (ge_mod (snd U))) cs).
      rewrite ebind_eok, sbody_c_mod.
      split; intros (yU & Hp & H); exists yU;
        (split; [ apply (path_unit_iff ps md Hps' Hmd); assumption | apply Hcs; assumption ]).
    - (* c_def *)
      intros m x o1 o2 [IH1 _] [IH2 _] cs Φ' Hcs L Φ; cbn [elab_body]. obj_case.
    - (* c_import *)
      intros fq ip spec cs Φ' Hcs L Φ; cbn [elab_body]; rewrite ebind_eok; split.
      + intros (E & HE & H). apply ltarget_iff in HE.
        eapply sb_import; [ eassumption | apply libinds_iff; reflexivity | apply Hcs; assumption ].
      + intros H; inversion H; subst. exists E; split; [ apply ltarget_iff; assumption |].
        match goal with Hl : libinds _ _ _ _ _ _ _ |- _ => apply libinds_iff in Hl; subst end.
        apply Hcs; assumption.
    - (* c_eval *)
      intros o oA [IH _] IHA cs Φ' Hcs L Φ; cbn [elab_body]. destruct oA as [oA |].
      + destruct IHA as [IHA _]. obj_case.
      + obj_case.
  Qed.
End Objects.

Section ObjectCorollaries.
  Variable (fp : fpath) (O : sscope) (Fs : list sframe).
  Hypotheses (HO : ss_wf O) (HFs : Forall sf_wf Fs).

  Lemma elab_iff : forall L o M, elab fp O Fs L o = eok M <-> sel fp O Fs L o M.
  Proof. intros; apply (proj1 (proj1 (objects_iff fp O Fs HO HFs) o)). Qed.

  Lemma elab_mod_iff : forall L o H, elab_mod fp O Fs L o = eok H <-> selm fp O Fs L o H.
  Proof. intros; apply (proj2 (proj1 (objects_iff fp O Fs HO HFs) o)). Qed.

  Lemma elab_params_iff : forall L ps tys, elab_params fp O Fs L ps = eok tys <-> sparams fp O Fs L ps tys.
  Proof.
    intros; apply params_iff; [ assumption .. |].
    apply Forall_forall; intros p _ L' M; apply elab_iff.
  Qed.

  Lemma itarget_iff : forall fq ip E, itarget_of fp O Fs fq ip = eok E <-> itarget fp O Fs fq ip E.
  Proof.
    intros. unfold itarget_of. destruct fq as [| f fq]; [ destruct ip as [| x ip] |]; split.
    - discriminate.
    - intros H; inversion H; congruence.
    - intros H; apply it_local, elab_dotted_iff, H; assumption.
    - intros H; inversion H; subst; [ apply elab_dotted_iff; assumption | congruence ].
    - intros H; inv_eok; constructor; discriminate.
    - intros H; inversion H; subst; reflexivity.
  Qed.
End ObjectCorollaries.

Lemma sparams_names : forall fp O Fs L ps tys, sparams fp O Fs L ps tys -> map fst tys = map fst ps.
Proof. induction 1; cbn; congruence. Qed.

Lemma scmd_params : forall fp O Fs F c F', scmd fp O Fs F c F' -> sf_params F' = sf_params F.
Proof.
  intros fp O.
  apply (scmd_wf_ind fp O (fun Fs F c F' _ => sf_params F' = sf_params F)
           (fun Fs F cs F' _ => sf_params F' = sf_params F)); intros; cbn; congruence.
Qed.

Lemma scmds_params : forall fp O Fs F cs F', scmds fp O Fs F cs F' -> sf_params F' = sf_params F.
Proof. induction 1; [ reflexivity |]. rewrite IHscmds; eapply scmd_params; eassumption. Qed.

(** ** Imports *)

Lemma alias_fresh_b_iff : forall taken sc y, alias_fresh_b taken sc y = true <-> alias_fresh taken sc y.
Proof.
  intros; unfold alias_fresh_b, alias_fresh, ss_free.
  rewrite andb_true_iff, !negb_true_iff, <- !mem_b_iff.
  destruct (mem_b y taken), (mem_b y (map fst (ss_alias sc))); intuition congruence.
Qed.

Lemma use_bind_err : forall E taken ns e, fold_left (use_bind E taken) ns (eerr e) = eerr e.
Proof. induction ns; intros; cbn; auto. Qed.

Lemma use_binds_iff : forall E taken ns sc sc',
    fold_left (use_bind E taken) ns (eok sc) = eok sc' <-> use_binds E taken ns sc sc'.
Proof.
  induction ns as [| n ns IH]; intros; cbn [fold_left].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - unfold use_bind at 2; cbn [ebind].
    destruct (alias_fresh_b taken sc n) eqn:Ef; cbn [echeck ebind].
    + rewrite IH. split; [ intros; constructor; [ apply alias_fresh_b_iff |]; assumption |].
      intros H; inversion H; assumption.
    + rewrite use_bind_err. split; [ discriminate |].
      intros H; inversion H; subst. apply alias_fresh_b_iff in H2. congruence.
Qed.

Lemma ibinds_iff : forall E taken spec sc sc',
    ibinds_of E taken spec sc = eok sc' <-> ibinds E taken spec sc sc'.
Proof.
  intros; destruct spec as [| y | ns]; cbn [ibinds_of].
  - split; [ intros H; inv_eok; constructor | intros H; inversion H; reflexivity ].
  - rewrite ebind_echeck, alias_fresh_b_iff. split.
    + intros [Hf H]; inv_eok; constructor; assumption.
    + intros H; inversion H; subst; auto.
  - rewrite use_binds_iff. split; [ intros; constructor; assumption | intros H; inversion H; assumption ].
Qed.

(** ** Commands *)

(** The loop of [elab_cmd] over a dotted module name. *)
Definition elab_open_path (ps : list (string * Cst.obj)) (md : Cst.mdef)
  : list string -> ustate -> eres ustate :=
  fix open_path (p : list string) (st : ustate) : eres ustate :=
    match p with
    | nil => eerr "empty module name"
    | x :: nil =>
        match md with
        | Cst.md_alias oE => elab_alias st x ps oE
        | Cst.md_where body =>
            let* _ := check_fresh st x in
            let* _ := check_params ps in
            let* tys := elab_params (us_unit st) (us_outer st) (us_frames st) nil ps in
            let* st1 := elab_cmds (us_open st (sf_new (us_path st ++ x :: nil) tys)) body in
            us_close x st1
        end
    | x :: p' =>
        let* _ := check_fresh st x in
        let* st1 := open_path p' (us_open st (sf_new (us_path st ++ x :: nil) nil)) in
        us_close x st1
    end.

Lemma elab_cmd_mod : forall st p ps md, elab_cmd st (Cst.c_mod p ps md) = elab_open_path ps md p st.
Proof. reflexivity. Qed.

Lemma check_fresh_ok : forall fp O F Fs imps x,
    check_fresh (us_mk fp O (F :: Fs) imps) x = eok tt <-> sf_fresh F x.
Proof.
  intros; unfold check_fresh, us_top; cbn [us_frames].
  rewrite <- sf_fresh_b_iff. destruct (sf_fresh_b F x); cbn; split; congruence.
Qed.

Lemma check_fresh_nil : forall fp O imps x u, check_fresh (us_mk fp O nil imps) x <> eok u.
Proof. discriminate. Qed.

Ltac cmd_sound HO :=
  repeat match goal with
    | H : sf_fresh_b _ _ = true |- _ => apply sf_fresh_b_iff in H
    | H : check_fresh _ _ = eok ?u |- _ => destruct u; apply check_fresh_ok in H
    | H : check_params _ = eok _ |- _ => apply check_params_ok in H
    | H : elab ?fp ?O ?Fs ?L ?o = eok _ |- _ => apply (elab_iff fp O Fs HO ltac:(assumption)) in H
    | H : elab_mod ?fp ?O ?Fs ?L ?o = eok _ |- _ => apply (elab_mod_iff fp O Fs HO ltac:(assumption)) in H
    | H : elab_params ?fp ?O ?Fs ?L ?ps = eok _ |- _ => apply (elab_params_iff fp O Fs HO ltac:(assumption)) in H
    | H : itarget_of ?fp ?O ?Fs ?fq ?ip = eok _ |- _ => apply (itarget_iff fp O Fs HO ltac:(assumption)) in H
    | H : ibinds_of _ _ _ _ = eok _ |- _ => apply ibinds_iff in H
    end.

Ltac cmd_complete HO :=
  repeat match goal with
    | H : sf_fresh ?F ?x |- _ => apply sf_fresh_b_iff in H
    | H : NoDup (@map (string * Cst.obj) string fst ?ps) |- _ => apply (proj2 (check_params_ok ps tt)) in H
    | H : sel ?fp ?O ?Fs ?L ?o ?M |- _ => apply (elab_iff fp O Fs HO ltac:(assumption)) in H
    | H : selm ?fp ?O ?Fs ?L ?o ?M |- _ => apply (elab_mod_iff fp O Fs HO ltac:(assumption)) in H
    | H : sparams ?fp ?O ?Fs ?L ?ps ?tys |- _ => apply (elab_params_iff fp O Fs HO ltac:(assumption)) in H
    | H : itarget ?fp ?O ?Fs ?fq ?ip ?E |- _ => apply (itarget_iff fp O Fs HO ltac:(assumption)) in H
    | H : ibinds _ _ _ _ _ |- _ => apply ibinds_iff in H
    end;
  repeat match goal with
    | H : ?e = _ |- context [?e] => rewrite H; cbn [ebind echeck]
    end.

Section Commands.
  Variable (fp : fpath) (O : sscope).
  Hypothesis (HO : ss_wf O).

  Definition Pc (c : Cst.cmd) : Prop :=
    forall Fs F imps st, Forall sf_wf (F :: Fs) ->
      elab_cmd (us_mk fp O (F :: Fs) imps) c = eok st <->
      exists F', scmd fp O Fs F c F' /\ st = us_mk fp O (F' :: Fs) imps.

  Definition Pcs (cs : list Cst.cmd) : Prop :=
    forall Fs F imps st, Forall sf_wf (F :: Fs) ->
      elab_cmds (us_mk fp O (F :: Fs) imps) cs = eok st <->
      exists F', scmds fp O Fs F cs F' /\ st = us_mk fp O (F' :: Fs) imps.

  Lemma cmds_of_cmd : forall cs, Forall Pc cs -> Pcs cs.
  Proof.
    induction 1 as [| c cs Hc Hcs IH]; intros Fs F imps st HF; cbn [elab_cmds].
    - split; [ intros H; inv_eok; eexists; split; [ constructor | reflexivity ] |].
      intros (F' & Hs & ->); inversion Hs; subst; reflexivity.
    - rewrite ebind_eok. split.
      + intros (st1 & H1 & H2). apply Hc in H1 as (F1 & Hs1 & ->); [| assumption ].
        inversion HF; subst.
        apply IH in H2 as (F2 & Hs2 & ->); [| constructor; [ eapply scmd_wf | ]; eassumption ].
        eexists; split; [ econstructor |]; eauto.
      + intros (F2 & Hs & ->). inversion Hs; subst. inversion HF; subst.
        exists (us_mk fp O (F1 :: Fs) imps); split; [ apply Hc; [ assumption | eauto ] |].
        apply IH; [ constructor; [ eapply scmd_wf | ]; eassumption | eauto ].
  Qed.

  Lemma import_iff : forall Fs F imps st fq ip spec, Forall sf_wf (F :: Fs) ->
      elab_cmd (us_mk fp O (F :: Fs) imps) (Cst.c_import fq ip spec) = eok st <->
      exists F', scmd fp O Fs F (Cst.c_import fq ip spec) F' /\ st = us_mk fp O (F' :: Fs) imps.
  Proof.
    intros * HF; cbn [elab_cmd elab_import us_frames us_unit us_outer us_imps]. split.
    - intros H; dest_eok; cmd_sound HO.
      eexists; split; [ constructor; econstructor; eassumption | reflexivity ].
    - intros (F' & Hs & ->). inversion Hs; subst.
      match goal with Hi : simport _ _ _ _ _ _ _ _ |- _ => inversion Hi; subst end.
      cmd_complete HO. reflexivity.
  Qed.

  Lemma path_iff : forall ps md, (forall body, md = Cst.md_where body -> Pcs body) ->
      forall p Fs F imps st, Forall sf_wf (F :: Fs) ->
      elab_open_path ps md p (us_mk fp O (F :: Fs) imps) = eok st <->
      exists F', scmd fp O Fs F (Cst.c_mod p ps md) F' /\ st = us_mk fp O (F' :: Fs) imps.
  Proof.
    intros ps md Hmd p; induction p as [| x [| z p] IH]; intros Fs F imps st HF.
    - split; [ discriminate | intros (? & Hs & _); inversion Hs ].
    - destruct md as [body | oE].
      + specialize (Hmd body eq_refl).
        cbn [elab_open_path us_unit us_outer us_frames us_path us_open]. split.
        * intros H; dest_eok; cmd_sound HO.
          match goal with
          | Hn : NoDup _, Ht : sparams _ _ _ _ _ ?tys, Hc : elab_cmds _ body = eok ?st1 |- _ =>
              pose proof (sparams_names _ _ _ _ _ _ Ht) as Hnm;
              apply Hmd in Hc as (N & HN & ->);
              [| constructor; [ apply sf_wf_new; rewrite Hnm; exact Hn | assumption ] ]
          end.
          cbn [us_close us_frames us_unit us_outer us_imps] in H. inv_eok.
          eexists; split; [| reflexivity ].
          rewrite (scmds_params _ _ _ _ _ _ HN); cbn [sf_params sf_new].
          eapply sc_mod; eassumption.
        * intros (F' & Hs & ->). inversion Hs; subst; [| congruence ].
          match goal with
          | Hn : NoDup (map fst ps), Ht : sparams _ _ _ _ ps ?tys, Hc : scmds _ _ _ _ body ?N, Hf : sf_fresh _ _ |- _ =>
              rename Hn into Hnd, Ht into Hpt, Hc into Hsc, Hf into Hfr
          end.
          pose proof (sparams_names _ _ _ _ _ _ Hpt) as Hnm.
          pose proof (scmds_params _ _ _ _ _ _ Hsc) as Hpar.
          assert (HN : Forall sf_wf (sf_new (sf_path F ++ x :: nil) tys :: F :: Fs))
            by (constructor; [ apply sf_wf_new; rewrite Hnm; exact Hnd | assumption ]).
          pose proof (proj2 (Hmd _ _ imps _ HN) (ex_intro _ N (conj Hsc eq_refl))) as Hb.
          rewrite (proj2 (check_fresh_ok _ _ _ _ _ _) Hfr); cbn [ebind].
          rewrite (proj2 (check_params_ok ps tt) Hnd); cbn [ebind].
          rewrite (proj2 (elab_params_iff fp O (F :: Fs) HO HF _ _ _) Hpt); cbn [ebind].
          unfold us_open; cbn [us_frames us_unit us_outer us_imps]. rewrite Hb. cbn [ebind us_close us_frames us_unit us_outer us_imps]. rewrite Hpar. reflexivity.
      + cbn [elab_open_path elab_alias us_top us_unit us_outer us_frames us_imps]. split.
        * intros H; dest_eok; cmd_sound HO.
          eexists; split; [ constructor; eassumption | reflexivity ].
        * intros (F' & Hs & ->). inversion Hs; subst; [| congruence ].
          cmd_complete HO. reflexivity.
    - change (elab_open_path ps md (x :: z :: p) (us_mk fp O (F :: Fs) imps)) with
        (let* _ := check_fresh (us_mk fp O (F :: Fs) imps) x in
         let* st1 := elab_open_path ps md (z :: p) (us_mk fp O (sf_new (sf_path F ++ x :: nil) nil :: F :: Fs) imps) in
         us_close x st1).
      assert (HN : Forall sf_wf (sf_new (sf_path F ++ x :: nil) nil :: F :: Fs))
        by (constructor; [ apply sf_wf_new; constructor | assumption ]).
      split.
      + intros H; dest_eok.
        match goal with Hc : check_fresh _ _ = eok ?u |- _ => destruct u; apply check_fresh_ok in Hc end.
        match goal with Ho : elab_open_path _ _ _ _ = eok _ |- _ =>
          apply IH in Ho as (N & HsN & ->); [| assumption ] end.
        match goal with Hc : us_close _ _ = eok _ |- _ =>
          cbn [us_close us_frames us_unit us_outer us_imps] in Hc; inv_eok end.
        eexists; split; [| reflexivity ].
        rewrite (scmd_params _ _ _ _ _ _ HsN). cbn [sf_params sf_new].
        apply sc_mod_path; [ discriminate | assumption .. ].
      + intros (F' & Hs & ->). inversion Hs; subst.
        rewrite (proj2 (check_fresh_ok _ _ _ _ _ _) ltac:(eassumption)); cbn [ebind].
        match goal with Hc : scmd _ _ _ _ (Cst.c_mod (z :: p) _ _) ?N |- _ =>
          pose proof (scmd_params _ _ _ _ _ _ Hc) as Hpar;
          rewrite (proj2 (IH _ _ imps _ HN) ltac:(eexists; split; [ exact Hc | reflexivity ])) end.
        cbn [ebind us_close us_frames us_unit us_outer us_imps]. rewrite Hpar. reflexivity.
  Qed.

  Lemma commands_all :
    (forall o : Cst.obj, True) /\ (forall d : Cst.decl, True) /\
    (forall md, forall body, md = Cst.md_where body -> Forall Pc body) /\ (forall c, Pc c).
  Proof.
    apply (Cst.cst_mut_ind (fun _ => True) (fun _ => True)
             (fun md => forall body, md = Cst.md_where body -> Forall Pc body) Pc);
      intros; auto; try discriminate.
    - (* md_where *)
      match goal with H : Cst.md_where _ = Cst.md_where _ |- _ => injection H as <- end. assumption.
    - (* c_mod *)
      intros Fs F imps st HF. rewrite elab_cmd_mod. apply path_iff; [| assumption ].
      intros body ->. apply cmds_of_cmd; auto.
    - (* c_def *)
      intros Fs F imps st HF; cbn [elab_cmd elab_def us_top us_unit us_outer us_frames us_imps]. split.
      + intros Hg; dest_eok; cmd_sound HO.
        eexists; split; [ constructor; eassumption | reflexivity ].
      + intros (F' & Hs & ->). inversion Hs; subst. cmd_complete HO. reflexivity.
    - (* c_import *)
      intros Fs F imps st HF; apply import_iff; assumption.
    - (* c_eval *)
      intros Fs F imps st HF; cbn [elab_cmd elab_eval us_top us_unit us_outer us_frames us_imps].
      destruct oA as [oA |]; split.
      + intros Hg; dest_eok; cmd_sound HO.
        eexists; split; [ constructor; eassumption | reflexivity ].
      + intros (F' & Hs & ->). inversion Hs; subst. cmd_complete HO. reflexivity.
      + intros Hg; dest_eok; cmd_sound HO.
        eexists; split; [ constructor; eassumption | reflexivity ].
      + intros (F' & Hs & ->). inversion Hs; subst. cmd_complete HO. reflexivity.
  Qed.

  Lemma commands_iff : forall c, Pc c.
  Proof. exact (proj2 (proj2 (proj2 commands_all))). Qed.

  Lemma commands_cmds_iff : forall cs, Pcs cs.
  Proof. intros; apply cmds_of_cmd, Forall_forall; intros; apply commands_iff. Qed.
End Commands.

(** ** Units *)

Lemma ss_wf_empty : ss_wf ss_empty.
Proof. constructor. Qed.

(** The leading imports, which no frame encloses yet. *)
Lemma imports_iff : forall fp cs O imps st, ss_wf O ->
    elab_cmds (us_mk fp O nil imps) cs = eok st <->
    exists O' is, simports fp O cs O' is /\ st = us_mk fp O' nil (imps ++ is).
Proof.
  intros fp; induction cs as [| c cs IH]; intros O imps st HO; cbn [elab_cmds].
  - split; [ intros H; inv_eok; exists O, nil; rewrite app_nil_r; split; [ constructor | reflexivity ] |].
    intros (O' & is & Hs & ->); inversion Hs; subst; rewrite app_nil_r; reflexivity.
  - rewrite ebind_eok. destruct c as [p ps md | m x oA oM | fq ip spec | oM oA].
    + split; [| intros (? & ? & Hs & _); inversion Hs ].
      intros (st1 & H & _). rewrite elab_cmd_mod in H.
      destruct p as [| y [| z p]]; [ discriminate | destruct md; cbn in H; discriminate | cbn in H; discriminate ].
    + split; [ intros (? & H & _); cbn in H; discriminate | intros (? & ? & Hs & _); inversion Hs ].
    + cbn [elab_cmd elab_import us_frames us_unit us_outer us_imps]. split.
      * intros (st1 & H1 & H2). dest_eok.
        apply (itarget_iff fp O nil HO ltac:(constructor)) in H. apply ibinds_iff in H0.
        assert (Hs : simport fp O nil nil O (Cst.c_import fq ip spec) x0 (cc_import (ifile fq) x (ispec_names spec)))
          by (constructor; assumption).
        apply IH in H2 as (O' & is & Hss & ->).
        -- exists O', (cc_import (ifile fq) x (ispec_names spec) :: is); split; [ econstructor; eassumption |].
           rewrite <- app_assoc; reflexivity.
        -- pose proof (simport_wf _ _ _ _ _ _ _ _ Hs) as Hw. rewrite !app_nil_r in Hw. exact (Hw HO).
      * intros (O' & is & Hs & ->). inversion Hs; subst.
        match goal with Hi : simport _ _ _ _ _ _ _ _ |- _ =>
          pose proof (simport_wf _ _ _ _ _ _ _ _ Hi) as Hw; rewrite !app_nil_r in Hw; inversion Hi; subst end.
        match goal with Ht : itarget _ _ _ _ _ _ |- _ =>
          rewrite (proj2 (itarget_iff fp O nil HO (Forall_nil _) _ _ _) Ht); cbn [ebind] end.
        cmd_complete HO. eexists; split; [ reflexivity |].
        apply IH; [ exact (Hw HO) |]. eexists _, _; split; [ eassumption |]. rewrite <- app_assoc; reflexivity.
    + split; [ destruct oA; intros (? & H & _); cbn in H; discriminate | intros (? & ? & Hs & _); inversion Hs ].
Qed.

Theorem elaborate_core_iff : forall prg u, elaborate_core prg = eok u <-> elab_spec prg u.
Proof.
  intros [imports [[fp ps] cs]] u. unfold elaborate_core. rewrite ebind_eok. split.
  - intros (st0 & H0 & H). apply imports_iff in H0 as (O & imps & Hi & ->); [| exact ss_wf_empty ].
    pose proof (simports_wf _ _ _ _ _ Hi ss_wf_empty) as HO.
    cbn [us_outer us_open us_unit us_imps us_frames app] in H.
    dest_eok.
    match goal with Hc : check_params _ = eok _ |- _ => apply check_params_ok in Hc end.
    match goal with Hp : elab_params _ _ _ _ _ = eok _ |- _ =>
      apply (elab_params_iff fp O nil HO (Forall_nil _)) in Hp; pose proof (sparams_names _ _ _ _ _ _ Hp) as Hnm end.
    match goal with Hc : elab_cmds _ cs = eok _ |- _ =>
      apply (commands_cmds_iff fp O HO) in Hc as (F & HF & ->);
      [| constructor; [ apply sf_wf_new; rewrite Hnm; assumption | constructor ] ] end.
    match goal with Hm : match us_frames _ with _ => _ end = eok _ |- _ => cbn [us_frames us_imps] in Hm; inv_eok end.
    rewrite (scmds_params _ _ _ _ _ _ HF). cbn [sf_params sf_new]. econstructor; eassumption.
  - intros Hs; inversion Hs as [? ? ? ? O imps tys F H1 H4 H5 H6]; subst.
    pose proof (simports_wf _ _ _ _ _ H1 ss_wf_empty) as HO.
    exists (us_mk fp O nil imps); split; [ apply imports_iff; [ exact ss_wf_empty | eauto ] |].
    cbn [us_outer us_open us_unit us_imps us_frames].
    pose proof (sparams_names _ _ _ _ _ _ H5) as Hnm.
    pose proof (scmds_params _ _ _ _ _ _ H6) as Hpar.
    rewrite (proj2 (check_params_ok ps tt) H4); cbn [ebind].
    rewrite (proj2 (elab_params_iff fp O nil HO ltac:(constructor) _ _ _) H5); cbn [ebind].
    unfold us_open; cbn [us_frames us_unit us_outer us_imps].
    rewrite (proj2 (commands_cmds_iff fp O HO _ nil _ imps _ ltac:(constructor; [ apply sf_wf_new; rewrite Hnm; assumption | constructor ])))
      by (eexists; split; [ eassumption | reflexivity ]).
    cbn [ebind us_frames us_imps]. rewrite Hpar. reflexivity.
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
