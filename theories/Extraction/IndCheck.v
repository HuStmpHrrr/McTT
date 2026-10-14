From Stdlib Require Import List ListDec String PeanoNat.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing Strengthening.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Consequences.
From Mctt.Core.Syntactic Require Import IndCong.
From Mctt.Core.Syntactic.System Require Import IndClassify MemberWf.
From Mctt.Extraction Require Import NbE PseudoMonadic TypeCheckBase.
Import Domain_Notations Wk_Notations Fixed_Notations.

(** * Checking the Forms of Inductive Types

    The cases of [ati_ind], [ati_con] and [ati_elim], shared by both
    checkers ([Extraction.TypeCheck] and [Reference.TypeCheck]).  The type
    former and a constructor recurse on nothing; the eliminator recurses on
    its scrutinee, its motive and its branches, and takes those recursive
    calls as arguments, so that the mutual fixpoints of the checkers only
    pass them on. *)

(** Whether every element of a list satisfies a predicate, from a decision
    for each element. *)
Definition forall_in_dec {X : Type} (Q : X -> Prop) :
  forall (L : list X), (forall x, In x L -> {Q x} + {~ Q x}) ->
    {forall x, In x L -> Q x} + {~ forall x, In x L -> Q x}.
Proof.
  fix go 1; intros [| x L] f.
  - left; intros ? [].
  - destruct (f x (or_introl eq_refl)) as [Hx | Hx]; [| right; intros H; apply Hx, H; left; reflexivity ].
    destruct (go L (fun y Hy => f y (or_intror Hy))) as [HL | HL]; [ left | right ].
    + intros y [<- | Hy]; auto.
    + intros H; apply HL; intros y Hy; apply H; right; exact Hy.
Defined.

Section Fixed_GCtx.
Context {GC : GCtx}.

(** Whether a normal form is an instance of an inductive type. *)
#[derive(equations=no,eliminator=no)]
Equations get_indty_nf (A : nf) : { p & { Rs | A = nf_indty p Rs } } + { forall p Rs, A <> nf_indty p Rs } :=
| nf_indty p Rs => pureo (existT _ p (exist _ Rs _))
| _ => inright _
.

Extraction Inline get_indty_nf.

(** ** The Type Former and the Constructors *)

Lemma ind_ty_order : forall G p D, ⊢ G -> ind_lookup gc_deps gc_stack p = Some D ->
    nbe_ty_order gc_deps gc_stack G (ind_ty D).
Proof.
  intros * HG Hl.
  destruct (decl_of_lookup _ _ _ _ _ HG Hl) as [HD Hc].
  destruct (ind_ty_typed _ _ _ _ HD Hc HG) as [j Hj].
  destruct (soundness_ty Hj) as [W [HW _]].
  eapply nbe_ty_order_sound; exact HW.
Qed.

Lemma con_ty_order : forall G p D c gs, ⊢ G -> ind_lookup gc_deps gc_stack p = Some D -> ind_con D c = Some gs ->
    nbe_ty_order gc_deps gc_stack G (con_ty p D gs).
Proof.
  intros * HG Hl Hcon.
  destruct (decl_of_lookup _ _ _ _ _ HG Hl) as [HD Hc].
  destruct (con_ty_typed _ _ _ _ _ _ _ HD Hc Hl Hcon HG) as [j Hj].
  destruct (soundness_ty Hj) as [W [HW _]].
  eapply nbe_ty_order_sound; exact HW.
Qed.

Lemma ind_ty_post : forall G p D W, ⊢ G -> ind_lookup gc_deps gc_stack p = Some D -> nbe_ty_f G (ind_ty D) W ->
    G ⊢a a_ind p ⟹ W /\ (exists UA u, G ⊢a W ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ W : Typeω@i).
Proof.
  intros * HG Hl HW.
  destruct (decl_of_lookup _ _ _ _ _ HG Hl) as [HD Hc].
  destruct (ind_ty_typed _ _ _ _ HD Hc HG) as [j Hj].
  split; [ econstructor; eassumption | eapply level_of_nbe; eassumption ].
Qed.

Lemma con_ty_post : forall G p D c gs W, ⊢ G -> ind_lookup gc_deps gc_stack p = Some D -> ind_con D c = Some gs ->
    nbe_ty_f G (con_ty p D gs) W ->
    G ⊢a a_con p c ⟹ W /\ (exists UA u, G ⊢a W ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ W : Typeω@i).
Proof.
  intros * HG Hl Hcon HW.
  destruct (decl_of_lookup _ _ _ _ _ HG Hl) as [HD Hc].
  destruct (con_ty_typed _ _ _ _ _ _ _ HD Hc Hl Hcon HG) as [j Hj].
  split; [ econstructor; eassumption | eapply level_of_nbe; eassumption ].
Qed.

Definition ind_infer G (HG : ⊢ G) (P : tenv G) p :
  { A : nf | G ⊢a a_ind p ⟹ A /\ (exists UA u, G ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ A : Typeω@i) }
  + { forall A, ~ G ⊢a a_ind p ⟹ A }.
Proof.
  destruct (ind_lookup gc_deps gc_stack p) as [D |] eqn:Hl.
  - refine (let (W, HW) := nbe_ty_env_impl gc_deps gc_stack G P (ind_ty D) (ind_ty_order G p D HG Hl) in
            inleft (exist _ W (ind_ty_post G p D W HG Hl HW))).
  - right; intros A H; inversion H; congruence.
Defined.

Definition con_infer G (HG : ⊢ G) (P : tenv G) p c :
  { A : nf | G ⊢a a_con p c ⟹ A /\ (exists UA u, G ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ A : Typeω@i) }
  + { forall A, ~ G ⊢a a_con p c ⟹ A }.
Proof.
  destruct (ind_lookup gc_deps gc_stack p) as [D |] eqn:Hl; [| right; intros A H; inversion H; congruence ].
  destruct (ind_con D c) as [gs |] eqn:Hcon; [| right; intros A H; inversion H; subst; congruence ].
  refine (let (W, HW) := nbe_ty_env_impl gc_deps gc_stack G P (con_ty p D gs) (con_ty_order G p D c gs HG Hl Hcon) in
          inleft (exist _ W (con_ty_post G p D c gs W HG Hl Hcon HW))).
Defined.

(** ** The Eliminator *)

Lemma elim_res_order : forall G M p Rs D A UA u,
    ⊢ G -> G ⊢a M ⟹ nf_indty p Rs -> ind_lookup gc_deps gc_stack p = Some D ->
    List.length (nfs_to_exps Rs) = ind_np D ->
    elim_mctx p D (List.firstn (ind_nu D) (nfs_to_exps Rs)) ++ G ⊢a A ⟹ UA -> is_univ_nf UA u ->
    nbe_ty_order gc_deps gc_stack G A[sb_of_list Id (List.skipn (ind_nu D) (nfs_to_exps Rs) ++ M :: nil)].
Proof.
  intros * HG HMi Hl HRl HAi Hu.
  destruct (alg_elim_res_typed _ _ _ _ _ _ _ _ HG HMi Hl HRl HAi Hu) as [k Hk].
  destruct (soundness_ty Hk) as [W [HW _]].
  eapply nbe_ty_order_sound; exact HW.
Qed.

(** The head of an eliminator split into the module it names and the
    arguments it carries. *)
Fixpoint me_unapps (H : modexp) : (modexp * list exp)%type :=
  match H with
  | me_app H' N => let (H0, Ns) := me_unapps H' in (H0, Ns ++ N :: nil)
  | _ => (H, nil)
  end.

Lemma me_unapps_spec : forall H, H = me_apps (fst (me_unapps H)) (snd (me_unapps H)) /\ me_noapp (fst (me_unapps H)).
Proof.
  induction H as [| | | H IH N |]; cbn; try (split; [ reflexivity | exact I ]).
  destruct (me_unapps H) as [H0 Ns]; cbn in *; destruct IH as [-> Hn].
  rewrite me_apps_snoc; split; [ reflexivity | exact Hn ].
Qed.

(** The parameters at which the type former at the head is checked: the
    first ones of the scrutinee's type. *)
Lemma elim_head_typed : forall G p D Rs k,
    ⊢ G -> ind_lookup gc_deps gc_stack p = Some D -> G ⊢ nf_indty p Rs : Typeω@k ->
    List.length (nfs_to_exps Rs) = ind_np D -> forall nh, nh <= ind_nu D ->
    (exists i, G ⊢ ind_ty_at D (List.firstn nh (nfs_to_exps Rs)) : Typeω@i) /\
    G ⊢ apps (a_ind p) (List.firstn nh (nfs_to_exps Rs)) : ind_ty_at D (List.firstn nh (nfs_to_exps Rs)).
Proof.
  intros * HG Hl HT HRl nh Hnh.
  destruct (decl_of_lookup _ _ _ _ _ HG Hl) as [HD Hc].
  pose proof (decl_closed_nu D Hc) as Hnu.
  pose proof (wf_ind_apps_inv _ _ _ _ _ Hl HT HRl) as HRt.
  destruct (wf_exp_eq_ind_apps_at _ _ _ (nfs_to_exps Rs) (nfs_to_exps Rs) nh HD Hc Hl HG HRl HRl
              ltac:(intros * H1 H2 H3; rewrite H1 in H2; injection H2 as <-; eapply wf_exp_eq_refl, HRt; eassumption)
              ltac:(lia)) as [He _].
  destruct (presup_exp_eq He) as (_ & HA & _ & HTy).
  split; [ exact HTy | exact HA ].
Qed.

(** The inversion of an eliminator, at the scrutinee's inferred type: the
    rule at the canonical head ([ati_elim]), reached directly or from a head
    resolving to it ([ati_elim_head]). *)
Lemma ati_elim_at : forall G H nm A Bs M T p Rs,
    G ⊢a a_elim H nm A Bs M ⟹ T -> G ⊢a M ⟹ nf_indty p Rs ->
    exists D UA u,
      ind_lookup gc_deps gc_stack p = Some D /\
      List.length (nfs_to_exps Rs) = ind_np D /\
      nm = S (ind_nn D) /\
      elim_mctx p D (List.firstn (ind_nu D) (nfs_to_exps Rs)) ++ G ⊢a A ⟹ UA /\
      is_univ_nf UA u /\
      brs_names (ind_cons D) Bs /\
      (forall c gs n B, ind_con D c = Some gs -> List.In (c, n, B) Bs ->
         n = (ind_nn D + List.length gs + cargs_nrec gs)%nat) /\
      (forall c gs n B, ind_con D c = Some gs -> List.In (c, n, B) Bs ->
         elim_bctx p D gs A (List.firstn (ind_nu D) (nfs_to_exps Rs)) ++ G
           ⊢a B ⟸ elim_bty p D c gs A (List.firstn (ind_nu D) (nfs_to_exps Rs))) /\
      nbe_ty_f G A[sb_of_list Id (List.skipn (ind_nu D) (nfs_to_exps Rs) ++ M :: nil)] T /\
      exists H0 Ns W,
        H = me_apps H0 Ns /\ me_noapp H0 /\ List.length Ns <= ind_nu D /\
        G ⊢a apps (a_ind p) Ns ⟸ ind_ty_at D (List.firstn (List.length Ns) (nfs_to_exps Rs)) /\
        nbe_f G (apps (a_ind p) Ns) (ind_ty_at D (List.firstn (List.length Ns) (nfs_to_exps Rs))) W /\
        nbe_f G (apps (a_ind p) (List.firstn (List.length Ns) (nfs_to_exps Rs)))
          (ind_ty_at D (List.firstn (List.length Ns) (nfs_to_exps Rs))) W /\
        (H0 = qname_mod p \/
         (H0 <> qname_mod p /\ G ⊢aᵐ H0 /\ exists T0, member_type gc_deps gc_stack G H0 nil (mr_ind p T0))).
Proof.
  intros * Hd HM.
  inversion Hd; subst.
  - match goal with
    | H1 : _ ⊢a ?M0 ⟹ nf_indty ?p0 _, H2 : _ ⊢a ?M0 ⟹ nf_indty ?p1 _ |- _ =>
        assert_fails constr_eq p0 p1;
        pose proof (functional_alg_type_infer H1 H2) as Heq; injection Heq; intros; subst
    end.
    exists D, UA, u; do 9 (split; [ first [ eassumption | reflexivity ] |]).
    exists (qname_mod p0), Ns, W; do 6 (split; [ first [ reflexivity | apply qname_mod_noapp | eassumption ] |]).
    left; reflexivity.
  - match goal with
    | Hm : member_type _ _ _ ?H0 nil (mr_ind ?p0 _), Hi : _ ⊢a a_elim (me_apps (qname_mod ?p0) ?Ns) _ _ _ _ ⟹ _ |- _ =>
        rename Hm into Hm0; rename Hi into Hi0
    end.
    inversion Hi0; subst.
    + match goal with
      | H1 : _ ⊢a ?M0 ⟹ nf_indty ?p0 _, H2 : _ ⊢a ?M0 ⟹ nf_indty ?p1 _ |- _ =>
          assert_fails constr_eq p0 p1;
          pose proof (functional_alg_type_infer H1 H2) as Heq; injection Heq; intros; subst
      end.
      match goal with Hq : me_apps (qname_mod ?a) ?N1 = me_apps (qname_mod ?b) ?N2 |- _ =>
        destruct (me_apps_inj _ _ _ _ (qname_mod_noapp _) (qname_mod_noapp _) Hq) as [Eq <-];
        assert (a = b) as <- by (apply (f_equal mod_qname) in Eq; rewrite !qname_mod_qname in Eq; injection Eq; auto) end.
      eexists _, _, _; do 9 (split; [ first [ eassumption | reflexivity ] |]).
      eexists _, _, _; do 6 (split; [ first [ reflexivity | exact (member_type_ind_noapp' _ _ _ _ _ _ Hm0) | eassumption ] |]).
      right; split; [ assumption | split; [ assumption | eexists; exact Hm0 ] ].
    + exfalso.
      match goal with
      | Hq : me_apps (qname_mod ?p0) ?N1 = me_apps ?H2 ?N2, Hm : member_type _ _ _ ?H2 nil (mr_ind ?p2 _),
        Hn : ?H2 <> qname_mod ?p2 |- _ =>
          destruct (me_apps_inj _ _ _ _ (qname_mod_noapp _) (member_type_ind_noapp' _ _ _ _ _ _ Hm) Hq) as [<- _];
          destruct (proj1 (member_type_ind_canon _ _) _ _ _ _ Hm0 _ _ eq_refl) as (T' & D' & Hp);
          apply Hn; rewrite (path_ind_self _ _ _ _ _ _ _ _ Hp Hm); reflexivity
      end.
Qed.

(** An eliminator's scrutinee infers an inductive type. *)
Lemma ati_elim_inf : forall G H nm A Bs M T,
    G ⊢a a_elim H nm A Bs M ⟹ T -> exists p Rs, G ⊢a M ⟹ nf_indty p Rs.
Proof.
  intros * Hd; inversion Hd; subst; eauto.
  match goal with
  | Hm : member_type _ _ _ ?H0 nil (mr_ind ?p0 _), Hi : _ ⊢a a_elim (me_apps (qname_mod ?p0) ?Ns) _ _ _ _ ⟹ _ |- _ =>
      rename Hm into Hm0; rename Hi into Hi0
  end.
  inversion Hi0; subst; eauto.
  exfalso.
  match goal with
  | Hq : me_apps (qname_mod ?p0) ?N1 = me_apps ?H2 ?N2, Hm : member_type _ _ _ ?H2 nil (mr_ind ?p2 _),
    Hn : ?H2 <> qname_mod ?p2 |- _ =>
      destruct (me_apps_inj _ _ _ _ (qname_mod_noapp _) (member_type_ind_noapp' _ _ _ _ _ _ Hm) Hq) as [<- _];
      destruct (proj1 (member_type_ind_canon _ _) _ _ _ _ Hm0 _ _ eq_refl) as (T' & D' & Hp);
      apply Hn; rewrite (path_ind_self _ _ _ _ _ _ _ _ Hp Hm); reflexivity
  end.
Qed.

Definition elim_infer G (HG : ⊢ G) (P : tenv G) H nm A (Bs : list (string * nat * exp)) M
  (rM : { T : nf | G ⊢a M ⟹ T /\ (exists UA u, G ⊢a T ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ T : Typeω@i) }
        + { forall T, ~ G ⊢a M ⟹ T })
  (infA : forall G' (HG' : ⊢ G') (P' : tenv G'),
      { UA : nf | G' ⊢a A ⟹ UA /\ (exists UB u, G' ⊢a UA ⟹ UB /\ is_univ_nf UB u) /\ (exists i : nat, G' ⊢ UA : Typeω@i) }
      + { forall UA, ~ G' ⊢a A ⟹ UA })
  (chkB : forall b, In b Bs -> forall G' A' (HA' : exists i, G' ⊢ A' : Typeω@i) (P' : tenv G'),
      { G' ⊢a snd b ⟸ A' } + { ~ G' ⊢a snd b ⟸ A' })
  (chkH0 : forall H0 Ns, H = me_apps H0 Ns -> { G ⊢aᵐ H0 } + { ~ G ⊢aᵐ H0 })
  (chkN : forall H0 Ns p A', H = me_apps H0 Ns -> (exists i, G ⊢ A' : Typeω@i) ->
      { G ⊢a apps (a_ind p) Ns ⟸ A' } + { ~ G ⊢a apps (a_ind p) Ns ⟸ A' }) :
  { T : nf | G ⊢a a_elim H nm A Bs M ⟹ T /\ (exists UA u, G ⊢a T ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ T : Typeω@i) }
  + { forall T, ~ G ⊢a a_elim H nm A Bs M ⟹ T }.
Proof.
  destruct rM as [[T (HMi & _ & HTt)] | HnM];
    [| right; intros T H'; destruct (ati_elim_inf _ _ _ _ _ _ _ H') as (? & ? & HM'); eapply HnM; exact HM' ].
  destruct (get_indty_nf T) as [[p [Rs ->]] | HnI];
    [| right; intros T' H'; destruct (ati_elim_inf _ _ _ _ _ _ _ H') as (p0 & Rs0 & HM');
       pose proof (functional_alg_type_infer HM' HMi) as Heq; symmetry in Heq; eapply HnI; exact Heq ].
  destruct (ind_lookup gc_deps gc_stack p) as [D |] eqn:Hl;
    [| right; intros T' H'; destruct (ati_elim_at _ _ _ _ _ _ _ _ _ H' HMi) as (D' & ? & ? & HD' & _); congruence ].
  pose (Us := List.firstn (ind_nu D) (nfs_to_exps Rs)).
  destruct (Nat.eq_dec (List.length (nfs_to_exps Rs)) (ind_np D)) as [HRl | HRl];
    [| right; intros T' H'; destruct (ati_elim_at _ _ _ _ _ _ _ _ _ H' HMi) as (D' & ? & ? & HD' & ? & _);
       rewrite Hl in HD'; injection HD' as <-; contradiction ].
  destruct (Nat.eq_dec nm (S (ind_nn D))) as [Hnm | Hnm];
    [| right; intros T' H'; destruct (ati_elim_at _ _ _ _ _ _ _ _ _ H' HMi) as (D' & ? & ? & HD' & ? & ? & _);
       rewrite Hl in HD'; injection HD' as <-; contradiction ].
  pose proof (alg_elim_mctx_wf _ _ _ _ _ HG HMi Hl HRl) as HMs.
  destruct (infA _ HMs (tenv_of _ HMs)) as [[UA (HAi & _)] | HnA];
    [| right; intros T' H'; destruct (ati_elim_at _ _ _ _ _ _ _ _ _ H' HMi) as (D' & ? & ? & HD' & ? & ? & ? & _);
       rewrite Hl in HD'; injection HD' as <-; eapply HnA; eassumption ].
  destruct (univ_nf_idx_dec UA) as [[u Hu] | Hnu];
    [| right; intros T' H'; destruct (ati_elim_at _ _ _ _ _ _ _ _ _ H' HMi) as (D' & UA' & u' & HD' & ? & ? & HAi' & Hu' & _);
       rewrite Hl in HD'; injection HD' as <-;
       rewrite (functional_alg_type_infer HAi HAi') in Hnu; eapply Hnu; exact Hu' ].
  destruct (list_eq_dec string_dec (List.map fst (ind_cons D)) (List.map (fun b => fst (fst b)) Bs)) as [HBn | HBn];
    [| right; intros T' H'; destruct (ati_elim_at _ _ _ _ _ _ _ _ _ H' HMi) as (D' & ? & ? & HD' & ? & ? & ? & ? & HBn' & _);
       rewrite Hl in HD'; injection HD' as <-; contradiction ].
  (** The arities of the branches. *)
  assert (fa : forall b, In b Bs -> {forall gs, ind_con D (fst (fst b)) = Some gs ->
                                       snd (fst b) = (ind_nn D + List.length gs + cargs_nrec gs)%nat}
                                   + {~ forall gs, ind_con D (fst (fst b)) = Some gs ->
                                       snd (fst b) = (ind_nn D + List.length gs + cargs_nrec gs)%nat}).
  { intros b _.
    destruct (ind_con D (fst (fst b))) as [gs |]; [| left; intros ? [=] ].
    destruct (Nat.eq_dec (snd (fst b)) (ind_nn D + List.length gs + cargs_nrec gs)) as [E | E].
    - left; intros ? [= <-]; exact E.
    - right; intros H'; exact (E (H' gs eq_refl)). }
  destruct (forall_in_dec _ Bs fa) as [HBa | HBa];
    [| right; intros T' H'; destruct (ati_elim_at _ _ _ _ _ _ _ _ _ H' HMi) as (D' & ? & ? & HD' & ? & ? & ? & ? & ? & HBa' & _);
       rewrite Hl in HD'; injection HD' as <-;
       apply HBa; intros [[c n] B] Hin gs Hcon; exact (HBa' _ _ _ _ Hcon Hin) ].
  (** The branches. *)
  assert (fb : forall b, In b Bs -> {forall gs, ind_con D (fst (fst b)) = Some gs ->
                                       elim_bctx p D gs A Us ++ G ⊢a snd b ⟸ elim_bty p D (fst (fst b)) gs A Us}
                                   + {~ forall gs, ind_con D (fst (fst b)) = Some gs ->
                                       elim_bctx p D gs A Us ++ G ⊢a snd b ⟸ elim_bty p D (fst (fst b)) gs A Us}).
  { intros b Hb.
    destruct (ind_con D (fst (fst b))) as [gs |] eqn:Hcon; [| left; intros ? [=] ].
    pose proof (alg_elim_bty_typed _ _ _ _ _ _ _ _ _ _ HG HMi Hl HRl HAi Hu Hcon) as HT.
    destruct (chkB b Hb (elim_bctx p D gs A Us ++ G) (elim_bty p D (fst (fst b)) gs A Us) HT
                (tenv_of _ (tenv_ctx_of_typ _ _ HT))) as [E | E].
    - left; intros ? [= <-]; exact E.
    - right; intros H'; exact (E (H' gs eq_refl)). }
  destruct (forall_in_dec _ Bs fb) as [HBc | HBc];
    [| right; intros T' H'; destruct (ati_elim_at _ _ _ _ _ _ _ _ _ H' HMi) as (D' & ? & ? & HD' & ? & ? & ? & ? & ? & ? & HBc' & _);
       rewrite Hl in HD'; injection HD' as <-;
       apply HBc; intros [[c n] B] Hin gs Hcon; exact (HBc' _ _ _ _ Hcon Hin) ].
  (** The head: the module it names, and the type former at its arguments,
      checked at the first parameters of the scrutinee's type and equal to
      the type former at those. *)
  pose proof (me_unapps_spec H) as HHs.
  destruct (me_unapps H) as [H0 Ns] eqn:Eu; cbn [fst snd] in HHs; destruct HHs as [EH HH0n].
  assert (Hhd : forall T', G ⊢a a_elim H nm A Bs M ⟹ T' ->
            exists W, List.length Ns <= ind_nu D /\
              G ⊢a apps (a_ind p) Ns ⟸ ind_ty_at D (List.firstn (List.length Ns) (nfs_to_exps Rs)) /\
              nbe_f G (apps (a_ind p) Ns) (ind_ty_at D (List.firstn (List.length Ns) (nfs_to_exps Rs))) W /\
              nbe_f G (apps (a_ind p) (List.firstn (List.length Ns) (nfs_to_exps Rs)))
                (ind_ty_at D (List.firstn (List.length Ns) (nfs_to_exps Rs))) W /\
              (H0 = qname_mod p \/
               (H0 <> qname_mod p /\ G ⊢aᵐ H0 /\ exists T0, member_type gc_deps gc_stack G H0 nil (mr_ind p T0)))).
  { intros T' H'; destruct (ati_elim_at _ _ _ _ _ _ _ _ _ H' HMi)
      as (D' & ? & ? & HD' & _ & _ & _ & _ & _ & _ & _ & _ & H0' & Ns' & W & EH' & Hn' & Hrest).
    rewrite Hl in HD'; injection HD' as <-.
    rewrite EH in EH'; destruct (me_apps_inj _ _ _ _ HH0n Hn' EH') as [<- <-].
    exists W; exact Hrest. }
  destruct (Compare_dec.le_dec (List.length Ns) (ind_nu D)) as [Hnh | Hnh];
    [| right; intros T' H'; destruct (Hhd _ H') as (? & ? & _); contradiction ].
  assert (HTA : (exists i, G ⊢ ind_ty_at D (List.firstn (List.length Ns) (nfs_to_exps Rs)) : Typeω@i) /\
                G ⊢ apps (a_ind p) (List.firstn (List.length Ns) (nfs_to_exps Rs))
                  : ind_ty_at D (List.firstn (List.length Ns) (nfs_to_exps Rs)))
    by (destruct HTt as [kT HTt]; exact (elim_head_typed _ _ _ _ _ HG Hl HTt HRl (List.length Ns) Hnh)).
  destruct HTA as [HTs HAR].
  destruct (chkN H0 Ns p _ EH HTs) as [HNc | HNc];
    [| right; intros T' H'; destruct (Hhd _ H') as (? & _ & ? & _); contradiction ].
  pose (Ts := ind_ty_at D (List.firstn (List.length Ns) (nfs_to_exps Rs))).
  pose (Rh := List.firstn (List.length Ns) (nfs_to_exps Rs)).
  assert (Ho1 : nbe_order gc_deps gc_stack G (apps (a_ind p) Ns) Ts).
  { destruct HTs as [iT HTs']; pose proof (alg_type_check_sound HNc HG HTs') as HN.
    destruct (soundness HN) as (W & HW & _); eapply nbe_order_sound; exact HW. }
  assert (Ho2 : nbe_order gc_deps gc_stack G (apps (a_ind p) Rh) Ts).
  { destruct (soundness HAR) as (W & HW & _); eapply nbe_order_sound; exact HW. }
  destruct (nbe_env_impl gc_deps gc_stack G P _ _ Ho1) as [W1 HW1].
  destruct (nbe_env_impl gc_deps gc_stack G P _ _ Ho2) as [W2 HW2].
  destruct (nf_eq_dec W1 W2) as [<- | HW];
    [| right; intros T' H'; destruct (Hhd _ H') as (W & _ & _ & HW1' & HW2' & _);
       apply HW; rewrite (functional_nbe _ _ _ _ _ HW1 HW1'), (functional_nbe _ _ _ _ _ HW2 HW2'); reflexivity ].
  (** The result, from the canonical head. *)
  assert (Hcan : { T' : nf | G ⊢a a_elim (me_apps (qname_mod p) Ns) nm A Bs M ⟹ T' /\
                   (exists UA u, G ⊢a T' ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ T' : Typeω@i) }).
  { refine (let (T', HT') := nbe_ty_env_impl gc_deps gc_stack G P
                               A[sb_of_list Id (List.skipn (ind_nu D) (nfs_to_exps Rs) ++ M :: nil)]
                               (elim_res_order _ _ _ _ _ _ _ _ HG HMi Hl HRl HAi Hu) in
            exist _ T' _).
    destruct (alg_elim_res_typed _ _ _ _ _ _ _ _ HG HMi Hl HRl HAi Hu) as [k Hk].
    split; [| eapply level_of_nbe; eassumption ].
    eapply ati_elim; try reflexivity; try eassumption.
    - intros c gs n B Hcon Hin; exact (HBa _ Hin gs Hcon).
    - intros c gs n B Hcon Hin; exact (HBc _ Hin gs Hcon). }
  destruct (IndClassify.modexp_eq_dec H0 (qname_mod p)) as [-> | Hne].
  { left; rewrite EH; exact Hcan. }
  (** A head other than the canonical one: it is a module, and resolves to
      the scrutinee's type. *)
  destruct (chkH0 H0 Ns EH) as [HHa | HHa];
    [| right; intros T' H'; destruct (Hhd _ H') as (? & _ & _ & _ & _ & [? | (_ & ? & _)]); contradiction ].
  pose proof (alg_modexp_sound HHa HG) as HHw.
  destruct (member_type_dec (ctx_wf_gctx _ _ _ HG) G H0 nil HHw) as [[R HR] | HnR];
    [| right; intros T' H'; destruct (Hhd _ H') as (? & _ & _ & _ & _ & [? | (_ & _ & T0 & HT0)]);
       [ contradiction | eapply HnR; exact HT0 ] ].
  destruct R as [A0 | T0 | p' T0];
    try solve [ right; intros T' H'; destruct (Hhd _ H') as (? & _ & _ & _ & _ & [? | (_ & _ & T1 & HT1)]);
                [ contradiction | pose proof (proj1 (member_type_functional _ _) _ _ _ _ HR _ HT1); discriminate ] ].
  destruct (qname_eq_dec p' p) as [-> | Hp'];
    [| right; intros T' H'; destruct (Hhd _ H') as (? & _ & _ & _ & _ & [? | (_ & _ & T1 & HT1)]);
       [ contradiction | pose proof (proj1 (member_type_functional _ _) _ _ _ _ HR _ HT1) as E;
                         injection E; intros; contradiction ] ].
  destruct Hcan as [T' (HT' & HT'2)].
  left; exists T'; split; [| exact HT'2 ].
  rewrite EH; eapply ati_elim_head; [ exact HHa | exact HR | exact Hne | reflexivity | exact HT' ].
Defined.
End Fixed_GCtx.
