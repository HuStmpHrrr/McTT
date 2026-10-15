From Stdlib Require Import List ListDec String PeanoNat.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing Strengthening.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import Consequences.
From Mctt.Extraction Require Import Lookup NbE PseudoMonadic TypeCheckBase.
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
Context {GC : GCtx} {F : FCtx gc_deps gc_stack}.

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
  destruct (ind_lookup_f gc_deps gc_stack p) as [[D |] Hl].
  - refine (let (W, HW) := nbe_ty_env_impl gc_deps gc_stack G P (ind_ty D) (ind_ty_order G p D HG Hl) in
            inleft (exist _ W (ind_ty_post G p D W HG Hl HW))).
  - right; intros A H; inversion H; congruence.
Defined.

Definition con_infer G (HG : ⊢ G) (P : tenv G) p c :
  { A : nf | G ⊢a a_con p c ⟹ A /\ (exists UA u, G ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ A : Typeω@i) }
  + { forall A, ~ G ⊢a a_con p c ⟹ A }.
Proof.
  destruct (ind_lookup_f gc_deps gc_stack p) as [[D |] Hl]; [| right; intros A H; inversion H; congruence ].
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

(** The inversion of [ati_elim], at the scrutinee's inferred type. *)
Lemma ati_elim_at : forall G nm A Bs M T p Rs,
    G ⊢a a_elim nm A Bs M ⟹ T -> G ⊢a M ⟹ nf_indty p Rs ->
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
      nbe_ty_f G A[sb_of_list Id (List.skipn (ind_nu D) (nfs_to_exps Rs) ++ M :: nil)] T.
Proof.
  intros * H HM.
  inversion H; subst.
  match goal with H1 : G ⊢a M ⟹ nf_indty ?p0 ?Rs0 |- _ =>
    pose proof (functional_alg_type_infer H1 HM) as Heq; injection Heq as -> -> end.
  do 3 eexists; repeat split; eassumption.
Qed.

Definition elim_infer G (HG : ⊢ G) (P : tenv G) nm A (Bs : list (string * nat * exp)) M
  (rM : { T : nf | G ⊢a M ⟹ T /\ (exists UA u, G ⊢a T ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ T : Typeω@i) }
        + { forall T, ~ G ⊢a M ⟹ T })
  (infA : forall G' (HG' : ⊢ G') (P' : tenv G'),
      { UA : nf | G' ⊢a A ⟹ UA /\ (exists UB u, G' ⊢a UA ⟹ UB /\ is_univ_nf UB u) /\ (exists i : nat, G' ⊢ UA : Typeω@i) }
      + { forall UA, ~ G' ⊢a A ⟹ UA })
  (chkB : forall b, In b Bs -> forall G' A' (HA' : exists i, G' ⊢ A' : Typeω@i) (P' : tenv G'),
      { G' ⊢a snd b ⟸ A' } + { ~ G' ⊢a snd b ⟸ A' }) :
  { T : nf | G ⊢a a_elim nm A Bs M ⟹ T /\ (exists UA u, G ⊢a T ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ T : Typeω@i) }
  + { forall T, ~ G ⊢a a_elim nm A Bs M ⟹ T }.
Proof.
  destruct rM as [[T (HMi & _ & _)] | HnM];
    [| right; intros T H; inversion H; subst; eapply HnM; eassumption ].
  destruct (get_indty_nf T) as [[p [Rs ->]] | HnI];
    [| right; intros T' H; inversion H; subst;
       match goal with H1 : G ⊢a M ⟹ nf_indty _ _ |- _ =>
         pose proof (functional_alg_type_infer H1 HMi) as Heq end;
       symmetry in Heq; eapply HnI; exact Heq ].
  destruct (ind_lookup_f gc_deps gc_stack p) as [[D |] Hl];
    [| right; intros T' H; destruct (ati_elim_at _ _ _ _ _ _ _ _ H HMi) as (D' & ? & ? & HD' & _); congruence ].
  pose (Us := List.firstn (ind_nu D) (nfs_to_exps Rs)).
  destruct (Nat.eq_dec (List.length (nfs_to_exps Rs)) (ind_np D)) as [HRl | HRl];
    [| right; intros T' H; destruct (ati_elim_at _ _ _ _ _ _ _ _ H HMi) as (D' & ? & ? & HD' & ? & _);
       rewrite Hl in HD'; injection HD' as <-; contradiction ].
  destruct (Nat.eq_dec nm (S (ind_nn D))) as [Hnm | Hnm];
    [| right; intros T' H; destruct (ati_elim_at _ _ _ _ _ _ _ _ H HMi) as (D' & ? & ? & HD' & ? & ? & _);
       rewrite Hl in HD'; injection HD' as <-; contradiction ].
  pose proof (alg_elim_mctx_wf _ _ _ _ _ HG HMi Hl HRl) as HMs.
  destruct (infA _ HMs (tenv_ext G P _ HMs)) as [[UA (HAi & _)] | HnA];
    [| right; intros T' H; destruct (ati_elim_at _ _ _ _ _ _ _ _ H HMi) as (D' & ? & ? & HD' & ? & ? & ? & _);
       rewrite Hl in HD'; injection HD' as <-; eapply HnA; eassumption ].
  destruct (univ_nf_idx_dec UA) as [[u Hu] | Hnu];
    [| right; intros T' H; destruct (ati_elim_at _ _ _ _ _ _ _ _ H HMi) as (D' & UA' & u' & HD' & ? & ? & HAi' & Hu' & _);
       rewrite Hl in HD'; injection HD' as <-;
       rewrite (functional_alg_type_infer HAi HAi') in Hnu; eapply Hnu; exact Hu' ].
  destruct (list_eq_dec string_dec (List.map fst (ind_cons D)) (List.map (fun b => fst (fst b)) Bs)) as [HBn | HBn];
    [| right; intros T' H; destruct (ati_elim_at _ _ _ _ _ _ _ _ H HMi) as (D' & ? & ? & HD' & ? & ? & ? & ? & HBn' & _);
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
    - right; intros H; exact (E (H gs eq_refl)). }
  destruct (forall_in_dec _ Bs fa) as [HBa | HBa];
    [| right; intros T' H; destruct (ati_elim_at _ _ _ _ _ _ _ _ H HMi) as (D' & ? & ? & HD' & ? & ? & ? & ? & ? & HBa' & _);
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
                (tenv_ext G P _ (tenv_ctx_of_typ _ _ HT))) as [E | E].
    - left; intros ? [= <-]; exact E.
    - right; intros H; exact (E (H gs eq_refl)). }
  destruct (forall_in_dec _ Bs fb) as [HBc | HBc];
    [| right; intros T' H; destruct (ati_elim_at _ _ _ _ _ _ _ _ H HMi) as (D' & ? & ? & HD' & ? & ? & ? & ? & ? & ? & HBc' & _);
       rewrite Hl in HD'; injection HD' as <-;
       apply HBc; intros [[c n] B] Hin gs Hcon; exact (HBc' _ _ _ _ Hcon Hin) ].
  refine (let (T', HT') := nbe_ty_env_impl gc_deps gc_stack G P
                             A[sb_of_list Id (List.skipn (ind_nu D) (nfs_to_exps Rs) ++ M :: nil)]
                             (elim_res_order _ _ _ _ _ _ _ _ HG HMi Hl HRl HAi Hu) in
          inleft (exist _ T' _)).
  destruct (alg_elim_res_typed _ _ _ _ _ _ _ _ HG HMi Hl HRl HAi Hu) as [k Hk].
  split; [| eapply level_of_nbe; eassumption ].
  eapply ati_elim; try eassumption.
  - intros c gs n B Hcon Hin; exact (HBa _ Hin gs Hcon).
  - intros c gs n B Hcon Hin; exact (HBc _ Hin gs Hcon).
Defined.

End Fixed_GCtx.
