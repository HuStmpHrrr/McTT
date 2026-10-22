From Stdlib Require Import Arith List ListDec String PeanoNat Lia.
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
    its scrutinee, its uniform parameters, and the annotations, motives and
    branches of its blocks, and takes those recursive calls as arguments,
    so that the mutual fixpoints of the checkers only pass them on. *)

(** ** Deciding Properties of Lists and of Indices *)

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

(** Whether a property holds of every index below [n], from a decision for
    each index that may assume it of the indices below. *)
Definition forall_lt_dec (Q : nat -> Prop) :
  forall n, (forall j, j < n -> (forall j', j' < j -> Q j') -> {Q j} + {~ Q j}) ->
    {forall j, j < n -> Q j} + {~ forall j, j < n -> Q j}.
Proof.
  fix go 1; intros [| n] f.
  - left; intros; lia.
  - destruct (go n (fun j Hj H => f j ltac:(lia) H)) as [Hn | Hn];
      [| right; intros H; apply Hn; intros j Hj; apply H; lia ].
    destruct (f n ltac:(lia) Hn) as [Hq | Hq]; [ left | right ].
    + intros j Hj; destruct (Nat.eq_dec j n) as [-> | Hne]; [ exact Hq | apply Hn; lia ].
    + intros H; apply Hq, H; lia.
Defined.

(** One bound for a property monotone in it at every index below [n], from
    a bound at each index or its absence. *)
Definition bound_lt_dec (Q : nat -> nat -> Prop) (Hmono : forall j l l', l <= l' -> Q j l -> Q j l') :
  forall n, (forall j, j < n -> {l | Q j l} + {forall l, ~ Q j l}) ->
    {L | forall j, j < n -> Q j L} + {forall L, ~ forall j, j < n -> Q j L}.
Proof.
  fix go 1; intros [| n] f.
  - left; exists 0; intros; lia.
  - destruct (go n (fun j Hj => f j ltac:(lia))) as [[L HL] | HL];
      [| right; intros L H; apply (HL L); intros j Hj; apply H; lia ].
    destruct (f n ltac:(lia)) as [[l Hl] | Hl]; [ left; exists (Nat.max L l) | right; intros L' H; exact (Hl L' (H n ltac:(lia))) ].
    intros j Hj; destruct (Nat.eq_dec j n) as [-> | Hne];
      [ eapply Hmono; [| exact Hl ]; lia | eapply Hmono; [| apply HL; lia ]; lia ].
Defined.

(** The lookups that name one thing name it once: two hypotheses that the
    same lookup returns two things make them one. *)
Ltac unify_lookups :=
  repeat match goal with
    | H1 : ?f ?x = Some ?a, H2 : ?f ?x = Some ?b |- _ =>
        assert_fails (constr_eq a b); rewrite H1 in H2; injection H2; clear H2; intros; subst
    end.

Section Fixed_GCtx.
Context {GC : GCtx} {F : FCtx gc_deps gc_stack}.

(** Whether a normal form is an instance of the type former of a member. *)
#[derive(equations=no,eliminator=no)]
Equations get_indty_nf (A : nf) : { p & { k & { Rs | A = nf_indty p k Rs } } } + { forall p k Rs, A <> nf_indty p k Rs } :=
| nf_indty p k Rs => pureo (existT _ p (existT _ k (exist _ Rs _)))
| _ => inright _
.

Extraction Inline get_indty_nf.

(** ** The Type Former and the Constructors *)

Lemma ind_ty_post : forall G p D k Mk W, ⊢ G -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    k < ind_ndecl D -> nbe_ty_f G (ind_ty D Mk) W ->
    G ⊢a a_ind p k ⟹ W /\ (exists UA u, G ⊢a W ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ W : Typeω@i).
Proof.
  intros * HG Hl Hk Hlt HW.
  destruct (decl_of_lookup _ _ _ _ _ HG Hl) as [HD Hc].
  destruct (ind_ty_typed _ _ _ _ _ _ HD Hc Hk HG) as [j Hj].
  split; [ econstructor; eassumption | eapply level_of_nbe; eassumption ].
Qed.

Lemma ind_ty_order : forall G p D k Mk, ⊢ G -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    nbe_ty_order gc_deps gc_stack G (ind_ty D Mk).
Proof.
  intros * HG Hl Hk.
  destruct (decl_of_lookup _ _ _ _ _ HG Hl) as [HD Hc].
  destruct (ind_ty_typed _ _ _ _ _ _ HD Hc Hk HG) as [j Hj].
  exact (nbe_order_of_typ _ _ _ Hj).
Qed.

Lemma con_ty_post : forall G p D k Mk c gs W, ⊢ G -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    ind_con Mk c = Some gs -> nbe_ty_f G (con_ty p D k Mk gs) W ->
    G ⊢a a_con p k c ⟹ W /\ (exists UA u, G ⊢a W ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ W : Typeω@i).
Proof.
  intros * HG Hl Hk Hcon HW.
  destruct (con_ty_typed _ _ G _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HG) (decls_of_ctx _ _ _ HG) Hl Hk Hcon HG) as [j Hj].
  split; [ econstructor; eassumption | eapply level_of_nbe; eassumption ].
Qed.

Lemma con_ty_order : forall G p D k Mk c gs, ⊢ G -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    ind_con Mk c = Some gs -> nbe_ty_order gc_deps gc_stack G (con_ty p D k Mk gs).
Proof.
  intros * HG Hl Hk Hcon.
  destruct (con_ty_typed _ _ G _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HG) (decls_of_ctx _ _ _ HG) Hl Hk Hcon HG) as [j Hj].
  exact (nbe_order_of_typ _ _ _ Hj).
Qed.

(** The type former of a declared member. *)
Definition ind_infer G (HG : ⊢ G) (P : tenv G) p k :
  { A : nf | G ⊢a a_ind p k ⟹ A /\ (exists UA u, G ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ A : Typeω@i) }
  + { forall A, ~ G ⊢a a_ind p k ⟹ A }.
Proof.
  destruct (ind_lookup_f gc_deps gc_stack p) as [[D |] Hl]; [| right; intros A H; inversion H; congruence ].
  destruct (ind_member D k) as [Mk |] eqn:Hk; [| right; intros A H; inversion H; subst; unify_lookups; congruence ].
  destruct (Compare_dec.lt_dec k (ind_ndecl D)) as [Hlt | Hlt]; [| right; intros A H; inversion H; subst; unify_lookups; contradiction ].
  refine (let (W, HW) := nbe_ty_env_impl gc_deps gc_stack G P (ind_ty D Mk) (ind_ty_order G p D k Mk HG Hl Hk) in
          inleft (exist _ W (ind_ty_post G p D k Mk W HG Hl Hk Hlt HW))).
Defined.

(** A constructor of a member. *)
Definition con_infer G (HG : ⊢ G) (P : tenv G) p k c :
  { A : nf | G ⊢a a_con p k c ⟹ A /\ (exists UA u, G ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ A : Typeω@i) }
  + { forall A, ~ G ⊢a a_con p k c ⟹ A }.
Proof.
  destruct (ind_lookup_f gc_deps gc_stack p) as [[D |] Hl]; [| right; intros A H; inversion H; congruence ].
  destruct (ind_member D k) as [Mk |] eqn:Hk; [| right; intros A H; inversion H; subst; unify_lookups; congruence ].
  destruct (ind_con Mk c) as [gs |] eqn:Hcon; [| right; intros A H; inversion H; subst; unify_lookups; congruence ].
  refine (let (W, HW) := nbe_ty_env_impl gc_deps gc_stack G P (con_ty p D k Mk gs) (con_ty_order G p D k Mk c gs HG Hl Hk Hcon) in
          inleft (exist _ W (con_ty_post G p D k Mk c gs W HG Hl Hk Hcon HW))).
Defined.

(** ** The Eliminator *)

(** What [ati_elim] asks of the eliminator [a_elim oq Us m Bks M] whose
    scrutinee infers [nf_indty pc k Rs], at the group [D] at [p] it
    eliminates, its member [Mm], the declared member [Mk] of the group
    [Dq] at [pc] the member's type is headed by, the member's block [bm],
    the universe [i] of the blocks' annotations and motives, and the type
    [T] it infers. *)
Record elim_alg_ok (G : ctx) (oq : option qname) (Us : list exp) (m : nat) (Bks : list eblock) (M : exp)
    (pc : qname) (k : nat) (Rs : nfs) (p : qname) (D : ind_decl) (Mm : imember) (Dq : ind_decl) (Mk : imember)
    (bm : eblock) (i : nat) (T : nf) : Prop := mk_elim_alg_ok
  { (** The group is found at [p] *)
    eao_lookup : ind_lookup gc_deps gc_stack p = Some D
    (** It is the group the eliminator names, or the scrutinee's at a
        declared member *)
  ; eao_grp : elim_grp D oq p m
    (** The member eliminated *)
  ; eao_member : ind_member D m = Some Mm
    (** Its type is headed by the declared member [k] of the group at [pc] *)
  ; eao_ref : im_ref p m Mm = (pc, k)
    (** That group is found *)
  ; eao_ref_lookup : ind_lookup gc_deps gc_stack pc = Some Dq
    (** And that member *)
  ; eao_ref_member : ind_member Dq k = Some Mk
    (** The scrutinee's type has all its parameters *)
  ; eao_nparams : List.length (nfs_to_exps Rs) = im_np Dq Mk
    (** The member's block *)
  ; eao_block : List.nth_error Bks m = Some bm
    (** One block per member *)
  ; eao_nblocks : List.length Bks = List.length (ind_members D)
    (** One uniform parameter per uniform parameter of the group *)
  ; eao_nuparams : List.length Us = ind_nu D
    (** The uniform parameters are checked at the group's telescope *)
  ; eao_uparams : forall j U T', List.nth_error Us j = Some U ->
      List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T' -> G ⊢a U ⟸ T'
    (** The member's uniform arguments agree with the scrutinee type's *)
  ; eao_agree : nfs_agree G (im_pre Mm Us) (List.firstn (ind_nu Dq) (nfs_to_exps Rs))
      (tele_insts (ind_uparams Dq) Id (im_pre Mm Us))
    (** Each block binds the non-uniform parameters and the scrutinee *)
  ; eao_nm : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_nm b = S (im_nn Mj)
    (** The annotations are checked at the universe *)
  ; eao_ann_typ : forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
      tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G ⊢a Z ⟸ Typeω@i
    (** Each annotation is its member's type *)
  ; eao_ann_conv : forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
      alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G) Z
        (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))
    (** The motives are checked at the universe *)
  ; eao_motive : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
      elim_mctx p D j Mj Us ++ G ⊢a eb_motive b ⟸ Typeω@i
    (** Each block has one branch per constructor, in order *)
  ; eao_names : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b)
    (** Each branch binds its constructor's arguments and recursive results *)
  ; eao_counts : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
      ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec gs)%nat
    (** The branches are checked at their types *)
  ; eao_branches : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
      ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
      elim_bctx p D Mj gs (blocks_motives Bks) Us ++ G ⊢a B ⟸ elim_bty p j Mj c gs (eb_motive b) Us
    (** The type is the normal form of the motive's instance *)
  ; eao_nbe : nbe_ty_f G (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu Dq) (nfs_to_exps Rs) ++ M :: nil)] T }.

(** The inversion of [ati_elim], at the scrutinee's inferred type. *)
Lemma ati_elim_inv : forall G oq Us m Bks M T pc k Rs, ⊢ᵍ gc_deps ⍮ gc_stack ->
    G ⊢a a_elim oq Us m Bks M ⟹ T -> G ⊢a M ⟹ nf_indty pc k Rs ->
    exists p D Mm Dq Mk bm i, elim_alg_ok G oq Us m Bks M pc k Rs p D Mm Dq Mk bm i T.
Proof.
  intros * Hg H HM.
  inversion H; subst.
  match goal with H1 : G ⊢a M ⟹ nf_indty ?p0 ?k0 ?Rs0 |- _ =>
    pose proof (functional_alg_type_infer Hg H1 HM) as Heq; injection Heq as -> -> -> end.
  match goal with Hl : ind_lookup _ _ ?p0 = Some ?D0, Hb : List.nth_error Bks m = Some ?bm0,
                  HA : forall j Mj b, _ -> _ -> _ ⊢a eb_motive b ⟸ Typeω@?i0,
                  Hm : ind_member ?D0 m = Some ?Mm0, Hk : ind_member ?Dq0 k = Some ?Mk0 |- _ =>
    exists p0, D0, Mm0, Dq0, Mk0, bm0, i0 end.
  constructor; assumption.
Qed.

Lemma ati_elim_of_ok : forall G oq Us m Bks M T pc k Rs p D Mm Dq Mk bm i,
    elim_alg_ok G oq Us m Bks M pc k Rs p D Mm Dq Mk bm i T -> G ⊢a M ⟹ nf_indty pc k Rs ->
    G ⊢a a_elim oq Us m Bks M ⟹ T.
Proof.
  intros * [] HM.
  eapply ati_elim with (p := p) (D := D) (Mm := Mm) (Dq := Dq) (Mk := Mk) (bm := bm) (i := i); try eassumption; reflexivity.
Qed.

(** The group an eliminator eliminates: the one it names, or at a declared
    member that of the scrutinee's type. *)
Definition elim_target (oq : option qname) (pc : qname) : qname :=
  match oq with Some p => p | None => pc end.

Lemma elim_target_eq : forall G p D oq m Mm pc k, ⊢ G -> ind_lookup gc_deps gc_stack p = Some D -> elim_grp D oq p m ->
    ind_member D m = Some Mm -> im_ref p m Mm = (pc, k) -> p = elim_target oq pc.
Proof.
  intros * HG Hl [-> | [-> Hlt]] Hm Hr; [ reflexivity |].
  destruct (decl_of_lookup _ _ _ _ _ HG Hl) as [HD _].
  destruct (member_lt_decl _ _ _ _ _ HD Hm Hlt) as [pm Hh].
  unfold im_ref in Hr; rewrite Hh in Hr; injection Hr as -> _; reflexivity.
Qed.

(** Terms checked, below [n], at the instances of a telescope are typed
    there. *)
Lemma tele_checks_typed : forall Δ Γ Ms n, tele_ass Δ -> ⊢ (Δ ++ Γ)%list -> ⊢ Γ ->
    (forall j N T, j < n -> List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> Γ ⊢a N ⟸ T) ->
    forall j N T, j < n -> List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> Γ ⊢ N : T.
Proof.
  intros * Hass HΔ HΓ Hc j; induction j as [j IH] using lt_wf_ind; intros N T Hj HN HT.
  destruct (tele_insts_typed _ _ _ _ Ms Hass HΔ (wf_sub_id _ _ _ HΓ) j T HT) as [iT HTt].
  - intros j' N' T' Hj' HN' HT'; exact (IH j' Hj' _ _ ltac:(lia) HN' HT').
  - exact (alg_type_check_sound (Hc _ _ _ Hj HN HT) HΓ HTt).
Qed.

(** Whether terms check at the instances of a telescope, each at its
    instance once those before it check. *)
Definition tele_check_dec G (HG : ⊢ G) (P : tenv G) Δ (Hass : tele_ass Δ) (HΔ : ⊢ (Δ ++ G)%list) (Ms : list exp)
    (chk : forall N, In N Ms -> forall G' A' (HA' : exists i, G' ⊢ A' : Typeω@i) (P' : tenv G'),
        { G' ⊢a N ⟸ A' } + { ~ G' ⊢a N ⟸ A' }) :
  { forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> G ⊢a N ⟸ T }
  + { ~ forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> G ⊢a N ⟸ T }.
Proof.
  pose (Q := fun j => forall N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> G ⊢a N ⟸ T).
  assert (f : forall j, j < List.length Ms -> (forall j', j' < j -> Q j') -> {Q j} + {~ Q j}).
  { intros j Hj Hpre; unfold Q.
    destruct (List.nth_error Ms j) as [N |] eqn:HN; [| left; intros ? ? [=] ].
    destruct (List.nth_error (tele_insts Δ Id Ms) j) as [T |] eqn:HT; [| left; intros ? ? _ [=] ].
    assert (HTt : exists i, G ⊢ T : Typeω@i).
    { eapply tele_insts_typed; [ exact Hass | exact HΔ | apply wf_sub_id, HG | exact HT |].
      intros j' N' T' Hj' HN' HT'.
      eapply (tele_checks_typed Δ G Ms j); [ exact Hass | exact HΔ | exact HG | | exact Hj' | exact HN' | exact HT' ].
      intros j'' N'' T'' Hj'' HN'' HT''; exact (Hpre j'' Hj'' _ _ HN'' HT''). }
    destruct (chk N (List.nth_error_In _ _ HN) G T HTt P) as [Hc | Hc];
      [ left; intros ? ? [= <-] [= <-]; exact Hc | right; intros HQ; exact (Hc (HQ _ _ eq_refl eq_refl)) ]. }
  destruct (forall_lt_dec Q (List.length Ms) f) as [HQ | HQ]; [ left | right ].
  - intros j N T HN HT; apply (HQ j); [ apply List.nth_error_Some; congruence | exact HN | exact HT ].
  - intros H; apply HQ; intros j _ N T HN HT; exact (H _ _ _ HN HT).
Defined.

(** [nfs_agree], position by position. *)
Lemma nfs_agree_nth : forall Γ Ms Rs Ts, nfs_agree Γ Ms Rs Ts ->
    forall j M R T, List.nth_error Ms j = Some M -> List.nth_error Rs j = Some R -> List.nth_error Ts j = Some T ->
      exists W, nbe_f Γ M T W /\ nbe_f Γ R T W.
Proof.
  induction 1 as [| M R T W Ms Rs Ts HM HR _ IH]; intros [| j] M' R' T' HM' HR' HT'; cbn in *; try discriminate.
  - injection HM' as <-; injection HR' as <-; injection HT' as <-; eauto.
  - eauto.
Qed.

Lemma typed_nbe_order_f : forall G M A, G ⊢ M : A -> nbe_order gc_deps gc_stack G M A.
Proof. intros * H; destruct (soundness H) as (W & HW & _); exact (nbe_order_sound _ _ _ _ _ _ HW). Qed.

(** Terms [Rs] of their own instances of a telescope that have, below
    [n], the normal forms of [Ms] at theirs are equal to them, and of
    their instances, up to [n]. *)
Lemma agree_prefix_eq : forall Δ G Ms Rs n, tele_ass Δ -> ⊢ (Δ ++ G)%list -> ⊢ G ->
    List.length Ms = List.length Δ -> List.length Rs = List.length Δ ->
    (forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> G ⊢ N : T) ->
    (forall j N T, List.nth_error Rs j = Some N -> List.nth_error (tele_insts Δ Id Rs) j = Some T -> G ⊢ N : T) ->
    (forall j N R T, j < n -> List.nth_error Ms j = Some N -> List.nth_error Rs j = Some R ->
       List.nth_error (tele_insts Δ Id Ms) j = Some T -> exists W, nbe_f G N T W /\ nbe_f G R T W) ->
    forall j R T, j <= n -> List.nth_error Rs j = Some R -> List.nth_error (tele_insts Δ Id Ms) j = Some T ->
      G ⊢ R : T /\ forall N, j < n -> List.nth_error Ms j = Some N -> G ⊢ N ≈ R : T.
Proof.
  intros * Hass HΔ HG HMl HRl HMs HRs Hag j; induction j as [j IH] using lt_wf_ind; intros R T Hj HR HT.
  assert (Hjl : j < List.length Δ) by (rewrite <- HRl; apply List.nth_error_Some; congruence).
  destruct (List.nth_error (tele_insts Δ Id Rs) j) as [T' |] eqn:HT';
    [| apply List.nth_error_None in HT'; rewrite length_tele_insts in HT' by exact Hass; lia ].
  destruct (tele_insts_cong_upto Δ G G Id Id Ms Rs Hass HΔ (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ HG)) j T T' HT HT')
    as [iT HTT].
  { intros j' N N' T0 Hj' HN HN' HT0; exact (proj2 (IH j' Hj' N' T0 ltac:(lia) HN' HT0) N ltac:(lia) HN). }
  assert (HRt : G ⊢ R : T) by (eapply wf_conv'; [ exact (HRs _ _ _ HR HT') | symmetry; exact HTT ]).
  split; [ exact HRt |].
  intros N Hjn HN; destruct (Hag _ _ _ _ Hjn HN HR HT) as (W & HNW & HRW).
  etransitivity; [ eapply soundness'; [ exact (HMs _ _ _ HN HT) | exact HNW ] | symmetry; eapply soundness'; eassumption ].
Qed.

(** Whether terms have, position by position, the normal forms of others
    at their instances of a telescope. *)
Definition nfs_agree_dec G (HG : ⊢ G) (P : tenv G) Δ (Hass : tele_ass Δ) (HΔ : ⊢ (Δ ++ G)%list) Ms Rs
    (HMl : List.length Ms = List.length Δ) (HRl : List.length Rs = List.length Δ)
    (HMs : forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> G ⊢ N : T)
    (HRs : forall j N T, List.nth_error Rs j = Some N -> List.nth_error (tele_insts Δ Id Rs) j = Some T -> G ⊢ N : T) :
  { nfs_agree G Ms Rs (tele_insts Δ Id Ms) } + { ~ nfs_agree G Ms Rs (tele_insts Δ Id Ms) }.
Proof.
  pose (Q := fun j => forall N R T, List.nth_error Ms j = Some N -> List.nth_error Rs j = Some R ->
                        List.nth_error (tele_insts Δ Id Ms) j = Some T -> exists W, nbe_f G N T W /\ nbe_f G R T W).
  assert (f : forall j, j < List.length Ms -> (forall j', j' < j -> Q j') -> {Q j} + {~ Q j}).
  { intros j Hj Hpre; unfold Q.
    destruct (List.nth_error Ms j) as [N |] eqn:HN; [| left; intros ? ? ? [=] ].
    destruct (List.nth_error Rs j) as [R |] eqn:HR; [| left; intros ? ? ? _ [=] ].
    destruct (List.nth_error (tele_insts Δ Id Ms) j) as [T |] eqn:HT; [| left; intros ? ? ? _ _ [=] ].
    pose proof (HMs _ _ _ HN HT) as HNt.
    pose proof (proj1 (agree_prefix_eq Δ G Ms Rs j Hass HΔ HG HMl HRl HMs HRs
                         (fun j' N' R' T' Hj' => Hpre j' Hj' N' R' T') j R T (le_n j) HR HT)) as HRt.
    destruct (nbe_env_impl gc_deps gc_stack G P N T (typed_nbe_order_f _ _ _ HNt)) as [W1 HW1].
    destruct (nbe_env_impl gc_deps gc_stack G P R T (typed_nbe_order_f _ _ _ HRt)) as [W2 HW2].
    destruct (nf_eq_dec W1 W2) as [<- | Hne].
    - left; intros ? ? ? [= <-] [= <-] [= <-]; exists W1; split; assumption.
    - right; intros HQ; destruct (HQ _ _ _ eq_refl eq_refl eq_refl) as (W & HW1' & HW2').
      apply Hne; transitivity W; [ eapply functional_nbe; eassumption | symmetry; eapply functional_nbe; eassumption ]. }
  destruct (forall_lt_dec Q (List.length Ms) f) as [HQ | HQ]; [ left | right ].
  - apply nfs_agree_of_nth; [ rewrite length_tele_insts by exact Hass; lia | rewrite length_tele_insts by exact Hass; lia |].
    intros j N R T HN HR HT; apply (HQ j); [ apply List.nth_error_Some; congruence | exact HN | exact HR | exact HT ].
  - intros Hag; apply HQ; intros j _; exact (nfs_agree_nth _ _ _ _ Hag j).
Defined.

(** A type checked at a universe is checked at every universe above. *)
Lemma check_typ_mono : forall Δ A l l', ⊢ Δ -> l <= l' -> Δ ⊢a A ⟸ Typeω@l -> Δ ⊢a A ⟸ Typeω@l'.
Proof.
  intros Δ A l l' HΔ Hll HA; destruct (Nat.eq_dec l l') as [<- | Hne]; [ exact HA |].
  eapply alg_type_check_subtyp; [ exact HA | apply wf_subtyp_univ; [ exact HΔ | lia ] ].
Qed.

(** A type that infers a universe is checked at its index. *)
Lemma check_typ_of_infer : forall Δ A UA u, ⊢ Δ -> Δ ⊢a A ⟹ UA -> is_univ_nf UA u -> Δ ⊢a A ⟸ Typeω@(unf_large u).
Proof. intros * HΔ HA Hu; eapply alg_type_check_typ_of; [ exact HΔ | exact HA | exact Hu | apply unf_le_large ]. Qed.

(** A type checked at a universe is typed at it. *)
Lemma check_typ_sound : forall Δ A l, ⊢ Δ -> Δ ⊢a A ⟸ Typeω@l -> Δ ⊢ A : Typeω@l.
Proof. intros * HΔ HA; exact (alg_type_check_sound HA HΔ (wf_typ _ _ _ _ HΔ)). Qed.

(** What the blocks of an eliminator ask of one universe [l] at the member
    [j]: its annotation and its motive are checked there. *)
Definition block_univ (G : ctx) (p : qname) (D : ind_decl) (Us : list exp) (Bks : list eblock) (j l : nat) : Prop :=
  (forall Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
     tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G ⊢a Z ⟸ Typeω@l) /\
  (forall Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
     elim_mctx p D j Mj Us ++ G ⊢a eb_motive b ⟸ Typeω@l).

Section Blocks.
  Variables (G : ctx) (HG : ⊢ G) (P : tenv G) (p : qname) (D : ind_decl) (Us : list exp) (Bks : list eblock).
  Hypothesis (HC : forall j Mj, ind_member D j = Some Mj -> ⊢ (elim_mctx p D j Mj Us ++ G)%list).

  Let Hg : ⊢ᵍ gc_deps ⍮ gc_stack := ctx_wf_gctx _ _ _ HG.

  (** The context of a member's annotation is well-formed, and its type
      there a type. *)
  Lemma ann_ctx_wf : forall j Mj, ind_member D j = Some Mj ->
      ⊢ (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G)%list /\
      exists jH, tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G
                   ⊢ ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)) : Typeω@jH.
  Proof. intros * Hj; pose proof (HC _ _ Hj) as H; unfold elim_mctx in H; cbn [List.app] in H; exact (ctx_decomp H). Qed.

  Lemma ann_mty_order : forall j Mj, ind_member D j = Some Mj ->
      nbe_ty_order gc_deps gc_stack (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G)
        (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj))).
  Proof. intros * Hj; destruct (ann_ctx_wf _ _ Hj) as [_ [jH HH]]; exact (nbe_order_of_typ _ _ _ HH). Qed.

  Lemma block_univ_mono : forall j l l', l <= l' -> block_univ G p D Us Bks j l -> block_univ G p D Us Bks j l'.
  Proof.
    intros * Hll [HZ HA]; split.
    - intros Mj b Z Hj Hb HZ'; eapply check_typ_mono; [ exact (proj1 (ann_ctx_wf _ _ Hj)) | exact Hll | eauto ].
    - intros Mj b Hj Hb; eapply check_typ_mono; [ exact (HC _ _ Hj) | exact Hll | eauto ].
  Qed.

  (** A universe for the annotation and the motive of the member [j]. *)
  Definition block_univ_dec
      (infZ : forall b Z, In b Bks -> eb_ann b = Some Z -> forall G' (HG' : ⊢ G') (P' : tenv G'),
          { UA : nf | G' ⊢a Z ⟹ UA /\ (exists UB u, G' ⊢a UA ⟹ UB /\ is_univ_nf UB u) /\ (exists i : nat, G' ⊢ UA : Typeω@i) }
          + { forall UA, ~ G' ⊢a Z ⟹ UA })
      (infA : forall b, In b Bks -> forall G' (HG' : ⊢ G') (P' : tenv G'),
          { UA : nf | G' ⊢a eb_motive b ⟹ UA /\ (exists UB u, G' ⊢a UA ⟹ UB /\ is_univ_nf UB u) /\ (exists i : nat, G' ⊢ UA : Typeω@i) }
          + { forall UA, ~ G' ⊢a eb_motive b ⟹ UA })
      (j : nat) : { l | block_univ G p D Us Bks j l } + { forall l, ~ block_univ G p D Us Bks j l }.
  Proof.
    destruct (ind_member D j) as [Mj |] eqn:Hj; [| left; exists 0; split; intros; congruence ].
    destruct (List.nth_error Bks j) as [b |] eqn:Hb; [| left; exists 0; split; intros; congruence ].
    destruct (ann_ctx_wf _ _ Hj) as [HΨ _].
    (** The annotation. *)
    assert (lZ : { l | forall Z, eb_ann b = Some Z -> tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G ⊢a Z ⟸ Typeω@l }
                 + { forall l, ~ forall Z, eb_ann b = Some Z -> tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G ⊢a Z ⟸ Typeω@l }).
    { destruct (eb_ann b) as [Z |] eqn:HZ; [| left; exists 0; intros; discriminate ].
      destruct (infZ b Z (List.nth_error_In _ _ Hb) HZ _ HΨ (tenv_ext G P _ HΨ)) as [[UA (HZi & _)] | HnZ].
      - destruct (univ_nf_idx_dec UA) as [[u Hu] | Hnu].
        + left; exists (unf_large u); intros ? [= <-]; exact (check_typ_of_infer _ _ _ _ HΨ HZi Hu).
        + right; intros l H.
          destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ (H Z eq_refl)) as (UA' & u' & HZi' & Hu' & _).
          rewrite (functional_alg_type_infer Hg HZi HZi') in Hnu; exact (Hnu _ Hu').
      - right; intros l H.
        destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ (H Z eq_refl)) as (UA' & u' & HZi' & _).
        exact (HnZ _ HZi'). }
    destruct lZ as [[lZ HlZ] | HnZ]; [| right; intros l [HZ _]; apply (HnZ l); intros Z HZ'; exact (HZ _ _ _ Hj Hb HZ') ].
    (** The motive. *)
    pose proof (HC _ _ Hj) as HCj.
    destruct (infA b (List.nth_error_In _ _ Hb) _ HCj (tenv_ext G P _ HCj)) as [[UA (HAi & _)] | HnA].
    - destruct (univ_nf_idx_dec UA) as [[u Hu] | Hnu].
      + left; exists (Nat.max lZ (unf_large u)); split.
        * intros Mj' b' Z Hj' Hb' HZ; rewrite Hj in Hj'; rewrite Hb in Hb'; injection Hj' as <-; injection Hb' as <-.
          eapply check_typ_mono; [ exact HΨ | | exact (HlZ _ HZ) ]; lia.
        * intros Mj' b' Hj' Hb'; rewrite Hj in Hj'; rewrite Hb in Hb'; injection Hj' as <-; injection Hb' as <-.
          eapply check_typ_mono; [ exact HCj | | exact (check_typ_of_infer _ _ _ _ HCj HAi Hu) ]; lia.
      + right; intros l [_ H].
        destruct (alg_type_check_typ_implies_alg_type_infer_typ HCj (H _ _ Hj Hb)) as (UA' & u' & HAi' & Hu' & _).
        rewrite (functional_alg_type_infer Hg HAi HAi') in Hnu; exact (Hnu _ Hu').
    - right; intros l [_ H].
      destruct (alg_type_check_typ_implies_alg_type_infer_typ HCj (H _ _ Hj Hb)) as (UA' & u' & HAi' & _).
      exact (HnA _ HAi').
  Defined.

  (** Whether the annotations, checked at the universe [L], are their
      members' types. *)
  Definition ann_conv_dec (L : nat) (HL : forall j, j < List.length Bks -> block_univ G p D Us Bks j L) :
    { forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
        alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G) Z
          (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj))) }
    + { ~ forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
        alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G) Z
          (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj))) }.
  Proof.
    pose (Q := fun j => forall Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
        alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G) Z
          (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))).
    assert (f : forall j, j < List.length Bks -> (forall j', j' < j -> Q j') -> {Q j} + {~ Q j}).
    { intros j Hjl _; unfold Q.
      destruct (ind_member D j) as [Mj |] eqn:Hj; [| left; intros; congruence ].
      destruct (List.nth_error Bks j) as [b |] eqn:Hb; [| left; intros; congruence ].
      destruct (eb_ann b) as [Z |] eqn:HZ; [| left; intros; congruence ].
      destruct (ann_ctx_wf _ _ Hj) as [HΨ _].
      pose proof (check_typ_sound _ _ _ HΨ (proj1 (HL j Hjl) _ _ _ Hj Hb HZ)) as HZt.
      destruct (nbe_ty_env_impl gc_deps gc_stack _ (tenv_ext G P _ HΨ) Z (nbe_order_of_typ _ _ _ HZt)) as [W1 HW1].
      destruct (nbe_ty_env_impl gc_deps gc_stack _ (tenv_ext G P _ HΨ) _ (ann_mty_order _ _ Hj)) as [W2 HW2].
      destruct (nf_eq_dec W1 W2) as [<- | Hne].
      - left; intros Mj' b' Z' Hj' Hb' HZ'; injection Hj' as <-; injection Hb' as <-.
        rewrite HZ in HZ'; injection HZ' as <-; exists W1; split; assumption.
      - right; intros HQ; destruct (HQ _ _ _ eq_refl eq_refl HZ) as (W & HW1' & HW2').
        apply Hne; transitivity W; [ eapply functional_nbe_ty; eassumption | symmetry; eapply functional_nbe_ty; eassumption ]. }
    destruct (forall_lt_dec Q (List.length Bks) f) as [HQ | HQ]; [ left | right ].
    - intros j Mj b Z Hj Hb; apply (HQ j); [ apply List.nth_error_Some; congruence | exact Hj | exact Hb ].
    - intros H; apply HQ; intros j _; exact (H j).
  Defined.

  (** A property of the blocks member by member, decided at each. *)
  Definition blocks_dec (Q : nat -> imember -> eblock -> Prop)
      (f : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> {Q j Mj b} + {~ Q j Mj b}) :
    { forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> Q j Mj b }
    + { ~ forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> Q j Mj b }.
  Proof.
    pose (Q' := fun j => forall Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> Q j Mj b).
    assert (f' : forall j, j < List.length Bks -> (forall j', j' < j -> Q' j') -> {Q' j} + {~ Q' j}).
    { intros j _ _; unfold Q'.
      destruct (ind_member D j) as [Mj |] eqn:Hj; [| left; intros; congruence ].
      destruct (List.nth_error Bks j) as [b |] eqn:Hb; [| left; intros; congruence ].
      destruct (f j Mj b Hj Hb) as [HQ | HQ].
      - left; intros Mj' b' Hj' Hb'; injection Hj' as <-; injection Hb' as <-; exact HQ.
      - right; intros H; exact (HQ (H _ _ eq_refl eq_refl)). }
    destruct (forall_lt_dec Q' (List.length Bks) f') as [HQ | HQ]; [ left | right ].
    - intros j Mj b Hj Hb; apply (HQ j); [ apply List.nth_error_Some; congruence | exact Hj | exact Hb ].
    - intros H; apply HQ; intros j _; exact (H j).
  Defined.
End Blocks.

(** A derivation of an eliminator, inverted against what the checker has
    computed so far: the group it eliminates is the one computed
    ([elim_target_eq]), and its lookups are the checker's. *)
Ltac inv_elim Hg HG HMi :=
  let H := match goal with H : _ ⊢a a_elim _ _ _ _ _ ⟹ _ |- _ => H end in
  let p' := fresh "p'" in
  destruct (ati_elim_inv _ _ _ _ _ _ _ _ _ _ Hg H HMi) as (p' & ?D' & ?Mm' & ?Dq' & ?Mk' & ?bm' & ?i' & []);
  clear H;
  match goal with
  | Hl' : ind_lookup _ _ p' = Some _, Hgr : elim_grp _ _ p' _, Hm' : ind_member _ _ = Some _, Hr' : im_ref p' _ _ = _ |- _ =>
      pose proof (elim_target_eq _ _ _ _ _ _ _ _ HG Hl' Hgr Hm' Hr'); subst p'
  end;
  try match goal with Ep : ?p0 = elim_target _ _ |- _ => rewrite <- Ep in * end;
  unify_lookups.

(** The eliminator.  The scrutinee infers the type former of the declared
    member [k] of the group [Dq] at [pc]; the group eliminated is the one
    named, or that one ([elim_target]).  The uniform parameters are checked
    one by one ([tele_check_dec]) and the member's uniform arguments at
    them compared with the scrutinee type's ([nfs_agree_dec]).  The blocks'
    annotations and motives infer universes, and are checked at the
    largest ([bound_lt_dec]), at which the branches' types are types. *)
Definition elim_infer G (HG : ⊢ G) (P : tenv G) oq (Us : list exp) m (Bks : list eblock) M
  (rM : { T : nf | G ⊢a M ⟹ T /\ (exists UA u, G ⊢a T ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ T : Typeω@i) }
        + { forall T, ~ G ⊢a M ⟹ T })
  (chkU : forall U, In U Us -> forall G' A' (HA' : exists i, G' ⊢ A' : Typeω@i) (P' : tenv G'),
      { G' ⊢a U ⟸ A' } + { ~ G' ⊢a U ⟸ A' })
  (infZ : forall b Z, In b Bks -> eb_ann b = Some Z -> forall G' (HG' : ⊢ G') (P' : tenv G'),
      { UA : nf | G' ⊢a Z ⟹ UA /\ (exists UB u, G' ⊢a UA ⟹ UB /\ is_univ_nf UB u) /\ (exists i : nat, G' ⊢ UA : Typeω@i) }
      + { forall UA, ~ G' ⊢a Z ⟹ UA })
  (infA : forall b, In b Bks -> forall G' (HG' : ⊢ G') (P' : tenv G'),
      { UA : nf | G' ⊢a eb_motive b ⟹ UA /\ (exists UB u, G' ⊢a UA ⟹ UB /\ is_univ_nf UB u) /\ (exists i : nat, G' ⊢ UA : Typeω@i) }
      + { forall UA, ~ G' ⊢a eb_motive b ⟹ UA })
  (chkB : forall b br, In b Bks -> In br (eb_brs b) -> forall G' A' (HA' : exists i, G' ⊢ A' : Typeω@i) (P' : tenv G'),
      { G' ⊢a snd br ⟸ A' } + { ~ G' ⊢a snd br ⟸ A' }) :
  { T : nf | G ⊢a a_elim oq Us m Bks M ⟹ T /\ (exists UA u, G ⊢a T ⟹ UA /\ is_univ_nf UA u) /\ (exists i : nat, G ⊢ T : Typeω@i) }
  + { forall T, ~ G ⊢a a_elim oq Us m Bks M ⟹ T }.
Proof.
  pose proof (ctx_wf_gctx _ _ _ HG) as Hg; pose proof (decls_of_ctx _ _ _ HG) as HDs.
  (** The scrutinee. *)
  destruct rM as [[T (HMi & _ & HTt)] | HnM]; [| right; intros T H; inversion H; subst; eapply HnM; eassumption ].
  destruct (get_indty_nf T) as [[pc [k [Rs ->]]] | HnI];
    [| right; intros T' H; inversion H; subst;
       match goal with H1 : G ⊢a M ⟹ nf_indty _ _ _ |- _ => pose proof (functional_alg_type_infer Hg H1 HMi) as Heq end;
       symmetry in Heq; eapply HnI; exact Heq ].
  destruct (ind_lookup_f gc_deps gc_stack pc) as [[Dq |] Hlq]; [| right; intros T' H; inv_elim Hg HG HMi; congruence ].
  destruct (ind_member Dq k) as [Mk |] eqn:Hk; [| right; intros T' H; inv_elim Hg HG HMi; congruence ].
  destruct (Nat.eq_dec (List.length (nfs_to_exps Rs)) (im_np Dq Mk)) as [HRl | HRl];
    [| right; intros T' H; inv_elim Hg HG HMi; contradiction ].
  (** The group eliminated and its member. *)
  destruct (ind_lookup_f gc_deps gc_stack (elim_target oq pc)) as [[D |] Hl];
    [| right; intros T' H; inv_elim Hg HG HMi; congruence ].
  assert (Hgrp : { elim_grp D oq (elim_target oq pc) m } + { ~ elim_grp D oq (elim_target oq pc) m }).
  { destruct oq as [q0 |]; [ left; left; reflexivity |].
    destruct (Compare_dec.lt_dec m (ind_ndecl D)) as [Hlt | Hlt]; [ left; right; split; [ reflexivity | exact Hlt ] |].
    right; intros [[=] | [_ Hlt']]; contradiction. }
  destruct Hgrp as [Hgrp | Hgrp]; [| right; intros T' H; inv_elim Hg HG HMi; contradiction ].
  destruct (ind_member D m) as [Mm |] eqn:Hm; [| right; intros T' H; inv_elim Hg HG HMi; congruence ].
  assert (Hrd : { im_ref (elim_target oq pc) m Mm = (pc, k) } + { im_ref (elim_target oq pc) m Mm <> (pc, k) }).
  { destruct (im_ref (elim_target oq pc) m Mm) as [pc' k'].
    destruct (qname_eq_dec pc' pc) as [-> | Hne]; [| right; intros [=]; contradiction ].
    destruct (Nat.eq_dec k' k) as [-> | Hne]; [ left; reflexivity | right; intros [=]; contradiction ]. }
  destruct Hrd as [Hr | Hr]; [| right; intros T' H; inv_elim Hg HG HMi; contradiction ].
  destruct (List.nth_error Bks m) as [bm |] eqn:Hb; [| right; intros T' H; inv_elim Hg HG HMi; congruence ].
  destruct (Nat.eq_dec (List.length Bks) (List.length (ind_members D))) as [HBl | HBl];
    [| right; intros T' H; inv_elim Hg HG HMi; contradiction ].
  destruct (Nat.eq_dec (List.length Us) (ind_nu D)) as [HUl | HUl];
    [| right; intros T' H; inv_elim Hg HG HMi; contradiction ].
  remember (elim_target oq pc) as p eqn:Ep in Hl, Hgrp, Hr.
  destruct (decl_of_lookup _ _ _ _ _ HG Hl) as [HD Hc].
  destruct (decl_of_lookup _ _ _ _ _ HG Hlq) as [HDq Hcq].
  (** The uniform parameters. *)
  destruct (tele_check_dec G HG P (ind_uparams D) (dc_ass _ Hc) (wf_uparams_app _ _ _ HD Hc _ HG) Us chkU) as [HUc | HUc];
    [| right; intros T' H; inv_elim Hg HG HMi; contradiction ].
  assert (HUt : forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
             G ⊢ U : T).
  { intros j U T HU HT.
    exact (tele_checks_typed _ _ Us (S j) (dc_ass _ Hc) (wf_uparams_app _ _ _ HD Hc _ HG) HG
             (fun j' N T' _ HN HT' => HUc j' N T' HN HT') j U T (Nat.lt_succ_diag_r j) HU HT). }
  (** The member's uniform arguments, against the scrutinee type's. *)
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HG Hl Hm Hr Hlq HUl HUt) as [HPrl HPrt].
  assert (HRt : forall j R T', List.nth_error (nfs_to_exps Rs) j = Some R ->
             List.nth_error (tele_insts (im_params Dq Mk) Id (nfs_to_exps Rs)) j = Some T' -> G ⊢ R : T')
    by (destruct HTt as [iT HTt]; exact (wf_ind_apps_inv _ _ _ _ _ _ _ Hlq Hk HTt HRl)).
  destruct (params_typed_split _ _ Dq Hcq _ _ _ _ Hk HRl HRt) as [HRu _].
  assert (HRl' : List.length (List.firstn (ind_nu Dq) (nfs_to_exps Rs)) = List.length (ind_uparams Dq))
    by (rewrite List.length_firstn; unfold im_np in HRl; unfold ind_nu in *; lia).
  destruct (nfs_agree_dec G HG P (ind_uparams Dq) (dc_ass _ Hcq) (wf_uparams_app _ _ _ HDq Hcq _ HG)
              (im_pre Mm Us) (List.firstn (ind_nu Dq) (nfs_to_exps Rs)) ltac:(unfold ind_nu in HPrl; exact HPrl) HRl' HPrt HRu)
    as [Hag | Hag];
    [| right; intros T' H; inv_elim Hg HG HMi; contradiction ].
  (** The blocks: the binders, then the universe of the annotations and the
      motives, the annotations' types, the branches' names and counts, and
      the branches. *)
  assert (HC : forall j Mj, ind_member D j = Some Mj -> ⊢ (elim_mctx p D j Mj Us ++ G)%list)
    by (intros; eapply elim_mctx_wf; eassumption).
  destruct (blocks_dec D Bks (fun j Mj b => eb_nm b = S (im_nn Mj)) (fun j Mj b _ _ => Nat.eq_dec _ _)) as [HBnm | HBnm];
    [| right; intros T' H; inv_elim Hg HG HMi; contradiction ].
  destruct (bound_lt_dec (block_univ G p D Us Bks) (block_univ_mono G p D Us Bks HC) (List.length Bks)
              (fun j _ => block_univ_dec G HG P p D Us Bks HC infZ infA j)) as [[L HL] | HnL];
    [| right; intros T' H; inv_elim Hg HG HMi;
       match goal with HA : forall j Mj b, _ -> _ -> _ ⊢a eb_motive b ⟸ Typeω@?i0 |- _ =>
         apply (HnL i0); intros j _; split; [ intros; eauto | intros; eauto ] end ].
  destruct (ann_conv_dec G P p D Us Bks HC L HL) as [HZc | HZc]; [| right; intros T' H; inv_elim Hg HG HMi; contradiction ].
  destruct (blocks_dec D Bks (fun j Mj b => brs_names (im_cons Mj) (eb_brs b))
              (fun j Mj b _ _ => list_eq_dec string_dec _ _)) as [HBn | HBn];
    [| right; intros T' H; inv_elim Hg HG HMi; contradiction ].
  assert (Hcount : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             { forall c gs n B, ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec gs)%nat }
             + { ~ forall c gs n B, ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec gs)%nat }).
  { intros j Mj b _ _.
    destruct (forall_in_dec (fun br => forall gs, ind_con Mj (fst (fst br)) = Some gs ->
                                       snd (fst br) = (im_nn Mj + List.length gs + cargs_nrec gs)%nat) (eb_brs b)) as [Ha | Ha].
    - intros br _; destruct (ind_con Mj (fst (fst br))) as [gs |]; [| left; intros ? [=] ].
      destruct (Nat.eq_dec (snd (fst br)) (im_nn Mj + List.length gs + cargs_nrec gs)) as [E | E];
        [ left; intros ? [= <-]; exact E | right; intros H; exact (E (H gs eq_refl)) ].
    - left; intros c gs n B Hcon Hin; exact (Ha _ Hin gs Hcon).
    - right; intros H; apply Ha; intros [[c n] B] Hin gs Hcon; exact (H _ _ _ _ Hcon Hin). }
  destruct (blocks_dec D Bks _ Hcount) as [HBa | HBa]; [| right; intros T' H; inv_elim Hg HG HMi; apply HBa; intros; eauto ].
  (** The branches, at their types: the motives are typed at [L]. *)
  assert (HAs : motives_typed gc_deps gc_stack G p D Us (blocks_motives Bks) L).
  { intros j Mj Hj; destruct (blocks_nth _ _ _ _ HBl Hj) as [b Hb0].
    rewrite (blocks_motives_nth _ _ _ Hb0).
    assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence).
    exact (check_typ_sound _ _ _ (HC _ _ Hj) (proj2 (HL j Hjl) _ _ Hj Hb0)). }
  assert (Hbt : forall j Mj b c gs, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
             exists i, elim_bctx p D Mj gs (blocks_motives Bks) Us ++ G ⊢ elim_bty p j Mj c gs (eb_motive b) Us : Typeω@i).
  { intros j Mj b c gs Hj Hb0 Hcon; exists L.
    assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence).
    pose proof (wf_bty_sub _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hj HG HUl HUt HC HAs Hcon) as Hbs.
    exact (sub_preserves_exp _ _ _ _ _ _ _ (check_typ_sound _ _ _ (HC _ _ Hj) (proj2 (HL j Hjl) _ _ Hj Hb0)) Hbs). }
  assert (Hbr : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             { forall c gs n B, ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
                 elim_bctx p D Mj gs (blocks_motives Bks) Us ++ G ⊢a B ⟸ elim_bty p j Mj c gs (eb_motive b) Us }
             + { ~ forall c gs n B, ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
                 elim_bctx p D Mj gs (blocks_motives Bks) Us ++ G ⊢a B ⟸ elim_bty p j Mj c gs (eb_motive b) Us }).
  { intros j Mj b Hj Hb0.
    destruct (forall_in_dec (fun br => forall gs, ind_con Mj (fst (fst br)) = Some gs ->
                elim_bctx p D Mj gs (blocks_motives Bks) Us ++ G ⊢a snd br ⟸ elim_bty p j Mj (fst (fst br)) gs (eb_motive b) Us)
                (eb_brs b)) as [Ha | Ha].
    - intros br Hin; destruct (ind_con Mj (fst (fst br))) as [gs |] eqn:Hcon; [| left; intros ? [=] ].
      pose proof (Hbt _ _ _ _ _ Hj Hb0 Hcon) as HT.
      destruct (chkB b br (List.nth_error_In _ _ Hb0) Hin _ _ HT (tenv_ext G P _ (tenv_ctx_of_typ _ _ HT))) as [E | E];
        [ left; intros ? [= <-]; exact E | right; intros H; exact (E (H gs eq_refl)) ].
    - left; intros c gs n B Hcon Hin; exact (Ha _ Hin gs Hcon).
    - right; intros H; apply Ha; intros [[c n] B] Hin gs Hcon; exact (H _ _ _ _ Hcon Hin). }
  destruct (blocks_dec D Bks _ Hbr) as [HBc | HBc]; [| right; intros T' H; inv_elim Hg HG HMi; apply HBc; intros; eauto ].
  (** The type: the normal form of the motive's instance. *)
  assert (Hel : G ⊢ a_elim oq Us m Bks M
                  : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu Dq) (nfs_to_exps Rs) ++ M :: nil)]).
  { eapply alg_elim_typed with (i := L); try eassumption; try reflexivity.
    all: first
      [ exact (alg_type_infer_sound HMi HG)
      | intros j U T0 HU HT0 HΓ i0 HTi; exact (alg_type_check_sound (HUc _ _ _ HU HT0) HΓ HTi)
      | intros j Mj b Z Hj Hb0 HZ HΨ i0 _;
        assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence);
        exact (check_typ_sound _ _ _ HΨ (proj1 (HL j Hjl) _ _ _ Hj Hb0 HZ))
      | intros j Mj b Hj Hb0 HΓ i0 _;
        assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence);
        exact (check_typ_sound _ _ _ HΓ (proj2 (HL j Hjl) _ _ Hj Hb0))
      | intros j Mj b c gs n B Hj Hb0 Hcon Hin HΓ i0 HTi; exact (alg_type_check_sound (HBc _ _ _ Hj Hb0 _ _ _ _ Hcon Hin) HΓ HTi)
      | intros j Mj b c gs n B Hj Hb0 Hcon Hin; exact (HBa _ _ _ Hj Hb0 _ _ _ _ Hcon Hin) ]. }
  assert (Hord : nbe_ty_order gc_deps gc_stack G
                   (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu Dq) (nfs_to_exps Rs) ++ M :: nil)])
    by (destruct (presup_exp_typ Hel) as [jT HTe]; exact (nbe_order_of_typ _ _ _ HTe)).
  refine (let (T', HT') := nbe_ty_env_impl gc_deps gc_stack G P _ Hord in inleft (exist _ T' _)).
  split; [| destruct (presup_exp_typ Hel) as [jT HTe]; eapply level_of_nbe; eassumption ].
  eapply ati_elim_of_ok; [| exact HMi ].
  econstructor; try eassumption.
  all: first
    [ intros j Mj b Z Hj Hb0 HZ;
      assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence);
      exact (proj1 (HL j Hjl) _ _ _ Hj Hb0 HZ)
    | intros j Mj b Hj Hb0;
      assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence);
      exact (proj2 (HL j Hjl) _ _ Hj Hb0)
    | intros j Mj b c gs n B Hj Hb0 Hcon Hin; exact (HBa _ _ _ Hj Hb0 _ _ _ _ Hcon Hin)
    | intros j Mj b c gs n B Hj Hb0 Hcon Hin; exact (HBc _ _ _ Hj Hb0 _ _ _ _ Hcon Hin) ].
Defined.

End Fixed_GCtx.
