From Stdlib Require Import Arith List ListDec String PeanoNat Lia.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing Strengthening.
From Mctt.Core Require Import Base.
From Mctt.Core.Consequences Require Import Consistency.
From Mctt.Extraction Require Import Lookup NbE PseudoMonadic TypeCheckBase.
Import Domain_Notations Wk_Notations Fixed_Notations.

(** * Checking the Forms of Inductive Types

    The cases of [alg_type_infer_ind_case], [alg_type_infer_con] and
    [alg_type_infer_elim].  The type former and a constructor recurse on
    nothing; the eliminator recurses on its scrutinee, its uniform
    parameters, and the scrutinee types, motives and branches of its
    blocks, and takes those recursive calls as arguments, so that the
    mutual fixpoint of the checker only passes them on. *)

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

(** Whether a kind is one an eliminator may target ([motive_kind]). *)
Definition motive_kind_dec (r : abs_kind) : { motive_kind r } + { ~ motive_kind r }.
Proof. destruct r; first [ left; constructor | right; intros H; inversion H ]. Defined.

(** The lookups that name one thing name it once: two hypotheses that the
    same lookup returns two things make them one. *)
Ltac unify_lookups :=
  repeat match goal with
    | H1 : ?f ?x = Some ?a, H2 : ?f ?x = Some ?b |- _ =>
        assert_fails (constr_eq a b); rewrite H1 in H2; injection H2; clear H2; intros; subst
    end.

(** The checker's rules of inductive types, through the fast context [F];
    the judgments are those of the global context it stands for. *)
Section Fixed_GCtx.
Variable F : FCtx.
#[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.

(** Whether a normal form is an instance of the type former of a member. *)
#[derive(equations=no,eliminator=no)]
Equations get_indty_nf (A : nf) : { p & { k & { Rs | A = nf_indty p k Rs } } } + { forall p k Rs, A <> nf_indty p k Rs } :=
| nf_indty p k Rs => pureo (existT _ p (existT _ k (exist _ Rs _)))
| _ => inright _
.

Extraction Inline get_indty_nf motive_kind_dec.

(** ** The Type Former and the Constructors *)

Lemma ind_ty_order : forall G p D k Mk, ⊢ G -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    nbe_ty_order gc_deps gc_stack G (ind_ty D Mk).
Proof.
  intros * HG Hl Hk.
  destruct (decl_of_lookup _ _ _ _ _ HG Hl) as [HD Hc].
  destruct (ind_ty_typed _ _ _ _ _ _ HD Hc Hk HG) as [j Hj].
  exact (nbe_order_of_typ _ _ _ Hj).
Qed.

Lemma con_ty_order : forall G p D k Mk c gs, ⊢ G -> ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk ->
    ind_con Mk c = Some gs -> nbe_ty_order gc_deps gc_stack G (con_ty p D k Mk gs).
Proof.
  intros * HG Hl Hk Hcon.
  destruct (con_ty_typed _ _ G _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HG) (decls_of_ctx _ _ _ HG) Hl Hk Hcon HG) as [j Hj].
  exact (nbe_order_of_typ _ _ _ Hj).
Qed.

(** The type former of a declared member. *)
Definition ind_infer G (HG : ⊢ G) (P : checker_env G) p k :
  { A : nf | G ⊢a a_ind p k ⟹ A } + { forall A, ~ G ⊢a a_ind p k ⟹ A }.
Proof.
  destruct (ind_lookup_f F p) as [[D |] Hl]; [| right; intros A H; inversion H; congruence ].
  destruct (ind_member D k) as [Mk |] eqn:Hk; [| right; intros A H; inversion H; subst; unify_lookups; congruence ].
  destruct (Compare_dec.lt_dec k (ind_ndecl D)) as [Hlt | Hlt]; [| right; intros A H; inversion H; subst; unify_lookups; contradiction ].
  refine (let (W, HW) := nbe_ty_env_impl F G P (ind_ty D Mk) (ind_ty_order G p D k Mk HG Hl Hk) in
          inleft (exist _ W _)).
  econstructor; eassumption.
Defined.

(** A constructor of a member. *)
Definition con_infer G (HG : ⊢ G) (P : checker_env G) p k c :
  { A : nf | G ⊢a a_con p k c ⟹ A } + { forall A, ~ G ⊢a a_con p k c ⟹ A }.
Proof.
  destruct (ind_lookup_f F p) as [[D |] Hl]; [| right; intros A H; inversion H; congruence ].
  destruct (ind_member D k) as [Mk |] eqn:Hk; [| right; intros A H; inversion H; subst; unify_lookups; congruence ].
  destruct (ind_con Mk c) as [gs |] eqn:Hcon; [| right; intros A H; inversion H; subst; unify_lookups; congruence ].
  refine (let (W, HW) := nbe_ty_env_impl F G P (con_ty p D k Mk gs) (con_ty_order G p D k Mk c gs HG Hl Hk Hcon) in
          inleft (exist _ W _)).
  econstructor; eassumption.
Defined.

(** ** The Eliminator *)

(** What [alg_type_infer_elim] asks of the eliminator [a_elim r p Us m Bks M]
    whose scrutinee infers [nf_indty pc k Rs], at the group [D] at [p] it
    eliminates, its member [Mm], the declared member [Mk] of the group
    [Dq] at [pc] the member's type is headed by, the member's block [bm],
    the universe [i] of the blocks' scrutinee types and motives (the
    motives at the sort of [r]), and the type [T] it infers. *)
Record elim_alg_ok (G : ctx) (r : abs_kind) (p : qname) (Us : list exp) (m : nat) (Bks : list eblock) (M : exp)
    (pc : qname) (k : nat) (Rs : list nf) (D : ind_decl) (Mm : imember) (Dq : ind_decl) (Mk : imember)
    (bm : eblock) (i : nat) (T : nf) : Prop := mk_elim_alg_ok
  { (** The group is found at [p] *)
    elim_ok_lookup : ind_lookup gc_deps gc_stack p = Some D
    (** The member eliminated *)
  ; elim_ok_member : ind_member D m = Some Mm
    (** Its type is headed by the declared member [k] of the group at [pc] *)
  ; elim_ok_ref : im_ref p m Mm = (pc, k)
    (** That group is found *)
  ; elim_ok_ref_lookup : ind_lookup gc_deps gc_stack pc = Some Dq
    (** And that member *)
  ; elim_ok_ref_member : ind_member Dq k = Some Mk
    (** The scrutinee's type has all its parameters *)
  ; elim_ok_nparams : List.length (List.map nf_to_exp Rs) = im_np Dq Mk
    (** The member's block *)
  ; elim_ok_block : List.nth_error Bks m = Some bm
    (** One block per member with a block *)
  ; elim_ok_block_count : List.length Bks = ind_nblk D
    (** One uniform parameter per uniform parameter of the group *)
  ; elim_ok_nuparams : List.length Us = ind_nu D
    (** The uniform parameters are checked at the group's telescope *)
  ; elim_ok_uparams : forall j U T', List.nth_error Us j = Some U ->
      List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T' -> G ⊢a U ⟸ T'
    (** The member's uniform arguments agree with the scrutinee type's *)
  ; elim_ok_agree : nfs_agree G (im_pre Mm Us) (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs))
      (tele_insts (ind_uparams Dq) Id (im_pre Mm Us))
    (** Each block binds the non-uniform parameters and the scrutinee *)
  ; elim_ok_binders : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_binder_count b = S (im_nn Mj)
    (** The scrutinee types are checked at the universe *)
  ; elim_ok_scrutinee_typed : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
      tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G ⊢a eb_scrutinee_type b ⟸ Typeω@i
    (** Each scrutinee type is its member's type *)
  ; elim_ok_scrutinee_conv : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
      alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G) (eb_scrutinee_type b)
        (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))
    (** The motives are checked at the sort of [r] at the universe *)
  ; elim_ok_motive : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
      elim_mctx p D j Mj Us ++ G ⊢a eb_motive b ⟸ abs_kind_sort r Typeω@i
    (** Each block has one branch per constructor, in order *)
  ; elim_ok_names : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b)
    (** Each branch binds its constructor's arguments and recursive results *)
  ; elim_ok_counts : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
      ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat
    (** The branches are checked at their types *)
  ; elim_ok_branches : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
      ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
      elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ G ⊢a B ⟸ elim_branch_type p D j Mj c gs (eb_motive b) Us
    (** The eliminator's kind is one of a motive *)
  ; elim_ok_kind : motive_kind r
    (** The type is the normal form of the motive's instance *)
  ; elim_ok_nbe : nbe_ty_f G (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu Dq) (List.map nf_to_exp Rs) ++ M :: nil)] T }.

(** The inversion of [alg_type_infer_elim], at the scrutinee's inferred type. *)
Lemma alg_type_infer_elim_inv : forall G r p Us m Bks M T pc k Rs, ⊢ᵍ gc_deps ⍮ gc_stack ->
    G ⊢a a_elim r p Us m Bks M ⟹ T -> G ⊢a M ⟹ nf_indty pc k Rs ->
    exists D Mm Dq Mk bm i, elim_alg_ok G r p Us m Bks M pc k Rs D Mm Dq Mk bm i T.
Proof.
  intros * Hg H HM.
  inversion H; subst.
  match goal with H1 : G ⊢a M ⟹ nf_indty ?p0 ?k0 ?Rs0 |- _ =>
    pose proof (functional_alg_type_infer Hg H1 HM) as Heq; injection Heq as -> -> -> end.
  match goal with Hl : ind_lookup _ _ p = Some ?D0, Hb : List.nth_error Bks m = Some ?bm0,
                  HA : forall j Mj b, _ -> _ -> _ ⊢a eb_motive b ⟸ abs_kind_sort _ Typeω@?i0,
                  Hm : ind_member ?D0 m = Some ?Mm0, Hk : ind_member ?Dq0 k = Some ?Mk0 |- _ =>
    exists D0, Mm0, Dq0, Mk0, bm0, i0 end.
  constructor; assumption.
Qed.

Lemma alg_type_infer_elim_of_ok : forall G r p Us m Bks M T pc k Rs D Mm Dq Mk bm i,
    elim_alg_ok G r p Us m Bks M pc k Rs D Mm Dq Mk bm i T -> G ⊢a M ⟹ nf_indty pc k Rs ->
    G ⊢a a_elim r p Us m Bks M ⟹ T.
Proof.
  intros * [] HM.
  eapply alg_type_infer_elim with (D := D) (Mm := Mm) (Dq := Dq) (Mk := Mk) (bm := bm) (i := i); try eassumption; reflexivity.
Qed.

(** Terms checked, below [n], at the instances of a telescope are typed
    there. *)
Lemma tele_checks_typed : forall Δ Γ Ms n, all_assumptions Δ -> ⊢ (Δ ++ Γ)%list -> ⊢ Γ ->
    (forall j N T, j < n -> List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> Γ ⊢a N ⟸ T) ->
    forall j N T, j < n -> List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> Γ ⊢ N : T.
Proof.
  intros * Hass HΔ HΓ Hc j; induction j as [j IH] using lt_wf_ind; intros N T Hj HN HT.
  destruct (tele_insts_typed _ _ _ _ Ms Hass HΔ (wf_sub_id _ _ _ HΓ) j T HT) as (ST & HST & HTt).
  - intros j' N' T' Hj' HN' HT'; exact (IH j' Hj' _ _ ltac:(lia) HN' HT').
  - exact (alg_type_check_sound_sort (Hc _ _ _ Hj HN HT) HΓ HST HTt).
Qed.

(** Whether terms check at the instances of a telescope, each at its
    instance once those before it check. *)
Definition tele_check_dec G (HG : ⊢ G) (P : checker_env G) Δ (Hass : all_assumptions Δ) (HΔ : ⊢ (Δ ++ G)%list) (Ms : list exp)
    (chk : forall N, In N Ms -> forall G' A' (HA' : G' ⊢ᵗ A') (P' : checker_env G'),
        { G' ⊢a N ⟸ A' } + { ~ G' ⊢a N ⟸ A' }) :
  { forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> G ⊢a N ⟸ T }
  + { ~ forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> G ⊢a N ⟸ T }.
Proof.
  pose (Q := fun j => forall N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> G ⊢a N ⟸ T).
  assert (f : forall j, j < List.length Ms -> (forall j', j' < j -> Q j') -> {Q j} + {~ Q j}).
  { intros j Hj Hpre; unfold Q.
    destruct (List.nth_error Ms j) as [N |] eqn:HN; [| left; intros ? ? [=] ].
    destruct (List.nth_error (tele_insts Δ Id Ms) j) as [T |] eqn:HT; [| left; intros ? ? _ [=] ].
    assert (HTt : G ⊢ᵗ T).
    { edestruct tele_insts_typed as (ST & HST & HTt); [ exact Hass | exact HΔ | apply wf_sub_id, HG | exact HT | |
                                                      exact (wf_type_of_sort _ HST HTt) ].
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
      exists W W', nbe_f Γ M T W /\ nbe_f Γ R T W' /\ nf_eq_upto_proofs W W'.
Proof.
  induction 1 as [| M R T W W' Ms Rs Ts HM HR HWW _ IH]; intros [| j] M' R' T' HM' HR' HT'; cbn in *; try discriminate.
  - injection HM' as <-; injection HR' as <-; injection HT' as <-; eauto.
  - eauto.
Qed.

(** A typed term has the order of its normalization. *)
Lemma typed_nbe_order_f : forall G M A, G ⊢ M : A -> nbe_order gc_deps gc_stack G M A.
Proof. intros * H; destruct (normalization H) as (W & HW); exact (nbe_order_sound _ _ _ _ _ _ HW). Qed.

(** Terms [Rs] of their own instances of a telescope that have, below
    [n], the normal forms of [Ms] at theirs, up to proofs, are equal to
    them, and of their instances, up to [n]. *)
Lemma agree_prefix_eq : forall Δ G Ms Rs n, all_assumptions Δ -> ⊢ (Δ ++ G)%list -> ⊢ G ->
    List.length Ms = List.length Δ -> List.length Rs = List.length Δ ->
    (forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> G ⊢ N : T) ->
    (forall j N T, List.nth_error Rs j = Some N -> List.nth_error (tele_insts Δ Id Rs) j = Some T -> G ⊢ N : T) ->
    (forall j N R T, j < n -> List.nth_error Ms j = Some N -> List.nth_error Rs j = Some R ->
       List.nth_error (tele_insts Δ Id Ms) j = Some T ->
       exists W W', nbe_f G N T W /\ nbe_f G R T W' /\ nf_eq_upto_proofs W W') ->
    forall j R T, j <= n -> List.nth_error Rs j = Some R -> List.nth_error (tele_insts Δ Id Ms) j = Some T ->
      G ⊢ R : T /\ forall N, j < n -> List.nth_error Ms j = Some N -> G ⊢ N ≈ R : T.
Proof.
  intros * Hass HΔ HG HMl HRl HMs HRs Hag j; induction j as [j IH] using lt_wf_ind; intros R T Hj HR HT.
  assert (Hjl : j < List.length Δ) by (rewrite <- HRl; apply List.nth_error_Some; congruence).
  destruct (List.nth_error (tele_insts Δ Id Rs) j) as [T' |] eqn:HT';
    [| apply List.nth_error_None in HT'; rewrite length_tele_insts in HT' by exact Hass; lia ].
  destruct (tele_insts_cong_upto Δ G G Id Id Ms Rs Hass HΔ (wf_sub_eq_refl _ _ _ _ _ (wf_sub_id _ _ _ HG)) j T T' HT HT')
    as (ST & HST & HTT).
  { intros j' N N' T0 Hj' HN HN' HT0; exact (proj2 (IH j' Hj' N' T0 ltac:(lia) HN' HT0) N ltac:(lia) HN). }
  assert (HRt : G ⊢ R : T) by (eapply exp_conv_sort; [ exact HST | symmetry; exact HTT | exact (HRs _ _ _ HR HT') ]).
  split; [ exact HRt |].
  intros N Hjn HN; destruct (Hag _ _ _ _ Hjn HN HR HT) as (W & W' & HNW & HRW & HWW).
  exact (soundness_upto_proofs (HMs _ _ _ HN HT) HRt HNW HRW HWW).
Qed.

(** Whether terms have, position by position, the normal forms of others,
    up to proofs, at their instances of a telescope. *)
Definition nfs_agree_dec G (P : checker_env G) Δ (Hass : all_assumptions Δ) (HΔ : ⊢ (Δ ++ G)%list) (HG : ⊢ G) Ms Rs
    (HMl : List.length Ms = List.length Δ) (HRl : List.length Rs = List.length Δ)
    (HMs : forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ Id Ms) j = Some T -> G ⊢ N : T)
    (HRs : forall j N T, List.nth_error Rs j = Some N -> List.nth_error (tele_insts Δ Id Rs) j = Some T -> G ⊢ N : T) :
  { nfs_agree G Ms Rs (tele_insts Δ Id Ms) } + { ~ nfs_agree G Ms Rs (tele_insts Δ Id Ms) }.
Proof.
  pose (Q := fun j => forall N R T, List.nth_error Ms j = Some N -> List.nth_error Rs j = Some R ->
                        List.nth_error (tele_insts Δ Id Ms) j = Some T ->
                        exists W W', nbe_f G N T W /\ nbe_f G R T W' /\ nf_eq_upto_proofs W W').
  assert (f : forall j, j < List.length Ms -> (forall j', j' < j -> Q j') -> {Q j} + {~ Q j}).
  { intros j Hj Hpre; unfold Q.
    destruct (List.nth_error Ms j) as [N |] eqn:HN; [| left; intros ? ? ? [=] ].
    destruct (List.nth_error Rs j) as [R |] eqn:HR; [| left; intros ? ? ? _ [=] ].
    destruct (List.nth_error (tele_insts Δ Id Ms) j) as [T |] eqn:HT; [| left; intros ? ? ? _ _ [=] ].
    pose proof (HMs _ _ _ HN HT) as HNt.
    pose proof (proj1 (agree_prefix_eq Δ G Ms Rs j Hass HΔ HG HMl HRl HMs HRs
                         (fun j' N' R' T' Hj' => Hpre j' Hj' N' R' T') j R T (le_n j) HR HT)) as HRt.
    destruct (nbe_env_impl F G P N T (typed_nbe_order_f _ _ _ HNt)) as [W1 HW1].
    destruct (nbe_env_impl F G P R T (typed_nbe_order_f _ _ _ HRt)) as [W2 HW2].
    destruct (nf_eq_upto_proofs_dec W1 W2) as [E | Hne].
    - left; intros ? ? ? [= <-] [= <-] [= <-]; exists W1, W2; repeat split; assumption.
    - right; intros HQ; destruct (HQ _ _ _ eq_refl eq_refl eq_refl) as (W & W' & HW1' & HW2' & E).
      apply Hne.
      replace W1 with W by (eapply functional_nbe; eassumption).
      replace W2 with W' by (eapply functional_nbe; eassumption).
      exact E. }
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
Lemma check_typ_of_infer : forall Δ A UA u, ⊢ Δ -> Δ ⊢a A ⟹ UA -> is_univ_nf UA u -> Δ ⊢a A ⟸ Typeω@(universe_nf_large_index u).
Proof. intros * HΔ HA Hu; eapply alg_type_check_typ_of; [ exact HΔ | exact HA | exact Hu | apply universe_nf_le_large ]. Qed.

(** A type checked at a universe is typed at it. *)
Lemma check_typ_sound : forall Δ A l, ⊢ Δ -> Δ ⊢a A ⟸ Typeω@l -> Δ ⊢ A : Typeω@l.
Proof. intros * HΔ HA; exact (alg_type_check_sound HA HΔ (wf_typ _ _ _ _ HΔ)). Qed.

(** A type checked at the sort of a motive's kind [r] at a universe is
    checked at the sort of [r] at every universe above: [Prop] does not
    depend on it. *)
Lemma check_sort_mono : forall Δ A r l l', motive_kind r -> ⊢ Δ -> l <= l' ->
    Δ ⊢a A ⟸ abs_kind_sort r Typeω@l -> Δ ⊢a A ⟸ abs_kind_sort r Typeω@l'.
Proof. intros * Hr HΔ Hll HA; destruct Hr; [ exact (check_typ_mono _ _ _ _ HΔ Hll HA) | exact HA ]. Qed.

(** A type checked at the sort of a motive's kind at a universe is typed
    there. *)
Lemma check_sort_sound : forall Δ A r l, motive_kind r -> ⊢ Δ -> Δ ⊢a A ⟸ abs_kind_sort r Typeω@l ->
    Δ ⊢ A : abs_kind_sort r Typeω@l.
Proof.
  intros * Hr HΔ HA.
  exact (alg_type_check_sound_sort HA HΔ (type_sort_universe (S l)) (motive_kind_sort_typed _ r l Hr HΔ)).
Qed.

(** What the blocks of an eliminator of the kind [r] ask of one universe
    [l] at the member [j]: its scrutinee type is checked there, and its
    motive at the sort of [r] there. *)
Definition block_univ (G : ctx) (r : abs_kind) (p : qname) (D : ind_decl) (Us : list exp) (Bks : list eblock) (j l : nat) : Prop :=
  (forall Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
     tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G ⊢a eb_scrutinee_type b ⟸ Typeω@l) /\
  (forall Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
     elim_mctx p D j Mj Us ++ G ⊢a eb_motive b ⟸ abs_kind_sort r Typeω@l).

Section Blocks.
  Variables (G : ctx) (HG : ⊢ G) (P : checker_env G) (r : abs_kind) (Hr : motive_kind r)
    (p : qname) (D : ind_decl) (Us : list exp) (Bks : list eblock).
  Hypothesis (HC : forall j Mj, ind_member D j = Some Mj -> ⊢ (elim_mctx p D j Mj Us ++ G)%list).

  Let Hg : ⊢ᵍ gc_deps ⍮ gc_stack := ctx_wf_gctx _ _ _ HG.

  (** The context of a member's scrutinee type is well-formed, and its
      type there a type. *)
  Lemma scrutinee_ctx_wf : forall j Mj, ind_member D j = Some Mj ->
      ⊢ (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G)%list /\
      tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G
        ⊢ᵗ ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)).
  Proof.
    intros * Hj; pose proof (HC _ _ Hj) as H; unfold elim_mctx in H; cbn [List.app] in H.
    split; [ exact (ctx_decomp_tail H) |].
    destruct (ctx_decomp_kind H) as (S0 & HS0k & HA0).
    exact (wf_type_of_sort _ (sort_kind_type_sort _ _ HS0k) HA0).
  Qed.

  Lemma scrutinee_mty_order : forall j Mj, ind_member D j = Some Mj ->
      nbe_ty_order gc_deps gc_stack (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G)
        (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj))).
  Proof. intros * Hj; destruct (scrutinee_ctx_wf _ _ Hj) as [_ HH]; exact (nbe_order_of_type _ _ HH). Qed.

  Lemma block_univ_mono : forall j l l', l <= l' -> block_univ G r p D Us Bks j l -> block_univ G r p D Us Bks j l'.
  Proof.
    intros * Hll [HZ HA]; split.
    - intros Mj b Hj Hb; eapply check_typ_mono; [ exact (proj1 (scrutinee_ctx_wf _ _ Hj)) | exact Hll | eauto ].
    - intros Mj b Hj Hb; eapply check_sort_mono; [ exact Hr | exact (HC _ _ Hj) | exact Hll | eauto ].
  Qed.

  (** A universe a type that infers [UA] is checked at, or none. *)
  Definition typ_univ_dec Δ (HΔ : ⊢ Δ) A UA (HAi : Δ ⊢a A ⟹ UA) :
    { l | Δ ⊢a A ⟸ Typeω@l } + { forall l, ~ Δ ⊢a A ⟸ Typeω@l }.
  Proof.
    pose proof (ctx_wf_gctx _ _ _ HΔ) as Hg'.
    destruct (univ_nf_idx_dec UA) as [[u Hu] | Hnu].
    - left; exists (universe_nf_large_index u); exact (check_typ_of_infer _ _ _ _ HΔ HAi Hu).
    - right; intros l H.
      destruct (alg_type_check_typ_implies_alg_type_infer_typ HΔ H) as (UA' & u' & HAi' & Hu' & _).
      rewrite (functional_alg_type_infer Hg' HAi HAi') in Hnu; exact (Hnu _ Hu').
  Defined.

  (** A motive's universe, from its inferred type: of the sort of [r], at
      a universe it is checked at, or none. *)
  Definition motive_univ_dec Δ (HΔ : ⊢ Δ) A UA (HAi : Δ ⊢a A ⟹ UA) :
    { l | Δ ⊢a A ⟸ abs_kind_sort r Typeω@l } + { forall l, ~ Δ ⊢a A ⟸ abs_kind_sort r Typeω@l }.
  Proof.
    pose proof (ctx_wf_gctx _ _ _ HΔ) as Hg'.
    destruct r; [ exact (typ_univ_dec Δ HΔ A UA HAi) | | exfalso; inversion Hr ].
    - destruct (prop_nf_dec UA) as [-> | Hnp].
      + left; exists 0; exact (alg_type_check_prop_of HΔ HAi).
      + right; intros l H; apply Hnp.
        exact (functional_alg_type_infer Hg' HAi (alg_type_check_prop_infer HΔ H)).
  Defined.

  (** A universe for the scrutinee type and the motive of the member
      [j]. *)
  Definition block_univ_dec
      (infZ : forall b, In b Bks -> forall G' (HG' : ⊢ G') (P' : checker_env G'),
          { UA : nf | G' ⊢a eb_scrutinee_type b ⟹ UA } + { forall UA, ~ G' ⊢a eb_scrutinee_type b ⟹ UA })
      (infA : forall b, In b Bks -> forall G' (HG' : ⊢ G') (P' : checker_env G'),
          { UA : nf | G' ⊢a eb_motive b ⟹ UA } + { forall UA, ~ G' ⊢a eb_motive b ⟹ UA })
      (j : nat) : { l | block_univ G r p D Us Bks j l } + { forall l, ~ block_univ G r p D Us Bks j l }.
  Proof.
    destruct (ind_member D j) as [Mj |] eqn:Hj; [| left; exists 0; split; intros; congruence ].
    destruct (List.nth_error Bks j) as [b |] eqn:Hb; [| left; exists 0; split; intros; congruence ].
    destruct (scrutinee_ctx_wf _ _ Hj) as [HΨ _].
    (** The scrutinee type. *)
    destruct (infZ b (List.nth_error_In _ _ Hb) _ HΨ (checker_env_ext F G P _ HΨ)) as [[UZ HZi] | HnZ];
      [| right; intros l [HZ _];
         destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ (HZ _ _ Hj Hb)) as (UA' & u' & HZi' & _);
         exact (HnZ _ HZi') ].
    destruct (typ_univ_dec _ HΨ _ _ HZi) as [[lZ HlZ] | HnZ]; [| right; intros l [HZ _]; exact (HnZ l (HZ _ _ Hj Hb)) ].
    (** The motive. *)
    pose proof (HC _ _ Hj) as HCj.
    destruct (infA b (List.nth_error_In _ _ Hb) _ HCj (checker_env_ext F G P _ HCj)) as [[UA HAi] | HnA].
    - destruct (motive_univ_dec _ HCj _ _ HAi) as [[lA HlA] | Hnu].
      + left; exists (Nat.max lZ lA); split.
        * intros Mj' b' Hj' Hb'; rewrite Hj in Hj'; rewrite Hb in Hb'; injection Hj' as <-; injection Hb' as <-.
          eapply check_typ_mono; [ exact HΨ | | exact HlZ ]; lia.
        * intros Mj' b' Hj' Hb'; rewrite Hj in Hj'; rewrite Hb in Hb'; injection Hj' as <-; injection Hb' as <-.
          eapply check_sort_mono; [ exact Hr | exact HCj | | exact HlA ]; lia.
      + right; intros l [_ H]; exact (Hnu l (H _ _ Hj Hb)).
    - right; intros l [_ H].
      destruct (alg_type_check_sort_infer HCj (type_sort_kind_universe r l) (H _ _ Hj Hb)) as (UA' & ? & ? & HAi' & _).
      exact (HnA _ HAi').
  Defined.

  (** Whether the scrutinee types, checked at the universe [L], are their
      members' types, up to proofs. *)
  Definition scrutinee_conv_dec (L : nat) (HL : forall j, j < List.length Bks -> block_univ G r p D Us Bks j L) :
    { forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
        alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G) (eb_scrutinee_type b)
          (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj))) }
    + { ~ forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
        alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G) (eb_scrutinee_type b)
          (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj))) }.
  Proof.
    pose (Q := fun j => forall Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
        alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ G) (eb_scrutinee_type b)
          (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))).
    assert (f : forall j, j < List.length Bks -> (forall j', j' < j -> Q j') -> {Q j} + {~ Q j}).
    { intros j Hjl _; unfold Q.
      destruct (ind_member D j) as [Mj |] eqn:Hj; [| left; intros; congruence ].
      destruct (List.nth_error Bks j) as [b |] eqn:Hb; [| left; intros; congruence ].
      destruct (scrutinee_ctx_wf _ _ Hj) as [HΨ _].
      pose proof (check_typ_sound _ _ _ HΨ (proj1 (HL j Hjl) _ _ Hj Hb)) as HZt.
      destruct (nbe_ty_env_impl F _ (checker_env_ext F G P _ HΨ) _ (nbe_order_of_typ _ _ _ HZt)) as [W1 HW1].
      destruct (nbe_ty_env_impl F _ (checker_env_ext F G P _ HΨ) _ (scrutinee_mty_order _ _ Hj)) as [W2 HW2].
      destruct (nf_eq_upto_proofs_dec W1 W2) as [E | Hne].
      - left; intros Mj' b' Hj' Hb'; injection Hj' as <-; injection Hb' as <-.
        exists W1, W2; repeat split; assumption.
      - right; intros HQ; destruct (HQ _ _ eq_refl eq_refl) as (W & W' & HW1' & HW2' & E).
        apply Hne.
        replace W1 with W by (eapply functional_nbe_ty; eassumption).
        replace W2 with W' by (eapply functional_nbe_ty; eassumption).
        exact E. }
    destruct (forall_lt_dec Q (List.length Bks) f) as [HQ | HQ]; [ left | right ].
    - intros j Mj b Hj Hb; apply (HQ j); [ apply List.nth_error_Some; congruence | exact Hj | exact Hb ].
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
    computed so far: its lookups are the checker's. *)
Ltac inv_elim Hg HMi :=
  let H := match goal with H : _ ⊢a a_elim _ _ _ _ _ _ ⟹ _ |- _ => H end in
  destruct (alg_type_infer_elim_inv _ _ _ _ _ _ _ _ _ _ _ Hg H HMi) as (?D' & ?Mm' & ?Dq' & ?Mk' & ?bm' & ?i' & []);
  clear H;
  unify_lookups.

(** The eliminator.  The scrutinee infers the type former of the declared
    member [k] of the group [Dq] at [pc]; the group eliminated is the one
    at [p].  The uniform parameters are checked one by one
    ([tele_check_dec]) and the member's uniform arguments at them compared
    with the scrutinee type's ([nfs_agree_dec]).  The blocks' scrutinee
    types and motives infer universes, and are checked at the largest
    ([bound_lt_dec]), at which the branches' types are types. *)
Definition elim_infer G (HG : ⊢ G) (P : checker_env G) r p (Us : list exp) m (Bks : list eblock) M
  (rM : { T : nf | G ⊢a M ⟹ T } + { forall T, ~ G ⊢a M ⟹ T })
  (chkU : forall U, In U Us -> forall G' A' (HA' : G' ⊢ᵗ A') (P' : checker_env G'),
      { G' ⊢a U ⟸ A' } + { ~ G' ⊢a U ⟸ A' })
  (infZ : forall b, In b Bks -> forall G' (HG' : ⊢ G') (P' : checker_env G'),
      { UA : nf | G' ⊢a eb_scrutinee_type b ⟹ UA } + { forall UA, ~ G' ⊢a eb_scrutinee_type b ⟹ UA })
  (infA : forall b, In b Bks -> forall G' (HG' : ⊢ G') (P' : checker_env G'),
      { UA : nf | G' ⊢a eb_motive b ⟹ UA } + { forall UA, ~ G' ⊢a eb_motive b ⟹ UA })
  (chkB : forall b br, In b Bks -> In br (eb_brs b) -> forall G' A' (HA' : G' ⊢ᵗ A') (P' : checker_env G'),
      { G' ⊢a snd br ⟸ A' } + { ~ G' ⊢a snd br ⟸ A' }) :
  { T : nf | G ⊢a a_elim r p Us m Bks M ⟹ T } + { forall T, ~ G ⊢a a_elim r p Us m Bks M ⟹ T }.
Proof.
  pose proof (ctx_wf_gctx _ _ _ HG) as Hg; pose proof (decls_of_ctx _ _ _ HG) as HDs.
  (** The kind of the eliminator. *)
  destruct (motive_kind_dec r) as [Hmk | Hmk]; [| right; intros T H; inversion H; subst; contradiction ].
  (** The scrutinee. *)
  destruct rM as [[T HMi] | HnM]; [| right; intros T H; inversion H; subst; eapply HnM; eassumption ].
  pose proof (alg_type_infer_sound HMi HG) as HMt.
  destruct (get_indty_nf T) as [[pc [k [Rs ->]]] | HnI];
    [| right; intros T' H; inversion H; subst;
       match goal with H1 : G ⊢a M ⟹ nf_indty _ _ _ |- _ => pose proof (functional_alg_type_infer Hg H1 HMi) as Heq end;
       symmetry in Heq; eapply HnI; exact Heq ].
  destruct (ind_lookup_f F pc) as [[Dq |] Hlq]; [| right; intros T' H; inv_elim Hg HMi; congruence ].
  destruct (ind_member Dq k) as [Mk |] eqn:Hk; [| right; intros T' H; inv_elim Hg HMi; congruence ].
  destruct (Nat.eq_dec (List.length (List.map nf_to_exp Rs)) (im_np Dq Mk)) as [HRl | HRl];
    [| right; intros T' H; inv_elim Hg HMi; contradiction ].
  (** The group eliminated and its member. *)
  destruct (ind_lookup_f F p) as [[D |] Hl]; [| right; intros T' H; inv_elim Hg HMi; congruence ].
  destruct (ind_member D m) as [Mm |] eqn:Hm; [| right; intros T' H; inv_elim Hg HMi; congruence ].
  assert (Hrd : { im_ref p m Mm = (pc, k) } + { im_ref p m Mm <> (pc, k) }).
  { destruct (im_ref p m Mm) as [pc' k'].
    destruct (qname_eq_dec pc' pc) as [-> | Hne]; [| right; intros [=]; contradiction ].
    destruct (Nat.eq_dec k' k) as [-> | Hne]; [ left; reflexivity | right; intros [=]; contradiction ]. }
  destruct Hrd as [Hr | Hr]; [| right; intros T' H; inv_elim Hg HMi; contradiction ].
  destruct (List.nth_error Bks m) as [bm |] eqn:Hb; [| right; intros T' H; inv_elim Hg HMi; congruence ].
  destruct (Nat.eq_dec (List.length Bks) (ind_nblk D)) as [HBl | HBl];
    [| right; intros T' H; inv_elim Hg HMi; contradiction ].
  destruct (Nat.eq_dec (List.length Us) (ind_nu D)) as [HUl | HUl];
    [| right; intros T' H; inv_elim Hg HMi; contradiction ].
  destruct (decl_of_lookup _ _ _ _ _ HG Hl) as [HD Hc].
  destruct (decl_of_lookup _ _ _ _ _ HG Hlq) as [HDq Hcq].
  (** The member eliminated has a block: it is no record view. *)
  pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ HD)) as Hsuf.
  pose proof (block_member_not_rview _ _ _ _ _ Hsuf HBl Hm Hb) as Hnr.
  (** The uniform parameters. *)
  destruct (tele_check_dec G HG P (ind_uparams D) (decl_closed_ass _ Hc) (wf_uparams_app _ _ _ HD Hc _ HG) Us chkU) as [HUc | HUc];
    [| right; intros T' H; inv_elim Hg HMi; contradiction ].
  assert (HUt : forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
             G ⊢ U : T).
  { intros j U T HU HT.
    exact (tele_checks_typed _ _ Us (S j) (decl_closed_ass _ Hc) (wf_uparams_app _ _ _ HD Hc _ HG) HG
             (fun j' N T' _ HN HT' => HUc j' N T' HN HT') j U T (Nat.lt_succ_diag_r j) HU HT). }
  (** The member's uniform arguments, against the scrutinee type's. *)
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HG Hl Hm Hnr Hr Hlq HUl HUt) as [HPrl HPrt].
  assert (HRt : forall j R T', List.nth_error (List.map nf_to_exp Rs) j = Some R ->
             List.nth_error (tele_insts (im_params Dq Mk) Id (List.map nf_to_exp Rs)) j = Some T' -> G ⊢ R : T').
  { destruct (presup_exp_typ_sorted HMt (apps_exp_not_level_sort (List.map nf_to_exp Rs) (a_ind pc k) ltac:(discriminate)))
      as (Skk & _ & Hkk).
    exact (wf_ind_apps_inv _ _ _ _ _ _ _ Hlq Hk Hkk HRl). }
  destruct (params_typed_split _ _ Dq Hcq _ _ _ _ Hk HRl HRt) as [HRu _].
  assert (HRl' : List.length (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) = List.length (ind_uparams Dq))
    by (rewrite List.length_firstn; unfold im_np in HRl; unfold ind_nu in *; lia).
  destruct (nfs_agree_dec G P (ind_uparams Dq) (decl_closed_ass _ Hcq) (wf_uparams_app _ _ _ HDq Hcq _ HG) HG
              (im_pre Mm Us) (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) ltac:(unfold ind_nu in HPrl; exact HPrl) HRl' HPrt HRu)
    as [Hag | Hag];
    [| right; intros T' H; inv_elim Hg HMi; contradiction ].
  (** The blocks: the binders, then the universe of the scrutinee types
      and the motives, the scrutinee types' conversions, the branches'
      names and counts, and the branches. *)
  assert (HC : forall j Mj, ind_member D j = Some Mj -> ⊢ (elim_mctx p D j Mj Us ++ G)%list)
    by (intros; eapply elim_mctx_wf; eassumption).
  destruct (blocks_dec D Bks (fun j Mj b => eb_binder_count b = S (im_nn Mj)) (fun j Mj b _ _ => Nat.eq_dec _ _)) as [HBnm | HBnm];
    [| right; intros T' H; inv_elim Hg HMi; contradiction ].
  destruct (bound_lt_dec (block_univ G r p D Us Bks) (block_univ_mono G r Hmk p D Us Bks HC) (List.length Bks)
              (fun j _ => block_univ_dec G P r Hmk p D Us Bks HC infZ infA j)) as [[L HL] | HnL];
    [| right; intros T' H; inv_elim Hg HMi;
       match goal with HA : forall j Mj b, _ -> _ -> _ ⊢a eb_motive b ⟸ abs_kind_sort _ Typeω@?i0 |- _ =>
         apply (HnL i0); intros j _; split; [ intros; eauto | intros; eauto ] end ].
  destruct (scrutinee_conv_dec G P r p D Us Bks HC L HL) as [HZc | HZc]; [| right; intros T' H; inv_elim Hg HMi; contradiction ].
  destruct (blocks_dec D Bks (fun j Mj b => brs_names (im_cons Mj) (eb_brs b))
              (fun j Mj b _ _ => list_eq_dec string_dec _ _)) as [HBn | HBn];
    [| right; intros T' H; inv_elim Hg HMi; contradiction ].
  assert (Hcount : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             { forall c gs n B, ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat }
             + { ~ forall c gs n B, ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat }).
  { intros j Mj b _ _.
    destruct (forall_in_dec (fun br => forall gs, ind_con Mj (fst (fst br)) = Some gs ->
                                       snd (fst br) = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat) (eb_brs b)) as [Ha | Ha].
    - intros br _; destruct (ind_con Mj (fst (fst br))) as [gs |]; [| left; intros ? [=] ].
      destruct (Nat.eq_dec (snd (fst br)) (im_nn Mj + List.length gs + cargs_nrec D gs)) as [E | E];
        [ left; intros ? [= <-]; exact E | right; intros H; exact (E (H gs eq_refl)) ].
    - left; intros c gs n B Hcon Hin; exact (Ha _ Hin gs Hcon).
    - right; intros H; apply Ha; intros [[c n] B] Hin gs Hcon; exact (H _ _ _ _ Hcon Hin). }
  destruct (blocks_dec D Bks _ Hcount) as [HBa | HBa]; [| right; intros T' H; inv_elim Hg HMi; apply HBa; intros; eauto ].
  (** The branches, at their types: the motives are typed at [L]. *)
  assert (HAs : motives_typed gc_deps gc_stack G p D Us (blocks_motives Bks) r L).
  { intros j Mj Hj Hjr; destruct (blocks_nth _ _ _ _ Hsuf HBl Hj Hjr) as [b Hb0].
    rewrite (blocks_motives_nth _ _ _ Hb0).
    assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence).
    exact (check_sort_sound _ _ _ _ Hmk (HC _ _ Hj) (proj2 (HL j Hjl) _ _ Hj Hb0)). }
  (** A branch's type is the motive's instance, of the motive's sort. *)
  assert (Hbt : forall j Mj b c gs, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
             elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ G ⊢ᵗ elim_branch_type p D j Mj c gs (eb_motive b) Us).
  { intros j Mj b c gs Hj Hb0 Hcon.
    assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence).
    pose proof (wf_branch_type_sub _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hj (block_member_not_rview _ _ _ _ _ Hsuf HBl Hj Hb0)
                  HG HUl HUt HC HAs Hmk Hcon) as Hbs.
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ (check_sort_sound _ _ _ _ Hmk (HC _ _ Hj) (proj2 (HL j Hjl) _ _ Hj Hb0)) Hbs) as HbT.
    rewrite abs_kind_sort_sub in HbT; cbn [exp_sub] in HbT.
    exact (wf_type_of_sort _ (type_sort_kind_universe r L) HbT). }
  assert (Hbr : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             { forall c gs n B, ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
                 elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ G ⊢a B ⟸ elim_branch_type p D j Mj c gs (eb_motive b) Us }
             + { ~ forall c gs n B, ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
                 elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ G ⊢a B ⟸ elim_branch_type p D j Mj c gs (eb_motive b) Us }).
  { intros j Mj b Hj Hb0.
    destruct (forall_in_dec (fun br => forall gs, ind_con Mj (fst (fst br)) = Some gs ->
                elim_bctx r p D Mj gs (blocks_motives Bks) Us ++ G ⊢a snd br ⟸ elim_branch_type p D j Mj (fst (fst br)) gs (eb_motive b) Us)
                (eb_brs b)) as [Ha | Ha].
    - intros br Hin; destruct (ind_con Mj (fst (fst br))) as [gs |] eqn:Hcon; [| left; intros ? [=] ].
      pose proof (Hbt _ _ _ _ _ Hj Hb0 Hcon) as HT.
      destruct (chkB b br (List.nth_error_In _ _ Hb0) Hin _ _ HT (checker_env_ext F G P _ (wf_type_ctx _ _ HT))) as [E | E];
        [ left; intros ? [= <-]; exact E | right; intros H; exact (E (H gs eq_refl)) ].
    - left; intros c gs n B Hcon Hin; exact (Ha _ Hin gs Hcon).
    - right; intros H; apply Ha; intros [[c n] B] Hin gs Hcon; exact (H _ _ _ _ Hcon Hin). }
  destruct (blocks_dec D Bks _ Hbr) as [HBc | HBc]; [| right; intros T' H; inv_elim Hg HMi; apply HBc; intros; eauto ].
  (** The type: the normal form of the motive's instance. *)
  assert (Hel : G ⊢ a_elim r p Us m Bks M
                  : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu Dq) (List.map nf_to_exp Rs) ++ M :: nil)]).
  { eapply alg_elim_typed with (i := L); try eassumption; try reflexivity.
    all: first
      [ intros j U T0 HU HT0 HΓ S0 HS0 HTi; exact (alg_type_check_sound_sort (HUc _ _ _ HU HT0) HΓ HS0 HTi)
      | intros j Mj b Hj Hb0 HΨ S0 _ _;
        assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence);
        exact (check_typ_sound _ _ _ HΨ (proj1 (HL j Hjl) _ _ Hj Hb0))
      | intros j Mj b Hj Hb0 HΓ S0 _ _;
        assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence);
        exact (check_sort_sound _ _ _ _ Hmk HΓ (proj2 (HL j Hjl) _ _ Hj Hb0))
      | intros j Mj b c gs n B Hj Hb0 Hcon Hin HΓ S0 HS0 HTi;
        exact (alg_type_check_sound_sort (HBc _ _ _ Hj Hb0 _ _ _ _ Hcon Hin) HΓ HS0 HTi)
      | intros j Mj b c gs n B Hj Hb0 Hcon Hin; exact (HBa _ _ _ Hj Hb0 _ _ _ _ Hcon Hin) ]. }
  assert (Hord : nbe_ty_order gc_deps gc_stack G
                   (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu Dq) (List.map nf_to_exp Rs) ++ M :: nil)])
    by exact (nbe_order_of_type _ _ (presup_exp_typ Hel)).
  refine (let (T', HT') := nbe_ty_env_impl F G P _ Hord in inleft (exist _ T' _)).
  eapply alg_type_infer_elim_of_ok; [| exact HMi ].
  econstructor; try eassumption.
  all: first
    [ intros j Mj b Hj Hb0;
      assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence);
      exact (proj1 (HL j Hjl) _ _ Hj Hb0)
    | intros j Mj b Hj Hb0;
      assert (Hjl : j < List.length Bks) by (apply List.nth_error_Some; congruence);
      exact (proj2 (HL j Hjl) _ _ Hj Hb0)
    | intros j Mj b c gs n B Hj Hb0 Hcon Hin; exact (HBa _ _ _ Hj Hb0 _ _ _ _ Hcon Hin)
    | intros j Mj b c gs n B Hj Hb0 Hcon Hin; exact (HBc _ _ _ Hj Hb0 _ _ _ _ Hcon Hin) ].
Defined.

End Fixed_GCtx.
