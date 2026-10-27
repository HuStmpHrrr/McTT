(** * The Instances the Classification Meets, and the Siblings

    Where the classification of a group declaration's arguments
    ([Core.Syntactic.System.Command], [cls_arg_in]) finds a nested
    occurrence: in the normal form of an argument's type, at the end of
    its [Π]s, the type former of a declared member of a filed group at
    uniform arguments ([cls_arg_view]).  Those instances are typed views
    whose arguments are their own normal forms ([view_inv],
    [view_meets_inv]), and so are a typed view's siblings, the members of
    its container's group at its arguments ([sib_view_inv]); the siblings
    of a view sibling are siblings ([view_entry_sibs]), by the view
    equations.  The same for records: the classification finds a record
    view at the end of an argument's normal form, the record type at all
    its parameters ([cls_arg_record_view]), a typed record view whose
    arguments are their own normal forms ([record_view_inv],
    [nest_record_view_inv]); a container's record member gives a record
    view sibling ([sib_record], [sib_record_inv]). *)

From Stdlib Require Import Lia List PeanoNat String.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base Completeness Soundness Consequences.NormalFormWeakening.
From Mctt.Core Require Import Consequences.Consistency Semantic.Realizability.
From Mctt.Core.Semantic.Inductives Require Import NestAcc.
From Mctt.Algorithmic Require Import Strengthening.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Extraction Require Import ViewsSearch IndDecl.
From Mctt.Core.Completeness.LogicalRelation Require Import Telescope Instance.
From Mctt.Core.Completeness.Consequences Require Import Types.
From Mctt.Core.Completeness.Inductives Require Import Decl Model ArgTypes Elim.
From Mctt.Core.Completeness Require Import LogicalRelation UnitCases.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Syntactic Require Import NfRename.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Core.Syntactic.System.Inductives Require Import UniformParams Views.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

(** The [j]-th value of a telescope's readback, read at its type in the
    environment of the values before it. *)
Lemma read_ps_nth : forall Θ Ξ s ρ T vs Ws, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ws ->
    forall j A v, List.nth_error T j = Some (ce_ass A) -> List.nth_error vs j = Some v ->
    exists a V, ⟦ A ⟧ Θ ⍮ Ξ ⍮ env_args ρ (List.firstn j vs) ↘ a /\ Rnf ⇓ a v in Θ ⍮ Ξ ⍮ s ↘ V /\
      List.nth_error Ws j = Some V.
Proof.
  induction 1 as [| ? ? ? ? ? ? ? ? ? Ea HV Hr IH]; intros [| j] A' v' HT Hv; cbn in HT, Hv; try discriminate.
  - injection HT as <-; injection Hv as <-; do 2 eexists; cbn; eauto.
  - destruct (IH _ _ _ HT Hv) as (a1 & V1 & Ea1 & HVa & Hn); exists a1, V1; cbn; auto.
Qed.

(** ** Normal Forms of Types, Read Structurally *)

Lemma nbe_ty_pi_inv : forall Θ Ξ Γ B C W, nbe_ty Θ Ξ Γ (a_pi B C) W ->
    exists WB WC, W = nf_pi WB WC /\ nbe_ty Θ Ξ Γ B WB /\ nbe_ty Θ Ξ (ce_ass B :: Γ) C WC.
Proof.
  intros * [ρ m Hi He Hr].
  inversion He; subst.
  inversion Hr; subst.
  do 2 eexists; split; [ reflexivity |].
  split; econstructor; eauto.
  constructor; eassumption.
Qed.

(** ** Where the Classification Finds a Nested Occurrence *)

(** A chain of [Π]s over the domains [Bs], outermost first. *)
Fixpoint pis (Bs : list exp) (E : exp) : exp :=
  match Bs with
  | nil => E
  | B :: Bs' => a_pi B (pis Bs' E)
  end.

Lemma img_pat_spec : forall pat T A, img_pat pat T = Some A -> T = A[wk_pat pat]ʷ.
Proof.
  intros * H; unfold img_pat in H.
  destruct (exp_eq_dec T T[unwk_pat pat]ʷ[wk_pat pat]ʷ) as [E |]; [ injection H as <-; exact E | discriminate ].
Qed.

Lemma img_pats_spec : forall pat Ts As, img_pats pat Ts = Some As -> Ts = List.map (fun A => A[wk_pat pat]ʷ) As.
Proof.
  induction Ts as [| T Ts IH]; intros As H; cbn in H; [ injection H as <-; reflexivity |].
  destruct (img_pat pat T) as [A |] eqn:E1; [| discriminate ].
  destruct (img_pats pat Ts) as [As' |] eqn:E2; [| discriminate ].
  injection H as <-; cbn; rewrite <- (img_pat_spec _ _ _ E1), <- (IH _ eq_refl); reflexivity.
Qed.

(** A shape the classification finds a nested occurrence [(qc, k, Cs)] in
    ends, past its domains, in the type former of the declared member [k]
    of the filed group at [qc] at arguments the first [m] of which, the
    group's uniform ones, are [Cs] weakened past the domains, the
    arguments before and the member's non-uniform parameters. *)
Lemma cls_sh_view : forall grp recs nu np n pat T d t qc k Cs,
    cls_sh grp recs nu np n pat d T = Some t -> In (vk_ind qc k Cs) (rptyp_view t) ->
    exists Bs E m, T = pis Bs E /\ (forall B C, E <> a_pi B C) /\ app_head E = a_ind qc k /\ grp qc k = Some m /\
      m <= List.length (app_args E) /\
      List.firstn m (app_args E) = List.map (fun C => C[wk_pat (List.repeat true (d + List.length Bs + List.length pat + (np - nu)))]ʷ) Cs.
Proof.
  (* a shape that is no [Π] ends here *)
  assert (Hnest : forall grp recs nu np n pat d T t qc k Cs, (forall B C, T <> a_pi B C) ->
      match app_head T with
      | a_var x => cls_self nu np n pat d x (app_args T)
      | a_ind qc k => cls_nest grp nu np n pat d qc k (app_args T)
      | a_record qr => cls_record_view recs nu np n pat d qr (app_args T)
      | _ => None
      end = Some t -> In (vk_ind qc k Cs) (rptyp_view t) ->
      exists m, app_head T = a_ind qc k /\ grp qc k = Some m /\ m <= List.length (app_args T) /\
        List.firstn m (app_args T) = List.map (fun C => C[wk_pat (List.repeat true (d + List.length pat + (np - nu)))]ʷ) Cs).
  { intros * HT H Hin.
    destruct (app_head T) eqn:Eh; try discriminate.
    - unfold cls_nest in H.
      destruct (grp _ _) as [m |] eqn:Eg; [| discriminate ].
      destruct (m <=? _) eqn:Em; [| discriminate ].
      destruct (img_pats _ (List.firstn m _)) as [Cs1 |] eqn:EC; [| discriminate ].
      destruct (img_pats _ (List.skipn m _)) as [Ns |] eqn:EN; [| discriminate ].
      destruct (selfs_occur _ _ _); [| discriminate ].
      injection H as <-; destruct Hin as [[= <- <- <-] | []].
      exists m; repeat split; [ exact Eg | apply Nat.leb_le; exact Em | exact (img_pats_spec _ _ _ EC) ].
    - unfold cls_self in H; destruct (_ && _)%bool; [| discriminate ].
      destruct (list_eq_dec _ _ _); [| discriminate ].
      destruct (img_pats _ _); cbn in H; [ injection H as <-; destruct Hin | discriminate ].
    - unfold cls_record_view in H.
      destruct (recs _) as [m |]; [| discriminate ].
      destruct (Nat.eqb _ _); [| discriminate ].
      destruct (img_pats _ _); [| discriminate ].
      destruct (_ && _)%bool; [| discriminate ].
      injection H as <-; destruct Hin as [[=] | []]. }
  intros grp recs nu np n pat T; induction T; intros d t qc0 k0 Cs0 Hcl Hin.
  all: try (match type of Hcl with cls_sh _ _ _ _ _ _ _ ?T0 = _ =>
              destruct (Hnest grp recs nu np n pat d T0 t qc0 k0 Cs0 ltac:(intros ? ? [=]) Hcl Hin) as (mlen & Hh & Hg & Hm & HC) end;
            exists nil; eexists; exists mlen; cbn [pis List.length]; rewrite Nat.add_0_r;
            split; [ reflexivity |];
            repeat split; [ intros ? ? [=] | exact Hh | exact Hg | exact Hm | exact HC ]).
  (* the [Π]: its codomain under one more domain *)
  cbn [cls_sh] in Hcl.
  destruct (img_pat _ T1) as [B0 |]; [| discriminate ].
  destruct (cls_sh grp recs nu np n pat (S d) T2) as [t' |] eqn:Et; cbn in Hcl; [ injection Hcl as <- | discriminate ].
  destruct (IHT2 _ _ _ _ _ Et Hin) as (Bs & E & m & -> & HE & Hh & Hg & Hm & HC).
  exists (T1 :: Bs), E, m; cbn [pis List.length]; repeat split; try assumption.
  rewrite HC; replace (d + S (List.length Bs)) with (S d + List.length Bs) by lia; reflexivity.
Qed.

(** A shape the classification finds a record view [(qr, Is)] in ends,
    past its domains, in the record type at [qr] at all its parameters,
    which are [Is] weakened past the domains, the arguments before and
    the member's non-uniform parameters, a [Self] occurring in them only
    where a type former or a [Π] takes it. *)
Lemma cls_sh_record_view : forall grp recs nu np n pat T d t qr Is,
    cls_sh grp recs nu np n pat d T = Some t -> In (vk_record qr Is) (rptyp_view t) ->
    exists Bs E, T = pis Bs E /\ (forall B C, E <> a_pi B C) /\ app_head E = a_record qr /\
      recs qr = Some (List.length (app_args E)) /\ selfs_guarded nu n Is = true /\
      app_args E = List.map (fun C => C[wk_pat (List.repeat true (d + List.length Bs + List.length pat + (np - nu)))]ʷ) Is.
Proof.
  (* a shape that is no [Π] ends here *)
  assert (Hrec : forall grp recs nu np n pat d T t qr Is, (forall B C, T <> a_pi B C) ->
      match app_head T with
      | a_var x => cls_self nu np n pat d x (app_args T)
      | a_ind qc k => cls_nest grp nu np n pat d qc k (app_args T)
      | a_record qr => cls_record_view recs nu np n pat d qr (app_args T)
      | _ => None
      end = Some t -> In (vk_record qr Is) (rptyp_view t) ->
      app_head T = a_record qr /\ recs qr = Some (List.length (app_args T)) /\ selfs_guarded nu n Is = true /\
        app_args T = List.map (fun C => C[wk_pat (List.repeat true (d + List.length pat + (np - nu)))]ʷ) Is).
  { intros * HT H Hin.
    destruct (app_head T) eqn:Eh; try discriminate.
    - unfold cls_nest in H.
      destruct (grp _ _) as [m |]; [| discriminate ].
      destruct (m <=? _); [| discriminate ].
      destruct (img_pats _ (List.firstn m _)); [| discriminate ].
      destruct (img_pats _ (List.skipn m _)); [| discriminate ].
      destruct (selfs_occur _ _ _); [| discriminate ].
      injection H as <-; destruct Hin as [[=] | []].
    - unfold cls_self in H; destruct (_ && _)%bool; [| discriminate ].
      destruct (list_eq_dec _ _ _); [| discriminate ].
      destruct (img_pats _ _); cbn in H; [ injection H as <-; destruct Hin | discriminate ].
    - unfold cls_record_view in H.
      destruct (recs _) as [m |] eqn:Em; [| discriminate ].
      destruct (Nat.eqb m _) eqn:Eml; [| discriminate ].
      destruct (img_pats _ _) as [Is1 |] eqn:EI; [| discriminate ].
      destruct (selfs_occur _ _ _ && selfs_guarded _ _ _)%bool eqn:Eg; [| discriminate ].
      injection H as <-; destruct Hin as [[= <- <-] | []].
      apply Nat.eqb_eq in Eml; subst m; apply andb_prop in Eg as [_ Eg].
      repeat split; [ exact Em | exact Eg | exact (img_pats_spec _ _ _ EI) ]. }
  intros grp recs nu np n pat T; induction T; intros d t qr0 Is0 Hcl Hin.
  all: try (match type of Hcl with cls_sh _ _ _ _ _ _ _ ?T0 = _ =>
              destruct (Hrec grp recs nu np n pat d T0 t qr0 Is0 ltac:(intros ? ? [=]) Hcl Hin) as (Hh & Hg & Hgu & HC) end;
            exists nil; eexists; cbn [pis List.length]; rewrite Nat.add_0_r;
            split; [ reflexivity |];
            repeat split; [ intros ? ? [=] | exact Hh | exact Hg | exact Hgu | exact HC ]).
  (* the [Π]: its codomain under one more domain *)
  cbn [cls_sh] in Hcl.
  destruct (img_pat _ T1) as [B0 |]; [| discriminate ].
  destruct (cls_sh grp recs nu np n pat (S d) T2) as [t' |] eqn:Et; cbn in Hcl; [ injection Hcl as <- | discriminate ].
  destruct (IHT2 _ _ _ _ Et Hin) as (Bs & E & -> & HE & Hh & Hg & Hgu & HC).
  exists (T1 :: Bs), E; cbn [pis List.length]; repeat split; try assumption.
  rewrite HC; replace (d + S (List.length Bs)) with (S d + List.length Bs) by lia; reflexivity.
Qed.

(** So does an argument the classification finds a nested occurrence
    in. *)
Lemma cls_arg_view : forall grp recs nu np n pat T g qc k Cs,
    cls_arg grp recs nu np n pat T = Some g -> In (vk_ind qc k Cs) (rcarg_view g) ->
    exists Bs E m, T = pis Bs E /\ (forall B C, E <> a_pi B C) /\ app_head E = a_ind qc k /\ grp qc k = Some m /\
      m <= List.length (app_args E) /\
      List.firstn m (app_args E) = List.map (fun C => C[wk_pat (List.repeat true (List.length Bs + List.length pat + (np - nu)))]ʷ) Cs.
Proof.
  intros * H Hin; unfold cls_arg in H.
  destruct (img_pat _ T); [ injection H as <-; destruct Hin |].
  destruct (cls_sh grp recs nu np n pat 0 T) as [t |] eqn:Et; cbn in H; [ injection H as <- | discriminate ].
  exact (cls_sh_view _ _ _ _ _ _ _ _ _ _ _ _ Et Hin).
Qed.

(** And one it finds a record view in. *)
Lemma cls_arg_record_view : forall grp recs nu np n pat T g qr Is,
    cls_arg grp recs nu np n pat T = Some g -> In (vk_record qr Is) (rcarg_view g) ->
    exists Bs E, T = pis Bs E /\ (forall B C, E <> a_pi B C) /\ app_head E = a_record qr /\
      recs qr = Some (List.length (app_args E)) /\ selfs_guarded nu n Is = true /\
      app_args E = List.map (fun C => C[wk_pat (List.repeat true (List.length Bs + List.length pat + (np - nu)))]ʷ) Is.
Proof.
  intros * H Hin; unfold cls_arg in H.
  destruct (img_pat _ T); [ injection H as <-; destruct Hin |].
  destruct (cls_sh grp recs nu np n pat 0 T) as [t |] eqn:Et; cbn in H; [ injection H as <- | discriminate ].
  exact (cls_sh_record_view _ _ _ _ _ _ _ _ _ _ _ Et Hin).
Qed.

(** The classification as written, with no filed group and no record,
    finds no nested occurrence. *)
Lemma cls_arg_none_view : forall nu np n pat T g, cls_arg grp_none rec_none nu np n pat T = Some g -> rcarg_view g = nil.
Proof.
  intros * H; destruct (rcarg_view g) as [| [qc k Cs | qr Is] zs] eqn:E; [ reflexivity | |].
  - destruct (cls_arg_view _ _ _ _ _ _ _ _ qc k Cs H ltac:(rewrite E; left; reflexivity)) as (? & ? & ? & _ & _ & _ & Hg & _).
    discriminate.
  - destruct (cls_arg_record_view _ _ _ _ _ _ _ _ qr Is H ltac:(rewrite E; left; reflexivity)) as (? & ? & _ & _ & _ & Hg & _).
    discriminate.
Qed.

(** ** Typed Views

    A view [(qc, k, Cs)] over the context [Γu] of a group declaration (its
    uniform parameters, the [Self]s and the frames' parameters) is typed
    when [qc] files a group whose member [k] is declared, and [Cs] are
    typed at its uniform telescope there. *)
#[warnings="-cannot-define-projection"]
Record view_typed (Θ : gdeps) (Ξ : gstack) (Γu : ctx) (qc : qname) (k : nat) (Cs : list exp) : Prop := mk_view_typed
  { (** The container's group *)
    typed_group : ind_decl
    (** It is filed at [qc] *)
  ; typed_lookup : ind_lookup Θ Ξ qc = Some typed_group
    (** The member [k] is declared *)
  ; typed_declared : k < ind_ndecl typed_group
    (** As many arguments as uniform parameters *)
  ; typed_length : List.length Cs = ind_nu typed_group
    (** Each argument is typed at the uniform telescope at those before *)
  ; typed_args : forall j C T, List.nth_error Cs j = Some C ->
      List.nth_error (tele_insts (ind_uparams typed_group) Id Cs) j = Some T -> Θ ⍮ Ξ ⍮ Γu ⊢ C : T
    (** The context is well formed *)
  ; typed_ctx : ⊢ Θ ⍮ Ξ ⍮ Γu }.

(** A typed view whose arguments are their own normal forms: the views
    the search meets after the declaration's own instances. *)
#[warnings="-cannot-define-projection"]
Record view_inv (Θ : gdeps) (Ξ : gstack) (Γu : ctx) (qc : qname) (k : nat) (Cs : list exp) : Prop := mk_view_inv
  { (** It is typed *)
    inv_typed : view_typed Θ Ξ Γu qc k Cs
    (** The normal forms of its arguments *)
  ; inv_normal_forms : list nf
    (** They are the arguments' normal forms at the uniform telescope *)
  ; inv_nbes : forall D, ind_lookup Θ Ξ qc = Some D -> nbes Θ Ξ Γu Cs (tele_insts (ind_uparams D) Id Cs) inv_normal_forms
    (** And the arguments themselves *)
  ; inv_normal : Cs = List.map nf_to_exp inv_normal_forms }.

(** A record view [(qr, Is)] over [Γu] is typed when [qr] files a record
    and [Is] are typed at its parameters there. *)
#[warnings="-cannot-define-projection"]
Record record_view_typed (Θ : gdeps) (Ξ : gstack) (Γu : ctx) (qr : qname) (Is : list exp) : Prop := mk_record_view_typed
  { (** The record *)
    typed_record : record_decl
    (** It is filed at [qr] *)
  ; typed_record_lookup : record_lookup Θ Ξ qr = Some typed_record
    (** As many arguments as parameters *)
  ; typed_record_length : List.length Is = List.length (record_params typed_record)
    (** Each argument is typed at the parameters at those before *)
  ; typed_record_args : forall j C T, List.nth_error Is j = Some C ->
      List.nth_error (tele_insts (record_params typed_record) Id Is) j = Some T -> Θ ⍮ Ξ ⍮ Γu ⊢ C : T
    (** The context is well formed *)
  ; typed_record_ctx : ⊢ Θ ⍮ Ξ ⍮ Γu }.

(** A typed record view whose arguments are their own normal forms. *)
#[warnings="-cannot-define-projection"]
Record record_view_inv (Θ : gdeps) (Ξ : gstack) (Γu : ctx) (qr : qname) (Is : list exp) : Prop := mk_record_view_inv
  { (** It is typed *)
    record_inv_typed : record_view_typed Θ Ξ Γu qr Is
    (** The normal forms of its arguments *)
  ; record_inv_normal_forms : list nf
    (** They are the arguments' normal forms at the parameters *)
  ; record_inv_nbes : forall Rr, record_lookup Θ Ξ qr = Some Rr ->
      nbes Θ Ξ Γu Is (tele_insts (record_params Rr) Id Is) record_inv_normal_forms
    (** And the arguments themselves *)
  ; record_inv_normal : Is = List.map nf_to_exp record_inv_normal_forms }.

(** The invariant of a view of either kind. *)
Definition key_inv (Θ : gdeps) (Ξ : gstack) (Γu : ctx) (x : view_key) : Prop :=
  match x with
  | vk_ind qc k Cs => view_inv Θ Ξ Γu qc k Cs
  | vk_record qr Is => record_view_inv Θ Ξ Γu qr Is
  end.

Lemma unwk_wk_pat : forall pat, wk_eq (wk_compose (wk_pat pat) (unwk_pat pat)) wk_id.
Proof.
  induction pat as [| [] pat IH]; intros x; cbn; [ reflexivity | |].
  - unfold wk_compose, wk_shift in *; cbn; apply IH.
  - destruct x as [| x]; cbn; [ reflexivity |].
    unfold wk_compose in IH; rewrite IH; reflexivity.
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  (** The arguments of the normal form of an inductive type are the normal
      forms of its arguments, each at its type. *)
  Lemma nbe_ind_args : forall Γ p D k Mk Ms Rs,
      ind_lookup gc_deps gc_stack p = Some D -> ind_member D k = Some Mk -> List.length Ms = im_np D Mk ->
      (forall j P T, List.nth_error Ms j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ms) j = Some T ->
         Γ ⊢ P : T) ->
      nbe_ty_f Γ (apps (a_ind p k) Ms) (nf_indty p k Rs) ->
      forall j P T, List.nth_error Ms j = Some P -> List.nth_error (tele_insts (im_params D Mk) Id Ms) j = Some T ->
        exists R, List.nth_error Rs j = Some R /\ nbe_f Γ P T R.
  Proof.
    intros * Hl Hk HMl HMs HW j P T HP HT.
    assert (HΓ : ⊢ Γ) by (pose proof (HMs j P T HP HT); gen_presups; assumption).
    destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [Hdt Hc].
    destruct HW as [ρ m Hinit Ea Hr].
    apply Modules.eval_apps_exp in Ea as (f & ms & Ef & Ems & Eap).
    inversion Ef; subst.
    apply eval_apps_ind_inv in Eap; cbn in Eap; subst.
    inversion Hr; subst.
    match goal with H4 : ind_lookup _ _ p = Some ?D0, H5 : ind_member ?D0 k = Some ?M0 |- _ =>
      rewrite Hl in H4; injection H4 as <-; rewrite Hk in H5; injection H5 as <- end.
    pose proof HT as HT0; apply tele_insts_nth in HT0 as (A & HA & ->).
    destruct (eval_exps_nth _ _ _ _ _ Ems HP) as (v & Hv & Ev).
    match goal with H7 : Rps ms at _ in _ ⍮ _ ⍮ nil ⍮ _ ↘ Rs |- _ =>
      destruct (read_ps_nth _ _ _ _ _ _ _ H7 _ _ _ HA Hv) as (a & V & Ea & HV & HnV) end.
    exists V; split; [ exact HnV |].
    (** [P] at its type, at the initial environment *)
    pose proof (completeness_fundamental_exp _ _ _ (HMs j P _ HP HT)) as HPs.
    destruct (rel_exp_under_ctx_at_initial_env HPs) as (ρ1 & i & R & t & m1 & m2 & Hi1 & Et & Em1 & Em2 & Htt & Hm).
    pose proof (functional_initial_env _ _ Hi1 _ Hinit) as ->.
    pose proof (functional_eval_exp _ _ _ _ Em1 Ev) as ->.
    pose proof (functional_eval_exp _ _ _ _ Em2 Ev) as ->.
    (** the closed prefix of the telescope the [j]-th type is over *)
    assert (Hsplit : exists Δhi C0, im_params D Mk = Δhi ++ ce_ass A :: C0 /\ List.length C0 = j).
    { destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
      exists (List.rev l2), (List.rev l1); split; [| rewrite List.length_rev; exact Hl1 ].
      rewrite <- (List.rev_involutive (im_params D Mk)), Hrev, List.rev_app_distr; cbn; rewrite <- List.app_assoc; reflexivity. }
    destruct Hsplit as (Δhi & C0 & HΔ & HlC0).
    pose proof (decl_closed_params_ass _ _ _ Hc Hk) as Hass.
    pose proof (completeness_fundamental_ctx _ (member_params_wf _ _ _ _ _ Hdt Hk)) as HΔs.
    rewrite HΔ in Hass, HΔs.
    pose proof (rel_ctx_wf_app_r _ _ HΔs) as HAC.
    destruct (rel_ctx_wf_ass_inv HAC) as [jA HAs].
    pose proof (rel_ctx_wf_tail HAC) as HC0.
    assert (HC0a : tele_ass C0) by (apply List.Forall_app in Hass as [_ H]; inversion H; assumption).
    assert (Hjl : j < List.length Ms).
    { rewrite HMl, <- length_im_params, HΔ, List.length_app; cbn; lia. }
    (** the arguments before, an instance of the prefix *)
    assert (Hpre : forall k0 N T0, List.nth_error (List.firstn j Ms) k0 = Some N ->
              List.nth_error (tele_insts C0 Id (List.firstn j Ms)) k0 = Some T0 -> Γ ⊨ N : T0).
    { intros k0 N T0 HN HT0.
      assert (Hk0 : k0 < j) by (assert (Hn : List.nth_error (List.firstn j Ms) k0 <> None) by congruence;
                                 apply List.nth_error_Some in Hn; rewrite List.length_firstn in Hn; lia).
      apply completeness_fundamental_exp, (HMs k0).
      - rewrite List.nth_error_firstn in HN; destruct (k0 <? j) eqn:E; [ exact HN | discriminate ].
      - rewrite <- (List.firstn_skipn j Ms), HΔ.
        replace (Δhi ++ ce_ass A :: C0) with ((Δhi ++ ce_ass A :: nil) ++ C0) by (rewrite <- List.app_assoc; reflexivity).
        rewrite tele_insts_app by (try exact HC0a; rewrite List.length_firstn; lia).
        rewrite List.nth_error_app1; [ exact HT0 |].
        rewrite length_tele_insts by exact HC0a; rewrite List.length_firstn; lia. }
    pose proof (completeness_fundamental_ctx _ HΓ) as HΓs.
    pose proof (gsub_closed_inst C0 Γ (List.firstn j Ms) HC0a HC0 HΓs ltac:(rewrite List.length_firstn; lia) Hpre) as Hg.
    assert (Efm : forall n Ms0 ms0, ⟦ Ms0 ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms0 ->
              ⟦ List.firstn n Ms0 ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ List.firstn n ms0).
    { induction n as [| n IHn]; intros Ms0 ms0 H0; [ cbn; constructor |].
      destruct H0; cbn; constructor; auto. }
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
    destruct (rel_ctx_wf_per_ctx_env HC0) as [RK HRK].
    destruct (per_ctx_then_per_env_initial_env HRΓ) as (ρa & ρb & Hia & Hib & Hab).
    pose proof (functional_initial_env _ _ Hia _ Hinit) as ->.
    pose proof (functional_initial_env _ _ Hib _ Hinit) as ->.
    assert (Eτ : ⟦ sb_of_list Id (List.firstn j Ms) ⟧s ρ ↘ env_args ρ (List.firstn j ms))
      by (apply eval_sb_of_list; [ apply eval_sub_id | apply Efm, Ems ]).
    pose proof (gsub_valid Hg) as Hτ.
    destruct (closed_app_sem C0 Γ HC0a HC0 HΓs) as [HCΓ Hres].
    destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ].
    pose proof (rel_sub_under_ctx_at' Hτ HRΓ HRCΓ _ _ _ _ Hab Eτ Eτ) as HBB.
    pose proof (Hres _ _ HRK HRCΓ _ _ HBB) as HBBK.
    assert (HlF : List.length (List.firstn j ms) = List.length C0) by (rewrite List.length_firstn; lia).
    pose proof (closed_env_base C0 RK _ _ ρ ρ ρ nil HC0a HC0 HRK HlF HlF HBBK) as HF.
    (** the type of [P] at [ρ] is related to the telescope's at the values
        before, the type readback reads [P]'s value at *)
    destruct (closed_typ_inst nil C0 Γ A jA (sb_of_list Id (List.firstn j Ms)) RΓ RK RΓ ρ nil
                (env_args ρ (List.firstn j ms)) (env_args nil (List.firstn j ms))
                HC0a HC0 HC0a HC0 HΓs HRΓ HRK HRΓ HAs Hτ Hab eq_refl Eτ HF) as (a1 & b & Ea1 & Eb & Hab1).
    cbn [sb_qn env_args] in Ea1.
    pose proof (functional_eval_exp _ _ _ _ Ea1 Et) as ->.
    pose proof (functional_eval_exp _ _ _ _ Eb Ea) as ->.
    destruct Hab1 as [R1 HR1].
    assert (Hm1 : R1 v v) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ Htt HR1); exact Hm).
    destruct (per_elem_then_per_top HR1 Hm1 (List.length Γ)) as (W & HW1 & HW2).
    assert (W = V) as -> by (eapply (proj1 functional_read); eassumption).
    econstructor; eassumption.
  Qed.

  (** The arguments of the normal form of a record type are the normal
      forms of its arguments, each at its type. *)
  Lemma nbe_record_args : forall Γ p R Ms Rs (i : nat),
      record_lookup gc_deps gc_stack p = Some R -> Γ ⊢ apps (a_record p) Ms : Typeω@i ->
      nbe_ty_f Γ (apps (a_record p) Ms) (nf_record p Rs) ->
      forall j P T, List.nth_error Ms j = Some P -> List.nth_error (tele_insts (record_params R) Id Ms) j = Some T ->
        exists R', List.nth_error Rs j = Some R' /\ nbe_f Γ P T R'.
  Proof.
    intros * Hl HT HW j P T HP HTj.
    pose proof (wf_record_apps_len _ _ _ _ _ Hl HT) as HMl.
    pose proof (wf_record_apps_inv _ _ _ _ _ Hl HT HMl) as HMs.
    destruct (wf_record_inversion (wf_record_own_apps _ _ _ _ _ _ _ HT Hl)) as [R0 Hl0 _ Hass _ _ HF _ _ _].
    rewrite Hl in Hl0; injection Hl0 as <-.
    assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
    destruct HW as [ρ m Hinit Ea Hr].
    apply Modules.eval_apps_exp in Ea as (f & ms & Ef & Ems & Eap).
    inversion Ef; subst.
    apply eval_apps_record_inv in Eap; cbn in Eap; subst.
    inversion Hr; subst.
    match goal with H4 : record_lookup _ _ p = Some ?R1 |- _ => rewrite Hl in H4; injection H4 as <- end.
    pose proof HTj as HT0; apply tele_insts_nth in HT0 as (A & HA & ->).
    destruct (eval_exps_nth _ _ _ _ _ Ems HP) as (v & Hv & Ev).
    match goal with H7 : Rps ms at _ in _ ⍮ _ ⍮ nil ⍮ _ ↘ Rs |- _ =>
      destruct (read_ps_nth _ _ _ _ _ _ _ H7 _ _ _ HA Hv) as (a & V & Ea & HV & HnV) end.
    exists V; split; [ exact HnV |].
    (** [P] at its type, at the initial environment *)
    pose proof (completeness_fundamental_exp _ _ _ (HMs j P _ HP HTj)) as HPs.
    destruct (rel_exp_under_ctx_at_initial_env HPs) as (ρ1 & i' & R1 & t & m1 & m2 & Hi1 & Et & Em1 & Em2 & Htt & Hm).
    pose proof (functional_initial_env _ _ Hi1 _ Hinit) as ->.
    pose proof (functional_eval_exp _ _ _ _ Em1 Ev) as ->.
    pose proof (functional_eval_exp _ _ _ _ Em2 Ev) as ->.
    (** the closed prefix of the telescope the [j]-th type is over *)
    assert (Hsplit : exists Δhi C0, record_params R = Δhi ++ ce_ass A :: C0 /\ List.length C0 = j).
    { destruct (List.nth_error_split _ _ HA) as (l1 & l2 & Hrev & Hl1).
      exists (List.rev l2), (List.rev l1); split; [| rewrite List.length_rev; exact Hl1 ].
      rewrite <- (List.rev_involutive (record_params R)), Hrev, List.rev_app_distr; cbn; rewrite <- List.app_assoc; reflexivity. }
    destruct Hsplit as (Δhi & C0 & HΔ & HlC0).
    pose proof (completeness_fundamental_ctx _ (ctx_app_wf_tail _ _ _ _ HF)) as HΔs.
    rewrite HΔ in Hass, HΔs.
    pose proof (rel_ctx_wf_app_r _ _ HΔs) as HAC.
    destruct (rel_ctx_wf_ass_inv HAC) as [jA HAs].
    pose proof (rel_ctx_wf_tail HAC) as HC0.
    assert (HC0a : tele_ass C0) by (apply List.Forall_app in Hass as [_ H]; inversion H; assumption).
    assert (Hjl : j < List.length Ms) by (rewrite HMl, HΔ, List.length_app; cbn; lia).
    (** the arguments before, an instance of the prefix *)
    assert (Hpre : forall k0 N T0, List.nth_error (List.firstn j Ms) k0 = Some N ->
              List.nth_error (tele_insts C0 Id (List.firstn j Ms)) k0 = Some T0 -> Γ ⊨ N : T0).
    { intros k0 N T0 HN HT0.
      assert (Hk0 : k0 < j) by (assert (Hn : List.nth_error (List.firstn j Ms) k0 <> None) by congruence;
                                 apply List.nth_error_Some in Hn; rewrite List.length_firstn in Hn; lia).
      apply completeness_fundamental_exp, (HMs k0).
      - rewrite List.nth_error_firstn in HN; destruct (k0 <? j) eqn:E; [ exact HN | discriminate ].
      - rewrite <- (List.firstn_skipn j Ms), HΔ.
        replace (Δhi ++ ce_ass A :: C0) with ((Δhi ++ ce_ass A :: nil) ++ C0) by (rewrite <- List.app_assoc; reflexivity).
        rewrite tele_insts_app by (try exact HC0a; rewrite List.length_firstn; lia).
        rewrite List.nth_error_app1; [ exact HT0 |].
        rewrite length_tele_insts by exact HC0a; rewrite List.length_firstn; lia. }
    pose proof (completeness_fundamental_ctx _ HΓ) as HΓs.
    pose proof (gsub_closed_inst C0 Γ (List.firstn j Ms) HC0a HC0 HΓs ltac:(rewrite List.length_firstn; lia) Hpre) as Hg.
    assert (Efm : forall n Ms0 ms0, ⟦ Ms0 ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ ms0 ->
              ⟦ List.firstn n Ms0 ⟧* gc_deps ⍮ gc_stack ⍮ ρ ↘ List.firstn n ms0).
    { induction n as [| n IHn]; intros Ms0 ms0 H0; [ cbn; constructor |].
      destruct H0; cbn; constructor; auto. }
    destruct (rel_ctx_wf_per_ctx_env HΓs) as [RΓ HRΓ].
    destruct (rel_ctx_wf_per_ctx_env HC0) as [RK HRK].
    destruct (per_ctx_then_per_env_initial_env HRΓ) as (ρa & ρb & Hia & Hib & Hab).
    pose proof (functional_initial_env _ _ Hia _ Hinit) as ->.
    pose proof (functional_initial_env _ _ Hib _ Hinit) as ->.
    assert (Eτ : ⟦ sb_of_list Id (List.firstn j Ms) ⟧s ρ ↘ env_args ρ (List.firstn j ms))
      by (apply eval_sb_of_list; [ apply eval_sub_id | apply Efm, Ems ]).
    pose proof (gsub_valid Hg) as Hτ.
    destruct (closed_app_sem C0 Γ HC0a HC0 HΓs) as [HCΓ Hres].
    destruct (rel_ctx_wf_per_ctx_env HCΓ) as [RCΓ HRCΓ].
    pose proof (rel_sub_under_ctx_at' Hτ HRΓ HRCΓ _ _ _ _ Hab Eτ Eτ) as HBB.
    pose proof (Hres _ _ HRK HRCΓ _ _ HBB) as HBBK.
    assert (HlF : List.length (List.firstn j ms) = List.length C0) by (rewrite List.length_firstn; lia).
    pose proof (closed_env_base C0 RK _ _ ρ ρ ρ nil HC0a HC0 HRK HlF HlF HBBK) as HF0.
    (** the type of [P] at [ρ] is related to the telescope's at the values
        before, the type readback reads [P]'s value at *)
    destruct (closed_typ_inst nil C0 Γ A jA (sb_of_list Id (List.firstn j Ms)) RΓ RK RΓ ρ nil
                (env_args ρ (List.firstn j ms)) (env_args nil (List.firstn j ms))
                HC0a HC0 HC0a HC0 HΓs HRΓ HRK HRΓ HAs Hτ Hab eq_refl Eτ HF0) as (a1 & b & Ea1 & Eb & Hab1).
    cbn [sb_qn env_args] in Ea1.
    pose proof (functional_eval_exp _ _ _ _ Ea1 Et) as ->.
    pose proof (functional_eval_exp _ _ _ _ Eb Ea) as ->.
    destruct Hab1 as [R2 HR2].
    assert (Hm1 : R2 v v) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ Htt HR2); exact Hm).
    destruct (per_elem_then_per_top HR2 Hm1 (List.length Γ)) as (W & HW1 & HW2).
    assert (W = V) as -> by (eapply (proj1 functional_read); eassumption).
    econstructor; eassumption.
  Qed.

  (** ** The Pieces of a Normal Form of a Type *)

  Lemma wk_pat_trues : forall L, wk_eq (wk_pat (List.repeat true L)) (wk_shiftn L).
  Proof.
    induction L as [| L IH]; intros x; cbn; [ unfold wk_shiftn; lia |].
    unfold wk_compose, wk_shift; rewrite IH; unfold wk_shiftn; lia.
  Qed.

  Lemma apps_head_args : forall M, apps (app_head M) (app_args M) = M.
  Proof.
    induction M; try reflexivity.
    cbn [app_head app_args]; rewrite apps_exp_app; cbn; rewrite IHM1; reflexivity.
  Qed.

  Lemma app_head_apps : forall M Ns, app_head (apps M Ns) = app_head M.
  Proof. intros M Ns; revert M; induction Ns as [| N Ns IH]; intros M; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

  Lemma app_args_apps : forall M Ns, app_args (apps M Ns) = app_args M ++ Ns.
  Proof.
    intros M Ns; revert M; induction Ns as [| N Ns IH]; intros M; cbn; [ rewrite List.app_nil_r; reflexivity |].
    rewrite IH; cbn; rewrite <- List.app_assoc; reflexivity.
  Qed.

  Lemma member_ref_shape : forall ch H, member_ref H ch = a_true \/ exists H' x, member_ref H ch = a_mem H' x.
  Proof.
    induction ch as [| y ch IH]; intros H; [ left; reflexivity |].
    destruct ch as [| z ch']; [ right; exists H, y; reflexivity | exact (IH (me_mem H y)) ].
  Qed.

  (** A neutral is no [Π] and no inductive type. *)
  Lemma ne_head_not_ind : forall u, (forall X Y, ne_to_exp u <> a_pi X Y) /\ (forall p k, app_head (ne_to_exp u) <> a_ind p k).
  Proof.
    induction u; cbn; split; intros; try discriminate; [ apply (proj2 IHu) | |];
      match goal with |- context [qname_term ?p] =>
        unfold qname_term; destruct (member_ref_shape (q_chain p) (me_unit (q_unit p))) as [E | (H' & x & E)];
        rewrite E; discriminate end.
  Qed.

  (** The normal forms readback gives types. *)
  Inductive type_nf : nf -> Prop :=
  (** A large universe *)
  | type_nf_typ : forall i, type_nf (nf_typ i)
  (** A small universe *)
  | type_nf_univ : forall c xs, type_nf (nf_univ c xs)
  (** A type of levels *)
  | type_nf_level : forall n, type_nf (nf_level n)
  (** [⊤] *)
  | type_nf_True : type_nf nf_True
  (** [⊥] *)
  | type_nf_False : type_nf nf_False
  (** A [Π] into a type *)
  | type_nf_pi : forall A B, type_nf B -> type_nf (nf_pi A B)
  (** A member of a group at its parameters *)
  | type_nf_indty : forall p k Ms, type_nf (nf_indty p k Ms)
  (** A neutral *)
  | type_nf_neut : forall u, type_nf (nf_neut u)
  (** A record type at its parameters *)
  | type_nf_record : forall p Ms, type_nf (nf_record p Ms).

  Lemma read_typ_type_nf : forall s m W, Rtyp m in gc_deps ⍮ gc_stack ⍮ s ↘ W -> type_nf W.
  Proof. induction 1; constructor; assumption. Qed.

  Lemma nf_pi_view : forall W X Y, type_nf W -> nf_to_exp W = a_pi X Y ->
      exists W1 W2, W = nf_pi W1 W2 /\ type_nf W2 /\ nf_to_exp W1 = X /\ nf_to_exp W2 = Y.
  Proof.
    intros W X Y HW H; destruct HW; cbn in H; try discriminate.
    - injection H as <- <-; do 2 eexists; eauto.
    - destruct (List.map nf_to_exp _) using List.rev_ind; cbn in H; [ discriminate | rewrite apps_exp_app in H; discriminate ].
    - exfalso; exact (proj1 (ne_head_not_ind _) _ _ H).
    - destruct (List.map nf_to_exp _) using List.rev_ind; cbn in H; [ discriminate | rewrite apps_exp_app in H; discriminate ].
  Qed.

  Lemma nf_pis_end : forall Bs E W, type_nf W -> nf_to_exp W = pis Bs E -> exists WE, type_nf WE /\ nf_to_exp WE = E.
  Proof.
    induction Bs as [| B Bs IH]; intros E W HW H; cbn in H; [ exists W; split; assumption |].
    destruct (nf_pi_view _ _ _ HW H) as (W1 & W2 & -> & HW2 & _ & HE2); exact (IH _ _ HW2 HE2).
  Qed.

  Lemma nf_ind_view : forall W p k, type_nf W -> app_head (nf_to_exp W) = a_ind p k ->
      exists Rs, W = nf_indty p k Rs.
  Proof.
    intros W p k HW H; destruct HW; cbn in H; try discriminate.
    - rewrite app_head_apps in H; cbn in H; injection H as <- <-; eexists; reflexivity.
    - exfalso; exact (proj2 (ne_head_not_ind _) _ _ H).
    - rewrite app_head_apps in H; cbn in H; discriminate.
  Qed.

  (** A neutral is no record type. *)
  Lemma ne_head_not_record : forall u p, app_head (ne_to_exp u) <> a_record p.
  Proof.
    induction u; cbn; intros; try discriminate; try exact (IHu _);
      match goal with |- context [qname_term ?p] =>
        unfold qname_term; destruct (member_ref_shape (q_chain p) (me_unit (q_unit p))) as [E | (H' & x & E)];
        rewrite E; discriminate end.
  Qed.

  Lemma nf_record_view : forall W p, type_nf W -> app_head (nf_to_exp W) = a_record p -> exists Rs, W = nf_record p Rs.
  Proof.
    intros W p HW H; destruct HW; cbn in H; try discriminate.
    - rewrite app_head_apps in H; cbn in H; discriminate.
    - exfalso; exact (ne_head_not_record _ _ H).
    - rewrite app_head_apps in H; cbn in H; injection H as <-; eexists; reflexivity.
  Qed.

  (** The end of a typed chain of [Π]s is a type under its domains. *)
  Lemma pis_typed_inv : forall Bs Γ E (i : nat), Γ ⊢ pis Bs E : Typeω@i -> doms_ctx Bs ++ Γ ⊢ E : Typeω@i.
  Proof.
    induction Bs as [| B Bs IH]; intros Γ E i H; cbn in H |- *; [ exact H |].
    destruct (wf_pi_inversion' H) as [_ HC].
    unfold doms_ctx in *; cbn [List.map List.rev]; rewrite <- List.app_assoc; exact (IH _ _ _ HC).
  Qed.

  (** A type former applied, at a universe, is applied to all its
      parameters: its value reads back as a type only then. *)
  Lemma ind_type_length : forall Γ p D k Mk Ms (i : nat), ind_lookup gc_deps gc_stack p = Some D ->
      ind_member D k = Some Mk -> Γ ⊢ apps (a_ind p k) Ms : Typeω@i -> List.length Ms = im_np D Mk.
  Proof.
    intros * Hl Hk HT.
    destruct (soundness_ty HT) as (W & [ρ m Hinit Ea Hr] & _).
    apply Modules.eval_apps_exp in Ea as (f & ms & Ef & Ems & Eap).
    inversion Ef; subst.
    apply eval_apps_ind_inv in Eap; cbn in Eap; subst.
    inversion Hr; subst.
    match goal with H4 : ind_lookup _ _ p = Some ?D0, H5 : ind_member ?D0 k = Some ?M0 |- _ =>
      rewrite Hl in H4; injection H4 as <-; rewrite Hk in H5; injection H5 as <- end.
    rewrite <- (eval_exps_length _ _ _ Ems); assumption.
  Qed.

  (** A normal form whose weakening past a telescope of assumptions is
      typed at a weakened type is typed at the type. *)
  Lemma nf_strengthen_tele : forall Δ Γ (W : nf) T (i : nat), tele_ass Δ -> ⊢ Δ ++ Γ -> Γ ⊢ T : Typeω@i ->
      Δ ++ Γ ⊢ (W : exp)[wk_shiftn (List.length Δ)]ʷ : T[wk_shiftn (List.length Δ)]ʷ -> Γ ⊢ W : T.
  Proof.
    induction Δ as [| e Δ IH]; intros Γ W T i Hass HΔ HT HW.
    - cbn [List.length List.app] in HW |- *;
        rewrite !(exp_wk_id_ext _ (wk_shiftn 0)) in HW by (intros x; unfold wk_shiftn, wk_id; lia); exact HW.
    - assert (He : exists A, e = ce_ass A) by (inversion Hass as [| ? ? He _]; exact He).
      destruct He as [A ->].
      assert (Hass' : tele_ass Δ) by (inversion Hass; assumption).
      cbn [List.app] in HΔ |- *; cbn [List.length] in HW.
      pose proof (ctx_decomp_tail HΔ) as HΔ'.
      apply (IH Γ W T i Hass' HΔ' HT).
      assert (Hsh : forall M, M[wk_shiftn (S (List.length Δ))]ʷ = M[wk_shiftn (List.length Δ)]ʷ[↑]ʷ)
        by (intros M; symmetry; apply exp_wk_wk_ext; intros x; unfold wk_compose, wk_shiftn, wk_shift; lia).
      rewrite !Hsh in HW.
      rewrite <- (proj1 nf_wk_to_exp) in HW |- *.
      eapply nf_strengthen_shift; [ exact HΔ | | exact HW ].
      eapply (wk_preserves_exp _ _ _ _ Typeω@i); [ exact HT | apply wf_wk_shiftn_app; [ exact HΔ' | eapply ctx_app_wf_tail; exact HΔ' ] ].
  Qed.

  (** ** The Instances the Classification Meets Are Typed *)

  (** An argument type in a context [Δ ++ Γu], [Δ] the arguments before
      it and the member's non-uniform parameters, classified as its normal
      form: each nested occurrence it meets is a typed view over [Γu]. *)
  Theorem nest_view_typed : forall Δ Γu T W (i : nat) nu np n pat g qc k Cs,
      tele_ass Δ -> List.length Δ = List.length pat + (np - nu) ->
      Δ ++ Γu ⊢ T : Typeω@i -> nbe_ty_f (Δ ++ Γu) T W ->
      cls_arg (grp_info gc_deps gc_stack) (rec_info gc_deps gc_stack) nu np n pat (nf_to_exp W) = Some g ->
      In (vk_ind qc k Cs) (rcarg_view g) ->
      view_typed gc_deps gc_stack Γu qc k Cs.
  Proof.
    intros * Hass Hlen HT HW Hcls Hin.
    destruct (cls_arg_view _ _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs & E & m & HWe & HE & Hh & Hg & Hm & HC).
    unfold grp_info in Hg.
    destruct (ind_lookup gc_deps gc_stack qc) as [D2 |] eqn:Hl2; [| discriminate ].
    destruct (k <? ind_ndecl D2) eqn:Hk2; [ injection Hg as <- | discriminate ].
    apply Nat.ltb_lt in Hk2.
    destruct (List.nth_error (ind_members D2) k) as [Mk2 |] eqn:HMk2;
      [| apply List.nth_error_None in HMk2; pose proof (ind_ndecl_le D2); lia ].
    change (ind_member D2 k = Some Mk2) in HMk2.
    (** the normal form is a type, so is the end of its [Π]s, under them *)
    pose proof (soundness_ty' HT HW) as HTW.
    assert (HWt : Δ ++ Γu ⊢ nf_to_exp W : Typeω@i) by (gen_presups; assumption).
    rewrite HWe in HWt.
    pose proof (pis_typed_inv _ _ _ _ HWt) as HEt.
    destruct HW as [ρ0 m0 Hi0 Ee0 Hr0].
    destruct (nf_pis_end _ _ _ (read_typ_type_nf _ _ _ Hr0) HWe) as (WE & HWE & HWEe).
    rewrite <- HWEe in Hh; destruct (nf_ind_view _ _ _ HWE Hh) as [Rs ->].
    cbn [nf_to_exp] in HWEe; subst E.
    rewrite app_args_apps in HC, Hm; cbn [app_args List.app] in HC, Hm.
    (** its parameters are typed *)
    pose proof (ind_type_length _ _ _ _ _ _ _ Hl2 HMk2 HEt) as HRl.
    pose proof (wf_ind_apps_inv _ _ _ _ _ _ _ Hl2 HMk2 HEt HRl) as HRt.
    assert (HΓe : ⊢ doms_ctx Bs ++ Δ ++ Γu) by (gen_presups; assumption).
    assert (HΓu : ⊢ Γu) by (rewrite List.app_assoc in HΓe; eapply ctx_app_wf_tail; exact HΓe).
    destruct (decl_of_lookup _ _ _ _ _ HΓu Hl2) as [Hdt Hc2].
    assert (HCl : List.length Cs = ind_nu D2).
    { apply (f_equal (@List.length _)) in HC; rewrite List.length_map, List.length_firstn in HC; lia. }
    set (L := List.length Bs + List.length pat + (np - nu)) in *.
    assert (HLe : List.length (doms_ctx Bs ++ Δ) = L)
      by (unfold L, doms_ctx; rewrite List.length_app, List.length_rev, List.length_map; lia).
    apply (mk_view_typed _ _ _ _ _ _ D2 Hl2 Hk2 HCl); [| exact HΓu ].
    (** and the uniform ones, strengthened past the [Π]s' domains, the
        arguments before and the member's non-uniform parameters, are
        typed over [Γu] *)
    apply (tele_insts_typed_all (ind_uparams D2) nil Γu Id Cs (decl_typed_ass _ _ _ Hdt)
             ltac:(rewrite List.app_nil_r; exact (decl_typed_uparams_field _ _ _ Hdt)) (wf_sub_to_nil _ _ _ HΓu)).
    intros j N T0 HN HT0 [i0 HT0t].
    assert (Hj : j < ind_nu D2) by (rewrite <- HCl; apply List.nth_error_Some; congruence).
    set (φ := wk_pat (List.repeat true L)) in *.
    assert (HNw : List.nth_error (List.map nf_to_exp Rs) j = Some N[φ]ʷ).
    { rewrite <- (List.firstn_skipn (ind_nu D2) (List.map nf_to_exp Rs)), List.nth_error_app1
        by (rewrite List.length_firstn; lia).
      rewrite HC, List.nth_error_map, HN; reflexivity. }
    assert (HTw : List.nth_error (tele_insts (im_params D2 Mk2) Id (List.map nf_to_exp Rs)) j = Some T0[φ]ʷ).
    { rewrite <- (List.firstn_skipn (ind_nu D2) (List.map nf_to_exp Rs)).
      unfold im_params; rewrite tele_insts_app by (try exact (decl_typed_ass _ _ _ Hdt); rewrite List.length_firstn; unfold ind_nu in *; lia).
      rewrite List.nth_error_app1 by (rewrite length_tele_insts by exact (decl_typed_ass _ _ _ Hdt); rewrite List.length_firstn; unfold ind_nu in *; lia).
      rewrite HC.
      rewrite (List.map_ext (fun C => C[φ]ʷ) (fun M => M[ι φ]) (fun M => eq_sym (exp_sub_of_wk M φ))).
      rewrite (tele_insts_closed_sub _ _ _ _ _ (decl_typed_ass _ _ _ Hdt) (decl_closed_uparams _ Hc2) HT0), exp_sub_of_wk; reflexivity. }
    pose proof (HRt _ _ _ HNw HTw) as HNt.
    rewrite List.nth_error_map in HNw.
    destruct (List.nth_error Rs j) as [R |] eqn:HR; cbn in HNw; [ injection HNw as HRN | discriminate ].
    assert (HNR : N = nf_to_exp (nf_wk (unwk_pat (List.repeat true L)) R)).
    { rewrite (proj1 nf_wk_to_exp), HRN, exp_wk_wk_ext with (χ := wk_id) by apply unwk_wk_pat; symmetry; apply exp_wk_id. }
    rewrite HNR in HNt |- *.
    apply (nf_strengthen_tele (doms_ctx Bs ++ Δ) Γu _ T0 i0); [ | rewrite <- List.app_assoc; exact HΓe | exact HT0t |].
    { unfold tele_ass; apply List.Forall_app; split; [ unfold doms_ctx; apply List.Forall_rev, tele_ass_map_ass | exact Hass ]. }
    rewrite HLe, <- List.app_assoc.
    rewrite <- !(exp_wk_wk_eq _ φ (wk_shiftn L)) by apply wk_pat_trues; exact HNt.
  Qed.

  (** ** Normal Instances *)

  (** A type's normal form is its own. *)
  Lemma nbe_ty_self : forall Γ T W (i : nat), Γ ⊢ T : Typeω@i -> nbe_ty_f Γ T W -> nbe_ty_f Γ (nf_to_exp W) W.
  Proof.
    intros * HT HW.
    destruct (completeness_ty (soundness_ty' HT HW)) as (W' & HW1 & HW2).
    pose proof (functional_nbe_ty _ _ _ _ HW HW1) as <-; exact HW2.
  Qed.

  (** The normal form of a chain of [Π]s, its own, ends in the normal
      form of the end under the domains. *)
  Lemma nbe_ty_pis : forall Bs Γ E W, type_nf W -> nbe_ty_f Γ (nf_to_exp W) W -> nf_to_exp W = pis Bs E ->
      exists WE, type_nf WE /\ nbe_ty_f (doms_ctx Bs ++ Γ) E WE /\ nf_to_exp WE = E.
  Proof.
    induction Bs as [| B Bs IH]; intros Γ E W HW HnW HWe; cbn in HWe.
    - exists W; rewrite HWe in HnW; auto.
    - destruct (nf_pi_view _ _ _ HW HWe) as (W1 & W2 & -> & HW2 & HW1e & HW2e).
      cbn [nf_to_exp] in HnW.
      destruct (nbe_ty_pi_inv _ _ _ _ _ _ HnW) as (WB & WC & [= <- <-] & _ & HC).
      rewrite HW1e in HC.
      unfold doms_ctx in *; cbn [List.map List.rev]; rewrite <- List.app_assoc.
      apply (IH _ _ _ HW2); [ exact HC | exact HW2e ].
  Qed.

  (** Normalizing commutes with weakening past a telescope of
      assumptions. *)
  Lemma nbe_wk_tele : forall Δ Γ M T W, tele_ass Δ -> ⊢ Δ ++ Γ -> Γ ⊢ M : T -> nbe_f Γ M T W ->
      exists W', nbe_f (Δ ++ Γ) M[wk_shiftn (List.length Δ)]ʷ T[wk_shiftn (List.length Δ)]ʷ W' /\
        nf_to_exp W' = (nf_to_exp W)[wk_shiftn (List.length Δ)]ʷ.
  Proof.
    induction Δ as [| e Δ IH]; intros Γ M T W Hass HΔ HM HW.
    - cbn [List.length List.app]; exists W.
      rewrite !(exp_wk_id_ext _ (wk_shiftn 0)) by (intros x; unfold wk_shiftn, wk_id; lia); auto.
    - assert (He : exists A, e = ce_ass A) by (inversion Hass as [| ? ? He _]; exact He).
      destruct He as [A ->].
      assert (Hass' : tele_ass Δ) by (inversion Hass; assumption).
      cbn [List.app] in HΔ |- *.
      pose proof (ctx_decomp_tail HΔ) as HΔ'.
      destruct (IH _ _ _ _ Hass' HΔ' HM HW) as (W1 & HW1 & HW1e).
      assert (HM1 : Δ ++ Γ ⊢ M[wk_shiftn (List.length Δ)]ʷ : T[wk_shiftn (List.length Δ)]ʷ)
        by (eapply wk_preserves_exp; [ exact HM | apply wf_wk_shiftn_app; [ exact HΔ' | eapply ctx_app_wf_tail; exact HΔ' ] ]).
      pose proof (nbe_wk _ _ _ _ _ HΔ HM1 HW1) as HW2.
      assert (Hsh : forall N, N[wk_shiftn (List.length Δ)]ʷ[↑]ʷ = N[wk_shiftn (S (List.length Δ))]ʷ)
        by (intros N; apply exp_wk_wk_ext; intros x; unfold wk_compose, wk_shiftn, wk_shift; lia).
      rewrite !Hsh in HW2.
      exists (nf_wk ↑ W1); cbn [List.length]; split; [ exact HW2 |].
      rewrite (proj1 nf_wk_to_exp), HW1e, Hsh; reflexivity.
  Qed.

  (** The types of a member's uniform parameters, at parameters whose
      uniform ones are weakenings, are the weakenings of theirs. *)
  Lemma tele_insts_params_uniform_wk : forall D Mk Cs Ms φ j T, tele_ass (ind_uparams D) -> ctx_scoped 0 (ind_uparams D) ->
      List.length Cs = ind_nu D -> List.firstn (ind_nu D) Ms = List.map (fun C => C[φ]ʷ) Cs ->
      List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T ->
      List.nth_error (tele_insts (im_params D Mk) Id Ms) j = Some T[φ]ʷ.
  Proof.
    intros * Hass Hsc HCl HC HT.
    assert (Hj : j < ind_nu D)
      by (assert (Hn : List.nth_error (tele_insts (ind_uparams D) Id Cs) j <> None) by congruence;
          apply List.nth_error_Some in Hn; rewrite length_tele_insts in Hn by exact Hass; unfold ind_nu in *; lia).
    assert (HMl : ind_nu D <= List.length Ms)
      by (apply (f_equal (@List.length _)) in HC; rewrite List.length_firstn, List.length_map in HC; lia).
    rewrite <- (List.firstn_skipn (ind_nu D) Ms).
    unfold im_params; rewrite tele_insts_app by (try exact Hass; rewrite List.length_firstn; unfold ind_nu in *; lia).
    rewrite List.nth_error_app1 by (rewrite length_tele_insts by exact Hass; rewrite List.length_firstn; unfold ind_nu in *; lia).
    rewrite HC, (List.map_ext (fun C => C[φ]ʷ) (fun M => M[ι φ]) (fun M => eq_sym (exp_sub_of_wk M φ))).
    rewrite (tele_insts_closed_sub _ _ _ _ _ Hass Hsc HT), exp_sub_of_wk; reflexivity.
  Qed.

  (** A term's normal form at equal types is one. *)
  Lemma nbe_conv_typ : forall Γ M A A' W (i : nat), Γ ⊢ M : A -> Γ ⊢ A ≈ A' : Typeω@i -> nbe_f Γ M A W -> nbe_f Γ M A' W.
  Proof.
    intros * HM HAA' [ρ a m Hinit Ea Em Hr].
    destruct (rel_typ_under_ctx_at_initial_env (completeness_fundamental_exp_eq _ _ _ _ HAA'))
      as (ρ1 & a1 & a' & Hi1 & Ea1 & Ea' & [R Hr1]).
    pose proof (functional_initial_env _ _ Hi1 _ Hinit) as ->.
    pose proof (functional_eval_exp _ _ _ _ Ea1 Ea) as ->.
    destruct (rel_exp_under_ctx_at_initial_env (completeness_fundamental_exp _ _ _ HM))
      as (ρ2 & j & R2 & a2 & m1 & m2 & Hi2 & Ea2 & Em1 & Em2 & Haa & Hm).
    pose proof (functional_initial_env _ _ Hi2 _ Hinit) as ->.
    pose proof (functional_eval_exp _ _ _ _ Ea2 Ea) as ->.
    pose proof (functional_eval_exp _ _ _ _ Em1 Em) as ->.
    pose proof (functional_eval_exp _ _ _ _ Em2 Em) as ->.
    assert (Hm' : R m m) by (apply (per_univ_elem_right_irrel _ _ _ _ _ _ _ Haa Hr1); exact Hm).
    destruct (per_elem_then_per_top Hr1 Hm' (List.length Γ)) as (W' & HW1 & HW2).
    assert (W' = W) as -> by exact (proj1 functional_read _ _ _ HW1 _ Hr).
    econstructor; eassumption.
  Qed.

  (** A term's normal form, at its type, is its own. *)
  Lemma nbe_self : forall Γ M A W, Γ ⊢ M : A -> nbe_f Γ M A W -> nbe_f Γ (nf_to_exp W) A W.
  Proof.
    intros * HM HW.
    destruct (completeness (soundness' HM HW)) as (W' & HW1 & HW2).
    pose proof (functional_nbe _ _ _ _ _ HW HW1) as <-; exact HW2.
  Qed.

  (** Terms each its own normal form at its type normalize together. *)
  Lemma nbes_of_each : forall Γ Ms As, List.length Ms = List.length As ->
      (forall j M A, List.nth_error Ms j = Some M -> List.nth_error As j = Some A ->
         Γ ⊢ M : A /\ exists W, nbe_f Γ M A W /\ nf_to_exp W = M) ->
      exists Ws, nbes gc_deps gc_stack Γ Ms As Ws /\ Ms = List.map nf_to_exp Ws.
  Proof.
    induction Ms as [| M Ms IH]; intros [| A As] Hl H; cbn in Hl; try discriminate.
    - exists nil; split; [ constructor | reflexivity ].
    - destruct (H 0 M A eq_refl eq_refl) as (HM & W & HW & HWe).
      destruct (IH As ltac:(lia) (fun j => H (S j))) as (Ws & HWs & ->).
      exists (W :: Ws); split; [ constructor; assumption | cbn; rewrite HWe; reflexivity ].
  Qed.

  (** The nested occurrences the classification finds in a normal form
      are typed views whose arguments are their own normal forms. *)
  Theorem nest_view_inv : forall Δ Γu T W (i : nat) nu np n pat g qc k Cs,
      tele_ass Δ -> List.length Δ = List.length pat + (np - nu) ->
      Δ ++ Γu ⊢ T : Typeω@i -> nbe_ty_f (Δ ++ Γu) T W ->
      cls_arg (grp_info gc_deps gc_stack) (rec_info gc_deps gc_stack) nu np n pat (nf_to_exp W) = Some g ->
      In (vk_ind qc k Cs) (rcarg_view g) ->
      view_inv gc_deps gc_stack Γu qc k Cs.
  Proof.
    intros * Hass Hlen HT HW Hcls Hin.
    pose proof (nest_view_typed _ _ _ _ _ _ _ _ _ _ _ _ _ Hass Hlen HT HW Hcls Hin) as Hvt.
    destruct Hvt as [D2 Hl2 Hk2 HCl HCt HΓu] eqn:EHvt.
    destruct (cls_arg_view _ _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs & E & m & HWe & HE & Hh & Hg & Hm & HC).
    unfold grp_info in Hg; rewrite Hl2 in Hg.
    destruct (k <? ind_ndecl D2); [ injection Hg as <- | discriminate ].
    destruct (List.nth_error (ind_members D2) k) as [Mk2 |] eqn:HMk2;
      [| apply List.nth_error_None in HMk2; pose proof (ind_ndecl_le D2); lia ].
    change (ind_member D2 k = Some Mk2) in HMk2.
    (** the end of the normal form, normal under the [Π]s' domains *)
    pose proof HW as [ρ0 m0 _ _ Hr0]; pose proof (read_typ_type_nf _ _ _ Hr0) as HWn.
    destruct (nbe_ty_pis _ _ _ _ HWn (nbe_ty_self _ _ _ _ HT HW) HWe) as (WE & HWE & HnE & HWEe).
    rewrite <- HWEe in Hh; destruct (nf_ind_view _ _ _ HWE Hh) as [Rs ->].
    cbn [nf_to_exp] in HWEe; subst E.
    rewrite app_args_apps in HC; cbn [app_args List.app] in HC.
    pose proof (soundness_ty' HT HW) as HTW.
    assert (HWt : Δ ++ Γu ⊢ nf_to_exp W : Typeω@i) by (gen_presups; assumption).
    rewrite HWe in HWt; pose proof (pis_typed_inv _ _ _ _ HWt) as HEt.
    pose proof (ind_type_length _ _ _ _ _ _ _ Hl2 HMk2 HEt) as HRl.
    pose proof (wf_ind_apps_inv _ _ _ _ _ _ _ Hl2 HMk2 HEt HRl) as HRt.
    assert (HΓe : ⊢ doms_ctx Bs ++ Δ ++ Γu) by (gen_presups; assumption).
    destruct (decl_of_lookup _ _ _ _ _ HΓu Hl2) as [Hdt Hc2].
    set (L := List.length Bs + List.length pat + (np - nu)) in *.
    set (φ := wk_pat (List.repeat true L)) in *.
    assert (HLe : List.length (doms_ctx Bs ++ Δ) = L)
      by (unfold L, doms_ctx; rewrite List.length_app, List.length_rev, List.length_map; lia).
    assert (HassE : tele_ass (doms_ctx Bs ++ Δ))
      by (unfold tele_ass; apply List.Forall_app; split; [ unfold doms_ctx; apply List.Forall_rev, tele_ass_map_ass | exact Hass ]).
    (** each argument, at the end, is the normal form of its weakening,
        which is the weakening of its own *)
    destruct (nbes_of_each Γu Cs (tele_insts (ind_uparams D2) Id Cs)
                ltac:(rewrite length_tele_insts by exact (decl_typed_ass _ _ _ Hdt); unfold ind_nu in *; lia)) as (Ws & HWs & HCW).
    { intros j C T0 HN HT0; split; [ exact (HCt _ _ _ HN HT0) |].
      pose proof (HCt _ _ _ HN HT0) as HCj.
      destruct (soundness HCj) as (Wj & HWj & _).
      destruct (nbe_wk_tele (doms_ctx Bs ++ Δ) Γu C T0 Wj HassE ltac:(rewrite <- List.app_assoc; exact HΓe) HCj HWj)
        as (Wj' & HWj' & HWj'e).
      assert (HNw : List.nth_error (List.map nf_to_exp Rs) j = Some C[φ]ʷ).
      { assert (Hj : j < ind_nu D2) by (rewrite <- HCl; apply List.nth_error_Some; congruence).
        rewrite <- (List.firstn_skipn (ind_nu D2) (List.map nf_to_exp Rs)), List.nth_error_app1
          by (rewrite List.length_firstn, HRl; unfold im_np, ind_nu in *; lia).
        rewrite HC, List.nth_error_map, HN; reflexivity. }
      pose proof (tele_insts_params_uniform_wk D2 Mk2 Cs (List.map nf_to_exp Rs) φ j T0 (decl_typed_ass _ _ _ Hdt) (decl_closed_uparams _ Hc2) HCl HC HT0) as HTw.
      destruct (nbe_ind_args _ _ _ _ _ _ _ Hl2 HMk2 HRl HRt HnE j _ _ HNw HTw) as (Rj & HRj & HnRj).
      rewrite HLe in HWj', HWj'e; rewrite <- List.app_assoc in HWj'.
      rewrite <- !(exp_wk_wk_eq _ φ (wk_shiftn L)) in HWj' by apply wk_pat_trues.
      rewrite <- (exp_wk_wk_eq _ φ (wk_shiftn L)) in HWj'e by apply wk_pat_trues.
      pose proof (functional_nbe _ _ _ _ _ HnRj HWj') as ->.
      exists Wj; split; [ exact HWj |].
      rewrite List.nth_error_map, HRj in HNw; cbn in HNw; injection HNw as HNw.
      rewrite HWj'e in HNw.
      apply (f_equal (fun M => M[unwk_pat (List.repeat true L)]ʷ)) in HNw.
      unfold φ in HNw; rewrite !(exp_wk_wk_ext _ _ _ wk_id (unwk_wk_pat _)), !exp_wk_id in HNw; exact HNw. }
    refine (mk_view_inv _ _ _ _ _ _ Hvt Ws _ HCW).
    intros D0 Hl0; rewrite Hl2 in Hl0; injection Hl0 as <-; exact HWs.
  Qed.

  (** The record end of a normal form the classification finds a record
      view in: the record type at the normal forms [Rs] of its arguments,
      which are the instance weakened, all typed at the parameters. *)
  Lemma nest_record_end : forall Δ Γu T W (i : nat) nu np n pat g qr Is,
      Δ ++ Γu ⊢ T : Typeω@i -> nbe_ty_f (Δ ++ Γu) T W ->
      cls_arg (grp_info gc_deps gc_stack) (rec_info gc_deps gc_stack) nu np n pat (nf_to_exp W) = Some g ->
      In (vk_record qr Is) (rcarg_view g) ->
      exists Bs Rr Rs, nf_to_exp W = pis Bs (apps (a_record qr) (List.map nf_to_exp Rs)) /\
        record_lookup gc_deps gc_stack qr = Some Rr /\
        doms_ctx Bs ++ Δ ++ Γu ⊢ apps (a_record qr) (List.map nf_to_exp Rs) : Typeω@i /\
        nbe_ty_f (doms_ctx Bs ++ Δ ++ Γu) (apps (a_record qr) (List.map nf_to_exp Rs)) (nf_record qr Rs) /\
        List.length Rs = List.length (record_params Rr) /\ selfs_guarded nu n Is = true /\
        List.map nf_to_exp Rs = List.map (fun C => C[wk_pat (List.repeat true (List.length Bs + List.length pat + (np - nu)))]ʷ) Is.
  Proof.
    intros * HT HW Hcls Hin.
    destruct (cls_arg_record_view _ _ _ _ _ _ _ _ _ _ Hcls Hin) as (Bs & E & HWe & HE & Hh & Hr & Hgu & HC).
    unfold rec_info in Hr.
    destruct (record_lookup gc_deps gc_stack qr) as [Rr |] eqn:Hl2; [| discriminate ]; cbn in Hr; injection Hr as Hr.
    pose proof HW as [ρ0 m0 _ _ Hr0]; pose proof (read_typ_type_nf _ _ _ Hr0) as HWn.
    destruct (nbe_ty_pis _ _ _ _ HWn (nbe_ty_self _ _ _ _ HT HW) HWe) as (WE & HWE & HnE & HWEe).
    rewrite <- HWEe in Hh; destruct (nf_record_view _ _ HWE Hh) as [Rs ->].
    cbn [nf_to_exp] in HWEe; subst E.
    rewrite app_args_apps in HC, Hr; cbn [app_args List.app] in HC, Hr.
    pose proof (soundness_ty' HT HW) as HTW.
    assert (HWt : Δ ++ Γu ⊢ nf_to_exp W : Typeω@i) by (gen_presups; assumption).
    rewrite HWe in HWt; pose proof (pis_typed_inv _ _ _ _ HWt) as HEt.
    exists Bs, Rr, Rs; repeat split; try assumption.
    rewrite List.length_map in Hr; lia.
  Qed.

  (** The record views the classification finds in a normal form are
      typed. *)
  Theorem nest_record_view_typed : forall Δ Γu T W (i : nat) nu np n pat g qr Is,
      tele_ass Δ -> List.length Δ = List.length pat + (np - nu) ->
      Δ ++ Γu ⊢ T : Typeω@i -> nbe_ty_f (Δ ++ Γu) T W ->
      cls_arg (grp_info gc_deps gc_stack) (rec_info gc_deps gc_stack) nu np n pat (nf_to_exp W) = Some g ->
      In (vk_record qr Is) (rcarg_view g) ->
      record_view_typed gc_deps gc_stack Γu qr Is.
  Proof.
    intros * Hass Hlen HT HW Hcls Hin.
    destruct (nest_record_end _ _ _ _ _ _ _ _ _ _ _ _ HT HW Hcls Hin) as (Bs & Rr & Rs & HWe & Hl2 & HEt & HnE & HRl & _ & HC).
    pose proof (wf_record_apps_inv _ _ _ _ _ Hl2 HEt ltac:(rewrite List.length_map; exact HRl)) as HRt.
    destruct (wf_record_inversion (wf_record_own_apps _ _ _ _ _ _ _ HEt Hl2)) as [R0 Hl0 _ HRa _ _ HF _ _ _].
    rewrite Hl2 in Hl0; injection Hl0 as <-.
    assert (HΓe : ⊢ doms_ctx Bs ++ Δ ++ Γu) by (gen_presups; assumption).
    assert (HΓu : ⊢ Γu) by (rewrite List.app_assoc in HΓe; eapply ctx_app_wf_tail; exact HΓe).
    pose proof (wf_record_closed _ _ _ _ _ HΓu Hl2) as Hc2.
    assert (HCl : List.length Is = List.length (record_params Rr)).
    { apply (f_equal (@List.length _)) in HC; rewrite !List.length_map in HC; lia. }
    set (L := List.length Bs + List.length pat + (np - nu)) in *.
    assert (HLe : List.length (doms_ctx Bs ++ Δ) = L)
      by (unfold L, doms_ctx; rewrite List.length_app, List.length_rev, List.length_map; lia).
    apply (mk_record_view_typed _ _ _ _ _ Rr Hl2 HCl); [| exact HΓu ].
    (** the arguments, strengthened past the [Π]s' domains, the arguments
        before and the member's non-uniform parameters, are typed over
        [Γu] *)
    apply (tele_insts_typed_all (record_params Rr) nil Γu Id Is HRa
             ltac:(rewrite List.app_nil_r; exact (ctx_app_wf_tail _ _ _ _ HF)) (wf_sub_to_nil _ _ _ HΓu)).
    intros j N T0 HN HT0 [i0 HT0t].
    set (φ := wk_pat (List.repeat true L)) in *.
    assert (HNw : List.nth_error (List.map nf_to_exp Rs) j = Some N[φ]ʷ) by (rewrite HC, List.nth_error_map, HN; reflexivity).
    assert (HTw : List.nth_error (tele_insts (record_params Rr) Id (List.map nf_to_exp Rs)) j = Some T0[φ]ʷ).
    { rewrite HC, (List.map_ext (fun C => C[φ]ʷ) (fun M => M[ι φ]) (fun M => eq_sym (exp_sub_of_wk M φ))).
      rewrite (tele_insts_closed_sub _ _ _ _ _ HRa (closed_params _ Hc2) HT0), exp_sub_of_wk; reflexivity. }
    pose proof (HRt _ _ _ HNw HTw) as HNt.
    rewrite List.nth_error_map in HNw.
    destruct (List.nth_error Rs j) as [R |] eqn:HR; cbn in HNw; [ injection HNw as HRN | discriminate ].
    assert (HNR : N = nf_to_exp (nf_wk (unwk_pat (List.repeat true L)) R)).
    { rewrite (proj1 nf_wk_to_exp), HRN, exp_wk_wk_ext with (χ := wk_id) by apply unwk_wk_pat; symmetry; apply exp_wk_id. }
    rewrite HNR in HNt |- *.
    apply (nf_strengthen_tele (doms_ctx Bs ++ Δ) Γu _ T0 i0); [ | rewrite <- List.app_assoc; exact HΓe | exact HT0t |].
    { unfold tele_ass; apply List.Forall_app; split; [ unfold doms_ctx; apply List.Forall_rev, tele_ass_map_ass | exact Hass ]. }
    rewrite HLe, <- List.app_assoc.
    rewrite <- !(exp_wk_wk_eq _ φ (wk_shiftn L)) by apply wk_pat_trues; exact HNt.
  Qed.

  (** The record views the classification finds in a normal form are
      typed, their arguments their own normal forms. *)
  Theorem nest_record_view_inv : forall Δ Γu T W (i : nat) nu np n pat g qr Is,
      tele_ass Δ -> List.length Δ = List.length pat + (np - nu) ->
      Δ ++ Γu ⊢ T : Typeω@i -> nbe_ty_f (Δ ++ Γu) T W ->
      cls_arg (grp_info gc_deps gc_stack) (rec_info gc_deps gc_stack) nu np n pat (nf_to_exp W) = Some g ->
      In (vk_record qr Is) (rcarg_view g) ->
      record_view_inv gc_deps gc_stack Γu qr Is.
  Proof.
    intros * Hass Hlen HT HW Hcls Hin.
    pose proof (nest_record_view_typed _ _ _ _ _ _ _ _ _ _ _ _ Hass Hlen HT HW Hcls Hin) as Hvt.
    destruct Hvt as [Rr Hl2 HCl HCt HΓu] eqn:EHvt.
    destruct (nest_record_end _ _ _ _ _ _ _ _ _ _ _ _ HT HW Hcls Hin) as (Bs & Rr' & Rs & HWe & Hl2' & HEt & HnE & HRl & _ & HC).
    rewrite Hl2 in Hl2'; injection Hl2' as <-.
    assert (HΓe : ⊢ doms_ctx Bs ++ Δ ++ Γu) by (gen_presups; assumption).
    destruct (wf_record_inversion (wf_record_own_apps _ _ _ _ _ _ _ HEt Hl2)) as [R0 Hl0 _ HRa _ _ _ _ _ _].
    rewrite Hl2 in Hl0; injection Hl0 as <-.
    pose proof (wf_record_closed _ _ _ _ _ HΓu Hl2) as Hc2.
    set (L := List.length Bs + List.length pat + (np - nu)) in *.
    set (φ := wk_pat (List.repeat true L)) in *.
    assert (HLe : List.length (doms_ctx Bs ++ Δ) = L)
      by (unfold L, doms_ctx; rewrite List.length_app, List.length_rev, List.length_map; lia).
    assert (HassE : tele_ass (doms_ctx Bs ++ Δ))
      by (unfold tele_ass; apply List.Forall_app; split; [ unfold doms_ctx; apply List.Forall_rev, tele_ass_map_ass | exact Hass ]).
    (** each argument, at the end, is the normal form of its weakening,
        which is the weakening of its own *)
    destruct (nbes_of_each Γu Is (tele_insts (record_params Rr) Id Is)
                ltac:(rewrite length_tele_insts by exact HRa; lia)) as (Ws & HWs & HCW).
    { intros j C T0 HN HT0; split; [ exact (HCt _ _ _ HN HT0) |].
      pose proof (HCt _ _ _ HN HT0) as HCj.
      destruct (soundness HCj) as (Wj & HWj & _).
      destruct (nbe_wk_tele (doms_ctx Bs ++ Δ) Γu C T0 Wj HassE ltac:(rewrite <- List.app_assoc; exact HΓe) HCj HWj)
        as (Wj' & HWj' & HWj'e).
      assert (HNw : List.nth_error (List.map nf_to_exp Rs) j = Some C[φ]ʷ) by (rewrite HC, List.nth_error_map, HN; reflexivity).
      assert (HTw : List.nth_error (tele_insts (record_params Rr) Id (List.map nf_to_exp Rs)) j = Some T0[φ]ʷ).
      { rewrite HC, (List.map_ext (fun C => C[φ]ʷ) (fun M => M[ι φ]) (fun M => eq_sym (exp_sub_of_wk M φ))).
        rewrite (tele_insts_closed_sub _ _ _ _ _ HRa (closed_params _ Hc2) HT0), exp_sub_of_wk; reflexivity. }
      destruct (nbe_record_args _ _ _ _ _ _ Hl2 HEt HnE j _ _ HNw HTw) as (Rj & HRj & HnRj).
      rewrite HLe in HWj', HWj'e; rewrite <- List.app_assoc in HWj'.
      rewrite <- !(exp_wk_wk_eq _ φ (wk_shiftn L)) in HWj' by apply wk_pat_trues.
      rewrite <- (exp_wk_wk_eq _ φ (wk_shiftn L)) in HWj'e by apply wk_pat_trues.
      pose proof (functional_nbe _ _ _ _ _ HnRj HWj') as ->.
      exists Wj; split; [ exact HWj |].
      rewrite List.nth_error_map, HRj in HNw; cbn in HNw; injection HNw as HNw.
      rewrite HWj'e in HNw.
      apply (f_equal (fun M => M[unwk_pat (List.repeat true L)]ʷ)) in HNw.
      unfold φ in HNw; rewrite !(exp_wk_wk_ext _ _ _ wk_id (unwk_wk_pat _)), !exp_wk_id in HNw; exact HNw. }
    refine (mk_record_view_inv _ _ _ _ _ Hvt Ws _ HCW).
    intros R0 Hl0; rewrite Hl2 in Hl0; injection Hl0 as <-; exact HWs.
  Qed.

  (** The instances the classification finds in a normal form are of the
      invariant. *)
  Corollary nest_key_inv : forall Δ Γu T W (i : nat) nu np n pat g z,
      tele_ass Δ -> List.length Δ = List.length pat + (np - nu) ->
      Δ ++ Γu ⊢ T : Typeω@i -> nbe_ty_f (Δ ++ Γu) T W ->
      cls_arg (grp_info gc_deps gc_stack) (rec_info gc_deps gc_stack) nu np n pat (nf_to_exp W) = Some g ->
      In z (rcarg_view g) -> key_inv gc_deps gc_stack Γu z.
  Proof.
    intros * Hass Hlen HT HW Hcls Hin; destruct z as [qc k Cs | qr Is]; cbn [key_inv].
    - exact (nest_view_inv _ _ _ _ _ _ _ _ _ _ _ _ _ Hass Hlen HT HW Hcls Hin).
    - exact (nest_record_view_inv _ _ _ _ _ _ _ _ _ _ _ _ Hass Hlen HT HW Hcls Hin).
  Qed.
End Fixed_GCtx.

(** ** The Siblings of a View *)

(** The sibling [e] of a view of a container's group at [Cs], from its
    member [M] at position [i]. *)
Inductive sib_entry (Θ : gdeps) (Ξ : gstack) (Γc : ctx) (qc : qname) (Cs : list exp) : nat -> imember -> view_key -> Prop :=
(** A declared member: itself at [Cs] *)
| sib_decl : forall i M pm, im_head M = mh_decl pm -> sib_entry Θ Ξ Γc qc Cs i M (vk_ind qc i Cs)
(** A view: the member it views, at its own uniform arguments at [Cs],
    normalized *)
| sib_view : forall i M qv kv Iv vmv Dv Ws, im_head M = mh_view qv kv Iv vmv -> ind_lookup Θ Ξ qv = Some Dv ->
    nbes Θ Ξ Γc (List.map (fun I => I[sb_of_list sb_id Cs]) Iv)
      (List.map (fun T => T[sb_of_list sb_id Cs]) (tele_insts (ind_uparams Dv) sb_id Iv)) Ws ->
    sib_entry Θ Ξ Γc qc Cs i M (vk_ind qv kv (List.map nf_to_exp Ws))
(** A record view: the record at its instance at [Cs], normalized *)
| sib_record : forall i M qr Ir fl Rr Ws, im_head M = mh_record qr Ir fl -> record_lookup Θ Ξ qr = Some Rr ->
    nbes Θ Ξ Γc (List.map (fun I => I[sb_of_list sb_id Cs]) Ir)
      (List.map (fun T => T[sb_of_list sb_id Cs]) (tele_insts (record_params Rr) sb_id Ir)) Ws ->
    sib_entry Θ Ξ Γc qc Cs i M (vk_record qr (List.map nf_to_exp Ws)).

Lemma sibs_from_nth : forall Θ Ξ Γc qc Cs i ms ss, sibs_from Θ Ξ Γc qc Cs i ms ss ->
    List.length ss = List.length ms /\
    forall j M, List.nth_error ms j = Some M -> exists e, List.nth_error ss j = Some e /\ sib_entry Θ Ξ Γc qc Cs (i + j) M e.
Proof.
  induction 1 as [i | i M ms ss pm Hh Hs IH | i M ms ss qv kv Iv vmv Dv Ws Hh Hl Hn Hs IH
                 | i M ms ss qr Ir fl Rr Ws Hh Hl Hn Hs IH].
  - split; [ reflexivity | intros [] ? ?; discriminate ].
  - destruct IH as [IHl IH]; split; [ cbn; lia |].
    intros [| j] M0 HM0; cbn in HM0.
    + injection HM0 as <-; eexists; split; [ reflexivity |]; rewrite Nat.add_0_r; eapply sib_decl; eassumption.
    + destruct (IH _ _ HM0) as (e & He & Hse); exists e; split; [ exact He |].
      replace (i + S j) with (S i + j) by lia; exact Hse.
  - destruct IH as [IHl IH]; split; [ cbn; lia |].
    intros [| j] M0 HM0; cbn in HM0.
    + injection HM0 as <-; eexists; split; [ reflexivity |]; rewrite Nat.add_0_r; eapply sib_view; eassumption.
    + destruct (IH _ _ HM0) as (e & He & Hse); exists e; split; [ exact He |].
      replace (i + S j) with (S i + j) by lia; exact Hse.
  - destruct IH as [IHl IH]; split; [ cbn; lia |].
    intros [| j] M0 HM0; cbn in HM0.
    + injection HM0 as <-; eexists; split; [ reflexivity |]; rewrite Nat.add_0_r; eapply sib_record; eassumption.
    + destruct (IH _ _ HM0) as (e & He & Hse); exists e; split; [ exact He |].
      replace (i + S j) with (S i + j) by lia; exact Hse.
Qed.

Lemma sibs_from_in : forall Θ Ξ Γc qc Cs i ms ss, sibs_from Θ Ξ Γc qc Cs i ms ss ->
    forall e, In e ss -> exists j M, List.nth_error ms j = Some M /\ List.nth_error ss j = Some e /\ sib_entry Θ Ξ Γc qc Cs (i + j) M e.
Proof.
  intros * Hs e He.
  destruct (sibs_from_nth _ _ _ _ _ _ _ _ Hs) as [Hl Hn].
  destruct (List.In_nth_error _ _ He) as [j Hj].
  destruct (List.nth_error ms j) as [M |] eqn:HM.
  2:{ apply List.nth_error_None in HM.
      assert (Hj' : List.nth_error ss j <> None) by congruence; apply List.nth_error_Some in Hj'; lia. }
  destruct (Hn _ _ HM) as (e' & He' & Hse); rewrite Hj in He'; injection He' as <-.
  exists j, M; auto.
Qed.

Lemma nbes_functional : forall Θ Ξ Γ Ms As Ws Ws', nbes Θ Ξ Γ Ms As Ws -> nbes Θ Ξ Γ Ms As Ws' -> Ws = Ws'.
Proof.
  intros * H; revert Ws'; induction H as [| M Ms A As W Ws HM HW Hn IH]; intros Ws' H'; inversion H'; subst; [ reflexivity |].
  f_equal; [ eapply functional_nbe; eassumption | apply IH; assumption ].
Qed.

Lemma sibs_from_functional : forall Θ Ξ Γc qc Cs i ms ss ss', sibs_from Θ Ξ Γc qc Cs i ms ss -> sibs_from Θ Ξ Γc qc Cs i ms ss' ->
    ss = ss'.
Proof.
  intros * H; revert ss'; induction H as [i | i M ms ss pm Hh Hs IH | i M ms ss qv kv Iv vmv Dv Ws Hh Hl Hn Hs IH
                                         | i M ms ss qr Ir fl Rr Ws Hh Hl Hn Hs IH];
    intros ss' H'; inversion H'; subst; try congruence.
  - f_equal; apply IH; assumption.
  - repeat match goal with
      | Hh' : im_head M = _ |- _ => tryif unify Hh' Hh then fail else (rewrite Hh in Hh'; injection Hh' as <- <- <- <-)
      | Hl' : ind_lookup _ _ qv = _ |- _ => tryif unify Hl' Hl then fail else (rewrite Hl in Hl'; injection Hl' as <-)
      end.
    match goal with Hn' : nbes _ _ _ _ _ ?Ws' |- _ => tryif unify Ws' Ws then fail else
      rewrite (nbes_functional _ _ _ _ _ _ _ Hn' Hn) end.
    f_equal; apply IH; assumption.
  - repeat match goal with
      | Hh' : im_head M = _ |- _ => tryif unify Hh' Hh then fail else (rewrite Hh in Hh'; injection Hh' as <- <- <-)
      | Hl' : record_lookup _ _ qr = _ |- _ => tryif unify Hl' Hl then fail else (rewrite Hl in Hl'; injection Hl' as <-)
      end.
    match goal with Hn' : nbes _ _ _ _ _ ?Ws' |- _ => tryif unify Ws' Ws then fail else
      rewrite (nbes_functional _ _ _ _ _ _ _ Hn' Hn) end.
    f_equal; apply IH; assumption.
Qed.

(** The siblings of a view depend on its container's group and its
    instance only. *)
Lemma view_sibs_same : forall Θ Ξ R qc k k' Cs ss ss', view_sibs Θ Ξ R (vk_ind qc k Cs) ss -> view_sibs Θ Ξ R (vk_ind qc k' Cs) ss' ->
    ss = ss'.
Proof.
  intros * H H'; inversion H as [? ? ? D1 ? Hl1 Hs1 |]; inversion H' as [? ? ? D2 ? Hl2 Hs2 |]; subst.
  rewrite Hl1 in Hl2; injection Hl2 as <-; exact (sibs_from_functional _ _ _ _ _ _ _ _ _ Hs1 Hs2).
Qed.

Lemma nbes_nth : forall Θ Ξ Γ Ms As Ws, nbes Θ Ξ Γ Ms As Ws ->
    List.length Ws = List.length Ms /\ List.length As = List.length Ms /\
    forall j M A, List.nth_error Ms j = Some M -> List.nth_error As j = Some A ->
      exists W, List.nth_error Ws j = Some W /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : A /\ nbe Θ Ξ Γ M A W.
Proof.
  induction 1 as [| M Ms A As W Ws HM HW Hn IH];
    [ split; [ reflexivity | split; [ reflexivity | intros j M A HM; destruct j; discriminate ] ] |].
  destruct IH as (IH1 & IH2 & IH); cbn; split; [ lia | split; [ lia |] ].
  intros [| j] M0 A0 HM0 HA0; cbn in HM0, HA0;
    [ injection HM0 as <-; injection HA0 as <-; exists W; cbn; auto | exact (IH _ _ _ HM0 HA0) ].
Qed.

Section SiblingInv.
  Context {GC : GCtx}.

  (** Normal forms of terms of a closed telescope's instance are typed at
      the telescope's instance at them, and their own normal forms
      there. *)
  Lemma nbes_inst_inv : forall Γ U Ms Ws, tele_ass U -> ctx_scoped 0 U -> ⊢ U -> ⊢ Γ ->
      nbes gc_deps gc_stack Γ Ms (tele_insts U Id Ms) Ws ->
      (forall j N T, List.nth_error (List.map nf_to_exp Ws) j = Some N ->
         List.nth_error (tele_insts U Id (List.map nf_to_exp Ws)) j = Some T -> Γ ⊢ N : T) /\
      exists Ws', nbes gc_deps gc_stack Γ (List.map nf_to_exp Ws) (tele_insts U Id (List.map nf_to_exp Ws)) Ws' /\
        List.map nf_to_exp Ws = List.map nf_to_exp Ws'.
  Proof.
    intros * Hass Hsc HU HΓ Hn.
    destruct (nbes_nth _ _ _ _ _ _ Hn) as (HlW & HlA & Hnth).
    assert (Heq : forall j N N' T, List.nth_error Ms j = Some N -> List.nth_error (List.map nf_to_exp Ws) j = Some N' ->
              List.nth_error (tele_insts U Id Ms) j = Some T -> Γ ⊢ N ≈ N' : T).
    { intros * HN HN' HT; destruct (Hnth _ _ _ HN HT) as (W & HW & HNt & HNW).
      rewrite List.nth_error_map, HW in HN'; cbn in HN'; injection HN' as <-.
      exact (soundness' HNt HNW). }
    assert (HTT : forall j T T', List.nth_error (tele_insts U Id Ms) j = Some T ->
              List.nth_error (tele_insts U Id (List.map nf_to_exp Ws)) j = Some T' -> exists i, Γ ⊢ T ≈ T' : Typeω@i).
    { intros * HT HT'; eapply (tele_insts_cong_upto U nil Γ Id Id Ms (List.map nf_to_exp Ws) Hass
                                ltac:(rewrite List.app_nil_r; exact HU) (wf_sub_eq_refl _ _ _ _ _ (wf_sub_to_nil _ _ _ HΓ)) j T T' HT HT').
      intros j' N N' T0 _ HN HN' HT0; exact (Heq _ _ _ _ HN HN' HT0). }
    assert (Hty : forall j N T, List.nth_error (List.map nf_to_exp Ws) j = Some N ->
              List.nth_error (tele_insts U Id (List.map nf_to_exp Ws)) j = Some T ->
              Γ ⊢ N : T /\ exists W, nbe_f Γ N T W /\ nf_to_exp W = N).
    { intros * HN HT'.
      assert (Hj : j < List.length Ms) by (rewrite <- HlW, <- (List.length_map nf_to_exp); apply List.nth_error_Some; congruence).
      destruct (nth_error_lt_some' Ms j Hj) as [M HM].
      assert (Hj' : j < List.length (tele_insts U Id Ms)) by lia.
      destruct (nth_error_lt_some' _ j Hj') as [T0 HT0].
      destruct (Hnth _ _ _ HM HT0) as (W & HW & HMt & HMW).
      rewrite List.nth_error_map, HW in HN; cbn in HN; injection HN as <-.
      destruct (HTT _ _ _ HT0 HT') as [i Hi].
      pose proof (soundness' HMt HMW) as HMW'.
      assert (HWt : Γ ⊢ nf_to_exp W : T0) by (gen_presups; assumption).
      split; [ exact (wf_conv' _ _ _ _ _ _ _ HWt Hi) |].
      exists W; split; [ eapply nbe_conv_typ; [ exact HWt | exact Hi | exact (nbe_self _ _ _ _ HMt HMW) ] | reflexivity ]. }
    split; [ intros; apply (Hty j); assumption |].
    apply nbes_of_each; [ rewrite length_tele_insts in HlA |- * by exact Hass; rewrite List.length_map, HlW; lia |].
    intros; apply (Hty j); assumption.
  Qed.

  (** Equal instances of a closed telescope have equal normal forms. *)
  Lemma nbes_conv_inst : forall Γ U Ms Ms' Ws Ws', tele_ass U -> ⊢ U -> ⊢ Γ ->
      nbes gc_deps gc_stack Γ Ms (tele_insts U Id Ms) Ws -> nbes gc_deps gc_stack Γ Ms' (tele_insts U Id Ms') Ws' ->
      List.length Ms = List.length Ms' ->
      (forall j N N' T, List.nth_error Ms j = Some N -> List.nth_error Ms' j = Some N' ->
         List.nth_error (tele_insts U Id Ms) j = Some T -> Γ ⊢ N ≈ N' : T) ->
      Ws = Ws'.
  Proof.
    intros * Hass HU HΓ Hn Hn' Hl Heq.
    destruct (nbes_nth _ _ _ _ _ _ Hn) as (HlW & HlA & Hnth).
    destruct (nbes_nth _ _ _ _ _ _ Hn') as (HlW' & HlA' & Hnth').
    apply List.nth_error_ext; intros j.
    destruct (Nat.lt_ge_cases j (List.length Ms)) as [Hj | Hj].
    - destruct (nth_error_lt_some' Ms j Hj) as [N HN].
      destruct (nth_error_lt_some' Ms' j ltac:(lia)) as [N' HN'].
      destruct (nth_error_lt_some' (tele_insts U Id Ms) j ltac:(lia)) as [T HT].
      destruct (nth_error_lt_some' (tele_insts U Id Ms') j ltac:(lia)) as [T' HT'].
      destruct (Hnth _ _ _ HN HT) as (W & HW & HNt & HNW).
      destruct (Hnth' _ _ _ HN' HT') as (W' & HW' & HNt' & HNW').
      rewrite HW, HW'; f_equal.
      destruct (tele_insts_cong_upto U nil Γ Id Id Ms Ms' Hass ltac:(rewrite List.app_nil_r; exact HU)
                  (wf_sub_eq_refl _ _ _ _ _ (wf_sub_to_nil _ _ _ HΓ)) j T T' HT HT') as [i Hi].
      { intros j' M0 M0' T0 _ HM0 HM0' HT0; exact (Heq _ _ _ _ HM0 HM0' HT0). }
      destruct (completeness (Heq _ _ _ _ HN HN' HT)) as (W0 & HW0 & HW0').
      pose proof (functional_nbe _ _ _ _ _ HNW HW0) as <-.
      pose proof (nbe_conv_typ _ _ _ _ _ _ (wf_conv' _ _ _ _ _ _ _ HNt' ltac:(symmetry; exact Hi)) Hi HW0') as HN'W.
      exact (functional_nbe _ _ _ _ _ HN'W HNW').
    - rewrite !(proj2 (List.nth_error_None _ _)) by lia; reflexivity.
  Qed.

  (** A view sibling is a typed view whose arguments are their own normal
      forms. *)
  Lemma sib_view_inv : forall Γu qc D' Cs i M qv kv Iv vmv Dv Ws,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qc = Some D' -> ind_member D' i = Some M ->
      im_head M = mh_view qv kv Iv vmv -> ind_lookup gc_deps gc_stack qv = Some Dv ->
      nbes gc_deps gc_stack Γu (List.map (fun I => I[sb_of_list sb_id Cs]) Iv)
        (List.map (fun T => T[sb_of_list sb_id Cs]) (tele_insts (ind_uparams Dv) sb_id Iv)) Ws ->
      view_inv gc_deps gc_stack Γu qv kv (List.map nf_to_exp Ws).
  Proof.
    intros * Hg HΓu Hl HM Hh Hlv Hn.
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HM Hh) as (Dv' & Mk' & Hlv' & HMk' & Hkv & HIl & _).
    rewrite Hlv in Hlv'; injection Hlv' as <-.
    destruct (decl_of_glookup _ _ _ _ Hg Hlv) as [Hdtv Hcv].
    rewrite (tele_insts_sub (ind_uparams Dv) 0 Id Id (sb_of_list sb_id Cs) Iv (decl_closed_ass _ Hcv) (decl_closed_uparams _ Hcv)
               ltac:(intros; lia)) in Hn.
    destruct (nbes_inst_inv _ _ _ _ (decl_closed_ass _ Hcv) (decl_closed_uparams _ Hcv) (decl_typed_uparams_field _ _ _ Hdtv) HΓu Hn) as (Hty & Ws' & Hn' & HWs').
    destruct (nbes_nth _ _ _ _ _ _ Hn) as (HlW & _).
    assert (HlWs : List.length (List.map nf_to_exp Ws) = ind_nu Dv) by (rewrite List.length_map, HlW, List.length_map; exact HIl).
    refine (mk_view_inv _ _ _ _ _ _ (mk_view_typed _ _ _ _ _ _ Dv Hlv Hkv HlWs Hty HΓu) Ws' _ HWs').
    intros D0 Hl0; rewrite Hlv in Hl0; injection Hl0 as <-; exact Hn'.
  Qed.

  (** A record view sibling is a typed record view whose arguments are
      their own normal forms. *)
  Lemma sib_record_inv : forall Γu qc D' Cs i M qr Ir fl Rr Ws,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qc = Some D' -> ind_member D' i = Some M ->
      im_head M = mh_record qr Ir fl -> record_lookup gc_deps gc_stack qr = Some Rr ->
      nbes gc_deps gc_stack Γu (List.map (fun I => I[sb_of_list sb_id Cs]) Ir)
        (List.map (fun T => T[sb_of_list sb_id Cs]) (tele_insts (record_params Rr) sb_id Ir)) Ws ->
      record_view_inv gc_deps gc_stack Γu qr (List.map nf_to_exp Ws).
  Proof.
    intros * Hg HΓu Hl HM Hh Hlr Hn.
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt _].
    destruct (rview_struct_record _ _ _ (decl_typed_rstruct _ _ _ Hdt) _ _ _ _ _ HM Hh) as [Rr' HRf].
    pose proof (rview_record_lookup _ _ _ _ _ _ HRf) as Hlr'; rewrite Hlr in Hlr'; injection Hlr' as <-.
    pose proof (rview_record_count _ _ _ _ _ _ HRf) as HIl.
    pose proof (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) Hlr) as HcR.
    pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hlr) as HRt.
    pose proof (record_typed_fctx_wf _ _ _ HRt 0 ltac:(lia)) as HP; cbn [record_fctx List.app] in HP.
    rewrite (record_params_insts_sub Rr Ir (sb_of_list sb_id Cs) HcR) in Hn.
    destruct (nbes_inst_inv _ _ _ _ (typed_params_ass _ _ _ HRt) (closed_params _ HcR) HP HΓu Hn) as (Hty & Ws' & Hn' & HWs').
    destruct (nbes_nth _ _ _ _ _ _ Hn) as (HlW & _).
    assert (HlWs : List.length (List.map nf_to_exp Ws) = List.length (record_params Rr))
      by (rewrite List.length_map, HlW, List.length_map; exact HIl).
    refine (mk_record_view_inv _ _ _ _ _ (mk_record_view_typed _ _ _ _ _ Rr Hlr HlWs Hty HΓu) Ws' _ HWs').
    intros R0 Hl0; rewrite Hlr in Hl0; injection Hl0 as <-; exact Hn'.
  Qed.

  (** The siblings of a view sibling of [(q, k, Cs)] are siblings of
      [(q, k, Cs)]: the view equations of [q]'s group at [Cs]. *)
  Lemma view_entry_sibs : forall Γu qx D Cs m Mm qv kv Iv vm Ws Dqv ss ssy,
      ⊢ᵍ gc_deps ⍮ gc_stack -> ⊢ Γu -> ind_lookup gc_deps gc_stack qx = Some D -> List.length Cs = ind_nu D ->
      (forall j C T, List.nth_error Cs j = Some C -> List.nth_error (tele_insts (ind_uparams D) Id Cs) j = Some T -> Γu ⊢ C : T) ->
      ind_member D m = Some Mm -> im_head Mm = mh_view qv kv Iv vm -> ind_lookup gc_deps gc_stack qv = Some Dqv ->
      nbes gc_deps gc_stack Γu (List.map (fun I => I[sb_of_list sb_id Cs]) Iv)
        (List.map (fun T => T[sb_of_list sb_id Cs]) (tele_insts (ind_uparams Dqv) sb_id Iv)) Ws ->
      sibs_from gc_deps gc_stack Γu qx Cs 0 (ind_members D) ss ->
      sibs_from gc_deps gc_stack Γu qv (List.map nf_to_exp Ws) 0 (ind_members Dqv) ssy ->
      incl ssy ss.
  Proof.
    intros * Hg HΓu Hl HCl HCt HMm Hh Hlv Hn Hss Hssy e He.
    destruct (decl_of_glookup _ _ _ _ Hg Hl) as [Hdt Hc].
    destruct (decl_of_glookup _ _ _ _ Hg Hlv) as [Hdtv Hcv].
    destruct (decl_typed_view _ _ _ Hdt _ _ _ _ _ _ HMm Hh) as (Dqv' & Mkv & Hlv' & HMkv & Hkv & HIl & Hvml & Hvmk & _).
    rewrite Hlv in Hlv'; injection Hlv' as <-.
    pose proof (wf_uparams_sub _ _ _ _ _ Hdt HΓu HCl HCt) as HσC.
    destruct (sibs_from_in _ _ _ _ _ _ _ _ Hssy _ He) as (i' & Mi' & HMi' & Hei' & Hse).
    cbn [Nat.add] in Hse.
    assert (Hi'l : i' < List.length vm) by (rewrite Hvml; apply List.nth_error_Some; congruence).
    destruct (nth_error_lt_some' vm i' Hi'l) as [v Hv].
    destruct (sibs_from_nth _ _ _ _ _ _ _ _ Hss) as [Hssl Hssn].
    inversion Hse as [? ? pm' Hhd | ? ? q'' k'' Is'' vm'' D'' We Hhd Hl'' Hne | ? ? q'' Is'' fl'' R'' We Hhd Hl'' Hne]; subst.
    - (* a declared member of the sibling's group: the view of it at the
         same instance *)
      destruct (decl_typed_view_decl _ _ _ Hdt _ _ _ _ _ _ _ _ _ _ _ HMm Hh Hlv HMi' Hhd Hv) as (Mv & vm' & HMv & HhMv).
      destruct (Hssn _ _ HMv) as (e0 & He0 & Hse0).
      inversion Hse0 as [? ? ? Hh0 | ? ? qv0 kv0 Iv0 vm0 Dv0 Ws0 Hh0 Hl0 Hn0 | ? ? ? ? ? ? ? Hh0 ? ?]; subst; rewrite HhMv in Hh0;
        try discriminate.
      injection Hh0 as <- <- <- <-.
      rewrite Hlv in Hl0; injection Hl0 as <-.
      rewrite (nbes_functional _ _ _ _ _ _ _ Hn0 Hn) in He0.
      exact (List.nth_error_In _ _ He0).
    - (* a view of the sibling's group: the view of the same member, at an
         instance equal to the sibling's instance there *)
      destruct (decl_typed_view_view _ _ _ Hdt m Mm qv kv Iv vm Dqv i' Mi' v q'' k'' Is'' vm'' HMm Hh Hlv HMi' Hhd Hv)
        as (Mv & X & vm' & HMv & HhMv & HXl).
      destruct (Hssn _ _ HMv) as (e0 & He0 & Hse0).
      inversion Hse0 as [? ? ? Hh0 | ? ? qv0 kv0 Iv0 vm0 Dv0 Ws0 Hh0 Hl0 Hn0 | ? ? ? ? ? ? ? Hh0 ? ?]; subst; rewrite HhMv in Hh0;
        try discriminate.
      injection Hh0 as <- <- <- <-.
      rewrite Hl'' in Hl0; injection Hl0 as <-.
      destruct (decl_of_glookup _ _ _ _ Hg Hl'') as [Hdt'' Hc''].
      rewrite (tele_insts_sub (ind_uparams D'') 0 Id Id (sb_of_list sb_id Cs) X (decl_closed_ass _ Hc'') (decl_closed_uparams _ Hc'')
                 ltac:(intros; lia)) in Hn0.
      rewrite (tele_insts_sub (ind_uparams D'') 0 Id Id (sb_of_list sb_id (List.map nf_to_exp Ws)) Is'' (decl_closed_ass _ Hc'') (decl_closed_uparams _ Hc'')
                 ltac:(intros; lia)) in Hne.
      enough (Hw : Ws0 = We) by (subst Ws0; exact (List.nth_error_In _ _ He0)).
      assert (HsIs : List.Forall (exp_scoped (ind_nu Dqv)) Is'') by exact (decl_closed_head_scoped Dqv Hcv _ _ _ _ _ _ HMi' Hhd).
      set (σC := sb_of_list sb_id Cs) in *.
      set (σY := sb_of_list sb_id (List.map nf_to_exp Ws)) in *.
      assert (HIvC : forall I, In I Is'' -> I[sb_of_list Id Iv][σC] = I[sb_of_list Id (List.map (fun J => J[σC]) Iv)]).
      { intros I HI; apply exp_list_grp_sb0; rewrite HIl; rewrite List.Forall_forall in HsIs; exact (HsIs _ HI). }
      rewrite (tele_insts_sub (ind_uparams Dqv) 0 Id Id σC Iv (decl_closed_ass _ Hcv) (decl_closed_uparams _ Hcv) ltac:(intros; lia)) in Hn.
      destruct (nbes_nth _ _ _ _ _ _ Hn) as (HlWs & HlTs & Hnth).
      (** the view's instance at [Cs] is equal to its normal form *)
      assert (HσIY : Γu ⊢ˢ sb_of_list Id (List.map (fun J => J[σC]) Iv) ≈ σY : ind_uparams Dqv).
      { rewrite <- (List.app_nil_r (ind_uparams Dqv)).
        eapply wf_sub_eq_of_list; [ exact (decl_closed_ass _ Hcv) | rewrite List.app_nil_r; exact (decl_typed_uparams_field _ _ _ Hdtv)
                                  | exact (wf_sub_eq_refl _ _ _ _ _ (wf_sub_to_nil _ _ _ HΓu)) | rewrite List.length_map; exact HIl
                                  | rewrite List.length_map, HlWs, List.length_map; exact HIl |].
        intros j0 N0 N0' T0 HN0 HN0' HT0.
        destruct (Hnth _ _ _ HN0 HT0) as (W0 & HW0 & HN0t & HN0W).
        rewrite List.nth_error_map, HW0 in HN0'; cbn in HN0'; injection HN0' as <-.
        exact (soundness' HN0t HN0W). }
      assert (HUD : ⊢ ind_uparams D) by exact (decl_typed_uparams_field _ _ _ Hdt).
      assert (HTsub : forall (τ : sub) Ms j0 T0, List.nth_error (tele_insts (ind_uparams D'') Id Ms) j0 = Some T0 ->
                List.nth_error (tele_insts (ind_uparams D'') Id (List.map (fun M => M[τ]) Ms)) j0 = Some T0[τ])
        by (intros; apply tele_insts_closed_sub; [ exact (decl_closed_ass _ Hc'') | exact (decl_closed_uparams _ Hc'') | assumption ]).
      apply (nbes_conv_inst Γu (ind_uparams D'') _ _ _ _ (decl_closed_ass _ Hc'') (decl_typed_uparams_field _ _ _ Hdt'') HΓu Hn0 Hne);
        [ rewrite !List.length_map; exact HXl |].
      intros j N N' T HN HN' HT.
      apply nth_error_map_inv in HN as (Cj & HCj & ->); apply nth_error_map_inv in HN' as (Ij & HIj & ->).
      assert (Hjl : j < List.length Is'') by (apply List.nth_error_Some; congruence).
      assert (HUa'' : tele_ass (ind_uparams D'')) by exact (decl_closed_ass _ Hc'').
      destruct (nth_error_lt_some' (tele_insts (ind_uparams D'') Id Is'') j
                  ltac:(rewrite length_tele_insts by exact HUa''; pose proof (decl_typed_view _ _ _ Hdtv _ _ _ _ _ _ HMi' Hhd) as (? & ? & Hl3 & _ & _ & HIl3 & _);
                        rewrite Hl'' in Hl3; injection Hl3 as <-; unfold ind_nu in HIl3; lia)) as [T0 HT0].
      destruct (nth_error_lt_some' (tele_insts (ind_uparams D'') Id X) j
                  ltac:(rewrite length_tele_insts by exact HUa'';
                        assert (HT1l : j < List.length (tele_insts (ind_uparams D'') Id Is'')) by (apply List.nth_error_Some; congruence);
                        rewrite length_tele_insts in HT1l by exact HUa''; lia)) as [T1 HT1].
      pose proof (HTsub σC X j T1 HT1) as HT1C; rewrite HT in HT1C; injection HT1C as ->.
      (** the view equation of the instances, at the group's uniform
          parameters *)
      assert (HeqD : forall j' C C' T', List.nth_error X j' = Some C ->
                List.nth_error (List.map (fun I => I[sb_of_list Id Iv]) Is'') j' = Some C' ->
                List.nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T' ->
                ind_uparams D ⊢ C ≈ C' : T'[sb_of_list Id Iv])
        by (intros; eapply (decl_typed_view_view_is _ _ _ _ Hg Hdt Hl m Mm qv kv Iv vm Dqv i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm');
            eassumption).
      assert (HIjv : List.nth_error (List.map (fun I => I[sb_of_list Id Iv]) Is'') j = Some Ij[sb_of_list Id Iv])
        by (rewrite List.nth_error_map, HIj; reflexivity).
      pose proof (HeqD _ _ _ _ HCj HIjv HT0) as Hab.
      destruct (tele_insts_cong_upto (ind_uparams D'') nil (ind_uparams D) Id Id (List.map (fun I => I[sb_of_list Id Iv]) Is'') X
                  HUa'' ltac:(rewrite List.app_nil_r; exact (decl_typed_uparams_field _ _ _ Hdt'')) (wf_sub_eq_refl _ _ _ _ _ (wf_sub_to_nil _ _ _ HUD))
                  j _ _ (HTsub _ _ _ _ HT0) HT1) as [i HT01].
      { intros j' N0 N0' T0' _ HN0 HN0' HT0'.
        assert (Hj'l : j' < List.length (tele_insts (ind_uparams D'') Id Is''))
          by (rewrite length_tele_insts by exact HUa'';
              assert (Hx : j' < List.length (tele_insts (ind_uparams D'') Id (List.map (fun I => I[sb_of_list Id Iv]) Is'')))
                by (apply List.nth_error_Some; congruence);
              rewrite length_tele_insts, List.length_map in Hx by exact HUa''; lia).
        destruct (nth_error_lt_some' _ _ Hj'l) as [T' HT'].
        rewrite (HTsub _ _ _ _ HT') in HT0'; injection HT0' as <-.
        apply nth_error_map_inv in HN0 as (I0 & HI0 & ->).
        apply wf_exp_eq_sym; apply (HeqD j'); [ exact HN0' | rewrite List.nth_error_map, HI0; reflexivity | exact HT' ]. }
      (** moved to [Γu] along [Cs], and the view's instance replaced by its
          normal form *)
      pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ Hab HσC) as Hab'.
      pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HT01 HσC) as HT01'; cbn [exp_sub] in HT01'.
      rewrite (HIvC Ij (List.nth_error_In _ _ HIj)) in Hab'.
      pose proof (decl_typed_view_is _ _ _ _ Hg Hdtv Hlv i' Mi' q'' k'' Is'' vm'' D'' j Ij T0 HMi' Hhd Hl'' HIj HT0) as HIjt.
      pose proof (sub_eq_preserves_exp _ _ _ _ _ HIjt _ _ _ HσIY) as Hb.
      assert (HTT : T0[sb_of_list Id (List.map (fun J => J[σC]) Iv)] = T0[sb_of_list Id Iv][σC]).
      { pose proof (HTsub σC _ _ _ (HTsub (sb_of_list Id Iv) _ _ _ HT0)) as E1.
        pose proof (HTsub (sb_of_list Id (List.map (fun J => J[σC]) Iv)) _ _ _ HT0) as E2.
        rewrite List.map_map, (List.map_ext_in _ (fun I => I[sb_of_list Id (List.map (fun J => J[σC]) Iv)])) in E1
          by (intros I HI; exact (HIvC I HI)).
        rewrite E1 in E2; injection E2 as E2; symmetry; exact E2. }
      rewrite HTT in Hb.
      eapply wf_exp_eq_conv'; [ eapply wf_exp_eq_trans; [ exact Hab' | exact Hb ] | exact HT01' ].
    - (* a record view of the sibling's group: the record view of the same
         record, at an instance equal to the sibling's instance there *)
      destruct (decl_typed_view_rview _ _ _ Hdt m Mm qv kv Iv vm Dqv i' Mi' v q'' Is'' fl'' HMm Hh Hlv HMi' Hhd Hv)
        as (Mv & X & HMv & HhMv & HXl).
      destruct (Hssn _ _ HMv) as (e0 & He0 & Hse0).
      inversion Hse0 as [? ? ? Hh0 | ? ? ? ? ? ? ? ? Hh0 ? ? | ? ? qr0 Ir0 fl0 R0 Ws0 Hh0 Hl0 Hn0]; subst; rewrite HhMv in Hh0;
        try discriminate.
      injection Hh0 as <- <- <-.
      rewrite Hl'' in Hl0; injection Hl0 as <-.
      pose proof (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ Hg) Hl'') as HcR.
      pose proof (record_lookup_typed _ _ Hg (gctx_valid_syn _ _ Hg) _ _ Hl'') as HRt.
      pose proof (record_typed_fctx_wf _ _ _ HRt 0 ltac:(lia)) as HP0; cbn [record_fctx List.app] in HP0.
      assert (HRa : tele_ass (record_params R'')) by exact (typed_params_ass _ _ _ HRt).
      rewrite (record_params_insts_sub R'' X (sb_of_list sb_id Cs) HcR) in Hn0.
      rewrite (record_params_insts_sub R'' Is'' (sb_of_list sb_id (List.map nf_to_exp Ws)) HcR) in Hne.
      enough (Hw : Ws0 = We) by (subst Ws0; exact (List.nth_error_In _ _ He0)).
      assert (HsIs : List.Forall (exp_scoped (ind_nu Dqv)) Is'') by exact (decl_closed_rhead_scoped Dqv Hcv _ _ _ _ _ HMi' Hhd).
      set (σC := sb_of_list sb_id Cs) in *.
      set (σY := sb_of_list sb_id (List.map nf_to_exp Ws)) in *.
      assert (HIvC : forall I, In I Is'' -> I[sb_of_list Id Iv][σC] = I[sb_of_list Id (List.map (fun J => J[σC]) Iv)]).
      { intros I HI; apply exp_list_grp_sb0; rewrite HIl; rewrite List.Forall_forall in HsIs; exact (HsIs _ HI). }
      rewrite (tele_insts_sub (ind_uparams Dqv) 0 Id Id σC Iv (decl_closed_ass _ Hcv) (decl_closed_uparams _ Hcv) ltac:(intros; lia)) in Hn.
      destruct (nbes_nth _ _ _ _ _ _ Hn) as (HlWs & HlTs & Hnth).
      (** the view's instance at [Cs] is equal to its normal form *)
      assert (HσIY : Γu ⊢ˢ sb_of_list Id (List.map (fun J => J[σC]) Iv) ≈ σY : ind_uparams Dqv).
      { rewrite <- (List.app_nil_r (ind_uparams Dqv)).
        eapply wf_sub_eq_of_list; [ exact (decl_closed_ass _ Hcv) | rewrite List.app_nil_r; exact (decl_typed_uparams_field _ _ _ Hdtv)
                                  | exact (wf_sub_eq_refl _ _ _ _ _ (wf_sub_to_nil _ _ _ HΓu)) | rewrite List.length_map; exact HIl
                                  | rewrite List.length_map, HlWs, List.length_map; exact HIl |].
        intros j0 N0 N0' T0 HN0 HN0' HT0.
        destruct (Hnth _ _ _ HN0 HT0) as (W0 & HW0 & HN0t & HN0W).
        rewrite List.nth_error_map, HW0 in HN0'; cbn in HN0'; injection HN0' as <-.
        exact (soundness' HN0t HN0W). }
      assert (HUD : ⊢ ind_uparams D) by exact (decl_typed_uparams_field _ _ _ Hdt).
      assert (HTsub : forall (τ : sub) Ms j0 T0, List.nth_error (tele_insts (record_params R'') Id Ms) j0 = Some T0 ->
                List.nth_error (tele_insts (record_params R'') Id (List.map (fun M => M[τ]) Ms)) j0 = Some T0[τ])
        by (intros; apply tele_insts_closed_sub; [ exact HRa | exact (closed_params _ HcR) | assumption ]).
      destruct (rview_struct_record _ _ _ (decl_typed_rstruct _ _ _ Hdtv) _ _ _ _ _ HMi' Hhd) as [R3 HR3].
      pose proof (rview_record_lookup _ _ _ _ _ _ HR3) as Hl3; rewrite Hl'' in Hl3; injection Hl3 as <-.
      pose proof (rview_record_count _ _ _ _ _ _ HR3) as HIl''.
      apply (nbes_conv_inst Γu (record_params R'') _ _ _ _ HRa HP0 HΓu Hn0 Hne);
        [ rewrite !List.length_map; exact HXl |].
      intros j N N' T HN HN' HT.
      apply nth_error_map_inv in HN as (Cj & HCj & ->); apply nth_error_map_inv in HN' as (Ij & HIj & ->).
      destruct (nth_error_lt_some' (tele_insts (record_params R'') Id Is'') j
                  ltac:(rewrite length_tele_insts by exact HRa; assert (Hjl : j < List.length Is'') by (apply List.nth_error_Some; congruence);
                        lia)) as [T0 HT0].
      destruct (nth_error_lt_some' (tele_insts (record_params R'') Id X) j
                  ltac:(rewrite length_tele_insts by exact HRa;
                        assert (HT1l : j < List.length (tele_insts (record_params R'') Id Is'')) by (apply List.nth_error_Some; congruence);
                        rewrite length_tele_insts in HT1l by exact HRa; lia)) as [T1 HT1].
      pose proof (HTsub σC X j T1 HT1) as HT1C; rewrite HT in HT1C; injection HT1C as ->.
      (** the record view equation of the instances, at the group's
          uniform parameters *)
      assert (HeqD : forall j' C C' T', List.nth_error X j' = Some C ->
                List.nth_error (List.map (fun I => I[sb_of_list Id Iv]) Is'') j' = Some C' ->
                List.nth_error (tele_insts (record_params R'') Id Is'') j' = Some T' ->
                ind_uparams D ⊢ C ≈ C' : T'[sb_of_list Id Iv])
        by (intros; eapply (decl_typed_view_rview_is _ _ _ _ Hg Hdt Hl m Mm qv kv Iv vm Dqv i' Mi' v q'' Is'' fl'' R'' Mv X fl'');
            eassumption).
      assert (HIjv : List.nth_error (List.map (fun I => I[sb_of_list Id Iv]) Is'') j = Some Ij[sb_of_list Id Iv])
        by (rewrite List.nth_error_map, HIj; reflexivity).
      pose proof (HeqD _ _ _ _ HCj HIjv HT0) as Hab.
      destruct (tele_insts_cong_upto (record_params R'') nil (ind_uparams D) Id Id (List.map (fun I => I[sb_of_list Id Iv]) Is'') X
                  HRa ltac:(rewrite List.app_nil_r; exact HP0) (wf_sub_eq_refl _ _ _ _ _ (wf_sub_to_nil _ _ _ HUD))
                  j _ _ (HTsub _ _ _ _ HT0) HT1) as [i HT01].
      { intros j' N0 N0' T0' _ HN0 HN0' HT0'.
        assert (Hj'l : j' < List.length (tele_insts (record_params R'') Id Is''))
          by (rewrite length_tele_insts by exact HRa;
              assert (Hx : j' < List.length (tele_insts (record_params R'') Id (List.map (fun I => I[sb_of_list Id Iv]) Is'')))
                by (apply List.nth_error_Some; congruence);
              rewrite length_tele_insts, List.length_map in Hx by exact HRa; lia).
        destruct (nth_error_lt_some' _ _ Hj'l) as [T' HT'].
        rewrite (HTsub _ _ _ _ HT') in HT0'; injection HT0' as <-.
        apply nth_error_map_inv in HN0 as (I0 & HI0 & ->).
        apply wf_exp_eq_sym; apply (HeqD j'); [ exact HN0' | rewrite List.nth_error_map, HI0; reflexivity | exact HT' ]. }
      (** moved to [Γu] along [Cs], and the view's instance replaced by its
          normal form *)
      pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ Hab HσC) as Hab'.
      pose proof (sub_preserves_exp_eq _ _ _ _ _ _ _ _ HT01 HσC) as HT01'; cbn [exp_sub] in HT01'.
      rewrite (HIvC Ij (List.nth_error_In _ _ HIj)) in Hab'.
      pose proof (decl_typed_rview_is _ _ _ _ Hg Hdtv Hlv i' Mi' q'' Is'' fl'' R'' j Ij T0 HMi' Hhd Hl'' HIj HT0) as HIjt.
      pose proof (sub_eq_preserves_exp _ _ _ _ _ HIjt _ _ _ HσIY) as Hb.
      assert (HTT : T0[sb_of_list Id (List.map (fun J => J[σC]) Iv)] = T0[sb_of_list Id Iv][σC]).
      { pose proof (HTsub σC _ _ _ (HTsub (sb_of_list Id Iv) _ _ _ HT0)) as E1.
        pose proof (HTsub (sb_of_list Id (List.map (fun J => J[σC]) Iv)) _ _ _ HT0) as E2.
        rewrite List.map_map, (List.map_ext_in _ (fun I => I[sb_of_list Id (List.map (fun J => J[σC]) Iv)])) in E1
          by (intros I HI; exact (HIvC I HI)).
        rewrite E1 in E2; injection E2 as E2; symmetry; exact E2. }
      rewrite HTT in Hb.
      eapply wf_exp_eq_conv'; [ eapply wf_exp_eq_trans; [ exact Hab' | exact Hb ] | exact HT01' ].
  Qed.
End SiblingInv.

(** ** Where a Constructor's Classified Arguments Meet an Instance *)

(** An instance the classified arguments [gs] meet is met by one of them,
    classified in the context of those before it, with as many bits as
    arguments before. *)
Lemma cls_args_in_meet : forall Θ Ξ Γp nu np n pat args1 args gs,
    cls_args_in Θ Ξ Γp nu np n pat args1 args gs -> List.length pat = List.length args1 ->
    forall z, In z (List.concat (List.map rcarg_view gs)) ->
    exists args1' T g pat', cls_arg_in Θ Ξ (rtele args1' ++ Γp) nu np n pat' T g /\ In z (rcarg_view g) /\
      List.length pat' = List.length args1'.
Proof.
  induction 1 as [| pat args1 y T args g gs Hg Hgs IH]; intros Hl z Hz; cbn in Hz; [ destruct Hz |].
  apply List.in_app_or in Hz as [Hz | Hz].
  - exists args1, T, g, pat; auto.
  - apply IH; [ rewrite List.length_app; cbn; lia | exact Hz ].
Qed.

(** An instance the classified constructors meet. *)
Lemma cls_cons_in_meet : forall Θ Ξ Γp nu np n rcs cs, cls_cons_in Θ Ξ Γp nu np n rcs cs ->
    forall z, In z (rcons_views cs) ->
    exists args1' T g pat', cls_arg_in Θ Ξ (rtele args1' ++ Γp) nu np n pat' T g /\ In z (rcarg_view g) /\
      List.length pat' = List.length args1'.
Proof.
  unfold cls_cons_in, rcons_views; induction 1 as [| rc c rcs cs [_ Hc] _ IH]; intros z Hz; cbn in Hz; [ destruct Hz |].
  apply List.in_app_or in Hz as [Hz | Hz]; [| exact (IH _ Hz) ].
  exact (cls_args_in_meet _ _ _ _ _ _ _ _ _ _ Hc eq_refl _ Hz).
Qed.

(** The instances any view's constructors meet are typed views, whose
    arguments are their own normal forms. *)
Theorem view_meets_inv : forall Θ Ξ R x cs z, view_cls Θ Ξ R x cs -> In z (rcons_views cs) ->
    key_inv Θ Ξ (rd_uctx Ξ R) z.
Proof.
  intros * Hx Hz.
  inversion Hx as [qx kx Csx D' Mk' cs' HD' HMk' Hcls | qx Isx Rr cs' HRr Hcls]; subst.
  - destruct (cls_cons_in_meet _ _ _ _ _ _ _ _ Hcls _ Hz) as (args1 & T & g & pat & Hg & Hin & Hl).
    inversion Hg as [g' Hsyn | i W g' Hnf HT HW Hcl]; subst.
    + rewrite (cls_arg_none_view _ _ _ _ _ _ Hsyn) in Hin; destruct Hin.
    + set (Δ := rtele args1 ++ tele_sub (im_nparams Mk') (sb_of_list sb_id Csx)).
      assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Δ ++ rd_uctx Ξ R) by (unfold Δ; rewrite <- List.app_assoc; gen_presups; assumption).
      destruct (decl_of_lookup _ _ _ _ _ HΓ HD') as [Hdt _].
      apply (@nest_key_inv (gc_mk Θ Ξ) Δ (rd_uctx Ξ R) T W i (rd_nu R) (im_nn Mk' + rd_nu R) (rd_n R) pat g); cbn.
      * unfold Δ, tele_ass, rtele; apply List.Forall_app; split;
          [ apply List.Forall_rev, List.Forall_map, List.Forall_forall; intros; eexists; reflexivity
          | apply tele_ass_sub, (decl_typed_nparams_ass _ _ _ Hdt _ _ HMk') ].
      * unfold Δ, rtele; rewrite List.length_app, List.length_rev, List.length_map, length_tele_sub; unfold im_nn; lia.
      * unfold Δ; rewrite <- List.app_assoc; exact HT.
      * unfold Δ; rewrite <- List.app_assoc; exact HW.
      * exact Hcl.
      * exact Hin.
  - (** a record view: its fields, over the group's context *)
    destruct (cls_cons_in_meet _ _ _ _ _ _ _ _ Hcls _ Hz) as (args1 & T & g & pat & Hg & Hin & Hl).
    inversion Hg as [g' Hsyn | i W g' Hnf HT HW Hcl]; subst.
    + rewrite (cls_arg_none_view _ _ _ _ _ _ Hsyn) in Hin; destruct Hin.
    + apply (@nest_key_inv (gc_mk Θ Ξ) (rtele args1) (rd_uctx Ξ R) T W i (rd_nu R) (rd_nu R) (rd_n R) pat g); cbn.
      * unfold tele_ass, rtele; apply List.Forall_rev, List.Forall_map, List.Forall_forall; intros; eexists; reflexivity.
      * unfold rtele; rewrite List.length_rev, List.length_map; lia.
      * exact HT.
      * exact HW.
      * exact Hcl.
      * exact Hin.
Qed.
