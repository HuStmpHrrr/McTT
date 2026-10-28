(** * The Branches of a View's Blocks in its Container's Eliminator

    The eliminator of a group [D] at its view is the container's
    eliminator at the view's blocks wrapped ([view_wrap], E1′): the block of
    the container's member [i'] is that of the member [v] the view takes it
    to, each branch the group's at an instance ([wrap_br]).  The instance
    is a substitution of the group's branch's context, from a context made
    of the view's member's own parameters and arguments, with a recursive
    result at each leaf path the container has ([wrap_bctx], [leaf_in]):
    the group's eliminator at the others.  This is the semantic counterpart
    of the branches of [Views.v] (Section [ViewBranch]), read on the
    group's side: the context is valid ([valid_wrap_bctx]), the instance is
    a substitution built from valid parts ([gsub_wrap_br]), and so the
    wrapped branch is valid there ([valid_wrap_br]). *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Syntactic.System Require Import Definitions Scoping.
From Mctt.Core.Syntactic.System.Inductives Require Import Syntax Typing Views.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas MemberWf.
From Mctt.Core.Completeness Require Import LogicalRelation ContextCases UniverseCases.
From Mctt.Core.Completeness.LogicalRelation Require Import Substitution Instance Telescope.
From Mctt.Core.Completeness Require Import LetCases UnitCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Completeness.Modules Require Import MemberTypes.
From Mctt.Core.Completeness Require Import VariableCases FunctionCases LevelCases SubtypingCases.
From Mctt.Core.Completeness.Inductives Require Import Decl Model FiledViews ArgTypes ViewEquations ViewArgs Con Elim Iota.
From Mctt.Core.Semantic Require Import Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndPER IndCanon ViewCoherence IndElim.
From Mctt.Core.Semantic Require Import Evaluation.Modules.
From Mctt.Core.Semantic.PER Require Import Tele.
Import Domain_Notations Fixed_Notations Wk_Notations.
#[local] Open Scope list_scope.

(** ** The Context of a Wrapped Branch

    A wrapped branch's context has [nn] non-uniform parameters, [na]
    arguments and [r] recursive results; [wrap_base] is the instance of
    the group's parameters there (the uniform parameters [Us] weakened,
    the non-uniform ones as variables), which the shapes of the arguments
    are moved by after the arguments before them ([cargs_sub]). *)
Definition wrap_base (Us : list exp) (nn na r : nat) : sub :=
  sb_of_list (sb_of_wk (wk_shiftn (r + na + nn))) (List.map (fun U => U[wk_shiftn (r + na + nn)]ʷ) Us ++ vars_from (r + na) nn).

(** The recursive results along the leaf paths [ls] of an argument
    recursive in the view and in its container (the container's shape
    [t']): one per path the container has ([leaf_in]), at the group's type
    of the recursive result along it, [r] of them before.  [gs0] are the
    view's arguments before. *)
Fixpoint wrap_leaves_ctx (D' : ind_decl) (t' : ptyp) (nn : nat) (As Us : list exp) (na : nat) (gs0 : list carg) (r : nat)
    (ls : list leaf_path) : ctx :=
  match ls with
  | nil => nil
  | l :: ls' =>
      if leaf_in D' t' l
      then wrap_leaves_ctx D' t' nn As Us na gs0 (S r) ls' ++
             ce_ass (leaf_ihty As (sb_of_wk (wk_shiftn (r + na + nn))) (cargs_sub (wrap_base Us nn na r) gs0 (vars_from r na))
                       (a_var (r + (na - 1 - List.length gs0))) l) :: nil
      else wrap_leaves_ctx D' t' nn As Us na gs0 r ls'
  end.

(** The recursive results of a view's constructor that its container has
    ([gs'] the container's arguments, [gs] the view's): of each argument
    recursive in both, those along the leaf paths the container has; an
    argument recursive in the view only has none.  [gs0] are the view's
    arguments before, [r] the recursive results before. *)
Fixpoint wrap_ihs_ctx (D D' : ind_decl) (nn : nat) (As Us : list exp) (na : nat) (gs0 : list carg) (r : nat)
    (gs' gs : list carg) : ctx :=
  match gs', gs with
  | ca_rec t' :: gs1', ca_rec t :: gs1 =>
      let ls := shape_leaves (rv_leaves D) (pat_nargs (cargs_pat gs0) + nn) t in
      wrap_ihs_ctx D D' nn As Us na (gs0 ++ ca_rec t :: nil) (leaves_in_count D' t' ls + r) gs1' gs1 ++
        wrap_leaves_ctx D' t' nn As Us na gs0 r ls
  | ca_arg _ :: gs1', ca_rec t :: gs1 => wrap_ihs_ctx D D' nn As Us na (gs0 ++ ca_rec t :: nil) r gs1' gs1
  | _ :: gs1', ca_arg A :: gs1 => wrap_ihs_ctx D D' nn As Us na (gs0 ++ ca_arg A :: nil) r gs1' gs1
  | _, _ => nil
  end.

(** The context of a wrapped branch ([wrap_br]): the view's member's
    non-uniform parameters and arguments, and the recursive results the
    container has, the motives being [As]. *)
Definition wrap_bctx (pq : qname) (D D' : ind_decl) (M : imember) (gs' gs : list carg) (As Us : list exp) : ctx :=
  wrap_ihs_ctx D D' (im_nn M) As Us (List.length gs) nil 0 gs' gs ++
  tele_sub (cargs_ctx pq D M gs) (sb_qn (im_nn M) (sb_of_list Id Us)) ++
  tele_sub (im_nparams M) (sb_of_list Id Us).

(** The instance of the view's branch's context in a wrapped branch: the
    substitution [wrap_br] moves the branch by. *)
Definition wrap_br_sub (pq : qname) (D D' : ind_decl) (Us : list exp) (Bks : list eblock) (Mv : imember) (gs' gs : list carg)
  : sub :=
  let nn := im_nn Mv in
  let na := List.length gs' in
  let nr' := cargs_nrec D' gs' in
  let n' := (nn + na + nr')%nat in
  let Us' := List.map (fun U => U[wk_shiftn n']ʷ) Us in
  let nvars := vars_from (nr' + na) nn in
  let avars := vars_from nr' na in
  let ihs := elim_ihs pq D (Some pq) Us' (blocks_wk Bks (wk_shiftn n')) (sb_of_list (sb_of_wk (wk_shiftn n')) (Us' ++ nvars))
               nn gs avars in
  sb_of_list (sb_of_wk (wk_shiftn n')) (nvars ++ avars ++ wrap_ihs D' D gs' gs ihs 0 nr').

Lemma wrap_br_snd : forall pq D D' Us Bks Mv Bs c gs' gs n B, ind_con Mv c = Some gs -> brs_lookup Bs c = Some (n, B) ->
    snd (wrap_br pq D D' Us Bks Mv Bs c gs') = B[wrap_br_sub pq D D' Us Bks Mv gs' gs].
Proof. intros * Hc Hb; unfold wrap_br, wrap_br_sub; cbv zeta; rewrite Hc, Hb; reflexivity. Qed.

Lemma length_wrap_leaves_ctx : forall D' t' nn As Us na gs0 ls r,
    List.length (wrap_leaves_ctx D' t' nn As Us na gs0 r ls) = leaves_in_count D' t' ls.
Proof.
  intros D' t' nn As Us na gs0; induction ls as [| l ls IH]; intros r; cbn [wrap_leaves_ctx]; [ reflexivity |].
  unfold leaves_in_count in *; cbn [List.filter]; destruct (leaf_in D' t' l); cbn [List.length];
    rewrite ?List.length_app, IH; cbn [List.length]; lia.
Qed.

Lemma wrap_leaves_ctx_app : forall D' t' nn As Us na gs0 ls1 ls2 r,
    wrap_leaves_ctx D' t' nn As Us na gs0 r (ls1 ++ ls2)
    = wrap_leaves_ctx D' t' nn As Us na gs0 (leaves_in_count D' t' ls1 + r) ls2 ++ wrap_leaves_ctx D' t' nn As Us na gs0 r ls1.
Proof.
  intros D' t' nn As Us na gs0; induction ls1 as [| l ls1 IH]; intros ls2 r; cbn [List.app wrap_leaves_ctx];
    [ rewrite List.app_nil_r; reflexivity |].
  unfold leaves_in_count in *; cbn [List.filter]; destruct (leaf_in D' t' l); cbn [List.length].
  - rewrite IH, <- List.app_assoc; f_equal; f_equal; lia.
  - apply IH.
Qed.

(** The recursive results along the leaf paths [ls], selected by [inb]: a
    variable of the context, the next of [r'] before [nr'], at a selected
    path, the term of [ihs] at the others ([wrap_leaves] at [leaf_in]). *)
Fixpoint sel_leaves (inb : leaf_path -> bool) (ls : list leaf_path) (ihs : list exp) (r' nr' : nat) : list exp :=
  match ls, ihs with
  | l :: ls', ih :: ihs' =>
      if inb l then a_var (nr' - 1 - r') :: sel_leaves inb ls' ihs' (S r') nr'
      else ih :: sel_leaves inb ls' ihs' r' nr'
  | _, _ => nil
  end.

Lemma wrap_leaves_sel : forall D' t' ls ihs r' nr', wrap_leaves D' t' ls ihs r' nr' = sel_leaves (leaf_in D' t') ls ihs r' nr'.
Proof. intros D' t'; induction ls as [| l ls IH]; intros [| ih ihs] r' nr'; cbn; try reflexivity; rewrite !IH; reflexivity. Qed.

Lemma sel_leaves_none : forall ls ihs r' nr', List.length ihs = List.length ls -> sel_leaves (fun _ => false) ls ihs r' nr' = ihs.
Proof. induction ls as [| l ls IH]; intros [| ih ihs] r' nr' H; cbn in *; try discriminate; [ reflexivity | rewrite IH by lia; reflexivity ]. Qed.

Lemma length_sel_leaves : forall inb ls ihs r' nr', List.length ihs = List.length ls ->
    List.length (sel_leaves inb ls ihs r' nr') = List.length ls.
Proof.
  intros inb; induction ls as [| l ls IH]; intros [| ih ihs] r' nr' H; cbn in *; try discriminate; [ reflexivity |].
  destruct (inb l); cbn; rewrite IH by lia; reflexivity.
Qed.

Lemma cargs_kinds_app_inv : forall gs1' gs1 gs2' gs2, List.length gs1' = List.length gs1 ->
    cargs_kinds (gs1' ++ gs2') (gs1 ++ gs2) -> cargs_kinds gs1' gs1 /\ cargs_kinds gs2' gs2.
Proof.
  induction gs1' as [| [] gs1' IH]; intros [| [] gs1] * Hl H; cbn in Hl; try discriminate; cbn in H |- *;
    try contradiction; try (split; [ exact I | exact H ]); exact (IH gs1 gs2' gs2 ltac:(lia) H).
Qed.

Lemma cargs_kinds_app : forall gs1' gs1 gs2' gs2, cargs_kinds gs1' gs1 -> cargs_kinds gs2' gs2 ->
    cargs_kinds (gs1' ++ gs2') (gs1 ++ gs2).
Proof. induction gs1' as [| [] gs1' IH]; intros [| [] gs1] * H1 H2; cbn in *; try contradiction; auto. Qed.

Lemma cargs_nrec_app' : forall D gs1 gs2, cargs_nrec D (gs1 ++ gs2) = cargs_nrec D gs1 + cargs_nrec D gs2.
Proof. intros D; induction gs1 as [| [] gs1 IH]; intros; cbn; rewrite ?IH; lia. Qed.

Lemma cargs_nin_app : forall D D' gs1' gs1 gs2' gs2, cargs_kinds gs1' gs1 ->
    cargs_nin D D' (gs1' ++ gs2') (gs1 ++ gs2) = cargs_nin D D' gs1' gs1 + cargs_nin D D' gs2' gs2.
Proof. intros D D'; induction gs1' as [| [] gs1' IH]; intros [| [] gs1] * H; cbn in *; try contradiction; rewrite ?IH by exact H; lia. Qed.

(** Which leaf paths of an argument's shape are the container's does not
    depend on the binders the shape's components are over. *)
Lemma leaves_in_count_shift : forall D D' t' t m,
    leaves_in_count D' t' (shape_leaves (rv_leaves D) m t) = leaves_in_count D' t' (shape_leaves (rv_leaves D) 0 t).
Proof. intros; apply leaves_in_count_ext, leaf_in_shape_leaves. Qed.

Lemma length_wrap_ihs_ctx : forall D D' nn As Us na gs' gs gs0 r,
    cargs_kinds gs' gs -> List.length (wrap_ihs_ctx D D' nn As Us na gs0 r gs' gs) = cargs_nin D D' gs' gs.
Proof.
  intros D D' nn As Us na; induction gs' as [| [] gs' IH]; intros [| [] gs] * H; cbn in *; try contradiction; try reflexivity;
    rewrite ?List.length_app, ?length_wrap_leaves_ctx, IH by exact H; try reflexivity.
  rewrite leaves_in_count_shift; lia.
Qed.

Lemma wrap_ihs_ctx_app : forall D D' nn As Us na gs1' gs1 gs2' gs2 gs0 r, cargs_kinds gs1' gs1 ->
    wrap_ihs_ctx D D' nn As Us na gs0 r (gs1' ++ gs2') (gs1 ++ gs2)
    = wrap_ihs_ctx D D' nn As Us na (gs0 ++ gs1) (cargs_nin D D' gs1' gs1 + r) gs2' gs2
        ++ wrap_ihs_ctx D D' nn As Us na gs0 r gs1' gs1.
Proof.
  intros D D' nn As Us na; induction gs1' as [| [A' | t'] gs1' IH]; intros [| [A | t] gs1] * Hk; cbn in Hk; try contradiction.
  - cbn; rewrite !List.app_nil_r; reflexivity.
  - cbn [List.app wrap_ihs_ctx cargs_nin]; rewrite IH by exact Hk; rewrite <- List.app_assoc; reflexivity.
  - cbn [List.app wrap_ihs_ctx cargs_nin]; rewrite IH by exact Hk; rewrite <- List.app_assoc; reflexivity.
  - cbn [List.app wrap_ihs_ctx cargs_nin]; rewrite IH by exact Hk.
    rewrite <- !List.app_assoc; cbn [List.app]; rewrite (leaves_in_count_shift D D' t' t); f_equal; f_equal; lia.
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Valid Blocks

    The conditions the eliminator's rules ask of its blocks [Bks] at the
    uniform parameters [Us], over [Γ], the motives of universe [i]: a block
    per member with one, each motive of its member's context, the branches
    named and of arity as the constructors, each branch of its type in its
    context. *)
Record valid_blocks (p : qname) (D : ind_decl) (Γ : ctx) (Us : list exp) (Bks : list eblock) (i : nat) : Prop :=
  mk_valid_blocks
  { (** A block per member with one *)
    valid_blocks_len : List.length Bks = ind_nblk D
    (** Each block binds as many variables as its member's motive *)
  ; valid_blocks_nm : blocks_nm_ok D Bks
    (** Each motive context is valid *)
  ; valid_blocks_mctx : forall j Mj, ind_member D j = Some Mj -> ⊨ elim_mctx p D j Mj Us ++ Γ
    (** Each motive is a valid type in its context *)
  ; valid_blocks_motive : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
      elim_mctx p D j Mj Us ++ Γ ⊨ eb_motive b : Typeω@i
    (** Each block has one branch per constructor, in order *)
  ; valid_blocks_names : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b)
    (** Each branch context is valid *)
  ; valid_blocks_bctx : forall j Mj c gs, ind_member D j = Some Mj -> ind_con Mj c = Some gs ->
      ⊨ elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ
    (** Each branch binds the parameters, the arguments and the recursive
        results *)
  ; valid_blocks_arity : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
      In (c, n, B) (eb_brs b) -> n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat
    (** Each branch is valid at its branch type *)
  ; valid_blocks_branch : forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> ind_con Mj c = Some gs ->
      In (c, n, B) (eb_brs b) ->
      elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ ⊨ B : elim_bty p D j Mj c gs (eb_motive b) Us }.

(** A block at each member with one. *)
Lemma valid_blocks_has : forall p D Γ Us Bks i, decl_typed gc_deps gc_stack D -> valid_blocks p D Γ Us Bks i ->
    forall j Mj, ind_member D j = Some Mj -> im_is_rview Mj = false -> exists b, List.nth_error Bks j = Some b.
Proof. intros * Hdt HBk; exact (block_of_nblk D Bks Hdt (valid_blocks_len _ _ _ _ _ _ HBk)). Qed.

(** Valid blocks moved by a substitution built from valid parts. *)
Lemma valid_blocks_gsub : forall p D Γ Us Bks i Ψ β, decl_closed D -> List.length Us = ind_nu D ->
    gsub Ψ β Γ -> valid_blocks p D Γ Us Bks i ->
    valid_blocks p D Ψ (List.map (fun U => U[β]) Us) (blocks_sub Bks β) i.
Proof.
  intros * Hc HUl Hβ [HBks HnmA HMall HAv HnaA HBc HarA HBv].
  assert (Hgm : forall k Mk, ind_member D k = Some Mk ->
             gsub (elim_mctx p D k Mk (List.map (fun U => U[β]) Us) ++ Ψ) (sb_qn (S (im_nn Mk)) β) (elim_mctx p D k Mk Us ++ Γ)).
  { intros * HMk.
    pose proof (gsub_qn _ _ _ _ Hβ (elim_mctx_ass p D k Mk Us Hc HMk) (HMall _ _ HMk)) as G.
    rewrite (elim_mctx_sub p D k Mk Us β Hc HMk HUl), length_elim_mctx in G; exact G. }
  assert (Hgb : forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
             gsub (elim_bctx p D Mk gs (blocks_motives (blocks_sub Bks β)) (List.map (fun U => U[β]) Us) ++ Ψ)
               (sb_qn (cargs_nrec D gs + List.length gs + im_nn Mk) β) (elim_bctx p D Mk gs (blocks_motives Bks) Us ++ Γ)).
  { intros * HMk Hcon.
    pose proof (gsub_qn _ _ _ _ Hβ (elim_bctx_ass p D k Mk gs (blocks_motives Bks) Us Hc HMk) (HBc _ _ _ _ HMk Hcon)) as G.
    rewrite (elim_bctx_sub p D k Mk c gs (blocks_motives Bks) (blocks_motives (blocks_sub Bks β)) Us β Hc HMk
               (cons_lookup_in _ _ _ Hcon) HUl (fun j0 Mj0 HMj0 => blocks_motives_sub D Bks β j0 Mj0 HnmA HMj0)),
      length_elim_bctx in G.
    exact G. }
  constructor.
  - rewrite length_blocks_sub; exact HBks.
  - apply blocks_nm_ok_sub; exact HnmA.
  - intros * HMk; exact (gsub_rel_ctx_wf _ _ _ (Hgm _ _ HMk)).
  - intros * HMk Hb1.
    destruct (nth_error_blocks_sub_inv _ _ _ _ Hb1) as (b2 & Hb2 & ->).
    rewrite eb_motive_sub, (HnmA _ _ _ HMk Hb2).
    pose proof (rel_exp_under_ctx_gsub (Hgm _ _ HMk) (HAv _ _ _ HMk Hb2)) as H; cbn [exp_sub] in H; exact H.
  - intros * HMk Hb1; destruct (nth_error_blocks_sub_inv _ _ _ _ Hb1) as (b2 & Hb2 & ->).
    rewrite eb_brs_sub; apply brs_names_sub; exact (HnaA _ _ _ HMk Hb2).
  - intros * HMk Hcon; exact (gsub_rel_ctx_wf _ _ _ (Hgb _ _ _ _ HMk Hcon)).
  - intros * HMk Hb1 Hcon Hin; destruct (nth_error_blocks_sub_inv _ _ _ _ Hb1) as (b2 & Hb2 & ->).
    rewrite eb_brs_sub in Hin; destruct (brs_in_sub _ _ _ _ _ Hin) as [B0 Hin0]; exact (HarA _ _ _ _ _ _ _ HMk Hb2 Hcon Hin0).
  - intros * HMk Hb1 Hcon Hin.
    destruct (nth_error_blocks_sub_inv _ _ _ _ Hb1) as (b2 & Hb2 & ->).
    rewrite eb_brs_sub in Hin.
    apply List.in_map_iff in Hin as ([[c0 n0] B0] & Hw & Hin0); cbn in Hw; injection Hw as <- <- <-.
    pose proof (HarA _ _ _ _ _ _ _ HMk Hb2 Hcon Hin0) as Hn0.
    pose proof (rel_exp_under_ctx_gsub (Hgb _ _ _ _ HMk Hcon) (HBv _ _ _ _ _ _ _ HMk Hb2 Hcon Hin0)) as H.
    replace (cargs_nrec D gs + List.length gs + im_nn Mj) with (im_nn Mj + List.length gs + cargs_nrec D gs) in H by lia.
    rewrite (elim_bty_sub p D j Mj c0 gs _ Us β Hc HMk HUl) in H.
    rewrite eb_motive_sub, (HnmA _ _ _ HMk Hb2), Hn0; exact H.
Qed.

(** ** Substitutions of the Wrapped Branch's Context *)

Lemma cargs_sub_cong : forall gs σ σ' As, sb_eq σ σ' -> sb_eq (cargs_sub σ gs As) (cargs_sub σ' gs As).
Proof.
  induction gs as [| [] gs IH]; intros σ σ' [| N As] H; cbn; try exact H; apply IH; [ apply sb_extend_cong, H | exact H ].
Qed.

Lemma cargs_sub_compose : forall gs σ As τ,
    sb_eq (cargs_sub σ gs As ⨟ τ) (cargs_sub (σ ⨟ τ) gs (List.map (fun M => M[τ]) As)).
Proof.
  induction gs as [| [] gs IH]; intros σ [| N As] τ; cbn [cargs_sub List.map]; try reflexivity.
  - rewrite IH; apply cargs_sub_cong, sb_extend_compose.
  - apply IH.
Qed.

(** Below the non-recursive arguments and [m] more variables, an instance
    after the arguments depends on its base below [m] only. *)
Lemma cargs_sub_lt_base : forall gs σ σ' As m, List.length gs <= List.length As ->
    (forall z, z < m -> σ z = σ' z) ->
    forall y, y < List.length (cargs_nonrec gs) + m -> cargs_sub σ gs As y = cargs_sub σ' gs As y.
Proof.
  induction gs as [| [B | t] gs IH]; intros σ σ' [| N As] m Hl Hσ y Hy; cbn in *; try lia; try exact (Hσ y Hy).
  - apply (IH _ _ _ (S m)); [ lia | | lia ].
    intros [| z] Hz; cbn; [ reflexivity | apply Hσ; lia ].
  - apply (IH _ _ _ m); [ lia | exact Hσ | exact Hy ].
Qed.

(** The instance at a stage of [r] recursive results the container has:
    the non-uniform parameters and the arguments as variables, followed by
    the group's recursive results so far [L]. *)
Definition wrap_inst (nn na r : nat) (L : list exp) : sub :=
  sb_of_list (sb_of_wk (wk_shiftn (r + na + nn))) (vars_from (r + na) nn ++ vars_from r na ++ L).

Lemma wrap_inst_shift : forall nn na r L, sb_eq (sb_of_wk (wk_shiftn (List.length L + na + nn)) ⨟ wrap_inst nn na r L)
    (sb_of_wk (wk_shiftn (r + na + nn))).
Proof.
  intros * x; unfold wrap_inst; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn].
  replace (x + (List.length L + na + nn)) with (List.length (vars_from (r + na) nn ++ vars_from r na ++ L) + x)
    by (rewrite !List.length_app, !length_vars_from; lia).
  rewrite sb_of_list_ge; reflexivity.
Qed.

Lemma wrap_inst_ihs_sub : forall nn Us na r (gs1 : list carg) L, List.length gs1 <= na ->
    sb_eq (ihs_sub nn Us na (cargs_pat gs1) (List.length L) ⨟ wrap_inst nn na r L)
          (cargs_sub (wrap_base Us nn na r) gs1 (vars_from r na)).
Proof.
  intros * Hg; unfold wrap_inst, wrap_base.
  apply ihs_sub_view; [ apply length_vars_from | apply length_vars_from | exact Hg ].
Qed.

Lemma wrap_inst_arg : forall nn na r L x, x < na -> (a_var (List.length L + x))[wrap_inst nn na r L] = a_var (r + x).
Proof.
  intros * Hx; unfold wrap_inst; change (exp_sub (a_var ?y) ?s) with (sentry_exp (s y)).
  rewrite List.app_assoc, sb_of_list_app, sb_of_list_ge, sb_of_list_app.
  rewrite sb_of_list_vars by exact Hx; reflexivity.
Qed.

(** The group's recursive result along a leaf path of an argument, in the
    wrapped branch's context. *)
Lemma wrap_ihty_eq : forall As nn Us na r (gs1 : list carg) l L, List.length gs1 < na ->
    (leaf_ihty As (sb_of_wk (wk_shiftn (List.length L + na + nn))) (ihs_sub nn Us na (cargs_pat gs1) (List.length L))
       (a_var (List.length L + na - 1 - List.length (cargs_pat gs1))) l)[wrap_inst nn na r L]
    = leaf_ihty As (sb_of_wk (wk_shiftn (r + na + nn))) (cargs_sub (wrap_base Us nn na r) gs1 (vars_from r na))
        (a_var (r + (na - 1 - List.length gs1))) l.
Proof.
  intros * Hlt.
  rewrite leaf_ihty_sub, length_cargs_pat.
  replace (List.length L + na - 1 - List.length gs1) with (List.length L + (na - 1 - List.length gs1)) by lia.
  rewrite wrap_inst_arg by lia.
  apply leaf_ihty_sb_eq; [ apply wrap_inst_shift | apply wrap_inst_ihs_sub; lia ].
Qed.

(** The parameters' instance at a later stage, [k] more recursive
    results. *)
Lemma wrap_base_shift : forall Us nn na r k,
    sb_eq (wrap_base Us nn na r ⨟ sb_of_wk (wk_shiftn k)) (wrap_base Us nn na (r + k)).
Proof.
  intros; unfold wrap_base; rewrite sb_of_list_compose_gen.
  rewrite List.map_app, List.map_map, (map_sub_of_wk (vars_from (r + na) nn)), vars_from_wk_shiftn.
  replace (r + na + k) with (r + k + na) by lia.
  replace (List.map (fun x => x[wk_shiftn (r + na + nn)]ʷ[ι wk_shiftn k]) Us) with (List.map (fun U => U[wk_shiftn (r + k + na + nn)]ʷ) Us).
  - apply sb_of_list_cong; intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn]; f_equal; lia.
  - apply List.map_ext; intros U; rewrite exp_sub_of_wk, exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; lia.
Qed.

Lemma wrap_cargs_shift : forall Us nn na r k (gs1 : list carg),
    sb_eq (cargs_sub (wrap_base Us nn na r) gs1 (vars_from r na) ⨟ sb_of_wk (wk_shiftn k))
          (cargs_sub (wrap_base Us nn na (r + k)) gs1 (vars_from (r + k) na)).
Proof.
  intros; rewrite cargs_sub_compose, map_sub_of_wk, vars_from_wk_shiftn.
  apply cargs_sub_cong, wrap_base_shift.
Qed.

(** The same type at a later stage, [k] more recursive results. *)
Lemma wrap_ihty_shift : forall As nn Us na r k (gs1 : list carg) l,
    (leaf_ihty As (sb_of_wk (wk_shiftn (r + na + nn))) (cargs_sub (wrap_base Us nn na r) gs1 (vars_from r na))
       (a_var (r + (na - 1 - List.length gs1))) l)[wk_shiftn k]ʷ
    = leaf_ihty As (sb_of_wk (wk_shiftn (r + k + na + nn))) (cargs_sub (wrap_base Us nn na (r + k)) gs1 (vars_from (r + k) na))
        (a_var (r + k + (na - 1 - List.length gs1))) l.
Proof.
  intros; rewrite <- exp_sub_of_wk, leaf_ihty_sub.
  replace ((a_var (r + (na - 1 - List.length gs1)))[ι wk_shiftn k]) with (a_var (r + k + (na - 1 - List.length gs1)))
    by (cbn; f_equal; unfold wk_shiftn; lia).
  apply leaf_ihty_sb_eq; [| apply wrap_cargs_shift ].
  intros x; cbn [sb_compose sb_of_wk sentry_sub wk_shiftn]; f_equal; unfold wk_shiftn; lia.
Qed.

(** ** A Wrapped Branch

    The view's member [v] ([Mv]), with a block, a constructor [c] of it,
    its arguments [gs] as the group has them and [gs'] as the container
    does, the container's group [D'], the group's blocks [Bks] valid at the
    uniform parameters [Us] over [Γ]. *)
Section WrapBranch.
  #[local] Set Default Proof Using "All".
  Variable (VP : qname -> ind_decl -> Prop) (p : qname) (D : ind_decl).
  Hypotheses (HP : valid_groups VP) (HPD : VP p D).
  Let Hvg := valid_groups_valid VP HP p D HPD.
  Let Hcv := containers_valid_of_groups VP HP p D HPD.
  Let HD := valid_group_valid _ _ Hvg.
  Let Hc := valid_group_closed _ _ Hvg.
  Let Hl := valid_group_lookup _ _ Hvg.
  Let Hdt := valid_group_typed _ _ Hvg.
  Let Ua : tele_ass (ind_uparams D) := uparams_ass D Hc.

  Variable (Γ : ctx) (Us : list exp) (Bks : list eblock) (i : nat).
  Hypotheses (HΓ : ⊨ Γ) (HUl : List.length Us = ind_nu D)
    (HUs : forall k U T, List.nth_error Us k = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) k = Some T -> Γ ⊨ U : T)
    (HBk : valid_blocks p D Γ Us Bks i).
  Variable (D' : ind_decl) (v : nat) (Mv : imember) (c : String.string) (gs' gs : list carg).
  Hypotheses (HMv : ind_member D v = Some Mv) (HrvMv : im_is_rview Mv = false) (Hcon : ind_con Mv c = Some gs)
    (Hk : cargs_kinds gs' gs).
  Let As := blocks_motives Bks.
  Let nn := im_nn Mv.
  Let na := List.length gs.
  Let τU := sb_of_list Id Us.
  Let Cs := tele_sub (cargs_ctx p D Mv gs) (sb_qn nn τU).
  Let Ns := tele_sub (im_nparams Mv) τU.
  Let Ψc := Cs ++ Ns ++ Γ.

  Lemma w_Hin : List.In (c, gs) (im_cons Mv).
  Proof. exact (cons_lookup_in _ _ _ Hcon). Qed.

  Lemma w_HΨc : ⊨ Ψc.
  Proof.
    pose proof (valid_blocks_bctx _ _ _ _ _ _ HBk _ _ _ _ HMv Hcon) as H; unfold elim_bctx in H; fold τU nn Cs Ns As in H.
    rewrite <- !List.app_assoc in H; exact (rel_ctx_wf_app_r _ _ H).
  Qed.

  Lemma w_LCs : List.length Cs = na.
  Proof. unfold Cs; rewrite length_tele_sub, length_cargs_ctx; reflexivity. Qed.

  Lemma w_LNs : List.length Ns = nn.
  Proof. unfold Ns; rewrite length_tele_sub, length_im_nparams; reflexivity. Qed.

  (** At a context [E ++ Ψc]: the weakening to [Γ], the uniform
      parameters weakened, the non-uniform parameters and the arguments as
      variables, each of its type. *)
  Section At.
    Variable (E : ctx).
    Hypothesis (HE : ⊨ E ++ Ψc).
    Let n := List.length E + na + nn.
    Let Uw := List.map (fun U => U[wk_shiftn n]ʷ) Us.
    Let Nw := vars_from (List.length E + na) nn.
    Let Aw := vars_from (List.length E) na.

    Lemma w_wk : E ++ Ψc ⊨ʷ (wk_shiftn n) : Γ.
    Proof.
      replace n with (List.length (E ++ Cs ++ Ns)) by (rewrite !List.length_app, w_LCs, w_LNs; unfold n; lia).
      replace (E ++ Ψc) with ((E ++ Cs ++ Ns) ++ Γ) in HE |- * by (unfold Ψc; rewrite <- !List.app_assoc; reflexivity).
      apply rel_wk_under_ctx_shiftn; exact HE.
    Qed.

    Lemma w_us : forall j U T0, List.nth_error Uw j = Some U ->
        List.nth_error (tele_insts (ind_uparams D) Id Uw) j = Some T0 -> E ++ Ψc ⊨ U : T0.
    Proof.
      intros j U' T' HU HT; unfold Uw in *.
      rewrite <- tele_insts_closed_wk in HT by (first [ exact Ua | exact (decl_uparams_closed D Hc) ]).
      apply nth_error_map_inv in HU as (U & HU & ->); apply nth_error_map_inv in HT as (T0 & HT & ->).
      exact (rel_exp_under_ctx_wk w_wk (HUs _ _ _ HU HT)).
    Qed.

    Lemma w_nvars : forall τ, (forall y, y < ind_nu D -> sentry_exp (τ y) = (sentry_exp (τU y))[wk_shiftn n]ʷ) ->
        forall j N T0, List.nth_error Nw j = Some N -> List.nth_error (tele_insts (im_nparams Mv) τ Nw) j = Some T0 ->
          E ++ Ψc ⊨ N : T0.
    Proof.
      intros τ Hτ j N T0 HN HT.
      unfold Nw in HN, HT.
      replace (vars_from (List.length E + na) nn) with (vars_from (List.length (E ++ Cs)) (List.length (im_nparams Mv))) in HN, HT
        by (rewrite List.length_app, w_LCs, length_im_nparams; reflexivity).
      destruct (vars_tele_lookup (E ++ Cs) (im_nparams Mv) τU τ Γ (ind_nu D)
                  (decl_closed_nparams_ass D Hc _ _ HMv) (decl_nparams_mvc _ _ _ Hdt _ _ HMv) (decl_closed_nparams_scoped D Hc _ _ HMv)
                  ltac:(intros y Hy; rewrite Hτ by exact Hy; rewrite List.length_app, w_LCs, length_im_nparams; unfold n;
                        f_equal; f_equal; lia)
                  _ _ _ HN HT) as (x & -> & Hx).
      fold Ns in Hx; rewrite <- List.app_assoc in Hx.
      apply valid_exp_under_ctx_vlookup; [ exact Hx | exact HE ].
    Qed.

    Lemma w_avars_gen : forall τ,
        (forall y, y < im_np D Mv -> sentry_exp (τ y) = (sentry_exp (sb_qn nn τU y))[wk_shiftn (List.length E + na)]ʷ) ->
        forall j N T0, List.nth_error Aw j = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mv gs) τ Aw) j = Some T0 -> E ++ Ψc ⊨ N : T0.
    Proof.
      intros τ Hτ j N T0 HN HT.
      unfold Aw in HN, HT.
      replace (vars_from (List.length E) na) with (vars_from (List.length E) (List.length (cargs_ctx p D Mv gs))) in HN, HT
        by (rewrite length_cargs_ctx; reflexivity).
      destruct (vars_tele_lookup E (cargs_ctx p D Mv gs) (sb_qn nn τU) τ (Ns ++ Γ) (im_np D Mv)
                  (cargs_ctx_aux_ass _ _ _ _ _) (cargs_ctx_mvc _ _ _ _ _ _ _ _ Hdt Hc HMv w_Hin)
                  (decl_closed_cargs_scoped D Hc _ _ _ _ _ HMv w_Hin)) with (k := j) (N := N) (T := T0)
        as (x & -> & Hx).
      - intros y Hy; rewrite length_cargs_ctx; exact (Hτ y Hy).
      - exact HN.
      - exact HT.
      - apply valid_exp_under_ctx_vlookup; [ exact Hx | exact HE ].
    Qed.

    Lemma w_avars_cond : forall y, y < im_np D Mv ->
        sentry_exp (sb_of_list Id (Uw ++ Nw) y) = (sentry_exp (sb_qn nn τU y))[wk_shiftn (List.length E + na)]ʷ.
    Proof.
      intros y Hy.
      destruct (Nat.lt_ge_cases y nn) as [Hy1 | Hy1].
      - unfold Nw; rewrite sb_of_list_app, sb_of_list_vars by lia; rewrite sb_qn_lt by exact Hy1; cbn; f_equal; lia.
      - replace y with (List.length Nw + (y - nn)) at 1 by (unfold Nw; rewrite length_vars_from; lia).
        rewrite sb_of_list_app, sb_of_list_ge; unfold Uw; rewrite sb_of_list_map by (rewrite HUl; unfold im_np, nn in *; lia).
        rewrite sb_qn_ge by exact Hy1; rewrite <- sentry_exp_wk, exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; unfold n; lia.
    Qed.

    Lemma w_avars : forall j N T0, List.nth_error Aw j = Some N ->
        List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id (Uw ++ Nw)) Aw) j = Some T0 -> E ++ Ψc ⊨ N : T0.
    Proof. exact (w_avars_gen _ w_avars_cond). Qed.

    (** The parameters and the arguments as variables: an instance of
        [Ψc]. *)
    Lemma w_base : gsub (E ++ Ψc) (wrap_inst nn na (List.length E) nil) Ψc.
    Proof.
      assert (HΔa : tele_ass (tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU))
        by (apply tele_ass_sub, List.Forall_app; split; [ apply cargs_ctx_aux_ass | exact (decl_closed_nparams_ass D Hc _ _ HMv) ]).
      assert (EΨ : Ψc = tele_sub (cargs_ctx p D Mv gs ++ im_nparams Mv) τU ++ Γ)
        by (unfold Ψc, Cs, Ns; rewrite tele_sub_app, length_im_nparams, List.app_assoc; reflexivity).
      unfold wrap_inst; rewrite List.app_nil_r; fold Nw Aw; replace (List.length E + na + nn) with n by reflexivity.
      rewrite EΨ at 2.
      apply gsub_of_list; [ exact (gsub_wk _ _ _ w_wk HE HΓ) | exact HΔa | rewrite <- EΨ; exact w_HΨc
                          | rewrite List.length_app, length_tele_sub, List.length_app, length_cargs_ctx, length_im_nparams;
                            unfold Nw, Aw; rewrite !length_vars_from; unfold na, nn; lia |].
      intros j N T0 HN HT.
      rewrite tele_insts_tele_sub, tele_insts_app in HT
        by first [ exact (decl_closed_nparams_ass D Hc _ _ HMv) | unfold Nw; rewrite length_vars_from, length_im_nparams; reflexivity ].
      assert (Hl2 : List.length (tele_insts (im_nparams Mv) (τU ⨟ sb_of_wk (wk_shiftn n)) Nw) = nn)
        by (rewrite length_tele_insts by exact (decl_closed_nparams_ass D Hc _ _ HMv); unfold Nw; rewrite length_vars_from;
            unfold nn, im_nn; lia).
      destruct (Nat.lt_ge_cases j nn) as [Hj | Hj].
      - rewrite List.nth_error_app1 in HN by (unfold Nw; rewrite length_vars_from; lia).
        rewrite List.nth_error_app1 in HT by lia.
        refine (w_nvars (τU ⨟ sb_of_wk (wk_shiftn n)) _ j N T0 HN HT).
        intros y Hy; cbn [sb_compose]; rewrite <- sentry_exp_sub, exp_sub_of_wk; reflexivity.
      - rewrite List.nth_error_app2 in HN by (unfold Nw; rewrite length_vars_from; lia).
        rewrite List.nth_error_app2 in HT by lia.
        unfold Nw in HN; rewrite length_vars_from in HN; rewrite Hl2 in HT.
        refine (w_avars_gen (sb_of_list (τU ⨟ sb_of_wk (wk_shiftn n)) Nw) _ _ N T0 HN HT).
        intros y Hy.
        destruct (Nat.lt_ge_cases y nn) as [Hy1 | Hy1].
        + unfold Nw; rewrite sb_of_list_vars by lia; rewrite sb_qn_lt by exact Hy1; cbn; f_equal; lia.
        + replace y with (List.length Nw + (y - nn)) at 1 by (unfold Nw; rewrite length_vars_from; lia).
          rewrite sb_of_list_ge, sb_qn_ge by exact Hy1; cbn [sb_compose].
          rewrite <- sentry_exp_sub, <- sentry_exp_wk, exp_sub_of_wk, exp_wk_wk; apply exp_wk_wk_eq; intros z; cbn; unfold n; lia.
    Qed.

    (** The group's recursive result along a leaf path of a recursive
        argument after [gs1], as an elimination at the argument's
        variable ([elim_ihs]). *)
    Lemma w_ih_leaf : forall gs1 t gs2 l, gs = gs1 ++ ca_rec t :: gs2 ->
        In l (shape_leaves (rv_leaves D) (pat_nargs (cargs_pat gs1) + nn) t) ->
        E ++ Ψc ⊨ leaf_ih p D (Some p) Uw (blocks_wk Bks (wk_shiftn n)) (cargs_sub (wrap_base Us nn na (List.length E)) gs1 Aw)
                    (a_var (List.length E + (na - 1 - List.length gs1))) l
          : leaf_ihty As (sb_of_wk (wk_shiftn n)) (cargs_sub (wrap_base Us nn na (List.length E)) gs1 Aw)
              (a_var (List.length E + (na - 1 - List.length gs1))) l.
    Proof.
      intros * Heq Hinl.
      assert (Hlt : List.length gs1 < na) by (unfold na; rewrite Heq, List.length_app; cbn; lia).
      assert (LUw : List.length Uw = ind_nu D) by (unfold Uw; rewrite List.length_map; exact HUl).
      set (Ps := Uw ++ Nw).
      assert (HPl : List.length Ps = im_np D Mv) by (unfold Ps; rewrite List.length_app, LUw; unfold Nw; rewrite length_vars_from; unfold im_np, nn; lia).
      assert (HfP : List.firstn (ind_nu D) Ps = Uw) by (unfold Ps; rewrite <- LUw; apply firstn_app_len; reflexivity).
      pose proof (valid_blocks_gsub p D Γ Us Bks i (E ++ Ψc) (sb_of_wk (wk_shiftn n)) Hc HUl (gsub_wk _ _ _ w_wk HE HΓ) HBk) as HBk'.
      rewrite map_sub_of_wk, blocks_sub_of_wk in HBk'; fold Uw in HBk'; rewrite <- HfP in HBk'.
      destruct HBk' as [HBks' HnmA' HMall' HAv' HnaA' HBc' HarA' HBv'].
      destruct (valid_blocks_has _ _ _ _ _ _ Hdt HBk _ _ HMv HrvMv) as [b Hb].
      assert (Hb' : List.nth_error (blocks_wk Bks (wk_shiftn n)) v = Some (eblock_sub b (sb_of_wk (wk_shiftn n)))).
      { rewrite <- blocks_sub_of_wk, nth_error_blocks_sub, Hb; reflexivity. }
      assert (HPs : forall k P T, List.nth_error Ps k = Some P -> List.nth_error (tele_insts (im_params D Mv) Id Ps) k = Some T ->
                 E ++ Ψc ⊨ P : T).
      { intros k P T HP0 HT; unfold Ps in HP0, HT.
        refine (params_valid_join D v Mv (E ++ Ψc) Uw Nw Hc HMv LUw w_us _ k P T HP0 HT).
        intros j N T0 HN HT0; refine (w_nvars (sb_of_list Id Uw) _ j N T0 HN HT0).
        intros y Hy; unfold Uw; rewrite sb_of_list_map by lia; reflexivity. }
      assert (HAs : forall k N T, List.nth_error Aw k = Some N ->
                 List.nth_error (tele_insts (cargs_ctx p D Mv gs) (sb_of_list Id Ps) Aw) k = Some T -> E ++ Ψc ⊨ N : T)
        by exact w_avars.
      assert (HUs' : forall k U T, List.nth_error (List.firstn (ind_nu D) Ps) k = Some U ->
                 List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) k = Some T -> E ++ Ψc ⊨ U : T)
        by (rewrite HfP; exact w_us).
      assert (HUl' : List.length (List.firstn (ind_nu D) Ps) = ind_nu D) by (rewrite HfP; exact LUw).
      destruct (length_rec_ps D HD v Mv HMv c gs gs1 t gs2 Hcon Heq) as (Mj & HMj & HPj).
      pose proof (iota_frame VP p D HP HPD (E ++ Ψc) (Some p) v Mv _ (blocks_wk Bks (wk_shiftn n)) c gs Ps Aw i HE
                    (or_introl eq_refl) HMv Hb' Hcon HPl HPs ltac:(unfold Aw; rewrite length_vars_from; reflexivity) HAs
                    HBks' HnmA' HMall' HAv' HnaA' HBc' HarA' HBv' gs1 t gs2 Heq) as Hf.
      assert (Hinl' : In l (shape_leaves (rv_leaves D) (im_nn Mv + List.length (cargs_nonrec gs1) + 0) (ptyp_skip 0 t))).
      { replace (im_nn Mv + List.length (cargs_nonrec gs1) + 0) with (pat_nargs (cargs_pat gs1) + nn)
          by (rewrite pat_nargs_cargs_pat, cargs_strat_nonrec, List.length_rev, List.length_map; unfold nn; lia).
        exact Hinl. }
      pose proof (leaf_ih_valid VP p D HP HPD (E ++ Ψc) (Some p) (List.firstn (ind_nu D) Ps) (blocks_wk Bks (wk_shiftn n)) i HE
                    (or_introl eq_refl) HUl' HUs' HBks' HnmA' HMall' HAv' HnaA' HBc' HarA' HBv'
                    (S (ptyp_mem t)) v Mv c gs gs1 t gs2 HMv Hcon Heq Mj HMj (fun _ => Nat.lt_succ_diag_r _)
                    _ _ _ _ Hf 0 l (Nat.le_0_l _) Hinl') as H.
      cbn [List.firstn doms_ctx List.map List.rev tele_sub List.app sb_shift_iter sb_qn apps_vars_iter] in H.
      rewrite (List.map_ext _ (fun U => U) exp_sub_id), List.map_id, blocks_sub_id, HfP in H.
      assert (Ex : List.nth (List.length gs1) Aw (a_var 0) = a_var (List.length E + (na - 1 - List.length gs1))).
      { unfold Aw; replace (List.length gs1) with (na - 1 - (na - 1 - List.length gs1)) at 1 by lia; apply vars_from_nth; lia. }
      rewrite Ex in H.
      (** The instance of the parameters, at a base agreeing below them. *)
      assert (Hst : ptyp_scoped (List.length (cargs_nonrec gs1) + im_np D Mv) t).
      { pose proof (member_closed_recs _ _ (decl_closed_members _ Hc _ _ HMv) _ _ _ _ _ w_Hin Heq) as Hs.
        rewrite cargs_strat_nonrec, List.length_rev, List.length_map in Hs; exact Hs. }
      assert (Hsl : leaf_scoped (List.length (cargs_nonrec gs1) + im_np D Mv) l).
      { assert (Hst' : ptyp_scoped (pat_nargs (cargs_pat gs1) + nn + ind_nu D) t)
          by (replace (pat_nargs (cargs_pat gs1) + nn + ind_nu D) with (List.length (cargs_nonrec gs1) + im_np D Mv)
                by (rewrite pat_nargs_cargs_pat, cargs_strat_nonrec, List.length_rev, List.length_map; unfold im_np, nn; lia);
              exact Hst).
        pose proof (shape_leaves_scoped (rv_leaves D) (ind_nu D) t (pat_nargs (cargs_pat gs1) + nn) (rv_leaves_scoped D Hc) Hst') as HF.
        rewrite List.Forall_forall in HF; specialize (HF l Hinl).
        replace (List.length (cargs_nonrec gs1) + im_np D Mv) with (pat_nargs (cargs_pat gs1) + nn + ind_nu D)
          by (rewrite pat_nargs_cargs_pat, cargs_strat_nonrec, List.length_rev, List.length_map; unfold im_np, nn; lia).
        exact HF. }
      assert (Hag : forall y, y < List.length (cargs_nonrec gs1) + im_np D Mv ->
                 cargs_sub (sb_of_list Id Ps) gs1 Aw y = cargs_sub (wrap_base Us nn na (List.length E)) gs1 Aw y).
      { apply cargs_sub_lt_base; [ unfold Aw; rewrite length_vars_from; lia |].
        intros z Hz; unfold wrap_base; fold n; fold Uw Nw Ps; apply sb_of_list_lt_base; lia. }
      rewrite (leaf_ih_agree _ _ _ l _ _ _ _ _ _ Hsl Hag) in H.
      rewrite (leaf_ihty_sb_agree l _ _ _ _ _ _ Hsl Hag) in H.
      replace (leaf_ihty As (sb_of_wk (wk_shiftn n)) (cargs_sub (wrap_base Us nn na (List.length E)) gs1 Aw)
                 (a_var (List.length E + (na - 1 - List.length gs1))) l)
        with (leaf_ihty (blocks_motives (blocks_wk Bks (wk_shiftn n))) Id (cargs_sub (wrap_base Us nn na (List.length E)) gs1 Aw)
                (a_var (List.length E + (na - 1 - List.length gs1))) l); [ exact H |].
      pose proof (cargs_leaves_plen D v Mv c gs gs1 t gs2 (pat_nargs (cargs_pat gs1) + nn) Hc HMv w_Hin Heq) as HPL.
      rewrite List.Forall_forall in HPL; destruct (HPL l Hinl) as (Mq & HMq & Hlq).
      rewrite <- (leaf_ihty_base l As _ (sb_of_wk (wk_shiftn n)) Id).
      - apply leaf_ihty_sb_eq; [ apply sb_compose_id_right | reflexivity ].
      - rewrite <- blocks_sub_of_wk, Hlq; exact (blocks_motives_sub D Bks _ _ _ (valid_blocks_nm _ _ _ _ _ _ HBk) HMq).
    Qed.
  End At.

  Lemma w_len : List.length gs' = na.
  Proof. unfold na; exact (cargs_kinds_length _ _ Hk). Qed.

  Lemma w_kinds_split : forall G1' G2' G1 G2, gs' = G1' ++ G2' -> gs = G1 ++ G2 -> List.length G1' = List.length G1 ->
      cargs_kinds G1' G1 /\ cargs_kinds G2' G2.
  Proof. intros * E1 E2 Hlg; pose proof Hk as Hk0; rewrite E1, E2 in Hk0; exact (cargs_kinds_app_inv _ _ _ _ Hlg Hk0). Qed.

  (** *** The Wrapped Branch's Context Is Valid

      Each entry, at a leaf path the container has, is the type of the
      group's recursive result along it at the argument's variable
      ([w_ih_leaf]). *)
  Lemma w_valid_leaves : forall G1' t' G2' G1 t G2, gs' = G1' ++ ca_rec t' :: G2' -> gs = G1 ++ ca_rec t :: G2 ->
      List.length G1' = List.length G1 ->
      ⊨ wrap_ihs_ctx D D' nn As Us na nil 0 G1' G1 ++ Ψc ->
      forall ls1 ls2, shape_leaves (rv_leaves D) (pat_nargs (cargs_pat G1) + nn) t = ls1 ++ ls2 ->
      ⊨ wrap_leaves_ctx D' t' nn As Us na G1 (cargs_nin D D' G1' G1 + 0) ls1 ++ wrap_ihs_ctx D D' nn As Us na nil 0 G1' G1 ++ Ψc.
  Proof.
    intros * HG' HG Hlg HW ls1.
    destruct (w_kinds_split _ _ _ _ HG' HG Hlg) as [Hk1 _].
    induction ls1 as [| l ls1 IH] using List.rev_ind; intros ls2 Els; [ exact HW |].
    specialize (IH (l :: ls2) ltac:(rewrite Els, <- List.app_assoc; reflexivity)).
    rewrite wrap_leaves_ctx_app; cbn [wrap_leaves_ctx].
    destruct (leaf_in D' t' l) eqn:Hli; cbn [List.app]; [| exact IH ].
    set (Ec := wrap_leaves_ctx D' t' nn As Us na G1 (cargs_nin D D' G1' G1 + 0) ls1 ++ wrap_ihs_ctx D D' nn As Us na nil 0 G1' G1) in *.
    assert (HE : ⊨ Ec ++ Ψc) by (unfold Ec; rewrite <- List.app_assoc; exact IH).
    assert (LE : List.length Ec = leaves_in_count D' t' ls1 + (cargs_nin D D' G1' G1 + 0))
      by (unfold Ec; rewrite List.length_app, length_wrap_leaves_ctx, length_wrap_ihs_ctx by exact Hk1; lia).
    assert (Hinl : In l (shape_leaves (rv_leaves D) (pat_nargs (cargs_pat G1) + nn) t))
      by (rewrite Els; apply List.in_or_app; left; apply List.in_or_app; right; left; reflexivity).
    pose proof (w_ih_leaf Ec HE G1 t G2 l HG Hinl) as H.
    destruct (presup_rel_exp_under_ctx H) as [j HT].
    rewrite LE in HT.
    rewrite List.app_assoc; fold Ec.
    exact (rel_ctx_wf_extend HE HT).
  Qed.

  Lemma w_valid : forall G1' G2' G1 G2, gs' = G1' ++ G2' -> gs = G1 ++ G2 -> List.length G1' = List.length G1 ->
      ⊨ wrap_ihs_ctx D D' nn As Us na nil 0 G1' G1 ++ Ψc.
  Proof.
    induction G1' as [| g' G1' IH] using List.rev_ind; intros G2' G1 G2 HG' HG HGl.
    - destruct G1; [| discriminate ]; cbn; exact w_HΨc.
    - destruct (List.exists_last (l := G1) ltac:(intros ->; rewrite List.length_app in HGl; cbn in HGl; lia)) as (G1x & g & ->).
      rewrite !List.length_app in HGl; cbn in HGl.
      assert (HG'' : gs' = G1' ++ g' :: G2') by (rewrite HG', <- List.app_assoc; reflexivity).
      assert (HG0 : gs = G1x ++ g :: G2) by (rewrite HG, <- List.app_assoc; reflexivity).
      assert (HGl' : List.length G1' = List.length G1x) by lia.
      pose proof (IH _ _ _ HG'' HG0 HGl') as HE.
      destruct (w_kinds_split _ _ _ _ HG'' HG0 HGl') as [Hk1 Hkg].
      rewrite wrap_ihs_ctx_app by exact Hk1; cbn [List.app].
      destruct g' as [A' | t'], g as [A | t]; cbn in Hkg; try contradiction; cbn [wrap_ihs_ctx List.app]; try exact HE.
      rewrite <- List.app_assoc.
      exact (w_valid_leaves G1' t' G2' G1x t G2 HG'' HG0 HGl' HE _ nil ltac:(rewrite List.app_nil_r; reflexivity)).
  Qed.

  Lemma w_ctx_eq : wrap_bctx p D D' Mv gs' gs As Us ++ Γ = wrap_ihs_ctx D D' nn As Us na nil 0 gs' gs ++ Ψc.
  Proof. unfold wrap_bctx, Ψc, Cs, Ns; rewrite <- !List.app_assoc; reflexivity. Qed.

  (** The context of a wrapped branch is valid ([vb_ctx]). *)
  Theorem valid_wrap_bctx : ⊨ wrap_bctx p D D' Mv gs' gs As Us ++ Γ.
  Proof.
    rewrite w_ctx_eq.
    exact (w_valid gs' nil gs nil ltac:(rewrite List.app_nil_r; reflexivity) ltac:(rewrite List.app_nil_r; reflexivity) w_len).
  Qed.

  (** *** The Instance of the Group's Branch's Context

      In the whole wrapped branch's context [Ew ++ Ψc], whose recursive
      results are as many as the container's ([Hcnt]). *)
  Section Full.
    Let Ew := wrap_ihs_ctx D D' nn As Us na nil 0 gs' gs.
    Let R := List.length Ew.
    Let n := R + na + nn.
    Let Uw := List.map (fun U => U[wk_shiftn n]ʷ) Us.
    Let Bw := blocks_wk Bks (wk_shiftn n).
    Let Aw := vars_from R na.
    Let σw := wrap_base Us nn na R.

    Lemma f_HE : ⊨ Ew ++ Ψc.
    Proof. pose proof valid_wrap_bctx as H; rewrite w_ctx_eq in H; exact H. Qed.

    Lemma f_R : R = cargs_nin D D' gs' gs.
    Proof. unfold R, Ew; apply length_wrap_ihs_ctx; exact Hk. Qed.

    Lemma f_avar : forall gs1 g rest, gs = gs1 ++ g :: rest ->
        List.skipn (List.length gs1) Aw = a_var (R + (na - 1 - List.length gs1)) :: List.skipn (S (List.length gs1)) Aw.
    Proof.
      intros * Heq.
      assert (Hlt : List.length gs1 < na) by (unfold na; rewrite Heq, List.length_app; cbn; lia).
      apply skipn_nth_cons.
      assert (Ei : List.length gs1 = na - 1 - (na - 1 - List.length gs1)) by lia.
      rewrite Ei at 1; unfold Aw.
      rewrite (List.nth_error_nth' _ (a_var 0)) by (rewrite length_vars_from; lia).
      rewrite vars_from_nth by lia; reflexivity.
    Qed.

    Lemma f_sub_arg : forall gs1 A rest, gs = gs1 ++ ca_arg A :: rest ->
        cargs_sub σw (gs1 ++ ca_arg A :: nil) Aw = (cargs_sub σw gs1 Aw ,, a_var (R + (na - 1 - List.length gs1))).
    Proof.
      intros * Heq.
      assert (Hlt : List.length gs1 < na) by (unfold na; rewrite Heq, List.length_app; cbn; lia).
      pose proof (f_avar _ _ _ Heq) as Ha.
      rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r.
      rewrite (firstn_S_nth _ _ (a_var (R + (na - 1 - List.length gs1)))).
      - apply cargs_sub_snoc_arg; rewrite List.length_firstn; unfold Aw; rewrite length_vars_from; lia.
      - rewrite <- (List.firstn_skipn (List.length gs1) Aw), Ha, List.nth_error_app2
          by (rewrite List.length_firstn; unfold Aw; rewrite length_vars_from; lia).
        rewrite List.length_firstn, Nat.min_l by (unfold Aw; rewrite length_vars_from; lia).
        rewrite Nat.sub_diag; reflexivity.
    Qed.

    Lemma f_sub_rec : forall gs1 t rest, gs = gs1 ++ ca_rec t :: rest ->
        cargs_sub σw (gs1 ++ ca_rec t :: nil) Aw = cargs_sub σw gs1 Aw.
    Proof.
      intros * Heq.
      assert (Hlt : List.length gs1 < na) by (unfold na; rewrite Heq, List.length_app; cbn; lia).
      pose proof (f_avar _ _ _ Heq) as Ha.
      rewrite <- cargs_sub_firstn, <- (cargs_sub_firstn gs1), List.length_app, Nat.add_1_r.
      rewrite (firstn_S_nth _ _ (a_var (R + (na - 1 - List.length gs1)))).
      - apply cargs_sub_snoc_rec; rewrite List.length_firstn; unfold Aw; rewrite length_vars_from; lia.
      - rewrite <- (List.firstn_skipn (List.length gs1) Aw), Ha, List.nth_error_app2
          by (rewrite List.length_firstn; unfold Aw; rewrite length_vars_from; lia).
        rewrite List.length_firstn, Nat.min_l by (unfold Aw; rewrite length_vars_from; lia).
        rewrite Nat.sub_diag; reflexivity.
    Qed.

    (** The container's recursive result along a leaf path it has, of an
        argument recursive in both, a variable of the context. *)
    Lemma f_rec_var : forall gs1' t' rest' gs1 t rest ls1 l ls2, gs' = gs1' ++ ca_rec t' :: rest' -> gs = gs1 ++ ca_rec t :: rest ->
        List.length gs1' = List.length gs1 ->
        shape_leaves (rv_leaves D) (pat_nargs (cargs_pat gs1) + nn) t = ls1 ++ l :: ls2 -> leaf_in D' t' l = true ->
        Ew ++ Ψc ⊨ a_var (R - 1 - (List.length (List.filter (leaf_in D' t') ls1) + cargs_nin D D' gs1' gs1))
          : leaf_ihty As (sb_of_wk (wk_shiftn n)) (cargs_sub σw gs1 Aw) (a_var (R + (na - 1 - List.length gs1))) l.
    Proof.
      intros * E1' E1 Hl1 Els Hli.
      destruct (w_kinds_split _ _ _ _ E1' E1 Hl1) as [Hka Hkb]; cbn in Hkb.
      set (r := List.length (List.filter (leaf_in D' t') ls1) + (cargs_nin D D' gs1' gs1 + 0)).
      set (ls := shape_leaves (rv_leaves D) (pat_nargs (cargs_pat gs1) + nn) t) in *.
      set (Rest := wrap_ihs_ctx D D' nn As Us na (gs1 ++ ca_rec t :: nil) (leaves_in_count D' t' ls + (cargs_nin D D' gs1' gs1 + 0))
                     rest' rest
                   ++ wrap_leaves_ctx D' t' nn As Us na gs1 (S r) ls2).
      set (T0 := leaf_ihty As (sb_of_wk (wk_shiftn (r + na + nn))) (cargs_sub (wrap_base Us nn na r) gs1 (vars_from r na))
                   (a_var (r + (na - 1 - List.length gs1))) l).
      set (Pre := wrap_leaves_ctx D' t' nn As Us na gs1 (cargs_nin D D' gs1' gs1 + 0) ls1 ++ wrap_ihs_ctx D D' nn As Us na nil 0 gs1' gs1).
      assert (EE : Ew = Rest ++ ce_ass T0 :: Pre).
      { unfold Ew; rewrite E1', E1, wrap_ihs_ctx_app by exact Hka; cbn [List.app wrap_ihs_ctx].
        fold ls; rewrite Els at 2; rewrite wrap_leaves_ctx_app; cbn [wrap_leaves_ctx]; rewrite Hli.
        unfold Rest, Pre, T0, r, leaves_in_count; rewrite <- !List.app_assoc; reflexivity. }
      assert (LPre : List.length Pre = r)
        by (unfold Pre, r; rewrite List.length_app, length_wrap_leaves_ctx, length_wrap_ihs_ctx by exact Hka; unfold leaves_in_count; lia).
      assert (HR : R = List.length Rest + S r) by (unfold R; rewrite EE, List.length_app; cbn; lia).
      assert (Hlk : Ew ++ Ψc ∋ #(0 + List.length Rest) : T0[↑]ʷ[wk_shiftn (List.length Rest)]ʷ).
      { rewrite EE, <- List.app_assoc; apply ctx_lookup_app_r; constructor. }
      replace (R - 1 - (List.length (List.filter (leaf_in D' t') ls1) + cargs_nin D D' gs1' gs1)) with (0 + List.length Rest)
        by (unfold r in HR; lia).
      replace (leaf_ihty As (sb_of_wk (wk_shiftn n)) (cargs_sub σw gs1 Aw) (a_var (R + (na - 1 - List.length gs1))) l)
        with (T0[↑]ʷ[wk_shiftn (List.length Rest)]ʷ).
      - apply valid_exp_under_ctx_vlookup; [ exact Hlk | exact f_HE ].
      - rewrite exp_wk_wk.
        transitivity (T0[wk_shiftn (S (List.length Rest))]ʷ); [ apply exp_wk_wk_eq; intros z; cbn; lia |].
        unfold T0; rewrite wrap_ihty_shift.
        unfold n, σw, Aw; replace (r + S (List.length Rest)) with R by lia; reflexivity.
    Qed.

    (** The group's branch's context's entry along a leaf path of a
        recursive argument, after those of the paths before, is a type. *)
    Lemma f_bc_entry : forall gs1 t rest ls1 l ls2, gs = gs1 ++ ca_rec t :: rest ->
        shape_leaves (rv_leaves D) (pat_nargs (cargs_pat gs1) + nn) t = ls1 ++ l :: ls2 ->
        exists j : nat, leaves_ctx nn As Us na (cargs_pat gs1) (cargs_nrec D gs1) ls1
                          ++ ihs_ctx_aux (rv_leaves D) nn As Us na nil 0 gs1 ++ Ψc
          ⊨ leaf_ihty As (sb_of_wk (wk_shiftn ((cargs_nrec D gs1 + List.length ls1) + na + nn)))
              (ihs_sub nn Us na (cargs_pat gs1) (cargs_nrec D gs1 + List.length ls1))
              (a_var ((cargs_nrec D gs1 + List.length ls1) + na - 1 - List.length (cargs_pat gs1))) l : Typeω@j.
    Proof.
      intros * Heq Els.
      pose proof (valid_blocks_bctx _ _ _ _ _ _ HBk _ _ _ _ HMv Hcon) as H; unfold elim_bctx in H; fold τU nn Cs Ns As na in H.
      rewrite Heq in H at 1.
      replace (gs1 ++ ca_rec t :: rest) with ((gs1 ++ ca_rec t :: nil) ++ rest) in H by (rewrite <- List.app_assoc; reflexivity).
      rewrite ihs_ctx_aux_app, (ihs_ctx_aux_app _ _ _ _ _ gs1 (ca_rec t :: nil)), !List.app_nil_r in H.
      cbn [ihs_ctx_aux List.app Nat.add] in H; fold nn in H.
      rewrite Els, (leaves_ctx_app _ _ _ _ _ ls1 (l :: ls2)) in H; cbn [leaves_ctx] in H.
      rewrite <- !List.app_assoc in H; cbn [List.app] in H.
      pose proof (rel_ctx_wf_app_r _ _ (rel_ctx_wf_app_r _ _ H)) as H'.
      destruct (rel_ctx_wf_ass_inv H') as [j HT].
      exists j; exact HT.
    Qed.

    (** Along the leaf paths [ls2] of a recursive argument after [gs1]: the
        variables at the paths [inb] selects, the group's eliminator at the
        others. *)
    Lemma f_leaves : forall gs1 t rest inb r0, gs = gs1 ++ ca_rec t :: rest ->
        let ls := shape_leaves (rv_leaves D) (pat_nargs (cargs_pat gs1) + nn) t in
        let ih := leaf_ih p D (Some p) Uw Bw (cargs_sub σw gs1 Aw) (a_var (R + (na - 1 - List.length gs1))) in
        (forall ls1 l ls2, ls = ls1 ++ l :: ls2 -> inb l = true ->
           Ew ++ Ψc ⊨ a_var (R - 1 - (List.length (List.filter inb ls1) + r0))
             : leaf_ihty As (sb_of_wk (wk_shiftn n)) (cargs_sub σw gs1 Aw) (a_var (R + (na - 1 - List.length gs1))) l) ->
        forall ls2 ls1 L, ls = ls1 ++ ls2 -> List.length L = cargs_nrec D gs1 + List.length ls1 ->
        gsub (Ew ++ Ψc) (wrap_inst nn na R L)
          (leaves_ctx nn As Us na (cargs_pat gs1) (cargs_nrec D gs1) ls1 ++ ihs_ctx_aux (rv_leaves D) nn As Us na nil 0 gs1 ++ Ψc) ->
        gsub (Ew ++ Ψc) (wrap_inst nn na R (L ++ sel_leaves inb ls2 (List.map ih ls2) (List.length (List.filter inb ls1) + r0) R))
          (leaves_ctx nn As Us na (cargs_pat gs1) (cargs_nrec D gs1) (ls1 ++ ls2) ++ ihs_ctx_aux (rv_leaves D) nn As Us na nil 0 gs1 ++ Ψc).
    Proof.
      intros gs1 t rest inb r0 Heq ls ih Hvar ls2.
      assert (Hlt : List.length gs1 < na) by (unfold na; rewrite Heq, List.length_app; cbn; lia).
      induction ls2 as [| l ls2 IH]; intros ls1 L Els HL Hδ; cbn [sel_leaves List.map].
      - rewrite !List.app_nil_r; exact Hδ.
      - set (X := if inb l then a_var (R - 1 - (List.length (List.filter inb ls1) + r0)) else ih l).
        assert (EX : sel_leaves inb (l :: ls2) (ih l :: List.map ih ls2) (List.length (List.filter inb ls1) + r0) R
                     = X :: sel_leaves inb ls2 (List.map ih ls2) (List.length (List.filter inb (ls1 ++ l :: nil)) + r0) R).
        { unfold X; cbn [sel_leaves]; rewrite List.filter_app; cbn [List.filter].
          destruct (inb l); rewrite List.length_app; cbn [List.length]; rewrite ?Nat.add_0_r; [ f_equal; f_equal; lia | reflexivity ]. }
        cbn [sel_leaves] in EX; rewrite EX.
        assert (Hinl : In l ls) by (rewrite Els; apply List.in_or_app; right; left; reflexivity).
        assert (HX : Ew ++ Ψc ⊨ X : leaf_ihty As (sb_of_wk (wk_shiftn n)) (cargs_sub σw gs1 Aw) (a_var (R + (na - 1 - List.length gs1))) l).
        { unfold X; destruct (inb l) eqn:Hin; [ exact (Hvar ls1 l ls2 Els Hin) |].
          exact (w_ih_leaf Ew f_HE gs1 t rest l Heq Hinl). }
        destruct (f_bc_entry gs1 t rest ls1 l ls2 Heq Els) as [jT HT].
        replace (L ++ X :: _) with ((L ++ X :: nil) ++ sel_leaves inb ls2 (List.map ih ls2)
                                                        (List.length (List.filter inb (ls1 ++ l :: nil)) + r0) R)
          by (rewrite <- List.app_assoc; reflexivity).
        replace (ls1 ++ l :: ls2) with ((ls1 ++ l :: nil) ++ ls2) by (rewrite <- List.app_assoc; reflexivity).
        apply IH; [ rewrite Els, <- List.app_assoc; reflexivity | rewrite !List.length_app, HL; cbn; lia |].
        rewrite leaves_ctx_app; cbn [leaves_ctx List.app].
        unfold wrap_inst; rewrite !List.app_assoc, sb_of_list_app; cbn [sb_of_list]; rewrite <- !List.app_assoc.
        eapply gsub_ass; [ exact Hδ | exact HT |].
        fold (wrap_inst nn na R L).
        replace (cargs_nrec D gs1 + List.length ls1) with (List.length L) by lia.
        rewrite wrap_ihty_eq by exact Hlt; exact HX.
    Qed.

    (** The recursive results of the view's branch: those after the
        arguments [gs1] and [gs1'] so far. *)
    Lemma f_ihs : forall rest' rest gs1' gs1 L, gs' = gs1' ++ rest' -> gs = gs1 ++ rest -> List.length gs1' = List.length gs1 ->
        List.length L = cargs_nrec D gs1 ->
        gsub (Ew ++ Ψc) (wrap_inst nn na R L) (ihs_ctx_aux (rv_leaves D) nn As Us na nil 0 gs1 ++ Ψc) ->
        gsub (Ew ++ Ψc)
          (wrap_inst nn na R (L ++ wrap_ihs D' D rest' rest
                                   (elim_ihs p D (Some p) Uw Bw (cargs_sub σw gs1 Aw) (pat_nargs (cargs_pat gs1) + nn) rest
                                      (List.skipn (List.length gs1) Aw))
                                   (cargs_nin D D' gs1' gs1) R))
          (ihs_ctx_aux (rv_leaves D) nn As Us na nil 0 (gs1 ++ rest) ++ Ψc).
    Proof.
      induction rest' as [| g' rest' IH]; intros [| g rest] gs1' gs1 L E1' E1 Hl1 HL Hδ.
      - cbn [wrap_ihs]; rewrite !List.app_nil_r; exact Hδ.
      - exfalso; rewrite List.app_nil_r in E1'; rewrite E1', E1 in Hk.
        pose proof (cargs_kinds_length _ _ Hk) as H0; rewrite !List.length_app in H0; cbn in H0; lia.
      - exfalso; rewrite List.app_nil_r in E1; rewrite E1', E1 in Hk.
        pose proof (cargs_kinds_length _ _ Hk) as H0; rewrite !List.length_app in H0; cbn in H0; lia.
      - destruct (w_kinds_split _ _ _ _ E1' E1 Hl1) as [Hka Hkg]; cbn in Hkg.
        rewrite (f_avar _ _ _ E1).
        assert (E1a : gs' = (gs1' ++ g' :: nil) ++ rest') by (rewrite E1', <- List.app_assoc; reflexivity).
        assert (E1b : gs = (gs1 ++ g :: nil) ++ rest) by (rewrite E1, <- List.app_assoc; reflexivity).
        assert (Hl1' : List.length (gs1' ++ g' :: nil) = List.length (gs1 ++ g :: nil)) by (rewrite !List.length_app; cbn; lia).
        replace (gs1 ++ g :: rest) with ((gs1 ++ g :: nil) ++ rest) by (rewrite <- List.app_assoc; reflexivity).
        replace (S (List.length gs1)) with (List.length (gs1 ++ g :: nil)) by (rewrite List.length_app; cbn; lia).
        destruct g' as [A' | t'], g as [A | t]; cbn in Hkg; try contradiction.
        + (** non-recursive in both *)
          cbn [wrap_ihs elim_ihs]; rewrite <- (f_sub_arg _ _ _ E1).
          replace (S (pat_nargs (cargs_pat gs1) + nn)) with (pat_nargs (cargs_pat (gs1 ++ ca_arg A :: nil)) + nn)
            by (rewrite cargs_pat_snoc; reflexivity).
          replace (cargs_nin D D' gs1' gs1) with (cargs_nin D D' (gs1' ++ ca_arg A' :: nil) (gs1 ++ ca_arg A :: nil))
            by (rewrite cargs_nin_app by exact Hka; cbn; lia).
          apply IH; [ exact E1a | exact E1b | exact Hl1' | rewrite cargs_nrec_app'; cbn; lia |].
          rewrite ihs_ctx_aux_app, List.app_nil_r; cbn [ihs_ctx_aux List.app]; exact Hδ.
        + (** non-recursive in the container, recursive in the view: the
              group's eliminator along each path *)
          cbn [wrap_ihs elim_ihs List.hd List.tl].
          set (ls := shape_leaves (rv_leaves D) (pat_nargs (cargs_pat gs1) + nn) t).
          set (ih := leaf_ih p D (Some p) Uw Bw (cargs_sub σw gs1 Aw) (a_var (R + (na - 1 - List.length gs1)))).
          fold ls ih.
          assert (Els : List.length (shape_leaves (rv_leaves D) 0 t) = List.length (List.map ih ls))
            by (rewrite List.length_map; apply length_shape_leaves).
          rewrite Els, List.firstn_app, List.firstn_all, Nat.sub_diag, List.skipn_app, List.skipn_all, Nat.sub_diag.
          rewrite ?List.firstn_O, ?List.skipn_O, List.app_nil_r.
          pose proof (f_leaves gs1 t rest (fun _ => false) (cargs_nin D D' gs1' gs1) E1
                        ltac:(intros * _ Hf; discriminate) ls nil L eq_refl ltac:(cbn; lia)
                        ltac:(cbn [leaves_ctx List.app]; exact Hδ)) as Hlv.
          rewrite sel_leaves_none in Hlv by (rewrite List.length_map; reflexivity).
          rewrite <- (f_sub_rec _ _ _ E1).
          replace (pat_nargs (cargs_pat gs1) + nn) with (pat_nargs (cargs_pat (gs1 ++ ca_rec t :: nil)) + nn)
            by (rewrite cargs_pat_snoc; reflexivity).
          replace (cargs_nin D D' gs1' gs1) with (cargs_nin D D' (gs1' ++ ca_arg A' :: nil) (gs1 ++ ca_rec t :: nil))
            by (rewrite cargs_nin_app by exact Hka; cbn; lia).
          rewrite List.app_assoc.
          apply IH; [ exact E1a | exact E1b | exact Hl1'
                    | rewrite List.length_app, List.length_map, cargs_nrec_app', HL; cbn; unfold ls; rewrite (length_shape_leaves _ _ _ 0); lia |].
          rewrite ihs_ctx_aux_app, List.app_nil_r; cbn [ihs_ctx_aux List.app Nat.add].
          rewrite <- List.app_assoc; exact Hlv.
        + (** recursive in both: the container's results where the paths are
              its, the group's eliminator elsewhere *)
          cbn [wrap_ihs elim_ihs List.hd List.tl].
          set (ls := shape_leaves (rv_leaves D) (pat_nargs (cargs_pat gs1) + nn) t).
          set (ih := leaf_ih p D (Some p) Uw Bw (cargs_sub σw gs1 Aw) (a_var (R + (na - 1 - List.length gs1)))).
          fold ls ih.
          assert (Ein : List.map (leaf_in D' t') (shape_leaves (rv_leaves D) 0 t) = List.map (leaf_in D' t') ls)
            by apply leaf_in_shape_leaves.
          assert (Els : List.length (shape_leaves (rv_leaves D) 0 t) = List.length (List.map ih ls))
            by (rewrite List.length_map; apply length_shape_leaves).
          rewrite Els, List.firstn_app, List.firstn_all, Nat.sub_diag, List.skipn_app, List.skipn_all, Nat.sub_diag.
          rewrite ?List.firstn_O, ?List.skipn_O, List.app_nil_r.
          rewrite (wrap_leaves_in_ext _ _ _ ls _ _ _ Ein), (leaves_in_count_ext _ _ _ ls Ein), wrap_leaves_sel.
          pose proof (f_leaves gs1 t rest (leaf_in D' t') (cargs_nin D D' gs1' gs1) E1
                        (fun ls1 l ls2 Els0 Hin => f_rec_var gs1' t' rest' gs1 t rest ls1 l ls2 E1' E1 Hl1 Els0 Hin)
                        ls nil L eq_refl ltac:(cbn; lia) ltac:(cbn [leaves_ctx List.app]; exact Hδ)) as Hlv.
          cbn [List.filter List.length Nat.add] in Hlv.
          rewrite <- (f_sub_rec _ _ _ E1).
          replace (pat_nargs (cargs_pat gs1) + nn) with (pat_nargs (cargs_pat (gs1 ++ ca_rec t :: nil)) + nn)
            by (rewrite cargs_pat_snoc; reflexivity).
          replace (leaves_in_count D' t' ls + cargs_nin D D' gs1' gs1)
            with (cargs_nin D D' (gs1' ++ ca_rec t' :: nil) (gs1 ++ ca_rec t :: nil))
            by (rewrite cargs_nin_app by exact Hka; cbn [cargs_nin]; unfold ls;
                rewrite (leaves_in_count_shift D D' t' t (pat_nargs (cargs_pat gs1) + nn)); lia).
          rewrite List.app_assoc.
          apply IH; [ exact E1a | exact E1b | exact Hl1'
                    | rewrite List.length_app, length_sel_leaves, cargs_nrec_app', HL by (rewrite List.length_map; reflexivity);
                      cbn; unfold ls; rewrite (length_shape_leaves _ _ _ 0); lia |].
          rewrite ihs_ctx_aux_app, List.app_nil_r; cbn [ihs_ctx_aux List.app Nat.add].
          rewrite <- List.app_assoc; exact Hlv.
    Qed.

    (** The instance of the group's branch's context in the whole wrapped
        context. *)
    Lemma f_sub : gsub (Ew ++ Ψc)
        (wrap_inst nn na R (wrap_ihs D' D gs' gs (elim_ihs p D (Some p) Uw Bw σw nn gs Aw) 0 R))
        (ihs_ctx_aux (rv_leaves D) nn As Us na nil 0 gs ++ Ψc).
    Proof.
      pose proof (f_ihs gs' gs nil nil nil eq_refl eq_refl eq_refl eq_refl
                    ltac:(cbn [ihs_ctx_aux List.app]; exact (w_base Ew f_HE))) as H.
      cbn [List.app List.length List.skipn cargs_sub cargs_nin cargs_pat pat_nargs Nat.add] in H; exact H.
    Qed.
  End Full.

  (** The instance of the group's branch's context there is a
      substitution built from valid parts ([vb_sub]), when the wrapped
      branch's context has as many recursive results as the container's
      constructor. *)
  Theorem gsub_wrap_br : cargs_nin D D' gs' gs = cargs_nrec D' gs' ->
      gsub (wrap_bctx p D D' Mv gs' gs As Us ++ Γ) (wrap_br_sub p D D' Us Bks Mv gs' gs) (elim_bctx p D Mv gs As Us ++ Γ).
  Proof.
    intros Hcnt.
    pose proof f_sub as H.
    pose proof f_R as HR.
    rewrite w_ctx_eq.
    replace (elim_bctx p D Mv gs As Us ++ Γ) with (ihs_ctx_aux (rv_leaves D) nn As Us na nil 0 gs ++ Ψc)
      by (unfold elim_bctx, Ψc, Cs, Ns; rewrite <- !List.app_assoc; reflexivity).
    eapply gsub_eq; [ exact H |].
    rewrite HR, Hcnt; unfold wrap_inst, wrap_br_sub, wrap_base; cbv zeta; rewrite w_len.
    replace (cargs_nrec D' gs' + na + nn) with (nn + na + cargs_nrec D' gs') by lia.
    reflexivity.
  Qed.

  (** A wrapped branch is valid in its context, at the group's type moved
      by the instance ([vb_branch]). *)
  Theorem valid_wrap_br : cargs_nin D D' gs' gs = cargs_nrec D' gs' ->
      forall b n B, List.nth_error Bks v = Some b -> brs_lookup (eb_brs b) c = Some (n, B) ->
      wrap_bctx p D D' Mv gs' gs As Us ++ Γ ⊨ snd (wrap_br p D D' Us Bks Mv (eb_brs b) c gs')
        : (elim_bty p D v Mv c gs (eb_motive b) Us)[wrap_br_sub p D D' Us Bks Mv gs' gs].
  Proof.
    intros Hcnt * Hb Hlk.
    rewrite (wrap_br_snd _ _ _ _ _ _ _ _ _ _ _ _ Hcon Hlk).
    exact (rel_exp_under_ctx_gsub (gsub_wrap_br Hcnt)
             (valid_blocks_branch _ _ _ _ _ _ HBk _ _ _ _ _ _ _ HMv Hb Hcon (brs_lookup_in _ _ _ _ Hlk))).
  Qed.
End WrapBranch.

End Fixed_GCtx.
