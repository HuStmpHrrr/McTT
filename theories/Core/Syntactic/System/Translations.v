(** * Declarations as Written: Their Contexts, and the Translation of Mutual Definitions

    What both the typed fill ([Core.TypedElab]) and the command judgment
    ([Core.Syntactic.System.Command]) read of a declaration as written,
    so that it sits below both: the fill reads a part of a command in the
    context the command's run reads it in, and for a group and a mutual
    definition those contexts and that group are defined here.

    - The contexts a group's parts are written in: the [Self]s of its
      declared members ([rd_selfs]), its uniform parameters under them
      ([rd_uctx]), a declared member's constructor arguments ([rm_pctx]),
      and a constructor's arguments as a telescope ([rtele]).
    - The translation of a mutual definition: its group, read off its
      functions' scrutinees ([mdef_group]), and the eliminator each
      function is filed as ([mdef_blocks], [mdef_defs]). *)

From Stdlib Require Import List String PeanoNat Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Command Members.
From Mctt.Core.Syntactic.System Require Import Definitions Lemmas Structural.
From Mctt.Core.Syntactic.Inductives Require Export Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Semantic Require Import NbE.
Import Syntax_Notations GlobalCtx_Notations.

(** ** The Contexts of a Group as Written *)

(** The number of declared members of a raw declaration. *)
Definition rd_n (R : raw_decl) : nat := List.length (raw_decl_members R).
(** The number of uniform parameters of a raw declaration. *)
Definition rd_nu (R : raw_decl) : nat := List.length (raw_decl_uparams R).

(** The type of [Self_j]: the declared member's, over its own parameters,
    the group's uniform ones outermost. *)
Definition rd_self_ty (R : raw_decl) (Mr : raw_member) : typ :=
  ctx_pi (raw_member_nparams Mr ++ raw_decl_uparams R) (raw_member_sort Mr)[wk_shiftn (List.length (raw_member_nparams Mr))]ʷ.

(** The [Self]s, innermost first, each over those before it. *)
Fixpoint rd_selfs_from (R : raw_decl) (j : nat) (ms : list raw_member) : ctx :=
  match ms with
  | nil => nil
  | Mr :: ms' => rd_selfs_from R (S j) ms' ++ ce_ass (rd_self_ty R Mr)[wk_shiftn j]ʷ :: nil
  end.

(** The context of the [Self]s of all declared members, [Self_0]
    outermost. *)
Definition rd_selfs (R : raw_decl) : ctx := rd_selfs_from R 0 (raw_decl_members R).

(** The parameters' types are written over the frames' parameters, so
    under the [Self]s they are weakened past them: the group's uniform
    parameters, and a declared member's parameters. *)
Definition rd_uctx (Ξ : gstack) (R : raw_decl) : ctx :=
  tele_wk (raw_decl_uparams R) (wk_shiftn (rd_n R)) ++ rd_selfs R ++ gs_tele Ξ.

(** The context a declared member's constructor arguments are written in:
    its own parameters and the uniform ones, under the [Self]s and the
    frames' parameters. *)
Definition rm_pctx (Ξ : gstack) (R : raw_decl) (Mr : raw_member) : ctx :=
  tele_wk (raw_member_nparams Mr ++ raw_decl_uparams R) (wk_shiftn (rd_n R)) ++ rd_selfs R ++ gs_tele Ξ.

(** The arguments as written, as a telescope, innermost first. *)
Definition rtele (args : list (string * exp)) : ctx := List.rev (List.map (fun a => ce_ass (snd a)) args).

(** ** Mutual Definitions

    [mutual def (Δ) f (ys) (z : Z) : A | … with … end]: one function per
    member of a group, in any order, each matched to its member by the
    normal form of its scrutinee's type.  The group and its uniform
    parameters [Us], over [Δ] and the frames, are read off the first
    function's, a declared member.  A function's member is the first one
    whose type at [Us] and at the function's non-uniform parameters has
    the scrutinee's normal form; every member has exactly one function.
    Each is filed as the definition [λ Δ ys z. a_elim (Some pq) m Bks z]:
    a block per member, the function's of that member, its scrutinee's
    type the annotation, its result type the motive, its clauses the
    branches, moved under [ys] and [z]. *)

(** The first position of [W] among [Ws], of [m] among [ms]. *)
Fixpoint nf_index (W : nf) (Ws : list nf) : option nat :=
  match Ws with
  | nil => None
  | W' :: Ws' => if exp_eq_dec (nf_to_exp W) (nf_to_exp W') then Some 0 else option_map S (nf_index W Ws')
  end.

(** The first position of [m] among [ms]. *)
Fixpoint nat_index (m : nat) (ms : list nat) : option nat :=
  match ms with
  | nil => None
  | m' :: ms' => if Nat.eqb m m' then Some 0 else option_map S (nat_index m ms')
  end.

(** The block a function makes, under [k] more binders of the function it
    is the eliminator of. *)
Definition rf_block (k : nat) (f : raw_fun) : eblock :=
  let nn := List.length (raw_fun_nparams f) in
  eb_mk (S nn) (Some (raw_fun_scrut f)[wk_qn nn (wk_shiftn k)]ʷ) (raw_fun_res f)[wk_qn (S nn) (wk_shiftn k)]ʷ
    (List.map (fun b => (fst (fst b), snd (fst b), (snd b)[wk_qn (snd (fst b)) (wk_shiftn k)]ʷ)) (raw_fun_clauses f)).

(** The blocks, one per member [j < nm], of the function of member [j]. *)
Definition mdef_blocks (k nm : nat) (fs : list raw_fun) (ms : list nat) : list eblock :=
  List.map (fun j => match nat_index j ms with
                     | Some i => match List.nth_error fs i with Some g => rf_block k g | None => eb_mk 0 None a_True nil end
                     | None => eb_mk 0 None a_True nil
                     end)
    (List.seq 0 nm).

(** The definitions filed: each function's name, type and term.  The
    eliminator of the group [D] at [pq] carries the uniform parameters
    [Us], moved under the function's non-uniform parameters and its
    scrutinee. *)
Definition mdef_defs (pq : qname) (D : ind_decl) (Us : list exp) (Δ : ctx) (fs : list raw_fun) (ms : list nat) :
    list (string * typ * exp) :=
  List.map (fun fm =>
              let f := fst fm in
              let k := S (List.length (raw_fun_nparams f)) in
              (raw_fun_name f, ctx_pi Δ (ctx_pi (raw_fun_nparams f) (a_pi (raw_fun_scrut f) (raw_fun_res f))),
               ctx_fn Δ (ctx_fn (raw_fun_nparams f)
                           (a_fn (raw_fun_scrut f)
                              (a_elim (Some pq) (List.map (fun U => U[wk_shiftn k]ʷ) Us) (snd fm)
                                 (mdef_blocks k (ind_nblk D) fs ms) (a_var 0))))))
    (List.combine fs ms).

(** The member [m] of a function: its scrutinee's normal form is first
    that of [m]'s type at [Us] and at the function's non-uniform
    parameters, among the members with a block (a record view has none,
    so no function). *)
Inductive mdef_member (Θ : gdeps) (Ξ : gstack) (pq : qname) (D : ind_decl) (Us : list exp) (Δ : ctx) :
    raw_fun -> nat -> Prop :=
(** The only rule: the scrutinee's type and the members' types are types
    before they are normalized, as normalizing an untyped term need not
    terminate *)
| mdef_member_intro : forall f W Ws m Mm,
    (exists i, Θ ⍮ Ξ ⍮ raw_fun_nparams f ++ Δ ++ gs_tele Ξ ⊢ raw_fun_scrut f : Typeω@i) ->
    nbe_ty Θ Ξ (raw_fun_nparams f ++ Δ ++ gs_tele Ξ) (raw_fun_scrut f) W ->
    Forall2 (fun jM Wj =>
               (exists i, Θ ⍮ Ξ ⍮ raw_fun_nparams f ++ Δ ++ gs_tele Ξ
                  ⊢ im_ty_at pq (fst jM) (snd jM) (List.map (fun U => U[wk_shiftn (List.length (raw_fun_nparams f))]ʷ) Us)
                      (vars_from 0 (List.length (raw_fun_nparams f))) : Typeω@i) /\
               nbe_ty Θ Ξ (raw_fun_nparams f ++ Δ ++ gs_tele Ξ)
                 (im_ty_at pq (fst jM) (snd jM) (List.map (fun U => U[wk_shiftn (List.length (raw_fun_nparams f))]ʷ) Us)
                    (vars_from 0 (List.length (raw_fun_nparams f)))) Wj)
      (List.combine (List.seq 0 (ind_nblk D)) (ind_bmembers D)) Ws ->
    nf_index W Ws = Some m ->
    ind_member D m = Some Mm ->
    im_nn Mm = List.length (raw_fun_nparams f) ->
    mdef_member Θ Ξ pq D Us Δ f m.

(** [mdef_group Θ Ξ Δ f0 fs pq m0 Ps D Us ms]: the functions [f0 :: fs] of
    a mutual definition over [Δ] are of the group [D] at [pq], at the
    uniform parameters [Us], over [Δ] and the frames, read off the first
    function's scrutinee, whose normal form is the member [m0] at [Ps]; the
    function [i] is of the member [ms_i], each member of one function. *)
Record mdef_group (Θ : gdeps) (Ξ : gstack) (Δ : ctx) (f0 : raw_fun) (fs : list raw_fun) (pq : qname) (m0 : nat)
    (Ps : list nf) (D : ind_decl) (Us : list exp) (ms : list nat) : Prop := mk_mdef_group
  { (** The first function's scrutinee is a type, before it is normalized,
        as normalizing an untyped term need not terminate *)
    mdef_group_scrut_typed : exists i, Θ ⍮ Ξ ⍮ raw_fun_nparams f0 ++ Δ ++ gs_tele Ξ ⊢ raw_fun_scrut f0 : Typeω@i
    (** Its normal form is the member [m0] of the group at [pq], at [Ps] *)
  ; mdef_group_scrut_nf : nbe_ty Θ Ξ (raw_fun_nparams f0 ++ Δ ++ gs_tele Ξ) (raw_fun_scrut f0) (nf_indty pq m0 Ps)
    (** The group at [pq] is [D] *)
  ; mdef_group_lookup : ind_lookup Θ Ξ pq = Some D
    (** The member [m0] is a declared one *)
  ; mdef_group_declared : m0 < ind_ndecl D
    (** The uniform parameters, free of the first function's own
        parameters *)
  ; mdef_group_uparams :
      img_pats (List.repeat true (List.length (raw_fun_nparams f0))) (List.firstn (ind_nu D) (List.map nf_to_exp Ps)) = Some Us
    (** Each function's member *)
  ; mdef_group_members : Forall2 (mdef_member Θ Ξ pq D Us Δ) (f0 :: fs) ms
    (** One function per member with a block: all but the record views *)
  ; mdef_group_count : List.length ms = ind_nblk D
    (** No member has two functions *)
  ; mdef_group_distinct : List.NoDup ms }.

(** ** One Group, One Set of Parts *)

Lemma Forall2_functional : forall {X Y} (P : X -> Y -> Prop), (forall x y y', P x y -> P x y' -> y = y') ->
    forall xs ys ys', Forall2 P xs ys -> Forall2 P xs ys' -> ys = ys'.
Proof.
  intros X Y P HP xs ys ys' H; revert ys'; induction H as [| x y xs ys Hxy _ IH]; intros ys' H'; inversion H'; subst;
    [ reflexivity | f_equal; eauto ].
Qed.

Lemma mdef_member_functional : forall Θ Ξ pq D Us Δ f m m',
    mdef_member Θ Ξ pq D Us Δ f m -> mdef_member Θ Ξ pq D Us Δ f m' -> m = m'.
Proof.
  intros * H H'; destruct H as [f W Ws m Mm _ HW HWs Hi _ _];
    inversion H' as [f' W' Ws' m'' Mm' _ HW' HWs' Hi' _ _]; subst.
  pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-.
  assert (Ws = Ws') as <-.
  { eapply Forall2_functional; [| exact HWs | exact HWs' ].
    intros ? ? ? [_ H1] [_ H2]; cbv beta in H1, H2; exact (functional_nbe_ty _ _ _ _ H1 H2). }
  congruence.
Qed.

(** A mutual definition's functions are of one group, at one set of
    uniform parameters, each of one member. *)
Lemma mdef_group_functional : forall Θ Ξ Δ f0 fs pq m0 Ps D Us ms pq' m0' Ps' D' Us' ms',
    mdef_group Θ Ξ Δ f0 fs pq m0 Ps D Us ms -> mdef_group Θ Ξ Δ f0 fs pq' m0' Ps' D' Us' ms' ->
    pq = pq' /\ m0 = m0' /\ Ps = Ps' /\ D = D' /\ Us = Us' /\ ms = ms'.
Proof.
  intros * [_ HW Hl _ HU Hm _ _] [_ HW' Hl' _ HU' Hm' _ _].
  pose proof (functional_nbe_ty _ _ _ _ HW HW') as E; injection E as <- <- <-.
  rewrite Hl in Hl'; injection Hl' as <-.
  rewrite HU in HU'; injection HU' as <-.
  assert (ms = ms') as <-
    by (eapply Forall2_functional; [| exact Hm | exact Hm' ]; intros; eapply mdef_member_functional; eassumption).
  repeat split.
Qed.

(** The motives of a mutual definition's blocks are its functions'
    results, under their parameters. *)
Lemma mdef_blocks_motives_eq : forall k nm fs1 fs2 ms,
    Forall2 (fun f1 f2 => raw_fun_nparams f1 = raw_fun_nparams f2 /\ raw_fun_res f1 = raw_fun_res f2) fs1 fs2 ->
    blocks_motives (mdef_blocks k nm fs1 ms) = blocks_motives (mdef_blocks k nm fs2 ms).
Proof.
  intros * H; unfold blocks_motives, mdef_blocks; rewrite !List.map_map; apply List.map_ext; intros j.
  destruct (nat_index j ms) as [i |]; [| reflexivity ].
  revert i; induction H as [| f1 f2 fs1 fs2 [En Er] _ IH]; intros [| i]; cbn; try reflexivity.
  - unfold rf_block; rewrite En, Er; reflexivity.
  - apply IH.
Qed.

(** A function of a mutual definition is its parts. *)
Lemma raw_fun_parts_eq : forall f f',
    raw_fun_name f' = raw_fun_name f -> raw_fun_nparams f' = raw_fun_nparams f -> raw_fun_scrut f' = raw_fun_scrut f ->
    raw_fun_res f' = raw_fun_res f -> raw_fun_clauses f' = raw_fun_clauses f -> f' = f.
Proof. intros [] []; cbn; intros; subst; reflexivity. Qed.

(** A declared member as written is its parts. *)
Lemma raw_member_parts_eq : forall Mr Mr',
    raw_member_name Mr' = raw_member_name Mr -> raw_member_nparams Mr' = raw_member_nparams Mr -> raw_member_sort Mr' = raw_member_sort Mr ->
    raw_member_cons Mr' = raw_member_cons Mr -> Mr' = Mr.
Proof. intros [] []; cbn; intros; subst; reflexivity. Qed.

(** A group as written is its parts. *)
Lemma raw_decl_parts_eq : forall R R',
    raw_decl_uparams R' = raw_decl_uparams R -> raw_decl_members R' = raw_decl_members R -> raw_decl_rec_field R' = raw_decl_rec_field R -> R' = R.
Proof. intros [] []; cbn; intros; subst; reflexivity. Qed.

(** Arguments are their names and their telescope. *)
Lemma rtele_names_eq : forall args args', List.map fst args' = List.map fst args -> rtele args' = rtele args -> args' = args.
Proof.
  intros args args' En Et; unfold rtele in Et; apply (f_equal (@List.rev _)) in Et; rewrite !rev_involutive in Et.
  revert args En Et; induction args' as [| [y T] a' IH]; intros [| [z U] a] En Et; cbn in *; try discriminate;
    [ reflexivity |].
  injection En as -> En; injection Et as -> Et; rewrite (IH _ En Et); reflexivity.
Qed.

(** The [Self]s are read off the uniform parameters and the members'
    parameters and sorts. *)
Lemma rd_selfs_from_heads_eq : forall R1 R2 ms1 ms2 j, raw_decl_uparams R1 = raw_decl_uparams R2 ->
    Forall2 (fun M1 M2 => raw_member_nparams M1 = raw_member_nparams M2 /\ raw_member_sort M1 = raw_member_sort M2) ms1 ms2 ->
    rd_selfs_from R1 j ms1 = rd_selfs_from R2 j ms2.
Proof.
  intros * Eu H; revert j; induction H as [| M1 M2 ms1 ms2 [En Es] _ IH]; intros j; cbn; [ reflexivity |].
  rewrite IH; unfold rd_self_ty; rewrite Eu, En, Es; reflexivity.
Qed.

(** So is a member's context. *)
Lemma rm_pctx_heads_eq : forall Ξ R1 R2 Mr1 Mr2, raw_decl_uparams R1 = raw_decl_uparams R2 ->
    Forall2 (fun M1 M2 => raw_member_nparams M1 = raw_member_nparams M2 /\ raw_member_sort M1 = raw_member_sort M2) (raw_decl_members R1) (raw_decl_members R2) ->
    raw_member_nparams Mr1 = raw_member_nparams Mr2 -> rm_pctx Ξ R1 Mr1 = rm_pctx Ξ R2 Mr2.
Proof.
  intros * Eu Hm En; unfold rm_pctx, rd_selfs, rd_n.
  rewrite Eu, En, (rd_selfs_from_heads_eq _ _ _ _ 0 Eu Hm), (Forall2_length Hm); reflexivity.
Qed.
