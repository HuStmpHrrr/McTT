(** * Inductive Types: Reading a Group's Declaration

    A group's declaration ([ind_decl], in [Syntax]) is filed in the entry
    of each of its declared members ([ge_ind]), with the body of the
    member's module: its constructors (and the recursor).  The type former
    [a_ind pq k] and the constructors [a_con pq k c] name the member [k] of
    the group [pq], the path of the entry of its first member
    ([ind_lookup]); these are the counts and the types that typing,
    evaluation and readback read off it. *)

From Stdlib Require Import Lia List String PeanoNat.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Members.
From Mctt.Core.Syntactic.Inductives Require Export Group.
Import Syntax_Notations.
#[local] Open Scope list_scope.


(** The arguments of the constructor [c] of the member [M]. *)
Definition ind_con (M : imember) (c : string) : option (list carg) := cons_lookup (im_cons M) c.

(** The branch of the constructor [c]: the number of variables it binds,
    and its body. *)
Fixpoint brs_lookup (Bs : list (string * nat * exp)) (c : string) : option (nat * exp) :=
  match Bs with
  | nil => None
  | (c', n, B) :: Bs' => if String.eqb c c' then Some (n, B) else brs_lookup Bs' c
  end.

(** The number of recursive arguments among [gs]. *)
Fixpoint cargs_nrec (gs : list carg) : nat :=
  match gs with
  | nil => 0
  | ca_arg _ :: gs' => cargs_nrec gs'
  | ca_rec _ :: gs' => S (cargs_nrec gs')
  end.

(** ** A Property of All the Members of a List

    The values of a constructor, an inductive type and their parameters are
    lists, of which evaluation and readback take segments; a property of all
    the members of the list holds of all the members of a segment. *)

Section AllIn.
  Context {A : Type} (P : A -> Prop).

  Lemma all_in_nil : forall a, In a nil -> P a.
  Proof. intros ? []. Qed.

  Lemma all_in_cons : forall x l, P x -> (forall a, In a l -> P a) -> forall a, In a (x :: l) -> P a.
  Proof. intros * Hx Hl a [<- | Ha]; auto. Qed.

  Lemma all_in_app : forall l l', (forall a, In a l -> P a) -> (forall a, In a l' -> P a) ->
                                  forall a, In a (l ++ l') -> P a.
  Proof. intros * Hl Hl' a Ha; apply in_app_or in Ha as [Ha | Ha]; auto. Qed.

  Lemma all_in_firstn : forall n l, (forall a, In a l -> P a) -> forall a, In a (firstn n l) -> P a.
  Proof.
    intros * Hl a Ha; apply Hl; rewrite <- (firstn_skipn n l); apply in_or_app; left; assumption.
  Qed.

  Lemma all_in_skipn : forall n l, (forall a, In a l -> P a) -> forall a, In a (skipn n l) -> P a.
  Proof.
    intros * Hl a Ha; apply Hl; rewrite <- (firstn_skipn n l); apply in_or_app; right; assumption.
  Qed.

  Lemma all_in_tail : forall x l, (forall a, In a (x :: l) -> P a) -> forall a, In a l -> P a.
  Proof. intros * H a Ha; apply H; right; assumption. Qed.

  Lemma all_in_head : forall x l, (forall a, In a (x :: l) -> P a) -> P x.
  Proof. intros * H; apply H; left; reflexivity. Qed.

End AllIn.

(** Splits a goal [forall a, In a l -> P a] along the segments [l] is
    built of, down to hypotheses about whole lists or their tails, and
    leaves the members added one by one ([P x]) to [tac]. *)
Ltac all_in_with tac :=
  repeat lazymatch goal with
  | |- forall a, In a _ -> _ =>
  first [ eassumption
               | apply all_in_nil
               | match goal with H : forall a, In a (cons _ ?l) -> _ |- forall a, In a ?l -> _ =>
                   exact (all_in_tail _ _ _ H) end
               | apply all_in_app
               | apply all_in_firstn
               | apply all_in_skipn
               | apply all_in_cons; [ tac |] ]
  end.

Lemma brs_lookup_in : forall Bs c n B, brs_lookup Bs c = Some (n, B) -> In (c, n, B) Bs.
Proof.
  induction Bs as [| [[c' n'] B'] Bs IH]; cbn; intros * H; [ discriminate |].
  destruct (String.eqb_spec c c') as [-> | _]; [ injection H as -> ->; left; reflexivity | right; auto ].
Qed.

(** The environment of a branch extends the eliminator's by the
    non-uniform parameters, the arguments and the recursive results; the
    environment of the motive's instance at a neutral, by the non-uniform
    parameters and the neutral. *)
Lemma ind_branch_args_length : forall {A} D M (gs : list carg) (vs ihs : list A),
    List.length vs = im_np D M + List.length gs ->
    List.length (skipn (ind_nu D) (firstn (im_np D M) vs) ++ skipn (im_np D M) vs ++ ihs) =
      im_nn M + List.length gs + List.length ihs.
Proof.
  intros * H; rewrite !length_app, !length_skipn, length_firstn, Nat.min_l by lia.
  unfold im_np in *; lia.
Qed.

Lemma ind_motive_args_length : forall {A} D M (as' : list A) x,
    List.length as' = im_np D M ->
    List.length (skipn (ind_nu D) as' ++ x :: nil) = S (im_nn M).
Proof. intros * H; rewrite length_app, length_skipn; cbn; unfold im_np in *; lia. Qed.

(** The telescope of the non-uniform parameters, outermost first. *)
Lemma im_nn_tele_length : forall M, List.length (List.rev (im_nparams M)) = im_nn M.
Proof. intros; rewrite length_rev; reflexivity. Qed.

(** ** The Types of a Declaration

    What typing reads off a group [D] at [pq]: the types of the type
    formers and of the constructors, the contexts of the motives and of the
    branches of the eliminator, and the instances of telescopes at lists
    of terms.  All are built once, by typing; evaluation and readback use
    the declaration directly.

    The parameters of a member, [im_params D M], are a closed context,
    innermost first: its non-uniform ones, [im_nn M] of them, are the
    innermost.  The sort is in the context of the uniform ones. *)

Import Sub_Notations Wk_Notations.

(** The member [j] of the group [pq] at the uniform parameters [Us] and
    its non-uniform parameters [Ns]. *)
Definition ind_mty (pq : qname) (D : ind_decl) (j : nat) (Us Ns : list exp) : typ :=
  match ind_member D j with
  | Some M => im_ty_at pq j M Us Ns
  | None => a_True
  end.

(** The parameters of the member [M], and the uniform ones, as variables,
    under [k] more binders. *)
Definition ind_pvars (D : ind_decl) (M : imember) (k : nat) : list exp := vars_from k (im_np D M).
(** The uniform parameters as variables, under [k] binders and the [nn]
    non-uniform parameters of a member. *)
Definition ind_uvars (D : ind_decl) (nn k : nat) : list exp := vars_from (k + nn) (ind_nu D).

(** The type of the type former of a member: a [Π] over its parameters
    of the sort. *)
Definition ind_ty (D : ind_decl) (M : imember) : typ := ctx_pi (im_params D M) (ind_sort D)[wk_shiftn (im_nn M)]ʷ.

(** The types of the non-recursive arguments of a constructor are in the
    context of the non-recursive arguments before them: a recursive argument
    is not a binder for them ([cargs_strat]).  [wk_pat pat] sends that
    context into the one of all the arguments before, where [pat] tells,
    innermost first, which of them are recursive. *)
Fixpoint cargs_strat (gs : list carg) : ctx :=
  match gs with
  | nil => nil
  | ca_arg A :: gs' => cargs_strat gs' ++ ce_ass A :: nil
  | ca_rec _ :: gs' => cargs_strat gs'
  end.

(** ** Shapes

    A shape [pt_pi B1 (pt_pi B2 … (pt_self j Ps))] is a function from its
    domains [B1], [B2], …, each over the ones before it, into the member [j]
    at the non-uniform parameters [Ps], over all its domains.  Its domains,
    outermost first, and as a telescope, innermost first. *)
Fixpoint ptyp_doms {E : Set} (t : ptyp_g E) : list E :=
  match t with
  | pt_pi A t => A :: ptyp_doms t
  | _ => nil
  end.

Definition doms_ctx (Bs : list exp) : ctx := List.rev (List.map ce_ass Bs).
Definition ptyp_tele (t : ptyp) : ctx := doms_ctx (ptyp_doms t).
Definition ptyp_depth (t : ptyp) : nat := List.length (ptyp_doms t).

(** The shape of each recursive argument among [gs] ends in a member of
    [D] at as many parameters as the member has non-uniform ones. *)
Definition cargs_plen (D : ind_decl) (gs : list carg) : Prop :=
  forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 ->
    exists Mj, ind_member D (ptyp_mem t) = Some Mj /\ List.length (ptyp_ps t) = im_nn Mj.

(** The rest of a shape after [n] of its domains. *)
Fixpoint ptyp_skip (n : nat) (t : ptyp) : ptyp :=
  match n, t with
  | S n, pt_pi _ t => ptyp_skip n t
  | _, _ => t
  end.

(** The context of the domains of a shape, each weakened past the arguments
    before it by the pattern [pat] extended by the domains before it:
    the context in which the type of a recursive argument binds them. *)
Fixpoint sh_ctx (pat : list bool) (Bs : list exp) : ctx :=
  match Bs with
  | nil => nil
  | B :: Bs => sh_ctx (false :: pat) Bs ++ ce_ass B[wk_pat pat]ʷ :: nil
  end.

(** The type of a recursive argument of shape [t], in the context of all
    the arguments before it and the parameters of a member with [nn]
    non-uniform parameters, its components over the non-recursive
    arguments before it ([pat], innermost first, tells which of those
    before it are recursive): the [Π] over the domains of the member the
    shape ends in at the uniform parameters and the shape's non-uniform
    ones.  Under a domain the components are over one more variable, which
    is no recursive argument. *)
Fixpoint ptyp_ty (pq : qname) (D : ind_decl) (nn : nat) (pat : list bool) (t : ptyp) : typ :=
  match t with
  | pt_pi A t => a_pi A[wk_pat pat]ʷ (ptyp_ty pq D nn (false :: pat) t)
  | pt_self j Ps => ind_mty pq D j (ind_uvars D nn (List.length pat)) (List.map (fun P => P[wk_pat pat]ʷ) Ps)
  end.

(** The arguments of a constructor as a context over the parameters,
    innermost first: a recursive one is of the type of its shape. *)
Fixpoint cargs_ctx_aux (pq : qname) (D : ind_decl) (nn : nat) (pat : list bool) (gs : list carg) : ctx :=
  match gs with
  | nil => nil
  | ca_arg A :: gs' => cargs_ctx_aux pq D nn (false :: pat) gs' ++ ce_ass A[wk_pat pat]ʷ :: nil
  | ca_rec t :: gs' => cargs_ctx_aux pq D nn (true :: pat) gs' ++ ce_ass (ptyp_ty pq D nn pat t) :: nil
  end.

(** The arguments of a constructor of the member [M] as a context over its
    parameters, from no argument before. *)
Definition cargs_ctx (pq : qname) (D : ind_decl) (M : imember) (gs : list carg) : ctx :=
  cargs_ctx_aux pq D (im_nn M) nil gs.

(** ** The Group's Members as Variables

    The equations of a group's views mention the group itself: a view's
    instance is at the group's own types.  Before the group is filed they
    are checked with its declared members as variables, [Self_j] for the
    declared member [j], each of the member's type over the group's
    uniform parameters, the [Self]s inside the uniform parameters
    ([grp_sctx]); [IsS] gives each view's instance there.  Once the group
    is filed at [pq], [grp_sb pq D] instantiates [Self_j] by the type former
    [a_ind pq j] at the uniform parameters, and the checked forms become
    the filed ones. *)
Definition self_ty (D : ind_decl) (M : imember) : typ := ctx_pi (im_nparams M) (ind_sort D)[wk_shiftn (im_nn M)]ʷ.

(** The variables [Self_j], [Self_(j+1)], … of the members [ms], innermost
    first, each of its member's type over the [Self]s before it. *)
Fixpoint grp_selfs_from (D : ind_decl) (j : nat) (ms : list imember) : ctx :=
  match ms with
  | nil => nil
  | M :: ms' => grp_selfs_from D (S j) ms' ++ ce_ass (self_ty D M)[wk_shiftn j]ʷ :: nil
  end.

(** The variables of the declared members, [Self_0] outermost. *)
Definition grp_selfs (D : ind_decl) : ctx := grp_selfs_from D 0 (List.firstn (ind_ndecl D) (ind_members D)).

(** The context a group's views are checked in: the [Self]s inside the
    uniform parameters. *)
Definition grp_sctx (D : ind_decl) : ctx := grp_selfs D ++ ind_uparams D.

(** The [Self]s instantiated by the type formers of the filed group at
    [pq], at the uniform parameters. *)
Definition grp_sb (pq : qname) (D : ind_decl) : sub :=
  sb_of_list sb_id (List.map (fun j => apps (a_ind pq j) (vars_from 0 (ind_nu D))) (List.seq 0 (ind_ndecl D))).

(** The group's own data, which never mentions the group, moved under the
    [Self]s: [k] binders above the uniform parameters. *)
Definition self_wk (D : ind_decl) (k : nat) : wk := wk_qn k (wk_shiftn (ind_ndecl D)).

(** The type of the member [j] with the members as variables, [d] binders
    above the [Self]s, at the non-uniform parameters [Ns]: [Self_j] at a
    declared member, the container's at the view's instance [IsS j] at a
    view. *)
Definition self_mty (D : ind_decl) (IsS : nat -> list exp) (j d : nat) (Ns : list exp) : typ :=
  match ind_member D j with
  | Some Mj =>
      match im_head Mj with
      | mh_decl _ => apps_exp (a_var (d + (ind_ndecl D - 1 - j))) Ns
      | mh_view qc kc _ _ => apps_exp (a_ind qc kc) (List.map (fun I => I[wk_shiftn d]ʷ) (IsS j) ++ Ns)
      end
  | None => a_True
  end.

(** [ptyp_ty] and [cargs_ctx] with the members as variables. *)
Fixpoint sptyp_ty (D : ind_decl) (IsS : nat -> list exp) (nn : nat) (pat : list bool) (t : ptyp) : typ :=
  match t with
  | pt_pi A t => a_pi A[wk_pat pat]ʷ[self_wk D (List.length pat + nn)]ʷ (sptyp_ty D IsS nn (false :: pat) t)
  | pt_self j Ps => self_mty D IsS j (List.length pat + nn)
                      (List.map (fun P => P[wk_pat pat]ʷ[self_wk D (List.length pat + nn)]ʷ) Ps)
  end.

(** [cargs_ctx_aux] with the members as variables. *)
Fixpoint scargs_ctx_aux (D : ind_decl) (IsS : nat -> list exp) (nn : nat) (pat : list bool) (gs : list carg) : ctx :=
  match gs with
  | nil => nil
  | ca_arg A :: gs' => scargs_ctx_aux D IsS nn (false :: pat) gs' ++ ce_ass A[wk_pat pat]ʷ[self_wk D (List.length pat + nn)]ʷ :: nil
  | ca_rec t :: gs' => scargs_ctx_aux D IsS nn (true :: pat) gs' ++ ce_ass (sptyp_ty D IsS nn pat t) :: nil
  end.

(** [cargs_ctx] with the members as variables. *)
Definition scargs_ctx (D : ind_decl) (IsS : nat -> list exp) (M : imember) (gs : list carg) : ctx :=
  scargs_ctx_aux D IsS (im_nn M) nil gs.

(** The type of a constructor of the member [k]: a [Π] over the
    parameters and the arguments of the member at the parameters.  (For a
    view, this is the type of the container's constructor at the view's
    uniform arguments, as the group sees it.) *)
Definition con_ty (pq : qname) (D : ind_decl) (k : nat) (M : imember) (gs : list carg) : typ :=
  ctx_pi (im_params D M)
    (ctx_pi (cargs_ctx pq D M gs)
       (ind_mty pq D k (ind_uvars D (im_nn M) (List.length gs)) (vars_from (List.length gs) (im_nn M)))).

(** The instances of the types of a telescope [Δ] (innermost first) at the
    terms [Ms] (outermost first), the others free variables sent as [σ]
    does. *)
Fixpoint tele_insts_aux (Δr : list centry) (σ : sub) (Ms : list exp) : list typ :=
  match Δr, Ms with
  | ce_ass A :: Δr', M :: Ms' => A[σ] :: tele_insts_aux Δr' (σ ,, M) Ms'
  | _, _ => nil
  end.

Definition tele_insts (Δ : ctx) (σ : sub) (Ms : list exp) : list typ := tele_insts_aux (List.rev Δ) σ Ms.

(** ** The Eliminator

    The motive of the block of the member [k] is in the context of the
    member's non-uniform parameters, at the group's uniform ones [Us], and
    of the scrutinee. *)
Definition elim_mctx (pq : qname) (D : ind_decl) (k : nat) (M : imember) (Us : list exp) : ctx :=
  ce_ass (ind_mty pq D k (List.map (fun U => U[wk_shiftn (im_nn M)]ʷ) Us) (vars_from 0 (im_nn M)))
  :: tele_sub (im_nparams M) (sb_of_list Id Us).

(** The type of an argument of shape [t], its components moved by [σ], at
    the uniform parameters [Us]: [ptyp_ty] at an instance of the parameters
    and the arguments before. *)
Fixpoint ptyp_ty_at (pq : qname) (D : ind_decl) (Us : list exp) (σ : sub) (t : ptyp) : typ :=
  match t with
  | pt_pi B t => a_pi B[σ] (ptyp_ty_at pq D (List.map (fun U => U[wk_shift]ʷ) Us) (sb_q σ) t)
  | pt_self j Ps => ind_mty pq D j Us (List.map (fun P => P[σ]) Ps)
  end.

(** The type of the recursive result of an argument [x] of shape [t]: the
    motive of the member the shape ends in, among the motives [As], at the
    shape's non-uniform parameters and [x], under the shape's domains, at
    which [x] is applied.  The motives' context, the eliminator's, is moved
    by [β], the shape's components by [σ]. *)
Fixpoint ptyp_ihty (As : list exp) (β σ : sub) (x : exp) (t : ptyp) : typ :=
  match t with
  | pt_pi B t => a_pi B[σ] (ptyp_ihty As (β ⨟ sb_of_wk wk_shift) (sb_q σ) (a_app x[wk_shift]ʷ (a_var 0)) t)
  | pt_self j Ps => (List.nth j As a_True)[sb_of_list β (List.map (fun P => P[σ]) Ps ++ x :: nil)]
  end.

(** The recursive results of a constructor's arguments: the motive of the
    member each recursive argument's shape ends in, at the argument and the
    non-uniform parameters it is declared at.  [i] arguments of [gs] and [j]
    results come before; [na] is the number of all the arguments, [nn] that
    of the member's non-uniform parameters.  [ihs_sub] moves a shape's
    components from the context of the non-recursive arguments before it
    and the parameters to the branch's: past the recursive arguments before
    it, the uniform parameters instantiated by [Us], past the arguments
    after it and the results before it. *)
Definition ihs_sub (nn : nat) (Us : list exp) (na : nat) (pat : list bool) (j : nat) : sub :=
  (sb_of_wk (wk_pat pat) ⨟ sb_qn (List.length pat + nn) (sb_of_list Id Us))
    ⨟ sb_of_wk (wk_shiftn (na - List.length pat + j)).

(** The recursive results of a branch, after [j] of them, as a context:
    one per recursive argument, of its motive's type ([ihty]). *)
Fixpoint ihs_ctx_aux (nn : nat) (As : list exp) (Us : list exp) (na : nat)
    (pat : list bool) (j : nat) (gs : list carg) : ctx :=
  match gs with
  | nil => nil
  | ca_arg _ :: gs' => ihs_ctx_aux nn As Us na (false :: pat) j gs'
  | ca_rec t :: gs' =>
      ihs_ctx_aux nn As Us na (true :: pat) (S j) gs' ++
        ce_ass (ptyp_ihty As (sb_of_wk (wk_shiftn (j + na + nn))) (ihs_sub nn Us na pat j)
                  (a_var (j + na - 1 - List.length pat)) t) :: nil
  end.

(** The context of the branch of a constructor with arguments [gs] of the
    member [M]: the non-uniform parameters, the arguments and the recursive
    results, the motives being [As]. *)
Definition elim_bctx (pq : qname) (D : ind_decl) (M : imember) (gs : list carg) (As : list exp) (Us : list exp) : ctx :=
  ihs_ctx_aux (im_nn M) As Us (List.length gs) nil 0 gs ++
  tele_sub (cargs_ctx pq D M gs) (sb_qn (im_nn M) (sb_of_list Id Us)) ++
  tele_sub (im_nparams M) (sb_of_list Id Us).

(** The type of the branch: the motive [A] of the member [k] at the
    constructor applied to the parameters and the arguments. *)
Definition elim_bty (pq : qname) (k : nat) (M : imember) (c : string) (gs : list carg) (A : exp) (Us : list exp) : typ :=
  let na := List.length gs in
  let nn := im_nn M in
  let n := (nn + na + cargs_nrec gs)%nat in
  A[sb_of_list (sb_of_wk (wk_shiftn n))
      (vars_from (cargs_nrec gs + na) nn ++
       apps_exp (a_con (fst (im_ref pq k M)) (snd (im_ref pq k M)) c)
         (im_pre M (List.map (fun U => U[wk_shiftn n]ʷ) Us) ++
          vars_from (cargs_nrec gs + na) nn ++ vars_from (cargs_nrec gs) na) :: nil)].

(** The branches under [φ], each under the binders it has: what
    weakening does to the branches of an eliminator. *)
Definition brs_wk (Bs : list (string * nat * exp)) (φ : wk) : list (string * nat * exp) :=
  List.map (fun b => (fst b, (snd b)[wk_qn (snd (fst b)) φ]ʷ)) Bs.

(** The blocks under [φ]: what weakening does to the blocks of an
    eliminator ([exp_wk] unfolds to it). *)
Definition blocks_wk (Bks : list eblock) (φ : wk) : list eblock :=
  List.map (fun b =>
    match b with
    | eb_mk nm oZ A Bs =>
        eb_mk nm (option_map (fun Z => exp_wk Z (wk_qn (nm - 1) φ)) oZ) (exp_wk A (wk_qn nm φ))
          (List.map (fun br => (fst br, exp_wk (snd br) (wk_qn (snd (fst br)) φ))) Bs)
    end) Bks.

Lemma exp_wk_elim : forall oq Us m Bks M φ,
    (a_elim oq Us m Bks M)[φ]ʷ = a_elim oq (List.map (fun U => U[φ]ʷ) Us) m (blocks_wk Bks φ) M[φ]ʷ.
Proof. reflexivity. Qed.

(** The motives of the blocks, in order. *)
Definition blocks_motives (Bks : list eblock) : list exp := List.map eb_motive Bks.

(** ** Reading an Eliminator at its Member

    An eliminator of a group at its member [m] is read, when stuck, as the
    eliminator of the group the member is at: the group itself at a
    declared member, the container's at a view (E1′).  The blocks it reads
    are those of the members of that group, each the block of the member
    of this group [elim_src] gives: itself at a declared member, the view
    [vm] lists at a view.  Nothing is built: a block is looked up. *)
Definition im_sel (M : imember) : option (list nat) :=
  match im_head M with
  | mh_decl _ => None
  | mh_view _ _ _ vm => Some vm
  end.

(** The member of this group whose block the eliminator reads for the
    member [i] of the group it is read as. *)
Definition elim_src (sel : option (list nat)) (i : nat) : nat :=
  match sel with
  | None => i
  | Some vm => List.nth i vm 0
  end.

(** The motives of the members of the group read, in its order. *)
Definition motives_sel (sel : option (list nat)) (As : list exp) : list exp :=
  match sel with
  | None => As
  | Some vm => List.map (fun v => List.nth v As a_True) vm
  end.

(** The motive of each block read binds the non-uniform parameters of the
    member of the group read it is the block of, and the scrutinee. *)
Definition blocks_nm_at (Dq : ind_decl) (sel : option (list nat)) (Bks : list eblock) : Prop :=
  forall i Mi b, ind_member Dq i = Some Mi -> List.nth_error Bks (elim_src sel i) = Some b -> eb_nm b = S (im_nn Mi).

(** The eliminator a recursive result at the member [j] is, at the
    group's uniform parameters [Us]: for a group with views the group's,
    named; for one without, the eliminator itself. *)
Definition elim_at (pq : qname) (D : ind_decl) (oq : option qname) (Us : list exp) (Bks : list eblock) (j : nat) (M : exp) : exp :=
  a_elim (if ind_has_views D then Some pq else oq) Us j Bks M.

(** The recursive result of an argument [M] of shape [t], as an
    elimination: under the shape's domains, moved by [σ], the eliminator at
    [M] applied to them. *)
Fixpoint ptyp_ih (pq : qname) (D : ind_decl) (oq : option qname) (Us : list exp) (Bks : list eblock)
    (σ : sub) (M : exp) (t : ptyp) : exp :=
  match t with
  | pt_pi B t =>
      a_fn B[σ] (ptyp_ih pq D oq (List.map (fun U => U[wk_shift]ʷ) Us) (blocks_wk Bks wk_shift) (sb_q σ)
                   (a_app M[wk_shift]ʷ (a_var 0)) t)
  | pt_self j _ => elim_at pq D oq Us Bks j M
  end.

(** The recursive results of the arguments [As] of a constructor, as
    eliminations; [σ] instantiates the parameters and the non-recursive
    arguments before, which the shapes' domains are over. *)
Fixpoint elim_ihs (pq : qname) (D : ind_decl) (oq : option qname) (Us : list exp) (Bks : list eblock)
    (σ : sub) (gs : list carg) (As : list exp) : list exp :=
  match gs, As with
  | ca_arg _ :: gs', N :: As' => elim_ihs pq D oq Us Bks (σ ,, N) gs' As'
  | ca_rec t :: gs', M :: As' => ptyp_ih pq D oq Us Bks σ M t :: elim_ihs pq D oq Us Bks σ gs' As'
  | _, _ => nil
  end.

(** The branches are in the order of the constructors. *)
Definition brs_names (cs : list (string * list carg)) (Bs : list (string * nat * exp)) : Prop :=
  List.map fst cs = List.map (fun b => fst (fst b)) Bs.

(** The group of an eliminator: written, or that of the scrutinee's type,
    at a declared member. *)
Definition elim_grp (D : ind_decl) (oq : option qname) (pq : qname) (m : nat) : Prop :=
  oq = Some pq \/ (oq = None /\ m < ind_ndecl D).

(** The components of a recursive argument's shape as the type of the
    argument has them: the domain [d], under the arguments before it ([pat])
    and the domains before it, and the non-uniform parameters of the member
    the shape ends in, under all its domains ([ptyp_ty]). *)
Definition ptyp_dom_at (pat : list bool) (d : nat) (t : ptyp) : typ :=
  (List.nth d (ptyp_doms t) a_True)[wk_pat (List.repeat false d ++ pat)]ʷ.

(** The non-uniform parameters a shape ends in, under the arguments
    before ([pat]) and all its domains. *)
Definition ptyp_ps_at (pat : list bool) (t : ptyp) : list exp :=
  List.map (fun P => P[wk_pat (List.repeat false (ptyp_depth t) ++ pat)]ʷ) (ptyp_ps t).

(** The arguments [gs] of a view's constructor are those [gs'] of the
    container's at its arguments, as this group sees them: an argument
    recursive in the container is recursive in the view, at the view's
    member [vm] gives for the container's member, through as many domains;
    an argument the container takes as non-recursive may be either. *)
Fixpoint cargs_corr (vm : list nat) (gs' gs : list carg) : Prop :=
  match gs', gs with
  | nil, nil => True
  | ca_rec t' :: gs1', ca_rec t :: gs1 =>
      List.nth_error vm (ptyp_mem t') = Some (ptyp_mem t) /\ ptyp_depth t' = ptyp_depth t /\ cargs_corr vm gs1' gs1
  | ca_arg _ :: gs1', ca_arg _ :: gs1 => cargs_corr vm gs1' gs1
  | ca_arg _ :: gs1', ca_rec _ :: gs1 => cargs_corr vm gs1' gs1
  | _, _ => False
  end.

(** The arguments of a view's constructor that the view nests through
    (non-recursive in the container [gs'], recursive in the view [gs]) end
    in members of rank below [r] ([rk]).  The eliminator at a view reads
    back its branches with the eliminator at those members applied to fresh
    variables; the rank orders these readbacks. *)
Fixpoint cargs_nest_ok (rk : nat -> nat) (r : nat) (gs' gs : list carg) : Prop :=
  match gs', gs with
  | ca_arg _ :: gs1', ca_rec t :: gs1 => rk (ptyp_mem t) < r /\ cargs_nest_ok rk r gs1' gs1
  | _ :: gs1', _ :: gs1 => cargs_nest_ok rk r gs1' gs1
  | _, _ => True
  end.

(** ** The Eliminator at a View, as the Container's

    The eliminator of a group at its view of the declared member [k'] of
    the container's group [D'] at [Is] is the container's eliminator at
    [k'] (E1′): each block of the container's for its member [i'] is the
    block of the view [vm] gives for [i'], each branch for a container's
    constructor binding the container's arguments and recursive results,
    its body the view's branch, whose recursive results are the
    container's where the argument is recursive in the container, and the
    eliminator of the group at the argument where it is recursive in the
    view only.  [wrap_ihs gs' gs ihs r' nr']: the recursive results of the
    view's branch, [ihs] the group's ones, [r'] container's ones before,
    [nr'] the container's in all. *)
Fixpoint wrap_ihs (gs' gs : list carg) (ihs : list exp) (r' nr' : nat) : list exp :=
  match gs', gs with
  | ca_rec _ :: gs1', ca_rec _ :: gs1 => a_var (nr' - 1 - r') :: wrap_ihs gs1' gs1 (List.tl ihs) (S r') nr'
  | ca_arg _ :: gs1', ca_rec _ :: gs1 => List.hd a_True ihs :: wrap_ihs gs1' gs1 (List.tl ihs) r' nr'
  | _ :: gs1', ca_arg _ :: gs1 => wrap_ihs gs1' gs1 ihs r' nr'
  | _, _ => nil
  end.

(** The branch of the container's constructor [c] with arguments [gs'], the
    view's member [Mv] and its block's branches [Bs], under the context of
    the eliminator; [nn] non-uniform parameters. *)
Definition wrap_br (pq : qname) (D : ind_decl) (Us : list exp) (Bks : list eblock)
    (Mv : imember) (Bs : list (string * nat * exp)) (c : string) (gs' : list carg) : (string * nat * exp)%type :=
  let nn := im_nn Mv in
  let na := List.length gs' in
  let nr' := cargs_nrec gs' in
  let n' := (nn + na + nr')%nat in
  let gs := match ind_con Mv c with Some gs => gs | None => gs' end in
  let B := match brs_lookup Bs c with Some (_, B) => B | None => a_True end in
  let Us' := List.map (fun U => U[wk_shiftn n']ʷ) Us in
  let nvars := vars_from (nr' + na) nn in
  let avars := vars_from nr' na in
  let ihs := elim_ihs pq D (Some pq) Us' (blocks_wk Bks (wk_shiftn n')) (sb_of_list (sb_of_wk (wk_shiftn n')) (Us' ++ nvars)) gs avars in
  (c, n', B[sb_of_list (sb_of_wk (wk_shiftn n')) (nvars ++ avars ++ wrap_ihs gs' gs ihs 0 nr')]).

(** The members [vm] lists of [D] are those of the container's group [D']
    at the view's arguments, as the group's declaration says: as many,
    each a member of [D], with as many non-uniform parameters, the same
    constructors, and the arguments of each as the container's, classified
    for [D]. *)
Record vwrap_ok (D D' : ind_decl) (vm : list nat) : Prop := mk_vwrap_ok
  { (** [vm] lists one member of [D] per member of the container's group. *)
    vwo_length : List.length vm = List.length (ind_members D')
  (** Each member [vm] lists is a member of [D] with as many non-uniform
      parameters as the container's, the same constructors, and arguments
      corresponding to the container's ([cargs_corr]). *)
  ; vwo_members : forall i' Mi' v, ind_member D' i' = Some Mi' -> List.nth_error vm i' = Some v ->
      exists Mv, ind_member D v = Some Mv /\ im_nn Mv = im_nn Mi' /\
        List.map fst (im_cons Mv) = List.map fst (im_cons Mi') /\
        (forall c gs' gs, In (c, gs') (im_cons Mi') -> ind_con Mv c = Some gs -> cargs_corr vm gs' gs) }.

(** The container's blocks: one per member of the container's group [D']. *)
Definition vwrap_block (pq : qname) (D : ind_decl) (vm : list nat) (Us : list exp) (Bks : list eblock)
    (i' : nat) (Mi' : imember) : eblock :=
  let v := List.nth i' vm 0 in
  match List.nth_error Bks v, ind_member D v with
  | Some (eb_mk nm _ A Bs), Some Mv =>
      eb_mk nm None A (List.map (fun cg => wrap_br pq D Us Bks Mv Bs (fst cg) (snd cg)) (im_cons Mi'))
  | _, _ => eb_mk 0 None a_True nil
  end.

(** The container's blocks for its members [ms], from the member [i'] on. *)
Fixpoint vwrap_from (pq : qname) (D : ind_decl) (vm : list nat) (Us : list exp) (Bks : list eblock)
    (i' : nat) (ms : list imember) : list eblock :=
  match ms with
  | nil => nil
  | Mi' :: ms' => vwrap_block pq D vm Us Bks i' Mi' :: vwrap_from pq D vm Us Bks (S i') ms'
  end.

(** The blocks of the container's eliminator that the eliminator at a view
    reads as: one per member of the container's group [D']. *)
Definition vwrap (pq : qname) (D D' : ind_decl) (vm : list nat) (Us : list exp) (Bks : list eblock) : list eblock :=
  vwrap_from pq D vm Us Bks 0 (ind_members D').

Lemma nth_error_vwrap_from : forall pq D vm Us Bks ms s k b,
    List.nth_error (vwrap_from pq D vm Us Bks s ms) k = Some b ->
    exists Mi', List.nth_error ms k = Some Mi' /\ b = vwrap_block pq D vm Us Bks (s + k) Mi'.
Proof.
  induction ms as [| M ms IH]; intros * H; [ destruct k; discriminate |].
  destruct k as [| k]; cbn in H.
  - injection H as <-; exists M; rewrite Nat.add_0_r; auto.
  - destruct (IH _ _ _ H) as (Mi' & HM & ->); exists Mi'; split; [ exact HM | f_equal; lia ].
Qed.

Lemma length_vwrap : forall pq D D' vm Us Bks, List.length (vwrap pq D D' vm Us Bks) = List.length (ind_members D').
Proof.
  intros; unfold vwrap; generalize 0; induction (ind_members D'); intros; cbn; [ reflexivity | f_equal; apply IHl ].
Qed.

(** The sort of a declaration is a universe. *)
Definition ind_sort_univ (S : typ) : Prop := (exists i, S = Typeω@i) \/ (exists t, S = Type⟨t⟩).

(** The level of a small sort, and a level of none for a large one. *)
Definition ind_sort_lvl (S : typ) : exp :=
  match S with
  | a_univ t => t
  | _ => a_llit (0, 0)
  end.

(** ** Module Variables

    [exp_mvc d M]: every module variable of [M] is bound by one of the [d]
    binders above it inside the term, not free.  The parameters of a
    declaration are a telescope of assumptions, so their types have no free
    module variable; the typing rule of a declaration says so, which is what
    lets their instances at variables and at terms of variables coincide. *)

(** Every module variable of a term is bound by one of the [n] binders
    above it. *)
Fixpoint exp_mvc (n : nat) (M : exp) : Prop :=
  match M with
  | a_typ _ | a_level _ | a_llit _ | a_True | a_true | a_False => True
  | a_succl M | a_univ M => exp_mvc n M
  | a_maxl M N => exp_mvc n M /\ exp_mvc n N
  | a_exfalso A M => exp_mvc (S n) A /\ exp_mvc n M
  | a_ind _ _ | a_con _ _ _ | a_nlit _ | a_ntok => True
  | a_elim _ Us _ Bks M =>
      all_list (exp_mvc n) Us /\
      all_blocks (fun nm oZ A Bs => opt_all (exp_mvc (nm - 1 + n)) oZ /\ exp_mvc (nm + n) A /\
                                    all_brs (fun k B => exp_mvc (k + n) B) Bs) Bks /\ exp_mvc n M
  | a_pi A B | a_fn A B => exp_mvc n A /\ exp_mvc (S n) B
  | a_app M N => exp_mvc n M /\ exp_mvc n N
  | a_var _ => True
  | a_let b B => bnd_mvc n b /\ exp_mvc (S n) B
  | a_mem H _ => modexp_mvc n H
  | a_record _ => True
  | a_tuple T fs => exp_mvc n T /\ all_list (fun f => exp_mvc n (snd f)) fs
  | a_proj _ M => exp_mvc n M
  end
with modexp_mvc (n : nat) (H : modexp) : Prop :=
  match H with
  | me_unit _ => True
  | me_var x => x < n
  | me_mem H _ => modexp_mvc n H
  | me_app H N => modexp_mvc n H /\ exp_mvc n N
  | me_lit U => gunit_mvc n U
  end
with bnd_mvc (n : nat) (b : bnd) : Prop :=
  match b with
  | b_def oA M => match oA with Some A => exp_mvc n A | None => True end /\ exp_mvc n M
  | b_mod U => gunit_mvc n U
  end
with gunit_mvc (n : nat) (U : gunit) : Prop :=
  match U with
  | gu_mk Δ D =>
      (fix tele_mvc (Δ : list centry) : Prop :=
         match Δ with
         | nil => True
         | e :: Δ' => centry_mvc (List.length Δ' + n) e /\ tele_mvc Δ'
         end) Δ /\
      moddef_mvc (List.length Δ + n) D
  end
with moddef_mvc (n : nat) (D : moddef) : Prop :=
  match D with
  | md_body sm Φ => gmod_mvc n Φ
  | md_alias E => modexp_mvc n E
  end
with gmod_mvc (n : nat) (Φ : gmod) : Prop :=
  match Φ with
  | gm_nil => True
  | gm_ext Φ _ E => gmod_mvc n Φ /\ gentry_mvc (gm_binders Φ + n) E
  | gm_open Φ H _ => gmod_mvc n Φ /\ modexp_mvc (gm_binders Φ + n) H
  end
with gentry_mvc (n : nat) (E : gentry) : Prop :=
  match E with
  | ge_def _ _ A B => exp_mvc n A /\ match B with Some M => exp_mvc n M | None => True end
  | ge_mod _ U => gunit_mvc n U
  | ge_ind _ _ _ D Φ => gmod_mvc (ind_nu D + n) Φ
  | ge_def_mod _ A M U => exp_mvc n A /\ exp_mvc n M /\ gunit_mvc n U
  | ge_record _ _ R Φ => gmod_mvc (S (List.length (record_params R)) + n) Φ
  end
with centry_mvc (n : nat) (e : centry) : Prop :=
  match e with
  | ce_ass A => exp_mvc n A
  | ce_def A M => exp_mvc n A /\ exp_mvc n M
  | ce_mod U => gunit_mvc n U
  end.



(** A telescope whose types have no free module variable. *)
Definition ctx_mvc (Δ : ctx) : Prop := List.Forall (centry_mvc 0) Δ.

(** A declaration whose parameters' types, sort, views' uniform arguments
    and constructors' argument types have no free module variable. *)
Definition carg_mvc (g : carg) : Prop :=
  match g with
  | ca_arg A => exp_mvc 0 A
  | ca_rec t => List.Forall (exp_mvc 0) (ptyp_doms t) /\ List.Forall (exp_mvc 0) (ptyp_ps t)
  end.

(** A view's uniform arguments have no free module variable. *)
Definition mhead_mvc (h : mhead) : Prop :=
  match h with
  | mh_decl _ => True
  | mh_view _ _ Is _ => List.Forall (exp_mvc 0) Is
  end.

(** No free module variable anywhere in a group. *)
Record decl_mvc (D : ind_decl) : Prop := mk_decl_mvc
  { (** In the uniform parameters' types. *)
    dmv_uparams : ctx_mvc (ind_uparams D)
  (** In the sort. *)
  ; dmv_sort : exp_mvc 0 (ind_sort D)
  (** In each member's non-uniform parameters, view arguments and
      constructor arguments. *)
  ; dmv_members : forall k M, ind_member D k = Some M ->
      ctx_mvc (im_nparams M) /\ mhead_mvc (im_head M) /\
      (forall c gs, In (c, gs) (im_cons M) -> List.Forall carg_mvc gs) }.

(** No free module variable anywhere in a record declaration, as
    [decl_mvc] for a group: so its value's type, the type former at the
    parameters as variables, is a type over them ([record_self]). *)
Record record_mvc (R : record_decl) : Prop := mk_record_mvc
  { (** No parameter's type has a free module variable. *)
    params_mvc : ctx_mvc (record_params R)
  (** The sort has no free module variable. *)
  ; sort_mvc : exp_mvc 0 (record_sort R)
  (** No field's type has a free module variable. *)
  ; fields_mvc : forall k f T, List.nth_error (record_fields R) k = Some (f, T) -> exp_mvc 0 T }.

(** The types are read off a declaration once; [simpl] leaves them
    folded, and the lemmas below compute with them. *)
#[global] Arguments ind_ty : simpl never.
#[global] Arguments con_ty : simpl never.
#[global] Arguments cargs_ctx : simpl never.
#[global] Arguments tele_insts : simpl never.
#[global] Arguments vars_from : simpl never.
#[global] Arguments elim_mctx : simpl never.
#[global] Arguments elim_bctx : simpl never.
#[global] Arguments elim_bty : simpl never.
#[global] Arguments ihs_sub : simpl never.
#[global] Arguments ind_mty : simpl never.

(** ** Facts About the Types of a Declaration *)

Lemma cons_lookup_in : forall cs c gs, cons_lookup cs c = Some gs -> In (c, gs) cs.
Proof.
  induction cs as [| [c' gs'] cs IH]; cbn; intros c gs H; [ discriminate |].
  destruct (String.eqb_spec c c') as [-> | _]; [ injection H as ->; left; reflexivity | right; auto ].
Qed.

Lemma cons_lookup_of_in : forall cs c gs, In (c, gs) cs -> exists gs', cons_lookup cs c = Some gs'.
Proof.
  induction cs as [| [c' gs'] cs IH]; cbn; intros c gs H; [ destruct H |].
  destruct (String.eqb_spec c c') as [-> | Hne]; [ eauto |].
  destruct H as [H | H]; [ injection H as -> ->; contradiction | eauto ].
Qed.

Lemma brs_names_con : forall cs Bs c n B,
    brs_names cs Bs -> In (c, n, B) Bs -> exists gs, cons_lookup cs c = Some gs.
Proof.
  intros * Hn Hin.
  assert (Hc : In c (List.map fst cs)) by (rewrite Hn; apply List.in_map_iff; exists (c, n, B); auto).
  apply List.in_map_iff in Hc as ([c' gs] & Hc & Hin'); cbn in Hc; subst c'.
  exact (cons_lookup_of_in _ _ _ Hin').
Qed.

Lemma length_cargs_ctx_aux : forall pq D nn gs pat, List.length (cargs_ctx_aux pq D nn pat gs) = List.length gs.
Proof. induction gs as [| [] gs IH]; intros; cbn; rewrite ?length_app, ?IH; cbn; lia. Qed.

Lemma length_cargs_ctx : forall pq D M gs, List.length (cargs_ctx pq D M gs) = List.length gs.
Proof. intros; apply length_cargs_ctx_aux. Qed.

Lemma length_ihs_ctx_aux : forall nn As Us na gs pat j,
    List.length (ihs_ctx_aux nn As Us na pat j gs) = cargs_nrec gs.
Proof. induction gs as [| [] gs IH]; intros; cbn; rewrite ?length_app, ?IH; cbn; lia. Qed.

Lemma length_elim_mctx : forall pq D k M Us, List.length (elim_mctx pq D k M Us) = S (im_nn M).
Proof. intros; unfold elim_mctx; cbn; rewrite length_tele_sub; reflexivity. Qed.

Lemma length_elim_bctx : forall pq D M gs As Us,
    List.length (elim_bctx pq D M gs As Us) = (cargs_nrec gs + List.length gs + im_nn M)%nat.
Proof.
  intros; unfold elim_bctx; rewrite !length_app, length_ihs_ctx_aux, !length_tele_sub, length_cargs_ctx.
  unfold im_nn; lia.
Qed.

Lemma length_elim_ihs : forall pq D oq Us Bks σ gs As,
    List.length As = List.length gs -> List.length (elim_ihs pq D oq Us Bks σ gs As) = cargs_nrec gs.
Proof.
  intros pq D oq Us Bks σ gs; revert σ.
  induction gs as [| [] gs IH]; intros σ [| N As] Hl; cbn in *; try discriminate; try reflexivity.
  - apply IH; lia.
  - f_equal; apply IH; lia.
Qed.

Lemma length_vars_from : forall k n, List.length (vars_from k n) = n.
Proof. intros; unfold vars_from; rewrite length_map, length_rev, length_seq; reflexivity. Qed.

Lemma length_tele_insts_aux : forall Δr σ Ms,
    List.Forall (fun e => exists A, e = ce_ass A) Δr ->
    List.length (tele_insts_aux Δr σ Ms) = Nat.min (List.length Δr) (List.length Ms).
Proof.
  intros Δr σ Ms Hr; revert σ Ms.
  induction Hr as [| e Δr [A ->] Hr IH]; intros σ [| M Ms]; cbn; try reflexivity.
  rewrite IH; reflexivity.
Qed.

Lemma length_tele_insts : forall Δ σ Ms,
    List.Forall (fun e => exists A, e = ce_ass A) Δ ->
    List.length (tele_insts Δ σ Ms) = Nat.min (List.length Δ) (List.length Ms).
Proof.
  intros; unfold tele_insts; rewrite length_tele_insts_aux, length_rev; [ reflexivity |].
  apply Forall_rev; assumption.
Qed.

Lemma cargs_ctx_aux_ass : forall pq D nn gs pat, List.Forall (fun e => exists A, e = ce_ass A) (cargs_ctx_aux pq D nn pat gs).
Proof.
  induction gs as [| [] gs IH]; intros; cbn; [ constructor | |]; apply List.Forall_app; split; eauto.
Qed.
