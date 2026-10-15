(** * Inductive Types: Reading a Declaration

    A declaration ([ind_decl], in [Syntax]) is filed in the entry of its
    type ([ge_ind]), with the body of the type's module: its constructors
    and its recursor.  The type former [a_ind p] and the constructors
    [a_con p c] name it by the path [p] of the entry ([ind_lookup]); these
    are the counts that typing, evaluation and readback read off it. *)

From Stdlib Require Import Lia List String PeanoNat.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Members.
Import Syntax_Notations.
#[local] Open Scope list_scope.


(** The arguments of the constructor [c]. *)
Fixpoint cons_lookup (cs : list (string * list carg)) (c : string) : option (list carg) :=
  match cs with
  | nil => None
  | (c', gs) :: cs' => if String.eqb c c' then Some gs else cons_lookup cs' c
  end.

Definition ind_con (D : ind_decl) (c : string) : option (list carg) := cons_lookup (ind_cons D) c.

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

(** The non-uniform parameters are a segment of the parameters. *)
Lemma ind_nn_le : forall D, ind_nn D <= ind_np D.
Proof. intros; unfold ind_nn; apply Nat.le_sub_l. Qed.

(** The environment of a branch extends the eliminator's by the
    non-uniform parameters, the arguments and the recursive results; the
    environment of the motive's instance at a neutral, by the non-uniform
    parameters and the neutral. *)
Lemma ind_branch_args_length : forall {A} D (gs : list carg) (vs ihs : list A),
    List.length vs = ind_np D + List.length gs ->
    List.length (skipn (ind_nu D) (firstn (ind_np D) vs) ++ skipn (ind_np D) vs ++ ihs) =
      ind_nn D + List.length gs + List.length ihs.
Proof.
  intros * H; rewrite !length_app, !length_skipn, length_firstn, Nat.min_l by lia.
  unfold ind_nn; lia.
Qed.

Lemma ind_motive_args_length : forall {A} D (as' : list A) x,
    List.length as' = ind_np D ->
    List.length (skipn (ind_nu D) as' ++ x :: nil) = S (ind_nn D).
Proof. intros * H; rewrite length_app, length_skipn; cbn; unfold ind_nn; lia. Qed.

(** The telescope of the non-uniform parameters, outermost first. *)
Lemma ind_nn_tele_length : forall D, List.length (List.rev (List.firstn (ind_nn D) (ind_params D))) = ind_nn D.
Proof.
  intros; rewrite length_rev, length_firstn, Nat.min_l; [ reflexivity |].
  pose proof (ind_nn_le D); unfold ind_np in *; lia.
Qed.

(** ** The Types of a Declaration

    What typing reads off a declaration [D] of the type at [p]: the types of
    the type former and of the constructors, the contexts of the motive and
    of the branches of the eliminator, and the instances of telescopes at
    lists of terms.  All are built once, by typing; evaluation and readback
    use the declaration directly.

    The parameters [ind_params D] are a closed context, innermost first: the
    non-uniform ones, [ind_nn D] of them, are the innermost.  The sort is in
    the context of the uniform ones. *)

Import Sub_Notations Wk_Notations.

(** The substitution sending the innermost binders to the terms [Ms],
    outermost first, and the others as [σ] does. *)
Fixpoint sb_of_list (σ : sub) (Ms : list exp) : sub :=
  match Ms with
  | nil => σ
  | M :: Ms' => sb_of_list (σ ,, M) Ms'
  end.

(** The type of the type former applied to [Us], its outermost
    parameters: the [Π] over the others, at [Us]. *)
Definition ind_ty_at (D : ind_decl) (Us : list exp) : typ :=
  (ctx_pi (List.firstn (ind_np D - List.length Us) (ind_params D)) (ind_sort D)[wk_shiftn (ind_nn D)]ʷ)[sb_of_list Id Us].

(** The variables [#(k + n - 1)], …, [#k], outermost first. *)
Definition vars_from (k n : nat) : list exp := List.map (fun i => a_var (k + i)) (List.rev (List.seq 0 n)).

(** The parameters, and the uniform ones, as variables, under [k] more
    binders. *)
Definition ind_pvars (D : ind_decl) (k : nat) : list exp := vars_from k (ind_np D).
Definition ind_uvars (D : ind_decl) (k : nat) : list exp := vars_from (k + ind_nn D) (ind_nu D).


(** The type of the type former: a [Π] over all the parameters of the sort. *)
Definition ind_ty (D : ind_decl) : typ := ctx_pi (ind_params D) (ind_sort D)[wk_shiftn (ind_nn D)]ʷ.

(** The types of the non-recursive arguments of a constructor are in the
    context of the non-recursive arguments before them: a recursive argument
    is not a binder for them ([cargs_strat]).  [wk_pat pat] sends that
    context into the one of all the arguments before, where [pat] tells,
    innermost first, which of them are recursive. *)
Fixpoint wk_pat (pat : list bool) : wk :=
  match pat with
  | nil => fun x => x
  | false :: pat' => wk_q (wk_pat pat')
  | true :: pat' => wk_compose (wk_pat pat') wk_shift
  end.

Fixpoint cargs_strat (gs : list carg) : ctx :=
  match gs with
  | nil => nil
  | ca_arg A :: gs' => cargs_strat gs' ++ ce_ass A :: nil
  | ca_rec _ :: gs' => cargs_strat gs'
  end.

(** ** Shapes

    A shape [pt_pi B1 (pt_pi B2 … (pt_self 0 Ps))] is a function from its
    domains [B1], [B2], …, each over the ones before it, into the type at
    the non-uniform parameters [Ps], over all its domains.  Its domains,
    outermost first, and as a telescope, innermost first. *)
Fixpoint ptyp_doms {E : Set} (t : ptyp_g E) : list E :=
  match t with
  | pt_pi A t => A :: ptyp_doms t
  | _ => nil
  end.

Definition doms_ctx (Bs : list exp) : ctx := List.rev (List.map ce_ass Bs).
Definition ptyp_tele (t : ptyp) : ctx := doms_ctx (ptyp_doms t).
Definition ptyp_depth (t : ptyp) : nat := List.length (ptyp_doms t).

(** The shape of each recursive argument among [gs] ends at [nn]
    parameters. *)
Definition cargs_plen (nn : nat) (gs : list carg) : Prop :=
  forall gs1 t gs2, gs = gs1 ++ ca_rec t :: gs2 -> List.length (ptyp_ps t) = nn.

(** The pattern of the arguments [gs] of a constructor, innermost first:
    [true] at a recursive one. *)
Definition cargs_pat (gs : list carg) : list bool :=
  List.rev (List.map (fun g => match g with ca_rec _ => true | ca_arg _ => false end) gs).

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

(** Stage A′ has one type per block and no nesting: a shape ends in
    [pt_self 0]. *)
Fixpoint ptyp_simple {E : Set} (t : ptyp_g E) : bool :=
  match t with
  | pt_self 0 _ => true
  | pt_pi _ t => ptyp_simple t
  | _ => false
  end.

(** The type of a recursive argument of shape [t], in the context of all
    the arguments before it and the parameters, its components over the
    non-recursive arguments before it ([pat], innermost first, tells which
    of those before it are recursive): the [Π] over the domains of the type
    at the uniform parameters and the shape's non-uniform ones.  Under a
    domain the components are over one more variable, which is no recursive
    argument. *)
Fixpoint ptyp_ty (p : qname) (D : ind_decl) (pat : list bool) (t : ptyp) : typ :=
  match t with
  | pt_pi A t => a_pi A[wk_pat pat]ʷ (ptyp_ty p D (false :: pat) t)
  | _ => apps (a_ind p) (ind_uvars D (List.length pat) ++ List.map (fun P => P[wk_pat pat]ʷ) (ptyp_ps t))
  end.

(** The arguments of a constructor as a context over the parameters,
    innermost first: a recursive one is of the type of its shape. *)
Fixpoint cargs_ctx_aux (p : qname) (D : ind_decl) (pat : list bool) (gs : list carg) : ctx :=
  match gs with
  | nil => nil
  | ca_arg A :: gs' => cargs_ctx_aux p D (false :: pat) gs' ++ ce_ass A[wk_pat pat]ʷ :: nil
  | ca_rec t :: gs' => cargs_ctx_aux p D (true :: pat) gs' ++ ce_ass (ptyp_ty p D pat t) :: nil
  end.

Definition cargs_ctx (p : qname) (D : ind_decl) (gs : list carg) : ctx := cargs_ctx_aux p D nil gs.

(** The type of a constructor: a [Π] over the parameters and the
    arguments of the type at the parameters. *)
Definition con_ty (p : qname) (D : ind_decl) (gs : list carg) : typ :=
  ctx_pi (ind_params D) (ctx_pi (cargs_ctx p D gs) (apps (a_ind p) (ind_pvars D (List.length gs)))).

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

    The motive is in the context of the non-uniform parameters, at the
    uniform ones [Us], and of the scrutinee. *)
Definition elim_mctx (p : qname) (D : ind_decl) (Us : list exp) : ctx :=
  ce_ass (apps (a_ind p) (List.map (fun U => U[wk_shiftn (ind_nn D)]ʷ) Us ++ vars_from 0 (ind_nn D)))
  :: tele_sub (ind_nparams D) (sb_of_list Id Us).

(** The type of an argument of shape [t], its components moved by [σ], at
    the uniform parameters [Us]: [ptyp_ty] at an instance of the parameters
    and the arguments before. *)
Fixpoint ptyp_ty_at (p : qname) (Us : list exp) (σ : sub) (t : ptyp) : typ :=
  match t with
  | pt_pi B t => a_pi B[σ] (ptyp_ty_at p (List.map (fun U => U[wk_shift]ʷ) Us) (sb_q σ) t)
  | _ => apps (a_ind p) (Us ++ List.map (fun P => P[σ]) (ptyp_ps t))
  end.

(** The type of the recursive result of an argument [x] of shape [t]: the
    motive [A] at the shape's non-uniform parameters and [x], under the
    shape's domains, at which [x] is applied.  The motive's context, the
    eliminator's, is moved by [β], the shape's components by [σ]. *)
Fixpoint ptyp_ihty (A : exp) (β σ : sub) (x : exp) (t : ptyp) : typ :=
  match t with
  | pt_pi B t => a_pi B[σ] (ptyp_ihty A (β ⨟ sb_of_wk wk_shift) (sb_q σ) (a_app x[wk_shift]ʷ (a_var 0)) t)
  | _ => A[sb_of_list β (List.map (fun P => P[σ]) (ptyp_ps t) ++ x :: nil)]
  end.

(** The recursive results of a constructor's arguments: the motive [A] at
    each recursive argument and the non-uniform parameters it is declared
    at.  [i] arguments of [gs] and [j] results come before; [na] is the
    number of all the arguments.  [ihs_sub] moves a shape's components from
    the context of the non-recursive arguments before it and the
    parameters to the branch's: past the recursive arguments before it, the
    uniform parameters instantiated by [Us], past the arguments after it
    and the results before it. *)
Definition ihs_sub (D : ind_decl) (Us : list exp) (na : nat) (pat : list bool) (j : nat) : sub :=
  (sb_of_wk (wk_pat pat) ⨟ sb_qn (List.length pat + ind_nn D) (sb_of_list Id Us))
    ⨟ sb_of_wk (wk_shiftn (na - List.length pat + j)).

Fixpoint ihs_ctx_aux (D : ind_decl) (A : exp) (Us : list exp) (na : nat)
    (pat : list bool) (j : nat) (gs : list carg) : ctx :=
  match gs with
  | nil => nil
  | ca_arg _ :: gs' => ihs_ctx_aux D A Us na (false :: pat) j gs'
  | ca_rec t :: gs' =>
      ihs_ctx_aux D A Us na (true :: pat) (S j) gs' ++
        ce_ass (ptyp_ihty A (sb_of_wk (wk_shiftn (j + na + ind_nn D))) (ihs_sub D Us na pat j)
                  (a_var (j + na - 1 - List.length pat)) t) :: nil
  end.

(** The context of the branch of a constructor with arguments [gs]: the
    non-uniform parameters, the arguments and the recursive results. *)
Definition elim_bctx (p : qname) (D : ind_decl) (gs : list carg) (A : exp) (Us : list exp) : ctx :=
  ihs_ctx_aux D A Us (List.length gs) nil 0 gs ++
  tele_sub (cargs_ctx p D gs) (sb_qn (ind_nn D) (sb_of_list Id Us)) ++
  tele_sub (ind_nparams D) (sb_of_list Id Us).

(** The type of the branch: the motive at the constructor applied to the
    parameters and the arguments. *)
Definition elim_bty (p : qname) (D : ind_decl) (c : string) (gs : list carg) (A : exp) (Us : list exp) : typ :=
  let na := List.length gs in
  let n := (ind_nn D + na + cargs_nrec gs)%nat in
  A[sb_of_list (sb_of_wk (wk_shiftn n))
      (vars_from (cargs_nrec gs + na) (ind_nn D) ++
       apps (a_con p c) (List.map (fun U => U[wk_shiftn n]ʷ) Us ++
                         vars_from (cargs_nrec gs + na) (ind_nn D) ++ vars_from (cargs_nrec gs) na) :: nil)].

(** The branches under [φ], each under the binders it has: what
    weakening does to the branches of an eliminator. *)
Definition brs_wk (Bs : list (string * nat * exp)) (φ : wk) : list (string * nat * exp) :=
  List.map (fun b => (fst b, (snd b)[wk_qn (snd (fst b)) φ]ʷ)) Bs.

(** The recursive result of an argument [M] of shape [t], as an
    elimination: under the shape's domains, moved by [σ], the eliminator at
    [M] applied to them. *)
Fixpoint ptyp_ih (nm : nat) (A : exp) (Bs : list (string * nat * exp)) (σ : sub) (M : exp) (t : ptyp) : exp :=
  match t with
  | pt_pi B t => a_fn B[σ] (ptyp_ih nm A[wk_qn nm wk_shift]ʷ (brs_wk Bs wk_shift) (sb_q σ) (a_app M[wk_shift]ʷ (a_var 0)) t)
  | _ => a_elim nm A Bs M
  end.

(** The recursive results of the arguments [As] of a constructor, as
    eliminations; [σ] instantiates the parameters and the non-recursive
    arguments before, which the shapes' domains are over. *)
Fixpoint elim_ihs (nm : nat) (A : exp) (Bs : list (string * nat * exp)) (σ : sub) (gs : list carg) (As : list exp) : list exp :=
  match gs, As with
  | ca_arg _ :: gs', N :: As' => elim_ihs nm A Bs (σ ,, N) gs' As'
  | ca_rec t :: gs', M :: As' => ptyp_ih nm A Bs σ M t :: elim_ihs nm A Bs σ gs' As'
  | _, _ => nil
  end.

(** The branches are in the order of the constructors. *)
Definition brs_names (cs : list (string * list carg)) (Bs : list (string * nat * exp)) : Prop :=
  List.map fst cs = List.map (fun b => fst (fst b)) Bs.

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

Fixpoint exp_mvc (n : nat) (M : exp) : Prop :=
  match M with
  | a_typ _ | a_level _ | a_llit _ | a_nat | a_zero | a_True | a_true | a_False => True
  | a_succ M | a_succl M | a_univ M => exp_mvc n M
  | a_maxl M N => exp_mvc n M /\ exp_mvc n N
  | a_natrec A MZ MS M =>
      exp_mvc (S n) A /\ exp_mvc n MZ /\ exp_mvc (S (S n)) MS /\ exp_mvc n M
  | a_exfalso A M => exp_mvc (S n) A /\ exp_mvc n M
  | a_ind _ | a_con _ _ | a_nlit _ => True
  | a_elim nm A Bs M => exp_mvc (nm + n) A /\ all_brs (fun k B => exp_mvc (k + n) B) Bs /\ exp_mvc n M
  | a_pi A B | a_fn A B => exp_mvc n A /\ exp_mvc (S n) B
  | a_app M N => exp_mvc n M /\ exp_mvc n N
  | a_var _ => True
  | a_let b B => bnd_mvc n b /\ exp_mvc (S n) B
  | a_mem H _ => modexp_mvc n H
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
  | md_body Φ => gmod_mvc n Φ
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
  | ge_ind _ D Φ => gmod_mvc (ind_nu D + n) Φ
  | ge_ind_alias _ _ _ _ => True
  end
with centry_mvc (n : nat) (e : centry) : Prop :=
  match e with
  | ce_ass A => exp_mvc n A
  | ce_def A M => exp_mvc n A /\ exp_mvc n M
  | ce_mod U => gunit_mvc n U
  end.



(** A telescope whose types have no free module variable. *)
Definition ctx_mvc (Δ : ctx) : Prop := List.Forall (centry_mvc 0) Δ.

(** A declaration whose parameters' types, sort and constructors' argument
    types have no free module variable. *)
Definition carg_mvc (g : carg) : Prop :=
  match g with
  | ca_arg A => exp_mvc 0 A
  | ca_rec t => List.Forall (exp_mvc 0) (ptyp_doms t) /\ List.Forall (exp_mvc 0) (ptyp_ps t)
  end.

Definition decl_mvc (D : ind_decl) : Prop :=
  ctx_mvc (ind_params D) /\ exp_mvc 0 (ind_sort D) /\
  (forall c gs, In (c, gs) (ind_cons D) -> List.Forall carg_mvc gs).

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

Lemma length_cargs_ctx_aux : forall p D gs pat, List.length (cargs_ctx_aux p D pat gs) = List.length gs.
Proof. induction gs as [| [] gs IH]; intros; cbn; rewrite ?length_app, ?IH; cbn; lia. Qed.

Lemma length_cargs_ctx : forall p D gs, List.length (cargs_ctx p D gs) = List.length gs.
Proof. intros; apply length_cargs_ctx_aux. Qed.

Lemma length_ihs_ctx_aux : forall D A Us na gs pat j,
    List.length (ihs_ctx_aux D A Us na pat j gs) = cargs_nrec gs.
Proof. induction gs as [| [] gs IH]; intros; cbn; rewrite ?length_app, ?IH; cbn; lia. Qed.

Lemma length_nparams : forall D, List.length (ind_nparams D) = ind_nn D.
Proof. intros; unfold ind_nparams, ind_nn, ind_np; rewrite length_firstn; lia. Qed.

Lemma length_elim_mctx : forall p D Us, List.length (elim_mctx p D Us) = S (ind_nn D).
Proof. intros; unfold elim_mctx; cbn; rewrite length_tele_sub, length_nparams; reflexivity. Qed.

Lemma length_elim_bctx : forall p D gs A Us,
    List.length (elim_bctx p D gs A Us) = (cargs_nrec gs + List.length gs + ind_nn D)%nat.
Proof.
  intros; unfold elim_bctx; rewrite !length_app, length_ihs_ctx_aux, !length_tele_sub, length_cargs_ctx, length_nparams.
  lia.
Qed.

Lemma length_elim_ihs : forall nm A Bs σ gs As,
    List.length As = List.length gs -> List.length (elim_ihs nm A Bs σ gs As) = cargs_nrec gs.
Proof.
  intros nm A Bs σ gs; revert σ.
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

Lemma cargs_ctx_aux_ass : forall p D gs pat, List.Forall (fun e => exists A, e = ce_ass A) (cargs_ctx_aux p D pat gs).
Proof.
  induction gs as [| [] gs IH]; intros; cbn; [ constructor | |]; apply List.Forall_app; split; eauto.
Qed.
