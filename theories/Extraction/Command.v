(** * Running Commands

    The executable for [Core.Syntactic.System.Command].  It is sound by
    construction, since every result carries its [post_*], and complete by
    [run_impl_complete].

    A run maintains:

    - one [Θ] for the whole program, in which every loaded unit is filed once;
    - a table [K] giving the closure of each filed unit, that is, the paths
      of the state its own run ended in;
    - for the unit being run, the closure [D] of what it has imported so far.

    A unit is checked against [gds_restrict D Θ], which [equiv_restrict]
    relates to the judgment's state by weakening in both directions.  Loading
    recurses on the accessibility of the import chain ([load_step]).

    Each command is filled ([Extraction.TypedElab]: its literals, its
    eliminators' groups, its accesses through terms) and runs: the local
    opens of its bodies are checked where they stand.

    A run also logs each [eval] it checked, with its normal form
    ([eval_entry], certified by [eval_ok]), and fails with a [run_error]
    carrying the terms involved. *)

From Stdlib Require Import List String Wellfounded Wf_nat Lia.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base Soundness.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import Structural Command.
From Mctt.Core Require Import TypedElab.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf Paths LookupSound.
From Mctt.Core.Syntactic.System.Inductives Require Import IndRuns Runs.
From Mctt.Core.Syntactic.Inductives Require Import IndCong.
From Mctt.Extraction Require Import Lookup NbE TypeCheck GlobalCheck IndDecl RecordDecl MemberType Opens Privacy.
From Mctt.Extraction Require Import MdefGroup TypedElab.
Import Syntax_Notations GlobalCtx_Notations.

Local Open Scope string_scope.

(** ** Deciders

    [opt_case] is in [MdefGroup]. *)

Definition list_case {A} (l : list A) : {x : A & {l' | l = x :: l'}} + {l = nil} :=
  match l as l0 return {x : A & {l' | l0 = x :: l'}} + {l0 = nil} with
  | x :: l' => inleft (existT _ x (exist _ l' eq_refl))
  | nil => inright eq_refl
  end.

Definition gs_fresh_dec (x : string) (Ξ : gstack) : {gs_fresh x Ξ} + {~ gs_fresh x Ξ} :=
  match Ξ as Ξ0 return {gs_fresh x Ξ0} + {~ gs_fresh x Ξ0} with
  | (_, _, U) :: _ => check_gm_fresh x (gu_mod U)
  | nil => right (fun H => H)
  end.

(** The member of a group, with its index. *)
Definition member_case (D : ind_decl) (k : nat) : {Mk | ind_member D k = Some Mk} + {ind_member D k = None} :=
  opt_case (ind_member D k).

(** A normal type is the [Π] over its domains ([nf_pi_tele]), a telescope
    of assumptions, of its codomain. *)
Lemma nf_pi_tele_spec : forall W Ds C, nf_pi_tele W = (Ds, C) -> nf_to_exp W = ctx_pi Ds (nf_to_exp C) /\ tele_ass Ds.
Proof.
  induction W; intros * E; cbn [nf_pi_tele] in E;
    try (injection E as <- <-; split; [ reflexivity | constructor ]).
  destruct (nf_pi_tele W2) as [Ds' C'] eqn:E2; injection E as <- <-.
  destruct (IHW2 _ _ eq_refl) as [HW Ha].
  cbn [nf_to_exp]; rewrite ctx_pi_snoc, <- HW; split; [ reflexivity |].
  apply List.Forall_app; split; [ exact Ha | constructor; [ eexists; reflexivity | constructor ] ].
Qed.

(** A term of a normal type, at the variables of the type's domains, is of
    its codomain past them. *)
Lemma applied_vars_typed : forall Θ Ξ Γ M W Ds C, Θ ⍮ Ξ ⍮ Γ ⊢ M : nf_to_exp W -> nf_pi_tele W = (Ds, C) ->
    Θ ⍮ Ξ ⍮ Ds ++ Γ ⊢ exp_applied_to_vars M (List.length Ds) : nf_to_exp C.
Proof.
  intros * HM Ep; destruct (nf_pi_tele_spec _ _ _ Ep) as [HW Ha]; rewrite HW in HM.
  destruct (presup_exp_typ HM) as [i HT].
  pose proof (ctx_pi_inv_outer _ _ _ _ Ha HT) as HC.
  exact (wf_apps_vars _ _ _ _ _ _ _ Ha (presup_exp_ctx HC) HC HM).
Qed.

(** Whether a normal type is a universe. *)
Definition nf_is_universe_dec (W : nf) : {nf_is_universe W} + {~ nf_is_universe W} :=
  match W as W0 return {nf_is_universe W0} + {~ nf_is_universe W0} with
  | nf_typ _ => left I
  | nf_univ _ _ => left I
  | _ => right (fun H => H)
  end.

(** ** Closures and Paths *)

(** For each filed unit, the units its run filed, and the record of builtin
    bindings it ended with. *)
Definition kmap : Set := list (path * (list path * builtins)).

Equations kfind (K : kmap) (fp : path) : option (list path) by struct K :=
| nil, _ => None
| (fq, (D, _)) :: K', fp => if path_beq fp fq then Some D else kfind K' fp.

Equations kbt (K : kmap) (fp : path) : option builtins by struct K :=
| nil, _ => None
| (fq, (_, B)) :: K', fp => if path_beq fp fq then Some B else kbt K' fp.

Definition p_union (A B : list path) : list path :=
  fold_right (fun x acc => if in_dec path_eq_dec x acc then acc else x :: acc) A B.

Lemma p_union_iff : forall A B x, In x (p_union A B) <-> In x A \/ In x B.
Proof.
  intros A B; unfold p_union; induction B as [| y B IH]; intros x; cbn [fold_right In]; [ tauto |].
  destruct (in_dec path_eq_dec y _) as [Hy | Hy]; rewrite IH in *; cbn [In]; rewrite ?IH.
  - split; [ tauto | intros [H | [<- | H]]; tauto ].
  - tauto.
Qed.

(** The chain up to the unit imported again, where the cycle starts. *)
Equations chain_to (fp : path) (ch : list path) : list path by struct ch :=
| _, nil => nil
| fp, fq :: ch' => if path_beq fp fq then fq :: nil else fq :: chain_to fp ch'.

(** The cycle, from the unit imported again back to itself. *)
Definition cycle_chain (fp : path) (ch : list path) : list path :=
  List.app (rev (chain_to fp ch)) (fp :: nil).

(** ** Results

    The errors a run can fail with, carrying the terms involved, if any, for
    the driver to print.  The message of [run_error_unit] concerns the unit at the
    path it carries and does not repeat that path. *)

Inductive run_error : Set :=
| run_error_msg : string -> run_error
(** The body of a definition is not of its declared type, which is a type. *)
| run_error_def : string -> gstack -> typ -> exp -> run_error
(** The declared type of a definition with a body is not a type. *)
| run_error_def_typ : string -> gstack -> typ -> run_error
(** An ascribed eval: the term is not of its ascription, which is a type. *)
| run_error_eval_check : gstack -> exp -> typ -> run_error
(** An ascribed eval: the ascription of the term is not a type. *)
| run_error_eval_typ : gstack -> exp -> typ -> run_error
| run_error_eval_infer : gstack -> exp -> run_error
(** A small universe [Type@{t}] whose level [t] is of no type of levels,
    found by [find_level_blame] where a type or a telescope is rejected:
    [t] lives in the context the stack's telescope is extended by, innermost
    entry first. *)
| run_error_level : gstack -> ctx -> exp -> run_error
| run_error_cycle : list path -> run_error
| run_error_unit : path -> string -> run_error
(** A private member, named by its module, reached from outside it. *)
| run_error_private : qname -> string -> run_error
(** A member [y] selected from a term whose type infers to nothing:
    [run_error_access_no_type Ξ ox Γ M y], [M] in the context [Γ] the stack's
    telescope is extended by, innermost entry first ([TypedElab]), in
    the command declaring [ox], if it declares a name, so that the printer
    can name the binders it declares. *)
| run_error_access_no_type : gstack -> option string -> ctx -> exp -> string -> run_error
(** A member [y] selected from a term whose inferred type [A] is no record
    type: [run_error_access_not_record Ξ ox Γ M A y], [M] and [A] in the context
    [Γ] the stack's telescope is extended by, in the command declaring
    [ox]. *)
| run_error_access_not_record : gstack -> option string -> ctx -> exp -> typ -> string -> run_error
(** A member selected from a value of the record [p] that the record's
    module does not have: neither a field nor a member of its with-area. *)
| run_error_record_member : qname -> string -> run_error
(** A record type applied past its parameters, to a value, where a term
    stands: [run_error_record_value_term Ξ ox Γ M n], [M] the record type
    applied, its first [n] arguments the parameters, in the context [Γ]
    the stack's telescope is extended by, in the command declaring
    [ox].  It is the module of the value, not a term. *)
| run_error_record_value_term : gstack -> option string -> ctx -> exp -> nat -> run_error
(** A record value whose fields are not the record's in order: the record,
    its fields, then the field given where the other was due. *)
| run_error_record_fields_order : qname -> list string -> string -> string -> run_error
(** A record value with a field its record does not have *)
| run_error_record_field_unknown : qname -> string -> run_error
(** A record value without a field of its record *)
| run_error_record_field_missing : qname -> string -> run_error
(** A field of a record value whose value is not of the field's type:
    [run_error_record_field Ξ ox Γ p f M U], the field [f] of the record [p], its
    value [M], and the type [U] it is due at, the field's declared type at
    the record's parameters and the values of the fields before it, in
    normal form; [M] and [U] in the context [Γ] the stack's telescope is
    extended by, innermost entry first, in the command declaring [ox]
    ([field_value_blame]). *)
| run_error_record_field : gstack -> option string -> ctx -> qname -> string -> exp -> typ -> run_error
(** A private entry of a local body, by the chain of submodules from the
    local module, reached from outside it. *)
| run_error_private_local : list string -> string -> run_error
(** An open that generates nothing ([Opens]). *)
| run_error_import : xerr -> run_error
(** The argument [y] of the constructor [c] of the type [x] has [x] in an
    argument of another inductive type, its head. *)
| run_error_nested : string -> string -> string -> exp -> run_error
(** The non-uniform parameter at a position (outermost [0]) of the type
    [x]: its type is not in the sort; both live in the context. *)
| run_error_ind_npar : string -> nat -> ctx -> typ -> typ -> run_error
(** A chain from a unit, in term position, that names a module (an alias
    of the module of an inductive type included), not a term. *)
| run_error_mod_term : qname -> run_error
(** A path that names no inductive type where one is wanted. *)
| run_error_not_ind : qname -> run_error
(** A literal, a numeral or the token [ℕ], with no natural-number type
    bound ([Builtin]). *)
| run_error_lit : lerr -> run_error
(** A branch of an eliminator that binds [n] names where its constructor
    needs [k] non-uniform parameters, [a] arguments and [r] recursive
    results: [run_error_branch_arity c n k a r]. *)
| run_error_branch_arity : string -> nat -> nat -> nat -> nat -> run_error
(** A branch for no constructor of the eliminated type. *)
| run_error_branch_unknown : string -> run_error
(** A constructor with no branch, or with two. *)
| run_error_branch_missing : string -> run_error
| run_error_branch_dup : string -> run_error
(** Branches, one per constructor, not in the order [cs] of the
    constructors. *)
| run_error_branch_order : list string -> run_error
(** A mutual definition with another number of functions than its group
    has members: [run_error_mdef_count n m], [n] members and [m] functions. *)
| run_error_mdef_count : nat -> nat -> run_error
(** A function of a mutual definition with another number of non-uniform
    parameters than its member: [run_error_mdef_nparams f m n], [f] with [m], its
    member with [n]. *)
| run_error_mdef_nparams : string -> nat -> nat -> run_error
(** The scrutinee of an eliminator, in its context under the stack's
    telescope, whose type is not inferred ([None]) or is no inductive
    type ([Some A]): [run_error_elim_scrutinee Ξ ox Γ M oA], in the command
    declaring [ox], if it declares a name, so that the printer can name
    the binders it declares. *)
| run_error_elim_scrutinee : gstack -> option string -> ctx -> exp -> option typ -> run_error
(** An eliminator, in its context under the stack's telescope, no reading
    of which, own or view, fits its blocks: [run_error_elim_no_group Ξ Γ E], [E]
    the eliminator, its scrutinee filled. *)
| run_error_elim_no_group : gstack -> ctx -> exp -> run_error
(** An eliminator, in its context under the stack's telescope, several
    readings of which fit its blocks: [run_error_elim_ambiguous Ξ Γ E rs], [E]
    the eliminator, its scrutinee filled, [rs] the readings, each its
    group and its uniform parameters. *)
| run_error_elim_ambiguous : gstack -> ctx -> exp -> list (qname * list exp) -> run_error
(** An eliminator of a group whose blocks are not one per member in the
    member order, in its context under the stack's telescope:
    [run_error_elim_blocks Ξ Γ E ks is j], [E] the eliminator, [ks] the members
    with no block, [is] the positions of the written blocks that are for
    no member left ([elim_blocks_blame]), and [j] the member of the block
    marked [at], for the printer's skeleton of the eliminator.  Both lists
    are empty when every member has its block, out of order. *)
| run_error_elim_blocks : gstack -> ctx -> exp -> list nat -> list nat -> nat -> run_error
(** A view of the group being declared, an instance of a container met in
    the arguments, rejected: the group's first member, the instance, and
    why ([view_why]). *)
| run_error_view : string -> rview -> view_why -> run_error
(** An error, with the state it occurred in, for the printer: the units
    imported, the stack, and the natural numbers bound there, their type
    and constructors as [nat_view] gives them. *)
| run_error_nat : gdeps -> gstack -> option (qname * string * string) -> run_error -> run_error.

Definition priv_error (e : priv_err) : run_error :=
  match e with
  | priv_err_global qd x => run_error_private qd x
  | priv_err_local ch x => run_error_private_local ch x
  end.

(** The error for a rejected type or telescope: the blamed level if
    [find_level_blame] found one, otherwise the given error. *)
Definition blame_error {Θ Ξ Γ} (b : option (level_blame Θ Ξ Γ)) (e : run_error) : run_error :=
  match b with
  | Some (exist _ (Δ, t) _) => run_error_level Ξ Δ t
  | None => e
  end.

(** Where a term is rejected, a chain from a unit in it that names a
    module but stands where a term does: found syntactically, whether the
    chains name modules asked of the global context ([gc_module]), which
    does not read the local context for them, and whether they name a
    definition with a module part, which is a term too ([gc_entry]). *)
Section ModBlame.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** The head of a module expression applied. *)
  Fixpoint mod_head (H : modexp) : modexp :=
    match H with
    | me_app H' _ => mod_head H'
    | _ => H
    end.

  (** A member [x] of a module expression: a module named where a term
      stands, not the module of a member of a group of inductive types, a
      record type nor a definition with a module part, which are terms
      too; or a member of the module of a record value that the record's
      module does not have. *)
  Definition mod_term_blame (H : modexp) (x : string) : option run_error :=
    match mod_qname H with
    | Some mp =>
        match gc_module Θ Ξ (qname_app mp (x :: nil)), gc_entry Θ Ξ (qname_app mp (x :: nil)),
              ind_mlookup Θ Ξ (qname_app mp (x :: nil)), record_lookup Θ Ξ (qname_app mp (x :: nil)) with
        | Some _, Some (ge_def_mod _ _ _ _), _, _ => None
        | Some _, _, None, None => Some (run_error_mod_term (qname_app mp (x :: nil)))
        | _, _, _, _ => None
        end
    | None =>
        match H, mod_qname (mod_head H) with
        | me_app _ _, Some p =>
            match record_lookup Θ Ξ p, gc_resolve Θ Ξ (qname_app p (x :: nil)) with
            | Some _, None => Some (run_error_record_member p x)
            | _, _ => None
            end
        | _, _ => None
        end
    end.

  Definition first_some {X} (a : option X) (b : unit -> option X) : option X :=
    match a with Some _ => a | None => b tt end.

  Fixpoint mod_blame (M : exp) : option run_error :=
    match M with
    | a_succl M | a_univ M => mod_blame M
    | a_maxl M N | a_pi M N | a_fn M N | a_app M N => first_some (mod_blame M) (fun _ => mod_blame N)
    | a_exfalso A M => first_some (mod_blame M) (fun _ => mod_blame A)
    | a_elim _ Us _ Bks M =>
        first_some (mod_blame M) (fun _ => first_some
          ((fix exps (Us : list exp) : option run_error :=
              match Us with
              | nil => None
              | U :: Us' => first_some (mod_blame U) (fun _ => exps Us')
              end) Us)
          (fun _ => (fix blocks (Bks : list eblock) : option run_error :=
              match Bks with
              | nil => None
              | eb_mk _ oZ A Bs :: Bks' =>
                  first_some (match oZ with Some Z => mod_blame Z | None => None end)
                    (fun _ => first_some (mod_blame A) (fun _ => first_some
                      ((fix brs (Bs : list (string * nat * exp)) : option run_error :=
                          match Bs with
                          | nil => None
                          | b :: Bs' => first_some (mod_blame (snd b)) (fun _ => brs Bs')
                          end) Bs)
                      (fun _ => blocks Bks')))
              end) Bks))
    | a_let (b_def oA N) B =>
        first_some (match oA with Some A => mod_blame A | None => None end)
          (fun _ => first_some (mod_blame N) (fun _ => mod_blame B))
    | a_let (b_mod _) B => mod_blame B
    | a_mem H x => mod_term_blame H x
    | _ => None
    end.
End ModBlame.

(** A binder of a term a message is read in, whose type the message does
    not read: only the depth matters, for the printer to name the binders. *)
Definition unread_binder : centry := ce_ass a_True.

(** [n] such binders. *)
Definition unread_binders (n : nat) : ctx := List.repeat unread_binder n.

(** Where a term is rejected, a block of an eliminator whose branches do
    not match the constructors of the member it eliminates.  The member is
    read off the names of the branches: every member of a group of the
    global context that has a constructor of each branch's name, and the
    error is reported when all of them give the same one.  This only
    chooses the message. *)
Section BranchBlame.
  (** The groups filed in a module, its submodules' included: one per
      entry of a declared member, so a group may be listed more than
      once. *)
  Fixpoint gmod_inds (Φ : gmod) : list ind_decl :=
    match Φ with
    | gm_nil => nil
    | gm_ext Φ _ E =>
        match E with
        | ge_ind _ _ _ D Φi => D :: gmod_inds Φi
        | ge_mod _ (gu_mk _ (md_body sm Φi)) => gmod_inds Φi
        | _ => nil
        end ++ gmod_inds Φ
    | gm_open Φ _ _ => gmod_inds Φ
    end.

  (** The groups of the filed units and of the stack. *)
  Definition ctx_inds (Θ : gdeps) (Ξ : gstack) : list ind_decl :=
    flat_map (fun e => gmod_inds (gu_mod (snd e))) Θ ++ flat_map (fun e => gmod_inds (gu_mod (snd e))) Ξ.

  (** The members of those groups. *)
  Definition ctx_members (Θ : gdeps) (Ξ : gstack) : list imember :=
    flat_map (@ind_members _ _) (ctx_inds Θ Ξ).

  Definition brs_has (Bs : list (string * nat * exp)) (c : string) : nat :=
    List.length (List.filter (fun b => String.eqb (fst (fst b)) c) Bs).

  Fixpoint strs_eqb (xs ys : list string) : bool :=
    match xs, ys with
    | nil, nil => true
    | x :: xs, y :: ys => andb (String.eqb x y) (strs_eqb xs ys)
    | _, _ => false
    end.

  (** The first mismatch of the branches [Bs] against the constructors of
      the member [Mk]: a branch's binders, then a constructor without a
      branch or with two, then the order of the branches. *)
  Definition branch_check (Mk : imember) (Bs : list (string * nat * exp)) : option run_error :=
    first_some (first_some
      ((fix go (Bs0 : list (string * nat * exp)) : option run_error :=
          match Bs0 with
          | nil => None
          | (c, n, _) :: Bs0' =>
              match ind_con Mk c with
              | Some gs =>
                  if Nat.eqb n (im_nn Mk + List.length gs + cargs_nrec gs) then go Bs0'
                  else Some (run_error_branch_arity c n (im_nn Mk) (List.length gs) (cargs_nrec gs))
              | None => Some (run_error_branch_unknown c)
              end
          end) Bs)
      (fun _ => (fix go (cs : list (string * list carg)) : option run_error :=
          match cs with
          | nil => None
          | (c, _) :: cs' =>
              match brs_has Bs c with
              | 0 => Some (run_error_branch_missing c)
              | 1 => go cs'
              | _ => Some (run_error_branch_dup c)
              end
          end) (im_cons Mk)))
      (fun _ =>
         if strs_eqb (List.map (fun b => fst (fst b)) Bs) (List.map fst (im_cons Mk)) then None
         else Some (run_error_branch_order (List.map fst (im_cons Mk)))).

  Definition run_error_eqb (e1 e2 : run_error) : bool :=
    match e1, e2 with
    | run_error_branch_arity c n k a r, run_error_branch_arity c' n' k' a' r' =>
        andb (String.eqb c c') (andb (Nat.eqb n n') (andb (Nat.eqb k k') (andb (Nat.eqb a a') (Nat.eqb r r'))))
    | run_error_branch_unknown c, run_error_branch_unknown c' => String.eqb c c'
    | run_error_branch_missing c, run_error_branch_missing c' => String.eqb c c'
    | run_error_branch_dup c, run_error_branch_dup c' => String.eqb c c'
    | run_error_branch_order cs, run_error_branch_order cs' => strs_eqb cs cs'
    | _, _ => false
    end.

  (** The mismatch of a block's branches [Bs], if every member they could
      be for gives the same one. *)
  Definition elim_blame (Θ : gdeps) (Ξ : gstack) (Bs : list (string * nat * exp)) : option run_error :=
    match Bs with
    | nil => None
    | _ =>
        let is_con Mk b := match ind_con Mk (fst (fst b)) with Some _ => true | None => false end in
        let cands :=
          match List.filter (fun Mk => forallb (is_con Mk) Bs) (ctx_members Θ Ξ) with
          | nil => List.filter (fun Mk => existsb (is_con Mk) Bs) (ctx_members Θ Ξ)
          | Ms => Ms
          end in
        match List.map (fun Mk => branch_check Mk Bs) cands with
        | Some e :: rs => if forallb (fun r => match r with Some e' => run_error_eqb e e' | None => false end) rs then Some e else None
        | _ => None
        end
    end.

  (** The first mismatch of a block's branches in a term, inside out. *)
  Fixpoint brs_blame (Θ : gdeps) (Ξ : gstack) (M : exp) : option run_error :=
    match M with
    | a_succl M | a_univ M => brs_blame Θ Ξ M
    | a_maxl M N | a_pi M N | a_fn M N | a_app M N => first_some (brs_blame Θ Ξ M) (fun _ => brs_blame Θ Ξ N)
    | a_exfalso A M => first_some (brs_blame Θ Ξ M) (fun _ => brs_blame Θ Ξ A)
    | a_elim _ Us _ Bks M =>
        first_some (brs_blame Θ Ξ M) (fun _ => first_some
          ((fix exps (Us : list exp) : option run_error :=
              match Us with
              | nil => None
              | U :: Us' => first_some (brs_blame Θ Ξ U) (fun _ => exps Us')
              end) Us)
          (fun _ => (fix blocks (Bks : list eblock) : option run_error :=
              match Bks with
              | nil => None
              | eb_mk _ oZ A Bs :: Bks' =>
                  first_some (match oZ with Some Z => brs_blame Θ Ξ Z | None => None end)
                    (fun _ => first_some (brs_blame Θ Ξ A) (fun _ => first_some (elim_blame Θ Ξ Bs)
                      (fun _ => first_some
                        ((fix brs (Bs : list (string * nat * exp)) : option run_error :=
                            match Bs with
                            | nil => None
                            | b :: Bs' => first_some (brs_blame Θ Ξ (snd b)) (fun _ => brs Bs')
                            end) Bs)
                        (fun _ => blocks Bks'))))
              end) Bks))
    | a_let (b_def oA N) B =>
        first_some (match oA with Some A => brs_blame Θ Ξ A | None => None end)
          (fun _ => first_some (brs_blame Θ Ξ N) (fun _ => brs_blame Θ Ξ B))
    | a_let (b_mod _) B => brs_blame Θ Ξ B
    | _ => None
    end.
End BranchBlame.

(** Where a term is rejected, an eliminator of a group, its group known
    (filled, [Builtin.exp_fill]), that does not have one block per member
    of the group in the member order.  A written block is matched to a
    member by its branches, which name the member's constructors in order
    ([block_fits]); the blocks are matched in the order written, each to
    a member not matched yet, the first after the last one matched if
    there is one ([block_member]).  This only chooses the message. *)
Section BlocksBlame.
  Variables (Θ : gdeps) (Ξ : gstack).

  (** Whether the block [b] is for the member [Mk]: its branches are for
      [Mk]'s constructors, in order. *)
  Definition block_fits (Mk : imember) (b : eblock) : bool :=
    strs_eqb (List.map (fun br => fst (fst br)) (eb_brs b)) (List.map fst (im_cons Mk)).

  (** The member of [Ms] the block [b] is for, among those not [taken]:
      the first after the [last] one matched that it fits, else the first
      it fits. *)
  Definition block_member (Ms : list imember) (taken : list nat) (last : option nat) (b : eblock) : option nat :=
    let cands := List.filter (fun j => andb (negb (existsb (Nat.eqb j) taken))
                                   (match List.nth_error Ms j with Some Mk => block_fits Mk b | None => false end))
                   (List.seq 0 (List.length Ms)) in
    match List.filter (fun j => match last with Some l => Nat.ltb l j | None => true end) cands with
    | j :: _ => Some j
    | nil => List.hd_error cands
    end.

  (** The member each written block is for, in the order written. *)
  Fixpoint blocks_members (Ms : list imember) (taken : list nat) (last : option nat) (Bks : list eblock) : list (option nat) :=
    match Bks with
    | nil => nil
    | b :: Bks' =>
        match block_member Ms taken last b with
        | Some j => Some j :: blocks_members Ms (j :: taken) (Some j) Bks'
        | None => None :: blocks_members Ms taken last Bks'
        end
    end.

  (** The groups filed in a module, its submodules' included, each with
      its path, once per entry of a declared member. *)
  Fixpoint gmod_groups (Φ : gmod) : list qname :=
    match Φ with
    | gm_nil => nil
    | gm_ext Φ _ E =>
        match E with
        | ge_ind _ p _ _ Φi => p :: gmod_groups Φi
        | ge_mod _ (gu_mk _ (md_body sm Φi)) => gmod_groups Φi
        | _ => nil
        end ++ gmod_groups Φ
    | gm_open Φ _ _ => gmod_groups Φ
    end.

  (** The group of an eliminator: its own once filled; with none, the one
      group without uniform parameters, among those of the filed units and
      the stack, a member of which its block [m] is for.  That second case
      is a guess, a hint for the message only: it reads the branches'
      names, not the scrutinee's type, and is asked of a term already
      rejected, so it decides nothing about typing. *)
  Definition elim_group (oq : option qname) (m : nat) (Bks : list eblock) : option qname :=
    match oq with
    | Some p => Some p
    | None =>
        match List.nth_error Bks m with
        | None => None
        | Some b =>
            let ps := List.filter (fun p => match ind_lookup Θ Ξ p with
                                            | Some D => andb (Nat.eqb (ind_nu D) 0) (existsb (fun Mk => block_fits Mk b) (ind_members D))
                                            | None => false
                                            end)
                        (flat_map (fun e => gmod_groups (gu_mod (snd e))) Θ ++ flat_map (fun e => gmod_groups (gu_mod (snd e))) Ξ) in
            match ps with
            | p :: ps' => if forallb (fun p' => if qname_eq_dec p p' then true else false) ps' then Some p else None
            | nil => None
            end
        end
    end.

  (** The eliminator [E], in the context [Γ], if its blocks are too few or
      too many for its group, or one per member but out of order; the
      eliminator in the error has its group.  With as many blocks as
      members of which some match no member, the branches are to blame
      ([brs_blame]), not the blocks. *)
  Definition elim_blocks_check (Γ : ctx) (E : exp) : option run_error :=
    match E with
    | a_elim oq Us m Bks M0 =>
        match match elim_group oq m Bks with
              | Some p => option_map (fun D => (p, D)) (ind_lookup Θ Ξ p)
              | None => None
              end with
        | None => None
        | Some (p, D) =>
            let E := a_elim (Some p) Us m Bks M0 in
            let Ms := ind_members D in
            let a := blocks_members Ms nil None Bks in
            let missing :=
              List.filter (fun j => negb (existsb (fun o => match o with Some j' => Nat.eqb j j' | None => false end) a))
                (List.seq 0 (List.length Ms)) in
            let extra :=
              List.map snd (List.filter (fun x => match fst x with None => true | Some _ => false end)
                              (List.combine a (List.seq 0 (List.length Bks)))) in
            let j := match List.nth_error a m with Some (Some j) => j | _ => m end in
            let ordered :=
              forallb (fun x => match fst x with Some j' => Nat.eqb j' (snd x) | None => false end)
                (List.combine a (List.seq 0 (List.length Bks))) in
            if Nat.eqb (List.length Bks) (List.length Ms) then
              match missing, extra with
              | nil, nil => if ordered then None else Some (run_error_elim_blocks Ξ Γ E nil nil j)
              | _, _ => None
              end
            else Some (run_error_elim_blocks Ξ Γ E missing extra j)
        end
    | _ => None
    end.

  (** The first eliminator in a term, in the context [Γ] of its binders,
      whose blocks do not match its group: its parts first, then itself. *)
  Fixpoint blocks_blame (Γ : ctx) (M : exp) : option run_error :=
    match M with
    | a_succl M | a_univ M => blocks_blame Γ M
    | a_maxl M N | a_app M N => first_some (blocks_blame Γ M) (fun _ => blocks_blame Γ N)
    | a_pi A B | a_fn A B => first_some (blocks_blame Γ A) (fun _ => blocks_blame (ce_ass A :: Γ) B)
    | a_exfalso A M => first_some (blocks_blame Γ M) (fun _ => blocks_blame (unread_binder :: Γ) A)
    | a_elim oq Us m Bks M0 =>
        first_some (blocks_blame Γ M0) (fun _ => first_some
          ((fix exps (Us : list exp) : option run_error :=
              match Us with
              | nil => None
              | U :: Us' => first_some (blocks_blame Γ U) (fun _ => exps Us')
              end) Us)
          (fun _ => first_some
            ((fix blocks (Bks : list eblock) : option run_error :=
                match Bks with
                | nil => None
                | eb_mk nm oZ A Bs :: Bks' =>
                    first_some (match oZ with Some Z => blocks_blame (unread_binders (nm - 1) ++ Γ) Z | None => None end)
                      (fun _ => first_some (blocks_blame (unread_binders nm ++ Γ) A) (fun _ => first_some
                        ((fix brs (Bs : list (string * nat * exp)) : option run_error :=
                            match Bs with
                            | nil => None
                            | b :: Bs' => first_some (blocks_blame (unread_binders (snd (fst b)) ++ Γ) (snd b)) (fun _ => brs Bs')
                            end) Bs)
                        (fun _ => blocks Bks')))
                end) Bks)
            (fun _ => elim_blocks_check Γ M)))
    | a_let (b_def oA N) B =>
        first_some (match oA with Some A => blocks_blame Γ A | None => None end)
          (fun _ => first_some (blocks_blame Γ N)
            (fun _ => blocks_blame (match oA with Some A => ce_def A N | None => unread_binder end :: Γ) B))
    | a_let (b_mod U) B => blocks_blame (ce_mod U :: Γ) B
    | _ => None
    end.
End BlocksBlame.

(** Where a term is rejected, a record type applied past its parameters,
    to a value, where a term stands; or a record value whose fields are
    not the record's, in order.  [ox] names the command, for the printer;
    the contexts are past the stack's telescope. *)
Section ValueBlame.
  Variables (Θ : gdeps) (Ξ : gstack) (ox : option string).

  (** The record a term's head names, with its declaration. *)
  Definition record_head (M : exp) : option (qname * record_decl) :=
    match app_head M with
    | a_record p => option_map (pair p) (record_lookup Θ Ξ p)
    | a_mem H x =>
        match mod_qname H with
        | Some mp => option_map (pair (qname_app mp (x :: nil))) (record_lookup Θ Ξ (qname_app mp (x :: nil)))
        | None => None
        end
    | _ => None
    end.

  (** The first name given, of [ys], where another of [xs] was due. *)
  Fixpoint first_mismatch (ys xs : list string) : option (string * string) :=
    match ys, xs with
    | y :: ys', x :: xs' => if String.eqb y x then first_mismatch ys' xs' else Some (y, x)
    | _, _ => None
    end.

  (** The fields [fs] of a value of the record [R] at [p]: one it does not
      have, then one of it missing, then one out of order. *)
  Definition fields_blame (p : qname) (R : record_decl) (fs : list (string * exp)) : option run_error :=
    let xs := List.map fst (record_fields R) in
    let ys := List.map fst fs in
    match List.find (fun y => negb (List.existsb (String.eqb y) xs)) ys with
    | Some y => Some (run_error_record_field_unknown p y)
    | None =>
        match List.find (fun x => negb (List.existsb (String.eqb x) ys)) xs with
        | Some x => Some (run_error_record_field_missing p x)
        | None =>
            match first_mismatch ys xs with
            | Some (y, x) => Some (run_error_record_fields_order p xs y x)
            | None => None
            end
        end
    end.

  (** A record type applied to more arguments than it has parameters. *)
  Definition applied_blame (Γ : ctx) (M : exp) : option run_error :=
    match record_head M with
    | Some (_, R) =>
        if Nat.ltb (List.length (record_params R)) (List.length (app_args M))
        then Some (run_error_record_value_term Ξ ox Γ M (List.length (record_params R)))
        else None
    | None => None
    end.

  Fixpoint value_blame (Γ : ctx) (M : exp) : option run_error :=
    match M with
    | a_succl M0 | a_univ M0 | a_proj _ M0 => value_blame Γ M0
    | a_maxl M0 N => first_some (value_blame Γ M0) (fun _ => value_blame Γ N)
    | a_app M0 N =>
        first_some (applied_blame Γ M) (fun _ => first_some (value_blame Γ M0) (fun _ => value_blame Γ N))
    | a_pi A B | a_fn A B => first_some (value_blame Γ A) (fun _ => value_blame (ce_ass A :: Γ) B)
    | a_exfalso A M0 => first_some (value_blame Γ M0) (fun _ => value_blame (unread_binder :: Γ) A)
    | a_let (b_def oA N) B =>
        first_some (match oA with Some A => value_blame Γ A | None => None end)
          (fun _ => first_some (value_blame Γ N) (fun _ => value_blame (unread_binder :: Γ) B))
    | a_let (b_mod U) B => value_blame (ce_mod U :: Γ) B
    | a_tuple T fs =>
        first_some (match record_head T with Some (p, R) => fields_blame p R fs | None => None end)
          (fun _ => first_some (value_blame Γ T) (fun _ =>
            (fix fields (fs : list (string * exp)) : option run_error :=
               match fs with
               | nil => None
               | (_, N) :: fs' => first_some (value_blame Γ N) (fun _ => fields fs')
               end) fs))
    | a_elim _ Us _ Bks M0 =>
        first_some (value_blame Γ M0) (fun _ => first_some
          ((fix exps (Us : list exp) : option run_error :=
              match Us with
              | nil => None
              | U :: Us' => first_some (value_blame Γ U) (fun _ => exps Us')
              end) Us)
          (fun _ =>
            (fix blocks (Bks : list eblock) : option run_error :=
               match Bks with
               | nil => None
               | eb_mk nm _ A Bs :: Bks' =>
                   first_some (value_blame (unread_binders nm ++ Γ) A) (fun _ => first_some
                     ((fix brs (Bs : list (string * nat * exp)) : option run_error :=
                         match Bs with
                         | nil => None
                         | b :: Bs' => first_some (value_blame (unread_binders (snd (fst b)) ++ Γ) (snd b)) (fun _ => brs Bs')
                         end) Bs)
                     (fun _ => blocks Bks'))
               end) Bks))
    | _ => None
    end.
End ValueBlame.

(** Where a term is rejected, a record value one of whose fields is not of
    its type: the first such field, in order, each checked against its
    declared type at the record's parameters and the values of the fields
    before it, as the tuple case of the checker checks it
    ([field_checks]).  The record value is reached through the [λ]s and
    the annotated [let]s around it, in the context they extend; a field
    whose value is itself a record value is searched first, so the error
    names the innermost field.  The fields are checked with the checker
    only once the whole term has been rejected, so this only chooses the
    message. *)
(** A context extended by a definition at the type its definiens has. *)
Lemma wf_ctx_extend_def_typed : forall Θ Ξ Γ A N, Θ ⍮ Ξ ⍮ Γ ⊢ N : A -> ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ N.
Proof. intros * HN; gen_presups; eapply wf_ctx_extend_def; eassumption. Qed.

Section FieldBlame.
  (** The lookup data of the checks ([Extraction.Lookup]), the global
      context, and the command declaring [ox], for the printer. *)
  Variables (FF : forall Θ Ξ, FCtx Θ Ξ) (Θ : gdeps) (Ξ : gstack) (ox : option string).

  (** The term [M] in the context [Δ] the stack's telescope is extended
      by, innermost entry first. *)
  Fixpoint field_value_blame (Δ : ctx) (HΔ : ⊢ Θ ⍮ Ξ ⍮ (Δ ++ gs_tele Ξ)) (M : exp) {struct M} : option run_error :=
    match M with
    | a_fn A B =>
        match check_typ FF Θ Ξ (Δ ++ gs_tele Ξ) HΔ A with
        | inleft (exist _ i HA) => field_value_blame (ce_ass A :: Δ) (wf_ctx_extend _ _ _ _ _ HA) B
        | inright _ => None
        end
    | a_let (b_def (Some A) N) B =>
        match check_typ FF Θ Ξ (Δ ++ gs_tele Ξ) HΔ A with
        | inleft (exist _ i HA) =>
            match check_exp_typed FF Θ Ξ (Δ ++ gs_tele Ξ) HΔ A (ex_intro _ i HA) N with
            | left HN => field_value_blame (ce_def A N :: Δ) (wf_ctx_extend_def _ _ _ _ _ _ HA HN) B
            | right _ => None
            end
        | inright _ => None
        end
    (** An unannotated [let], at the type its definiens infers, as the
        typed fill reads it. *)
    | a_let (b_def None N) B =>
        match @type_infer_at (gc_mk Θ Ξ) (FF Θ Ξ) (Δ ++ gs_tele Ξ) HΔ N (user_exp_all N) with
        | inleft (exist _ W HN) => field_value_blame (ce_def (nf_to_exp W) N :: Δ) (wf_ctx_extend_def_typed _ _ _ _ _ HN) B
        | inright _ => None
        end
    | a_tuple T fs =>
        match record_head Θ Ξ T with
        | Some (p, R) =>
            (fix fields (k : nat) (fs0 : list (string * exp)) {struct fs0} : option run_error :=
               match fs0 with
               | nil => None
               | (f, N) :: fs' =>
                   match List.nth_error (record_fields R) k with
                   | Some (_, U) =>
                       let Uk := U[sb_of_list Id (app_args T ++ List.firstn k (List.map snd fs))] in
                       match check_typ FF Θ Ξ (Δ ++ gs_tele Ξ) HΔ Uk with
                       | inleft (exist _ i HU) =>
                           match check_exp_typed FF Θ Ξ (Δ ++ gs_tele Ξ) HΔ Uk (ex_intro _ i HU) N with
                           | left _ => fields (S k) fs'
                           | right _ =>
                               first_some (field_value_blame Δ HΔ N)
                                 (fun _ =>
                                    let (W, _) := @nbe_ty_impl Θ Ξ (FF Θ Ξ) (Δ ++ gs_tele Ξ) Uk
                                                    (typ_nbe_ty_order Θ Ξ _ _ _ HU) in
                                    Some (run_error_record_field Ξ ox Δ p f N (nf_to_exp W)))
                           end
                       | inright _ => None
                       end
                   | None => None
                   end
               end) 0 fs
        | None => None
        end
    | _ => None
    end.
End FieldBlame.

(** The error for a rejected definition body or [eval] term [M], of the
    command declaring [ox]: a field of a record value in [M] whose value is
    not of its type ([field_value_blame]), otherwise the given error. *)
Definition field_error (FF : forall Θ Ξ, FCtx Θ Ξ) Θ Ξ (ox : option string)
    (HΞ : ⊢ Θ ⍮ Ξ ⍮ gs_tele Ξ) (M : exp) (e : run_error) : run_error :=
  match field_value_blame FF Θ Ξ ox nil HΞ M with
  | Some e' => e'
  | None => e
  end.

(** The error for a rejected term of the command declaring [ox]: a module
    where a term stands, if there is one, then a record value's module
    where a term stands or a record value with wrong fields, then an
    eliminator whose blocks do not match its group, then one whose
    branches do not match its type, otherwise the given error. *)
Definition mod_error {Θ Ξ} (Hg : ⊢ᵍ Θ ⍮ Ξ) (ox : option string) (Ms : list exp)
    (e : run_error) : run_error :=
  match List.fold_right (fun M r => first_some (first_some (mod_blame Θ Ξ M)
                                      (fun _ => first_some (value_blame Θ Ξ ox nil M)
                                        (fun _ => first_some (blocks_blame Θ Ξ nil M) (fun _ => brs_blame Θ Ξ M))))
                                      (fun _ => r)) None Ms with
  | Some e' => e'
  | None => e
  end.

Definition tele_blame_error {Θ Ξ Γ Δ} (b : option (level_blame Θ Ξ Γ) + { ⊢ Θ ⍮ Ξ ⍮ (Δ ++ Γ) })
    (e : run_error) : run_error :=
  match b with
  | inleft ob => blame_error ob e
  | inright _ => e
  end.

Inductive rres (A : Type) : Type :=
| rok : A -> rres A
| rerr : run_error -> rres A.

Arguments rok {A}.
Arguments rerr {A}.

(** A checked and normalized [eval]: in the restriction [eval_entry_deps] of the
    state to the imports so far, on the stack [eval_entry_stack], and in the context
    of the frames' parameters, the expression [eval_entry_exp] has type [eval_entry_typ]
    (ascribed or inferred) and normalizes to [eval_entry_nf]. *)
Record eval_entry : Set :=
  { eval_entry_deps : gdeps; eval_entry_stack : gstack; eval_entry_exp : exp; eval_entry_typ : typ; eval_entry_nf : nf }.

Record eval_ok (e : eval_entry) : Prop := mk_eval_ok
  { eval_ok_wf : ⊢ᵍ eval_entry_deps e ⍮ eval_entry_stack e
  ; eval_ok_typ : eval_entry_deps e ⍮ eval_entry_stack e ⍮ gs_tele (eval_entry_stack e) ⊢ eval_entry_exp e : eval_entry_typ e
  ; eval_ok_nbe : nbe (eval_entry_deps e) (eval_entry_stack e) (gs_tele (eval_entry_stack e)) (eval_entry_exp e) (eval_entry_typ e) (eval_entry_nf e) }.

Definition logs_ok (l : list eval_entry) : Prop := forall e, In e l -> eval_ok e.

(** The log of a run, in program order, with every entry certified. *)
Definition elog : Set := {l | logs_ok l}.

Definition log_nil : elog := exist logs_ok nil (fun e (H : In e nil) => False_ind _ H).

Definition log_app (l1 l2 : elog) : elog.
Proof.
  refine (exist _ (List.app (proj1_sig l1) (proj1_sig l2)) _).
  abstract (intros e He; apply in_app_or in He as [He | He]; [ exact (proj2_sig l1 _ He) | exact (proj2_sig l2 _ He) ]).
Defined.

Lemma typed_nbe_order {Θ Ξ Γ M A} : Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> nbe_order Θ Ξ Γ M A.
Proof. intros H; destruct (soundness H) as (W & HW & _); exact (nbe_order_sound _ _ _ _ _ _ HW). Qed.

(** Whether a term of a normal type is a type former of an inductive type
    ([ind_former]): its normal form at the variables of the type's
    domains, computed once, is decisive, since normal forms are unique. *)
Definition ind_former_dec (Θ : gdeps) (Ξ : gstack) (F : FCtx Θ Ξ) (Γ : ctx) (M : exp) (W : nf)
    (HM : Θ ⍮ Ξ ⍮ Γ ⊢ M : nf_to_exp W) : {ind_former Θ Ξ Γ M W} + {~ ind_former Θ Ξ Γ M W}.
Proof.
  unfold ind_former.
  destruct (nf_pi_tele W) as [Ds C] eqn:Ep.
  destruct (nf_is_universe_dec C) as [Hu | Hu]; [| right; intros [Hu' _]; contradiction ].
  destruct (@nbe_impl Θ Ξ F (Ds ++ Γ) (exp_applied_to_vars M (List.length Ds)) (nf_to_exp C)
              (typed_nbe_order (applied_vars_typed _ _ _ _ _ _ _ HM Ep))) as [W' HW'].
  destruct W';
    try (right; intros (_ & p0 & k0 & Rs0 & Hn); pose proof (functional_nbe _ _ _ _ _ HW' Hn) as E; discriminate E).
  left; split; [ exact Hu | do 3 eexists; exact HW' ].
Defined.

(** Likewise of a record type ([record_former]). *)
Definition record_former_dec (Θ : gdeps) (Ξ : gstack) (F : FCtx Θ Ξ) (Γ : ctx) (M : exp) (W : nf)
    (HM : Θ ⍮ Ξ ⍮ Γ ⊢ M : nf_to_exp W) : {record_former Θ Ξ Γ M W} + {~ record_former Θ Ξ Γ M W}.
Proof.
  unfold record_former.
  destruct (nf_pi_tele W) as [Ds C] eqn:Ep.
  destruct (nf_is_universe_dec C) as [Hu | Hu]; [| right; intros [Hu' _]; contradiction ].
  destruct (@nbe_impl Θ Ξ F (Ds ++ Γ) (exp_applied_to_vars M (List.length Ds)) (nf_to_exp C)
              (typed_nbe_order (applied_vars_typed _ _ _ _ _ _ _ HM Ep))) as [W' HW'].
  destruct W';
    try (right; intros (_ & p0 & Rs0 & Hn); pose proof (functional_nbe _ _ _ _ _ HW' Hn) as E; discriminate E).
  left; split; [ exact Hu | do 2 eexists; exact HW' ].
Defined.

(** Normalize a checked [eval] into its entry. *)
Lemma eval_log_ok {Θ Ξ M A W} : ⊢ᵍ Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> nbe Θ Ξ (gs_tele Ξ) M A W ->
  logs_ok ({| eval_entry_deps := Θ; eval_entry_stack := Ξ; eval_entry_exp := M; eval_entry_typ := A; eval_entry_nf := W |} :: nil).
Proof. intros HΞ HM HW e [<- | []]; constructor; cbn; auto. Qed.

Definition eval_log (Θ : gdeps) (Ξ : gstack) (F : FCtx Θ Ξ) (HΞ : ⊢ᵍ Θ ⍮ Ξ) (M : exp) (A : typ)
  (HM : Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A) : elog :=
  match @nbe_impl Θ Ξ F (gs_tele Ξ) M A (typed_nbe_order HM) with
  | exist _ W HW => exist _ _ (eval_log_ok HΞ HM HW)
  end.

Lemma sub_none : forall Θ Θ' fp, Θ ⊑ Θ' -> gds_lookup Θ' fp = None -> gds_lookup Θ fp = None.
Proof. intros * Hs Hn; destruct (gds_lookup Θ fp) eqn:E; [ rewrite (Hs _ _ E) in Hn; discriminate | reflexivity ]. Qed.

Lemma sub_dom : forall Θ Θ' fp, Θ ⊑ Θ' -> In fp (gds_dom Θ) -> In fp (gds_dom Θ').
Proof.
  intros * Hs H; rewrite gds_dom_lookup in *; destruct (gds_lookup Θ fp) eqn:E; [| contradiction ].
  rewrite (Hs _ _ E); discriminate.
Qed.

Lemma dom_merge : forall Θ Θ' fp,
    In fp (gds_dom (gds_merge Θ Θ')) <-> In fp (gds_dom Θ) \/ In fp (gds_dom Θ').
Proof.
  intros; rewrite !gds_dom_lookup; split.
  - intros H; destruct (gds_lookup Θ fp) eqn:E1; [ left; discriminate |].
    right; intros E2; apply H, merge_none; auto.
  - intros [H | H] E; apply merge_none in E as [E1 E2]; contradiction.
Qed.

Lemma dom_cons : forall fp U Θ fq, In fq (gds_dom ((fp, U) :: Θ)) <-> fq = fp \/ In fq (gds_dom Θ).
Proof. intros; cbn; split; intros [H | H]; auto. Qed.

(** Being a type former of an inductive type, a normal form, moves along an
    equivalence. *)
Lemma equiv_ind_former : forall Θ Θ' Ξ Γ M W, gds_equiv Θ Θ' -> ind_former Θ Ξ Γ M W -> ind_former Θ' Ξ Γ M W.
Proof.
  intros * He; unfold ind_former; destruct (nf_pi_tele W) as [Ds C].
  intros (Hu & p & k & Rs & Hn); split; [ exact Hu | exists p, k, Rs; exact (equiv_nbe _ _ _ He _ _ _ _ Hn) ].
Qed.

(** Likewise of a record type. *)
Lemma equiv_record_former : forall Θ Θ' Ξ Γ M W, gds_equiv Θ Θ' -> record_former Θ Ξ Γ M W -> record_former Θ' Ξ Γ M W.
Proof.
  intros * He; unfold record_former; destruct (nf_pi_tele W) as [Ds C].
  intros (Hu & p & Rs & Hn); split; [ exact Hu | exists p, Rs; exact (equiv_nbe _ _ _ He _ _ _ _ Hn) ].
Qed.

(** A type inferred algorithmically moves along an equivalence. *)
Lemma equiv_alg_infer : forall Θ Θ' Ξ Γ W M, gds_equiv Θ Θ' ->
    @alg_type_infer (gc_mk Θ Ξ) Γ W M -> @alg_type_infer (gc_mk Θ' Ξ) Γ W M.
Proof. intros * He; exact (proj1 (proj2 (equiv_alg_all _ _ _ He)) _ _ _). Qed.

(** ** Mutual Definitions *)

(** The definitions [ds] filed in order in [Ξ]. *)
Fixpoint mdefs_stack (b pv : bool) (ds : list (string * typ * exp)) (Ξ : gstack) : gstack :=
  match ds with
  | nil => Ξ
  | (x, A, M) :: ds' => mdefs_stack b pv ds' (gs_add x (gs_def b pv Ξ A M) Ξ)
  end.

(** Filing the definitions ends on [mdefs_stack]. *)
Lemma mdefs_run_stack : forall Θ b pv ds Ξ Ξ', mdefs_run Θ b pv ds Ξ Ξ' -> Ξ' = mdefs_stack b pv ds Ξ.
Proof. induction 1; cbn [mdefs_stack]; auto. Qed.

(** [mdef_why], [mdef_member_dec] and [mdef_members_dec] are in
    [MdefGroup], with the group's decision ([mdef_group_dec]). *)

(** Why a definition of a mutual definition is not filed: its name is not
    fresh, or its term is not of its type. *)
Inductive mdefs_why : Set :=
(** The name, taken *)
| mdefs_why_dup : string -> mdefs_why
(** The name, the stack, the type and the term *)
| mdefs_why_untyped : string -> gstack -> typ -> exp -> mdefs_why.

(** The definitions filed in order, each checked as [run_cmd_def] does. *)
Fixpoint mdefs_dec (Θ : gdeps) (b pv : bool) (ds : list (string * typ * exp)) (Ξ : gstack) (HΞ : ⊢ᵍ Θ ⍮ Ξ) {struct ds} :
    (mdefs_run Θ b pv ds Ξ (mdefs_stack b pv ds Ξ) + {e : mdefs_why | forall Ξ', ~ mdefs_run Θ b pv ds Ξ Ξ'})%type.
Proof.
  destruct ds as [| [[x A] M] ds'].
  - left; constructor.
  - destruct (gs_fresh_dec x Ξ) as [Hfr | Hn];
      [| right; exists (mdefs_why_dup x); intros Ξ' Hr; inversion Hr; subst; contradiction ].
    destruct (check_exp_at Θ Ξ HΞ (gs_tele Ξ) A M) as [HM | Hn];
      [| right; exists (mdefs_why_untyped x Ξ A M); intros Ξ' Hr; inversion Hr; subst; contradiction ].
    destruct (mdefs_dec Θ b pv ds' (gs_add x (gs_def b pv Ξ A M) Ξ) (add_def_wf _ _ _ _ _ _ _ HΞ HM Hfr)) as [Hr | [e Hn]];
      [ left; econstructor; eassumption | right; exists e; intros Ξ' Hr'; inversion Hr'; subst; eapply Hn; eassumption ].
Defined.

(** Filing the definitions alike along an equivalence. *)
Lemma equiv_mdefs_run : forall Θ Θ' b pv ds Ξ Ξ', gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ ->
    mdefs_run Θ b pv ds Ξ Ξ' -> mdefs_run Θ' b pv ds Ξ Ξ'.
Proof.
  intros * He HΞ Hr; revert HΞ; induction Hr as [| x A M ds Ξ Ξ' HM Hfr _ IH]; intros HΞ; [ constructor |].
  pose proof (equiv_exp _ _ _ _ _ _ He HΞ HM) as HM'.
  econstructor; [ exact HM' | exact Hfr | apply IH, add_def_wf; assumption ].
Qed.

(** What a command's checks look names up in ([Extraction.Lookup]): the
    trie of the filed units, and the declaration of the type bound as the
    natural numbers, looked up once per check rather than once per
    eliminator. *)
Definition fctx_cmd (B : builtins) (Θ : gdeps) (Ξ : gstack) : FCtx Θ Ξ :=
  fctx_at Θ Ξ (builtins_nat B).

(** ** The Views of a Group *)

(** The views [Vs] of the declaration [R] whose declared members'
    constructors classify as [csD], with what [run_cmd_ind_case] asks of them. *)
Record views_ok (Θ : gdeps) (Ξ : gstack) (R : raw_decl) (csD : list (list (string * list rcarg)))
    (Vs : list rview) (Ss : list (list rview)) (csV : list (list (string * list rcarg))) (Nvs : list ctx) : Prop :=
  mk_views_ok
  { (** each view's siblings *)
    views_siblings : Forall2 (view_sibs Θ Ξ R) Vs Ss;
    (** each view's constructors, classified *)
    views_classified : Forall2 (view_cls Θ Ξ R) Vs csV;
    (** each view's non-uniform parameters, filed *)
    views_nparams : Forall2 (view_nps Θ Ξ R) Vs Nvs;
    (** the views, found from the instances met *)
    views_search_run : views_bfs (sibs_tbl Vs Ss) (meets_tbl Vs csV) nil (List.concat (List.map rcons_views csD)) Vs }.

(** The views found, with their tables. *)
Definition views_found (Θ : gdeps) (Ξ : gstack) (R : raw_decl) (csD : list (list (string * list rcarg))) : Type :=
  {Vs : list rview & {Ss : list (list rview) & {csV : list (list (string * list rcarg)) &
     {Nvs : list ctx | views_ok Θ Ξ R csD Vs Ss csV Nvs}}}}.

(** The views alike along an equivalence. *)
Lemma equiv_views_ok : forall Θ Θ' Ξ R csD Vs Ss csV Nvs, gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ ->
    views_ok Θ Ξ R csD Vs Ss csV Nvs -> views_ok Θ' Ξ R csD Vs Ss csV Nvs.
Proof.
  intros * He HΞ [Hs Hc Hn Hb]; constructor; [| | | exact Hb ].
  - eapply Forall2_impl; [ intros x ss; apply (equiv_view_sibs _ _ _ He HΞ) | exact Hs ].
  - eapply Forall2_impl; [ intros x cs; apply (equiv_view_cls _ _ _ He HΞ) | exact Hc ].
  - eapply Forall2_impl; [ intros x Nv; apply (equiv_view_nps _ _ _ He HΞ) | exact Hn ].
Qed.

(** The views of a group are found in one way. *)
Lemma views_ok_functional : forall Θ Ξ R csD Vs Ss csV Nvs Vs' Ss' csV' Nvs',
    views_ok Θ Ξ R csD Vs Ss csV Nvs -> views_ok Θ Ξ R csD Vs' Ss' csV' Nvs' ->
    Vs = Vs' /\ Ss = Ss' /\ csV = csV' /\ Nvs = Nvs'.
Proof.
  intros * [Hs Hv Hn Hb] [Hs' Hv' Hn' Hb'].
  assert (Agree : forall x, In x Vs -> In x Vs' -> sibs_tbl Vs Ss x = sibs_tbl Vs' Ss' x /\ meets_tbl Vs csV x = meets_tbl Vs' csV' x).
  { intros x Hx Hx'.
    destruct (rview_index_in_some _ _ Hx) as [v Hvi]; destruct (rview_index_in_some _ _ Hx') as [v' Hvi'].
    unfold sibs_tbl, meets_tbl; rewrite Hvi, Hvi'; split.
    - eapply view_sibs_functional; eapply Forall2_index; eassumption.
    - f_equal; eapply view_cls_functional; eapply Forall2_index; eassumption. }
  pose proof (views_bfs_functional _ _ _ _ _ Hb _ _ _ Hb' Agree) as <-.
  split; [ reflexivity |].
  split; [ eapply Forall2_functional; [ exact (view_sibs_functional Θ Ξ R) | exact Hs | exact Hs' ] |].
  split; [ eapply Forall2_functional; [ exact (view_cls_functional Θ Ξ R) | exact Hv | exact Hv' ] |].
  eapply Forall2_functional; [ exact (view_nps_functional Θ Ξ R) | exact Hn | exact Hn' ].
Qed.

Section Impl.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  (** How the views of a group are found: [ViewsFound.views_search], which
      [Entrypoint] supplies (it is defined over this file's [views_found]). *)
  Variable views_search : forall Θ Ξ (HΞ : ⊢ᵍ Θ ⍮ Ξ) R csD, rres (views_found Θ Ξ R csD).
  (** The search finds the views whenever there are some. *)
  Hypothesis views_search_complete : forall Θ Ξ HΞ R csD Vs Ss csV Nvs,
      views_ok Θ Ξ R csD Vs Ss csV Nvs -> exists v, views_search Θ Ξ HΞ R csD = rok v.
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).
  #[local] Abbreviation canon := (canon load_path read to_core).
  #[local] Abbreviation run_wf := (run_wf load_path read to_core).
  #[local] Abbreviation run_functional := run_functional.

  (** ** The Invariants *)

  Definition set_eq (A B : list path) : Prop := forall x, In x A <-> In x B.

  (** A set of paths closed under the closures [K] records. *)
  Definition closedK (K : kmap) (D : list path) : Prop :=
    forall x Dx, In x D -> kfind K x = Some Dx -> incl Dx D.

  (** The records of a map are those [K] keeps. *)
  Definition rb_in (K : kmap) (Rb : bmap) : Prop :=
    forall fp BU, bm_lookup Rb fp = Some BU -> kbt K fp = Some BU.

  (** The records of the judgment's state [ΘR]: canonical, and those [K]
      keeps. *)
  Definition rb_ok (K : kmap) (ΘR : gdeps) (Rb : bmap) : Prop := canon Rb ΘR /\ rb_in K Rb.

  (** A filed unit is what loading its file yields, under a chain starting
      with it, and [K] keeps the record that run ends with.  The state that
      run ended in is filed as well, below the unit in [Θ], and [K] records
      its domain, closed, and the records of what it filed. *)
  #[warnings="-cannot-define-projection"]
  Record entry_ok (Θ : gdeps) (K : kmap) (fp : path) (U : gunit) : Prop := mk_entry_ok
    { entry_ok_dom : list path
    ; entry_ok_bt : builtins
    ; entry_ok_src : string
    ; entry_ok_prog : Cst.prog
    ; entry_ok_unit : cunit
    ; entry_ok_chain : list path
    ; entry_ok_rb : bmap
    ; entry_ok_deps : gdeps
    ; entry_ok_kfind : kfind K fp = Some entry_ok_dom
    ; entry_ok_kbt : kbt K fp = Some entry_ok_bt
    ; entry_ok_closed : closedK K entry_ok_dom
    ; entry_ok_load : load_path fp = Some entry_ok_src
    ; entry_ok_read : read entry_ok_src = Some entry_ok_prog
    ; entry_ok_path : prog_path entry_ok_prog = fp
    ; entry_ok_core : to_core entry_ok_prog = Some entry_ok_unit
    ; entry_ok_run : run_unit (fp :: entry_ok_chain) entry_ok_unit entry_ok_bt entry_ok_rb entry_ok_deps U
    ; entry_ok_sub_field : entry_ok_deps ⊑ Θ
    ; entry_ok_set : set_eq entry_ok_dom (gds_dom entry_ok_deps)
    ; entry_ok_rb_in : rb_in K entry_ok_rb }.

  (** Each filed unit is [entry_ok] for the units below it. *)
  Fixpoint entries_ok (K : kmap) (Θ : gdeps) : Prop :=
    match Θ with
    | nil => True
    | (fp, U) :: Θ' => entry_ok Θ' K fp U /\ entries_ok K Θ'
    end.

  (** The invariant of the global state for a run under chain [ch]; in
      particular, nothing on the chain is filed yet. *)
  Record ginv (ch : list path) (Θ : gdeps) (K : kmap) : Prop :=
    { gi_wf : ⊢ᵍ Θ ⍮ nil
    ; gi_chain : forall x, In x ch -> gds_lookup Θ x = None
    ; gi_entry : entries_ok K Θ
    ; gi_kdom : forall fp D, kfind K fp = Some D -> gds_lookup Θ fp <> None }.

  (** The invariant of the unit being run, relative to the judgment's state
      [ΘR]: the units [D] it imported are those of [ΘR], filed identically
      in [Θ].  The judgment's records are [rb_ok], apart. *)
  Record linv (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (ΘR : gdeps) (Ξ : gstack) : Prop :=
    { li_g : ginv ch Θ K
    ; li_sub : ΘR ⊑ Θ
    ; li_dom : set_eq D (gds_dom ΘR)
    ; li_closed : closedK K D
    ; li_wf : ⊢ᵍ ΘR ⍮ Ξ
    ; li_stack : stack_in ch Ξ }.

  Record ext (Θ : gdeps) (K : kmap) (Θ' : gdeps) (K' : kmap) : Prop := mk_ext
    { ext_sub : Θ ⊑ Θ'
    ; ext_kfind : forall x Dx, kfind K x = Some Dx -> kfind K' x = Some Dx
    ; ext_kbt : forall x Bx, kbt K x = Some Bx -> kbt K' x = Some Bx }.

  (** Whatever a run files, it imports; hence at the top level the result has
      exactly the domain of the judgment's state. *)
  Definition grows (Θ Θ' : gdeps) (D' : list path) : Prop :=
    forall x, In x (gds_dom Θ') -> In x (gds_dom Θ) \/ In x D'.

  Record cstate : Set := cst { cstate_deps : gdeps; cstate_k : kmap; cstate_dom : list path; cstate_bt : builtins; cstate_stack : gstack }.
  Record ustate : Set := ust { us_deps : gdeps; us_k : kmap; us_dom : list path; us_bt : builtins; us_unit : gunit }.

  (** What a run of commands from [Θ ⍮ K] to [r] proves: the judgment, from
      the judgment's state and records the run started at, reaches [cmd_post_deps]
      and [cmd_post_rb] ([run]), and the invariants hold again. *)
  #[warnings="-cannot-define-projection"]
  Record cmd_post (run : bmap -> gdeps -> Prop) ch (Θ : gdeps) (K : kmap) (r : cstate) : Prop := mk_cmd_post
    { cmd_post_deps : gdeps
    ; cmd_post_rb : bmap
    ; cmd_post_run : run cmd_post_rb cmd_post_deps
    ; cmd_post_linv : linv ch (cstate_deps r) (cstate_k r) (cstate_dom r) cmd_post_deps (cstate_stack r)
    ; cmd_post_rb_ok : rb_ok (cstate_k r) cmd_post_deps cmd_post_rb
    ; cmd_post_ext : ext Θ K (cstate_deps r) (cstate_k r)
    ; cmd_post_grows : grows Θ (cstate_deps r) (cstate_dom r) }.

  Definition post_cmd ch Θ K D B Ξ c (r : cstate) : Prop :=
    forall ΘR RbR, linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      cmd_post (fun RbR' ΘR' => ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ ΘR' ⍮ cstate_stack r ⍮ cstate_bt r ⍮ RbR') ch Θ K r.

  Definition post_cmds ch Θ K D B Ξ cs (r : cstate) : Prop :=
    forall ΘR RbR, linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      cmd_post (fun RbR' ΘR' => ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR' ⍮ cstate_stack r ⍮ cstate_bt r ⍮ RbR') ch Θ K r.

  (** A command filled ([fill_cmd]) and run, as [run_cmds_cons] does. *)
  Definition post_lcmd ch Θ K D B Ξ c (r : cstate) : Prop :=
    forall ΘR RbR, linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      cmd_post (fun RbR' ΘR' => exists c', fill_cmd ΘR Ξ B c c' /\
                                  ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c' ⇝ ΘR' ⍮ cstate_stack r ⍮ cstate_bt r ⍮ RbR') ch Θ K r.

  (** A unit runs from no binding and nothing filed. *)
  #[warnings="-cannot-define-projection"]
  Record unit_post ch (Θ : gdeps) (K : kmap) (u : cunit) (r : ustate) : Prop := mk_unit_post
    { unit_post_rb : bmap
    ; unit_post_deps : gdeps
    ; unit_post_run : run_unit ch u (us_bt r) unit_post_rb unit_post_deps (us_unit r)
    ; unit_post_ginv : ginv ch (us_deps r) (us_k r)
    ; unit_post_sub : unit_post_deps ⊑ us_deps r
    ; unit_post_set : set_eq (us_dom r) (gds_dom unit_post_deps)
    ; unit_post_closed : closedK (us_k r) (us_dom r)
    ; unit_post_rb_in : rb_in (us_k r) unit_post_rb
    ; unit_post_ext : ext Θ K (us_deps r) (us_k r)
    ; unit_post_grows : grows Θ (us_deps r) (us_dom r) }.

  Definition post_unit ch Θ K u (r : ustate) : Prop := ginv ch Θ K -> unit_post ch Θ K u r.

  (** ** Consequences of the Invariants *)

  Lemma entry_ok_sub : forall Θ1 Θ2 K fp U, Θ1 ⊑ Θ2 -> entry_ok Θ1 K fp U -> entry_ok Θ2 K fp U.
  Proof.
    intros * Hs [D BU src prg u ch RbU ΘU HK HB Hcl Hl Hr Hp Ht Hu Hsub Hdom HR].
    apply (mk_entry_ok _ _ _ _ D BU src prg u ch RbU ΘU); try assumption.
    eapply gds_sub_trans; eassumption.
  Qed.

  Lemma entries_ok_lookup : forall K Θ, ⊢ᵍ Θ ⍮ nil -> entries_ok K Θ ->
      forall fp U, gds_lookup Θ fp = Some U -> entry_ok Θ K fp U.
  Proof.
    intros K; induction Θ as [| [fq V] Θ IH]; intros Hwf HE fp U HU; [ discriminate |]; destruct HE as [HV HΘ].
    destruct (wf_gstack_file_inv _ _ _ Hwf) as (Hwf0 & _ & Hn).
    apply (entry_ok_sub Θ); [ apply gds_sub_cons, Hn |].
    cbn in HU; destruct (path_beq fp fq) eqn:Hb; [| exact (IH Hwf0 HΘ _ _ HU) ].
    apply path_beq_true in Hb as ->; injection HU as <-; exact HV.
  Qed.

  Lemma ginv_entry {ch Θ K} : ginv ch Θ K -> forall fp U, gds_lookup Θ fp = Some U -> entry_ok Θ K fp U.
  Proof. intros G; exact (entries_ok_lookup _ _ (gi_wf _ _ _ G) (gi_entry _ _ _ G)). Qed.

  Lemma entries_closure : forall K D Θ, closedK K D -> entries_ok K Θ -> closure_ok D Θ.
  Proof.
    intros K D; induction Θ as [| [fp U] Θ IH]; intros Hcl HΘ; [ exact I |].
    destruct HΘ as [[Dfp BU src prg u ch0 RbU ΘU HK _ _ _ _ _ _ Hu Hsub Hdom _] HΘ].
    split; [| auto ]; intros Hin.
    destruct (proj1 (proj2 (proj2 run_wf)) _ _ _ _ _ _ Hu) as (_ & _ & HwU); cbn [hd] in HwU.
    exists ΘU; split; [ exact HwU | split; [ exact Hsub |] ].
    intros x Hx; apply (Hcl _ _ Hin HK), Hdom, Hx.
  Qed.

  Lemma ginv_restrict_wf {ch Θ K D} : ginv ch Θ K -> closedK K D -> ⊢ᵍ gds_restrict D Θ ⍮ nil.
  Proof. intros G Hcl; exact (restrict_wf _ _ (gi_wf _ _ _ G) (entries_closure _ _ _ Hcl (gi_entry _ _ _ G))). Qed.

  Lemma linv_in {ch Θ K D ΘR Ξ} : linv ch Θ K D ΘR Ξ -> forall x, In x D -> gds_lookup Θ x <> None.
  Proof.
    intros Hli x Hx; apply (li_dom _ _ _ _ _ _ Hli), gds_dom_lookup in Hx.
    destruct (gds_lookup ΘR x) eqn:E; [| contradiction ].
    rewrite (li_sub _ _ _ _ _ _ Hli _ _ E); discriminate.
  Qed.

  Lemma linv_equiv {ch Θ K D ΘR Ξ} : linv ch Θ K D ΘR Ξ -> gds_equiv ΘR (gds_restrict D Θ).
  Proof.
    intros Hli; exact (equiv_restrict _ _ _ (li_sub _ _ _ _ _ _ Hli) (li_dom _ _ _ _ _ _ Hli)).
  Qed.

  Lemma linv_restrict_gctx {ch Θ K D ΘR Ξ} : linv ch Θ K D ΘR Ξ -> ⊢ᵍ gds_restrict D Θ ⍮ Ξ.
  Proof.
    intros Hli; exact (equiv_gctx _ _ _ (linv_equiv Hli)
                         (ginv_restrict_wf (li_g _ _ _ _ _ _ Hli) (li_closed _ _ _ _ _ _ Hli))
                         (li_wf _ _ _ _ _ _ Hli)).
  Qed.

  Lemma pre_gctx {ch Θ K D Ξ} : (exists ΘR, linv ch Θ K D ΘR Ξ) -> ⊢ᵍ gds_restrict D Θ ⍮ Ξ.
  Proof. intros [ΘR Hli]; exact (linv_restrict_gctx Hli). Qed.

  Lemma pre_ctx {ch Θ K D Ξ} : (exists ΘR, linv ch Θ K D ΘR Ξ) -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ.
  Proof. intros H; exact (wf_gs_tele _ _ (pre_gctx H)). Qed.

  Lemma linv_stack {ch Θ K D ΘR Ξ Ξ'} :
    linv ch Θ K D ΘR Ξ -> ⊢ᵍ ΘR ⍮ Ξ' -> stack_in ch Ξ' -> linv ch Θ K D ΘR Ξ'.
  Proof. intros [] H Hs; constructor; assumption. Qed.

  Lemma linv_run_wf {ch Θ K D B RbR ΘR Ξ c B' RbR' ΘR' Ξ'} :
    linv ch Θ K D ΘR Ξ -> canon RbR ΘR -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
    ⊢ᵍ ΘR' ⍮ Ξ' /\ canon RbR' ΘR' /\ ΘR ⊑ ΘR' /\ bt_le B B'.
  Proof.
    intros Hli Hc Hr;
      exact (proj1 run_wf _ _ _ _ _ _ _ _ _ _ Hr (li_wf _ _ _ _ _ _ Hli) Hc (li_stack _ _ _ _ _ _ Hli)).
  Qed.

  Lemma linv_run_stack {ch Θ K D B RbR ΘR Ξ c B' RbR' ΘR' Ξ'} :
    linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' -> stack_in ch Ξ'.
  Proof.
    intros Hli Hr; exact (stack_in_shape _ _ _ (proj1 (run_params load_path read to_core) _ _ _ _ _ _ _ _ _ _ Hr)
                            (li_stack _ _ _ _ _ _ Hli)).
  Qed.

  Lemma linv_run_same {ch Θ K D B RbR ΘR Ξ c B' Ξ'} :
    linv ch Θ K D ΘR Ξ -> canon RbR ΘR -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ ΘR ⍮ Ξ' ⍮ B' ⍮ RbR -> linv ch Θ K D ΘR Ξ'.
  Proof.
    intros Hli Hc Hr; apply (linv_stack Hli); [ exact (proj1 (linv_run_wf Hli Hc Hr)) | exact (linv_run_stack Hli Hr) ].
  Qed.

  Lemma linv_push {ch Θ K D ΘR Ξ x Δ} :
    linv ch Θ K D ΘR Ξ -> tele_ass Δ -> gs_fresh x Ξ -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    ⊢ ΘR ⍮ Ξ ⍮ Δ ++ gs_tele Ξ /\ linv ch Θ K D ΘR (gs_push (qname_in (gs_path Ξ) x) Δ Ξ).
  Proof.
    intros Hli Htel Hfr HΔ.
    assert (HΔ' : ⊢ ΘR ⍮ Ξ ⍮ Δ ++ gs_tele Ξ)
      by exact (equiv_ctx _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HΔ).
    split; [ exact HΔ' |]; apply (linv_stack Hli); [| exact (stack_in_push _ _ _ _ (li_stack _ _ _ _ _ _ Hli) Hfr) ].
    apply wf_gstack_cons; [ apply (li_wf _ _ _ _ _ _ Hli) | constructor; [ exact Htel | exact HΔ' ] |].
    destruct Ξ as [| [[mp Kq] U] Ξ]; [ contradiction |]; cbn; exists x; split; [ reflexivity | exact Hfr ].
  Qed.

  (** A unit's own frame: its path heads the chain, so it is not filed. *)
  Lemma linv_push_unit {fp ch Θ K D ΘR P} :
    linv (fp :: ch) Θ K D ΘR nil -> tele_ass P -> ⊢ gds_restrict D Θ ⍮ nil ⍮ P ->
    ⊢ ΘR ⍮ nil ⍮ P /\ linv (fp :: ch) Θ K D ΘR (gs_push (q_abs fp nil) P nil).
  Proof.
    intros Hli Htel HP.
    assert (HP' : ⊢ ΘR ⍮ nil ⍮ P)
      by exact (equiv_ctx _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HP).
    split; [ exact HP' |]; apply (linv_stack Hli); [| intros ? ? ? [[= <- <- <-] | []]; left; reflexivity ].
    apply wf_gstack_cons;
      [ apply (li_wf _ _ _ _ _ _ Hli) | constructor; [ exact Htel | cbn; rewrite app_nil_r; exact HP' ] |].
    cbn; split; [| reflexivity ].
    exact (sub_none _ _ _ (li_sub _ _ _ _ _ _ Hli) (gi_chain _ _ _ (li_g _ _ _ _ _ _ Hli) _ (or_introl eq_refl))).
  Qed.

  Lemma ext_refl : forall Θ K, ext Θ K Θ K.
  Proof. constructor; [ apply gds_sub_refl | auto | auto ]. Qed.

  Lemma ext_trans : forall Θ1 K1 Θ2 K2 Θ3 K3, ext Θ1 K1 Θ2 K2 -> ext Θ2 K2 Θ3 K3 -> ext Θ1 K1 Θ3 K3.
  Proof. intros * [H1 H2 H2'] [H3 H4 H4']; constructor; [ eapply gds_sub_trans; eassumption | auto | auto ]. Qed.

  Lemma grows_refl : forall Θ D, grows Θ Θ D.
  Proof. intros ? ? ? ?; left; assumption. Qed.

  Lemma closedK_cons : forall K T fp Dfp Bfp,
      closedK K T -> (forall y, In y T -> y <> fp) -> closedK ((fp, (Dfp, Bfp)) :: K) T.
  Proof.
    intros * Hcl Hne y Dy Hy HK; simp kfind in HK; rewrite (path_beq_false _ _ (Hne _ Hy)) in HK; eauto.
  Qed.

  Lemma rb_in_cons : forall K fp Dfp Bfp Rb,
      (forall y By, bm_lookup Rb y = Some By -> y <> fp) -> rb_in K Rb -> rb_in ((fp, (Dfp, Bfp)) :: K) Rb.
  Proof.
    intros * Hne HR y By Hy; simp kbt; rewrite (path_beq_false _ _ (Hne _ _ Hy)); exact (HR _ _ Hy).
  Qed.

  Lemma entries_ok_cons_K : forall K fp Dfp Bfp Θ,
      (forall y Dy, kfind K y = Some Dy -> y <> fp) -> (forall y By, kbt K y = Some By -> y <> fp) ->
      (forall y, In y (gds_dom Θ) -> y <> fp) ->
      entries_ok K Θ -> entries_ok ((fp, (Dfp, Bfp)) :: K) Θ.
  Proof.
    intros K fp Dfp Bfp; induction Θ as [| [fq V] Θ IH]; intros HK HKb Hd HΘ; [ exact I |].
    destruct HΘ as [[Dy By src prg u ch RbU ΘUy HKy HBy Hcly Hl Hr Hp Ht Hu Hsuby Hdomy HRy] HΘ].
    split; [| apply IH; [ exact HK | exact HKb | intros y Hy; apply Hd; right; exact Hy | exact HΘ ] ].
    apply (mk_entry_ok _ _ _ _ Dy By src prg u ch RbU ΘUy); try assumption.
    - simp kfind; rewrite path_beq_false by (eapply HK; eassumption); exact HKy.
    - simp kbt; rewrite path_beq_false by (eapply HK; eassumption); exact HBy.
    - apply closedK_cons; [ exact Hcly | intros z Hz; apply Hd; right; apply (sub_dom _ _ _ Hsuby), Hdomy, Hz ].
    - intros z Bz Hz; simp kbt; rewrite path_beq_false; [ exact (HRy _ _ Hz) | exact (HKb _ _ (HRy _ _ Hz)) ].
  Qed.

  Lemma ginv_nil : forall ch, ginv ch nil nil.
  Proof. intros; constructor; [ constructor | reflexivity | exact I | discriminate ]. Qed.

  Lemma nil_linv {ch Θ K} : ginv ch Θ K -> linv ch Θ K nil nil nil.
  Proof.
    intros G; constructor; [ exact G | discriminate | intros ?; cbn; tauto | intros ? ? [] | | intros ? ? ? [] ].
    constructor; constructor; constructor.
  Qed.

  Lemma rb_ok_nil : forall K, rb_ok K nil nil.
  Proof. intros; split; [ apply canon_nil | intros ? ? H; discriminate H ]. Qed.

  (** A command filled at the restriction, then run, is filled and run at
      the judgment's state, which has the same lookups. *)
  Lemma fill_lift {ch Θ K D B Ξ c c' r} :
    fill_cmd (gds_restrict D Θ) Ξ B c c' -> post_cmd ch Θ K D B Ξ c' r -> post_lcmd ch Θ K D B Ξ c r.
  Proof.
    intros Ha Hp ΘR RbR Hli Hrb; destruct (Hp _ _ Hli Hrb) as [ΘR' RbR' Hr Hli' Hrb' Hext Hgr].
    apply (mk_cmd_post _ _ _ _ _ ΘR' RbR'); try assumption.
    exists c'; split; [ exact (equiv_fill_cmd _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) Ha) | exact Hr ].
  Qed.


  (** ** One Step per Rule

      Each lemma proves the [post_*] of one branch of the executable from the
      checks that branch makes. *)

  Lemma def_ok {ch Θ K D B Ξ x b pv A M} :
    gs_fresh x Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_cmd ch Θ K D B Ξ (cc_def x b pv A (Some M)) (cst Θ K D B (gs_add x (gs_def b pv Ξ A M) Ξ)).
  Proof.
    intros Hfr HM ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_def x b pv A (Some M) ⇝ ΘR ⍮ gs_add x (gs_def b pv Ξ A M) Ξ ⍮ B ⍮ RbR).
    { constructor; [| exact Hfr ].
      exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HM). }
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR);
      [ exact Hr | exact (linv_run_same Hli (proj1 Hrb) Hr) | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  Lemma axiom_ok {ch Θ K D B Ξ x b pv A i} :
    gs_fresh x Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i ->
    post_cmd ch Θ K D B Ξ (cc_def x b pv A None) (cst Θ K D B (gs_add x (gs_axiom b pv Ξ A) Ξ)).
  Proof.
    intros Hfr HA ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_def x b pv A None ⇝ ΘR ⍮ gs_add x (gs_axiom b pv Ξ A) Ξ ⍮ B ⍮ RbR).
    { econstructor; [| exact Hfr ].
      exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HA). }
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR);
      [ exact Hr | exact (linv_run_same Hli (proj1 Hrb) Hr) | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  Lemma eval_check_ok {ch Θ K D B Ξ M A} :
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_cmd ch Θ K D B Ξ (cc_eval M (Some A)) (cst Θ K D B Ξ).
  Proof.
    intros HM ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_eval M (Some A) ⇝ ΘR ⍮ Ξ ⍮ B ⍮ RbR)
      by (constructor; exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HM)).
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [ exact Hr | exact Hli | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  (** A builtin binding, with the premises of [run_cmd_builtin] at the
      restriction. *)
  Lemma builtin_ok {ch Θ K D B Ξ E M W p Dd z s B'} :
    modexp_as_term E = Some M ->
    @alg_type_infer (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) W M ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : nf_to_exp W ->
    nf_is_universe W ->
    nbe (gds_restrict D Θ) Ξ (gs_tele Ξ) M (nf_to_exp W) (nf_indty p 0 nil) ->
    ind_lookup (gds_restrict D Θ) Ξ p = Some Dd -> nat_shape Dd = Some (z, s) -> ind_sort Dd = nat_sort ->
    bt_bind_nat B p = Some B' ->
    post_cmd ch Θ K D B Ξ (cc_builtin nat_kind E) (cst Θ K D B' Ξ).
  Proof.
    intros Ht HW HM Hu Hn Hl Hs Hsort Hb ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as He.
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_builtin nat_kind E ⇝ ΘR ⍮ Ξ ⍮ B' ⍮ RbR).
    { eapply run_cmd_builtin; [ exact Ht | exact (equiv_alg_infer _ _ _ _ _ _ He HW)
                         | exact (equiv_exp _ _ _ _ _ _ He (li_wf _ _ _ _ _ _ Hli) HM) | exact Hu
                         | exact (equiv_nbe _ _ _ He _ _ _ _ Hn)
                         | rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); exact Hl
                         | exact Hs | exact Hsort | exact Hb ]. }
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [ exact Hr | exact Hli | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  Lemma eval_infer_ok {ch Θ K D B Ξ M} (A : typ) :
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_cmd ch Θ K D B Ξ (cc_eval M None) (cst Θ K D B Ξ).
  Proof.
    intros HM ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_eval M None ⇝ ΘR ⍮ Ξ ⍮ B ⍮ RbR)
      by (econstructor; exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HM)).
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [ exact Hr | exact Hli | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  Lemma mod_pre {ch Θ K D Ξ x Δ} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> tele_ass Δ -> gs_fresh x Ξ -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    exists ΘR, linv ch Θ K D ΘR (gs_push (qname_in (gs_path Ξ) x) Δ Ξ).
  Proof. intros [ΘR Hli] Htel Hfr HΔ; exists ΘR; exact (proj2 (linv_push Hli Htel Hfr HΔ)). Qed.

  Lemma mod_ok {ch Θ K D B Ξ x pv Δ cs r mp Kf U Ξ2} :
    tele_ass Δ -> gs_fresh x Ξ -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    post_cmds ch Θ K D B (gs_push (qname_in (gs_path Ξ) x) Δ Ξ) cs r -> cstate_stack r = (mp, Kf, U) :: Ξ2 ->
    post_cmd ch Θ K D B Ξ (cc_mod x pv Δ cs) (cst (cstate_deps r) (cstate_k r) (cstate_dom r) (cstate_bt r) (gs_add x (ge_body pv Δ (gu_mod U)) Ξ)).
  Proof.
    intros Htel Hfr HΔ Hpost HΞ ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    destruct (linv_push Hli Htel Hfr HΔ) as [HΔ' Hli'].
    destruct (Hpost _ _ Hli' Hrb) as [ΘR' RbR' Hrun Hli2 Hrb2 Hext Hgr]; cbn beta in Hrun.
    rewrite HΞ in Hrun, Hli2.
    destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun) as [F HF]; injection HF as <- ->.
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_mod x pv Δ cs ⇝ ΘR' ⍮ gs_add x (ge_body pv Δ (gu_mod U)) Ξ ⍮ cstate_bt r ⍮ RbR')
      by (econstructor; eassumption).
    apply (mk_cmd_post _ _ _ _ _ ΘR' RbR' Hr); [| exact Hrb2 | assumption | assumption ].
    apply (linv_stack Hli2); [ exact (proj1 (linv_run_wf Hli (proj1 Hrb) Hr)) | exact (linv_run_stack Hli Hr) ].
  Qed.

  Lemma alias_ok {ch Θ K D B Ξ x pv Δ E} :
    tele_ass Δ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E -> gs_fresh x Ξ ->
    post_cmd ch Θ K D B Ξ (cc_alias x pv Δ E) (cst Θ K D B (gs_add x (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))) Ξ)).
  Proof.
    intros Htel HΔ HE Hfr ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as Heq.
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_alias x pv Δ E ⇝ ΘR ⍮ gs_add x (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))) Ξ ⍮ B ⍮ RbR)
      by (constructor; [ exact Htel | exact (equiv_ext _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HΔ)
                       | exact (equiv_modexp _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HE) | exact Hfr ]).
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR);
      [ exact Hr | exact (linv_run_same Hli (proj1 Hrb) Hr) | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  (** An inductive alias, with the premises of [run_cmd_ind_alias] at the
      restriction. *)
  Lemma indalias_ok {ch Θ K D B Ξ x pv Δ E M W} :
    tele_ass Δ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    modexp_as_term E = Some M ->
    @alg_type_infer (gc_mk (gds_restrict D Θ) Ξ) (Δ ++ gs_tele Ξ) W M ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ M : nf_to_exp W ->
    ind_former (gds_restrict D Θ) Ξ (Δ ++ gs_tele Ξ) M W ->
    gs_fresh x Ξ ->
    post_cmd ch Θ K D B Ξ (cc_ind_alias x pv Δ E) (cst Θ K D B (gs_add x (dm_entry Ξ pv Δ (nf_to_exp W) M E) Ξ)).
  Proof.
    intros Htel HΔ HE Ht HW HM Hf Hfr ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as Heq.
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_ind_alias x pv Δ E ⇝
                   ΘR ⍮ gs_add x (dm_entry Ξ pv Δ (nf_to_exp W) M E) Ξ ⍮ B ⍮ RbR).
    { eapply run_cmd_ind_alias; [ exact Htel | exact (equiv_ext _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HΔ)
                           | exact (equiv_modexp _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HE) | exact Ht
                           | exact (equiv_alg_infer _ _ _ _ _ _ Heq HW)
                           | exact (equiv_exp _ _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HM)
                           | exact (equiv_ind_former _ _ _ _ _ _ Heq Hf) | exact Hfr ]. }
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR);
      [ exact Hr | exact (linv_run_same Hli (proj1 Hrb) Hr) | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  (** A record alias, with the premises of [run_cmd_record_alias] at the
      restriction. *)
  Lemma recalias_ok {ch Θ K D B Ξ x pv Δ E M W} :
    tele_ass Δ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    modexp_as_term E = Some M ->
    @alg_type_infer (gc_mk (gds_restrict D Θ) Ξ) (Δ ++ gs_tele Ξ) W M ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ M : nf_to_exp W ->
    record_former (gds_restrict D Θ) Ξ (Δ ++ gs_tele Ξ) M W ->
    gs_fresh x Ξ ->
    post_cmd ch Θ K D B Ξ (cc_record_alias x pv Δ E) (cst Θ K D B (gs_add x (dm_entry Ξ pv Δ (nf_to_exp W) M E) Ξ)).
  Proof.
    intros Htel HΔ HE Ht HW HM Hf Hfr ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as Heq.
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_record_alias x pv Δ E ⇝
                   ΘR ⍮ gs_add x (dm_entry Ξ pv Δ (nf_to_exp W) M E) Ξ ⍮ B ⍮ RbR).
    { eapply run_cmd_record_alias; [ exact Htel | exact (equiv_ext _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HΔ)
                              | exact (equiv_modexp _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HE) | exact Ht
                              | exact (equiv_alg_infer _ _ _ _ _ _ Heq HW)
                              | exact (equiv_exp _ _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HM)
                              | exact (equiv_record_former _ _ _ _ _ _ Heq Hf) | exact Hfr ]. }
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR);
      [ exact Hr | exact (linv_run_same Hli (proj1 Hrb) Hr) | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  (** A unit the unit being run imported already: its record, kept in [K],
      is merged in again. *)
  Lemma load_in_ok {ch Θ K D B Ξ fp U BU B'} :
    In fp D -> gds_lookup Θ fp = Some U -> kbt K fp = Some BU -> bt_merge B BU = Some B' ->
    post_cmd ch Θ K D B Ξ (cc_load fp) (cst Θ K D B' Ξ).
  Proof.
    intros Hin HU HB Hm ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    apply (li_dom _ _ _ _ _ _ Hli), gds_dom_lookup in Hin.
    destruct (gds_lookup ΘR fp) as [V |] eqn:E'; [| contradiction ].
    destruct (proj1 (proj1 Hrb) _ _ E') as [BU' src prg u ch0 RbU ΘU EB _ _ _ _].
    pose proof (proj2 Hrb _ _ EB) as HB'; rewrite HB in HB'; injection HB' as <-.
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_load fp ⇝ ΘR ⍮ Ξ ⍮ B' ⍮ RbR) by (eapply run_cmd_load_filed; eassumption).
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [ exact Hr | exact Hli | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  (** A record kept in [K] is of a unit [K] has the closure of. *)
  Lemma kbt_kfind : forall K fp B, kbt K fp = Some B -> exists D, kfind K fp = Some D.
  Proof.
    induction K as [| [fq [Dq Bq]] K IH]; intros fp B H; simp kbt in H; [ discriminate |].
    simp kfind; destruct (path_beq fp fq); [ eauto | exact (IH _ _ H) ].
  Qed.

  (** Loading a filed unit that the unit being run has not imported yet:
      the judgment loads it, which the entry of [Θ] justifies once the chain
      is changed; it ends with the record [K] keeps. *)
  Lemma hit_linv {ch Θ K D Ξ fp U Dfp BU} :
    ~ In fp D -> gds_lookup Θ fp = Some U -> kfind K fp = Some Dfp -> kbt K fp = Some BU ->
    forall ΘR RbR, linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
    exists src prg u RbU ΘU, gds_lookup ΘR fp = None /\ ~ In fp ch /\ load_path fp = Some src /\
      read src = Some prg /\ prog_path prg = fp /\ to_core prg = Some u /\ run_unit (fp :: ch) u BU RbU ΘU U /\
      linv ch Θ K (p_union D (fp :: Dfp)) (gds_merge ΘR ((fp, U) :: ΘU)) Ξ /\
      rb_ok K (gds_merge ΘR ((fp, U) :: ΘU)) (bm_merge RbR ((fp, BU) :: RbU)).
  Proof.
    intros Hnin HU HK HB ΘR RbR Hli Hrb.
    pose proof (li_g _ _ _ _ _ _ Hli) as G.
    destruct (ginv_entry G _ _ HU)
      as [Dfp' BU' src prg u ch0 RbU ΘU HK' HB' Hcl Hl Hrd Hp Ht Hu Hsub Hdom HRU].
    rewrite HK in HK'; injection HK' as <-; rewrite HB in HB'; injection HB' as <-.
    assert (Hn : gds_lookup ΘR fp = None)
      by (apply gds_dom_none; intros Hin; apply Hnin, (li_dom _ _ _ _ _ _ Hli), Hin).
    assert (Hnch : ~ In fp ch) by (intros Hin; rewrite (gi_chain _ _ _ G _ Hin) in HU; discriminate).
    assert (Hu' : run_unit (fp :: ch) u BU RbU ΘU U).
    { apply (proj1 (proj2 (proj2 (run_chain_irrel load_path read to_core))) _ _ _ _ _ _ Hu ch).
      intros x [<- | Hin].
      - exact (proj1 (proj2 (proj2 (run_chain_fresh load_path read to_core))) _ _ _ _ _ _ Hu _ (or_introl eq_refl)).
      - exact (sub_none _ _ _ Hsub (gi_chain _ _ _ G _ Hin)). }
    destruct (load_wf load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ (li_wf _ _ _ _ _ _ Hli) (proj1 Hrb)
                (li_stack _ _ _ _ _ _ Hli) Hn Hnch Hl Hrd Ht Hu') as (Hwf' & Hc' & _).
    exists src, prg, u, RbU, ΘU; do 7 (split; [ assumption |]).
    split; [ constructor; [ exact G | | | | exact Hwf' | exact (li_stack _ _ _ _ _ _ Hli) ] |].
    - intros y V HV; apply merge_inv in HV as [HV | HV]; [ exact (li_sub _ _ _ _ _ _ Hli _ _ HV) |].
      cbn in HV; destruct (path_beq y fp) eqn:Hb; [| exact (Hsub _ _ HV) ].
      apply path_beq_true in Hb as ->; injection HV as <-; exact HU.
    - intros y; rewrite p_union_iff, dom_merge, dom_cons, <- (li_dom _ _ _ _ _ _ Hli y), <- (Hdom y); cbn [In].
      intuition congruence.
    - intros y Dy Hy HKy; apply p_union_iff in Hy as [Hy | [<- | Hy]]; intros z Hz; apply p_union_iff.
      + left; exact (li_closed _ _ _ _ _ _ Hli _ _ Hy HKy _ Hz).
      + rewrite HK in HKy; injection HKy as <-; right; right; exact Hz.
      + right; right; exact (Hcl _ _ Hy HKy _ Hz).
    - split; [ exact Hc' |].
      intros y By Hy; rewrite bm_lookup_merge in Hy; destruct (bm_lookup RbR y) eqn:E.
      + injection Hy as <-; exact (proj2 Hrb _ _ E).
      + cbn in Hy; destruct (path_beq y fp) eqn:Hb; [ apply path_beq_true in Hb as ->; injection Hy as <-; exact HB | exact (HRU _ _ Hy) ].
  Qed.

  Lemma load_hit_ok {ch Θ K D B Ξ fp U Dfp BU B'} :
    ~ In fp D -> gds_lookup Θ fp = Some U -> kfind K fp = Some Dfp -> kbt K fp = Some BU -> bt_merge B BU = Some B' ->
    post_cmd ch Θ K D B Ξ (cc_load fp) (cst Θ K (p_union D (fp :: Dfp)) B' Ξ).
  Proof.
    intros Hnin HU HK HB Hm ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    destruct (hit_linv Hnin HU HK HB _ _ Hli Hrb) as (src & prg & u & RbU & ΘU & Hn & Hnch & Hl & Hrd & Hp & Ht & Hu & Hli' & Hrb').
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_load fp ⇝ gds_merge ΘR ((fp, U) :: ΘU) ⍮ Ξ ⍮ B' ⍮ bm_merge RbR ((fp, BU) :: RbU))
      by (eapply run_cmd_load; eassumption).
    apply (mk_cmd_post _ _ _ _ _ (gds_merge ΘR ((fp, U) :: ΘU)) (bm_merge RbR ((fp, BU) :: RbU)));
      [ exact Hr | exact Hli' | exact Hrb' | apply ext_refl | apply grows_refl ].
  Qed.

  Lemma load_pre {ch Θ K D Ξ fp} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> gds_lookup Θ fp = None -> ~ In fp ch -> ginv (fp :: ch) Θ K.
  Proof.
    intros [ΘR Hli] Hn Hnch; pose proof (li_g _ _ _ _ _ _ Hli) as [].
    constructor; auto; intros x [<- | Hx]; auto.
  Qed.

  (** A loaded unit is filed on top of everything its run filed, which holds
      the state the judgment's run ended in, with the record it ended with;
      the bindings are [B'], that record merged in. *)
  Definition load_state (fp : path) (D : list path) (Ξ : gstack) (B' : builtins) (r : ustate) : cstate :=
    cst ((fp, us_unit r) :: us_deps r) ((fp, (us_dom r, us_bt r)) :: us_k r) (p_union D (fp :: us_dom r)) B' Ξ.

  Lemma load_linv {ch Θ K D Ξ fp src prg u r B'} :
    gds_lookup Θ fp = None -> ~ In fp ch ->
    load_path fp = Some src -> read src = Some prg -> prog_path prg = fp -> to_core prg = Some u ->
    post_unit (fp :: ch) Θ K u r -> forall ΘR RbR, linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
    exists RbU ΘU, gds_lookup ΘR fp = None /\ run_unit (fp :: ch) u (us_bt r) RbU ΘU (us_unit r) /\
      linv ch (cstate_deps (load_state fp D Ξ B' r)) (cstate_k (load_state fp D Ξ B' r)) (cstate_dom (load_state fp D Ξ B' r))
        (gds_merge ΘR ((fp, us_unit r) :: ΘU)) Ξ /\
      rb_ok (cstate_k (load_state fp D Ξ B' r)) (gds_merge ΘR ((fp, us_unit r) :: ΘU)) (bm_merge RbR ((fp, us_bt r) :: RbU)) /\
      ext Θ K (cstate_deps (load_state fp D Ξ B' r)) (cstate_k (load_state fp D Ξ B' r)) /\
      grows Θ (cstate_deps (load_state fp D Ξ B' r)) (cstate_dom (load_state fp D Ξ B' r)).
  Proof.
    intros Hn Hnch Hl Hrd Hp Ht Hpost ΘR RbR Hli Hrb.
    pose proof (li_g _ _ _ _ _ _ Hli) as G.
    assert (Gin : ginv (fp :: ch) Θ K) by (eapply load_pre; [ exists ΘR; exact Hli | assumption | assumption ]).
    destruct r as [Θ1 K1 Dfp B1 U]; unfold load_state; cbn [us_deps us_k us_dom us_bt us_unit cstate_deps cstate_k cstate_dom cstate_bt cstate_stack] in *.
    destruct (Hpost Gin) as [RbU ΘU Hu G1 Hsub1 Hdom1 Hcl1 HRU [Hext1 HextK HextB] Hgr1].
    cbn [us_deps us_k us_dom us_bt us_unit] in *.
    destruct (proj1 (proj2 (proj2 run_wf)) _ _ _ _ _ _ Hu) as (HwU & HcU & HUu); cbn [hd] in HUu.
    assert (HnR : gds_lookup ΘR fp = None) by exact (sub_none _ _ _ (li_sub _ _ _ _ _ _ Hli) Hn).
    destruct (load_wf load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ (li_wf _ _ _ _ _ _ Hli) (proj1 Hrb)
                (li_stack _ _ _ _ _ _ Hli) HnR Hnch Hl Hrd Ht Hu) as (Hwf' & Hc' & _).
    assert (Hn1 : gds_lookup Θ1 fp = None) by exact (gi_chain _ _ _ G1 _ (or_introl eq_refl)).
    set (ΘN := (fp, U) :: Θ1).
    assert (HwN : ⊢ᵍ ΘN ⍮ nil).
    { apply wf_gstack_file'; [ exact (gi_wf _ _ _ G1) | | exact Hn1 ].
      eapply unit_deps_grow; [ exact Hsub1 | exact (gi_wf _ _ _ G1) | exact Hn1 | exact HUu ]. }
    assert (Hsub1N : Θ1 ⊑ ΘN) by exact (gds_sub_cons _ _ _ Hn1).
    assert (HfpN : gds_lookup ΘN fp = Some U) by (cbn; rewrite path_beq_refl; reflexivity).
    assert (HsubU : ΘU ⊑ ΘN) by exact (gds_sub_trans _ _ _ Hsub1 Hsub1N).
    assert (HK1 : forall y Dy, kfind K1 y = Some Dy -> y <> fp)
      by (intros y Dy HKy ->; exact (gi_kdom _ _ _ G1 _ _ HKy Hn1)).
    assert (HKb1 : forall y By, kbt K1 y = Some By -> y <> fp)
      by (intros y By HKy; destruct (kbt_kfind _ _ _ HKy) as [Dy HKy']; exact (HK1 _ _ HKy')).
    assert (Hd1 : forall y, In y (gds_dom Θ1) -> y <> fp)
      by (intros y Hy ->; apply gds_dom_lookup in Hy; contradiction).
    assert (Hdfp : forall y, In y Dfp -> y <> fp)
      by (intros y Hy; apply Hd1, (sub_dom _ _ _ Hsub1), Hdom1, Hy).
    assert (HRU' : rb_in ((fp, (Dfp, B1)) :: K1) RbU)
      by (apply rb_in_cons; [ intros y By Hy; exact (HKb1 _ _ (HRU _ _ Hy)) | exact HRU ]).
    assert (GN : ginv ch ΘN ((fp, (Dfp, B1)) :: K1)).
    { constructor; [ exact HwN | | | ].
      - intros y Hy; cbn; rewrite path_beq_false by (intros ->; contradiction).
        exact (gi_chain _ _ _ G1 _ (or_intror Hy)).
      - split; [| exact (entries_ok_cons_K _ _ _ _ _ HK1 HKb1 Hd1 (gi_entry _ _ _ G1)) ].
        apply (mk_entry_ok _ _ _ _ Dfp B1 src prg u ch RbU ΘU);
          [ simp kfind; rewrite path_beq_refl; reflexivity | simp kbt; rewrite path_beq_refl; reflexivity
          | exact (closedK_cons _ _ _ _ _ Hcl1 Hdfp) | assumption .. ].
      - intros y Dy HKy; simp kfind in HKy; destruct (path_beq y fp) eqn:Hb.
        + apply path_beq_true in Hb as ->; rewrite HfpN; discriminate.
        + intros E; apply (gi_kdom _ _ _ G1 _ _ HKy), (sub_none _ _ _ Hsub1N), E. }
    assert (Hfresh : forall y, gds_lookup Θ y <> None -> y <> fp) by (intros y Hy ->; contradiction).
    exists RbU, ΘU; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack us_deps us_k us_dom us_bt us_unit].
    split; [ exact HnR | split; [ exact Hu |] ].
    split; [| split; [| split ] ].
    - constructor; [ exact GN | | | | exact Hwf' | exact (li_stack _ _ _ _ _ _ Hli) ].
      + intros y V HV; apply merge_inv in HV as [HV | HV].
        * exact (Hsub1N _ _ (Hext1 _ _ (li_sub _ _ _ _ _ _ Hli _ _ HV))).
        * cbn in HV; destruct (path_beq y fp) eqn:Hb; [| exact (HsubU _ _ HV) ].
          apply path_beq_true in Hb as ->; injection HV as <-; exact HfpN.
      + intros y; rewrite p_union_iff, dom_merge, dom_cons, <- (li_dom _ _ _ _ _ _ Hli y), <- (Hdom1 y); cbn [In].
        intuition congruence.
      + intros y Dy Hy HKy; simp kfind in HKy; destruct (path_beq y fp) eqn:Hb.
        * apply path_beq_true in Hb as ->; injection HKy as <-; intros z Hz; apply p_union_iff; right; right; exact Hz.
        * intros z Hz; apply p_union_iff; apply p_union_iff in Hy as [Hy | [<- | Hy]].
          -- left; pose proof (linv_in Hli _ Hy) as Hy'.
             destruct (gds_lookup Θ y) as [Vy |] eqn:Ey; [| contradiction ].
             destruct (ginv_entry G _ _ Ey) as [Dy' _ _ _ _ _ _ _ HKy' _ _ _ _ _ _ _ _ _ _].
             rewrite (HextK _ _ HKy') in HKy; injection HKy as <-.
             exact (li_closed _ _ _ _ _ _ Hli _ _ Hy HKy' _ Hz).
          -- rewrite path_beq_refl in Hb; discriminate.
          -- right; right; exact (Hcl1 _ _ Hy HKy _ Hz).
    - split; [ exact Hc' |].
      intros y By Hy; rewrite bm_lookup_merge in Hy; destruct (bm_lookup RbR y) eqn:E.
      + injection Hy as <-; simp kbt; rewrite path_beq_false; [ exact (HextB _ _ (proj2 Hrb _ _ E)) |].
        apply Hfresh; intros Hny; apply (proj2 (proj1 Hrb) _ _ E).
        destruct (gds_lookup ΘR y) eqn:Ey; [ exfalso; rewrite (li_sub _ _ _ _ _ _ Hli _ _ Ey) in Hny; discriminate | reflexivity ].
      + cbn in Hy; destruct (path_beq y fp) eqn:Hb.
        * apply path_beq_true in Hb as ->; injection Hy as <-; simp kbt; rewrite path_beq_refl; reflexivity.
        * exact (HRU' _ _ Hy).
    - constructor; [ exact (gds_sub_trans _ _ _ Hext1 Hsub1N) | |].
      + intros y Dy HKy; simp kfind; rewrite path_beq_false; [ exact (HextK _ _ HKy) |].
        intros ->; exact (gi_kdom _ _ _ G _ _ HKy Hn).
      + intros y By HKy; simp kbt; rewrite path_beq_false; [ exact (HextB _ _ HKy) |].
        destruct (kbt_kfind _ _ _ HKy) as [Dy HKy']; intros ->; exact (gi_kdom _ _ _ G _ _ HKy' Hn).
    - intros y Hy; unfold ΘN in Hy; apply dom_cons in Hy as [-> | Hy].
      + right; apply p_union_iff; right; left; reflexivity.
      + destruct (Hgr1 _ Hy) as [H | H]; [ left; exact H | right; apply p_union_iff; right; right; exact H ].
  Qed.

  Lemma load_ok {ch Θ K D B Ξ fp src prg u r B'} :
    gds_lookup Θ fp = None -> ~ In fp ch ->
    load_path fp = Some src -> read src = Some prg -> prog_path prg = fp -> to_core prg = Some u ->
    post_unit (fp :: ch) Θ K u r -> bt_merge B (us_bt r) = Some B' ->
    post_cmd ch Θ K D B Ξ (cc_load fp) (load_state fp D Ξ B' r).
  Proof.
    intros Hn Hnch Hl Hrd Hp Ht Hpost Hm ΘR RbR Hli Hrb.
    destruct (load_linv (B' := B') Hn Hnch Hl Hrd Hp Ht Hpost _ _ Hli Hrb) as (RbU & ΘU & HnR & Hu & Hli' & Hrb' & Hext & Hgr).
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_load fp ⇝
                   gds_merge ΘR ((fp, us_unit r) :: ΘU) ⍮ Ξ ⍮ B' ⍮ bm_merge RbR ((fp, us_bt r) :: RbU))
      by (eapply run_cmd_load; eassumption).
    apply (mk_cmd_post _ _ _ _ _ (gds_merge ΘR ((fp, us_unit r) :: ΘU)) (bm_merge RbR ((fp, us_bt r) :: RbU)));
      [ exact Hr | exact Hli' | exact Hrb' | exact Hext | exact Hgr ].
  Qed.

  (** ** The Generated Entries of an Import *)

  Definition post_gens ch Θ K D Ξ gs Ξ' : Prop :=
    forall ΘR, linv ch Θ K D ΘR Ξ -> gens_run ΘR Ξ gs Ξ' /\ linv ch Θ K D ΘR Ξ'.

  Lemma gens_nil_ok {ch Θ K D Ξ} : post_gens ch Θ K D Ξ nil Ξ.
  Proof. intros ΘR Hli; split; [ constructor | exact Hli ]. Qed.

  Lemma gdef_step {ch Θ K D ΘR Ξ d pv A M} :
    linv ch Θ K D ΘR Ξ -> gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    ΘR ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A /\ linv ch Θ K D ΘR (gs_add d (gs_def true pv Ξ A M) Ξ).
  Proof.
    intros Hli Hfr HM.
    pose proof (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HM) as HM'.
    split; [ exact HM' |].
    exact (linv_stack Hli (add_def_wf _ _ _ _ _ _ _ (li_wf _ _ _ _ _ _ Hli) HM' Hfr)
             (stack_in_add _ _ _ _ (li_stack _ _ _ _ _ _ Hli))).
  Qed.

  Lemma galias_step {ch Θ K D ΘR Ξ d pv E} :
    linv ch Θ K D ΘR Ξ -> gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    ΘR ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E /\ linv ch Θ K D ΘR (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ).
  Proof.
    intros Hli Hfr HE.
    pose proof (equiv_modexp _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HE) as HE'.
    split; [ exact HE' |].
    apply (linv_stack Hli); [| exact (stack_in_add _ _ _ _ (li_stack _ _ _ _ _ _ Hli)) ].
    apply (add_alias_wf _ _ _ _ nil); [ exact (li_wf _ _ _ _ _ _ Hli) | constructor | | exact HE' | exact Hfr ].
    constructor; exact (presup_modexp_eq_ctx HE').
  Qed.

  Lemma gdef_pre {ch Θ K D Ξ d pv A M} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    exists ΘR, linv ch Θ K D ΘR (gs_add d (gs_def true pv Ξ A M) Ξ).
  Proof. intros [ΘR Hli] Hfr HM; exists ΘR; exact (proj2 (gdef_step Hli Hfr HM)). Qed.

  Lemma galias_pre {ch Θ K D Ξ d pv E} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    exists ΘR, linv ch Θ K D ΘR (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ).
  Proof. intros [ΘR Hli] Hfr HE; exists ΘR; exact (proj2 (galias_step Hli Hfr HE)). Qed.

  Lemma gdef_ok {ch Θ K D Ξ d pv A M gs Ξ'} :
    gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_gens ch Θ K D (gs_add d (gs_def true pv Ξ A M) Ξ) gs Ξ' ->
    post_gens ch Θ K D Ξ (ig_def d pv A M :: gs) Ξ'.
  Proof.
    intros Hfr HM Hp ΘR Hli; destruct (gdef_step (pv := pv) Hli Hfr HM) as [HM' Hli'].
    destruct (Hp _ Hli') as [Hg Hli2]; split; [ constructor; assumption | exact Hli2 ].
  Qed.

  Lemma galias_ok {ch Θ K D Ξ d pv E gs Ξ'} :
    gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    post_gens ch Θ K D (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ) gs Ξ' ->
    post_gens ch Θ K D Ξ (ig_alias d pv E :: gs) Ξ'.
  Proof.
    intros Hfr HE Hp ΘR Hli; destruct (galias_step (pv := pv) Hli Hfr HE) as [HE' Hli'].
    destruct (Hp _ Hli') as [Hg Hli2]; split; [ constructor; assumption | exact Hli2 ].
  Qed.

  (** A generated definition with a module part, its term [M] of the type
      [W] inferred for it and its module part the alias of [E]. *)
  Lemma gdm_step {ch Θ K D ΘR Ξ d pv M E W} :
    linv ch Θ K D ΘR Ξ -> gs_fresh d Ξ ->
    @alg_type_infer (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) W M ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : nf_to_exp W ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    @alg_type_infer (gc_mk ΘR Ξ) (gs_tele Ξ) W M /\ ΘR ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : nf_to_exp W /\
    ΘR ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E /\ linv ch Θ K D ΘR (gs_add d (dm_entry Ξ pv nil (nf_to_exp W) M E) Ξ).
  Proof.
    intros Hli Hfr HW HM HE.
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as Heq.
    pose proof (equiv_exp _ _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HM) as HM'.
    pose proof (equiv_modexp _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HE) as HE'.
    split; [ exact (equiv_alg_infer _ _ _ _ _ _ Heq HW) | split; [ exact HM' | split; [ exact HE' |] ] ].
    apply (linv_stack Hli); [| exact (stack_in_add _ _ _ _ (li_stack _ _ _ _ _ _ Hli)) ].
    apply (add_dm_wf _ _ _ _ nil); [ exact (li_wf _ _ _ _ _ _ Hli) | constructor | | exact HM' | exact HE' | exact Hfr ].
    constructor; exact (presup_exp_ctx HM').
  Qed.

  (** The invariant after a generated definition with a module part. *)
  Lemma gdm_pre {ch Θ K D Ξ d pv M E W} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> gs_fresh d Ξ ->
    @alg_type_infer (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) W M ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : nf_to_exp W ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    exists ΘR, linv ch Θ K D ΘR (gs_add d (dm_entry Ξ pv nil (nf_to_exp W) M E) Ξ).
  Proof. intros [ΘR Hli] Hfr HW HM HE; exists ΘR; exact (proj2 (proj2 (proj2 (gdm_step Hli Hfr HW HM HE)))). Qed.

  (** A generated definition with a module part, then the rest, run as
      [gens_run_def_mod] runs them. *)
  Lemma gdm_ok {ch Θ K D Ξ d pv A M E W gs Ξ'} :
    gs_fresh d Ξ ->
    @alg_type_infer (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) W M ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : nf_to_exp W ->
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    post_gens ch Θ K D (gs_add d (dm_entry Ξ pv nil (nf_to_exp W) M E) Ξ) gs Ξ' ->
    post_gens ch Θ K D Ξ (ig_def_mod d pv A M E :: gs) Ξ'.
  Proof.
    intros Hfr HW HM HE Hp ΘR Hli; destruct (gdm_step (pv := pv) Hli Hfr HW HM HE) as (HW' & HM' & HE' & Hli').
    destruct (Hp _ Hli') as [Hg Hli2]; split; [ econstructor; eassumption | exact Hli2 ].
  Qed.

  (** An import declares what its items generate, which files nothing. *)
  (** What an open generates is read off descriptions, which read the
      dependencies through their lookups alone. *)
  Lemma open_gens_equiv : forall Θ1 Θ2 Ξ Γ H its gs, gds_equiv Θ1 Θ2 ->
      open_gens Θ1 Ξ Γ H its gs -> open_gens Θ2 Ξ Γ H its gs.
  Proof.
    intros * He [R Rm HR HRm Hg Hok].
    pose proof (gds_equiv_mdenote_all _ _ Ξ He) as (H1 & _ & _ & _ & H5).
    apply (mk_open_gens _ _ _ _ _ _ R Rm); [ exact (H1 _ _ _ HR) | | exact (H5 _ _ _ _ Hg) | exact Hok ].
    exact HRm.
  Qed.

  Lemma import_ok {ch Θ K D B Ξ E its gs Ξ'} (Hg : ⊢ᵍ gds_restrict D Θ ⍮ Ξ)
    (HE : gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E) :
    import_gen _ _ Hg (gs_tele Ξ) E E HE its = xok gs ->
    post_gens ch Θ K D Ξ gs Ξ' ->
    post_cmd ch Θ K D B Ξ (cc_open E its) (cst Θ K D B Ξ').
  Proof.
    intros Hgen Hgs ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    destruct (Hgs _ Hli) as [Hr Hli'].
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as Heq.
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [| exact Hli' | exact Hrb | apply ext_refl | apply grows_refl ].
    eapply run_cmd_open; [ exact (equiv_modexp _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HE) | | exact Hr ].
    apply (import_gen_spec _ _ Hg) in Hgen.
    exact (open_gens_equiv _ _ _ _ _ _ _ Heq Hgen).
  Qed.

  (** ** Groups *)

  (** The recursor module of a group reads the global context only for
      the names of the members its views are of. *)
  Lemma equiv_grec_mod_cmd : forall Θ1 Θ2 Ξ pq Dd Δu, gds_equiv Θ1 Θ2 ->
      grec_mod_cmd Θ1 Ξ pq Dd Δu = grec_mod_cmd Θ2 Ξ pq Dd Δu.
  Proof.
    intros * He; unfold grec_mod_cmd, grec_names.
    assert (Hn : forall p j, member_name Θ1 Ξ p j = member_name Θ2 Ξ p j)
      by (intros; unfold member_name; rewrite (gds_equiv_ind_lookup _ _ _ _ He); reflexivity).
    assert (Hm : List.map (grec_member_name Θ1 Ξ) (ind_members Dd) = List.map (grec_member_name Θ2 Ξ) (ind_members Dd)).
    { apply List.map_ext; intros M; unfold grec_member_name; destruct (im_head M) as [pm | qc k Is vm]; [ reflexivity |].
      rewrite Hn; f_equal; f_equal; apply List.map_ext; intros I.
      destruct (app_head I); try reflexivity; rewrite Hn; reflexivity. }
    rewrite Hm; reflexivity.
  Qed.

  Lemma equiv_rec_cmds : forall Θ1 Θ2 Ξ R pq Dd, gds_equiv Θ1 Θ2 -> rec_cmds Θ1 Ξ R pq Dd = rec_cmds Θ2 Ξ R pq Dd.
  Proof. intros * He; unfold rec_cmds; rewrite (equiv_grec_mod_cmd _ _ _ _ _ _ He); reflexivity. Qed.

  (** So do the commands of a declared member's module. *)
  Lemma equiv_ind_mod_cmds : forall Θ1 Θ2 Ξ R pq Dd k M, gds_equiv Θ1 Θ2 ->
      ind_mod_cmds Θ1 Ξ R pq Dd k M = ind_mod_cmds Θ2 Ξ R pq Dd k M.
  Proof. intros * He; unfold ind_mod_cmds, ind_grec_cmds; rewrite (equiv_grec_mod_cmd _ _ _ _ _ _ He); reflexivity. Qed.

  (** The first of the members [xs] is well formed with an empty module,
      where it is declared. *)
  Definition head_entry ch Θ K D Ξ pv pq Dd k (xs : list string) : Prop :=
    match xs with
    | nil => True
    | x :: _ => forall ΘR, linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k Dd ⋄
    end.

  (** A later member is well formed with an empty module where it is
      declared. *)
  Lemma later_head_entry {ch Θ K D Ξ pv R pq Dd k xs} : mems_pre Ξ R pq Dd (S k) xs ->
      head_entry ch Θ K D Ξ pv pq Dd (S k) xs.
  Proof.
    intros Hp; destruct xs as [| x xs]; [ exact I |]; intros ΘR Hli.
    destruct (mems_pre_later _ _ _ _ _ _ Hp ltac:(apply PeanoNat.Nat.lt_0_succ)) as [mq Kq Δ Φ Ξ0 y0 pv0 Φm -> He ->].
    destruct (mems_pre_heads _ _ _ _ _ _ Hp 0 x eq_refl) as (M & HM & Hh); rewrite PeanoNat.Nat.add_0_r in HM.
    pose proof (mems_pre_count _ _ _ _ _ _ Hp) as Hc; cbn [List.length] in Hc.
    eapply later_member_entry;
      [ exact (li_wf _ _ _ _ _ _ Hli) | exact He | exact HM | apply PeanoNat.Nat.lt_0_succ
      | eapply PeanoNat.Nat.lt_le_trans; [| exact Hc ]; rewrite PeanoNat.Nat.add_succ_r; apply PeanoNat.Nat.lt_succ_r, PeanoNat.Nat.le_add_r
      | exact Hh | exact (mems_pre_uparams _ _ _ _ _ _ Hp) ].
  Qed.

  (** The first member is, by the group checked at its views' instances. *)
  Lemma first_head_entry {ch Θ K D Ξ pv R pq Dd xs IsS} : mems_pre Ξ R pq Dd 0 xs ->
      ind_nil_at (gds_restrict D Θ) Ξ pq Dd IsS -> head_entry ch Θ K D Ξ pv pq Dd 0 xs.
  Proof.
    intros Hp Hnil; destruct xs as [| x xs]; [ exact I |]; intros ΘR Hli.
    rewrite <- (mems_pre_first _ _ _ _ _ _ Hp eq_refl x xs eq_refl).
    exact (ind_nil_at_entry _ _ _ _ _
             (equiv_ind_nil_at _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) _ _ _ Hnil) pv).
  Qed.

  (** A mutual definition, with the premises of [run_cmd_mdef] at the
      restriction: its definitions are filed as [mdefs_stack] says. *)
  Lemma mdef_ok {ch Θ K D B Ξ b pv Δ f0 fs pq m0 Ps Dd Us ms} :
    tele_ass Δ ->
    ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    mdef_group (gds_restrict D Θ) Ξ Δ f0 fs pq m0 Ps Dd Us ms ->
    mdefs_run (gds_restrict D Θ) b pv (mdef_defs pq Dd Us Δ (f0 :: fs) ms) Ξ
      (mdefs_stack b pv (mdef_defs pq Dd Us Δ (f0 :: fs) ms) Ξ) ->
    post_cmd ch Θ K D B Ξ (cc_mdef b pv Δ (f0 :: fs))
      (cst Θ K D B (mdefs_stack b pv (mdef_defs pq Dd Us Δ (f0 :: fs) ms) Ξ)).
  Proof.
    intros Htel HΔ Hgp Hr ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as Heq.
    pose proof (li_wf _ _ _ _ _ _ Hli) as HΞ.
    assert (Hrun : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_mdef b pv Δ (f0 :: fs) ⇝
                     ΘR ⍮ mdefs_stack b pv (mdef_defs pq Dd Us Δ (f0 :: fs) ms) Ξ ⍮ B ⍮ RbR).
    { eapply run_cmd_mdef;
        [ exact Htel | exact (equiv_ctx _ _ _ _ Heq HΞ HΔ) | exact (equiv_mdef_group _ _ _ _ _ _ _ _ _ _ _ _ Heq HΞ Hgp)
        | exact (equiv_mdefs_run _ _ _ _ _ _ _ Heq HΞ Hr) ]. }
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR);
      [ exact Hrun | exact (linv_run_same Hli (proj1 Hrb) Hrun) | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  (** The rejection of an argument the classification does not accept. *)
  Definition cls_msg (x c y : string) (r : nat) : string :=
    match r with
    | 0 => "the argument " ++ y ++ " of " ++ c ++ " depends on a recursive argument"
    | 2 => x ++ " occurs in the domain of a function in the argument " ++ y ++ " of " ++ c ++
             ", which is not strictly positive"
    | 3 => x ++ " is not applied to its uniform parameters as declared in the argument " ++ y ++ " of " ++ c
    | 4 => x ++ " occurs in the argument " ++ y ++ " of " ++ c ++
             " under a head that does not compute (an opaque definition, an axiom or a parameter)"
    | _ => x ++ " occurs in a non-positive position in the argument " ++ y ++ " of " ++ c
    end.

  (** The records [K] keeps of the units of [ΘR]: the judgment's records
      exist whenever its state does. *)
  Fixpoint rb_of (K : kmap) (Θ : gdeps) : bmap :=
    match Θ with
    | nil => nil
    | (fp, _) :: Θ' => match kbt K fp with Some B => (fp, B) :: rb_of K Θ' | None => rb_of K Θ' end
    end.

  Lemma bm_lookup_rb_of : forall K Θ fp,
      bm_lookup (rb_of K Θ) fp = match gds_lookup Θ fp with Some _ => kbt K fp | None => None end.
  Proof.
    intros K; induction Θ as [| [fq V] Θ IH]; intros fp; [ reflexivity |]; cbn [rb_of gds_lookup].
    destruct (kbt K fq) as [Bq |] eqn:Eq; cbn [bm_lookup]; destruct (path_beq fp fq) eqn:Hb;
      try (apply path_beq_true in Hb as ->); rewrite ?IH; try reflexivity;
      try (symmetry; exact Eq); destruct (gds_lookup Θ fq); congruence.
  Qed.

  Lemma linv_rb {ch Θ K D ΘR Ξ} : linv ch Θ K D ΘR Ξ -> exists RbR, rb_ok K ΘR RbR.
  Proof.
    intros Hli; exists (rb_of K ΘR); split; [ split |].
    - intros fp U HU.
      destruct (ginv_entry (li_g _ _ _ _ _ _ Hli) _ _ (li_sub _ _ _ _ _ _ Hli _ _ HU))
        as [D0 BU src prg u ch0 RbU ΘU _ HB _ Hl Hr _ Ht Hu _ _ _].
      apply (mk_canon_entry _ _ _ _ _ _ BU src prg u ch0 RbU ΘU); [ rewrite bm_lookup_rb_of, HU; exact HB | assumption .. ].
    - intros fp BU HB; rewrite bm_lookup_rb_of in HB; destruct (gds_lookup ΘR fp); [ discriminate | discriminate HB ].
    - intros fp BU HB; rewrite bm_lookup_rb_of in HB; destruct (gds_lookup ΘR fp); [ exact HB | discriminate HB ].
  Qed.

  Lemma nil_ok {ch Θ K D B Ξ} : post_cmds ch Θ K D B Ξ nil (cst Θ K D B Ξ).
  Proof.
    intros ΘR RbR Hli Hrb.
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [ constructor | exact Hli | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  Lemma cons_pre {ch Θ K D B Ξ c r} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> post_lcmd ch Θ K D B Ξ c r ->
    exists ΘR, linv ch (cstate_deps r) (cstate_k r) (cstate_dom r) ΘR (cstate_stack r).
  Proof.
    intros [ΘR Hli] Hp; destruct (linv_rb Hli) as [RbR Hrb].
    destruct (Hp _ _ Hli Hrb) as [ΘR' RbR' _ Hli' _ _ _]; eauto.
  Qed.

  (** The imports of a later step include those of an earlier one. *)
  Lemma dom_grows {ch Θ1 K1 D1 B1 RbR1 ΘR1 Ξ1 Θ2 K2 D2 B2 RbR2 ΘR2 Ξ2 cs} :
    linv ch Θ1 K1 D1 ΘR1 Ξ1 -> canon RbR1 ΘR1 -> ΘR1 ⍮ Ξ1 ⍮ B1 ⍮ RbR1 ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR2 ⍮ Ξ2 ⍮ B2 ⍮ RbR2 ->
    linv ch Θ2 K2 D2 ΘR2 Ξ2 -> incl D1 D2.
  Proof.
    intros Hli1 Hc Hr Hli2 x Hx.
    destruct (proj1 (proj2 run_wf) _ _ _ _ _ _ _ _ _ _ Hr (li_wf _ _ _ _ _ _ Hli1) Hc
                (li_stack _ _ _ _ _ _ Hli1)) as (_ & _ & Hs & _).
    apply (li_dom _ _ _ _ _ _ Hli2), (sub_dom _ _ _ Hs), (li_dom _ _ _ _ _ _ Hli1), Hx.
  Qed.

  Lemma cons_ok {ch Θ K D B Ξ c cs r1 r2} :
    acc_ok (gds_restrict D Θ) Ξ (cmd_refs c) ->
    post_lcmd ch Θ K D B Ξ c r1 -> post_cmds ch (cstate_deps r1) (cstate_k r1) (cstate_dom r1) (cstate_bt r1) (cstate_stack r1) cs r2 ->
    post_cmds ch Θ K D B Ξ (c :: cs) r2.
  Proof.
    intros Hac H1 H2 ΘR RbR Hli Hrb.
    pose proof (equiv_acc _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) Hac) as Hac'.
    destruct (H1 _ _ Hli Hrb) as [ΘR1 RbR1 (c3 & Ha & Hr1) Hli1 Hrb1 He1 Hg1].
    destruct (H2 _ _ Hli1 Hrb1) as [ΘR2 RbR2 Hr2 Hli2 Hrb2 He2 Hg2]; cbn beta in Hr2.
    apply (mk_cmd_post _ _ _ _ _ ΘR2 RbR2); [ econstructor; eassumption | exact Hli2 | exact Hrb2
                                            | eapply ext_trans; eassumption |].
    intros x Hx; destruct (Hg2 _ Hx) as [Hx1 | Hx1]; [| right; exact Hx1 ].
    destruct (Hg1 _ Hx1) as [Hx0 | Hx0]; [ left; exact Hx0 | right; exact (dom_grows Hli1 (proj1 Hrb1) Hr2 Hli2 _ Hx0) ].
  Qed.

  (** Growth composes, when the imports of the later step include those
      of the earlier one. *)
  Lemma grows_trans {Θ0 Θ1 Θ2 D1 D2} : grows Θ0 Θ1 D1 -> grows Θ1 Θ2 D2 -> incl D1 D2 -> grows Θ0 Θ2 D2.
  Proof.
    intros H1 H2 Hi x Hx; destruct (H2 _ Hx) as [Hx1 | Hx1]; [| right; exact Hx1 ].
    destruct (H1 _ Hx1) as [Hx0 | Hx0]; [ left; exact Hx0 | right; exact (Hi _ Hx0) ].
  Qed.

  (** *** Groups *)

  (** The frame of a declared member's module, opened where the member is
      declared, keeps the invariant. *)
  Lemma linv_push_ind {ch Θ K D ΘR Ξ x pv R pq Dd k} :
    linv ch Θ K D ΘR Ξ -> gs_fresh x Ξ -> ind_uparams Dd = (raw_decl_uparams R ++ gs_tele Ξ)%list ->
    ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k Dd ⋄ ->
    linv ch Θ K D ΘR (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ).
  Proof.
    intros Hli Hfr Hu HE; destruct (ind_nil_entry_uparams _ _ _ _ _ _ _ _ HE Hu) as [Htel HΔ].
    apply (linv_stack Hli); [| exact (stack_in_push_ind _ _ _ _ _ _ _ (li_stack _ _ _ _ _ _ Hli) Hfr) ].
    destruct Ξ as [| [[mq Kq] Uq] Ξ0]; [ contradiction |].
    apply wf_gstack_cons; [ exact (li_wf _ _ _ _ _ _ Hli) | eapply wf_gmod_ind_nil; eassumption |].
    cbn; exists x; split; [ reflexivity | exact Hfr ].
  Qed.

  Lemma push_ind_pre {ch Θ K D Ξ x pv R pq Dd k} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> gs_fresh x Ξ -> ind_uparams Dd = (raw_decl_uparams R ++ gs_tele Ξ)%list ->
    (forall ΘR, linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k Dd ⋄) ->
    exists ΘR, linv ch Θ K D ΘR (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ).
  Proof. intros [ΘR Hli] Hfr Hu HE; exists ΘR; exact (linv_push_ind Hli Hfr Hu (HE _ Hli)). Qed.

  (** A declared member's module, its commands run in its frame by [r1]:
      the frame closes into the member's entry, as [run_ind_members_cons] files it. *)
  Lemma member_ok {ch Θ K D B Ξ pv R pq Dd k x M r1 mp Kf U Ξ2} :
    gs_fresh x Ξ -> ind_uparams Dd = (raw_decl_uparams R ++ gs_tele Ξ)%list ->
    (forall ΘR, linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k Dd ⋄) ->
    post_cmds ch Θ K D B (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ) (ind_mod_cmds (gds_restrict D Θ) (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ) R pq Dd k M) r1 ->
    cstate_stack r1 = (mp, Kf, U) :: Ξ2 ->
    forall ΘR RbR, linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      cmd_post (fun RbR' ΘR' => ΘR ⍮ gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ ⍮ B ⍮ RbR
                                  ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩
                                  ind_mod_cmds ΘR (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ) R pq Dd k M ⇝*
                                  ΘR' ⍮ (mp, Kf, U) :: Ξ ⍮ cstate_bt r1 ⍮ RbR') ch Θ K
        (cst (cstate_deps r1) (cstate_k r1) (cstate_dom r1) (cstate_bt r1) (gs_add x (ge_ind pv pq k Dd (gu_mod U)) Ξ)).
  Proof.
    intros Hfr Hu HE Hpost HΞ ΘR RbR Hli Hrb.
    pose proof (HE _ Hli) as HE0.
    pose proof (linv_push_ind Hli Hfr Hu HE0) as Hli'.
    destruct (Hpost _ _ Hli' Hrb) as [ΘR1 RbR1 Hrun Hli1 Hrb1 Hext Hgr]; cbn beta in Hrun.
    rewrite HΞ in Hrun, Hli1.
    rewrite <- (equiv_ind_mod_cmds _ _ _ _ _ _ _ _ (linv_equiv Hli)) in Hrun.
    destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun) as [F HF]; injection HF as _ ->.
    destruct (ind_member_run_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (li_wf _ _ _ _ _ _ Hli) Hu Hfr HE0 Hrun)
      as [HΘ _ _ Hw _]; subst ΘR1.
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR1 Hrun); cbn [cstate_deps cstate_k cstate_dom cstate_stack]; [| exact Hrb1 | exact Hext | exact Hgr ].
    apply (linv_stack Hli1); [ exact Hw | exact (stack_in_add _ _ _ _ (li_stack _ _ _ _ _ _ Hli)) ].
  Qed.

  Lemma member_pre {ch Θ K D B Ξ pv R pq Dd k x M r1 mp Kf U Ξ2} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> gs_fresh x Ξ -> ind_uparams Dd = (raw_decl_uparams R ++ gs_tele Ξ)%list ->
    (forall ΘR, linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k Dd ⋄) ->
    post_cmds ch Θ K D B (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ) (ind_mod_cmds (gds_restrict D Θ) (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ) R pq Dd k M) r1 ->
    cstate_stack r1 = (mp, Kf, U) :: Ξ2 ->
    exists ΘR, linv ch (cstate_deps r1) (cstate_k r1) (cstate_dom r1) ΘR (gs_add x (ge_ind pv pq k Dd (gu_mod U)) Ξ).
  Proof.
    intros [ΘR Hli] Hfr Hu HE Hpost HΞ; destruct (linv_rb Hli) as [RbR Hrb].
    destruct (member_ok Hfr Hu HE Hpost HΞ _ _ Hli Hrb) as [ΘR' RbR' _ Hli' _ _ _]; eauto.
  Qed.

  (** What a run of the declared members [k], [k + 1], … named [xs] proves. *)
  Definition post_mems ch Θ K D B Ξ pv R pq Dd k xs (r : cstate) : Prop :=
    forall ΘR RbR, linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      cmd_post (fun RbR' ΘR' => run_ind_members load_path read to_core ch B RbR ΘR Ξ pv R pq Dd k xs
                                  (cstate_bt r) RbR' ΘR' (cstate_stack r)) ch Θ K r.

  Lemma mems_nil_ok {ch Θ K D B Ξ pv R pq Dd k} : post_mems ch Θ K D B Ξ pv R pq Dd k nil (cst Θ K D B Ξ).
  Proof.
    intros ΘR RbR Hli Hrb.
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [ constructor | exact Hli | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  Lemma mems_cons_ok {ch Θ K D B Ξ pv R pq Dd k x xs M r1 mp Kf U Ξ2 r2} :
    ind_member Dd k = Some M -> gs_fresh x Ξ -> ind_uparams Dd = (raw_decl_uparams R ++ gs_tele Ξ)%list ->
    (forall ΘR, linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k Dd ⋄) ->
    post_cmds ch Θ K D B (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ) (ind_mod_cmds (gds_restrict D Θ) (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ) R pq Dd k M) r1 ->
    cstate_stack r1 = (mp, Kf, U) :: Ξ2 ->
    post_mems ch (cstate_deps r1) (cstate_k r1) (cstate_dom r1) (cstate_bt r1) (gs_add x (ge_ind pv pq k Dd (gu_mod U)) Ξ) pv R pq Dd (S k) xs r2 ->
    post_mems ch Θ K D B Ξ pv R pq Dd k (x :: xs) r2.
  Proof.
    intros HM Hfr Hu HE Hpost HΞ H2 ΘR RbR Hli Hrb.
    destruct (member_ok Hfr Hu HE Hpost HΞ _ _ Hli Hrb) as [ΘR1 RbR1 Hr1 Hli1 Hrb1 He1 Hg1];
      cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack] in *.
    destruct (H2 _ _ Hli1 Hrb1) as [ΘR2 RbR2 Hr2 Hli2 Hrb2 He2 Hg2]; cbn beta in Hr2.
    destruct (ind_members_run_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr2 (li_wf _ _ _ _ _ _ Hli1)
                ltac:(rewrite gs_tele_add; exact Hu)) as [HΘ _ _ _ _].
    apply (mk_cmd_post _ _ _ _ _ ΘR2 RbR2);
      [ eapply run_ind_members_cons; [ exact HM | exact Hfr | exact (HE _ Hli) | exact Hr1 | exact Hr2 ]
      | exact Hli2 | exact Hrb2 | eapply ext_trans; eassumption |].
    apply (grows_trans Hg1 Hg2); intros y Hy.
    apply (li_dom _ _ _ _ _ _ Hli2); rewrite HΘ; apply (li_dom _ _ _ _ _ _ Hli1); exact Hy.
  Qed.

  Lemma mems_post_pre {ch Θ K D B Ξ pv R pq Dd k xs r} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> post_mems ch Θ K D B Ξ pv R pq Dd k xs r ->
    exists ΘR, linv ch (cstate_deps r) (cstate_k r) (cstate_dom r) ΘR (cstate_stack r).
  Proof.
    intros [ΘR Hli] Hp; destruct (linv_rb Hli) as [RbR Hrb].
    destruct (Hp _ _ Hli Hrb) as [ΘR' RbR' _ Hli' _ _ _]; eauto.
  Qed.

  (** A group declaration, with the premises of [run_cmd_ind_case] at the
      restriction: its declared members, each with its module, then its
      recursor module, if any, from where they end. *)
  Lemma ind_ok {ch Θ K D B Ξ pv R Mr0 Mrs csD Vs Ss csV Nvs Dd r1 r2} :
    raw_decl_members R = Mr0 :: Mrs ->
    Forall (fun Mr => raw_member_sort Mr = raw_member_sort Mr0) Mrs ->
    Forall2 (rm_cls (gds_restrict D Θ) Ξ R) (raw_decl_members R) csD ->
    Forall2 (view_sibs (gds_restrict D Θ) Ξ R) Vs Ss ->
    Forall2 (view_cls (gds_restrict D Θ) Ξ R) Vs csV ->
    Forall2 (view_nps (gds_restrict D Θ) Ξ R) Vs Nvs ->
    views_bfs (sibs_tbl Vs Ss) (meets_tbl Vs csV) nil (List.concat (List.map rcons_views csD)) Vs ->
    rd_filed (gds_restrict D Θ) Ξ R Vs Ss csD csV Nvs = Some Dd ->
    ind_nil_at (gds_restrict D Θ) Ξ (ind_qname Ξ (raw_member_name Mr0)) Dd (grp_self_insts (ind_qname Ξ (raw_member_name Mr0)) Dd) ->
    gen_names_free Ξ R Dd ->
    post_mems ch Θ K D B Ξ pv R (ind_qname Ξ (raw_member_name Mr0)) Dd 0 (List.map raw_member_name (raw_decl_members R)) r1 ->
    post_cmds ch (cstate_deps r1) (cstate_k r1) (cstate_dom r1) (cstate_bt r1) (cstate_stack r1)
      (rec_cmds (gds_restrict (cstate_dom r1) (cstate_deps r1)) (cstate_stack r1) R (ind_qname Ξ (raw_member_name Mr0)) Dd) r2 ->
    post_cmd ch Θ K D B Ξ (cc_ind pv R) r2.
  Proof.
    intros HR Hsort Hcls Hsibs Hvcls Hvnps Hbfs Hfil Hnil Hgn H1 H2 ΘR RbR Hli Hrb.
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as Heq.
    pose proof (li_wf _ _ _ _ _ _ Hli) as HΞ.
    pose proof (equiv_rm_cls _ _ _ Heq HΞ _ _ _ Hcls) as Hcls'.
    assert (Hsibs' : Forall2 (view_sibs ΘR Ξ R) Vs Ss)
      by (eapply Forall2_impl; [ intros x ss; apply (equiv_view_sibs _ _ _ Heq HΞ) | exact Hsibs ]).
    assert (Hvcls' : Forall2 (view_cls ΘR Ξ R) Vs csV)
      by (eapply Forall2_impl; [ intros x cs; apply (equiv_view_cls _ _ _ Heq HΞ) | exact Hvcls ]).
    assert (Hvnps' : Forall2 (view_nps ΘR Ξ R) Vs Nvs)
      by (eapply Forall2_impl; [ intros x Nv; apply (equiv_view_nps _ _ _ Heq HΞ) | exact Hvnps ]).
    assert (Hfil' : rd_filed ΘR Ξ R Vs Ss csD csV Nvs = Some Dd) by (rewrite <- (equiv_rd_filed _ _ _ Heq); exact Hfil).
    pose proof (equiv_ind_nil_at _ _ _ Heq HΞ _ _ _ Hnil) as Hnil'.
    destruct (H1 _ _ Hli Hrb) as [ΘR1 RbR1 Hr1 Hli1 Hrb1 He1 Hg1]; cbn beta in Hr1.
    destruct (H2 _ _ Hli1 Hrb1) as [ΘR2 RbR2 Hr2 Hli2 Hrb2 He2 Hg2]; cbn beta in Hr2.
    rewrite <- (equiv_rec_cmds _ _ _ _ _ _ (linv_equiv Hli1)) in Hr2.
    apply (mk_cmd_post _ _ _ _ _ ΘR2 RbR2); [ eapply run_cmd_ind_case; eassumption | exact Hli2 | exact Hrb2
                                            | eapply ext_trans; eassumption |].
    exact (grows_trans Hg1 Hg2 (dom_grows Hli1 (proj1 Hrb1) Hr2 Hli2)).
  Qed.

  (** *** Records *)

  (** The frame of a record's module, opened where the record is declared,
      keeps the invariant. *)
  Lemma linv_push_record {ch Θ K D ΘR Ξ x pv Δ Srt fs} :
    linv ch Θ K D ΘR Ξ -> gs_fresh x Ξ ->
    ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_record pv (ind_qname Ξ x) (record_at Ξ Δ Srt fs) ⋄ ->
    linv ch Θ K D ΘR (gs_push_record (ind_qname Ξ x) (record_at Ξ Δ Srt fs) Δ Ξ).
  Proof.
    intros Hli Hfr HE; destruct (record_nil_entry_params _ _ _ _ _ _ _ _ HE) as [Htel HΔ].
    apply (linv_stack Hli); [| exact (stack_in_push_record _ _ _ _ _ (li_stack _ _ _ _ _ _ Hli) Hfr) ].
    destruct Ξ as [| [[mq Kq] Uq] Ξ0]; [ contradiction |].
    apply wf_gstack_cons;
      [ exact (li_wf _ _ _ _ _ _ Hli) | eapply wf_gmod_record_nil; [ exact Htel | exact HΔ | exact HE | reflexivity ] |].
    cbn; exists x; split; [ reflexivity | exact Hfr ].
  Qed.

  (** A record typed at the restriction is checked with an empty module at
      every state the invariant relates to it. *)
  Lemma record_entry_at {ch Θ K D Ξ pv x Δ Srt fs} :
    record_typed (gds_restrict D Θ) Ξ (record_at Ξ Δ Srt fs) ->
    forall ΘR, linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_record pv (ind_qname Ξ x) (record_at Ξ Δ Srt fs) ⋄.
  Proof.
    intros Ht ΘR Hli; apply record_entry_of_typed.
    refine (record_typed_emb _ _ _ _ _ _ Ht).
    constructor; [ exact (li_wf _ _ _ _ _ _ Hli) | apply gc_sub_deps; exact (proj1 (gds_equiv_sym _ _ (linv_equiv Hli))) ].
  Qed.

  Lemma record_pre {ch Θ K D Ξ x Δ Srt fs} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> gs_fresh x Ξ -> record_typed (gds_restrict D Θ) Ξ (record_at Ξ Δ Srt fs) ->
    exists ΘR, linv ch Θ K D ΘR (gs_push_record (ind_qname Ξ x) (record_at Ξ Δ Srt fs) Δ Ξ).
  Proof. intros [ΘR Hli] Hfr Ht; exists ΘR; exact (linv_push_record Hli Hfr (record_entry_at (pv := false) Ht _ Hli)). Qed.

  (** Where a run of commands ends, the invariant holds. *)
  Lemma cmds_post_pre {ch Θ K D B Ξ cs r} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> post_cmds ch Θ K D B Ξ cs r ->
    exists ΘR, linv ch (cstate_deps r) (cstate_k r) (cstate_dom r) ΘR (cstate_stack r).
  Proof.
    intros [ΘR Hli] Hp; destruct (linv_rb Hli) as [RbR Hrb].
    destruct (Hp _ _ Hli Hrb) as [ΘR' RbR' _ Hli' _ _ _]; eauto.
  Qed.

  (** A record, typed at the restriction, its module's field definitions
      run in its frame, then its with-area: the frame closes into the
      record's entry, as [run_cmd_record] files it. *)
  Lemma record_ok {ch Θ K D B Ξ x pv Δ Srt fs cs r1 r2 mp Kf U Ξ2} :
    gs_fresh x Ξ -> record_typed (gds_restrict D Θ) Ξ (record_at Ξ Δ Srt fs) ->
    post_cmds ch Θ K D B (gs_push_record (ind_qname Ξ x) (record_at Ξ Δ Srt fs) Δ Ξ)
      (record_field_cmds (record_at Ξ Δ Srt fs)) r1 ->
    post_cmds ch (cstate_deps r1) (cstate_k r1) (cstate_dom r1) (cstate_bt r1) (cstate_stack r1) cs r2 ->
    cstate_stack r2 = (mp, Kf, U) :: Ξ2 ->
    post_cmd ch Θ K D B Ξ (cc_record x pv Δ Srt fs cs)
      (cst (cstate_deps r2) (cstate_k r2) (cstate_dom r2) (cstate_bt r2) (gs_add x (ge_record pv (ind_qname Ξ x) (record_at Ξ Δ Srt fs) (gu_mod U)) Ξ)).
  Proof.
    intros Hfr Ht H1 H2 HΞ ΘR RbR Hli Hrb; cbn [cstate_deps cstate_k cstate_dom cstate_bt cstate_stack].
    pose proof (record_entry_at (pv := pv) (x := x) Ht _ Hli) as HE.
    pose proof (linv_push_record Hli Hfr (record_entry_at (pv := false) Ht _ Hli)) as Hli'.
    destruct (H1 _ _ Hli' Hrb) as [ΘR1 RbR1 Hr1 Hli1 Hrb1 He1 Hg1]; cbn beta in Hr1.
    destruct (H2 _ _ Hli1 Hrb1) as [ΘR2 RbR2 Hr2 Hli2 Hrb2 He2 Hg2]; cbn beta in Hr2.
    rewrite HΞ in Hr2, Hli2.
    destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ (run_cmds_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr1 Hr2))
      as [F HF]; injection HF as _ ->.
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_record x pv Δ Srt fs cs ⇝
                   ΘR2 ⍮ gs_add x (ge_record pv (ind_qname Ξ x) (record_at Ξ Δ Srt fs) (gu_mod U)) Ξ ⍮ cstate_bt r2 ⍮ RbR2)
      by (eapply run_cmd_record; eassumption).
    apply (mk_cmd_post _ _ _ _ _ ΘR2 RbR2 Hr); [| exact Hrb2 | eapply ext_trans; eassumption |].
    - apply (linv_stack Hli2); [ exact (proj1 (linv_run_wf Hli (proj1 Hrb) Hr)) | exact (linv_run_stack Hli Hr) ].
    - exact (grows_trans Hg1 Hg2 (dom_grows Hli1 (proj1 Hrb1) Hr2 Hli2)).
  Qed.

  Lemma unit_pre {ch Θ K} : ginv ch Θ K -> exists ΘR, linv ch Θ K nil ΘR nil.
  Proof. intros G; exists nil; exact (nil_linv G). Qed.

  (** The imports run on the empty stack, from no binding, and leave the
      stack empty. *)
  Lemma unit_imports {ch Θ K imps r1} :
    ginv ch Θ K -> post_cmds ch Θ K nil bt_empty nil imps r1 ->
    exists ΘR1 RbR1, nil ⍮ nil ⍮ bt_empty ⍮ nil ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ imps ⇝* ΘR1 ⍮ nil ⍮ cstate_bt r1 ⍮ RbR1 /\ cstate_stack r1 = nil /\
      linv ch (cstate_deps r1) (cstate_k r1) (cstate_dom r1) ΘR1 nil /\ rb_ok (cstate_k r1) ΘR1 RbR1 /\
      ext Θ K (cstate_deps r1) (cstate_k r1) /\ grows Θ (cstate_deps r1) (cstate_dom r1).
  Proof.
    intros G Hp; destruct (Hp _ _ (nil_linv G) (rb_ok_nil K)) as [ΘR1 RbR1 Hr1 Hli1 Hrb1 He1 Hg1]; cbn beta in Hr1.
    pose proof (run_cmds_empty _ _ _ _ _ _ _ _ _ _ _ _ Hr1) as HΞ; rewrite HΞ in Hr1, Hli1.
    exists ΘR1, RbR1; exact (conj Hr1 (conj HΞ (conj Hli1 (conj Hrb1 (conj He1 Hg1))))).
  Qed.

  Lemma unit_gctx {ch Θ K imps r1} :
    ginv ch Θ K -> post_cmds ch Θ K nil bt_empty nil imps r1 -> ⊢ᵍ gds_restrict (cstate_dom r1) (cstate_deps r1) ⍮ nil.
  Proof. intros G Hp; destruct (unit_imports G Hp) as (ΘR1 & _ & _ & _ & Hli1 & _); exact (linv_restrict_gctx Hli1). Qed.

  Lemma unit_body_pre {fp ch Θ K imps r1 P} :
    ginv (fp :: ch) Θ K -> post_cmds (fp :: ch) Θ K nil bt_empty nil imps r1 -> tele_ass P ->
    ⊢ gds_restrict (cstate_dom r1) (cstate_deps r1) ⍮ nil ⍮ P ->
    exists ΘR, linv (fp :: ch) (cstate_deps r1) (cstate_k r1) (cstate_dom r1) ΘR (gs_push (q_abs fp nil) P nil).
  Proof.
    intros G Hp Htel HP; destruct (unit_imports G Hp) as (ΘR1 & _ & _ & _ & Hli1 & _).
    exists ΘR1; exact (proj2 (linv_push_unit Hli1 Htel HP)).
  Qed.

  Lemma unit_ok {fp ch Θ K imps P0 P cs r1 r2 mp Kf U Ξ2} :
    post_cmds (fp :: ch) Θ K nil bt_empty nil imps r1 ->
    fill_params (gds_restrict (cstate_dom r1) (cstate_deps r1)) nil (cstate_bt r1) P0 P ->
    tele_ass P ->
    ⊢ gds_restrict (cstate_dom r1) (cstate_deps r1) ⍮ nil ⍮ P ->
    acc_ok (gds_restrict (cstate_dom r1) (cstate_deps r1)) nil (tele_refs nil P0) ->
    post_cmds (fp :: ch) (cstate_deps r1) (cstate_k r1) (cstate_dom r1) (cstate_bt r1) (gs_push (q_abs fp nil) P nil) cs r2 ->
    cstate_stack r2 = (mp, Kf, U) :: Ξ2 ->
    post_unit (fp :: ch) Θ K (imps, P0, cs) (ust (cstate_deps r2) (cstate_k r2) (cstate_dom r2) (cstate_bt r2) U).
  Proof.
    intros Hp1 Hfa Htel HP Hac Hp2 HΞ G; cbn [us_deps us_k us_dom us_bt us_unit].
    destruct (unit_imports G Hp1) as (ΘR1 & RbR1 & Hr1 & _ & Hli1 & Hrb1 & He1 & Hg1).
    pose proof (equiv_acc _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli1)) Hac) as Hac'.
    pose proof (equiv_fill_params _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli1)) (li_wf _ _ _ _ _ _ Hli1) Hfa) as Hfa'.
    destruct (linv_push_unit Hli1 Htel HP) as [HP' Hli1'].
    destruct (Hp2 _ _ Hli1' Hrb1) as [ΘR2 RbR2 Hr2 Hli2 Hrb2 He2 Hg2]; cbn beta in Hr2.
    rewrite HΞ in Hr2, Hli2.
    destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr2) as [F HF]; injection HF as <- ->.
    destruct Hli2 as [G2 Hs2 Hd2 Hc2 _ _].
    apply (mk_unit_post _ _ _ _ _ RbR2 ΘR2);
      [ eapply run_unit_intro; [ exact Hr1 | exact Hfa' | exact Htel | exact HP' | exact Hac' | exact Hr2 ]
      | exact G2 | exact Hs2 | exact Hd2 | exact Hc2 | exact (proj2 Hrb2) | eapply ext_trans; eassumption |].
    intros x Hx; destruct (Hg2 _ Hx) as [Hx1 | Hx1]; [| right; exact Hx1 ].
    destruct (Hg1 _ Hx1) as [Hx0 | Hx0]; [ left; exact Hx0 | right ].
    apply Hd2, (sub_dom _ _ _ (proj1 (proj2 (proj2 (proj1 (proj2 run_wf) _ _ _ _ _ _ _ _ _ _ Hr2
                                                 (li_wf _ _ _ _ _ _ Hli1') (proj1 Hrb1)
                                                 (li_stack _ _ _ _ _ _ Hli1')))))).
    apply (li_dom _ _ _ _ _ _ Hli1), Hx0.
  Qed.

  (** ** The Executable

      Recursion on commands is structural, including on the command lists
      nested in modules: the local helper [go] of [cmds_step] takes the
      function for one command as a uniform parameter, so the guard checker
      sees through it.  Only a load recurses on something else: the chain
      grows by an unfiled path that [load_path] knows ([load_step]), and
      [run_unit_impl] is structural on the accessibility proof.  The
      executable takes that proof, never the list of files. *)

  #[warnings="-cannot-define-projection"]
  Record load_step (ch' ch : list path) : Prop := mk_load_step
    { load_step_path : path
    ; load_step_src : string
    ; load_step_chain : ch' = load_step_path :: ch
    ; load_step_fresh : ~ In load_step_path ch
    ; load_step_load : load_path load_step_path = Some load_step_src }.

  Definition load_step_intro {ch fp src} (Hn : ~ In fp ch) (Hs : load_path fp = Some src) :
    load_step (fp :: ch) ch :=
    mk_load_step _ _ fp src eq_refl Hn Hs.

  (** How a unit loaded under chain [ch] is run.  Its log holds the evals of
      the unit itself, not of the units it loads. *)
  Definition loader (ch : list path) : Type :=
    forall fp src, ~ In fp ch -> load_path fp = Some src ->
      forall Θ K u, ginv (fp :: ch) Θ K -> rres ({r | post_unit (fp :: ch) Θ K u r} * elog)%type.

  Definition cmd_fun (ch : list path) : Type :=
    forall Θ K D B Ξ c (H : exists ΘR, linv ch Θ K D ΘR Ξ), rres ({r | post_lcmd ch Θ K D B Ξ c r} * elog)%type.

  Equations cmds_step (ch : list path) (rc : cmd_fun ch) :
    forall Θ K D B Ξ cs (H : exists ΘR, linv ch Θ K D ΘR Ξ), rres ({r | post_cmds ch Θ K D B Ξ cs r} * elog)%type :=
  cmds_step ch rc := go
  where go Θ0 K0 D0 B0 Ξ0 (cs : list ccmd) (H0 : exists ΘR, linv ch Θ0 K0 D0 ΘR Ξ0) :
    rres ({r | post_cmds ch Θ0 K0 D0 B0 Ξ0 cs r} * elog)%type by struct cs :=
  | Θ0, K0, D0, B0, Ξ0, nil, H0 => rok (exist _ _ nil_ok, log_nil)
  | Θ0, K0, D0, B0, Ξ0, c :: cs', H0 with refs_check (gds_restrict D0 Θ0) Ξ0 (pre_gctx H0) (cmd_refs c) => {
    | inleft (exist _ e _) => rerr (run_error_nat (gds_restrict D0 Θ0) Ξ0 (nat_view (gds_restrict D0 Θ0) Ξ0 B0) (priv_error e))
    | inright Hac with rc Θ0 K0 D0 B0 Ξ0 c H0 => {
      | rerr e => rerr (run_error_nat (gds_restrict D0 Θ0) Ξ0 (nat_view (gds_restrict D0 Θ0) Ξ0 B0) e)
      | rok (exist _ r1 Hr1, l1) with go (cstate_deps r1) (cstate_k r1) (cstate_dom r1) (cstate_bt r1) (cstate_stack r1) cs' (cons_pre H0 Hr1) => {
        | rerr e => rerr e
        | rok (exist _ r2 Hr2, l2) => rok (exist _ _ (cons_ok Hac Hr1 Hr2), log_app l1 l2) } } }.

  Definition da_ok {ch Θ K D B Ξ c Ξ'} (Hp : post_cmd ch Θ K D B Ξ c (cst Θ K D B Ξ')) :
      {Ξ0 | post_cmd ch Θ K D B Ξ c (cst Θ K D B Ξ0)} := exist _ Ξ' Hp.

  (** A definition or an alias, checked as written: the non-recursive step
      of [cc_def] and [cc_alias], which also runs the commands an import
      generates. *)
  Equations defalias_step (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (c : ccmd) (H : exists ΘR, linv ch Θ K D ΘR Ξ) : rres {Ξ' | post_cmd ch Θ K D B Ξ c (cst Θ K D B Ξ')} :=
  | ch, Θ, K, D, B, Ξ, cc_def x b pv A (Some M), H with gs_fresh_dec x Ξ => {
    | right _ => rerr (run_error_msg ("duplicate name " ++ x))
    | left Hfr with check_typ (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A => {
      | inright _ => rerr (blame_error (find_level_blame fctx_none _ _ _ (pre_ctx H) A)
                            (mod_error (pre_gctx H) (Some x) (A :: nil) (run_error_def_typ x Ξ A)))
      | inleft (exist _ i HA) with check_exp_typed (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A (ex_intro _ i HA) M => {
        | left HM => rok (da_ok (def_ok Hfr HM))
        | right _ =>
            rerr (mod_error (pre_gctx H) (Some x) (M :: nil)
                    (field_error (fctx_cmd B) (gds_restrict D Θ) Ξ (Some x) (pre_ctx H) M (run_error_def x Ξ A M))) } } }
  | ch, Θ, K, D, B, Ξ, cc_def x b pv A None, H with gs_fresh_dec x Ξ => {
    | right _ => rerr (run_error_msg ("duplicate name " ++ x))
    | left Hfr with check_typ (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A => {
      | inleft (exist _ i HA) => rok (da_ok (axiom_ok Hfr HA))
      | inright _ =>
          rerr (blame_error (find_level_blame fctx_none _ _ _ (pre_ctx H) A)
                  (mod_error (pre_gctx H) (Some x) (A :: nil) (run_error_msg ("the type of axiom " ++ x ++ " is not a type")))) } }
  | ch, Θ, K, D, B, Ξ, cc_alias x pv Δ E, H with tele_ass_dec Δ => {
    | right _ => rerr (run_error_msg ("parameters of module " ++ x ++ " that are not assumptions"))
    | left Htel with check_ext (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) Δ => {
      | right _ =>
          rerr (tele_blame_error (find_tele_blame fctx_none _ _ _ (pre_ctx H) Δ)
                  (run_error_msg ("ill-formed parameters of module " ++ x)))
      | left HΔ with check_modexp (fctx_cmd B) (gds_restrict D Θ) Ξ (Δ ++ gs_tele Ξ) (ext_eq_ctx_left _ _ _ _ _ HΔ) E => {
        | right _ => rerr (run_error_msg ("ill-formed module expression for module " ++ x))
        | left HE with gs_fresh_dec x Ξ => {
          | right _ => rerr (run_error_msg ("duplicate name " ++ x))
          | left Hfr => rok (da_ok (alias_ok Htel HΔ HE Hfr)) } } } }
  | _, _, _, _, _, _, _, _ => rerr (run_error_msg "internal error: not a definition or an alias").

  (** The entries an import generates, in order, as [gens_run] declares
      them: written by no one, so with no privacy check. *)
  Fixpoint gens_impl (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (gs : list igen) (H : exists ΘR, linv ch Θ K D ΘR Ξ) {struct gs} : rres {Ξ' | post_gens ch Θ K D Ξ gs Ξ'} :=
    match gs as gs0 return rres {Ξ' | post_gens ch Θ K D Ξ gs0 Ξ'} with
    | nil => rok (exist _ Ξ gens_nil_ok)
    | ig_def d pv A M :: gs' =>
        match gs_fresh_dec d Ξ with
        | right _ => rerr (run_error_msg ("duplicate name " ++ d))
        | left Hfr =>
            match check_exp (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A M with
            | right _ => rerr (run_error_def d Ξ A M)
            | left HM =>
                match gens_impl ch Θ K D B (gs_add d (gs_def true pv Ξ A M) Ξ) gs' (gdef_pre H Hfr HM) with
                | rerr e => rerr e
                | rok (exist _ Ξ' Hp) => rok (exist _ Ξ' (gdef_ok Hfr HM Hp))
                end
            end
        end
    | ig_alias d pv E :: gs' =>
        match gs_fresh_dec d Ξ with
        | right _ => rerr (run_error_msg ("duplicate name " ++ d))
        | left Hfr =>
            match check_modexp (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) E with
            | right _ => rerr (run_error_msg ("ill-formed module expression for module " ++ d))
            | left HE =>
                match gens_impl ch Θ K D B (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ) gs'
                        (galias_pre H Hfr HE) with
                | rerr e => rerr e
                | rok (exist _ Ξ' Hp) => rok (exist _ Ξ' (galias_ok Hfr HE Hp))
                end
            end
        end
    | ig_def_mod d pv A M E :: gs' =>
        match gs_fresh_dec d Ξ with
        | right _ => rerr (run_error_msg ("duplicate name " ++ d))
        | left Hfr =>
            match @type_infer (gc_mk (gds_restrict D Θ) Ξ) (fctx_cmd B (gds_restrict D Θ) Ξ) (gs_tele Ξ) (pre_ctx H) M
                    (type_infer_order_all M) with
            | inright _ => rerr (run_error_msg ("ill-formed definition " ++ d))
            | inleft (exist _ W HWs) =>
                match check_modexp (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) E with
                | right _ => rerr (run_error_msg ("ill-formed module expression for module " ++ d))
                | left HE =>
                    let HM := alg_type_infer_sound (proj1 HWs) (pre_ctx H) in
                    match gens_impl ch Θ K D B (gs_add d (dm_entry Ξ pv nil (nf_to_exp W) M E) Ξ) gs'
                            (gdm_pre H Hfr (proj1 HWs) HM HE) with
                    | rerr e => rerr e
                    | rok (exist _ Ξ' Hp) => rok (exist _ Ξ' (gdm_ok (A := A) Hfr (proj1 HWs) HM HE Hp))
                    end
                end
            end
        end
    end.

  Definition cmd_ok {ch Θ K D B Ξ c r} (Hp : post_cmd ch Θ K D B Ξ c r) : {r0 | post_cmd ch Θ K D B Ξ c r0} :=
    exist _ r Hp.

  (** The last name of the path of an inductive type. *)
  Definition ind_short (p : qname) : string := List.last (q_chain p) EmptyString.

  (** A binding that another one meets. *)
  Definition bound_msg (B : builtins) : string :=
    match builtins_nat B with
    | Some p0 => "the natural numbers are bound already, to " ++ ind_short p0
    | None => "the natural numbers are bound already"
    end.

  Definition nat_shape_msg (p : qname) : string :=
    ind_short p ++ " is not shaped as the natural numbers: it must have no parameter, " ++
    "one constructor without arguments and one with a single recursive argument".

  Definition bt_cmd_ok {ch Θ K D B Ξ c B'} (Hp : post_cmd ch Θ K D B Ξ c (cst Θ K D B' Ξ)) :
      {B0 | post_cmd ch Θ K D B Ξ c (cst Θ K D B0 Ξ)} := exist _ B' Hp.

  (** The path a command names a module by, as written, if it is one. *)
  Definition written_name (E : modexp) (p : qname) : qname :=
    match mod_qname E with Some pq => pq | None => p end.

  (** A builtin bound to something that is no inductive type. *)
  Definition builtin_target_error (E : modexp) : run_error :=
    match mod_qname E with
    | Some pq => run_error_not_ind pq
    | None => run_error_msg "the natural numbers must be bound to an inductive type, named by its path"
    end.

  (** A builtin binding, checked premise by premise: the module expression
      read as a term, its inferred type, then its normal form. *)
  Equations builtin_step (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (k : string) (E : modexp) (H : exists ΘR, linv ch Θ K D ΘR Ξ) :
    rres {B' | post_cmd ch Θ K D B Ξ (cc_builtin k E) (cst Θ K D B' Ξ)} :=
  | ch, Θ, K, D, B, Ξ, k, E, H with string_dec k nat_kind => {
    | right _ => rerr (run_error_msg ("there is no builtin " ++ k))
    | left Hk with opt_case (modexp_as_term E) => {
      | inright _ => rerr (builtin_target_error E)
      | inleft (exist _ M Ht)
          with @type_infer (gc_mk (gds_restrict D Θ) Ξ) (fctx_cmd B (gds_restrict D Θ) Ξ) (gs_tele Ξ) (pre_ctx H) M
                 (type_infer_order_all M) => {
        | inright _ => rerr (builtin_target_error E)
        | inleft (exist _ W HWs) with nf_is_universe_dec W => {
          | right _ => rerr (builtin_target_error E)
          | left Hu
              with @nbe_impl (gds_restrict D Θ) Ξ (fctx_cmd B (gds_restrict D Θ) Ξ) (gs_tele Ξ) M (nf_to_exp W)
                     (typed_nbe_order (alg_type_infer_sound (proj1 HWs) (pre_ctx H))) => {
            | exist _ (nf_indty p 0 nil) Hn with opt_case (ind_lookup (gds_restrict D Θ) Ξ p) => {
              | inright _ => rerr (run_error_not_ind p)
              | inleft (exist _ Dd Hl) with inspect (nat_shape Dd) => {
                | exist _ None _ => rerr (run_error_msg (nat_shape_msg p))
                | exist _ (Some (z, s)) Hs with inspect (is_nat_sort (ind_sort Dd)) => {
                  | exist _ false _ => rerr (run_error_msg ("the natural numbers must be declared in Type@0, not " ++ ind_short p))
                  | exist _ true Ek with inspect (bt_bind_nat B p) => {
                    | exist _ None _ => rerr (run_error_msg (bound_msg B))
                    | exist _ (Some B') Hb =>
                        rok (bt_cmd_ok (eq_rect _ (fun k0 => post_cmd ch Θ K D B Ξ (cc_builtin k0 E) (cst Θ K D B' Ξ))
                                         (builtin_ok Ht (proj1 HWs) (alg_type_infer_sound (proj1 HWs) (pre_ctx H)) Hu Hn
                                            Hl Hs (proj1 (is_nat_sort_spec _) Ek) Hb) _ (eq_sym Hk))) } } } }
            | exist _ (nf_indty p _ _) _ => rerr (run_error_msg (nat_shape_msg (written_name E p)))
            | exist _ _ _ => rerr (builtin_target_error E) } } } } }.

  (** The module a well-formed module expression applies is well formed
      ([modexp_gen]). *)
  Lemma me_apps_head_wf : forall Θ0 Ξ0 Γ H0 L,
      Θ0 ⍮ Ξ0 ⍮ Γ ⊢ᵐ me_apps H0 L ≈ me_apps H0 L -> Θ0 ⍮ Ξ0 ⍮ Γ ⊢ᵐ H0 ≈ H0.
  Proof.
    intros *; induction L as [| N L IH] using List.rev_ind; intros HH; [ exact HH |].
    rewrite me_apps_snoc in HH; apply IH.
    exact (proj1 (proj1 (modexp_gen _ _ _ _ _ HH))).
  Qed.

  Lemma me_unapps_head_wf : forall Θ0 Ξ0 Γ E,
      Θ0 ⍮ Ξ0 ⍮ Γ ⊢ᵐ E ≈ E -> Θ0 ⍮ Ξ0 ⍮ Γ ⊢ᵐ fst (me_unapps E) ≈ fst (me_unapps E).
  Proof.
    intros * HE; rewrite (proj1 (me_unapps_spec E)) in HE; exact (me_apps_head_wf _ _ _ _ _ HE).
  Qed.

  (** An inductive alias whose module expression names no inductive type. *)
  Definition alias_target_error (x : string) (E : modexp) : run_error :=
    match mod_qname (fst (me_unapps E)) with
    | Some pq => run_error_not_ind pq
    | None => run_error_msg ("inductive alias " ++ x ++ " must name an inductive type by its path")
    end.

  (** An inductive alias whose module expression is ill-formed although the
      module it applies is not: an inductive type applied past its uniform
      parameters is named as such. *)
  Definition alias_wf_error (x : string) (Θr : gdeps) (Ξ : gstack) (Hg : ⊢ᵍ Θr ⍮ Ξ) (Γ : ctx) (E : modexp)
      (Hh : Θr ⍮ Ξ ⍮ Γ ⊢ᵐ fst (me_unapps E) ≈ fst (me_unapps E)) : run_error :=
    match mdenote_impl Θr Ξ Hg Γ (fst (me_unapps E)) (dn_order_of_wf _ _ Hg _ _ _ Hh) with
    | inleft (exist _ (ds_dm Θ0 _ M _) _) =>
        (* a type former: its term part is the group's constant applied to
           the arguments given so far *)
        match app_head M with
        | a_ind p _ =>
            match ind_lookup Θr Ξ p with
            | Some Dp =>
                if Nat.ltb (ind_nu Dp) (List.length (app_args M) + (List.length (snd (me_unapps E)) - List.length Θ0))
                then run_error_msg ("inductive alias " ++ x ++ ": more arguments than uniform parameters of " ++ ind_short p)
                else run_error_msg ("ill-formed inductive alias " ++ x)
            | None => run_error_msg ("ill-formed inductive alias " ++ x)
            end
        | _ => run_error_msg ("ill-formed inductive alias " ++ x)
        end
    | _ => run_error_msg ("ill-formed inductive alias " ++ x)
    end.

  (** A record alias whose module expression names no record type. *)
  Definition recalias_target_error (x : string) : run_error :=
    run_error_msg ("record alias " ++ x ++ " must name a record type").

  (** An inductive alias, checked premise by premise: its parameters, the
      module it applies, the module expression, read as a term, its type
      inferred, and whether it is a type former of an inductive type. *)
  Equations indalias_step (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (x : string) (pv : bool) (Δ : ctx) (E : modexp) (H : exists ΘR, linv ch Θ K D ΘR Ξ) :
    rres {Ξ' | post_cmd ch Θ K D B Ξ (cc_ind_alias x pv Δ E) (cst Θ K D B Ξ')} :=
  | ch, Θ, K, D, B, Ξ, x, pv, Δ, E, H with tele_ass_dec Δ => {
    | right _ => rerr (run_error_msg ("parameters of inductive alias " ++ x ++ " that are not assumptions"))
    | left Htel with check_ext (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) Δ => {
      | right _ => rerr (run_error_msg ("ill-formed inductive alias " ++ x))
      | left HΔ with check_modexp (fctx_cmd B) (gds_restrict D Θ) Ξ (Δ ++ gs_tele Ξ) (ext_eq_ctx_left _ _ _ _ _ HΔ) (fst (me_unapps E)) => {
        | right _ => rerr (alias_target_error x E)
        | left Hh with check_modexp (fctx_cmd B) (gds_restrict D Θ) Ξ (Δ ++ gs_tele Ξ) (ext_eq_ctx_left _ _ _ _ _ HΔ) E => {
          | right _ => rerr (alias_wf_error x _ _ (pre_gctx H) _ E Hh)
          | left HE with opt_case (modexp_as_term E) => {
            | inright _ => rerr (alias_target_error x E)
            | inleft (exist _ M Ht)
                with @type_infer (gc_mk (gds_restrict D Θ) Ξ) (fctx_cmd B (gds_restrict D Θ) Ξ) (Δ ++ gs_tele Ξ)
                       (ext_eq_ctx_left _ _ _ _ _ HΔ) M (type_infer_order_all M) => {
              | inright _ => rerr (alias_target_error x E)
              | inleft (exist _ W HWs)
                  with ind_former_dec (gds_restrict D Θ) Ξ (fctx_cmd B (gds_restrict D Θ) Ξ) (Δ ++ gs_tele Ξ) M W
                         (alg_type_infer_sound (proj1 HWs) (ext_eq_ctx_left _ _ _ _ _ HΔ)) => {
                | right _
                    with record_former_dec (gds_restrict D Θ) Ξ (fctx_cmd B (gds_restrict D Θ) Ξ) (Δ ++ gs_tele Ξ) M W
                           (alg_type_infer_sound (proj1 HWs) (ext_eq_ctx_left _ _ _ _ _ HΔ)) => {
                  | left _ => rerr (run_error_msg ("inductive alias " ++ x ++ " names a record type: use record"))
                  | right _ => rerr (alias_target_error x E) }
                | left Hf with gs_fresh_dec x Ξ => {
                  | right _ => rerr (run_error_msg ("duplicate name " ++ x))
                  | left Hfr =>
                      rok (da_ok (indalias_ok Htel HΔ HE Ht (proj1 HWs)
                                    (alg_type_infer_sound (proj1 HWs) (ext_eq_ctx_left _ _ _ _ _ HΔ)) Hf Hfr)) } } } } } } } }.

  (** A record alias, checked as an inductive alias is, for a type former
      of a record type. *)
  Equations recalias_step (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (x : string) (pv : bool) (Δ : ctx) (E : modexp) (H : exists ΘR, linv ch Θ K D ΘR Ξ) :
    rres {Ξ' | post_cmd ch Θ K D B Ξ (cc_record_alias x pv Δ E) (cst Θ K D B Ξ')} :=
  | ch, Θ, K, D, B, Ξ, x, pv, Δ, E, H with tele_ass_dec Δ => {
    | right _ => rerr (run_error_msg ("parameters of record alias " ++ x ++ " that are not assumptions"))
    | left Htel with check_ext (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) Δ => {
      | right _ => rerr (run_error_msg ("ill-formed record alias " ++ x))
      | left HΔ with check_modexp (fctx_cmd B) (gds_restrict D Θ) Ξ (Δ ++ gs_tele Ξ) (ext_eq_ctx_left _ _ _ _ _ HΔ) E => {
        | right _ => rerr (run_error_msg ("ill-formed record alias " ++ x))
        | left HE with opt_case (modexp_as_term E) => {
          | inright _ => rerr (recalias_target_error x)
          | inleft (exist _ M Ht)
              with @type_infer (gc_mk (gds_restrict D Θ) Ξ) (fctx_cmd B (gds_restrict D Θ) Ξ) (Δ ++ gs_tele Ξ)
                     (ext_eq_ctx_left _ _ _ _ _ HΔ) M (type_infer_order_all M) => {
            | inright _ => rerr (recalias_target_error x)
            | inleft (exist _ W HWs)
                with record_former_dec (gds_restrict D Θ) Ξ (fctx_cmd B (gds_restrict D Θ) Ξ) (Δ ++ gs_tele Ξ) M W
                       (alg_type_infer_sound (proj1 HWs) (ext_eq_ctx_left _ _ _ _ _ HΔ)) => {
              | right _
                  with ind_former_dec (gds_restrict D Θ) Ξ (fctx_cmd B (gds_restrict D Θ) Ξ) (Δ ++ gs_tele Ξ) M W
                         (alg_type_infer_sound (proj1 HWs) (ext_eq_ctx_left _ _ _ _ _ HΔ)) => {
                | left _ => rerr (run_error_msg ("record alias " ++ x ++ " names an inductive type: use inductive"))
                | right _ => rerr (recalias_target_error x) }
              | left Hf with gs_fresh_dec x Ξ => {
                | right _ => rerr (run_error_msg ("duplicate name " ++ x))
                | left Hfr =>
                    rok (da_ok (recalias_ok Htel HΔ HE Ht (proj1 HWs)
                                  (alg_type_infer_sound (proj1 HWs) (ext_eq_ctx_left _ _ _ _ _ HΔ)) Hf Hfr)) } } } } } } }.

  (** The message of a function with no member. *)
  Definition mdef_why_error (f : string) (e : mdef_why) : run_error :=
    match e with
    | mdef_why_scrut_untyped => run_error_msg ("the scrutinee's type of " ++ f ++ " is not a type")
    | mdef_why_member_untyped _ => run_error_msg ("a member of the group is not a type at the uniform parameters of " ++ f)
    | mdef_why_no_member _ => run_error_msg ("the scrutinee's type of " ++ f ++ " is that of no member of the group")
    | mdef_why_nparams n m => run_error_mdef_nparams f m n
    end.

  (** The message of a definition not filed. *)
  Definition mdefs_why_error (e : mdefs_why) : run_error :=
    match e with
    | mdefs_why_dup x => run_error_msg ("duplicate name " ++ x)
    | mdefs_why_untyped x Ξ A M => run_error_def x Ξ A M
    end.

  (** The message of functions with no group. *)
  Definition mdef_group_why_error (e : mdef_group_why) : run_error :=
    match e with
    | mdef_group_why_function f w => mdef_why_error f w
    | mdef_group_why_not_inductive f => run_error_msg ("the scrutinee's type of " ++ f ++ " is not an inductive type")
    | mdef_group_why_no_group pq => run_error_not_ind pq
    | mdef_group_why_view f => run_error_msg ("the scrutinee's type of " ++ f ++ " is a view, not a declared type")
    | mdef_group_why_uparams f =>
        run_error_msg ("the uniform parameters of the scrutinee's type of " ++ f ++ " depend on its non-uniform parameters")
    | mdef_group_why_count n m => run_error_mdef_count n m
    | mdef_group_why_shared => run_error_msg "two functions of a mutual definition are for the same member"
    end.

  (** A mutual definition, checked premise by premise: its parameters, its
      functions' group ([mdef_group_dec]), then the definitions filed. *)
  Equations mdef_step (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (b pv : bool) (Δ : ctx) (fs : list raw_fun) (H : exists ΘR, linv ch Θ K D ΘR Ξ) :
    rres {Ξ' | post_cmd ch Θ K D B Ξ (cc_mdef b pv Δ fs) (cst Θ K D B Ξ')} :=
  | ch, Θ, K, D, B, Ξ, b, pv, Δ, nil, H => rerr (run_error_msg "a mutual definition with no function")
  | ch, Θ, K, D, B, Ξ, b, pv, Δ, f0 :: fs, H with tele_ass_dec Δ => {
    | right _ => rerr (run_error_msg "parameters of a mutual definition that are not assumptions")
    | left Htel with check_ctx (fctx_cmd B) (gds_restrict D Θ) Ξ (pre_gctx H) (Δ ++ gs_tele Ξ) => {
      | right _ => rerr (tele_blame_error (find_tele_blame fctx_none _ _ _ (pre_ctx H) Δ)
                           (run_error_msg "ill-formed parameters of a mutual definition"))
      | left HΔ with mdef_group_dec (gds_restrict D Θ) Ξ (pre_gctx H) Δ f0 fs => {
        | inr e => rerr (mdef_group_why_error e)
        | inl (exist _ (pq, m0, Ps, Dd, Us, ms) Hgp)
            with mdefs_dec (gds_restrict D Θ) b pv (mdef_defs pq Dd Us Δ (f0 :: fs) ms) Ξ (pre_gctx H) => {
          | inr (exist _ e _) => rerr (mdefs_why_error e)
          | inl Hr => rok (da_ok (mdef_ok Htel HΔ Hgp Hr)) } } } }.

  (** ** The Recursor Module of a Group

      A group's recursor module ([rec_cmds]) is run by a step of its own,
      which does not recur on the command: a module whose commands are
      generated definitions, each filled as it is, then checked by
      [defalias_step]. *)

  (** The first name of [xs] that occurs again after it. *)
  Fixpoint first_dup (xs : list string) : option string :=
    match xs with
    | nil => None
    | y :: xs' => if List.existsb (String.eqb y) xs' then Some y else first_dup xs'
    end.

  (** The first name a command of a record's with-area declares that is a
      field of the record: such a command cannot run, its name taken by
      the field's definition ([record_field_cmds_taken]). *)
  Fixpoint field_clash (fs : list (string * typ)) (cs : list ccmd) : option string :=
    match cs with
    | nil => None
    | c :: cs' =>
        match cmd_decl_name c with
        | Some y => if List.existsb (String.eqb y) (List.map fst fs) then Some y else field_clash fs cs'
        | None => field_clash fs cs'
        end
    end.

  Lemma field_clash_some : forall fs cs f, field_clash fs cs = Some f ->
      exists c, In c cs /\ cmd_decl_name c = Some f /\ In f (List.map fst fs).
  Proof.
    intros fs; induction cs as [| c cs IH]; intros f Hc; cbn in Hc; [ discriminate |].
    destruct (cmd_decl_name c) as [y |] eqn:Ey.
    - destruct (List.existsb (String.eqb y) (List.map fst fs)) eqn:Eb.
      + injection Hc as <-; apply List.existsb_exists in Eb as (z & Hz & Hq); apply String.eqb_eq in Hq; subst z.
        exists c; split; [ left; reflexivity | split; assumption ].
      + destruct (IH _ Hc) as (c' & Hin & Hn & Hf); exists c'; split; [ right; exact Hin | split; assumption ].
    - destruct (IH _ Hc) as (c' & Hin & Hn & Hf); exists c'; split; [ right; exact Hin | split; assumption ].
  Qed.

  (** Why a record declaration is rejected. *)
  Definition record_why_error (x : string) (fs : list (string * typ)) (e : record_why) : run_error :=
    match e with
    | rw_params => run_error_msg ("parameters of record " ++ x ++ " that are not assumptions")
    | rw_mvc => run_error_msg ("a type of record " ++ x ++ " mentions a module variable")
    | rw_sort => run_error_msg ("the sort of record " ++ x ++ " is not a universe")
    | rw_dup =>
        run_error_msg ("duplicate field name " ++ match first_dup (List.map fst fs) with Some f => f | None => "" end
                ++ " in record " ++ x)
    | rw_field f => run_error_msg ("the type of field " ++ f ++ " of record " ++ x ++ " is not a type of its sort")
    end.

  (** Running a list of commands, from each state the invariant holds at. *)
  Definition cmds_fun (ch : list path) : Type :=
    forall Θ K D B Ξ cs (H : exists ΘR, linv ch Θ K D ΘR Ξ), rres ({r | post_cmds ch Θ K D B Ξ cs r} * elog)%type.

  (** A generated command runs as the command it wraps, taken as it is:
      its fill is itself ([cc_gen]), and [rc_gen] runs it. *)
  Lemma gen_lift {ch Θ K D B Ξ c r} : post_cmd ch Θ K D B Ξ c r -> cmd_genable c -> post_lcmd ch Θ K D B Ξ (cc_gen c) r.
  Proof.
    intros Hp Hgen ΘR RbR Hli Hrb; destruct (Hp _ _ Hli Hrb) as [ΘR' RbR' Hr Hli' Hrb' He Hg].
    apply (mk_cmd_post _ _ _ _ _ ΘR' RbR'); [| exact Hli' | exact Hrb' | exact He | exact Hg ].
    exists (cc_gen c); split; [ apply fill_cmd_gen |].
    exact (run_to_gen _ _ _ _ _ _ _ _ _ _ _ _ _ Hgen Hr).
  Qed.

  (** A step on a command, lifted to the generated command wrapping it. *)
  Definition gen_wrap {ch Θ K D B Ξ c} (s : rres ({r | post_cmd ch Θ K D B Ξ c r} * elog)%type) (Hgen : cmd_genable c) :
      rres ({r | post_lcmd ch Θ K D B Ξ (cc_gen c) r} * elog)%type :=
    match s with
    | rok (exist _ r Hr, l) => rok (exist _ r (gen_lift Hr Hgen), l)
    | rerr e => rerr e
    end.

  (** A generated module, its body run by [rb], its parameters as
      generated. *)
  Equations gen_mod_step (ch : list path) (rb : cmds_fun ch) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins)
    (Ξ : gstack) (x : string) (pv : bool) (Δ : ctx) (cs : list ccmd) (H : exists ΘR, linv ch Θ K D ΘR Ξ) :
    rres ({r | post_cmd ch Θ K D B Ξ (cc_mod x pv Δ cs) r} * elog)%type :=
  | ch, rb, Θ, K, D, B, Ξ, x, pv, Δ, cs, H with tele_ass_dec Δ => {
    | right _ => rerr (run_error_msg ("parameters of module " ++ x ++ " that are not assumptions"))
    | left Htel with check_ctx (fctx_cmd B) (gds_restrict D Θ) Ξ (pre_gctx H) (Δ ++ gs_tele Ξ) => {
      | right _ => rerr (run_error_msg ("ill-formed parameters of module " ++ x))
      | left HΔ with gs_fresh_dec x Ξ => {
        | right _ => rerr (run_error_msg ("duplicate name " ++ x))
        | left Hfr with rb Θ K D B (gs_push (qname_in (gs_path Ξ) x) Δ Ξ) cs (mod_pre H Htel Hfr HΔ) => {
          | rerr e => rerr e
          | rok (exist _ r Hr, l) with list_case (cstate_stack r) => {
            | inleft (existT _ (mp, Kf, U) (exist _ _ HΞ)) => rok (exist _ _ (mod_ok Htel Hfr HΔ Hr HΞ), l)
            | inright _ => rerr (run_error_msg "internal error: a module body lost its frame") } } } } }.

  (** A generated definition, as generated. *)
  Definition gen_def_cmd (ch : list path) : cmd_fun ch :=
    fun Θ K D B Ξ c H =>
      match c as c0 return rres ({r | post_lcmd ch Θ K D B Ξ c0 r} * elog)%type with
      | cc_gen (cc_def x b pv A (Some M)) =>
          match defalias_step ch Θ K D B Ξ (cc_def x b pv A (Some M)) H with
          | rok (exist _ Ξ' Hp) => rok (exist _ _ (gen_lift Hp I), log_nil)
          | rerr e => rerr e
          end
      | _ => rerr (run_error_msg "internal error: not a generated definition")
      end.

  (** The commands a group generates: definitions, and modules of
      definitions, each generated. *)
  Definition rec_cmd (ch : list path) : cmd_fun ch :=
    fun Θ K D B Ξ c H =>
      match c as c0 return rres ({r | post_lcmd ch Θ K D B Ξ c0 r} * elog)%type with
      | cc_gen (cc_mod x pv Δ cs) => gen_wrap (gen_mod_step ch (cmds_step ch (gen_def_cmd ch)) Θ K D B Ξ x pv Δ cs H) I
      | c0 => gen_def_cmd ch Θ K D B Ξ c0 H
      end.

  (** The recursor module of a group, run after its entries. *)
  Definition rec_step (ch : list path) : cmds_fun ch := cmds_step ch (rec_cmd ch).

  (** The declared members [k], [k + 1], … of a group, named [xs]: each
      member's module's commands run in its frame by [rec_step], as
      [run_ind_members_cons] runs them, and the member filed with the body they end
      with. *)
  Equations members_step (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (pv : bool) (R : raw_decl) (pq : qname) (Dd : ind_decl) (k : nat) (xs : list string)
    (H : exists ΘR, linv ch Θ K D ΘR Ξ) (Hp : mems_pre Ξ R pq Dd k xs) (HE : head_entry ch Θ K D Ξ pv pq Dd k xs) :
    rres ({r | post_mems ch Θ K D B Ξ pv R pq Dd k xs r} * elog)%type by struct xs :=
  | ch, Θ, K, D, B, Ξ, pv, R, pq, Dd, k, nil, H, Hp, HE => rok (exist _ _ mems_nil_ok, log_nil)
  | ch, Θ, K, D, B, Ξ, pv, R, pq, Dd, k, x :: xs', H, Hp, HE with member_case Dd k => {
    | inright _ => rerr (run_error_msg "internal error: a declared member is missing")
    | inleft (exist _ M HM)
        with rec_step ch Θ K D B (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ)
               (ind_mod_cmds (gds_restrict D Θ) (gs_push_ind (ind_qname Ξ x) pq k Dd (raw_decl_uparams R) Ξ) R pq Dd k M)
               (push_ind_pre H (mems_fresh_head Hp) (mems_pre_uparams _ _ _ _ _ _ Hp) HE) => {
      | rerr e => rerr e
      | rok (exist _ r1 Hr1, l1) with list_case (cstate_stack r1) => {
        | inright _ => rerr (run_error_msg "internal error: a member's module lost its frame")
        | inleft (existT _ (mp, Kf, U) (exist _ Ξ2 HΞ))
            with members_step ch (cstate_deps r1) (cstate_k r1) (cstate_dom r1) (cstate_bt r1) (gs_add x (ge_ind pv pq k Dd (gu_mod U)) Ξ)
                   pv R pq Dd (S k) xs'
                   (member_pre H (mems_fresh_head Hp) (mems_pre_uparams _ _ _ _ _ _ Hp) HE Hr1 HΞ)
                   (mems_pre_tail Hp pv (gu_mod U)) (later_head_entry (mems_pre_tail Hp pv (gu_mod U))) => {
          | rerr e => rerr e
          | rok (exist _ r2 Hr2, l2) =>
              rok (exist _ r2 (mems_cons_ok HM (mems_fresh_head Hp) (mems_pre_uparams _ _ _ _ _ _ Hp) HE Hr1 HΞ Hr2),
                   log_app l1 l2) } } } }.

  (** ** Why a Group Is Ill Formed

      Read only for the checker's message, once [ind_nil_at_dec] has
      rejected the group. *)

  (** Which non-uniform parameter, if any, of the telescope [l] (innermost
      first, over [U]) has a type not in the sort [S]: its position,
      outermost [0], the context its type is in, its type and the sort
      there. *)
  Fixpoint npar_blame (Θ0 : gdeps) (Ξ : gstack) (HΞ : ⊢ᵍ Θ0 ⍮ Ξ) (U : ctx) (S : typ) (l : ctx)
    : option (nat * ctx * typ * typ) :=
    match l with
    | nil => None
    | ce_ass T :: Δ2 =>
        match npar_blame Θ0 Ξ HΞ U S Δ2 with
        | Some r => Some r
        | None =>
            if check_exp_at Θ0 Ξ HΞ (Δ2 ++ U)%list S[wk_shiftn (List.length Δ2)]ʷ T then None
            else Some (List.length Δ2, (Δ2 ++ U)%list, T, S[wk_shiftn (List.length Δ2)]ʷ)
        end
    | _ :: Δ2 => npar_blame Θ0 Ξ HΞ U S Δ2
    end.

  (** The first declared member, with its name, whose non-uniform
      parameters [npar_blame] blames. *)
  Fixpoint members_npar_blame (Θ0 : gdeps) (Ξ : gstack) (HΞ : ⊢ᵍ Θ0 ⍮ Ξ) (Dd : ind_decl)
    (Mrs : list raw_member) (Ms : list imember) : option (string * (nat * ctx * typ * typ)) :=
    match Mrs, Ms with
    | Mr :: Mrs', Mk :: Ms' =>
        match npar_blame Θ0 Ξ HΞ (ind_uparams Dd) (ind_sort Dd) (im_nparams Mk) with
        | Some r => Some (raw_member_name Mr, r)
        | None => members_npar_blame Θ0 Ξ HΞ Dd Mrs' Ms'
        end
    | _, _ => None
    end.

  (** Whether a recursive argument of some member is its member at a
      number of non-uniform arguments other than that member's: the
      member's position, if so. *)
  Definition rec_arity_blame (Dd : ind_decl) : option nat :=
    List.find (fun j => negb (forallb (fun Mi =>
                 forallb (fun cg => forallb (fun g => match g with
                                                      | ca_rec t =>
                                                          if Nat.eqb (ptyp_mem t) j then
                                                            Nat.eqb (List.length (ptyp_ps t))
                                                              (match ind_member Dd j with Some Mj => im_nn Mj | None => 0 end)
                                                          else true
                                                      | ca_arg _ => true
                                                      end) (snd cg)) (im_cons Mi)) (ind_members Dd)))
      (List.seq 0 (List.length (ind_members Dd))).

  (** The message of an ill-formed group: a non-uniform parameter not in
      the sort, a recursive argument at the wrong number of arguments, or
      the group itself. *)
  Definition ind_wf_error (Θ0 : gdeps) (Ξ : gstack) (HΞ : ⊢ᵍ Θ0 ⍮ Ξ) (R : raw_decl) (Mr0 : raw_member) (Dd : ind_decl)
    : run_error :=
    match members_npar_blame Θ0 Ξ HΞ Dd (raw_decl_members R) (ind_members Dd) with
    | Some (x, (k, Δ, T, St)) => run_error_ind_npar x k Δ T St
    | None =>
        match rec_arity_blame Dd with
        | Some j =>
            run_error_msg ("a recursive argument is "
                    ++ match List.nth_error (raw_decl_members R) j with Some Mr => raw_member_name Mr | None => raw_member_name Mr0 end
                    ++ " applied to all its parameters")
        | None => run_error_msg ("ill-formed inductive declaration " ++ raw_member_name Mr0)
        end
    end.

  (** The first member of [ms] whose name is not fresh in [Ξ]. *)
  Fixpoint first_taken (Ξ : gstack) (ms : list raw_member) : option string :=
    match ms with
    | nil => None
    | Mr :: ms' => if gs_fresh_dec (raw_member_name Mr) Ξ then first_taken Ξ ms' else Some (raw_member_name Mr)
    end.

  (** Whether the first declared member of [D] has a constructor [c]. *)
  Definition first_has_con (D : ind_decl) (c : string) : bool :=
    match ind_member D 0 with
    | Some M => List.existsb (String.eqb c) (List.map fst (im_cons M))
    | None => false
    end.

  Lemma first_has_con_false : forall D c, first_has_con D c = false ->
      forall M, ind_member D 0 = Some M -> ~ In c (List.map fst (im_cons M)).
  Proof.
    intros * H M HM Hin; unfold first_has_con in H; rewrite HM in H.
    rewrite <- Bool.not_true_iff_false, List.existsb_exists in H; apply H; exists c; split; [ exact Hin | apply String.eqb_refl ].
  Qed.

  Lemma first_has_con_true : forall D c M, ind_member D 0 = Some M -> In c (List.map fst (im_cons M)) ->
      first_has_con D c = true.
  Proof.
    intros * HM Hin; unfold first_has_con; rewrite HM.
    apply List.existsb_exists; exists c; split; [ exact Hin | apply String.eqb_refl ].
  Qed.

  (** Which name a group declared as [R] at [Ξ], filed as [D], with first
      member [x0], generates where one of its own names is: [rec] or
      [Rec] at a constructor of the first member, [Rec] at a member of a
      [mutual T] group or already in [T]'s frame ([gen_names_free]). *)
  Definition gen_names_blame (Ξ : gstack) (R : raw_decl) (D : ind_decl) (x0 : string) : option run_error :=
    if (ind_has_rec D && first_has_con D "rec")%bool then
      Some (run_error_msg ("rec is the recursor of " ++ x0 ++ ", not a constructor"))
    else if (negb (raw_decl_rec_field R) && first_has_con D "Rec")%bool then
      Some (run_error_msg ("Rec is the recursor module of " ++ x0 ++ ", not a constructor"))
    else if (raw_decl_rec_field R && List.existsb (String.eqb "Rec") (List.map raw_member_name (raw_decl_members R)))%bool then
      Some (run_error_msg ("Rec is the recursor module of " ++ qname_last (gs_path Ξ) ++ ", not a member"))
    else if (raw_decl_rec_field R && negb (if gs_fresh_dec "Rec" Ξ then true else false))%bool then
      Some (run_error_msg "duplicate name Rec")
    else None.

  Lemma gen_names_blame_none {Ξ R D x0} : gen_names_blame Ξ R D x0 = None -> gen_names_free Ξ R D.
  Proof.
    unfold gen_names_blame; intros H.
    destruct (ind_has_rec D && first_has_con D "rec")%bool eqn:E1; [ discriminate |].
    destruct (negb (raw_decl_rec_field R) && first_has_con D "Rec")%bool eqn:E2; [ discriminate |].
    destruct (raw_decl_rec_field R && List.existsb (String.eqb "Rec") (List.map raw_member_name (raw_decl_members R)))%bool eqn:E3; [ discriminate |].
    destruct (raw_decl_rec_field R && negb (if gs_fresh_dec "Rec" Ξ then true else false))%bool eqn:E4; [ discriminate |].
    constructor.
    - intros Hr; rewrite Hr in E1; exact (first_has_con_false _ _ E1).
    - intros Hr; rewrite Hr in E2; exact (first_has_con_false _ _ E2).
    - intros Hr Hin; rewrite Hr in E3; cbn [andb] in E3.
      rewrite <- Bool.not_true_iff_false, List.existsb_exists in E3; apply E3.
      exists "Rec"%string; split; [ exact Hin | apply String.eqb_refl ].
    - intros Hr; rewrite Hr in E4; cbn [andb] in E4.
      destruct (gs_fresh_dec "Rec" Ξ) as [Hf | Hf]; [ exact Hf | discriminate ].
  Qed.

  Lemma gen_names_blame_free {Ξ R D x0} : gen_names_free Ξ R D -> gen_names_blame Ξ R D x0 = None.
  Proof.
    intros [H1 H2 H3 H4]; unfold gen_names_blame.
    assert (Hfc : forall c, (forall M, ind_member D 0 = Some M -> ~ In c (List.map fst (im_cons M))) ->
                    first_has_con D c = false).
    { intros c Hc; unfold first_has_con; destruct (ind_member D 0) as [M |] eqn:HM; [| reflexivity ].
      apply Bool.not_true_iff_false; intros E; apply List.existsb_exists in E as (c' & Hc' & Hq).
      apply String.eqb_eq in Hq; subst c'; exact (Hc M eq_refl Hc'). }
    assert (E1 : (ind_has_rec D && first_has_con D "rec")%bool = false).
    { destruct (ind_has_rec D) eqn:Er; [ exact (Hfc _ (H1 eq_refl)) | reflexivity ]. }
    assert (E2 : (negb (raw_decl_rec_field R) && first_has_con D "Rec")%bool = false).
    { destruct (raw_decl_rec_field R) eqn:Ed; [ reflexivity | exact (Hfc _ (H2 eq_refl)) ]. }
    assert (E3 : (raw_decl_rec_field R && List.existsb (String.eqb "Rec") (List.map raw_member_name (raw_decl_members R)))%bool = false).
    { destruct (raw_decl_rec_field R) eqn:Ed; [| reflexivity ]; cbn [andb negb].
      apply Bool.not_true_iff_false; intros E; apply List.existsb_exists in E as (c & Hc & Hq).
      apply String.eqb_eq in Hq; subst c; exact (H3 eq_refl Hc). }
    assert (E4 : (raw_decl_rec_field R && negb (if gs_fresh_dec "Rec" Ξ then true else false))%bool = false).
    { destruct (raw_decl_rec_field R) eqn:Ed; [| reflexivity ]; cbn [andb negb].
      destruct (gs_fresh_dec "Rec" Ξ) as [Hf | Hf]; [ reflexivity | exfalso; exact (Hf (H4 eq_refl)) ]. }
    rewrite E1, E2, E3, E4; reflexivity.
  Qed.

  (** A group declaration, checked premise by premise: one sort, the
      declared members' constructors classified, the views found, the
      group filed, its names, the group well formed at its views'
      instances read back, and the names it generates free; then its
      members, each with its module, by [members_step], and its recursor
      module, if any, by [rec_step]. *)
  Equations ind_step (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (pv : bool) (R : raw_decl) (H : exists ΘR, linv ch Θ K D ΘR Ξ) :
    rres ({r | post_cmd ch Θ K D B Ξ (cc_ind pv R) r} * elog)%type :=
  | ch, Θ, K, D, B, Ξ, pv, R, H with list_case (raw_decl_members R) => {
    | inright _ => rerr (run_error_msg "a declaration of no inductive type")
    | inleft (existT _ Mr0 (exist _ Mrs HR))
        with Forall_dec (fun Mr => raw_member_sort Mr = raw_member_sort Mr0) (fun Mr => exp_eq_dec (raw_member_sort Mr) (raw_member_sort Mr0)) Mrs => {
      | right _ => rerr (run_error_msg ("the types declared with " ++ raw_member_name Mr0 ++ " are not all of its sort"))
      | left Hsort with rms_cls_dec (gds_restrict D Θ) Ξ (pre_gctx H) R (raw_decl_members R) => {
        | inr (exist _ (x, c, y, cls_why_code sf) _) => rerr (run_error_msg (cls_msg x c y sf))
        | inr (exist _ (x, c, y, cls_why_unapplied k) _) =>
            rerr (run_error_msg (cls_msg (List.nth k (List.map raw_member_name (raw_decl_members R)) x) c y 3))
        | inr (exist _ (x, c, y, cls_why_nested h) _) => rerr (run_error_nested x c y h)
        | inl (exist _ csD Hcls) with views_search (gds_restrict D Θ) Ξ (pre_gctx H) R csD => {
          | rerr e => rerr e
          | rok (existT _ Vs (existT _ Ss (existT _ csV (exist _ Nvs Hv))))
              with opt_case (rd_filed (gds_restrict D Θ) Ξ R Vs Ss csD csV Nvs) => {
            | inright _ => rerr (run_error_msg ("internal error: the group of " ++ raw_member_name Mr0 ++ " cannot be filed"))
            | inleft (exist _ Dd Hfil) with nodup_dec (List.map raw_member_name (raw_decl_members R)) => {
              | right _ => rerr (run_error_msg ("two types declared with " ++ raw_member_name Mr0 ++ " have one name"))
              | left Hnd with Forall_dec (fun Mr => gs_fresh (raw_member_name Mr) Ξ) (fun Mr => gs_fresh_dec (raw_member_name Mr) Ξ) (raw_decl_members R) => {
                | right _ =>
                    rerr (run_error_msg ("duplicate name " ++ match first_taken Ξ (raw_decl_members R) with Some x => x | None => raw_member_name Mr0 end))
                | left Hfr
                    with ind_nil_at_dec (gds_restrict D Θ) Ξ (pre_gctx H) (ind_qname Ξ (raw_member_name Mr0)) Dd
                           (grp_self_insts (ind_qname Ξ (raw_member_name Mr0)) Dd) => {
                  | right _ => rerr (ind_wf_error (gds_restrict D Θ) Ξ (pre_gctx H) R Mr0 Dd)
                  | left Hnil with inspect (gen_names_blame Ξ R Dd (raw_member_name Mr0)) => {
                  | exist _ (Some e) _ => rerr e
                  | exist _ None Egn
                      with members_step ch Θ K D B Ξ pv R (ind_qname Ξ (raw_member_name Mr0)) Dd 0 (List.map raw_member_name (raw_decl_members R)) H
                             (ind_mems_pre HR Hfil Hnd Hfr) (first_head_entry (ind_mems_pre HR Hfil Hnd Hfr) Hnil) => {
                    | rerr e => rerr e
                    | rok (exist _ r1 Hr1, l1)
                        with rec_step ch (cstate_deps r1) (cstate_k r1) (cstate_dom r1) (cstate_bt r1) (cstate_stack r1)
                               (rec_cmds (gds_restrict (cstate_dom r1) (cstate_deps r1)) (cstate_stack r1) R (ind_qname Ξ (raw_member_name Mr0)) Dd)
                               (mems_post_pre H Hr1) => {
                      | rerr e => rerr e
                      | rok (exist _ r2 Hr2, l2) =>
                          rok (exist _ r2 (ind_ok HR Hsort Hcls (views_siblings _ _ _ _ _ _ _ _ Hv) (views_classified _ _ _ _ _ _ _ _ Hv)
                                             (views_nparams _ _ _ _ _ _ _ _ Hv) (views_search_run _ _ _ _ _ _ _ _ Hv) Hfil Hnil
                                             (gen_names_blame_none Egn) Hr1 Hr2),
                               log_app l1 l2) } } } } } } } } } } }.

  (** Every expanded command but a module, which recurses on its body. *)
  Equations simple_step (ch : list path) (L : loader ch) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (c : ccmd) (H : exists ΘR, linv ch Θ K D ΘR Ξ) : rres ({r | post_cmd ch Θ K D B Ξ c r} * elog)%type :=
  | ch, L, Θ, K, D, B, Ξ, cc_def x b pv A M, H with defalias_step ch Θ K D B Ξ (cc_def x b pv A M) H => {
    | rerr e => rerr e
    | rok (exist _ Ξ' Hp) => rok (cmd_ok Hp, log_nil) }
  | ch, L, Θ, K, D, B, Ξ, cc_alias x pv Δ E, H with defalias_step ch Θ K D B Ξ (cc_alias x pv Δ E) H => {
    | rerr e => rerr e
    | rok (exist _ Ξ' Hp) => rok (cmd_ok Hp, log_nil) }
  | ch, L, Θ, K, D, B, Ξ, cc_mod _ _ _ _, H => rerr (run_error_msg "internal error: a module is run by its own step")
  | ch, L, Θ, K, D, B, Ξ, cc_record _ _ _ _ _ _, H => rerr (run_error_msg "internal error: a record is run by its own step")
  | ch, L, Θ, K, D, B, Ξ, cc_gen _, H => rerr (run_error_msg "internal error: a generated command is run by its own step")
  | ch, L, Θ, K, D, B, Ξ, cc_load fp, H with opt_case (gds_lookup Θ fp) => {
    | inleft (exist _ U HU) with opt_case (kbt K fp) => {
      | inright _ => rerr (run_error_msg "internal error: a filed unit has no record")
      | inleft (exist _ BU HB) with inspect (bt_merge B BU) => {
        | exist _ None _ => rerr (run_error_msg (bound_msg B))
        | exist _ (Some B') Hm with in_dec path_eq_dec fp D => {
          | left Hin => rok (exist _ _ (load_in_ok Hin HU HB Hm), log_nil)
          | right Hnin with opt_case (kfind K fp) => {
            | inleft (exist _ Dfp HK) => rok (exist _ _ (load_hit_ok Hnin HU HK HB Hm), log_nil)
            | inright _ => rerr (run_error_msg "internal error: a filed unit has no closure") } } } }
    | inright Hn with in_dec path_eq_dec fp ch => {
      | left _ => rerr (run_error_cycle (cycle_chain fp ch))
      | right Hnch with opt_case (load_path fp) => {
        | inright _ => rerr (run_error_unit fp "cannot find unit")
        | inleft (exist _ src Hsrc) with opt_case (read src) => {
          | inright _ => rerr (run_error_unit fp "cannot parse unit")
          | inleft (exist _ prg Hprg) with path_eq_dec (prog_path prg) fp => {
            | right _ => rerr (run_error_unit fp "the file of the unit declares another unit")
            | left Hp with opt_case (to_core prg) => {
              | inright _ => rerr (run_error_unit fp "cannot elaborate unit")
              | inleft (exist _ u Hu) with L fp src Hnch Hsrc Θ K u (load_pre H Hn Hnch) => {
                | rerr e => rerr e
                | rok (exist _ r Hr, _) with inspect (bt_merge B (us_bt r)) => {
                  | exist _ None _ => rerr (run_error_msg (bound_msg B))
                  | exist _ (Some B') Hm => rok (exist _ _ (load_ok Hn Hnch Hsrc Hprg Hp Hu Hr Hm), log_nil) } } } } } } } }
  | ch, L, Θ, K, D, B, Ξ, cc_open E its, H with check_modexp (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) E => {
    | right _ => rerr (run_error_import (xe_target E))
    | left HE with inspect (import_gen _ _ (pre_gctx H) (gs_tele Ξ) E E HE its) => {
      | exist _ (xfail e) _ => rerr (run_error_import e)
      | exist _ (xok gs) Eg with gens_impl ch Θ K D B Ξ gs H => {
        | rerr e => rerr e
        | rok (exist _ Ξ' Hgs) => rok (exist _ _ (import_ok (pre_gctx H) HE Eg Hgs), log_nil) } } }
  | ch, L, Θ, K, D, B, Ξ, cc_eval M (Some A), H
      with check_typ (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A => {
    | inright _ => rerr (blame_error (find_level_blame fctx_none _ _ _ (pre_ctx H) A)
                          (mod_error (pre_gctx H) None (A :: nil) (run_error_eval_typ Ξ M A)))
    | inleft (exist _ i HA)
        with check_exp_typed (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A (ex_intro _ i HA) M => {
      | left HM => rok (exist _ _ (eval_check_ok HM), eval_log _ _ (fctx_cmd B _ _) (pre_gctx H) M A HM)
      | right _ =>
          rerr (mod_error (pre_gctx H) None (M :: nil)
                  (field_error (fctx_cmd B) (gds_restrict D Θ) Ξ None (pre_ctx H) M (run_error_eval_check Ξ M A))) } }
  | ch, L, Θ, K, D, B, Ξ, cc_eval M None, H
      with @type_infer_at (gc_mk (gds_restrict D Θ) Ξ) (fctx_cmd B (gds_restrict D Θ) Ξ) (gs_tele Ξ) (pre_ctx H) M (user_exp_all M) => {
    | inleft (exist _ A HA) => rok (exist _ _ (eval_infer_ok A HA), eval_log _ _ (fctx_cmd B _ _) (pre_gctx H) M A HA)
    | inright _ =>
        rerr (mod_error (pre_gctx H) None (M :: nil)
                (field_error (fctx_cmd B) (gds_restrict D Θ) Ξ None (pre_ctx H) M (run_error_eval_infer Ξ M))) }
  | ch, L, Θ, K, D, B, Ξ, cc_builtin k p, H with builtin_step ch Θ K D B Ξ k p H => {
    | rerr e => rerr e
    | rok (exist _ B' Hp) => rok (cmd_ok Hp, log_nil) }
  | ch, L, Θ, K, D, B, Ξ, cc_ind_alias x pv Δ E, H with indalias_step ch Θ K D B Ξ x pv Δ E H => {
    | rerr e => rerr e
    | rok (exist _ Ξ' Hp) => rok (cmd_ok Hp, log_nil) }
  | ch, L, Θ, K, D, B, Ξ, cc_record_alias x pv Δ E, H with recalias_step ch Θ K D B Ξ x pv Δ E H => {
    | rerr e => rerr e
    | rok (exist _ Ξ' Hp) => rok (cmd_ok Hp, log_nil) }
  | ch, L, Θ, K, D, B, Ξ, cc_ind pv R, H with ind_step ch Θ K D B Ξ pv R H => {
    | rerr e => rerr e
    | rok (exist _ r Hp, l) => rok (cmd_ok Hp, l) }
  | ch, L, Θ, K, D, B, Ξ, cc_mdef b pv Δ fs, H with mdef_step ch Θ K D B Ξ b pv Δ fs H => {
    | rerr e => rerr e
    | rok (exist _ Ξ' Hp) => rok (cmd_ok Hp, log_nil) }.

  (** The error of a rejected command: the first open of it that
      generates nothing, if any, otherwise the error found. *)
  (** An open's target, checked in the context the error reader builds. *)
  Definition mod_chk {Θ Ξ} (Hg : ⊢ᵍ Θ ⍮ Ξ) (Γ : ctx) (E : modexp) : option (Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E) :=
    match check_ctx fctx_none Θ Ξ Hg Γ with
    | left HΓ =>
        match check_modexp fctx_none Θ Ξ Γ HΓ E with
        | left HE => Some HE
        | right _ => None
        end
    | right _ => None
    end.

  Definition open_error {Θ Ξ} (Hg : ⊢ᵍ Θ ⍮ Ξ) (c : ccmd) (e : run_error) : run_error :=
    match cmd_open_error Θ Ξ Hg (mod_chk Hg) (frame_skel Ξ) c with
    | Some e' => run_error_import e'
    | None => e
    end.

  Definition tele_error {Θ Ξ} (Hg : ⊢ᵍ Θ ⍮ Ξ) (S : skel) (Δ : ctx) (e : run_error) : run_error :=
    match tele_open_error Θ Ξ Hg (mod_chk Hg) S Δ with
    | Some e' => run_error_import e'
    | None => e
    end.

  (** The first block of an eliminator of the group [D] whose branches do
      not match its member's constructors ([branch_check]), the blocks
      taken in member order. *)
  Definition blocks_branch_blame (D : ind_decl) (Bks : list eblock) : option run_error :=
    List.fold_right (fun mb r => first_some (branch_check (fst mb) (eb_brs (snd mb))) (fun _ => r)) None
      (List.combine (ind_members D) Bks).

  (** Why a command declaring [ox] has no fill, as a run error: a term's
      context is given past the stack's telescope.  An eliminator no
      reading of which fits its blocks is blamed on its scrutinee's own
      group [pc]: on its blocks, too few, too many or out of member order
      ([elim_blocks_check]), else on a block's branches
      ([blocks_branch_blame]), else as fitting no group. *)
  Definition fill_run_error {Θ Ξ} (Hg : ⊢ᵍ Θ ⍮ Ξ) (ox : option string) (e : fill_failure) : run_error :=
    let past (Γ : ctx) := List.firstn (List.length Γ - List.length (gs_tele Ξ)) Γ in
    match e with
    | fill_failure_no_type y Γ M => run_error_access_no_type Ξ ox (past Γ) M y
    | fill_failure_not_record y Γ M W => run_error_access_not_record Ξ ox (past Γ) M (nf_to_exp W) y
    | fill_failure_private qd x => run_error_private qd x
    | fill_failure_mdef_group e' => mdef_group_why_error e'
    | fill_failure_literal e' => run_error_lit e'
    | fill_failure_elim_scrutinee Γ M oW => run_error_elim_scrutinee Ξ ox (past Γ) M (option_map nf_to_exp oW)
    | fill_failure_elim_none Γ pc k Rs m Bks M =>
        match ind_lookup Θ Ξ pc with
        | Some D =>
            match elim_blocks_check Θ Ξ (past Γ) (a_elim (Some pc) (List.firstn (ind_nu D) (List.map nf_to_exp Rs)) m Bks M) with
            | Some e' => e'
            | None =>
                match blocks_branch_blame D Bks with
                | Some e' => e'
                | None => run_error_elim_no_group Ξ (past Γ) (a_elim None nil m Bks M)
                end
            end
        | None => run_error_elim_no_group Ξ (past Γ) (a_elim None nil m Bks M)
        end
    | fill_failure_elim_ambiguous Γ E rs => run_error_elim_ambiguous Ξ (past Γ) E rs
    | fill_failure_body Γ Φ =>
        match oe_body Θ Ξ Hg (mod_chk Hg) (List.map centry_skel Γ) Φ with
        | xfail e' => run_error_import e'
        | xok _ => run_error_msg "a local open of a body opens no module"
        end
    | fill_failure_message s => run_error_msg s
    end.

  (** Whether a fill failure is final: a member selected through a term
      that infers no type, or no record type, or is private; a mutual
      definition's functions with no group; a literal with no binding; an
      eliminator whose scrutinee's type is no inductive type, or with no
      reading or several.  Any other failure, a scrutinee with no type
      included, is of a command that does not run anyway; the run,
      unfilled, says why ([fill_simple]). *)
  Definition fill_failure_final (e : fill_failure) : bool :=
    match e with
    | fill_failure_no_type y _ _ | fill_failure_not_record y _ _ _ => negb (String.eqb y "")
    | fill_failure_private _ _ | fill_failure_mdef_group _ | fill_failure_literal _ => true
    | fill_failure_elim_scrutinee _ _ (Some _) | fill_failure_elim_none _ _ _ _ _ _ _
    | fill_failure_elim_ambiguous _ _ _ | fill_failure_body _ _ => true
    | fill_failure_elim_scrutinee _ _ None | fill_failure_message _ => false
    end.

  (** A command filled, then run by [simple_step].  When the fill fails
      other than finally, the error is the unfilled command's run's, if it
      fails. *)
  Definition fill_simple (ch : list path) (L : loader ch) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (c : ccmd) (H : exists ΘR, linv ch Θ K D ΘR Ξ) : rres ({r | post_lcmd ch Θ K D B Ξ c r} * elog)%type :=
    match inspect (fill_cmd_fn (gds_restrict D Θ) Ξ B (pre_gctx H) (fctx_cmd B) c) with
    | exist _ (fill_error e) _ =>
        if fill_failure_final e then rerr (fill_run_error (pre_gctx H) (cmd_decl_name c) e)
        else match simple_step ch L Θ K D B Ξ c H with
             | rerr e' => rerr (open_error (pre_gctx H) c e')
             | rok _ => rerr (fill_run_error (pre_gctx H) (cmd_decl_name c) e)
             end
    | exist _ (fill_ok c') Ea =>
        match simple_step ch L Θ K D B Ξ c' H with
        | rok (exist _ r Hp, l) => rok (exist _ r (fill_lift (fill_cmd_fn_sound _ _ _ _ _ _ _ Ea) Hp), l)
        | rerr e => rerr (open_error (pre_gctx H) c' e)
        end
    end.

  #[derive(eliminator=no)]
  Equations run_cmd_impl (ch : list path) (L : loader ch) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (c : ccmd) (H : exists ΘR, linv ch Θ K D ΘR Ξ) : rres ({r | post_lcmd ch Θ K D B Ξ c r} * elog)%type by struct c :=
  | ch, L, Θ, K, D, B, Ξ, cc_mod x pv Δ0 cs, H
      with inspect (fill_params_fn (gds_restrict D Θ) Ξ B (pre_gctx H) (fctx_cmd B) Δ0) => {
    | exist _ (fill_error e) _ => rerr (fill_run_error (pre_gctx H) None e)
    | exist _ (fill_ok Δ) Ea with tele_ass_dec Δ => {
    | right _ => rerr (tele_error (pre_gctx H) (frame_skel Ξ) Δ (run_error_msg ("parameters of module " ++ x ++ " that are not assumptions")))
    | left Htel with check_ctx (fctx_cmd B) (gds_restrict D Θ) Ξ (pre_gctx H) (Δ ++ gs_tele Ξ) => {
      | right _ =>
          rerr (tele_error (pre_gctx H) (frame_skel Ξ) Δ (tele_blame_error (find_tele_blame fctx_none _ _ _ (pre_ctx H) Δ)
                  (run_error_msg ("ill-formed parameters of module " ++ x))))
      | left HΔ with gs_fresh_dec x Ξ => {
        | right _ => rerr (run_error_msg ("duplicate name " ++ x))
        | left Hfr with cmds_step ch (run_cmd_impl ch L) Θ K D B (gs_push (qname_in (gs_path Ξ) x) Δ Ξ) cs
                          (mod_pre H Htel Hfr HΔ) => {
          | rerr e => rerr e
          | rok (exist _ r Hr, l) with list_case (cstate_stack r) => {
            | inleft (existT _ (mp, Kf, U) (exist _ _ HΞ)) =>
                rok (exist _ _ (fill_lift
                                  (fill_cmd_mod_params _ _ _ _ _ _ _ _ (fill_params_fn_sound _ _ _ _ _ _ _ Ea))
                                  (mod_ok Htel Hfr HΔ Hr HΞ)), l)
            | inright _ => rerr (run_error_msg "internal error: a module body lost its frame") } } } } } }
  | ch, L, Θ, K, D, B, Ξ, cc_record x pv Δ0 S0 fs0 cs, H
      with inspect (fill_record_fn (gds_restrict D Θ) Ξ B (pre_gctx H) (fctx_cmd B) x pv Δ0 S0 fs0 cs) => {
    | exist _ (fill_error e) _ => rerr (fill_run_error (pre_gctx H) None e)
    | exist _ (fill_ok (Δ, Srt, fs)) Ea
        with record_typed_dec (gds_restrict D Θ) Ξ (pre_gctx H) (record_at Ξ Δ Srt fs) => {
    | inr (exist _ e _) => rerr (record_why_error x fs e)
    | inl Ht with gs_fresh_dec x Ξ => {
      | right _ => rerr (run_error_msg ("duplicate name " ++ x))
      | left Hfr with inspect (field_clash fs cs) => {
      | exist _ (Some f) _ => rerr (run_error_msg (f ++ " is a field of record " ++ x))
      | exist _ None _
          with cmds_step ch (gen_def_cmd ch) Θ K D B (gs_push_record (ind_qname Ξ x) (record_at Ξ Δ Srt fs) Δ Ξ)
                 (record_field_cmds (record_at Ξ Δ Srt fs)) (record_pre H Hfr Ht) => {
        | rerr e => rerr e
        | rok (exist _ r1 Hr1, l1)
            with cmds_step ch (run_cmd_impl ch L) (cstate_deps r1) (cstate_k r1) (cstate_dom r1) (cstate_bt r1) (cstate_stack r1) cs
                   (cmds_post_pre (record_pre H Hfr Ht) Hr1) => {
          | rerr e => rerr e
          | rok (exist _ r2 Hr2, l2) with list_case (cstate_stack r2) => {
            | inleft (existT _ (mp, Kf, U) (exist _ _ HΞ)) =>
                rok (exist _ _ (fill_lift (fill_record_fn_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ea)
                                  (record_ok (pv := pv) Hfr Ht Hr1 Hr2 HΞ)), log_app l1 l2)
            | inright _ => rerr (run_error_msg "internal error: a record's module lost its frame") } } } } } } }
  | ch, L, Θ, K, D, B, Ξ, cc_def x b pv A M, H => fill_simple ch L Θ K D B Ξ (cc_def x b pv A M) H
  | ch, L, Θ, K, D, B, Ξ, cc_alias x pv Δ E, H => fill_simple ch L Θ K D B Ξ (cc_alias x pv Δ E) H
  | ch, L, Θ, K, D, B, Ξ, cc_load fp, H => fill_simple ch L Θ K D B Ξ (cc_load fp) H
  | ch, L, Θ, K, D, B, Ξ, cc_open E its, H => fill_simple ch L Θ K D B Ξ (cc_open E its) H
  | ch, L, Θ, K, D, B, Ξ, cc_eval M oA, H => fill_simple ch L Θ K D B Ξ (cc_eval M oA) H
  | ch, L, Θ, K, D, B, Ξ, cc_ind pv R, H => fill_simple ch L Θ K D B Ξ (cc_ind pv R) H
  | ch, L, Θ, K, D, B, Ξ, cc_mdef b pv Δ fs, H => fill_simple ch L Θ K D B Ξ (cc_mdef b pv Δ fs) H
  | ch, L, Θ, K, D, B, Ξ, cc_builtin k p, H => fill_simple ch L Θ K D B Ξ (cc_builtin k p) H
  | ch, L, Θ, K, D, B, Ξ, cc_ind_alias x pv Δ E, H => fill_simple ch L Θ K D B Ξ (cc_ind_alias x pv Δ E) H
  | ch, L, Θ, K, D, B, Ξ, cc_record_alias x pv Δ E, H => fill_simple ch L Θ K D B Ξ (cc_record_alias x pv Δ E) H
  | ch, L, Θ, K, D, B, Ξ, cc_gen (cc_def x b pv A (Some M)), H with simple_step ch L Θ K D B Ξ (cc_def x b pv A (Some M)) H => {
    | rerr e => rerr e
    | rok (exist _ r Hr, l) => rok (exist _ r (gen_lift Hr I), l) }
  | ch, L, Θ, K, D, B, Ξ, cc_gen (cc_mod x pv Δ cs), H
      with gen_mod_step ch (cmds_step ch (run_cmd_impl ch L)) Θ K D B Ξ x pv Δ cs H => {
    | rerr e => rerr e
    | rok (exist _ r Hr, l) => rok (exist _ r (gen_lift Hr I), l) }
  | ch, L, Θ, K, D, B, Ξ, cc_gen _, H => rerr (run_error_msg "internal error: only definitions and modules are generated").

  Definition run_cmds_impl (ch : list path) (L : loader ch) := cmds_step ch (run_cmd_impl ch L).

  Definition run_unit_step (ch : list path) (L : loader ch) (Θ : gdeps) (K : kmap) (u : cunit)
    (H : ginv ch Θ K) : rres ({r | post_unit ch Θ K u r} * elog)%type :=
    match ch as ch0 return loader ch0 -> ginv ch0 Θ K -> rres ({r | post_unit ch0 Θ K u r} * elog)%type with
    | nil => fun _ _ => rerr (run_error_msg "internal error: no unit to run")
    | fp :: ch0 => fun L H =>
    match u as u0 return rres ({r | post_unit (fp :: ch0) Θ K u0 r} * elog)%type with
    | (imps, P0, cs) =>
        match run_cmds_impl (fp :: ch0) L Θ K nil bt_empty nil imps (unit_pre H) with
        | rerr e => rerr e
        | rok (exist _ r1 Hr1, l1) =>
            match inspect (fill_params_fn (gds_restrict (cstate_dom r1) (cstate_deps r1)) nil (cstate_bt r1) (unit_gctx H Hr1)
                             (fctx_cmd (cstate_bt r1)) P0) with
            | exist _ (fill_error e) _ =>
                rerr (run_error_nat (gds_restrict (cstate_dom r1) (cstate_deps r1)) nil (nat_view (gds_restrict (cstate_dom r1) (cstate_deps r1)) nil (cstate_bt r1))
                        (fill_run_error (unit_gctx H Hr1) None e))
            | exist _ (fill_ok P) Ea =>
            match tele_ass_dec P with
            | right _ => rerr (run_error_nat (gds_restrict (cstate_dom r1) (cstate_deps r1)) nil (nat_view (gds_restrict (cstate_dom r1) (cstate_deps r1)) nil (cstate_bt r1))
                                (tele_error (unit_gctx H Hr1) nil P (run_error_msg "unit parameters that are not assumptions")))
            | left Htel =>
            match check_ctx (fctx_cmd (cstate_bt r1)) (gds_restrict (cstate_dom r1) (cstate_deps r1)) nil (unit_gctx H Hr1) P with
            | right _ =>
                rerr (run_error_nat (gds_restrict (cstate_dom r1) (cstate_deps r1)) nil (nat_view (gds_restrict (cstate_dom r1) (cstate_deps r1)) nil (cstate_bt r1))
                        (tele_error (unit_gctx H Hr1) nil P (tele_blame_error (find_tele_blame fctx_none _ _ _ (wf_ctx_empty _ _ (unit_gctx H Hr1)) P)
                        (run_error_msg "ill-formed unit parameters"))))
            | left HP =>
            match refs_check (gds_restrict (cstate_dom r1) (cstate_deps r1)) nil (unit_gctx H Hr1) (tele_refs nil P0) with
            | inleft (exist _ e _) => rerr (run_error_nat (gds_restrict (cstate_dom r1) (cstate_deps r1)) nil (nat_view (gds_restrict (cstate_dom r1) (cstate_deps r1)) nil (cstate_bt r1)) (priv_error e))
            | inright Hac =>
                match run_cmds_impl (fp :: ch0) L (cstate_deps r1) (cstate_k r1) (cstate_dom r1) (cstate_bt r1) (gs_push (q_abs fp nil) P nil) cs
                        (unit_body_pre H Hr1 Htel HP) with
                | rerr e => rerr e
                | rok (exist _ r2 Hr2, l2) =>
                    match list_case (cstate_stack r2) with
                    | inleft (existT _ (mp, Kf, U) (exist _ _ HΞ)) =>
                        rok (exist _ _ (unit_ok Hr1 (fill_params_fn_sound _ _ _ _ _ _ _ Ea) Htel HP Hac Hr2 HΞ),
                             log_app l1 l2)
                    | inright _ => rerr (run_error_msg "internal error: a unit body lost its frame")
                    end
                end
            end
            end
            end
            end
        end
    end
    end L H.

  #[derive(eliminator=no)]
  Equations run_unit_impl (ch : list path) (Hacc : Acc load_step ch) :
    forall Θ K u, ginv ch Θ K -> rres ({r | post_unit ch Θ K u r} * elog)%type by struct Hacc :=
  run_unit_impl ch Hacc :=
    run_unit_step ch (fun fp src Hn Hs => run_unit_impl (fp :: ch) (Acc_inv Hacc (load_step_intro Hn Hs))).

  Definition loader_of (ch : list path) (Hacc : Acc load_step ch) : loader ch :=
    fun fp src Hn Hs => run_unit_impl (fp :: ch) (Acc_inv Hacc (load_step_intro Hn Hs)).

  Lemma run_unit_impl_unfold : forall ch Hacc, run_unit_impl ch Hacc = run_unit_step ch (loader_of ch Hacc).
  Proof. intros; exact (run_unit_impl_equation_1 ch Hacc). Qed.

  (** The program given on the command line is run like an imported unit,
      with itself as the whole chain, nothing filed and no builtin binding;
      the result has the bindings the run ends with, which the printer
      reads.  The log holds its own evals; those of the units it loads are
      checked but not returned. *)
  Definition prog_impl (prg : Cst.prog) (Hacc : Acc load_step (prog_path prg :: nil)) :
    rres (builtins * gdeps * gunit * list eval_entry)%type :=
    match to_core prg with
    | None => rerr (run_error_msg "cannot elaborate the program")
    | Some u =>
        match run_unit_impl (prog_path prg :: nil) Hacc nil nil u (ginv_nil _) with
        | rok (exist _ r _, l) => rok (us_bt r, us_deps r, us_unit r, proj1_sig l)
        | rerr e => rerr e
        end
    end.

  (** ** Soundness

      By construction: a result carries its [post_*], whatever the loader and
      the accessibility proof. *)

  Lemma unit_equiv {ch Θ K u r} :
    ginv ch Θ K -> post_unit ch Θ K u r ->
    exists RbU ΘU, run_unit ch u (us_bt r) RbU ΘU (us_unit r) /\ ginv ch (us_deps r) (us_k r) /\
      gds_equiv ΘU (gds_restrict (us_dom r) (us_deps r)) /\ grows Θ (us_deps r) (us_dom r) /\
      ΘU ⊑ us_deps r /\ set_eq (us_dom r) (gds_dom ΘU).
  Proof.
    intros G Hp; destruct (Hp G) as [RbU ΘU Hu G' Hsub Hdom _ _ _ Hgr].
    exists RbU, ΘU; split; [ exact Hu | split; [ exact G' |] ].
    split; [ exact (equiv_restrict _ _ _ Hsub Hdom) |].
    split; [ exact Hgr | split; assumption ].
  Qed.

  (** A command runs filled: its literals, its eliminators and its member
      accesses through terms. *)
  Theorem run_cmd_impl_sound : forall ch L Θ K D B Ξ c H r ΘR RbR,
      linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR -> run_cmd_impl ch L Θ K D B Ξ c H = rok r ->
      exists c' ΘR' RbR', fill_cmd ΘR Ξ B c c' /\
        ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c' ⇝ ΘR' ⍮ cstate_stack (proj1_sig (fst r)) ⍮ cstate_bt (proj1_sig (fst r)) ⍮ RbR' /\
        linv ch (cstate_deps (proj1_sig (fst r))) (cstate_k (proj1_sig (fst r))) (cstate_dom (proj1_sig (fst r))) ΘR' (cstate_stack (proj1_sig (fst r))) /\ logs_ok (proj1_sig (snd r)).
  Proof.
    intros * Hli Hrb _; destruct r as [[r Hr] [l Hl]]; destruct (Hr _ _ Hli Hrb) as [ΘR' RbR' (c' & ? & ?) ? _ _ _]; cbn.
    exists c', ΘR', RbR'; tauto.
  Qed.

  Theorem run_cmds_impl_sound : forall ch L Θ K D B Ξ cs H r ΘR RbR,
      linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR -> run_cmds_impl ch L Θ K D B Ξ cs H = rok r ->
      exists ΘR' RbR', ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR' ⍮ cstate_stack (proj1_sig (fst r)) ⍮ cstate_bt (proj1_sig (fst r)) ⍮ RbR' /\
        linv ch (cstate_deps (proj1_sig (fst r))) (cstate_k (proj1_sig (fst r))) (cstate_dom (proj1_sig (fst r))) ΘR' (cstate_stack (proj1_sig (fst r))) /\ logs_ok (proj1_sig (snd r)).
  Proof.
    intros * Hli Hrb _; destruct r as [[r Hr] [l Hl]]; destruct (Hr _ _ Hli Hrb) as [ΘR' RbR' ? ? _ _ _]; cbn; eauto.
  Qed.

  Theorem run_unit_impl_sound : forall ch Hacc Θ K u H r,
      run_unit_impl ch Hacc Θ K u H = rok r ->
      exists RbU ΘU, run_unit ch u (us_bt (proj1_sig (fst r))) RbU ΘU (us_unit (proj1_sig (fst r))) /\
        ginv ch (us_deps (proj1_sig (fst r))) (us_k (proj1_sig (fst r))) /\
        gds_equiv ΘU (gds_restrict (us_dom (proj1_sig (fst r))) (us_deps (proj1_sig (fst r)))) /\
        logs_ok (proj1_sig (snd r)).
  Proof.
    intros * _; destruct r as [[r Hr] [l Hl]]; destruct (unit_equiv H Hr) as (RbU & ΘU & ? & ? & ? & _); cbn; eauto 7.
  Qed.

  (** ** Completeness

      By induction on the derivation, for every accessibility proof.  The
      executable loads only where the derivation does ([run_cmd_load]), and
      under the same chain.  For a unit filed already, the derivation loads
      it, but the executable shares it without recursing.  Both expand a
      command with an oracle meeting the specification, hence identically. *)

  Lemma def_complete : forall ch B RbR ΘR Ξ x b pv A oM B' RbR' ΘR' Ξ' Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_def x b pv A oM ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, defalias_step ch Θ K D B Ξ (cc_def x b pv A oM) H = rok r.
  Proof.
    intros * Hli Hr; inversion Hr; subst; simp defalias_step;
      (destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp defalias_step).
    - match goal with HM : _ ⍮ _ ⍮ _ ⊢ _ : A |- _ =>
          pose proof (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HM) as HM0 end.
      match goal with |- context [check_typ ?f ?a ?b ?c ?d ?e] => destruct (check_typ f a b c d e) as [[j HA'] | HA'] end;
        simp defalias_step; [| exfalso; exact (not_exp_of_not_typ _ _ _ _ _ HA' HM0) ].
      match goal with |- context [check_exp_typed ?z ?a ?b ?c ?d ?e ?f ?g] => destruct (check_exp_typed z a b c d e f g) as [HM' | HM'] end;
        simp defalias_step; [ eexists; reflexivity |].
      exfalso; exact (HM' HM0).
    - (* an axiom: its type is a type *)
      match goal with |- context [check_typ ?f ?a ?b ?c ?d ?e] => destruct (check_typ f a b c d e) as [[j HA'] | HA'] end;
        simp defalias_step; [ eexists; reflexivity |].
      exfalso; eapply HA'.
      match goal with HA : _ ⍮ _ ⍮ _ ⊢ A : _ |- _ => exact (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HA) end.
  Qed.

  Lemma builtin_complete : forall ch B RbR ΘR Ξ k E B' RbR' ΘR' Ξ' Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_builtin k E ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, builtin_step ch Θ K D B Ξ k E H = rok r.
  Proof.
    intros * Hli Hr; inversion Hr; subst.
    try rename Ξ' into Ξ; try rename ΘR' into ΘR.
    match goal with
    | Ht0 : modexp_as_term E = Some ?M0, HW0 : alg_type_infer _ ?W0 ?M0, Hn0 : nbe _ _ _ ?M0 _ (nf_indty ?p0 0 nil),
      Hl0 : ind_lookup _ _ ?p0 = Some ?Dd0, Hs0 : nat_shape ?Dd0 = Some _, Hsort0 : ind_sort ?Dd0 = nat_sort,
      Hb0 : bt_bind_nat _ ?p0 = Some _ |- _ =>
        rename Ht0 into Ht; rename HW0 into HW; rename Hn0 into Hn; rename Hl0 into Hl; rename Hs0 into Hs;
        rename Hsort0 into Hsort; rename Hb0 into Hb; rename p0 into p; rename Dd0 into Dd; rename M0 into M;
        rename W0 into W
    end.
    pose proof (linv_equiv Hli) as He; pose proof (linv_restrict_gctx Hli) as Hgr.
    pose proof (equiv_alg_infer _ _ _ _ _ _ He HW) as HW'.
    simp builtin_step.
    destruct (string_dec nat_kind nat_kind) as [Hk | Hk]; [| contradiction ]; simp builtin_step.
    destruct (opt_case (modexp_as_term E)) as [[M1 Ht1] | Ht1]; [| congruence ].
    assert (M1 = M) as -> by congruence.
    simp builtin_step.
    match goal with |- context [@type_infer ?g ?f ?G ?a ?b ?c] => destruct (@type_infer g f G a b c) as [[W1 HWs] | Hno] end;
      [| exfalso; exact (Hno _ HW') ].
    pose proof (functional_alg_type_infer (GC := gc_mk (gds_restrict D Θ) Ξ) Hgr (proj1 HWs) HW') as EW; subst W1.
    simp builtin_step.
    destruct (nf_is_universe_dec W) as [Hu' | Hu']; [| contradiction ]; simp builtin_step.
    match goal with |- context [@nbe_impl ?a ?b ?c ?d ?e ?f ?g] => destruct (@nbe_impl a b c d e f g) as [W2 Hn2] end.
    pose proof (functional_nbe _ _ _ _ _ Hn2 (equiv_nbe _ _ _ He _ _ _ _ Hn)) as ->.
    simp builtin_step.
    assert (Hl' : ind_lookup (gds_restrict D Θ) Ξ p = Some Dd)
      by (rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); exact Hl).
    destruct (opt_case (ind_lookup (gds_restrict D Θ) Ξ p)) as [[Dd' Hl''] | Hn'']; simp builtin_step; [| congruence ].
    assert (Dd' = Dd) as -> by congruence.
    destruct (inspect (nat_shape Dd)) as [[[z' s'] |] Es]; simp builtin_step; [| congruence ].
    destruct (inspect (is_nat_sort (ind_sort Dd))) as [[|] Ek]; simp builtin_step;
      [| rewrite Hsort in Ek; discriminate ].
    destruct (inspect (bt_bind_nat B p)) as [[B1 |] Eb]; simp builtin_step; [ eexists; reflexivity | congruence ].
  Qed.

  Lemma indalias_complete : forall ch B RbR ΘR Ξ x pv Δ E B' RbR' ΘR' Ξ' Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_ind_alias x pv Δ E ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, indalias_step ch Θ K D B Ξ x pv Δ E H = rok r.
  Proof.
    intros * Hli Hr; inversion Hr; subst.
    match goal with
    | HΔ0 : _ ⍮ _ ⍮ _ ⊢ˣ Δ ≈ Δ, HH0 : _ ⍮ _ ⍮ _ ⊢ᵐ E ≈ E, Ht0 : modexp_as_term E = Some ?M0,
      HW0 : alg_type_infer _ ?W0 ?M0, Hf0 : ind_former _ _ _ ?M0 ?W0 |- _ =>
        rename HΔ0 into HΔ; rename HH0 into HH; rename Ht0 into Ht; rename HW0 into HW; rename Hf0 into Hf;
        rename M0 into M; rename W0 into W
    end.
    pose proof (linv_equiv Hli) as He; pose proof (linv_restrict_gctx Hli) as Hgr.
    pose proof (equiv_modexp _ _ _ _ _ He Hgr HH) as HE0.
    pose proof (equiv_alg_infer _ _ _ _ _ _ He HW) as HW'.
    simp indalias_step.
    destruct (tele_ass_dec Δ) as [Htel' | Htel']; [| contradiction ]; simp indalias_step.
    match goal with |- context [check_ext ?f ?a ?b ?c ?d ?e] => destruct (check_ext f a b c d e) as [HΔ' | HΔ'] end;
      [| exfalso; apply HΔ'; exact (equiv_ext _ _ _ _ _ He Hgr HΔ) ].
    simp indalias_step.
    destruct (check_modexp _ _ _ _ _ (fst (me_unapps E))) as [Hh | Hh]; simp indalias_step;
      [| exfalso; exact (Hh (me_unapps_head_wf _ _ _ _ HE0)) ].
    destruct (check_modexp _ _ _ _ _ E) as [HE' | HE']; simp indalias_step; [| exfalso; exact (HE' HE0) ].
    destruct (opt_case (modexp_as_term E)) as [[M1 Ht1] | Ht1]; [| congruence ].
    assert (M1 = M) as -> by congruence.
    simp indalias_step.
    match goal with |- context [@type_infer ?g ?f ?G ?a ?b ?c] => destruct (@type_infer g f G a b c) as [[W1 HWs] | Hno] end;
      [| exfalso; exact (Hno _ HW') ].
    pose proof (functional_alg_type_infer (GC := gc_mk (gds_restrict D Θ) Ξ) Hgr (proj1 HWs) HW') as EW; subst W1.
    simp indalias_step.
    match goal with |- context [ind_former_dec ?a ?b ?c ?d ?e ?f ?g] => destruct (ind_former_dec a b c d e f g) as [Hf' | Hf'] end;
      [| exfalso; exact (Hf' (equiv_ind_former _ _ _ _ _ _ He Hf)) ].
    simp indalias_step.
    destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp indalias_step; eexists; reflexivity.
  Qed.

  Lemma recalias_complete : forall ch B RbR ΘR Ξ x pv Δ E B' RbR' ΘR' Ξ' Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_record_alias x pv Δ E ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, recalias_step ch Θ K D B Ξ x pv Δ E H = rok r.
  Proof.
    intros * Hli Hr; inversion Hr; subst.
    match goal with
    | HΔ0 : _ ⍮ _ ⍮ _ ⊢ˣ Δ ≈ Δ, HH0 : _ ⍮ _ ⍮ _ ⊢ᵐ E ≈ E, Ht0 : modexp_as_term E = Some ?M0,
      HW0 : alg_type_infer _ ?W0 ?M0, Hf0 : record_former _ _ _ ?M0 ?W0 |- _ =>
        rename HΔ0 into HΔ; rename HH0 into HH; rename Ht0 into Ht; rename HW0 into HW; rename Hf0 into Hf;
        rename M0 into M; rename W0 into W
    end.
    pose proof (linv_equiv Hli) as He; pose proof (linv_restrict_gctx Hli) as Hgr.
    pose proof (equiv_modexp _ _ _ _ _ He Hgr HH) as HE0.
    pose proof (equiv_alg_infer _ _ _ _ _ _ He HW) as HW'.
    simp recalias_step.
    destruct (tele_ass_dec Δ) as [Htel' | Htel']; [| contradiction ]; simp recalias_step.
    match goal with |- context [check_ext ?f ?a ?b ?c ?d ?e] => destruct (check_ext f a b c d e) as [HΔ' | HΔ'] end;
      [| exfalso; apply HΔ'; exact (equiv_ext _ _ _ _ _ He Hgr HΔ) ].
    simp recalias_step.
    destruct (check_modexp _ _ _ _ _ E) as [HE' | HE']; simp recalias_step; [| exfalso; exact (HE' HE0) ].
    destruct (opt_case (modexp_as_term E)) as [[M1 Ht1] | Ht1]; [| congruence ].
    assert (M1 = M) as -> by congruence.
    simp recalias_step.
    match goal with |- context [@type_infer ?g ?f ?G ?a ?b ?c] => destruct (@type_infer g f G a b c) as [[W1 HWs] | Hno] end;
      [| exfalso; exact (Hno _ HW') ].
    pose proof (functional_alg_type_infer (GC := gc_mk (gds_restrict D Θ) Ξ) Hgr (proj1 HWs) HW') as EW; subst W1.
    simp recalias_step.
    match goal with |- context [record_former_dec ?a ?b ?c ?d ?e ?f ?g] => destruct (record_former_dec a b c d e f g) as [Hf' | Hf'] end;
      [| exfalso; exact (Hf' (equiv_record_former _ _ _ _ _ _ He Hf)) ].
    simp recalias_step.
    destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp recalias_step; eexists; reflexivity.
  Qed.

  Lemma alias_complete : forall ch B RbR ΘR Ξ x pv Δ E B' RbR' ΘR' Ξ' Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_alias x pv Δ E ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, defalias_step ch Θ K D B Ξ (cc_alias x pv Δ E) H = rok r.
  Proof.
    intros * Hli Hr; inversion Hr as [| | | ? ? ? ? ? ? ? ? ? Htel HΔ HE Hfr | | | | | | | | | | | | |]; subst; simp defalias_step.
    destruct (tele_ass_dec Δ) as [Htel' | Htel']; [| contradiction ]; simp defalias_step.
    match goal with |- context [check_ext ?f ?a ?b ?c ?d ?e] => destruct (check_ext f a b c d e) as [HΔ' | HΔ'] end;
      [| exfalso; apply HΔ'; exact (equiv_ext _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HΔ) ].
    simp defalias_step.
    match goal with |- context [check_modexp ?f ?a ?b ?c ?d ?e] => destruct (check_modexp f a b c d e) as [HE' | HE'] end;
      [| exfalso; apply HE'; exact (equiv_modexp _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HE) ].
    simp defalias_step.
    destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp defalias_step.
    eexists; reflexivity.
  Qed.

  Lemma gens_complete : forall ΘR Ξ gs Ξ', gens_run ΘR Ξ gs Ξ' ->
      forall ch Θ K D B (Hx : exists ΘR0, linv ch Θ K D ΘR0 Ξ), linv ch Θ K D ΘR Ξ ->
      exists r, gens_impl ch Θ K D B Ξ gs Hx = rok r.
  Proof.
    induction 1 as [Ξ | Ξ d pv A M gs Ξ' HM Hfr Hg IH | Ξ d pv E gs Ξ' HE Hfr Hg IH | Ξ d pv A M E W gs Ξ' HW HM HE Hfr Hg IH];
      intros ch Θ K D B Hx Hli; cbn [gens_impl]; [ eexists; reflexivity | | |].
    - destruct (gs_fresh_dec d Ξ) as [Hfr' | Hfr']; [| contradiction ].
      match goal with |- context [check_exp ?z ?a ?b ?c ?d ?e ?f] => destruct (check_exp z a b c d e f) as [HM' | HM'] end;
        [| exfalso; apply HM'; exact (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HM) ].
      destruct (IH ch Θ K D B (gdef_pre Hx Hfr' HM') (proj2 (gdef_step (pv := pv) Hli Hfr' HM'))) as [[Ξ1 Hp] E].
      rewrite E; eexists; reflexivity.
    - destruct (gs_fresh_dec d Ξ) as [Hfr' | Hfr']; [| contradiction ].
      match goal with |- context [check_modexp ?f ?a ?b ?c ?d ?e] => destruct (check_modexp f a b c d e) as [HE' | HE'] end;
        [| exfalso; apply HE'; exact (equiv_modexp _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HE) ].
      destruct (IH ch Θ K D B (galias_pre Hx Hfr' HE') (proj2 (galias_step (pv := pv) Hli Hfr' HE'))) as [[Ξ1 Hp] E1].
      rewrite E1; eexists; reflexivity.
    - (* a definition with a module part: the type inferred is the one *)
      destruct (gs_fresh_dec d Ξ) as [Hfr' | Hfr']; [| contradiction ].
      pose proof (equiv_alg_infer _ _ _ _ _ _ (linv_equiv Hli) HW) as HW'.
      match goal with |- context [@type_infer ?g ?f ?G ?a ?b ?c] => destruct (@type_infer g f G a b c) as [[W1 HWs] | Hno] end;
        [| exfalso; exact (Hno _ HW') ].
      pose proof (functional_alg_type_infer (GC := gc_mk (gds_restrict D Θ) Ξ) (linv_restrict_gctx Hli) (proj1 HWs) HW') as EW;
        subst W1.
      match goal with |- context [check_modexp ?f ?a ?b ?c ?d ?e] => destruct (check_modexp f a b c d e) as [HE' | HE'] end;
        [| exfalso; apply HE'; exact (equiv_modexp _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HE) ].
      match goal with |- context [gens_impl ch Θ K D B ?Ξ1 gs ?Hx1] =>
        destruct (IH ch Θ K D B Hx1
                    (proj2 (proj2 (proj2 (gdm_step (pv := pv) Hli Hfr' (proj1 HWs)
                                             (alg_type_infer_sound (proj1 HWs) (pre_ctx Hx)) HE')))))
          as [[Ξ1' Hp] E1] end.
      rewrite E1; eexists; reflexivity.
  Qed.

  (** Literals keep the kind of a command, and a module's commands. *)
  (** The former of a command. *)
  Definition ccmd_head (c : ccmd) : nat :=
    match c with
    | cc_def _ _ _ _ _ => 0
    | cc_mod _ _ _ _ => 1
    | cc_alias _ _ _ _ => 2
    | cc_load _ => 3
    | cc_open _ _ => 4
    | cc_eval _ _ => 5
    | cc_ind _ _ => 6
    | cc_mdef _ _ _ _ => 9
    | cc_builtin _ _ => 7
    | cc_ind_alias _ _ _ _ => 8
    | cc_gen _ => 10
    | cc_record _ _ _ _ _ _ => 11
    | cc_record_alias _ _ _ _ => 12
    end.

  (** A generated command is taken as it is: its fill is itself, and its
      run is that of the command it wraps. *)
  Lemma gen_parts {ch ΘR Ξ B RbR c c' B' RbR' ΘR' Ξ'} :
    fill_cmd ΘR Ξ B (cc_gen c) c' ->
    ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c' ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
    ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR'.
  Proof.
    intros Hf Hr; rewrite (fill_cmd_generated _ _ _ _ _ Hf _ eq_refl) in Hr.
    exact (run_gen_inv _ _ _ _ _ _ _ _ _ _ _ _ _ Hr).
  Qed.

  (** A mutual definition the judgment runs, the executable runs. *)
  Lemma mdef_complete : forall ch B RbR ΘR Ξ b pv Δ fs B' RbR' ΘR' Ξ' Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_mdef b pv Δ fs ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, mdef_step ch Θ K D B Ξ b pv Δ fs H = rok r.
  Proof.
    intros * Hli Hr;
      inversion Hr as [| | | | | | | | ? ? ? ? ? ? ? ? f0 fs0 pq m0 Ps Dd Us ms Ξ1 Htel HΔ Hgp Hrun | | | | | | | |];
      subst.
    pose proof (linv_equiv Hli) as He; pose proof (linv_restrict_gctx Hli) as Hgr.
    simp mdef_step.
    destruct (tele_ass_dec Δ) as [Htel' | Htel']; [| contradiction ]; simp mdef_step.
    match goal with |- context [check_ctx ?f ?a ?b ?c ?d] => destruct (check_ctx f a b c d) as [HΔ' | HΔ'] end;
      [| exfalso; apply HΔ'; exact (equiv_ctx _ _ _ _ He Hgr HΔ) ].
    simp mdef_step.
    destruct (mdef_group_dec_complete _ _ (pre_gctx H) _ _ _ _ _ _ _ _ _
                (equiv_mdef_group _ _ _ _ _ _ _ _ _ _ _ _ He Hgr Hgp)) as [Hp E]; rewrite E.
    simp mdef_step.
    destruct (mdefs_dec _ _ _ _ _ _) as [Hr' | [e Hn]].
    - simp mdef_step; eexists; reflexivity.
    - exfalso; exact (Hn _ (equiv_mdefs_run _ _ _ _ _ _ _ He Hgr Hrun)).
  Qed.

  (** The fill keeps the kind of a command. *)
  Lemma fill_cmd_head : forall Θ0 Ξ B c c', fill_cmd Θ0 Ξ B c c' -> ccmd_head c' = ccmd_head c.
  Proof. intros * Hf; inversion Hf; reflexivity. Qed.

  (** A generated command is its own fill. *)
  Lemma fill_cmd_gen_eq : forall Θ0 Ξ B c c', fill_cmd Θ0 Ξ B c c' -> ccmd_head c = 10 -> c' = c.
  Proof. intros * Hf Hh; inversion Hf; subst; first [ reflexivity | cbn in Hh; discriminate ]. Qed.

  (** The fill the executable finds is the judgment's. *)
  Lemma fill_found {ch Θ K D ΘR Ξ B c c'} (Hg : ⊢ᵍ gds_restrict D Θ ⍮ Ξ) (FF : forall Θ0 Ξ0, FCtx Θ0 Ξ0) :
    linv ch Θ K D ΘR Ξ -> fill_cmd ΘR Ξ B c c' -> fill_cmd_fn (gds_restrict D Θ) Ξ B Hg FF c = fill_ok c'.
  Proof.
    intros Hli Hfc; apply fill_cmd_fn_complete.
    exact (equiv_fill_cmd _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) Hfc).
  Qed.

  (** *** The Recursor Module's Step

      A list of commands, each of which [rc] runs whenever the judgment
      does, [cmds_step] runs; so does [rec_step] the recursor module of a
      group, a module of definitions. *)

  Lemma cmds_step_complete (ch : list path) (rc : cmd_fun ch) (P : ccmd -> Prop) :
    (forall Θ K D B Ξ (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ) ΘR RbR c c' B' RbR' ΘR' Ξ',
        P c -> linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR -> fill_cmd ΘR Ξ B c c' ->
        ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c' ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
        exists r, rc Θ K D B Ξ c H = rok r) ->
    forall cs, Forall P cs -> forall Θ K D B Ξ (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ) ΘR RbR B' RbR' ΘR' Ξ',
      linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, cmds_step ch rc Θ K D B Ξ cs H = rok r.
  Proof.
    intros Hrc cs HP; induction HP as [| c cs Hc HP IH]; intros * Hli Hrb Hr; simp cmds_step; [ eexists; reflexivity |].
    inversion Hr as [| ? ? ? ? ? ? c3 ? B1 Rb1 ΘR1 Ξ1 ? ? ? ? Hac Hfc Hc2 Hcs]; subst.
    match goal with |- context [refs_check ?a ?b ?c ?d] => destruct (refs_check a b c d) as [[e Hq] | Hac'] end;
      simp cmds_step; [ exfalso; apply Hq; exact (equiv_acc _ _ _ _ (linv_equiv Hli) Hac) |].
    destruct (Hrc _ _ _ _ _ H _ _ _ _ _ _ _ _ Hc Hli Hrb Hfc Hc2) as [[[r1 Hp1] l1] E1]; rewrite E1; simp cmds_step.
    destruct (Hp1 _ _ Hli Hrb) as [ΘR1' RbR1' (c3' & Hfc' & Hr1) Hli1 Hrb1 _ _].
    pose proof (fill_cmd_functional _ _ _ (li_wf _ _ _ _ _ _ Hli) _ _ _ Hfc' Hfc) as ->.
    destruct (run_cmd_functional load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc2 Hr1) as (<- & HΞ1 & HB1 & HR1);
      subst Ξ1 B1 Rb1.
    destruct (IH _ _ _ _ _ (cons_pre H Hp1) _ _ _ _ _ _ Hli1 Hrb1 Hcs) as [[[r2 Hp2] l2] E2]; simp cmds_step in E2; rewrite E2.
    simp cmds_step; eexists; reflexivity.
  Qed.

  (** A generated module whose body [rb] runs whenever the judgment
      does. *)
  Lemma gen_mod_step_complete : forall ch (rb : cmds_fun ch) Θ K D B Ξ (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ) ΘR RbR
      x pv Δ cs B' RbR' ΘR' Ξ',
      (forall Θ1 K1 D1 B1 Ξ1 (H1 : exists ΘR0, linv ch Θ1 K1 D1 ΘR0 Ξ1) ΘR1 RbR1 B2 RbR2 ΘR2 Ξ2,
         linv ch Θ1 K1 D1 ΘR1 Ξ1 -> rb_ok K1 ΘR1 RbR1 ->
         ΘR1 ⍮ Ξ1 ⍮ B1 ⍮ RbR1 ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR2 ⍮ Ξ2 ⍮ B2 ⍮ RbR2 ->
         exists r, rb Θ1 K1 D1 B1 Ξ1 cs H1 = rok r) ->
      linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_mod x pv Δ cs ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, gen_mod_step ch rb Θ K D B Ξ x pv Δ cs H = rok r.
  Proof.
    intros * Hrb_ok Hli Hrb Hc.
    inversion Hc as [| | ? ? ? ? ? ? ? ? ? ? ? ? mp Kf U Htel HΔ Hfr Hr | | | | | | | | | | | | | | ]; subst.
    simp gen_mod_step.
    destruct (tele_ass_dec Δ) as [Htel' | Htel']; [| contradiction ]; simp gen_mod_step.
    match goal with |- context [check_ctx ?f ?a ?b ?c ?d] => destruct (check_ctx f a b c d) as [HΔ' | HΔ'] end;
      [| exfalso; apply HΔ'; exact (equiv_ctx _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HΔ) ].
    simp gen_mod_step.
    destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp gen_mod_step.
    destruct (linv_push Hli Htel' Hfr' HΔ') as [_ Hli'].
    destruct (Hrb_ok _ _ _ _ _ (mod_pre H Htel' Hfr' HΔ') _ _ _ _ _ _ Hli' Hrb Hr) as [[[r Hp] l] E]; rewrite E.
    simp gen_mod_step.
    destruct (Hp _ _ Hli' Hrb) as [ΘR2 RbR2 Hr2 _ _ _ _]; cbn beta in Hr2;
      destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr2) as [F HF].
    destruct (list_case (cstate_stack r)) as [[[[mp' Kf'] U'] [Ξ2 HΞ]] | HΞ]; simp gen_mod_step; [ eexists; reflexivity | congruence ].
  Qed.

  (** A generated definition the judgment runs, [gen_def_cmd] runs. *)
  Lemma gen_def_cmd_complete : forall ch Θ1 K1 D1 B1 Ξ1 (H1 : exists ΘR0, linv ch Θ1 K1 D1 ΘR0 Ξ1) ΘR1 RbR1 c c3
      B2 RbR2 ΘR2 Ξ2,
      cmd_is_def c -> linv ch Θ1 K1 D1 ΘR1 Ξ1 -> fill_cmd ΘR1 Ξ1 B1 c c3 ->
      ΘR1 ⍮ Ξ1 ⍮ B1 ⍮ RbR1 ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c3 ⇝ ΘR2 ⍮ Ξ2 ⍮ B2 ⍮ RbR2 ->
      exists r, gen_def_cmd ch Θ1 K1 D1 B1 Ξ1 c H1 = rok r.
  Proof.
    intros * Hd0 Hli2 Hfc2 Hc2.
    destruct c as [| | | | | | | | | | | | c]; try contradiction; destruct c as [x b pv A oM | | | | | | | | | | | |];
      try contradiction.
    pose proof (gen_parts Hfc2 Hc2) as Hc'.
    destruct oM as [M |];
      [| rewrite (fill_cmd_generated _ _ _ _ _ Hfc2 _ eq_refl) in Hc2; inversion Hc2 ].
    assert (E : exists r, defalias_step ch Θ1 K1 D1 B1 Ξ1 (cc_def x b pv A (Some M)) H1 = rok r)
      by (eapply def_complete; [ exact Hli2 | exact Hc' ]).
    destruct E as [[Ξd Hp] Er]; cbv beta iota delta [gen_def_cmd]; rewrite Er; eexists; reflexivity.
  Qed.

  (** Generated commands the judgment runs, [rec_step] runs. *)
  Lemma gen_step_complete : forall ch cs Θ K D B Ξ (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ) ΘR RbR B' RbR' ΘR' Ξ',
      Forall cmd_is_gen cs -> linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, rec_step ch Θ K D B Ξ cs H = rok r.
  Proof.
    intros * Hg Hli Hrb Hr; unfold rec_step.
    pose proof (gen_def_cmd_complete ch) as Hdef.
    eapply (cmds_step_complete ch (rec_cmd ch) cmd_is_gen); [| exact Hg | exact Hli | exact Hrb | exact Hr ].
    intros * Hgc Hli0 Hrb0 Hfc Hc.
    destruct c as [| | | | | | | | | | | | c]; try contradiction; destruct c as [x b pv A oM | x pv Δ0 cs0 | | | | | | | | | | |];
      try contradiction.
    - (* a generated definition *)
      cbv beta iota delta [rec_cmd]; eapply Hdef; [ exact I | exact Hli0 | exact Hfc | exact Hc ].
    - (* a generated module of generated definitions *)
      pose proof (gen_parts Hfc Hc) as Hc'.
      cbv beta iota delta [rec_cmd]; unfold gen_wrap.
      match goal with |- context [gen_mod_step ?a ?b ?T ?K ?D ?B ?X ?y ?p ?d ?cc ?HH] =>
        assert (E : exists r, gen_mod_step a b T K D B X y p d cc HH = rok r) end.
      { eapply gen_mod_step_complete; [| exact Hli0 | exact Hrb0 | exact Hc' ].
        intros * Hli1 Hrb1 Hr1.
        eapply (cmds_step_complete ch (gen_def_cmd ch) cmd_is_def); [| exact Hgc | exact Hli1 | exact Hrb1 | exact Hr1 ].
        intros * Hd0 Hli2 _ Hfc2 Hc2; eapply Hdef; [ exact Hd0 | exact Hli2 | exact Hfc2 | exact Hc2 ]. }
      destruct E as [[[r Hp] lg] Er]; rewrite Er; eexists; reflexivity.
  Qed.

  (** The declared members of a group the judgment runs, [members_step]
      runs. *)
  Lemma members_step_complete : forall ch xs Θ K D B Ξ pv R pq Dd k (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ) Hp HE
      ΘR RbR B' RbR' ΘR' Ξ',
      linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      run_ind_members load_path read to_core ch B RbR ΘR Ξ pv R pq Dd k xs B' RbR' ΘR' Ξ' ->
      exists r, members_step ch Θ K D B Ξ pv R pq Dd k xs H Hp HE = rok r.
  Proof.
    intros ch; induction xs as [| x xs IH]; intros * Hli Hrb Hr; simp members_step; [ eexists; reflexivity |].
    inversion Hr as [| ? ? ? ? ? ? ? ? ? ? ? ? M B1 Rb1 Θ1 mp Kf U B2 Rb2 Θ2 Ξ2 HM Hfr HE0 Hr1 Hrest]; subst.
    destruct (member_case Dd k) as [[M' HM'] | HM']; [| congruence ].
    assert (M' = M) as -> by congruence; simp members_step.
    rewrite (equiv_ind_mod_cmds _ _ _ _ _ _ _ _ (linv_equiv Hli)) in Hr1.
    pose proof (linv_push_ind Hli Hfr (mems_pre_uparams _ _ _ _ _ _ Hp) HE0) as Hli'.
    match goal with |- context [rec_step ?a ?b ?c ?d ?e ?f ?g ?h] =>
      destruct (gen_step_complete _ _ _ _ _ _ _ h _ _ _ _ _ _ (ind_mod_cmds_gen _ _ _ _ _ _ _) Hli' Hrb Hr1)
        as [[[r1 Hp1] l1] E1]; rewrite E1
    end.
    simp members_step.
    destruct (Hp1 _ _ Hli' Hrb) as [ΘR1 RbR1 Hr1' _ _ _ _]; cbn beta in Hr1'.
    destruct (proj1 (proj2 (@run_functional load_path read to_core)) _ _ _ _ _ _ _ _ _ _ Hr1 _ _ _ _ _ Hr1')
      as (<- & HΞ1 & HB1 & <-).
    destruct (list_case (cstate_stack r1)) as [[[[mp' Kf'] U'] [Ξ2' HΞ]] | HΞ]; [| congruence ].
    rewrite HΞ in HΞ1; injection HΞ1 as <- <- <- <-.
    simp members_step.
    destruct (member_ok (M := M) Hfr (mems_pre_uparams _ _ _ _ _ _ Hp) HE Hp1 HΞ _ _ Hli Hrb) as [ΘR2 RbR2 Hr2 Hli2 Hrb2 _ _];
      cbn beta in Hr2; cbn [cstate_deps cstate_k cstate_dom cstate_stack] in Hli2.
    rewrite <- (equiv_ind_mod_cmds _ _ _ _ _ _ _ _ (linv_equiv Hli)) in Hr1.
    destruct (proj1 (proj2 (@run_functional load_path read to_core)) _ _ _ _ _ _ _ _ _ _ Hr1 _ _ _ _ _ Hr2)
      as (<- & _ & _ & <-).
    rewrite HB1 in Hrest.
    match goal with |- context [members_step ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k' ?l ?m ?n ?o] =>
      destruct (IH _ _ _ _ _ _ _ _ _ _ m n o _ _ _ _ _ _ Hli2 Hrb2 Hrest) as [[[r2 Hp2] l2] E2]; rewrite E2
    end.
    simp members_step; eexists; reflexivity.
  Qed.

  (** The recursor module of a group the judgment runs, [rec_step] runs. *)
  Lemma rec_step_complete : forall ch Θ0 Ξ0 R pq Dd Θ K D B Ξ (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ) ΘR RbR B' RbR' ΘR' Ξ',
      linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ rec_cmds Θ0 Ξ0 R pq Dd ⇝* ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, rec_step ch Θ K D B Ξ (rec_cmds Θ0 Ξ0 R pq Dd) H = rok r.
  Proof. intros * Hli Hrb Hr; exact (gen_step_complete _ _ _ _ _ _ _ H _ _ _ _ _ _ (rec_cmds_gen _ _ _ _ _) Hli Hrb Hr). Qed.

  (** A group declaration the judgment runs, the executable runs. *)
  Lemma ind_complete : forall ch B RbR ΘR Ξ pv R B' RbR' ΘR' Ξ' Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_ind pv R ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, ind_step ch Θ K D B Ξ pv R H = rok r.
  Proof.
    intros * Hli Hrb Hr;
      inversion Hr as [| | | | | | | ? ? ? ? ? ? ? Mr0 Mrs csD Vs Ss csV Nvs Dd B1 Rb1 Θ1 Ξ1 ? ? ? ? HR Hsort Hcls Hsibs Hvcls Hvnps Hbfs Hfil Hnil Hgn Hent Hrc | | | | | | | | |];
      subst.
    pose proof (linv_equiv Hli) as He; pose proof (linv_restrict_gctx Hli) as Hgr.
    pose proof (equiv_rm_cls _ _ _ He Hgr _ _ _ Hcls) as HclsR.
    pose proof (equiv_views_ok _ _ _ _ _ _ _ _ _ He Hgr (mk_views_ok _ _ _ _ _ _ _ _ Hsibs Hvcls Hvnps Hbfs)) as HvR.
    pose proof (equiv_ind_nil_at _ _ _ He Hgr _ _ _ Hnil) as HnilR.
    destruct (ind_members_run_fresh load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hent) as [Hnd Hfr].
    simp ind_step.
    destruct (list_case (raw_decl_members R)) as [[Mr0' [Mrs' HR']] | HR']; [| congruence ].
    pose proof (eq_trans (eq_sym HR) HR') as ER; injection ER as <- <-; simp ind_step.
    destruct (Forall_dec _ _ Mrs) as [Hsort' | Hsort']; [| contradiction ]; simp ind_step.
    destruct (rms_cls_dec _ _ _ R (raw_decl_members R)) as [[csD' Hcls'] | [[[[x c] y] w] Hn]];
      [| exfalso; exact (Hn _ HclsR) ].
    assert (csD' = csD) as ->
      by (eapply Forall2_functional; [| exact Hcls' | exact HclsR ];
          intros; unfold rm_cls in *; eapply cls_cons_in_functional; eassumption).
    simp ind_step.
    destruct (views_search_complete _ _ (pre_gctx H) _ _ _ _ _ _ HvR) as [v Ev]; rewrite Ev.
    destruct v as (Vs' & Ss' & csV' & Nvs' & Hv'); simp ind_step.
    destruct (views_ok_functional _ _ _ _ _ _ _ _ _ _ _ _ Hv' HvR) as (-> & -> & -> & ->).
    assert (HfilR : rd_filed (gds_restrict D Θ) Ξ R Vs Ss csD csV Nvs = Some Dd)
      by (rewrite <- (equiv_rd_filed _ _ _ He); exact Hfil).
    destruct (opt_case (rd_filed _ _ _ _ _ _ _ _)) as [[Dd' Hfil'] | Hfil']; [| congruence ].
    assert (Dd' = Dd) as -> by congruence; simp ind_step.
    destruct (nodup_dec _) as [Hnd' | Hnd']; [| contradiction ]; simp ind_step.
    destruct (Forall_dec _ _ (raw_decl_members R)) as [Hfr' | Hfr'].
    2:{ exfalso; apply Hfr'; rewrite List.Forall_map in Hfr; exact Hfr. }
    simp ind_step.
    destruct (ind_nil_at_dec _ _ _ _ _ _) as [Hnil' | Hnil']; [| contradiction ]; simp ind_step.
    destruct (inspect (gen_names_blame Ξ R Dd (raw_member_name Mr0))) as [[e |] Egn];
      [ exfalso; rewrite (gen_names_blame_free Hgn) in Egn; discriminate |]; simp ind_step.
    (* the members, then the recursor module from where they end *)
    match goal with |- context [members_step ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k' ?l ?m ?n ?o] =>
      destruct (members_step_complete _ _ _ _ _ _ _ _ _ _ _ _ m n o _ _ _ _ _ _ Hli Hrb Hent) as [[[r1 Hp1] l1] E1]; rewrite E1
    end.
    simp ind_step.
    destruct (Hp1 _ _ Hli Hrb) as [ΘR1 RbR1 Hr1 Hli1 Hrb1 _ _]; cbn beta in Hr1.
    destruct (proj2 (proj2 (proj2 (@run_functional load_path read to_core))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hent _ _ _ _ _ Hr1)
      as (-> & -> & -> & ->).
    rewrite (equiv_rec_cmds _ _ _ _ _ _ (linv_equiv Hli1)) in Hrc.
    match goal with |- context [rec_step ?a ?b ?c ?d ?e ?f ?g ?h] =>
      destruct (rec_step_complete _ _ _ _ _ _ _ _ _ _ _ h _ _ _ _ _ _ Hli1 Hrb1 Hrc) as [[[r2 Hp2] l2] E2]; rewrite E2
    end.
    simp ind_step; eexists; reflexivity.
  Qed.

  Lemma fill_simple_complete {ch L Θ K D B ΘR Ξ c c'} (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ) :
    linv ch Θ K D ΘR Ξ -> fill_cmd ΘR Ξ B c c' ->
    (exists r, simple_step ch L Θ K D B Ξ c' H = rok r) ->
    exists r, fill_simple ch L Θ K D B Ξ c H = rok r.
  Proof.
    intros Hli Hfc [r Er]; unfold fill_simple.
    pose proof (fill_found (pre_gctx H) (fctx_cmd B) Hli Hfc) as Ea.
    destruct (inspect (fill_cmd_fn _ _ _ _ _ c)) as [[c3' | e] Ea']; [ assert (c3' = c') as -> by congruence | exfalso; congruence ].
    cbv beta iota.
    rewrite Er; destruct r as [[r Hp] l]; eexists; reflexivity.
  Qed.

  (** Every command but a module, a record and a generated command runs
      by [simple_step] once filled. *)
  Lemma nonmod_complete {ch L Θ K D B ΘR Ξ c c'} (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ) :
    ccmd_head c' <> 1 -> ccmd_head c' <> 10 -> ccmd_head c' <> 11 -> linv ch Θ K D ΘR Ξ -> fill_cmd ΘR Ξ B c c' ->
    (exists r, simple_step ch L Θ K D B Ξ c' H = rok r) ->
    exists r, run_cmd_impl ch L Θ K D B Ξ c H = rok r.
  Proof.
    intros Hc Hg Hrc Hli Hfc Hs.
    rewrite (fill_cmd_head _ _ _ _ _ Hfc) in Hc, Hg, Hrc.
    destruct c; try (exfalso; first [ exact (Hc eq_refl) | exact (Hg eq_refl) | exact (Hrc eq_refl) ]); simp run_cmd_impl;
      eapply fill_simple_complete; eassumption.
  Qed.

  (** A record's field definitions are generated definitions. *)
  Lemma record_field_cmds_def : forall R, Forall cmd_is_def (record_field_cmds R).
  Proof.
    intros R; unfold record_field_cmds; generalize 0; induction (record_fields R) as [| [f T] fs IH]; intros k;
      cbn; constructor; [ exact I | apply IH ].
  Qed.

  Theorem run_impl_complete :
    (forall ch B RbR ΘR Ξ c' B' RbR' ΘR' Ξ', ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c' ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
       forall Hacc Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ), linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
       forall c, fill_cmd ΘR Ξ B c c' ->
         exists r, run_cmd_impl ch (loader_of ch Hacc) Θ K D B Ξ c H = rok r) /\
    (forall ch B RbR ΘR Ξ cs B' RbR' ΘR' Ξ', ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
       forall Hacc Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ), linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
         exists r, run_cmds_impl ch (loader_of ch Hacc) Θ K D B Ξ cs H = rok r) /\
    (forall ch u B' RbU ΘU U, run_unit ch u B' RbU ΘU U ->
       forall Hacc Θ K (H : ginv ch Θ K), exists r, run_unit_impl ch Hacc Θ K u H = rok r) /\
    (** the declared members of a group are run by [ind_complete], from
        the whole declaration *)
    (forall ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ',
       run_ind_members load_path read to_core ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ' -> True).
  Proof.
    apply run_mut_dind.
    - (* a definition *)
      intros ch B Rb ΘR Ξ x b pv A M HM Hfr Hacc Θ K D H Hli Hrb c Hfc.
      refine (nonmod_complete H _ _ _ Hli Hfc _); [ cbn; discriminate | cbn; discriminate | cbn; discriminate |]; simp simple_step.
      destruct (def_complete ch B Rb ΘR Ξ x b pv A (Some M) _ _ _ _ Θ K D H Hli ltac:(constructor; eassumption)) as [[Ξ1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* an axiom *)
      intros ch B Rb ΘR Ξ x b pv A i HA Hfr Hacc Θ K D H Hli Hrb c Hfc.
      refine (nonmod_complete H _ _ _ Hli Hfc _); [ cbn; discriminate | cbn; discriminate | cbn; discriminate |]; simp simple_step.
      destruct (def_complete ch B Rb ΘR Ξ x b pv A None _ _ _ _ Θ K D H Hli ltac:(econstructor; eassumption)) as [[Ξ1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* a module *)
      intros ch B Rb B' Rb' ΘR Ξ x pv Δ cs ΘR' mp Kf U Htel HΔ Hfr Hr IH Hacc Θ K D H Hli Hrb c Hfc.
      destruct (fill_cmd_to_mod _ _ _ _ _ _ _ _ Hfc) as (Δe & -> & Hfp).
      simp run_cmd_impl.
      pose proof (fill_params_fn_complete _ _ _ (pre_gctx H) (fctx_cmd B) _ _
                    (equiv_fill_params _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) Hfp)) as Ea.
      destruct (inspect (fill_params_fn _ _ _ _ _ Δe)) as [[Δ' | e] Ea'];
        [ assert (Δ' = Δ) as -> by congruence | exfalso; congruence ].
      simp run_cmd_impl.
      destruct (tele_ass_dec Δ) as [Htel' | Htel']; [| contradiction ]; simp run_cmd_impl.
      match goal with |- context [check_ctx ?f ?a ?b ?c ?d] => destruct (check_ctx f a b c d) as [HΔ' | HΔ'] end;
        [| exfalso; apply HΔ'; exact (equiv_ctx _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HΔ) ].
      simp run_cmd_impl.
      destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp run_cmd_impl.
      destruct (linv_push Hli Htel' Hfr' HΔ') as [_ Hli'].
      destruct (IH Hacc Θ K D (mod_pre H Htel' Hfr' HΔ') Hli' Hrb) as [[[r Hp] l] E]; unfold run_cmds_impl in E; rewrite E.
      simp run_cmd_impl.
      destruct (Hp _ _ Hli' Hrb) as [ΘR2 RbR2 Hr2 _ _ _ _]; cbn beta in Hr2; destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr2) as [F HF].
      destruct (list_case (cstate_stack r)) as [[[[mp' Kf'] U'] [Ξ2 HΞ]] | HΞ]; simp run_cmd_impl; [ eexists; reflexivity | congruence ].
    - (* an alias *)
      intros ch B Rb ΘR Ξ x pv Δ E Htel HΔ HE Hfr Hacc Θ K D H Hli Hrb c Hfc.
      refine (nonmod_complete H _ _ _ Hli Hfc _); [ cbn; discriminate | cbn; discriminate | cbn; discriminate |]; simp simple_step.
      destruct (alias_complete ch B Rb ΘR Ξ x pv Δ E _ _ _ _ Θ K D H Hli ltac:(constructor; assumption)) as [[Ξ1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* a load of a unit the judgment has *)
      intros ch B Rb B' ΘR Ξ fp U BU HU HBU Hm Hacc Θ K D H Hli Hrb c Hfc.
      refine (nonmod_complete H _ _ _ Hli Hfc _); [ cbn; discriminate | cbn; discriminate | cbn; discriminate |]; simp simple_step.
      pose proof (li_sub _ _ _ _ _ _ Hli _ _ HU) as HUg.
      assert (Hin : In fp D) by (apply (li_dom _ _ _ _ _ _ Hli), gds_dom_lookup; rewrite HU; discriminate).
      destruct (opt_case (gds_lookup Θ fp)) as [[U' HU'] | HU']; [| congruence ].
      assert (U' = U) as -> by congruence; simp simple_step.
      pose proof (proj2 Hrb _ _ HBU) as HB.
      destruct (opt_case (kbt K fp)) as [[BU' HB'] | HB']; [| congruence ].
      assert (BU' = BU) as -> by congruence; simp simple_step.
      destruct (inspect (bt_merge B BU)) as [[B1 |] Em]; [| congruence ]; simp simple_step.
      destruct (in_dec path_eq_dec fp D) as [Hin' | Hin']; [| contradiction ]; simp simple_step.
      eexists; reflexivity.
    - (* a load: shared if some other unit filed it, run otherwise *)
      intros ch B Rb B' ΘR Ξ fp src prg u BU RbU ΘU U Hn Hnin Hld Hrd Hp Ht Hu IH Hm Hacc Θ K D H Hli Hrb c Hfc.
      refine (nonmod_complete H _ _ _ Hli Hfc _); [ cbn; discriminate | cbn; discriminate | cbn; discriminate |]; simp simple_step.
      assert (HnD : ~ In fp D)
        by (intros Hin; apply (li_dom _ _ _ _ _ _ Hli), gds_dom_lookup in Hin; contradiction).
      destruct (opt_case (gds_lookup Θ fp)) as [[U' HU'] | Hng]; simp simple_step.
      + (* filed by another unit: its record is the one this run ends with *)
        destruct (ginv_entry (li_g _ _ _ _ _ _ Hli) _ _ HU')
          as [Dfp BU' src' prg' u' ch0 RbU' ΘU' HK HB _ Hl' Hr' _ Ht' Hu' _ _ _].
        assert (src' = src) as -> by congruence; assert (prg' = prg) as -> by congruence; assert (u' = u) as -> by congruence.
        destruct (run_unit_functional load_path read to_core (fp :: ch0) (fp :: ch) _ _ _ _ _ _ _ _ _ eq_refl Hu' Hu)
          as (_ & _ & <- & _).
        destruct (opt_case (kbt K fp)) as [[BU1 HB1] | HB1]; [| congruence ].
        assert (BU1 = BU') as -> by congruence; simp simple_step.
        destruct (inspect (bt_merge B BU')) as [[B1 |] Em]; [| congruence ]; simp simple_step.
        destruct (in_dec path_eq_dec fp D) as [Hin | Hin]; [ contradiction |]; simp simple_step.
        destruct (opt_case (kfind K fp)) as [[Dfp' HK'] | HK']; [| congruence ]; simp simple_step.
        eexists; reflexivity.
      + destruct (in_dec path_eq_dec fp ch) as [Hin | Hin]; [ contradiction |]; simp simple_step.
        destruct (opt_case (load_path fp)) as [[src' Hl'] | Hl']; [| congruence ].
        assert (src' = src) as -> by congruence; simp simple_step.
        destruct (opt_case (read src)) as [[prg' Hr'] | Hr']; [| congruence ].
        assert (prg' = prg) as -> by congruence; simp simple_step.
        destruct (path_eq_dec (prog_path prg) fp) as [Hp' | Hp']; [| contradiction ]; simp simple_step.
        destruct (opt_case (to_core prg)) as [[u' Ht'] | Ht']; [| congruence ].
        assert (u' = u) as -> by congruence; simp simple_step.
        unfold loader_of.
        match goal with |- context [run_unit_impl (fp :: ch) ?a Θ K u ?b] =>
          destruct (IH a Θ K b) as [[[r Hpost] l] E']; rewrite E'; simp simple_step;
          destruct (Hpost b) as [RbU' ΘU' Hu' _ _ _ _ _ _ _]
        end.
        destruct (run_unit_functional load_path read to_core (fp :: ch) (fp :: ch) _ _ _ _ _ _ _ _ _ eq_refl Hu' Hu)
          as (_ & _ & HB & _).
        destruct (inspect (bt_merge B (us_bt r))) as [[B1 |] Em];
          [| exfalso; pose proof Em as Em'; rewrite HB in Em'; congruence ]; simp simple_step.
        eexists; reflexivity.
    - (* an import: its target, then its generated commands *)
      intros ch B Rb ΘR Ξ E its gs Ξ' HE Hgen Hgs Hacc Θ K D H Hli Hrb c Hfc.
      refine (nonmod_complete H _ _ _ Hli Hfc _); [ cbn; discriminate | cbn; discriminate | cbn; discriminate |]; simp simple_step.
      match goal with |- context [check_modexp ?f ?a ?b ?c ?d ?e] => destruct (check_modexp f a b c d e) as [HE' | HE'] end;
        [| exfalso; apply HE'; exact (equiv_modexp _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HE) ].
      simp simple_step.
      pose proof (open_gens_equiv _ _ _ _ _ _ _ (linv_equiv Hli) Hgen) as Hgen'.
      apply (import_gen_spec _ _ (pre_gctx H) _ _ _ HE') in Hgen' as Eg.
      destruct (inspect _) as [[gs1 | e] Eg']; [ assert (gs1 = gs) as -> by congruence | exfalso; congruence ].
      simp simple_step.
      destruct (gens_complete _ _ _ _ Hgs _ _ _ _ B H Hli) as [[Ξ1 Hp1] E1]; rewrite E1; simp simple_step.
      eexists; reflexivity.
    - (* a group declaration *)
      intros ch B Rb ΘR Ξ pv R Mr0 Mrs csD Vs Ss csV Nvs Dd B1 Rb1 ΘR1 Ξ1 B' Rb' ΘR' Ξ'' HR Hsort Hcls Hsibs Hvcls Hvnps Hbfs
        Hfil Hnil Hgn Hent _ Hrc _ Hacc Θ K D H Hli Hrb c Hfc.
      refine (nonmod_complete H _ _ _ Hli Hfc _); [ cbn; discriminate | cbn; discriminate | cbn; discriminate |]; simp simple_step.
      destruct (ind_complete ch B Rb ΘR Ξ pv R _ _ _ _ Θ K D H Hli Hrb ltac:(econstructor; eassumption)) as [[[r Hp] l] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* a mutual definition *)
      intros ch B Rb ΘR Ξ b pv Δ f0 fs pq m0 Ps Dd Us ms Ξ' Htel HΔ Hgp Hrun
        Hacc Θ K D H Hli Hrb c Hfc.
      refine (nonmod_complete H _ _ _ Hli Hfc _); [ cbn; discriminate | cbn; discriminate | cbn; discriminate |]; simp simple_step.
      destruct (mdef_complete ch B Rb ΘR Ξ b pv Δ (f0 :: fs) _ _ _ _ Θ K D H Hli ltac:(econstructor; eassumption))
        as [[Ξ1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* a builtin binding *)
      intros ch B Rb B' ΘR Ξ E M W p Dd z s Ht HW HM Hu Hn Hld Hs Hsort Hb Hacc Θ K D H Hli Hrb c Hfc.
      refine (nonmod_complete H _ _ _ Hli Hfc _); [ cbn; discriminate | cbn; discriminate | cbn; discriminate |]; simp simple_step.
      destruct (builtin_complete ch B Rb ΘR Ξ nat_kind E _ _ _ _ Θ K D H Hli ltac:(econstructor; eassumption)) as [[B1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* an inductive alias *)
      intros ch B Rb ΘR Ξ x pv Δ E M W Htel HΔ HEw Ht HW HM Hf Hfr Hacc Θ K D H Hli Hrb c Hfc.
      refine (nonmod_complete H _ _ _ Hli Hfc _); [ cbn; discriminate | cbn; discriminate | cbn; discriminate |]; simp simple_step.
      destruct (indalias_complete ch B Rb ΘR Ξ x pv Δ E _ _ _ _ Θ K D H Hli ltac:(econstructor; eassumption)) as [[Ξ1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* a record alias *)
      intros ch B Rb ΘR Ξ x pv Δ E M W Htel HΔ HEw Ht HW HM Hf Hfr Hacc Θ K D H Hli Hrb c Hfc.
      refine (nonmod_complete H _ _ _ Hli Hfc _); [ cbn; discriminate | cbn; discriminate | cbn; discriminate |]; simp simple_step.
      destruct (recalias_complete ch B Rb ΘR Ξ x pv Δ E _ _ _ _ Θ K D H Hli ltac:(econstructor; eassumption)) as [[Ξ1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* a record: its declaration, its field definitions, then its with-area *)
      intros ch B Rb ΘR Ξ x pv Δ Srt fs cs B1 Rb1 ΘR1 Ξ1 B' Rb' ΘR' mp Kf U Hfr HE Hr1 _ Hr2 IH2 Hacc Θ K D H Hli Hrb c Hfc.
      destruct (fill_cmd_to_record _ _ _ _ _ _ _ _ _ _ Hfc) as (Δe & Se & fse & ->).
      simp run_cmd_impl.
      pose proof (fill_record_fn_complete _ _ _ (pre_gctx H) (fctx_cmd B) _ _ _ _ _ _ _ _ _
                    (equiv_fill_cmd _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) Hfc)) as Ea.
      destruct (inspect (fill_record_fn _ _ _ _ _ x pv Δe Se fse cs)) as [[[[Δ' S'] fs'] | e] Ea'];
        [ assert (Ex : (Δ', S', fs') = (Δ, Srt, fs)) by congruence; injection Ex as -> -> -> | exfalso; congruence ].
      simp run_cmd_impl.
      assert (HtR : record_typed (gds_restrict D Θ) Ξ (record_at Ξ Δ Srt fs)).
      { refine (record_typed_emb _ _ _ _ _ _ (proj1 wf_record_typed_all _ _ _ _ HE _ _ _ _ eq_refl)).
        constructor; [ exact (linv_restrict_gctx Hli) | apply gc_sub_deps; exact (proj1 (linv_equiv Hli)) ]. }
      destruct (record_typed_dec _ _ _ _) as [Ht | [e Hn]]; [| exfalso; exact (Hn HtR) ]; simp run_cmd_impl.
      destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp run_cmd_impl.
      destruct (inspect (field_clash fs cs)) as [[fc |] Ecl].
      { (* a with-area name that is a field's cannot run: the field took it *)
        exfalso; destruct (field_clash_some _ _ _ Ecl) as (c & Hin & Hn & Hcl).
        exact (run_cmds_taken load_path read to_core _ _ _ _ _ _ _ _ _ _ Hr2 c fc Hin Hn
                 (record_field_cmds_taken load_path read to_core _ _ _ _ _ (record_at Ξ Δ Srt fs) _ _ _ _ _ Hr1 Hcl)). }
      simp run_cmd_impl.
      pose proof (linv_push_record Hli Hfr' (record_entry_at (pv := false) Ht _ Hli)) as Hli'.
      destruct (cmds_step_complete ch (gen_def_cmd ch) cmd_is_def
                  ltac:(intros * Hd0 Hli2 _ Hfc2 Hc2;
                        eapply gen_def_cmd_complete; [ exact Hd0 | exact Hli2 | exact Hfc2 | exact Hc2 ])
                  _ (record_field_cmds_def _) _ _ _ _ _ (record_pre H Hfr' Ht) _ _ _ _ _ _ Hli' Hrb Hr1)
        as [[[r1 Hp1] l1] E1]; rewrite E1.
      simp run_cmd_impl.
      destruct (Hp1 _ _ Hli' Hrb) as [ΘR1' RbR1' Hr1' Hli1 Hrb1 _ _]; cbn beta in Hr1'.
      destruct (run_cmds_functional load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr1 Hr1') as (<- & HΞ1 & HB1 & HR1);
        subst Ξ1 B1 Rb1.
      destruct (IH2 Hacc _ _ _ (cmds_post_pre (record_pre H Hfr' Ht) Hp1) Hli1 Hrb1) as [[[r2 Hp2] l2] E2].
      unfold run_cmds_impl in E2; rewrite E2.
      simp run_cmd_impl.
      destruct (Hp2 _ _ Hli1 Hrb1) as [ΘR2 RbR2 Hr2' _ _ _ _]; cbn beta in Hr2'.
      destruct (run_cmds_functional load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr2 Hr2') as (_ & HΞ2 & _ & _).
      destruct (list_case (cstate_stack r2)) as [[[[mp' Kf'] U'] [Ξ2 HΞ]] | HΞ]; simp run_cmd_impl; [ eexists; reflexivity | congruence ].
    - (* an ascribed eval *)
      intros ch B Rb ΘR Ξ M A HM Hacc Θ K D H Hli Hrb c Hfc.
      refine (nonmod_complete H _ _ _ Hli Hfc _); [ cbn; discriminate | cbn; discriminate | cbn; discriminate |]; simp simple_step.
      pose proof (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HM) as HM0.
      match goal with |- context [check_typ ?f ?a ?b ?c ?d ?e] => destruct (check_typ f a b c d e) as [[j HA'] | HA'] end;
        simp simple_step; [| exfalso; exact (not_exp_of_not_typ _ _ _ _ _ HA' HM0) ].
      match goal with |- context [check_exp_typed ?z ?a ?b ?c ?d ?e ?f ?g] => destruct (check_exp_typed z a b c d e f g) as [HM' | HM'] end;
        simp simple_step.
      { eexists; reflexivity. }
      exfalso; exact (HM' HM0).
    - (* an inferred eval: failure of inference contradicts its completeness *)
      intros ch B Rb ΘR Ξ M A HM Hacc Θ K D H Hli Hrb c Hfc.
      refine (nonmod_complete H _ _ _ Hli Hfc _); [ cbn; discriminate | cbn; discriminate | cbn; discriminate |]; simp simple_step.
      match goal with |- context [@type_infer_at ?g ?f ?G ?a ?b ?c] => destruct (@type_infer_at g f G a b c) as [[A' HA'] | Hno] end;
        simp simple_step.
      { eexists; reflexivity. }
      exfalso.
      pose proof (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HM) as HM'.
      destruct (@alg_type_infer_complete (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) A M (user_exp_all M) HM') as (B0 & HB & _).
      exact (Hno B0 HB).
    - (* a generated definition: as generated, a definition *)
      intros ch B Rb ΘR Ξ x b pv A M HM Hfr Hacc Θ K D H Hli Hrb c Hfc.
      assert (E2 : cc_gen (cc_def x b pv A (Some M)) = c)
        by (apply (fill_cmd_gen_eq _ _ _ _ _ Hfc); rewrite <- (fill_cmd_head _ _ _ _ _ Hfc); reflexivity).
      subst c.
      assert (E : exists r, simple_step ch (loader_of ch Hacc) Θ K D B Ξ (cc_def x b pv A (Some M)) H = rok r).
      { simp simple_step.
        destruct (def_complete ch B Rb ΘR Ξ x b pv A (Some M) _ _ _ _ Θ K D H Hli ltac:(constructor; eassumption))
          as [[Ξ1 Hp] Er].
        rewrite Er; simp simple_step; eexists; reflexivity. }
      destruct E as [[[r Hp] l] E]; simp run_cmd_impl; rewrite E; simp run_cmd_impl; eexists; reflexivity.
    - (* a generated module: as generated, its body *)
      intros ch B Rb B' Rb' ΘR Ξ x pv Δ cs ΘR' mp Kf U Htel HΔ Hfr Hr IH Hacc Θ K D H Hli Hrb c Hfc.
      assert (E2 : cc_gen (cc_mod x pv Δ cs) = c)
        by (apply (fill_cmd_gen_eq _ _ _ _ _ Hfc); rewrite <- (fill_cmd_head _ _ _ _ _ Hfc); reflexivity).
      subst c.
      assert (E : exists r, gen_mod_step ch (cmds_step ch (run_cmd_impl ch (loader_of ch Hacc))) Θ K D B Ξ x pv Δ cs H = rok r).
      { simp gen_mod_step.
        destruct (tele_ass_dec Δ) as [Htel' | Htel']; [| contradiction ]; simp gen_mod_step.
        match goal with |- context [check_ctx ?f ?a ?b ?c ?d] => destruct (check_ctx f a b c d) as [HΔ' | HΔ'] end;
          [| exfalso; apply HΔ'; exact (equiv_ctx _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HΔ) ].
        simp gen_mod_step.
        destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp gen_mod_step.
        destruct (linv_push Hli Htel' Hfr' HΔ') as [_ Hli'].
        destruct (IH Hacc Θ K D (mod_pre H Htel' Hfr' HΔ') Hli' Hrb) as [[[r Hp] l] E]; unfold run_cmds_impl in E; rewrite E.
        simp gen_mod_step.
        destruct (Hp _ _ Hli' Hrb) as [ΘR2 RbR2 Hr2 _ _ _ _]; cbn beta in Hr2;
          destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr2) as [F HF].
        destruct (list_case (cstate_stack r)) as [[[[mp' Kf'] U'] [Ξ2 HΞ]] | HΞ]; simp gen_mod_step;
          [ eexists; reflexivity | congruence ]. }
      destruct E as [[[r Hp] l] E]; simp run_cmd_impl; rewrite E; simp run_cmd_impl; eexists; reflexivity.
    - intros ch B Rb ΘR Ξ Hacc Θ K D H Hli Hrb; unfold run_cmds_impl; simp cmds_step; eexists; reflexivity.
    - (* a sequence: the head's result is the judgment's, by determinism *)
      intros ch B Rb ΘR Ξ c c3 cs B1 Rb1 ΘR1 Ξ1 B2 Rb2 ΘR2 Ξ2 Hac Hfc Hc IHc Hcs IHcs Hacc Θ K D H Hli Hrb;
        unfold run_cmds_impl; simp cmds_step.
      match goal with |- context [refs_check ?a ?b ?c ?d] => destruct (refs_check a b c d) as [[e Hq] | Hac'] end;
        simp cmds_step; [ exfalso; apply Hq; exact (equiv_acc _ _ _ _ (linv_equiv Hli) Hac) |].
      destruct (IHc Hacc Θ K D H Hli Hrb c Hfc) as [[[r1 Hp1] l1] E1]; rewrite E1; simp cmds_step.
      destruct (Hp1 _ _ Hli Hrb) as [ΘR1' RbR1' (c3' & Hfc' & Hr1) Hli1 Hrb1 _ _].
      pose proof (fill_cmd_functional _ _ _ (li_wf _ _ _ _ _ _ Hli) _ _ _ Hfc' Hfc) as ->.
      destruct (run_cmd_functional load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc Hr1) as (<- & HΞ1 & HB1 & HR1); subst Ξ1 B1 Rb1.
      destruct (IHcs Hacc _ _ _ (cons_pre H Hp1) Hli1 Hrb1) as [[[r2 Hp2] l2] E2]; unfold run_cmds_impl in E2; simp cmds_step in E2; rewrite E2.
      simp cmds_step; eexists; reflexivity.
    - (* a unit *)
      intros fp ch B1 Rb1 B2 Rb2 imps P0 P cs ΘR1 ΘR2 mp Kf U Hi IHi HPa Htel HP Hac Hb IHb Hacc Θ K H.
      rewrite run_unit_impl_unfold; cbn [run_unit_step].
      destruct (IHi Hacc Θ K nil (unit_pre H) (nil_linv H) (rb_ok_nil K)) as [[[r1 Hp1] l1] E1]; rewrite E1; cbv beta iota.
      destruct (Hp1 _ _ (nil_linv H) (rb_ok_nil K)) as [ΘR1' RbR1' Hr1 Hli1 Hrb1 _ _]; cbn beta in Hr1.
      destruct (run_cmds_functional load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi Hr1) as (<- & HΞ & HB & HR);
        rewrite <- HΞ in Hli1.
      subst B1 Rb1.
      pose proof (fill_params_fn_complete _ _ _ (unit_gctx H Hp1) (fctx_cmd (cstate_bt r1)) _ _
                    (equiv_fill_params _ _ _ _ _ _ (linv_equiv Hli1) (linv_restrict_gctx Hli1) HPa)) as Ea.
      destruct (inspect (fill_params_fn _ _ _ _ _ P0)) as [[P' | e] Ea'];
        [ assert (P' = P) as -> by congruence | exfalso; congruence ].
      cbv beta iota.
      destruct (tele_ass_dec P) as [Htel' | Htel']; [| contradiction ]; cbv beta iota.
      match goal with |- context [check_ctx ?f ?a ?b ?c ?d] => destruct (check_ctx f a b c d) as [HP' | HP'] end;
        [| exfalso; apply HP'; exact (equiv_ctx _ _ _ _ (linv_equiv Hli1) (linv_restrict_gctx Hli1) HP) ].
      match goal with |- context [refs_check ?a ?b ?c ?d] => destruct (refs_check a b c d) as [[e Hq] | Hac'] end;
        [ exfalso; apply Hq; exact (equiv_acc _ _ _ _ (linv_equiv Hli1) Hac) | cbv beta iota ].
      destruct (linv_push_unit Hli1 Htel' HP') as [_ Hli1'].
      destruct (IHb Hacc _ _ _ (unit_body_pre H Hp1 Htel' HP') Hli1' Hrb1) as [[[r2 Hp2] l2] E2]; rewrite E2; cbv beta iota.
      destruct (Hp2 _ _ Hli1' Hrb1) as [ΘR2' RbR2' Hr2 _ _ _ _]; cbn beta in Hr2; destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr2) as [F HF].
      destruct (list_case (cstate_stack r2)) as [[[[mp' Kf'] U'] [Ξ2 HΞ2]] | HΞ2]; [ eexists; reflexivity | congruence ].
    - (* no member left *)
      intros; exact I.
    - (* a member *)
      intros; exact I.
  Qed.

  (** The result is the judgment's, by determinism. *)
  Corollary run_cmd_impl_complete : forall ch B RbR ΘR Ξ c0 c B' RbR' ΘR' Ξ' Hacc Θ K D
      (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR -> fill_cmd ΘR Ξ B c0 c ->
      ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, run_cmd_impl ch (loader_of ch Hacc) Θ K D B Ξ c0 H = rok r /\ cstate_stack (proj1_sig (fst r)) = Ξ' /\
        cstate_bt (proj1_sig (fst r)) = B' /\
        linv ch (cstate_deps (proj1_sig (fst r))) (cstate_k (proj1_sig (fst r))) (cstate_dom (proj1_sig (fst r))) ΘR' Ξ' /\
        rb_ok (cstate_k (proj1_sig (fst r))) ΘR' RbR'.
  Proof.
    intros * Hli Hrb Hfc Hr;
      destruct (proj1 run_impl_complete _ _ _ _ _ _ _ _ _ _ Hr Hacc _ _ _ H Hli Hrb _ Hfc) as [r E].
    exists r; split; [ exact E |].
    destruct r as [[r Hp] l]; destruct (Hp _ _ Hli Hrb) as [ΘR'' RbR'' (c' & Hfc' & Hr') Hli' Hrb' _ _].
    cbn [proj1_sig fst].
    pose proof (fill_cmd_functional _ _ _ (li_wf _ _ _ _ _ _ Hli) _ _ _ Hfc' Hfc) as ->.
    destruct (run_cmd_functional load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Hr') as (<- & HΞ & HB & <-).
    rewrite <- HΞ in Hli'; split; [ symmetry; exact HΞ | split; [ symmetry; exact HB | split; assumption ] ].
  Qed.

  Corollary run_cmds_impl_complete : forall ch B RbR ΘR Ξ cs B' RbR' ΘR' Ξ' Hacc Θ K D
      (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, run_cmds_impl ch (loader_of ch Hacc) Θ K D B Ξ cs H = rok r /\ cstate_stack (proj1_sig (fst r)) = Ξ' /\
        cstate_bt (proj1_sig (fst r)) = B' /\
        linv ch (cstate_deps (proj1_sig (fst r))) (cstate_k (proj1_sig (fst r))) (cstate_dom (proj1_sig (fst r))) ΘR' Ξ' /\
        rb_ok (cstate_k (proj1_sig (fst r))) ΘR' RbR'.
  Proof.
    intros * Hli Hrb Hr; destruct (proj1 (proj2 run_impl_complete) _ _ _ _ _ _ _ _ _ _ Hr Hacc _ _ _ H Hli Hrb) as [r E].
    exists r; split; [ exact E |].
    destruct r as [[r Hp] l]; destruct (Hp _ _ Hli Hrb) as [ΘR'' RbR'' Hr' Hli' Hrb' _ _]; cbn beta in Hr'; cbn [proj1_sig fst].
    destruct (run_cmds_functional load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Hr') as (<- & HΞ & HB & <-).
    rewrite <- HΞ in Hli'; split; [ symmetry; exact HΞ | split; [ symmetry; exact HB | split; assumption ] ].
  Qed.

  Corollary run_unit_impl_complete : forall ch u B' RbU ΘU U Hacc Θ K (H : ginv ch Θ K),
      run_unit ch u B' RbU ΘU U ->
      exists r, run_unit_impl ch Hacc Θ K u H = rok r /\ us_unit (proj1_sig (fst r)) = U /\
        us_bt (proj1_sig (fst r)) = B' /\
        ginv ch (us_deps (proj1_sig (fst r))) (us_k (proj1_sig (fst r))) /\
        gds_equiv ΘU (gds_restrict (us_dom (proj1_sig (fst r))) (us_deps (proj1_sig (fst r)))).
  Proof.
    intros * Hu; destruct (proj1 (proj2 (proj2 run_impl_complete)) _ _ _ _ _ _ Hu Hacc _ _ H) as [r E].
    exists r; split; [ exact E |].
    destruct r as [[r Hp] l]; destruct (unit_equiv H Hp) as (RbU' & ΘU' & Hu' & G' & Heq & _); cbn [proj1_sig fst].
    destruct (run_unit_functional load_path read to_core _ _ _ _ _ _ _ _ _ _ _ eq_refl Hu Hu') as (<- & HU & HB & _).
    rewrite <- HU, <- HB; split; [ reflexivity | split; [ reflexivity | split; assumption ] ].
  Qed.

  (** ** The Program

      Only what the program imports is filed, so the whole accumulated [Θ] is
      equivalent to the judgment's.  Each log entry is an eval of the program,
      typed and normalized in the restriction it was checked in. *)

  Theorem prog_impl_sound : forall prg Hacc B Θ U log,
      prog_impl prg Hacc = rok (B, Θ, U, log) ->
      (exists ΘR, prog_sem load_path read to_core prg B ΘR U /\ gds_equiv ΘR Θ) /\
      (forall e, In e log ->
         ⊢ᵍ eval_entry_deps e ⍮ eval_entry_stack e /\ eval_entry_deps e ⍮ eval_entry_stack e ⍮ gs_tele (eval_entry_stack e) ⊢ eval_entry_exp e : eval_entry_typ e /\
         nbe (eval_entry_deps e) (eval_entry_stack e) (gs_tele (eval_entry_stack e)) (eval_entry_exp e) (eval_entry_typ e) (eval_entry_nf e)).
  Proof.
    unfold prog_impl; intros * E.
    destruct (to_core prg) as [u |] eqn:Ht; [| discriminate ].
    revert E; match goal with |- context [run_unit_impl ?a ?b ?c ?d ?e ?f] =>
      destruct (run_unit_impl a b c d e f) as [[[r Hp] [l Hl]] | e'] end; intros E; [| discriminate ].
    injection E as <- <- <- <-; split; [| intros e He; destruct (Hl e He) as [Hw Ht' Hn]; auto ].
    destruct (unit_equiv (ginv_nil _) Hp) as (RbU & ΘU & Hu & G & _ & Hgr & Hsub & Hdom).
    exists ΘU; split; [ exists u RbU; assumption |].
    split; [ exact Hsub |].
    intros y V HV.
    destruct (Hgr y ltac:(apply gds_dom_lookup; rewrite HV; discriminate)) as [[] | Hy].
    apply Hdom, gds_dom_lookup in Hy; destruct (gds_lookup ΘU y) as [V' |] eqn:E; [| contradiction ].
    rewrite (Hsub _ _ E) in HV; injection HV as ->; reflexivity.
  Qed.

  Theorem prog_impl_complete : forall prg B ΘR U,
      prog_sem load_path read to_core prg B ΘR U ->
      forall Hacc, exists Θ log, prog_impl prg Hacc = rok (B, Θ, U, log) /\ gds_equiv ΘR Θ.
  Proof.
    intros * [u Rb Ht Hu] Hacc.
    destruct (proj1 (proj2 (proj2 run_impl_complete)) _ _ _ _ _ _ Hu Hacc nil nil (ginv_nil _)) as [[[r Hp] l] E].
    assert (Hprog : prog_impl prg Hacc = rok (us_bt r, us_deps r, us_unit r, proj1_sig l))
      by (unfold prog_impl; revert E; rewrite Ht; intros E; rewrite E; reflexivity).
    destruct (prog_impl_sound _ _ _ _ _ _ Hprog) as [(ΘR' & [u' Rb' Ht' Hu'] & Heq) _].
    rewrite Ht in Ht'; injection Ht' as <-.
    destruct (run_unit_functional load_path read to_core _ _ _ _ _ _ _ _ _ _ _ eq_refl Hu Hu') as (<- & -> & -> & _).
    exists (us_deps r), (proj1_sig l); split; assumption.
  Qed.
End Impl.

(** ** Finitely Many Files

    Only here is [load_path] assumed to know finitely many files.  Each load
    adds one of them to the chain, so loading terminates, in whatever order
    it happens.  The executable never sees the list: [all_files] is a thunk,
    so only its existence matters, and nothing has to compute it. *)

Section Files.
  Variable load_path : path -> option string.
  (** The files [load_path] knows, as a thunk: the termination proof needs
      such a list to exist, never its value. *)
  Variable all_files : unit -> list path.
  Hypothesis Hfiles : forall fp, (exists s, load_path fp = Some s) <-> In fp (all_files tt).

  (** How many known files the chain [ch] has not loaded yet; it decreases
      with every load. *)
  Definition unloaded (ch : list path) : nat :=
    List.length (filter (fun fp => if in_dec path_eq_dec fp ch then false else true) (all_files tt)).

  Lemma filter_mono : forall (p1 p2 : path -> bool) l, (forall y, p1 y = true -> p2 y = true) ->
      List.length (filter p1 l) <= List.length (filter p2 l).
  Proof.
    intros * Hpq; induction l as [| y l IH]; cbn; [ lia |].
    destruct (p1 y) eqn:Ep; [ rewrite (Hpq _ Ep); cbn; lia | destruct (p2 y); cbn; lia ].
  Qed.

  Lemma filter_strict : forall (p1 p2 : path -> bool) l x, (forall y, p1 y = true -> p2 y = true) ->
      In x l -> p1 x = false -> p2 x = true -> List.length (filter p1 l) < List.length (filter p2 l).
  Proof.
    intros * Hpq; induction l as [| y l IH]; intros Hin Hp Hq; [ contradiction |].
    pose proof (filter_mono p1 p2 l Hpq); destruct Hin as [-> | Hin]; cbn.
    - rewrite Hp, Hq; cbn; lia.
    - specialize (IH Hin Hp Hq).
      destruct (p1 y) eqn:Ep; [ rewrite (Hpq _ Ep); cbn; lia | destruct (p2 y); cbn; lia ].
  Qed.

  Theorem load_step_wf : well_founded (load_step load_path).
  Proof.
    apply (wf_incl _ _ (ltof _ unloaded)); [| apply well_founded_ltof ].
    intros ch' ch [fp s -> Hn Hs]; unfold ltof, unloaded.
    apply (filter_strict _ _ _ fp).
    - intros y; destruct (in_dec path_eq_dec y (fp :: ch)) as [| Hy]; [ discriminate |].
      destruct (in_dec path_eq_dec y ch) as [Hy' |]; [ exfalso; apply Hy; right; exact Hy' | reflexivity ].
    - apply Hfiles; eauto.
    - destruct (in_dec path_eq_dec fp (fp :: ch)) as [| Hc]; [ reflexivity | exfalso; apply Hc; left; reflexivity ].
    - destruct (in_dec path_eq_dec fp ch); [ contradiction | reflexivity ].
  Qed.

  Corollary prog_impl_complete_wf : forall read to_core vs
      (Hvs : forall Θ Ξ HΞ R csD Vs Ss csV Nvs, views_ok Θ Ξ R csD Vs Ss csV Nvs -> exists v, vs Θ Ξ HΞ R csD = rok v)
      prg B ΘR U,
      prog_sem load_path read to_core prg B ΘR U ->
      exists Θ log, prog_impl load_path read to_core vs prg (load_step_wf _) = rok (B, Θ, U, log) /\ gds_equiv ΘR Θ.
  Proof. intros read to_core vs Hvs * H; exact (prog_impl_complete _ _ _ vs Hvs _ _ _ _ H _). Qed.
End Files.
