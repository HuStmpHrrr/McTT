(** * The Checks of Commands

    What the run of commands ([Extraction.CommandRun]) checks a command
    with, apart from the run itself: the errors a run can fail with
    ([run_error]), and the searches that choose their messages once a term
    is rejected ([mod_blame], [brs_blame], [blocks_blame], [value_blame],
    [field_value_blame]); the deciders a command's checks need beyond the
    checker's ([ind_former_dec], [record_former_dec], [large_type_dec]);
    the fast entries of definitions, which store the values of their
    bodies ([def_fentry], [dm_fentry]); a mutual definition's definitions
    filed ([mdefs_dec]); and a group filed through the filed units
    ([raw_decl_filed_f]), with its views ([views_ok]).

    A run also logs each [eval] it checked, with its normal form
    ([eval_entry], certified by [eval_ok]). *)

From Stdlib Require Import List String Wellfounded Wf_nat Lia.
From Equations Require Import Equations.

From Mctt Require Import LibTactics.
From Mctt.Algorithmic Require Import Typing.
From Mctt.Core Require Import Base Soundness Completeness.
From Mctt.Core.Consequences Require Import Consistency.
From Mctt.Core.Completeness Require Import UniverseCases.
From Mctt.Core.Completeness.Global Require Import Args.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import Structural Command.
From Mctt.Core Require Import TypedElab.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf Paths LookupSound.
From Mctt.Core.Syntactic.System.Inductives Require Import IndRuns Runs.
From Mctt.Core.Syntactic.System.Records Require Import RecordRuns.
From Mctt.Core.Syntactic.System.Inductives Require Import IndCong.
From Mctt.Extraction Require Import Lookup NbE TypeCheck GlobalCheck IndDecl RecordDecl MemberType Opens Privacy.
From Mctt.Extraction Require Import MdefGroup TypedElab FastDesc LookupTwins FastState.
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

(** A decision of [levels_abstractable] at every global context, the one
    the checker is given (the flag decides it once units carry it). *)
Definition levels_abstractable_decider : Type :=
  forall Θ Ξ G Δ E, ⊢ Θ ⍮ Ξ ⍮ Δ ++ G -> { levels_abstractable Θ Ξ G Δ E } + { ~ levels_abstractable Θ Ξ G Δ E }.

(** The member of a group, with its index. *)
Definition member_case (D : ind_decl) (k : nat) : {Mk | ind_member D k = Some Mk} + {ind_member D k = None} :=
  opt_case (ind_member D k).

(** A normal type is the [Π] over its domains ([nf_pi_tele]), a telescope
    of assumptions, of its codomain. *)
Lemma nf_pi_tele_spec : forall W Ds C, nf_pi_tele W = (Ds, C) -> nf_to_exp W = ctx_pi Ds (nf_to_exp C) /\ all_assumptions Ds.
Proof.
  induction W; intros * E; cbn [nf_pi_tele] in E;
    try (injection E as <- <-; split; [ reflexivity | constructor ]).
  destruct a0; try (injection E as <- <-; split; [ reflexivity | constructor ]).
  destruct (nf_pi_tele W2) as [Ds' C'] eqn:E2; injection E as <- <-.
  destruct (IHW2 _ _ eq_refl) as [HW Ha].
  cbn [nf_to_exp]; rewrite ctx_pi_snoc, <- HW; split; [ reflexivity |].
  apply List.Forall_app; split; [ exact Ha | constructor; [ do 2 eexists; reflexivity | constructor ] ].
Qed.

(** A [Π] into a relevant codomain typed at a sort is a type of a large
    universe: its value at the initial environment is a [Π] of that kind
    ([typed_at_sort_of_initial_kind]). *)
Lemma relevant_pi_large : forall Θ Ξ Γ κ A B S, type_sort S -> Θ ⍮ Ξ ⍮ Γ ⊢ a_pi κ ak_relevant A B : S ->
    exists j : nat, Θ ⍮ Ξ ⍮ Γ ⊢ a_pi κ ak_relevant A B : Typeω@j.
Proof.
  intros * HS HT.
  pose proof (@completeness_fundamental_exp (gc_mk Θ Ξ) _ _ _ HT) as HTs.
  destruct (@rel_exp_under_ctx_at_initial_env (gc_mk Θ Ξ) _ _ _ _ (wf_ctx_scoped_exp HT) (wf_exp_scoped_term _ _ _ _ _ HT)
              (wf_exp_scoped_term _ _ _ _ _ HT) HTs) as [ρ a W W' Hρ Ea HW _ _].
  destruct HW as [w Hp _ | m w _ Em _].
  - exfalso; destruct HS; inversion Ea; subst; cbn in Hp; discriminate Hp.
  - destruct (@typed_at_sort_of_initial_kind (gc_mk Θ Ξ) _ _ _ _ _ HS HT Hρ Em) as [k Hk].
    inversion Em; subst; exists k; exact Hk.
Qed.

(** A term of a normal type, at the variables of the type's domains, is of
    its codomain past them: a relevant [Π]'s, at a large universe. *)
Lemma applied_vars_typed : forall Θ Ξ Γ M W Ds C, Θ ⍮ Ξ ⍮ Γ ⊢ M : nf_to_exp W -> nf_pi_tele W = (Ds, C) ->
    Θ ⍮ Ξ ⍮ Ds ++ Γ ⊢ exp_applied_to_vars M (List.length Ds) : nf_to_exp C.
Proof.
  intros * HM Ep; destruct (nf_pi_tele_spec _ _ _ Ep) as [HW Ha]; rewrite HW in HM.
  destruct Ds as [| e Ds0] using List.rev_ind.
  - cbn in HM |- *; unfold exp_applied_to_vars; cbn.
    rewrite exp_wk_id_ext by (intros x; cbn; lia); exact HM.
  - assert (He : exists κ A, e = ce_ass κ A)
      by (unfold all_assumptions in Ha; apply List.Forall_app in Ha as [_ He]; inversion He as [| ? ? He0]; exact He0).
    destruct He as (κ & A & ->).
    pose proof (presup_exp_typ HM) as Hty; rewrite ctx_pi_snoc in Hty.
    inversion Hty as [? S HS HT | ]; subst.
    destruct (relevant_pi_large _ _ _ _ _ _ _ HS HT) as [i HT'].
    rewrite <- ctx_pi_snoc in HT'.
    pose proof (ctx_pi_inv_outer _ _ _ _ Ha HT') as HC.
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
Definition unit_closure_map : Set := list (path * (list path * builtins)).

Equations unit_closure_find (K : unit_closure_map) (fp : path) : option (list path) by struct K :=
| nil, _ => None
| (fq, (D, _)) :: K', fp => if path_beq fp fq then Some D else unit_closure_find K' fp.

Equations unit_closure_builtins (K : unit_closure_map) (fp : path) : option builtins by struct K :=
| nil, _ => None
| (fq, (_, B)) :: K', fp => if path_beq fp fq then Some B else unit_closure_builtins K' fp.

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

Inductive run_error : Type :=
| run_error_msg : string -> run_error
(** The body of a definition is not of its declared type, which is a type. *)
| run_error_def : string -> fstack -> typ -> exp -> run_error
(** The declared type of a definition with a body is not a type. *)
| run_error_def_typ : string -> fstack -> typ -> run_error
(** An ascribed eval: the term is not of its ascription, which is a type. *)
| run_error_eval_check : fstack -> exp -> typ -> run_error
(** An ascribed eval: the ascription of the term is not a type. *)
| run_error_eval_typ : fstack -> exp -> typ -> run_error
| run_error_eval_infer : fstack -> exp -> run_error
(** A small universe [Type@{t}] whose level [t] is of no type of levels,
    found by [find_level_blame] where a type or a telescope is rejected:
    [t] lives in the context the stack's telescope is extended by, innermost
    entry first. *)
| run_error_level : fstack -> ctx -> exp -> run_error
| run_error_cycle : list path -> run_error
| run_error_unit : path -> string -> run_error
(** A private member, named by its module, reached from outside it. *)
| run_error_private : qname -> string -> run_error
(** A member [y] selected from a term whose type infers to nothing:
    [run_error_access_no_type Ξ ox Γ M y], [M] in the context [Γ] the stack's
    telescope is extended by, innermost entry first ([TypedElab]), in
    the command declaring [ox], if it declares a name, so that the printer
    can name the binders it declares. *)
| run_error_access_no_type : fstack -> option string -> ctx -> exp -> string -> run_error
(** A member [y] selected from a term whose inferred type [A] is no record
    type: [run_error_access_not_record Ξ ox Γ M A y], [M] and [A] in the context
    [Γ] the stack's telescope is extended by, in the command declaring
    [ox]. *)
| run_error_access_not_record : fstack -> option string -> ctx -> exp -> typ -> string -> run_error
(** A member selected from a value of the record [p] that the record's
    module does not have: neither a field nor a member of its with-area. *)
| run_error_record_member : qname -> string -> run_error
(** A record type applied past its parameters, to a value, where a term
    stands: [run_error_record_value_term Ξ ox Γ M n], [M] the record type
    applied, its first [n] arguments the parameters, in the context [Γ]
    the stack's telescope is extended by, in the command declaring
    [ox].  It is the module of the value, not a term. *)
| run_error_record_value_term : fstack -> option string -> ctx -> exp -> nat -> run_error
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
| run_error_record_field : fstack -> option string -> ctx -> qname -> string -> exp -> typ -> run_error
(** A private entry of a local body, by the chain of submodules from the
    local module, reached from outside it. *)
| run_error_private_local : list string -> string -> run_error
(** An open that generates nothing ([Opens]). *)
| run_error_import : open_failure_reason -> run_error
(** The argument [y] of the constructor [c] of the type [x] has [x] in an
    argument of another inductive type, its head. *)
| run_error_nested : string -> string -> string -> exp -> run_error
(** The argument [y] of the constructor [c] of the type [x] has a record
    at an instance in which [Self] [s] is an argument of the head [h], in
    the context [Δ], its first [k] entries unnamed. *)
| run_error_self_arg : string -> string -> string -> string -> nat -> ctx -> exp -> run_error
(** The non-uniform parameter at a position (outermost [0]) of the type
    [x]: its type is not in the sort; both live in the context. *)
| run_error_ind_nparams : string -> nat -> ctx -> typ -> typ -> run_error
(** A chain from a unit, in term position, that names a module (an alias
    of the module of an inductive type included), not a term. *)
| run_error_mod_term : qname -> run_error
(** A path that names no inductive type where one is wanted. *)
| run_error_not_ind : qname -> run_error
(** A literal, a numeral or the token [ℕ], with no natural-number type
    bound ([Builtin]). *)
| run_error_lit : literal_failure_reason -> run_error
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
| run_error_elim_scrutinee : fstack -> option string -> ctx -> exp -> option typ -> run_error
(** An eliminator, in its context under the stack's telescope, no reading
    of which, own or view, fits its blocks: [run_error_elim_no_group Ξ Γ E], [E]
    the eliminator, its scrutinee filled. *)
| run_error_elim_no_group : fstack -> ctx -> exp -> run_error
(** An eliminator, in its context under the stack's telescope, several
    readings of which fit its blocks: [run_error_elim_ambiguous Ξ Γ E rs], [E]
    the eliminator, its scrutinee filled, [rs] the readings, each its
    group and its uniform parameters. *)
| run_error_elim_ambiguous : fstack -> ctx -> exp -> list (qname * list exp) -> run_error
(** An eliminator of a group whose blocks are not one per member in the
    member order, in its context under the stack's telescope:
    [run_error_elim_blocks Ξ Γ E ks is j], [E] the eliminator, [ks] the members
    with no block, [is] the positions of the written blocks that are for
    no member left ([elim_blocks_blame]), and [j] the member of the block
    marked [at], for the printer's skeleton of the eliminator.  Both lists
    are empty when every member has its block, out of order. *)
| run_error_elim_blocks : fstack -> ctx -> exp -> list nat -> list nat -> nat -> run_error
(** A view of the group being declared, an instance of a container met in
    the arguments, rejected: the group's first member, the instance, and
    why ([view_why]). *)
| run_error_view : string -> view_key -> view_why -> run_error
(** An error, with the state it occurred in, for the printer: the units
    imported, the stack, both fast, and the natural numbers bound there,
    their type and constructors as [nat_view] gives them. *)
| run_error_nat : fview -> fstack -> option (qname * string * string) -> run_error -> run_error.

Definition privacy_run_error (e : privacy_error) : run_error :=
  match e with
  | privacy_error_global qd x => run_error_private qd x
  | privacy_error_local ch x => run_error_private_local ch x
  end.

(** The error for a rejected type or telescope at the frames [fs]: the
    blamed level if [find_level_blame] found one, otherwise the given
    error.  The blame is at the fast context [F] the check ran at. *)
Definition blame_error {F : FCtx} {Γ} (fs : fstack) (b : option (level_blame (fc_deps F) (fc_stack F) Γ)) (e : run_error) : run_error :=
  match b with
  | Some (exist _ (Δ, t) _) => run_error_level fs Δ t
  | None => e
  end.

(** Where a term is rejected, a chain from a unit in it that names a
    module but stands where a term does: found syntactically, whether the
    chains name modules asked of the global context ([gc_module]), which
    does not read the local context for them, and whether they name a
    definition with a module part, which is a term too ([gc_entry]); all
    looked up in the fast context [F]. *)
Section ModBlame.
  Variable F : FCtx.

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
        match fc_module F (qname_app mp (x :: nil)), fc_entry F (qname_app mp (x :: nil)),
              fc_mlookup F (qname_app mp (x :: nil)), fc_record F (qname_app mp (x :: nil)) with
        | Some _, Some (fe_def_mod _ _ _ _ _), _, _ => None
        | Some _, _, None, None => Some (run_error_mod_term (qname_app mp (x :: nil)))
        | _, _, _, _ => None
        end
    | None =>
        match H, mod_qname (mod_head H) with
        | me_app _ _, Some p =>
            match fc_record F p, fc_resolve F (qname_app p (x :: nil)) with
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
    | a_succl M | a_univ M | a_left M | a_right M => mod_blame M
    | a_maxl M N | a_pi _ _ M N | a_fn M N | a_app M N | a_and M N => first_some (mod_blame M) (fun _ => mod_blame N)
    | a_absurd A M => first_some (mod_blame M) (fun _ => mod_blame A)
    | a_conj P Q M N =>
        first_some (mod_blame P) (fun _ => first_some (mod_blame Q) (fun _ => first_some (mod_blame M) (fun _ => mod_blame N)))
    | a_elim _ _ Us _ Bks M =>
        first_some (mod_blame M) (fun _ => first_some
          ((fix exps (Us : list exp) : option run_error :=
              match Us with
              | nil => None
              | U :: Us' => first_some (mod_blame U) (fun _ => exps Us')
              end) Us)
          (fun _ => (fix blocks (Bks : list eblock) : option run_error :=
              match Bks with
              | nil => None
              | eb_mk _ Z A Bs :: Bks' =>
                  first_some (mod_blame Z)
                    (fun _ => first_some (mod_blame A) (fun _ => first_some
                      ((fix brs (Bs : list (string * nat * exp)) : option run_error :=
                          match Bs with
                          | nil => None
                          | b :: Bs' => first_some (mod_blame (snd b)) (fun _ => brs Bs')
                          end) Bs)
                      (fun _ => blocks Bks')))
              end) Bks))
    | a_let (b_def A N) B =>
        first_some (mod_blame A) (fun _ => first_some (mod_blame N) (fun _ => mod_blame B))
    | a_let (b_mod _) B => mod_blame B
    | a_mem H x => mod_term_blame H x
    | _ => None
    end.
End ModBlame.

(** A binder of a term a message is read in, whose type the message does
    not read: only the depth matters, for the printer to name the binders. *)
Definition unread_binder : centry := ce_ass ak_relevant a_prop.

(** [n] such binders. *)
Definition unread_binders (n : nat) : ctx := List.repeat unread_binder n.

(** Where a term is rejected, a block of an eliminator whose branches do
    not match the constructors of the member it eliminates.  The member is
    read off the names of the branches: every member of a group of the
    global context that has a constructor of each branch's name, and the
    error is reported when all of them give the same one.  This only
    chooses the message. *)
Section BranchBlame.
  (** The members of the groups of the units a fast context sees and of
      its frames ([fc_all_inds]), each with its group. *)
  Definition ctx_members (F : FCtx) : list (ind_decl * imember) :=
    flat_map (fun D => List.map (pair D) (ind_members D)) (fc_all_inds F).

  Definition brs_has (Bs : list (string * nat * exp)) (c : string) : nat :=
    List.length (List.filter (fun b => String.eqb (fst (fst b)) c) Bs).

  Fixpoint strings_eqb (xs ys : list string) : bool :=
    match xs, ys with
    | nil, nil => true
    | x :: xs, y :: ys => andb (String.eqb x y) (strings_eqb xs ys)
    | _, _ => false
    end.

  (** The first mismatch of the branches [Bs] against the constructors of
      the member [Mk] of the group [D]: a branch's binders, then a
      constructor without a branch or with two, then the order of the
      branches. *)
  Definition branch_check (D : ind_decl) (Mk : imember) (Bs : list (string * nat * exp)) : option run_error :=
    first_some (first_some
      ((fix go (Bs0 : list (string * nat * exp)) : option run_error :=
          match Bs0 with
          | nil => None
          | (c, n, _) :: Bs0' =>
              match ind_con Mk c with
              | Some gs =>
                  if Nat.eqb n (im_nn Mk + List.length gs + cargs_nrec D gs) then go Bs0'
                  else Some (run_error_branch_arity c n (im_nn Mk) (List.length gs) (cargs_nrec D gs))
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
         if strings_eqb (List.map (fun b => fst (fst b)) Bs) (List.map fst (im_cons Mk)) then None
         else Some (run_error_branch_order (List.map fst (im_cons Mk)))).

  Definition run_error_eqb (e1 e2 : run_error) : bool :=
    match e1, e2 with
    | run_error_branch_arity c n k a r, run_error_branch_arity c' n' k' a' r' =>
        andb (String.eqb c c') (andb (Nat.eqb n n') (andb (Nat.eqb k k') (andb (Nat.eqb a a') (Nat.eqb r r'))))
    | run_error_branch_unknown c, run_error_branch_unknown c' => String.eqb c c'
    | run_error_branch_missing c, run_error_branch_missing c' => String.eqb c c'
    | run_error_branch_dup c, run_error_branch_dup c' => String.eqb c c'
    | run_error_branch_order cs, run_error_branch_order cs' => strings_eqb cs cs'
    | _, _ => false
    end.

  (** The mismatch of a block's branches [Bs], if every member they could
      be for gives the same one. *)
  Definition elim_blame (F : FCtx) (Bs : list (string * nat * exp)) : option run_error :=
    match Bs with
    | nil => None
    | _ =>
        let is_con (DM : (ind_decl * imember)%type) b := match ind_con (snd DM) (fst (fst b)) with Some _ => true | None => false end in
        let cands :=
          match List.filter (fun DM => forallb (is_con DM) Bs) (ctx_members F) with
          | nil => List.filter (fun DM => existsb (is_con DM) Bs) (ctx_members F)
          | Ms => Ms
          end in
        match List.map (fun DM => branch_check (fst DM) (snd DM) Bs) cands with
        | Some e :: rs => if forallb (fun r => match r with Some e' => run_error_eqb e e' | None => false end) rs then Some e else None
        | _ => None
        end
    end.

  (** The first mismatch of a block's branches in a term, inside out. *)
  Fixpoint brs_blame (F : FCtx) (M : exp) : option run_error :=
    match M with
    | a_succl M | a_univ M | a_left M | a_right M => brs_blame F M
    | a_maxl M N | a_pi _ _ M N | a_fn M N | a_app M N | a_and M N => first_some (brs_blame F M) (fun _ => brs_blame F N)
    | a_absurd A M => first_some (brs_blame F M) (fun _ => brs_blame F A)
    | a_conj P Q M N =>
        first_some (brs_blame F P) (fun _ => first_some (brs_blame F Q) (fun _ => first_some (brs_blame F M) (fun _ => brs_blame F N)))
    | a_elim _ _ Us _ Bks M =>
        first_some (brs_blame F M) (fun _ => first_some
          ((fix exps (Us : list exp) : option run_error :=
              match Us with
              | nil => None
              | U :: Us' => first_some (brs_blame F U) (fun _ => exps Us')
              end) Us)
          (fun _ => (fix blocks (Bks : list eblock) : option run_error :=
              match Bks with
              | nil => None
              | eb_mk _ Z A Bs :: Bks' =>
                  first_some (brs_blame F Z)
                    (fun _ => first_some (brs_blame F A) (fun _ => first_some (elim_blame F Bs)
                      (fun _ => first_some
                        ((fix brs (Bs : list (string * nat * exp)) : option run_error :=
                            match Bs with
                            | nil => None
                            | b :: Bs' => first_some (brs_blame F (snd b)) (fun _ => brs Bs')
                            end) Bs)
                        (fun _ => blocks Bks'))))
              end) Bks))
    | a_let (b_def A N) B =>
        first_some (brs_blame F A) (fun _ => first_some (brs_blame F N) (fun _ => brs_blame F B))
    | a_let (b_mod _) B => brs_blame F B
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
  (** The fast context the groups are looked up in *)
  Variable F : FCtx.

  (** Whether the block [b] is for the member [Mk]: its branches are for
      [Mk]'s constructors, in order. *)
  Definition block_fits (Mk : imember) (b : eblock) : bool :=
    strings_eqb (List.map (fun br => fst (fst br)) (eb_brs b)) (List.map fst (im_cons Mk)).

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

  (** The group of an eliminator: its own once filled; with none, the one
      group without uniform parameters, among those of the units seen and
      the frames ([fc_all_groups]), a member of which its block [m] is
      for.  That second case is a guess, a hint for the message only: it
      reads the branches' names, not the scrutinee's type, and is asked of
      a term already rejected, so it decides nothing about typing. *)
  (** The eliminator [E], in the context [Γ], if its blocks are too few or
      too many for its group, or one per member but out of order.  With as
      many blocks as members of which some match no member, the branches
      are to blame ([brs_blame]), not the blocks. *)
  Definition elim_blocks_check (Γ : ctx) (E : exp) : option run_error :=
    match E with
    | a_elim r p Us m Bks M0 =>
        match option_map (fun D => (p, D)) (fc_ind F p) with
        | None => None
        | Some (p, D) =>
            let Ms := ind_block_members D in
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
              | nil, nil => if ordered then None else Some (run_error_elim_blocks (fc_frames F) Γ E nil nil j)
              | _, _ => None
              end
            else Some (run_error_elim_blocks (fc_frames F) Γ E missing extra j)
        end
    | _ => None
    end.

  (** The first eliminator in a term, in the context [Γ] of its binders,
      whose blocks do not match its group: its parts first, then itself. *)
  Fixpoint blocks_blame (Γ : ctx) (M : exp) : option run_error :=
    match M with
    | a_succl M | a_univ M | a_left M | a_right M => blocks_blame Γ M
    | a_maxl M N | a_app M N => first_some (blocks_blame Γ M) (fun _ => blocks_blame Γ N)
    | a_pi _ _ A B | a_fn A B | a_and A B => first_some (blocks_blame Γ A) (fun _ => blocks_blame (unread_binder :: Γ) B)
    | a_absurd A M => first_some (blocks_blame Γ M) (fun _ => blocks_blame Γ A)
    | a_conj P Q M N =>
        first_some (blocks_blame Γ P) (fun _ => first_some (blocks_blame (unread_binder :: Γ) Q)
          (fun _ => first_some (blocks_blame Γ M) (fun _ => blocks_blame Γ N)))
    | a_elim _ _ Us m Bks M0 =>
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
                | eb_mk nm Z A Bs :: Bks' =>
                    first_some (blocks_blame (unread_binders (nm - 1) ++ Γ) Z)
                      (fun _ => first_some (blocks_blame (unread_binders nm ++ Γ) A) (fun _ => first_some
                        ((fix brs (Bs : list (string * nat * exp)) : option run_error :=
                            match Bs with
                            | nil => None
                            | b :: Bs' => first_some (blocks_blame (unread_binders (snd (fst b)) ++ Γ) (snd b)) (fun _ => brs Bs')
                            end) Bs)
                        (fun _ => blocks Bks')))
                end) Bks)
            (fun _ => elim_blocks_check Γ M)))
    | a_let (b_def A N) B =>
        first_some (blocks_blame Γ A) (fun _ => first_some (blocks_blame Γ N) (fun _ => blocks_blame (ce_def A N :: Γ) B))
    | a_let (b_mod U) B => blocks_blame (ce_mod U :: Γ) B
    | _ => None
    end.
End BlocksBlame.

(** Where a term is rejected, a record type applied past its parameters,
    to a value, where a term stands; or a record value whose fields are
    not the record's, in order.  [ox] names the command, for the printer;
    the contexts are past the stack's telescope. *)
Section ValueBlame.
  (** The fast context the records are looked up in, and the command
      declaring [ox], for the printer *)
  Variables (F : FCtx) (ox : option string).

  (** The record a term's head names, with its declaration. *)
  Definition record_head (M : exp) : option (qname * record_decl) :=
    match app_head M with
    | a_record p => option_map (pair p) (fc_record F p)
    | a_mem H x =>
        match mod_qname H with
        | Some mp => option_map (pair (qname_app mp (x :: nil))) (fc_record F (qname_app mp (x :: nil)))
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
        then Some (run_error_record_value_term (fc_frames F) ox Γ M (List.length (record_params R)))
        else None
    | None => None
    end.

  Fixpoint value_blame (Γ : ctx) (M : exp) : option run_error :=
    match M with
    | a_succl M0 | a_univ M0 | a_proj _ M0 | a_left M0 | a_right M0 => value_blame Γ M0
    | a_maxl M0 N => first_some (value_blame Γ M0) (fun _ => value_blame Γ N)
    | a_app M0 N =>
        first_some (applied_blame Γ M) (fun _ => first_some (value_blame Γ M0) (fun _ => value_blame Γ N))
    | a_pi _ _ A B | a_fn A B | a_and A B => first_some (value_blame Γ A) (fun _ => value_blame (unread_binder :: Γ) B)
    | a_absurd A M0 => first_some (value_blame Γ M0) (fun _ => value_blame Γ A)
    | a_conj P Q M0 N =>
        first_some (value_blame Γ P) (fun _ => first_some (value_blame (unread_binder :: Γ) Q)
          (fun _ => first_some (value_blame Γ M0) (fun _ => value_blame Γ N)))
    | a_let (b_def A N) B =>
        first_some (value_blame Γ A) (fun _ => first_some (value_blame Γ N) (fun _ => value_blame (ce_def A N :: Γ) B))
    | a_let (b_mod U) B => value_blame (ce_mod U :: Γ) B
    | a_tuple T fs =>
        first_some (match record_head T with Some (p, R) => fields_blame p R fs | None => None end)
          (fun _ => first_some (value_blame Γ T) (fun _ =>
            (fix fields (fs : list (string * exp)) : option run_error :=
               match fs with
               | nil => None
               | (_, N) :: fs' => first_some (value_blame Γ N) (fun _ => fields fs')
               end) fs))
    | a_elim _ _ Us _ Bks M0 =>
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
Section FieldBlame.
  (** The fast context of the checks ([Extraction.Lookup]), and the
      command declaring [ox], for the printer. *)
  Variables (F : FCtx) (ox : option string).
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  (** The decision of [levels_abstractable] the checker is given *)
  Variable levels_abstractable_dec : forall G Δ E, ⊢ Θ ⍮ Ξ ⍮ Δ ++ G ->
      { levels_abstractable Θ Ξ G Δ E } + { ~ levels_abstractable Θ Ξ G Δ E }.

  (** The term [M] in the context [Δ] the frames' parameters are extended
      by, innermost entry first. *)
  Fixpoint field_value_blame (Δ : ctx) (HΔ : ⊢ Θ ⍮ Ξ ⍮ (Δ ++ fc_tele F)) (M : exp) {struct M} : option run_error :=
    match M with
    | a_fn A B =>
        match check_type F levels_abstractable_dec (Δ ++ fc_tele F) HΔ A with
        | inleft (existT _ r (exist _ i HA)) =>
            field_value_blame (ce_ass r A :: Δ) (wf_ctx_extend _ _ _ _ _ _ HA (sort_kind_abs_kind_sort r i)) B
        | inright _ => None
        end
    | a_let (b_def A N) B =>
        match check_type F levels_abstractable_dec (Δ ++ fc_tele F) HΔ A with
        | inleft (existT _ r (exist _ i HA)) =>
            match check_exp_typed F levels_abstractable_dec (Δ ++ fc_tele F) HΔ A (type_of_check_type F _ _ _ _ HA) N with
            | left HN => field_value_blame (ce_def A N :: Δ) (wf_ctx_extend_def _ _ _ _ _ _ HA (type_sort_kind_universe r i) HN) B
            | right _ => None
            end
        | inright _ => None
        end
    | a_tuple T fs =>
        match record_head F T with
        | Some (p, R) =>
            (fix fields (k : nat) (fs0 : list (string * exp)) {struct fs0} : option run_error :=
               match fs0 with
               | nil => None
               | (f, N) :: fs' =>
                   match List.nth_error (record_fields R) k with
                   | Some (_, U) =>
                       let Uk := U[sb_of_list Id (app_args T ++ List.firstn k (List.map snd fs))] in
                       match check_type F levels_abstractable_dec (Δ ++ fc_tele F) HΔ Uk with
                       | inleft (existT _ r (exist _ i HU)) =>
                           match check_exp_typed F levels_abstractable_dec (Δ ++ fc_tele F) HΔ Uk (type_of_check_type F _ _ _ _ HU) N with
                           | left _ => fields (S k) fs'
                           | right _ =>
                               first_some (field_value_blame Δ HΔ N)
                                 (fun _ =>
                                    let (W, _) := nbe_ty_impl F (Δ ++ fc_tele F) Uk
                                                    (@nbe_order_of_type (fc_gctx F) _ _ (type_of_check_type F _ _ _ _ HU)) in
                                    Some (run_error_record_field (fc_frames F) ox Δ p f N (nf_to_exp W)))
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
Definition field_error (F : FCtx) (ox : option string)
    (levels_abstractable_dec : forall G Δ E, ⊢ fc_deps F ⍮ fc_stack F ⍮ Δ ++ G ->
       { levels_abstractable (fc_deps F) (fc_stack F) G Δ E } + { ~ levels_abstractable (fc_deps F) (fc_stack F) G Δ E })
    (HΞ : ⊢ fc_deps F ⍮ fc_stack F ⍮ fc_tele F) (M : exp) (e : run_error) : run_error :=
  match field_value_blame F ox levels_abstractable_dec nil HΞ M with
  | Some e' => e'
  | None => e
  end.

(** The error for a rejected term of the command declaring [ox]: a module
    where a term stands, if there is one, then a record value's module
    where a term stands or a record value with wrong fields, then an
    eliminator whose blocks do not match its group, then one whose
    branches do not match its type, otherwise the given error. *)
Definition mod_error (F : FCtx) (ox : option string) (Ms : list exp)
    (e : run_error) : run_error :=
  match List.fold_right (fun M r => first_some (first_some (mod_blame F M)
                                      (fun _ => first_some (value_blame F ox nil M)
                                        (fun _ => first_some (blocks_blame F nil M) (fun _ => brs_blame F M))))
                                      (fun _ => r)) None Ms with
  | Some e' => e'
  | None => e
  end.

(** The error for a rejected telescope at the frames [fs]: the blamed
    level, if any, at the fast context [F] the check ran at *)
Definition tele_blame_error {F : FCtx} {Γ Δ} (fs : fstack)
    (b : option (level_blame (fc_deps F) (fc_stack F) Γ) + { ⊢ fc_deps F ⍮ fc_stack F ⍮ (Δ ++ Γ) })
    (e : run_error) : run_error :=
  match b with
  | inleft ob => blame_error fs ob e
  | inright _ => e
  end.

Inductive run_result (A : Type) : Type :=
| run_success : A -> run_result A
| run_failure : run_error -> run_result A.

Arguments run_success {A}.
Arguments run_failure {A}.

(** A checked and normalized [eval]: in the units seen [eval_entry_view] (the
    state restricted to the imports so far), on the frames [eval_entry_frames],
    both fast, and in the context of the frames' parameters, the expression
    [eval_entry_exp] has type [eval_entry_typ] (ascribed or inferred) and
    normalizes to [eval_entry_nf]. *)
Record eval_entry : Type :=
  { (** the units seen *)
    eval_entry_view : fview
    (** the open frames *)
  ; eval_entry_frames : fstack
    (** the term evaluated *)
  ; eval_entry_exp : exp
    (** its type, ascribed or inferred *)
  ; eval_entry_typ : typ
    (** its normal form *)
  ; eval_entry_nf : nf }.

(** The Core filed units an entry stands for, for types only *)
Definition eval_entry_deps (e : eval_entry) : gdeps := view_deps (eval_entry_view e).
(** The Core stack an entry stands for, for types only *)
Definition eval_entry_stack (e : eval_entry) : gstack := decode_stack (eval_entry_frames e).

Record eval_ok (e : eval_entry) : Prop := mk_eval_ok
  { eval_ok_wf : ⊢ᵍ eval_entry_deps e ⍮ eval_entry_stack e
  ; eval_ok_typ : eval_entry_deps e ⍮ eval_entry_stack e ⍮ gs_tele (eval_entry_stack e) ⊢ eval_entry_exp e : eval_entry_typ e
  ; eval_ok_nbe : nbe (eval_entry_deps e) (eval_entry_stack e) (gs_tele (eval_entry_stack e)) (eval_entry_exp e) (eval_entry_typ e) (eval_entry_nf e) }.

Definition logs_ok (l : list eval_entry) : Prop := forall e, In e l -> eval_ok e.

(** The log of a run, in program order, with every entry certified. *)
Definition certified_log : Type := {l | logs_ok l}.

Definition log_nil : certified_log := exist logs_ok nil (fun e (H : In e nil) => False_ind _ H).

Definition log_app (l1 l2 : certified_log) : certified_log.
Proof.
  refine (exist _ (List.app (proj1_sig l1) (proj1_sig l2)) _).
  abstract (intros e He; apply in_app_or in He as [He | He]; [ exact (proj2_sig l1 _ He) | exact (proj2_sig l2 _ He) ]).
Defined.

Lemma typed_nbe_order {Θ Ξ Γ M A} : Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> nbe_order Θ Ξ Γ M A.
Proof. intros H; destruct (soundness H) as (W & HW & _); exact (nbe_order_sound _ _ _ _ _ _ HW). Qed.

(** Whether a term of a normal type is a type former of an inductive type
    ([ind_former]): its normal form at the variables of the type's
    domains, computed once, is decisive, since normal forms are unique. *)
Definition ind_former_dec (F : FCtx) (Γ : ctx) (M : exp) (W : nf)
    (HM : fc_deps F ⍮ fc_stack F ⍮ Γ ⊢ M : nf_to_exp W) :
    {ind_former (fc_deps F) (fc_stack F) Γ M W} + {~ ind_former (fc_deps F) (fc_stack F) Γ M W}.
Proof.
  unfold ind_former.
  destruct (nf_pi_tele W) as [Ds C] eqn:Ep.
  destruct (nf_is_universe_dec C) as [Hu | Hu]; [| right; intros [Hu' _]; contradiction ].
  destruct (nbe_impl F (Ds ++ Γ) (exp_applied_to_vars M (List.length Ds)) (nf_to_exp C)
              (typed_nbe_order (applied_vars_typed _ _ _ _ _ _ _ HM Ep))) as [W' HW'].
  destruct W';
    try (right; intros (_ & p0 & k0 & Rs0 & Hn); pose proof (functional_nbe _ _ _ _ _ HW' Hn) as E; discriminate E).
  left; split; [ exact Hu | do 3 eexists; exact HW' ].
Defined.

(** Likewise of a record type ([record_former]). *)
Definition record_former_dec (F : FCtx) (Γ : ctx) (M : exp) (W : nf)
    (HM : fc_deps F ⍮ fc_stack F ⍮ Γ ⊢ M : nf_to_exp W) :
    {record_former (fc_deps F) (fc_stack F) Γ M W} + {~ record_former (fc_deps F) (fc_stack F) Γ M W}.
Proof.
  unfold record_former.
  destruct (nf_pi_tele W) as [Ds C] eqn:Ep.
  destruct (nf_is_universe_dec C) as [Hu | Hu]; [| right; intros [Hu' _]; contradiction ].
  destruct (nbe_impl F (Ds ++ Γ) (exp_applied_to_vars M (List.length Ds)) (nf_to_exp C)
              (typed_nbe_order (applied_vars_typed _ _ _ _ _ _ _ HM Ep))) as [W' HW'].
  destruct W';
    try (right; intros (_ & p0 & Rs0 & Hn); pose proof (functional_nbe _ _ _ _ _ HW' Hn) as E; discriminate E).
  left; split; [ exact Hu | do 2 eexists; exact HW' ].
Defined.

(** Normalize a checked [eval] into its entry. *)
Lemma eval_log_ok {F M A W} : ⊢ᵍ fc_deps F ⍮ fc_stack F -> fc_deps F ⍮ fc_stack F ⍮ fc_tele F ⊢ M : A ->
  nbe (fc_deps F) (fc_stack F) (fc_tele F) M A W ->
  logs_ok ({| eval_entry_view := fc_view F; eval_entry_frames := fc_frames F; eval_entry_exp := M; eval_entry_typ := A;
              eval_entry_nf := W |} :: nil).
Proof.
  intros HΞ HM HW e [<- | []]; rewrite <- (fc_tele_ok F) in HM, HW.
  constructor; unfold eval_entry_deps, eval_entry_stack; cbn [eval_entry_view eval_entry_frames eval_entry_exp eval_entry_typ eval_entry_nf];
    rewrite <- fc_deps_view, <- fc_stack_frames; assumption.
Qed.

(** The entry of a checked [eval], normalized at the fast context [F] *)
Definition eval_log (F : FCtx) (HΞ : ⊢ᵍ fc_deps F ⍮ fc_stack F) (M : exp) (A : typ)
  (HM : fc_deps F ⍮ fc_stack F ⍮ fc_tele F ⊢ M : A) : certified_log :=
  match nbe_impl F (fc_tele F) M A (typed_nbe_order HM) with
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

(** A type inferred algorithmically moves along an equivalence to
    well-formed dependencies. *)
Lemma equiv_alg_infer : forall Θ Θ' Ξ Γ W M, gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ ->
    @alg_type_infer (gc_mk Θ Ξ) Γ W M -> @alg_type_infer (gc_mk Θ' Ξ) Γ W M.
Proof. intros * He Hg; exact (proj1 (proj2 (equiv_alg_all _ _ _ He Hg)) _ _ _). Qed.

(** Parameters of evaluated kinds stay so along an equivalence. *)
Lemma equiv_params_evaluated : forall Θ Θ' Ξ Γ Δ l, gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ ->
    params_evaluated Θ Ξ Γ Δ l -> params_evaluated Θ' Ξ Γ Δ l.
Proof.
  intros * He HΞ HR Δ1 κ T Δ2 E; destruct (HR _ _ _ _ E) as [H | H]; [ left | right ]; exact (equiv_exp _ _ _ _ _ _ He HΞ H).
Qed.

(** A member of a group well formed as an entry has uniform parameters of
    its own of evaluated kinds, over the frames' parameters: by the
    premise of its rule, or by (R) of its module. *)
Lemma ind_entry_params_evaluated : forall Θ Ξ mp pv pq k D Φ Δu,
    Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_ind pv pq k D Φ -> ind_uparams D = (Δu ++ gs_tele Ξ)%list ->
    exists l, params_evaluated Θ Ξ (gs_tele Ξ) Δu l.
Proof.
  intros * HE; revert Δu; inversion HE; subst; intros Δu' Hu.
  all: match goal with HU : ind_uparams ?D0 = (?Δ0 ++ gs_tele _)%list |- _ =>
         assert_fails constr_eq Δ0 Δu'; rewrite Hu in HU; apply app_inv_tail in HU; subst Δ0 end.
  all: try solve [ eexists; eapply params_evaluated_of_sorts; eassumption | eexists; eassumption ].
  match goal with HΦ : _ ⍮ _ ⍮ _ ⍮ fk_ind _ _ _ ⍮ _ ⊢ᵍᵐ _ |- _ =>
    destruct (wf_gmod_params_evaluated _ _ _ _ _ _ HΦ) as [l Hl]; exists l; exact Hl end.
Qed.

(** The uniform parameters of a member of a group just filed in the
    innermost frame are of evaluated kinds there: the entry is well formed
    in the frame before it ([wf_gmod_ext]). *)
Lemma added_ind_params_evaluated : forall Θ Ξ x pv pq k Dd Φx Δu,
    gs_fresh x Ξ -> ⊢ᵍ Θ ⍮ gs_add x (ge_ind pv pq k Dd Φx) Ξ -> ind_uparams Dd = (Δu ++ gs_tele Ξ)%list ->
    exists l, params_evaluated Θ (gs_add x (ge_ind pv pq k Dd Φx) Ξ) (gs_tele (gs_add x (ge_ind pv pq k Dd Φx) Ξ)) Δu l.
Proof.
  intros * Hfr Hg Hu.
  destruct Ξ as [| [[mq Kq] U] Ξ0]; [ contradiction |]; cbn [gs_add] in Hg |- *.
  destruct (wf_gstack_cons_inv _ _ _ _ _ Hg) as (Hg0 & HU & Hff).
  pose proof (wf_gunit_mod _ _ _ _ _ HU) as HΦ; cbn [gu_mod gu_params] in HΦ.
  inversion HΦ; subst.
  (** the frame before the entry, where it is well formed *)
  assert (HgU : ⊢ᵍ Θ ⍮ (mq, Kq, gu_body (gu_params U) (gu_mod U)) :: Ξ0)
    by (apply wf_gstack_cons; [ exact Hg0 | eassumption | exact Hff ]).
  match goal with HE : _ ⍮ _ ⍮ _ ⊢ᵉ ge_ind _ _ _ _ _ |- _ =>
    destruct (ind_entry_params_evaluated _ _ _ _ _ _ _ _ _ HE Hu) as [l Hl] end.
  exists l.
  exact (params_evaluated_embed _ _ _ _ _ _ _ (Build_gctx_embedding _ _ _ _ Hg (gc_sub_add _ _ x (ge_ind pv pq k Dd Φx) HgU Hfr)) Hl).
Qed.

(** ** Mutual Definitions *)

(** [mdef_why], [mdef_member_dec] and [mdef_members_dec] are in
    [MdefGroup], with the group's decision ([mdef_group_dec]). *)

(** Why a definition of a mutual definition is not filed: its name is not
    fresh, or its term is not of its type. *)
Inductive mdefs_why : Type :=
(** The name, taken *)
| mdefs_why_dup : string -> mdefs_why
(** The name, the stack and the type, which is no type *)
| mdefs_why_untyped_type : string -> fstack -> typ -> mdefs_why
(** The name, the stack, the type and the term *)
| mdefs_why_untyped : string -> fstack -> typ -> exp -> mdefs_why.

(** A definition filed, its frames wf: the frames, read in Core, kept
    canonical. *)
Lemma add_def_canon : forall Θ Ξ x b pv r A M, ⊢ᵍ Θ ⍮ gs_add x (gs_def b pv r Ξ A M) Ξ ->
    canon_stack (gs_add x (gs_def b pv r Ξ A M) Ξ).
Proof. intros * H; exact (proj2 (canon_of_wf _ _ H)). Qed.

(** ** Values Stored at Definitions

    A transparent definition of a type of a universe is filed with the
    value its body has, fast, in the empty environment ([closed_value]).
    The evaluation of a closed term of such a type in the empty context
    has an order: the term has a normal form ([soundness]), which reads
    its value. *)
Lemma closed_eval_order {Θ Ξ M A} : (exists i : nat, Θ ⍮ Ξ ⍮ nil ⊢ A : Typeω@i) -> Θ ⍮ Ξ ⍮ nil ⊢ M : A ->
    Mctt.Extraction.Evaluation.eval_exp_order Θ Ξ M nil.
Proof.
  intros [i HA] HM; destruct (soundness HM) as (W & [ρ a Hρ Ea Ht] & _).
  destruct Ht as [w Hp _ | m w _ Em _]; [| inversion Hρ; subst; exact (Mctt.Extraction.Evaluation.eval_exp_order_sound _ _ _ _ _ Em) ].
  (** a term of a type of a large universe is no proof *)
  exfalso.
  destruct (@typed_at_sort_of_initial_kind (gc_mk Θ Ξ) _ _ _ _ _ (type_sort_universe i) HA Hρ Ea) as [k Hk].
  rewrite Hp in Hk.
  pose proof (@kind_sort_unique (gc_mk Θ Ξ) nil A ak_propositional ak_relevant k i Hk HA) as E; discriminate E.
Qed.

(** The value a closed term of a type of a large universe has, fast, in
    the empty environment *)
Definition closed_value (F : FCtx) (M : exp) (A : typ) (HA : exists i : nat, fc_deps F ⍮ fc_stack F ⍮ nil ⊢ A : Typeω@i)
    (HM : fc_deps F ⍮ fc_stack F ⍮ nil ⊢ M : A) :
    { v | value_ok (fc_deps F) (fc_stack F) M v } :=
  let (v, Hv) := Mctt.Extraction.Evaluation.fast_eval_exp_impl F M nil (Forall_nil _) (closed_eval_order HA HM) in
  exist _ v (mk_value_ok _ _ _ _ (proj1 Hv) (proj2 Hv)).

(** A term of a type of a large universe typed under a telescope, closed
    over it *)
Lemma under_typed {Θ Ξ Δ Γ M A} {i : nat} : Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Typeω@i -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ ctx_fn Δ M : ctx_pi Δ A /\ exists j : nat, Θ ⍮ Ξ ⍮ Γ ⊢ ctx_pi Δ A : Typeω@j.
Proof.
  intros HA HM; split;
    [ exact (ctx_fn_at_wf _ _ ak_relevant _ _ _ _ _ ltac:(discriminate) (presup_exp_ctx HM) HA HM)
    | exact (ctx_pi_at_wf _ _ ak_relevant _ _ _ _ ltac:(discriminate) (presup_exp_ctx HM) HA) ].
Qed.

Lemma closed_typed {Θ Ξ Γ M A} {i : nat} : Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ nil ⊢ ctx_fn Γ M : ctx_pi Γ A /\ exists j : nat, Θ ⍮ Ξ ⍮ nil ⊢ ctx_pi Γ A : Typeω@j.
Proof. intros HA HM; rewrite <- (app_nil_r Γ) in HA, HM; exact (under_typed HA HM). Qed.

(** "Is [A] a type of a large universe?", the level found: the sort its
    type infers ([check_type]) is a universe.  None at another kind, since
    a type is of one kind only ([kind_sort_unique]): [n = 0] is no type
    of a universe. *)
Definition large_type_dec (F : FCtx)
    (levels_abstractable_dec : forall G Δ E, ⊢ fc_deps F ⍮ fc_stack F ⍮ Δ ++ G ->
       { levels_abstractable (fc_deps F) (fc_stack F) G Δ E } + { ~ levels_abstractable (fc_deps F) (fc_stack F) G Δ E })
    (Γ : ctx) (HΓ : ⊢ fc_deps F ⍮ fc_stack F ⍮ Γ) (A : typ) :
    { i : nat | fc_deps F ⍮ fc_stack F ⍮ Γ ⊢ A : Typeω@i } + { forall i : nat, ~ fc_deps F ⍮ fc_stack F ⍮ Γ ⊢ A : Typeω@i }.
Proof.
  destruct (check_type F levels_abstractable_dec Γ HΓ A) as [(r & i & HA) | HnA].
  - destruct (abs_kind_eq_dec r ak_relevant) as [-> | Hr]; [ left; exists i; exact HA |].
    right; intros j Hj; apply Hr.
    exact (@kind_sort_unique (fc_gctx F) Γ A r ak_relevant i j ltac:(rewrite fc_gctx_eta; exact HA) ltac:(rewrite fc_gctx_eta; exact Hj)).
  - right; intros j Hj; exact (HnA ak_relevant j Hj).
Defined.

(** The fast entry of a definition [A ≔ M] of the kind [κ] in the
    innermost frame of [F]: a transparent one of a type of a universe
    stores the value of its body, closed over the frames' parameters; any
    other stores none, which a lookup evaluates when it needs it *)
Definition def_fentry (F : FCtx) (b pv : bool) (κ : abs_kind) (i : nat) (A M : exp)
    (HA : fc_deps F ⍮ fc_stack F ⍮ fc_tele F ⊢ A : abs_kind_sort κ Typeω@i) (HM : fc_deps F ⍮ fc_stack F ⍮ fc_tele F ⊢ M : A) :
    { e : fentry | fentry_drop e = translate_entry (fs_def b pv κ (fc_frames F) A M) /\ fentry_values_ok (fc_deps F) (fc_stack F) e } :=
  match b as b0, κ as κ0
    return fc_deps F ⍮ fc_stack F ⍮ fc_tele F ⊢ A : abs_kind_sort κ0 Typeω@i ->
      { e : fentry | fentry_drop e = translate_entry (fs_def b0 pv κ0 (fc_frames F) A M) /\ fentry_values_ok (fc_deps F) (fc_stack F) e } with
  | true, ak_relevant => fun HA =>
      let (v, Hv) := closed_value F (ctx_fn (fc_tele F) M) (ctx_pi (fc_tele F) A) (proj2 (closed_typed HA HM)) (proj1 (closed_typed HA HM)) in
      exist _ (fe_def true pv ak_relevant (ctx_pi (fc_tele F) A) (Some (ctx_fn (fc_tele F) M)) (Some v)) (conj eq_refl Hv)
  | b0, κ0 => fun _ =>
      exist _ (translate_entry (fs_def b0 pv κ0 (fc_frames F) A M)) (conj (translate_entry_drop _) (translate_entry_values _ _ _))
  end HA.

(** The fast entry of a definition with a module part [A ≔ M ‖ E] under
    [Δ], in the innermost frame of [F]: it stores the value of its term,
    closed over [Δ] and the frames' parameters *)
Lemma closed_under_typed {Θ Ξ Δ Γ M A} {i : nat} : Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Typeω@i -> Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ nil ⊢ ctx_fn Γ (ctx_fn Δ M) : ctx_pi Γ (ctx_pi Δ A) /\ exists j : nat, Θ ⍮ Ξ ⍮ nil ⊢ ctx_pi Γ (ctx_pi Δ A) : Typeω@j.
Proof. intros HA HM; destruct (under_typed HA HM) as [HM' [j HA']]; exact (closed_typed HA' HM'). Qed.

Definition dm_fentry (F : FCtx) (pv : bool) (Δ : ctx) (i : nat) (A M : exp) (E : modexp)
    (HA : fc_deps F ⍮ fc_stack F ⍮ Δ ++ fc_tele F ⊢ A : Typeω@i) (HM : fc_deps F ⍮ fc_stack F ⍮ Δ ++ fc_tele F ⊢ M : A) :
    { e : fentry | fentry_drop e = translate_entry (fs_dm_entry (fc_frames F) pv Δ A M E) /\ fentry_values_ok (fc_deps F) (fc_stack F) e } :=
  let (v, Hv) := closed_value F (ctx_fn (fc_tele F) (ctx_fn Δ M)) (ctx_pi (fc_tele F) (ctx_pi Δ A))
                   (proj2 (closed_under_typed HA HM)) (proj1 (closed_under_typed HA HM)) in
  exist _ (fe_def_mod pv (ctx_pi (fc_tele F) (ctx_pi Δ A)) (ctx_fn (fc_tele F) (ctx_fn Δ M)) (translate_unit (gu_mk (Δ ++ fc_tele F) (md_alias E))) (Some v))
    (conj (f_equal (fun u => fe_def_mod pv (ctx_pi (fc_tele F) (ctx_pi Δ A)) (ctx_fn (fc_tele F) (ctx_fn Δ M)) u None)
             (translate_unit_drop (gu_mk (Δ ++ fc_tele F) (md_alias E))))
       (conj Hv (translate_unit_values (fc_deps F) (fc_stack F) (gu_mk (Δ ++ fc_tele F) (md_alias E))))).

(** The frames [fs'] the definitions [ds] end with, filed on the frames
    [fs] of the units seen [v] *)
Record mdefs_filed (v : fview) (b pv : bool) (ds : list (string * typ * exp)) (fs fs' : fstack) : Prop := mk_mdefs_filed
  { (** they are a fast context, with the units seen *)
    mf_ok : fctx_ok v fs'
    (** their values are right where each frame is open *)
  ; mf_values : frames_values_ok (view_deps v) fs'
    (** they are those [mdefs_run] ends with *)
  ; mf_run : mdefs_run (view_deps v) b pv ds (decode_stack fs) (decode_stack fs') }.

(** The definitions filed in order, each checked as [run_cmd_def] does, on
    the frames [fs] of the units seen [v], fast: the frames they end with,
    and that they are those [mdefs_run] ends with. *)
Fixpoint mdefs_dec (lvd : levels_abstractable_decider) (v : fview) (b pv : bool) (ds : list (string * typ * exp)) (fs : fstack)
    (Hok : fctx_ok v fs) (HΞ : ⊢ᵍ view_deps v ⍮ decode_stack fs) (Hv : frames_values_ok (view_deps v) fs) {struct ds} :
    ({fs' : fstack | mdefs_filed v b pv ds fs fs'}
     + {e : mdefs_why | forall Ξ', ~ mdefs_run (view_deps v) b pv ds (decode_stack fs) Ξ'})%type.
Proof.
  pose (F := mk_fctx v fs Hok None).
  assert (HΞF : ⊢ᵍ fc_deps F ⍮ fc_stack F) by (rewrite fc_deps_view, fc_stack_frames; exact HΞ).
  destruct ds as [| [[x A] M] ds'].
  - left; exists fs; constructor; [ exact Hok | exact Hv | constructor ].
  - destruct (fctx_ok_frames _ _ Hok) as [Hr Hc].
    destruct (fs_fresh_sum x fs Hr Hc) as [Hfr | Hn];
      [| right; exists (mdefs_why_dup x); intros Ξ' Hr'; inversion Hr'; subst; contradiction ].
    (** the judgments at [F] are those at the Core stack *)
    assert (Eqs : fc_deps F = view_deps v /\ fc_stack F = decode_stack fs /\ fc_tele F = gs_tele (decode_stack fs))
      by (unfold F; rewrite fc_deps_view, fc_stack_frames, <- (fc_tele_ok (mk_fctx v fs Hok None)), fc_stack_frames;
          cbn [fc_view fc_frames]; repeat split).
    destruct Eqs as (Ed & Es & Et).
    destruct (check_ctx F (lvd _ _) HΞF (fc_tele F)) as [HT | HnT].
    2:{ right; exists (mdefs_why_untyped_type x fs A); intros Ξ' Hr'; inversion Hr'; subst; apply HnT.
        rewrite Ed, Es, Et; gen_presups; assumption. }
    destruct (large_type_dec F (lvd _ _) (fc_tele F) HT A) as [[i HA] | HnA].
    2:{ right; exists (mdefs_why_untyped_type x fs A); intros Ξ' Hr'; inversion Hr'; subst.
        match goal with HA0 : _ ⍮ _ ⍮ _ ⊢ A : Typeω@?i0 |- _ => apply (HnA i0); rewrite Ed, Es, Et; exact HA0 end. }
    destruct (check_exp_typed F (lvd _ _) (fc_tele F) HT A (type_of_check_type F _ _ ak_relevant i HA) M) as [HM | Hn].
    2:{ right; exists (mdefs_why_untyped x fs A M); intros Ξ' Hr'; inversion Hr'; subst; apply Hn.
        rewrite Ed, Es, Et; assumption. }
    pose proof HA as HAF; rewrite Ed, Es, Et in HA.
    assert (HM' : view_deps v ⍮ decode_stack fs ⍮ gs_tele (decode_stack fs) ⊢ M : A) by (rewrite <- Et, <- Ed, <- Es; exact HM).
    pose proof (add_def_wf _ _ _ b pv ak_relevant _ _ _ HΞ HA ltac:(intros [=]) HM' Hfr) as HΞ'.
    pose proof (add_def_canon _ _ _ _ _ _ _ _ HΞ') as HcΞ'.
    rewrite <- fs_def_dec in HΞ', HcΞ'.
    destruct (def_fentry F b pv ak_relevant i A M HAF HM) as [e0 [Hd Hev]].
    change (fentry_drop e0 = translate_entry (fs_def b pv ak_relevant fs A M)) in Hd.
    assert (Hev' : fentry_values_ok (view_deps v) (decode_stack fs) e0)
      by (unfold F in Hev; rewrite fc_deps_view, fc_stack_frames in Hev; exact Hev).
    destruct (mdefs_dec lvd v b pv ds' (fs_add x e0 fs)
                (fctx_ok_add _ _ _ _ _ Hok Hd HcΞ' (gc_sub_add _ _ _ _ HΞ Hfr) HΞ HΞ'
                   (fentry_values_grow _ _ _ _ (gc_sub_add _ _ _ _ HΞ Hfr) HΞ HΞ' _ Hev'))
                (eq_ind_r (fun Ξ0 => ⊢ᵍ view_deps v ⍮ Ξ0) HΞ' (decode_stack_add _ _ _ _ Hr Hd HcΞ'))
                (frames_values_add_before _ _ _ _ _ HΞ HΞ' Hv (decode_stack_add _ _ _ _ Hr Hd HcΞ') Hev'))
      as [[fs' [Hok' Hv' Hr']] | [e Hn]].
    + left; exists fs'; constructor; [ exact Hok' | exact Hv' |].
      rewrite (decode_stack_add _ _ _ _ Hr Hd HcΞ'), fs_def_dec in Hr'.
      econstructor; eassumption.
    + right; exists e; intros Ξ' Hr'; inversion Hr'; subst; eapply Hn.
      rewrite (decode_stack_add _ _ _ _ Hr Hd HcΞ'), fs_def_dec; eassumption.
Defined.

(** Filing the definitions alike along an equivalence. *)
Lemma equiv_mdefs_run : forall Θ Θ' b pv ds Ξ Ξ', gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ ->
    mdefs_run Θ b pv ds Ξ Ξ' -> mdefs_run Θ' b pv ds Ξ Ξ'.
Proof.
  intros * He HΞ Hr; revert HΞ; induction Hr as [| x A M i ds Ξ Ξ' HA HM Hfr _ IH]; intros HΞ; [ constructor |].
  pose proof (equiv_exp _ _ _ _ _ _ He HΞ HM) as HM'.
  pose proof (equiv_exp _ _ _ _ _ _ He HΞ HA) as HA'.
  econstructor; [ exact HA' | exact HM' | exact Hfr |].
  apply IH; eapply (add_def_wf _ _ _ b pv ak_relevant); [ exact HΞ | exact HA' | intros [=] | exact HM' | exact Hfr ].
Qed.

(** What a command's checks look names up in ([Extraction.Lookup]) is
    [fctx_cmd] ([Extraction.FastState]): the units seen and the frames,
    fast, and the declaration of the type bound as the natural numbers,
    looked up once per check rather than once per eliminator. *)

(** ** Filing a Group, Through the Filed Units

    [raw_decl_filed] with its lookups through an [FCtx]: what the checker
    computes, equal to [raw_decl_filed] ([raw_decl_filed_f_ok]). *)

Section FiledThroughUnits.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  (** [raw_view_filed], its container and record found through [F]. *)
  Definition raw_view_filed_f (σ : sub) (n : nat) (Ks : list view_key) (x : view_key) (ss : list view_key)
      (cs : list (string * list classified_carg)) (Nv : ctx) : option imember :=
    match x with
    | vk_ind qc k Cs =>
        let Is := List.map (fun C => C[σ]) Cs in
        match fc_ind F qc with
        | Some D' =>
            match ind_member D' k, classified_cons_num n Ks cs with
            | Some _, Some cs' =>
                Some (mk_imember
                        (mh_view qc k Is (List.map (fun s => n + match view_key_index s Ks with Some v => v | None => 0 end) ss))
                        Nv cs')
            | _, _ => None
            end
        | None => None
        end
    | vk_record qr Cs =>
        match fc_record F qr, classified_cons_num n Ks cs with
        | Some Rr, Some cs' =>
            Some (mk_imember (mh_record qr (List.map (fun C => C[σ]) Cs) (List.map fst (record_fields Rr))) Nv cs')
        | _, _ => None
        end
    end.

  Lemma raw_view_filed_f_ok : forall σ n Ks x ss cs Nv, raw_view_filed_f σ n Ks x ss cs Nv = raw_view_filed Θ Ξ σ n Ks x ss cs Nv.
  Proof.
    intros; destruct x as [qc k Cs | qr Is]; unfold raw_view_filed_f, raw_view_filed; [ rewrite fc_ind_ok | rewrite fc_record_ok ]; reflexivity.
  Qed.

  (** [raw_views_filed] through [raw_view_filed_f]. *)
  Fixpoint raw_views_filed_f (σ : sub) (n : nat) (Ks xs Vs : list view_key) (Ss : list (list view_key))
      (css : list (list (string * list classified_carg))) (Nvs : list ctx) : option (list imember) :=
    match xs with
    | nil => Some nil
    | x :: xs' =>
        match view_key_index x Vs with
        | Some v =>
            match raw_view_filed_f σ n Ks x (List.nth v Ss nil) (List.nth v css nil) (List.nth v Nvs nil),
                  raw_views_filed_f σ n Ks xs' Vs Ss css Nvs with
            | Some M, Some Ms => Some (M :: Ms)
            | _, _ => None
            end
        | None => None
        end
    end.

  Lemma raw_views_filed_f_ok : forall σ n Ks xs Vs Ss css Nvs,
      raw_views_filed_f σ n Ks xs Vs Ss css Nvs = raw_views_filed Θ Ξ σ n Ks xs Vs Ss css Nvs.
  Proof.
    induction xs as [| x xs IH]; intros; cbn [raw_views_filed_f raw_views_filed]; [ reflexivity |].
    destruct (view_key_index x Vs); [ rewrite raw_view_filed_f_ok, IH |]; reflexivity.
  Qed.

  (** [raw_decl_filed] through [raw_views_filed_f]. *)
  Definition raw_decl_filed_f (R : raw_decl) (Vs : list view_key) (Ss : list (list view_key))
      (csD csV : list (list (string * list classified_carg))) (Nvs : list ctx) : option ind_decl :=
    match raw_decl_members R with
    | Mr0 :: _ =>
        let σ := sb_selfs (fs_ind_qname (fc_frames F) (raw_member_name Mr0)) (raw_decl_nu R) (raw_decl_nmembers R) (List.length (fc_tele F)) in
        let Ks := filed_keys (meets_table Vs csV) Vs in
        match raw_members_filed_f (fc_frames F) (raw_decl_nmembers R) Ks (raw_decl_members R) csD, raw_views_filed_f σ (raw_decl_nmembers R) Ks Ks Vs Ss csV Nvs with
        | Some Ms, Some Mv => Some (mk_ind (raw_decl_uparams R ++ fc_tele F) (raw_member_sort Mr0) (Ms ++ Mv))
        | _, _ => None
        end
    | nil => None
    end.

  Lemma raw_decl_filed_f_ok : forall R Vs Ss csD csV Nvs, raw_decl_filed_f R Vs Ss csD csV Nvs = raw_decl_filed Θ Ξ R Vs Ss csD csV Nvs.
  Proof.
    intros; unfold raw_decl_filed_f, raw_decl_filed; destruct (raw_decl_members R); [ reflexivity |].
    rewrite raw_views_filed_f_ok, raw_members_filed_f_dec, fs_ind_qname_dec, <- fc_tele_ok, <- fc_stack_frames; reflexivity.
  Qed.

  (** The filed group, or that there is none, computed by [raw_decl_filed_f]. *)
  Definition raw_decl_filed_case (R : raw_decl) (Vs : list view_key) (Ss : list (list view_key))
      (csD csV : list (list (string * list classified_carg))) (Nvs : list ctx) :
      {Dd | raw_decl_filed Θ Ξ R Vs Ss csD csV Nvs = Some Dd} + {raw_decl_filed Θ Ξ R Vs Ss csD csV Nvs = None} :=
    match opt_case (raw_decl_filed_f R Vs Ss csD csV Nvs) with
    | inleft (exist _ Dd E) => inleft (exist _ Dd (eq_trans (eq_sym (raw_decl_filed_f_ok R Vs Ss csD csV Nvs)) E))
    | inright E => inright (eq_trans (eq_sym (raw_decl_filed_f_ok R Vs Ss csD csV Nvs)) E)
    end.
End FiledThroughUnits.

(** ** The Views of a Group *)

(** The views [Vs] of the declaration [R] whose declared members'
    constructors classify as [csD], with what [run_cmd_ind_case] asks of them. *)
Record views_ok (Θ : gdeps) (Ξ : gstack) (R : raw_decl) (csD : list (list (string * list classified_carg)))
    (Vs : list view_key) (Ss : list (list view_key)) (csV : list (list (string * list classified_carg))) (Nvs : list ctx) : Prop :=
  mk_views_ok
  { (** each view's siblings *)
    views_siblings : Forall2 (view_siblings Θ Ξ R) Vs Ss;
    (** each view's constructors, classified *)
    views_classified : Forall2 (view_classify Θ Ξ R) Vs csV;
    (** each view's non-uniform parameters, filed *)
    views_nparams : Forall2 (view_nparams Θ Ξ R) Vs Nvs;
    (** the views, found from the instances met *)
    views_search_run : views_dfs (siblings_table Vs Ss) (meets_table Vs csV) nil (List.concat (List.map classified_cons_views csD)) Vs }.

(** The views found, with their tables. *)
Definition views_found (Θ : gdeps) (Ξ : gstack) (R : raw_decl) (csD : list (list (string * list classified_carg))) : Type :=
  {Vs : list view_key & {Ss : list (list view_key) & {csV : list (list (string * list classified_carg)) &
     {Nvs : list ctx | views_ok Θ Ξ R csD Vs Ss csV Nvs}}}}.

(** The views alike along an equivalence. *)
Lemma equiv_views_ok : forall Θ Θ' Ξ R csD Vs Ss csV Nvs, gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ ->
    views_ok Θ Ξ R csD Vs Ss csV Nvs -> views_ok Θ' Ξ R csD Vs Ss csV Nvs.
Proof.
  intros * He HΞ [Hs Hc Hn Hb]; constructor; [| | | exact Hb ].
  - eapply Forall2_impl; [ intros x ss; apply (equiv_view_siblings _ _ _ He HΞ) | exact Hs ].
  - eapply Forall2_impl; [ intros x cs; apply (equiv_view_classify _ _ _ He HΞ) | exact Hc ].
  - eapply Forall2_impl; [ intros x Nv; apply (equiv_view_nparams _ _ _ He HΞ) | exact Hn ].
Qed.

(** The views of a group are found in one way. *)
Lemma views_ok_functional : forall Θ Ξ R csD Vs Ss csV Nvs Vs' Ss' csV' Nvs',
    views_ok Θ Ξ R csD Vs Ss csV Nvs -> views_ok Θ Ξ R csD Vs' Ss' csV' Nvs' ->
    Vs = Vs' /\ Ss = Ss' /\ csV = csV' /\ Nvs = Nvs'.
Proof.
  intros * [Hs Hv Hn Hb] [Hs' Hv' Hn' Hb'].
  assert (Agree : forall x, In x Vs -> In x Vs' -> siblings_table Vs Ss x = siblings_table Vs' Ss' x /\ meets_table Vs csV x = meets_table Vs' csV' x).
  { intros x Hx Hx'.
    destruct (view_key_index_in_some _ _ Hx) as [v Hvi]; destruct (view_key_index_in_some _ _ Hx') as [v' Hvi'].
    unfold siblings_table, meets_table; rewrite Hvi, Hvi'; split.
    - eapply view_siblings_functional; eapply Forall2_index; eassumption.
    - f_equal; eapply view_classify_functional; eapply Forall2_index; eassumption. }
  pose proof (views_dfs_functional _ _ _ _ _ Hb _ _ _ Hb' Agree) as <-.
  split; [ reflexivity |].
  split; [ eapply Forall2_functional; [ exact (view_siblings_functional Θ Ξ R) | exact Hs | exact Hs' ] |].
  split; [ eapply Forall2_functional; [ exact (view_classify_functional Θ Ξ R) | exact Hv | exact Hv' ] |].
  eapply Forall2_functional; [ exact (view_nparams_functional Θ Ξ R) | exact Hn | exact Hn' ].
Qed.
