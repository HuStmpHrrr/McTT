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

    Each command gets its literals ([Builtin]) and runs as written: the
    local opens of its bodies are checked where they stand.

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
From Mctt.Core.Syntactic.System.Inductives Require Import Rec.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf Paths LookupSound.
From Mctt.Extraction Require Import Lookup NbE TypeCheck GlobalCheck IndDecl MemberType Opens Privacy.
Import Syntax_Notations GlobalCtx_Notations.

Local Open Scope string_scope.

(** ** Deciders *)

Definition opt_case {A} (o : option A) : {a | o = Some a} + {o = None} :=
  match o as o0 return {a | o0 = Some a} + {o0 = None} with
  | Some a => inleft (exist _ a eq_refl)
  | None => inright eq_refl
  end.

Definition list_case {A} (l : list A) : {x : A & {l' | l = x :: l'}} + {l = nil} :=
  match l as l0 return {x : A & {l' | l0 = x :: l'}} + {l0 = nil} with
  | x :: l' => inleft (existT _ x (exist _ l' eq_refl))
  | nil => inright eq_refl
  end.

Definition gs_fresh_dec (x : string) (Ξ : gstack) : {gs_fresh x Ξ} + {~ gs_fresh x Ξ} :=
  match Ξ as Ξ0 return {gs_fresh x Ξ0} + {~ gs_fresh x Ξ0} with
  | (_, U) :: _ => check_gm_fresh x (gu_mod U)
  | nil => right (fun H => H)
  end.

(** An inductive alias entry: its premises, the telescope as written. *)
Lemma wf_gentry_ind_alias_inv : forall Θ Ξ mp pv Δ p Ns,
    Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns ->
    tele_ass Δ /\ Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ /\
    exists D, ind_lookup Θ Ξ p = Some D /\ List.length Ns <= ind_nu D /\
      Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ apps (a_ind p) Ns : ind_ty_at D Ns /\
      Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ me_apps (qname_mod p) Ns ≈ me_apps (qname_mod p) Ns.
Proof.
  intros * HE; inversion HE; subst.
  match goal with Heq : (?Δ0 ++ gs_tele Ξ)%list = (Δ ++ gs_tele Ξ)%list |- _ => apply List.app_inv_tail in Heq as -> end.
  split; [ assumption | split; [ assumption | eexists; repeat split; eassumption ] ].
Qed.

(** An inductive alias entry, decided premise by premise. *)
Definition ind_alias_entry_dec (Θ : gdeps) (Ξ : gstack) (HΞ : ⊢ᵍ Θ ⍮ Ξ) (mp : qname) (pv : bool) (Δ : ctx) (p : qname) (Ns : list exp) :
    { Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns } + { ~ Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns }.
Proof.
  destruct (tele_ass_dec Δ) as [Htel | Hn]; [| right; intros HE; exact (Hn (proj1 (wf_gentry_ind_alias_inv _ _ _ _ _ _ _ HE))) ].
  destruct (check_ext fctx_none Θ Ξ (gs_tele Ξ) (wf_gs_tele _ _ HΞ) Δ) as [HΔ | Hn];
    [| right; intros HE; exact (Hn (proj1 (proj2 (wf_gentry_ind_alias_inv _ _ _ _ _ _ _ HE)))) ].
  destruct (ind_lookup Θ Ξ p) as [D |] eqn:Hl;
    [| right; intros HE; destruct (proj2 (proj2 (wf_gentry_ind_alias_inv _ _ _ _ _ _ _ HE))) as (D & Hl' & _); congruence ].
  destruct (Compare_dec.le_dec (List.length Ns) (ind_nu D)) as [Hle | Hn];
    [| right; intros HE; destruct (proj2 (proj2 (wf_gentry_ind_alias_inv _ _ _ _ _ _ _ HE))) as (D' & Hl' & Hle' & _);
       rewrite Hl in Hl'; injection Hl' as <-; exact (Hn Hle') ].
  destruct (check_exp fctx_none Θ Ξ (Δ ++ gs_tele Ξ) (ext_eq_ctx_left _ _ _ _ _ HΔ) (ind_ty_at D Ns) (apps (a_ind p) Ns)) as [HM | Hn];
    [| right; intros HE; destruct (proj2 (proj2 (wf_gentry_ind_alias_inv _ _ _ _ _ _ _ HE))) as (D' & Hl' & _ & HM' & _);
       rewrite Hl in Hl'; injection Hl' as <-; exact (Hn HM') ].
  destruct (check_modexp fctx_none Θ Ξ (Δ ++ gs_tele Ξ) (ext_eq_ctx_left _ _ _ _ _ HΔ) (me_apps (qname_mod p) Ns)) as [HH | Hn];
    [| right; intros HE; destruct (proj2 (proj2 (wf_gentry_ind_alias_inv _ _ _ _ _ _ _ HE))) as (D' & _ & _ & _ & HH');
       exact (Hn HH') ].
  left; econstructor; eassumption.
Defined.

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
    the driver to print.  The message of [re_unit] concerns the unit at the
    path it carries and does not repeat that path. *)

Inductive run_error : Set :=
| re_msg : string -> run_error
(** The body of a definition is not of its declared type, which is a type. *)
| re_def : string -> gstack -> typ -> exp -> run_error
(** The declared type of a definition with a body is not a type. *)
| re_def_typ : string -> gstack -> typ -> run_error
(** An ascribed eval: the term is not of its ascription, which is a type. *)
| re_eval_check : gstack -> exp -> typ -> run_error
(** An ascribed eval: the ascription of the term is not a type. *)
| re_eval_typ : gstack -> exp -> typ -> run_error
| re_eval_infer : gstack -> exp -> run_error
(** A small universe [Type@{t}] whose level [t] is of no type of levels,
    found by [find_level_blame] where a type or a telescope is rejected:
    [t] lives in the context the stack's telescope is extended by, innermost
    entry first. *)
| re_level : gstack -> ctx -> exp -> run_error
| re_cycle : list path -> run_error
| re_unit : path -> string -> run_error
(** A private member, named by its module, reached from outside it. *)
| re_private : qname -> string -> run_error
(** A private entry of a local body, by the chain of submodules from the
    local module, reached from outside it. *)
| re_private_local : list string -> string -> run_error
(** An open that generates nothing ([Opens]). *)
| re_import : xerr -> run_error
(** The argument [y] of the constructor [c] of the type [x] has [x] in an
    argument of another inductive type, its head. *)
| re_nested : string -> string -> string -> exp -> run_error
(** The non-uniform parameter at a position (outermost [0]) of the type
    [x]: its type is not in the sort; both live in the context. *)
| re_ind_npar : string -> nat -> ctx -> typ -> typ -> run_error
(** A chain from a unit, in term position, that names a module (an alias
    of the module of an inductive type included), not a term. *)
| re_mod_term : qname -> run_error
(** A path that names no inductive type where one is wanted. *)
| re_not_ind : qname -> run_error
(** A literal, a numeral or the token [ℕ], with no natural-number type
    bound ([Builtin]). *)
| re_lit : lerr -> run_error
(** A branch of an eliminator that binds [n] names where its constructor
    needs [k] non-uniform parameters, [a] arguments and [r] recursive
    results: [re_branch_arity c n k a r]. *)
| re_branch_arity : string -> nat -> nat -> nat -> nat -> run_error
(** A branch for no constructor of the eliminated type. *)
| re_branch_unknown : string -> run_error
(** A constructor with no branch, or with two. *)
| re_branch_missing : string -> run_error
| re_branch_dup : string -> run_error
(** Branches, one per constructor, not in the order [cs] of the
    constructors. *)
| re_branch_order : list string -> run_error
(** An error, with the state it occurred in, for the printer: the units
    imported, the stack, and the natural numbers bound there, their type
    and constructors as [nat_view] gives them. *)
| re_nat : gdeps -> gstack -> option (qname * string * string) -> run_error -> run_error.

Definition priv_error (e : priv_err) : run_error :=
  match e with
  | pe_global qd x => re_private qd x
  | pe_local ch x => re_private_local ch x
  end.

(** The error for a rejected type or telescope: the blamed level if
    [find_level_blame] found one, otherwise the given error. *)
Definition blame_error {Θ Ξ Γ} (b : option (level_blame Θ Ξ Γ)) (e : run_error) : run_error :=
  match b with
  | Some (exist _ (Δ, t) _) => re_level Ξ Δ t
  | None => e
  end.

(** Where a term is rejected, a chain from a unit in it that names a
    module but stands where a term does: found syntactically, whether the
    chains name modules asked of the global context ([gc_module]), which
    does not read the local context for them, and whether they name an
    inductive alias, which is a term, asked of [it]. *)
Section ModBlame.
  Variables (Θ : gdeps) (Ξ : gstack).
  Variable it : qname -> option ind_alias_view.

  Definition mod_term_blame (H : modexp) (x : string) : option run_error :=
    match mod_qname H with
    | Some mp =>
        match gc_module Θ Ξ (qname_app mp (x :: nil)), it (qname_app mp (x :: nil)) with
        | Some _, None => Some (re_mod_term (qname_app mp (x :: nil)))
        | _, _ => None
        end
    | None => None
    end.

  Definition first_some {X} (a : option X) (b : unit -> option X) : option X :=
    match a with Some _ => a | None => b tt end.

  Fixpoint mod_blame (M : exp) : option run_error :=
    match M with
    | a_succl M | a_univ M => mod_blame M
    | a_maxl M N | a_pi M N | a_fn M N | a_app M N => first_some (mod_blame M) (fun _ => mod_blame N)
    | a_exfalso A M => first_some (mod_blame M) (fun _ => mod_blame A)
    | a_elim _ A Bs M =>
        first_some (mod_blame M) (fun _ => first_some (mod_blame A)
          (fun _ => (fix brs (Bs : list (string * nat * exp)) : option run_error :=
                       match Bs with
                       | nil => None
                       | b :: Bs' => first_some (mod_blame (snd b)) (fun _ => brs Bs')
                       end) Bs))
    | a_let (b_def oA N) B =>
        first_some (match oA with Some A => mod_blame A | None => None end)
          (fun _ => first_some (mod_blame N) (fun _ => mod_blame B))
    | a_let (b_mod _) B => mod_blame B
    | a_mem H x => mod_term_blame H x
    | _ => None
    end.
End ModBlame.

(** Where a term is rejected, an eliminator whose branches do not match the
    constructors of the type it eliminates.  The type is read off the
    names of the branches: every inductive type of the global context that
    has a constructor of each branch's name, and the error is reported when
    all of them give the same one.  This only chooses the message. *)
Section BranchBlame.
  Fixpoint gmod_inds (Φ : gmod) : list ind_decl :=
    match Φ with
    | gm_nil => nil
    | gm_ext Φ _ E =>
        match E with
        | ge_ind _ _ D Φi => D :: gmod_inds Φi
        | ge_mod _ (gu_mk _ (md_body sm Φi)) => gmod_inds Φi
        | _ => nil
        end ++ gmod_inds Φ
    | gm_open Φ _ _ => gmod_inds Φ
    end.

  Definition ctx_inds (Θ : gdeps) (Ξ : gstack) : list ind_decl :=
    flat_map (fun e => gmod_inds (gu_mod (snd e))) Θ ++ flat_map (fun e => gmod_inds (gu_mod (snd e))) Ξ.

  Definition brs_has (Bs : list (string * nat * exp)) (c : string) : nat :=
    List.length (List.filter (fun b => String.eqb (fst (fst b)) c) Bs).

  Fixpoint strs_eqb (xs ys : list string) : bool :=
    match xs, ys with
    | nil, nil => true
    | x :: xs, y :: ys => andb (String.eqb x y) (strs_eqb xs ys)
    | _, _ => false
    end.

  (** The first mismatch of the branches [Bs] against the constructors of
      [D]: a branch's binders, then a constructor without a branch or with
      two, then the order of the branches. *)
  Definition branch_check (D : ind_decl) (Bs : list (string * nat * exp)) : option run_error :=
    first_some (first_some
      ((fix go (Bs0 : list (string * nat * exp)) : option run_error :=
          match Bs0 with
          | nil => None
          | (c, n, _) :: Bs0' =>
              match ind_con D c with
              | Some gs =>
                  if Nat.eqb n (ind_nn D + List.length gs + cargs_nrec gs) then go Bs0'
                  else Some (re_branch_arity c n (ind_nn D) (List.length gs) (cargs_nrec gs))
              | None => Some (re_branch_unknown c)
              end
          end) Bs)
      (fun _ => (fix go (cs : list (string * list carg)) : option run_error :=
          match cs with
          | nil => None
          | (c, _) :: cs' =>
              match brs_has Bs c with
              | 0 => Some (re_branch_missing c)
              | 1 => go cs'
              | _ => Some (re_branch_dup c)
              end
          end) (ind_cons D)))
      (fun _ =>
         if strs_eqb (List.map (fun b => fst (fst b)) Bs) (List.map fst (ind_cons D)) then None
         else Some (re_branch_order (List.map fst (ind_cons D)))).

  Definition run_error_eqb (e1 e2 : run_error) : bool :=
    match e1, e2 with
    | re_branch_arity c n k a r, re_branch_arity c' n' k' a' r' =>
        andb (String.eqb c c') (andb (Nat.eqb n n') (andb (Nat.eqb k k') (andb (Nat.eqb a a') (Nat.eqb r r'))))
    | re_branch_unknown c, re_branch_unknown c' => String.eqb c c'
    | re_branch_missing c, re_branch_missing c' => String.eqb c c'
    | re_branch_dup c, re_branch_dup c' => String.eqb c c'
    | re_branch_order cs, re_branch_order cs' => strs_eqb cs cs'
    | _, _ => false
    end.

  Definition elim_blame (Θ : gdeps) (Ξ : gstack) (Bs : list (string * nat * exp)) : option run_error :=
    match Bs with
    | nil => None
    | _ =>
        let is_con D b := match ind_con D (fst (fst b)) with Some _ => true | None => false end in
        let cands :=
          match List.filter (fun D => forallb (is_con D) Bs) (ctx_inds Θ Ξ) with
          | nil => List.filter (fun D => existsb (is_con D) Bs) (ctx_inds Θ Ξ)
          | Ds => Ds
          end in
        match List.map (fun D => branch_check D Bs) cands with
        | Some e :: rs => if forallb (fun r => match r with Some e' => run_error_eqb e e' | None => false end) rs then Some e else None
        | _ => None
        end
    end.

  Fixpoint brs_blame (Θ : gdeps) (Ξ : gstack) (M : exp) : option run_error :=
    match M with
    | a_succl M | a_univ M => brs_blame Θ Ξ M
    | a_maxl M N | a_pi M N | a_fn M N | a_app M N => first_some (brs_blame Θ Ξ M) (fun _ => brs_blame Θ Ξ N)
    | a_exfalso A M => first_some (brs_blame Θ Ξ M) (fun _ => brs_blame Θ Ξ A)
    | a_elim _ A Bs M =>
        first_some (brs_blame Θ Ξ M) (fun _ => first_some (brs_blame Θ Ξ A)
          (fun _ => first_some (elim_blame Θ Ξ Bs)
          (fun _ => (fix brs (Bs : list (string * nat * exp)) : option run_error :=
                       match Bs with
                       | nil => None
                       | b :: Bs' => first_some (brs_blame Θ Ξ (snd b)) (fun _ => brs Bs')
                       end) Bs)))
    | a_let (b_def oA N) B =>
        first_some (match oA with Some A => brs_blame Θ Ξ A | None => None end)
          (fun _ => first_some (brs_blame Θ Ξ N) (fun _ => brs_blame Θ Ξ B))
    | a_let (b_mod _) B => brs_blame Θ Ξ B
    | _ => None
    end.
End BranchBlame.

(** The error for a rejected term: a module where a term stands, if there
    is one, then an eliminator whose branches do not match its type,
    otherwise the given error. *)
Definition mod_error {Θ Ξ} (Hg : ⊢ᵍ Θ ⍮ Ξ) (it : qname -> option ind_alias_view) (Ms : list exp) (e : run_error) : run_error :=
  match List.fold_right (fun M r => first_some (first_some (mod_blame Θ Ξ it M) (fun _ => brs_blame Θ Ξ M)) (fun _ => r)) None Ms with
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

(** A checked and normalized [eval]: in the restriction [ev_deps] of the
    state to the imports so far, on the stack [ev_stack], and in the context
    of the frames' parameters, the expression [ev_exp] has type [ev_typ]
    (ascribed or inferred) and normalizes to [ev_nf]. *)
Record eval_entry : Set :=
  { ev_deps : gdeps; ev_stack : gstack; ev_exp : exp; ev_typ : typ; ev_nf : nf }.

Record eval_ok (e : eval_entry) : Prop := mk_eval_ok
  { evo_wf : ⊢ᵍ ev_deps e ⍮ ev_stack e
  ; evo_typ : ev_deps e ⍮ ev_stack e ⍮ gs_tele (ev_stack e) ⊢ ev_exp e : ev_typ e
  ; evo_nbe : nbe (ev_deps e) (ev_stack e) (gs_tele (ev_stack e)) (ev_exp e) (ev_typ e) (ev_nf e) }.

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

(** Normalize a checked [eval] into its entry. *)
Lemma eval_log_ok {Θ Ξ M A W} : ⊢ᵍ Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> nbe Θ Ξ (gs_tele Ξ) M A W ->
  logs_ok ({| ev_deps := Θ; ev_stack := Ξ; ev_exp := M; ev_typ := A; ev_nf := W |} :: nil).
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

(** An inductive alias entry moves along an equivalence, premise by
    premise. *)
Lemma equiv_ind_alias_entry : forall Θ Θ' Ξ mp pv Δ p Ns, gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ ->
    Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns -> Θ' ⍮ Ξ ⍮ mp ⊢ᵉ ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns.
Proof.
  intros * He HΞ HE; destruct (wf_gentry_ind_alias_inv _ _ _ _ _ _ _ HE) as (Htel & HΔ & D & Hl & Hle & HM & HH).
  econstructor;
    [ exact Htel | exact (equiv_ext _ _ _ _ _ He HΞ HΔ)
    | rewrite ind_lookup_unfold in *; rewrite <- (gds_equiv_module _ _ _ _ He); exact Hl | exact Hle
    | exact (equiv_exp _ _ _ _ _ _ He HΞ HM) | exact (equiv_modexp _ _ _ _ _ He HΞ HH) ].
Qed.

(** What a command's checks look names up in ([Extraction.Lookup]): the
    trie of the filed units, and the declaration of the type bound as the
    natural numbers, looked up once per check rather than once per
    eliminator. *)
Definition fctx_cmd (B : builtins) (Θ : gdeps) (Ξ : gstack) : FCtx Θ Ξ :=
  fctx_at Θ Ξ (bt_nat B).

Section Impl.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).
  #[local] Abbreviation canon := (canon load_path read to_core).
  #[local] Abbreviation run_wf := (run_wf load_path read to_core).
  #[local] Abbreviation run_functional := (run_functional load_path read to_core).

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
    { eo_dom : list path
    ; eo_bt : builtins
    ; eo_src : string
    ; eo_prog : Cst.prog
    ; eo_unit : cunit
    ; eo_chain : list path
    ; eo_rb : bmap
    ; eo_deps : gdeps
    ; eo_kfind : kfind K fp = Some eo_dom
    ; eo_kbt : kbt K fp = Some eo_bt
    ; eo_closed : closedK K eo_dom
    ; eo_load : load_path fp = Some eo_src
    ; eo_read : read eo_src = Some eo_prog
    ; eo_path : prog_path eo_prog = fp
    ; eo_core : to_core eo_prog = Some eo_unit
    ; eo_run : run_unit (fp :: eo_chain) eo_unit eo_bt eo_rb eo_deps U
    ; eo_sub : eo_deps ⊑ Θ
    ; eo_set : set_eq eo_dom (gds_dom eo_deps)
    ; eo_rb_in : rb_in K eo_rb }.

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

  Record cstate : Set := cst { cs_deps : gdeps; cs_k : kmap; cs_dom : list path; cs_bt : builtins; cs_stack : gstack }.
  Record ustate : Set := ust { us_deps : gdeps; us_k : kmap; us_dom : list path; us_bt : builtins; us_unit : gunit }.

  (** What a run of commands from [Θ ⍮ K] to [r] proves: the judgment, from
      the judgment's state and records the run started at, reaches [cp_deps]
      and [cp_rb] ([run]), and the invariants hold again. *)
  #[warnings="-cannot-define-projection"]
  Record cmd_post (run : bmap -> gdeps -> Prop) ch (Θ : gdeps) (K : kmap) (r : cstate) : Prop := mk_cmd_post
    { cp_deps : gdeps
    ; cp_rb : bmap
    ; cp_run : run cp_rb cp_deps
    ; cp_linv : linv ch (cs_deps r) (cs_k r) (cs_dom r) cp_deps (cs_stack r)
    ; cp_rb_ok : rb_ok (cs_k r) cp_deps cp_rb
    ; cp_ext : ext Θ K (cs_deps r) (cs_k r)
    ; cp_grows : grows Θ (cs_deps r) (cs_dom r) }.

  Definition post_cmd ch Θ K D B Ξ c (r : cstate) : Prop :=
    forall ΘR RbR, linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      cmd_post (fun RbR' ΘR' => ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ ΘR' ⍮ cs_stack r ⍮ cs_bt r ⍮ RbR') ch Θ K r.

  Definition post_cmds ch Θ K D B Ξ cs (r : cstate) : Prop :=
    forall ΘR RbR, linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      cmd_post (fun RbR' ΘR' => ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR' ⍮ cs_stack r ⍮ cs_bt r ⍮ RbR') ch Θ K r.

  (** A command with its literals generated ([Builtin]) and run, as
      [rcs_cons] does. *)
  Definition post_lcmd ch Θ K D B Ξ c (r : cstate) : Prop :=
    forall ΘR RbR, linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
      cmd_post (fun RbR' ΘR' => exists c1, cmd_lits_ok ΘR Ξ B c c1 /\
                                  ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c1 ⇝ ΘR' ⍮ cs_stack r ⍮ cs_bt r ⍮ RbR') ch Θ K r.

  (** A unit runs from no binding and nothing filed. *)
  #[warnings="-cannot-define-projection"]
  Record unit_post ch (Θ : gdeps) (K : kmap) (u : cunit) (r : ustate) : Prop := mk_unit_post
    { up_rb : bmap
    ; up_deps : gdeps
    ; up_run : run_unit ch u (us_bt r) up_rb up_deps (us_unit r)
    ; up_ginv : ginv ch (us_deps r) (us_k r)
    ; up_sub : up_deps ⊑ us_deps r
    ; up_set : set_eq (us_dom r) (gds_dom up_deps)
    ; up_closed : closedK (us_k r) (us_dom r)
    ; up_rb_in : rb_in (us_k r) up_rb
    ; up_ext : ext Θ K (us_deps r) (us_k r)
    ; up_grows : grows Θ (us_deps r) (us_dom r) }.

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
    destruct (proj2 (proj2 run_wf) _ _ _ _ _ _ Hu) as (_ & _ & HwU); cbn [hd] in HwU.
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
    destruct Ξ as [| [mp U] Ξ]; [ contradiction |]; cbn; exists x; split; [ reflexivity | exact Hfr ].
  Qed.

  (** A unit's own frame: its path heads the chain, so it is not filed. *)
  Lemma linv_push_unit {fp ch Θ K D ΘR P} :
    linv (fp :: ch) Θ K D ΘR nil -> tele_ass P -> ⊢ gds_restrict D Θ ⍮ nil ⍮ P ->
    ⊢ ΘR ⍮ nil ⍮ P /\ linv (fp :: ch) Θ K D ΘR (gs_push (q_abs fp nil) P nil).
  Proof.
    intros Hli Htel HP.
    assert (HP' : ⊢ ΘR ⍮ nil ⍮ P)
      by exact (equiv_ctx _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HP).
    split; [ exact HP' |]; apply (linv_stack Hli); [| intros ? ? [[= <- <-] | []]; left; reflexivity ].
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
    intros G; constructor; [ exact G | discriminate | intros ?; cbn; tauto | intros ? ? [] | | intros ? ? [] ].
    constructor; constructor; constructor.
  Qed.

  Lemma rb_ok_nil : forall K, rb_ok K nil nil.
  Proof. intros; split; [ apply canon_nil | intros ? ? H; discriminate H ]. Qed.

  (** The literals are generated from the bound type's declaration, which
      the restriction has as the judgment's state does. *)
  Lemma equiv_nat_view : forall Θ Θ' Ξ B, gds_equiv Θ Θ' -> nat_view Θ Ξ B = nat_view Θ' Ξ B.
  Proof.
    intros * He; unfold nat_view; destruct (bt_nat B) as [p |]; [| reflexivity ].
    rewrite ind_lookup_unfold, (gds_equiv_module _ _ _ _ He); reflexivity.
  Qed.

  Lemma linv_nat_view {ch Θ K D B ΘR Ξ} : linv ch Θ K D ΘR Ξ -> nat_view ΘR Ξ B = nat_view (gds_restrict D Θ) Ξ B.
  Proof. intros Hli; exact (equiv_nat_view _ _ _ _ (linv_equiv Hli)). Qed.

  Lemma lits_lift {ch Θ K D B Ξ c c1 r} :
    cmd_lits (nat_view (gds_restrict D Θ) Ξ B) c = lok c1 ->
    post_cmd ch Θ K D B Ξ c1 r -> post_lcmd ch Θ K D B Ξ c r.
  Proof.
    intros El Hp ΘR RbR Hli Hrb; destruct (Hp _ _ Hli Hrb) as [ΘR' RbR' Hr Hli' Hrb' Hext Hgr].
    apply (mk_cmd_post _ _ _ _ _ ΘR' RbR'); try assumption.
    exists c1; split; [ unfold cmd_lits_ok; rewrite (linv_nat_view Hli); exact El | exact Hr ].
  Qed.

  Lemma lits_eq {ch Θ K D B ΘR Ξ c c1} :
    linv ch Θ K D ΘR Ξ -> cmd_lits_ok ΘR Ξ B c c1 -> cmd_lits (nat_view (gds_restrict D Θ) Ξ B) c = lok c1.
  Proof. intros Hli Hl; unfold cmd_lits_ok in Hl; rewrite (linv_nat_view Hli) in Hl; exact Hl. Qed.


  (** ** One Step per Rule

      Each lemma proves the [post_*] of one branch of the executable from the
      checks that branch makes. *)

  Lemma def_ok {ch Θ K D B Ξ x b pv A M} :
    gs_fresh x Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_cmd ch Θ K D B Ξ (cc_def x b pv A (Some M)) (cst Θ K D B (gs_add x (gs_def b pv Ξ A M) Ξ)).
  Proof.
    intros Hfr HM ΘR RbR Hli Hrb; cbn [cs_deps cs_k cs_dom cs_bt cs_stack].
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
    intros Hfr HA ΘR RbR Hli Hrb; cbn [cs_deps cs_k cs_dom cs_bt cs_stack].
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
    intros HM ΘR RbR Hli Hrb; cbn [cs_deps cs_k cs_dom cs_bt cs_stack].
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_eval M (Some A) ⇝ ΘR ⍮ Ξ ⍮ B ⍮ RbR)
      by (constructor; exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HM)).
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [ exact Hr | exact Hli | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  (** A builtin binding, with the premises of [rc_builtin] at the
      restriction. *)
  Lemma builtin_ok {ch Θ K D B Ξ E p Dd z s B'} :
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
    mdenote (gds_restrict D Θ) Ξ (gs_tele Ξ) E (ds_ind nil p nil) ->
    ind_lookup (gds_restrict D Θ) Ξ p = Some Dd -> nat_shape Dd = Some (z, s) -> ind_sort Dd = nat_sort ->
    bt_bind_nat B p = Some B' ->
    post_cmd ch Θ K D B Ξ (cc_builtin nat_kind E) (cst Θ K D B' Ξ).
  Proof.
    intros HE Hm Hl Hs Hsort Hb ΘR RbR Hli Hrb; cbn [cs_deps cs_k cs_dom cs_bt cs_stack].
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as He.
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_builtin nat_kind E ⇝ ΘR ⍮ Ξ ⍮ B' ⍮ RbR).
    { eapply rc_builtin; [ exact (equiv_modexp _ _ _ _ _ He (li_wf _ _ _ _ _ _ Hli) HE)
                         | exact (gds_equiv_mdenote _ _ _ _ _ _ He Hm)
                         | rewrite ind_lookup_unfold in *; rewrite <- (gds_equiv_module _ _ _ _ He); exact Hl
                         | exact Hs | exact Hsort | exact Hb ]. }
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [ exact Hr | exact Hli | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  Lemma eval_infer_ok {ch Θ K D B Ξ M} (A : typ) :
    gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    post_cmd ch Θ K D B Ξ (cc_eval M None) (cst Θ K D B Ξ).
  Proof.
    intros HM ΘR RbR Hli Hrb; cbn [cs_deps cs_k cs_dom cs_bt cs_stack].
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_eval M None ⇝ ΘR ⍮ Ξ ⍮ B ⍮ RbR)
      by (econstructor; exact (equiv_exp _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HM)).
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [ exact Hr | exact Hli | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  Lemma mod_pre {ch Θ K D Ξ x Δ} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> tele_ass Δ -> gs_fresh x Ξ -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    exists ΘR, linv ch Θ K D ΘR (gs_push (qname_in (gs_path Ξ) x) Δ Ξ).
  Proof. intros [ΘR Hli] Htel Hfr HΔ; exists ΘR; exact (proj2 (linv_push Hli Htel Hfr HΔ)). Qed.

  Lemma mod_ok {ch Θ K D B Ξ x pv Δ cs r mp U Ξ2} :
    tele_ass Δ -> gs_fresh x Ξ -> ⊢ gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
    post_cmds ch Θ K D B (gs_push (qname_in (gs_path Ξ) x) Δ Ξ) cs r -> cs_stack r = (mp, U) :: Ξ2 ->
    post_cmd ch Θ K D B Ξ (cc_mod x pv Δ cs) (cst (cs_deps r) (cs_k r) (cs_dom r) (cs_bt r) (gs_add x (ge_body pv Δ (gu_mod U)) Ξ)).
  Proof.
    intros Htel Hfr HΔ Hpost HΞ ΘR RbR Hli Hrb; cbn [cs_deps cs_k cs_dom cs_bt cs_stack].
    destruct (linv_push Hli Htel Hfr HΔ) as [HΔ' Hli'].
    destruct (Hpost _ _ Hli' Hrb) as [ΘR' RbR' Hrun Hli2 Hrb2 Hext Hgr]; cbn beta in Hrun.
    rewrite HΞ in Hrun, Hli2.
    destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun) as [F HF]; injection HF as <- ->.
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_mod x pv Δ cs ⇝ ΘR' ⍮ gs_add x (ge_body pv Δ (gu_mod U)) Ξ ⍮ cs_bt r ⍮ RbR')
      by (econstructor; eassumption).
    apply (mk_cmd_post _ _ _ _ _ ΘR' RbR' Hr); [| exact Hrb2 | assumption | assumption ].
    apply (linv_stack Hli2); [ exact (proj1 (linv_run_wf Hli (proj1 Hrb) Hr)) | exact (linv_run_stack Hli Hr) ].
  Qed.

  Lemma alias_ok {ch Θ K D B Ξ x pv Δ E} :
    tele_ass Δ -> gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E -> gs_fresh x Ξ ->
    post_cmd ch Θ K D B Ξ (cc_alias x pv Δ E) (cst Θ K D B (gs_add x (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))) Ξ)).
  Proof.
    intros Htel HΔ HE Hfr ΘR RbR Hli Hrb; cbn [cs_deps cs_k cs_dom cs_bt cs_stack].
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as Heq.
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_alias x pv Δ E ⇝ ΘR ⍮ gs_add x (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))) Ξ ⍮ B ⍮ RbR)
      by (constructor; [ exact Htel | exact (equiv_ext _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HΔ)
                       | exact (equiv_modexp _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HE) | exact Hfr ]).
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR);
      [ exact Hr | exact (linv_run_same Hli (proj1 Hrb) Hr) | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  (** An inductive alias, with the premises of [rc_ind_alias] at the
      restriction. *)
  Lemma indalias_ok {ch Θ K D B Ξ x pv Δ E Θ' p Ns} :
    gds_restrict D Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    mdenote (gds_restrict D Θ) Ξ (Δ ++ gs_tele Ξ) E (ds_ind Θ' p Ns) ->
    gds_restrict D Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind_alias pv ((Θ' ++ Δ) ++ gs_tele Ξ) p Ns ->
    gs_fresh x Ξ ->
    post_cmd ch Θ K D B Ξ (cc_ind_alias x pv Δ E) (cst Θ K D B (gs_add x (ge_ind_alias pv (Θ' ++ Δ ++ gs_tele Ξ) p Ns) Ξ)).
  Proof.
    intros HE Hm HEn Hfr ΘR RbR Hli Hrb; cbn [cs_deps cs_k cs_dom cs_bt cs_stack].
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as Heq.
    pose proof (equiv_ind_alias_entry _ _ _ _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HEn) as HEn'.
    rewrite <- List.app_assoc in HEn'.
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_ind_alias x pv Δ E ⇝ ΘR ⍮ gs_add x (ge_ind_alias pv (Θ' ++ Δ ++ gs_tele Ξ) p Ns) Ξ ⍮ B ⍮ RbR).
    { eapply rc_ind_alias; [ exact (equiv_modexp _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HE)
                           | exact (gds_equiv_mdenote _ _ _ _ _ _ Heq Hm) | exact HEn' | exact Hfr ]. }
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR);
      [ exact Hr | exact (linv_run_same Hli (proj1 Hrb) Hr) | exact Hrb | apply ext_refl | apply grows_refl ].
  Qed.

  (** A unit the unit being run imported already: its record, kept in [K],
      is merged in again. *)
  Lemma load_in_ok {ch Θ K D B Ξ fp U BU B'} :
    In fp D -> gds_lookup Θ fp = Some U -> kbt K fp = Some BU -> bt_merge B BU = Some B' ->
    post_cmd ch Θ K D B Ξ (cc_load fp) (cst Θ K D B' Ξ).
  Proof.
    intros Hin HU HB Hm ΘR RbR Hli Hrb; cbn [cs_deps cs_k cs_dom cs_bt cs_stack].
    apply (li_dom _ _ _ _ _ _ Hli), gds_dom_lookup in Hin.
    destruct (gds_lookup ΘR fp) as [V |] eqn:E'; [| contradiction ].
    destruct (proj1 (proj1 Hrb) _ _ E') as [BU' src prg u ch0 RbU ΘU EB _ _ _ _].
    pose proof (proj2 Hrb _ _ EB) as HB'; rewrite HB in HB'; injection HB' as <-.
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_load fp ⇝ ΘR ⍮ Ξ ⍮ B' ⍮ RbR) by (eapply rc_load_filed; eassumption).
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
    { apply (proj2 (proj2 (run_chain_irrel load_path read to_core)) _ _ _ _ _ _ Hu ch).
      intros x [<- | Hin].
      - exact (proj2 (proj2 (run_chain_fresh load_path read to_core)) _ _ _ _ _ _ Hu _ (or_introl eq_refl)).
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
    intros Hnin HU HK HB Hm ΘR RbR Hli Hrb; cbn [cs_deps cs_k cs_dom cs_bt cs_stack].
    destruct (hit_linv Hnin HU HK HB _ _ Hli Hrb) as (src & prg & u & RbU & ΘU & Hn & Hnch & Hl & Hrd & Hp & Ht & Hu & Hli' & Hrb').
    assert (Hr : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_load fp ⇝ gds_merge ΘR ((fp, U) :: ΘU) ⍮ Ξ ⍮ B' ⍮ bm_merge RbR ((fp, BU) :: RbU))
      by (eapply rc_load; eassumption).
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
      linv ch (cs_deps (load_state fp D Ξ B' r)) (cs_k (load_state fp D Ξ B' r)) (cs_dom (load_state fp D Ξ B' r))
        (gds_merge ΘR ((fp, us_unit r) :: ΘU)) Ξ /\
      rb_ok (cs_k (load_state fp D Ξ B' r)) (gds_merge ΘR ((fp, us_unit r) :: ΘU)) (bm_merge RbR ((fp, us_bt r) :: RbU)) /\
      ext Θ K (cs_deps (load_state fp D Ξ B' r)) (cs_k (load_state fp D Ξ B' r)) /\
      grows Θ (cs_deps (load_state fp D Ξ B' r)) (cs_dom (load_state fp D Ξ B' r)).
  Proof.
    intros Hn Hnch Hl Hrd Hp Ht Hpost ΘR RbR Hli Hrb.
    pose proof (li_g _ _ _ _ _ _ Hli) as G.
    assert (Gin : ginv (fp :: ch) Θ K) by (eapply load_pre; [ exists ΘR; exact Hli | assumption | assumption ]).
    destruct r as [Θ1 K1 Dfp B1 U]; unfold load_state; cbn [us_deps us_k us_dom us_bt us_unit cs_deps cs_k cs_dom cs_bt cs_stack] in *.
    destruct (Hpost Gin) as [RbU ΘU Hu G1 Hsub1 Hdom1 Hcl1 HRU [Hext1 HextK HextB] Hgr1].
    cbn [us_deps us_k us_dom us_bt us_unit] in *.
    destruct (proj2 (proj2 run_wf) _ _ _ _ _ _ Hu) as (HwU & HcU & HUu); cbn [hd] in HUu.
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
    exists RbU, ΘU; cbn [cs_deps cs_k cs_dom cs_bt cs_stack us_deps us_k us_dom us_bt us_unit].
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
      by (eapply rc_load; eassumption).
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

  Lemma gindalias_step {ch Θ K D ΘR Ξ d pv Δ p Ns} :
    linv ch Θ K D ΘR Ξ -> gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ qname_in (gs_path Ξ) d ⊢ᵉ ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns ->
    ΘR ⍮ Ξ ⍮ qname_in (gs_path Ξ) d ⊢ᵉ ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns /\
    linv ch Θ K D ΘR (gs_add d (ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns) Ξ).
  Proof.
    intros Hli Hfr HE.
    pose proof (equiv_ind_alias_entry _ _ _ _ _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) (li_wf _ _ _ _ _ _ Hli) HE) as HE'.
    split; [ exact HE' |].
    exact (linv_stack Hli (add_entry_wf _ _ _ _ (li_wf _ _ _ _ _ _ Hli) HE' Hfr)
             (stack_in_add _ _ _ _ (li_stack _ _ _ _ _ _ Hli))).
  Qed.

  Lemma gindalias_pre {ch Θ K D Ξ d pv Δ p Ns} :
    (exists ΘR, linv ch Θ K D ΘR Ξ) -> gs_fresh d Ξ ->
    gds_restrict D Θ ⍮ Ξ ⍮ qname_in (gs_path Ξ) d ⊢ᵉ ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns ->
    exists ΘR, linv ch Θ K D ΘR (gs_add d (ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns) Ξ).
  Proof. intros [ΘR Hli] Hfr HE; exists ΘR; exact (proj2 (gindalias_step Hli Hfr HE)). Qed.

  Lemma gindalias_ok {ch Θ K D Ξ d pv Δ p Ns gs Ξ'} :
    gs_fresh d Ξ -> gds_restrict D Θ ⍮ Ξ ⍮ qname_in (gs_path Ξ) d ⊢ᵉ ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns ->
    post_gens ch Θ K D (gs_add d (ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns) Ξ) gs Ξ' ->
    post_gens ch Θ K D Ξ (ig_ind_alias d pv Δ p Ns :: gs) Ξ'.
  Proof.
    intros Hfr HE Hp ΘR Hli; destruct (gindalias_step Hli Hfr HE) as [HE' Hli'].
    destruct (Hp _ Hli') as [Hg Hli2]; split; [ econstructor; eassumption | exact Hli2 ].
  Qed.

  (** An import declares what its items generate, which files nothing. *)
  (** What an open generates is read off descriptions, which read the
      dependencies through their lookups alone. *)
  Lemma open_gens_equiv : forall Θ1 Θ2 Ξ g Γ H its gs, gds_equiv Θ1 Θ2 ->
      open_gens Θ1 Ξ g Γ H its gs -> open_gens Θ2 Ξ g Γ H its gs.
  Proof.
    intros * He [R Rm HR HRm Hg Hok].
    pose proof (gds_equiv_mdenote_all _ _ Ξ He) as (H1 & _ & _ & _ & H5).
    apply (mk_open_gens _ _ _ _ _ _ _ R Rm); [ exact (H1 _ _ _ HR) | | exact (H5 _ _ _ _ _ Hg) | exact Hok ].
    destruct R; cbn [ds_mod] in HRm |- *; try exact HRm.
    rewrite <- (gds_equiv_body _ _ _ _ He); exact HRm.
  Qed.

  Lemma import_ok {ch Θ K D B Ξ E its gs Ξ'} (Hg : ⊢ᵍ gds_restrict D Θ ⍮ Ξ)
    (HE : gds_restrict D Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E) :
    import_gen _ _ Hg (gs_tele Ξ) E E HE true its = xok gs ->
    post_gens ch Θ K D Ξ gs Ξ' ->
    post_cmd ch Θ K D B Ξ (cc_open E its) (cst Θ K D B Ξ').
  Proof.
    intros Hgen Hgs ΘR RbR Hli Hrb; cbn [cs_deps cs_k cs_dom cs_bt cs_stack].
    destruct (Hgs _ Hli) as [Hr Hli'].
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as Heq.
    apply (mk_cmd_post _ _ _ _ _ ΘR RbR); [| exact Hli' | exact Hrb | apply ext_refl | apply grows_refl ].
    eapply rc_open; [ exact (equiv_modexp _ _ _ _ _ Heq (li_wf _ _ _ _ _ _ Hli) HE) | | exact Hr ].
    apply (import_gen_spec _ _ Hg) in Hgen.
    exact (open_gens_equiv _ _ _ _ _ _ _ _ Heq Hgen).
  Qed.

  (** A declaration files its entry where it is declared: the
      declaration, checked alone, and the members it generates, which then
      check ([ind_gens_typed]). *)
  Lemma ind_ok {ch Θ K D B Ξ x pv R cs} :
    cls_cons_in (gds_restrict D Θ) Ξ R cs -> gs_fresh x Ξ ->
    gds_restrict D Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)) ⋄ ->
    ~ In "rec"%string (List.map fst (ind_cons (gs_ind Ξ (rd_filed R cs)))) ->
    post_cmd ch Θ K D B Ξ (cc_ind x pv R) (cst Θ K D B (gs_add x (ge_ind pv (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs))
                              (gen_body (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)))) Ξ)).
  Proof.
    intros Hcls Hfr HE Hrec ΘR RbR Hli Hrb; cbn [cs_deps cs_k cs_dom cs_bt cs_stack].
    pose proof (gds_equiv_sym _ _ (linv_equiv Hli)) as Heq.
    pose proof (li_wf _ _ _ _ _ _ Hli) as HΞ.
    pose proof (equiv_gentry_ind _ _ _ _ _ _ Heq HΞ HE) as HE'.
    pose proof (equiv_cls_cons_in _ _ _ _ _ Heq HΞ Hcls) as Hcls'.
    assert (Hrun : ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_ind x pv R ⇝ ΘR ⍮ gs_add x (ge_ind pv (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)) (gen_body (ind_qname Ξ x) (gs_ind Ξ (rd_filed R cs)))) Ξ ⍮ B ⍮ RbR).
    { eapply rc_ind; [ exact Hcls' | exact Hfr |].
      destruct Ξ as [| [mq [Δ [[] Φ0 | E0]]] Ξ0]; [ contradiction | | |].
      - exfalso; destruct (wf_gstack_cons_inv _ _ _ _ HΞ) as (_ & [Δ' Φ' [=] _] & _).
      - apply ind_gens_typed; [ exact HΞ | exact Hfr | exact HE' | exact Hrec ].
      - exfalso; destruct (wf_gstack_cons_inv _ _ _ _ HΞ) as (_ & [Δ' Φ' [=] _] & _). }
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
    exists ΘR, linv ch (cs_deps r) (cs_k r) (cs_dom r) ΘR (cs_stack r).
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
    post_lcmd ch Θ K D B Ξ c r1 -> post_cmds ch (cs_deps r1) (cs_k r1) (cs_dom r1) (cs_bt r1) (cs_stack r1) cs r2 ->
    post_cmds ch Θ K D B Ξ (c :: cs) r2.
  Proof.
    intros Hac H1 H2 ΘR RbR Hli Hrb.
    pose proof (equiv_acc _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli)) Hac) as Hac'.
    destruct (H1 _ _ Hli Hrb) as [ΘR1 RbR1 (c1 & Hl & Hr1) Hli1 Hrb1 He1 Hg1].
    destruct (H2 _ _ Hli1 Hrb1) as [ΘR2 RbR2 Hr2 Hli2 Hrb2 He2 Hg2]; cbn beta in Hr2.
    apply (mk_cmd_post _ _ _ _ _ ΘR2 RbR2); [ econstructor; eassumption | exact Hli2 | exact Hrb2
                                            | eapply ext_trans; eassumption |].
    intros x Hx; destruct (Hg2 _ Hx) as [Hx1 | Hx1]; [| right; exact Hx1 ].
    destruct (Hg1 _ Hx1) as [Hx0 | Hx0]; [ left; exact Hx0 | right; exact (dom_grows Hli1 (proj1 Hrb1) Hr2 Hli2 _ Hx0) ].
  Qed.

  Lemma unit_pre {ch Θ K} : ginv ch Θ K -> exists ΘR, linv ch Θ K nil ΘR nil.
  Proof. intros G; exists nil; exact (nil_linv G). Qed.

  (** The imports run on the empty stack, from no binding, and leave the
      stack empty. *)
  Lemma unit_imports {ch Θ K imps r1} :
    ginv ch Θ K -> post_cmds ch Θ K nil bt_empty nil imps r1 ->
    exists ΘR1 RbR1, nil ⍮ nil ⍮ bt_empty ⍮ nil ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ imps ⇝* ΘR1 ⍮ nil ⍮ cs_bt r1 ⍮ RbR1 /\ cs_stack r1 = nil /\
      linv ch (cs_deps r1) (cs_k r1) (cs_dom r1) ΘR1 nil /\ rb_ok (cs_k r1) ΘR1 RbR1 /\
      ext Θ K (cs_deps r1) (cs_k r1) /\ grows Θ (cs_deps r1) (cs_dom r1).
  Proof.
    intros G Hp; destruct (Hp _ _ (nil_linv G) (rb_ok_nil K)) as [ΘR1 RbR1 Hr1 Hli1 Hrb1 He1 Hg1]; cbn beta in Hr1.
    pose proof (run_cmds_empty _ _ _ _ _ _ _ _ _ _ _ _ Hr1) as HΞ; rewrite HΞ in Hr1, Hli1.
    exists ΘR1, RbR1; exact (conj Hr1 (conj HΞ (conj Hli1 (conj Hrb1 (conj He1 Hg1))))).
  Qed.

  Lemma unit_gctx {ch Θ K imps r1} :
    ginv ch Θ K -> post_cmds ch Θ K nil bt_empty nil imps r1 -> ⊢ᵍ gds_restrict (cs_dom r1) (cs_deps r1) ⍮ nil.
  Proof. intros G Hp; destruct (unit_imports G Hp) as (ΘR1 & _ & _ & _ & Hli1 & _); exact (linv_restrict_gctx Hli1). Qed.

  (** The literals of the parameters, from the bindings the imports end
      with. *)
  Lemma unit_lits {ch Θ K imps r1 P0 P1} :
    ginv ch Θ K -> post_cmds ch Θ K nil bt_empty nil imps r1 ->
    tele_lits (nat_view (gds_restrict (cs_dom r1) (cs_deps r1)) nil (cs_bt r1)) P0 = lok P1 ->
    forall ΘR1, linv ch (cs_deps r1) (cs_k r1) (cs_dom r1) ΘR1 nil -> tele_lits_ok ΘR1 nil (cs_bt r1) P0 P1.
  Proof. intros G Hp El ΘR1 Hli1; unfold tele_lits_ok; rewrite (linv_nat_view Hli1); exact El. Qed.

  Lemma unit_body_pre {fp ch Θ K imps r1 P} :
    ginv (fp :: ch) Θ K -> post_cmds (fp :: ch) Θ K nil bt_empty nil imps r1 -> tele_ass P ->
    ⊢ gds_restrict (cs_dom r1) (cs_deps r1) ⍮ nil ⍮ P ->
    exists ΘR, linv (fp :: ch) (cs_deps r1) (cs_k r1) (cs_dom r1) ΘR (gs_push (q_abs fp nil) P nil).
  Proof.
    intros G Hp Htel HP; destruct (unit_imports G Hp) as (ΘR1 & _ & _ & _ & Hli1 & _).
    exists ΘR1; exact (proj2 (linv_push_unit Hli1 Htel HP)).
  Qed.

  Lemma unit_ok {fp ch Θ K imps P0 P cs r1 r2 mp U Ξ2} :
    post_cmds (fp :: ch) Θ K nil bt_empty nil imps r1 ->
    tele_lits (nat_view (gds_restrict (cs_dom r1) (cs_deps r1)) nil (cs_bt r1)) P0 = lok P ->
    tele_ass P ->
    ⊢ gds_restrict (cs_dom r1) (cs_deps r1) ⍮ nil ⍮ P ->
    acc_ok (gds_restrict (cs_dom r1) (cs_deps r1)) nil (tele_refs nil P0) ->
    post_cmds (fp :: ch) (cs_deps r1) (cs_k r1) (cs_dom r1) (cs_bt r1) (gs_push (q_abs fp nil) P nil) cs r2 ->
    cs_stack r2 = (mp, U) :: Ξ2 ->
    post_unit (fp :: ch) Θ K (imps, P0, cs) (ust (cs_deps r2) (cs_k r2) (cs_dom r2) (cs_bt r2) U).
  Proof.
    intros Hp1 El Htel HP Hac Hp2 HΞ G; cbn [us_deps us_k us_dom us_bt us_unit].
    destruct (unit_imports G Hp1) as (ΘR1 & RbR1 & Hr1 & _ & Hli1 & Hrb1 & He1 & Hg1).
    pose proof (equiv_acc _ _ _ _ (gds_equiv_sym _ _ (linv_equiv Hli1)) Hac) as Hac'.
    destruct (linv_push_unit Hli1 Htel HP) as [HP' Hli1'].
    destruct (Hp2 _ _ Hli1' Hrb1) as [ΘR2 RbR2 Hr2 Hli2 Hrb2 He2 Hg2]; cbn beta in Hr2.
    rewrite HΞ in Hr2, Hli2.
    destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr2) as [F HF]; injection HF as <- ->.
    destruct Hli2 as [G2 Hs2 Hd2 Hc2 _ _].
    apply (mk_unit_post _ _ _ _ _ RbR2 ΘR2);
      [ eapply ru_intro; [ exact Hr1 | exact (unit_lits G Hp1 El _ Hli1) | exact Htel | exact HP' | exact Hac' | exact Hr2 ]
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
    { ls_path : path
    ; ls_src : string
    ; ls_chain : ch' = ls_path :: ch
    ; ls_fresh : ~ In ls_path ch
    ; ls_load : load_path ls_path = Some ls_src }.

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
    | inleft (exist _ e _) => rerr (re_nat (gds_restrict D0 Θ0) Ξ0 (nat_view (gds_restrict D0 Θ0) Ξ0 B0) (priv_error e))
    | inright Hac with rc Θ0 K0 D0 B0 Ξ0 c H0 => {
      | rerr e => rerr (re_nat (gds_restrict D0 Θ0) Ξ0 (nat_view (gds_restrict D0 Θ0) Ξ0 B0) e)
      | rok (exist _ r1 Hr1, l1) with go (cs_deps r1) (cs_k r1) (cs_dom r1) (cs_bt r1) (cs_stack r1) cs' (cons_pre H0 Hr1) => {
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
    | right _ => rerr (re_msg ("duplicate name " ++ x))
    | left Hfr with check_typ (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A => {
      | inright _ => rerr (blame_error (find_level_blame fctx_none _ _ _ (pre_ctx H) A)
                            (mod_error (pre_gctx H) (ind_target (gds_restrict D Θ) Ξ) (A :: nil) (re_def_typ x Ξ A)))
      | inleft (exist _ i HA) with check_exp_typed (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A (ex_intro _ i HA) M => {
        | left HM => rok (da_ok (def_ok Hfr HM))
        | right _ => rerr (mod_error (pre_gctx H) (ind_target (gds_restrict D Θ) Ξ) (M :: nil) (re_def x Ξ A M)) } } }
  | ch, Θ, K, D, B, Ξ, cc_def x b pv A None, H with gs_fresh_dec x Ξ => {
    | right _ => rerr (re_msg ("duplicate name " ++ x))
    | left Hfr with check_typ (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A => {
      | inleft (exist _ i HA) => rok (da_ok (axiom_ok Hfr HA))
      | inright _ =>
          rerr (blame_error (find_level_blame fctx_none _ _ _ (pre_ctx H) A)
                  (mod_error (pre_gctx H) (ind_target (gds_restrict D Θ) Ξ) (A :: nil) (re_msg ("the type of axiom " ++ x ++ " is not a type")))) } }
  | ch, Θ, K, D, B, Ξ, cc_alias x pv Δ E, H with tele_ass_dec Δ => {
    | right _ => rerr (re_msg ("parameters of module " ++ x ++ " that are not assumptions"))
    | left Htel with check_ext (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) Δ => {
      | right _ =>
          rerr (tele_blame_error (find_tele_blame fctx_none _ _ _ (pre_ctx H) Δ)
                  (re_msg ("ill-formed parameters of module " ++ x)))
      | left HΔ with check_modexp (fctx_cmd B) (gds_restrict D Θ) Ξ (Δ ++ gs_tele Ξ) (ext_eq_ctx_left _ _ _ _ _ HΔ) E => {
        | right _ => rerr (re_msg ("ill-formed module expression for module " ++ x))
        | left HE with gs_fresh_dec x Ξ => {
          | right _ => rerr (re_msg ("duplicate name " ++ x))
          | left Hfr => rok (da_ok (alias_ok Htel HΔ HE Hfr)) } } } }
  | _, _, _, _, _, _, _, _ => rerr (re_msg "internal error: not a definition or an alias").

  (** The entries an import generates, in order, as [gens_run] declares
      them: written by no one, so with no privacy check. *)
  Fixpoint gens_impl (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (gs : list igen) (H : exists ΘR, linv ch Θ K D ΘR Ξ) {struct gs} : rres {Ξ' | post_gens ch Θ K D Ξ gs Ξ'} :=
    match gs as gs0 return rres {Ξ' | post_gens ch Θ K D Ξ gs0 Ξ'} with
    | nil => rok (exist _ Ξ gens_nil_ok)
    | ig_def d pv A M :: gs' =>
        match gs_fresh_dec d Ξ with
        | right _ => rerr (re_msg ("duplicate name " ++ d))
        | left Hfr =>
            match check_exp (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A M with
            | right _ => rerr (re_def d Ξ A M)
            | left HM =>
                match gens_impl ch Θ K D B (gs_add d (gs_def true pv Ξ A M) Ξ) gs' (gdef_pre H Hfr HM) with
                | rerr e => rerr e
                | rok (exist _ Ξ' Hp) => rok (exist _ Ξ' (gdef_ok Hfr HM Hp))
                end
            end
        end
    | ig_alias d pv E :: gs' =>
        match gs_fresh_dec d Ξ with
        | right _ => rerr (re_msg ("duplicate name " ++ d))
        | left Hfr =>
            match check_modexp (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) E with
            | right _ => rerr (re_msg ("ill-formed module expression for module " ++ d))
            | left HE =>
                match gens_impl ch Θ K D B (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ) gs'
                        (galias_pre H Hfr HE) with
                | rerr e => rerr e
                | rok (exist _ Ξ' Hp) => rok (exist _ Ξ' (galias_ok Hfr HE Hp))
                end
            end
        end
    | ig_ind_alias d pv Δ p Ns :: gs' =>
        match gs_fresh_dec d Ξ with
        | right _ => rerr (re_msg ("duplicate name " ++ d))
        | left Hfr =>
            match ind_alias_entry_dec (gds_restrict D Θ) Ξ (pre_gctx H) (qname_in (gs_path Ξ) d) pv Δ p Ns with
            | right _ => rerr (re_msg ("ill-formed inductive alias " ++ d))
            | left HE =>
                match gens_impl ch Θ K D B (gs_add d (ge_ind_alias pv (Δ ++ gs_tele Ξ) p Ns) Ξ) gs'
                        (gindalias_pre H Hfr HE) with
                | rerr e => rerr e
                | rok (exist _ Ξ' Hp) => rok (exist _ Ξ' (gindalias_ok Hfr HE Hp))
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
    match bt_nat B with
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
    | Some pq => re_not_ind pq
    | None => re_msg "the natural numbers must be bound to an inductive type, named by its path"
    end.

  (** A builtin binding, checked premise by premise: the module expression,
      then what it denotes. *)
  Equations builtin_step (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (k : string) (E : modexp) (H : exists ΘR, linv ch Θ K D ΘR Ξ) :
    rres {B' | post_cmd ch Θ K D B Ξ (cc_builtin k E) (cst Θ K D B' Ξ)} :=
  | ch, Θ, K, D, B, Ξ, k, E, H with string_dec k nat_kind => {
    | right _ => rerr (re_msg ("there is no builtin " ++ k))
    | left Hk with check_modexp (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) E => {
      | right _ => rerr (builtin_target_error E)
      | left HE with mdenote_impl (gds_restrict D Θ) Ξ (pre_gctx H) (gs_tele Ξ) E (dn_order_of_wf _ _ (pre_gctx H) _ _ _ HE) => {
        | inleft (exist _ (ds_ind nil p nil) Hm) with opt_case (ind_lookup (gds_restrict D Θ) Ξ p) => {
          | inright _ => rerr (re_not_ind p)
          | inleft (exist _ Dd Hl) with inspect (nat_shape Dd) => {
            | exist _ None _ => rerr (re_msg (nat_shape_msg p))
            | exist _ (Some (z, s)) Hs with inspect (is_nat_sort (ind_sort Dd)) => {
              | exist _ false _ => rerr (re_msg ("the natural numbers must be declared in Type@0, not " ++ ind_short p))
              | exist _ true Ek with inspect (bt_bind_nat B p) => {
                | exist _ None _ => rerr (re_msg (bound_msg B))
                | exist _ (Some B') Hb =>
                    rok (bt_cmd_ok (eq_rect _ (fun k0 => post_cmd ch Θ K D B Ξ (cc_builtin k0 E) (cst Θ K D B' Ξ))
                                     (builtin_ok HE Hm Hl Hs (proj1 (is_nat_sort_spec _) Ek) Hb) _ (eq_sym Hk))) } } } }
        | inleft (exist _ (ds_ind _ p _) _) => rerr (re_msg (nat_shape_msg (written_name E p)))
        | inleft _ => rerr (builtin_target_error E)
        | inright _ => rerr (builtin_target_error E) } } }.

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
    | Some pq => re_not_ind pq
    | None => re_msg ("inductive alias " ++ x ++ " must name an inductive type by its path")
    end.

  (** An inductive alias whose module expression is ill-formed although the
      module it applies is not: an inductive type applied past its uniform
      parameters is named as such. *)
  Definition alias_wf_error (x : string) (Θr : gdeps) (Ξ : gstack) (Hg : ⊢ᵍ Θr ⍮ Ξ) (Γ : ctx) (E : modexp)
      (Hh : Θr ⍮ Ξ ⍮ Γ ⊢ᵐ fst (me_unapps E) ≈ fst (me_unapps E)) : run_error :=
    match mdenote_impl Θr Ξ Hg Γ (fst (me_unapps E)) (dn_order_of_wf _ _ Hg _ _ _ Hh) with
    | inleft (exist _ (ds_ind Θ0 p Ns0) _) =>
        match ind_lookup Θr Ξ p with
        | Some Dp =>
            if Nat.ltb (ind_nu Dp) (List.length Ns0 + (List.length (snd (me_unapps E)) - List.length Θ0))
            then re_msg ("inductive alias " ++ x ++ ": more arguments than uniform parameters of " ++ ind_short p)
            else re_msg ("ill-formed inductive alias " ++ x)
        | None => re_msg ("ill-formed inductive alias " ++ x)
        end
    | _ => re_msg ("ill-formed inductive alias " ++ x)
    end.

  (** An inductive alias, checked premise by premise: its parameters, the
      module it applies, the module expression, what that denotes, and the
      entry it files. *)
  Equations indalias_step (ch : list path) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (x : string) (pv : bool) (Δ : ctx) (E : modexp) (H : exists ΘR, linv ch Θ K D ΘR Ξ) :
    rres {Ξ' | post_cmd ch Θ K D B Ξ (cc_ind_alias x pv Δ E) (cst Θ K D B Ξ')} :=
  | ch, Θ, K, D, B, Ξ, x, pv, Δ, E, H with check_ext (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) Δ => {
    | right _ => rerr (re_msg ("ill-formed inductive alias " ++ x))
    | left HΔ with check_modexp (fctx_cmd B) (gds_restrict D Θ) Ξ (Δ ++ gs_tele Ξ) (ext_eq_ctx_left _ _ _ _ _ HΔ) (fst (me_unapps E)) => {
      | right _ => rerr (alias_target_error x E)
      | left Hh with check_modexp (fctx_cmd B) (gds_restrict D Θ) Ξ (Δ ++ gs_tele Ξ) (ext_eq_ctx_left _ _ _ _ _ HΔ) E => {
        | right _ => rerr (alias_wf_error x _ _ (pre_gctx H) _ E Hh)
        | left HE with mdenote_impl (gds_restrict D Θ) Ξ (pre_gctx H) (Δ ++ gs_tele Ξ) E (dn_order_of_wf _ _ (pre_gctx H) _ _ _ HE) => {
          | inleft (exist _ (ds_ind Θ' p Ns) Hm) with gs_fresh_dec x Ξ => {
            | right _ => rerr (re_msg ("duplicate name " ++ x))
            | left Hfr with opt_case (ind_lookup (gds_restrict D Θ) Ξ p) => {
              | inright _ => rerr (re_not_ind p)
              | inleft (exist _ Dp Hp) with Compare_dec.le_dec (List.length Ns) (ind_nu Dp) => {
                | right _ => rerr (re_msg ("inductive alias " ++ x ++ ": more arguments than uniform parameters of " ++ ind_short p))
                | left _ with ind_alias_entry_dec (gds_restrict D Θ) Ξ (pre_gctx H) (ind_qname Ξ x) pv (Θ' ++ Δ) p Ns => {
                  | right _ => rerr (re_msg ("ill-formed inductive alias " ++ x))
                  | left HEn => rok (da_ok (indalias_ok HE Hm HEn Hfr)) } } } }
          | inleft _ => rerr (alias_target_error x E)
          | inright _ => rerr (alias_target_error x E) } } } }.

  (** Every expanded command but a module, which recurses on its body. *)
  Equations simple_step (ch : list path) (L : loader ch) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (c : ccmd) (H : exists ΘR, linv ch Θ K D ΘR Ξ) : rres ({r | post_cmd ch Θ K D B Ξ c r} * elog)%type :=
  | ch, L, Θ, K, D, B, Ξ, cc_def x b pv A M, H with defalias_step ch Θ K D B Ξ (cc_def x b pv A M) H => {
    | rerr e => rerr e
    | rok (exist _ Ξ' Hp) => rok (cmd_ok Hp, log_nil) }
  | ch, L, Θ, K, D, B, Ξ, cc_alias x pv Δ E, H with defalias_step ch Θ K D B Ξ (cc_alias x pv Δ E) H => {
    | rerr e => rerr e
    | rok (exist _ Ξ' Hp) => rok (cmd_ok Hp, log_nil) }
  | ch, L, Θ, K, D, B, Ξ, cc_mod _ _ _ _, H => rerr (re_msg "internal error: a module is run by its own step")
  | ch, L, Θ, K, D, B, Ξ, cc_load fp, H with opt_case (gds_lookup Θ fp) => {
    | inleft (exist _ U HU) with opt_case (kbt K fp) => {
      | inright _ => rerr (re_msg "internal error: a filed unit has no record")
      | inleft (exist _ BU HB) with inspect (bt_merge B BU) => {
        | exist _ None _ => rerr (re_msg (bound_msg B))
        | exist _ (Some B') Hm with in_dec path_eq_dec fp D => {
          | left Hin => rok (exist _ _ (load_in_ok Hin HU HB Hm), log_nil)
          | right Hnin with opt_case (kfind K fp) => {
            | inleft (exist _ Dfp HK) => rok (exist _ _ (load_hit_ok Hnin HU HK HB Hm), log_nil)
            | inright _ => rerr (re_msg "internal error: a filed unit has no closure") } } } }
    | inright Hn with in_dec path_eq_dec fp ch => {
      | left _ => rerr (re_cycle (cycle_chain fp ch))
      | right Hnch with opt_case (load_path fp) => {
        | inright _ => rerr (re_unit fp "cannot find unit")
        | inleft (exist _ src Hsrc) with opt_case (read src) => {
          | inright _ => rerr (re_unit fp "cannot parse unit")
          | inleft (exist _ prg Hprg) with path_eq_dec (prog_path prg) fp => {
            | right _ => rerr (re_unit fp "the file of the unit declares another unit")
            | left Hp with opt_case (to_core prg) => {
              | inright _ => rerr (re_unit fp "cannot elaborate unit")
              | inleft (exist _ u Hu) with L fp src Hnch Hsrc Θ K u (load_pre H Hn Hnch) => {
                | rerr e => rerr e
                | rok (exist _ r Hr, _) with inspect (bt_merge B (us_bt r)) => {
                  | exist _ None _ => rerr (re_msg (bound_msg B))
                  | exist _ (Some B') Hm => rok (exist _ _ (load_ok Hn Hnch Hsrc Hprg Hp Hu Hr Hm), log_nil) } } } } } } } }
  | ch, L, Θ, K, D, B, Ξ, cc_open E its, H with check_modexp (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) E => {
    | right _ => rerr (re_import (xe_target E))
    | left HE with inspect (import_gen _ _ (pre_gctx H) (gs_tele Ξ) E E HE true its) => {
      | exist _ (xfail e) _ => rerr (re_import e)
      | exist _ (xok gs) Eg with gens_impl ch Θ K D B Ξ gs H => {
        | rerr e => rerr e
        | rok (exist _ Ξ' Hgs) => rok (exist _ _ (import_ok (pre_gctx H) HE Eg Hgs), log_nil) } } }
  | ch, L, Θ, K, D, B, Ξ, cc_eval M (Some A), H
      with check_typ (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A => {
    | inright _ => rerr (blame_error (find_level_blame fctx_none _ _ _ (pre_ctx H) A)
                          (mod_error (pre_gctx H) (ind_target (gds_restrict D Θ) Ξ) (A :: nil) (re_eval_typ Ξ M A)))
    | inleft (exist _ i HA)
        with check_exp_typed (fctx_cmd B) (gds_restrict D Θ) Ξ (gs_tele Ξ) (pre_ctx H) A (ex_intro _ i HA) M => {
      | left HM => rok (exist _ _ (eval_check_ok HM), eval_log _ _ (fctx_cmd B _ _) (pre_gctx H) M A HM)
      | right _ => rerr (mod_error (pre_gctx H) (ind_target (gds_restrict D Θ) Ξ) (M :: nil) (re_eval_check Ξ M A)) } }
  | ch, L, Θ, K, D, B, Ξ, cc_eval M None, H
      with @type_infer_at (gc_mk (gds_restrict D Θ) Ξ) (fctx_cmd B (gds_restrict D Θ) Ξ) (gs_tele Ξ) (pre_ctx H) M (user_exp_all M) => {
    | inleft (exist _ A HA) => rok (exist _ _ (eval_infer_ok A HA), eval_log _ _ (fctx_cmd B _ _) (pre_gctx H) M A HA)
    | inright _ => rerr (mod_error (pre_gctx H) (ind_target (gds_restrict D Θ) Ξ) (M :: nil) (re_eval_infer Ξ M)) }
  | ch, L, Θ, K, D, B, Ξ, cc_builtin k p, H with builtin_step ch Θ K D B Ξ k p H => {
    | rerr e => rerr e
    | rok (exist _ B' Hp) => rok (cmd_ok Hp, log_nil) }
  | ch, L, Θ, K, D, B, Ξ, cc_ind_alias x pv Δ E, H with indalias_step ch Θ K D B Ξ x pv Δ E H => {
    | rerr e => rerr e
    | rok (exist _ Ξ' Hp) => rok (cmd_ok Hp, log_nil) }
  | ch, L, Θ, K, D, B, Ξ, cc_ind x pv R, H with cls_cons_in_dec (gds_restrict D Θ) Ξ (pre_gctx H) R => {
    | inr (exist _ (c, y, cw_code sf) _) => rerr (re_msg (cls_msg x c y sf))
    | inr (exist _ (c, y, cw_nested h) _) => rerr (re_nested x c y h)
    | inl (exist _ cs Hcls) with inspect (rec_arity_ok (rd_filed R cs)) => {
      | exist _ false _ =>
          rerr (re_msg ("a recursive argument is " ++ x ++ " applied to all its parameters"))
      | exist _ true _ with gs_fresh_dec x Ξ => {
        | right _ => rerr (re_msg ("duplicate name " ++ x))
        | left Hfr
            with ind_entry_dec (gds_restrict D Θ) Ξ (pre_gctx H)
                   (ind_qname Ξ x) pv (gs_ind Ξ (rd_filed R cs)) (ind_decl_shape Ξ R cs) => {
          | right _ =>
              match npar_blame (gds_restrict D Θ) Ξ (pre_gctx H)
                      (ind_uparams (gs_ind Ξ (rd_filed R cs))) (ind_sort (gs_ind Ξ (rd_filed R cs)))
                      (ind_nparams (gs_ind Ξ (rd_filed R cs))) with
              | Some (k, Δ, T, St) => rerr (re_ind_npar x k Δ T St)
              | None => rerr (re_msg ("ill-formed inductive declaration " ++ x))
              end
          | left HE with in_dec string_dec "rec"%string (List.map fst (ind_cons (gs_ind Ξ (rd_filed R cs)))) => {
            | left _ => rerr (re_msg ("rec is the recursor of " ++ x ++ ", not a constructor"))
            | right Hrec => rok (exist _ _ (ind_ok Hcls Hfr HE Hrec), log_nil) } } } } }.

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
    | Some e' => re_import e'
    | None => e
    end.

  Definition tele_error {Θ Ξ} (Hg : ⊢ᵍ Θ ⍮ Ξ) (S : skel) (Δ : ctx) (e : run_error) : run_error :=
    match tele_open_error Θ Ξ Hg (mod_chk Hg) S Δ with
    | Some e' => re_import e'
    | None => e
    end.

  (** A command with its literals generated, then run by [simple_step]. *)
  Definition lits_simple (ch : list path) (L : loader ch) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (c : ccmd) (H : exists ΘR, linv ch Θ K D ΘR Ξ) : rres ({r | post_lcmd ch Θ K D B Ξ c r} * elog)%type :=
    match inspect (cmd_lits (nat_view (gds_restrict D Θ) Ξ B) c) with
    | exist _ (lfail e) _ => rerr (re_lit e)
    | exist _ (lok c1) El =>
        match simple_step ch L Θ K D B Ξ c1 H with
        | rok (exist _ r Hp, l) => rok (exist _ r (lits_lift El Hp), l)
        | rerr e => rerr (open_error (pre_gctx H) c1 e)
        end
    end.

  Lemma cmd_lits_mod : forall nv x pv Δ0 Δ1 cs, tele_lits nv Δ0 = lok Δ1 -> cmd_lits nv (cc_mod x pv Δ0 cs) = lok (cc_mod x pv Δ1 cs).
  Proof. intros * E; cbn [cmd_lits]; rewrite E; reflexivity. Qed.

  #[derive(eliminator=no)]
  Equations run_cmd_impl (ch : list path) (L : loader ch) (Θ : gdeps) (K : kmap) (D : list path) (B : builtins) (Ξ : gstack)
    (c : ccmd) (H : exists ΘR, linv ch Θ K D ΘR Ξ) : rres ({r | post_lcmd ch Θ K D B Ξ c r} * elog)%type by struct c :=
  | ch, L, Θ, K, D, B, Ξ, cc_mod x pv Δ0 cs, H with inspect (tele_lits (nat_view (gds_restrict D Θ) Ξ B) Δ0) => {
    | exist _ (lfail e) _ => rerr (re_lit e)
    | exist _ (lok Δ) El with tele_ass_dec Δ => {
    | right _ => rerr (tele_error (pre_gctx H) (frame_skel Ξ) Δ (re_msg ("parameters of module " ++ x ++ " that are not assumptions")))
    | left Htel with check_ctx (fctx_cmd B) (gds_restrict D Θ) Ξ (pre_gctx H) (Δ ++ gs_tele Ξ) => {
      | right _ =>
          rerr (tele_error (pre_gctx H) (frame_skel Ξ) Δ (tele_blame_error (find_tele_blame fctx_none _ _ _ (pre_ctx H) Δ)
                  (re_msg ("ill-formed parameters of module " ++ x))))
      | left HΔ with gs_fresh_dec x Ξ => {
        | right _ => rerr (re_msg ("duplicate name " ++ x))
        | left Hfr with cmds_step ch (run_cmd_impl ch L) Θ K D B (gs_push (qname_in (gs_path Ξ) x) Δ Ξ) cs
                          (mod_pre H Htel Hfr HΔ) => {
          | rerr e => rerr e
          | rok (exist _ r Hr, l) with list_case (cs_stack r) => {
            | inleft (existT _ (mp, U) (exist _ _ HΞ)) =>
                rok (exist _ _ (lits_lift (cmd_lits_mod _ x pv _ _ cs El) (mod_ok Htel Hfr HΔ Hr HΞ)), l)
            | inright _ => rerr (re_msg "internal error: a module body lost its frame") } } } } } }
  | ch, L, Θ, K, D, B, Ξ, cc_def x b pv A M, H => lits_simple ch L Θ K D B Ξ (cc_def x b pv A M) H
  | ch, L, Θ, K, D, B, Ξ, cc_alias x pv Δ E, H => lits_simple ch L Θ K D B Ξ (cc_alias x pv Δ E) H
  | ch, L, Θ, K, D, B, Ξ, cc_load fp, H => lits_simple ch L Θ K D B Ξ (cc_load fp) H
  | ch, L, Θ, K, D, B, Ξ, cc_open E its, H => lits_simple ch L Θ K D B Ξ (cc_open E its) H
  | ch, L, Θ, K, D, B, Ξ, cc_eval M oA, H => lits_simple ch L Θ K D B Ξ (cc_eval M oA) H
  | ch, L, Θ, K, D, B, Ξ, cc_ind x pv R, H => lits_simple ch L Θ K D B Ξ (cc_ind x pv R) H
  | ch, L, Θ, K, D, B, Ξ, cc_builtin k p, H => lits_simple ch L Θ K D B Ξ (cc_builtin k p) H
  | ch, L, Θ, K, D, B, Ξ, cc_ind_alias x pv Δ E, H => lits_simple ch L Θ K D B Ξ (cc_ind_alias x pv Δ E) H.

  Definition run_cmds_impl (ch : list path) (L : loader ch) := cmds_step ch (run_cmd_impl ch L).

  Definition run_unit_step (ch : list path) (L : loader ch) (Θ : gdeps) (K : kmap) (u : cunit)
    (H : ginv ch Θ K) : rres ({r | post_unit ch Θ K u r} * elog)%type :=
    match ch as ch0 return loader ch0 -> ginv ch0 Θ K -> rres ({r | post_unit ch0 Θ K u r} * elog)%type with
    | nil => fun _ _ => rerr (re_msg "internal error: no unit to run")
    | fp :: ch0 => fun L H =>
    match u as u0 return rres ({r | post_unit (fp :: ch0) Θ K u0 r} * elog)%type with
    | (imps, P0, cs) =>
        match run_cmds_impl (fp :: ch0) L Θ K nil bt_empty nil imps (unit_pre H) with
        | rerr e => rerr e
        | rok (exist _ r1 Hr1, l1) =>
            match inspect (tele_lits (nat_view (gds_restrict (cs_dom r1) (cs_deps r1)) nil (cs_bt r1)) P0) with
            | exist _ (lfail e) _ => rerr (re_nat (gds_restrict (cs_dom r1) (cs_deps r1)) nil (nat_view (gds_restrict (cs_dom r1) (cs_deps r1)) nil (cs_bt r1)) (re_lit e))
            | exist _ (lok P) El =>
            match tele_ass_dec P with
            | right _ => rerr (re_nat (gds_restrict (cs_dom r1) (cs_deps r1)) nil (nat_view (gds_restrict (cs_dom r1) (cs_deps r1)) nil (cs_bt r1))
                                (tele_error (unit_gctx H Hr1) nil P (re_msg "unit parameters that are not assumptions")))
            | left Htel =>
            match check_ctx (fctx_cmd (cs_bt r1)) (gds_restrict (cs_dom r1) (cs_deps r1)) nil (unit_gctx H Hr1) P with
            | right _ =>
                rerr (re_nat (gds_restrict (cs_dom r1) (cs_deps r1)) nil (nat_view (gds_restrict (cs_dom r1) (cs_deps r1)) nil (cs_bt r1))
                        (tele_error (unit_gctx H Hr1) nil P (tele_blame_error (find_tele_blame fctx_none _ _ _ (wf_ctx_empty _ _ (unit_gctx H Hr1)) P)
                        (re_msg "ill-formed unit parameters"))))
            | left HP =>
            match refs_check (gds_restrict (cs_dom r1) (cs_deps r1)) nil (unit_gctx H Hr1) (tele_refs nil P0) with
            | inleft (exist _ e _) => rerr (re_nat (gds_restrict (cs_dom r1) (cs_deps r1)) nil (nat_view (gds_restrict (cs_dom r1) (cs_deps r1)) nil (cs_bt r1)) (priv_error e))
            | inright Hac =>
                match run_cmds_impl (fp :: ch0) L (cs_deps r1) (cs_k r1) (cs_dom r1) (cs_bt r1) (gs_push (q_abs fp nil) P nil) cs
                        (unit_body_pre H Hr1 Htel HP) with
                | rerr e => rerr e
                | rok (exist _ r2 Hr2, l2) =>
                    match list_case (cs_stack r2) with
                    | inleft (existT _ (mp, U) (exist _ _ HΞ)) =>
                        rok (exist _ _ (unit_ok Hr1 El Htel HP Hac Hr2 HΞ), log_app l1 l2)
                    | inright _ => rerr (re_msg "internal error: a unit body lost its frame")
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
    | None => rerr (re_msg "cannot elaborate the program")
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

  (** A command runs with its literals, as expanded. *)
  Theorem run_cmd_impl_sound : forall ch L Θ K D B Ξ c H r ΘR RbR,
      linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR -> run_cmd_impl ch L Θ K D B Ξ c H = rok r ->
      exists c1 ΘR' RbR', cmd_lits_ok ΘR Ξ B c c1 /\
        ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c1 ⇝ ΘR' ⍮ cs_stack (proj1_sig (fst r)) ⍮ cs_bt (proj1_sig (fst r)) ⍮ RbR' /\
        linv ch (cs_deps (proj1_sig (fst r))) (cs_k (proj1_sig (fst r))) (cs_dom (proj1_sig (fst r))) ΘR' (cs_stack (proj1_sig (fst r))) /\ logs_ok (proj1_sig (snd r)).
  Proof.
    intros * Hli Hrb _; destruct r as [[r Hr] [l Hl]]; destruct (Hr _ _ Hli Hrb) as [ΘR' RbR' (c1 & ? & ?) ? _ _ _]; cbn; eauto 9.
  Qed.

  Theorem run_cmds_impl_sound : forall ch L Θ K D B Ξ cs H r ΘR RbR,
      linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR -> run_cmds_impl ch L Θ K D B Ξ cs H = rok r ->
      exists ΘR' RbR', ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR' ⍮ cs_stack (proj1_sig (fst r)) ⍮ cs_bt (proj1_sig (fst r)) ⍮ RbR' /\
        linv ch (cs_deps (proj1_sig (fst r))) (cs_k (proj1_sig (fst r))) (cs_dom (proj1_sig (fst r))) ΘR' (cs_stack (proj1_sig (fst r))) /\ logs_ok (proj1_sig (snd r)).
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
      executable loads only where the derivation does ([rc_load]), and
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
    | HH0 : _ ⍮ _ ⍮ _ ⊢ᵐ E ≈ E, Hm0 : mdenote _ _ _ E (ds_ind nil ?p0 nil), Hl0 : ind_lookup _ _ ?p0 = Some ?Dd0,
      Hs0 : nat_shape ?Dd0 = Some _, Hsort0 : ind_sort ?Dd0 = nat_sort, Hb0 : bt_bind_nat _ ?p0 = Some _ |- _ =>
        rename HH0 into HH; rename Hm0 into Hm; rename Hl0 into Hl; rename Hs0 into Hs; rename Hsort0 into Hsort;
        rename Hb0 into Hb; rename p0 into p; rename Dd0 into Dd
    end.
    pose proof (linv_equiv Hli) as He; pose proof (linv_restrict_gctx Hli) as Hgr.
    pose proof (gds_equiv_mdenote _ _ _ _ _ _ He Hm) as Hm'.
    simp builtin_step.
    destruct (string_dec nat_kind nat_kind) as [Hk | Hk]; [| contradiction ]; simp builtin_step.
    destruct (check_modexp _ _ _ _ _ E) as [HE' | HE']; simp builtin_step;
      [| exfalso; exact (HE' (equiv_modexp _ _ _ _ _ He Hgr HH)) ].
    destruct (mdenote_impl _ _ _ _ _ _) as [[R HR] | HN]; [| exfalso; exact (HN _ Hm') ].
    pose proof (proj1 (mdenote_functional_all _ _ Hgr) _ _ _ HR _ Hm') as ->.
    simp builtin_step.
    assert (Hl' : ind_lookup (gds_restrict D Θ) Ξ p = Some Dd)
      by (rewrite ind_lookup_unfold in *; rewrite <- (gds_equiv_module _ _ _ _ He); exact Hl).
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
    pose proof (linv_equiv Hli) as He; pose proof (linv_restrict_gctx Hli) as Hgr.
    match goal with
    | HH0 : _ ⍮ _ ⍮ _ ⊢ᵐ E ≈ E, Hm0 : mdenote _ _ _ E (ds_ind _ _ _), HEn0 : _ ⍮ _ ⍮ _ ⊢ᵉ ge_ind_alias _ _ _ _ |- _ =>
        rename HH0 into HH; rename Hm0 into Hm; rename HEn0 into HEn
    end.
    pose proof (equiv_modexp _ _ _ _ _ He Hgr HH) as HE0.
    pose proof (gds_equiv_mdenote _ _ _ _ _ _ He Hm) as Hm'.
    rewrite List.app_assoc in HEn.
    pose proof (equiv_ind_alias_entry _ _ _ _ _ _ _ _ He Hgr HEn) as HEn0.
    destruct (wf_gentry_ind_alias_inv _ _ _ _ _ _ _ HEn0) as (_ & _ & D0 & Hl0 & Hle0 & _).
    simp indalias_step.
    destruct (check_ext _ _ _ _ _ Δ) as [HΔ | HΔ]; simp indalias_step;
      [| exfalso; exact (HΔ (ext_of_ctx _ _ _ _ (presup_modexp_eq_ctx HE0))) ].
    destruct (check_modexp _ _ _ _ _ (fst (me_unapps E))) as [Hh | Hh]; simp indalias_step;
      [| exfalso; exact (Hh (me_unapps_head_wf _ _ _ _ HE0)) ].
    destruct (check_modexp _ _ _ _ _ E) as [HE' | HE']; simp indalias_step; [| exfalso; exact (HE' HE0) ].
    destruct (mdenote_impl _ _ _ _ _ _) as [[R HR] | HN]; [| exfalso; exact (HN _ Hm') ].
    pose proof (proj1 (mdenote_functional_all _ _ Hgr) _ _ _ HR _ Hm') as ->.
    simp indalias_step.
    destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp indalias_step.
    destruct (opt_case (ind_lookup _ _ _)) as [[D1 Hl1] | Hl1]; [| congruence ].
    assert (D1 = D0) as -> by congruence.
    simp indalias_step.
    destruct (Compare_dec.le_dec _ _) as [Hle' | Hle']; [| contradiction ].
    simp indalias_step.
    match goal with |- context [ind_alias_entry_dec ?a ?b ?c ?d ?e ?f ?g ?h] => destruct (ind_alias_entry_dec a b c d e f g h) as [HE'' | HE''] end;
      [| contradiction ].
    simp indalias_step; eexists; reflexivity.
  Qed.

  Lemma alias_complete : forall ch B RbR ΘR Ξ x pv Δ E B' RbR' ΘR' Ξ' Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_alias x pv Δ E ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, defalias_step ch Θ K D B Ξ (cc_alias x pv Δ E) H = rok r.
  Proof.
    intros * Hli Hr; inversion Hr as [| | | ? ? ? ? ? ? ? ? ? Htel HΔ HE Hfr | | | | | | | |]; subst; simp defalias_step.
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
    induction 1 as [Ξ | Ξ d pv A M gs Ξ' HM Hfr Hg IH | Ξ d pv E gs Ξ' HE Hfr Hg IH | Ξ d pv Δ p Ns gs Ξ' HE Hfr Hg IH];
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
    - destruct (gs_fresh_dec d Ξ) as [Hfr' | Hfr']; [| contradiction ].
      match goal with |- context [ind_alias_entry_dec ?a ?b ?c ?d ?e ?f ?g ?h] => destruct (ind_alias_entry_dec a b c d e f g h) as [HE' | HE'] end;
        [| exfalso; apply HE'; exact (equiv_ind_alias_entry _ _ _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HE) ].
      destruct (IH ch Θ K D B (gindalias_pre Hx Hfr' HE') (proj2 (gindalias_step Hli Hfr' HE'))) as [[Ξ1 Hp] E1].
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
    | cc_ind _ _ _ => 6
    | cc_builtin _ _ => 7
    | cc_ind_alias _ _ _ _ => 8
    end.

  Lemma cmd_lits_head : forall nv c c1, cmd_lits nv c = lok c1 -> ccmd_head c1 = ccmd_head c.
  Proof.
    intros nv [x b pv A M | x pv Δ cs | x pv Δ E | fp | E its | M oA | x pv R | k H | x pv Δ H] c1 El;
      cbn [cmd_lits] in El;
      repeat match goal with
        | H : lbind ?m _ = lok _ |- _ => destruct m; cbn [lbind] in H; [| discriminate ]
        end;
      injection El as <-; reflexivity.
  Qed.

  Lemma cmd_lits_mod_inv : forall nv x pv Δ0 cs c1, cmd_lits nv (cc_mod x pv Δ0 cs) = lok c1 ->
      exists Δ1, tele_lits nv Δ0 = lok Δ1 /\ c1 = cc_mod x pv Δ1 cs.
  Proof.
    intros * El; cbn [cmd_lits] in El; destruct (tele_lits nv Δ0) as [Δ1 | e]; cbn [lbind] in El; [| discriminate ].
    injection El as <-; eauto.
  Qed.

  Lemma lits_simple_complete {ch L Θ K D B ΘR Ξ c c1} (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ) :
    linv ch Θ K D ΘR Ξ -> cmd_lits_ok ΘR Ξ B c c1 ->
    (exists r, simple_step ch L Θ K D B Ξ c1 H = rok r) ->
    exists r, lits_simple ch L Θ K D B Ξ c H = rok r.
  Proof.
    intros Hli Hl [r Er]; unfold lits_simple.
    pose proof (lits_eq Hli Hl) as El.
    destruct (inspect (cmd_lits _ c)) as [[c1' | e] El']; [ assert (c1' = c1) as -> by congruence | exfalso; congruence ].
    rewrite Er; destruct r as [[r Hp] l]; eexists; reflexivity.
  Qed.

  (** Every command but a module runs by [simple_step] once its literals
      are generated. *)
  Lemma nonmod_complete {ch L Θ K D B ΘR Ξ c c1} (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ) :
    ccmd_head c1 <> 1 -> linv ch Θ K D ΘR Ξ -> cmd_lits_ok ΘR Ξ B c c1 ->
    (exists r, simple_step ch L Θ K D B Ξ c1 H = rok r) ->
    exists r, run_cmd_impl ch L Θ K D B Ξ c H = rok r.
  Proof.
    intros Hc1 Hli Hl Hs.
    assert (Hc : ccmd_head c <> 1) by (rewrite <- (cmd_lits_head _ _ _ Hl); exact Hc1).
    destruct c; try (exfalso; apply Hc; reflexivity); simp run_cmd_impl; eapply lits_simple_complete; eassumption.
  Qed.

  Theorem run_impl_complete :
    (forall ch B RbR ΘR Ξ c' B' RbR' ΘR' Ξ', ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c' ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
       forall Hacc Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ), linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
       forall c, cmd_lits_ok ΘR Ξ B c c' ->
         exists r, run_cmd_impl ch (loader_of ch Hacc) Θ K D B Ξ c H = rok r) /\
    (forall ch B RbR ΘR Ξ cs B' RbR' ΘR' Ξ', ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
       forall Hacc Θ K D (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ), linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR ->
         exists r, run_cmds_impl ch (loader_of ch Hacc) Θ K D B Ξ cs H = rok r) /\
    (forall ch u B' RbU ΘU U, run_unit ch u B' RbU ΘU U ->
       forall Hacc Θ K (H : ginv ch Θ K), exists r, run_unit_impl ch Hacc Θ K u H = rok r).
  Proof.
    apply run_mut_dind.
    - (* a definition *)
      intros ch B Rb ΘR Ξ x b pv A M HM Hfr Hacc Θ K D H Hli Hrb c Hl.
      refine (nonmod_complete H _ Hli Hl _); [ cbn; discriminate |]; simp simple_step.
      destruct (def_complete ch B Rb ΘR Ξ x b pv A (Some M) _ _ _ _ Θ K D H Hli ltac:(constructor; eassumption)) as [[Ξ1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* an axiom *)
      intros ch B Rb ΘR Ξ x b pv A i HA Hfr Hacc Θ K D H Hli Hrb c Hl.
      refine (nonmod_complete H _ Hli Hl _); [ cbn; discriminate |]; simp simple_step.
      destruct (def_complete ch B Rb ΘR Ξ x b pv A None _ _ _ _ Θ K D H Hli ltac:(econstructor; eassumption)) as [[Ξ1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* a module *)
      intros ch B Rb B' Rb' ΘR Ξ x pv Δ cs ΘR' mp U Htel HΔ Hfr Hr IH Hacc Θ K D H Hli Hrb c Hl.
      pose proof (lits_eq Hli Hl) as El.
      assert (Hc : ccmd_head c = 1) by (rewrite <- (cmd_lits_head _ _ _ El); reflexivity).
      destruct c as [| x0 pv0 Δ0 cs0 | | | | | | |]; try discriminate.
      destruct (cmd_lits_mod_inv _ _ _ _ _ _ El) as (Δ1 & EΔ1 & [= <- <- <- <-]).
      simp run_cmd_impl.
      destruct (inspect (tele_lits _ Δ0)) as [[Δ1' | e] EΔ1']; [ assert (Δ1' = Δ) as -> by congruence | exfalso; congruence ].
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
      destruct (list_case (cs_stack r)) as [[[mp' U'] [Ξ2 HΞ]] | HΞ]; simp run_cmd_impl; [ eexists; reflexivity | congruence ].
    - (* an alias *)
      intros ch B Rb ΘR Ξ x pv Δ E Htel HΔ HE Hfr Hacc Θ K D H Hli Hrb c Hl.
      refine (nonmod_complete H _ Hli Hl _); [ cbn; discriminate |]; simp simple_step.
      destruct (alias_complete ch B Rb ΘR Ξ x pv Δ E _ _ _ _ Θ K D H Hli ltac:(constructor; assumption)) as [[Ξ1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* a load of a unit the judgment has *)
      intros ch B Rb B' ΘR Ξ fp U BU HU HBU Hm Hacc Θ K D H Hli Hrb c Hl.
      refine (nonmod_complete H _ Hli Hl _); [ cbn; discriminate |]; simp simple_step.
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
      intros ch B Rb B' ΘR Ξ fp src prg u BU RbU ΘU U Hn Hnin Hld Hrd Hp Ht Hu IH Hm Hacc Θ K D H Hli Hrb c Hl.
      refine (nonmod_complete H _ Hli Hl _); [ cbn; discriminate |]; simp simple_step.
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
      intros ch B Rb ΘR Ξ E its gs Ξ' HE Hgen Hgs Hacc Θ K D H Hli Hrb c Hl.
      refine (nonmod_complete H _ Hli Hl _); [ cbn; discriminate |]; simp simple_step.
      match goal with |- context [check_modexp ?f ?a ?b ?c ?d ?e] => destruct (check_modexp f a b c d e) as [HE' | HE'] end;
        [| exfalso; apply HE'; exact (equiv_modexp _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HE) ].
      simp simple_step.
      pose proof (open_gens_equiv _ _ _ _ _ _ _ _ (linv_equiv Hli) Hgen) as Hgen'.
      apply (import_gen_spec _ _ (pre_gctx H) _ _ _ HE') in Hgen' as Eg.
      destruct (inspect _) as [[gs1 | e] Eg']; [ assert (gs1 = gs) as -> by congruence | exfalso; congruence ].
      simp simple_step.
      destruct (gens_complete _ _ _ _ Hgs _ _ _ _ B H Hli) as [[Ξ1 Hp1] E1]; rewrite E1; simp simple_step.
      eexists; reflexivity.
    - (* a declaration: its classification, its entry *)
      intros ch B Rb ΘR Ξ x pv R cs Hcls Hfr HE Hacc Θ K D H Hli Hrb c Hl.
      refine (nonmod_complete H _ Hli Hl _); [ cbn; discriminate |]; simp simple_step.
      pose proof (equiv_cls_cons_in _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) Hcls) as HclsR.
      destruct (cls_cons_in_dec (gds_restrict D Θ) Ξ (pre_gctx H) R) as [[cs' Hcls'] | [[[c' y] sf] Hn]];
        [| exfalso; exact (Hn _ HclsR) ].
      pose proof (cls_cons_in_functional _ _ _ _ _ Hcls' HclsR) as ->; simp simple_step.
      pose proof (wf_gentry_ind_base _ _ _ _ _ _ HE) as HE0.
      destruct (inspect _) as [[|] Ea];
        [| exfalso; pose proof (rec_arity_of_entry _ _ _ _ _ HE0) as Ht; rewrite rec_arity_gs_ind in Ht; congruence ].
      simp simple_step.
      destruct (gs_fresh_dec x Ξ) as [Hfr' | Hfr']; [| contradiction ]; simp simple_step.
      match goal with |- context [ind_entry_dec ?a ?b ?c ?d ?e ?f ?g] => destruct (ind_entry_dec a b c d e f g) as [HE' | HE'] end;
        [| exfalso; apply HE'; exact (equiv_gentry_ind _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HE0) ].
      simp simple_step.
      destruct (in_dec string_dec "rec"%string _) as [Hr | Hr];
        [ exfalso; exact (wf_gentry_ind_rec_fresh _ _ _ _ _ _ HE Hr) | simp simple_step; eexists; reflexivity ].
    - (* a builtin binding *)
      intros ch B Rb B' ΘR Ξ E p Dd z s HEw Hm Hld Hs Hsort Hb Hacc Θ K D H Hli Hrb c Hl.
      refine (nonmod_complete H _ Hli Hl _); [ cbn; discriminate |]; simp simple_step.
      destruct (builtin_complete ch B Rb ΘR Ξ nat_kind E _ _ _ _ Θ K D H Hli ltac:(econstructor; eassumption)) as [[B1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* an inductive alias *)
      intros ch B Rb ΘR Ξ x pv Δ E Θ' p Ns HEw Hm HE Hfr Hacc Θ K D H Hli Hrb c Hl.
      refine (nonmod_complete H _ Hli Hl _); [ cbn; discriminate |]; simp simple_step.
      destruct (indalias_complete ch B Rb ΘR Ξ x pv Δ E _ _ _ _ Θ K D H Hli ltac:(econstructor; eassumption)) as [[Ξ1 Hp] Er].
      rewrite Er; simp simple_step; eexists; reflexivity.
    - (* an ascribed eval *)
      intros ch B Rb ΘR Ξ M A HM Hacc Θ K D H Hli Hrb c Hl.
      refine (nonmod_complete H _ Hli Hl _); [ cbn; discriminate |]; simp simple_step.
      pose proof (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HM) as HM0.
      match goal with |- context [check_typ ?f ?a ?b ?c ?d ?e] => destruct (check_typ f a b c d e) as [[j HA'] | HA'] end;
        simp simple_step; [| exfalso; exact (not_exp_of_not_typ _ _ _ _ _ HA' HM0) ].
      match goal with |- context [check_exp_typed ?z ?a ?b ?c ?d ?e ?f ?g] => destruct (check_exp_typed z a b c d e f g) as [HM' | HM'] end;
        simp simple_step.
      { eexists; reflexivity. }
      exfalso; exact (HM' HM0).
    - (* an inferred eval: failure of inference contradicts its completeness *)
      intros ch B Rb ΘR Ξ M A HM Hacc Θ K D H Hli Hrb c Hl.
      refine (nonmod_complete H _ Hli Hl _); [ cbn; discriminate |]; simp simple_step.
      match goal with |- context [@type_infer_at ?g ?f ?G ?a ?b ?c] => destruct (@type_infer_at g f G a b c) as [[A' HA'] | Hno] end;
        simp simple_step.
      { eexists; reflexivity. }
      exfalso.
      pose proof (equiv_exp _ _ _ _ _ _ (linv_equiv Hli) (linv_restrict_gctx Hli) HM) as HM'.
      destruct (@alg_type_infer_complete (gc_mk (gds_restrict D Θ) Ξ) (gs_tele Ξ) A M (user_exp_all M) HM') as (B0 & HB & _).
      exact (Hno B0 HB).
    - intros ch B Rb ΘR Ξ Hacc Θ K D H Hli Hrb; unfold run_cmds_impl; simp cmds_step; eexists; reflexivity.
    - (* a sequence: the head's result is the judgment's, by determinism *)
      intros ch B Rb ΘR Ξ c c1 cs B1 Rb1 ΘR1 Ξ1 B2 Rb2 ΘR2 Ξ2 Hac Hl Hc IHc Hcs IHcs Hacc Θ K D H Hli Hrb; unfold run_cmds_impl; simp cmds_step.
      match goal with |- context [refs_check ?a ?b ?c ?d] => destruct (refs_check a b c d) as [[e Hq] | Hac'] end;
        simp cmds_step; [ exfalso; apply Hq; exact (equiv_acc _ _ _ _ (linv_equiv Hli) Hac) |].
      destruct (IHc Hacc Θ K D H Hli Hrb c Hl) as [[[r1 Hp1] l1] E1]; rewrite E1; simp cmds_step.
      destruct (Hp1 _ _ Hli Hrb) as [ΘR1' RbR1' (c1' & Hl' & Hr1) Hli1 Hrb1 _ _].
      unfold cmd_lits_ok in Hl, Hl'; rewrite Hl in Hl'; injection Hl' as <-.
      destruct (run_cmd_functional load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc Hr1) as (<- & HΞ1 & HB1 & HR1); subst Ξ1 B1 Rb1.
      destruct (IHcs Hacc _ _ _ (cons_pre H Hp1) Hli1 Hrb1) as [[[r2 Hp2] l2] E2]; unfold run_cmds_impl in E2; simp cmds_step in E2; rewrite E2.
      simp cmds_step; eexists; reflexivity.
    - (* a unit *)
      intros fp ch B1 Rb1 B2 Rb2 imps P0 P cs ΘR1 ΘR2 mp U Hi IHi HPl Htel HP Hac Hb IHb Hacc Θ K H.
      rewrite run_unit_impl_unfold; cbn [run_unit_step].
      destruct (IHi Hacc Θ K nil (unit_pre H) (nil_linv H) (rb_ok_nil K)) as [[[r1 Hp1] l1] E1]; rewrite E1; cbv beta iota.
      destruct (Hp1 _ _ (nil_linv H) (rb_ok_nil K)) as [ΘR1' RbR1' Hr1 Hli1 Hrb1 _ _]; cbn beta in Hr1.
      destruct (run_cmds_functional load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi Hr1) as (<- & HΞ & HB & HR);
        rewrite <- HΞ in Hli1.
      subst B1 Rb1.
      pose proof HPl as HPl'; unfold tele_lits_ok in HPl'; rewrite (linv_nat_view Hli1) in HPl'.
      destruct (inspect (tele_lits _ P0)) as [[P1' | e] El]; [ assert (P1' = P) as -> by congruence | exfalso; congruence ].
      cbv beta iota.
      destruct (tele_ass_dec P) as [Htel' | Htel']; [| contradiction ]; cbv beta iota.
      match goal with |- context [check_ctx ?f ?a ?b ?c ?d] => destruct (check_ctx f a b c d) as [HP' | HP'] end;
        [| exfalso; apply HP'; exact (equiv_ctx _ _ _ _ (linv_equiv Hli1) (linv_restrict_gctx Hli1) HP) ].
      match goal with |- context [refs_check ?a ?b ?c ?d] => destruct (refs_check a b c d) as [[e Hq] | Hac'] end;
        [ exfalso; apply Hq; exact (equiv_acc _ _ _ _ (linv_equiv Hli1) Hac) | cbv beta iota ].
      destruct (linv_push_unit Hli1 Htel' HP') as [_ Hli1'].
      destruct (IHb Hacc _ _ _ (unit_body_pre H Hp1 Htel' HP') Hli1' Hrb1) as [[[r2 Hp2] l2] E2]; rewrite E2; cbv beta iota.
      destruct (Hp2 _ _ Hli1' Hrb1) as [ΘR2' RbR2' Hr2 _ _ _ _]; cbn beta in Hr2; destruct (run_cmds_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr2) as [F HF].
      destruct (list_case (cs_stack r2)) as [[[mp' U'] [Ξ2 HΞ2]] | HΞ2]; [ eexists; reflexivity | congruence ].
  Qed.

  (** The result is the judgment's, by determinism. *)
  Corollary run_cmd_impl_complete : forall ch B RbR ΘR Ξ c0 c B' RbR' ΘR' Ξ' Hacc Θ K D
      (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR -> cmd_lits_ok ΘR Ξ B c0 c ->
      ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, run_cmd_impl ch (loader_of ch Hacc) Θ K D B Ξ c0 H = rok r /\ cs_stack (proj1_sig (fst r)) = Ξ' /\
        cs_bt (proj1_sig (fst r)) = B' /\
        linv ch (cs_deps (proj1_sig (fst r))) (cs_k (proj1_sig (fst r))) (cs_dom (proj1_sig (fst r))) ΘR' Ξ' /\
        rb_ok (cs_k (proj1_sig (fst r))) ΘR' RbR'.
  Proof.
    intros * Hli Hrb Hl Hr; destruct (proj1 run_impl_complete _ _ _ _ _ _ _ _ _ _ Hr Hacc _ _ _ H Hli Hrb _ Hl) as [r E].
    exists r; split; [ exact E |].
    destruct r as [[r Hp] l]; destruct (Hp _ _ Hli Hrb) as [ΘR'' RbR'' (c1' & Hl' & Hr') Hli' Hrb' _ _].
    cbn [proj1_sig fst].
    unfold cmd_lits_ok in Hl, Hl'; rewrite Hl in Hl'; injection Hl' as <-.
    destruct (run_cmd_functional load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr Hr') as (<- & HΞ & HB & <-).
    rewrite <- HΞ in Hli'; split; [ symmetry; exact HΞ | split; [ symmetry; exact HB | split; assumption ] ].
  Qed.

  Corollary run_cmds_impl_complete : forall ch B RbR ΘR Ξ cs B' RbR' ΘR' Ξ' Hacc Θ K D
      (H : exists ΘR0, linv ch Θ K D ΘR0 Ξ),
      linv ch Θ K D ΘR Ξ -> rb_ok K ΘR RbR -> ΘR ⍮ Ξ ⍮ B ⍮ RbR ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* ΘR' ⍮ Ξ' ⍮ B' ⍮ RbR' ->
      exists r, run_cmds_impl ch (loader_of ch Hacc) Θ K D B Ξ cs H = rok r /\ cs_stack (proj1_sig (fst r)) = Ξ' /\
        cs_bt (proj1_sig (fst r)) = B' /\
        linv ch (cs_deps (proj1_sig (fst r))) (cs_k (proj1_sig (fst r))) (cs_dom (proj1_sig (fst r))) ΘR' Ξ' /\
        rb_ok (cs_k (proj1_sig (fst r))) ΘR' RbR'.
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
    intros * Hu; destruct (proj2 (proj2 run_impl_complete) _ _ _ _ _ _ Hu Hacc _ _ H) as [r E].
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
         ⊢ᵍ ev_deps e ⍮ ev_stack e /\ ev_deps e ⍮ ev_stack e ⍮ gs_tele (ev_stack e) ⊢ ev_exp e : ev_typ e /\
         nbe (ev_deps e) (ev_stack e) (gs_tele (ev_stack e)) (ev_exp e) (ev_typ e) (ev_nf e)).
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
    destruct (proj2 (proj2 run_impl_complete) _ _ _ _ _ _ Hu Hacc nil nil (ginv_nil _)) as [[[r Hp] l] E].
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
    it happens.  The executable never sees the list. *)

Section Files.
  Variable load_path : path -> option string.
  Variable all_files : list path.
  Hypothesis Hfiles : forall fp, (exists s, load_path fp = Some s) <-> In fp all_files.

  Definition unloaded (ch : list path) : nat :=
    List.length (filter (fun fp => if in_dec path_eq_dec fp ch then false else true) all_files).

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

  Corollary prog_impl_complete_wf : forall read to_core prg B ΘR U,
      prog_sem load_path read to_core prg B ΘR U ->
      exists Θ log, prog_impl load_path read to_core prg (load_step_wf _) = rok (B, Θ, U, log) /\ gds_equiv ΘR Θ.
  Proof. intros * H; exact (prog_impl_complete _ _ _ _ _ _ _ H _). Qed.
End Files.
