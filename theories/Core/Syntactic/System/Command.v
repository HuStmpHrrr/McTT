(** * The Static Semantics of Commands

    A command moves the global state: the filed units [Θ] and the stack [Ξ] of
    open frames.  [cc_load] loads the unit it names, if it is not filed yet,
    by running that unit's own commands from nothing, and merges the units
    that run filed into [Θ]; the chain of units whose loading is in progress
    is what rules a cycle out.  [cc_open] declares the names its items
    generate ([items_gen], the relation the local opens of bodies share) as
    definitions, aliases and inductive aliases of the frame.  A command runs
    filled ([TypedElab]): its literals, eliminators and accesses through
    terms are filled first; no other expansion comes first.

    Resolution is lexical — a unit is named by its full path, and an import
    lists the names it binds — so elaborating a unit needs none of the units
    it imports, which are only loaded while it runs. *)

From Stdlib Require Import List String PeanoNat Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Command Members Builtin.
From Mctt.Core.Syntactic.System Require Import Definitions Lemmas Structural.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.Inductives Require Export Inductives.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing.
From Mctt.Core.Syntactic.System.Global Require Import MemberWf Modules.
From Mctt.Core.Syntactic.System Require Export Privacy Translations.
From Mctt.Core Require Export TypedElab.
From Mctt.Core.Semantic Require Import NbE.
Import Syntax_Notations GlobalCtx_Notations.

Reserved Notation "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ] c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'"
  (at level 70, Ξ at level 69, B at level 69, Rb at level 69, ch at level 69, c at level 69, Θ' at level 69, Ξ' at level 69, B' at level 69, Rb' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ] cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'"
  (at level 70, Ξ at level 69, B at level 69, Rb at level 69, ch at level 69, cs at level 69, Θ' at level 69, Ξ' at level 69, B' at level 69, Rb' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ]⟨ lp ⍮ rd ⍮ tc ⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'"
  (at level 70, Ξ at level 69, B at level 69, Rb at level 69, ch at level 69, lp at level 69, rd at level 69, tc at level 69, c at level 69, Θ' at level 69, Ξ' at level 69, B' at level 69, Rb' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ]⟨ lp ⍮ rd ⍮ tc ⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'"
  (at level 70, Ξ at level 69, B at level 69, Rb at level 69, ch at level 69, lp at level 69, rd at level 69, tc at level 69, cs at level 69, Θ' at level 69, Ξ' at level 69, B' at level 69, Rb' at level 69).

(** ** The Stack

    A frame is an unfinished unit or module, named by its (absolute) module
    path: parameters, and the members declared so far.  A member's type and
    body are checked in the telescope of all the frames' parameters,
    [gs_tele], and stored generalized over it. *)

Definition gs_path (Ξ : gstack) : qname :=
  match Ξ with
  | (mp, _, _) :: _ => mp
  | nil => q_abs nil nil
  end.

Definition gs_push (mp : qname) (Δ : ctx) (Ξ : gstack) : gstack := (mp, fk_module, gu_body Δ ⋄) :: Ξ.

(** The frame of the module of the declared member [k] of the group [D]
    at [pq], opened at [mp] with the parameters [Δ] and no member yet. *)
Definition gs_push_ind (mp pq : qname) (k : nat) (D : ind_decl) (Δ : ctx) (Ξ : gstack) : gstack :=
  (mp, fk_ind pq k D, gu_body Δ ⋄) :: Ξ.

(** The frame of the module of the record type [R] at [mp], opened with
    the record's own parameters [Δ] and then a value of it
    ([record_self]), and no member yet. *)
Definition gs_push_record (mp : qname) (R : record_decl) (Δ : ctx) (Ξ : gstack) : gstack :=
  (mp, fk_record R, gu_body (ce_ass (record_self mp R) :: Δ) ⋄) :: Ξ.

Definition gs_add (x : string) (E : gentry) (Ξ : gstack) : gstack :=
  match Ξ with
  | (mp, K, U) :: Ξ' => (mp, K, gu_body (gu_params U) (gu_mod U ⊳ x ↦ E)) :: Ξ'
  | nil => nil
  end.

Definition gs_fresh (x : string) (Ξ : gstack) : Prop :=
  match Ξ with
  | (_, _, U) :: _ => gm_fresh x (gu_mod U)
  | nil => False
  end.

(** A definition and an axiom as they are filed: closed over the frames'
    parameters. *)
Definition gs_def (b pv : bool) (Ξ : gstack) (A M : exp) : gentry :=
  ge_def b pv (ctx_pi (gs_tele Ξ) A) (Some (ctx_fn (gs_tele Ξ) M)).

Definition gs_axiom (b pv : bool) (Ξ : gstack) (A : exp) : gentry :=
  ge_def b pv (ctx_pi (gs_tele Ξ) A) None.

(** ** Opens

    The definitions and aliases an open generates ([items_gen]), declared in
    the frame in order, with the premises of [rc_def] and [rc_alias]: what
    the import references is checked once, as written ([rcs_cons]), and a
    generated type is not written, so nothing here checks privacy. *)

(** [gens_run Θ Ξ gs Ξ']: declaring the generated items [gs] in order in
    the frame [Ξ] gives [Ξ']. *)
Inductive gens_run (Θ : gdeps) : gstack -> list igen -> gstack -> Prop :=
(** No item leaves the frame as it is *)
| gr_nil : forall Ξ, gens_run Θ Ξ nil Ξ
(** A generated definition, checked at its type as [rc_def] does *)
| gr_def : forall Ξ d pv A M gs Ξ',
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> gs_fresh d Ξ ->
    gens_run Θ (gs_add d (gs_def true pv Ξ A M) Ξ) gs Ξ' ->
    gens_run Θ Ξ (ig_def d pv A M :: gs) Ξ'
(** A generated module alias, its target checked as [rc_alias] does *)
| gr_alias : forall Ξ d pv E gs Ξ',
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E -> gs_fresh d Ξ ->
    gens_run Θ (gs_add d (ge_mod pv (gu_mk (gs_tele Ξ) (md_alias E))) Ξ) gs Ξ' ->
    gens_run Θ Ξ (ig_alias d pv E :: gs) Ξ'
(** A generated inductive alias, closed over the frame's parameters and
    checked as an entry *)
| gr_ind_alias : forall Ξ d pv Δ pm p k Ns gs Ξ',
    Θ ⍮ Ξ ⍮ qname_in (gs_path Ξ) d ⊢ᵉ ge_ind_alias pv (Δ ++ gs_tele Ξ) pm p k Ns -> gs_fresh d Ξ ->
    gens_run Θ (gs_add d (ge_ind_alias pv (Δ ++ gs_tele Ξ) pm p k Ns) Ξ) gs Ξ' ->
    gens_run Θ Ξ (ig_ind_alias d pv Δ pm p k Ns :: gs) Ξ'.

(** ** Groups of Inductive Declarations

    A group is filed as one entry per declared member, in order
    ([ge_ind]): the group, with the parameters of the frames as its
    outermost uniform parameters, and the body of the member's module.
    The module is filled by generated commands ([ind_mod_cmds]), run in
    its frame as the commands of a module body are, and checked by the
    ordinary module judgment ([wf_gentry_ind_body]).  As a term, the path
    of a member's entry is its type former ([wf_mem_glob_ind]); the group
    is named by the path of its first member. *)

(** The path of the declared type [x] a declaration makes. *)
Definition ind_qname (Ξ : gstack) (x : string) : qname := qname_in (gs_path Ξ) x.

(** The recursor of the only member [M] of the filed group [D] at [pq],
    over the module's parameters (the uniform ones): at a finite level
    [u], a motive [P : Π Δn. Π (z : X us ns). Type⟨u⟩], one branch per
    constructor, of the type the eliminator gives a branch at the motive
    [P], then [Π Δn. Π (z : X us ns). P ns z].  It is the eliminator, at
    that motive, of branches that are the branch arguments applied to what
    they bind.  Below [k] binders past [P], the motive is [P] under [Δn]
    and [z], and the uniform parameters are the module's. *)
Definition rec_motive (M : imember) (k : nat) : exp :=
  apps (a_var (S (im_nn M) + k)) (vars_from 0 (S (im_nn M))).

Definition rec_uvars (D : ind_decl) (k : nat) : list exp := vars_from (2 + k) (ind_nu D).

(** The branch types, outermost first, the [k]-th under [k] before it. *)
Fixpoint rec_btys (pq : qname) (D : ind_decl) (M : imember) (k : nat) (cs : list (string * list carg)) : list centry :=
  match cs with
  | nil => nil
  | (c, gs) :: cs' =>
      ce_ass (ctx_pi (elim_bctx pq D M gs (rec_motive M k :: nil) (rec_uvars D k))
                (elim_bty pq 0 M c gs (rec_motive M k) (rec_uvars D k)))
      :: rec_btys pq D M (S k) cs'
  end.

(** The level, the motive and the branches, innermost first. *)
Definition rec_tele (pq : qname) (D : ind_decl) (M : imember) : ctx :=
  List.rev (rec_btys pq D M 0 (im_cons M)) ++
  ce_ass (ctx_pi (elim_mctx pq D 0 M (vars_from 1 (ind_nu D))) (a_univ (a_var (S (im_nn M))))) ::
  ce_ass (a_level 0) :: nil.

(** The type of the recursor: over its level, motive and branches, a
    function from the member's parameters and a scrutinee to the motive. *)
Definition rec_ty (pq : qname) (D : ind_decl) (M : imember) : typ :=
  let K := List.length (im_cons M) in
  ctx_pi (rec_tele pq D M) (ctx_pi (elim_mctx pq D 0 M (rec_uvars D K)) (rec_motive M K)).

(** The branches of the eliminator, each the [j]-th branch argument applied
    to the variables the branch binds. *)
Fixpoint rec_brs (M : imember) (K j : nat) (cs : list (string * list carg)) : list (string * nat * exp) :=
  match cs with
  | nil => nil
  | (c, gs) :: cs' =>
      let n := (im_nn M + List.length gs + cargs_nrec gs)%nat in
      (c, n, apps (a_var (n + S (im_nn M) + (K - 1 - j))) (vars_from 0 n)) :: rec_brs M K (S j) cs'
  end.

(** The recursor itself, of type [rec_ty]: the eliminator at the motive
    argument, of the branches [rec_brs], on the scrutinee. *)
Definition rec_fn (pq : qname) (D : ind_decl) (M : imember) : exp :=
  let K := List.length (im_cons M) in
  ctx_fn (rec_tele pq D M)
    (ctx_fn (elim_mctx pq D 0 M (rec_uvars D K))
       (a_elim None (rec_uvars D (K + S (im_nn M))) 0 (eb_mk (S (im_nn M)) None (rec_motive M (K + S (im_nn M))) (rec_brs M K 0 (im_cons M)) :: nil)
          (a_var 0))).

(** A group has a recursor when it is one member, and no view. *)
Definition ind_has_rec (D : ind_decl) : bool := Nat.eqb (List.length (ind_members D)) 1.

(** ** The Recursor Module of a Group

    Every group files a recursor module [Rec], checked as any module is: a
    group declared by [mutual T where] in [T]'s frame after its members
    ([rec_cmds]), any other in the module of its first declared member
    ([ind_grec_cmds]).  Its
    parameters, innermost first: one case per constructor of each member,
    in member order; one motive per member, [P_i : Π (nps_i) (z : M_i Us
    nps_i). Type@{u}]; the level [u]; the group's own uniform parameters.
    It has one function per member, [rec_<member>], of type [Π (nps_j) (z
    : M_j Us nps_j). P_j nps_j z], the eliminator of the group at the
    member, at the motives, its branches the cases at what they bind.  A
    declared member is named by its own name, a view by its instance: the
    container member's name, then the names of the members its arguments
    are headed by, joined by [_]; a name met again gets [_2], [_3], …. *)

(** The motive of the member [i], [Mi], of a group of [N] members, under
    [k] binders past the motives and its own [S (im_nn Mi)] binders. *)
Definition grec_motive (N i : nat) (Mi : imember) (k : nat) : exp :=
  apps (a_var (S (im_nn Mi) + k + (N - 1 - i))) (vars_from 0 (S (im_nn Mi))).

(** The group's uniform parameters, under [k] binders past the [N]
    motives and the level. *)
Definition grec_uvars (D : ind_decl) (N k : nat) : list exp := vars_from (k + N + 1) (ind_nu D).

(** The motives of all members, under [k] binders past the motives. *)
Definition grec_motives (D : ind_decl) (k : nat) : list exp :=
  List.map (fun iM => grec_motive (List.length (ind_members D)) (fst iM) (snd iM) k)
    (List.combine (List.seq 0 (List.length (ind_members D))) (ind_members D)).

(** The motives' types, outermost first: the member [i]'s under the [i]
    motives before it and the level. *)
Definition grec_motive_tys (pq : qname) (D : ind_decl) : list centry :=
  List.map (fun iM => ce_ass (ctx_pi (elim_mctx pq D (fst iM) (snd iM) (vars_from (S (fst iM)) (ind_nu D)))
                                     (a_univ (a_var (S (im_nn (snd iM)) + fst iM)))))
    (List.combine (List.seq 0 (List.length (ind_members D))) (ind_members D)).

(** The cases' types, outermost first, from the member [i] on, [k] cases
    before: the case of the constructor [c] of [Mi], of the motive of [Mi]
    at the constructor, under the binders of a branch for it. *)
Fixpoint grec_case_tys (pq : qname) (D : ind_decl) (i k : nat) (ms : list imember) : list centry :=
  match ms with
  | nil => nil
  | Mi :: ms' =>
      let N := List.length (ind_members D) in
      (fix cases (k : nat) (cs : list (string * list carg)) : list centry :=
         match cs with
         | nil => nil
         | (c, gs) :: cs' =>
             ce_ass (ctx_pi (elim_bctx pq D Mi gs (grec_motives D k) (grec_uvars D N k))
                       (elim_bty pq i Mi c gs (grec_motive N i Mi k) (grec_uvars D N k)))
             :: cases (S k) cs'
         end) k (im_cons Mi)
      ++ grec_case_tys pq D (S i) (k + List.length (im_cons Mi)) ms'
  end.

(** The number of cases of a group. *)
Definition grec_ncases (D : ind_decl) : nat := List.fold_right (fun Mi n => List.length (im_cons Mi) + n) 0 (ind_members D).

(** The parameters of the module, innermost first, over the frames'
    parameters, the group's own uniform parameters [Δu] outermost. *)
Definition grec_tele (pq : qname) (D : ind_decl) (Δu : ctx) : ctx :=
  List.rev (grec_case_tys pq D 0 0 (ind_members D)) ++ List.rev (grec_motive_tys pq D) ++ ce_ass (a_level 0) :: Δu.

(** The branches of the block of the member [Mi], whose cases start at
    [kc], in the function of a member of [nj] binders: each the case
    applied to what the branch binds. *)
Fixpoint grec_brs (K nj kc : nat) (Mi : imember) (cs : list (string * list carg)) : list (string * nat * exp) :=
  match cs with
  | nil => nil
  | (c, gs) :: cs' =>
      let n := (im_nn Mi + List.length gs + cargs_nrec gs)%nat in
      (c, n, apps (a_var (n + nj + (K - 1 - kc))) (vars_from 0 n)) :: grec_brs K nj (S kc) Mi cs'
  end.

(** The blocks of the eliminator in the function of a member of [nj]
    binders, from the member [i] on, [kc] cases before. *)
Fixpoint grec_blocks (D : ind_decl) (K nj i kc : nat) (ms : list imember) : list eblock :=
  match ms with
  | nil => nil
  | Mi :: ms' =>
      eb_mk (S (im_nn Mi)) None (grec_motive (List.length (ind_members D)) i Mi (K + nj))
        (grec_brs K nj kc Mi (im_cons Mi))
      :: grec_blocks D K nj (S i) (kc + List.length (im_cons Mi)) ms'
  end.

(** The function of the member [j], [Mj]: its type and its body. *)
Definition grec_fn_ty (pq : qname) (D : ind_decl) (j : nat) (Mj : imember) : typ :=
  let N := List.length (ind_members D) in
  let K := grec_ncases D in
  ctx_pi (elim_mctx pq D j Mj (grec_uvars D N K)) (grec_motive N j Mj K).

Definition grec_fn (pq : qname) (D : ind_decl) (j : nat) (Mj : imember) : exp :=
  let N := List.length (ind_members D) in
  let K := grec_ncases D in
  ctx_fn (elim_mctx pq D j Mj (grec_uvars D N K))
    (a_elim (Some pq) (grec_uvars D N (K + S (im_nn Mj))) j
       (grec_blocks D K (S (im_nn Mj)) 0 0 (ind_members D)) (a_var 0)).

(** The last name of a path. *)
Definition qname_last (p : qname) : string := List.last (q_chain p) EmptyString.

(** The name of the declared member [j] of the group filed at [p]. *)
Definition member_name (Θ : gdeps) (Ξ : gstack) (p : qname) (j : nat) : string :=
  match ind_lookup Θ Ξ p with
  | Some D => match ind_mpath D j with Some pm => qname_last pm | None => EmptyString end
  | None => EmptyString
  end.

(** The name of a member: a declared one's own, a view's from its
    instance. *)
Definition grec_member_name (Θ : gdeps) (Ξ : gstack) (Mi : imember) : string :=
  match im_head Mi with
  | mh_decl pm => qname_last pm
  | mh_view qc k Is _ =>
      (member_name Θ Ξ qc k ++
       String.concat EmptyString
         (List.map (fun I => match app_head I with
                             | a_ind p j => "_" ++ member_name Θ Ξ p j
                             | _ => EmptyString
                             end) Is))%string
  end.

(** A decimal numeral, as written. *)
Fixpoint uint_string (d : Decimal.uint) : string :=
  match d with
  | Decimal.Nil => EmptyString
  | Decimal.D0 d' => "0" ++ uint_string d'
  | Decimal.D1 d' => "1" ++ uint_string d'
  | Decimal.D2 d' => "2" ++ uint_string d'
  | Decimal.D3 d' => "3" ++ uint_string d'
  | Decimal.D4 d' => "4" ++ uint_string d'
  | Decimal.D5 d' => "5" ++ uint_string d'
  | Decimal.D6 d' => "6" ++ uint_string d'
  | Decimal.D7 d' => "7" ++ uint_string d'
  | Decimal.D8 d' => "8" ++ uint_string d'
  | Decimal.D9 d' => "9" ++ uint_string d'
  end%string.

(** The names [xs], each met again after [seen] given the first suffix
    [_2], [_3], … that makes it new.  The candidates [x], [x_2], …,
    [x_(|seen|+1)] are [|seen| + 1] distinct names, so by pigeonhole one of
    them is not in [seen]: trying them in order, the last is returned
    unchecked, and it is new when all before it are taken.  The bound is
    structural, not fuel: the search never runs out, and a name that were
    not new would only make the module's [rc_def] reject it as not
    fresh. *)
Fixpoint grec_fresh_names (seen : list string) (xs : list string) : list string :=
  match xs with
  | nil => nil
  | x :: xs' =>
      let pick := (fix try (n : nat) (m : nat) : string :=
                     let cand := match n with 0 => x | _ => (x ++ "_" ++ uint_string (Nat.to_uint (S n)))%string end in
                     match m with
                     | 0 => cand
                     | S m' => if List.existsb (String.eqb cand) seen then try (S n) m' else cand
                     end) 0 (List.length seen) in
      pick :: grec_fresh_names (seen ++ pick :: nil) xs'
  end.

(** The functions' names, [rec_] then the members'. *)
Definition grec_names (Θ : gdeps) (Ξ : gstack) (D : ind_decl) : list string :=
  List.map (fun x => ("rec_" ++ x)%string) (grec_fresh_names nil (List.map (grec_member_name Θ Ξ) (ind_members D))).

(** The command that files the recursor module [Rec] of the group [D] at
    [pq], its names read at [Θ ⍮ Ξ], with [Δu] the uniform parameters its
    own parameters end in: the group's own ones in the frame the members
    are filed in, none in the module of a member, whose frame binds
    them.  The module and its definitions are generated ([cc_gen]). *)
Definition grec_mod_cmd (Θ : gdeps) (Ξ : gstack) (pq : qname) (D : ind_decl) (Δu : ctx) : ccmd :=
  cc_gen (cc_mod "Rec" false (grec_tele pq D Δu)
    (List.map (fun jx => let '(j, Mj, x) := jx in cc_gen (cc_def x true false (grec_fn_ty pq D j Mj) (Some (grec_fn pq D j Mj))))
       (List.combine (List.combine (List.seq 0 (List.length (ind_members D))) (ind_members D)) (grec_names Θ Ξ D)))).

(** The commands that file the recursor module of the group [D] at [pq],
    declared as [R], after its members, at the stack [Ξ] they are filed
    in: none unless [R] asks for it. *)
Definition rec_cmds (Θ : gdeps) (Ξ : gstack) (R : raw_decl) (pq : qname) (D : ind_decl) : list ccmd :=
  if rd_rec R then grec_mod_cmd Θ Ξ pq D (rd_uparams R) :: nil else nil.

(** ** The Module of a Declared Member

    The module of the declared member [k], [M], of the group [D] at [pq]
    is filled by commands run in its frame, whose parameters are the
    group's uniform ones, as the commands of a module body are: one
    transparent public definition per constructor, the constructor at the
    module's parameters ([ind_con_cmd]); the recursor [rec] of a group of
    one member and no view; and, in the first declared member's module of
    a group not declared by [mutual T where], the recursor module [Rec],
    whose parameters are those of [grec_tele] without the uniform ones,
    which the frame binds already ([ind_mod_cmds]). *)

(** The definition of the constructor [c] of arguments [gs]: its type over
    the member's non-uniform parameters and its arguments, its term the
    constructor at the module's parameters; generated ([cc_gen]). *)
Definition ind_con_cmd (pq : qname) (D : ind_decl) (k : nat) (M : imember) (cg : (string * list carg)%type) : ccmd :=
  cc_gen (cc_def (fst cg) true false
    (ctx_pi (im_nparams M) (ctx_pi (cargs_ctx pq D M (snd cg)) (apps (a_ind pq k) (ind_pvars D M (List.length (snd cg))))))
    (Some (apps (a_con pq k (fst cg)) (vars_from 0 (ind_nu D))))).

(** The recursor [rec], when the group has one; generated. *)
Definition ind_rec_cmds (pq : qname) (D : ind_decl) (M : imember) : list ccmd :=
  if ind_has_rec D then cc_gen (cc_def "rec" true false (rec_ty pq D M) (Some (rec_fn pq D M))) :: nil else nil.

(** The recursor module [Rec], in the first declared member's module of a
    group not declared by [mutual T where]. *)
Definition ind_grec_cmds (Θ : gdeps) (Ξ : gstack) (R : raw_decl) (pq : qname) (D : ind_decl) (k : nat) : list ccmd :=
  if Nat.eqb k 0 && negb (rd_rec R) then grec_mod_cmd Θ Ξ pq D nil :: nil else nil.

(** The commands of the module of the declared member [k], [M]: its
    constructors, the recursor, and the recursor module, in that order;
    the names of [Rec]'s functions are read at [Θ ⍮ Ξ], the stack the
    commands run in: the member's frame, through which the group is
    found. *)
Definition ind_mod_cmds (Θ : gdeps) (Ξ : gstack) (R : raw_decl) (pq : qname) (D : ind_decl) (k : nat) (M : imember) :
    list ccmd :=
  List.map (ind_con_cmd pq D k M) (im_cons M) ++ ind_rec_cmds pq D M ++ ind_grec_cmds Θ Ξ R pq D k.

(** The names a group declared as [R] at the stack [Ξ], filed as [D],
    generates are left free by its own: [rec] and [Rec] name no
    constructor of the module they are filed in, and the recursor module
    of a [mutual T] group is fresh in [T]'s frame. *)
Record gen_names_free (Ξ : gstack) (R : raw_decl) (D : ind_decl) : Prop := mk_gen_names_free
  { (** The recursor [rec] of a one-member group is no constructor of it *)
    rec_not_constructor : ind_has_rec D = true -> forall M, ind_member D 0 = Some M ->
      ~ In "rec"%string (List.map fst (im_cons M))
    (** The recursor module [Rec] in the first member's module is no
        constructor of it *)
  ; rec_module_not_constructor : rd_rec R = false -> forall M, ind_member D 0 = Some M ->
      ~ In "Rec"%string (List.map fst (im_cons M))
    (** The recursor module of a [mutual T] group is no member of it *)
  ; mutual_rec_not_member : rd_rec R = true -> ~ In "Rec"%string (List.map rm_name (rd_members R))
    (** nor declared in [T]'s frame before it *)
  ; mutual_rec_fresh : rd_rec R = true -> gs_fresh "Rec"%string Ξ }.

(** ** Classifying the Arguments

    Each argument of each constructor of each declared member is a type in
    the context it is written in: the arguments before it, the member's
    parameters, the variables [Self_0], …, [Self_(n-1)] of the declared
    members ([rd_selfs], [Self_0] outermost), the frames' parameters.  It
    is classified ([cls_arg]) as written when that finds it free or
    recursive in a declared member, and as its normal form otherwise: so
    [Arr Ord], with [Arr X := ℕ → X], is classified as [ℕ → Ord] is, and a
    nested occurrence is found on normal forms only, where two instances
    are the same view exactly when they are equal.  The classification is
    a function of the argument. *)

(** The contexts a group's parts are written in ([rd_selfs], [rm_pctx],
    [rtele]) are in [Translations]. *)

(** The number of uniform parameters of the filed group at [qc], if [k] is
    one of its declared members. *)
Definition grp_info (Θ : gdeps) (Ξ : gstack) (qc : qname) (k : nat) : option nat :=
  match ind_lookup Θ Ξ qc with
  | Some D' => if k <? ind_ndecl D' then Some (ind_nu D') else None
  | None => None
  end.

(** An argument [T] in the context [Γ], the arguments before it recursive
    as [pat] says. *)
Inductive cls_arg_in (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (nu np n : nat) (pat : list bool) (T : exp) : rcarg -> Prop :=
(** As written. *)
| cls_in_syn : forall g,
    cls_arg grp_none nu np n pat T = Some g ->
    cls_arg_in Θ Ξ Γ nu np n pat T g
(** As its normal form, when not as written. *)
| cls_in_nf : forall i W g,
    cls_arg grp_none nu np n pat T = None ->
    Θ ⍮ Ξ ⍮ Γ ⊢ T : Typeω@i ->
    nbe_ty Θ Ξ Γ T W ->
    cls_arg (grp_info Θ Ξ) nu np n pat (nf_to_exp W) = Some g ->
    cls_arg_in Θ Ξ Γ nu np n pat T g.

(** [cls_args_in Θ Ξ Γp nu np n pat args1 args gs]: the arguments [args],
    after [args1] (recursive as [pat] says), classify as [gs], each in the
    context of those before it over [Γp]. *)
Inductive cls_args_in (Θ : gdeps) (Ξ : gstack) (Γp : ctx) (nu np n : nat) :
    list bool -> list (string * exp) -> list (string * exp) -> list rcarg -> Prop :=
(** No argument left *)
| cls_args_in_nil : forall pat args1, cls_args_in Θ Ξ Γp nu np n pat args1 nil nil
(** The next argument, classified, then the rest after it *)
| cls_args_in_cons : forall pat args1 y T args g gs,
    cls_arg_in Θ Ξ (rtele args1 ++ Γp) nu np n pat T g ->
    cls_args_in Θ Ξ Γp nu np n (rcarg_bit g :: pat) (args1 ++ (y, T) :: nil) args gs ->
    cls_args_in Θ Ξ Γp nu np n pat args1 ((y, T) :: args) (g :: gs).

(** The raw constructors [rcs] classify as [cs], pointwise, keeping their
    names. *)
Definition cls_cons_in (Θ : gdeps) (Ξ : gstack) (Γp : ctx) (nu np n : nat)
    (rcs : list (string * list (string * exp))) (cs : list (string * list rcarg)) : Prop :=
  Forall2 (fun rc c => fst rc = fst c /\ cls_args_in Θ Ξ Γp nu np n nil nil (snd rc) (snd c)) rcs cs.

(** The constructors of a declared member. *)
Definition rm_cls (Θ : gdeps) (Ξ : gstack) (R : raw_decl) (Mr : raw_member) (cs : list (string * list rcarg)) : Prop :=
  cls_cons_in Θ Ξ (rm_pctx Ξ R Mr) (rd_nu R) (List.length (rm_nparams Mr) + rd_nu R) (rd_n R) (rm_cons Mr) cs.

Lemma cls_arg_in_functional : forall Θ Ξ Γ nu np n pat T g g',
    cls_arg_in Θ Ξ Γ nu np n pat T g -> cls_arg_in Θ Ξ Γ nu np n pat T g' -> g = g'.
Proof.
  intros * H H'; destruct H as [g Hg | i W g Hn _ HW Hg]; inversion H' as [g'' Hg' | i' W' g'' Hn' _ HW' Hg']; subst.
  - congruence.
  - congruence.
  - congruence.
  - pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-; congruence.
Qed.

Lemma cls_args_in_functional : forall Θ Ξ Γp nu np n pat args1 args gs gs',
    cls_args_in Θ Ξ Γp nu np n pat args1 args gs -> cls_args_in Θ Ξ Γp nu np n pat args1 args gs' -> gs = gs'.
Proof.
  intros * H; revert gs'; induction H as [| pat args1 y T args g gs Hg Hgs IH]; intros gs' H'; inversion H'; subst;
    [ reflexivity |].
  match goal with Hg' : cls_arg_in _ _ _ _ _ _ _ _ ?g' |- _ =>
    pose proof (cls_arg_in_functional _ _ _ _ _ _ _ _ _ _ Hg Hg') as <- end.
  f_equal; apply IH; assumption.
Qed.

Lemma cls_cons_in_functional : forall Θ Ξ Γp nu np n rcs cs cs',
    cls_cons_in Θ Ξ Γp nu np n rcs cs -> cls_cons_in Θ Ξ Γp nu np n rcs cs' -> cs = cs'.
Proof.
  unfold cls_cons_in; intros Θ Ξ Γp nu np n rcs.
  induction rcs as [| rc rcs IH]; intros * H H'; inversion H; inversion H'; subst; [ reflexivity |].
  destruct y as [c gs], y0 as [c' gs']; cbn in *; destruct_conjs; subst.
  f_equal; [ f_equal; eapply cls_args_in_functional; eassumption | apply IH; assumption ].
Qed.

(** ** The Views

    A view is an instance [(qc, k, Cs)] met: the declared member [k] of the
    filed group at [qc] at the uniform arguments [Cs], normal, over the
    group's own uniform parameters, the [Self]s and the frames'.  Its
    non-uniform parameters are the container's member's at [Cs],
    normalized, and filed when they are free of the [Self]s, without them
    ([view_nps]): the group checks them against the container's at its
    [Self]s, so they cannot mention the group.  Its
    constructors are the container's member's, each argument the container's
    type at [Cs], classified as a declared member's is ([view_cls]).  Its
    siblings are the members of the container's group at [Cs]
    ([sibs_from]): a declared one at [Cs], a view of it at its own uniform
    arguments at [Cs], normalized. *)

(** The type of a context entry; a module slot counts as [True]. *)
Definition centry_ty (e : centry) : typ :=
  match e with ce_ass A => A | ce_def A _ => A | ce_mod _ => a_True end.

(** A telescope, innermost first, as arguments, outermost first. *)
Definition ctx_args (Δ : ctx) : list (string * exp) := List.rev (List.map (fun e => (""%string, centry_ty e)) Δ).

(** The constructors of a view [(qc, k, Cs)], classified: the container's
    member's, each argument its type at [Cs], classified as a declared
    member's is. *)
Inductive view_cls (Θ : gdeps) (Ξ : gstack) (R : raw_decl) : rview -> list (string * list rcarg) -> Prop :=
(** The only rule *)
| view_cls_intro : forall qc k Cs D' Mk' cs,
    ind_lookup Θ Ξ qc = Some D' ->
    ind_member D' k = Some Mk' ->
    cls_cons_in Θ Ξ (tele_sub (im_nparams Mk') (sb_of_list sb_id Cs) ++ rd_uctx Ξ R) (rd_nu R) (im_nn Mk' + rd_nu R) (rd_n R)
      (List.map (fun cg => (fst cg, ctx_args (tele_sub (cargs_ctx qc D' Mk' (snd cg)) (sb_qn (im_nn Mk') (sb_of_list sb_id Cs)))))
         (im_cons Mk'))
      cs ->
    view_cls Θ Ξ R (qc, k, Cs) cs.

(** A telescope of assumptions, innermost first, each normalized in the
    ones before it, over [Γ]. *)
Inductive nbe_tele (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : ctx -> ctx -> Prop :=
(** The empty telescope *)
| nbe_tele_nil : nbe_tele Θ Ξ Γ nil nil
(** The innermost assumption, normalized in the ones before it; it is a
    type there first, as normalizing an untyped term need not terminate *)
| nbe_tele_cons : forall A Δ W Δ',
    (exists i, Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A : Typeω@i) ->
    nbe_ty Θ Ξ (Δ ++ Γ) A W ->
    nbe_tele Θ Ξ Γ Δ Δ' ->
    nbe_tele Θ Ξ Γ (ce_ass A :: Δ) (ce_ass (nf_to_exp W) :: Δ').

(** The preimage of a telescope of assumptions under the pattern
    weakening [pat], each entry under those before it, if it has one. *)
Fixpoint img_tele (pat : list bool) (Δ : ctx) : option ctx :=
  match Δ with
  | nil => Some nil
  | ce_ass A :: Δ' =>
      match img_pat (List.repeat false (List.length Δ') ++ pat) A, img_tele pat Δ' with
      | Some A0, Some Δ0 => Some (ce_ass A0 :: Δ0)
      | _, _ => None
      end
  | _ :: _ => None
  end.

(** The non-uniform parameters of a view, filed: the container's member's
    at [Cs], normalized over the group's own uniform parameters, the
    [Self]s and the frames', free of the [Self]s and without them. *)
Inductive view_nps (Θ : gdeps) (Ξ : gstack) (R : raw_decl) : rview -> ctx -> Prop :=
(** The only rule *)
| view_nps_intro : forall qc k Cs D' Mk' Ws Nv,
    ind_lookup Θ Ξ qc = Some D' ->
    ind_member D' k = Some Mk' ->
    nbe_tele Θ Ξ (rd_uctx Ξ R) (tele_sub (im_nparams Mk') (sb_of_list sb_id Cs)) Ws ->
    img_tele (List.repeat false (rd_nu R) ++ List.repeat true (rd_n R)) Ws = Some Nv ->
    view_nps Θ Ξ R (qc, k, Cs) Nv.

(** [nbes Θ Ξ Γ Ms As Ws]: the terms [Ms] normalize pointwise at the
    types [As] to [Ws], all in [Γ]. *)
Inductive nbes (Θ : gdeps) (Ξ : gstack) (Γ : ctx) : list exp -> list typ -> list nf -> Prop :=
(** No term *)
| nbes_nil : nbes Θ Ξ Γ nil nil nil
(** The first term, typed at its type first, as normalizing an untyped
    term need not terminate, then the rest *)
| nbes_cons : forall M Ms A As W Ws,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> nbe Θ Ξ Γ M A W -> nbes Θ Ξ Γ Ms As Ws -> nbes Θ Ξ Γ (M :: Ms) (A :: As) (W :: Ws).

(** [sibs_from Θ Ξ Γc qc Cs i ms ss]: the members [ms] of the container's
    group at [qc], from position [i], at the uniform arguments [Cs], are
    the views [ss]. *)
Inductive sibs_from (Θ : gdeps) (Ξ : gstack) (Γc : ctx) (qc : qname) (Cs : list exp) :
    nat -> list imember -> list rview -> Prop :=
(** No member left *)
| sibs_from_nil : forall i, sibs_from Θ Ξ Γc qc Cs i nil nil
(** A declared member: itself at [Cs] *)
| sibs_from_decl : forall i M ms ss pm,
    im_head M = mh_decl pm ->
    sibs_from Θ Ξ Γc qc Cs (S i) ms ss ->
    sibs_from Θ Ξ Γc qc Cs i (M :: ms) ((qc, i, Cs) :: ss)
(** A view of the container: the member it views, at its own uniform
    arguments at [Cs], normalized *)
| sibs_from_view : forall i M ms ss qv kv Iv vmv Dv Ws,
    im_head M = mh_view qv kv Iv vmv ->
    ind_lookup Θ Ξ qv = Some Dv ->
    nbes Θ Ξ Γc (List.map (fun I => I[sb_of_list sb_id Cs]) Iv)
      (List.map (fun T => T[sb_of_list sb_id Cs]) (tele_insts (ind_uparams Dv) sb_id Iv)) Ws ->
    sibs_from Θ Ξ Γc qc Cs (S i) ms ss ->
    sibs_from Θ Ξ Γc qc Cs i (M :: ms) ((qv, kv, List.map nf_to_exp Ws) :: ss).

(** The siblings of a view [(qc, k, Cs)]: the members of the container's
    group at [Cs], over the group's own context. *)
Inductive view_sibs (Θ : gdeps) (Ξ : gstack) (R : raw_decl) : rview -> list rview -> Prop :=
(** The only rule *)
| view_sibs_intro : forall qc k Cs D' ss,
    ind_lookup Θ Ξ qc = Some D' ->
    sibs_from Θ Ξ (rd_uctx Ξ R) qc Cs 0 (ind_members D') ss ->
    view_sibs Θ Ξ R (qc, k, Cs) ss.

(** ** Filing the Group

    The declared members, then the views, numbered in the order found; a
    view's uniform arguments with the [Self]s instantiated ([sb_selfs]:
    [Self_j] is the type former of the member [j] at the frames'
    parameters), so that they are over the filed group's uniform
    parameters, the group's own and the frames'. *)

(** Under [nu] uniform parameters, [Self_j] for [j < n] becomes the type
    former of member [j] of the group at [pq] applied to the [t] frames'
    parameters. *)
Definition sb_selfs (pq : qname) (nu n t : nat) : sub :=
  sb_qn nu (sb_of_list sb_id (List.map (fun j => apps (a_ind pq j) (vars_from 0 t)) (List.seq 0 n))).

(** The declared members filed, each with its classified constructors
    numbered against the views [Vs], if they all are. *)
Fixpoint rms_filed (Ξ : gstack) (n : nat) (Vs : list rview) (ms : list raw_member)
    (css : list (list (string * list rcarg))) : option (list imember) :=
  match ms, css with
  | nil, nil => Some nil
  | Mr :: ms', cs :: css' =>
      match rcons_num n Vs cs, rms_filed Ξ n Vs ms' css' with
      | Some cs', Some Ms => Some (mk_imember (mh_decl (ind_qname Ξ (rm_name Mr))) (rm_nparams Mr) cs' :: Ms)
      | _, _ => None
      end
  | _, _ => None
  end.

(** A view [x] filed: its head with the uniform arguments instantiated by
    [σ] and its siblings numbered after the [n] declared members, its
    filed non-uniform parameters [Nv] and its numbered constructors. *)
Definition rv_filed (Θ : gdeps) (Ξ : gstack) (σ : sub) (n : nat) (Vs : list rview) (x : rview) (ss : list rview)
    (cs : list (string * list rcarg)) (Nv : ctx) : option imember :=
  let '(qc, k, Cs) := x in
  let Is := List.map (fun C => C[σ]) Cs in
  match ind_lookup Θ Ξ qc with
  | Some D' =>
      match ind_member D' k, rcons_num n Vs cs with
      | Some _, Some cs' =>
          Some (mk_imember
                  (mh_view qc k Is (List.map (fun s => n + match rview_index s Vs with Some v => v | None => 0 end) ss))
                  Nv cs')
      | _, _ => None
      end
  | None => None
  end.

(** The views [xs] filed pointwise with [rv_filed], if they all are. *)
Fixpoint rvs_filed (Θ : gdeps) (Ξ : gstack) (σ : sub) (n : nat) (Vs xs : list rview) (Ss : list (list rview))
    (css : list (list (string * list rcarg))) (Nvs : list ctx) : option (list imember) :=
  match xs, Ss, css, Nvs with
  | nil, nil, nil, nil => Some nil
  | x :: xs', ss :: Ss', cs :: css', Nv :: Nvs' =>
      match rv_filed Θ Ξ σ n Vs x ss cs Nv, rvs_filed Θ Ξ σ n Vs xs' Ss' css' Nvs' with
      | Some M, Some Ms => Some (M :: Ms)
      | _, _ => None
      end
  | _, _, _, _ => None
  end.

(** The filed group: the declared members then the views, over the
    group's uniform parameters and the frames', at the first member's
    sort, the [Self]s instantiated at the first member's path. *)
Definition rd_filed (Θ : gdeps) (Ξ : gstack) (R : raw_decl) (Vs : list rview) (Ss : list (list rview))
    (csD csV : list (list (string * list rcarg))) (Nvs : list ctx) : option ind_decl :=
  match rd_members R with
  | Mr0 :: _ =>
      let σ := sb_selfs (ind_qname Ξ (rm_name Mr0)) (rd_nu R) (rd_n R) (List.length (gs_tele Ξ)) in
      match rms_filed Ξ (rd_n R) Vs (rd_members R) csD, rvs_filed Θ Ξ σ (rd_n R) Vs Vs Ss csV Nvs with
      | Some Ms, Some Mv => Some (mk_ind (rd_uparams R ++ gs_tele Ξ) (rm_sort Mr0) (Ms ++ Mv))
      | _, _ => None
      end
  | nil => None
  end.

(** ** The Views' Instances with the Members as Variables

    [wf_gentry_ind_nil] checks a group's views at their instances with the
    members as variables, [IsS], linked to the filed instances [Is] by
    [Is = map (fun I => I[grp_sb mp D]) (IsS k)].  The link does not
    determine [IsS]: [grp_sb] is not injective ([Self_0] and the type
    former of the member [0] at the uniform parameters have one image), and
    no lemma rules out a typed [IsS] that mentions the group being
    declared, which is not filed yet.  So the command fixes [IsS]: the
    filed instances with each type former of a declared member at the
    uniform parameters read back as that member's variable
    ([exp_self_form]), and checks the group at it ([ind_nil_at]), which
    gives the entry ([ind_nil_at_entry]). *)

(** [self_var pq D d M]: the variable [Self_j], [d] binders above the
    [Self]s, if [M] is the type former of the declared member [j] of the
    group at [pq] at the uniform parameters, [d] binders above them. *)
Definition self_var (pq : qname) (D : ind_decl) (d : nat) (M : exp) : option nat :=
  match app_head M with
  | a_ind pq' j =>
      if qname_eq_dec pq' pq then
        if (j <? ind_ndecl D) && (if list_eq_dec exp_eq_dec (app_args M) (vars_from d (ind_nu D)) then true else false)
        then Some (d + (ind_ndecl D - 1 - j))
        else None
      else None
  | _ => None
  end.

(** [exp_self_form pq D d M]: [M], [d] binders above the uniform
    parameters of the group [D] at [pq], with each type former of a
    declared member at the uniform parameters the member's variable
    ([self_var]), and every other variable of the uniform parameters moved
    past the [Self]s, which [grp_sctx D] puts inside them.  The instances
    are normal forms, which have no [let] and no module literal; those are
    left as they are. *)
Fixpoint exp_self_form (pq : qname) (D : ind_decl) (d : nat) (M : exp) {struct M} : exp :=
  match self_var pq D d M with
  | Some x => a_var x
  | None =>
      match M with
      | a_univ M' => a_univ (exp_self_form pq D d M')
      | a_succl M' => a_succl (exp_self_form pq D d M')
      | a_maxl M1 M2 => a_maxl (exp_self_form pq D d M1) (exp_self_form pq D d M2)
      | a_exfalso A M' => a_exfalso (exp_self_form pq D (S d) A) (exp_self_form pq D d M')
      | a_elim oq Us m Bks M' =>
          a_elim oq (List.map (exp_self_form pq D d) Us) m
            ((fix blocks_self_form (Bks : list eblock) : list eblock :=
                match Bks with
                | nil => nil
                | eb_mk nm oZ A Bs :: Bks' =>
                    eb_mk nm (match oZ with Some Z => Some (exp_self_form pq D (nm - 1 + d) Z) | None => None end)
                      (exp_self_form pq D (nm + d) A)
                      (List.map (fun b => (fst b, exp_self_form pq D (snd (fst b) + d) (snd b))) Bs)
                    :: blocks_self_form Bks'
                end) Bks)
            (exp_self_form pq D d M')
      | a_pi A B => a_pi (exp_self_form pq D d A) (exp_self_form pq D (S d) B)
      | a_fn A M' => a_fn (exp_self_form pq D d A) (exp_self_form pq D (S d) M')
      | a_app M1 M2 => a_app (exp_self_form pq D d M1) (exp_self_form pq D d M2)
      | a_var x => a_var (if x <? d then x else x + ind_ndecl D)
      | a_mem H x => a_mem (modexp_self_form pq D d H) x
      | a_tuple T fs => a_tuple (exp_self_form pq D d T) (List.map (fun f => (fst f, exp_self_form pq D d (snd f))) fs)
      | a_proj f M' => a_proj f (exp_self_form pq D d M')
      | _ => M
      end
  end
(** [exp_self_form] on module expressions: the module variables moved past
    the [Self]s, the arguments read back. *)
with modexp_self_form (pq : qname) (D : ind_decl) (d : nat) (H : modexp) {struct H} : modexp :=
  match H with
  | me_var x => me_var (if x <? d then x else x + ind_ndecl D)
  | me_mem H' y => me_mem (modexp_self_form pq D d H') y
  | me_app H' N => me_app (modexp_self_form pq D d H') (exp_self_form pq D d N)
  | _ => H
  end.

(** The views' instances with the members as variables: at a view, its
    filed instance read back ([exp_self_form]). *)
Definition grp_self_insts (pq : qname) (D : ind_decl) (k : nat) : list exp :=
  match ind_member D k with
  | Some Mk =>
      match im_head Mk with
      | mh_view _ _ Is _ => List.map (exp_self_form pq D 0) Is
      | mh_decl _ => nil
      end
  | None => nil
  end.

(** The premises of [wf_gentry_ind_nil], at the views' instances with the
    members as variables [IsS] given, rather than any: the command checks
    the group at the instances it reads back ([grp_self_insts]). *)
Inductive ind_nil_at (Θ : gdeps) (Ξ : gstack) (mp : qname) (D : ind_decl) (IsS : nat -> list exp) : Prop :=
(** The only rule: the premises of [wf_gentry_ind_nil], [IsS] fixed *)
| mk_ind_nil_at : forall Δ M0 i n,
    ind_uparams D = Δ ++ gs_tele Ξ ->
    tele_ass (ind_uparams D) ->
    decl_mvc D ->
    List.length (gs_tele Ξ) <= ind_nu D ->
    ⊢ Θ ⍮ Ξ ⍮ ind_uparams D ->
    ind_order_ok D ->
    ind_member D 0 = Some M0 ->
    im_head M0 = mh_decl mp ->
    ind_sort_univ (ind_sort D) ->
    Θ ⍮ Ξ ⍮ ind_uparams D ⊢ ind_sort D : Typeω@i ->
    Θ ⍮ Ξ ⍮ ind_uparams D ⊢ ind_sort_lvl (ind_sort D) : Level@n ->
    (forall k Mk, ind_member D k = Some Mk -> tele_ass (im_nparams Mk)) ->
    (forall k Mk, ind_member D k = Some Mk -> List.NoDup (List.map fst (im_cons Mk))) ->
    (forall k Mk Δ1 T Δ2, ind_member D k = Some Mk -> im_nparams Mk = Δ1 ++ ce_ass T :: Δ2 ->
       Θ ⍮ Ξ ⍮ Δ2 ++ ind_uparams D ⊢ T : (ind_sort D)[wk_shiftn (List.length Δ2)]ʷ) ->
    (forall k Mk c gs gs1 A gs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_arg A :: gs2 ->
       Θ ⍮ Ξ ⍮ cargs_strat gs1 ++ im_params D Mk
         ⊢ A : (ind_sort D)[wk_shiftn (List.length (cargs_strat gs1) + im_nn Mk)]ʷ) ->
    (forall k Mk c gs gs1 t gs2 Bs1 B Bs2, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) ->
       gs = gs1 ++ ca_rec t :: gs2 -> ptyp_doms t = Bs1 ++ B :: Bs2 ->
       Θ ⍮ Ξ ⍮ doms_ctx Bs1 ++ cargs_strat gs1 ++ im_params D Mk
         ⊢ B : (ind_sort D)[wk_shiftn (List.length Bs1 + List.length (cargs_strat gs1) + im_nn Mk)]ʷ) ->
    (forall k Mk c gs, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) -> cargs_plen D gs) ->
    (forall k Mk c gs gs1 t gs2 Mj j P T, ind_member D k = Some Mk -> In (c, gs) (im_cons Mk) ->
       gs = gs1 ++ ca_rec t :: gs2 -> ind_member D (ptyp_mem t) = Some Mj ->
       nth_error (ptyp_ps t) j = Some P ->
       nth_error (tele_insts (im_nparams Mj)
                    (sb_of_wk (wk_shiftn (ptyp_depth t + List.length (cargs_strat gs1) + im_nn Mk))) (ptyp_ps t)) j
         = Some T ->
       Θ ⍮ Ξ ⍮ ptyp_tele t ++ cargs_strat gs1 ++ im_params D Mk ⊢ P : T) ->
    (** the views *)
    (forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       exists D' Mk', ind_lookup Θ Ξ qc = Some D' /\ ind_member D' k' = Some Mk' /\ k' < ind_ndecl D' /\
         List.length Is = ind_nu D' /\ List.length vm = List.length (ind_members D') /\
         List.nth_error vm k' = Some k /\
         List.map fst (im_cons Mk) = List.map fst (im_cons Mk') /\
         (forall c gs' gs, ind_con Mk' c = Some gs' -> ind_con Mk c = Some gs -> cargs_corr vm gs' gs)) ->
    (** each view's instance [Is] is [IsS] with the members as variables *)
    (forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       Is = List.map (fun I => I[grp_sb mp D]) (IsS k)) ->
    (forall k Mk qc k' Is vm D' j I T, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> nth_error (IsS k) j = Some I ->
       nth_error (tele_insts (ind_uparams D') Id (IsS k)) j = Some T ->
       Θ ⍮ Ξ ⍮ grp_sctx D ⊢ I : T) ->
    (forall k Mk qc k' Is vm D' i' Mi' v pm', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_decl pm' ->
       nth_error vm i' = Some v ->
       exists Mv vm', ind_member D v = Some Mv /\ im_head Mv = mh_view qc i' Is vm') ->
    (forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' ->
       nth_error vm i' = Some v ->
       exists Mv X vm', ind_member D v = Some Mv /\ im_head Mv = mh_view q'' k'' X vm' /\
         List.length X = List.length Is'') ->
    (forall k Mk qc k' Is vm D' i' Mi' v q'' k'' Is'' vm'' D'' Mv X vm' j' C C' T,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_view q'' k'' Is'' vm'' ->
       ind_lookup Θ Ξ q'' = Some D'' ->
       nth_error vm i' = Some v -> ind_member D v = Some Mv -> im_head Mv = mh_view q'' k'' X vm' ->
       nth_error (IsS v) j' = Some C ->
       nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
       nth_error (tele_insts (ind_uparams D'') Id Is'') j' = Some T ->
       Θ ⍮ Ξ ⍮ grp_sctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)]) ->
    (** the view equations *)
    (forall k Mk qc k' Is vm D' i' Mi' v Mv, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv ->
       Θ ⍮ Ξ ⍮ grp_sctx D ⊢ˣ tele_wk (im_nparams Mv) (self_wk D 0) ≈ tele_sub (im_nparams Mi') (sb_of_list Id (IsS k))) ->
    (forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       Θ ⍮ Ξ ⍮ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
         ⊢ˣ tele_sub (cargs_ctx qc D' Mi' gs') (sb_qn (im_nn Mv) (sb_of_list Id (IsS k))) ≈ scargs_ctx D IsS Mv gs) ->
    (forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 d,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       d < ptyp_depth t ->
       Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (List.firstn d (ptyp_doms t))) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
         ⊢ (ptyp_dom_at (cargs_pat gs1') d t')[sb_qn (d + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
         ≈ (ptyp_dom_at (cargs_pat gs1) d t)[self_wk D (d + List.length gs1 + im_nn Mv)]ʷ : Typeω@i) ->
    (forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 Mj j P' P T,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       ind_member D (ptyp_mem t) = Some Mj ->
       nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P' -> nth_error (ptyp_ps_at (cargs_pat gs1) t) j = Some P ->
       nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                    (ptyp_ps_at (cargs_pat gs1) t)) j = Some T ->
       Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
         ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
         : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ) ->
    (forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs gs1' t' gs2' gs1 t gs2 Mj j P' P T,
       ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> nth_error vm i' = Some v ->
       ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
       gs' = gs1' ++ ca_rec t' :: gs2' -> gs = gs1 ++ ca_rec t :: gs2 -> List.length gs1' = List.length gs1 ->
       ind_member D (ptyp_mem t) = Some Mj ->
       nth_error (ptyp_ps_at (cargs_pat gs1') t') j = Some P' -> nth_error (ptyp_ps_at (cargs_pat gs1) t) j = Some P ->
       nth_error (tele_insts (im_nparams Mj) (sb_of_list Id (ind_uvars D (im_nn Mv) (ptyp_depth t + List.length gs1)))
                    (ptyp_ps_at (cargs_pat gs1) t)) j = Some T ->
       Θ ⍮ Ξ ⍮ tele_wk (sh_ctx (cargs_pat gs1) (ptyp_doms t)) (self_wk D (List.length gs1 + im_nn Mv))
                 ++ scargs_ctx D IsS Mv gs1 ++ tele_wk (im_nparams Mv) (self_wk D 0) ++ grp_sctx D
         ⊢ P'[sb_qn (ptyp_depth t + List.length gs1 + im_nn Mv) (sb_of_list Id (IsS k))]
         ≈ P[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ
         : T[self_wk D (ptyp_depth t + List.length gs1 + im_nn Mv)]ʷ) ->
    (forall k Mk qc k' Is vm D', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       ind_lookup Θ Ξ qc = Some D' ->
       Θ ⍮ Ξ ⍮ grp_sctx D ⊢ (ind_sort D')[sb_of_list Id (IsS k)] ⊆ (ind_sort D)[self_wk D 0]ʷ) ->
    (** the views' nesting is well founded *)
    (exists rk, view_rank_ok Θ Ξ D rk) ->
    (** each view's members are those of the container's group *)
    (forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
       exists D', ind_lookup Θ Ξ qc = Some D' /\ vwrap_ok D D' vm) ->
    (** the views agree on their maps *)
    view_maps_coherent Θ Ξ D ->
    ind_nil_at Θ Ξ mp D IsS.

(** The group checked at the instances [IsS] is a well-formed entry. *)
Lemma ind_nil_at_entry : forall Θ Ξ mp D IsS, ind_nil_at Θ Ξ mp D IsS -> forall pv, Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_ind pv mp 0 D ⋄.
Proof. intros * [] pv; eapply wf_gentry_ind_nil; eassumption. Qed.

(** ** Mutual Definitions

    A mutual definition's group ([mdef_group]) and the definitions it
    files ([mdef_defs]) are in [Translations]; they are filed in order,
    each checked as a definition is. *)

(** [mdefs_run Θ b pv ds Ξ Ξ']: filing the definitions [ds] in order in
    [Ξ], each checked at its type as [rc_def] does, gives [Ξ']. *)
Inductive mdefs_run (Θ : gdeps) (b pv : bool) : list (string * typ * exp) -> gstack -> gstack -> Prop :=
(** No definition left *)
| mdefs_nil : forall Ξ, mdefs_run Θ b pv nil Ξ Ξ
(** The next definition, checked and filed, then the rest *)
| mdefs_cons : forall x A M ds Ξ Ξ',
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    gs_fresh x Ξ ->
    mdefs_run Θ b pv ds (gs_add x (gs_def b pv Ξ A M) Ξ) Ξ' ->
    mdefs_run Θ b pv ((x, A, M) :: ds) Ξ Ξ'.

(** ** Merging Filed Units

    A loaded unit runs from nothing, so what its run filed is merged into the
    importer's units: the ones not filed yet are added on top, in their order.
    A path filed on both sides was loaded by two runs of the same file, so it
    is the same unit ([canon_agree]). *)

Definition gds_mem (fp : path) (Θ : gdeps) : bool :=
  match gds_lookup Θ fp with Some _ => true | None => false end.

Definition gds_merge (Θ Θ' : gdeps) : gdeps :=
  filter (fun e => negb (gds_mem (fst e) Θ)) Θ' ++ Θ.

Definition gds_agree (Θ Θ' : gdeps) : Prop :=
  forall fp U U', gds_lookup Θ fp = Some U -> gds_lookup Θ' fp = Some U' -> U = U'.

(** ** The Records of Filed Units

    The record of builtin bindings each filed unit ended with, apart from
    the units themselves: merged as they are ([bm_merge]). *)

Definition bmap : Set := list (path * builtins).

Fixpoint bm_lookup (Rb : bmap) (fp : path) : option builtins :=
  match Rb with
  | nil => None
  | (fq, B) :: Rb' => if path_beq fp fq then Some B else bm_lookup Rb' fp
  end.

Definition bm_mem (fp : path) (Rb : bmap) : bool :=
  match bm_lookup Rb fp with Some _ => true | None => false end.

Definition bm_merge (Rb Rb' : bmap) : bmap :=
  filter (fun e => negb (bm_mem (fst e) Rb)) Rb' ++ Rb.

Lemma bm_lookup_merge : forall Rb Rb' fp,
    bm_lookup (bm_merge Rb Rb') fp = match bm_lookup Rb fp with Some B => Some B | None => bm_lookup Rb' fp end.
Proof.
  intros Rb Rb' fp; unfold bm_merge; induction Rb' as [| [fq V] Rb' IH]; cbn [filter List.app].
  - destruct (bm_lookup Rb fp); reflexivity.
  - unfold bm_mem at 1; cbn [fst]; destruct (bm_lookup Rb fq) eqn:Hq; cbn [negb]; rewrite ?IH.
    + cbn [bm_lookup]; destruct (bm_lookup Rb fp) eqn:Hp; [ reflexivity |].
      destruct (path_beq fp fq) eqn:Hb; [ apply path_beq_true in Hb; congruence | reflexivity ].
    + cbn [bm_lookup List.app]; rewrite IH.
      destruct (path_beq fp fq) eqn:Hb; [| reflexivity ].
      apply path_beq_true in Hb; subst; rewrite Hq; reflexivity.
Qed.

(** ** Record Declarations

    A record is filed as one entry ([ge_record]): its declaration, with the
    parameters of the frames as its outermost parameters, and the body of
    its module, an ordinary module over the record's parameters and then a
    value of it.  The body starts with the record's fields, one generated
    definition each, the field's projection of the value, followed by the
    entries of the with-area's commands, run in the record's frame as the
    commands of a module body are. *)

(** The record declared over the frames' parameters with its own
    parameters [Δ], its sort [S] and its fields [fs], all as written over
    [Δ] and the frames' parameters. *)
Definition record_at (Ξ : gstack) (Δ : ctx) (S : typ) (fs : list (string * typ)) : record_decl :=
  mk_record_decl (Δ ++ gs_tele Ξ) S fs.

(** The type of the field [k], of type [T] over the fields before it and
    the parameters, in the record's module: at the module's parameters and
    the projections of its value at the fields before it, as [wf_proj]
    types the projection. *)
Definition record_field_ty (R : record_decl) (k : nat) (T : typ) : typ :=
  T[sb_of_list Id (vars_from 1 (List.length (record_params R)) ++ record_pre R k (a_var 0))].

(** The field definitions of the fields [fs] of [R] from the field [k] on:
    each the field's projection of the module's value, at its type. *)
Fixpoint record_fields_cmds (R : record_decl) (k : nat) (fs : list (string * typ)) : list ccmd :=
  match fs with
  | nil => nil
  | (f, T) :: fs' =>
      cc_gen (cc_def f true false (record_field_ty R k T) (Some (a_proj f (a_var 0)))) :: record_fields_cmds R (S k) fs'
  end.

(** The field definitions of the record [R], the first entries of its
    module. *)
Definition record_field_cmds (R : record_decl) : list ccmd := record_fields_cmds R 0 (record_fields R).

(** The name a command declares in the frame it runs in, if any. *)
Definition cmd_decl_name (c : ccmd) : option string :=
  match c with
  | cc_def x _ _ _ _ | cc_mod x _ _ _ | cc_alias x _ _ _ | cc_ind_alias x _ _ _ | cc_record x _ _ _ _ _ => Some x
  | _ => None
  end.

(** The fill keeps the name a command declares. *)
Lemma fill_cmd_name : forall Θ Ξ B c c', fill_cmd Θ Ξ B c c' -> cmd_decl_name c' = cmd_decl_name c.
Proof. intros * H; destruct H; reflexivity. Qed.

(** ** Privacy

    Every command checks the terms it introduces for access to private
    members ([acc_ok], in [Privacy]); typing does not. *)

Section Semantics.
  (** File IO: the contents of the unit at a path, if there is one. *)
  Variable load_path : path -> option string.
  (** Lexing and parsing.  The lexer is OCaml, so this is a parameter too. *)
  Variable read : string -> option Cst.prog.
  (** Elaboration into core commands, which needs no filed unit. *)
  Variable to_core : Cst.prog -> option cunit.

  (** ** Running

      [Θ ⍮ Ξ ⊢[ch] c ⇝ Θ' ⍮ Ξ']: [ch] is the chain of units being loaded, the
      one running [c] first.  Only [rc_load] changes [Θ]; the premises
      of [rc_def], [rc_axiom], [rc_mod] and [rc_alias] are those of
      [wf_gentry_def], [wf_gentry_axiom], [wf_gmod_nil] and
      [wf_gentry_alias], with the freshness of [wf_gmod_ext].  Privacy is checked by
      [rcs_cons], on the command as written.

      [B] is the record of builtin bindings of the unit being run, and [Rb]
      the records the filed units ended with, one per unit of [Θ]: a unit
      sees the bindings it makes and those of the units it imports, never
      those of the unit importing it. *)

  (** Running one command; mutually, a list of them and a unit. *)
  Inductive run_cmd : list path -> builtins -> bmap -> gdeps -> gstack -> ccmd -> builtins -> bmap -> gdeps -> gstack -> Prop :=
  (** A definition: its body is checked at its type. *)
  | rc_def : forall ch B Rb Θ Ξ x b pv A M,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_def x b pv A (Some M) ⇝ Θ ⍮ gs_add x (gs_def b pv Ξ A M) Ξ ⍮ B ⍮ Rb
  (** An axiom: only its type is checked. *)
  | rc_axiom : forall ch B Rb Θ Ξ x b pv A i,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_def x b pv A None ⇝ Θ ⍮ gs_add x (gs_axiom b pv Ξ A) Ξ ⍮ B ⍮ Rb
  (** The body ends on the frame it opened, the stack below as it was; that
      frame becomes the member [x] of the one below, as it is. *)
  | rc_mod : forall ch B Rb B' Rb' Θ Ξ x pv Δ cs Θ' mp K U,
      tele_ass Δ ->
      ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
      gs_fresh x Ξ ->
      Θ ⍮ gs_push (qname_in (gs_path Ξ) x) Δ Ξ ⍮ B ⍮ Rb ⊢[ch] cs ⇝* Θ' ⍮ (mp, K, U) :: Ξ ⍮ B' ⍮ Rb' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_mod x pv Δ cs ⇝ Θ' ⍮ gs_add x (ge_body pv Δ (gu_mod U)) Ξ ⍮ B' ⍮ Rb'
  (** An alias is filed with the frames' parameters it is declared under. *)
  | rc_alias : forall ch B Rb Θ Ξ x pv Δ E,
      tele_ass Δ ->
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
      Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_alias x pv Δ E ⇝ Θ ⍮ gs_add x (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))) Ξ ⍮ B ⍮ Rb
  (** A unit filed already, by an earlier load: shared, not reloaded; the
      record it ended with is merged in. *)
  | rc_load_filed : forall ch B Rb B' Θ Ξ fp U BU,
      gds_lookup Θ fp = Some U ->
      bm_lookup Rb fp = Some BU ->
      bt_merge B BU = Some B' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_load fp ⇝ Θ ⍮ Ξ ⍮ B' ⍮ Rb
  (** Not filed: load it, run it from nothing with itself added to the chain,
      file it on top of what it filed, and merge that in.  A unit already in the
      chain is still being loaded, so loading it is a cycle, and no rule
      applies.  The unit runs from no binding; the record it ends with is
      merged in, and filed with it. *)
  | rc_load : forall ch B Rb B' Θ Ξ fp src prg u BU RbU ΘU U,
      gds_lookup Θ fp = None ->
      ~ In fp ch ->
      load_path fp = Some src ->
      read src = Some prg ->
      prog_path prg = fp ->
      to_core prg = Some u ->
      run_unit (fp :: ch) u BU RbU ΘU U ->
      bt_merge B BU = Some B' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_load fp ⇝ gds_merge Θ ((fp, U) :: ΘU) ⍮ Ξ ⍮ B' ⍮ bm_merge Rb ((fp, BU) :: RbU)
  (** An open checks that its target is a module, and declares the
      definitions and aliases its items generate in this frame. *)
  | rc_open : forall ch B Rb Θ Ξ E its gs Ξ',
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ E ≈ E ->
      open_gens Θ Ξ true (gs_tele Ξ) E its gs ->
      gens_run Θ Ξ gs Ξ' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_open E its ⇝ Θ ⍮ Ξ' ⍮ B ⍮ Rb
  (** A group as written, its members of one sort: the arguments of the
      declared members classified ([rm_cls]); the views, found from the
      instances met ([views_bfs]), each with its siblings, its
      constructors classified and its non-uniform parameters filed
      ([view_nps]); the group filed ([rd_filed]) and checked at its
      views' instances read back ([ind_nil_at], [grp_self_insts]); the
      names it generates left free ([gen_names_free]); the declared
      members, each with its module ([run_ind_members]); then, for a group
      declared by [mutual T where], its recursor module ([rec_cmds]), run
      as written commands are. *)
  | rc_ind : forall ch B Rb Θ Ξ pv R Mr0 Mrs csD Vs Ss csV Nvs D B' Rb' Θ' Ξ' B'' Rb'' Θ'' Ξ'',
      rd_members R = Mr0 :: Mrs ->
      Forall (fun Mr => rm_sort Mr = rm_sort Mr0) Mrs ->
      Forall2 (rm_cls Θ Ξ R) (rd_members R) csD ->
      Forall2 (view_sibs Θ Ξ R) Vs Ss ->
      Forall2 (view_cls Θ Ξ R) Vs csV ->
      Forall2 (view_nps Θ Ξ R) Vs Nvs ->
      views_bfs (sibs_tbl Vs Ss) (meets_tbl Vs csV) nil (List.concat (List.map rcons_views csD)) Vs ->
      rd_filed Θ Ξ R Vs Ss csD csV Nvs = Some D ->
      ind_nil_at Θ Ξ (ind_qname Ξ (rm_name Mr0)) D (grp_self_insts (ind_qname Ξ (rm_name Mr0)) D) ->
      gen_names_free Ξ R D ->
      run_ind_members ch B Rb Θ Ξ pv R (ind_qname Ξ (rm_name Mr0)) D 0 (List.map rm_name (rd_members R)) B' Rb' Θ' Ξ' ->
      Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ⊢[ch] rec_cmds Θ' Ξ' R (ind_qname Ξ (rm_name Mr0)) D ⇝* Θ'' ⍮ Ξ'' ⍮ B'' ⍮ Rb'' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_ind pv R ⇝ Θ'' ⍮ Ξ'' ⍮ B'' ⍮ Rb''
  (** A mutual definition: the group, its uniform parameters and each
      function's member ([mdef_group]), and the definitions filed in order,
      each checked as a definition is. *)
  | rc_mdef : forall ch B Rb Θ Ξ b pv Δ f0 fs pq m0 Ps D Us ms Ξ',
      tele_ass Δ ->
      ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
      mdef_group Θ Ξ Δ f0 fs pq m0 Ps D Us ms ->
      mdefs_run Θ b pv (mdef_defs pq D Us Δ (f0 :: fs) ms) Ξ Ξ' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_mdef b pv Δ (f0 :: fs) ⇝ Θ ⍮ Ξ' ⍮ B ⍮ Rb
  (** [builtin natural := X]: [X], a module expression, denotes an inductive type at no argument
      and over no parameter, with the shape of the natural numbers, in
      [Type@0]; its binding is merged in ([bt_bind_nat]), so it is bound
      unless another type is. *)
  | rc_builtin : forall ch B Rb B' Θ Ξ H p D z s,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ᵐ H ≈ H ->
      mdenote Θ Ξ (gs_tele Ξ) H (ds_ind nil p 0 nil) ->
      ind_lookup Θ Ξ p = Some D ->
      nat_shape D = Some (z, s) ->
      ind_sort D = nat_sort ->
      bt_bind_nat B p = Some B' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_builtin nat_kind H ⇝ Θ ⍮ Ξ ⍮ B' ⍮ Rb
  (** [inductive x Δ := E]: [E], a module expression, denotes an inductive
      type at arguments [Ns], over the parameters [Θ'] it is still
      abstracted over; the alias stores the canonical path and the
      arguments, over [Θ'] and [Δ], checked as its entry. *)
  | rc_ind_alias : forall ch B Rb Θ Ξ x pv Δ H Θ' p k Ns D pm,
      Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ H ≈ H ->
      mdenote Θ Ξ (Δ ++ gs_tele Ξ) H (ds_ind Θ' p k Ns) ->
      ind_lookup Θ Ξ p = Some D ->
      ind_mpath D k = Some pm ->
      Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind_alias pv (Θ' ++ Δ ++ gs_tele Ξ) pm p k Ns ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_ind_alias x pv Δ H ⇝
        Θ ⍮ gs_add x (ge_ind_alias pv (Θ' ++ Δ ++ gs_tele Ξ) pm p k Ns) Ξ ⍮ B ⍮ Rb
  (** A record: checked with an empty module where it is filed
      ([wf_gentry_record]); its module's frame is opened over the record's
      own parameters and then a value of it, its field definitions and then
      its with-area run in it as a module body's commands do, and the record
      is filed with the body they end with, as [rim_cons] files a member of
      a group. *)
  | rc_record : forall ch B Rb Θ Ξ x pv Δ Srt fs cs B1 Rb1 Θ1 Ξ1 B' Rb' Θ' mp K U,
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_record pv (ind_qname Ξ x) (record_at Ξ Δ Srt fs) ⋄ ->
      Θ ⍮ gs_push_record (ind_qname Ξ x) (record_at Ξ Δ Srt fs) Δ Ξ ⍮ B ⍮ Rb ⊢[ch]
        record_field_cmds (record_at Ξ Δ Srt fs) ⇝* Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
      Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ⊢[ch] cs ⇝* Θ' ⍮ (mp, K, U) :: Ξ ⍮ B' ⍮ Rb' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_record x pv Δ Srt fs cs ⇝
        Θ' ⍮ gs_add x (ge_record pv (ind_qname Ξ x) (record_at Ξ Δ Srt fs) (gu_mod U)) Ξ ⍮ B' ⍮ Rb'
  (** An [eval] changes nothing, but must type-check where it stands. *)
  | rc_eval_check : forall ch B Rb Θ Ξ M A,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_eval M (Some A) ⇝ Θ ⍮ Ξ ⍮ B ⍮ Rb
  (** An [eval] with no type given: it must have some type. *)
  | rc_eval_infer : forall ch B Rb Θ Ξ M A,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_eval M None ⇝ Θ ⍮ Ξ ⍮ B ⍮ Rb
  (** A generated definition runs as a definition does; it makes no
      reference of its own ([cmd_refs]), so its privacy is not checked. *)
  | rc_gen_def : forall ch B Rb Θ Ξ x b pv A M,
      Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_gen (cc_def x b pv A (Some M)) ⇝ Θ ⍮ gs_add x (gs_def b pv Ξ A M) Ξ ⍮ B ⍮ Rb
  (** A generated module runs as a module does; nor is its privacy
      checked. *)
  | rc_gen_mod : forall ch B Rb B' Rb' Θ Ξ x pv Δ cs Θ' mp K U,
      tele_ass Δ ->
      ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
      gs_fresh x Ξ ->
      Θ ⍮ gs_push (qname_in (gs_path Ξ) x) Δ Ξ ⍮ B ⍮ Rb ⊢[ch] cs ⇝* Θ' ⍮ (mp, K, U) :: Ξ ⍮ B' ⍮ Rb' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] cc_gen (cc_mod x pv Δ cs) ⇝ Θ' ⍮ gs_add x (ge_body pv Δ (gu_mod U)) Ξ ⍮ B' ⍮ Rb'
  where "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ] c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'" := (run_cmd ch B Rb Θ Ξ c B' Rb' Θ' Ξ')

  with run_cmds : list path -> builtins -> bmap -> gdeps -> gstack -> list ccmd -> builtins -> bmap -> gdeps -> gstack -> Prop :=
  | rcs_nil : forall ch B Rb Θ Ξ, Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] nil ⇝* Θ ⍮ Ξ ⍮ B ⍮ Rb
  (** Each command is checked for privacy as written, then filled
      ([fill_cmd]: its literals from the builtin bindings, its
      eliminators' groups and uniform parameters from their scrutinees'
      types, its accesses through terms of record types), before it
      runs. *)
  | rcs_cons : forall ch B Rb Θ Ξ c c' cs B1 Rb1 Θ1 Ξ1 B2 Rb2 Θ2 Ξ2,
      acc_ok Θ Ξ (cmd_refs c) ->
      fill_cmd Θ Ξ B c c' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] c' ⇝ Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
      Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ⊢[ch] cs ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2 ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch] c :: cs ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2
  where "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ] cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'" := (run_cmds ch B Rb Θ Ξ cs B' Rb' Θ' Ξ')

  (** [run_unit (fp :: ch) u B Rb Θ U]: the unit [fp], at the head of the
      chain, runs from nothing filed and no binding.  Its leading loads run
      on the empty stack, then its parameters are filled ([fill_params])
      and checked against what they filed, then its body runs in its own
      frame, named [fp]; [Θ] is what it filed, [Rb] their records, [U]
      the unit, [B] its own record. *)
  with run_unit : list path -> cunit -> builtins -> bmap -> gdeps -> gunit -> Prop :=
  | ru_intro : forall fp ch B1 Rb1 B2 Rb2 imps P P' cs Θ1 Θ2 mp K U,
      nil ⍮ nil ⍮ bt_empty ⍮ nil ⊢[fp :: ch] imps ⇝* Θ1 ⍮ nil ⍮ B1 ⍮ Rb1 ->
      fill_params Θ1 nil B1 P P' ->
      tele_ass P' ->
      ⊢ Θ1 ⍮ nil ⍮ P' ->
      acc_ok Θ1 nil (tele_refs nil P) ->
      Θ1 ⍮ gs_push (q_abs fp nil) P' nil ⍮ B1 ⍮ Rb1 ⊢[fp :: ch] cs ⇝* Θ2 ⍮ (mp, K, U) :: nil ⍮ B2 ⍮ Rb2 ->
      run_unit (fp :: ch) (imps, P, cs) B2 Rb2 Θ2 U

  (** [run_ind_members ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ']: the
      declared members [k], [k + 1], … of the group [D] at [pq], declared
      as [R], named [xs], in order.  Each is checked with an empty module
      where it is filed, after those before it; its module's frame is
      opened over the group's own uniform parameters, its generated
      commands ([ind_mod_cmds]) run in it as a module body's do, and the
      member is filed with the body they end with, as [rc_mod] files a
      module. *)
  with run_ind_members : list path -> builtins -> bmap -> gdeps -> gstack -> bool -> raw_decl -> qname -> ind_decl ->
                         nat -> list string -> builtins -> bmap -> gdeps -> gstack -> Prop :=
  (** No member left *)
  | rim_nil : forall ch B Rb Θ Ξ pv R pq D k, run_ind_members ch B Rb Θ Ξ pv R pq D k nil B Rb Θ Ξ
  (** The member [k], named [x]: checked with an empty module, its
      module's commands run in its frame, filed; then the rest *)
  | rim_cons : forall ch B Rb Θ Ξ pv R pq D k x xs M B1 Rb1 Θ1 mp K U B2 Rb2 Θ2 Ξ2,
      ind_member D k = Some M ->
      gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k D ⋄ ->
      Θ ⍮ gs_push_ind (ind_qname Ξ x) pq k D (rd_uparams R) Ξ ⍮ B ⍮ Rb ⊢[ch]
        ind_mod_cmds Θ (gs_push_ind (ind_qname Ξ x) pq k D (rd_uparams R) Ξ) R pq D k M ⇝*
        Θ1 ⍮ (mp, K, U) :: Ξ ⍮ B1 ⍮ Rb1 ->
      run_ind_members ch B1 Rb1 Θ1 (gs_add x (ge_ind pv pq k D (gu_mod U)) Ξ) pv R pq D (S k) xs B2 Rb2 Θ2 Ξ2 ->
      run_ind_members ch B Rb Θ Ξ pv R pq D k (x :: xs) B2 Rb2 Θ2 Ξ2.

  (** The unit given on the command line: run like an imported one, with
      itself as the whole chain; [B] is the record it ends with. *)
  #[warnings="-cannot-define-projection"]
  Record prog_sem (prg : Cst.prog) (B : builtins) (Θ : gdeps) (U : gunit) : Prop := mk_prog_sem
    { ps_unit : cunit
    ; ps_record : bmap
    ; ps_core : to_core prg = Some ps_unit
    ; ps_run : run_unit (prog_path prg :: nil) ps_unit B ps_record Θ U }.
End Semantics.

(** Outside the section, the judgments also name the file IO [lp], the
    lexer and parser [rd] and the elaborator [tc] they run with. *)
Notation "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ]⟨ lp ⍮ rd ⍮ tc ⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'" :=
  (run_cmd lp rd tc ch B Rb Θ Ξ c B' Rb' Θ' Ξ').
Notation "Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ ch ]⟨ lp ⍮ rd ⍮ tc ⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'" :=
  (run_cmds lp rd tc ch B Rb Θ Ξ cs B' Rb' Θ' Ξ').


(** ** A Cycle Has No Meaning *)

Lemma load_acyclic : forall load_path read to_core ch B Rb Θ Ξ fp B' Rb' Θ' Ξ',
    In fp ch ->
    gds_lookup Θ fp = None ->
    ~ Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_load fp ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'.
Proof.
  intros * Hin Hnone Hr; inversion Hr; subst; [ congruence | contradiction ].
Qed.

(** ** Running is Deterministic

    Every rule is a check, never a choice, and [load_path], [read] and [to_core]
    are functions; the chain only decides whether a run succeeds.  This is what
    makes a path filed by two runs the same unit, so the merge loses
    nothing. *)

Lemma open_gens_functional : forall Θ Ξ io Γ H its gs1 gs2, ⊢ᵍ Θ ⍮ Ξ ->
    open_gens Θ Ξ io Γ H its gs1 -> open_gens Θ Ξ io Γ H its gs2 -> gs1 = gs2.
Proof.
  intros * Hg [_ _ _ _ H1 _] [_ _ _ _ H2 _].
  destruct (mdenote_functional_all _ _ Hg) as (_ & _ & _ & _ & Hf); exact (Hf _ _ _ _ _ H1 _ H2).
Qed.

Lemma gens_run_functional : forall Θ Ξ gs Ξ1, gens_run Θ Ξ gs Ξ1 -> forall Ξ2, gens_run Θ Ξ gs Ξ2 -> Ξ1 = Ξ2.
Proof. induction 1; intros * H2; inversion H2; subst; auto. Qed.

Lemma Forall2_index : forall {Y} (P : rview -> Y -> Prop) Vs Ys x v d, Forall2 P Vs Ys -> rview_index x Vs = Some v ->
    P x (List.nth v Ys d).
Proof.
  intros * H Hv; apply rview_index_in in Hv; revert v Hv; induction H as [| y0 y Vs Ys Hy _ IH]; intros [| v] Hv;
    cbn in Hv; try discriminate; [ injection Hv as <-; exact Hy | apply IH; exact Hv ].
Qed.

Lemma rview_index_in_some : forall x Vs, In x Vs -> exists v, rview_index x Vs = Some v.
Proof.
  intros x Vs H; apply rview_mem_spec in H; unfold rview_mem in H.
  destruct (rview_index x Vs); [ eauto | discriminate ].
Qed.

Lemma nbes_functional : forall Θ Ξ Γ Ms As Ws Ws', nbes Θ Ξ Γ Ms As Ws -> nbes Θ Ξ Γ Ms As Ws' -> Ws = Ws'.
Proof.
  intros * H; revert Ws'; induction H; intros Ws' H'; inversion H'; subst; [ reflexivity |].
  f_equal; [ eapply functional_nbe; eassumption | auto ].
Qed.

Lemma sibs_from_functional : forall Θ Ξ Γc qc Cs i ms ss ss',
    sibs_from Θ Ξ Γc qc Cs i ms ss -> sibs_from Θ Ξ Γc qc Cs i ms ss' -> ss = ss'.
Proof.
  intros * H; revert ss'; induction H; intros ss' H'; inversion H'; subst; try congruence; f_equal; auto.
  match goal with H1 : im_head ?M = _, H2 : im_head ?M = _ |- _ => rewrite H1 in H2; injection H2 as <- <- <- <- end.
  match goal with H1 : ind_lookup _ _ ?qn = _, H2 : ind_lookup _ _ ?qn = _ |- _ => rewrite H1 in H2; injection H2 as <- end.
  f_equal; f_equal; eapply nbes_functional; eassumption.
Qed.

Lemma view_sibs_functional : forall Θ Ξ R x ss ss', view_sibs Θ Ξ R x ss -> view_sibs Θ Ξ R x ss' -> ss = ss'.
Proof.
  intros * H H'; destruct H; inversion H'; subst.
  match goal with H1 : ind_lookup _ _ ?qn = _, H2 : ind_lookup _ _ ?qn = _ |- _ => rewrite H1 in H2; injection H2 as <- end.
  eapply sibs_from_functional; eassumption.
Qed.

Lemma view_cls_functional : forall Θ Ξ R x cs cs', view_cls Θ Ξ R x cs -> view_cls Θ Ξ R x cs' -> cs = cs'.
Proof.
  intros * H H'; destruct H; inversion H'; subst.
  match goal with H1 : ind_lookup _ _ ?qn = _, H2 : ind_lookup _ _ ?qn = _ |- _ => rewrite H1 in H2; injection H2 as <- end.
  match goal with H1 : ind_member ?D ?k = _, H2 : ind_member ?D ?k = _ |- _ => rewrite H1 in H2; injection H2 as <- end.
  eapply cls_cons_in_functional; eassumption.
Qed.

Lemma nbe_tele_functional : forall Θ Ξ Γ Δ Ws Ws', nbe_tele Θ Ξ Γ Δ Ws -> nbe_tele Θ Ξ Γ Δ Ws' -> Ws = Ws'.
Proof.
  intros * H; revert Ws'; induction H as [| A Δ W Δ' _ HW _ IH]; intros Ws' H'; inversion H'; subst; [ reflexivity |].
  match goal with HW' : nbe_ty _ _ _ A ?W' |- _ => pose proof (functional_nbe_ty _ _ _ _ HW HW') as <- end.
  f_equal; apply IH; assumption.
Qed.

Lemma view_nps_functional : forall Θ Ξ R x Nv Nv', view_nps Θ Ξ R x Nv -> view_nps Θ Ξ R x Nv' -> Nv = Nv'.
Proof.
  intros * H H'; destruct H; inversion H'; subst.
  match goal with H1 : ind_lookup _ _ ?qn = _, H2 : ind_lookup _ _ ?qn = _ |- _ => rewrite H1 in H2; injection H2 as <- end.
  match goal with H1 : ind_member ?D ?k = _, H2 : ind_member ?D ?k = _ |- _ => rewrite H1 in H2; injection H2 as <- end.
  match goal with H1 : nbe_tele _ _ _ _ ?W1, H2 : nbe_tele _ _ _ _ ?W2 |- _ =>
    pose proof (nbe_tele_functional _ _ _ _ _ _ H1 H2) as <- end.
  congruence.
Qed.

(** A group is classified, its views found and it is filed in one way. *)
Lemma rc_ind_functional : forall Θ Ξ R Mr0 csD Vs Ss csV Nvs D Mr0' csD' Vs' Ss' csV' Nvs' D',
    rd_filed Θ Ξ R Vs Ss csD csV Nvs = Some D ->
    Forall2 (rm_cls Θ Ξ R) (rd_members R) csD ->
    Forall2 (view_sibs Θ Ξ R) Vs Ss ->
    Forall2 (view_cls Θ Ξ R) Vs csV ->
    Forall2 (view_nps Θ Ξ R) Vs Nvs ->
    views_bfs (sibs_tbl Vs Ss) (meets_tbl Vs csV) nil (List.concat (List.map rcons_views csD)) Vs ->
    rd_filed Θ Ξ R Vs' Ss' csD' csV' Nvs' = Some D' ->
    Forall2 (rm_cls Θ Ξ R) (rd_members R) csD' ->
    Forall2 (view_sibs Θ Ξ R) Vs' Ss' ->
    Forall2 (view_cls Θ Ξ R) Vs' csV' ->
    Forall2 (view_nps Θ Ξ R) Vs' Nvs' ->
    views_bfs (sibs_tbl Vs' Ss') (meets_tbl Vs' csV') nil (List.concat (List.map rcons_views csD')) Vs' ->
    forall Mrs Mrs', rd_members R = Mr0 :: Mrs -> rd_members R = Mr0' :: Mrs' ->
    Mr0 = Mr0' /\ D = D'.
Proof.
  intros * Hf Hc Hs Hv Hn Hb Hf' Hc' Hs' Hv' Hn' Hb' Mrs Mrs' HM HM'.
  rewrite HM in HM'; injection HM' as <- <-.
  assert (Ecs : csD = csD') by (eapply Forall2_functional; [| exact Hc | exact Hc' ];
                                intros; unfold rm_cls in *; eapply cls_cons_in_functional; eassumption).
  subst csD'.
  assert (Agree : forall x, In x Vs -> In x Vs' -> sibs_tbl Vs Ss x = sibs_tbl Vs' Ss' x /\ meets_tbl Vs csV x = meets_tbl Vs' csV' x).
  { intros x Hx Hx'.
    destruct (rview_index_in_some _ _ Hx) as [v Hvi]; destruct (rview_index_in_some _ _ Hx') as [v' Hvi'].
    unfold sibs_tbl, meets_tbl; rewrite Hvi, Hvi'; split.
    - eapply view_sibs_functional; eapply Forall2_index; eassumption.
    - f_equal; eapply view_cls_functional; eapply Forall2_index; eassumption. }
  pose proof (views_bfs_functional _ _ _ _ _ Hb _ _ _ Hb' Agree) as <-.
  assert (ESs : Ss = Ss') by (eapply Forall2_functional; [ exact (view_sibs_functional Θ Ξ R) | exact Hs | exact Hs' ]).
  assert (EcsV : csV = csV') by (eapply Forall2_functional; [ exact (view_cls_functional Θ Ξ R) | exact Hv | exact Hv' ]).
  assert (ENv : Nvs = Nvs') by (eapply Forall2_functional; [ exact (view_nps_functional Θ Ξ R) | exact Hn | exact Hn' ]).
  subst Ss' csV' Nvs'; rewrite Hf in Hf'; injection Hf' as <-.
  split; reflexivity.
Qed.

Lemma mdefs_run_functional : forall Θ b pv ds Ξ Ξ1, mdefs_run Θ b pv ds Ξ Ξ1 -> forall Ξ2, mdefs_run Θ b pv ds Ξ Ξ2 -> Ξ1 = Ξ2.
Proof. induction 1; intros Ξ2 H2; inversion H2; subst; auto. Qed.

Scheme run_cmd_mind := Minimality for run_cmd Sort Prop
with run_cmds_mind := Minimality for run_cmds Sort Prop
with run_unit_mind := Minimality for run_unit Sort Prop
with run_ind_members_mind := Minimality for run_ind_members Sort Prop.
Combined Scheme run_mut_ind from run_cmd_mind, run_cmds_mind, run_unit_mind, run_ind_members_mind.

Section Determinism.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).
  #[local] Abbreviation run_ind_members := (run_ind_members load_path read to_core).

  (** A command with terms of its own checks a judgment where it runs, so
      its global context is well formed. *)
  Lemma run_cmd_gctx : forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ',
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> cmd_terms c = true -> ⊢ᵍ Θ ⍮ Ξ.
  Proof.
    intros * H; induction H; intros Ht; cbn in Ht; try discriminate;
      first [ solve [ auto ]
            | eapply ctx_wf_gctx, presup_exp_ctx; eassumption
            | eapply ctx_wf_gctx; eassumption
            | eapply ctx_wf_gctx, presup_ext_eq_ctx; eassumption
            | eapply ctx_wf_gctx, presup_modexp_eq_ctx; eassumption
            | match goal with Hn : ind_nil_at _ _ _ _ _ |- _ => destruct Hn; eapply ctx_wf_gctx; eassumption end
            | eapply wf_gentry_gctx; eassumption ].
  Qed.

  (** Two fills of a command agree when one of them runs. *)
  Lemma fill_unique_run : forall ch B Rb Θ Ξ c d1 d2 B' Rb' Θ' Ξ',
      fill_cmd Θ Ξ B c d1 -> fill_cmd Θ Ξ B c d2 ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ d2 ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> d1 = d2.
  Proof.
    intros * F1 F2 Hr.
    destruct (cmd_terms c) eqn:Ht.
    - assert (Ht2 : cmd_terms d2 = true) by (rewrite (fill_cmd_terms _ _ _ _ _ F2); exact Ht).
      exact (fill_cmd_functional _ _ _ (run_cmd_gctx _ _ _ _ _ _ _ _ _ _ Hr Ht2) _ _ _ F1 F2).
    - rewrite (fill_cmd_no_terms _ _ _ _ _ Ht F1), (fill_cmd_no_terms _ _ _ _ _ Ht F2); reflexivity.
  Qed.

  (** A unit runs in a frame named by the head of its chain, from no
      binding, so two runs of it agree when their chains have the same
      head. *)
  Theorem run_functional :
    (forall ch B Rb Θ Ξ c B1 Rb1 Θ1 Ξ1, Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
       forall ch' B2 Rb2 Θ2 Ξ2, Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch']⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2 ->
         Θ1 = Θ2 /\ Ξ1 = Ξ2 /\ B1 = B2 /\ Rb1 = Rb2) /\
    (forall ch B Rb Θ Ξ cs B1 Rb1 Θ1 Ξ1, Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
       forall ch' B2 Rb2 Θ2 Ξ2, Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch']⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2 ->
         Θ1 = Θ2 /\ Ξ1 = Ξ2 /\ B1 = B2 /\ Rb1 = Rb2) /\
    (forall ch u B1 Rb1 Θ1 U1, run_unit ch u B1 Rb1 Θ1 U1 ->
       forall ch' B2 Rb2 Θ2 U2, hd nil ch = hd nil ch' -> run_unit ch' u B2 Rb2 Θ2 U2 ->
         Θ1 = Θ2 /\ U1 = U2 /\ B1 = B2 /\ Rb1 = Rb2) /\
    (forall ch B Rb Θ Ξ pv R pq D k xs B1 Rb1 Θ1 Ξ1, run_ind_members ch B Rb Θ Ξ pv R pq D k xs B1 Rb1 Θ1 Ξ1 ->
       forall ch' B2 Rb2 Θ2 Ξ2, run_ind_members ch' B Rb Θ Ξ pv R pq D k xs B2 Rb2 Θ2 Ξ2 ->
         Θ1 = Θ2 /\ Ξ1 = Ξ2 /\ B1 = B2 /\ Rb1 = Rb2).
  Proof.
    (* the second derivation is the last hypothesis; fills, expansions
       and generations are unique *)
    apply run_mut_ind; intros; lazymatch goal with H2 : _ |- _ => inversion H2; subst end;
      try congruence; try solve [ repeat split; congruence ].
    all: repeat match goal with
      | F1 : fill_cmd ?a ?b ?B ?c ?d1, F2 : fill_cmd ?a ?b ?B ?c ?d2,
        Hr : run_cmd _ _ _ ?a ?b ?d2 _ _ _ _ |- _ =>
          assert_fails constr_eq d1 d2;
          pose proof (fill_unique_run _ _ _ _ _ _ _ _ _ _ _ _ F1 F2 Hr); subst d2
      | H1 : open_gens ?a ?b ?o ?G ?E ?is ?g1, H2 : open_gens ?a ?b ?o ?G ?E ?is ?g2,
        HE : _ ⍮ _ ⍮ _ ⊢ᵐ _ ≈ _ |- _ =>
          assert_fails constr_eq g1 g2;
          pose proof (open_gens_functional _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE)) H1 H2); subst g2
      end.
    (* an inductive alias: the inductive type its target denotes is one *)
    all: try solve [
      match goal with
      | He : _ ⍮ _ ⍮ _ ⊢ᵉ _, H1 : mdenote _ _ ?G ?H ?R1, H2 : mdenote _ _ ?G ?H ?R2 |- _ =>
          assert_fails constr_eq R1 R2;
          pose proof (proj1 (mdenote_functional_all _ _ (wf_gentry_gctx _ _ _ _ He)) _ _ _ H1 _ H2) as E;
          injection E as <- <- <-; repeat split; auto
      end ].
    (* a builtin binding: the type its target denotes is one, and so is the binding it makes *)
    all: try solve [
      match goal with
      | HE : _ ⍮ _ ⍮ _ ⊢ᵐ ?H ≈ _, H1 : mdenote _ _ ?G ?H ?R1, H2 : mdenote _ _ ?G ?H ?R2 |- _ =>
          assert_fails constr_eq R1 R2;
          pose proof (proj1 (mdenote_functional_all _ _ (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx HE))) _ _ _ H1 _ H2) as E;
          injection E as <-; repeat split; congruence
      end ].
    - (* a module: its body *)
      match goal with
      | IH : forall _ _ _ _ _, run_cmds _ _ _ _ _ _ _ _ _ _ -> _, H : run_cmds _ _ _ _ _ _ _ _ _ _ |- _ =>
          destruct (IH _ _ _ _ _ H) as (-> & [= -> -> ->] & -> & ->)
      end; repeat split; auto.
    - (* a load: the same file, hence the same unit *)
      repeat match goal with
        | H1 : ?f ?x = Some ?a, H2 : ?f ?x = Some ?b |- _ =>
            rewrite H1 in H2; injection H2 as <-
        end.
      match goal with
      | IH : forall _ _ _ _ _, _ -> run_unit _ _ _ _ _ _ -> _, H : run_unit ?c _ _ _ _ _ |- _ =>
          destruct (IH c _ _ _ _ eq_refl H) as (-> & -> & -> & ->)
      end; repeat split; congruence.
    - (* an import: its generated commands *)
      match goal with
      | H1 : gens_run _ _ ?gs _, H2 : gens_run _ _ ?gs _ |- _ =>
          rewrite (gens_run_functional _ _ _ _ H1 _ H2)
      end; repeat split; auto.
    - (* a group: its classification, its views and its filing, then its
         recursor module *)
      match goal with
      | Hf : rd_filed _ _ _ ?Vs ?Ss ?cs ?cV ?Nv = Some ?D1,
        Hc : Forall2 (rm_cls _ _ _) _ ?cs, Hs : Forall2 (view_sibs _ _ _) ?Vs ?Ss,
        Hv : Forall2 (view_cls _ _ _) ?Vs ?cV, Hn : Forall2 (view_nps _ _ _) ?Vs ?Nv,
        Hb : views_bfs _ _ _ _ ?Vs, HM : rd_members _ = ?M1 :: _,
        Hf' : rd_filed _ _ _ ?Vs' ?Ss' ?cs' ?cV' ?Nv' = Some ?D2,
        Hc' : Forall2 (rm_cls _ _ _) _ ?cs', Hs' : Forall2 (view_sibs _ _ _) ?Vs' ?Ss',
        Hv' : Forall2 (view_cls _ _ _) ?Vs' ?cV', Hn' : Forall2 (view_nps _ _ _) ?Vs' ?Nv',
        Hb' : views_bfs _ _ _ _ ?Vs', HM' : rd_members _ = ?M2 :: _ |- _ =>
          assert_fails constr_eq D1 D2;
          destruct (rc_ind_functional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                      Hf Hc Hs Hv Hn Hb Hf' Hc' Hs' Hv' Hn' Hb' _ _ HM HM') as (<- & <-)
      end.
      match goal with
      | IH : forall _ _ _ _ _, run_ind_members _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _,
        H : run_ind_members _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          destruct (IH _ _ _ _ _ H) as (? & ? & ? & ?); subst
      end.
      match goal with
      | IH : forall _ _ _ _ _, run_cmds _ _ _ _ _ ?cs _ _ _ _ -> _, H : run_cmds _ _ _ _ _ ?cs _ _ _ _ |- _ =>
          exact (IH _ _ _ _ _ H)
      end.
    - (* a mutual definition: the group, each function's member *)
      match goal with
      | H1 : mdef_group _ _ _ _ _ _ _ _ _ _ _, H2 : mdef_group _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          assert_fails constr_eq H1 H2;
          destruct (mdef_group_functional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2) as (<- & <- & <- & <- & <- & <-)
      end.
      repeat split; auto; eapply mdefs_run_functional; eassumption.
    - (* a record: its field definitions, then its with-area from where they end *)
      match goal with
      | IH1 : forall _ _ _ _ _, run_cmds _ _ _ _ _ (record_field_cmds _) _ _ _ _ -> _,
        H1 : run_cmds _ _ _ _ _ (record_field_cmds _) _ _ _ _ |- _ =>
          destruct (IH1 _ _ _ _ _ H1) as (? & ? & ? & ?); subst
      end.
      match goal with
      | IH2 : forall _ _ _ _ _, run_cmds _ _ _ _ _ ?cs _ _ _ _ -> _, H2 : run_cmds _ _ _ _ _ ?cs _ _ _ _ |- _ =>
          destruct (IH2 _ _ _ _ _ H2) as (-> & [= -> -> ->] & -> & ->)
      end; repeat split; auto.
    - (* a generated module: its body *)
      match goal with
      | IH : forall _ _ _ _ _, run_cmds _ _ _ _ _ _ _ _ _ _ -> _, H : run_cmds _ _ _ _ _ _ _ _ _ _ |- _ =>
          destruct (IH _ _ _ _ _ H) as (-> & [= -> -> ->] & -> & ->)
      end; repeat split; auto.
    - (* a sequence: its head, then its tail from the same state *)
      match goal with
      | IH1 : forall _ _ _ _ _, run_cmd _ _ _ _ _ ?c _ _ _ _ -> _, H1 : run_cmd _ _ _ _ _ ?c _ _ _ _ |- _ =>
          destruct (IH1 _ _ _ _ _ H1) as (? & ? & ? & ?); subst
      end.
      match goal with
      | IH2 : forall _ _ _ _ _, run_cmds _ _ _ _ _ ?cs _ _ _ _ -> _, H2 : run_cmds _ _ _ _ _ ?cs _ _ _ _ |- _ =>
          destruct (IH2 _ _ _ _ _ H2) as (? & ? & ? & ?); subst
      end.
      repeat split; auto.
    - (* a unit: its loads, then its body from what they filed *)
      cbn [hd] in *; subst.
      match goal with
      | IH1 : forall _ _ _ _ _, run_cmds _ _ _ nil nil ?is _ _ _ _ -> _, H1 : run_cmds _ _ _ nil nil ?is _ _ _ _ |- _ =>
          destruct (IH1 _ _ _ _ _ H1) as (? & ? & ? & ?); subst
      end.
      repeat match goal with
      | H1 : fill_params ?a ?b ?B ?c ?c1, H2 : fill_params ?a ?b ?B ?c ?c2, HP : ⊢ ?a ⍮ ?b ⍮ _ |- _ =>
          assert_fails constr_eq c1 c2;
          pose proof (fill_params_functional _ _ _ (ctx_wf_gctx _ _ _ HP) _ _ _ H1 H2); subst c2
      end.
      match goal with
      | IH2 : forall _ _ _ _ _, run_cmds _ _ _ ?T (gs_push ?mp ?P nil) ?cs _ _ _ _ -> _,
        H2 : run_cmds _ _ _ ?T (gs_push ?mp ?P nil) ?cs _ _ _ _ |- _ =>
          destruct (IH2 _ _ _ _ _ H2) as (? & Heq & ? & ?); injection Heq; intros; subst
      end; repeat split; auto.
    - (* a member: its module's commands, then the rest from where they end *)
      match goal with H1 : ind_member ?D ?k = _, H2 : ind_member ?D ?k = _ |- _ => rewrite H1 in H2; injection H2 as <- end.
      match goal with
      | IH1 : forall _ _ _ _ _, run_cmds _ _ _ _ _ ?cs _ _ _ _ -> _, H1 : run_cmds _ _ _ _ _ ?cs _ _ _ _ |- _ =>
          destruct (IH1 _ _ _ _ _ H1) as (? & Heq & ? & ?); injection Heq as <- <- <-; subst
      end.
      match goal with
      | IH2 : forall _ _ _ _ _, run_ind_members _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _,
        H2 : run_ind_members _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          exact (IH2 _ _ _ _ _ H2)
      end.
  Qed.

  Corollary run_cmd_functional : forall ch ch' B Rb Θ Ξ c B1 Rb1 Θ1 Ξ1 B2 Rb2 Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch']⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2 -> Θ1 = Θ2 /\ Ξ1 = Ξ2 /\ B1 = B2 /\ Rb1 = Rb2.
  Proof. intros * H1 H2; exact (proj1 run_functional _ _ _ _ _ _ _ _ _ _ H1 _ _ _ _ _ H2). Qed.

  Corollary run_cmds_functional : forall ch ch' B Rb Θ Ξ cs B1 Rb1 Θ1 Ξ1 B2 Rb2 Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch']⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2 -> Θ1 = Θ2 /\ Ξ1 = Ξ2 /\ B1 = B2 /\ Rb1 = Rb2.
  Proof. intros * H1 H2; exact (proj1 (proj2 run_functional) _ _ _ _ _ _ _ _ _ _ H1 _ _ _ _ _ H2). Qed.

  Corollary run_unit_functional : forall ch ch' u B1 Rb1 Θ1 U1 B2 Rb2 Θ2 U2,
      hd nil ch = hd nil ch' -> run_unit ch u B1 Rb1 Θ1 U1 -> run_unit ch' u B2 Rb2 Θ2 U2 ->
      Θ1 = Θ2 /\ U1 = U2 /\ B1 = B2 /\ Rb1 = Rb2.
  Proof. intros * Hh H1 H2; exact (proj1 (proj2 (proj2 run_functional)) _ _ _ _ _ _ H1 _ _ _ _ _ Hh H2). Qed.
End Determinism.

(** ** Merging Keeps Both Sides *)

Lemma gds_lookup_merge : forall Θ Θ' fp,
    gds_lookup (gds_merge Θ Θ') fp = match gds_lookup Θ fp with Some U => Some U | None => gds_lookup Θ' fp end.
Proof.
  intros Θ Θ' fp; unfold gds_merge; induction Θ' as [| [fq V] Θ' IH]; cbn [filter List.app].
  - destruct (gds_lookup Θ fp); reflexivity.
  - unfold gds_mem at 1; cbn [fst]; destruct (gds_lookup Θ fq) eqn:Hq; cbn [negb]; rewrite ?IH.
    + cbn [gds_lookup]; destruct (gds_lookup Θ fp) eqn:Hp; [ reflexivity |].
      destruct (path_beq fp fq) eqn:Hb; [ apply path_beq_true in Hb; congruence | reflexivity ].
    + cbn [gds_lookup List.app]; rewrite IH.
      destruct (path_beq fp fq) eqn:Hb; [| reflexivity ].
      apply path_beq_true in Hb; subst; rewrite Hq; reflexivity.
Qed.

Lemma merge_cons : forall Θ fp U Θ',
    gds_merge Θ ((fp, U) :: Θ') = if gds_mem fp Θ then gds_merge Θ Θ' else (fp, U) :: gds_merge Θ Θ'.
Proof. intros; unfold gds_merge; cbn; destruct (gds_mem fp Θ); reflexivity. Qed.

Lemma merge_inv : forall Θ Θ' fp U,
    gds_lookup (gds_merge Θ Θ') fp = Some U ->
    gds_lookup Θ fp = Some U \/ gds_lookup Θ' fp = Some U.
Proof. intros * H; rewrite gds_lookup_merge in H; destruct (gds_lookup Θ fp); auto. Qed.

Lemma merge_none : forall Θ Θ' fp,
    gds_lookup (gds_merge Θ Θ') fp = None <-> gds_lookup Θ fp = None /\ gds_lookup Θ' fp = None.
Proof. intros; rewrite gds_lookup_merge; destruct (gds_lookup Θ fp); intuition discriminate. Qed.

Lemma merge_left : forall Θ Θ', Θ ⊑ gds_merge Θ Θ'.
Proof. intros * fp U HU; rewrite gds_lookup_merge, HU; reflexivity. Qed.

Lemma merge_right : forall Θ Θ', gds_agree Θ Θ' -> Θ' ⊑ gds_merge Θ Θ'.
Proof.
  intros * Hag fp U HU; rewrite gds_lookup_merge.
  destruct (gds_lookup Θ fp) eqn:E; [ f_equal; eapply Hag; eassumption | exact HU ].
Qed.

(** ** Filing More Units Keeps an Open Stack Well Formed

    Each entry of each frame was checked against the units filed when the frame
    was open; resolution only grows along [Θ ⊑ Θ'] ([gc_sub_deps]), so its
    typing moves along an embedding.  A frame names its own unit, which must
    stay unfiled: that is the only thing [Θ'] has to grant. *)

Lemma deps_grow : forall Θ Θ' Ξ,
    Θ ⊑ Θ' -> ⊢ Θ' ⍮ Ξ ⍮ ⋅ ->
    (forall Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ' ⍮ Ξ ⍮ Γ) /\
    (forall Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ' ⍮ Ξ ⍮ Γ ⊢ M : A) /\
    (forall Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> Θ' ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A) /\
    (forall Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> Θ' ⍮ Ξ ⍮ Γ ⊢ A ⊆ A') /\
    (forall Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ' ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ') /\
    (forall Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ' ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U') /\
    (forall Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ' ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H').
Proof.
  intros * Hs Hb; apply emb_preserves_wf; constructor;
    [ eapply ctx_wf_gctx; exact Hb | apply gc_sub_deps; exact Hs ].
Qed.

Lemma frame_fresh_grow : forall Θ Θ' Ξ mp,
    frame_fresh Θ Ξ mp -> gds_lookup Θ' (q_unit mp) = None -> frame_fresh Θ' Ξ mp.
Proof. intros * H Hn; destruct Ξ as [| [mq V] Ξ]; cbn in *; [ split; [ exact Hn | exact (proj2 H) ] | exact H ]. Qed.

(** An entry checked at its path in the innermost frame keeps the stack
    well formed. *)
Lemma add_entry_wf : forall Θ Ξ x E,
    ⊢ᵍ Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ qname_in (gs_path Ξ) x ⊢ᵉ E -> gs_fresh x Ξ ->
    ⊢ᵍ Θ ⍮ gs_add x E Ξ.
Proof.
  intros * HΞ HE Hfr.
  destruct Ξ as [| [[mp K] [P Φ1]] Ξ]; [ contradiction |]; cbn in Hfr, HE |- *.
  inversion HΞ as [| | ? ? ? ? ? ? Hs0 HΦ Hff]; subst.
  apply wf_gstack_cons; [ exact Hs0 | | exact Hff ].
  cbn; econstructor; [ eassumption | exact HE | exact Hfr ].
Qed.

Lemma add_ind_wf : forall Θ Ξ x pv pq k D Φ,
    ⊢ᵍ Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ qname_in (gs_path Ξ) x ⊢ᵉ ge_ind pv pq k D Φ -> gs_fresh x Ξ ->
    ⊢ᵍ Θ ⍮ gs_add x (ge_ind pv pq k D Φ) Ξ.
Proof. intros; apply add_entry_wf; assumption. Qed.

(** A member checked with an empty module has its group's own uniform
    parameters, over the frames', as assumptions of a well-formed context:
    those its module is opened over. *)
Lemma ind_nil_entry_uparams : forall Θ Ξ mp pv pq k D Δu,
    Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_ind pv pq k D ⋄ -> ind_uparams D = Δu ++ gs_tele Ξ ->
    tele_ass Δu /\ ⊢ Θ ⍮ Ξ ⍮ Δu ++ gs_tele Ξ.
Proof.
  intros * HE Hu.
  assert (Hass : tele_ass (ind_uparams D) -> tele_ass Δu) by (rewrite Hu; intros Ha; apply Forall_app in Ha; tauto).
  inversion HE; subst.
  - split; [ auto | rewrite <- Hu; assumption ].
  - split; [ auto | rewrite <- Hu; assumption ].
  - match goal with Hm : _ ⍮ _ ⍮ _ ⍮ fk_ind _ _ _ ⍮ _ ⊢ᵍᵐ ⋄, Hu' : ind_uparams D = ?Δ' ++ _ |- _ =>
      inversion Hm; subst; rewrite Hu in Hu'; apply app_inv_tail in Hu'; subst Δ' end.
    split; assumption.
Qed.

(** A record checked with an empty module has its own parameters, over the
    frames', as assumptions of a well-formed context: those its module is
    opened over, before its value. *)
Lemma record_nil_entry_params : forall Θ Ξ mp pv pr Δ Srt fs,
    Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_record pv pr (record_at Ξ Δ Srt fs) ⋄ ->
    tele_ass Δ /\ ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ.
Proof.
  intros * HE.
  assert (HP : record_params (record_at Ξ Δ Srt fs) = Δ ++ gs_tele Ξ) by reflexivity.
  inversion HE; subst.
  - split.
    + match goal with Ha : tele_ass (record_params _) |- _ => rewrite HP in Ha; apply Forall_app in Ha; tauto end.
    + match goal with HS : _ ⍮ _ ⍮ record_params _ ⊢ᵤ _ |- _ => rewrite HP in HS; exact (presup_is_univ_ctx HS) end.
  - match goal with Hm : _ ⍮ _ ⍮ _ ⍮ fk_record _ ⍮ _ ⊢ᵍᵐ ⋄ |- _ => inversion Hm; subst end.
    match goal with Hp : record_params _ = ?Δ' ++ _, Ha : tele_ass ?Δ', HC : ⊢ _ ⍮ _ ⍮ ?Δ' ++ _ |- _ =>
      rewrite HP in Hp; apply app_inv_tail in Hp; subst; split; assumption end.
Qed.

(** A later declared member of a group whose first member's entry is in
    the innermost frame is well formed with an empty module, where it is
    declared. *)
Lemma later_member_entry : forall Θ mq Kq Δ Φ Ξ0 y0 pv0 Φm D k Mk x pv Δu,
    ⊢ᵍ Θ ⍮ (mq, Kq, gu_body Δ Φ) :: Ξ0 ->
    gm_entry Φ (y0 :: nil) = Some (ge_ind pv0 (qname_in mq y0) 0 D Φm) ->
    ind_member D k = Some Mk -> 0 < k -> k < ind_ndecl D -> im_head Mk = mh_decl (qname_in mq x) ->
    ind_uparams D = Δu ++ gs_tele ((mq, Kq, gu_body Δ Φ) :: Ξ0) ->
    Θ ⍮ (mq, Kq, gu_body Δ Φ) :: Ξ0 ⍮ qname_in mq x ⊢ᵉ ge_ind pv (qname_in mq y0) k D ⋄.
Proof.
  intros * HΞ He HMk Hk Hlt Hh Hu.
  assert (Hl : ind_lookup Θ ((mq, Kq, gu_body Δ Φ) :: Ξ0) (qname_in mq y0) = Some D).
  { assert (HeE : gc_entry Θ ((mq, Kq, gu_body Δ Φ) :: Ξ0) (qname_in mq y0) = Some (ge_ind pv0 (qname_in mq y0) 0 D Φm))
      by (apply (proj2 (loc_entry _ _ HΞ mq (Δ ++ gs_tele Ξ0) Φ ltac:(left; unfold gc_frame; cbn; rewrite qname_strip_refl; reflexivity) _ _));
        exact He).
    rewrite ind_lookup_unfold, (proj2 (gc_entry_ind _ _ _ _ _ _ _ _ HeE)); reflexivity. }
  destruct (decl_of_lookup _ _ ⋅ _ _ (wf_ctx_empty _ _ HΞ) Hl) as [HD _].
  destruct (decl_typed_uparams _ _ _ HD) as [HU Hass].
  eapply wf_gentry_ind_mem_nil; eassumption.
Qed.

(** The name of an entry of a frame is fresh in the body before it. *)
Lemma wf_gstack_ext_fresh : forall Θ mq Kq Δ Φ0 y E Ξ0,
    ⊢ᵍ Θ ⍮ (mq, Kq, gu_body Δ (Φ0 ⊳ y ↦ E)) :: Ξ0 -> gm_fresh y Φ0.
Proof.
  intros * Hg; destruct (wf_gstack_cons_inv _ _ _ _ _ Hg) as (_ & HU & _).
  pose proof (wf_gunit_mod _ _ _ _ _ HU) as HΦ; cbn in HΦ; inversion HΦ; subst; assumption.
Qed.

Section GrowDeps.
  Variables (Θ Θ' : gdeps).
  Hypothesis Hsub : Θ ⊑ Θ'.

  Lemma global_deps_grow :
    (forall Θ0 Ξ mp E, Θ0 ⍮ Ξ ⍮ mp ⊢ᵉ E -> Θ0 = Θ -> ⊢ᵍ Θ' ⍮ Ξ ->
       gds_lookup Θ' (q_unit mp) = None -> Θ' ⍮ Ξ ⍮ mp ⊢ᵉ E) /\
    (forall Θ0 Ξ mp K Δ Φ, Θ0 ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> Θ0 = Θ -> ⊢ᵍ Θ' ⍮ Ξ ->
       gds_lookup Θ' (q_unit mp) = None -> Θ' ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ).
  Proof.
    apply global_wf_mut_ind; intros; subst.
    all: try assert (Hb : ⊢ Θ' ⍮ Ξ ⍮ ⋅) by (constructor; assumption).
    all: try pose proof (deps_grow _ _ _ Hsub Hb) as (Hc & He & Hq & Hst & Hx & _ & Hm).
    - econstructor; [ apply He; eassumption | intros; apply He; eauto ].
    - econstructor; auto.
    - econstructor; [ assumption | apply Hx; assumption | apply Hm; assumption ].
    - (* a group, before the members of its first member's module: a
         container found at [Θ'] is the one found at [Θ] *)
      assert (Hs : gc_sub Θ Ξ Θ' Ξ) by (apply gc_sub_deps; exact Hsub).
      match goal with |- _ ⍮ _ ⍮ _ ⊢ᵉ ge_ind _ _ _ ?D0 _ => assert (HD : decl_typed Θ Ξ D0) by build_decl_typed end.
      pose proof (decl_typed_container _ _ _ _ _ Hs HD) as Hcont.
      econstructor; try eassumption;
        [ .. | exact (view_maps_coherent_gc_sub _ _ _ _ _ Hcont (dt_view_maps_coherent _ _ _ HD)) ].
      all: intros;
        repeat match goal with
        | Hk : ind_member ?D0 ?k = Some ?Mk, Hh : im_head ?Mk = mh_view ?qc _ _ _, Hl : ind_lookup _ _ ?qc = Some _ |- _ =>
            apply (Hcont _ _ _ _ _ _ _ Hk Hh) in Hl
        end.
      all: try solve [ first [ apply Hc | apply He | apply Hq | apply Hst | apply Hx ]; eauto ].
      all: try solve [ match goal with Hp : _ |- _ => eapply Hp; eassumption end ].
      (* the rank, at the containers found at [Θ'] *)
      all: try solve [ match goal with
        | Hrk : exists rk, view_rank_ok _ _ ?D0 rk |- exists rk, view_rank_ok _ _ ?D0 rk =>
            destruct Hrk as [rk [Hr0 Hr1]]; exists rk; constructor; [ exact Hr0 |];
            intros * Hk Hh Hl; pose proof (Hcont _ _ _ _ _ _ _ Hk Hh Hl); intros; eapply Hr1; eassumption
        end ].
      (* the views' members, at the containers found at [Θ'] *)
      all: try solve [ match goal with
        | Hvw : forall k Mk qc k' Is vm, ind_member ?D0 k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
                  exists D', ind_lookup _ _ qc = Some D' /\ vwrap_ok ?D0 D' vm,
          Hk : ind_member ?D0 _ = Some _, Hh : im_head _ = mh_view _ _ _ _ |- exists D', _ /\ vwrap_ok _ _ _ =>
            destruct (Hvw _ _ _ _ _ _ Hk Hh) as (D' & Hl & Hw);
            exists D'; split; [ exact (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hl) | exact Hw ]
        end ].
      (* the container of a view *)
      match goal with
      | Hv : forall k Mk qc k' Is vm, ind_member ?D0 k = Some Mk -> im_head Mk = mh_view qc k' Is vm -> exists D' Mk', _,
        Hk : ind_member ?D0 _ = Some _, Hh : im_head _ = mh_view _ _ _ _ |- _ =>
          destruct (Hv _ _ _ _ _ _ Hk Hh) as (D' & Mk' & Hl & Hrest);
          exists D', Mk'; split; [ exact (ind_lookup_gc_sub _ _ _ _ _ _ Hs Hl) | exact Hrest ]
      end.
    - (* a later declared member of a group *)
      match goal with Hg : ⊢ᵍ Θ' ⍮ ?X |- _ => pose proof (deps_grow _ _ _ Hsub (wf_ctx_empty _ _ Hg)) as (Hc' & _) end.
      eapply wf_gentry_ind_mem_nil; try eassumption;
        first [ apply Hc'; eassumption | eapply ind_lookup_gc_sub; [ apply gc_sub_deps; exact Hsub | eassumption ] ].
    - (* a member with the body of its module, an ordinary module *)
      econstructor; [ eassumption | auto ].
    - (* an inductive alias *)
      eapply wf_gentry_ind_alias; try eassumption;
        first [ apply Hx; assumption | apply He; assumption | apply Hm; assumption
              | eapply ind_lookup_gc_sub; [ apply gc_sub_deps; exact Hsub | eassumption ]
              | eapply ind_mlookup_gc_sub; [ apply gc_sub_deps; exact Hsub | eassumption ] ].
    - (* a record *)
      econstructor; try eassumption; [| intros; apply He; eauto ].
      match goal with Hu : wf_is_univ _ _ _ _ |- _ =>
        inversion Hu; subst; [ constructor; apply Hc; assumption | econstructor; apply He; eassumption ] end.
    - (* a record with the body of its module, an ordinary module *)
      econstructor; [ eassumption | auto ].
    - econstructor; [ assumption | apply Hc; assumption ].
    - (* the module of a member, before its first entry *)
      match goal with Hg : ⊢ᵍ Θ' ⍮ ?X |- _ => pose proof (deps_grow _ _ _ Hsub (wf_ctx_empty _ _ Hg)) as (Hc' & _) end.
      eapply wf_gmod_ind_nil; [ assumption | apply Hc'; assumption | auto | assumption ].
    - (* the module of a record, before its first entry *)
      match goal with Hg : ⊢ᵍ Θ' ⍮ ?X |- _ => pose proof (deps_grow _ _ _ Hsub (wf_ctx_empty _ _ Hg)) as (Hc' & _) end.
      eapply wf_gmod_record_nil; [ assumption | apply Hc'; assumption | auto | assumption ].
    - match goal with HE : Θ ⍮ _ ⍮ qname_in _ _ ⊢ᵉ _ |- _ => pose proof (wf_gentry_gctx _ _ _ _ HE) as Hg0 end.
      destruct (wf_gstack_cons_inv _ _ _ _ _ Hg0) as (_ & _ & Hff).
      assert (HΦ : Θ' ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ) by auto.
      econstructor; [ exact HΦ | | assumption ].
      match goal with IH : _ = _ -> ⊢ᵍ _ ⍮ (mp, K, gu_body Δ Φ) :: Ξ -> _ |- _ => apply IH end;
        [ reflexivity | | assumption ].
      apply wf_gstack_cons; [ assumption | exact HΦ | eapply frame_fresh_grow; eassumption ].
  Qed.

  Lemma gstack_deps_grow : forall Ξ, ⊢ᵍ Θ ⍮ Ξ -> ⊢ᵍ Θ' ⍮ nil ->
      (forall mp K U, In (mp, K, U) Ξ -> gds_lookup Θ' (q_unit mp) = None) -> ⊢ᵍ Θ' ⍮ Ξ.
  Proof.
    induction Ξ as [| [[mp K] U] Ξ IH]; intros HΞ HΘ' Hfr; [ exact HΘ' |].
    destruct (wf_gstack_cons_inv _ _ _ _ _ HΞ) as (HΞ0 & HU & Hff).
    assert (HΞ' : ⊢ᵍ Θ' ⍮ Ξ) by (apply IH; [ assumption | assumption | intros; eapply Hfr; right; eassumption ]).
    pose proof (Hfr mp K U (or_introl eq_refl)) as Hn.
    destruct HU as [Δ Φ -> HΦ].
    apply wf_gstack_cons; [ exact HΞ' | | eapply frame_fresh_grow; eassumption ].
    eapply (proj2 global_deps_grow); eauto.
  Qed.

  (** A filed unit, which sees no frame but its own, named by its path: that
      path must stay unfiled. *)
  Lemma unit_deps_grow : forall fp U,
      ⊢ᵍ Θ' ⍮ nil -> gds_lookup Θ' fp = None ->
      Θ ⍮ nil ⍮ q_abs fp nil ⍮ fk_module ⊢ᵍᵘ U -> Θ' ⍮ nil ⍮ q_abs fp nil ⍮ fk_module ⊢ᵍᵘ U.
  Proof.
    intros * HΘ' Hn [Δ Φ -> HΦ]; apply wf_gunit_intro.
    eapply (proj2 global_deps_grow); [ eassumption | reflexivity | exact HΘ' | exact Hn ].
  Qed.
End GrowDeps.

(** ** Merging Keeps Well-formedness

    A unit of the right side was checked against the units below it there,
    which the merge extends; the sides agree, so the merge has them as they
    are. *)

Theorem merge_wf : forall Θ Θ',
    ⊢ᵍ Θ ⍮ nil -> ⊢ᵍ Θ' ⍮ nil -> gds_agree Θ Θ' -> ⊢ᵍ gds_merge Θ Θ' ⍮ nil.
Proof.
  intros Θ Θ' HΘ; induction Θ' as [| [fp U] Θ' IH]; intros HΘ' Hag; [ exact HΘ |].
  destruct (wf_gstack_file_inv _ _ _ HΘ') as (HΘ0 & HU & Hn).
  assert (Hag0 : gds_agree Θ Θ').
  { intros fq V V' H1 H2; apply (Hag fq V V' H1); cbn.
    destruct (path_beq fq fp) eqn:Hb; [ apply path_beq_true in Hb; subst; congruence | exact H2 ]. }
  assert (HM : ⊢ᵍ gds_merge Θ Θ' ⍮ nil) by auto.
  rewrite merge_cons; unfold gds_mem; destruct (gds_lookup Θ fp) eqn:Hf; [ exact HM |].
  assert (HnM : gds_lookup (gds_merge Θ Θ') fp = None) by (apply merge_none; split; assumption).
  apply wf_gstack_file'; [ exact HM | | exact HnM ].
  eapply unit_deps_grow; [ apply merge_right, Hag0 | exact HM | exact HnM | exact HU ].
Qed.

(** ** Running Keeps the State Well Formed

    The state stays canonical, not only well formed: that is what makes a
    loaded unit agree with what is filed already, so the merge is well formed.
    Loading files the derivation of the unit it ran, hence the dependent
    scheme. *)

Scheme run_cmd_dind := Induction for run_cmd Sort Prop
with run_cmds_dind := Induction for run_cmds Sort Prop
with run_unit_dind := Induction for run_unit Sort Prop
with run_ind_members_dind := Induction for run_ind_members Sort Prop.
Combined Scheme run_mut_dind from run_cmd_dind, run_cmds_dind, run_unit_dind, run_ind_members_dind.

(** What a run keeps of a stack: each frame's path, kind and parameters. *)
Definition gs_shape (Ξ : gstack) : list (qname * frame_kind * ctx) := map (fun f => (fst f, gu_params (snd f))) Ξ.

Lemma gs_add_params : forall x E Ξ, gs_shape (gs_add x E Ξ) = gs_shape Ξ.
Proof. intros ? ? [| [[? ?] ?] ?]; reflexivity. Qed.

Lemma gs_tele_add : forall x E Ξ, gs_tele (gs_add x E Ξ) = gs_tele Ξ.
Proof. intros ? ? [| [[? ?] ?] ?]; reflexivity. Qed.

(** A name is fresh in a frame with an entry added iff it is fresh in it
    and not the entry's. *)
Lemma gs_fresh_add_inv : forall y x E Ξ, gs_fresh y (gs_add x E Ξ) -> gs_fresh y Ξ /\ y <> x.
Proof.
  intros * H; destruct Ξ as [| [[mp K] U] Ξ']; [ contradiction |]; cbn in H |- *.
  destruct U as [Δ [sm Φ | E0]]; cbn in H |- *; unfold gm_fresh in *; cbn [gm_names In] in H |- *;
    split; intros Hy; apply H; auto.
Qed.

Lemma gs_fresh_add : forall y x E Ξ, gs_fresh y Ξ -> y <> x -> gs_fresh y (gs_add x E Ξ).
Proof.
  intros * H Hn; destruct Ξ as [| [[mp K] U] Ξ']; [ contradiction |]; cbn in H |- *.
  destruct U as [Δ [sm Φ | E0]]; cbn in H |- *; unfold gm_fresh in *; cbn [gm_names In];
    (intros [Hy | Hy]; [ exact (Hn (eq_sym Hy)) | exact (H Hy) ]).
Qed.

Lemma gs_path_add : forall x E Ξ, gs_path (gs_add x E Ξ) = gs_path Ξ.
Proof. intros ? ? [| [[? ?] ?] ?]; reflexivity. Qed.

(** A filed group's uniform parameters are its own, over the frames'. *)
Lemma rd_filed_uparams : forall Θ Ξ R Vs Ss csD csV Nvs D,
    rd_filed Θ Ξ R Vs Ss csD csV Nvs = Some D -> ind_uparams D = rd_uparams R ++ gs_tele Ξ.
Proof.
  intros * Hf; unfold rd_filed in Hf; destruct (rd_members R) as [| Mr0 ?]; [ discriminate |].
  repeat match type of Hf with context [match ?e with _ => _ end] => destruct e end; try discriminate.
  injection Hf as <-; reflexivity.
Qed.

(** The declared members of a filed group are its first ones, each named
    after its raw member ([rms_filed]); the views after them. *)
Lemma rms_filed_heads : forall Ξ n Vs ms css Ms, rms_filed Ξ n Vs ms css = Some Ms ->
    List.length Ms = List.length ms /\
    forall i M, List.nth_error Ms i = Some M ->
      exists Mr, List.nth_error ms i = Some Mr /\ im_head M = mh_decl (ind_qname Ξ (rm_name Mr)).
Proof.
  induction ms as [| Mr ms IH]; intros [| cs css] Ms H; cbn in H; try discriminate.
  - injection H as <-; split; [ reflexivity | intros [] ? [=] ].
  - destruct (rcons_num n Vs cs) as [cs' |]; [| discriminate ].
    destruct (rms_filed Ξ n Vs ms css) as [Ms' |] eqn:E; [| discriminate ].
    injection H as <-; destruct (IH _ _ E) as [Hl Hh].
    split; [ cbn; rewrite Hl; reflexivity |].
    intros [| i] M HM; cbn in HM; [ injection HM as <-; exists Mr; split; reflexivity | exact (Hh _ _ HM) ].
Qed.

(** The members a group's views are filed as are not declared ones. *)
Lemma rvs_filed_views : forall Θ Ξ σ n Vs xs Ss css Nvs Ms, rvs_filed Θ Ξ σ n Vs xs Ss css Nvs = Some Ms ->
    forall M, In M Ms -> im_is_decl M = false.
Proof.
  induction xs as [| x xs IH]; intros [| ss Ss] [| cs css] [| Nv Nvs] Ms H; cbn in H; try discriminate.
  - injection H as <-; intros M [].
  - destruct (rv_filed Θ Ξ σ n Vs x ss cs Nv) as [M0 |] eqn:E0; [| discriminate ].
    destruct (rvs_filed Θ Ξ σ n Vs xs Ss css Nvs) as [Ms' |] eqn:E; [| discriminate ].
    injection H as <-; intros M [<- | HM]; [| exact (IH _ _ _ _ E _ HM) ].
    unfold rv_filed in E0; destruct x as [[qc k] Cs].
    destruct (ind_lookup Θ Ξ qc) as [D' |]; [| discriminate ].
    destruct (ind_member D' k), (rcons_num n Vs cs); try discriminate.
    injection E0 as <-; reflexivity.
Qed.

(** Filtering keeps a list all of whose elements pass, and empties one
    none of whose elements does. *)
Lemma filter_all_true : forall {X} (f : X -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof. induction l as [| x l IH]; intros H; cbn; [ reflexivity |]; rewrite (H x (or_introl eq_refl)), IH; auto with datatypes. Qed.

Lemma filter_all_false : forall {X} (f : X -> bool) l, (forall x, In x l -> f x = false) -> List.filter f l = nil.
Proof. induction l as [| x l IH]; intros H; cbn; [ reflexivity |]; rewrite (H x (or_introl eq_refl)), IH; auto with datatypes. Qed.

(** A filed group declares as many members as are written, each at its
    position, named after its raw member. *)
Lemma rd_filed_decl : forall Θ Ξ R Vs Ss csD csV Nvs D, rd_filed Θ Ξ R Vs Ss csD csV Nvs = Some D ->
    ind_ndecl D = List.length (rd_members R) /\
    forall i Mr, List.nth_error (rd_members R) i = Some Mr ->
      exists M, ind_member D i = Some M /\ im_head M = mh_decl (ind_qname Ξ (rm_name Mr)).
Proof.
  intros * H; unfold rd_filed in H; destruct (rd_members R) as [| Mr0 Mrs] eqn:HR; [ discriminate |].
  destruct (rms_filed _ _ _ _ _) as [Ms |] eqn:E1; [| discriminate ].
  destruct (rvs_filed _ _ _ _ _ _ _ _ _) as [Mv |] eqn:E2; [| discriminate ].
  injection H as <-; destruct (rms_filed_heads _ _ _ _ _ _ E1) as [Hl Hh].
  pose proof (rvs_filed_views _ _ _ _ _ _ _ _ _ _ E2) as Hv.
  split.
  - unfold ind_ndecl; cbn [ind_members]; rewrite List.filter_app, (filter_all_false _ Mv Hv), List.app_nil_r.
    rewrite filter_all_true; [ exact Hl |].
    intros M HM; destruct (List.In_nth_error _ _ HM) as [i Hi].
    destruct (Hh _ _ Hi) as (Mr & _ & Hhd); unfold im_is_decl; rewrite Hhd; reflexivity.
  - intros i Mr Hi.
    assert (Hlt : i < List.length Ms) by (rewrite Hl; apply List.nth_error_Some; congruence).
    destruct (List.nth_error Ms i) as [M |] eqn:HM; [| apply List.nth_error_None in HM; exfalso; exact (Nat.lt_irrefl _ (Nat.lt_le_trans _ _ _ Hlt HM)) ].
    destruct (Hh _ _ HM) as (Mr' & Hi' & Hhd); rewrite Hi in Hi'; injection Hi' as <-.
    exists M; split; [ unfold ind_member; cbn [ind_members]; rewrite List.nth_error_app1 by exact Hlt; exact HM | exact Hhd ].
Qed.

(** The frames of a stack belong to units on the chain: the ones being
    loaded, so none a load files. *)
Definition stack_in (ch : list path) (Ξ : gstack) : Prop :=
  forall mp K U, In (mp, K, U) Ξ -> In (q_unit mp) ch.

Lemma stack_in_add : forall ch x E Ξ, stack_in ch Ξ -> stack_in ch (gs_add x E Ξ).
Proof.
  intros * H mp K U Hin; destruct Ξ as [| [[mq Kq] V] Ξ]; [ contradiction |].
  destruct Hin as [[= <- <- <-] | Hin]; [ eapply H; left; reflexivity | eapply H; right; exact Hin ].
Qed.

Lemma stack_in_push : forall ch x Δ Ξ,
    stack_in ch Ξ -> gs_fresh x Ξ -> stack_in ch (gs_push (qname_in (gs_path Ξ) x) Δ Ξ).
Proof.
  intros * H Hfr mp K U [[= <- <- <-] | Hin]; [| eapply H; exact Hin ].
  destruct Ξ as [| [[mq Kq] V] Ξ]; [ contradiction |]; cbn; eapply H; left; reflexivity.
Qed.

(** Likewise the frame of the module of a member. *)
Lemma stack_in_push_ind : forall ch x pq k D Δ Ξ,
    stack_in ch Ξ -> gs_fresh x Ξ -> stack_in ch (gs_push_ind (qname_in (gs_path Ξ) x) pq k D Δ Ξ).
Proof.
  intros * H Hfr mp K U [[= <- <- <-] | Hin]; [| eapply H; exact Hin ].
  destruct Ξ as [| [[mq Kq] V] Ξ]; [ contradiction |]; cbn; eapply H; left; reflexivity.
Qed.

Lemma stack_in_push_record : forall ch x R Δ Ξ,
    stack_in ch Ξ -> gs_fresh x Ξ -> stack_in ch (gs_push_record (qname_in (gs_path Ξ) x) R Δ Ξ).
Proof.
  intros * H Hfr mp K U [[= <- <- <-] | Hin]; [| eapply H; exact Hin ].
  destruct Ξ as [| [[mq Kq] V] Ξ]; [ contradiction |]; cbn; eapply H; left; reflexivity.
Qed.

(** A definition or an alias, checked against the frame so far, keeps the
    stack well formed. *)
Lemma add_def_wf : forall Θ Ξ x b pv A M,
    ⊢ᵍ Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A -> gs_fresh x Ξ -> ⊢ᵍ Θ ⍮ gs_add x (gs_def b pv Ξ A M) Ξ.
Proof.
  intros * HΞ HM Hfr.
  destruct Ξ as [| [[mp K] [P Φ]] Ξ]; [ contradiction |]; cbn in Hfr |- *.
  inversion HΞ as [| | ? ? ? ? ? ? Hs0 HΦ Hff]; subst.
  apply wf_gstack_cons; [ exact Hs0 | | exact Hff ].
  destruct (presup_exp_typ HM) as [i HA].
  cbn; econstructor; [ eassumption | unfold gs_def; eapply wf_gentry_def_body; [ exact HA | exact HM ] | exact Hfr ].
Qed.

Lemma add_axiom_wf : forall Θ Ξ x b pv A i,
    ⊢ᵍ Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i -> gs_fresh x Ξ -> ⊢ᵍ Θ ⍮ gs_add x (gs_axiom b pv Ξ A) Ξ.
Proof.
  intros * HΞ HA Hfr.
  destruct Ξ as [| [[mp K] [P Φ]] Ξ]; [ contradiction |]; cbn in Hfr |- *.
  inversion HΞ as [| | ? ? ? ? ? ? Hs0 HΦ Hff]; subst.
  apply wf_gstack_cons; [ exact Hs0 | | exact Hff ].
  cbn; econstructor; [ eassumption | unfold gs_axiom; eapply wf_gentry_def_axiom; exact HA | exact Hfr ].
Qed.

Lemma add_alias_wf : forall Θ Ξ x pv Δ E,
    ⊢ᵍ Θ ⍮ Ξ -> tele_ass Δ -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ -> Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
    gs_fresh x Ξ -> ⊢ᵍ Θ ⍮ gs_add x (ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E))) Ξ.
Proof.
  intros * HΞ Htel HΔ HE Hfr.
  destruct Ξ as [| [[mp K] [P Φ]] Ξ]; [ contradiction |]; cbn in Hfr |- *.
  inversion HΞ as [| | ? ? ? ? ? ? Hs0 HΦ Hff]; subst.
  apply wf_gstack_cons; [ exact Hs0 | | exact Hff ].
  cbn; econstructor; [ eassumption | constructor; assumption | exact Hfr ].
Qed.



Lemma gens_run_wf : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> ⊢ᵍ Θ ⍮ Ξ -> ⊢ᵍ Θ ⍮ Ξ'.
Proof.
  induction 1; intros HΞ; [ exact HΞ | apply IHgens_run; apply add_def_wf; assumption | |].
  - apply IHgens_run; apply (add_alias_wf _ _ _ _ nil); try assumption; [ constructor |].
    constructor; exact (presup_modexp_eq_ctx H).
  - apply IHgens_run; apply add_entry_wf; assumption.
Qed.

Lemma gens_run_shape : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> gs_shape Ξ' = gs_shape Ξ.
Proof. induction 1; rewrite ?IHgens_run, ?gs_add_params; reflexivity. Qed.

Lemma gens_run_tl : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> tl Ξ' = tl Ξ /\ List.length Ξ' = List.length Ξ.
Proof.
  assert (Hadd : forall x E Ξ, tl (gs_add x E Ξ) = tl Ξ /\ List.length (gs_add x E Ξ) = List.length Ξ)
    by (intros ? ? [| [[? ?] ?] ?]; split; reflexivity).
  induction 1; [ auto | .. ]; destruct IHgens_run as [Ht Hl]; rewrite Ht, Hl; apply Hadd.
Qed.

(** ** Inductive Types Stay Where They Are Declared

    An entry added to the innermost frame, and a closed module frame filed
    as a member of the frame below it, keep every inductive type that could
    be read before. *)

Lemma ind_lookup_add : forall Θ Ξ x E p D,
    ⊢ᵍ Θ ⍮ Ξ -> gs_fresh x Ξ -> ind_lookup Θ Ξ p = Some D -> ind_lookup Θ (gs_add x E Ξ) p = Some D.
Proof.
  intros * HΞ Hfr Hl.
  destruct Ξ as [| [[mq Kq] U] Ξ0]; [ contradiction |].
  destruct (wf_gstack_cons_inv _ _ _ _ _ HΞ) as (_ & [P Ψ -> _] & _).
  cbn in Hfr |- *.
  eapply ind_lookup_gc_sub; [ apply gc_sub_grow; exact Hfr | exact Hl ].
Qed.

Lemma gens_run_ind_lookup : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> ⊢ᵍ Θ ⍮ Ξ ->
    forall p D, ind_lookup Θ Ξ p = Some D -> ind_lookup Θ Ξ' p = Some D.
Proof.
  induction 1; intros HΞ p0 D0 Hl; [ exact Hl | .. ]; apply IHgens_run; try (apply ind_lookup_add; assumption).
  - apply add_def_wf; assumption.
  - apply (add_alias_wf _ _ _ _ nil); try assumption; [ constructor |].
    constructor; exact (presup_modexp_eq_ctx H).
  - apply add_entry_wf; assumption.
Qed.

(** The definitions of a mutual definition, filed in order, likewise. *)
Lemma mdefs_run_wf : forall Θ b pv ds Ξ Ξ', mdefs_run Θ b pv ds Ξ Ξ' -> ⊢ᵍ Θ ⍮ Ξ -> ⊢ᵍ Θ ⍮ Ξ'.
Proof. induction 1; intros HΞ; [ exact HΞ | apply IHmdefs_run; apply add_def_wf; assumption ]. Qed.

Lemma mdefs_run_shape : forall Θ b pv ds Ξ Ξ', mdefs_run Θ b pv ds Ξ Ξ' -> gs_shape Ξ' = gs_shape Ξ.
Proof. induction 1; rewrite ?IHmdefs_run, ?gs_add_params; reflexivity. Qed.

Lemma mdefs_run_tl : forall Θ b pv ds Ξ Ξ', mdefs_run Θ b pv ds Ξ Ξ' -> tl Ξ' = tl Ξ /\ List.length Ξ' = List.length Ξ.
Proof.
  assert (Hadd : forall x E Ξ, tl (gs_add x E Ξ) = tl Ξ /\ List.length (gs_add x E Ξ) = List.length Ξ)
    by (intros ? ? [| [[? ?] ?] ?]; split; reflexivity).
  induction 1; [ auto | .. ]; destruct IHmdefs_run as [Ht Hl]; rewrite Ht, Hl; apply Hadd.
Qed.

Lemma mdefs_run_ind_lookup : forall Θ b pv ds Ξ Ξ', mdefs_run Θ b pv ds Ξ Ξ' -> ⊢ᵍ Θ ⍮ Ξ ->
    forall p D0, ind_lookup Θ Ξ p = Some D0 -> ind_lookup Θ Ξ' p = Some D0.
Proof.
  induction 1; intros HΞ p0 D0 Hl; [ exact Hl |]; apply IHmdefs_run; [ apply add_def_wf; assumption |].
  apply ind_lookup_add; assumption.
Qed.

(** A frame, of either kind, closed into the member it becomes: what was
    read in it is read in that member. *)
Lemma gc_sub_close : forall Θ Ξ x pv K Δ Φ,
    ⊢ᵍ Θ ⍮ Ξ -> gs_fresh x Ξ -> kind_tele (qname_in (gs_path Ξ) x) K Δ (gs_tele Ξ) ->
    gc_sub Θ ((qname_in (gs_path Ξ) x, K, gu_body Δ Φ) :: Ξ) Θ
      (gs_add x (frame_entry pv (qname_in (gs_path Ξ) x) K Δ Φ) Ξ).
Proof.
  intros * HΞ Hfr HK.
  destruct Ξ as [| [[mq Kq] U] Ξ0]; [ contradiction |].
  destruct (wf_gstack_cons_inv _ _ _ _ _ HΞ) as (_ & [P Ψ -> _] & _).
  cbn [gs_path gs_add gu_params gu_mod gs_fresh] in Hfr |- *.
  apply (gc_sub_nested _ _ _ pv); [ apply gc_sub_grow; exact Hfr | | exact HK ].
  exact (Ctb_frame Θ mq Kq P Ψ x _ Ξ0 _ _ (gc_sub_refl _ _)).
Qed.

Lemma ind_lookup_close : forall Θ Ξ x pv K Δ Φ p D,
    ⊢ᵍ Θ ⍮ Ξ -> gs_fresh x Ξ -> kind_tele (qname_in (gs_path Ξ) x) K Δ (gs_tele Ξ) ->
    ind_lookup Θ ((qname_in (gs_path Ξ) x, K, gu_body Δ Φ) :: Ξ) p = Some D ->
    ind_lookup Θ (gs_add x (frame_entry pv (qname_in (gs_path Ξ) x) K Δ Φ) Ξ) p = Some D.
Proof. intros * HΞ Hfr HK Hl; exact (ind_lookup_gc_sub _ _ _ _ _ _ (gc_sub_close _ _ _ pv _ _ Φ HΞ Hfr HK) Hl). Qed.

(** Read under frames of units not filed: as filed. *)
Lemma ind_lookup_below : forall Θ Ξ p D,
    (forall mp K U, In (mp, K, U) Ξ -> gds_lookup Θ (q_unit mp) = None) ->
    ind_lookup Θ nil p = Some D -> ind_lookup Θ Ξ p = Some D.
Proof.
  intros * Hfr Hl.
  (* no frame of [Ξ] is at a path of a filed unit *)
  assert (Hno : forall U ip, gs_find Ξ p = Some (U, ip) -> False).
  { intros U ip Hg; destruct (gs_find_unit _ _ _ _ Hg) as (mp & K & Hin & Hu).
    unfold ind_lookup, ind_lookup_u, ind_mlookup_u, gc_module, gc_module_u in Hl; cbn [gs_find_ind gs_find_tele] in Hl.
    rewrite <- Hu, (Hfr _ _ _ Hin) in Hl; discriminate. }
  unfold ind_lookup, ind_lookup_u, ind_mlookup_u, gc_module, gc_module_u in *; cbn [gs_find_ind gs_find_tele] in Hl.
  destruct (gs_find_ind Ξ p) as [r |] eqn:Hk.
  - exfalso; destruct (gs_find_ind_tele _ _ _ Hk) as (U & T & Hf).
    apply (Hno U nil); rewrite gs_find_tele_find, Hf; reflexivity.
  - destruct (gs_find_tele Ξ p) as [[[U ip] T] |] eqn:Hf; [| exact Hl ].
    exfalso; apply (Hno U ip); rewrite gs_find_tele_find, Hf; reflexivity.
Qed.

(** A binding well formed at one state is at another that reads every
    inductive type the first does. *)
Lemma builtins_wf_mono : forall Θ Ξ Θ' Ξ' B,
    (forall p D, ind_lookup Θ Ξ p = Some D -> ind_lookup Θ' Ξ' p = Some D) ->
    builtins_wf Θ Ξ B -> builtins_wf Θ' Ξ' B.
Proof. intros * Hm Hb p Hp; destruct (Hb p Hp) as [D z s Hl Hs Ho]; exact (mk_nat_binding_ok _ _ _ D z s (Hm _ _ Hl) Hs Ho). Qed.

(** A record read under no frame is read under frames of units not filed. *)
Lemma builtins_wf_below : forall Θ Ξ B,
    (forall mp K U, In (mp, K, U) Ξ -> gds_lookup Θ (q_unit mp) = None) ->
    builtins_wf Θ nil B -> builtins_wf Θ Ξ B.
Proof. intros * Hfr; apply builtins_wf_mono; intros; apply ind_lookup_below; assumption. Qed.

(** The records of filed units, each read where the units are filed. *)
Definition bm_wf (Θ : gdeps) (Rb : bmap) : Prop :=
  forall fp BU, bm_lookup Rb fp = Some BU -> builtins_wf Θ nil BU.

Lemma bm_wf_sub : forall Θ Θ' Rb, Θ ⊑ Θ' -> bm_wf Θ Rb -> bm_wf Θ' Rb.
Proof.
  intros * Hs HR fp BU HB; eapply builtins_wf_mono; [| exact (HR _ _ HB) ].
  intros; eapply ind_lookup_gc_sub; [ apply gc_sub_deps; exact Hs | eassumption ].
Qed.

(** The group a declared member's entry files, at its path. *)
Lemma ind_lookup_added : forall Θ Ξ x pv D Φ,
    Ξ <> nil -> ind_lookup Θ (gs_add x (ge_ind pv (qname_in (gs_path Ξ) x) 0 D Φ) Ξ) (qname_in (gs_path Ξ) x) = Some D.
Proof.
  intros * Hn; destruct Ξ as [| [[mp K] U] Ξ0]; [ contradiction |].
  rewrite ind_lookup_unfold, ind_mlookup_unfold; cbn [gs_add gs_path].
  change (qname_in mp x) with (qname_app mp (x :: nil)).
  cbn [gs_find_ind]; rewrite qname_strip_app.
  rewrite gc_module_frame_here; cbn; rewrite String.eqb_refl; reflexivity.
Qed.

Section WellFormed.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).
  #[local] Abbreviation run_ind_members := (run_ind_members load_path read to_core).

  Lemma run_chain_fresh :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall fq, In fq ch -> gds_lookup Θ fq = None -> gds_lookup Θ' fq = None) /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall fq, In fq ch -> gds_lookup Θ fq = None -> gds_lookup Θ' fq = None) /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U -> forall fq, In fq ch -> gds_lookup Θ fq = None) /\
    (forall ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ', run_ind_members ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ' ->
       forall fq, In fq ch -> gds_lookup Θ fq = None -> gds_lookup Θ' fq = None).
  Proof.
    apply run_mut_ind; intros; eauto.
    - (* a load files what its unit filed, and the unit, which is not on the chain *)
      destruct (gds_lookup (gds_merge _ _) fq) eqn:Ef; [ exfalso | reflexivity ].
      apply merge_inv in Ef as [Ef | Ef]; [ congruence |].
      cbn in Ef; destruct (path_beq fq fp) eqn:Hb.
      + apply path_beq_true in Hb; subst; contradiction.
      + match goal with IH : forall _, In _ (fp :: ch) -> _ |- _ => rewrite (IH fq ltac:(right; assumption)) in Ef end.
        discriminate.
  Qed.

  (** A run keeps the parameters of every frame. *)
  Lemma run_params :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> gs_shape Ξ' = gs_shape Ξ) /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> gs_shape Ξ' = gs_shape Ξ) /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U -> True) /\
    (forall ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ', run_ind_members ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ' ->
       gs_shape Ξ' = gs_shape Ξ).
  Proof.
    apply run_mut_ind; intros; rewrite ?gs_add_params in *;
      solve [ congruence | exact I | eapply gens_run_shape; eassumption
            | eapply mdefs_run_shape; eassumption
            | erewrite gens_run_shape by eassumption; apply gs_add_params ].
  Qed.

  (** A filed unit is what loading its file yields, and its record in [Rb]
      the record that run ends with; [Rb] records only filed units. *)
  #[warnings="-cannot-define-projection"]
  Record canon_entry (Rb : bmap) (fp : path) (U : gunit) : Prop := mk_canon_entry
    { cn_record : builtins
    ; cn_src : string
    ; cn_prog : Cst.prog
    ; cn_unit : cunit
    ; cn_chain : list path
    ; cn_rb : bmap
    ; cn_deps : gdeps
    ; cn_lookup : bm_lookup Rb fp = Some cn_record
    ; cn_load : load_path fp = Some cn_src
    ; cn_read : read cn_src = Some cn_prog
    ; cn_core : to_core cn_prog = Some cn_unit
    ; cn_run : run_unit (fp :: cn_chain) cn_unit cn_record cn_rb cn_deps U }.

  Definition canon (Rb : bmap) (Θ : gdeps) : Prop :=
    (forall fp U, gds_lookup Θ fp = Some U -> canon_entry Rb fp U) /\
    (forall fp BU, bm_lookup Rb fp = Some BU -> gds_lookup Θ fp <> None).

  Definition bm_agree (Rb Rb' : bmap) : Prop :=
    forall fp B B', bm_lookup Rb fp = Some B -> bm_lookup Rb' fp = Some B' -> B = B'.

  (** Two runs of the same file give the same unit and the same record. *)
  Lemma canon_agree : forall Rb1 Θ1 Rb2 Θ2, canon Rb1 Θ1 -> canon Rb2 Θ2 -> gds_agree Θ1 Θ2 /\ bm_agree Rb1 Rb2.
  Proof.
    intros * [H1 H1'] [H2 H2'].
    assert (Hrun : forall fp U1 U2, gds_lookup Θ1 fp = Some U1 -> gds_lookup Θ2 fp = Some U2 ->
                     U1 = U2 /\ bm_lookup Rb1 fp = bm_lookup Rb2 fp).
    { intros fp U1 U2 E1 E2.
      destruct (H1 _ _ E1) as [B1 src prg u ch R1 T1 EB1 Hl Hr Ht Hu].
      destruct (H2 _ _ E2) as [B2 src' prg' u' ch' R2 T2 EB2 Hl' Hr' Ht' Hu'].
      rewrite Hl in Hl'; injection Hl' as <-; rewrite Hr in Hr'; injection Hr' as <-;
        rewrite Ht in Ht'; injection Ht' as <-.
      destruct (run_unit_functional load_path read to_core (fp :: ch) (fp :: ch') _ _ _ _ _ _ _ _ _ eq_refl Hu Hu') as (_ & -> & -> & _).
      split; congruence. }
    split.
    - intros fp U1 U2 E1 E2; exact (proj1 (Hrun _ _ _ E1 E2)).
    - intros fp B1 B2 E1 E2.
      destruct (gds_lookup Θ1 fp) as [U1 |] eqn:F1; [| exfalso; exact (H1' _ _ E1 F1) ].
      destruct (gds_lookup Θ2 fp) as [U2 |] eqn:F2; [| exfalso; exact (H2' _ _ E2 F2) ].
      pose proof (proj2 (Hrun _ _ _ F1 F2)) as E; congruence.
  Qed.

  Lemma canon_nil : canon nil nil.
  Proof. split; intros * H; discriminate H. Qed.

  Lemma canon_file : forall ch fp src prg u BU RbU ΘU U,
      load_path fp = Some src -> read src = Some prg -> to_core prg = Some u ->
      run_unit (fp :: ch) u BU RbU ΘU U -> canon RbU ΘU -> canon ((fp, BU) :: RbU) ((fp, U) :: ΘU).
  Proof.
    intros * Hl Hr Ht Hu [Hc Hc']; split.
    - intros fq V HV; cbn in HV; destruct (path_beq fq fp) eqn:Hb.
      + apply path_beq_true in Hb as ->; injection HV as <-.
        apply (mk_canon_entry _ _ _ BU src prg u ch RbU ΘU); [ cbn; rewrite path_beq_refl; reflexivity | assumption .. ].
      + destruct (Hc _ _ HV) as [B0 src0 prg0 u0 ch0 R0 T0 E0 Hl0 Hr0 Ht0 Hu0].
        apply (mk_canon_entry _ _ _ B0 src0 prg0 u0 ch0 R0 T0); [ cbn; rewrite Hb; exact E0 | assumption .. ].
    - intros fq B0 HB; cbn in HB |- *; destruct (path_beq fq fp); [ discriminate | exact (Hc' _ _ HB) ].
  Qed.

  Lemma canon_merge : forall Rb1 Θ1 Rb2 Θ2, canon Rb1 Θ1 -> canon Rb2 Θ2 -> canon (bm_merge Rb1 Rb2) (gds_merge Θ1 Θ2).
  Proof.
    intros * [H1 H1'] [H2 H2']; split.
    - intros fp U HU; rewrite gds_lookup_merge in HU.
      destruct (gds_lookup Θ1 fp) as [U1 |] eqn:E1.
      + injection HU as <-; destruct (H1 _ _ E1) as [B0 src prg u ch R0 T0 EB Hl Hr Ht Hu].
        apply (mk_canon_entry _ _ _ B0 src prg u ch R0 T0); [ rewrite bm_lookup_merge, EB; reflexivity | assumption .. ].
      + destruct (H2 _ _ HU) as [B0 src prg u ch R0 T0 EB Hl Hr Ht Hu].
        apply (mk_canon_entry _ _ _ B0 src prg u ch R0 T0); [| assumption .. ].
        rewrite bm_lookup_merge; destruct (bm_lookup Rb1 fp) eqn:F; [ exfalso; exact (H1' _ _ F E1) | exact EB ].
    - intros fp B0 HB; rewrite bm_lookup_merge in HB; rewrite gds_lookup_merge.
      destruct (bm_lookup Rb1 fp) eqn:F.
      + destruct (gds_lookup Θ1 fp) eqn:E; [ discriminate | exfalso; exact (H1' _ _ F E) ].
      + destruct (gds_lookup Θ1 fp); [ discriminate | exact (H2' _ _ HB) ].
  Qed.

  Lemma stack_in_shape : forall ch Ξ Ξ', gs_shape Ξ' = gs_shape Ξ -> stack_in ch Ξ -> stack_in ch Ξ'.
  Proof.
    intros * Hs H mp K U Hin.
    assert (Hin' : In (mp, K, gu_params U) (gs_shape Ξ')) by (apply (in_map (fun f => (fst f, gu_params (snd f))) _ _ Hin)).
    rewrite Hs in Hin'; apply in_map_iff in Hin' as ([[mq Kq] V] & [= -> -> _] & HV); eapply H; exact HV.
  Qed.

  Theorem run_wf :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ -> ⊢ᵍ Θ' ⍮ Ξ' /\ canon Rb' Θ' /\ Θ ⊑ Θ' /\ bt_le B B') /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ -> ⊢ᵍ Θ' ⍮ Ξ' /\ canon Rb' Θ' /\ Θ ⊑ Θ' /\ bt_le B B') /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U ->
       ⊢ᵍ Θ ⍮ nil /\ canon Rb Θ /\ Θ ⍮ nil ⍮ q_abs (hd nil ch) nil ⍮ fk_module ⊢ᵍᵘ U) /\
    (forall ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ', run_ind_members ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ' ->
       ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ -> ind_uparams D = rd_uparams R ++ gs_tele Ξ ->
       ⊢ᵍ Θ' ⍮ Ξ' /\ canon Rb' Θ' /\ Θ ⊑ Θ' /\ bt_le B B').
  Proof.
    apply run_mut_dind.
    - (* a definition: the new member is checked against the frame so far *)
      intros ch B Rb Θ Ξ x b pv A M HM Hfr HΞ Hc Hst.
      repeat split; [ apply add_def_wf; assumption | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - (* an axiom: its type is checked against the frame so far *)
      intros ch B Rb Θ Ξ x b pv A i HA Hfr HΞ Hc Hst.
      repeat split; [ eapply add_axiom_wf; eassumption | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - (* a module: its body ends on a frame with the path and parameters it opened with *)
      intros ch B Rb B' Rb' Θ Ξ x pv Δ cs Θ' mp' K' U Htel HΔ Hfr Hr IH HΞ Hc Hst.
      destruct Ξ as [| [[mp K] [P Φ]] Ξ0]; [ contradiction |]; cbn [gs_fresh gs_path] in Hfr, Hr, IH |- *.
      assert (Hpush : ⊢ᵍ Θ ⍮ gs_push (qname_in mp x) Δ ((mp, K, gu_mk P Φ) :: Ξ0)).
      { apply wf_gstack_cons; [ exact HΞ | constructor; [ exact Htel | exact HΔ ] |].
        cbn; exists x; split; [ reflexivity | exact Hfr ]. }
      destruct (IH Hpush Hc (stack_in_push _ x Δ _ Hst Hfr)) as (HΞ' & Hc' & Hsub & Hle).
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr) as Hp; cbn in Hp; injection Hp as -> -> HP.
      split; [| split; [| split ]]; try assumption.
      inversion HΞ' as [| | ? ? ? ? ? ? Hs1 HU Hff1]; subst.
      inversion Hs1 as [| | ? ? ? ? ? ? Hs0 HV Hff0]; subst.
      apply wf_gstack_cons; [ exact Hs0 | | exact Hff0 ].
      cbn; econstructor; [ eassumption | constructor; eassumption | exact Hfr ].
    - (* an alias: checked against the frame so far, as a definition is *)
      intros ch B Rb Θ Ξ x pv Δ E Htel HΔ HE Hfr HΞ Hc Hst.
      repeat split; [ apply add_alias_wf; assumption | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - (* a shared unit: its record merged in *)
      intros * _ _ Hm HΞ Hc Hst.
      repeat split; [ exact HΞ | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | exact (proj1 (bt_merge_le _ _ _ Hm)) ].
    - (* a load: the unit is filed on its own, then merged in; the frames are
         of units on the chain, so it files none of them.  What was filed
         before was loaded from the same files, so it agrees with what the
         unit filed. *)
      intros ch B Rb B' Θ Ξ fp src prg u BU RbU ΘU U Hn Hnin Hl Hr Hp Ht Hu IH Hm HΞ Hc Hst.
      destruct IH as (HΘU & HcU & HU); cbn [hd] in HU.
      pose proof (proj1 (proj2 (proj2 run_chain_fresh)) _ _ _ _ _ _ Hu fp ltac:(left; reflexivity)) as HfU.
      assert (Hcf : canon ((fp, BU) :: RbU) ((fp, U) :: ΘU)) by (eapply canon_file; eassumption).
      assert (Hag : gds_agree Θ ((fp, U) :: ΘU)) by exact (proj1 (canon_agree _ _ _ _ Hc Hcf)).
      assert (Hwf : ⊢ᵍ gds_merge Θ ((fp, U) :: ΘU) ⍮ nil)
        by (apply merge_wf; [ eapply wf_gstack_deps; eassumption | apply wf_gstack_file'; assumption | exact Hag ]).
      split; [ eapply gstack_deps_grow; [ apply merge_left | exact HΞ | exact Hwf |] |].
      + intros mq Kq V Hin; pose proof (Hst _ _ _ Hin) as Hch.
        destruct (gds_lookup (gds_merge _ _) (q_unit mq)) eqn:E; [ exfalso | reflexivity ].
        apply merge_inv in E as [E | E].
        * rewrite (wf_gstack_frames _ _ HΞ _ _ _ Hin) in E; discriminate.
        * cbn in E; destruct (path_beq (q_unit mq) fp) eqn:Hb.
          -- apply path_beq_true in Hb; rewrite Hb in Hch; contradiction.
          -- rewrite (proj1 (proj2 (proj2 run_chain_fresh)) _ _ _ _ _ _ Hu _ (or_intror Hch)) in E; discriminate.
      + pose proof (canon_merge _ _ _ _ Hc Hcf) as Hcm.
        repeat split; [ exact (proj1 Hcm) | exact (proj2 Hcm) | apply merge_left | exact (proj1 (bt_merge_le _ _ _ Hm)) ].
    - (* an import: what its generated commands make *)
      intros * _ _ Hg HΞ Hc Hst.
      repeat split; [ exact (gens_run_wf _ _ _ _ Hg HΞ) | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - (* a group: its members, each with its module, then its recursor
         module, run as written commands are *)
      intros * _ _ _ _ _ _ _ Hf _ _ Hm IHm Hr IHr HΞ Hc Hst.
      destruct (IHm HΞ Hc Hst (rd_filed_uparams _ _ _ _ _ _ _ _ _ Hf)) as (H1 & Hc1 & Hs1 & Hl1).
      pose proof (stack_in_shape _ _ _ (proj2 (proj2 (proj2 run_params)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm) Hst) as Hst1.
      destruct (IHr H1 Hc1 Hst1) as (H2 & Hc2 & Hs2 & Hl2).
      split; [ exact H2 | split; [ exact Hc2 | split; eauto using gds_sub_trans, bt_le_trans ] ].
    - (* a mutual definition: its definitions, each checked as a definition is *)
      intros * _ _ _ Hd HΞ Hc Hst.
      repeat split; [ exact (mdefs_run_wf _ _ _ _ _ _ Hd HΞ) | exact (proj1 Hc) | exact (proj2 Hc)
                    | apply gds_sub_refl | apply bt_le_refl ].
    - (* a builtin binding: nothing filed, and its binding merged in *)
      intros * _ _ _ _ _ Hb HΞ Hc Hst.
      repeat split; [ exact HΞ | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | exact (bt_bind_nat_le _ _ _ Hb) ].
    - (* an inductive alias: its entry, checked where it is declared *)
      intros * _ _ _ _ HE Hfr HΞ Hc Hst.
      repeat split; [ apply add_entry_wf; assumption | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - (* a record: checked with an empty module, its module's frame opened
         over its parameters and a value of it, its field definitions and
         its with-area run in it, and the record filed with the body they
         end with *)
      intros ch B Rb Θ Ξ x pv Δ Srt fs cs B1 Rb1 Θ1 Ξ1 B' Rb' Θ' mp' K' U Hfr HE Hr1 IH1 Hr2 IH2 HΞ Hc Hst.
      destruct Ξ as [| [[mq Kq] Uq] Ξ0]; [ contradiction |].
      destruct (record_nil_entry_params _ _ _ _ _ _ _ _ HE) as [Htel HΔ].
      assert (Hpush : ⊢ᵍ Θ ⍮ gs_push_record (ind_qname ((mq, Kq, Uq) :: Ξ0) x)
                              (record_at ((mq, Kq, Uq) :: Ξ0) Δ Srt fs) Δ ((mq, Kq, Uq) :: Ξ0)).
      { apply wf_gstack_cons; [ exact HΞ | eapply wf_gmod_record_nil; [ exact Htel | exact HΔ | exact HE | reflexivity ] |].
        cbn; exists x; split; [ reflexivity | exact Hfr ]. }
      pose proof (stack_in_push_record _ x (record_at ((mq, Kq, Uq) :: Ξ0) Δ Srt fs) Δ _ Hst Hfr) as Hst'.
      destruct (IH1 Hpush Hc Hst') as (H1 & Hc1 & Hs1 & Hl1).
      pose proof (stack_in_shape _ _ _ (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr1) Hst') as Hst1.
      destruct (IH2 H1 Hc1 Hst1) as (H2 & Hc2 & Hs2 & Hl2).
      pose proof (eq_trans (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr2) (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr1))
        as Hp; cbn in Hp; injection Hp as -> -> HP.
      destruct (wf_gstack_cons_inv _ _ _ _ _ H2) as (H20 & [Δ2 Φ -> HΦ] & _); cbn in HP; subst Δ2.
      split; [| split; [ exact Hc2 | split; [ eapply gds_sub_trans; eassumption | eapply bt_le_trans; eassumption ] ] ].
      apply add_entry_wf; [ exact H20 | | exact Hfr ].
      eapply wf_gentry_record_body; [ reflexivity | exact HΦ ].
    - intros * _ HΞ Hc _; repeat split; [ exact HΞ | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - intros * _ HΞ Hc _; repeat split; [ exact HΞ | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - (* a generated definition: as a definition *)
      intros ch B Rb Θ Ξ x b pv A M HM Hfr HΞ Hc Hst.
      repeat split; [ apply add_def_wf; assumption | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - (* a generated module: as a module *)
      intros ch B Rb B' Rb' Θ Ξ x pv Δ cs Θ' mp' K' U Htel HΔ Hfr Hr IH HΞ Hc Hst.
      destruct Ξ as [| [[mp K] [P Φ]] Ξ0]; [ contradiction |]; cbn [gs_fresh gs_path] in Hfr, Hr, IH |- *.
      assert (Hpush : ⊢ᵍ Θ ⍮ gs_push (qname_in mp x) Δ ((mp, K, gu_mk P Φ) :: Ξ0)).
      { apply wf_gstack_cons; [ exact HΞ | constructor; [ exact Htel | exact HΔ ] |].
        cbn; exists x; split; [ reflexivity | exact Hfr ]. }
      destruct (IH Hpush Hc (stack_in_push _ x Δ _ Hst Hfr)) as (HΞ' & Hc' & Hsub & Hle).
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr) as Hp; cbn in Hp; injection Hp as -> -> HP.
      split; [| split; [| split ]]; try assumption.
      inversion HΞ' as [| | ? ? ? ? ? ? Hs1 HU Hff1]; subst.
      inversion Hs1 as [| | ? ? ? ? ? ? Hs0 HV Hff0]; subst.
      apply wf_gstack_cons; [ exact Hs0 | | exact Hff0 ].
      cbn; econstructor; [ eassumption | constructor; eassumption | exact Hfr ].
    - intros * HΞ Hc _; repeat split; [ exact HΞ | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - intros * _ _ Hr1 IH1 Hr2 IH2 HΞ Hc Hst.
      destruct (IH1 HΞ Hc Hst) as (H1 & Hc1 & Hs1 & Hl1).
      pose proof (stack_in_shape _ _ _ (proj1 run_params _ _ _ _ _ _ _ _ _ _ Hr1) Hst) as Hst1.
      destruct (IH2 H1 Hc1 Hst1) as (H2 & Hc2 & Hs2 & Hl2).
      split; [ exact H2 | split; [ exact Hc2 | split; eauto using gds_sub_trans, bt_le_trans ] ].
    - (* a unit: its imports from nothing, its parameters, then its body in
         the frame named by its path, which nothing it imported filed *)
      intros fp ch B1 Rb1 B2 Rb2 imps P0 P cs Θ1 Θ2 mp K U Hi IHi _ Htel HP _ Hb IHb.
      destruct (IHi ltac:(constructor; constructor) canon_nil ltac:(intros ? ? ? [])) as (H1 & Hc1 & _ & _).
      assert (Hn1 : gds_lookup Θ1 fp = None)
        by exact (proj1 (proj2 run_chain_fresh) _ _ _ _ _ _ _ _ _ _ Hi fp (or_introl eq_refl) eq_refl).
      assert (Hpush : ⊢ᵍ Θ1 ⍮ gs_push (q_abs fp nil) P nil).
      { apply wf_gstack_cons; [ exact H1 | constructor | ].
        - exact Htel.
        - cbn; rewrite app_nil_r; exact HP.
        - cbn; split; [ exact Hn1 | reflexivity ]. }
      destruct (IHb Hpush Hc1 ltac:(intros ? ? ? [[= <- <- <-] | []]; left; reflexivity)) as (H2 & Hc2 & _ & _).
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hb) as Hp; cbn in Hp; injection Hp as -> -> _.
      inversion H2; subst.
      split; [ eapply wf_gstack_deps; eassumption | split; [ exact Hc2 | cbn; apply wf_gunit_intro; assumption ] ].
    - (* no member left *)
      intros ch B Rb Θ Ξ pv R pq D k HΞ Hc Hst Hu.
      repeat split; [ exact HΞ | exact (proj1 Hc) | exact (proj2 Hc) | apply gds_sub_refl | apply bt_le_refl ].
    - (* a member: checked with an empty module, its module's frame opened
         over the group's uniform parameters, its commands run in it, and
         the member filed with the body they end with *)
      intros ch B Rb Θ Ξ pv R pq D k x xs M B1 Rb1 Θ1 mp K U B2 Rb2 Θ2 Ξ2 HM Hfr HE Hr IHr Hrest IHrest HΞ Hc Hst Hu.
      destruct Ξ as [| [[mq Kq] Uq] Ξ0]; [ contradiction |].
      destruct (ind_nil_entry_uparams _ _ _ _ _ _ _ _ HE Hu) as [Htel HΔ].
      assert (Hpush : ⊢ᵍ Θ ⍮ gs_push_ind (ind_qname ((mq, Kq, Uq) :: Ξ0) x) pq k D (rd_uparams R) ((mq, Kq, Uq) :: Ξ0)).
      { apply wf_gstack_cons; [ exact HΞ | eapply wf_gmod_ind_nil; eassumption |].
        cbn; exists x; split; [ reflexivity | exact Hfr ]. }
      destruct (IHr Hpush Hc (stack_in_push_ind _ x pq k D (rd_uparams R) _ Hst Hfr)) as (H1 & Hc1 & Hs1 & Hl1).
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr) as Hp; cbn in Hp; injection Hp as -> -> HP.
      destruct (wf_gstack_cons_inv _ _ _ _ _ H1) as (H10 & [Δ Φ -> HΦ] & _); cbn in HP; subst Δ.
      assert (Hadd : ⊢ᵍ Θ1 ⍮ gs_add x (ge_ind pv pq k D (gu_mod (gu_body (rd_uparams R) Φ))) ((mq, Kq, Uq) :: Ξ0)).
      { apply add_entry_wf; [ exact H10 | | exact Hfr ].
        eapply wf_gentry_ind_body; [ exact Hu | exact HΦ ]. }
      destruct (IHrest Hadd Hc1 (stack_in_add _ _ _ _ Hst) ltac:(rewrite gs_tele_add; exact Hu)) as (H2 & Hc2 & Hs2 & Hl2).
      split; [ exact H2 | split; [ exact Hc2 | split; eauto using gds_sub_trans, bt_le_trans ] ].
  Qed.

  (** ** Runs of Generated Commands

      The commands a group generates — the definitions of its members'
      modules ([ind_mod_cmds]) and its recursor module ([rec_cmds],
      [ind_grec_cmds]) — are definitions and modules of definitions: they
      load nothing and bind nothing, so their run files no unit and keeps
      the records, and it is well formed from where it runs, whatever the
      loads before checked.  The stack it runs on embeds into the one it
      ends with. *)

  (** A generated definition or axiom. *)
  Definition cmd_is_def (c : ccmd) : Prop := match c with cc_gen (cc_def _ _ _ _ _) => True | _ => False end.

  (** A generated command: a definition, or a module of definitions. *)
  Definition cmd_is_gen (c : ccmd) : Prop :=
    match c with
    | cc_gen (cc_def _ _ _ _ _) => True
    | cc_gen (cc_mod _ _ _ cs) => Forall cmd_is_def cs
    | _ => False
    end.

  (** What a run of generated commands keeps. *)
  Record gen_run (Θ : gdeps) (Ξ : gstack) (B : builtins) (Rb : bmap)
      (Θ' : gdeps) (Ξ' : gstack) (B' : builtins) (Rb' : bmap) : Prop := mk_gen_run
    { (** No unit is filed *)
      gr_deps : Θ' = Θ
      (** No binding is made *)
    ; gr_builtins : B' = B
      (** No record is merged *)
    ; gr_records : Rb' = Rb
      (** The stack it ends with is well formed *)
    ; gr_wf : ⊢ᵍ Θ ⍮ Ξ'
      (** The stack it runs on embeds into the one it ends with *)
    ; gr_sub : gc_sub Θ Ξ Θ Ξ' }.

  (** An entry added to the innermost frame embeds the stack. *)
  Lemma gc_sub_add : forall Θ Ξ x E, ⊢ᵍ Θ ⍮ Ξ -> gs_fresh x Ξ -> gc_sub Θ Ξ Θ (gs_add x E Ξ).
  Proof.
    intros * HΞ Hfr; destruct Ξ as [| [[mq Kq] U] Ξ]; [ contradiction |].
    destruct (wf_gstack_cons_inv _ _ _ _ _ HΞ) as (_ & [P Ψ -> _] & _).
    apply gc_sub_grow; exact Hfr.
  Qed.

  (** A run of a generated command is a run of the command it wraps. *)
  Lemma run_gen_inv : forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ',
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_gen c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'.
  Proof. intros * H; inversion H; subst; econstructor; eassumption. Qed.

  (** A command that may be generated: a definition with a body, or a
      module. *)
  Definition cmd_genable (c : ccmd) : Prop :=
    match c with
    | cc_def _ _ _ _ (Some _) | cc_mod _ _ _ _ => True
    | _ => False
    end.

  (** Such a command, generated, runs as it does. *)
  Lemma run_to_gen : forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', cmd_genable c ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_gen c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb'.
  Proof.
    intros * Hg H; destruct c as [x b pv A [M |] | | | | | | | | | | |]; try contradiction;
      inversion H; subst; econstructor; eassumption.
  Qed.

  (** Definitions file no unit, bind nothing, and keep the stack well
      formed. *)
  Lemma defs_run_wf : forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ',
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
      Forall cmd_is_def cs -> ⊢ᵍ Θ ⍮ Ξ -> gen_run Θ Ξ B Rb Θ' Ξ' B' Rb'.
  Proof.
    intros * Hr Hd; revert ch B Rb Θ Ξ B' Rb' Θ' Ξ' Hr.
    induction Hd as [| c cs Hd0 Hds IH ]; intros * Hr HΞ; inversion Hr; subst;
      [ constructor; [ reflexivity | reflexivity | reflexivity | exact HΞ | apply gc_sub_refl ] |].
    lazymatch goal with
    | Ha : fill_cmd _ _ _ c ?c3, Hc : run_cmd _ _ _ _ _ ?c3 _ _ _ _, Hcs : run_cmds _ _ _ _ _ cs _ _ _ _ |- _ =>
        assert (c3 = c) by (destruct c; try contradiction; exact (fill_cmd_generated _ _ _ _ _ Ha _ eq_refl));
        subst c3; rename Hcs into Hrest; rename Hc into Hrun
    end.
    destruct c; try contradiction; destruct c; try contradiction; apply run_gen_inv in Hrun; inversion Hrun; subst.
    - destruct (IH _ _ _ _ _ _ _ _ _ Hrest (add_def_wf _ _ _ _ _ _ _ HΞ ltac:(eassumption) ltac:(eassumption)))
        as [-> -> -> Hw Hs].
      constructor; [ reflexivity | reflexivity | reflexivity | exact Hw |].
      eapply gc_sub_trans; [ apply gc_sub_add; [ exact HΞ | eassumption ] | exact Hs ].
    - destruct (IH _ _ _ _ _ _ _ _ _ Hrest (add_axiom_wf _ _ _ _ _ _ _ HΞ ltac:(eassumption) ltac:(eassumption)))
        as [-> -> -> Hw Hs].
      constructor; [ reflexivity | reflexivity | reflexivity | exact Hw |].
      eapply gc_sub_trans; [ apply gc_sub_add; [ exact HΞ | eassumption ] | exact Hs ].
  Qed.

  (** Generated commands likewise. *)
  Lemma gen_cmds_run_wf : forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ',
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
      Forall cmd_is_gen cs -> ⊢ᵍ Θ ⍮ Ξ -> gen_run Θ Ξ B Rb Θ' Ξ' B' Rb'.
  Proof.
    intros * Hr Hd; revert ch B Rb Θ Ξ B' Rb' Θ' Ξ' Hr.
    induction Hd as [| c cs Hd0 Hds IH ]; intros * Hr HΞ; inversion Hr; subst;
      [ constructor; [ reflexivity | reflexivity | reflexivity | exact HΞ | apply gc_sub_refl ] |].
    pose proof Hd0 as Hd2.
    match goal with
    | Ha : fill_cmd _ _ _ c ?c3, Hc : run_cmd _ _ _ _ _ ?c3 _ _ _ _, Hcs : run_cmds _ _ _ _ _ cs _ _ _ _ |- _ =>
        assert (c3 = c) by (destruct c; try contradiction; exact (fill_cmd_generated _ _ _ _ _ Ha _ eq_refl));
        subst c3; rename Hcs into Hrest; rename Hc into Hrun
    end.
    assert (Hstep : forall Ξn, ⊢ᵍ Θ ⍮ Ξn -> gc_sub Θ Ξ Θ Ξn ->
              Θ ⍮ Ξn ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
              gen_run Θ Ξ B Rb Θ' Ξ' B' Rb').
    { intros Ξn Hw1 Hs1 Hr1; destruct (IH _ _ _ _ _ _ _ _ _ Hr1 Hw1) as [-> -> -> Hw Hs].
      constructor; [ reflexivity | reflexivity | reflexivity | exact Hw | eapply gc_sub_trans; eassumption ]. }
    destruct c; try contradiction; destruct c; try contradiction; apply run_gen_inv in Hrun; inversion Hrun; subst.
    - exact (Hstep _ (add_def_wf _ _ _ _ _ _ _ HΞ ltac:(eassumption) ltac:(eassumption)) (gc_sub_add _ _ _ _ HΞ ltac:(eassumption)) Hrest).
    - exact (Hstep _ (add_axiom_wf _ _ _ _ _ _ _ HΞ ltac:(eassumption) ltac:(eassumption)) (gc_sub_add _ _ _ _ HΞ ltac:(eassumption)) Hrest).
    - (* a module of definitions: its body, then its frame filed *)
      match goal with Hb : run_cmds _ _ _ _ (gs_push _ _ _) _ _ _ _ _ |- _ => rename Hb into Hbody end.
      match goal with Hf : gs_fresh ?x0 Ξ |- _ => rename Hf into Hfr end.
      destruct Ξ as [| [[mq Kq] [P Φ]] Ξs]; [ contradiction |]; cbn [gs_fresh gs_path] in Hfr, Hbody |- *.
      assert (Hpush : ⊢ᵍ Θ ⍮ gs_push (qname_in mq s) l ((mq, Kq, gu_mk P Φ) :: Ξs)).
      { apply wf_gstack_cons; [ exact HΞ | constructor; assumption |].
        cbn; exists s; split; [ reflexivity | exact Hfr ]. }
      destruct (defs_run_wf _ _ _ _ _ _ _ _ _ _ Hbody Hd2 Hpush) as [-> -> -> HΞ' _].
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hbody) as Hp; cbn in Hp; injection Hp as -> -> HP.
      destruct (wf_gstack_cons_inv _ _ _ _ _ HΞ') as (Hs0 & [Δ' Φ' -> HΦ'] & _); cbn in HP; subst Δ'.
      refine (Hstep _ _ _ Hrest); [| apply gc_sub_add; [ exact HΞ | exact Hfr ] ].
      apply add_entry_wf; [ exact Hs0 | constructor; exact HΦ' | exact Hfr ].
  Qed.

  (** The commands of the recursor module of a group are generated. *)
  Lemma grec_mod_cmd_gen : forall Θ Ξ pq D Δu, cmd_is_gen (grec_mod_cmd Θ Ξ pq D Δu).
  Proof.
    intros; cbn; apply Forall_forall; intros c0 Hin; apply in_map_iff in Hin as ([[j Mj] x0] & <- & _); exact I.
  Qed.

  Lemma rec_cmds_gen : forall Θ Ξ R pq D, Forall cmd_is_gen (rec_cmds Θ Ξ R pq D).
  Proof. intros; unfold rec_cmds; destruct (rd_rec R); [ constructor; [ apply grec_mod_cmd_gen | constructor ] | constructor ]. Qed.

  (** So are those of the module of a declared member. *)
  Lemma ind_mod_cmds_gen : forall Θ Ξ R pq D k M, Forall cmd_is_gen (ind_mod_cmds Θ Ξ R pq D k M).
  Proof.
    intros; unfold ind_mod_cmds, ind_rec_cmds, ind_grec_cmds.
    apply Forall_app; split; [| apply Forall_app; split ].
    - apply Forall_forall; intros c0 Hin; apply in_map_iff in Hin as (cg & <- & _); exact I.
    - destruct (ind_has_rec D); [ constructor; [ exact I | constructor ] | constructor ].
    - destruct (_ && _); [ constructor; [ apply grec_mod_cmd_gen | constructor ] | constructor ].
  Qed.

  (** The recursor module of a group files no unit, and the stack it runs
      on, well formed, embeds into the one it ends with. *)
  Lemma rec_cmds_run_wf : forall ch B Rb Θ Ξ Θ0 Ξ0 R pq D B' Rb' Θ' Ξ',
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ rec_cmds Θ0 Ξ0 R pq D ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
      ⊢ᵍ Θ ⍮ Ξ -> gen_run Θ Ξ B Rb Θ' Ξ' B' Rb'.
  Proof. intros * Hr HΞ; exact (gen_cmds_run_wf _ _ _ _ _ _ _ _ _ _ Hr (rec_cmds_gen _ _ _ _ _) HΞ). Qed.

  (** A member's module, its generated commands run in its frame, closed
      into the member's entry: no unit is filed, nothing is bound, and the
      stack it is declared in embeds into the one with the entry. *)
  Lemma ind_member_run_gen : forall ch B Rb Θ Ξ pv R pq D k x M B1 Rb1 Θ1 mp K U,
      ⊢ᵍ Θ ⍮ Ξ -> ind_uparams D = rd_uparams R ++ gs_tele Ξ -> gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k D ⋄ ->
      Θ ⍮ gs_push_ind (ind_qname Ξ x) pq k D (rd_uparams R) Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩
        ind_mod_cmds Θ (gs_push_ind (ind_qname Ξ x) pq k D (rd_uparams R) Ξ) R pq D k M ⇝*
        Θ1 ⍮ (mp, K, U) :: Ξ ⍮ B1 ⍮ Rb1 ->
      gen_run Θ Ξ B Rb Θ1 (gs_add x (ge_ind pv pq k D (gu_mod U)) Ξ) B1 Rb1.
  Proof.
    intros * HΞ Hu Hfr HE Hr.
    destruct Ξ as [| [[mq Kq] Uq] Ξ0]; [ contradiction |].
    destruct (ind_nil_entry_uparams _ _ _ _ _ _ _ _ HE Hu) as [Htel HΔ].
    assert (Hpush : ⊢ᵍ Θ ⍮ gs_push_ind (ind_qname ((mq, Kq, Uq) :: Ξ0) x) pq k D (rd_uparams R) ((mq, Kq, Uq) :: Ξ0)).
    { apply wf_gstack_cons; [ exact HΞ | eapply wf_gmod_ind_nil; eassumption |].
      cbn; exists x; split; [ reflexivity | exact Hfr ]. }
    destruct (gen_cmds_run_wf _ _ _ _ _ _ _ _ _ _ Hr (ind_mod_cmds_gen _ _ _ _ _ _ _) Hpush) as [-> -> -> H1 _].
    pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr) as Hp; cbn in Hp; injection Hp as -> -> HP.
    destruct (wf_gstack_cons_inv _ _ _ _ _ H1) as (H10 & [Δ Φ -> HΦ] & _); cbn in HP; subst Δ.
    constructor; [ reflexivity | reflexivity | reflexivity | | apply gc_sub_add; [ exact HΞ | exact Hfr ] ].
    apply add_entry_wf; [ exact H10 | | exact Hfr ].
    eapply wf_gentry_ind_body; [ exact Hu | exact HΦ ].
  Qed.

  (** The declared members of a group, each with its module: likewise. *)
  Lemma ind_members_run_gen : forall ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ',
      run_ind_members ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ' ->
      ⊢ᵍ Θ ⍮ Ξ -> ind_uparams D = rd_uparams R ++ gs_tele Ξ -> gen_run Θ Ξ B Rb Θ' Ξ' B' Rb'.
  Proof.
    induction 1 as [ch B Rb Θ Ξ pv R pq D k | ch B Rb Θ Ξ pv R pq D k x xs M B1 Rb1 Θ1 mp K U B2 Rb2 Θ2 Ξ2 HM Hfr HE Hr Hrest IH];
      intros HΞ Hu.
    - constructor; [ reflexivity | reflexivity | reflexivity | exact HΞ | apply gc_sub_refl ].
    - destruct (ind_member_run_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΞ Hu Hfr HE Hr) as [-> -> -> H1 Hs1].
      destruct (IH H1 ltac:(rewrite gs_tele_add; exact Hu)) as [-> -> -> H2 Hs2].
      constructor; [ reflexivity | reflexivity | reflexivity | exact H2 | eapply gc_sub_trans; eassumption ].
  Qed.

  (** After the declared members, the group is found at its first member's
      path. *)
  Lemma ind_members_run_lookup : forall ch B Rb Θ Ξ pv R D x xs B' Rb' Θ' Ξ',
      run_ind_members ch B Rb Θ Ξ pv R (ind_qname Ξ x) D 0 (x :: xs) B' Rb' Θ' Ξ' ->
      ⊢ᵍ Θ ⍮ Ξ -> ind_uparams D = rd_uparams R ++ gs_tele Ξ -> ind_lookup Θ' Ξ' (ind_qname Ξ x) = Some D.
  Proof.
    intros * Hr HΞ Hu.
    inversion Hr as [| ? ? ? ? ? ? ? ? ? ? x' xs' M B1 Rb1 Θ1 mp K U B2 Rb2 Θ2 Ξ2 HM Hfr HE Hr1 Hrest]; subst.
    destruct (ind_member_run_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΞ Hu Hfr HE Hr1) as [-> -> -> H1 _].
    destruct (ind_members_run_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrest H1 ltac:(rewrite gs_tele_add; exact Hu)) as [-> _ _ _ Hs2].
    eapply ind_lookup_gc_sub; [ exact Hs2 |].
    apply ind_lookup_added; intros ->; exact Hfr.
  Qed.

  (** The members a run files are named apart, each fresh where the run
      starts. *)
  Lemma ind_members_run_fresh : forall ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ',
      run_ind_members ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ' -> List.NoDup xs /\ Forall (fun x => gs_fresh x Ξ) xs.
  Proof.
    induction 1 as [| ch B Rb Θ Ξ pv R pq D k x xs M B1 Rb1 Θ1 mp K U B2 Rb2 Θ2 Ξ2 HM Hfr HE Hr Hrest [Hnd Hall]];
      [ split; constructor |].
    split; [ constructor; [| exact Hnd ] | constructor; [ exact Hfr |] ].
    - intros Hin; destruct (gs_fresh_add_inv _ _ _ _ (proj1 (List.Forall_forall _ _) Hall x Hin)) as [_ []]; reflexivity.
    - eapply Forall_impl; [| exact Hall ]; intros y Hy; exact (proj1 (gs_fresh_add_inv _ _ _ _ Hy)).
  Qed.

  (** What a load files is well formed, whatever the import checks. *)
  Lemma load_wf : forall ch Rb Θ Ξ fp src prg u BU RbU ΘU U,
      ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ -> gds_lookup Θ fp = None -> ~ In fp ch ->
      load_path fp = Some src -> read src = Some prg -> to_core prg = Some u ->
      run_unit (fp :: ch) u BU RbU ΘU U ->
      ⊢ᵍ gds_merge Θ ((fp, U) :: ΘU) ⍮ Ξ /\ canon (bm_merge Rb ((fp, BU) :: RbU)) (gds_merge Θ ((fp, U) :: ΘU)) /\
        Θ ⊑ gds_merge Θ ((fp, U) :: ΘU).
  Proof.
    intros * HΞ Hc Hst Hn Hnin Hl Hr Ht Hu.
    destruct (proj1 (proj2 (proj2 run_wf)) _ _ _ _ _ _ Hu) as (HΘU & HcU & HU); cbn [hd] in HU.
    pose proof (proj1 (proj2 (proj2 run_chain_fresh)) _ _ _ _ _ _ Hu fp ltac:(left; reflexivity)) as HfU.
    assert (Hcf : canon ((fp, BU) :: RbU) ((fp, U) :: ΘU)) by (eapply canon_file; eassumption).
    assert (Hag : gds_agree Θ ((fp, U) :: ΘU)) by exact (proj1 (canon_agree _ _ _ _ Hc Hcf)).
    assert (Hwf : ⊢ᵍ gds_merge Θ ((fp, U) :: ΘU) ⍮ nil)
      by (apply merge_wf; [ eapply wf_gstack_deps; eassumption | apply wf_gstack_file'; assumption | exact Hag ]).
    split; [ eapply gstack_deps_grow; [ apply merge_left | exact HΞ | exact Hwf |] |].
    + intros mq Kq V Hin; pose proof (Hst _ _ _ Hin) as Hch.
      destruct (gds_lookup (gds_merge _ _) (q_unit mq)) eqn:E; [ exfalso | reflexivity ].
      apply merge_inv in E as [E | E].
      * rewrite (wf_gstack_frames _ _ HΞ _ _ _ Hin) in E; discriminate.
      * cbn in E; destruct (path_beq (q_unit mq) fp) eqn:Hb.
        -- apply path_beq_true in Hb; rewrite Hb in Hch; contradiction.
        -- rewrite (proj1 (proj2 (proj2 run_chain_fresh)) _ _ _ _ _ _ Hu _ (or_intror Hch)) in E; discriminate.
    + split; [ apply canon_merge; assumption | apply merge_left ].
  Qed.

  Corollary load_coherent : forall ch B Rb B' Rb' Θ Ξ fp Θ',
      ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_load fp ⇝ Θ' ⍮ Ξ ⍮ B' ⍮ Rb' ->
      ⊢ᵍ Θ' ⍮ nil /\ gds_lookup Θ' fp <> None.
  Proof.
    intros * HΞ Hc Hst Hr; destruct (proj1 run_wf _ _ _ _ _ _ _ _ _ _ Hr HΞ Hc Hst) as (H' & _ & _).
    split; [ eapply wf_gstack_deps; eassumption |].
    inversion Hr; subst; [ congruence |].
    (* [fp] was loaded: it is filed on top of what its run filed *)
    rewrite merge_none; cbn; rewrite path_beq_refl; intros [_ ?]; discriminate.
  Qed.

  Corollary prog_sem_wf : forall prg B Θ U,
      prog_sem load_path read to_core prg B Θ U ->
      ⊢ᵍ Θ ⍮ nil /\ Θ ⍮ nil ⍮ q_abs (prog_path prg) nil ⍮ fk_module ⊢ᵍᵘ U.
  Proof.
    intros * [u Rb _ Hu]; destruct (proj1 (proj2 (proj2 run_wf)) _ _ _ _ _ _ Hu) as (? & _ & ?); split; assumption.
  Qed.

  (** ** Builtin Bindings Stay Well Formed

      A binding is made of an inductive type of the right shape where it is
      read ([rc_builtin]), and a run keeps reading it: entries are added,
      module frames are closed into members, units are filed and merged,
      and records are merged ([bt_merge_wf]).  The record of a unit, and
      those of the units it filed, are read where it is filed. *)
  Theorem run_builtins_wf :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ -> builtins_wf Θ Ξ B -> bm_wf Θ Rb ->
       builtins_wf Θ' Ξ' B' /\ bm_wf Θ' Rb') /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ -> builtins_wf Θ Ξ B -> bm_wf Θ Rb ->
       builtins_wf Θ' Ξ' B' /\ bm_wf Θ' Rb') /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U ->
       builtins_wf ((hd nil ch, U) :: Θ) nil B /\ bm_wf ((hd nil ch, U) :: Θ) Rb) /\
    (forall ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ', run_ind_members ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ' ->
       ⊢ᵍ Θ ⍮ Ξ -> canon Rb Θ -> stack_in ch Ξ -> ind_uparams D = rd_uparams R ++ gs_tele Ξ ->
       builtins_wf Θ Ξ B -> bm_wf Θ Rb -> builtins_wf Θ' Ξ' B' /\ bm_wf Θ' Rb').
  Proof.
    assert (Hadd : forall Θ Ξ x E B, ⊢ᵍ Θ ⍮ Ξ -> gs_fresh x Ξ -> builtins_wf Θ Ξ B -> builtins_wf Θ (gs_add x E Ξ) B)
      by (intros * HΞ Hfr; apply builtins_wf_mono; intros; apply ind_lookup_add; assumption).
    apply run_mut_ind.
    - intros * _ Hfr HΞ _ _ Hb HR; split; [ apply Hadd; assumption | exact HR ].
    - intros * _ Hfr HΞ _ _ Hb HR; split; [ apply Hadd; assumption | exact HR ].
    - (* a module: read in its frame, then in the member it becomes *)
      intros ch B Rb B' Rb' Θ Ξ x pv Δ cs Θ' mp' K' U Htel HΔ Hfr Hr IH HΞ Hc Hst Hb HR.
      destruct Ξ as [| [[mp K] [P Φ]] Ξ0]; [ contradiction |]; cbn [gs_fresh gs_path] in Hfr, Hr, IH |- *.
      assert (Hff : frame_fresh Θ ((mp, K, gu_mk P Φ) :: Ξ0) (qname_in mp x))
        by (cbn; exists x; split; [ reflexivity | exact Hfr ]).
      assert (Hpush : ⊢ᵍ Θ ⍮ gs_push (qname_in mp x) Δ ((mp, K, gu_mk P Φ) :: Ξ0))
        by (apply wf_gstack_cons; [ exact HΞ | constructor; [ exact Htel | exact HΔ ] | exact Hff ]).
      pose proof (stack_in_push _ x Δ _ Hst Hfr) as Hst'.
      assert (Hb0 : builtins_wf Θ (gs_push (qname_in mp x) Δ ((mp, K, gu_mk P Φ) :: Ξ0)) B)
        by (eapply builtins_wf_mono; [ intros; eapply ind_lookup_gc_sub; [ apply gc_sub_push; exact Hff | eassumption ] | exact Hb ]).
      destruct (proj1 (proj2 run_wf) _ _ _ _ _ _ _ _ _ _ Hr Hpush Hc Hst') as (HΞ' & _).
      destruct (IH Hpush Hc Hst' Hb0 HR) as [Hb' HR'].
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr) as Hp; cbn in Hp; injection Hp as -> -> HP.
      destruct (wf_gstack_cons_inv _ _ _ _ _ HΞ') as (HΞ0 & [Δ' Φ' -> _] & _).
      cbn in HP; subst Δ'; cbn [gu_mod].
      split; [| exact HR' ].
      eapply builtins_wf_mono; [| exact Hb' ].
      intros p0 D0 Hl; apply (ind_lookup_close _ ((mp, K, gu_mk P Φ) :: Ξ0) x pv fk_module); [ exact HΞ0 | exact Hfr | exact I | exact Hl ].
    - intros * _ _ _ Hfr HΞ _ _ Hb HR; split; [ apply Hadd; assumption | exact HR ].
    - (* a shared unit: its record, read where it is filed, merged in *)
      intros ch B Rb B' Θ Ξ fp U BU _ HBU Hm HΞ _ _ Hb HR; split; [| exact HR ].
      eapply bt_merge_wf; [ exact Hb | | exact Hm ].
      apply builtins_wf_below; [ exact (wf_gstack_frames _ _ HΞ) | exact (HR _ _ HBU) ].
    - (* a load: the unit's record is read where it is filed, and so is what
         was read before *)
      intros ch B Rb B' Θ Ξ fp src prg u BU RbU ΘU U Hn Hnin Hl Hrd Hpp Ht Hu IH Hm HΞ Hc Hst Hb HR.
      cbn [hd] in IH; destruct IH as [HbU HRU].
      assert (Hrun : Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_load fp ⇝ gds_merge Θ ((fp, U) :: ΘU) ⍮ Ξ ⍮ B' ⍮ bm_merge Rb ((fp, BU) :: RbU))
        by (eapply rc_load; eassumption).
      destruct (proj1 run_wf _ _ _ _ _ _ _ _ _ _ Hrun HΞ Hc Hst) as (HΞ' & _ & Hsub & _).
      pose proof (proj1 (proj2 (proj2 run_chain_fresh)) _ _ _ _ _ _ Hu fp ltac:(left; reflexivity)) as HfU.
      destruct (proj1 (proj2 (proj2 run_wf)) _ _ _ _ _ _ Hu) as (_ & HcU & _).
      assert (Hcf : canon ((fp, BU) :: RbU) ((fp, U) :: ΘU)) by (eapply canon_file; eassumption).
      assert (Hsub' : (fp, U) :: ΘU ⊑ gds_merge Θ ((fp, U) :: ΘU))
        by (apply merge_right; exact (proj1 (canon_agree _ _ _ _ Hc Hcf))).
      assert (HRm : bm_wf (gds_merge Θ ((fp, U) :: ΘU)) (bm_merge Rb ((fp, BU) :: RbU))).
      { intros fq Bq Hq; rewrite bm_lookup_merge in Hq.
        destruct (bm_lookup Rb fq) as [Bq' |] eqn:E.
        - injection Hq as <-; exact (bm_wf_sub _ _ _ Hsub HR _ _ E).
        - assert (HRU' : bm_wf ((fp, U) :: ΘU) ((fp, BU) :: RbU))
            by (intros fr Br Hr0; cbn in Hr0; destruct (path_beq fr fp); [ injection Hr0 as <-; exact HbU | exact (HRU _ _ Hr0) ]).
          exact (bm_wf_sub _ _ _ Hsub' HRU' _ _ Hq). }
      split; [| exact HRm ].
      eapply bt_merge_wf; [| | exact Hm ].
      + eapply builtins_wf_mono; [ intros; eapply ind_lookup_gc_sub; [ apply gc_sub_deps; exact Hsub | eassumption ] | exact Hb ].
      + apply builtins_wf_below; [ exact (wf_gstack_frames _ _ HΞ') |].
        eapply builtins_wf_mono; [ intros; eapply ind_lookup_gc_sub; [ apply gc_sub_deps; exact Hsub' | eassumption ] | exact HbU ].
    - intros * _ _ Hg HΞ _ _ Hb HR; split; [| exact HR ].
      revert Hb; apply builtins_wf_mono; intros; eapply gens_run_ind_lookup; eassumption.
    - (* a group: its members, then its recursor module *)
      intros * _ _ _ _ _ _ _ Hf _ _ Hm IHm Hr IHr HΞ Hc Hst Hb HR.
      pose proof (rd_filed_uparams _ _ _ _ _ _ _ _ _ Hf) as Hu.
      destruct (proj2 (proj2 (proj2 run_wf)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm HΞ Hc Hst Hu) as (H1 & Hc1 & _).
      pose proof (stack_in_shape _ _ _ (proj2 (proj2 (proj2 run_params)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hm) Hst) as Hst1.
      destruct (IHm HΞ Hc Hst Hu Hb HR) as [Hb1 HR1].
      exact (IHr H1 Hc1 Hst1 Hb1 HR1).
    - intros * _ _ _ Hd HΞ _ _ Hb HR; split; [| exact HR ].
      revert Hb; apply builtins_wf_mono; intros; eapply mdefs_run_ind_lookup; eassumption.
    - (* a binding: of a type read here *)
      intros ch B Rb B' Θ Ξ H p D z0 s0 _ Hl Hs Ho Hso Hbd _ _ _ Hb HR; split; [| exact HR ].
      eapply bt_merge_wf; [ exact Hb | | exact Hbd ].
      intros p1 Hq; cbn in Hq; injection Hq as <-; exact (mk_nat_binding_ok _ _ _ D z0 s0 Hs Ho Hso).
    - intros * _ _ _ _ _ Hfr HΞ _ _ Hb HR; split; [ apply Hadd; assumption | exact HR ].
    - (* a record: read in its module's frame, then in the record it becomes *)
      intros ch B Rb Θ Ξ x pv Δ Srt fs cs B1 Rb1 Θ1 Ξ1 B' Rb' Θ' mp' K' U Hfr HE Hr1 IH1 Hr2 IH2 HΞ Hc Hst Hb HR.
      destruct Ξ as [| [[mq Kq] Uq] Ξ0]; [ contradiction |].
      destruct (record_nil_entry_params _ _ _ _ _ _ _ _ HE) as [Htel HΔ].
      assert (Hff : frame_fresh Θ ((mq, Kq, Uq) :: Ξ0) (ind_qname ((mq, Kq, Uq) :: Ξ0) x))
        by (cbn; exists x; split; [ reflexivity | exact Hfr ]).
      assert (Hpush : ⊢ᵍ Θ ⍮ gs_push_record (ind_qname ((mq, Kq, Uq) :: Ξ0) x)
                              (record_at ((mq, Kq, Uq) :: Ξ0) Δ Srt fs) Δ ((mq, Kq, Uq) :: Ξ0))
        by (apply wf_gstack_cons; [ exact HΞ | eapply wf_gmod_record_nil; [ exact Htel | exact HΔ | exact HE | reflexivity ]
                                  | exact Hff ]).
      pose proof (stack_in_push_record _ x (record_at ((mq, Kq, Uq) :: Ξ0) Δ Srt fs) Δ _ Hst Hfr) as Hst'.
      match type of Hpush with ⊢ᵍ _ ⍮ ?Xp =>
        assert (Hb0 : builtins_wf Θ Xp B)
          by (eapply builtins_wf_mono; [ intros; eapply ind_lookup_gc_sub; [ apply gc_sub_push; exact Hff | eassumption ]
                                       | exact Hb ]) end.
      destruct (proj1 (proj2 run_wf) _ _ _ _ _ _ _ _ _ _ Hr1 Hpush Hc Hst') as (H1 & Hc1 & _).
      destruct (IH1 Hpush Hc Hst' Hb0 HR) as [Hb1 HR1].
      pose proof (stack_in_shape _ _ _ (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr1) Hst') as Hst1.
      destruct (proj1 (proj2 run_wf) _ _ _ _ _ _ _ _ _ _ Hr2 H1 Hc1 Hst1) as (H2 & Hc2 & _).
      destruct (IH2 H1 Hc1 Hst1 Hb1 HR1) as [Hb2 HR2].
      pose proof (eq_trans (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr2) (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr1))
        as Hp; cbn in Hp; injection Hp as -> -> HP.
      destruct (wf_gstack_cons_inv _ _ _ _ _ H2) as (H10 & [Δ1 Φ -> HΦ] & _); cbn in HP; subst Δ1.
      split; [| exact HR2 ].
      eapply builtins_wf_mono; [| exact Hb2 ].
      intros p0 D0 Hl; exact (ind_lookup_close _ ((mq, Kq, Uq) :: Ξ0) x pv
                                (fk_record (record_at ((mq, Kq, Uq) :: Ξ0) Δ Srt fs))
                                (ce_ass (record_self (ind_qname ((mq, Kq, Uq) :: Ξ0) x) (record_at ((mq, Kq, Uq) :: Ξ0) Δ Srt fs)) :: Δ)
                                Φ _ _ H10 Hfr (ex_intro _ Δ (conj eq_refl eq_refl)) Hl).
    - intros; split; assumption.
    - intros; split; assumption.
    - (* a generated definition: as a definition *)
      intros * _ Hfr HΞ _ _ Hb HR; split; [ apply Hadd; assumption | exact HR ].
    - (* a generated module: as a module *)
      intros ch B Rb B' Rb' Θ Ξ x pv Δ cs Θ' mp' K' U Htel HΔ Hfr Hr IH HΞ Hc Hst Hb HR.
      destruct Ξ as [| [[mp K] [P Φ]] Ξ0]; [ contradiction |]; cbn [gs_fresh gs_path] in Hfr, Hr, IH |- *.
      assert (Hff : frame_fresh Θ ((mp, K, gu_mk P Φ) :: Ξ0) (qname_in mp x))
        by (cbn; exists x; split; [ reflexivity | exact Hfr ]).
      assert (Hpush : ⊢ᵍ Θ ⍮ gs_push (qname_in mp x) Δ ((mp, K, gu_mk P Φ) :: Ξ0))
        by (apply wf_gstack_cons; [ exact HΞ | constructor; [ exact Htel | exact HΔ ] | exact Hff ]).
      pose proof (stack_in_push _ x Δ _ Hst Hfr) as Hst'.
      assert (Hb0 : builtins_wf Θ (gs_push (qname_in mp x) Δ ((mp, K, gu_mk P Φ) :: Ξ0)) B)
        by (eapply builtins_wf_mono; [ intros; eapply ind_lookup_gc_sub; [ apply gc_sub_push; exact Hff | eassumption ] | exact Hb ]).
      destruct (proj1 (proj2 run_wf) _ _ _ _ _ _ _ _ _ _ Hr Hpush Hc Hst') as (HΞ' & _).
      destruct (IH Hpush Hc Hst' Hb0 HR) as [Hb' HR'].
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr) as Hp; cbn in Hp; injection Hp as -> -> HP.
      destruct (wf_gstack_cons_inv _ _ _ _ _ HΞ') as (HΞ0 & [Δ' Φ' -> _] & _).
      cbn in HP; subst Δ'; cbn [gu_mod].
      split; [| exact HR' ].
      eapply builtins_wf_mono; [| exact Hb' ].
      intros p0 D0 Hl; apply (ind_lookup_close _ ((mp, K, gu_mk P Φ) :: Ξ0) x pv fk_module); [ exact HΞ0 | exact Hfr | exact I | exact Hl ].
    - intros; split; assumption.
    - intros * _ _ Hr1 IH1 _ IH2 HΞ Hc Hst Hb HR.
      destruct (proj1 run_wf _ _ _ _ _ _ _ _ _ _ Hr1 HΞ Hc Hst) as (H1 & Hc1 & _).
      pose proof (stack_in_shape _ _ _ (proj1 run_params _ _ _ _ _ _ _ _ _ _ Hr1) Hst) as Hst1.
      destruct (IH1 HΞ Hc Hst Hb HR) as [Hb1 HR1].
      exact (IH2 H1 Hc1 Hst1 Hb1 HR1).
    - (* a unit: its imports, its frame pushed, then filed *)
      intros fp ch B1 Rb1 B2 Rb2 imps P0 P cs Θ1 Θ2 mp K U Hi IHi _ Htel HP _ Hbd IHb.
      assert (Hnil : ⊢ᵍ nil ⍮ nil) by (constructor; constructor).
      destruct (proj1 (proj2 run_wf) _ _ _ _ _ _ _ _ _ _ Hi Hnil canon_nil ltac:(intros ? ? ? [])) as (H1 & Hc1 & _).
      assert (Hn1 : gds_lookup Θ1 fp = None)
        by exact (proj1 (proj2 run_chain_fresh) _ _ _ _ _ _ _ _ _ _ Hi fp (or_introl eq_refl) eq_refl).
      assert (Hff : frame_fresh Θ1 nil (q_abs fp nil)) by (cbn; split; [ exact Hn1 | reflexivity ]).
      assert (Hpush : ⊢ᵍ Θ1 ⍮ gs_push (q_abs fp nil) P nil).
      { apply wf_gstack_cons; [ exact H1 | constructor | exact Hff ].
        - exact Htel.
        - cbn; rewrite app_nil_r; exact HP. }
      destruct (IHi Hnil canon_nil ltac:(intros ? ? ? []) ltac:(intros p Hp; discriminate) ltac:(intros ? ? Hq; discriminate))
        as [Hb1 HR1].
      assert (Hb1' : builtins_wf Θ1 (gs_push (q_abs fp nil) P nil) B1)
        by (eapply builtins_wf_mono; [ intros; eapply ind_lookup_gc_sub; [ apply gc_sub_push; exact Hff | eassumption ] | exact Hb1 ]).
      destruct (IHb Hpush Hc1 ltac:(intros ? ? ? [[= <- <- <-] | []]; left; reflexivity) Hb1' HR1) as [Hb2 HR2].
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hbd) as Hp; cbn in Hp; injection Hp as -> -> _.
      assert (Hn2 : gds_lookup Θ2 fp = None)
        by exact (proj1 (proj2 run_chain_fresh) _ _ _ _ _ _ _ _ _ _ Hbd fp (or_introl eq_refl) Hn1).
      cbn [hd]; split.
      + eapply builtins_wf_mono; [| exact Hb2 ].
        intros p0 D0 Hl0; rewrite ind_lookup_file; exact Hl0.
      + exact (bm_wf_sub _ _ _ (gds_sub_cons _ _ _ Hn2) HR2).
    - intros; split; assumption.
    - (* a member: read in its module's frame, then in the member it becomes *)
      intros ch B Rb Θ Ξ pv R pq D k x xs M B1 Rb1 Θ1 mp K U B2 Rb2 Θ2 Ξ2 HM Hfr HE Hr IHr Hrest IHrest HΞ Hc Hst Hu Hb HR.
      destruct Ξ as [| [[mq Kq] Uq] Ξ0]; [ contradiction |].
      destruct (ind_nil_entry_uparams _ _ _ _ _ _ _ _ HE Hu) as [Htel HΔ].
      assert (Hff : frame_fresh Θ ((mq, Kq, Uq) :: Ξ0) (ind_qname ((mq, Kq, Uq) :: Ξ0) x))
        by (cbn; exists x; split; [ reflexivity | exact Hfr ]).
      assert (Hpush : ⊢ᵍ Θ ⍮ gs_push_ind (ind_qname ((mq, Kq, Uq) :: Ξ0) x) pq k D (rd_uparams R) ((mq, Kq, Uq) :: Ξ0))
        by (apply wf_gstack_cons; [ exact HΞ | eapply wf_gmod_ind_nil; eassumption | exact Hff ]).
      pose proof (stack_in_push_ind _ x pq k D (rd_uparams R) _ Hst Hfr) as Hst'.
      assert (Hb0 : builtins_wf Θ (gs_push_ind (ind_qname ((mq, Kq, Uq) :: Ξ0) x) pq k D (rd_uparams R) ((mq, Kq, Uq) :: Ξ0)) B)
        by (eapply builtins_wf_mono; [ intros; eapply ind_lookup_gc_sub; [ apply gc_sub_push; exact Hff | eassumption ] | exact Hb ]).
      destruct (proj1 (proj2 run_wf) _ _ _ _ _ _ _ _ _ _ Hr Hpush Hc Hst') as (H1 & Hc1 & _).
      destruct (IHr Hpush Hc Hst' Hb0 HR) as [Hb1 HR1].
      pose proof (proj1 (proj2 run_params) _ _ _ _ _ _ _ _ _ _ Hr) as Hp; cbn in Hp; injection Hp as -> -> HP.
      destruct (wf_gstack_cons_inv _ _ _ _ _ H1) as (H10 & [Δ Φ -> HΦ] & _); cbn in HP; subst Δ.
      assert (Hadd' : ⊢ᵍ Θ1 ⍮ gs_add x (ge_ind pv pq k D (gu_mod (gu_body (rd_uparams R) Φ))) ((mq, Kq, Uq) :: Ξ0)).
      { apply add_entry_wf; [ exact H10 | | exact Hfr ].
        eapply wf_gentry_ind_body; [ exact Hu | exact HΦ ]. }
      apply IHrest; [ exact Hadd' | exact Hc1 | exact (stack_in_add _ _ _ _ Hst) | rewrite gs_tele_add; exact Hu | | exact HR1 ].
      eapply builtins_wf_mono; [| exact Hb1 ].
      intros p0 D0 Hl; exact (ind_lookup_close _ ((mq, Kq, Uq) :: Ξ0) x pv (fk_ind pq k D) (rd_uparams R) Φ _ _ H10 Hfr Hu Hl).
  Qed.

  (** At the end of a program, its record is of a type it reads. *)
  Corollary prog_sem_builtins_wf : forall prg B Θ U,
      prog_sem load_path read to_core prg B Θ U -> builtins_wf ((prog_path prg, U) :: Θ) nil B.
  Proof. intros * [u Rb _ Hu]; exact (proj1 (proj1 (proj2 (proj2 run_builtins_wf)) _ _ _ _ _ _ Hu)). Qed.
End WellFormed.


(** ** Restricting to What a Unit Imported

    The executable ([Extraction.Command]) keeps one set of filed units for the
    whole program, so no unit is run twice; but a unit runs from nothing, and
    may mention only what it imported.  So it is checked against the
    restriction of that set to the paths it imported, which has the lookups of
    the judgment's state ([equiv_restrict]).  Checking against the whole set
    would accept a unit mentioning a unit it never imported, filed by someone
    else. *)

Definition gds_restrict (S : list path) (Θ : gdeps) : gdeps :=
  filter (fun e => existsb (path_beq (fst e)) S) Θ.

Definition gds_dom (Θ : gdeps) : list path := map fst Θ.

Definition gds_equiv (Θ Θ' : gdeps) : Prop := Θ ⊑ Θ' /\ Θ' ⊑ Θ.

Lemma existsb_path_beq : forall fp S, existsb (path_beq fp) S = true <-> In fp S.
Proof.
  intros; rewrite existsb_exists; split.
  - intros (fq & Hin & Hb); apply path_beq_true in Hb as ->; exact Hin.
  - intros Hin; exists fp; split; [ exact Hin | apply path_beq_refl ].
Qed.

Lemma gds_lookup_restrict : forall S Θ fp,
    gds_lookup (gds_restrict S Θ) fp = if existsb (path_beq fp) S then gds_lookup Θ fp else None.
Proof.
  unfold gds_restrict; induction Θ as [| [fq V] Θ IH]; intros; cbn [filter fst].
  - destruct (existsb _ _); reflexivity.
  - destruct (path_beq fp fq) eqn:Hb.
    + apply path_beq_true in Hb as <-.
      destruct (existsb (path_beq fp) S) eqn:E; cbn [gds_lookup]; rewrite ?path_beq_refl, ?IH, ?E; reflexivity.
    + destruct (existsb (path_beq fq) S); cbn [gds_lookup]; rewrite ?Hb; apply IH.
Qed.

Corollary restrict_sub : forall S Θ, gds_restrict S Θ ⊑ Θ.
Proof. intros * fp U; rewrite gds_lookup_restrict; destruct (existsb _ _); [ auto | discriminate ]. Qed.

Lemma gds_dom_lookup : forall Θ fp, In fp (gds_dom Θ) <-> gds_lookup Θ fp <> None.
Proof.
  induction Θ as [| [fq V] Θ IH]; intros; cbn [gds_dom map In fst gds_lookup].
  - split; [ contradiction | intros H; apply H; reflexivity ].
  - destruct (path_beq fp fq) eqn:Hb.
    + apply path_beq_true in Hb as ->; split; [ discriminate | auto ].
    + rewrite <- IH; split; [| auto ].
      intros [-> | H]; [ rewrite path_beq_refl in Hb; discriminate | exact H ].
Qed.

Lemma gds_dom_none : forall Θ fp, ~ In fp (gds_dom Θ) <-> gds_lookup Θ fp = None.
Proof.
  intros; rewrite gds_dom_lookup; destruct (gds_lookup Θ fp); split; intros H;
    [ exfalso; apply H; discriminate | discriminate | reflexivity | intros H'; apply H'; reflexivity ].
Qed.

Lemma gds_equiv_refl : forall Θ, gds_equiv Θ Θ.
Proof. intros; split; apply gds_sub_refl. Qed.

Lemma gds_equiv_sym : forall Θ Θ', gds_equiv Θ Θ' -> gds_equiv Θ' Θ.
Proof. intros * [H1 H2]; split; assumption. Qed.

Lemma gds_equiv_trans : forall Θ1 Θ2 Θ3, gds_equiv Θ1 Θ2 -> gds_equiv Θ2 Θ3 -> gds_equiv Θ1 Θ3.
Proof. intros * [H1 H2] [H3 H4]; split; eauto using gds_sub_trans. Qed.

(** A judgment state below [Θ], with domain [S], is equivalent to the
    restriction of [Θ] to [S]. *)
Lemma equiv_restrict : forall ΘA Θ S,
    ΘA ⊑ Θ -> (forall x, In x S <-> In x (gds_dom ΘA)) ->
    gds_equiv ΘA (gds_restrict S Θ).
Proof.
  intros * Hsub Hdom; split.
  - intros x V HV; rewrite gds_lookup_restrict.
    assert (Hx : In x S) by (apply Hdom, gds_dom_lookup; rewrite HV; discriminate).
    apply existsb_path_beq in Hx; rewrite Hx; auto.
  - intros x V HV; rewrite gds_lookup_restrict in HV.
    destruct (existsb (path_beq x) S) eqn:Hb; [| discriminate ]; apply existsb_path_beq, Hdom, gds_dom_lookup in Hb.
    destruct (gds_lookup ΘA x) as [V' |] eqn:E; [| contradiction ].
    rewrite (Hsub _ _ E) in HV; injection HV as ->; reflexivity.
Qed.

(** Term judgments and [⊢ᵍ] only read lookups, so they cross [gds_equiv] both
    ways by weakening alone. *)
Lemma equiv_gctx : forall Θ Θ' Ξ, gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ nil -> ⊢ᵍ Θ ⍮ Ξ -> ⊢ᵍ Θ' ⍮ Ξ.
Proof.
  intros * [H H'] HΘ' HΞ; apply (gstack_deps_grow _ _ H _ HΞ HΘ').
  intros mp K U Hin; pose proof (wf_gstack_frames _ _ HΞ _ _ _ Hin) as Hn.
  destruct (gds_lookup Θ' (q_unit mp)) eqn:E; [ rewrite (H' _ _ E) in Hn; discriminate | reflexivity ].
Qed.

Lemma equiv_exp : forall Θ Θ' Ξ Γ M A,
    gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ' ⍮ Ξ ⍮ Γ ⊢ M : A.
Proof.
  intros * [H _] HΞ HM; apply (deps_grow _ _ _ H); [ constructor; exact HΞ | exact HM ].
Qed.

Lemma equiv_ctx : forall Θ Θ' Ξ Γ,
    gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ -> ⊢ Θ ⍮ Ξ ⍮ Γ -> ⊢ Θ' ⍮ Ξ ⍮ Γ.
Proof.
  intros * [H _] HΞ HΓ; apply (deps_grow _ _ _ H); [ constructor; exact HΞ | exact HΓ ].
Qed.

Lemma equiv_ext : forall Θ Θ' Ξ Γ Ψ,
    gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ -> Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ -> Θ' ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ.
Proof.
  intros * [H _] HΞ HΨ; apply (deps_grow _ _ _ H); [ constructor; exact HΞ | exact HΨ ].
Qed.

Lemma equiv_modexp : forall Θ Θ' Ξ Γ E,
    gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E -> Θ' ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E.
Proof.
  intros * [H _] HΞ HE; apply (deps_grow _ _ _ H); [ constructor; exact HΞ | exact HE ].
Qed.

Lemma equiv_acc : forall Θ Θ' Ξ l, gds_equiv Θ Θ' -> acc_ok Θ Ξ l -> acc_ok Θ' Ξ l.
Proof. intros * Heq Hl; eapply acc_ok_dsub; [ exact (proj2 Heq) | exact Hl ]. Qed.

(** ** The Restriction is Well Formed

    Without strengthening: a unit of the restriction was checked against
    units below it, all imported, which the restriction below it extends. *)

(** Every filed unit of [S] was checked against units of [S] filed, as they
    are, below it. *)
Fixpoint closure_ok (S : list path) (Θ : gdeps) : Prop :=
  match Θ with
  | nil => True
  | (fp, U) :: Θ' =>
      (In fp S -> exists ΘU, ΘU ⍮ nil ⍮ q_abs fp nil ⍮ fk_module ⊢ᵍᵘ U /\ ΘU ⊑ Θ' /\ forall x, In x (gds_dom ΘU) -> In x S) /\
      closure_ok S Θ'
  end.

Theorem restrict_wf : forall S Θ, ⊢ᵍ Θ ⍮ nil -> closure_ok S Θ -> ⊢ᵍ gds_restrict S Θ ⍮ nil.
Proof.
  intros S; induction Θ as [| [fp U] Θ IH]; intros Hwf Hc; [ exact Hwf |].
  destruct Hc as [Hc Hcl]; destruct (wf_gstack_file_inv _ _ _ Hwf) as (HΘ & _ & Hn).
  assert (HR : ⊢ᵍ gds_restrict S Θ ⍮ nil) by auto.
  unfold gds_restrict; cbn [filter fst]; fold (gds_restrict S Θ).
  destruct (existsb (path_beq fp) S) eqn:Hb; [| exact HR ].
  apply existsb_path_beq in Hb; destruct (Hc Hb) as (ΘU & HU & Hsub & Hdom).
  assert (HnR : gds_lookup (gds_restrict S Θ) fp = None)
    by (rewrite gds_lookup_restrict; destruct (existsb _ _); [ exact Hn | reflexivity ]).
  apply wf_gstack_file'; [ exact HR | | exact HnR ].
  eapply unit_deps_grow; [| exact HR | exact HnR | exact HU ].
  intros x V HV; rewrite gds_lookup_restrict.
  assert (Hx : In x S) by (apply Hdom, gds_dom_lookup; rewrite HV; discriminate).
  apply existsb_path_beq in Hx; rewrite Hx; exact (Hsub _ _ HV).
Qed.

(** ** Chains and Stacks of Runs *)

Section Runs.
  Variables (load_path : path -> option string) (read : string -> option Cst.prog)
            (to_core : Cst.prog -> option cunit).
  #[local] Abbreviation run_cmd := (run_cmd load_path read to_core).
  #[local] Abbreviation run_cmds := (run_cmds load_path read to_core).
  #[local] Abbreviation run_unit := (run_unit load_path read to_core).
  #[local] Abbreviation run_ind_members := (run_ind_members load_path read to_core).

  Lemma run_dom_mono :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall x, gds_lookup Θ x <> None -> gds_lookup Θ' x <> None) /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall x, gds_lookup Θ x <> None -> gds_lookup Θ' x <> None) /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U -> True) /\
    (forall ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ', run_ind_members ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ' ->
       forall x, gds_lookup Θ x <> None -> gds_lookup Θ' x <> None).
  Proof.
    apply run_mut_ind; intros; auto.
    intros Ef; apply merge_none in Ef as [Ef _]; contradiction.
  Qed.

  (** The chain only decides whether a load is a cycle, so a run stands under
      any chain avoiding every unit it filed: what justifies sharing a unit
      loaded under one chain with an import under another. *)
  Lemma run_chain_irrel :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall ch', (forall x, In x ch' -> gds_lookup Θ' x = None) -> Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch']⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb') /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall ch', (forall x, In x ch' -> gds_lookup Θ' x = None) -> Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch']⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb') /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U ->
       forall ch', (forall x, In x (hd nil ch :: ch') -> gds_lookup Θ x = None) -> run_unit (hd nil ch :: ch') u B Rb Θ U) /\
    (forall ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ', run_ind_members ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ' ->
       forall ch', (forall x, In x ch' -> gds_lookup Θ' x = None) -> run_ind_members ch' B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ').
  Proof.
    (* what a run filed before its last step it still has after it *)
    assert (Hpre : forall ch B Rb Θ Ξ cs B1 Rb1 Θ1 Ξ1 ch', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
              (forall x, In x ch' -> gds_lookup Θ1 x = None) ->
              forall x, In x ch' -> gds_lookup Θ x = None).
    { intros * Hr Hch x Hx; destruct (gds_lookup Θ x) eqn:Ef; [ exfalso | reflexivity ].
      eapply (proj1 (proj2 run_dom_mono)); [ exact Hr | rewrite Ef; discriminate | apply Hch, Hx ]. }
    assert (Hpre' : forall ch B Rb Θ Ξ pv R pq D k xs B1 Rb1 Θ1 Ξ1 ch', run_ind_members ch B Rb Θ Ξ pv R pq D k xs B1 Rb1 Θ1 Ξ1 ->
              (forall x, In x ch' -> gds_lookup Θ1 x = None) ->
              forall x, In x ch' -> gds_lookup Θ x = None).
    { intros * Hr Hch x Hx; destruct (gds_lookup Θ x) eqn:Ef; [ exfalso | reflexivity ].
      eapply (proj2 (proj2 (proj2 run_dom_mono))); [ exact Hr | rewrite Ef; discriminate | apply Hch, Hx ]. }
    apply run_mut_ind.
    - intros; constructor; assumption.
    - intros; eapply rc_axiom; eassumption.
    - intros; econstructor; eauto.
    - intros; eapply rc_alias; eassumption.
    - intros; eapply rc_load_filed; eassumption.
    - intros ch B Rb B' Θ Ξ fp src prg u BU RbU ΘU U Hn Hnin Hl Hr Hp Ht Hu IH Hm ch' Hch.
      eapply rc_load; try eassumption.
      + intros Hin; specialize (Hch _ Hin); apply merge_none in Hch as [_ Hf].
        cbn in Hf; rewrite path_beq_refl in Hf; discriminate.
      + apply IH; intros x [<- | Hin].
        * exact (proj1 (proj2 (proj2 (run_chain_fresh load_path read to_core))) _ _ _ _ _ _ Hu _ (or_introl eq_refl)).
        * specialize (Hch _ Hin); apply merge_none in Hch as [_ Hf].
          cbn in Hf; destruct (path_beq x fp); [ discriminate | exact Hf ].
    - intros; econstructor; eauto.
    - intros * HM Hs Hc Hv Hn Hcl Hb Hf Hnil Hgn Hm IHm Hr IHr ch' Hch.
      eapply rc_ind; try eassumption; [ apply IHm; eapply Hpre; eassumption | apply IHr; exact Hch ].
    - intros; eapply rc_mdef; eassumption.
    - intros; eapply rc_builtin; eassumption.
    - intros; eapply rc_ind_alias; eassumption.
    - intros * Hfr HE Hr1 IH1 Hr2 IH2 ch' Hch.
      eapply rc_record; [ exact Hfr | exact HE | apply IH1; eapply Hpre; eassumption | apply IH2; exact Hch ].
    - intros; apply rc_eval_check; assumption.
    - intros; eapply rc_eval_infer; eassumption.
    - intros; apply rc_gen_def; assumption.
    - intros; eapply rc_gen_mod; eauto.
    - intros; constructor.
    - intros * Ha Hfa Hr1 IH1 Hr2 IH2 ch' Hch.
      econstructor; [ exact Ha | exact Hfa | apply IH1; eapply Hpre; eassumption | auto ].
    - intros fp ch B1 Rb1 B2 Rb2 imps P P3 cs Θ1 Θ2 mp K U Hi IHi Hfa Htel HP Ha Hb IHb ch' Hch.
      cbn [hd] in *; econstructor;
        [ apply IHi; eapply Hpre; eassumption | eassumption | assumption | assumption | assumption | auto ].
    - intros; constructor.
    - intros * HM Hfr HE Hr IHr Hrest IHrest ch' Hch.
      econstructor; [ exact HM | exact Hfr | exact HE | apply IHr; eapply Hpre'; eassumption | apply IHrest; exact Hch ].
  Qed.

  Lemma run_tl :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> tl Ξ' = tl Ξ /\ List.length Ξ' = List.length Ξ) /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> tl Ξ' = tl Ξ /\ List.length Ξ' = List.length Ξ) /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U -> True) /\
    (forall ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ', run_ind_members ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ' ->
       tl Ξ' = tl Ξ /\ List.length Ξ' = List.length Ξ).
  Proof.
    assert (Hadd : forall x E Ξ, tl (gs_add x E Ξ) = tl Ξ /\ List.length (gs_add x E Ξ) = List.length Ξ)
      by (intros ? ? [| [[? ?] ?] ?]; split; reflexivity).
    apply run_mut_ind; intros; auto;
      try (match goal with Hg : gens_run _ (gs_add _ _ _) _ _ |- _ =>
             destruct (gens_run_tl _ _ _ _ Hg) as [-> ->]; apply Hadd end);
      try (eapply gens_run_tl; eassumption);
      try (match goal with H : tl ?Ξ2 = tl (gs_add ?x ?E ?Ξ) /\ _ |- _ => destruct (Hadd x E Ξ) end);
      try (eapply mdefs_run_tl; eassumption); intuition congruence.
  Qed.

  (** Commands keep the stack below the frame they run in, and an empty stack
      empty. *)
  Corollary run_cmds_tail : forall ch B Rb Θ F Ξ cs B' Rb' Θ' Ξ',
      Θ ⍮ F :: Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> exists F', Ξ' = F' :: Ξ.
  Proof.
    intros * H; destruct (proj1 (proj2 run_tl) _ _ _ _ _ _ _ _ _ _ H) as [Ht Hl].
    destruct Ξ' as [| F' Ξ']; cbn in *; [ discriminate | subst; eauto ].
  Qed.

  Corollary run_cmds_empty : forall ch B Rb Θ cs B' Rb' Θ' Ξ', Θ ⍮ nil ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> Ξ' = nil.
  Proof.
    intros * H; destruct (proj1 (proj2 run_tl) _ _ _ _ _ _ _ _ _ _ H) as [_ Hl].
    destruct Ξ'; [ reflexivity | discriminate ].
  Qed.

  (** A name taken in the innermost frame stays taken: a run only adds
      entries to the frame it runs in. *)
  Lemma run_fresh_back :
    (forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall y, gs_fresh y Ξ' -> gs_fresh y Ξ) /\
    (forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
       forall y, gs_fresh y Ξ' -> gs_fresh y Ξ) /\
    (forall ch u B Rb Θ U, run_unit ch u B Rb Θ U -> True) /\
    (forall ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ', run_ind_members ch B Rb Θ Ξ pv R pq D k xs B' Rb' Θ' Ξ' ->
       forall y, gs_fresh y Ξ' -> gs_fresh y Ξ).
  Proof.
    assert (Hg : forall Θ Ξ gs Ξ', gens_run Θ Ξ gs Ξ' -> forall y, gs_fresh y Ξ' -> gs_fresh y Ξ)
      by (induction 1; intros y Hy; [ exact Hy | .. ]; exact (proj1 (gs_fresh_add_inv _ _ _ _ (IHgens_run _ Hy)))).
    assert (Hm : forall Θ b pv ds Ξ Ξ', mdefs_run Θ b pv ds Ξ Ξ' -> forall y, gs_fresh y Ξ' -> gs_fresh y Ξ)
      by (induction 1; intros y Hy; [ exact Hy | exact (proj1 (gs_fresh_add_inv _ _ _ _ (IHmdefs_run _ Hy))) ]).
    apply run_mut_ind; intros; try exact I;
      repeat match goal with H : gs_fresh _ (gs_add _ _ _) |- _ => apply gs_fresh_add_inv in H as [H _] end;
      try solve [ eauto ].
    (* a member: the rest of the group from the frame with it added *)
    match goal with
    | H : forall y, gs_fresh y ?X -> gs_fresh y (gs_add _ _ ?Z), Hy : gs_fresh ?y ?X |- gs_fresh ?y ?Z =>
        exact (proj1 (gs_fresh_add_inv _ _ _ _ (H _ Hy)))
    end.
  Qed.

  (** A command that declares a name runs only where the name is fresh. *)
  Lemma run_decl_fresh : forall ch B Rb Θ Ξ c B' Rb' Θ' Ξ' y,
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ c ⇝ Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' -> cmd_decl_name c = Some y -> gs_fresh y Ξ.
  Proof. intros * H Hn; inversion H; subst; cbn in Hn; try discriminate; injection Hn as <-; assumption. Qed.

  (** No command of a run declares a name taken where the run starts. *)
  Lemma run_cmds_taken : forall ch B Rb Θ Ξ cs B' Rb' Θ' Ξ',
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
      forall c y, In c cs -> cmd_decl_name c = Some y -> ~ gs_fresh y Ξ -> False.
  Proof.
    intros * H; induction H as [| ch B Rb Θ Ξ c0 c3 cs B1 Rb1 Θ1 Ξ1 B2 Rb2 Θ2 Ξ2 _ Hfa Hr _ IH];
      intros c y Hin Hn Ht; [ destruct Hin |].
    destruct Hin as [<- | Hin].
    - apply Ht; eapply run_decl_fresh; [ exact Hr |].
      rewrite <- Hn; exact (fill_cmd_name _ _ _ _ _ Hfa).
    - apply (IH c y Hin Hn); intros Hy; apply Ht; exact (proj1 run_fresh_back _ _ _ _ _ _ _ _ _ _ Hr _ Hy).
  Qed.

  (** After its field definitions, each field of a record is taken in its
      module's frame. *)
  Lemma record_field_cmds_taken : forall ch B Rb Θ Ξ R B' Rb' Θ' Ξ' f,
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ record_field_cmds R ⇝* Θ' ⍮ Ξ' ⍮ B' ⍮ Rb' ->
      In f (List.map fst (record_fields R)) -> ~ gs_fresh f Ξ'.
  Proof.
    intros ch B Rb Θ Ξ R B' Rb' Θ' Ξ' f; unfold record_field_cmds; generalize 0.
    revert B Rb Θ Ξ; induction (record_fields R) as [| [g T] fs IH]; intros B Rb Θ Ξ k Hr Hin; [ destruct Hin |].
    cbn in Hr; inversion Hr as [| ? ? ? ? ? ? c3 ? B1 Rb1 Θ1 Ξ1 ? ? ? ? _ Hfa Hc Hcs]; subst.
    rewrite (fill_cmd_generated _ _ _ _ _ Hfa _ eq_refl) in Hc.
    inversion Hc; subst.
    destruct Hin as [<- | Hin]; [| exact (IH _ _ _ _ _ Hcs Hin) ].
    intros Hy; apply (proj1 (proj2 run_fresh_back) _ _ _ _ _ _ _ _ _ _ Hcs) in Hy.
    apply gs_fresh_add_inv in Hy as [_ Hne]; exact (Hne eq_refl).
  Qed.

End Runs.

(** ** Lookups of a Run of a Declaration

    What [FiledConstructorTypes.rc_ind_con_types] reads off a run: the filed
    declaration and its constructors. *)

Lemma Forall2_in_left : forall {X Y} (Rl : X -> Y -> Prop) l1 l2 a,
    Forall2 Rl l1 l2 -> In a l1 -> exists b, In b l2 /\ Rl a b.
Proof.
  intros * H; induction H as [| a1 b1 l1 l2 Hab H IH]; intros Hin; [ destruct Hin |].
  destruct Hin as [<- | Hin]; [ exists b1; split; [ left; reflexivity | exact Hab ] |].
  destruct (IH Hin) as (b & Hb & Hr); exists b; split; [ right; exact Hb | exact Hr ].
Qed.

Lemma cons_lookup_nodup : forall cs c gs, NoDup (map fst cs) -> In (c, gs) cs -> cons_lookup cs c = Some gs.
Proof.
  induction cs as [| [c' gs'] cs IH]; intros * Hnd Hin; [ destruct Hin |]; destruct Hin as [[= <- <-] | Hin]; cbn.
  - rewrite String.eqb_refl; reflexivity.
  - inversion Hnd as [| ? ? Hn Hnd']; subst.
    destruct (String.eqb_spec c c') as [<- |]; [| apply IH; assumption ].
    exfalso; apply Hn, (in_map fst _ (c, gs)), Hin.
Qed.

(** ** Deciding the Rank and the Views' Members

    A group's checker computes a rank of its views ([grp_rank]) and checks
    it ([rank_check]): a declared member is of rank [0], a view one more
    than the members its blocks nest through, after as many rounds as the
    group has members.  A group accepted by the check has a rank
    ([rank_check_sound]); a group with a cycle of nest edges has none, and
    is rejected.  The members a view's [vm] lists are checked likewise
    ([vwrap_check_sound]), and so is the agreement of the views' maps
    ([view_maps_check_sound]). *)

(** The members the positions of a view's block nest through. *)
Fixpoint cargs_nest_targets (gs' gs : list carg) : list nat :=
  match gs', gs with
  | ca_arg _ :: gs1', ca_rec t :: gs1 => ptyp_mem t :: cargs_nest_targets gs1' gs1
  | _ :: gs1', _ :: gs1 => cargs_nest_targets gs1' gs1
  | _, _ => nil
  end.

Lemma cargs_nest_ok_of_targets : forall rk r gs' gs,
    (forall j, In j (cargs_nest_targets gs' gs) -> rk j < r) -> cargs_nest_ok rk r gs' gs.
Proof.
  induction gs' as [| [A' | t'] gs' IH]; intros [| [A | t] gs] H; cbn in H |- *; auto.
Qed.

(** The nest edges of the member [k] of [D]: those of the blocks of the
    members of its container's group, at a view. *)
Definition member_nest_targets (Θ : gdeps) (Ξ : gstack) (D : ind_decl) (M : imember) : list nat :=
  match im_head M with
  | mh_decl _ => nil
  | mh_view qc _ _ vm =>
      match ind_lookup Θ Ξ qc with
      | Some D' =>
          List.concat
            (List.map (fun iM =>
               match List.nth_error vm (fst iM) with
               | Some v =>
                   match ind_member D v with
                   | Some Mv =>
                       List.concat (List.map (fun cg =>
                         match ind_con Mv (fst cg) with
                         | Some gs => cargs_nest_targets (snd cg) gs
                         | None => nil
                         end) (im_cons (snd iM)))
                   | None => nil
                   end
               | None => nil
               end) (List.combine (List.seq 0 (List.length (ind_members D'))) (ind_members D')))
      | None => nil
      end
  end.

(** The rank after [m] rounds. *)
Fixpoint grp_rank_iter (Θ : gdeps) (Ξ : gstack) (D : ind_decl) (m : nat) (k : nat) : nat :=
  match m with
  | 0 => 0
  | S m' =>
      match ind_member D k with
      | Some M =>
          match im_head M with
          | mh_decl _ => 0
          | mh_view _ _ _ _ => S (List.fold_right Nat.max 0 (List.map (grp_rank_iter Θ Ξ D m') (member_nest_targets Θ Ξ D M)))
          end
      | None => 0
      end
  end.

(** The candidate rank of each member: [grp_rank_iter] after as many
    rounds as the group has members. *)
Definition grp_rank (Θ : gdeps) (Ξ : gstack) (D : ind_decl) : nat -> nat :=
  grp_rank_iter Θ Ξ D (List.length (ind_members D)).

(** The check that [grp_rank] is a rank ([view_rank_ok]): every declared
    member at rank 0, every view above each member it nests. *)
Definition rank_check (Θ : gdeps) (Ξ : gstack) (D : ind_decl) : bool :=
  let rk := grp_rank Θ Ξ D in
  List.forallb (fun kM =>
    match im_head (snd kM) with
    | mh_decl _ => Nat.eqb (rk (fst kM)) 0
    | mh_view _ _ _ _ => List.forallb (fun j => Nat.ltb (rk j) (rk (fst kM))) (member_nest_targets Θ Ξ D (snd kM))
    end) (List.combine (List.seq 0 (List.length (ind_members D))) (ind_members D)).

Lemma in_combine_seq : forall {X} (l : list X) k M, List.nth_error l k = Some M ->
    In (k, M) (List.combine (List.seq 0 (List.length l)) l).
Proof.
  intros X l; enough (H : forall s k M, List.nth_error l k = Some M -> In (s + k, M) (List.combine (List.seq s (List.length l)) l))
    by (intros k M Hk; exact (H 0 k M Hk)).
  induction l as [| x l IH]; intros s [| k] M Hk; cbn in Hk |- *; try discriminate.
  - injection Hk as <-; left; f_equal; lia.
  - right; replace (s + S k) with (S s + k) by lia; exact (IH _ _ _ Hk).
Qed.

Lemma in_concat_map : forall {X Y} (f : X -> list Y) l x y, In x l -> In y (f x) -> In y (List.concat (List.map f l)).
Proof. intros * Hx Hy; apply List.in_concat; exists (f x); split; [ apply List.in_map; exact Hx | exact Hy ]. Qed.

(** A group the check accepts has a rank. *)
Theorem rank_check_sound : forall Θ Ξ D, rank_check Θ Ξ D = true -> view_rank_ok Θ Ξ D (grp_rank Θ Ξ D).
Proof.
  intros * Hc; unfold rank_check in Hc; rewrite List.forallb_forall in Hc.
  constructor.
  - intros k Mk pm HMk Hh.
    specialize (Hc _ (in_combine_seq _ _ _ HMk)); cbn in Hc; rewrite Hh in Hc; apply Nat.eqb_eq; exact Hc.
  - intros k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs HMk Hh Hl HMi' Hvm HMv Hc' Hcv.
    specialize (Hc _ (in_combine_seq _ _ _ HMk)); cbn in Hc; rewrite Hh in Hc; rewrite List.forallb_forall in Hc.
    apply cargs_nest_ok_of_targets; intros j Hj; apply Nat.ltb_lt, Hc.
    unfold member_nest_targets; rewrite Hh, Hl.
    eapply in_concat_map; [ exact (in_combine_seq _ _ _ HMi') |]; cbn [fst snd]; rewrite Hvm, HMv.
    eapply in_concat_map; [ exact (cons_lookup_in _ _ _ Hc') |]; cbn [fst snd]; unfold ind_con in Hcv |- *; rewrite Hcv; exact Hj.
Qed.

(** The members a view's [vm] lists, checked. *)
Fixpoint cargs_corrb (vm : list nat) (gs' gs : list carg) : bool :=
  match gs', gs with
  | nil, nil => true
  | ca_rec t' :: gs1', ca_rec t :: gs1 =>
      match List.nth_error vm (ptyp_mem t') with
      | Some j => Nat.eqb j (ptyp_mem t) && Nat.eqb (ptyp_depth t') (ptyp_depth t) && cargs_corrb vm gs1' gs1
      | None => false
      end
  | ca_arg _ :: gs1', ca_arg _ :: gs1 => cargs_corrb vm gs1' gs1
  | ca_arg _ :: gs1', ca_rec _ :: gs1 => cargs_corrb vm gs1' gs1
  | _, _ => false
  end.

Lemma cargs_corrb_sound : forall vm gs' gs, cargs_corrb vm gs' gs = true -> cargs_corr vm gs' gs.
Proof.
  induction gs' as [| [A' | t'] gs' IH]; intros [| [A | t] gs] H; cbn in H |- *; try discriminate; auto.
  destruct (List.nth_error vm (ptyp_mem t')) as [j |] eqn:Hj; [| discriminate ].
  apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2].
  apply Nat.eqb_eq in H1, H2; subst; auto.
Qed.

(** The check of [vwrap_ok D D' vm]: [vm] has one entry per member of the
    container group [D'], and each listed member of [D] has the
    container member's parameter count, constructor names and argument
    shapes. *)
Definition vwrap_check (D D' : ind_decl) (vm : list nat) : bool :=
  Nat.eqb (List.length vm) (List.length (ind_members D')) &&
  List.forallb (fun iM =>
    match List.nth_error vm (fst iM) with
    | Some v =>
        match ind_member D v with
        | Some Mv =>
            Nat.eqb (im_nn Mv) (im_nn (snd iM)) &&
            (if list_eq_dec string_dec (List.map fst (im_cons Mv)) (List.map fst (im_cons (snd iM))) then true else false) &&
            List.forallb (fun cg =>
              match ind_con Mv (fst cg) with
              | Some gs => cargs_corrb vm (snd cg) gs
              | None => true
              end) (im_cons (snd iM))
        | None => false
        end
    | None => true
    end) (List.combine (List.seq 0 (List.length (ind_members D'))) (ind_members D')).

(** A view's members the check accepts are the container group's members
    at the view's arguments. *)
Theorem vwrap_check_sound : forall D D' vm, vwrap_check D D' vm = true -> vwrap_ok D D' vm.
Proof.
  intros * H; unfold vwrap_check in H; apply andb_true_iff in H as [Hl H].
  rewrite List.forallb_forall in H; constructor; [ apply Nat.eqb_eq; exact Hl |].
  intros i' Mi' v HMi' Hv.
  specialize (H _ (in_combine_seq _ _ _ HMi')); cbn [fst snd] in H; rewrite Hv in H.
  destruct (ind_member D v) as [Mv |] eqn:HMv; [| discriminate ].
  apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2].
  exists Mv; split; [ reflexivity | split; [ apply Nat.eqb_eq; exact H1 | split ] ].
  - destruct (list_eq_dec string_dec _ _) as [E |]; [ exact E | discriminate ].
  - intros c gs' gs Hin Hc; rewrite List.forallb_forall in H3; specialize (H3 _ Hin); cbn [fst snd] in H3.
    rewrite Hc in H3; exact (cargs_corrb_sound _ _ _ H3).
Qed.

(** The agreement of the views' maps, checked. *)
Definition option_nat_eq_dec : forall x y : option nat, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

(** The check of [view_map_at vm M vmv]. *)
Definition view_map_at_check (vm : list nat) (M : imember) (vmv : list nat) : bool :=
  match im_head M with
  | mh_decl _ => if list_eq_dec Nat.eq_dec vmv vm then true else false
  | mh_view _ _ _ vm'' =>
      if list_eq_dec option_nat_eq_dec (List.map (List.nth_error vm) vm'') (List.map Some vmv) then true else false
  end.

Lemma view_map_at_check_sound : forall vm M vmv, view_map_at_check vm M vmv = true -> view_map_at vm M vmv.
Proof.
  intros * H; unfold view_map_at_check in H; unfold view_map_at.
  destruct (im_head M); destruct (list_eq_dec _ _ _) as [E |]; first [ exact E | discriminate ].
Qed.

(** The check of [view_maps_coherent]: for each view, and each member of
    its container that it maps, [view_map_at_check] at that member. *)
Definition view_maps_check (Θ : gdeps) (Ξ : gstack) (D : ind_decl) : bool :=
  List.forallb (fun Mk =>
    match im_head Mk with
    | mh_decl _ => true
    | mh_view qc _ _ vm =>
        match ind_lookup Θ Ξ qc with
        | Some D' =>
            List.forallb (fun iM =>
              match List.nth_error vm (fst iM) with
              | Some v =>
                  match ind_member D v with
                  | Some Mv =>
                      match im_head Mv with
                      | mh_decl _ => true
                      | mh_view _ _ _ vmv => view_map_at_check vm (snd iM) vmv
                      end
                  | None => true
                  end
              | None => true
              end) (List.combine (List.seq 0 (List.length (ind_members D'))) (ind_members D'))
        | None => true
        end
    end) (ind_members D).

(** A group the check accepts has views whose maps agree. *)
Theorem view_maps_check_sound : forall Θ Ξ D, view_maps_check Θ Ξ D = true -> view_maps_coherent Θ Ξ D.
Proof.
  intros * H; unfold view_maps_check in H; rewrite List.forallb_forall in H.
  intros k Mk qc k' Is vm D' i' Mi' v Mv qv kv Iv vmv HMk Hh Hl HMi' Hv HMv HhMv.
  specialize (H _ (List.nth_error_In _ _ HMk)); rewrite Hh, Hl, List.forallb_forall in H.
  specialize (H _ (in_combine_seq _ _ _ HMi')); cbn [fst snd] in H; rewrite Hv, HMv, HhMv in H.
  exact (view_map_at_check_sound _ _ _ H).
Qed.
