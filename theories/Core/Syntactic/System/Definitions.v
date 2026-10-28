(** * The Syntactic Judgments

    Substitution is a meta-level operation rather than a syntactic
    constructor, so:

    - there is no [wf_exp_sub] rule and there are no [_sub] computation rules;
      how a substitution distributes over each term former, how substitutions
      compose and what the identity does are theorems about [exp_sub], proved
      in [Core.Syntactic.Substitution] and used by [rewrite];
    - the four judgments about terms (context well-formedness, typing, term
      equality and subtyping) mention no substitution judgment, and are
      mutually defined with the six about units, extensions, module
      expressions and the global context;
    - weakening and substitution typing are derived judgments: statements that
      an operation maps every binding of one context to something of the right
      type in the other.  Their closure properties (identity, extension,
      lifting, composition) are lemmas, in [Core.Syntactic.System.Structural].

    One rule is stated more generally than in the paper:

    - [wf_subtyp_pi] checks the codomains in [Γ ▹ A'] rather than [Γ ▹ A].  The
      two are interderivable given [Γ ⊢ A ≈ A' : Typeω@i] and context
      conversion, and [Γ ▹ A'] is what the soundness proof wants.

    Every judgment reads the two global components a global resolves in: the
    filed units [Θ] and the definition stack [Ξ], as in
    [Θ ⍮ Ξ ⍮ Γ ⊢ M : A].  They are indices, not parameters: no rule about terms
    changes them, but a filed unit is checked against the units before it and a
    stack frame against the frames outside it, so [⊢ᵍ Θ ⍮ Ξ] is an induction
    that varies them, as [⊢ Γ] varies [Γ]. *)

From Stdlib Require Import Lia List Classes.RelationClasses Setoid Morphisms.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Substitution Members Records.
From Mctt.Core.Syntactic.Inductives Require Export Inductives.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.

(** [Θ] at next level, as [Γ] of the short form [⊢ Γ] ([Fixed.v]), so that
    the two share their prefix and parse together. *)
Reserved Notation "⊢ Θ ⍮ Ξ ⍮ Γ" (at level 70, Θ at next level, Ξ at level 69, Γ at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ M : A" (at level 70, Ξ at level 69, Γ at level 69, M at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A" (at level 70, Ξ at level 69, Γ at level 69, M at level 69, M' at level 69, A at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A'" (at level 70, Ξ at level 69, Γ at level 69, A at level 69, A' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U" (at level 70, Ξ at level 69, Γ at level 69, U at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'" (at level 70, Ξ at level 69, Γ at level 69, Ψ at level 69, Ψ' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U'" (at level 70, Ξ at level 69, Γ at level 69, U at level 69, U' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H'" (at level 70, Ξ at level 69, Γ at level 69, H at level 69, H' at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ʷ φ : Δ" (at level 70, Ξ at level 69, Γ at level 69, φ constr at level 60, Δ at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ" (at level 70, Ξ at level 69, Γ at level 69, σ at level 69, Δ at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ" (at level 70, Ξ at level 69, Γ at level 69, σ at level 69, σ' at level 69, Δ at level 69).
Reserved Notation "Γ ∋ '#' x : A" (at level 70, x constr at level 0, A at level 69).
Reserved Notation "Γ ∋ '#' x ≔ M : A" (at level 70, x constr at level 0, M at level 69, A at level 69).
Reserved Notation "⊢ᵍ Θ ⍮ Ξ" (at level 70, Θ at level 69, Ξ at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ mp ⊢ᵉ E" (at level 70, Ξ at level 69, mp at level 69, E at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ" (at level 70, Ξ at level 69, mp at level 69, K at level 69, Δ at level 69, Φ at level 69).
Reserved Notation "Θ ⍮ Ξ ⍮ mp ⍮ K ⊢ᵍᵘ U" (at level 70, Ξ at level 69, mp at level 69, K at level 69, U at level 69).

Generalizable All Variables.

(** ** Context Lookup

    A lookup carries the weakenings that separate the binding from the top of
    the context, so [Var] below needs no shifting of its own.  The shift here is
    the weakening [↑], not the substitution [Wk]: everything that has to move a
    looked-up type past a lifted operation does so with [exp_wk_shift_wk_q] or
    [exp_wk_shift_sub_q], both of which are stated for [↑]. *)

Inductive ctx_lookup : nat -> typ -> ctx -> Prop :=
  (** The innermost entry, an assumption: its type, weakened past it *)
  | here : `(Γ ▹ A ∋ #0 : A[↑]ʷ)
  (** The innermost entry, a definition: its type, weakened past it *)
  | here_def : `(Γ ▸ A ≔ M ∋ #0 : A[↑]ʷ)
  (** The innermost entry, a definition with a module part: the type of its
      term part, weakened past it *)
  | here_dm : `(Γ ▸ₘ A ≔ M ‖ U ∋ #0 : A[↑]ʷ)
  (** An entry under one more entry: its type, weakened past that one too *)
  | there : `(Γ ∋ #n : A -> e :: Γ ∋ #(S n) : A[↑]ʷ)
where "Γ ∋ '#' x : A" := (ctx_lookup x A Γ) : type_scope.

(** The body of a definition entry, weakened to the use site like its type. *)
Inductive ctx_lookup_def : nat -> typ -> exp -> ctx -> Prop :=
  (** The innermost entry, a definition: its body and its type, weakened
      past it *)
  | def_here : `(Γ ▸ A ≔ M ∋ #0 ≔ M[↑]ʷ : A[↑]ʷ)
  (** The innermost entry, a definition with a module part: the body and
      the type of its term part, weakened past it *)
  | def_here_dm : `(Γ ▸ₘ A ≔ M ‖ U ∋ #0 ≔ M[↑]ʷ : A[↑]ʷ)
  (** A definition under one more entry: its body and type, weakened past
      that one too *)
  | def_there : `(Γ ∋ #n ≔ M : A -> e :: Γ ∋ #(S n) ≔ M[↑]ʷ : A[↑]ʷ)
where "Γ ∋ '#' x ≔ M : A" := (ctx_lookup_def x A M Γ) : type_scope.

(** ** Shapes of Units

    A telescope of parameters has assumptions only ([tele_ass], with the
    member types in [Members]). *)

(** Two bodies compared entry by entry: the same names and kinds in the same
    order, the same privacy, and transparent definitions with a body; and
    local opens at the same places, with the same items. *)
Definition entry_shape (E E' : gentry) : Prop :=
  match E, E' with
  | ge_def b pv _ (Some _), ge_def b' pv' _ (Some _) => b = true /\ b' = true /\ pv = pv'
  | ge_mod pv _, ge_mod pv' _ => pv = pv'
  | ge_def_mod pv _ _ _, ge_def_mod pv' _ _ _ => pv = pv'
  | _, _ => False
  end.

Fixpoint body_shape (Φ Φ' : gmod) : Prop :=
  match Φ, Φ' with
  | gm_nil, gm_nil => True
  | gm_ext Φ x E, gm_ext Φ' x' E' => body_shape Φ Φ' /\ x = x' /\ entry_shape E E'
  | gm_open Φ _ its, gm_open Φ' _ its' => body_shape Φ Φ' /\ its = its'
  | _, _ => False
  end.

(** The annotation of a local definition, if any, is the type it is checked
    at; without one, the type is any its body has. *)
Definition let_ann (oA : option typ) (A : typ) : Prop := oA = None \/ oA = Some A.

(** A rank [rk] of the members of a group [D]: [0] at a declared member,
    and below a view's at every member the view nests through in any block
    the eliminator at the view reads (one per member [i'] of the
    container's group, the block of the member [v] the view takes it to).
    The readback of a stuck eliminator at a view reads its branches with
    the eliminator at those members applied to fresh variables; the rank
    makes that recursion well founded. *)
Record view_rank_ok (Θ : gdeps) (Ξ : gstack) (D : ind_decl) (rk : nat -> nat) : Prop := mk_view_rank_ok
  { (** A declared member has rank [0] *)
    view_rank_ok_decl : forall k Mk pm, ind_member D k = Some Mk -> im_head Mk = mh_decl pm -> rk k = 0
    (** A view's rank is above that of every member it nests through, in
        every block the eliminator at the view reads: by a whole argument or
        along a leaf path of an argument recursive in both *)
  ; view_rank_ok_nest : forall k Mk qc k' Is vm D' i' Mi' v Mv c gs' gs, ind_member D k = Some Mk ->
      im_head Mk = mh_view qc k' Is vm -> ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' ->
      List.nth_error vm i' = Some v -> ind_member D v = Some Mv -> ind_con Mi' c = Some gs' -> ind_con Mv c = Some gs ->
      cargs_nest_ok D D' rk (rk k) gs' gs
    (** A record view's rank is above that of every member its recursive
        fields end in, at each of its constructors (it has one,
        [rview_struct_con]; the rank does not rely on that, as the check
        [rank_check] reads them all) *)
  ; view_rank_ok_rview : forall k Mk qr Is fl c gs gs1 t gs2, ind_member D k = Some Mk ->
      im_head Mk = mh_record qr Is fl -> List.In (c, gs) (im_cons Mk) -> gs = gs1 ++ ca_rec t :: gs2 ->
      rk (ptyp_mem t) < rk k }.

(** A record view's head [mh_record qr Is fl] names the record [R] filed
    at [qr], at as many arguments as it has parameters, its fields as
    [R]'s. *)
Record rview_record_facts (Θ : gdeps) (Ξ : gstack) (R : record_decl) (qr : qname) (Is : list exp) (fl : list String.string) : Prop :=
  mk_rview_record_facts
  { (** [R] is the record filed at [qr] *)
    rview_record_lookup : record_lookup Θ Ξ qr = Some R
    (** The fields are named as [R]'s, in order *)
  ; rview_record_names : fl = List.map fst (record_fields R)
    (** There are as many arguments as [R] has parameters *)
  ; rview_record_count : List.length Is = List.length (record_params R)
    (** [R]'s parameters are assumptions *)
  ; rview_record_ass : tele_ass (record_params R)
    (** The fields have distinct names, so a leaf path's projection names
        one field ([leaf_in]) *)
  ; rview_record_nodup : List.NoDup fl }.

(** The facts about the record views of a group [D] that involve no
    judgment: each is a record's at its instance ([rview_record_facts]),
    with no non-uniform parameters, its one constructor [rview_con] taking
    its fields in order; the record views come last ([rview_suffix_ok])
    and their fields end only in record views before them
    ([rview_order_ok]). *)
Record rview_struct_ok (Θ : gdeps) (Ξ : gstack) (D : ind_decl) : Prop := mk_rview_struct_ok
  { (** A record view is a filed record at as many arguments as it has
        parameters, its fields named as its head names them *)
    rview_struct_record : forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
      exists R, rview_record_facts Θ Ξ R qr Is fl
    (** It has no non-uniform parameters *)
  ; rview_struct_nparams : forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
      im_nparams Mk = nil
    (** Its one constructor is [rview_con], of one argument per field *)
  ; rview_struct_con : forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
      exists gs, im_cons Mk = (rview_con, gs) :: nil /\ List.length gs = List.length fl
    (** The record views come last *)
  ; rview_struct_suffix : rview_suffix_ok D
    (** Their fields end only in record views before them *)
  ; rview_struct_order : rview_order_ok D }.

(** [vmv] is the map of the view of [D] that a view with map [vm] takes
    the container's member [M] to: [vm] itself at a declared [M]; at a
    view [M] with map [vm''], [vm''] followed by [vm], each of its members
    one [vm] maps.  A record view is taken to a record view, never to a
    view. *)
Definition view_map_at (vm : list nat) (M : imember) (vmv : list nat) : Prop :=
  match im_head M with
  | mh_decl _ => vmv = vm
  | mh_view _ _ _ vm'' => List.map (List.nth_error vm) vm'' = List.map Some vmv
  | mh_record _ _ _ => False
  end.

(** The views of a group agree on their maps: of a view [k] with map [vm]
    and a member [i'] of its container, the member [v] of [D] [vm] takes
    [i'] to is a view of map [view_map_at vm Mi'].  The core command
    collects one view per instance, with its siblings, so the groups it
    builds have it; the eliminator at a view and the one at its container
    read a neutral alike only with it. *)
Definition view_maps_coherent (Θ : gdeps) (Ξ : gstack) (D : ind_decl) : Prop :=
  forall k Mk qc k' Is vm D' i' Mi' v Mv qv kv Iv vmv,
    ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
    ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' ->
    List.nth_error vm i' = Some v -> ind_member D v = Some Mv -> im_head Mv = mh_view qv kv Iv vmv ->
    view_map_at vm Mi' vmv.

(** ** The Mutually Defined Judgments

    Four about terms, three about units, extensions and module expressions,
    and three about the global context.  All ten are one
    [Inductive … with …]: an entry's type and body are checked by the term
    judgments, so presupposition has to be proved for all of them at once. *)

Inductive wf_ctx : gdeps -> gstack -> ctx -> Prop :=
(** The base case carries what the judgment is relative to, as [wf_gmod_nil] and
    [wf_gstack_nil] do; [wf_ctx_extend] then needs no context premise of its own,
    since typing its head presupposes one.  This is the edge that makes the block
    genuinely mutual in both directions: a term appeals to [⊢ᵍ], and [⊢ᵍ] is
    checked by the term judgments. *)
| wf_ctx_empty :
  `( ⊢ᵍ Θ ⍮ Ξ ->
     ⊢ Θ ⍮ Ξ ⍮ ⋅ )
| wf_ctx_extend :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ▹ A )
| wf_ctx_extend_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M )
(** A module slot holds a well-formed unit. *)
| wf_ctx_extend_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ▹ₘ U )
(** A definition with a module part: a definition and a module slot. *)
| wf_ctx_extend_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ▸ₘ A ≔ M ‖ U )
where "⊢ Θ ⍮ Ξ ⍮ Γ" := (wf_ctx Θ Ξ Γ) : type_scope

with wf_exp : gdeps -> gstack -> ctx -> typ -> exp -> Prop :=
(** A large universe is in the next one. *)
| wf_typ :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i : Typeω@(S i) )
(** A small universe at a level is in the small universe at the next one.
    The level is an arbitrary term, so a universe may be indexed by a
    variable. *)
| wf_univ :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ : Type⟨succl M⟩ )
(** Every type of levels is small, at the least level. *)
| wf_level :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Level@n : Type@0 )
(** A level is a literal, a successor, or a join.  [Level@n] is the type of
    the levels below ω·(n+1), so a literal is of the sorts at least its
    tier. *)
| wf_llit :
  `( fst o <= n ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o : Level@n )
(** The successor of a level. *)
| wf_succl :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ succl M : Level@n )
(** The join of two levels. *)
| wf_maxl :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl M N : Level@n )
(** The unit type is small, at the least level. *)
| wf_True :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ : Type@0 )
(** The unit's only element. *)
| wf_true :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ⋆ : ⊤ )
(** The empty type is small, at the least level. *)
| wf_False :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ : Type@0 )
(** Elimination of the empty type, at a motive over it. *)
| wf_exfalso :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ efq M return A : A[Id,,M] )
(** The type former of a declared member of a group of inductive types, of
    the type the declaration gives: a [Π] over its parameters of the
    sort. *)
| wf_ind :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some M ->
     k < ind_ndecl D ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_ind p k : ind_ty D M )
(** A constructor of a member: a [Π] over the parameters and the
    arguments of the member at the parameters.  At a view, the view's own
    parameters and arguments, into the container's member at the view's
    arguments: the normal form of a value read at a view
    ([wf_exp_eq_con_view]).  The type is a closed type, of a well-formed
    context of arguments, and the rest of the type of a recursive argument
    after any number of its shape's domains is a type, under those domains:
    all follow from the declaration, and are premises so that the semantic
    models read them off the derivation. *)
| wf_con :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some M ->
     ind_con M c = Some gs ->
     ⊢ Θ ⍮ Ξ ⍮ cargs_ctx p D M gs ++ im_params D M ->
     (forall gs1 t gs2 j, gs = gs1 ++ ca_rec t :: gs2 -> j <= List.length (ptyp_doms t) ->
        ⊢ Θ ⍮ Ξ ⍮ (sh_ctx (cargs_pat gs1) (List.firstn j (ptyp_doms t)) ++ cargs_ctx p D M gs1 ++ im_params D M)
                  ▹ ptyp_ty p D (im_nn M) (List.repeat false j ++ cargs_pat gs1) (ptyp_skip j t)) ->
     Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D k M gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_con p k c : con_ty p D k M gs )
(** The eliminator of the group at [p], at the member [m], at the
    parameters [Ps] (the group's uniform ones, then the member's
    non-uniform ones): one block per member of the group, in order, each
    with its motive under the member's non-uniform parameters and the
    scrutinee, an annotation, if any, the member's type there, and its
    branches, one per constructor in order, under the non-uniform
    parameters, the constructor's arguments and the recursive results, the
    result of an argument recursive in the member [j] being at the motive
    of [j].  The parameters are typed one by one, at the instances of their
    telescope.  The eliminator carries the uniform parameters [Us], those
    of the scrutinee's type: the scrutinee and each annotated block are at
    the members' types at them.  The record views have no block (there are
    [ind_nblk D] blocks, for the members before them), and a recursive
    argument at a record view has the results of its fields' leaf paths.
    The premises on the motives' and the branches' contexts range over
    every member, the record views too; this is harmless: a record view's
    motive context is its record type at [Us] and its branch context its
    fields with their leaf paths' results, both well formed by the
    declaration, and no block reads them. *)
| wf_elim :
  `( ind_lookup Θ Ξ p = Some D ->
     elim_grp D oq p m ->
     ind_member D m = Some Mm ->
     List.nth_error Bks m = Some bm ->
     List.length Bks = ind_nblk D ->
     List.length Ps = im_np D Mm ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
     Us = List.firstn (ind_nu D) Ps ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : Typeω@i) ->
     (forall k Mk, ind_member D k = Some Mk ->        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                     ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
          : elim_bty p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_elim oq Us m Bks M : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] )
(** A [Π] is in a universe its domain and codomain are in, small or large.
    The codomain's universe is the weakening of the domain's: a universe that
    mentions the bound variable has no name here. *)
| wf_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : U ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : U[↑]ʷ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : U )
(** A λ-abstraction, over a type. *)
| wf_fn :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ λ A M : Π A B )
(** An application, at the codomain instantiated by the argument. *)
| wf_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M $ N : B[Id,,N] )
(** A local definition, of its annotated type or of a type its body has. *)
| wf_let :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
     let_ann oA A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA M) B : C[Id,,M] )
(** A local module occupies one index, a slot holding its unit.  The body's
    type is premised to be a type, as the canonical type of [wf_mem] is:
    equivalent substitutions are moved through the body by [ζ], and the two
    sides then meet at that type. *)
| wf_let_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ C : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B : C[Id ,,ₘ me_lit U] )
(** A member: the module expression is well formed and looks the member up
    ([mdenote] of the selection) as a term, at the type the lookup reads.
    This is the only typing rule for members.  The type is premised to be a
    type, as the induction moving a typing along equivalent substitutions
    needs it, and the δ-reduct, if any, to inhabit it, as soundness needs
    it.  A filed axiom or abstract definition read bare has no δ-reduct
    ([mdesc_named]), so the premise never asks for the member itself. *)
| wf_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     (forall M, mdesc_reduct R = Some M -> Θ ⍮ Ξ ⍮ Γ ⊢ M : A) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x : A )
(** A variable, at the type the context gives it. *)
| wf_vlookup :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ #x : A )
(** The type former of a record, of the type its declaration gives: a [Π]
    over its parameters of its sort.  The facts about the declaration are
    premises, as for [wf_con], so that the semantic models read them off
    the derivation: the field names are distinct, the parameters are
    assumptions, the type is a closed type, the fields' context is well
    formed, the sort is a universe over the parameters, and each field is
    a type in the sort over the fields before it and the parameters. *)
| wf_record :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     record_lookup Θ Ξ p = Some R ->
     List.NoDup (List.map fst (record_fields R)) ->
     tele_ass (record_params R) ->
     Θ ⍮ Ξ ⍮ ⋅ ⊢ record_ty R : Typeω@i ->
     ⊢ Θ ⍮ Ξ ⍮ record_fctx R (List.length (record_fields R)) ++ record_params R ->
     Θ ⍮ Ξ ⍮ record_params R ⊢ᵤ record_sort R ->
     (forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
        Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R ⊢ T : (record_sort R)[wk_shiftn k]ʷ) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R )
(** An element of a record type [T], the type former at the parameters
    [Ns]: the fields by name in the declaration's order, each at its type
    at the parameters and the values of the fields before it.  [T] is
    premised to be a type, as the type of [wf_mem] is. *)
| wf_tuple :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ T : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R ->
     record_lookup Θ Ξ p = Some R ->
     List.length Ns = List.length (record_params R) ->
     (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
     List.map fst fs = List.map fst (record_fields R) ->
     (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
        Θ ⍮ Ξ ⍮ Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs : T )
(** A field, at its type at the parameters and the projections of the
    fields before it.  That type is premised to be a type, as the type of
    [wf_mem] is. *)
| wf_proj :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : apps_exp (a_record p) Ns ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R ->
     record_lookup Θ Ξ p = Some R ->
     List.length Ns = List.length (record_params R) ->
     (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
     List.nth_error (record_fields R) k = Some (f, U) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k M)] : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_proj f M : U[sb_of_list Id (Ns ++ record_pre R k M)] )
(** Subsumption: a term is at every type above its type. *)
| wf_exp_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     (** This premise is needed for soundness.  It is asymmetric: only [A'] is
         checked.  Checking [A] as well would make even
         [Γ ⊢ Typeω@0[↑]ʷ : Typeω@1] underivable, since weakening it would require
         [Γ ⊢ Typeω@1[↑]ʷ : Typeω@2], which requires [Γ ⊢ Typeω@2[↑]ʷ : Typeω@3], and
         so on. *)
     Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A' )
where "Θ ⍮ Ξ ⍮ Γ ⊢ M : A" := (wf_exp Θ Ξ Γ A M) : type_scope

with wf_exp_eq : gdeps -> gstack -> ctx -> typ -> exp -> exp -> Prop :=
(** *** Congruence rules *)
| wf_exp_eq_typ_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i ≈ Typeω@i : Typeω@(S i) )
| wf_exp_eq_univ_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ ≈ Type⟨M'⟩ : Type⟨succl M⟩ )
| wf_exp_eq_level_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Level@n ≈ Level@n : Type@0 )
| wf_exp_eq_llit_cong :
  `( fst o <= n ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o ≈ 𝕃ᵒ o : Level@n )
| wf_exp_eq_succl_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ succl M ≈ succl M' : Level@n )
| wf_exp_eq_maxl_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl M N ≈ maxl M' N' : Level@n )
(** *** The Level Equations

    Levels are a join semilattice with a least element and an inflationary
    successor that distributes over the join; the literal [ω·a + b] is the
    [b]-th successor of the limit [ω·a], and the limit [ω·(n+1)] is above
    every level of sort [n] (absorption).  These are the equations of
    Danielsson–Favier–Kubánek Fig. 2 and absorption, and they are complete
    for the canonical forms of [Core.Syntactic.Levels.Levels]: two levels are equal
    exactly when they have the same canonical form. *)
| wf_exp_eq_llit_succl :
  `( a <= n ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ(a, S b) ≈ succl (𝕃ᵒ(a, b)) : Level@n )
| wf_exp_eq_maxl_absorb :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl M (𝕃ᵒ(S n, 0)) ≈ 𝕃ᵒ(S n, 0) : Level@(S n) )
| wf_exp_eq_maxl_zero :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃@0) M ≈ M : Level@n )
| wf_exp_eq_maxl_assoc :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ P : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl (maxl M N) P ≈ maxl M (maxl N P) : Level@n )
| wf_exp_eq_maxl_comm :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl M N ≈ maxl N M : Level@n )
| wf_exp_eq_maxl_idem :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl M M ≈ M : Level@n )
| wf_exp_eq_succl_maxl :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ succl (maxl M N) ≈ maxl (succl M) (succl N) : Level@n )
| wf_exp_eq_maxl_succl :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl M (succl M) ≈ succl M : Level@n )
| wf_exp_eq_True_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ ≈ ⊤ : Type@0 )
| wf_exp_eq_true_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ⋆ ≈ ⋆ : ⊤ )
| wf_exp_eq_False_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ ≈ ⊥ : Type@0 )
| wf_exp_eq_exfalso_cong :
  `( Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ ⊥ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ⊥ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ efq M return A ≈ efq M' return A' : A[Id,,M] )
| wf_exp_eq_ind_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some M ->
     k < ind_ndecl D ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_ind p k ≈ a_ind p k : ind_ty D M )
| wf_exp_eq_con_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     ind_member D k = Some M ->
     ind_con M c = Some gs ->
     ⊢ Θ ⍮ Ξ ⍮ cargs_ctx p D M gs ++ im_params D M ->
     Θ ⍮ Ξ ⍮ ⋅ ⊢ con_ty p D k M gs : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_con p k c ≈ a_con p k c : con_ty p D k M gs )
(** The eliminator, its blocks and its scrutinee varying: the blocks are
    compared position by position, their annotations each checked, their
    branches position by position, at the left motives.  The groups as
    written may differ (one of them taken from the scrutinee's type). *)
| wf_exp_eq_elim_cong :
  `( ind_lookup Θ Ξ p = Some D ->
     elim_grp D oq p m ->
     elim_grp D oq' p m ->
     ind_member D m = Some Mm ->
     List.nth_error Bks m = Some bm ->
     List.length Bks = ind_nblk D ->
     List.length Bks' = ind_nblk D ->
     List.length Ps = im_np D Mm ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
     List.length Ps' = im_np D Mm ->
     (forall k P P' T, nth_error Ps k = Some P -> nth_error Ps' k = Some P' ->
        nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T -> Θ ⍮ Ξ ⍮ Γ ⊢ P ≈ P' : T) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
     Us = List.firstn (ind_nu D) Ps ->
     Us' = List.firstn (ind_nu D) Ps' ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_nm b = S (im_nn Mk)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks' k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : Typeω@i) ->
     (forall k Mk b b', ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b ≈ eb_motive b' : Typeω@i) ->
     (forall k Mk, ind_member D k = Some Mk ->        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
     (forall k b b', List.nth_error Bks k = Some b -> List.nth_error Bks' k = Some b' ->
        List.map fst (eb_brs b) = List.map fst (eb_brs b')) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                     ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
     (forall k Mk b b' i c gs n B B', ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        List.nth_error Bks' k = Some b' ->
        nth_error (eb_brs b) i = Some (c, n, B) -> nth_error (eb_brs b') i = Some (c, n, B') ->
        ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B ≈ B'
          : elim_bty p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_elim oq Us m Bks M ≈ a_elim oq' Us' m Bks' M' : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] )
| wf_exp_eq_pi_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A : U ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : U ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : U[↑]ʷ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ≈ Π A' B' : U )
| wf_exp_eq_fn_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M ≈ M' : B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ λ A M ≈ λ A' M' : Π A B )
| wf_exp_eq_app_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M $ N ≈ M' $ N' : B[Id,,N] )
| wf_exp_eq_let_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B ≈ B' : C ->
     let_ann oA A ->
     let_ann oA' A' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA M) B ≈ a_let (b_def oA' M') B' : C[Id,,M] )
(** The right-hand side is typed in its own context, which differs from the
    left's by the unit. *)
| wf_exp_eq_let_mod_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B ≈ B' : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B ≈ ℓₘ U' in B' : C[Id ,,ₘ me_lit U] )
(** Members of equivalent module expressions, both looked up as terms, at
    the type the left one is looked up at.  The right-hand side is premised
    to be typed there, as presupposition needs it before any lemma relating
    what equivalent module expressions look up. *)
| wf_exp_eq_mem_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     mdenote Θ Ξ Γ (me_mem H' x) R' ->
     mdesc_type R' = Some A' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H' x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ a_mem H' x : A )
| wf_exp_eq_var :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ #x ≈ #x : A )
(** *** Computation rules *)
| wf_exp_eq_pi_beta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ M : B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ (λ A M) $ N ≈ M[Id,,N] : B[Id,,N] )
(** [ι]: the eliminator on a constructor is the constructor's branch, at
    the non-uniform parameters, the arguments and the recursive results
    ([elim_ihs]): the eliminator at a recursive argument, and at one of a
    function shape [λ x. elim (f x)].  The arguments are typed one by one,
    at the instances of their telescope at the parameters. *)
| wf_exp_eq_elim_iota :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     ind_lookup Θ Ξ p = Some D ->
     elim_grp D oq p m ->
     ind_member D m = Some Mm ->
     List.nth_error Bks m = Some bm ->
     ind_con Mm c = Some gs ->
     List.length Bks = ind_nblk D ->
     List.length Ps = im_np D Mm ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
     List.length As = List.length gs ->
     (forall k N T, nth_error As k = Some N -> nth_error (tele_insts (cargs_ctx p D Mm gs) (sb_of_list Id Ps) As) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊢ N : T) ->
     Us = List.firstn (ind_nu D) Ps ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : Typeω@i) ->
     (forall k Mk, ind_member D k = Some Mk ->        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                     ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
          : elim_bty p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     brs_lookup (eb_brs bm) c = Some (n, B) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_elim oq Us m Bks (apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                                    (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As))
       ≈ B[sb_of_list Id (List.skipn (ind_nu D) Ps ++ As ++
                          elim_ihs p D oq (List.firstn (ind_nu D) Ps) Bks (sb_of_list Id Ps) (im_nn Mm) gs As)]
       : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++
                          apps (a_con (fst (im_ref p m Mm)) (snd (im_ref p m Mm)) c)
                            (im_pre Mm (List.firstn (ind_nu D) Ps) ++ List.skipn (ind_nu D) Ps ++ As) :: nil)] )
(** The eliminator at a view is the eliminator of the view's own group at
    the container's member, its blocks those of the members of this group
    that are the container's group's members at the view's arguments
    ([view_wrap], E1′): a stuck eliminator at a view is a stuck one of the
    container, at the container's uniform parameters (the view's
    arguments) when the container's group has views too. *)
| wf_exp_eq_elim_view :
  `( ind_lookup Θ Ξ p = Some D ->
     elim_grp D oq p m ->
     ind_member D m = Some Mm ->
     im_head Mm = mh_view qc k' Is vm ->
     ind_lookup Θ Ξ qc = Some D' ->
     view_wrap_ok D D' vm ->
     List.nth_error Bks m = Some bm ->
     List.length Bks = ind_nblk D ->
     List.length Ps = im_np D Mm ->
     (forall k P T, nth_error Ps k = Some P -> nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T ->
        Θ ⍮ Ξ ⍮ Γ ⊢ P : T) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
     Us = List.firstn (ind_nu D) Ps ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_nm b = S (im_nn Mk)) ->
     (forall k Mk b Z, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> eb_ann b = Some Z ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ▹ Z
                     ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        Θ ⍮ Ξ ⍮ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ++ Γ ⊢ eb_motive b : Typeω@i) ->
     (forall k Mk, ind_member D k = Some Mk ->        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps) ≈ elim_mctx p D k Mk (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b, ind_member D k = Some Mk -> List.nth_error Bks k = Some b -> brs_names (im_cons Mk) (eb_brs b)) ->
     (forall k Mk c gs, ind_member D k = Some Mk -> ind_con Mk c = Some gs ->
        Θ ⍮ Ξ ⍮ Γ ⊢ˣ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)
                     ≈ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps)) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        n = (im_nn Mk + List.length gs + cargs_nrec D gs)%nat) ->
     (forall k Mk b c gs n B, ind_member D k = Some Mk -> List.nth_error Bks k = Some b ->
        ind_con Mk c = Some gs -> In (c, n, B) (eb_brs b) ->
        Θ ⍮ Ξ ⍮ elim_bctx p D Mk gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ ⊢ B
          : elim_bty p D k Mk c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_elim oq Us m Bks M
       ≈ a_elim (Some qc) (im_pre Mm (List.firstn (ind_nu D) Ps)) k'
           (view_wrap p D D' vm (List.firstn (ind_nu D) Ps) Bks) M
       : (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)] )
(** A constructor of a view at the group's uniform parameters [Us] is the
    container's constructor at the view's arguments there, both sides at
    the same type. *)
| wf_exp_eq_con_view :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_view qc k Is vm ->
     List.length Us = ind_nu D ->
     Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp (a_con p j c) (Us ++ Ms) : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp (a_con qc k c) (im_pre Mj Us ++ Ms) : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp (a_con p j c) (Us ++ Ms) ≈ apps_exp (a_con qc k c) (im_pre Mj Us ++ Ms) : A )
(** The constructor of a record view at the group's uniform parameters
    [Us] and the fields [Ms] is the tuple of the fields, by name, at the
    record type at the view's instance there, both sides at the same
    type. *)
| wf_exp_eq_con_rview :
  `( ind_lookup Θ Ξ p = Some D ->
     ind_member D j = Some Mj ->
     im_head Mj = mh_record qr Is fl ->
     List.length Us = ind_nu D ->
     List.length Ms = List.length fl ->
     Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp (a_con p j c) (Us ++ Ms) : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple (apps_exp (a_record qr) (im_pre Mj Us)) (List.combine fl Ms) : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ apps_exp (a_con p j c) (Us ++ Ms) ≈ a_tuple (apps_exp (a_record qr) (im_pre Mj Us)) (List.combine fl Ms) : A )
(** [ζ]: a local definition is substituted into its body. *)
| wf_exp_eq_let_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ▸ A ≔ M ⊢ B : C ->
     let_ann oA A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def oA M) B ≈ B[Id,,M] : C[Id,,M] )
(** [ζ] for local modules: the slot is replaced by the unit. *)
| wf_exp_eq_let_mod_zeta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ C : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ₘ U ⊢ B : C ->
     Θ ⍮ Ξ ⍮ Γ ⊢ ℓₘ U in B ≈ B[Id ,,ₘ me_lit U] : C[Id ,,ₘ me_lit U] )
(** [δ] for members: a member is the δ-reduct the lookup reads: the body of
    a transparent definition at the arguments, the name of a filed axiom or
    abstract definition at them, or a type former. *)
| wf_exp_eq_mem_delta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H ->
     mdenote Θ Ξ Γ (me_mem H x) R ->
     mdesc_type R = Some A ->
     mdesc_reduct R = Some M ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_mem H x ≈ M : A )
(** [δ] for local definitions: a defined variable is its body.  It is stated
    at every depth, since weakening moves a definition arbitrarily deep. *)
| wf_exp_eq_var_delta :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ #x ≈ M : A )
(** *** Uniqueness rule *)
| wf_exp_eq_fn_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : Π A B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ λ A M[↑]ʷ $ #0 : Π A B )
| wf_exp_eq_true_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊤ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ ⋆ : ⊤ )
(** *** Records *)
(** The record type former is equal to itself, with the premises of
    [wf_record]. *)
| wf_exp_eq_record_cong :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     record_lookup Θ Ξ p = Some R ->
     List.NoDup (List.map fst (record_fields R)) ->
     tele_ass (record_params R) ->
     Θ ⍮ Ξ ⍮ ⋅ ⊢ record_ty R : Typeω@i ->
     ⊢ Θ ⍮ Ξ ⍮ record_fctx R (List.length (record_fields R)) ++ record_params R ->
     Θ ⍮ Ξ ⍮ record_params R ⊢ᵤ record_sort R ->
     (forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
        Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R ⊢ T : (record_sort R)[wk_shiftn k]ʷ) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_record p ≈ a_record p : record_ty R )
(** Record elements of equal types with equal fields, both sides typed.
    The parameters are typed and the field names are the declaration's, as
    in [wf_tuple]: the semantic models relate the two tuples at the record
    type only at parameters they read as valid. *)
| wf_exp_eq_tuple_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs : T ->
     Θ ⍮ Ξ ⍮ Γ ⊢ T ≈ T' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
     record_lookup Θ Ξ p = Some R ->
     List.length Ns = List.length (record_params R) ->
     (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
     List.map fst fs = List.map fst (record_fields R) ->
     List.map fst fs' = List.map fst fs ->
     (forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
        List.nth_error (record_fields R) k = Some (f, U) ->
        Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T' fs' : T ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs ≈ a_tuple T' fs' : T )
(** The fields of equal records, at the field's type at the parameters and
    the projections of the fields before it, with the premises of
    [wf_proj]: the semantic models relate the two projections only at the
    field's type; at any other type they are equal by subsumption.  The
    right-hand side is premised at that type, as for [wf_exp_eq_tuple_cong]:
    its own type is at the projections of [M'], equal to it only by this
    rule at the fields before. *)
| wf_exp_eq_proj_cong :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : apps_exp (a_record p) Ns ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_record p : record_ty R ->
     record_lookup Θ Ξ p = Some R ->
     List.length Ns = List.length (record_params R) ->
     (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A ->
        Θ ⍮ Ξ ⍮ Γ ⊢ N : A) ->
     List.nth_error (record_fields R) k = Some (f, U) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k M)] : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_proj f M' : U[sb_of_list Id (Ns ++ record_pre R k M)] ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_proj f M ≈ a_proj f M' : U[sb_of_list Id (Ns ++ record_pre R k M)] )
(** Field-β: the field of a record element is its first field so named.
    Both sides are premised to be of the type: the field's type at the
    element's projections and at its fields are equal only by the field-β
    of the fields before it. *)
| wf_exp_eq_field_beta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs : T ->
     field_lookup fs f = Some M ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_proj f (a_tuple T fs) : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_proj f (a_tuple T fs) ≈ M : A )
(** η for records: an element is the tuple of its projections.  The
    parameters are all given, as in [wf_tuple]: the semantic models read the
    record type only at all its parameters. *)
| wf_exp_eq_record_eta :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M : apps_exp (a_record p) Ns ->
     record_lookup Θ Ξ p = Some R ->
     List.length Ns = List.length (record_params R) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple (apps_exp (a_record p) Ns) (record_eta_fields R M) : apps_exp (a_record p) Ns ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ a_tuple (apps_exp (a_record p) Ns) (record_eta_fields R M) : apps_exp (a_record p) Ns )
(** *** Subsumption and the PER rules *)
| wf_exp_eq_subtyp :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i ->
     (** This premise mirrors the one of [wf_exp_subtyp]. *)
     Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A' )
| wf_exp_eq_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M' ≈ M : A )
| wf_exp_eq_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M' ≈ M'' : A ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M'' : A )
where "Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A" := (wf_exp_eq Θ Ξ Γ A M M') : type_scope

(** *** Subtyping *)
with wf_subtyp : gdeps -> gstack -> ctx -> typ -> typ -> Prop :=
| wf_subtyp_refl :
  (** This premise lets the presupposition lemmas be proved independently: it
      gives presupposition for the right-hand side directly. *)
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ⊆ M' )
| wf_subtyp_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ M ⊆ M' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M' ⊆ M'' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M ⊆ M'' )
| wf_subtyp_univ :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     i < j ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Typeω@i ⊆ Typeω@j )
(** A small universe below one at a larger level.  The order on levels is
    [maxl M M' ≈ M'], which is decidable on canonical forms
    ([Core.Syntactic.Levels.Levels.lvl_le]) and never the order on realisers. *)
| wf_subtyp_suniv :
  (** The two typings let the presupposition lemmas be proved independently,
      as in [wf_subtyp_refl]. *)
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ maxl M M' ≈ M' : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ ⊆ Type⟨M'⟩ )
(** A type of levels is below every type of levels of a larger sort: every
    level of a sort is a level of each larger one. *)
| wf_subtyp_level :
  `( m <= n ->
     ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Level@m ⊆ Level@n )
(** A small universe below every large one. *)
| wf_subtyp_small_large :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ ⊆ Typeω@i )
| wf_subtyp_pi :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ▹ A' ⊢ B ⊆ B' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ⊆ Π A' B' )
where "Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A'" := (wf_subtyp Θ Ξ Γ A A') : type_scope

(** *** Universes

    [Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U]: [U] is a universe, large or small at a level of
    [Γ]. *)
with wf_is_univ : gdeps -> gstack -> ctx -> typ -> Prop :=
| wf_is_univ_large :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵤ Typeω@i )
| wf_is_univ_small :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ L : Level@n ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵤ Type⟨L⟩ )
where "Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U" := (wf_is_univ Θ Ξ Γ U) : type_scope



(** ** Modules

    Equivalence of modules is pointwise: two units are equivalent when their
    entries are, one by one and in the same order, and two module expressions
    when their parts are.  Well-formedness is the reflexive instance.

    [Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'] compares two extensions of [Γ] entry by entry.  An
    entry is compared in the left extension; the right one's entry is also
    typed in the right extension, so that presupposition needs no context
    conversion. *)
with wf_ext_eq : gdeps -> gstack -> ctx -> ctx -> ctx -> Prop :=
| wf_ext_eq_nil :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ ⋅ ≈ ⋅ )
| wf_ext_eq_ass :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▹ A ≈ Ψ' ▹ A' )
| wf_ext_eq_def :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ M' : A' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▸ A ≔ M ≈ Ψ' ▸ A' ≔ M' )
| wf_ext_eq_mod :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ᵘ U' ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▹ₘ U ≈ Ψ' ▹ₘ U' )
(** A definition with a module part: as a definition and as a module
    slot. *)
| wf_ext_eq_dm :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ A ≈ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ M : A ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ M ≈ M' : A ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ A' : Typeω@i ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ M' : A' ->
     Θ ⍮ Ξ ⍮ Ψ ++ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Ψ' ++ Γ ⊢ᵘ U' ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ▸ₘ A ≔ M ‖ U ≈ Ψ' ▸ₘ A' ≔ M' ‖ U' )
where "Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ'" := (wf_ext_eq Θ Ξ Γ Ψ Ψ') : type_scope

(** Units.  Each side of a body unit is well formed where it stands: its
    body, read as the entries its local opens generate ([body_xp]), and its
    parameters form an extension of [Γ], and the target of each open is a
    module there.
    The two sides have the same shape as written, opens at the same places
    with the same items, and as expanded ([body_shape]), and are compared
    entry by entry through their expansions; the targets of the opens are
    compared pairwise, filled in like the entries.  Each entry is compared with the entries
    before it filled in ([gm_fill]: a definition by its body, a module by
    its unit), in the left parameters' context, and each filled-in entry of
    the right side is typed in the right parameters' context, as the parts of
    an extension are: so the comparison never reads one side's entries in the
    other side's body.  An entry is compared through its parts: its term
    part ([entry_tm]) as a definition is, and its module part
    ([entry_unit]) as a module is, so a definition with a module part is
    compared as both.  Every entry can be filled in:
    a local body has no bodiless definition and no inductive type.  The
    level of the type of the definition named [y] is [lv y]. *)
with wf_unit_eq : gdeps -> gstack -> ctx -> gunit -> gunit -> Prop :=
| wf_unit_eq_body :
  `( body_xp Θ Ξ (Δ ++ Γ) Φ Φx ->
     body_xp Θ Ξ (Δ' ++ Γ) Φ' Φx' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx ++ Δ ≈ body_ctx Φx ++ Δ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ˣ body_ctx Φx' ++ Δ' ≈ body_ctx Φx' ++ Δ' ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A[σ] : Typeω@(lv y)) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ A[σ] ≈ A'[σ'] : Typeω@(lv y)) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M[σ] : A[σ]) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ M[σ] ≈ M'[σ'] : A[σ]) ->
     (forall y Φ0 E U Φ0' E' U' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ U[σ]ᵘ ≈ U'[σ']ᵘ) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ A'[σ'] : Typeω@(lv y)) ->
     (forall y Φ0 E A M Φ0' E' A' M' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_tm E' = Some (A', M') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ M'[σ'] : A'[σ']) ->
     (forall y Φ0 E U Φ0' E' U' σ σ',
        gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
        gm_prefix_upto Φx' y = Some (gm_ext Φ0' y E') -> entry_unit E' = Some U' ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ᵘ U'[σ']ᵘ ≈ U'[σ']ᵘ) ->
     (forall k Ψ H, nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> Θ ⍮ Ξ ⍮ Ψ ++ Δ ++ Γ ⊢ᵐ H ≈ H) ->
     (forall k Ψ' H', nth_error (body_opens Φ' Φx') k = Some (Ψ', H') -> Θ ⍮ Ξ ⍮ Ψ' ++ Δ' ++ Γ ⊢ᵐ H' ≈ H') ->
     (forall k Φ0 H Φ0' H' σ σ',
        nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) ->
        nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ H[σ]ᵐ ≈ H'[σ']ᵐ) ->
     (forall k Φ0 H Φ0' H' σ σ',
        nth_error (body_opens_at Φ Φx) k = Some (Φ0, H) ->
        nth_error (body_opens_at Φ' Φx') k = Some (Φ0', H') ->
        gm_fill Φ0 = Some σ -> gm_fill Φ0' = Some σ' ->
        Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ᵐ H'[σ']ᵐ ≈ H'[σ']ᵐ) ->
     tele_ass Δ ->
     tele_ass Δ' ->
     List.length Δ = List.length Δ' ->
     body_shape Φ Φ' ->
     body_shape Φx Φx' ->
     List.NoDup (gm_names Φ) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ' Φ' )
| wf_unit_eq_alias :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ' ->
     tele_ass Δ ->
     tele_ass Δ' ->
     Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵐ E ≈ E' ->
     Θ ⍮ Ξ ⍮ Δ' ++ Γ ⊢ᵐ E' ≈ E' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias E) ≈ gu_mk Δ' (md_alias E') )
(** An alias of a literal is the literal over both telescopes, the alias's
    outermost: the merge lookup performs ([udenote_alias], [mdesc_up]).  The
    alias's parameters form an extension of [Γ], and the literal is a unit
    under them. *)
| wf_unit_eq_flatten :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ˣ Δ ≈ Δ ->
     tele_ass Δ ->
     Θ ⍮ Ξ ⍮ Δ ++ Γ ⊢ᵘ gu_mk Δ' D ≈ gu_mk Δ' D ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk Δ (md_alias (me_lit (gu_mk Δ' D))) ≈ gu_mk (Δ' ++ Δ) D )
| wf_unit_eq_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U' ≈ U )
| wf_unit_eq_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U' ≈ U'' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U'' )
where "Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U'" := (wf_unit_eq Θ Ξ Γ U U') : type_scope

(** Module expressions.  A module expression is a module when the module
    part of what it denotes has a telescope ([mdesc_mod_tele]), and an argument is
    checked against the outermost parameter of that telescope
    ([tele_view]): a module is applied to at most as many arguments as it has
    parameters.  Both arguments are typed, as the parts of an extension are,
    and so is the parameter's type. *)
with wf_modexp_eq : gdeps -> gstack -> ctx -> modexp -> modexp -> Prop :=
(** *** Congruence *)
(** A loaded unit or an open frame. *)
| wf_me_unit :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     gc_unit Θ Ξ (me_unit fp) = Some TΦ ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_unit fp ≈ me_unit fp )
| wf_me_var :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_var x ≈ me_var x )
| wf_me_lit :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_lit U ≈ me_lit U' )
(** A selection: on both sides the member is a module, by what the
    selection denotes ([mdenote]), the module part having a telescope. *)
| wf_me_mem :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     mdesc_mod_tele R = Some T ->
     mdenote Θ Ξ Γ (me_mem H' y) R' ->
     mdesc_mod_tele R' = Some T' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H' y )
(** An application: the argument is checked against the outermost
    parameter of the telescope of what the module expression denotes. *)
| wf_me_app :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     mdenote Θ Ξ Γ H R ->
     mdesc_mod_tele R = Some T ->
     tele_view T = Some (B, T1) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B : Typeω@i ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : B ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N ≈ N' : B ->
     mdenote Θ Ξ Γ H' R' ->
     mdesc_mod_tele R' = Some T' ->
     tele_view T' = Some (B', T1') ->
     Θ ⍮ Ξ ⍮ Γ ⊢ B' : Typeω@j ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N' : B' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H' N' )
(** *** [δ] *)
(** A slot is its unit. *)
| wf_me_delta_slot :
  `( ⊢ Θ ⍮ Ξ ⍮ Γ ->
     Γ ∋ #x ≔ₘ U ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_var x ≈ me_lit U )
(** A module member is the unit the module part of what the selection looks
    up stands for ([mdesc_unit]): a body module of a filed module, the filed
    module at its own path; an alias, its target's; a module of a local
    body, its literal with the entries before it filled in. *)
| wf_me_delta_sel :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_mem H y ≈ me_mem H y ->
     mdenote Θ Ξ Γ (me_mem H y) R ->
     mdesc_mod R = Some Rm ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_mem H y ≈ mdesc_unit Rm )
(** *** [β] *)
(** A literal body or alias given its outermost parameter is the literal
    instantiated; an alias with no parameter is its target. *)
| wf_me_beta_body :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass X :: nil) (md_body sm_open Φ) ≈ gu_mk (Δ ++ ce_ass X :: nil) (md_body sm_open Φ) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) (md_body sm_open Φ))) N
       ≈ me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_body sm_open (gmod_sub Φ (sb_qn (length Δ) (Id,,N))))) )
| wf_me_beta_alias :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵘ gu_mk (Δ ++ ce_ass X :: nil) (md_alias E) ≈ gu_mk (Δ ++ ce_ass X :: nil) (md_alias E) ->
     Θ ⍮ Ξ ⍮ Γ ⊢ N : X ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_app (me_lit (gu_mk (Δ ++ ce_ass X :: nil) (md_alias E))) N
       ≈ me_lit (gu_mk (tele_sub Δ (Id,,N)) (md_alias E[sb_qn (length Δ) (Id,,N)]ᵐ)) )
| wf_me_beta_alias0 :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ E ≈ E ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ me_lit (gu_mk nil (md_alias E)) ≈ E )
| wf_me_sym :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H' ≈ H )
| wf_me_trans :
  `( Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H' ≈ H'' ->
     Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H'' )
where "Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H'" := (wf_modexp_eq Θ Ξ Γ H H') : type_scope

(** ** Well-formedness of the Global Context

    Part of the same mutual definition: an entry's type and body are checked by
    the term judgments, and a use of a global appeals to [⊢ᵍ Θ ⍮ Ξ].

    A unit is checked against the units filed before it, and a frame against
    the frames outside it, which is why both components are indices of the whole
    block.

    A member of a parameterized module is checked in the telescope of
    parameters it lives under, and stored generalized over it ([ctx_pi],
    [ctx_fn]).  [ge_mod] records only the parameters it adds to that telescope;
    a [gunit] records all of it, which is why a unit is checked at [⋅].

    Canonicity is part of well-formedness: [wf_gmod_ext] asks for freshness, so a
    well-formed context resolves deterministically without a separate
    condition. *)

(** An entry is checked against the current module, which is the head of [Ξ]:
    that frame is what [wf_gmod_ext] pushed, and it carries the parameters and the
    members declared so far.  The local context is the telescope of all the
    frames' parameters, [gs_tele Ξ]: parameters are ordinary λ-variables.  A
    definition is stored generalized over that telescope, so what is filed is
    closed, and nothing has to be done to it when it is read anywhere else.  [mp]
    is the entry's own module path, which a nested module's frame is named by. *)

with wf_gentry : gdeps -> gstack -> qname -> gentry -> Prop :=
(** A definition or an axiom: its type is a type, and its body, if it has
    one, carries the type. *)
| wf_gentry_def :
  `( Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i ->
     (forall M, oM = Some M -> Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A) ->
     Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_def b pv (ctx_pi (gs_tele Ξ) A) (option_map (ctx_fn (gs_tele Ξ)) oM) )
(** An internal module, under the parameters [Δ'] it declares. *)
| wf_gentry_mod :
  `( Θ ⍮ Ξ ⍮ mp ⍮ fk_module ⍮ Δ' ⊢ᵍᵐ Φ ->
     Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_body pv Δ' Φ )
(** An alias, under the parameters [Δ] it declares.  It is filed with its
    full telescope, so that it is closed; its target is checked, and its
    arguments with it, where it is declared. *)
| wf_gentry_alias :
  `( tele_ass Δ ->
     Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
     Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
     Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_mod pv (gu_mk (Δ ++ gs_tele Ξ) (md_alias E)) )
(** A group of inductive types, at its first member, before the members of
    its module: its declaration, with uniform parameters [Δ] over the
    frames' parameters.  The sort is checked in the uniform parameters; for
    each member, declared or view, its non-uniform parameters at the sort,
    a non-recursive argument of a constructor in the member's parameters
    and the non-recursive arguments before it, at the sort, and a recursive
    argument by its shape: each domain of a function shape there and under
    the domains before it, at the sort, and the non-uniform parameters of
    the member it ends in under all its domains.  A view of the declared
    member [k'] of the filed group at [qc] at [Is]: [Is] are that group's
    uniform parameters, its siblings are the views [vm] lists, its
    non-uniform parameters those of the container's member at [Is], its
    constructors the container's at [Is] (the view equations), classified
    for this group ([cargs_corr]), and its sort in this group's.  The types are not filed yet, so no argument mentions
    them but as a recursive argument: positivity is by construction.  No
    type of the declaration has a free module variable ([decl_mvc]), as no
    type in a context of assumptions. *)
| wf_gentry_ind_nil :
  `( ind_uparams D = Δ ++ gs_tele Ξ ->
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
     (** each view's instance [Is] is [IsS] with the members as variables
         ([grp_sctx]); the instance and the view equations are checked
         there, as the group is not filed yet *)
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
     (** the view equations, for each member [i'] of the container's group
         and the member [v] of this group the view takes it to: the
         non-uniform parameters, the arguments of each constructor, and, of an
         argument recursive in both, each domain of the shapes and the
         non-uniform parameters of the members they end in; the container's
         parameters at the view's instance are also typed at the view's
         types, as presupposition needs them before the sides of an equation
         are typed *)
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
     (** the record views: the facts without a judgment
         ([rview_struct_ok]); each instance is [IsS] with the members as
         variables, and, there, each instance typed at the record's
         parameters, the record's fields at it equal to the view's
         classified ones (the record view equations), and the record's
         sort at it in the group's *)
     rview_struct_ok Θ Ξ D ->
     (forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
        Is = List.map (fun I => I[grp_sb mp D]) (IsS k)) ->
     (forall k Mk qr Is fl R j I T, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
        record_lookup Θ Ξ qr = Some R -> nth_error (IsS k) j = Some I ->
        nth_error (tele_insts (record_params R) Id (IsS k)) j = Some T ->
        Θ ⍮ Ξ ⍮ grp_sctx D ⊢ I : T) ->
     (forall k Mk qr Is fl R c gs, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
        record_lookup Θ Ξ qr = Some R -> im_cons Mk = (c, gs) :: nil ->
        Θ ⍮ Ξ ⍮ grp_sctx D ⊢ˣ tele_sub (record_fctx R (List.length (record_fields R))) (sb_of_list Id (IsS k))
                              ≈ scargs_ctx D IsS Mk gs) ->
     (forall k Mk qr Is fl R, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
        record_lookup Θ Ξ qr = Some R ->
        Θ ⍮ Ξ ⍮ grp_sctx D ⊢ (record_sort R)[sb_of_list Id (IsS k)] ⊆ (ind_sort D)[self_wk D 0]ʷ) ->
     (** the record view's type is in the group's sort.  This follows in
         principle from the instance's typing and the sort premise by the
         record's formation rule, but that rule holds at the record's own
         position in the global context, and moving it into [grp_sctx D]
         needs a weakening of the global context the presupposition does
         not have; so it is a premise *)
     (forall k Mk qr Is fl, ind_member D k = Some Mk -> im_head Mk = mh_record qr Is fl ->
        Θ ⍮ Ξ ⍮ grp_sctx D ⊢ apps_exp (a_record qr) (IsS k) : (ind_sort D)[self_wk D 0]ʷ) ->
     (** a view's map takes its container's record views to record views
         of the same record, at instances equal to the container's at the
         view's instance *)
     (forall k Mk qc k' Is vm D' i' Mi' v q'' Is'' fl'', ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
        ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_record q'' Is'' fl'' ->
        nth_error vm i' = Some v ->
        exists Mv X, ind_member D v = Some Mv /\ im_head Mv = mh_record q'' X fl'' /\ List.length X = List.length Is'') ->
     (forall k Mk qc k' Is vm D' i' Mi' v q'' Is'' fl'' R'' Mv X fl j' C C' T,
        ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
        ind_lookup Θ Ξ qc = Some D' -> ind_member D' i' = Some Mi' -> im_head Mi' = mh_record q'' Is'' fl'' ->
        record_lookup Θ Ξ q'' = Some R'' ->
        nth_error vm i' = Some v -> ind_member D v = Some Mv -> im_head Mv = mh_record q'' X fl ->
        nth_error (IsS v) j' = Some C ->
        nth_error (List.map (fun I => I[sb_of_list Id (IsS k)]) Is'') j' = Some C' ->
        nth_error (tele_insts (record_params R'') Id Is'') j' = Some T ->
        Θ ⍮ Ξ ⍮ grp_sctx D ⊢ C ≈ C' : T[sb_of_list Id (IsS k)]) ->
     (** the views' nesting is well founded *)
     (exists rk, view_rank_ok Θ Ξ D rk) ->
     (** each view's members are those of the container's group, as the
         eliminator at the view reads them *)
     (forall k Mk qc k' Is vm, ind_member D k = Some Mk -> im_head Mk = mh_view qc k' Is vm ->
        exists D', ind_lookup Θ Ξ qc = Some D' /\ view_wrap_ok D D' vm) ->
     (** the views agree on their maps *)
     view_maps_coherent Θ Ξ D ->
     Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_ind pv mp 0 D ⋄ )
(** A later declared member of a group, before the members of its module:
    the group is filed at its first member, [y0], an entry of the same
    module before it. *)
| wf_gentry_ind_mem_nil :
  `( ind_uparams D = Δu ++ gs_tele ((mq, Kq, gu_body Δ Φ0) :: Ξ) ->
     tele_ass (ind_uparams D) ->
     ⊢ Θ ⍮ (mq, Kq, gu_body Δ Φ0) :: Ξ ⍮ ind_uparams D ->
     gm_entry Φ0 (y0 :: nil) = Some (ge_ind pv0 (qname_in mq y0) 0 D Φm) ->
     ind_lookup Θ ((mq, Kq, gu_body Δ Φ0) :: Ξ) (qname_in mq y0) = Some D ->
     ind_member D k = Some Mk ->
     0 < k ->
     k < ind_ndecl D ->
     im_head Mk = mh_decl (qname_in mq y) ->
     Θ ⍮ (mq, Kq, gu_body Δ Φ0) :: Ξ ⍮ qname_in mq y ⊢ᵉ ge_ind pv (qname_in mq y0) k D ⋄ )
(** A declared member of a group with the body of its module: the body
    is checked as an ordinary module over the uniform parameters, in the
    member's open frame, which carries the declaration ([fk_ind]); the
    declaration itself is checked where the module starts
    ([wf_gmod_ind_nil]).  The member is filed only when its frame
    closes. *)
| wf_gentry_ind_body :
  `( ind_uparams D = Δu ++ gs_tele Ξ ->
     Θ ⍮ Ξ ⍮ mp ⍮ fk_ind pq k D ⍮ Δu ⊢ᵍᵐ Φ ->
     Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_ind pv pq k D Φ )
(** A definition with a module part: its term part as a transparent
    definition is ([wf_gentry_def]), over the frames' parameters, and its
    module part as an alias under the parameters [Δ] it declares is
    ([wf_gentry_alias]); both are filed closed. *)
| wf_gentry_def_mod :
  `( Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i ->
     Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
     tele_ass Δ ->
     Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ˣ Δ ≈ Δ ->
     Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ⊢ᵐ E ≈ E ->
     Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_def_mod pv (ctx_pi (gs_tele Ξ) A) (ctx_fn (gs_tele Ξ) M) (gu_mk (Δ ++ gs_tele Ξ) (md_alias E)) )
(** A record type, with parameters [Δ] over the frames' parameters, before
    the members of its module: its sort is a universe over the parameters,
    its field names are distinct, and each field is a type in the sort
    over the fields before it and the parameters.  The record is not filed
    while its fields are checked, so no field mentions it: records are not
    recursive, by construction.  No type of the declaration has a free
    module variable ([record_mvc]), as no type in a context of assumptions. *)
| wf_gentry_record :
  `( record_params R = Δ ++ gs_tele Ξ ->
     tele_ass (record_params R) ->
     record_mvc R ->
     Θ ⍮ Ξ ⍮ record_params R ⊢ᵤ record_sort R ->
     List.NoDup (List.map fst (record_fields R)) ->
     (forall k f T, List.nth_error (record_fields R) k = Some (f, T) ->
        Θ ⍮ Ξ ⍮ record_fctx R k ++ record_params R ⊢ T : (record_sort R)[wk_shiftn k]ʷ) ->
     Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_record pv mp R ⋄ )
(** A record type with the body of its module: the body is checked as an
    ordinary module over the record's own parameters and then a value of
    the record ([record_self]), in the record's open frame, which carries
    the declaration ([fk_record]); the declaration itself is checked where
    the module starts ([wf_gmod_record_nil]).  The record is filed only
    when its frame closes. *)
| wf_gentry_record_body :
  `( record_params R = Δ ++ gs_tele Ξ ->
     Θ ⍮ Ξ ⍮ mp ⍮ fk_record R ⍮ ce_ass (record_self mp R) :: Δ ⊢ᵍᵐ Φ ->
     Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_record pv mp R Φ )
where "Θ ⍮ Ξ ⍮ mp ⊢ᵉ E" := (wf_gentry Θ Ξ mp E) : type_scope

(** The module at path [mp], of kind [K], with own parameters [Δ], a
    telescope over the frames' parameters [gs_tele Ξ]. *)
with wf_gmod : gdeps -> gstack -> qname -> frame_kind -> ctx -> gmod -> Prop :=
(** An ordinary module, before its members *)
| wf_gmod_nil :
  `( tele_ass Δ ->
     ⊢ Θ ⍮ Ξ ⍮ Δ ++ gs_tele Ξ ->
     Θ ⍮ Ξ ⍮ mp ⍮ fk_module ⍮ Δ ⊢ᵍᵐ ⋄ )
(** The module of the declared member [k] of the group [D] at [pq], before
    its members: the member's declaration, checked as an entry with an
    empty module ([wf_gentry_ind_nil], [wf_gentry_ind_mem_nil]), and the
    module's parameters, the uniform ones, over the frames' parameters,
    as [wf_gmod_nil] has them.  A member is declared in an enclosing
    frame, so its module is no unit. *)
| wf_gmod_ind_nil :
  `( tele_ass Δ ->
     ⊢ Θ ⍮ (mq, Kq, Uq) :: Ξ ⍮ Δ ++ gs_tele ((mq, Kq, Uq) :: Ξ) ->
     Θ ⍮ (mq, Kq, Uq) :: Ξ ⍮ mp ⊢ᵉ ge_ind pv pq k D ⋄ ->
     ind_uparams D = Δ ++ gs_tele ((mq, Kq, Uq) :: Ξ) ->
     Θ ⍮ (mq, Kq, Uq) :: Ξ ⍮ mp ⍮ fk_ind pq k D ⍮ Δ ⊢ᵍᵐ ⋄ )
(** The module of the record type [R], before its members: the record's
    declaration, checked as an entry with an empty module
    ([wf_gentry_record]), and the module's parameters: the record's own,
    over the frames' parameters, as [wf_gmod_nil] has them, and then a
    value of the record ([record_self]).  The value's type names the
    record, found only inside the record's frame, so it is typed there
    (as [wf_gs_tele] shows), not here ([frame_params]).  A record is
    declared in an enclosing frame, so its module is no unit. *)
| wf_gmod_record_nil :
  `( tele_ass Δ ->
     ⊢ Θ ⍮ (mq, Kq, Uq) :: Ξ ⍮ Δ ++ gs_tele ((mq, Kq, Uq) :: Ξ) ->
     Θ ⍮ (mq, Kq, Uq) :: Ξ ⍮ mp ⊢ᵉ ge_record pv mp R ⋄ ->
     record_params R = Δ ++ gs_tele ((mq, Kq, Uq) :: Ξ) ->
     Θ ⍮ (mq, Kq, Uq) :: Ξ ⍮ mp ⍮ fk_record R ⍮ ce_ass (record_self mp R) :: Δ ⊢ᵍᵐ ⋄ )
(** The entry is checked against the members declared before it: the module so
    far is [gu_mk Δ Φ], pushed as the innermost frame under its own path,
    of the module's kind. *)
| wf_gmod_ext :
  `( Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ ->
     Θ ⍮ (mp, K, gu_body Δ Φ) :: Ξ ⍮ qname_in mp x ⊢ᵉ E ->
     gm_fresh x Φ ->
     Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ ⊳ x ↦ E )
where "Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ" := (wf_gmod Θ Ξ mp K Δ Φ) : type_scope

(** The filed units [Θ] and the stack [Ξ] of open frames, innermost first.
    A frame is checked against the frames outside it, and a unit is filed by
    closing the only open frame, named by its path, after which it is checked
    against the units filed before it.  So a unit sees no stack and not
    itself, and a [qu_rel] index inside a frame counts outward from there.
    Freshness ([frame_fresh]) makes a path filed at most once. *)

with wf_gstack : gdeps -> gstack -> Prop :=
| wf_gstack_nil : ⊢ᵍ nil ⍮ nil
| wf_gstack_file :
  `( ⊢ᵍ Θ ⍮ (q_abs fp nil, fk_module, U) :: nil ->
     ⊢ᵍ (fp, U) :: Θ ⍮ nil )
| wf_gstack_cons :
  `( ⊢ᵍ Θ ⍮ Ξ ->
     Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ ->
     frame_fresh Θ Ξ mp ->
     ⊢ᵍ Θ ⍮ (mp, K, gu_body Δ Φ) :: Ξ )
where "⊢ᵍ Θ ⍮ Ξ" := (wf_gstack Θ Ξ) : type_scope.

(** The schemes are [Minimality], not [Induction]: nothing in this development
    is proved by a statement that mentions the derivation itself, and dropping
    the derivation arguments keeps the goals of a mutual induction readable and
    within reach of [mauto].

    A [Scheme] may name any subset of the block, and the judgments it leaves
    out survive as ordinary hypotheses in the cases that mention them. *)

Scheme wf_ctx_mut_ind := Minimality for wf_ctx Sort Prop
with wf_exp_mut_ind := Minimality for wf_exp Sort Prop
with wf_exp_eq_mut_ind := Minimality for wf_exp_eq Sort Prop
with wf_subtyp_mut_ind := Minimality for wf_subtyp Sort Prop
with wf_is_univ_mut_ind := Minimality for wf_is_univ Sort Prop
with wf_ext_eq_mut_ind := Minimality for wf_ext_eq Sort Prop
with wf_unit_eq_mut_ind := Minimality for wf_unit_eq Sort Prop
with wf_modexp_eq_mut_ind := Minimality for wf_modexp_eq Sort Prop.
Combined Scheme syntactic_wf_mut_ind from
  wf_ctx_mut_ind,
  wf_exp_mut_ind,
  wf_exp_eq_mut_ind,
  wf_subtyp_mut_ind,
  wf_is_univ_mut_ind,
  wf_ext_eq_mut_ind,
  wf_unit_eq_mut_ind,
  wf_modexp_eq_mut_ind.

(** The three-way scheme is the shape of [wk_preserves_wf], [sub_preserves_wf]
    and [sub_eq_preserves_exp]: each of them
    transports the three judgments about a fixed context along an operation,
    and says nothing about context well-formedness.  Generating it as a scheme
    in its own right (rather than combining the four-way one) means it takes
    exactly three predicates: the [⊢ Γ] premises of rules like [wf_typ] survive
    as ordinary hypotheses. *)

Scheme wf_exp_mind := Minimality for wf_exp Sort Prop
with wf_exp_eq_mind := Minimality for wf_exp_eq Sort Prop
with wf_subtyp_mind := Minimality for wf_subtyp Sort Prop
with wf_is_univ_mind := Minimality for wf_is_univ Sort Prop
with wf_ext_eq_mind := Minimality for wf_ext_eq Sort Prop
with wf_unit_eq_mind := Minimality for wf_unit_eq Sort Prop
with wf_modexp_eq_mind := Minimality for wf_modexp_eq Sort Prop.
Combined Scheme syntactic_wf_mut_ind' from
  wf_exp_mind,
  wf_exp_eq_mind,
  wf_subtyp_mind,
  wf_is_univ_mind,
  wf_ext_eq_mind,
  wf_unit_eq_mind,
  wf_modexp_eq_mind.

(** The two-way scheme is the shape of the soundness fundamental theorem: the
    gluing model relates contexts and terms, and its
    subtyping case consumes [Γ ⊢ A ⊆ A'] syntactically, so neither of the
    two equality judgments needs a predicate. *)

Scheme wf_ctx_mind' := Minimality for wf_ctx Sort Prop
with wf_exp_mind' := Minimality for wf_exp Sort Prop
with wf_is_univ_mind' := Minimality for wf_is_univ Sort Prop.
Combined Scheme syntactic_wf_ctx_exp_mut_ind from
  wf_ctx_mind',
  wf_exp_mind',
  wf_is_univ_mind'.

(** The global subset: the shape of [wf_global_canon] and
    [gsub_preserves_global]. *)

Scheme wf_gentry_mut_ind := Minimality for wf_gentry Sort Prop
with wf_gmod_mut_ind := Minimality for wf_gmod Sort Prop.
Combined Scheme global_wf_mut_ind from
  wf_gentry_mut_ind,
  wf_gmod_mut_ind.

(** The whole block, for a statement that has to cross between the two
    directions — the term judgments appeal to [⊢ᵍ Θ ⍮ Ξ] and the global ones to
    typing, so presupposition is proved here or not at all. *)

Scheme wf_ctx_mut_ind_all := Minimality for wf_ctx Sort Prop
with wf_exp_mut_ind_all := Minimality for wf_exp Sort Prop
with wf_exp_eq_mut_ind_all := Minimality for wf_exp_eq Sort Prop
with wf_subtyp_mut_ind_all := Minimality for wf_subtyp Sort Prop
with wf_is_univ_mut_ind_all := Minimality for wf_is_univ Sort Prop
with wf_ext_eq_mut_ind_all := Minimality for wf_ext_eq Sort Prop
with wf_unit_eq_mut_ind_all := Minimality for wf_unit_eq Sort Prop
with wf_modexp_eq_mut_ind_all := Minimality for wf_modexp_eq Sort Prop
with wf_gentry_mut_ind_all := Minimality for wf_gentry Sort Prop
with wf_gmod_mut_ind_all := Minimality for wf_gmod Sort Prop
with wf_gstack_mut_ind_all := Minimality for wf_gstack Sort Prop.
Combined Scheme wf_mut_ind_all from
  wf_ctx_mut_ind_all,
  wf_exp_mut_ind_all,
  wf_exp_eq_mut_ind_all,
  wf_subtyp_mut_ind_all,
  wf_is_univ_mut_ind_all,
  wf_ext_eq_mut_ind_all,
  wf_unit_eq_mut_ind_all,
  wf_modexp_eq_mut_ind_all,
  wf_gentry_mut_ind_all,
  wf_gmod_mut_ind_all,
  wf_gstack_mut_ind_all.

(** ** Units

    A unit filed at a level, or a frame of the stack, is a body checked by
    [⊢ᵍᵐ]: [⊢ᵍᵘ] is not a judgment of its own, but this definition, which the
    block states inline ([wf_gstack_cons]).  Two further
    projections are presuppositions, in [Presup]: [⊢ Θ ⍮ Ξ ⍮ gu_params U] of
    [⊢ᵍᵐ], hence of [⊢ᵍᵘ], and [⊢ᵍ Θ ⍮ nil] of [⊢ᵍ Θ ⍮ Ξ]. *)

#[warnings="-cannot-define-projection"]
Record wf_gunit (Θ : gdeps) (Ξ : gstack) (mp : qname) (K : frame_kind) (U : gunit) : Prop := mk_wf_gunit
  { (** The unit's parameters *)
    wf_gunit_params : ctx
    (** The unit's body *)
  ; wf_gunit_body : gmod
    (** The unit is a body module *)
  ; wf_gunit_eq : U = gu_body wf_gunit_params wf_gunit_body
    (** Its body is a module of kind [K] *)
  ; wf_gunit_wf : Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ wf_gunit_params ⊢ᵍᵐ wf_gunit_body }.
Notation "Θ ⍮ Ξ ⍮ mp ⍮ K ⊢ᵍᵘ U" := (wf_gunit Θ Ξ mp K U) : type_scope.

Lemma wf_gunit_intro : forall Θ Ξ mp K Δ Φ, Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ Δ ⊢ᵍᵐ Φ -> Θ ⍮ Ξ ⍮ mp ⍮ K ⊢ᵍᵘ gu_body Δ Φ.
Proof. intros; econstructor; [ reflexivity | eassumption ]. Qed.

Lemma wf_gunit_mod : forall Θ Ξ mp K U, Θ ⍮ Ξ ⍮ mp ⍮ K ⊢ᵍᵘ U -> Θ ⍮ Ξ ⍮ mp ⍮ K ⍮ gu_params U ⊢ᵍᵐ gu_mod U.
Proof. intros * [Δ Φ -> H]; exact H. Qed.

(** The unit form of the two constructors that file one. *)

Lemma wf_gstack_cons' : forall Θ Ξ mp K U,
    ⊢ᵍ Θ ⍮ Ξ -> Θ ⍮ Ξ ⍮ mp ⍮ K ⊢ᵍᵘ U -> frame_fresh Θ Ξ mp -> ⊢ᵍ Θ ⍮ (mp, K, U) :: Ξ.
Proof. intros * ? [Δ Φ -> ?] ?; apply wf_gstack_cons; assumption. Qed.

Lemma wf_gstack_cons_inv : forall Θ Ξ mp K U,
    ⊢ᵍ Θ ⍮ (mp, K, U) :: Ξ -> ⊢ᵍ Θ ⍮ Ξ /\ Θ ⍮ Ξ ⍮ mp ⍮ K ⊢ᵍᵘ U /\ frame_fresh Θ Ξ mp.
Proof. inversion 1; subst; eauto using wf_gunit_intro. Qed.

(** Filing, from the premises of the frame it closes. *)
Lemma wf_gstack_file' : forall Θ fp U,
    ⊢ᵍ Θ ⍮ nil -> Θ ⍮ nil ⍮ q_abs fp nil ⍮ fk_module ⊢ᵍᵘ U -> gds_lookup Θ fp = None -> ⊢ᵍ (fp, U) :: Θ ⍮ nil.
Proof. intros * ? ? ?; apply wf_gstack_file, wf_gstack_cons'; [ assumption | assumption | split; [ assumption | reflexivity ] ]. Qed.

Lemma wf_gstack_file_inv : forall Θ fp U,
    ⊢ᵍ (fp, U) :: Θ ⍮ nil -> ⊢ᵍ Θ ⍮ nil /\ Θ ⍮ nil ⍮ q_abs fp nil ⍮ fk_module ⊢ᵍᵘ U /\ gds_lookup Θ fp = None.
Proof.
  inversion 1; subst.
  match goal with H : ⊢ᵍ _ ⍮ _ :: nil |- _ => destruct (wf_gstack_cons_inv _ _ _ _ _ H) as (? & ? & [? _]) end; auto.
Qed.

#[export]
Hint Constructors wf_ctx wf_exp wf_exp_eq wf_subtyp wf_is_univ ctx_lookup ctx_lookup_def : mctt.


Lemma let_ann_none : forall A, let_ann None A.
Proof. intros; left; reflexivity. Qed.

Lemma let_ann_some : forall A, let_ann (Some A) A.
Proof. intros; right; reflexivity. Qed.

#[export]
Hint Resolve let_ann_none let_ann_some : mctt.

Ltac solve_let_ann := first [ apply let_ann_some | eassumption | apply let_ann_none ].

(** The annotations of the local definitions in context, as the two cases. *)
Ltac destruct_let_ann :=
  repeat match goal with H : let_ann _ _ |- _ => destruct H as [-> | ->] end; cbv beta iota in *.

#[export]
Hint Constructors wf_ext_eq wf_unit_eq wf_modexp_eq : mctt.

(** The two instances of [wf_gentry_def], with a body and without (an
    axiom), whose conclusions name the entry as it is filed. *)
Lemma wf_gentry_def_body : forall Θ Ξ mp b pv A M i,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_def b pv (ctx_pi (gs_tele Ξ) A) (Some (ctx_fn (gs_tele Ξ) M)).
Proof.
  intros * HA HM; change (Some (ctx_fn (gs_tele Ξ) M)) with (option_map (ctx_fn (gs_tele Ξ)) (Some M)).
  eapply wf_gentry_def; [ exact HA | intros ? [= <-]; exact HM ].
Qed.

Lemma wf_gentry_def_axiom : forall Θ Ξ mp b pv A i,
    Θ ⍮ Ξ ⍮ gs_tele Ξ ⊢ A : Typeω@i ->
    Θ ⍮ Ξ ⍮ mp ⊢ᵉ ge_def b pv (ctx_pi (gs_tele Ξ) A) None.
Proof.
  intros * HA; change (@None exp) with (option_map (ctx_fn (gs_tele Ξ)) None).
  eapply wf_gentry_def; [ exact HA | discriminate ].
Qed.

#[export]
Hint Constructors wf_gentry wf_gmod wf_gstack : mctt.
#[export]
Hint Resolve wf_gentry_def_body wf_gentry_def_axiom : mctt.
#[export]
Hint Resolve wf_gunit_intro : mctt.

(** ** Weakening and Substitution Typing

    These are the derived judgments.
    They are records, not inductive relations: a weakening or a substitution is
    well-typed exactly when it sends each binding of its source context to
    something of the correspondingly transported type in its target.  Nothing
    here is recursive, so none of it belongs in the mutual block above; the
    price is that closure under the operations ([Id], [_,,_], [q], [_⨟_]) has to
    be proved, which is what [wf_wk_id]–[wf_wk_compose] and
    [wf_sub_id]–[wf_sub_q] do. *)

Record wf_wk (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (φ : wk) : Prop := wf_wk_intro
{ wf_wk_dom : ⊢ Θ ⍮ Ξ ⍮ Γ
; wf_wk_cod : ⊢ Θ ⍮ Ξ ⍮ Δ
; wf_wk_lookup : forall x A, Δ ∋ #x : A -> Γ ∋ #(φ x) : A[φ]ʷ
(** A renaming sends a definition to the same definition. *)
; wf_wk_lookup_def : forall x A M, Δ ∋ #x ≔ M : A -> Γ ∋ #(φ x) ≔ M[φ]ʷ : A[φ]ʷ
(** A renaming sends a module slot to a slot of the same unit. *)
; wf_wk_lookup_mod : forall x U, Δ ∋ #x ≔ₘ U -> Γ ∋ #(φ x) ≔ₘ gunit_wk U φ
}.
Notation "Θ ⍮ Ξ ⍮ Γ ⊢ʷ φ : Δ" := (wf_wk Θ Ξ Γ Δ φ) : type_scope.

Record wf_sub (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (σ : sub) : Prop := wf_sub_intro
{ wf_sub_dom : ⊢ Θ ⍮ Ξ ⍮ Γ
; wf_sub_cod : ⊢ Θ ⍮ Ξ ⍮ Δ
; wf_sub_apply : forall x A, Δ ∋ #x : A -> Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ] : A[σ]
(** A substitution sends a definition to something equal to its body. *)
; wf_sub_apply_def : forall x A M, Δ ∋ #x ≔ M : A -> Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ] ≈ M[σ] : A[σ]
(** A substitution sends a module slot to the unit it holds, transported:
    as a well-formed literal (the module part of an [se_mod] or an
    [se_dm]), or as a slot holding that unit. *)
; wf_sub_apply_mod : forall x U, Δ ∋ #x ≔ₘ U ->
    (sentry_modexp (σ x) = me_lit U[σ]ᵘ /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U[σ]ᵘ ≈ U[σ]ᵘ) \/ exists y, σ x = se_var y /\ Γ ∋ #y ≔ₘ U[σ]ᵘ
}.
Notation "Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ" := (wf_sub Θ Ξ Γ Δ σ) : type_scope.

(** The type at which the images are equated is [A[σ]]; it could equally be
    [A[σ']], since [sub_eq_preserves_exp] shows the two are equal types. *)
Record wf_sub_eq (Θ : gdeps) (Ξ : gstack) (Γ Δ : ctx) (σ σ' : sub) : Prop := wf_sub_eq_intro
{ wf_sub_eq_left : Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ
; wf_sub_eq_right : Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ' : Δ
; wf_sub_eq_apply : forall x A, Δ ∋ #x : A -> Θ ⍮ Ξ ⍮ Γ ⊢ #x[σ] ≈ #x[σ'] : A[σ]
(** A module slot is sent to equal module expressions. *)
; wf_sub_eq_apply_mod : forall x U, Δ ∋ #x ≔ₘ U -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ sentry_modexp (σ x) ≈ sentry_modexp (σ' x)
}.
Notation "Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ ≈ σ' : Δ" := (wf_sub_eq Θ Ξ Γ Δ σ σ') : type_scope.

(** The projections are not registered in [mctt]: each of them
    has a conclusion ([⊢ Γ], [Γ ⊢ˢ σ : Δ]) that the corresponding introduction
    rule also produces, so the pair would let [eauto] cycle. [Lemmas.v] states
    the presuppositions it actually wants as separate lemmas. *)

(** [wf_wk], [wf_sub] and [wf_sub_eq] are all invariant under pointwise equality
    of the operation: the operation only ever occurs applied to an index or
    applied to an expression, and both of those respect pointwise equality
    ([exp_wk_Proper], [exp_sub_Proper]). *)

#[export]
Instance wf_wk_Proper Θ Ξ Γ Δ : Proper (wk_eq ==> iff) (wf_wk Θ Ξ Γ Δ).
Proof.
  assert (forall φ ψ, wk_eq φ ψ -> Θ ⍮ Ξ ⍮ Γ ⊢ʷ φ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ʷ ψ : Δ) as Himp.
  {
    intros φ ψ Heq [? ? Hlk Hlkd Hlkm].
    econstructor; try eassumption.
    - intros x A ?.
      replace (ψ x) with (φ x) by apply Heq.
      rewrite <- Heq.
      now apply Hlk.
    - intros x A M ?.
      replace (ψ x) with (φ x) by apply Heq.
      rewrite <- !Heq.
      now apply Hlkd.
    - intros x U ?.
      replace (ψ x) with (φ x) by apply Heq.
      rewrite <- Heq.
      now apply Hlkm.
  }
  intros φ ψ Heq; split; apply Himp; [ assumption | now symmetry ].
Qed.

#[export]
Instance wf_sub_Proper Θ Ξ Γ Δ : Proper (sb_eq ==> iff) (wf_sub Θ Ξ Γ Δ).
Proof.
  assert (forall σ τ, sb_eq σ τ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ σ : Δ -> Θ ⍮ Ξ ⍮ Γ ⊢ˢ τ : Δ) as Himp.
  {
    intros σ τ Heq [? ? Hap Hapd Hapm].
    econstructor; try eassumption.
    - intros x A ?.
      rewrite <- !Heq.
      now apply Hap.
    - intros x A M ?.
      rewrite <- !Heq.
      now apply Hapd.
    - intros x U HU.
      rewrite <- (Heq x), <- (gunit_sub_sb_eq U σ τ Heq).
      now apply Hapm.
  }
  intros σ τ Heq; split; apply Himp; [ assumption | now symmetry ].
Qed.

(** ** Immediate & Independent Presuppositions *)

(** The two forms of a literal's typing the proofs below name: at its own
    sort, the least one, and at sort [0] for a finite one. *)
Lemma wf_llit_ord : forall {Θ Ξ Γ o},
    ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o : Level@(fst o).
Proof. intros; apply wf_llit; [ reflexivity | assumption ]. Qed.

Lemma wf_llit_fin : forall {Θ Ξ Γ n},
    ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃@n : Level.
Proof. intros; apply wf_llit; [ reflexivity | assumption ]. Qed.

#[export]
Hint Resolve wf_llit_ord wf_llit_fin : mctt.
(** The side condition of [wf_llit] and of the literal equations: the tier
    of a literal is at most the sort. *)
#[export]
Hint Extern 1 (fst _ <= _) => cbn [fst]; lia : mctt.

(** A small universe is a type of every large universe. *)
Lemma wf_univ_large_tm : forall {Θ Ξ Γ M i n},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ : Typeω@i.
Proof.
  intros * HΓ HM; eapply wf_exp_subtyp;
    [ eapply wf_univ, HM | apply wf_typ, HΓ | eapply wf_subtyp_small_large; [ exact HΓ | apply wf_succl, HM ] ].
Qed.

Lemma wf_univ_large : forall {Θ Ξ Γ o i},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ o⟩ : Typeω@i.
Proof. intros; eapply wf_univ_large_tm; [ assumption | apply wf_llit_ord; assumption ]. Qed.

(** The base types are types of every large universe. *)
Lemma wf_True_large : forall {Θ Ξ Γ i}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ : Typeω@i.
Proof. intros; eapply wf_exp_subtyp; [ apply wf_True | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_False_large : forall {Θ Ξ Γ i}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ : Typeω@i.
Proof. intros; eapply wf_exp_subtyp; [ apply wf_False | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_level_large : forall {Θ Ξ Γ i n}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ Level@n : Typeω@i.
Proof. intros; eapply wf_exp_subtyp; [ apply wf_level | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_exp_eq_level_cong_large : forall {Θ Ξ Γ i n}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ Level@n ≈ Level@n : Typeω@i.
Proof. intros; eapply wf_exp_eq_subtyp; [ apply wf_exp_eq_level_cong | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_exp_eq_True_cong_large : forall {Θ Ξ Γ i}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ⊤ ≈ ⊤ : Typeω@i.
Proof. intros; eapply wf_exp_eq_subtyp; [ apply wf_exp_eq_True_cong | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_exp_eq_False_cong_large : forall {Θ Ξ Γ i}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ ⊥ ≈ ⊥ : Typeω@i.
Proof. intros; eapply wf_exp_eq_subtyp; [ apply wf_exp_eq_False_cong | apply wf_typ | eapply wf_subtyp_small_large ]; first [ eassumption | apply wf_llit_fin; eassumption ]. Qed.

Lemma wf_exp_eq_univ_cong_large_tm : forall {Θ Ξ Γ M M' i n},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M⟩ ≈ Type⟨M'⟩ : Typeω@i.
Proof.
  intros * HΓ HMt HM; eapply wf_exp_eq_subtyp;
    [ eapply wf_exp_eq_univ_cong, HM | apply wf_typ, HΓ
    | eapply wf_subtyp_small_large; [ exact HΓ | apply wf_succl, HMt ] ].
Qed.

Lemma wf_exp_eq_univ_cong_large : forall {Θ Ξ Γ o i}, ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ o⟩ ≈ Type⟨𝕃ᵒ o⟩ : Typeω@i.
Proof. intros; eapply wf_exp_eq_univ_cong_large_tm; [ assumption | apply wf_llit_ord; assumption | apply wf_exp_eq_llit_cong; [ reflexivity | assumption ] ]. Qed.

(** ** Literal Levels

    The literal form of the universe rules, which the closed types and the
    stage-1 statements are written with: [succl 𝕃@n] is [𝕃@(S n)] and the
    order on literals is the order on their indices, so the general rules give
    them back. *)
(** ** The Universe Congruence, Right-Hand Side

    [Type⟨M⟩ ≈ Type⟨M'⟩] is stated at [Type⟨succl M⟩], so presupposition
    for the right-hand side has to move [Type⟨M'⟩] from [Type⟨succl M'⟩]
    there.  That is a subtyping, by the level equation [maxl M' M ≈ M], which
    needs reflexivity at [M] only — and [M ≈ M] is [M ≈ M'] composed with its
    symmetry, so no induction over typing is needed here. *)
Lemma wf_exp_eq_maxl_right : forall {Θ Ξ Γ M M' n},
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl M' M ≈ M : Level@n.
Proof.
  intros * HM H.
  assert (HMM : Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M : Level@n)
    by (eapply wf_exp_eq_trans; [ exact H | apply wf_exp_eq_sym, H ]).
  eapply wf_exp_eq_trans;
    [ apply wf_exp_eq_maxl_cong; [ apply wf_exp_eq_sym, H | exact HMM ]
    | apply wf_exp_eq_maxl_idem, HM ].
Qed.

Lemma wf_subtyp_suniv_succl_eq : forall {Θ Ξ Γ M M' n},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨succl M'⟩ ⊆ Type⟨succl M⟩.
Proof.
  intros * HΓ HM HM' H; eapply wf_subtyp_suniv;
    [ exact HΓ | apply wf_succl, HM' | apply wf_succl, HM |].
  eapply wf_exp_eq_trans;
    [ apply wf_exp_eq_sym, wf_exp_eq_succl_maxl; [ exact HM' | exact HM ]
    | apply wf_exp_eq_succl_cong, wf_exp_eq_maxl_right; [ exact HM | exact H ] ].
Qed.

Lemma wf_univ_cong_right : forall {Θ Ξ Γ M M' n},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨M'⟩ : Type⟨succl M⟩.
Proof.
  intros * HΓ HM HM' H.
  assert (HT : Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨succl M⟩ : Typeω@0)
    by (eapply wf_univ_large_tm; [ exact HΓ | apply wf_succl, HM ]).
  eapply wf_exp_subtyp;
    [ eapply wf_univ, HM' | exact HT
    | eapply wf_subtyp_suniv_succl_eq; [ exact HΓ | exact HM | exact HM' | exact H ] ].
Qed.

(** Below a literal, below its successor. *)
Lemma wf_exp_eq_maxl_succl_right : forall {Θ Ξ Γ} o o' n,
    fst o <= n ->
    fst o' <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ o) (𝕃ᵒ o') ≈ 𝕃ᵒ o' : Level@n ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ o) (succl (𝕃ᵒ o')) ≈ succl (𝕃ᵒ o') : Level@n.
Proof.
  intros * Ho Ho' HΓ H.
  assert (HM : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o : Level@n) by (apply wf_llit; assumption).
  assert (HN : Θ ⍮ Ξ ⍮ Γ ⊢ 𝕃ᵒ o' : Level@n) by (apply wf_llit; assumption).
  assert (HSN : Θ ⍮ Ξ ⍮ Γ ⊢ succl (𝕃ᵒ o') : Level@n) by (apply wf_succl, HN).
  eapply wf_exp_eq_trans;
    [ apply wf_exp_eq_maxl_cong;
      [ apply wf_exp_eq_llit_cong; assumption
      | apply wf_exp_eq_sym, wf_exp_eq_maxl_succl, HN ] |].
  eapply wf_exp_eq_trans; [ apply wf_exp_eq_sym, wf_exp_eq_maxl_assoc; [ exact HM | exact HN | exact HSN ] |].
  eapply wf_exp_eq_trans;
    [ apply wf_exp_eq_maxl_cong;
      [ exact H | apply wf_exp_eq_succl_cong, wf_exp_eq_llit_cong; assumption ] |].
  apply wf_exp_eq_maxl_succl, HN.
Qed.

(** Two literals of one tier, [ω·a + b] below [ω·a + (b + d)]. *)
Lemma wf_exp_eq_maxl_llit_tier : forall {Θ Ξ Γ} a b d n,
    a <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ(a, b)) (𝕃ᵒ(a, d + b)) ≈ 𝕃ᵒ(a, d + b) : Level@n.
Proof.
  intros Θ Ξ Γ a b d n Ha HΓ; induction d as [| d IH]; cbn.
  - apply wf_exp_eq_maxl_idem, wf_llit; assumption.
  - eapply wf_exp_eq_trans;
      [ apply wf_exp_eq_maxl_cong;
        [ apply wf_exp_eq_llit_cong; assumption | apply wf_exp_eq_llit_succl; assumption ] |].
    eapply wf_exp_eq_trans;
      [ apply wf_exp_eq_maxl_succl_right; [ exact Ha | exact Ha | exact HΓ | exact IH ] |].
    apply wf_exp_eq_sym, wf_exp_eq_llit_succl; assumption.
Qed.

(** The limit [ω·a'] is above every literal of a lower tier: absorption, at
    the sort just below [a'], moved up to [n]. *)
Lemma wf_exp_eq_maxl_llit_limit : forall {Θ Ξ Γ} a b a' n,
    a < a' ->
    a' <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ(a, b)) (𝕃ᵒ(a', 0)) ≈ 𝕃ᵒ(a', 0) : Level@n.
Proof.
  intros Θ Ξ Γ a b a' n Ha Hn HΓ.
  destruct a' as [| m]; [ lia |].
  eapply wf_exp_eq_subtyp;
    [ apply wf_exp_eq_maxl_absorb, wf_llit; [ cbn; lia | exact HΓ ]
    | apply (wf_level_large (i := 0)), HΓ
    | apply wf_subtyp_level; [ exact Hn | exact HΓ ] ].
Qed.

(** A literal of a lower tier is below every literal of a higher one. *)
Lemma wf_exp_eq_maxl_llit_lower : forall {Θ Ξ Γ} a b a' d n,
    a < a' ->
    a' <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ(a, b)) (𝕃ᵒ(a', d)) ≈ 𝕃ᵒ(a', d) : Level@n.
Proof.
  intros Θ Ξ Γ a b a' d n Ha Hn HΓ; induction d as [| d IH].
  - apply wf_exp_eq_maxl_llit_limit; assumption.
  - eapply wf_exp_eq_trans;
      [ apply wf_exp_eq_maxl_cong;
        [ apply wf_exp_eq_llit_cong; [ cbn; lia | exact HΓ ] | apply wf_exp_eq_llit_succl; assumption ] |].
    eapply wf_exp_eq_trans;
      [ apply wf_exp_eq_maxl_succl_right; [ cbn; lia | exact Hn | exact HΓ | exact IH ] |].
    apply wf_exp_eq_sym, wf_exp_eq_llit_succl; assumption.
Qed.

Lemma wf_exp_eq_maxl_llit_ordinal_le : forall {Θ Ξ Γ} o o' n,
    ordinal_le o o' ->
    fst o' <= n ->
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ maxl (𝕃ᵒ o) (𝕃ᵒ o') ≈ 𝕃ᵒ o' : Level@n.
Proof.
  intros Θ Ξ Γ [a b] [a' b'] n Hle Hn HΓ; unfold ordinal_le in Hle; cbn in Hle, Hn.
  destruct Hle as [Ha | [<- Hb]].
  - apply wf_exp_eq_maxl_llit_lower; assumption.
  - replace b' with ((b' - b) + b) by lia; apply wf_exp_eq_maxl_llit_tier; assumption.
Qed.

Lemma wf_subtyp_small_large_lit : forall {Θ Ξ Γ o i},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ o⟩ ⊆ Typeω@i.
Proof. intros; eapply wf_subtyp_small_large; [ assumption | apply wf_llit_ord; assumption ]. Qed.

Lemma wf_subtyp_suniv_ordinal_le : forall {Θ Ξ Γ o o'},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    ordinal_le o o' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ o⟩ ⊆ Type⟨𝕃ᵒ o'⟩.
Proof.
  intros * HΓ Hle.
  assert (fst o <= fst o') by (destruct o, o'; unfold ordinal_le in Hle; cbn in *; lia).
  eapply (wf_subtyp_suniv _ _ _ (fst o'));
    [ assumption | apply wf_llit; assumption | apply wf_llit; [ reflexivity | assumption ]
    | apply wf_exp_eq_maxl_llit_ordinal_le; [ assumption | reflexivity | assumption ] ].
Qed.

Lemma wf_subtyp_suniv_succl : forall {Θ Ξ Γ a b},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨succl 𝕃ᵒ(a, b)⟩ ⊆ Type⟨𝕃ᵒ(a, S b)⟩.
Proof.
  intros; eapply (wf_subtyp_suniv _ _ _ a);
    [ assumption | apply wf_succl, wf_llit; [ reflexivity | assumption ] | apply wf_llit; [ reflexivity | assumption ] |].
  eapply wf_exp_eq_trans;
    [ apply wf_exp_eq_maxl_cong;
      [ apply wf_exp_eq_sym, wf_exp_eq_llit_succl; [ reflexivity | assumption ]
      | apply wf_exp_eq_llit_cong; [ reflexivity | assumption ] ]
    | apply wf_exp_eq_maxl_idem, wf_llit; [ reflexivity | assumption ] ].
Qed.

Lemma wf_univ_lit : forall {Θ Ξ Γ a b},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ(a, b)⟩ : Type⟨𝕃ᵒ(a, S b)⟩.
Proof.
  intros * HΓ.
  assert (H1 : Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ(a, b)⟩ : Type⟨succl 𝕃ᵒ(a, b)⟩)
    by (eapply (wf_univ _ _ _ a), wf_llit; [ reflexivity | exact HΓ ]).
  assert (H2 : Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ(a, S b)⟩ : Typeω@0) by (apply wf_univ_large; exact HΓ).
  eapply wf_exp_subtyp; [ exact H1 | exact H2 | apply wf_subtyp_suniv_succl, HΓ ].
Qed.

Lemma wf_exp_eq_univ_cong_lit : forall {Θ Ξ Γ a b},
    ⊢ Θ ⍮ Ξ ⍮ Γ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ(a, b)⟩ ≈ Type⟨𝕃ᵒ(a, b)⟩ : Type⟨𝕃ᵒ(a, S b)⟩.
Proof.
  intros * HΓ.
  assert (H1 : Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ(a, b)⟩ ≈ Type⟨𝕃ᵒ(a, b)⟩ : Type⟨succl 𝕃ᵒ(a, b)⟩)
    by (eapply (wf_exp_eq_univ_cong _ _ _ a), wf_exp_eq_llit_cong; [ reflexivity | exact HΓ ]).
  assert (H2 : Θ ⍮ Ξ ⍮ Γ ⊢ Type⟨𝕃ᵒ(a, S b)⟩ : Typeω@0) by (apply wf_univ_large; exact HΓ).
  eapply wf_exp_eq_subtyp; [ exact H1 | exact H2 | apply wf_subtyp_suniv_succl, HΓ ].
Qed.

#[export]
Hint Resolve wf_univ_lit wf_exp_eq_univ_cong_lit : mctt.

(** The universe at an index [u], as a term of the large universe just above
    it: [Typeω@j] is in [Typeω@(S j)], and every small universe is in
    [Typeω@0]. *)
Lemma wf_universe_index_term : forall {Θ Ξ Γ} {u : universe_index},
    ⊢ Θ ⍮ Ξ ⍮ Γ -> Θ ⍮ Ξ ⍮ Γ ⊢ universe_index_term u : Typeω@(large_level_above u).
Proof. intros ? ? ? []; [ apply wf_univ_large | apply wf_typ ]. Qed.

(** A universe is closed, so no substitution reaches it. *)
Lemma exp_sub_universe_index_term : forall u σ, (universe_index_term u)[σ] = universe_index_term u.
Proof. intros [] ?; reflexivity. Qed.


(** As hints, these fix a large universe the goal leaves open to [Typeω@0]
    (a small one to [Type@0]), so that a search never ends with an
    uninstantiated level. *)
Ltac fix_open_level i := first [ is_evar i; first [ unify i 0 | unify i ordinal_zero ] | idtac ].

(** [wf_subtyp_small_large] constrains nothing about the small level, so as a
    constructor hint it would leave it open whenever the left-hand side is;
    it applies only to a known small universe. *)
#[export]
Remove Hints wf_subtyp_small_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨_⟩ ⊆ Typeω@?i) => fix_open_level i; eapply wf_subtyp_small_large : mctt.
(** The literal form of the two hints above keeps the depth of a search that
    only meets small universes at literal levels. *)
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨𝕃ᵒ _⟩ ⊆ Typeω@?i) => fix_open_level i; apply wf_subtyp_small_large_lit : mctt.

#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨_⟩ : Typeω@?i) => fix_open_level i; eapply wf_univ_large_tm : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨𝕃ᵒ _⟩ : Typeω@?i) => fix_open_level i; apply wf_univ_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Level@_ : Typeω@?i) => fix_open_level i; apply wf_level_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Level@_ ≈ Level@_ : Typeω@?i) => fix_open_level i; apply wf_exp_eq_level_cong_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ⊤ : Typeω@?i) => fix_open_level i; apply wf_True_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ⊥ : Typeω@?i) => fix_open_level i; apply wf_False_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ⊤ ≈ ⊤ : Typeω@?i) => fix_open_level i; apply wf_exp_eq_True_cong_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ ⊥ ≈ ⊥ : Typeω@?i) => fix_open_level i; apply wf_exp_eq_False_cong_large : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨_⟩ ≈ Type⟨_⟩ : Typeω@?i) => fix_open_level i; eapply wf_exp_eq_univ_cong_large_tm : mctt.
#[export]
Hint Extern 1 (_ ⍮ _ ⍮ _ ⊢ Type⟨𝕃ᵒ _⟩ ≈ Type⟨𝕃ᵒ _⟩ : Typeω@?i) => fix_open_level i; apply wf_exp_eq_univ_cong_large : mctt.

(** ** The Context of a Judgment

    Every judgment presupposes its context well formed.  These come first,
    each by an induction that reads it off whichever premise is stated at
    [Γ]. *)

Lemma presup_ext_eq_ctx : forall {Θ Ξ Γ Ψ Ψ'}, Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  induction 1; auto.
Qed.

#[export]
Hint Resolve presup_ext_eq_ctx : mctt.

Lemma presup_unit_eq_ctx : forall {Θ Ξ Γ U U'}, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  induction 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_unit_eq_ctx : mctt.

Lemma presup_modexp_eq_ctx : forall {Θ Ξ Γ H H'}, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  induction 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_modexp_eq_ctx : mctt.

(** A unit equivalence presupposes the reflexive instances of both sides. *)
Lemma wf_unit_eq_refl_left : forall {Θ Ξ Γ U U'}, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U.
Proof. intros; eapply wf_unit_eq_trans; [ eassumption | apply wf_unit_eq_sym; eassumption ]. Qed.

Lemma wf_unit_eq_refl_right : forall {Θ Ξ Γ U U'}, Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U' ≈ U'.
Proof. intros; eapply wf_unit_eq_trans; [ apply wf_unit_eq_sym; eassumption | eassumption ]. Qed.

Lemma wf_modexp_eq_refl_left : forall {Θ Ξ Γ H H'}, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros; eapply wf_me_trans; [ eassumption | apply wf_me_sym; eassumption ]. Qed.

Lemma wf_modexp_eq_refl_right : forall {Θ Ξ Γ H H'}, Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H' ≈ H'.
Proof. intros; eapply wf_me_trans; [ apply wf_me_sym; eassumption | eassumption ]. Qed.

Lemma ctx_decomp_mod : forall {Θ Ξ Γ U},
    ⊢ Θ ⍮ Ξ ⍮ Γ ▹ₘ U ->
    ⊢ Θ ⍮ Ξ ⍮ Γ /\ Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U.
Proof.
  inversion 1; eauto using presup_unit_eq_ctx.
Qed.

Corollary ctx_decomp_mod_left : forall {Θ Ξ Γ U}, ⊢ Θ ⍮ Ξ ⍮ Γ ▹ₘ U -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof. intros * ?%ctx_decomp_mod; easy. Qed.

Corollary ctx_decomp_mod_unit : forall {Θ Ξ Γ U}, ⊢ Θ ⍮ Ξ ⍮ Γ ▹ₘ U -> Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U.
Proof. intros * ?%ctx_decomp_mod; easy. Qed.

#[export]
Hint Resolve ctx_decomp_mod_left ctx_decomp_mod_unit : mctt.

Lemma presup_exp_ctx : forall {Θ Ξ Γ M A}, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  induction 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_exp_ctx : mctt.

Lemma presup_exp_eq_ctx : forall {Θ Ξ Γ M M' A}, Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  induction 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_ctx : mctt.

Lemma presup_is_univ_ctx : forall {Θ Ξ Γ U}, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  inversion 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_is_univ_ctx : mctt.

Lemma presup_subtyp_ctx : forall {Θ Ξ Γ A B}, Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ B -> ⊢ Θ ⍮ Ξ ⍮ Γ.
Proof.
  induction 1; mautosolve 2.
Qed.

#[export]
Hint Resolve presup_subtyp_ctx : mctt.

(** The two instances of [wf_pi] and of its congruence, at a large
    universe and at a small one. *)
Lemma wf_pi_large : forall Θ Ξ Γ i A B,
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i -> Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Typeω@i -> Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : Typeω@i.
Proof. intros * HA HB; eapply wf_pi; [ apply wf_is_univ_large; eapply presup_exp_ctx, HA | exact HA | exact HB ]. Qed.

Lemma wf_pi_lvl : forall Θ Ξ Γ n L A B,
    Θ ⍮ Ξ ⍮ Γ ⊢ L : Level@n -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Type⟨L⟩ -> Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B : Type⟨L[↑]ʷ⟩ -> Θ ⍮ Ξ ⍮ Γ ⊢ Π A B : Type⟨L⟩.
Proof. intros * HL HA HB; eapply wf_pi; [ eapply wf_is_univ_small, HL | exact HA | exact HB ]. Qed.

Lemma wf_exp_eq_pi_cong_large : forall Θ Ξ Γ i A A' B B',
    Θ ⍮ Ξ ⍮ Γ ⊢ A : Typeω@i -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Typeω@i -> Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : Typeω@i ->
    Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Typeω@i.
Proof. intros * HA HAA HB; eapply wf_exp_eq_pi_cong; [ apply wf_is_univ_large; eapply presup_exp_ctx, HA | exact HA | exact HAA | exact HB ]. Qed.

Lemma wf_exp_eq_pi_cong_lvl : forall Θ Ξ Γ n L A A' B B',
    Θ ⍮ Ξ ⍮ Γ ⊢ L : Level@n -> Θ ⍮ Ξ ⍮ Γ ⊢ A : Type⟨L⟩ -> Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : Type⟨L⟩ ->
    Θ ⍮ Ξ ⍮ Γ ▹ A ⊢ B ≈ B' : Type⟨L[↑]ʷ⟩ -> Θ ⍮ Ξ ⍮ Γ ⊢ Π A B ≈ Π A' B' : Type⟨L⟩.
Proof. intros * HL HA HAA HB; eapply wf_exp_eq_pi_cong; [ eapply wf_is_univ_small, HL | exact HA | exact HAA | exact HB ]. Qed.

#[export]
Hint Resolve wf_pi_large wf_pi_lvl wf_exp_eq_pi_cong_large wf_exp_eq_pi_cong_lvl : mctt.

(** A universe is a type. *)
Lemma wf_is_univ_typ : forall {Θ Ξ Γ U}, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> exists i, Θ ⍮ Ξ ⍮ Γ ⊢ U : Typeω@i.
Proof.
  inversion 1; subst; [ exists (S i); apply wf_typ; assumption |].
  exists 0; eapply wf_exp_subtyp; [ eapply wf_univ; eassumption | apply wf_typ; mauto 2 | eapply wf_subtyp_small_large; mauto 2 ].
Qed.

#[export]
Hint Resolve wf_is_univ_typ : mctt.

Lemma presup_subtyp_right : forall {Θ Ξ Γ A B}, Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ B -> exists i, Θ ⍮ Ξ ⍮ Γ ⊢ B : Typeω@i.
Proof.
  induction 1; mautosolve.
Qed.

#[export]
Hint Resolve presup_subtyp_right : mctt.

(** ** Subtyping Rules without Extra Arguments *)

Lemma wf_exp_subtyp' : forall Θ Ξ Γ A A' M,
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M : A'.
Proof.
  intros.
  assert (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_subtyp' : mctt.
#[export]
Remove Hints wf_exp_subtyp : mctt.

Lemma wf_exp_eq_subtyp' : forall Θ Ξ Γ A A' M M',
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A'.
Proof.
  intros.
  assert (exists i, Θ ⍮ Ξ ⍮ Γ ⊢ A' : Typeω@i) as [] by mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_subtyp' : mctt.
#[export]
Remove Hints wf_exp_eq_subtyp : mctt.

(** ** Term Equality is a PER

    Reflexivity at a well-typed term is not available here — it needs an
    induction over typing, so it lives in [Core.Syntactic.System.Lemmas]
    together with the [PERElem] instance that lets [saturate_refl] use it.  The
    same goes for [wf_sub_eq], whose symmetry and transitivity need
    [sub_eq_preserves_exp] to move between the types [A[σ]] and [A[σ']]. *)

#[export]
Instance wf_exp_eq_PER Θ Ξ Γ A : PER (wf_exp_eq Θ Ξ Γ A).
Proof.
  split.
  - eauto using wf_exp_eq_sym.
  - eauto using wf_exp_eq_trans.
Qed.

#[export]
Instance wf_subtyp_Transitive Θ Ξ Γ : Transitive (wf_subtyp Θ Ξ Γ).
Proof.
  hnf; mauto.
Qed.

Add Parametric Morphism Θ Ξ Γ T : (wf_exp_eq Θ Ξ Γ T)
    with signature wf_exp_eq Θ Ξ Γ T ==> eq ==> iff as wf_exp_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism Θ Ξ Γ T : (wf_exp_eq Θ Ξ Γ T)
    with signature eq ==> wf_exp_eq Θ Ξ Γ T ==> iff as wf_exp_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.
