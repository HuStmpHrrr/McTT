(** * The Typed Fill

    The elaborator is untyped: it resolves names into the user syntax
    ([UserSyntax]), which holds what is written and nothing else.  The
    command judgment fills each written command into core syntax, in one
    depth-first pass, before it runs, each part read in the context
    algorithmic typing ([alg_type_infer]) reads it in.  The core keeps
    every annotation explicit; the fill writes each one the user may
    omit:

    - Literals: where the natural numbers are bound ([Builtin]), a numeral
      ([surface_nlit]) stands for the chain of the bound type's constructors and
      the token [ℕ] ([surface_ntok]) for its type former.  Without a binding a
      literal has no fill.
    - Eliminators: an eliminator as written carries no group, no uniform
      parameters and no sort ([surface_elim m Bks M]).  The group and the
      parameters are read off its scrutinee's inferred type
      ([elim_target]): the eliminator is filled when exactly one reading
      of it fits its blocks.  A block's scrutinee type, when omitted, is
      the member's type at the parameters and the block's binders.
    - Sorts: the tag of a [Π], of an eliminator and of a body's
      definition is the sort its codomain, motive or type infers to.
    - Omitted annotations ([surface_hole]): an unannotated [let] binds its
      definition at the type it infers; [conj (m : P) n] proves the
      conjunction whose second part is the type [n] infers; an [eval]
      without a type is at the type its term infers.
    - Accesses: for [e.f] the elaborator emits the member [f] of the
      module expression [e] stands for, or, when [e] is no path, the
      member [f] of the term [e] ([surface_proj_term]).  A term [M] whose type
      infers to the record type [p] at the parameters [Rs] stands, in
      module position, for the record's module at [Rs], then [M]
      ([record_value_module]):
<<
    (λ (q : Pair ℕ ℕ) → q.fst)   is filled to   (λ (q : Pair ℕ ℕ) → (Pair ℕ ℕ q).fst)
>>
      A member selected from the module of a record value must be
      accessible ([sel_ok]): privacy is checked on the command as written,
      where the selection is from a term, so it is checked here once the
      record is known.

    A written command is filled to the core commands it runs as: one,
    or, for a module and a record, the opening of its frame, its body's
    commands as written, which are filled when they run, and the closing
    of the frame.  The fill reads algorithmic inference ([⊢a]), which
    gives one type ([functional_alg_type_infer]), so the fill, and the
    run, are functional. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Command Builtin Records.
From Mctt.Core.Syntactic.System Require Import Privacy Translations.
From Mctt.Core.TypedElab Require Export ElimTarget.
From Mctt.Algorithmic.Typing Require Import Definitions.
Import Syntax_Notations.

(** The constructor names of each block of an eliminator as written,
    which [elim_target] matches against the groups' members. *)
Definition surface_block_names (Bks : list surface_block) : list (list string) :=
  List.map (fun b => match b with surface_eb_mk _ _ _ Bs => List.map (fun br => fst (fst br)) Bs end) Bks.

(** A term as written with no subterm and nothing to fill: its core
    term. *)
Definition surface_exp_leaf (M : surface_exp) : option exp :=
  match M with
  | surface_typ n => Some (a_typ n)
  | surface_level n => Some (a_level n)
  | surface_llit o => Some (a_llit o)
  | surface_prop => Some a_prop
  | surface_True => Some a_True
  | surface_tt => Some a_tt
  | surface_False => Some a_False
  | surface_var x => Some (a_var x)
  | _ => None
  end.

Section Fill.
  Variables (Θ : gdeps) (Ξ : gstack) (B : builtins).
  #[local] Instance GC : GCtx := gc_mk Θ Ξ.

  (** The module of the record [p] at the parameters [Rs], at the value
      [M]: the record's module applied to its full telescope
      ([record_mod_tele]), the parameters then the value. *)
  Definition record_value_module (p : qname) (Rs : list nf) (M : exp) : modexp :=
    me_apps (qname_mod p) (List.map nf_to_exp Rs ++ M :: nil).

  (** What a module expression in module position reads as. *)
  Inductive module_read : Set :=
  (** A module, filled *)
  | read_module : modexp -> module_read
  (** A term, filled: the expression has a term at its head *)
  | read_term : exp -> module_read.

  (** A member [y] selected from the module of a record value, the record
      [p] when it is one ([Some p]), is accessible, as [glob_ok] says of
      any member of a module named by its path.  A selection from any
      other module is checked as written. *)
  Definition sel_ok (op : option qname) (y : string) : Prop :=
    match op with
    | None => True
    | Some p => glob_ok Θ Ξ (qname_mod p) y
    end.

  (** The tag of a [Π], an eliminator or a definition whose codomain,
      motive or type infers to the type [W]: [propositional] at [Prop],
      [relevant] otherwise.  At a type that is neither [Prop] nor a
      universe the tag is [relevant], and the typing rule rejects the
      term. *)
  Definition sort_relevance (W : nf) : relevance :=
    match W with
    | nf_prop => propositional
    | _ => relevant
    end.

  (** The binder [k] of [Γ] holds a term only, an assumption or a
      definition, and so reads as a term in module position. *)
  Definition term_binder (Γ : ctx) (k : nat) : Prop :=
    match List.nth_error Γ k with
    | Some (ce_ass _) | Some (ce_def _ _) => True
    | _ => False
    end.

  (** The members an open's items name. *)
  Definition items_members (its : list import_item) : list string :=
    List.flat_map (fun it => match fst (fst it) with Some n => n :: nil | None => nil end) its.

  (** ** The Fill of Terms

      [fill_exp Γ M M']: the term [M] as written, read in [Γ], is filled
      to the core term [M'].  The contexts are those of algorithmic
      typing: a binder's type is its filled type; a [let] binds its filled
      definition at its filled (or inferred) type; an eliminator's
      annotations, motives and branches are read in the contexts
      [alg_type_infer_elim] reads them in, at its group and its uniform
      parameters and filled motives; a local body's entries in the context
      of the expansion of the filled entries before them ([body_xp]). *)
  Inductive fill_exp : ctx -> surface_exp -> exp -> Prop :=
  (** A term with no subterm and nothing to fill *)
  | fill_exp_leaf : forall Γ M M', surface_exp_leaf M = Some M' -> fill_exp Γ M M'
  (** A numeral: the chain of the bound type's constructors *)
  | fill_exp_nlit : forall Γ n p z s,
      nat_view Θ Ξ B = Some (p, z, s) -> fill_exp Γ (surface_nlit n) (nat_chain p z s n)
  (** The token [ℕ]: the bound type's type former *)
  | fill_exp_ntok : forall Γ p z s,
      nat_view Θ Ξ B = Some (p, z, s) -> fill_exp Γ surface_ntok (a_ind p 0)
  (** A universe at a level *)
  | fill_exp_univ : forall Γ M M', fill_exp Γ M M' -> fill_exp Γ (surface_univ M) (a_univ M')
  (** A level's successor *)
  | fill_exp_succl : forall Γ M M', fill_exp Γ M M' -> fill_exp Γ (surface_succl M) (a_succl M')
  (** A join of levels *)
  | fill_exp_maxl : forall Γ M M' N N', fill_exp Γ M M' -> fill_exp Γ N N' -> fill_exp Γ (surface_maxl M N) (a_maxl M' N')
  (** [efq M return C] *)
  | fill_exp_absurd : forall Γ C C' M M',
      fill_exp Γ C C' -> fill_exp Γ M M' -> fill_exp Γ (surface_absurd C M) (a_absurd C' M')
  (** A [Π]: the codomain under the filled domain; its tag the sort the
      filled codomain infers to *)
  | fill_exp_pi : forall Γ A A' B B' W,
      fill_exp Γ A A' -> fill_exp (Γ ▹ A') B B' -> ⊢ Θ ⍮ Ξ ⍮ Γ ▹ A' -> Γ ▹ A' ⊢a B' ⟹ W ->
      fill_exp Γ (surface_pi A B) (a_pi (sort_relevance W) A' B')
  (** A conjunction: the second proposition under the filled first *)
  | fill_exp_and : forall Γ P P' Q Q', fill_exp Γ P P' -> fill_exp (Γ ▹ P') Q Q' -> fill_exp Γ (surface_and P Q) (a_and P' Q')
  (** A proof of a conjunction with its second proposition written *)
  | fill_exp_conj : forall Γ P P' Q Q' M M' N N',
      Q <> surface_hole ->
      fill_exp Γ P P' -> fill_exp (Γ ▹ P') Q Q' -> fill_exp Γ M M' -> fill_exp Γ N N' ->
      fill_exp Γ (surface_conj P Q M N) (a_conj P' Q' M' N')
  (** A proof of a conjunction as written, [conj (m : P) n]: the second
      proposition is the type the filled second component infers to,
      weakened past the first's binder *)
  | fill_exp_conj_right_inferred : forall Γ P P' M M' N N' W,
      fill_exp Γ P P' -> fill_exp Γ M M' -> fill_exp Γ N N' -> ⊢ Θ ⍮ Ξ ⍮ Γ -> Γ ⊢a N' ⟹ W ->
      fill_exp Γ (surface_conj P surface_hole M N) (a_conj P' (exp_wk (nf_to_exp W) wk_shift) M' N')
  (** The first component of a proof of a conjunction *)
  | fill_exp_left : forall Γ M M', fill_exp Γ M M' -> fill_exp Γ (surface_left M) (a_left M')
  (** The second component *)
  | fill_exp_right : forall Γ M M', fill_exp Γ M M' -> fill_exp Γ (surface_right M) (a_right M')
  (** A [λ]: the body under the filled domain *)
  | fill_exp_fn : forall Γ A A' M M', fill_exp Γ A A' -> fill_exp (Γ ▹ A') M M' -> fill_exp Γ (surface_fn A M) (a_fn A' M')
  (** An application *)
  | fill_exp_app : forall Γ M M' N N', fill_exp Γ M M' -> fill_exp Γ N N' -> fill_exp Γ (surface_app M N) (a_app M' N')
  (** A [let] with its type written: the rest under the filled
      definition *)
  | fill_exp_let_ann : forall Γ A A' M M' B B',
      A <> surface_hole ->
      fill_exp Γ A A' -> fill_exp Γ M M' -> fill_exp (Γ ▸ A' ≔ M') B B' ->
      fill_exp Γ (surface_let (surface_b_def A M) B) (a_let (b_def A' M') B')
  (** A [let] without one: the definition at the type it infers, which
      the fill writes as its annotation *)
  | fill_exp_let_infer : forall Γ M M' W B B',
      fill_exp Γ M M' -> ⊢ Θ ⍮ Ξ ⍮ Γ -> Γ ⊢a M' ⟹ W -> fill_exp (Γ ▸ nf_to_exp W ≔ M') B B' ->
      fill_exp Γ (surface_let (surface_b_def surface_hole M) B) (a_let (b_def (nf_to_exp W) M') B')
  (** A local module: the rest under the filled unit *)
  | fill_exp_let_mod : forall Γ U U' B B',
      fill_unit Γ U U' -> fill_exp (Γ ▹ₘ U') B B' -> fill_exp Γ (surface_let (surface_b_mod U) B) (a_let (b_mod U') B')
  (** A member: its module filled; a member of a record value's module
      accessible *)
  | fill_exp_mem : forall Γ H H' op x,
      fill_mod Γ H H' op -> sel_ok op x -> fill_exp Γ (surface_mem H x) (a_mem H' x)
  (** A member of a term, [t.x] for [t] no path: the member [x] of the
      module of [t]'s record type at [t], accessible *)
  | fill_exp_proj_term : forall Γ M M' p Rs x,
      fill_exp Γ M M' -> ⊢ Θ ⍮ Ξ ⍮ Γ -> Γ ⊢a M' ⟹ nf_record p Rs -> sel_ok (Some p) x ->
      fill_exp Γ (surface_proj_term M x) (a_mem (record_value_module p Rs M') x)
  (** A record value: its type and its fields *)
  | fill_exp_tuple : forall Γ T T' fs fs',
      fill_exp Γ T T' -> fill_field_vals Γ fs fs' -> fill_exp Γ (surface_tuple T fs) (a_tuple T' fs')
  (** An eliminator as written: its scrutinee filled; its group [p] and
      uniform parameters [Us] the one reading of it that fits its blocks,
      read off the scrutinee's inferred type ([elim_target]); its blocks
      at them and at the filled motives; its tag the sort the filled
      motive of the scrutinee's member [m] infers to *)
  | fill_exp_elim : forall Γ m Bks Bks' M M' pc k Rs p D Us Mm bm W,
      fill_exp Γ M M' ->
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      Γ ⊢a M' ⟹ nf_indty pc k Rs ->
      elim_target Θ Ξ pc k Rs m (surface_block_names Bks) = elim_target_one p Us ->
      ind_lookup Θ Ξ p = Some D ->
      ind_member D m = Some Mm ->
      List.nth_error Bks' m = Some bm ->
      ⊢ Θ ⍮ Ξ ⍮ elim_mctx p D m Mm Us ++ Γ ->
      elim_mctx p D m Mm Us ++ Γ ⊢a eb_motive bm ⟹ W ->
      fill_blocks (sort_relevance W) Γ p D Us (blocks_motives Bks') 0 Bks Bks' ->
      fill_exp Γ (surface_elim m Bks M) (a_elim (sort_relevance W) p Us m Bks' M')

  (** The fields of a record value, each its name and its value *)
  with fill_field_vals : ctx -> list (string * surface_exp) -> list (string * exp) -> Prop :=
  (** No field *)
  | fill_field_vals_nil : forall Γ, fill_field_vals Γ nil nil
  (** The first field, then the rest *)
  | fill_field_vals_cons : forall Γ f M M' fs fs',
      fill_exp Γ M M' -> fill_field_vals Γ fs fs' -> fill_field_vals Γ ((f, M) :: fs) ((f, M') :: fs')

  (** The blocks of an eliminator of the group [p], [D], from the member
      [j] on, at the uniform parameters [Us] and the motives [As]: each its
      scrutinee's type over its member's non-uniform parameters, its motive
      over them and the scrutinee, and its branches, with as many binders
      as [alg_type_infer_elim] asks, at the eliminator's tag [r] *)
  with fill_blocks : relevance -> ctx -> qname -> ind_decl -> list exp -> list exp -> nat -> list surface_block -> list eblock -> Prop :=
  (** No block *)
  | fill_blocks_nil : forall r Γ p D Us As j, fill_blocks r Γ p D Us As j nil nil
  (** The block of the member [j], then the rest *)
  | fill_blocks_cons : forall r Γ p D Us As j Mj nm Z Z' A A' Bs Bs' Bks Bks',
      ind_member D j = Some Mj ->
      nm = S (im_nn Mj) ->
      fill_scrutinee_type Γ p D j Mj Us Z Z' ->
      fill_exp (elim_mctx p D j Mj Us ++ Γ) A A' ->
      fill_brs r Γ p D Mj Us As Bs Bs' ->
      fill_blocks r Γ p D Us As (S j) Bks Bks' ->
      fill_blocks r Γ p D Us As j (surface_eb_mk nm Z A Bs :: Bks) (eb_mk nm Z' A' Bs' :: Bks')

  (** The scrutinee's type of the block of the member [j], [Mj], over its
      non-uniform parameters *)
  with fill_scrutinee_type : ctx -> qname -> ind_decl -> nat -> imember -> list exp -> surface_exp -> exp -> Prop :=
  (** Written: filled *)
  | fill_scrutinee_type_written : forall Γ p D j Mj Us Z Z',
      Z <> surface_hole ->
      fill_exp (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) Z Z' ->
      fill_scrutinee_type Γ p D j Mj Us Z Z'
  (** Omitted: the member's type at the uniform parameters and the
      non-uniform ones, the scrutinee's type in the motive's context
      ([elim_mctx]) *)
  | fill_scrutinee_type_omitted : forall Γ p D j Mj Us,
      fill_scrutinee_type Γ p D j Mj Us surface_hole (member_scrutinee_type p D j Mj Us)

  (** The branches of a block of the member [Mj], each in its
      constructor's branch context at the tag [r] *)
  with fill_brs : relevance -> ctx -> qname -> ind_decl -> imember -> list exp -> list exp ->
                  list (string * nat * surface_exp) -> list (string * nat * exp) -> Prop :=
  (** No branch *)
  | fill_brs_nil : forall r Γ p D Mj Us As, fill_brs r Γ p D Mj Us As nil nil
  (** The branch of the constructor [c], then the rest *)
  | fill_brs_cons : forall r Γ p D Mj Us As c gs n B B' Bs Bs',
      ind_con Mj c = Some gs ->
      n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat ->
      fill_exp (elim_bctx r p D Mj gs As Us ++ Γ) B B' ->
      fill_brs r Γ p D Mj Us As Bs Bs' ->
      fill_brs r Γ p D Mj Us As ((c, n, B) :: Bs) ((c, n, B') :: Bs')

  (** A term that may be absent *)
  with fill_optional_exp : ctx -> option surface_exp -> option exp -> Prop :=
  (** Absent *)
  | fill_optional_exp_none : forall Γ, fill_optional_exp Γ None None
  (** Present *)
  | fill_optional_exp_some : forall Γ M M', fill_exp Γ M M' -> fill_optional_exp Γ (Some M) (Some M')

  (** [fill_read Γ H r]: in module position, [H] reads as [r] *)
  with fill_read : ctx -> surface_modexp -> module_read -> Prop :=
  (** A unit *)
  | fill_read_unit : forall Γ fp, fill_read Γ (surface_me_unit fp) (read_module (me_unit fp))
  (** A binder that is no term binder: a module slot, a definition with a
      module part (read as its module part, as a member with a term part
      and a module part is), or nothing, which typing rejects *)
  | fill_read_slot : forall Γ k, ~ term_binder Γ k -> fill_read Γ (surface_me_var k) (read_module (me_var k))
  (** A term binder: the term *)
  | fill_read_var : forall Γ k, term_binder Γ k -> fill_read Γ (surface_me_var k) (read_term (a_var k))
  (** A member that is no term: a module, or nothing, which typing
      rejects *)
  | fill_read_mem_module : forall Γ H H' op y,
      fill_mod Γ H H' op -> sel_ok op y ->
      (forall r A oM, ~ mdenote Θ Ξ Γ (me_mem H' y) (mdesc_term r A oM)) ->
      fill_read Γ (surface_me_mem H y) (read_module (me_mem H' y))
  (** A member that is a term: the term *)
  | fill_read_mem_term : forall Γ H H' op y r A oM,
      fill_mod Γ H H' op -> sel_ok op y ->
      mdenote Θ Ξ Γ (me_mem H' y) (mdesc_term r A oM) ->
      fill_read Γ (surface_me_mem H y) (read_term (a_mem H' y))
  (** A module applied: a module *)
  | fill_read_app_module : forall Γ H H' N N',
      fill_read Γ H (read_module H') -> fill_exp Γ N N' -> fill_read Γ (surface_me_app H N) (read_module (me_app H' N'))
  (** A term applied: a term *)
  | fill_read_app_term : forall Γ H M N N',
      fill_read Γ H (read_term M) -> fill_exp Γ N N' -> fill_read Γ (surface_me_app H N) (read_term (a_app M N'))

  (** [fill_mod Γ H H' op]: in module position, [H] is the module [H'];
      [op] is the record [H'] is the module of a value of, when [H] has a
      term at its head *)
  with fill_mod : ctx -> surface_modexp -> modexp -> option qname -> Prop :=
  (** A module *)
  | fill_mod_module : forall Γ H H', fill_read Γ H (read_module H') -> fill_mod Γ H H' None
  (** A term of a record type: the record's module at the type's
      parameters, then the term *)
  | fill_mod_term : forall Γ H M p Rs,
      fill_read Γ H (read_term M) ->
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      Γ ⊢a M ⟹ nf_record p Rs ->
      fill_mod Γ H (record_value_module p Rs M) (Some p)

  (** A unit: its telescope, then its definition under it *)
  with fill_unit : ctx -> surface_unit -> gunit -> Prop :=
  (** The only rule: the telescope filled, then the definition under the
      filled telescope *)
  | fill_unit_mk : forall Γ Δ Δ' D D',
      fill_tele Γ Δ Δ' -> fill_def (Δ' ++ Γ) D D' -> fill_unit Γ (surface_gu_mk Δ D) (gu_mk Δ' D')

  (** A unit's definition *)
  with fill_def : ctx -> surface_moddef -> moddef -> Prop :=
  (** An alias: its target, which may be a record value *)
  | fill_def_alias : forall Γ E E' op, fill_mod Γ E E' op -> fill_def Γ (surface_md_alias E) (md_alias E')
  (** A body, stored open: its entries mention the parameters and the
      entries before them *)
  | fill_def_body : forall Γ Φ Φ', fill_body Γ Φ Φ' -> fill_def Γ (surface_md_body Φ) (md_body sm_open Φ')

  (** A telescope of assumptions, innermost first, each over the filled
      ones after it *)
  with fill_tele : ctx -> list surface_exp -> ctx -> Prop :=
  (** The empty telescope *)
  | fill_tele_nil : forall Γ, fill_tele Γ nil nil
  (** An assumption *)
  | fill_tele_ass : forall Γ Δ Δ' A A',
      fill_tele Γ Δ Δ' -> fill_exp (Δ' ++ Γ) A A' -> fill_tele Γ (A :: Δ) (ce_ass A' :: Δ')

  (** A local body, entry by entry, each in the context of the expansion
      of the filled entries before it *)
  with fill_body : ctx -> surface_body -> gmod -> Prop :=
  (** The empty body *)
  | fill_body_nil : forall Γ, fill_body Γ surface_gm_nil gm_nil
  (** A definition: its tag the sort its filled type infers to *)
  | fill_body_def : forall Γ Φ Φ' Φx x b pv A A' oM oM' W,
      fill_body Γ Φ Φ' -> body_xp Θ Ξ Γ Φ' Φx ->
      fill_exp (body_ctx Φx ++ Γ) A A' -> fill_optional_exp (body_ctx Φx ++ Γ) oM oM' ->
      ⊢ Θ ⍮ Ξ ⍮ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢a A' ⟹ W ->
      fill_body Γ (surface_gm_ext Φ x (surface_ge_def b pv A oM)) (gm_ext Φ' x (ge_def b pv (sort_relevance W) A' oM'))
  (** A module *)
  | fill_body_mod : forall Γ Φ Φ' Φx x pv U U',
      fill_body Γ Φ Φ' -> body_xp Θ Ξ Γ Φ' Φx -> fill_unit (body_ctx Φx ++ Γ) U U' ->
      fill_body Γ (surface_gm_ext Φ x (surface_ge_mod pv U)) (gm_ext Φ' x (ge_mod pv U'))
  (** A local open: its target, which may be a record value, whose
      members its items name accessible *)
  | fill_body_open : forall Γ Φ Φ' Φx H H' op its,
      fill_body Γ Φ Φ' -> body_xp Θ Ξ Γ Φ' Φx -> fill_mod (body_ctx Φx ++ Γ) H H' op ->
      Forall (sel_ok op) (items_members its) ->
      fill_body Γ (surface_gm_open Φ H its) (gm_open Φ' H' its).

  Scheme fill_exp_mut_ind := Induction for fill_exp Sort Prop
  with fill_field_vals_mut_ind := Induction for fill_field_vals Sort Prop
  with fill_blocks_mut_ind := Induction for fill_blocks Sort Prop
  with fill_scrutinee_type_mut_ind := Induction for fill_scrutinee_type Sort Prop
  with fill_brs_mut_ind := Induction for fill_brs Sort Prop
  with fill_optional_exp_mut_ind := Induction for fill_optional_exp Sort Prop
  with fill_read_mut_ind := Induction for fill_read Sort Prop
  with fill_mod_mut_ind := Induction for fill_mod Sort Prop
  with fill_unit_mut_ind := Induction for fill_unit Sort Prop
  with fill_def_mut_ind := Induction for fill_def Sort Prop
  with fill_tele_mut_ind := Induction for fill_tele Sort Prop
  with fill_body_mut_ind := Induction for fill_body Sort Prop.
  Combined Scheme fill_mut_ind from fill_exp_mut_ind, fill_field_vals_mut_ind, fill_blocks_mut_ind,
    fill_scrutinee_type_mut_ind, fill_brs_mut_ind, fill_optional_exp_mut_ind, fill_read_mut_ind, fill_mod_mut_ind,
    fill_unit_mut_ind, fill_def_mut_ind, fill_tele_mut_ind, fill_body_mut_ind.

  (** Named types, outermost first, each over the filled ones before it:
      the fields of a record declaration ([record_fctx]) and the arguments
      of a constructor ([raw_args_tele]) *)
  Inductive fill_fields : ctx -> list (string * surface_exp) -> list (string * typ) -> Prop :=
  (** No field *)
  | fill_fields_nil : forall Γ, fill_fields Γ nil nil
  (** The first field, then the rest over it *)
  | fill_fields_cons : forall Γ f T T' fs fs',
      fill_exp Γ T T' -> fill_fields (Γ ▹ T') fs fs' -> fill_fields Γ ((f, T) :: fs) ((f, T') :: fs').

  (** ** The Fill of Commands

      Each part of a command is filled in the context its run reads it in.
      A mutual definition's functions are filled in two steps: their
      heads, their parameters and scrutinees, from which the group is read
      ([mdef_group]), then their results and clauses, in the contexts the
      eliminator its translation files ([mdef_defs]) reads them in, at the
      motives of the translation's own blocks ([mdef_blocks]). *)

  (** The head of a function of a mutual definition over [Γ], [f], its
      parameters and scrutinee filled, as [run_cmd_mdef] reads them, to
      [h]. *)
  Record fill_raw_fun_head (Γ : ctx) (f : surface_raw_fun) (h : raw_fun_head) : Prop := mk_fill_raw_fun_head
    { (** The name is kept *)
      fill_raw_fun_head_name : raw_fun_head_name h = surface_raw_fun_name f
      (** The parameters, over [Γ], are filled *)
    ; fill_raw_fun_head_nparams : fill_tele Γ (surface_raw_fun_nparams f) (raw_fun_head_nparams h)
      (** The scrutinee's type, over the filled parameters, is filled *)
    ; fill_raw_fun_head_scrut : fill_exp (raw_fun_head_nparams h ++ Γ) (surface_raw_fun_scrut f) (raw_fun_head_scrut h) }.

  (** A function [f] of the member [m] of the group [D] at [pq], at the
      uniform parameters [Us] and the motives [As], over [Γ], its head
      filled to [h], filled to [f']: the result in the motive's context,
      the clauses in their branches', as [alg_type_infer_elim] reads
      them. *)
  Record fill_raw_fun_body (pq : qname) (D : ind_decl) (Us : list exp) (Γ : ctx) (As : list exp)
      (f : surface_raw_fun) (h : raw_fun_head) (m : nat) (f' : raw_fun) : Prop := mk_fill_raw_fun_body
    { (** The head is the filled one *)
      fill_raw_fun_body_head : raw_fun_head_of f' = h
      (** The member is one of the group *)
    ; fill_raw_fun_body_member : ind_member D m <> None
      (** The result type, over the member's parameters and the scrutinee,
          is filled *)
    ; fill_raw_fun_body_res : forall Mm, ind_member D m = Some Mm ->
        fill_exp (elim_mctx pq D m Mm Us ++ Γ) (surface_raw_fun_res f) (raw_fun_res f')
      (** The clauses, each in its constructor's branch context, are
          filled *)
    ; fill_raw_fun_body_clauses : forall Mm, ind_member D m = Some Mm ->
        fill_brs relevant Γ pq D Mm Us As (surface_raw_fun_clauses f) (raw_fun_clauses f') }.

  (** A declared member [Mr] of a group whose filled form is [R'], filled
      to [Mr']: its parameters and sort over the uniform parameters, its
      constructors' arguments over its context ([raw_member_args_ctx]), in
      the filled group. *)
  Record fill_raw_member (R' : raw_decl) (Mr : surface_raw_member) (Mr' : raw_member) : Prop := mk_fill_raw_member
    { (** The name is kept *)
      fill_raw_member_name : raw_member_name Mr' = surface_raw_member_name Mr
      (** The parameters, over the uniform ones, are filled *)
    ; fill_raw_member_nparams : fill_tele (raw_decl_uparams R' ++ gs_tele Ξ) (surface_raw_member_nparams Mr) (raw_member_nparams Mr')
      (** The sort, over the uniform parameters, is filled *)
    ; fill_raw_member_sort : fill_exp (raw_decl_uparams R' ++ gs_tele Ξ) (surface_raw_member_sort Mr) (raw_member_sort Mr')
      (** Each constructor keeps its name, and its arguments, each over the
          ones before it, are filled over the member's context *)
    ; fill_raw_member_cons :
        Forall2 (fun rc rc' => fst rc' = fst rc /\ fill_fields (raw_member_args_ctx Ξ R' Mr') (snd rc) (snd rc'))
          (surface_raw_member_cons Mr) (raw_member_cons Mr') }.

  (** [fill_raw_decl R R']: the group as written [R] is filled to [R'],
      each part in the context the classification reads it in. *)
  Record fill_raw_decl (R : surface_raw_decl) (R' : raw_decl) : Prop := mk_fill_raw_decl
    { (** The uniform parameters, over the frames', are filled *)
      fill_raw_decl_uparams : fill_tele (gs_tele Ξ) (surface_raw_decl_uparams R) (raw_decl_uparams R')
      (** Whether the group files its recursor module is kept *)
    ; fill_raw_decl_rec : raw_decl_rec_field R' = surface_raw_decl_rec_field R
      (** Each declared member is filled, in order *)
    ; fill_raw_decl_members : Forall2 (fill_raw_member R') (surface_raw_decl_members R) (raw_decl_members R') }.

  (** [fill_cmd c its]: the written command [c] is filled to the items
      [its] it runs as, its terms read in the frames' telescope.  One rule
      per kind of command.  A module and a record open their frame, their
      body's commands follow as written, filled when they run, and the
      frame is closed. *)
  Inductive fill_cmd : surface_cmd -> list cmd_item -> Prop :=
  (** A definition: its type and its body *)
  | fill_cmd_def : forall x b pv A A' oM oM',
      fill_exp (gs_tele Ξ) A A' -> fill_optional_exp (gs_tele Ξ) oM oM' ->
      fill_cmd (surface_cmd_def x b pv A oM) (ci_core (core_cmd_def x b pv A' oM') :: nil)
  (** A module: its telescope, its frame opened, its commands as written,
      its frame closed *)
  | fill_cmd_mod : forall x pv Δ Δ' cs,
      fill_tele (gs_tele Ξ) Δ Δ' ->
      fill_cmd (surface_cmd_mod x pv Δ cs)
        (ci_core (core_cmd_mod_open x pv Δ') :: List.map ci_written cs ++ ci_core (core_cmd_close x pv) :: nil)
  (** A module alias: its telescope, then its target, which may be a
      record value *)
  | fill_cmd_alias : forall x pv Δ Δ' E E' op,
      fill_tele (gs_tele Ξ) Δ Δ' -> fill_mod (Δ' ++ gs_tele Ξ) E E' op ->
      fill_cmd (surface_cmd_alias x pv Δ E) (ci_core (core_cmd_alias x pv Δ' E') :: nil)
  (** An inductive alias: its telescope, then its target, a module *)
  | fill_cmd_ind_alias : forall x pv Δ Δ' E E',
      fill_tele (gs_tele Ξ) Δ Δ' -> fill_mod (Δ' ++ gs_tele Ξ) E E' None ->
      fill_cmd (surface_cmd_inductive_alias x pv Δ E) (ci_core (core_cmd_inductive_alias x pv Δ' E') :: nil)
  (** A record alias: its telescope, then its target, a module *)
  | fill_cmd_record_alias : forall x pv Δ Δ' E E',
      fill_tele (gs_tele Ξ) Δ Δ' -> fill_mod (Δ' ++ gs_tele Ξ) E E' None ->
      fill_cmd (surface_cmd_record_alias x pv Δ E) (ci_core (core_cmd_record_alias x pv Δ' E') :: nil)
  (** A load: itself *)
  | fill_cmd_load : forall fp, fill_cmd (surface_cmd_load fp) (ci_core (core_cmd_load fp) :: nil)
  (** An open: its target, which may be a record value, whose members its
      items name accessible *)
  | fill_cmd_open : forall E E' op its,
      fill_mod (gs_tele Ξ) E E' op -> Forall (sel_ok op) (items_members its) ->
      fill_cmd (surface_cmd_open E its) (ci_core (core_cmd_open E' its) :: nil)
  (** A builtin binding: its type, a module *)
  | fill_cmd_builtin : forall k E E',
      fill_mod (gs_tele Ξ) E E' None -> fill_cmd (surface_cmd_builtin k E) (ci_core (core_cmd_builtin k E') :: nil)
  (** An evaluation with its type written: its term and its type *)
  | fill_cmd_eval : forall M M' A A',
      A <> surface_hole ->
      fill_exp (gs_tele Ξ) M M' -> fill_exp (gs_tele Ξ) A A' ->
      fill_cmd (surface_cmd_eval M A) (ci_core (core_cmd_eval M' A') :: nil)
  (** An evaluation without one: at the type its term infers *)
  | fill_cmd_eval_infer : forall M M' W,
      fill_exp (gs_tele Ξ) M M' -> ⊢ Θ ⍮ Ξ ⍮ gs_tele Ξ -> gs_tele Ξ ⊢a M' ⟹ W ->
      fill_cmd (surface_cmd_eval M surface_hole) (ci_core (core_cmd_eval M' (nf_to_exp W)) :: nil)
  (** A group: each part in the context the classification reads it in *)
  | fill_cmd_ind_decl : forall pv R R',
      fill_raw_decl R R' -> fill_cmd (surface_cmd_inductive pv R) (ci_core (core_cmd_inductive pv R') :: nil)
  (** A mutual definition: its telescope; its functions' heads, from
      which the group is read as [run_cmd_mdef] reads it; then their
      results and clauses, at the group, at the motives of the blocks of
      the filled functions *)
  | fill_cmd_mdef : forall b pv Δ Δ' f0 fs h0 hs f0' fs' pq m0 Ps D Us ms,
      fill_tele (gs_tele Ξ) Δ Δ' ->
      Forall2 (fill_raw_fun_head (Δ' ++ gs_tele Ξ)) (f0 :: fs) (h0 :: hs) ->
      mdef_group Θ Ξ Δ' h0 hs pq m0 Ps D Us ms ->
      Forall2 (fun fhm f' => fill_raw_fun_body pq D Us (Δ' ++ gs_tele Ξ)
                               (blocks_motives (mdef_blocks 0 (ind_nblk D) (f0' :: fs') ms))
                               (fst (fst fhm)) (snd (fst fhm)) (snd fhm) f')
        (List.combine (List.combine (f0 :: fs) (h0 :: hs)) ms) (f0' :: fs') ->
      fill_cmd (surface_cmd_mdef b pv Δ (f0 :: fs)) (ci_core (core_cmd_mdef b pv Δ' (f0' :: fs')) :: nil)
  (** A record declaration: its parameters, its sort over them, its
      fields over them and the fields before; its frame opened, its
      with-area as written, its frame closed *)
  | fill_cmd_record : forall x pv Δ Δ' Srt Srt' fs fs' cs,
      fill_tele (gs_tele Ξ) Δ Δ' -> fill_exp (Δ' ++ gs_tele Ξ) Srt Srt' ->
      fill_fields (Δ' ++ gs_tele Ξ) fs fs' ->
      fill_cmd (surface_cmd_record x pv Δ Srt fs cs)
        (ci_core (core_cmd_record_open x pv Δ' Srt' fs') :: List.map ci_written cs ++ ci_core (core_cmd_close x pv) :: nil).

  (** A unit's parameter telescope, over the frames', filled entry by
      entry. *)
  Definition fill_params (Δ : list surface_exp) (Δ' : ctx) : Prop := fill_tele (gs_tele Ξ) Δ Δ'.
End Fill.

#[export]
Hint Constructors module_read fill_exp fill_field_vals fill_blocks fill_scrutinee_type fill_brs fill_optional_exp
  fill_read fill_mod fill_unit fill_def fill_tele fill_body fill_fields fill_cmd : mctt.
