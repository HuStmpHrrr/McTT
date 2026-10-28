(** * The Typed Fill

    The elaborator is untyped, and leaves three things to the command
    judgment, which fills them in one depth-first pass over each command
    before the command runs, each part read in the context algorithmic
    typing ([alg_type_infer]) reads it in:

    - Literals: where the natural numbers are bound ([Builtin]), a numeral
      ([a_nlit]) stands for the chain of the bound type's constructors and
      the token [ℕ] ([a_ntok]) for its type former.  Without a binding a
      literal has no fill.
    - Eliminators: an eliminator as written carries no group and no
      uniform parameters ([a_elim None nil m Bks M]).  They are read off
      its scrutinee's inferred type ([elim_target]): the eliminator is
      filled when exactly one reading of it fits its blocks.
    - Accesses: for [e.f] the elaborator emits the member [f] of the
      module expression [e] stands for, and when [e] is a term (a term
      binder, a term member of a module, a term applied) that module
      expression has a term at its head, which no typing rule accepts.  A
      term [M] whose type infers to the record type [p] at the parameters
      [Rs] stands, in module position, for the record's module at [Rs],
      then [M] ([record_value_module]):
<<
    (λ (q : Pair ℕ ℕ) → q.fst)   is filled to   (λ (q : Pair ℕ ℕ) → (Pair ℕ ℕ q).fst)
>>
      A member selected from the module of a record value must be
      accessible ([sel_ok]): privacy is checked on the command as written,
      where the selection is from a term, so it is checked here once the
      record is known.

    Every command and every unit's parameter telescope is filled; a term
    with nothing to fill is filled to itself.  The filled command is
    ordinary core and runs as any command does.  The fill reads
    algorithmic inference ([⊢a]), which gives one type
    ([functional_alg_type_infer]), so the fill, and the run, are
    functional. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Command Builtin Records.
From Mctt.Core.Syntactic.System Require Import Privacy Translations.
From Mctt.Core.TypedElab Require Export ElimTarget.
From Mctt.Algorithmic.Typing Require Import Definitions.
Import Syntax_Notations.

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

  (** A term with no subterm and nothing to fill: filled to itself.  The
      literals are filled by their own rules. *)
  Definition exp_leaf (M : exp) : bool :=
    match M with
    | a_typ _ | a_level _ | a_llit _ | a_True | a_true | a_False
    | a_ind _ _ | a_con _ _ _ | a_var _ | a_record _ => true
    | _ => false
    end.

  (** The binder [k] of [Γ] holds a term only, an assumption or a
      definition, and so reads as a term in module position. *)
  Definition term_binder (Γ : ctx) (k : nat) : Prop :=
    match List.nth_error Γ k with
    | Some (ce_ass _) | Some (ce_def _ _) => True
    | _ => False
    end.

  (** The members an open's items name. *)
  Definition items_members (its : list iitem) : list string :=
    List.flat_map (fun it => match fst (fst it) with Some n => n :: nil | None => nil end) its.

  (** ** The Fill of Terms

      [fill_exp Γ M M']: the term [M], read in [Γ], filled, is [M'].  The
      contexts are those of algorithmic typing: a binder's type is its
      filled type; an unannotated [let] binds its definition at the type
      it infers; an eliminator's annotations, motives and branches are
      read in the contexts [alg_type_infer_elim] reads them in, at its group and its
      uniform parameters and filled motives; a local body's entries in the
      context of the expansion of the filled entries before them
      ([body_xp]). *)
  Inductive fill_exp : ctx -> exp -> exp -> Prop :=
  (** A term with no subterm and nothing to fill *)
  | fill_exp_leaf : forall Γ M, exp_leaf M = true -> fill_exp Γ M M
  (** A numeral: the chain of the bound type's constructors *)
  | fill_exp_nlit : forall Γ n p z s,
      nat_view Θ Ξ B = Some (p, z, s) -> fill_exp Γ (a_nlit n) (nat_chain p z s n)
  (** The token [ℕ]: the bound type's type former *)
  | fill_exp_ntok : forall Γ p z s,
      nat_view Θ Ξ B = Some (p, z, s) -> fill_exp Γ a_ntok (a_ind p 0)
  (** A universe at a level *)
  | fill_exp_univ : forall Γ M M', fill_exp Γ M M' -> fill_exp Γ (a_univ M) (a_univ M')
  (** A level's successor *)
  | fill_exp_succl : forall Γ M M', fill_exp Γ M M' -> fill_exp Γ (a_succl M) (a_succl M')
  (** A join of levels *)
  | fill_exp_maxl : forall Γ M M' N N', fill_exp Γ M M' -> fill_exp Γ N N' -> fill_exp Γ (a_maxl M N) (a_maxl M' N')
  (** [efq M return A]: the motive under a proof of [⊥] *)
  | fill_exp_exfalso : forall Γ A A' M M',
      fill_exp (Γ ▹ ⊥) A A' -> fill_exp Γ M M' -> fill_exp Γ (a_exfalso A M) (a_exfalso A' M')
  (** A [Π]: the codomain under the filled domain *)
  | fill_exp_pi : forall Γ A A' B B', fill_exp Γ A A' -> fill_exp (Γ ▹ A') B B' -> fill_exp Γ (a_pi A B) (a_pi A' B')
  (** A [λ]: the body under the filled domain *)
  | fill_exp_fn : forall Γ A A' M M', fill_exp Γ A A' -> fill_exp (Γ ▹ A') M M' -> fill_exp Γ (a_fn A M) (a_fn A' M')
  (** An application *)
  | fill_exp_app : forall Γ M M' N N', fill_exp Γ M M' -> fill_exp Γ N N' -> fill_exp Γ (a_app M N) (a_app M' N')
  (** A [let] with an annotation: the rest under the filled definition *)
  | fill_exp_let_ann : forall Γ A A' M M' B B',
      fill_exp Γ A A' -> fill_exp Γ M M' -> fill_exp (Γ ▸ A' ≔ M') B B' ->
      fill_exp Γ (a_let (b_def (Some A) M) B) (a_let (b_def (Some A') M') B')
  (** A [let] without one: the definition at the type it infers, as
      [alg_type_infer_let] reads it *)
  | fill_exp_let_infer : forall Γ M M' W B B',
      fill_exp Γ M M' -> ⊢ Θ ⍮ Ξ ⍮ Γ -> Γ ⊢a M' ⟹ W -> fill_exp (Γ ▸ nf_to_exp W ≔ M') B B' ->
      fill_exp Γ (a_let (b_def None M) B) (a_let (b_def None M') B')
  (** A local module: the rest under the filled unit *)
  | fill_exp_let_mod : forall Γ U U' B B',
      fill_unit Γ U U' -> fill_exp (Γ ▹ₘ U') B B' -> fill_exp Γ (a_let (b_mod U) B) (a_let (b_mod U') B')
  (** A member: its module filled; a member of a record value's module
      accessible *)
  | fill_exp_mem : forall Γ H H' op x,
      fill_mod Γ H H' op -> sel_ok op x -> fill_exp Γ (a_mem H x) (a_mem H' x)
  (** A record value: its type and its fields *)
  | fill_exp_tuple : forall Γ T T' fs fs',
      fill_exp Γ T T' -> fill_fvals Γ fs fs' -> fill_exp Γ (a_tuple T fs) (a_tuple T' fs')
  (** A projection *)
  | fill_exp_proj : forall Γ f M M', fill_exp Γ M M' -> fill_exp Γ (a_proj f M) (a_proj f M')
  (** An eliminator as written: its scrutinee filled; its group [p] and
      uniform parameters [Us] the one reading of it that fits its blocks,
      read off the scrutinee's inferred type ([elim_target]); its blocks
      at them and at the filled motives *)
  | fill_exp_elim : forall Γ m Bks Bks' M M' pc k Rs p D Us,
      fill_exp Γ M M' ->
      ⊢ Θ ⍮ Ξ ⍮ Γ ->
      Γ ⊢a M' ⟹ nf_indty pc k Rs ->
      elim_target Θ Ξ pc k Rs m Bks = elim_target_one p Us ->
      ind_lookup Θ Ξ p = Some D ->
      fill_blocks Γ p D Us (blocks_motives Bks') 0 Bks Bks' ->
      fill_exp Γ (a_elim None nil m Bks M) (a_elim (Some p) Us m Bks' M')

  (** The fields of a record value, each its name and its value *)
  with fill_fvals : ctx -> list (string * exp) -> list (string * exp) -> Prop :=
  (** No field *)
  | fill_fvals_nil : forall Γ, fill_fvals Γ nil nil
  (** The first field, then the rest *)
  | fill_fvals_cons : forall Γ f M M' fs fs',
      fill_exp Γ M M' -> fill_fvals Γ fs fs' -> fill_fvals Γ ((f, M) :: fs) ((f, M') :: fs')

  (** The blocks of an eliminator of the group [p], [D], from the member
      [j] on, at the uniform parameters [Us] and the motives [As]: each its
      annotation over its member's non-uniform parameters, its motive over
      them and the scrutinee, and its branches, with as many binders as
      [alg_type_infer_elim] asks *)
  with fill_blocks : ctx -> qname -> ind_decl -> list exp -> list exp -> nat -> list eblock -> list eblock -> Prop :=
  (** No block *)
  | fill_blocks_nil : forall Γ p D Us As j, fill_blocks Γ p D Us As j nil nil
  (** The block of the member [j], then the rest *)
  | fill_blocks_cons : forall Γ p D Us As j Mj nm oZ oZ' A A' Bs Bs' Bks Bks',
      ind_member D j = Some Mj ->
      nm = S (im_nn Mj) ->
      fill_oexp (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) oZ oZ' ->
      fill_exp (elim_mctx p D j Mj Us ++ Γ) A A' ->
      fill_brs Γ p D Mj Us As Bs Bs' ->
      fill_blocks Γ p D Us As (S j) Bks Bks' ->
      fill_blocks Γ p D Us As j (eb_mk nm oZ A Bs :: Bks) (eb_mk nm oZ' A' Bs' :: Bks')

  (** The branches of a block of the member [Mj], each in its
      constructor's branch context *)
  with fill_brs : ctx -> qname -> ind_decl -> imember -> list exp -> list exp ->
                  list (string * nat * exp) -> list (string * nat * exp) -> Prop :=
  (** No branch *)
  | fill_brs_nil : forall Γ p D Mj Us As, fill_brs Γ p D Mj Us As nil nil
  (** The branch of the constructor [c], then the rest *)
  | fill_brs_cons : forall Γ p D Mj Us As c gs n B B' Bs Bs',
      ind_con Mj c = Some gs ->
      n = (im_nn Mj + List.length gs + cargs_nrec D gs)%nat ->
      fill_exp (elim_bctx p D Mj gs As Us ++ Γ) B B' ->
      fill_brs Γ p D Mj Us As Bs Bs' ->
      fill_brs Γ p D Mj Us As ((c, n, B) :: Bs) ((c, n, B') :: Bs')

  (** A term that may be absent *)
  with fill_oexp : ctx -> option exp -> option exp -> Prop :=
  (** Absent *)
  | fill_oexp_none : forall Γ, fill_oexp Γ None None
  (** Present *)
  | fill_oexp_some : forall Γ M M', fill_exp Γ M M' -> fill_oexp Γ (Some M) (Some M')

  (** [fill_read Γ H r]: in module position, [H] reads as [r] *)
  with fill_read : ctx -> modexp -> module_read -> Prop :=
  (** A unit *)
  | fill_read_unit : forall Γ fp, fill_read Γ (me_unit fp) (read_module (me_unit fp))
  (** A binder that is no term binder: a module slot, a definition with a
      module part (read as its module part, as a member with a term part
      and a module part is), or nothing, which typing rejects *)
  | fill_read_slot : forall Γ k, ~ term_binder Γ k -> fill_read Γ (me_var k) (read_module (me_var k))
  (** A term binder: the term *)
  | fill_read_var : forall Γ k, term_binder Γ k -> fill_read Γ (me_var k) (read_term (a_var k))
  (** A module literal *)
  | fill_read_lit : forall Γ U U', fill_unit Γ U U' -> fill_read Γ (me_lit U) (read_module (me_lit U'))
  (** A member that is no term: a module, or nothing, which typing
      rejects *)
  | fill_read_mem_module : forall Γ H H' op y,
      fill_mod Γ H H' op -> sel_ok op y ->
      (forall A oM, ~ mdenote Θ Ξ Γ (me_mem H' y) (mdesc_term A oM)) ->
      fill_read Γ (me_mem H y) (read_module (me_mem H' y))
  (** A member that is a term: the term *)
  | fill_read_mem_term : forall Γ H H' op y A oM,
      fill_mod Γ H H' op -> sel_ok op y ->
      mdenote Θ Ξ Γ (me_mem H' y) (mdesc_term A oM) ->
      fill_read Γ (me_mem H y) (read_term (a_mem H' y))
  (** A module applied: a module *)
  | fill_read_app_module : forall Γ H H' N N',
      fill_read Γ H (read_module H') -> fill_exp Γ N N' -> fill_read Γ (me_app H N) (read_module (me_app H' N'))
  (** A term applied: a term *)
  | fill_read_app_term : forall Γ H M N N',
      fill_read Γ H (read_term M) -> fill_exp Γ N N' -> fill_read Γ (me_app H N) (read_term (a_app M N'))

  (** [fill_mod Γ H H' op]: in module position, [H] is the module [H'];
      [op] is the record [H'] is the module of a value of, when [H] has a
      term at its head *)
  with fill_mod : ctx -> modexp -> modexp -> option qname -> Prop :=
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
  with fill_unit : ctx -> gunit -> gunit -> Prop :=
  (** The only rule: the telescope filled, then the definition under the
      filled telescope *)
  | fill_unit_mk : forall Γ Δ Δ' D D',
      fill_tele Γ Δ Δ' -> fill_def (Δ' ++ Γ) D D' -> fill_unit Γ (gu_mk Δ D) (gu_mk Δ' D')

  (** A unit's definition *)
  with fill_def : ctx -> moddef -> moddef -> Prop :=
  (** An alias: its target, which may be a record value *)
  | fill_def_alias : forall Γ E E' op, fill_mod Γ E E' op -> fill_def Γ (md_alias E) (md_alias E')
  (** A body *)
  | fill_def_body : forall Γ sm Φ Φ', fill_body Γ Φ Φ' -> fill_def Γ (md_body sm Φ) (md_body sm Φ')

  (** A telescope, innermost first, each entry over the filled ones after
      it *)
  with fill_tele : ctx -> ctx -> ctx -> Prop :=
  (** The empty telescope *)
  | fill_tele_nil : forall Γ, fill_tele Γ nil nil
  (** An assumption *)
  | fill_tele_ass : forall Γ Δ Δ' A A',
      fill_tele Γ Δ Δ' -> fill_exp (Δ' ++ Γ) A A' -> fill_tele Γ (ce_ass A :: Δ) (ce_ass A' :: Δ')
  (** A definition *)
  | fill_tele_def : forall Γ Δ Δ' A A' M M',
      fill_tele Γ Δ Δ' -> fill_exp (Δ' ++ Γ) A A' -> fill_exp (Δ' ++ Γ) M M' ->
      fill_tele Γ (ce_def A M :: Δ) (ce_def A' M' :: Δ')
  (** A module slot *)
  | fill_tele_mod : forall Γ Δ Δ' U U',
      fill_tele Γ Δ Δ' -> fill_unit (Δ' ++ Γ) U U' -> fill_tele Γ (ce_mod U :: Δ) (ce_mod U' :: Δ')
  (** A definition with a module part: its parts, each over the filled
      entries after it *)
  | fill_tele_dm : forall Γ Δ Δ' A A' M M' U U',
      fill_tele Γ Δ Δ' -> fill_exp (Δ' ++ Γ) A A' -> fill_exp (Δ' ++ Γ) M M' -> fill_unit (Δ' ++ Γ) U U' ->
      fill_tele Γ (ce_dm A M U :: Δ) (ce_dm A' M' U' :: Δ')

  (** A local body, entry by entry, each in the context of the expansion
      of the filled entries before it *)
  with fill_body : ctx -> gmod -> gmod -> Prop :=
  (** The empty body *)
  | fill_body_nil : forall Γ, fill_body Γ gm_nil gm_nil
  (** A definition *)
  | fill_body_def : forall Γ Φ Φ' Φx x b pv A A' oM oM',
      fill_body Γ Φ Φ' -> body_xp Θ Ξ Γ Φ' Φx ->
      fill_exp (body_ctx Φx ++ Γ) A A' -> fill_oexp (body_ctx Φx ++ Γ) oM oM' ->
      fill_body Γ (gm_ext Φ x (ge_def b pv A oM)) (gm_ext Φ' x (ge_def b pv A' oM'))
  (** A module *)
  | fill_body_mod : forall Γ Φ Φ' Φx x pv U U',
      fill_body Γ Φ Φ' -> body_xp Θ Ξ Γ Φ' Φx -> fill_unit (body_ctx Φx ++ Γ) U U' ->
      fill_body Γ (gm_ext Φ x (ge_mod pv U)) (gm_ext Φ' x (ge_mod pv U'))
  (** A definition with a module part: its type, its term and its unit *)
  | fill_body_dm : forall Γ Φ Φ' Φx x pv A A' M M' U U',
      fill_body Γ Φ Φ' -> body_xp Θ Ξ Γ Φ' Φx ->
      fill_exp (body_ctx Φx ++ Γ) A A' -> fill_exp (body_ctx Φx ++ Γ) M M' -> fill_unit (body_ctx Φx ++ Γ) U U' ->
      fill_body Γ (gm_ext Φ x (ge_def_mod pv A M U)) (gm_ext Φ' x (ge_def_mod pv A' M' U'))
  (** A local open: its target, which may be a record value, whose
      members its items name accessible *)
  | fill_body_open : forall Γ Φ Φ' Φx H H' op its,
      fill_body Γ Φ Φ' -> body_xp Θ Ξ Γ Φ' Φx -> fill_mod (body_ctx Φx ++ Γ) H H' op ->
      Forall (sel_ok op) (items_members its) ->
      fill_body Γ (gm_open Φ H its) (gm_open Φ' H' its).

  Scheme fill_exp_mut_ind := Induction for fill_exp Sort Prop
  with fill_fvals_mut_ind := Induction for fill_fvals Sort Prop
  with fill_blocks_mut_ind := Induction for fill_blocks Sort Prop
  with fill_brs_mut_ind := Induction for fill_brs Sort Prop
  with fill_oexp_mut_ind := Induction for fill_oexp Sort Prop
  with fill_read_mut_ind := Induction for fill_read Sort Prop
  with fill_mod_mut_ind := Induction for fill_mod Sort Prop
  with fill_unit_mut_ind := Induction for fill_unit Sort Prop
  with fill_def_mut_ind := Induction for fill_def Sort Prop
  with fill_tele_mut_ind := Induction for fill_tele Sort Prop
  with fill_body_mut_ind := Induction for fill_body Sort Prop.
  Combined Scheme fill_mut_ind from fill_exp_mut_ind, fill_fvals_mut_ind, fill_blocks_mut_ind, fill_brs_mut_ind,
    fill_oexp_mut_ind, fill_read_mut_ind, fill_mod_mut_ind, fill_unit_mut_ind, fill_def_mut_ind,
    fill_tele_mut_ind, fill_body_mut_ind.

  (** The fields of a record declaration, each over the filled ones before
      it ([record_fctx]) *)
  Inductive fill_fields : ctx -> list (string * typ) -> list (string * typ) -> Prop :=
  (** No field *)
  | fill_fields_nil : forall Γ, fill_fields Γ nil nil
  (** The first field, then the rest over it *)
  | fill_fields_cons : forall Γ f T T' fs fs',
      fill_exp Γ T T' -> fill_fields (Γ ▹ T') fs fs' -> fill_fields Γ ((f, T) :: fs) ((f, T') :: fs').

  (** ** The Fill of Commands

      Each part of a command is filled in the context its run reads it in.
      A mutual definition's functions are filled in two steps: their
      parameters and scrutinees, from which the group is read
      ([mdef_group]), then their results and clauses, in the contexts the
      eliminator its translation files ([mdef_defs]) reads them in, at the
      motives of the translation's own blocks ([mdef_blocks]). *)

  (** A function of a mutual definition over [Γ], its parameters and
      scrutinee filled, as [run_cmd_mdef] reads them, to [f']. *)
  Record fill_raw_fun_head (Γ : ctx) (f f' : raw_fun) : Prop := mk_fill_raw_fun_head
    { (** The name is kept *)
      fill_raw_fun_head_name : raw_fun_name f' = raw_fun_name f
      (** The parameters, over [Γ], are filled *)
    ; fill_raw_fun_head_nparams : fill_tele Γ (raw_fun_nparams f) (raw_fun_nparams f')
      (** The scrutinee's type, over the filled parameters, is filled *)
    ; fill_raw_fun_head_scrut : fill_exp (raw_fun_nparams f' ++ Γ) (raw_fun_scrut f) (raw_fun_scrut f')
      (** The result type is kept, filled with the clauses *)
    ; fill_raw_fun_head_res : raw_fun_res f' = raw_fun_res f
      (** The clauses are kept, filled with the result type *)
    ; fill_raw_fun_head_clauses : raw_fun_clauses f' = raw_fun_clauses f }.

  (** A function [f] of the member [m] of the group [D] at [pq], at the
      uniform parameters [Us] and the motives [As], over [Γ], its result
      and clauses filled to [f']: the result in the motive's context, the
      clauses in their branches', as [alg_type_infer_elim] reads them. *)
  Record fill_raw_fun_body (pq : qname) (D : ind_decl) (Us : list exp) (Γ : ctx) (As : list exp)
      (f : raw_fun) (m : nat) (f' : raw_fun) : Prop := mk_fill_raw_fun_body
    { (** The name is kept *)
      fill_raw_fun_body_name : raw_fun_name f' = raw_fun_name f
      (** The parameters are kept, filled already *)
    ; fill_raw_fun_body_nparams : raw_fun_nparams f' = raw_fun_nparams f
      (** The scrutinee's type is kept, filled already *)
    ; fill_raw_fun_body_scrut : raw_fun_scrut f' = raw_fun_scrut f
      (** The member is one of the group *)
    ; fill_raw_fun_body_member : ind_member D m <> None
      (** The result type, over the member's parameters and the scrutinee,
          is filled *)
    ; fill_raw_fun_body_res : forall Mm, ind_member D m = Some Mm ->
        fill_exp (elim_mctx pq D m Mm Us ++ Γ) (raw_fun_res f) (raw_fun_res f')
      (** The clauses, each in its constructor's branch context, are
          filled *)
    ; fill_raw_fun_body_clauses : forall Mm, ind_member D m = Some Mm ->
        fill_brs Γ pq D Mm Us As (raw_fun_clauses f) (raw_fun_clauses f') }.

  (** A constructor's arguments over [Γ], filled: the names kept, the
      types filled as a telescope, each over the ones before it, as
      [cls_args_in] reads them. *)
  Record fill_raw_args (Γ : ctx) (args args' : list (string * exp)) : Prop := mk_fill_raw_args
    { (** The names are kept *)
      fill_raw_args_names : List.map fst args' = List.map fst args
      (** The types, each over the ones before it, are filled *)
    ; fill_raw_args_types : fill_tele Γ (rtele args) (rtele args') }.

  (** A declared member [Mr] of a group whose filled form is [R'], filled
      to [Mr']: its parameters and sort over the uniform parameters, its
      constructors' arguments over its context ([rm_pctx]), in the filled
      group. *)
  Record fill_raw_member (R' : raw_decl) (Mr Mr' : raw_member) : Prop := mk_fill_raw_member
    { (** The name is kept *)
      fill_raw_member_name : raw_member_name Mr' = raw_member_name Mr
      (** The parameters, over the uniform ones, are filled *)
    ; fill_raw_member_nparams : fill_tele (raw_decl_uparams R' ++ gs_tele Ξ) (raw_member_nparams Mr) (raw_member_nparams Mr')
      (** The sort, over the uniform parameters, is filled *)
    ; fill_raw_member_sort : fill_exp (raw_decl_uparams R' ++ gs_tele Ξ) (raw_member_sort Mr) (raw_member_sort Mr')
      (** Each constructor keeps its name, and its arguments are filled
          over the member's context *)
    ; fill_raw_member_cons :
        Forall2 (fun rc rc' => fst rc' = fst rc /\ fill_raw_args (rm_pctx Ξ R' Mr') (snd rc) (snd rc'))
          (raw_member_cons Mr) (raw_member_cons Mr') }.

  (** [fill_raw_decl R R']: the group as written [R] is filled to [R'],
      each part in the context the classification reads it in. *)
  Record fill_raw_decl (R R' : raw_decl) : Prop := mk_fill_raw_decl
    { (** The uniform parameters, over the frames', are filled *)
      fill_raw_decl_uparams : fill_tele (gs_tele Ξ) (raw_decl_uparams R) (raw_decl_uparams R')
      (** Whether the group files its recursor module is kept *)
    ; fill_raw_decl_rec : raw_decl_rec_field R' = raw_decl_rec_field R
      (** Each declared member is filled, in order *)
    ; fill_raw_decl_members : Forall2 (fill_raw_member R') (raw_decl_members R) (raw_decl_members R') }.

  (** [fill_cmd c c']: the command [c] is filled to [c'], its terms read in
      the frames' telescope.  One rule per kind of command; a module's
      nested commands, and a record's with-area, are filled when they
      run, and a generated command is filled to itself ([core_cmd_gen]). *)
  Inductive fill_cmd : core_cmd -> core_cmd -> Prop :=
  (** A definition: its type and its body *)
  | fill_cmd_def : forall x b pv A A' oM oM',
      fill_exp (gs_tele Ξ) A A' -> fill_oexp (gs_tele Ξ) oM oM' ->
      fill_cmd (core_cmd_def x b pv A oM) (core_cmd_def x b pv A' oM')
  (** A module: its telescope; its commands are filled when they run *)
  | fill_cmd_mod : forall x pv Δ Δ' cs,
      fill_tele (gs_tele Ξ) Δ Δ' -> fill_cmd (core_cmd_mod x pv Δ cs) (core_cmd_mod x pv Δ' cs)
  (** A module alias: its telescope, then its target, which may be a
      record value *)
  | fill_cmd_alias : forall x pv Δ Δ' E E' op,
      fill_tele (gs_tele Ξ) Δ Δ' -> fill_mod (Δ' ++ gs_tele Ξ) E E' op ->
      fill_cmd (core_cmd_alias x pv Δ E) (core_cmd_alias x pv Δ' E')
  (** An inductive alias: its telescope, then its target, a module *)
  | fill_cmd_ind_alias : forall x pv Δ Δ' E E',
      fill_tele (gs_tele Ξ) Δ Δ' -> fill_mod (Δ' ++ gs_tele Ξ) E E' None ->
      fill_cmd (core_cmd_inductive_alias x pv Δ E) (core_cmd_inductive_alias x pv Δ' E')
  (** A record alias: its telescope, then its target, a module *)
  | fill_cmd_record_alias : forall x pv Δ Δ' E E',
      fill_tele (gs_tele Ξ) Δ Δ' -> fill_mod (Δ' ++ gs_tele Ξ) E E' None ->
      fill_cmd (core_cmd_record_alias x pv Δ E) (core_cmd_record_alias x pv Δ' E')
  (** A load: itself *)
  | fill_cmd_load : forall fp, fill_cmd (core_cmd_load fp) (core_cmd_load fp)
  (** An open: its target, which may be a record value, whose members its
      items name accessible *)
  | fill_cmd_open : forall E E' op its,
      fill_mod (gs_tele Ξ) E E' op -> Forall (sel_ok op) (items_members its) ->
      fill_cmd (core_cmd_open E its) (core_cmd_open E' its)
  (** A builtin binding: its type, a module *)
  | fill_cmd_builtin : forall k E E',
      fill_mod (gs_tele Ξ) E E' None -> fill_cmd (core_cmd_builtin k E) (core_cmd_builtin k E')
  (** An evaluation: its term and its type *)
  | fill_cmd_eval : forall M M' oA oA',
      fill_exp (gs_tele Ξ) M M' -> fill_oexp (gs_tele Ξ) oA oA' -> fill_cmd (core_cmd_eval M oA) (core_cmd_eval M' oA')
  (** A group: each part in the context the classification reads it in *)
  | fill_cmd_ind_decl : forall pv R R', fill_raw_decl R R' -> fill_cmd (core_cmd_inductive pv R) (core_cmd_inductive pv R')
  (** A mutual definition: its telescope; its functions' parameters and
      scrutinees, from which the group is read as [run_cmd_mdef] reads it; then
      their results and clauses, at the group, at the motives of the
      blocks of the filled functions *)
  | fill_cmd_mdef : forall b pv Δ Δ' f0 fs fh0 fsh f0' fs' pq m0 Ps D Us ms,
      fill_tele (gs_tele Ξ) Δ Δ' ->
      Forall2 (fill_raw_fun_head (Δ' ++ gs_tele Ξ)) (f0 :: fs) (fh0 :: fsh) ->
      mdef_group Θ Ξ Δ' fh0 fsh pq m0 Ps D Us ms ->
      Forall2 (fun fm f' => fill_raw_fun_body pq D Us (Δ' ++ gs_tele Ξ)
                              (blocks_motives (mdef_blocks 0 (ind_nblk D) (f0' :: fs') ms))
                              (fst fm) (snd fm) f')
        (List.combine (fh0 :: fsh) ms) (f0' :: fs') ->
      fill_cmd (core_cmd_mdef b pv Δ (f0 :: fs)) (core_cmd_mdef b pv Δ' (f0' :: fs'))
  (** A record declaration: its parameters, its sort over them, its
      fields over them and the fields before; its with-area is filled
      when it runs *)
  | fill_cmd_record : forall x pv Δ Δ' Srt Srt' fs fs' cs,
      fill_tele (gs_tele Ξ) Δ Δ' -> fill_exp (Δ' ++ gs_tele Ξ) Srt Srt' ->
      fill_fields (Δ' ++ gs_tele Ξ) fs fs' ->
      fill_cmd (core_cmd_record x pv Δ Srt fs cs) (core_cmd_record x pv Δ' Srt' fs' cs)
  (** A generated command: itself *)
  | fill_cmd_gen : forall c, fill_cmd (core_cmd_gen c) (core_cmd_gen c).

  (** A unit's parameter telescope, over the frames', filled entry by
      entry. *)
  Definition fill_params (Δ Δ' : ctx) : Prop := fill_tele (gs_tele Ξ) Δ Δ'.
End Fill.

#[export]
Hint Constructors module_read fill_exp fill_fvals fill_blocks fill_brs fill_oexp fill_read
  fill_mod fill_unit fill_def fill_tele fill_body fill_fields fill_cmd : mctt.
