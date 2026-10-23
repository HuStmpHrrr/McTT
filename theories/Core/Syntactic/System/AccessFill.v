(** * The Access Fill

    The elaborator is untyped: for [e.f] it emits the member [f] of the
    module expression [e] stands for, and when [e] is a term (a term
    binder, a term member of a module, a term applied), that module
    expression has a term at its head.  No typing rule accepts such a
    module expression.  When a command runs, after its literals and its
    eliminator fill, the access fill rewrites each one: a term [M] whose
    type infers to the record type [p] at the parameters [Rs] stands, in
    module position, for the record's module at [Rs], then [M]
    ([record_value_module]):

<<
    (λ (q : Pair ℕ ℕ) → q.fst)   is filled to   (λ (q : Pair ℕ ℕ) → (Pair ℕ ℕ q).fst)
>>

    The filled command is ordinary core and runs as any command does.

    - An access is a module position whose module expression has a term
      at its head ([fill_read]): a term binder, [me_var k] at a [k] that
      holds a term, as [q] above; or a member of a module that is a term,
      [me_mem H y] where [H.y] denotes a term, as [M.x] in [M.x.f] for a
      definition [x] of a record type.  Either may be applied to
      arguments, as [(g 3).fst] for a function [g] into a record type.
    - A command with no access ([cmd_access_free]) is filled to itself
      ([fill_cmd_plain]), with no typing.  Any other command is filled
      part by part, in the contexts algorithmic typing ([alg_type_infer])
      reads its parts in: that is where an access's term is inferred.
      The fill of a whole command ([fill_cmd]) is in [System.Command],
      next to the translations of inductive and mutual definitions whose
      contexts it reads; this file fills terms, telescopes and module
      expressions.
    - A member selected from the module of a record value must be
      accessible ([sel_ok]): privacy is checked on the command as written,
      where the selection is from a term, so it is checked here once the
      record is known.

    The command judgment reads algorithmic inference ([⊢a]) here: the
    record an access goes through is decided by its head's inferred type,
    and inference, unlike declarative typing, gives one type
    ([functional_alg_type_infer]), so the fill, and the run, are
    functional. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Command Builtin Records.
From Mctt.Core.Syntactic.System Require Import Privacy.
From Mctt.Algorithmic.Typing Require Import Definitions.
Import Syntax_Notations.

(** ** Skeletons

    What a context says of its binders' kinds: a module slot is kept with
    its unit, any other binder is a hole.  Which module expressions have a
    term at their head depends on the context through its skeleton only. *)
Definition ctx_skeleton (Γ : ctx) : ctx :=
  List.map (fun e => match e with ce_mod U => ce_mod U | _ => ce_hole end) Γ.

Section AccessFill.
  Variables (Θ : gdeps) (Ξ : gstack).
  #[local] Instance GC : GCtx := gc_mk Θ Ξ.

  (** The module of the record [p] at the parameters [Rs], at the value
      [M]: the record's module applied to its full telescope
      ([record_mod_tele]), the parameters then the value. *)
  Definition record_value_module (p : qname) (Rs : nfs) (M : exp) : modexp :=
    me_apps (qname_mod p) (nfs_to_exps Rs ++ M :: nil).

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

  (** A term with no subterm: filled to itself. *)
  Definition exp_leaf (M : exp) : bool :=
    match M with
    | a_typ _ | a_level _ | a_llit _ | a_ntok | a_True | a_true | a_False
    | a_ind _ _ | a_con _ _ _ | a_nlit _ | a_var _ | a_record _ => true
    | _ => false
    end.

  (** The members an open's items name. *)
  Definition items_members (its : list iitem) : list string :=
    List.flat_map (fun it => match fst (fst it) with Some n => n :: nil | None => nil end) its.

  (** ** The Fill

      [fill_exp Γ M M']: the term [M], read in [Γ], every access in it
      filled, is [M'].  The contexts are those of algorithmic typing: a
      binder's type is its filled type; an unannotated [let] binds its
      definition at the type it infers; an eliminator's annotations,
      motives and branches are read in the contexts [ati_elim] reads them
      in, at its group and its filled uniform parameters and motives; a
      local body's entries in the context of the expansion of the filled
      entries before them ([body_xp]). *)
  Inductive fill_exp : ctx -> exp -> exp -> Prop :=
  (** A term with no subterm *)
  | fill_exp_leaf : forall Γ M, exp_leaf M = true -> fill_exp Γ M M
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
      [ati_let] reads it *)
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
  (** An eliminator: its scrutinee; its group [p], the one it names, or,
      unnamed, the one of its scrutinee's inferred type; its uniform
      parameters; its blocks at the filled parameters and motives *)
  | fill_exp_elim : forall Γ oq p D Us Us' m Bks Bks' M M',
      fill_exp Γ M M' ->
      elim_group Γ oq M' p ->
      ind_lookup Θ Ξ p = Some D ->
      fill_exps Γ Us Us' ->
      fill_blocks Γ p D Us' (blocks_motives Bks') 0 Bks Bks' ->
      fill_exp Γ (a_elim oq Us m Bks M) (a_elim oq Us' m Bks' M')

  (** The group an eliminator is of *)
  with elim_group : ctx -> option qname -> exp -> qname -> Prop :=
  (** The group it names *)
  | elim_group_named : forall Γ p M, elim_group Γ (Some p) M p
  (** Unnamed, the group of the scrutinee's inferred type *)
  | elim_group_inferred : forall Γ M p k Rs,
      ⊢ Θ ⍮ Ξ ⍮ Γ -> Γ ⊢a M ⟹ nf_indty p k Rs -> elim_group Γ None M p

  (** Terms side by side, each in the same context *)
  with fill_exps : ctx -> list exp -> list exp -> Prop :=
  (** No term *)
  | fill_exps_nil : forall Γ, fill_exps Γ nil nil
  (** The first term, then the rest *)
  | fill_exps_cons : forall Γ M M' Ms Ms', fill_exp Γ M M' -> fill_exps Γ Ms Ms' -> fill_exps Γ (M :: Ms) (M' :: Ms')

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
      [ati_elim] asks *)
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
      n = (im_nn Mj + List.length gs + cargs_nrec gs)%nat ->
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
  (** A binder that holds no term: a module slot, or nothing, which typing
      rejects *)
  | fill_read_slot : forall Γ k, (forall A, ~ Γ ∋ #k : A) -> fill_read Γ (me_var k) (read_module (me_var k))
  (** A term binder: the term *)
  | fill_read_var : forall Γ k A, Γ ∋ #k : A -> fill_read Γ (me_var k) (read_term (a_var k))
  (** A module literal *)
  | fill_read_lit : forall Γ U U', fill_unit Γ U U' -> fill_read Γ (me_lit U) (read_module (me_lit U'))
  (** A member that is no term: a module, or nothing, which typing
      rejects *)
  | fill_read_mem_module : forall Γ H H' op y,
      fill_mod Γ H H' op -> sel_ok op y ->
      (forall A oM, ~ mdenote Θ Ξ Γ (me_mem H' y) (ds_term A oM)) ->
      fill_read Γ (me_mem H y) (read_module (me_mem H' y))
  (** A member that is a term: the term *)
  | fill_read_mem_term : forall Γ H H' op y A oM,
      fill_mod Γ H H' op -> sel_ok op y ->
      mdenote Θ Ξ Γ (me_mem H' y) (ds_term A oM) ->
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
  (** A local open: its target, which may be a record value, whose
      members its items name accessible *)
  | fill_body_open : forall Γ Φ Φ' Φx H H' op its,
      fill_body Γ Φ Φ' -> body_xp Θ Ξ Γ Φ' Φx -> fill_mod (body_ctx Φx ++ Γ) H H' op ->
      Forall (sel_ok op) (items_members its) ->
      fill_body Γ (gm_open Φ H its) (gm_open Φ' H' its).

  Scheme fill_exp_mut_ind := Induction for fill_exp Sort Prop
  with elim_group_mut_ind := Induction for elim_group Sort Prop
  with fill_exps_mut_ind := Induction for fill_exps Sort Prop
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
  Combined Scheme fill_mut_ind from fill_exp_mut_ind, elim_group_mut_ind, fill_exps_mut_ind, fill_fvals_mut_ind,
    fill_blocks_mut_ind, fill_brs_mut_ind, fill_oexp_mut_ind, fill_read_mut_ind, fill_mod_mut_ind,
    fill_unit_mut_ind, fill_def_mut_ind, fill_tele_mut_ind, fill_body_mut_ind.

  (** The fields of a record declaration, each over the filled ones before
      it ([record_fctx]) *)
  Inductive fill_fields : ctx -> list (string * typ) -> list (string * typ) -> Prop :=
  (** No field *)
  | fill_fields_nil : forall Γ, fill_fields Γ nil nil
  (** The first field, then the rest over it *)
  | fill_fields_cons : forall Γ f T T' fs fs',
      fill_exp Γ T T' -> fill_fields (Γ ▹ T') fs fs' -> fill_fields Γ ((f, T) :: fs) ((f, T') :: fs').

  (** ** Access-Free Terms

      [access_free_exp Γ M]: no module position in [M] has a term at its
      head, as [fill_read] reads it.  The contexts are skeletons: every
      binder that is no module slot is a hole ([ce_hole]), and an
      eliminator's blocks bind as many holes as they say.  Nothing here is
      typed. *)
  Inductive access_free_exp : ctx -> exp -> Prop :=
  (** A term with no subterm *)
  | access_free_exp_leaf : forall Γ M, exp_leaf M = true -> access_free_exp Γ M
  (** A universe at a level *)
  | access_free_exp_univ : forall Γ M, access_free_exp Γ M -> access_free_exp Γ (a_univ M)
  (** A level's successor *)
  | access_free_exp_succl : forall Γ M, access_free_exp Γ M -> access_free_exp Γ (a_succl M)
  (** A join of levels *)
  | access_free_exp_maxl : forall Γ M N, access_free_exp Γ M -> access_free_exp Γ N -> access_free_exp Γ (a_maxl M N)
  (** [efq M return A] *)
  | access_free_exp_exfalso : forall Γ A M,
      access_free_exp (ce_hole :: Γ) A -> access_free_exp Γ M -> access_free_exp Γ (a_exfalso A M)
  (** A [Π] *)
  | access_free_exp_pi : forall Γ A B,
      access_free_exp Γ A -> access_free_exp (ce_hole :: Γ) B -> access_free_exp Γ (a_pi A B)
  (** A [λ] *)
  | access_free_exp_fn : forall Γ A M,
      access_free_exp Γ A -> access_free_exp (ce_hole :: Γ) M -> access_free_exp Γ (a_fn A M)
  (** An application *)
  | access_free_exp_app : forall Γ M N, access_free_exp Γ M -> access_free_exp Γ N -> access_free_exp Γ (a_app M N)
  (** A [let] of a definition, with or without an annotation *)
  | access_free_exp_let : forall Γ oA M B,
      access_free_oexp Γ oA -> access_free_exp Γ M -> access_free_exp (ce_hole :: Γ) B ->
      access_free_exp Γ (a_let (b_def oA M) B)
  (** A local module *)
  | access_free_exp_let_mod : forall Γ U B,
      access_free_unit Γ U -> access_free_exp (ce_mod U :: Γ) B -> access_free_exp Γ (a_let (b_mod U) B)
  (** A member of a module with no term at its head *)
  | access_free_exp_mem : forall Γ H x, access_free_mod Γ H -> access_free_exp Γ (a_mem H x)
  (** A record value *)
  | access_free_exp_tuple : forall Γ T fs,
      access_free_exp Γ T -> access_free_fvals Γ fs -> access_free_exp Γ (a_tuple T fs)
  (** A projection *)
  | access_free_exp_proj : forall Γ f M, access_free_exp Γ M -> access_free_exp Γ (a_proj f M)
  (** An eliminator: its scrutinee, its uniform parameters, and its
      blocks, each binding as many holes as it says *)
  | access_free_exp_elim : forall Γ oq Us m Bks M,
      access_free_exp Γ M -> access_free_exps Γ Us -> access_free_blocks Γ Bks ->
      access_free_exp Γ (a_elim oq Us m Bks M)

  (** Terms side by side *)
  with access_free_exps : ctx -> list exp -> Prop :=
  (** No term *)
  | access_free_exps_nil : forall Γ, access_free_exps Γ nil
  (** The first term, then the rest *)
  | access_free_exps_cons : forall Γ M Ms,
      access_free_exp Γ M -> access_free_exps Γ Ms -> access_free_exps Γ (M :: Ms)

  (** The fields of a record value *)
  with access_free_fvals : ctx -> list (string * exp) -> Prop :=
  (** No field *)
  | access_free_fvals_nil : forall Γ, access_free_fvals Γ nil
  (** The first field, then the rest *)
  | access_free_fvals_cons : forall Γ f M fs,
      access_free_exp Γ M -> access_free_fvals Γ fs -> access_free_fvals Γ ((f, M) :: fs)

  (** The blocks of an eliminator: each its annotation under one hole
      fewer than its motive binds, its motive under them, its branches each
      under as many holes as it binds *)
  with access_free_blocks : ctx -> list eblock -> Prop :=
  (** No block *)
  | access_free_blocks_nil : forall Γ, access_free_blocks Γ nil
  (** The first block, then the rest *)
  | access_free_blocks_cons : forall Γ nm oZ A Bs Bks,
      access_free_oexp (ctx_holes (nm - 1) ++ Γ) oZ -> access_free_exp (ctx_holes nm ++ Γ) A ->
      access_free_brs Γ Bs -> access_free_blocks Γ Bks -> access_free_blocks Γ (eb_mk nm oZ A Bs :: Bks)

  (** The branches of a block *)
  with access_free_brs : ctx -> list (string * nat * exp) -> Prop :=
  (** No branch *)
  | access_free_brs_nil : forall Γ, access_free_brs Γ nil
  (** The first branch, then the rest *)
  | access_free_brs_cons : forall Γ c n B Bs,
      access_free_exp (ctx_holes n ++ Γ) B -> access_free_brs Γ Bs -> access_free_brs Γ ((c, n, B) :: Bs)

  (** A term that may be absent *)
  with access_free_oexp : ctx -> option exp -> Prop :=
  (** Absent *)
  | access_free_oexp_none : forall Γ, access_free_oexp Γ None
  (** Present *)
  | access_free_oexp_some : forall Γ M, access_free_exp Γ M -> access_free_oexp Γ (Some M)

  (** [access_free_mod Γ H]: [H], in module position, reads as a module,
      and no part of it has a term at its head *)
  with access_free_mod : ctx -> modexp -> Prop :=
  (** A unit *)
  | access_free_mod_unit : forall Γ fp, access_free_mod Γ (me_unit fp)
  (** A binder that holds no term *)
  | access_free_mod_var : forall Γ k, (forall A, ~ Γ ∋ #k : A) -> access_free_mod Γ (me_var k)
  (** A member that is no term *)
  | access_free_mod_mem : forall Γ H y,
      access_free_mod Γ H -> (forall A oM, ~ mdenote Θ Ξ Γ (me_mem H y) (ds_term A oM)) ->
      access_free_mod Γ (me_mem H y)
  (** A module applied *)
  | access_free_mod_app : forall Γ H N,
      access_free_mod Γ H -> access_free_exp Γ N -> access_free_mod Γ (me_app H N)
  (** A module literal *)
  | access_free_mod_lit : forall Γ U, access_free_unit Γ U -> access_free_mod Γ (me_lit U)

  (** A unit: its telescope, then its definition under it *)
  with access_free_unit : ctx -> gunit -> Prop :=
  (** The only rule: the telescope with no access, then the definition
      under it *)
  | access_free_unit_mk : forall Γ Δ D,
      access_free_tele Γ Δ -> access_free_def (Δ ++ Γ) D -> access_free_unit Γ (gu_mk Δ D)

  (** A unit's definition *)
  with access_free_def : ctx -> moddef -> Prop :=
  (** An alias *)
  | access_free_def_alias : forall Γ E, access_free_mod Γ E -> access_free_def Γ (md_alias E)
  (** A body *)
  | access_free_def_body : forall Γ sm Φ, access_free_body Γ Φ -> access_free_def Γ (md_body sm Φ)

  (** A telescope, each entry over the ones after it *)
  with access_free_tele : ctx -> ctx -> Prop :=
  (** The empty telescope *)
  | access_free_tele_nil : forall Γ, access_free_tele Γ nil
  (** An assumption *)
  | access_free_tele_ass : forall Γ Δ A,
      access_free_tele Γ Δ -> access_free_exp (Δ ++ Γ) A -> access_free_tele Γ (ce_ass A :: Δ)
  (** A definition *)
  | access_free_tele_def : forall Γ Δ A M,
      access_free_tele Γ Δ -> access_free_exp (Δ ++ Γ) A -> access_free_exp (Δ ++ Γ) M ->
      access_free_tele Γ (ce_def A M :: Δ)
  (** A module slot *)
  | access_free_tele_mod : forall Γ Δ U,
      access_free_tele Γ Δ -> access_free_unit (Δ ++ Γ) U -> access_free_tele Γ (ce_mod U :: Δ)

  (** A local body, entry by entry, each in the context of the expansion
      of the entries before it *)
  with access_free_body : ctx -> gmod -> Prop :=
  (** The empty body *)
  | access_free_body_nil : forall Γ, access_free_body Γ gm_nil
  (** A definition *)
  | access_free_body_def : forall Γ Φ Φx x b pv A oM,
      access_free_body Γ Φ -> body_xp Θ Ξ Γ Φ Φx ->
      access_free_exp (body_ctx Φx ++ Γ) A -> access_free_oexp (body_ctx Φx ++ Γ) oM ->
      access_free_body Γ (gm_ext Φ x (ge_def b pv A oM))
  (** A module *)
  | access_free_body_mod : forall Γ Φ Φx x pv U,
      access_free_body Γ Φ -> body_xp Θ Ξ Γ Φ Φx -> access_free_unit (body_ctx Φx ++ Γ) U ->
      access_free_body Γ (gm_ext Φ x (ge_mod pv U))
  (** A local open *)
  | access_free_body_open : forall Γ Φ Φx H its,
      access_free_body Γ Φ -> body_xp Θ Ξ Γ Φ Φx -> access_free_mod (body_ctx Φx ++ Γ) H ->
      access_free_body Γ (gm_open Φ H its).

  Scheme access_free_exp_mut_ind := Induction for access_free_exp Sort Prop
  with access_free_exps_mut_ind := Induction for access_free_exps Sort Prop
  with access_free_fvals_mut_ind := Induction for access_free_fvals Sort Prop
  with access_free_blocks_mut_ind := Induction for access_free_blocks Sort Prop
  with access_free_brs_mut_ind := Induction for access_free_brs Sort Prop
  with access_free_oexp_mut_ind := Induction for access_free_oexp Sort Prop
  with access_free_mod_mut_ind := Induction for access_free_mod Sort Prop
  with access_free_unit_mut_ind := Induction for access_free_unit Sort Prop
  with access_free_def_mut_ind := Induction for access_free_def Sort Prop
  with access_free_tele_mut_ind := Induction for access_free_tele Sort Prop
  with access_free_body_mut_ind := Induction for access_free_body Sort Prop.
  Combined Scheme access_free_mut_ind from access_free_exp_mut_ind, access_free_exps_mut_ind,
    access_free_fvals_mut_ind, access_free_blocks_mut_ind, access_free_brs_mut_ind, access_free_oexp_mut_ind,
    access_free_mod_mut_ind, access_free_unit_mut_ind, access_free_def_mut_ind, access_free_tele_mut_ind,
    access_free_body_mut_ind.

  (** The fields of a record declaration, each over holes for the fields
      before it. *)
  Definition access_free_fields (Γ : ctx) (fs : list (string * typ)) : Prop :=
    forall j f T, List.nth_error fs j = Some (f, T) -> access_free_exp (ctx_holes j ++ Γ) T.

End AccessFill.

#[export]
Hint Constructors module_read fill_exp elim_group fill_exps fill_fvals fill_blocks fill_brs fill_oexp fill_read
  fill_mod fill_unit fill_def fill_tele fill_body fill_fields access_free_exp access_free_exps access_free_fvals
  access_free_blocks access_free_brs access_free_oexp access_free_mod access_free_unit access_free_def
  access_free_tele access_free_body : mctt.
