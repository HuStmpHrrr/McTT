(** * Privacy

    Privacy is not a matter of typing: a public definition may unfold to a
    term naming a private one, and its type may name one, so typing and δ
    read no privacy flag.  It is a check on the terms a command introduces,
    as written: the first selection from an enclosing self slot is free,
    since that is a reference made inside the module that declares the
    member; every other selection is of a public member.

    What a reference selects from is read off the syntax by module tables
    ([ptab]), in a scope giving the table of each index: binders hold
    [pt_none], a local module the table of its unit, a self slot [pt_self]
    of the table of the body before the entry.  A chain from a unit is
    resolved in the unit the global context files under its path, at the
    part of the global context below it ([gtab]), which follows aliases to
    the module that declares the member. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Command Imports.
From Mctt.Core.Syntactic.System Require Export MemberLemmas.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** Whether an entry is private. *)
Definition ge_private (E : gentry) : bool :=
  match E with
  | ge_def pv _ _ => pv
  | ge_mod pv _ => pv
  end.

(** ** Module Tables *)

(** How a module is named in an error: a module of a unit, by its qualified
    name, or a submodule of a local module, by its chain from it. *)
Inductive bname : Set :=
| bn_glob : qname -> bname
| bn_local : list string -> bname.

Definition bn_sub (nm : bname) (y : string) : bname :=
  match nm with
  | bn_glob p => bn_glob (qname_in p y)
  | bn_local ch => bn_local (ch ++ y :: nil)
  end.

(** No induction principle: tables are only computed and read. *)
Unset Elimination Schemes.
Inductive ptab : Set :=
(** Nothing is known: a term variable, a parameter, a definition *)
| pt_none : ptab
(** The module at a chain of a unit, still to be resolved *)
| pt_glob : path -> list string -> ptab
(** The entries of a body, newest first, each with its privacy and table *)
| pt_body : bname -> list (string * bool * ptab) -> ptab
(** A self slot: selecting from it is free *)
| pt_self : ptab -> ptab.
Set Elimination Schemes.

(** The newest entry [x] of a body's table. *)
Fixpoint tab_find (x : string) (es : list (string * bool * ptab)) : option (bool * ptab) :=
  match es with
  | nil => None
  | (y, pv, t) :: es' => if String.eqb x y then Some (pv, t) else tab_find x es'
  end.

(** The table of the submodule [y]. *)
Fixpoint tab_sel (t : ptab) (y : string) : ptab :=
  match t with
  | pt_none => pt_none
  | pt_glob fp ch => pt_glob fp (ch ++ y :: nil)
  | pt_body _ es =>
      match tab_find y es with
      | Some (_, t') => t'
      | None => pt_none
      end
  | pt_self t => tab_sel t y
  end.

(** The table of a module expression, of a unit, of a body and of an entry,
    in the scope [S].  An entry of a body is read under its self slot. *)
Fixpoint mtab (S : list ptab) (H : modexp) : ptab :=
  match H with
  | me_unit fp => pt_glob fp nil
  | me_var k => nth k S pt_none
  | me_mem H y => tab_sel (mtab S H) y
  | me_app H _ => mtab S H
  | me_lit U => utab (bn_local nil) S U
  end
with utab (nm : bname) (S : list ptab) (U : gunit) : ptab :=
  match U with
  | gu_mk Δ D => dtab nm (repeat pt_none (List.length Δ) ++ S) D
  end
with dtab (nm : bname) (S : list ptab) (D : moddef) : ptab :=
  match D with
  | md_body Φ => pt_body nm (btab nm S Φ)
  | md_alias E => mtab S E
  end
with btab (nm : bname) (S : list ptab) (Φ : gmod) : list (string * bool * ptab) :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ x E =>
      let es := btab nm S Φ in
      (x, ge_private E, etab (bn_sub nm x) (pt_self (pt_body nm es) :: S) E) :: es
  | gm_open Φ H oz its =>
      let es := btab nm S Φ in
      let t := mtab (pt_self (pt_body nm es) :: S) H in
      let es1 := match oz with Some z => (z, true, t) :: es | None => es end in
      rev (map (fun it => let '(n, d, pv) := it in (d, pv, tab_sel t n)) its) ++ es1
  end
with etab (nm : bname) (S : list ptab) (E : gentry) : ptab :=
  match E with
  | ge_def _ _ _ => pt_none
  | ge_mod _ U => utab nm S U
  end.

(** The table a local binding gives its index. *)
Definition bnd_tab (S : list ptab) (b : bnd) : ptab :=
  match b with
  | b_def _ _ => pt_none
  | b_mod U => utab (bn_local nil) S U
  end.

(** The self table of a body, with no further entry. *)
Definition self_tab (nm : bname) (S : list ptab) (Φ : gmod) : ptab := pt_self (pt_body nm (btab nm S Φ)).

(** ** Member References *)

(** The references an open's items make: each member it names. *)
Definition item_refs (t : ptab) (its : list iitem) : list (ptab * string)%type :=
  map (fun it => let '(n, _, _) := it in (t, n)) its.

(** The member references a term is written with, each with the table of
    the module it selects from: every [a_mem H x] and every submodule
    [me_mem H y]. *)
Fixpoint exp_refs (S : list ptab) (M : exp) : list (ptab * string)%type :=
  match M with
  | a_typ _ | a_nat | a_zero | a_True | a_true | a_False | a_var _ | a_const _ => nil
  | a_succ M => exp_refs S M
  | a_natrec A MZ MS M =>
      exp_refs (pt_none :: S) A ++ exp_refs S MZ ++ exp_refs (pt_none :: pt_none :: S) MS ++ exp_refs S M
  | a_exfalso A M => exp_refs (pt_none :: S) A ++ exp_refs S M
  | a_pi A M | a_fn A M => exp_refs S A ++ exp_refs (pt_none :: S) M
  | a_app M N => exp_refs S M ++ exp_refs S N
  | a_let b B => bnd_refs S b ++ exp_refs (bnd_tab S b :: S) B
  | a_mem H x => (mtab S H, x) :: modexp_refs S H
  end
with modexp_refs (S : list ptab) (H : modexp) : list (ptab * string)%type :=
  match H with
  | me_unit _ | me_var _ => nil
  | me_mem H y => (mtab S H, y) :: modexp_refs S H
  | me_app H N => modexp_refs S H ++ exp_refs S N
  | me_lit U => gunit_refs (bn_local nil) S U
  end
with bnd_refs (S : list ptab) (b : bnd) : list (ptab * string)%type :=
  match b with
  | b_def oA M => match oA with Some A => exp_refs S A | None => nil end ++ exp_refs S M
  | b_mod U => gunit_refs (bn_local nil) S U
  end
with gunit_refs (nm : bname) (S : list ptab) (U : gunit) : list (ptab * string)%type :=
  match U with
  | gu_mk Δ D =>
      (fix tele_refs (Δ : list centry) : list (ptab * string)%type :=
         match Δ with
         | nil => nil
         | e :: Δ' => centry_refs (repeat pt_none (List.length Δ') ++ S) e ++ tele_refs Δ'
         end) Δ ++ moddef_refs nm (repeat pt_none (List.length Δ) ++ S) D
  end
with moddef_refs (nm : bname) (S : list ptab) (D : moddef) : list (ptab * string)%type :=
  match D with
  | md_body Φ => gmod_refs nm S Φ
  | md_alias E => modexp_refs S E
  end
with gmod_refs (nm : bname) (S : list ptab) (Φ : gmod) : list (ptab * string)%type :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ x E => gmod_refs nm S Φ ++ gentry_refs (bn_sub nm x) (self_tab nm S Φ :: S) E
  | gm_open Φ H _ its =>
      gmod_refs nm S Φ ++ modexp_refs (self_tab nm S Φ :: S) H ++
        item_refs (mtab (self_tab nm S Φ :: S) H) its
  end
with gentry_refs (nm : bname) (S : list ptab) (E : gentry) : list (ptab * string)%type :=
  match E with
  | ge_def _ A oM => exp_refs S A ++ match oM with Some M => exp_refs S M | None => nil end
  | ge_mod _ U => gunit_refs nm S U
  end
with centry_refs (S : list ptab) (e : centry) : list (ptab * string)%type :=
  match e with
  | ce_ass A => exp_refs S A
  | ce_def A M => exp_refs S A ++ exp_refs S M
  | ce_mod U => gunit_refs (bn_local nil) S U
  end.

Fixpoint tele_refs (S : list ptab) (Δ : ctx) : list (ptab * string)%type :=
  match Δ with
  | nil => nil
  | e :: Δ' => centry_refs (repeat pt_none (List.length Δ') ++ S) e ++ tele_refs S Δ'
  end.

(** The references a command makes, as written, in the scope [S] of its
    context: its own terms, and for an open, its target and each member its
    items name.  A module's nested commands are checked when they run. *)
Definition cmd_refs (S : list ptab) (c : ccmd) : list (ptab * string)%type :=
  match c with
  | cc_def _ _ _ A oM => exp_refs S A ++ match oM with Some M => exp_refs S M | None => nil end
  | cc_mod _ _ Δ _ => tele_refs S Δ
  | cc_alias _ _ Δ E => tele_refs S Δ ++ modexp_refs (repeat pt_none (List.length Δ) ++ S) E
  | cc_load _ => nil
  | cc_open E _ its => modexp_refs S E ++ item_refs (mtab S E) its
  | cc_eval M oA => exp_refs S M ++ match oA with Some A => exp_refs S A | None => nil end
  end.

(** ** The Scope of a Command

    A frame's self slot holds its body so far, named by the frame's chain in
    the unit [fp]; its parameters know nothing; a leading open's alias is the
    table of its target. *)
Fixpoint ctx_tabs (Γ : ctx) : list ptab :=
  match Γ with
  | nil => nil
  | ce_mod U :: Γ' => utab (bn_local nil) (ctx_tabs Γ') U :: ctx_tabs Γ'
  | _ :: Γ' => pt_none :: ctx_tabs Γ'
  end.

Fixpoint fctx_tabs (fp : path) (Γimp : ctx) (F : list frame) : list ptab :=
  match F with
  | nil => ctx_tabs Γimp
  | f :: F' =>
      let S := repeat pt_none (List.length (fr_params f)) ++ fctx_tabs fp Γimp F' in
      self_tab (bn_glob (q_abs fp (fr_chain f))) S (fr_body f) :: S
  end.

(** ** Resolution of a Chain of a Unit

    [gtab Θ fp ch]: the table of the module at the chain [ch] of the unit
    [fp], read in the unit filed under [fp] and, past an alias, in the part
    of [Θ] below it. *)
Definition tab_norm (k : path -> list string -> option ptab) (t : ptab) : option ptab :=
  match t with
  | pt_glob fp ch => k fp ch
  | _ => Some t
  end.

Fixpoint tab_walk (k : path -> list string -> option ptab) (t : ptab) (ch : list string) : option ptab :=
  match ch with
  | nil => tab_norm k t
  | y :: ch' =>
      match tab_norm k t with
      | Some t' => tab_walk k (tab_sel t' y) ch'
      | None => None
      end
  end.

Fixpoint gtab (Θ : gctx) (fp : path) (ch : list string) : option ptab :=
  match Θ with
  | nil => None
  | gd_const _ _ _ _ :: Θ' => gtab Θ' fp ch
  | gd_unit fq U :: Θ' =>
      if path_beq fp fq
      then tab_walk (gtab Θ') (utab (bn_glob (q_abs fp nil)) nil U) ch
      else gtab Θ' fp ch
  end.

(** ** Accessibility *)

(** A reference to [x] in the table [t]: free from a self slot, else to a
    public entry.  A reference into a module that does not resolve is left to
    typing, which rejects it. *)
Definition tab_ok (t : ptab) (x : string) : Prop :=
  match t with
  | pt_body _ es => option_map fst (tab_find x es) <> Some true
  | _ => True
  end.

Definition ref_ok (Θ : gctx) (r : (ptab * string)%type) : Prop :=
  match fst r with
  | pt_glob fp ch =>
      match gtab Θ fp ch with
      | Some t => tab_ok t (snd r)
      | None => True
      end
  | t => tab_ok t (snd r)
  end.

Definition acc_ok (Θ : gctx) (l : list (ptab * string)%type) : Prop :=
  List.Forall (ref_ok Θ) l.
