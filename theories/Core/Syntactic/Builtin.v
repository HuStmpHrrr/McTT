(** * Builtin Bindings

    [builtin natural ≔ X] binds the inductive type [X] as the natural
    numbers.  The bindings are a record, [builtins], apart from the filed
    units and the stack: no typing judgment reads it.  Each unit runs from
    the empty record; it gains the bindings of its own [builtin] commands
    and the records of the units it imports, merged ([bt_merge]), but never
    those of the unit importing it.  The command semantics threads the
    record of the unit being run, and keeps the record each filed unit ended
    with ([Core.Syntactic.System.Command]).

    Where a binding is made, a numeral ([a_nlit]) stands for the chain of
    the bound type's constructors and the token [ℕ] ([a_ntok]) for its type
    former: when a command runs, its literals are generated from the
    binding ([cmd_lits]).  Without a binding a literal is an error.  A
    literal has no typing, evaluation or readback rule. *)

From Stdlib Require Import List String Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Export Inductives.
From Mctt.Core.Syntactic Require Export Members Command.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** The kind of the binding, as the command names it. *)
Definition nat_kind : string := "natural".

(** The shape of the natural numbers: a group of one declared member and
    no view, no parameter, and two constructors, one without arguments,
    [z], and one with a single recursive argument, [s], in either order. *)
Definition nat_cons_shape (cs : list (string * list carg)) : option (string * string) :=
  match cs with
  | (c1, nil) :: (c2, ca_rec (pt_self 0 nil) :: nil) :: nil => Some (c1, c2)
  | (c2, ca_rec (pt_self 0 nil) :: nil) :: (c1, nil) :: nil => Some (c1, c2)
  | _ => None
  end.

(** The names of the zero and successor constructors of a group of the
    shape of the natural numbers, if [D] is one. *)
Definition nat_shape (D : ind_decl) : option (string * string) :=
  match ind_uparams D, ind_members D with
  | nil, mk_imember (mh_decl _) nil cs :: nil => nat_cons_shape cs
  | _, _ => None
  end.

(** The sort the natural numbers are declared in: [Type@0]. *)
Definition nat_sort : typ := a_univ (a_llit (0, 0)).

(** ** The Configuration *)

(** The builtin bindings of a run: the path of the type bound as the
    natural numbers, if one is. *)
Record builtins : Set := mk_builtins { bt_nat : option qname }.

Definition bt_empty : builtins := mk_builtins None.

(** A binding is well formed where its type is an inductive type of the
    shape of the natural numbers, in [Type@0], filed or on the stack.  This
    is a condition on its own, not part of typing. *)
#[warnings="-cannot-define-projection"]
Record nat_binding_ok (Θ : gdeps) (Ξ : gstack) (p : qname) : Prop := mk_nat_binding_ok
  { nbo_decl : ind_decl
  ; nbo_zero : string
  ; nbo_succ : string
  ; nbo_lookup : ind_lookup Θ Ξ p = Some nbo_decl
  ; nbo_shape : nat_shape nbo_decl = Some (nbo_zero, nbo_succ)
  ; nbo_sort : ind_sort nbo_decl = nat_sort }.

Definition builtins_wf (Θ : gdeps) (Ξ : gstack) (B : builtins) : Prop :=
  forall p, bt_nat B = Some p -> nat_binding_ok Θ Ξ p.

(** What a literal stands for at a state: the bound type and its
    constructors, the one without arguments first. *)
Definition nat_view (Θ : gdeps) (Ξ : gstack) (B : builtins) : option (qname * string * string) :=
  match bt_nat B with
  | Some p =>
      match ind_lookup Θ Ξ p with
      | Some D =>
          match nat_shape D with
          | Some (z, s) => Some (p, z, s)
          | None => None
          end
      | None => None
      end
  | None => None
  end.

(** The numeral [n] as the chain of the constructors [z] and [s] of [p]. *)
Fixpoint nat_chain (p : qname) (z s : string) (n : nat) : exp :=
  match n with
  | 0 => a_con p 0 z
  | S n' => a_app (a_con p 0 s) (nat_chain p z s n')
  end.

(** ** Literals *)

(** Why the literals of a command cannot be generated: a numeral, or the
    token [ℕ], with no natural-number type bound. *)
Inductive lerr : Set :=
| le_num : nat -> lerr
| le_tok : lerr.

Inductive lres (A : Type) : Type :=
| lok : A -> lres A
| lfail : lerr -> lres A.

Arguments lok {A}.
Arguments lfail {A}.

Definition lbind {A B} (m : lres A) (f : A -> lres B) : lres B :=
  match m with
  | lok a => f a
  | lfail e => lfail e
  end.

#[local] Notation "'let%' x ':=' m 'in' f" := (lbind m (fun x => f))
  (at level 200, x name, m at level 100, f at level 200, right associativity).

Definition lopt {A} (f : A -> lres A) (o : option A) : lres (option A) :=
  match o with
  | Some a => let% a' := f a in lok (Some a')
  | None => lok None
  end.

Fixpoint lmap {A B} (f : A -> lres B) (l : list A) : lres (list B) :=
  match l with
  | nil => lok nil
  | a :: l' => let% b := f a in let% bs := lmap f l' in lok (b :: bs)
  end.

Section Literals.
  (** The bound type and its constructors, if any. *)
  Variable nv : option (qname * string * string).

  (** A term with the natural-number type token and its numeric literals
      replaced by the bound type and its constructors, or an error if one
      appears and nothing is bound; mutually, for its other sorts. *)
  Fixpoint exp_lits (M : exp) {struct M} : lres exp :=
    match M with
    | a_typ _ | a_level _ | a_llit _ | a_True | a_true | a_False | a_var _ | a_ind _ _ | a_con _ _ _ => lok M
    | a_ntok =>
        match nv with
        | Some (p, _, _) => lok (a_ind p 0)
        | None => lfail le_tok
        end
    | a_nlit n =>
        match nv with
        | Some (p, z, s) => lok (nat_chain p z s n)
        | None => lfail (le_num n)
        end
    | a_univ M => let% M' := exp_lits M in lok (a_univ M')
    | a_succl M => let% M' := exp_lits M in lok (a_succl M')
    | a_maxl M N => let% M' := exp_lits M in let% N' := exp_lits N in lok (a_maxl M' N')
    | a_exfalso A M => let% A' := exp_lits A in let% M' := exp_lits M in lok (a_exfalso A' M')
    | a_elim oq Us m Bks M =>
        let% Us' := (fix ups_lits (Us : list exp) : lres (list exp) :=
                       match Us with
                       | nil => lok nil
                       | U :: Us0 => let% U' := exp_lits U in let% Us0' := ups_lits Us0 in lok (U' :: Us0')
                       end) Us in
        let% Bks' := (fix blocks_lits (Bks : list eblock) : lres (list eblock) :=
                        match Bks with
                        | nil => lok nil
                        | eb_mk nm oZ A Bs :: Bks0 =>
                            let% oZ' := (match oZ with
                                         | Some Z => let% Z' := exp_lits Z in lok (Some Z')
                                         | None => lok None
                                         end) in
                            let% A' := exp_lits A in
                            let% Bs' := (fix brs_lits (Bs : list (String.string * nat * exp)) : lres (list (String.string * nat * exp)) :=
                                           match Bs with
                                           | nil => lok nil
                                           | b :: Bs0 =>
                                               let% B' := exp_lits (snd b) in
                                               let% Bs0' := brs_lits Bs0 in
                                               lok ((fst b, B') :: Bs0')
                                           end) Bs in
                            let% Bks0' := blocks_lits Bks0 in
                            lok (eb_mk nm oZ' A' Bs' :: Bks0')
                        end) Bks in
        let% M' := exp_lits M in
        lok (a_elim oq Us' m Bks' M')
    | a_pi A B => let% A' := exp_lits A in let% B' := exp_lits B in lok (a_pi A' B')
    | a_fn A M => let% A' := exp_lits A in let% M' := exp_lits M in lok (a_fn A' M')
    | a_app M N => let% M' := exp_lits M in let% N' := exp_lits N in lok (a_app M' N')
    | a_let b B => let% b' := bnd_lits b in let% B' := exp_lits B in lok (a_let b' B')
    | a_mem H x => let% H' := modexp_lits H in lok (a_mem H' x)
    end
  with modexp_lits (H : modexp) {struct H} : lres modexp :=
    match H with
    | me_unit _ | me_var _ => lok H
    | me_mem H y => let% H' := modexp_lits H in lok (me_mem H' y)
    | me_app H N => let% H' := modexp_lits H in let% N' := exp_lits N in lok (me_app H' N')
    | me_lit U => let% U' := gunit_lits U in lok (me_lit U')
    end
  with bnd_lits (b : bnd) {struct b} : lres bnd :=
    match b with
    | b_def oA M => let% oA' := lopt exp_lits oA in let% M' := exp_lits M in lok (b_def oA' M')
    | b_mod U => let% U' := gunit_lits U in lok (b_mod U')
    end
  with gunit_lits (U : gunit) {struct U} : lres gunit :=
    match U with
    | gu_mk Δ D =>
        let% Δ' := (fix tele_lits (Δ : list centry) : lres ctx :=
                      match Δ with
                      | nil => lok nil
                      | e :: Δ0 => let% e' := centry_lits e in let% Δ0' := tele_lits Δ0 in lok (e' :: Δ0')
                      end) Δ in
        let% D' := moddef_lits D in
        lok (gu_mk Δ' D')
    end
  with moddef_lits (D : moddef) {struct D} : lres moddef :=
    match D with
    | md_body sm Φ => let% Φ' := gmod_lits Φ in lok (md_body sm Φ')
    | md_alias E => let% E' := modexp_lits E in lok (md_alias E')
    end
  with gmod_lits (Φ : gmod) {struct Φ} : lres gmod :=
    match Φ with
    | gm_nil => lok gm_nil
    | gm_ext Φ x E => let% Φ' := gmod_lits Φ in let% E' := gentry_lits E in lok (gm_ext Φ' x E')
    | gm_open Φ H its => let% Φ' := gmod_lits Φ in let% H' := modexp_lits H in lok (gm_open Φ' H' its)
    end
  with gentry_lits (E : gentry) {struct E} : lres gentry :=
    match E with
    | ge_def b pv A B => let% A' := exp_lits A in let% B' := lopt exp_lits B in lok (ge_def b pv A' B')
    | ge_mod pv U => let% U' := gunit_lits U in lok (ge_mod pv U')
    | ge_ind _ _ _ _ _ | ge_ind_alias _ _ _ _ _ _ => lok E
    end
  with centry_lits (e : centry) {struct e} : lres centry :=
    match e with
    | ce_ass A => let% A' := exp_lits A in lok (ce_ass A')
    | ce_def A M => let% A' := exp_lits A in let% M' := exp_lits M in lok (ce_def A' M')
    | ce_mod U => let% U' := gunit_lits U in lok (ce_mod U')
    end.

  Definition tele_lits (Δ : ctx) : lres ctx := lmap centry_lits Δ.

  (** A group's declaration as written. *)
  Definition member_lits (Rm : raw_member) : lres raw_member :=
    let% Δ' := tele_lits (rm_nparams Rm) in
    let% A' := exp_lits (rm_sort Rm) in
    let% cs' := lmap (fun cg => let% args := lmap (fun yT => let% T' := exp_lits (snd yT) in lok (fst yT, T')) (snd cg) in
                                lok (fst cg, args)) (rm_cons Rm) in
    lok (mk_rmem (rm_name Rm) Δ' A' cs').

  (** A group declaration as written, its literals replaced throughout. *)
  Definition decl_lits (R : raw_decl) : lres raw_decl :=
    let% Δ' := tele_lits (rd_uparams R) in
    let% ms' := lmap member_lits (rd_members R) in
    lok (mk_raw Δ' ms' (rd_rec R)).

  (** A function of a [mutual def] as written. *)
  Definition fun_lits (F : raw_fun) : lres raw_fun :=
    let% ys' := tele_lits (rf_nparams F) in
    let% Z' := exp_lits (rf_scrut F) in
    let% A' := exp_lits (rf_res F) in
    let% cl' := lmap (fun b => let% B' := exp_lits (snd b) in lok (fst b, B')) (rf_clauses F) in
    lok (mk_rfun (rf_name F) ys' Z' A' cl').

  (** A command's own terms: the nested commands of a module get their
      literals when they run. *)
  Definition cmd_lits (c : ccmd) : lres ccmd :=
    match c with
    | cc_def x b pv A M => let% A' := exp_lits A in let% M' := lopt exp_lits M in lok (cc_def x b pv A' M')
    | cc_mod x pv Δ cs => let% Δ' := tele_lits Δ in lok (cc_mod x pv Δ' cs)
    | cc_alias x pv Δ E => let% Δ' := tele_lits Δ in let% E' := modexp_lits E in lok (cc_alias x pv Δ' E')
    | cc_load fp => lok (cc_load fp)
    | cc_open E its => let% E' := modexp_lits E in lok (cc_open E' its)
    | cc_eval M oA => let% M' := exp_lits M in let% oA' := lopt exp_lits oA in lok (cc_eval M' oA')
    | cc_ind pv D => let% D' := decl_lits D in lok (cc_ind pv D')
    | cc_mdef b pv Δ fs => let% Δ' := tele_lits Δ in let% fs' := lmap fun_lits fs in lok (cc_mdef b pv Δ' fs')
    | cc_builtin k H => let% H' := modexp_lits H in lok (cc_builtin k H')
    | cc_ind_alias x pv Δ H => let% Δ' := tele_lits Δ in let% H' := modexp_lits H in lok (cc_ind_alias x pv Δ' H')
    end.
End Literals.

(** The literals of a command at a state. *)
Definition cmd_lits_ok (Θ : gdeps) (Ξ : gstack) (B : builtins) (c c' : ccmd) : Prop :=
  cmd_lits (nat_view Θ Ξ B) c = lok c'.

Definition tele_lits_ok (Θ : gdeps) (Ξ : gstack) (B : builtins) (Δ Δ' : ctx) : Prop :=
  tele_lits (nat_view Θ Ξ B) Δ = lok Δ'.

(** ** The Uniform Parameters of an Eliminator

    An eliminator as written carries no group and no uniform parameters
    ([a_elim None nil m Bks M]).  When a command runs, after its literals,
    each such eliminator with an annotated binder gets them from the
    annotation: block [0]'s, else block [m]'s ([elim_ann]).  The
    annotation's head is resolved by what it denotes ([mdenote]), as any
    member is: a member of a group of inductive types [ds_ind Θ' p k Ns],
    or the type former [a_ind p k] itself.  The uniform parameters are the
    first [ind_nu] of the arguments the head carries and the annotation
    applies, strengthened past the block's binders ([site_resolves]).

    The sites are found by a function ([exp_sites]), the filled term is
    computed from their results in order ([exp_fill]), and only the results
    come from a relation: the fill is functional as [mdenote] is.  An
    eliminator with no annotated binder keeps no uniform parameters; its
    typing then asks for none.

    Every term of the command is visited, those inside module expressions
    and module literals included: the arguments of an application, and the
    telescope and the entries of a literal, each entry in its body's
    context as written ([body_ctx]).  There a local open binds one hole per
    item: the elaborator reaches what an open generates through the opened
    module, not through these slots. *)

(** The annotation an eliminator's group and uniform parameters are read
    off, block [0]'s, else block [m]'s, with the number of binders it is
    under. *)
Definition elim_ann (m : nat) (Bks : list eblock) : option (nat * exp) :=
  match Bks with
  | eb_mk nm (Some Z) _ _ :: _ => Some (nm - 1, Z)
  | _ =>
      match List.nth_error Bks m with
      | Some (eb_mk nm (Some Z) _ _) => Some (nm - 1, Z)
      | _ => None
      end
  end.

(** Whether an eliminator is to be filled: as written, with an annotation. *)
Definition elim_site (oq : option qname) (Us : list exp) (m : nat) (Bks : list eblock) : option (nat * exp) :=
  match oq, Us with
  | None, nil => elim_ann m Bks
  | _, _ => None
  end.

(** A term binder in the context a site is resolved in.  The fill reads a
    context only through [mdenote], which needs its module entries and the
    depth of its binders: a term binder is a hole, whatever its type. *)
Definition ce_hole : centry := ce_ass a_True.

(** [n] term binders, as holes. *)
Definition ctx_holes (n : nat) : ctx := List.repeat ce_hole n.

(** A site: the context of the eliminator, the binders its annotation is
    under, and the annotation. *)
Definition fill_site : Set := (ctx * nat * exp)%type.

(** The sites of a term in the context [Γ], in order: an eliminator's own
    site, then those of its parts. *)
Fixpoint exp_sites (Γ : ctx) (M : exp) {struct M} : list fill_site :=
  match M with
  | a_univ M1 | a_succl M1 => exp_sites Γ M1
  | a_maxl M1 M2 | a_app M1 M2 => exp_sites Γ M1 ++ exp_sites Γ M2
  | a_exfalso A M1 => exp_sites (ce_hole :: Γ) A ++ exp_sites Γ M1
  | a_pi A B | a_fn A B => exp_sites Γ A ++ exp_sites (ce_hole :: Γ) B
  | a_let (b_def oA M1) B =>
      match oA with Some A => exp_sites Γ A | None => nil end ++ exp_sites Γ M1 ++ exp_sites (ce_hole :: Γ) B
  | a_let (b_mod U) B => unit_sites Γ U ++ exp_sites (ce_mod U :: Γ) B
  | a_elim oq Us m Bks M1 =>
      match elim_site oq Us m Bks with Some (d, Z) => (Γ, d, Z) :: nil | None => nil end ++
      (fix us_sites (Us : list exp) : list fill_site :=
         match Us with nil => nil | U :: Us' => exp_sites Γ U ++ us_sites Us' end) Us ++
      (fix blocks_sites (Bks : list eblock) : list fill_site :=
         match Bks with
         | nil => nil
         | eb_mk nm oZ A Bs :: Bks' =>
             match oZ with Some Z => exp_sites (ctx_holes (nm - 1) ++ Γ) Z | None => nil end ++
             exp_sites (ctx_holes nm ++ Γ) A ++
             (fix brs_sites (Bs : list (string * nat * exp)) : list fill_site :=
                match Bs with nil => nil | b :: Bs' => exp_sites (ctx_holes (snd (fst b)) ++ Γ) (snd b) ++ brs_sites Bs' end) Bs ++
             blocks_sites Bks'
         end) Bks ++
      exp_sites Γ M1
  | a_mem H _ => modexp_sites Γ H
  | _ => nil
  end
(** The sites of a module expression: the arguments it is applied to, and
    the literals in it. *)
with modexp_sites (Γ : ctx) (H : modexp) {struct H} : list fill_site :=
  match H with
  | me_mem H' _ => modexp_sites Γ H'
  | me_app H' N => modexp_sites Γ H' ++ exp_sites Γ N
  | me_lit U => unit_sites Γ U
  | me_unit _ | me_var _ => nil
  end
(** The sites of a unit: its telescope, each entry over those after it,
    then its definition under the telescope. *)
with unit_sites (Γ : ctx) (U : gunit) {struct U} : list fill_site :=
  match U with
  | gu_mk Δ D =>
      (fix tele_sites (Δ : list centry) : list fill_site :=
         match Δ with
         | nil => nil
         | e :: Δ' =>
             match e with
             | ce_ass A => exp_sites (Δ' ++ Γ) A
             | ce_def A M => exp_sites (Δ' ++ Γ) A ++ exp_sites (Δ' ++ Γ) M
             | ce_mod U' => unit_sites (Δ' ++ Γ) U'
             end ++ tele_sites Δ'
         end) Δ ++
      match D with
      | md_body _ Φ => body_sites (Δ ++ Γ) Φ
      | md_alias E => modexp_sites (Δ ++ Γ) E
      end
  end
(** The sites of a body, its entries in order, each in the context of the
    entries before it ([body_ctx]): a definition's type and body, a
    submodule's unit, an open's target.  A local body declares no inductive
    type, and an inductive alias carries no term as written. *)
with body_sites (Γ : ctx) (Φ : gmod) {struct Φ} : list fill_site :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ' _ E =>
      body_sites Γ Φ' ++
      match E with
      | ge_def _ _ A oM =>
          exp_sites (body_ctx Φ' ++ Γ) A ++ match oM with Some M => exp_sites (body_ctx Φ' ++ Γ) M | None => nil end
      | ge_mod _ U => unit_sites (body_ctx Φ' ++ Γ) U
      | ge_ind _ _ _ _ _ | ge_ind_alias _ _ _ _ _ _ => nil
      end
  | gm_open Φ' H _ => body_sites Γ Φ' ++ modexp_sites (body_ctx Φ' ++ Γ) H
  end.

(** The result of a site: the group, and the uniform parameters. *)
Definition fill_result : Set := (qname * list exp)%type.

(** A term filled from the results [rs] of its sites, in the order
    [exp_sites] lists them, and the results left over. *)
Fixpoint exp_fill (rs : list fill_result) (M : exp) {struct M} : (exp * list fill_result)%type :=
  match M with
  | a_univ M1 => let r := exp_fill rs M1 in (a_univ (fst r), snd r)
  | a_succl M1 => let r := exp_fill rs M1 in (a_succl (fst r), snd r)
  | a_maxl M1 M2 => let r1 := exp_fill rs M1 in let r2 := exp_fill (snd r1) M2 in (a_maxl (fst r1) (fst r2), snd r2)
  | a_app M1 M2 => let r1 := exp_fill rs M1 in let r2 := exp_fill (snd r1) M2 in (a_app (fst r1) (fst r2), snd r2)
  | a_exfalso A M1 => let r1 := exp_fill rs A in let r2 := exp_fill (snd r1) M1 in (a_exfalso (fst r1) (fst r2), snd r2)
  | a_pi A B => let r1 := exp_fill rs A in let r2 := exp_fill (snd r1) B in (a_pi (fst r1) (fst r2), snd r2)
  | a_fn A B => let r1 := exp_fill rs A in let r2 := exp_fill (snd r1) B in (a_fn (fst r1) (fst r2), snd r2)
  | a_let (b_def oA M1) B =>
      let rA := match oA with Some A => let r := exp_fill rs A in (Some (fst r), snd r) | None => (None, rs) end in
      let r1 := exp_fill (snd rA) M1 in
      let r2 := exp_fill (snd r1) B in
      (a_let (b_def (fst rA) (fst r1)) (fst r2), snd r2)
  | a_let (b_mod U) B =>
      let rU := unit_fill rs U in let r := exp_fill (snd rU) B in (a_let (b_mod (fst rU)) (fst r), snd r)
  | a_elim oq Us m Bks M1 =>
      let '(oq', Us', rs0) :=
        match elim_site oq Us m Bks, rs with
        | Some _, (p, Us1) :: rs' => (Some p, Us1, rs')
        | _, _ =>
            (oq, Us, rs)
        end in
      let rU := (fix us_fill (rs : list fill_result) (Us : list exp) : (list exp * list fill_result)%type :=
                   match Us with
                   | nil => (nil, rs)
                   | U :: Us0 => let r := exp_fill rs U in let r0 := us_fill (snd r) Us0 in (fst r :: fst r0, snd r0)
                   end) rs0 Us in
      let rB := (fix blocks_fill (rs : list fill_result) (Bks : list eblock) : (list eblock * list fill_result)%type :=
                   match Bks with
                   | nil => (nil, rs)
                   | eb_mk nm oZ A Bs :: Bks0 =>
                       let rZ := match oZ with Some Z => let r := exp_fill rs Z in (Some (fst r), snd r) | None => (None, rs) end in
                       let rA := exp_fill (snd rZ) A in
                       let rBs := (fix brs_fill (rs : list fill_result) (Bs : list (string * nat * exp)) :
                                     (list (string * nat * exp) * list fill_result)%type :=
                                     match Bs with
                                     | nil => (nil, rs)
                                     | b :: Bs0 => let r := exp_fill rs (snd b) in let r0 := brs_fill (snd r) Bs0 in
                                                   ((fst b, fst r) :: fst r0, snd r0)
                                     end) (snd rA) Bs in
                       let r0 := blocks_fill (snd rBs) Bks0 in
                       (eb_mk nm (fst rZ) (fst rA) (fst rBs) :: fst r0, snd r0)
                   end) (snd rU) Bks in
      let rM := exp_fill (snd rB) M1 in
      (a_elim oq' (match elim_site oq Us m Bks with Some _ => Us' | None => fst rU end) m (fst rB) (fst rM), snd rM)
  | a_mem H x => let r := modexp_fill rs H in (a_mem (fst r) x, snd r)
  | _ => (M, rs)
  end
(** A module expression filled, in the order [modexp_sites] lists its
    sites. *)
with modexp_fill (rs : list fill_result) (H : modexp) {struct H} : (modexp * list fill_result)%type :=
  match H with
  | me_mem H' y => let r := modexp_fill rs H' in (me_mem (fst r) y, snd r)
  | me_app H' N => let r1 := modexp_fill rs H' in let r2 := exp_fill (snd r1) N in (me_app (fst r1) (fst r2), snd r2)
  | me_lit U => let r := unit_fill rs U in (me_lit (fst r), snd r)
  | me_unit _ | me_var _ => (H, rs)
  end
(** A unit filled, in the order [unit_sites] lists its sites. *)
with unit_fill (rs : list fill_result) (U : gunit) {struct U} : (gunit * list fill_result)%type :=
  match U with
  | gu_mk Δ D =>
      let rΔ := (fix tele_fill (rs : list fill_result) (Δ : list centry) : (list centry * list fill_result)%type :=
                   match Δ with
                   | nil => (nil, rs)
                   | e :: Δ' =>
                       let re := match e with
                                 | ce_ass A => let r := exp_fill rs A in (ce_ass (fst r), snd r)
                                 | ce_def A M => let r1 := exp_fill rs A in let r2 := exp_fill (snd r1) M in
                                                 (ce_def (fst r1) (fst r2), snd r2)
                                 | ce_mod U' => let r := unit_fill rs U' in (ce_mod (fst r), snd r)
                                 end in
                       let r := tele_fill (snd re) Δ' in
                       (fst re :: fst r, snd r)
                   end) rs Δ in
      let rD := match D with
                | md_body sm Φ => let r := body_fill (snd rΔ) Φ in (md_body sm (fst r), snd r)
                | md_alias E => let r := modexp_fill (snd rΔ) E in (md_alias (fst r), snd r)
                end in
      (gu_mk (fst rΔ) (fst rD), snd rD)
  end
(** A body filled, in the order [body_sites] lists its sites. *)
with body_fill (rs : list fill_result) (Φ : gmod) {struct Φ} : (gmod * list fill_result)%type :=
  match Φ with
  | gm_nil => (gm_nil, rs)
  | gm_ext Φ' x E =>
      let r := body_fill rs Φ' in
      let rE := match E with
                | ge_def b pv A oM =>
                    let rA := exp_fill (snd r) A in
                    match oM with
                    | Some M => let rM := exp_fill (snd rA) M in (ge_def b pv (fst rA) (Some (fst rM)), snd rM)
                    | None => (ge_def b pv (fst rA) None, snd rA)
                    end
                | ge_mod pv U => let rU := unit_fill (snd r) U in (ge_mod pv (fst rU), snd rU)
                | ge_ind _ _ _ _ _ | ge_ind_alias _ _ _ _ _ _ => (E, snd r)
                end in
      (gm_ext (fst r) x (fst rE), snd rE)
  | gm_open Φ' H its =>
      let r := body_fill rs Φ' in let rH := modexp_fill (snd r) H in (gm_open (fst r) (fst rH) its, snd rH)
  end.

(** The sites of a telescope, each entry in the context of those after it
    over [Γ], innermost entry first. *)
Fixpoint tele_sites (Γ : ctx) (Δ : ctx) : list fill_site :=
  match Δ with
  | nil => nil
  | e :: Δ' =>
      match e with
      | ce_ass A => exp_sites (Δ' ++ Γ) A
      | ce_def A M => exp_sites (Δ' ++ Γ) A ++ exp_sites (Δ' ++ Γ) M
      | ce_mod U => unit_sites (Δ' ++ Γ) U
      end ++ tele_sites Γ Δ'
  end.

(** A telescope filled, in the order [tele_sites] lists its sites. *)
Fixpoint tele_fill (rs : list fill_result) (Δ : ctx) : (ctx * list fill_result)%type :=
  match Δ with
  | nil => (nil, rs)
  | e :: Δ' =>
      let re := match e with
                | ce_ass A => let r := exp_fill rs A in (ce_ass (fst r), snd r)
                | ce_def A M => let r1 := exp_fill rs A in let r2 := exp_fill (snd r1) M in (ce_def (fst r1) (fst r2), snd r2)
                | ce_mod U => let r := unit_fill rs U in (ce_mod (fst r), snd r)
                end in
      let r := tele_fill (snd re) Δ' in
      (fst re :: fst r, snd r)
  end.

(** A list of terms, each in its own context ([Γs]), and its fill. *)
Fixpoint list_sites (Γs : list ctx) (Ms : list exp) : list fill_site :=
  match Γs, Ms with
  | Γ :: Γs', M :: Ms' => exp_sites Γ M ++ list_sites Γs' Ms'
  | _, _ => nil
  end.

(** A list of terms filled, in order, threading the results. *)
Fixpoint list_fill (rs : list fill_result) (Ms : list exp) : (list exp * list fill_result)%type :=
  match Ms with
  | nil => (nil, rs)
  | M :: Ms' => let r := exp_fill rs M in let r' := list_fill (snd r) Ms' in (fst r :: fst r', snd r')
  end.

(** The sites of a declared member as written: its non-uniform
    parameters, over the uniform ones and the frames'; its sort, over
    them; each constructor argument, over those before it, the member's
    parameters and the [Self]s, then the frames' (as term binders: a
    declaration's telescopes have no module slot). *)
Definition member_sites (Ξ : gstack) (R : raw_decl) (Mr : raw_member) : list fill_site :=
  tele_sites (rd_uparams R ++ gs_tele Ξ) (rm_nparams Mr) ++
  exp_sites (rm_nparams Mr ++ rd_uparams R ++ gs_tele Ξ) (rm_sort Mr) ++
  List.concat (List.map (fun cg =>
    list_sites (List.map (fun j => ctx_holes (j + List.length (rm_nparams Mr) + List.length (rd_uparams R)
                                              + List.length (rd_members R)) ++ gs_tele Ξ) (List.seq 0 (List.length (snd cg))))
      (List.map snd (snd cg))) (rm_cons Mr)).

(** A declared member filled. *)
Definition member_fill (rs : list fill_result) (Mr : raw_member) : (raw_member * list fill_result)%type :=
  let rN := tele_fill rs (rm_nparams Mr) in
  let rS := exp_fill (snd rN) (rm_sort Mr) in
  let rC := (fix cons_fill (rs : list fill_result) (cs : list (string * list (string * exp))) :
               (list (string * list (string * exp)) * list fill_result)%type :=
               match cs with
               | nil => (nil, rs)
               | cg :: cs' =>
                   let ra := list_fill rs (List.map snd (snd cg)) in
                   let r' := cons_fill (snd ra) cs' in
                   ((fst cg, List.combine (List.map fst (snd cg)) (fst ra)) :: fst r', snd r')
               end) (snd rS) (rm_cons Mr) in
  (mk_rmem (rm_name Mr) (fst rN) (fst rS) (fst rC), snd rC).

(** The sites of a function of a [mutual def] as written: its non-uniform
    parameters over [Δ] and the frames', its scrutinee's type over them,
    its result type over the scrutinee, and each clause over the variables
    it binds. *)
Definition fun_sites (Ξ : gstack) (Δ : ctx) (f : raw_fun) : list fill_site :=
  tele_sites (Δ ++ gs_tele Ξ) (rf_nparams f) ++
  exp_sites (rf_nparams f ++ Δ ++ gs_tele Ξ) (rf_scrut f) ++
  exp_sites (ce_hole :: rf_nparams f ++ Δ ++ gs_tele Ξ) (rf_res f) ++
  List.concat (List.map (fun b => exp_sites (ctx_holes (snd (fst b)) ++ Δ ++ gs_tele Ξ) (snd b)) (rf_clauses f)).

(** A function filled. *)
Definition fun_fill (rs : list fill_result) (f : raw_fun) : (raw_fun * list fill_result)%type :=
  let rN := tele_fill rs (rf_nparams f) in
  let rZ := exp_fill (snd rN) (rf_scrut f) in
  let rA := exp_fill (snd rZ) (rf_res f) in
  let rC := (fix cl_fill (rs : list fill_result) (cl : list (string * nat * exp)) : (list (string * nat * exp) * list fill_result)%type :=
               match cl with
               | nil => (nil, rs)
               | b :: cl' => let r := exp_fill rs (snd b) in let r' := cl_fill (snd r) cl' in ((fst b, fst r) :: fst r', snd r')
               end) (snd rA) (rf_clauses f) in
  (mk_rfun (rf_name f) (fst rN) (fst rZ) (fst rA) (fst rC), snd rC).

(** The sites of a command's own terms, at the stack [Ξ]; a module's
    nested commands are filled when they run. *)
Definition cmd_sites (Ξ : gstack) (c : ccmd) : list fill_site :=
  match c with
  | cc_def _ _ _ A oM => exp_sites (gs_tele Ξ) A ++ match oM with Some M => exp_sites (gs_tele Ξ) M | None => nil end
  | cc_mod _ _ Δ _ => tele_sites (gs_tele Ξ) Δ
  | cc_alias _ _ Δ E | cc_ind_alias _ _ Δ E => tele_sites (gs_tele Ξ) Δ ++ modexp_sites (Δ ++ gs_tele Ξ) E
  | cc_eval M oA => exp_sites (gs_tele Ξ) M ++ match oA with Some A => exp_sites (gs_tele Ξ) A | None => nil end
  | cc_ind _ R => tele_sites (gs_tele Ξ) (rd_uparams R) ++ List.concat (List.map (member_sites Ξ R) (rd_members R))
  | cc_mdef _ _ Δ fs => tele_sites (gs_tele Ξ) Δ ++ List.concat (List.map (fun_sites Ξ Δ) fs)
  | cc_open E _ | cc_builtin _ E => modexp_sites (gs_tele Ξ) E
  | cc_load _ => nil
  end.

(** A command filled from the results of its sites. *)
Definition cmd_fill (rs : list fill_result) (c : ccmd) : ccmd :=
  match c with
  | cc_def x b pv A oM =>
      let rA := exp_fill rs A in
      cc_def x b pv (fst rA) match oM with Some M => Some (fst (exp_fill (snd rA) M)) | None => None end
  | cc_mod x pv Δ cs => cc_mod x pv (fst (tele_fill rs Δ)) cs
  | cc_alias x pv Δ E => let rΔ := tele_fill rs Δ in cc_alias x pv (fst rΔ) (fst (modexp_fill (snd rΔ) E))
  | cc_ind_alias x pv Δ H => let rΔ := tele_fill rs Δ in cc_ind_alias x pv (fst rΔ) (fst (modexp_fill (snd rΔ) H))
  | cc_open E its => cc_open (fst (modexp_fill rs E)) its
  | cc_builtin kd H => cc_builtin kd (fst (modexp_fill rs H))
  | cc_eval M oA =>
      let rM := exp_fill rs M in
      cc_eval (fst rM) match oA with Some A => Some (fst (exp_fill (snd rM) A)) | None => None end
  | cc_ind pv R =>
      let rU := tele_fill rs (rd_uparams R) in
      let rMs := (fix ms_fill (rs : list fill_result) (ms : list raw_member) : list raw_member :=
                    match ms with
                    | nil => nil
                    | Mr :: ms' => let r := member_fill rs Mr in fst r :: ms_fill (snd r) ms'
                    end) (snd rU) (rd_members R) in
      cc_ind pv (mk_raw (fst rU) rMs (rd_rec R))
  | cc_mdef b pv Δ fs =>
      let rD := tele_fill rs Δ in
      let rFs := (fix fs_fill (rs : list fill_result) (fs : list raw_fun) : list raw_fun :=
                    match fs with
                    | nil => nil
                    | f :: fs' => let r := fun_fill rs f in fst r :: fs_fill (snd r) fs'
                    end) (snd rD) fs in
      cc_mdef b pv (fst rD) rFs
  | cc_load _ => c
  end.

(** The arguments a member's type former gets from a head that denotes
    [ds_ind Θ' p k Ns] applied to [args]: [Ns] at the first [|Θ'|] of
    them, then the rest. *)
Definition head_args (Θ' : ctx) (Ns args : list exp) : list exp :=
  List.map (fun N => N[sb_of_list Id (List.firstn (List.length Θ') args)]) Ns ++ List.skipn (List.length Θ') args.

(** The result of a site: its annotation's head denotes a member of the
    group at [p], or is the type former of one; the uniform parameters are
    the first [ind_nu] arguments, strengthened past the [d] binders the
    annotation is under. *)
Inductive site_resolves (Θ : gdeps) (Ξ : gstack) : fill_site -> fill_result -> Prop :=
(** A member, resolved as any member is *)
| site_resolves_member : forall Γ d Z H x Θ' p k Ns D Us,
    app_head Z = a_mem H x ->
    mdenote Θ Ξ (ctx_holes d ++ Γ) (me_mem H x) (ds_ind Θ' p k Ns) ->
    ind_lookup Θ Ξ p = Some D ->
    img_pats (List.repeat true d) (List.firstn (ind_nu D) (head_args Θ' Ns (app_args Z))) = Some Us ->
    site_resolves Θ Ξ (Γ, d, Z) (p, Us)
(** The type former itself *)
| site_resolves_former : forall Γ d Z p k D Us,
    app_head Z = a_ind p k ->
    ind_lookup Θ Ξ p = Some D ->
    img_pats (List.repeat true d) (List.firstn (ind_nu D) (app_args Z)) = Some Us ->
    site_resolves Θ Ξ (Γ, d, Z) (p, Us).

(** A command filled: every site resolved, and the command computed from
    the results. *)
Definition elim_fill_ok (Θ : gdeps) (Ξ : gstack) (c c' : ccmd) : Prop :=
  exists rs, Forall2 (site_resolves Θ Ξ) (cmd_sites Ξ c) rs /\ cmd_fill rs c = c'.

(** A telescope over the stack's filled: every site resolved, and the
    telescope computed from the results (a unit's parameters). *)
Definition tele_fill_ok (Θ : gdeps) (Ξ : gstack) (Δ Δ' : ctx) : Prop :=
  exists rs, Forall2 (site_resolves Θ Ξ) (tele_sites (gs_tele Ξ) Δ) rs /\ fst (tele_fill rs Δ) = Δ'.

(** Whether a command has terms of its own, which may have sites. *)
Definition cmd_terms (c : ccmd) : bool :=
  match c with
  | cc_load _ => false
  | _ => true
  end.

(** A command without terms of its own has no sites. *)
Lemma cmd_sites_terms : forall Ξ c, cmd_terms c = false -> cmd_sites Ξ c = nil.
Proof. intros Ξ [] H; cbn in H |- *; first [ reflexivity | discriminate ]. Qed.

(** Filling keeps whether a command has terms of its own. *)
Lemma cmd_fill_terms : forall rs c, cmd_terms (cmd_fill rs c) = cmd_terms c.
Proof. intros rs []; reflexivity. Qed.

(** A command without terms of its own is filled as it is. *)
Lemma elim_fill_no_terms : forall Θ Ξ c c', cmd_terms c = false -> elim_fill_ok Θ Ξ c c' -> c' = c.
Proof.
  intros * Ht (rs & Hrs & <-); rewrite (cmd_sites_terms _ _ Ht) in Hrs; inversion Hrs; subst.
  destruct c; cbn in Ht |- *; first [ reflexivity | discriminate ].
Qed.

(** ** Merging

    Two records merge field by field: a field bound on one side only keeps
    that binding, and one bound on both sides must be bound to the same
    type.  A unit merges the record of each unit it imports into its own,
    and a [builtin] command merges the binding it makes. *)
Definition bt_merge (B1 B2 : builtins) : option builtins :=
  match bt_nat B1, bt_nat B2 with
  | None, o | o, None => Some (mk_builtins o)
  | Some p1, Some p2 => if qname_eq_dec p1 p2 then Some (mk_builtins (Some p1)) else None
  end.

Lemma bt_eta : forall B, mk_builtins (bt_nat B) = B.
Proof. intros []; reflexivity. Qed.

Lemma bt_merge_empty_l : forall B, bt_merge bt_empty B = Some B.
Proof. intros [o]; reflexivity. Qed.

Lemma bt_merge_empty_r : forall B, bt_merge B bt_empty = Some B.
Proof. intros [[p |]]; reflexivity. Qed.

Lemma bt_merge_comm : forall B1 B2, bt_merge B1 B2 = bt_merge B2 B1.
Proof.
  intros [[p1 |]] [[p2 |]]; unfold bt_merge; cbn; try reflexivity.
  destruct (qname_eq_dec p1 p2) as [<- | Hne];
    [ destruct (qname_eq_dec p1 p1); congruence | destruct (qname_eq_dec p2 p1); congruence ].
Qed.

Lemma bt_merge_idem : forall B, bt_merge B B = Some B.
Proof. intros [[p |]]; unfold bt_merge; cbn; [ destruct (qname_eq_dec p p); [ reflexivity | contradiction ] | reflexivity ]. Qed.

(** Associativity, where failure is a value of its own. *)
Lemma bt_merge_assoc : forall B1 B2 B3,
    match bt_merge B1 B2 with Some B12 => bt_merge B12 B3 | None => None end =
    match bt_merge B2 B3 with Some B23 => bt_merge B1 B23 | None => None end.
Proof.
  intros [[p1 |]] [[p2 |]] [[p3 |]]; unfold bt_merge; cbn;
    repeat (match goal with |- context [qname_eq_dec ?a ?b] => destruct (qname_eq_dec a b); try subst end; cbn);
    congruence.
Qed.

(** What a merge has: the bindings of both sides. *)
Lemma bt_merge_inv : forall B1 B2 B p,
    bt_merge B1 B2 = Some B -> bt_nat B = Some p -> bt_nat B1 = Some p \/ bt_nat B2 = Some p.
Proof.
  intros [[p1 |]] [[p2 |]] B p H Hp; unfold bt_merge in H; cbn in H;
    try (destruct (qname_eq_dec p1 p2)); try discriminate; injection H as <-; cbn in Hp; auto.
Qed.

(** A merge of well-formed records is well formed. *)
Lemma bt_merge_wf : forall Θ Ξ B1 B2 B,
    builtins_wf Θ Ξ B1 -> builtins_wf Θ Ξ B2 -> bt_merge B1 B2 = Some B -> builtins_wf Θ Ξ B.
Proof. intros * H1 H2 Hm p Hp; destruct (bt_merge_inv _ _ _ _ Hm Hp) as [E | E]; [ exact (H1 _ E) | exact (H2 _ E) ]. Qed.

(** The binding a [builtin natural ≔ X] command makes, from the bindings
    before it: [X] names the inductive type [p], with the shape of the
    natural numbers, in [Type@0]; it merges the binding of [p] alone. *)
Definition bt_bind_nat (B : builtins) (p : qname) : option builtins := bt_merge B (mk_builtins (Some p)).

(** ** Bindings Only Grow

    A record only gains bindings ([bt_merge_le]): those of an earlier point
    of a run are below those of a later one ([bt_le]). *)

Definition bt_le (B1 B2 : builtins) : Prop := bt_nat B1 = None \/ B1 = B2.

Lemma bt_le_refl : forall B, bt_le B B.
Proof. right; reflexivity. Qed.

Lemma bt_le_trans : forall B1 B2 B3, bt_le B1 B2 -> bt_le B2 B3 -> bt_le B1 B3.
Proof. intros * [H | <-] H2; [ left; exact H | exact H2 ]. Qed.

Lemma bt_merge_le : forall B1 B2 B, bt_merge B1 B2 = Some B -> bt_le B1 B /\ bt_le B2 B.
Proof.
  intros [[p1 |]] [[p2 |]] B H; unfold bt_merge in H; cbn in H;
    try (destruct (qname_eq_dec p1 p2) as [<- |]); try discriminate; injection H as <-;
    split; solve [ left; reflexivity | right; reflexivity ].
Qed.

Lemma bt_bind_nat_le : forall B p B', bt_bind_nat B p = Some B' -> bt_le B B'.
Proof. intros * H; exact (proj1 (bt_merge_le _ _ _ H)). Qed.

(** A successful step of a literal pass. *)
Lemma lbind_lok_inv : forall {A B} (m : lres A) (k : A -> lres B) r, lbind m k = lok r -> exists a, m = lok a /\ k a = lok r.
Proof. intros * H; destruct m; cbn in H; [ eauto | discriminate ]. Qed.

(** Whether a sort is [nat_sort]. *)
Definition is_nat_sort (A : exp) : bool :=
  match A with
  | a_univ (a_llit (0, 0)) => true
  | _ => false
  end.

Lemma is_nat_sort_spec : forall A, is_nat_sort A = true <-> A = nat_sort.
Proof.
  intros A; split; [| intros ->; reflexivity ].
  destruct A; try discriminate; cbn.
  destruct A; try discriminate.
  destruct o as [[| a] [| b]]; try discriminate; reflexivity.
Qed.
