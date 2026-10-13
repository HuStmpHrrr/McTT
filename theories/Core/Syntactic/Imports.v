(** * Opens: Generation and Expansion

    An open declares names for the members of a module: [open E use (n)]
    makes [n] a private definition equal to [E.n], [open E as y] makes [y]
    a private alias of [E].  What an item declares is computed from the
    member's type ([import_gen]), so it needs the member types of the global
    context, given here as an oracle ([mt_oracle]) that [mt_spec] ties to
    [member_type].

    At the global level an open is a command, [cc_open], which runs the
    definitions and aliases it generates as commands ([Command]).  In a local
    body it is a pre-form, [gm_open], that the core expands into ordinary
    entries before typing: [cmd_xp] is the identity on every former but
    [gm_open], which it replaces by the generated entries.  No typing rule
    mentions [gm_open]. *)

From Stdlib Require Import List String Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Members Command Builtin.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** ** Oracles *)

(** A member-type oracle, and what makes it the member types of [Θ ⍮ Ξ]. *)
Definition mt_oracle : Type := ctx -> modexp -> list string -> option mres.

Definition mt_spec (Θ : gdeps) (Ξ : gstack) (mt : mt_oracle) : Prop :=
  forall Γ H ch R, mt Γ H ch = Some R <-> member_type Θ Ξ Γ H ch R.

(** Two oracles meeting the specification agree everywhere. *)
Lemma mt_spec_ext : forall Θ Ξ mt mt', mt_spec Θ Ξ mt -> mt_spec Θ Ξ mt' ->
    forall Γ H ch, mt Γ H ch = mt' Γ H ch.
Proof.
  intros * Hs Hs' Γ H ch.
  destruct (mt Γ H ch) as [R |] eqn:E.
  - symmetry; apply Hs', Hs, E.
  - destruct (mt' Γ H ch) as [R |] eqn:E'; [| reflexivity ].
    apply Hs', Hs in E'; congruence.
Qed.

(** A declaration-site oracle, and what makes it [mdecl] of [Θ ⍮ Ξ]: the
    qualified name of the entry a chain reaches, read through aliases. *)
Definition md_oracle : Type := modexp -> list string -> option qname.

Definition md_spec (Θ : gdeps) (Ξ : gstack) (md : md_oracle) : Prop :=
  forall H ch p, md H ch = Some p <->
    exists qd pv, mdecl Θ Ξ H ch qd pv /\ p = qname_in qd (List.last ch EmptyString).

Lemma md_spec_ext : forall Θ Ξ md md', md_spec Θ Ξ md -> md_spec Θ Ξ md' ->
    forall H ch, md H ch = md' H ch.
Proof.
  intros * Hs Hs' H ch.
  destruct (md H ch) as [p |] eqn:E.
  - symmetry; apply Hs', Hs, E.
  - destruct (md' H ch) as [p |] eqn:E'; [| reflexivity ].
    apply Hs', Hs in E'; congruence.
Qed.

(** The oracles of expansion: member types, declaration sites, and what a
    numeral stands for ([nat_binding], a function of the state). *)
Record xoracle : Type := mk_xo { xo_mt : mt_oracle; xo_md : md_oracle; xo_nb : nbind }.

Definition xo_spec (Θ : gdeps) (Ξ : gstack) (xo : xoracle) : Prop :=
  mt_spec Θ Ξ (xo_mt xo) /\ md_spec Θ Ξ (xo_md xo) /\ xo_nb xo = nat_binding Θ Ξ.

(** ** Results *)

(** Why an import fails. *)
Inductive xerr : Set :=
(** The import target is not a module *)
| xe_target : modexp -> xerr
(** Not a member of the target *)
| xe_member : modexp -> string -> xerr
(** A member both used and exported *)
| xe_both : string -> xerr
(** A name the import declares twice *)
| xe_fresh : string -> xerr
(** The name of an eliminator, as written, is not of an inductive type *)
| xe_ind : qname -> xerr
(** A numeral where the visible bindings of the natural numbers disagree *)
| xe_nat : nat -> xerr.

Inductive xres (A : Type) : Type :=
| xok : A -> xres A
| xfail : xerr -> xres A.

Arguments xok {A}.
Arguments xfail {A}.

Definition xbind {A B} (m : xres A) (f : A -> xres B) : xres B :=
  match m with
  | xok a => f a
  | xfail e => xfail e
  end.

#[local] Notation "'let+' x ':=' m 'in' f" := (xbind m (fun x => f))
  (at level 200, x name, m at level 100, f at level 200, right associativity).

Fixpoint xmap {A B} (f : A -> xres B) (l : list A) : xres (list B) :=
  match l with
  | nil => xok nil
  | a :: l' => let+ b := f a in let+ bs := xmap f l' in xok (b :: bs)
  end.

(** ** Generation *)

(** What an item declares, read in the context of the import. *)
Inductive igen : Set :=
(** [ig_def d pv A M]: the definition [d] of type [A] equal to [M] *)
| ig_def : string -> bool -> typ -> exp -> igen
(** [ig_alias d pv E]: the alias [d] of [E] *)
| ig_alias : string -> bool -> modexp -> igen.

(** The item [it] of an import of [H]: a member's definition or alias, or
    the alias of [H] itself. *)
Definition item_gen (mt : mt_oracle) (Γ : ctx) (H : modexp) (it : iitem) : xres igen :=
  match it with
  | (None, d, pv) => xok (ig_alias d pv H)
  | (Some n, d, pv) =>
      match mt Γ H (n :: nil) with
      | Some (mr_term A) => xok (ig_def d pv A (a_mem H n))
      | Some (mr_mod _) => xok (ig_alias d pv (me_mem H n))
      | None => xfail (xe_member H n)
      end
  end.

(** The first member named both by a private and by a public item. *)
Definition src_has (n : string) (pv : bool) (its : list iitem) : bool :=
  existsb (fun it => match it with
                     | (Some m, _, pv') => String.eqb n m && Bool.eqb pv pv'
                     | _ => false
                     end) its.

Definition both_dup (its : list iitem) : option string :=
  match find (fun it => match it with
                        | (Some n, _, pv) => src_has n (negb pv) its
                        | _ => false
                        end) its with
  | Some (Some n, _, _) => Some n
  | _ => None
  end.

(** The first name a list repeats. *)
Fixpoint name_dup (xs : list string) : option string :=
  match xs with
  | nil => None
  | x :: xs' => if existsb (String.eqb x) xs' then Some x else name_dup xs'
  end.

(** [import_gen mt Γ H its]: [H] is a module, each item names a member of
    it, no member is both used and exported, and the names declared are
    distinct; then each item's declaration, all in [Γ]. *)
Definition import_gen (mt : mt_oracle) (Γ : ctx) (H : modexp) (its : list iitem) : xres (list igen) :=
  match mt Γ H nil with
  | Some (mr_mod _) =>
      let+ gs := xmap (item_gen mt Γ H) its in
      match both_dup its with
      | Some n => xfail (xe_both n)
      | None =>
          match name_dup (map iitem_name its) with
          | Some d => xfail (xe_fresh d)
          | None => xok gs
          end
      end
  | _ => xfail (xe_target H)
  end.

Lemma import_gen_ext : forall mt mt', (forall Γ H ch, mt Γ H ch = mt' Γ H ch) ->
    forall Γ H its, import_gen mt Γ H its = import_gen mt' Γ H its.
Proof.
  intros * Hext Γ H its; unfold import_gen; rewrite Hext.
  replace (xmap (item_gen mt Γ H) its) with (xmap (item_gen mt' Γ H) its); [ reflexivity |].
  induction its as [| [[[n |] d] pv] its IH]; cbn; [ reflexivity | | ]; rewrite ?Hext, IH; reflexivity.
Qed.

(** ** Expansion

    [S] is the slot skeleton of the context: [Some U] for a module slot
    holding the (already expanded) unit [U], [None] for anything else.  The
    oracle is asked in the context [skel_ctx S]: member types read a context
    only through its module slots. *)

Abbreviation skel := (list (option gunit)).

Definition skel_ctx (S : skel) : ctx :=
  map (fun o => match o with Some U => ce_mod U | None => ce_ass a_nat end) S.

Definition centry_skel (e : centry) : option gunit :=
  match e with
  | ce_mod U => Some U
  | _ => None
  end.

Definition entry_skel (E : gentry) : option gunit :=
  match E with
  | ge_mod _ U => Some U
  | _ => None
  end.

Definition bnd_skel (b : bnd) : option gunit :=
  match b with
  | b_mod U => Some U
  | _ => None
  end.

(** The skeleton of the indices a body binds, newest first. *)
Fixpoint body_skel (Φ : gmod) : skel :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ _ E => entry_skel E :: body_skel Φ
  | gm_open Φ _ its => repeat None (List.length its) ++ body_skel Φ
  end.

(** A generated item as a body entry. *)
Definition ig_entry (g : igen) : (string * gentry)%type :=
  match g with
  | ig_def d pv A M => (d, ge_def true pv A (Some M))
  | ig_alias d pv E => (d, ge_mod pv (gu_mk nil (md_alias E)))
  end.

(** The generated entries appended to [Φ], in order.  All are read in the
    context of the import, so the [k]-th is weakened by the [k] before it. *)
Fixpoint gens_append (Φ : gmod) (k : nat) (gs : list igen) : gmod :=
  match gs with
  | nil => Φ
  | g :: gs' =>
      let '(d, E) := ig_entry g in
      gens_append (gm_ext Φ d (gentry_wk E (wk_shiftn k))) (S k) gs'
  end.

(** An inductive type read as a term: the module [x] of [H] that its
    declaration is filed in, the module's arguments applied to its type
    former. *)
Definition ind_head (md : md_oracle) (H : modexp) (x : string) : option exp :=
  match modexp_spine H with
  | (me_unit fp, args, pre) =>
      option_map (fun p => apps (a_ind p) args) (md (me_unit fp) (pre ++ x :: ind_name :: nil))
  | _ => None
  end.

(** The name of an eliminator as written, [M.#] for the module [M] the
    user names, resolved through aliases to the declaration's. *)
Definition elim_xp (md : md_oracle) (p : qname) : xres qname :=
  match md (me_unit (q_unit p)) (q_chain p) with
  | Some p' => xok p'
  | None => xfail (xe_ind p)
  end.

Definition mem_xp (md : md_oracle) (H : modexp) (x : string) : exp :=
  match ind_head md H x with
  | Some M => M
  | None => a_mem H x
  end.

Section Expansion.
  Variable xo : xoracle.

  Fixpoint exp_xp (S : skel) (M : exp) {struct M} : xres exp :=
    match M with
    | a_typ _ | a_level _ | a_llit _ | a_nat | a_zero | a_True | a_true | a_False | a_var _ => xok M
    | a_univ M => let+ M' := exp_xp S M in xok (a_univ M')
    | a_succ M => let+ M' := exp_xp S M in xok (a_succ M')
    | a_succl M => let+ M' := exp_xp S M in xok (a_succl M')
    | a_maxl M N =>
        let+ M' := exp_xp S M in
        let+ N' := exp_xp S N in
        xok (a_maxl M' N')
    | a_natrec A MZ MS M =>
        let+ A' := exp_xp (None :: S) A in
        let+ MZ' := exp_xp S MZ in
        let+ MS' := exp_xp (None :: None :: S) MS in
        let+ M' := exp_xp S M in
        xok (a_natrec A' MZ' MS' M')
    | a_exfalso A M =>
        let+ A' := exp_xp (None :: S) A in
        let+ M' := exp_xp S M in
        xok (a_exfalso A' M')
    | a_ind _ | a_con _ _ => xok M
    (** A numeral: the chain of the constructors of the natural numbers
        bound, or the builtin [ℕ]'s where none is bound. *)
    | a_nlit n =>
        match xo_nb xo with
        | nb_none => xok (nat_to_exp n)
        | nb_one p z s => xok (nat_chain p z s n)
        | nb_many => xfail (xe_nat n)
        end
    | a_elim p nm A Bs M =>
        let+ p' := elim_xp (xo_md xo) p in
        let+ A' := exp_xp (List.repeat None nm ++ S) A in
        let+ Bs' := (fix brs_xp (Bs : list (String.string * nat * exp)) : xres (list (String.string * nat * exp)) :=
                       match Bs with
                       | nil => xok nil
                       | b :: Bs0 =>
                           let+ B' := exp_xp (List.repeat None (snd (fst b)) ++ S) (snd b) in
                           let+ Bs0' := brs_xp Bs0 in
                           xok ((fst b, B') :: Bs0')
                       end) Bs in
        let+ M' := exp_xp S M in
        xok (a_elim p' nm A' Bs' M')
    | a_pi A B =>
        let+ A' := exp_xp S A in
        let+ B' := exp_xp (None :: S) B in
        xok (a_pi A' B')
    | a_fn A M =>
        let+ A' := exp_xp S A in
        let+ M' := exp_xp (None :: S) M in
        xok (a_fn A' M')
    | a_app M N =>
        let+ M' := exp_xp S M in
        let+ N' := exp_xp S N in
        xok (a_app M' N')
    | a_let b B =>
        let+ b' := bnd_xp S b in
        let+ B' := exp_xp (bnd_skel b' :: S) B in
        xok (a_let b' B')
    | a_mem H x => let+ H' := modexp_xp S H in xok (mem_xp (xo_md xo) H' x)
    end
  with modexp_xp (S : skel) (H : modexp) {struct H} : xres modexp :=
    match H with
    | me_unit _ | me_var _ => xok H
    | me_mem H y => let+ H' := modexp_xp S H in xok (me_mem H' y)
    | me_app H N =>
        let+ H' := modexp_xp S H in
        let+ N' := exp_xp S N in
        xok (me_app H' N')
    | me_lit U => let+ U' := gunit_xp S U in xok (me_lit U')
    end
  with bnd_xp (S : skel) (b : bnd) {struct b} : xres bnd :=
    match b with
    | b_def oA M =>
        let+ oA' := match oA with
                    | Some A => let+ A' := exp_xp S A in xok (Some A')
                    | None => xok None
                    end in
        let+ M' := exp_xp S M in
        xok (b_def oA' M')
    | b_mod U => let+ U' := gunit_xp S U in xok (b_mod U')
    end
  with gunit_xp (S : skel) (U : gunit) {struct U} : xres gunit :=
    match U with
    | gu_mk Δ D =>
        let+ Δ' := (fix tele_xp (Δ : list centry) : xres ctx :=
                      match Δ with
                      | nil => xok nil
                      | e :: Δ0 =>
                          let+ Δ0' := tele_xp Δ0 in
                          let+ e' := centry_xp (map centry_skel Δ0' ++ S) e in
                          xok (e' :: Δ0')
                      end) Δ in
        let+ D' := moddef_xp (map centry_skel Δ' ++ S) D in
        xok (gu_mk Δ' D')
    end
  with moddef_xp (S : skel) (D : moddef) {struct D} : xres moddef :=
    match D with
    | md_body Φ => let+ Φ' := gmod_xp S Φ in xok (md_body Φ')
    | md_alias E => let+ E' := modexp_xp S E in xok (md_alias E')
    end
  with gmod_xp (S : skel) (Φ : gmod) {struct Φ} : xres gmod :=
    match Φ with
    | gm_nil => xok gm_nil
    | gm_ext Φ x E =>
        let+ Φ' := gmod_xp S Φ in
        let+ E' := gentry_xp (body_skel Φ' ++ S) E in
        xok (gm_ext Φ' x E')
    | gm_open Φ H its =>
        let+ Φ' := gmod_xp S Φ in
        let+ H' := modexp_xp (body_skel Φ' ++ S) H in
        let+ gs := import_gen (xo_mt xo) (skel_ctx (body_skel Φ' ++ S)) H' its in
        xok (gens_append Φ' 0 gs)
    end
  with gentry_xp (S : skel) (E : gentry) {struct E} : xres gentry :=
    match E with
    | ge_def b pv A B =>
        let+ A' := exp_xp S A in
        let+ B' := match B with
                   | Some M => let+ M' := exp_xp S M in xok (Some M')
                   | None => xok None
                   end in
        xok (ge_def b pv A' B')
    | ge_mod pv U => let+ U' := gunit_xp S U in xok (ge_mod pv U')
    | ge_ind _ _ => xok E
    end
  with centry_xp (S : skel) (e : centry) {struct e} : xres centry :=
    match e with
    | ce_ass A => let+ A' := exp_xp S A in xok (ce_ass A')
    | ce_def A M =>
        let+ A' := exp_xp S A in
        let+ M' := exp_xp S M in
        xok (ce_def A' M')
    | ce_mod U => let+ U' := gunit_xp S U in xok (ce_mod U')
    end.

  (** A telescope, each entry in the skeleton of the entries outside it. *)
  Fixpoint tele_xp (S : skel) (Δ : ctx) : xres ctx :=
    match Δ with
    | nil => xok nil
    | e :: Δ0 =>
        let+ Δ0' := tele_xp S Δ0 in
        let+ e' := centry_xp (map centry_skel Δ0' ++ S) e in
        xok (e' :: Δ0')
    end.

  (** The arguments of a constructor as written: each binds a variable for
      the ones after it. *)
  Fixpoint rargs_xp (S : skel) (args : list (string * exp)) : xres (list (string * exp)) :=
    match args with
    | nil => xok nil
    | (y, T) :: args' =>
        let+ T' := exp_xp S T in
        let+ args'' := rargs_xp (None :: S) args' in
        xok ((y, T') :: args'')
    end.

  (** A declaration as written: its parameters as a telescope, its sort over
      the uniform ones, its constructors' arguments over the declared type
      and all the parameters. *)
  Definition decl_xp (S : skel) (R : raw_decl) : xres raw_decl :=
    let+ Δ' := tele_xp S (rd_params R) in
    let S' := map centry_skel Δ' ++ S in
    let+ A' := exp_xp (skipn (List.length (rd_params R) - rd_nu R) S') (rd_sort R) in
    let+ cs' := xmap (fun cg => let+ args := rargs_xp (None :: S') (snd cg) in xok (fst cg, args)) (rd_cons R) in
    xok (mk_raw (rd_nu R) Δ' A' cs').

  (** A command's own terms: the nested commands of a module are expanded
      when they run. *)
  Definition cmd_xp (S : skel) (c : ccmd) : xres ccmd :=
    match c with
    | cc_def x b pv A (Some M) =>
        let+ A' := exp_xp S A in
        let+ M' := exp_xp S M in
        xok (cc_def x b pv A' (Some M'))
    | cc_def x b pv A None =>
        let+ A' := exp_xp S A in
        xok (cc_def x b pv A' None)
    | cc_mod x pv Δ cs =>
        let+ Δ' := tele_xp S Δ in
        xok (cc_mod x pv Δ' cs)
    | cc_alias x pv Δ E =>
        let+ Δ' := tele_xp S Δ in
        let+ E' := modexp_xp (map centry_skel Δ' ++ S) E in
        xok (cc_alias x pv Δ' E')
    | cc_load fp => xok (cc_load fp)
    | cc_open E its =>
        let+ E' := modexp_xp S E in
        xok (cc_open E' its)
    | cc_eval M oA =>
        let+ M' := exp_xp S M in
        let+ oA' := match oA with
                    | Some A => let+ A' := exp_xp S A in xok (Some A')
                    | None => xok None
                    end in
        xok (cc_eval M' oA')
    | cc_ind x pv D =>
        let+ D' := decl_xp S D in
        xok (cc_ind x pv D')
    | cc_builtin k p =>
        let+ p' := elim_xp (xo_md xo) p in
        xok (cc_builtin k p')
    end.
End Expansion.

(** The skeleton of a frame: its parameters are assumptions. *)
Definition frame_skel (Ξ : gstack) : skel := map (fun _ => None) (gs_tele Ξ).

(** ** The Declarative Wrappers

    Expansion and generation with any oracles meeting the specifications.
    Any two such oracles agree ([mt_spec_ext], [md_spec_ext]), so the
    results are unique ([xp_ext]). *)

Definition cmd_xp_ok (Θ : gdeps) (Ξ : gstack) (c c' : ccmd) : Prop :=
  exists xo, xo_spec Θ Ξ xo /\ cmd_xp xo (frame_skel Ξ) c = xok c'.

Definition tele_xp_ok (Θ : gdeps) (Ξ : gstack) (S : skel) (Δ Δ' : ctx) : Prop :=
  exists xo, xo_spec Θ Ξ xo /\ tele_xp xo S Δ = xok Δ'.

Definition import_gen_ok (Θ : gdeps) (Ξ : gstack) (Γ : ctx) (H : modexp) (its : list iitem) (gs : list igen) : Prop :=
  exists mt, mt_spec Θ Ξ mt /\ import_gen mt Γ H its = xok gs.

(** ** Expansion Reads the Oracle Only *)

Section Ext.
  Variables (mt mt' : xoracle).
  Hypothesis Hext : forall Γ H ch, xo_mt mt Γ H ch = xo_mt mt' Γ H ch.
  Hypothesis Hdext : forall H ch, xo_md mt H ch = xo_md mt' H ch.
  Hypothesis Hnext : xo_nb mt = xo_nb mt'.

  Lemma mem_xp_ext : forall H x, mem_xp (xo_md mt) H x = mem_xp (xo_md mt') H x.
  Proof.
    intros; unfold mem_xp, ind_head; destruct (modexp_spine H) as [[[] ?] ?]; rewrite ?Hdext; reflexivity.
  Qed.

  #[local]
  Ltac xp_step :=
    repeat (cbn [xbind] in *;
            first
              [ match goal with
                | IH : forall S, ?f mt S ?x = ?f mt' S ?x |- context [?f mt ?S' ?x] => rewrite (IH S')
                end
              | rewrite (import_gen_ext _ _ Hext)
              | rewrite mem_xp_ext
              | match goal with
                | |- context [xbind (?f mt' ?S ?x) _] => destruct (f mt' S x)
                | |- context [xbind (import_gen (xo_mt mt') ?G ?H ?its) _] => destruct (import_gen (xo_mt mt') G H its)
                | |- context [match ?o with Some _ => _ | None => _ end] => is_var o; destruct o
                end
              | rewrite Hnext ]);
    try reflexivity.

  Lemma xp_ext_all :
    (forall M S, exp_xp mt S M = exp_xp mt' S M) /\
    (forall H S, modexp_xp mt S H = modexp_xp mt' S H) /\
    (forall b S, bnd_xp mt S b = bnd_xp mt' S b) /\
    (forall U S, gunit_xp mt S U = gunit_xp mt' S U) /\
    (forall D S, moddef_xp mt S D = moddef_xp mt' S D) /\
    (forall Φ S, gmod_xp mt S Φ = gmod_xp mt' S Φ) /\
    (forall E S, gentry_xp mt S E = gentry_xp mt' S E) /\
    (forall e S, centry_xp mt S e = centry_xp mt' S e).
  Proof.
    apply syn_mut_ind; intros; cbn [exp_xp modexp_xp bnd_xp gunit_xp moddef_xp gmod_xp gentry_xp centry_xp].
    all: try solve [ xp_step ].
    - (* an eliminator: its name, its motive, its branches, its scrutinee *)
      unfold elim_xp; rewrite Hdext; destruct (xo_md mt' _ _); cbn [xbind]; [| reflexivity ].
      rewrite H; destruct (exp_xp mt' _ A); cbn [xbind]; [| reflexivity ].
      match goal with |- xbind ?a _ = xbind ?b _ => assert (Ht : a = b) end.
      { clear - H0; induction H0 as [| b Bs Hb HF IH]; [ reflexivity |]; cbn [xbind].
        rewrite Hb; destruct (exp_xp mt' _ (snd b)); cbn [xbind]; [ rewrite IH |]; reflexivity. }
      rewrite Ht; match goal with |- xbind ?t _ = _ => destruct t end; cbn [xbind]; [ rewrite H1 |]; reflexivity.
    - (* a definition binding *)
      destruct oA as [A |]; [ rewrite (H A eq_refl) |]; xp_step.
    - (* a unit: its telescope, then its definition *)
      match goal with |- xbind ?a _ = xbind ?b _ => assert (Ht : a = b) end.
      { clear H0; induction H as [| e Δ He HF IH]; [ reflexivity |]; cbn [xbind]; rewrite IH.
        match goal with |- xbind ?t _ = _ => destruct t end; cbn [xbind]; [ rewrite He |]; reflexivity. }
      rewrite Ht; match goal with |- xbind ?t _ = _ => destruct t end; cbn [xbind]; [ rewrite H0 |]; reflexivity.
    - (* an entry: its type, then its body *)
      destruct B as [M |]; [ rewrite (H0 M eq_refl) |]; xp_step.
  Qed.

  Lemma tele_xp_ext : forall Δ S, tele_xp mt S Δ = tele_xp mt' S Δ.
  Proof.
    induction Δ as [| e Δ IH]; intros; cbn; [ reflexivity |]; rewrite IH.
    destruct (tele_xp mt' S Δ); cbn; [ rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 xp_ext_all))))))) |];
      reflexivity.
  Qed.

  Lemma decl_xp_ext : forall R S, decl_xp mt S R = decl_xp mt' S R.
  Proof.
    destruct xp_ext_all as (He & _).
    assert (Hr : forall args S, rargs_xp mt S args = rargs_xp mt' S args).
    { induction args as [| [y T] args IH]; intros; cbn; [ reflexivity |].
      rewrite He; destruct (exp_xp mt' S T); cbn; [ rewrite IH |]; reflexivity. }
    intros [nu Δ A cs] S; unfold decl_xp; cbn [rd_params rd_sort rd_cons rd_nu].
    rewrite tele_xp_ext; destruct (tele_xp mt' S Δ) as [Δ' |]; cbn [xbind]; [| reflexivity ].
    rewrite He; destruct (exp_xp mt' _ A); cbn [xbind]; [| reflexivity ].
    match goal with |- xbind ?a _ = xbind ?b _ => assert (Ht : a = b) end.
    { induction cs as [| cg cs IH]; cbn; [ reflexivity |].
      rewrite Hr; destruct (rargs_xp mt' _ (snd cg)); cbn; [ rewrite IH |]; reflexivity. }
    rewrite Ht; reflexivity.
  Qed.

  Lemma cmd_xp_ext : forall c S, cmd_xp mt S c = cmd_xp mt' S c.
  Proof.
    destruct xp_ext_all as (He & Hm & _).
    intros [x b pv A [M |] | x pv Δ cs | x pv Δ E | fp | E its | M [A |] | x pv D | k p] S; cbn [cmd_xp];
      rewrite ?He, ?Hm, ?tele_xp_ext, ?decl_xp_ext; try reflexivity.
    all: try solve [ unfold elim_xp; rewrite Hdext; reflexivity ].
    all: repeat (cbn [xbind]; first
                  [ match goal with
                    | |- context [exp_xp mt ?S ?x] => rewrite (He x S)
                    | |- context [modexp_xp mt ?S ?x] => rewrite (Hm x S)
                    end
                  | match goal with
                    | |- context [xbind (?f mt' ?S ?x) _] => destruct (f mt' S x)
                    end ]); reflexivity.
  Qed.
End Ext.

Lemma cmd_xp_ok_functional : forall Θ Ξ c c1 c2, cmd_xp_ok Θ Ξ c c1 -> cmd_xp_ok Θ Ξ c c2 -> c1 = c2.
Proof.
  intros * (mt1 & (Hs1 & Hd1 & Hn1) & E1) (mt2 & (Hs2 & Hd2 & Hn2) & E2).
  rewrite (cmd_xp_ext _ _ (mt_spec_ext _ _ _ _ Hs1 Hs2) (md_spec_ext _ _ _ _ Hd1 Hd2) (eq_trans Hn1 (eq_sym Hn2))) in E1; congruence.
Qed.

Lemma tele_xp_ok_functional : forall Θ Ξ S Δ Δ1 Δ2, tele_xp_ok Θ Ξ S Δ Δ1 -> tele_xp_ok Θ Ξ S Δ Δ2 -> Δ1 = Δ2.
Proof.
  intros * (mt1 & (Hs1 & Hd1 & Hn1) & E1) (mt2 & (Hs2 & Hd2 & Hn2) & E2).
  rewrite (tele_xp_ext _ _ (mt_spec_ext _ _ _ _ Hs1 Hs2) (md_spec_ext _ _ _ _ Hd1 Hd2) (eq_trans Hn1 (eq_sym Hn2))) in E1; congruence.
Qed.

Lemma import_gen_ok_functional : forall Θ Ξ Γ H its gs1 gs2,
    import_gen_ok Θ Ξ Γ H its gs1 -> import_gen_ok Θ Ξ Γ H its gs2 -> gs1 = gs2.
Proof.
  intros * (mt1 & Hs1 & E1) (mt2 & Hs2 & E2).
  rewrite (import_gen_ext _ _ (mt_spec_ext _ _ _ _ Hs1 Hs2)) in E1; congruence.
Qed.

(** Any oracle meeting the specification computes the wrapped results. *)
Lemma cmd_xp_ok_spec : forall Θ Ξ xo c c', xo_spec Θ Ξ xo -> cmd_xp_ok Θ Ξ c c' -> cmd_xp xo (frame_skel Ξ) c = xok c'.
Proof.
  intros * (Hs & Hd & Hn) (mt1 & (Hs1 & Hd1 & Hn1) & E1);
    rewrite (cmd_xp_ext _ _ (mt_spec_ext _ _ _ _ Hs Hs1) (md_spec_ext _ _ _ _ Hd Hd1) (eq_trans Hn (eq_sym Hn1))); exact E1.
Qed.

Lemma tele_xp_ok_spec : forall Θ Ξ xo S Δ Δ', xo_spec Θ Ξ xo -> tele_xp_ok Θ Ξ S Δ Δ' -> tele_xp xo S Δ = xok Δ'.
Proof.
  intros * (Hs & Hd & Hn) (mt1 & (Hs1 & Hd1 & Hn1) & E1);
    rewrite (tele_xp_ext _ _ (mt_spec_ext _ _ _ _ Hs Hs1) (md_spec_ext _ _ _ _ Hd Hd1) (eq_trans Hn (eq_sym Hn1))); exact E1.
Qed.

Lemma import_gen_ok_spec : forall Θ Ξ mt Γ H its gs, mt_spec Θ Ξ mt ->
    import_gen_ok Θ Ξ Γ H its gs -> import_gen mt Γ H its = xok gs.
Proof.
  intros * Hs (mt1 & Hs1 & E1); rewrite (import_gen_ext _ _ (mt_spec_ext _ _ _ _ Hs Hs1)); exact E1.
Qed.

(** The specification depends on member types only, so an oracle meeting it
    for one global context meets it for any with the same member types. *)
Lemma mt_spec_transfer : forall Θ Ξ Θ' Ξ' mt,
    (forall Γ H ch R, member_type Θ Ξ Γ H ch R <-> member_type Θ' Ξ' Γ H ch R) ->
    mt_spec Θ Ξ mt -> mt_spec Θ' Ξ' mt.
Proof. intros * Heq Hs Γ H ch R; rewrite <- Heq; apply Hs. Qed.

Lemma md_spec_transfer : forall Θ Ξ Θ' Ξ' md,
    (forall H ch qd pv, mdecl Θ Ξ H ch qd pv <-> mdecl Θ' Ξ' H ch qd pv) ->
    md_spec Θ Ξ md -> md_spec Θ' Ξ' md.
Proof.
  intros * Heq Hs H ch p; split; intros Hp.
  - apply Hs in Hp as (qd & pv & Hd & ->); exists qd, pv; split; [ apply Heq; exact Hd | reflexivity ].
  - apply Hs; destruct Hp as (qd & pv & Hd & ->); exists qd, pv; split; [ apply Heq; exact Hd | reflexivity ].
Qed.

(** ** Expansion Keeps the Command

    Expansion changes a command's terms only: its former and its other
    arguments stay. *)

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
  end.

Lemma cmd_xp_head : forall mt S c c', cmd_xp mt S c = xok c' -> ccmd_head c' = ccmd_head c.
Proof.
  intros mt S [x b pv A [M |] | x pv Δ cs | x pv Δ E | fp | E its | M [A |] | x pv D | k p] c' Ex; cbn in Ex;
    repeat match goal with
           | Ex : xbind ?m _ = xok _ |- _ => destruct m; cbn in Ex; [| discriminate ]
           end;
    injection Ex as <-; reflexivity.
Qed.

(** An axiom stays an axiom, and a definition a definition. *)
Lemma cmd_xp_def_inv : forall mt S x b pv A oM c', cmd_xp mt S (cc_def x b pv A oM) = xok c' ->
    exists A' oM', c' = cc_def x b pv A' oM' /\ (oM = None <-> oM' = None).
Proof.
  intros * Ex; destruct oM as [M |]; cbn in Ex; destruct (exp_xp mt S A); cbn in Ex; try discriminate.
  - destruct (exp_xp mt S M); cbn in Ex; [| discriminate ]; injection Ex as <-.
    do 2 eexists; split; [ reflexivity | split; discriminate ].
  - injection Ex as <-; do 2 eexists; split; [ reflexivity | tauto ].
Qed.

Lemma cmd_xp_alias_inv : forall mt S x pv Δ E c', cmd_xp mt S (cc_alias x pv Δ E) = xok c' ->
    exists Δ' E', c' = cc_alias x pv Δ' E'.
Proof.
  intros * Ex; cbn in Ex; destruct (tele_xp mt S Δ) as [Δ' |]; cbn in Ex; [| discriminate ].
  destruct (modexp_xp mt _ E); cbn in Ex; [| discriminate ]; injection Ex as <-; eauto.
Qed.

Lemma cmd_xp_mod_inv : forall mt S x pv Δ cs c', cmd_xp mt S (cc_mod x pv Δ cs) = xok c' ->
    exists Δ', tele_xp mt S Δ = xok Δ' /\ c' = cc_mod x pv Δ' cs.
Proof.
  intros * Ex; cbn in Ex; destruct (tele_xp mt S Δ) as [Δ' |]; cbn in Ex; [| discriminate ].
  injection Ex as <-; eauto.
Qed.

Lemma cmd_xp_mod : forall mt S x pv Δ Δ' cs, tele_xp mt S Δ = xok Δ' ->
    cmd_xp mt S (cc_mod x pv Δ cs) = xok (cc_mod x pv Δ' cs).
Proof. intros * E; cbn; rewrite E; reflexivity. Qed.
