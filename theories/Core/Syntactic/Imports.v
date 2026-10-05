(** * Opens: Generation and Expansion

    An open declares names for the members of a module: [open E use (n)]
    makes [n] a private definition equal to [E.n], [open E as Z] makes [Z]
    a private alias of [E], and the items of [open E as Z use (n)] select
    from [Z].

    In a frame an open is a command, [cc_open].  Whether an item declares a
    definition or an alias is decided on the member's kind alone
    ([open_gen]), which an oracle gives ([mk_oracle], tied to
    [member_kind] by [mk_spec]); the command gives each definition the
    normal form of its member type ([Command]).  In a local body an open
    is a pre-form, [gm_open], that the core expands into ordinary entries
    before typing ([open_local]): [cmd_xp] is the identity on every former
    but [gm_open], which it replaces by the generated entries, each
    definition at its member type as it stands, which an oracle gives
    ([mt_oracle], tied to [member_type] by [mt_spec]).  No typing rule
    mentions [gm_open].

    Entries are self-style, so every entry of a body is read in a context of
    the same shape, its self slot over the context of the body: what an open
    generates needs no weakening to be appended. *)

From Stdlib Require Import List String Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Members Command.
Import Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Oracles *)

(** A member-type oracle, and what makes it the member types of [Θ]. *)
Definition mt_oracle : Type := ctx -> modexp -> list string -> option mres.

Definition mt_spec (Θ : gctx) (mt : mt_oracle) : Prop :=
  forall Γ H ch R, mt Γ H ch = Some R <-> member_type Θ Γ H ch R.

(** A member-kind oracle, and what makes it the member kinds of [Θ]. *)
Definition mk_oracle : Type := ctx -> modexp -> list string -> option mkind.

Definition mk_spec (Θ : gctx) (mk : mk_oracle) : Prop :=
  forall Γ H ch k, mk Γ H ch = Some k <-> member_kind Θ Γ H ch k.

(** The kinds a member-type oracle gives. *)
Definition mt_kinds (mt : mt_oracle) : mk_oracle := fun Γ H ch => option_map mres_kind (mt Γ H ch).

(** Two oracles meeting the specification agree everywhere. *)
Lemma mt_spec_ext : forall Θ mt mt', mt_spec Θ mt -> mt_spec Θ mt' ->
    forall Γ H ch, mt Γ H ch = mt' Γ H ch.
Proof.
  intros * Hs Hs' Γ H ch.
  destruct (mt Γ H ch) as [R |] eqn:E.
  - symmetry; apply Hs', Hs, E.
  - destruct (mt' Γ H ch) as [R |] eqn:E'; [| reflexivity ].
    apply Hs', Hs in E'; congruence.
Qed.

Lemma mk_spec_ext : forall Θ mk mk', mk_spec Θ mk -> mk_spec Θ mk' ->
    forall Γ H ch, mk Γ H ch = mk' Γ H ch.
Proof.
  intros * Hs Hs' Γ H ch.
  destruct (mk Γ H ch) as [k |] eqn:E.
  - symmetry; apply Hs', Hs, E.
  - destruct (mk' Γ H ch) as [k |] eqn:E'; [| reflexivity ].
    apply Hs', Hs in E'; congruence.
Qed.

(** ** Results *)

(** Why an open fails. *)
Inductive xerr : Set :=
(** The open target is not a module *)
| xe_target : modexp -> xerr
(** Not a member of the target *)
| xe_member : modexp -> string -> xerr
(** A member both used and exported *)
| xe_both : string -> xerr
(** A name the open declares twice *)
| xe_fresh : string -> xerr.

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

(** What an item declares, decided on the kind of the member alone: its
    type is computed where the item is declared. *)
Inductive igen : Set :=
(** [ig_def d pv H n]: the definition [d] equal to [H.n] *)
| ig_def : string -> bool -> modexp -> string -> igen
(** [ig_alias d pv E]: the alias [d] of [E] *)
| ig_alias : string -> bool -> modexp -> igen.

(** The item [it], selecting from [src] in [Γ]: a member's definition, or
    the alias of a submodule.  A missing member is reported against the
    target [E] of the open. *)
Definition item_gen (mk : mk_oracle) (Γ : ctx) (src E : modexp) (it : iitem) : xres igen :=
  let '(n, d, pv) := it in
  match mk Γ src (n :: nil) with
  | Some mk_term => xok (ig_def d pv src n)
  | Some mk_mod => xok (ig_alias d pv (me_mem src n))
  | None => xfail (xe_member E n)
  end.

(** The first member named both by a private and by a public item. *)
Definition src_has (n : string) (pv : bool) (its : list iitem) : bool :=
  existsb (fun it => let '(m, _, pv') := it in String.eqb n m && Bool.eqb pv pv') its.

Definition both_dup (its : list iitem) : option string :=
  match find (fun it => let '(n, _, pv) := it in src_has n (negb pv) its) its with
  | Some (n, _, _) => Some n
  | None => None
  end.

(** The first name a list repeats. *)
Fixpoint name_dup (xs : list string) : option string :=
  match xs with
  | nil => None
  | x :: xs' => if existsb (String.eqb x) xs' then Some x else name_dup xs'
  end.

(** [open_with k item E oz its]: [k] is the kind of the target [E], which
    must be a module; each item gives what [item] makes of it, no member is
    both used and exported, and the names declared, the alias [Z] included,
    are distinct. *)
Definition open_with {I : Type} (k : option mkind) (item : iitem -> xres I) (E : modexp)
  (oz : option string) (its : list iitem) : xres (list I) :=
  match k with
  | Some mk_mod =>
      let+ gs := xmap item its in
      match both_dup its with
      | Some n => xfail (xe_both n)
      | None =>
          match name_dup (open_names oz its) with
          | Some d => xfail (xe_fresh d)
          | None => xok gs
          end
      end
  | _ => xfail (xe_target E)
  end.

Lemma open_with_ext : forall I k (item item' : iitem -> xres I), (forall it, item it = item' it) ->
    forall E oz its, open_with k item E oz its = open_with k item' E oz its.
Proof.
  intros * Hext E oz its; unfold open_with.
  replace (xmap item its) with (xmap item' its); [ reflexivity |].
  induction its as [| it its IH]; cbn; [ reflexivity | ]; rewrite Hext, IH; reflexivity.
Qed.

(** [open_gen mk Γ E oZ Γs src its]: the items of an open of [E] in [Γ],
    each read from [src] in [Γs].  [src] is [E] in [Γ], or the alias [Z] in
    the context after it. *)
Definition open_gen (mk : mk_oracle) (Γ : ctx) (E : modexp) (oz : option string)
  (Γs : ctx) (src : modexp) (its : list iitem) : xres (list igen) :=
  open_with (mk Γ E nil) (item_gen mk Γs src E) E oz its.

Lemma open_gen_ext : forall mk mk', (forall Γ H ch, mk Γ H ch = mk' Γ H ch) ->
    forall Γ E oz Γs src its, open_gen mk Γ E oz Γs src its = open_gen mk' Γ E oz Γs src its.
Proof.
  intros * Hext Γ E oz Γs src its; unfold open_gen; rewrite Hext.
  apply open_with_ext; intros [[n d] pv]; cbn; rewrite Hext; reflexivity.
Qed.

(** ** Opens in a Body

    In a body, an open is read in the self context of its position: the
    alias, if any, is an entry of the body, and its items select from the
    alias through the self slot. *)

Definition open_alias (Φ : gmod) (E : modexp) (oz : option string) : gmod :=
  match oz with
  | Some z => Φ ⊳ z ↦ ge_mod true (gu_mk nil (md_alias E))
  | None => Φ
  end.

Definition open_src (E : modexp) (oz : option string) : modexp :=
  match oz with
  | Some z => me_mem (me_var 0) z
  | None => E
  end.

(** In a body, an item is an entry at once: a definition gets the member
    type, which [mt] gives, as it stands. *)
Definition item_entry (mt : mt_oracle) (Γ : ctx) (src E : modexp) (it : iitem) : xres (string * gentry)%type :=
  let '(n, d, pv) := it in
  match mt Γ src (n :: nil) with
  | Some (mr_term A) => xok (d, ge_def pv A (Some (a_mem src n)))
  | Some (mr_mod _) => xok (d, ge_mod pv (gu_mk nil (md_alias (me_mem src n))))
  | None => xfail (xe_member E n)
  end.

Definition open_local (mt : mt_oracle) (Γ : ctx) (E : modexp) (oz : option string)
  (Γs : ctx) (src : modexp) (its : list iitem) : xres (list (string * gentry)%type) :=
  open_with (mt_kinds mt Γ E nil) (item_entry mt Γs src E) E oz its.

Lemma open_local_ext : forall mt mt', (forall Γ H ch, mt Γ H ch = mt' Γ H ch) ->
    forall Γ E oz Γs src its, open_local mt Γ E oz Γs src its = open_local mt' Γ E oz Γs src its.
Proof.
  intros * Hext Γ E oz Γs src its; unfold open_local, mt_kinds; rewrite Hext.
  apply open_with_ext; intros [[n d] pv]; cbn; rewrite Hext; reflexivity.
Qed.

(** The generated entries appended to [Φ], in order. *)
Fixpoint ents_append (Φ : gmod) (es : list (string * gentry)%type) : gmod :=
  match es with
  | nil => Φ
  | (d, E) :: es' => ents_append (gm_ext Φ d E) es'
  end.

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

Definition bnd_skel (b : bnd) : option gunit :=
  match b with
  | b_mod U => Some U
  | _ => None
  end.

(** The skeleton of a context. *)
Definition ctx_skel (Γ : ctx) : skel := map centry_skel Γ.

Section Expansion.
  Variable mt : mt_oracle.

  Fixpoint exp_xp (S : skel) (M : exp) {struct M} : xres exp :=
    match M with
    | a_typ _ | a_nat | a_zero | a_True | a_true | a_False | a_var _ | a_const _ => xok M
    | a_succ M => let+ M' := exp_xp S M in xok (a_succ M')
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
    | a_mem H x => let+ H' := modexp_xp S H in xok (a_mem H' x)
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
        let+ E' := gentry_xp (Some (gu_body nil Φ') :: S) E in
        xok (gm_ext Φ' x E')
    | gm_open Φ H oz its =>
        let+ Φ' := gmod_xp S Φ in
        let+ H' := modexp_xp (Some (gu_body nil Φ') :: S) H in
        let+ es := open_local mt (skel_ctx (Some (gu_body nil Φ') :: S)) H' oz
                     (skel_ctx (Some (gu_body nil (open_alias Φ' H' oz)) :: S)) (open_src H' oz) its in
        xok (ents_append (open_alias Φ' H' oz) es)
    end
  with gentry_xp (S : skel) (E : gentry) {struct E} : xres gentry :=
    match E with
    | ge_def pv A oM =>
        let+ A' := exp_xp S A in
        let+ oM' := match oM with
                    | Some M => let+ M' := exp_xp S M in xok (Some M')
                    | None => xok None
                    end in
        xok (ge_def pv A' oM')
    | ge_mod pv U => let+ U' := gunit_xp S U in xok (ge_mod pv U')
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

  (** A command's own terms: the nested commands of a module are expanded
      when they run. *)
  Definition cmd_xp (S : skel) (c : ccmd) : xres ccmd :=
    match c with
    | cc_def x b pv A oM =>
        let+ A' := exp_xp S A in
        let+ oM' := match oM with
                    | Some M => let+ M' := exp_xp S M in xok (Some M')
                    | None => xok None
                    end in
        xok (cc_def x b pv A' oM')
    | cc_mod x pv Δ cs =>
        let+ Δ' := tele_xp S Δ in
        xok (cc_mod x pv Δ' cs)
    | cc_alias x pv Δ E =>
        let+ Δ' := tele_xp S Δ in
        let+ E' := modexp_xp (map centry_skel Δ' ++ S) E in
        xok (cc_alias x pv Δ' E')
    | cc_load fp => xok (cc_load fp)
    | cc_open E oz its =>
        let+ E' := modexp_xp S E in
        xok (cc_open E' oz its)
    | cc_eval M oA =>
        let+ M' := exp_xp S M in
        let+ oA' := match oA with
                    | Some A => let+ A' := exp_xp S A in xok (Some A')
                    | None => xok None
                    end in
        xok (cc_eval M' oA')
    end.
End Expansion.

(** ** The Declarative Wrappers

    Expansion and generation with any oracle meeting the specification.  Any
    two such oracles agree ([mt_spec_ext]), so the results are unique
    ([xp_ext]).  A command is expanded in the skeleton of the context it is
    checked in. *)

Definition cmd_xp_ok (Θ : gctx) (Γ : ctx) (c c' : ccmd) : Prop :=
  exists mt, mt_spec Θ mt /\ cmd_xp mt (ctx_skel Γ) c = xok c'.

Definition tele_xp_ok (Θ : gctx) (S : skel) (Δ Δ' : ctx) : Prop :=
  exists mt, mt_spec Θ mt /\ tele_xp mt S Δ = xok Δ'.

(** The items of an open in a frame, by kinds. *)
Definition open_gen_ok (Θ : gctx) (Γ : ctx) (E : modexp) (oz : option string)
  (Γs : ctx) (src : modexp) (its : list iitem) (gs : list igen) : Prop :=
  exists mk, mk_spec Θ mk /\ open_gen mk Γ E oz Γs src its = xok gs.

(** ** Expansion Reads the Oracle Only *)

Section Ext.
  Variables (mt mt' : mt_oracle).
  Hypothesis Hext : forall Γ H ch, mt Γ H ch = mt' Γ H ch.

  #[local]
  Ltac xp_step :=
    repeat (cbn [xbind] in *;
            first
              [ match goal with
                | IH : forall S, ?f mt S ?x = ?f mt' S ?x |- context [?f mt ?S' ?x] => rewrite (IH S')
                end
              | rewrite (open_local_ext _ _ Hext)
              | match goal with
                | |- context [xbind (?f mt' ?S ?x) _] => destruct (f mt' S x)
                | |- context [xbind (open_local mt' ?G ?H ?oz ?Gs ?src ?its) _] => destruct (open_local mt' G H oz Gs src its)
                | |- context [match ?o with Some _ => _ | None => _ end] => is_var o; destruct o
                end ]);
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
    - (* a definition binding *)
      destruct oA as [A |]; [ rewrite (H A eq_refl) |]; xp_step.
    - (* a unit: its telescope, then its definition *)
      match goal with |- xbind ?a _ = xbind ?b _ => assert (Ht : a = b) end.
      { clear H0; induction H as [| e Δ He HF IH]; [ reflexivity |]; cbn [xbind]; rewrite IH.
        match goal with |- xbind ?t _ = _ => destruct t end; cbn [xbind]; [ rewrite He |]; reflexivity. }
      rewrite Ht; match goal with |- xbind ?t _ = _ => destruct t end; cbn [xbind]; [ rewrite H0 |]; reflexivity.
    - (* a definition entry, with or without a body *)
      destruct oM as [M |]; [ rewrite (H0 M eq_refl) |]; xp_step.
  Qed.

  Lemma tele_xp_ext : forall Δ S, tele_xp mt S Δ = tele_xp mt' S Δ.
  Proof.
    induction Δ as [| e Δ IH]; intros; cbn; [ reflexivity |]; rewrite IH.
    destruct (tele_xp mt' S Δ); cbn; [ rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 xp_ext_all))))))) |];
      reflexivity.
  Qed.

  Lemma cmd_xp_ext : forall c S, cmd_xp mt S c = cmd_xp mt' S c.
  Proof.
    destruct xp_ext_all as (He & Hm & _).
    intros [x b pv A [M |] | x pv Δ cs | x pv Δ E | fp | E oz its | M [A |]] S; cbn [cmd_xp];
      rewrite ?He, ?Hm, ?tele_xp_ext; try reflexivity.
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

Lemma cmd_xp_ok_functional : forall Θ Γ c c1 c2, cmd_xp_ok Θ Γ c c1 -> cmd_xp_ok Θ Γ c c2 -> c1 = c2.
Proof.
  intros * (mt1 & Hs1 & E1) (mt2 & Hs2 & E2).
  rewrite (cmd_xp_ext _ _ (mt_spec_ext _ _ _ Hs1 Hs2)) in E1; congruence.
Qed.

Lemma tele_xp_ok_functional : forall Θ S Δ Δ1 Δ2, tele_xp_ok Θ S Δ Δ1 -> tele_xp_ok Θ S Δ Δ2 -> Δ1 = Δ2.
Proof.
  intros * (mt1 & Hs1 & E1) (mt2 & Hs2 & E2).
  rewrite (tele_xp_ext _ _ (mt_spec_ext _ _ _ Hs1 Hs2)) in E1; congruence.
Qed.

Lemma open_gen_ok_functional : forall Θ Γ E oz Γs src its gs1 gs2,
    open_gen_ok Θ Γ E oz Γs src its gs1 -> open_gen_ok Θ Γ E oz Γs src its gs2 -> gs1 = gs2.
Proof.
  intros * (mk1 & Hs1 & E1) (mk2 & Hs2 & E2).
  rewrite (open_gen_ext _ _ (mk_spec_ext _ _ _ Hs1 Hs2)) in E1; congruence.
Qed.

(** Any oracle meeting the specification computes the wrapped results. *)
Lemma cmd_xp_ok_spec : forall Θ Γ mt c c', mt_spec Θ mt -> cmd_xp_ok Θ Γ c c' -> cmd_xp mt (ctx_skel Γ) c = xok c'.
Proof.
  intros * Hs (mt1 & Hs1 & E1); rewrite (cmd_xp_ext _ _ (mt_spec_ext _ _ _ Hs Hs1)); exact E1.
Qed.

Lemma tele_xp_ok_spec : forall Θ mt S Δ Δ', mt_spec Θ mt -> tele_xp_ok Θ S Δ Δ' -> tele_xp mt S Δ = xok Δ'.
Proof.
  intros * Hs (mt1 & Hs1 & E1); rewrite (tele_xp_ext _ _ (mt_spec_ext _ _ _ Hs Hs1)); exact E1.
Qed.

Lemma open_gen_ok_spec : forall Θ mk Γ E oz Γs src its gs, mk_spec Θ mk ->
    open_gen_ok Θ Γ E oz Γs src its gs -> open_gen mk Γ E oz Γs src its = xok gs.
Proof.
  intros * Hs (mk1 & Hs1 & E1); rewrite (open_gen_ext _ _ (mk_spec_ext _ _ _ Hs Hs1)); exact E1.
Qed.

(** The specification depends on member types only, so an oracle meeting it
    for one global context meets it for any with the same member types. *)
Lemma mt_spec_transfer : forall Θ Θ' mt,
    (forall Γ H ch R, member_type Θ Γ H ch R <-> member_type Θ' Γ H ch R) ->
    mt_spec Θ mt -> mt_spec Θ' mt.
Proof. intros * Heq Hs Γ H ch R; rewrite <- Heq; apply Hs. Qed.

(** ** Expansion Keeps the Command

    Expansion changes a command's terms only: its former and its other
    arguments stay. *)

Definition ccmd_head (c : ccmd) : nat :=
  match c with
  | cc_def _ _ _ _ _ => 0
  | cc_mod _ _ _ _ => 1
  | cc_alias _ _ _ _ => 2
  | cc_load _ => 3
  | cc_open _ _ _ => 4
  | cc_eval _ _ => 5
  end.

Lemma cmd_xp_head : forall mt S c c', cmd_xp mt S c = xok c' -> ccmd_head c' = ccmd_head c.
Proof.
  intros mt S [x b pv A M | x pv Δ cs | x pv Δ E | fp | E oz its | M [A |]] c' Ex; cbn in Ex;
    repeat match goal with
           | Ex : xbind ?m _ = xok _ |- _ => destruct m; cbn in Ex; [| discriminate ]
           end;
    injection Ex as <-; reflexivity.
Qed.

Lemma cmd_xp_def_inv : forall mt S x b pv A oM c', cmd_xp mt S (cc_def x b pv A oM) = xok c' ->
    exists A' oM', c' = cc_def x b pv A' oM' /\ (oM = None <-> oM' = None).
Proof.
  intros * Ex; cbn in Ex; destruct (exp_xp mt S A); cbn in Ex; [| discriminate ].
  destruct oM as [M |]; cbn in Ex.
  - destruct (exp_xp mt S M); cbn in Ex; [| discriminate ].
    injection Ex as <-; do 2 eexists; split; [ reflexivity | split; congruence ].
  - injection Ex as <-; do 2 eexists; split; [ reflexivity | split; congruence ].
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
