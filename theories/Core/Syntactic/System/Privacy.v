(** * Privacy

    Privacy is not a matter of typing: a public definition may unfold to a
    term naming a private one, and its type may name one, so typing and δ
    read no privacy flag.  It is a check on the terms a command introduces,
    as expanded ([Imports]): every member reference rooted at a unit is to a
    public member, or to a member of a module that is an open frame or an
    ancestor of one, that is, the reference is made inside the module
    declaring the member.  Aliases are followed through the global context to
    the module that declares the member.  A reference into a local body, read
    off the syntax by module tables ([ptab]), is to a public entry: inside
    the body, its entries are variables. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Command.
From Mctt.Core.Syntactic.System Require Export MemberLemmas.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** ** Entries

    [gc_entry Θ Ξ p] is the entry a path names, a definition or a submodule,
    read through body modules as [gc_resolve] is: it carries the privacy flag
    of a submodule, which no other lookup reports. *)
Fixpoint gm_entry (Φ : gmod) (ip : list string) : option gentry :=
  match Φ with
  | gm_nil => None
  | gm_ext Φ y E =>
      match ip with
      | nil => None
      | x :: ip' =>
          if String.eqb x y
          then match ip', E with
               | nil, _ => Some E
               | _ :: _, ge_mod _ (gu_mk _ (md_body Φ')) => gm_entry Φ' ip'
               | _, _ => None
               end
          else gm_entry Φ ip
      end
  | gm_open Φ _ _ => gm_entry Φ ip
  end.

Definition gc_entry (Θ : gdeps) (Ξ : gstack) (p : qname) : option gentry :=
  match gs_find Ξ p with
  | Some (U, ip) => gm_entry (gu_mod U) ip
  | None =>
      match gds_lookup Θ (q_unit p) with
      | Some U => gm_entry (gu_mod U) (q_chain p)
      | None => None
      end
  end.

Lemma gm_entry_resolve : forall Φ ip E, gm_resolve Φ ip = Some E -> gm_entry Φ ip = Some E.
Proof.
  fix IH 1; intros [| Φ y E0 | Φ c] ip E H; cbn in H |- *; try discriminate; [| exact (IH _ _ _ H) ].
  destruct ip as [| x ip']; [ discriminate |].
  destruct (String.eqb x y); [| exact (IH _ _ _ H) ].
  destruct ip' as [| z ip''], E0 as [b pv A B | pm [Δ [Φ' | E']]]; try discriminate; auto.
Qed.

Lemma gm_entry_alias : forall Φ T x ip U r, gm_submodule T Φ x ip = Some (mr_alias U r) -> r <> nil ->
    gm_entry Φ (x :: ip) = None.
Proof.
  fix IH 1; intros [| Φ y E0 | Φ c] * H Hr; cbn in H |- *; try discriminate; [| exact (IH _ _ _ _ _ _ H Hr) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H Hr) ].
  destruct E0 as [b pv A B | pm [Δ [Φ' | E']]]; try discriminate.
  - destruct ip as [| z ip']; [ discriminate |]; exact (IH _ _ _ _ _ _ H Hr).
  - injection H as _ <-; destruct ip as [| z ip']; [ contradiction | reflexivity ].
Qed.

Lemma gc_entry_resolve : forall Θ Ξ p E, gc_resolve Θ Ξ p = Some E -> gc_entry Θ Ξ p = Some E.
Proof.
  intros * H; unfold gc_resolve, gc_entry in *.
  destruct (gs_find Ξ p) as [[U ip] |]; [ apply gm_entry_resolve; exact H |].
  destruct (gds_lookup Θ (q_unit p)); [ apply gm_entry_resolve; exact H | discriminate ].
Qed.

Lemma gc_entry_alias : forall Θ Ξ p U r, gc_module Θ Ξ p = Some (mr_alias U r) -> r <> nil ->
    gc_entry Θ Ξ p = None.
Proof.
  intros * H Hr; unfold gc_module, gc_entry in *; rewrite gs_find_tele_find.
  destruct (gs_find_tele Ξ p) as [[[V [| x ip]] T] |]; cbn; [ discriminate | exact (gm_entry_alias _ _ _ _ _ _ H Hr) |].
  destruct (gds_lookup Θ (q_unit p)); [| discriminate ].
  destruct (q_chain p) as [| x ip]; cbn in H; [ discriminate | exact (gm_entry_alias _ _ _ _ _ _ H Hr) ].
Qed.

Lemma gc_entry_dsub : forall Θ1 Θ2 Ξ p E, Θ1 ⊑ Θ2 -> gc_entry Θ1 Ξ p = Some E -> gc_entry Θ2 Ξ p = Some E.
Proof.
  intros * Hs H; unfold gc_entry in *.
  destruct (gs_find Ξ p) as [[U ip] |]; [ exact H |].
  destruct (gds_lookup Θ1 (q_unit p)) as [V |] eqn:E1; [| discriminate ].
  rewrite (Hs _ _ E1); exact H.
Qed.

(** Whether an entry is private. *)
Definition ge_private (E : gentry) : bool :=
  match E with
  | ge_def _ pv _ _ => pv
  | ge_mod pv _ => pv
  end.

(** ** The Module that Declares a Member

    [mdecl Θ Ξ H ch qd pv]: the member at the chain [ch] of the module
    expression [H], reached from a unit, a definition or a submodule, is
    declared in the module named [qd], with privacy [pv].  A chain through a
    global alias goes on in the alias's target, past its arguments. *)
Inductive mdecl (Θ : gdeps) (Ξ : gstack) : modexp -> list string -> qname -> bool -> Prop :=
(** A member reached through body modules, declared in the module the chain
    names before it. *)
| mdl_entry : forall fp ch E pv,
    gc_entry Θ Ξ (q_abs fp ch) = Some E ->
    ge_private E = pv ->
    mdecl Θ Ξ (me_unit fp) ch (q_abs fp (removelast ch)) pv
(** A chain past an alias goes on in the alias's target. *)
| mdl_alias : forall fp ch T E r qd pv,
    r <> nil ->
    gc_module Θ Ξ (q_abs fp ch) = Some (mr_alias (gu_mk T (md_alias E)) r) ->
    mdecl Θ Ξ E r qd pv ->
    mdecl Θ Ξ (me_unit fp) ch qd pv
(** A selection is read as a longer chain from its module. *)
| mdl_mem : forall H y ch qd pv,
    mdecl Θ Ξ H (y :: ch) qd pv ->
    mdecl Θ Ξ (me_mem H y) ch qd pv
(** Arguments do not change where a member is declared. *)
| mdl_app : forall H N ch qd pv,
    mdecl Θ Ξ H ch qd pv ->
    mdecl Θ Ξ (me_app H N) ch qd pv.

#[export]
Hint Constructors mdecl : mctt.

Lemma mdecl_functional : forall Θ Ξ H ch qd pv, mdecl Θ Ξ H ch qd pv ->
    forall qd' pv', mdecl Θ Ξ H ch qd' pv' -> qd = qd' /\ pv = pv'.
Proof.
  induction 1; intros * H2; inversion H2; subst.
  all: try match goal with H1 : gc_module _ _ ?p = Some (mr_alias _ ?r), Hr : ?r <> nil, H2 : gc_entry _ _ ?p = Some _ |- _ =>
         rewrite (gc_entry_alias _ _ _ _ _ H1 Hr) in H2; discriminate end.
  all: try match goal with H1 : gc_entry _ _ ?p = Some _, H2 : gc_entry _ _ ?p = Some _ |- _ =>
         rewrite H1 in H2; injection H2; intros; subst; split; reflexivity end.
  all: try match goal with H1 : gc_module _ _ ?p = Some _, H2 : gc_module _ _ ?p = Some _ |- _ =>
         rewrite H1 in H2; injection H2; intros; subst end.
  all: eauto.
Qed.

(** Declarations are read off lookups, which more dependencies only extend. *)
Lemma mdecl_dsub : forall Θ1 Θ2 Ξ, Θ1 ⊑ Θ2 ->
    forall H ch qd pv, mdecl Θ1 Ξ H ch qd pv -> mdecl Θ2 Ξ H ch qd pv.
Proof.
  intros * Hs; induction 1; [ eapply mdl_entry | eapply mdl_alias | eapply mdl_mem | eapply mdl_app ];
    eauto using gc_entry_dsub, gc_sub_module, gc_sub_deps.
Qed.

(** What follows an alias on a module path is the rest of that path. *)
Lemma gm_submodule_alias_suffix : forall Φ T x ip U r,
    gm_submodule T Φ x ip = Some (mr_alias U r) -> exists pre, ip = pre ++ r.
Proof.
  fix IH 1; intros [| Φ y E0 | Φ c] * H; cbn in H; try discriminate; [| exact (IH _ _ _ _ _ _ H) ].
  destruct (String.eqb x y); [| exact (IH _ _ _ _ _ _ H) ].
  destruct E0 as [b pv A B | pm [Δ [Φ' | E']]]; try discriminate.
  - destruct ip as [| z ip']; [ discriminate |].
    destruct (IH _ _ _ _ _ _ H) as (pre & ->); exists (z :: pre); reflexivity.
  - injection H as _ <-; exists nil; reflexivity.
Qed.

Lemma gs_find_tele_suffix : forall Ξ p U ip T,
    gs_find_tele Ξ p = Some (U, ip, T) -> exists pre, q_chain p = pre ++ ip.
Proof.
  induction Ξ as [| [mp V] Ξ IH]; intros * H; cbn in H; [ discriminate |].
  unfold qname_strip in H.
  destruct (path_beq (q_unit mp) (q_unit p)); [| exact (IH _ _ _ _ H) ].
  destruct (strip_prefix (q_chain mp) (q_chain p)) eqn:E; [| exact (IH _ _ _ _ H) ].
  injection H as _ <- _; exists (q_chain mp); exact (strip_prefix_spec _ _ _ E).
Qed.

Lemma gc_module_alias_suffix : forall Θ Ξ p U r,
    gc_module Θ Ξ p = Some (mr_alias U r) -> exists pre, q_chain p = pre ++ r.
Proof.
  intros * H; unfold gc_module in H.
  destruct (gs_find_tele Ξ p) as [[[V [| x ip]] T] |] eqn:Ef; [ discriminate | |].
  - destruct (gs_find_tele_suffix _ _ _ _ _ Ef) as (pre & ->).
    destruct (gm_submodule_alias_suffix _ _ _ _ _ _ H) as (pre' & ->).
    exists (pre ++ x :: pre'); rewrite <- List.app_assoc; reflexivity.
  - destruct (gds_lookup Θ (q_unit p)); [| discriminate ].
    destruct (q_chain p) as [| x ip]; cbn in H; [ discriminate |].
    destruct (gm_submodule_alias_suffix _ _ _ _ _ _ H) as (pre & ->).
    exists (x :: pre); reflexivity.
Qed.

(** The module [mdecl] finds declares the member: the last name of the
    chain names an entry of it, with the privacy found. *)
Lemma mdecl_entry : forall Θ Ξ H ch qd pv, mdecl Θ Ξ H ch qd pv -> ch <> nil ->
    forall d, exists E, gc_entry Θ Ξ (qname_in qd (List.last ch d)) = Some E /\ ge_private E = pv.
Proof.
  induction 1 as [fp ch E pv HE <- | fp ch T E r qd pv Hr Hm _ IH | H y ch qd pv _ IH | H N ch qd pv _ IH ];
    intros Hch d.
  - exists E; split; [| reflexivity ].
    unfold qname_in; cbn; rewrite <- (List.app_removelast_last _ Hch); exact HE.
  - destruct (gc_module_alias_suffix _ _ _ _ _ Hm) as (pre & Ep); cbn in Ep; subst ch.
    rewrite (List.app_removelast_last d Hr), List.app_assoc, !List.last_last.
    exact (IH Hr d).
  - destruct ch as [| z ch]; [ contradiction |].
    destruct (IH ltac:(discriminate) d) as (E & HE & Hp); exists E; split; [| exact Hp ].
    cbn [List.last] in HE; exact HE.
  - exact (IH Hch d).
Qed.

(** ** Module Tables

    What a reference may know of the module it selects from: nothing, that
    the module is reached from a unit (the global check below decides), or
    the entries of a body, newest first, each with its privacy and its own
    table.  [pt_body ch es] also records the chain [ch] of submodules
    selected from the local module it was read from, which the checker
    reports.  The tables are read off the syntax, in a scope [S] giving the
    table of each index: binders hold [pt_none], a local module the table of
    its unit. *)
(** No induction principle: tables are only computed and read. *)
Unset Elimination Schemes.
Inductive ptab : Set :=
(** Nothing is known: a term variable, a parameter, a definition *)
| pt_none : ptab
(** A chain from a unit, arguments dropped *)
| pt_glob : modexp -> ptab
(** The entries of a local body, newest first *)
| pt_body : list string -> list (string * bool * ptab) -> ptab.
Set Elimination Schemes.

(** The newest entry [x] of a body's table. *)
Fixpoint tab_find (x : string) (es : list (string * bool * ptab)) : option (bool * ptab) :=
  match es with
  | nil => None
  | (y, pv, t) :: es' => if String.eqb x y then Some (pv, t) else tab_find x es'
  end.

(** The table of the submodule [y]. *)
Definition tab_sel (t : ptab) (y : string) : ptab :=
  match t with
  | pt_none => pt_none
  | pt_glob H => pt_glob (me_mem H y)
  | pt_body ch es =>
      match tab_find y es with
      | Some (_, pt_body _ es') => pt_body (ch ++ y :: nil) es'
      | Some (_, t') => t'
      | None => pt_none
      end
  end.

(** The tables a body's entries bind, newest first, as a scope. *)
Definition tab_scope (es : list (string * bool * ptab)) : list ptab := map snd es.

(** Whether an import item declares a private name. *)
Definition iitem_private (it : iitem) : bool := let '(_, _, pv) := it in pv.

(** What an import item names, in the table [t] of the imported module:
    the module itself, or its member. *)
Definition item_tab (t : ptab) (it : iitem) : ptab :=
  match it with
  | (None, _, _) => t
  | (Some n, _, _) => tab_sel t n
  end.

(** The references an import's items make: each member it names. *)
Definition item_refs (t : ptab) (its : list iitem) : list (ptab * string)%type :=
  flat_map (fun it => match it with
                      | (Some n, _, _) => (t, n) :: nil
                      | (None, _, _) => nil
                      end) its.

Fixpoint mtab (S : list ptab) (H : modexp) : ptab :=
  match H with
  | me_unit fp => pt_glob (me_unit fp)
  | me_var k => nth k S pt_none
  | me_mem H y => tab_sel (mtab S H) y
  | me_app H _ => mtab S H
  | me_lit U => utab S U
  end
with utab (S : list ptab) (U : gunit) : ptab :=
  match U with
  | gu_mk Δ D => dtab (repeat pt_none (List.length Δ) ++ S) D
  end
with dtab (S : list ptab) (D : moddef) : ptab :=
  match D with
  | md_body Φ => pt_body nil (btab S Φ)
  | md_alias E => mtab S E
  end
with btab (S : list ptab) (Φ : gmod) : list (string * bool * ptab) :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ x E => let es := btab S Φ in (x, ge_private E, etab (tab_scope es ++ S) E) :: es
  | gm_open Φ H its =>
      let es := btab S Φ in
      let t := mtab (tab_scope es ++ S) H in
      rev (map (fun it => (iitem_name it, iitem_private it, item_tab t it)) its) ++ es
  end
with etab (S : list ptab) (E : gentry) : ptab :=
  match E with
  | ge_def _ _ _ _ => pt_none
  | ge_mod _ U => utab S U
  end.

(** The table a local binding gives its index. *)
Definition bnd_tab (S : list ptab) (b : bnd) : ptab :=
  match b with
  | b_def _ _ => pt_none
  | b_mod U => utab S U
  end.

(** ** Member References *)

(** The member references a term is written with, each with the table of
    the module it selects from: every [a_mem H x] and every submodule
    [me_mem H y]. *)
Fixpoint exp_refs (S : list ptab) (M : exp) : list (ptab * string)%type :=
  match M with
  | a_typ _ | a_univ _ | a_nat | a_zero | a_True | a_true | a_False | a_var _ => nil
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
  | me_lit U => gunit_refs S U
  end
with bnd_refs (S : list ptab) (b : bnd) : list (ptab * string)%type :=
  match b with
  | b_def oA M => match oA with Some A => exp_refs S A | None => nil end ++ exp_refs S M
  | b_mod U => gunit_refs S U
  end
with gunit_refs (S : list ptab) (U : gunit) : list (ptab * string)%type :=
  match U with
  | gu_mk Δ D =>
      (fix tele_refs (Δ : list centry) : list (ptab * string)%type :=
         match Δ with
         | nil => nil
         | e :: Δ' => centry_refs (repeat pt_none (List.length Δ') ++ S) e ++ tele_refs Δ'
         end) Δ ++ moddef_refs (repeat pt_none (List.length Δ) ++ S) D
  end
with moddef_refs (S : list ptab) (D : moddef) : list (ptab * string)%type :=
  match D with
  | md_body Φ => gmod_refs S Φ
  | md_alias E => modexp_refs S E
  end
with gmod_refs (S : list ptab) (Φ : gmod) : list (ptab * string)%type :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ _ E => gmod_refs S Φ ++ gentry_refs (tab_scope (btab S Φ) ++ S) E
  | gm_open Φ H its =>
      gmod_refs S Φ ++ modexp_refs (tab_scope (btab S Φ) ++ S) H ++
        item_refs (mtab (tab_scope (btab S Φ) ++ S) H) its
  end
with gentry_refs (S : list ptab) (E : gentry) : list (ptab * string)%type :=
  match E with
  | ge_def _ _ A B => exp_refs S A ++ match B with Some M => exp_refs S M | None => nil end
  | ge_mod _ U => gunit_refs S U
  end
with centry_refs (S : list ptab) (e : centry) : list (ptab * string)%type :=
  match e with
  | ce_ass A => exp_refs S A
  | ce_def A M => exp_refs S A ++ exp_refs S M
  | ce_mod U => gunit_refs S U
  end.

Fixpoint tele_refs (S : list ptab) (Δ : ctx) : list (ptab * string)%type :=
  match Δ with
  | nil => nil
  | e :: Δ' => centry_refs (repeat pt_none (List.length Δ') ++ S) e ++ tele_refs S Δ'
  end.

(** The references a command makes, as written: its own terms, and for an
    import, its target and each member its items name.  A module's nested
    commands are checked when they run. *)
Definition cmd_refs (c : ccmd) : list (ptab * string)%type :=
  match c with
  | cc_def _ _ _ A oM => exp_refs nil A ++ match oM with Some M => exp_refs nil M | None => nil end
  | cc_mod _ _ Δ _ => tele_refs nil Δ
  | cc_alias _ _ Δ E => tele_refs nil Δ ++ modexp_refs nil E
  | cc_load _ => nil
  | cc_open E its => modexp_refs nil E ++ item_refs (mtab nil E) its
  | cc_eval M oA => exp_refs nil M ++ match oA with Some A => exp_refs nil A | None => nil end
  end.

(** ** Accessibility *)

(** The module [qd] is an open frame, or an ancestor of one: a reference made
    here is made inside it. *)
Definition open_anc (Ξ : gstack) (qd : qname) : Prop :=
  exists mp U suf, List.In (mp, U) Ξ /\ q_unit mp = q_unit qd /\ q_chain mp = q_chain qd ++ suf.

(** A reference to [x] in a module reached from a unit is to a public
    member, or made inside the module declaring it. *)
Definition glob_ok (Θ : gdeps) (Ξ : gstack) (H : modexp) (x : string) : Prop :=
  match modexp_spine H with
  | (me_unit fp, _, pre) =>
      forall qd, mdecl Θ Ξ (me_unit fp) (pre ++ x :: nil) qd true -> open_anc Ξ qd
  | _ => True
  end.

(** A reference into a local body is to a public entry: inside the body,
    its entries are variables, not references. *)
Definition ref_ok (Θ : gdeps) (Ξ : gstack) (r : (ptab * string)%type) : Prop :=
  match fst r with
  | pt_glob H => glob_ok Θ Ξ H (snd r)
  | pt_body _ es => option_map fst (tab_find (snd r) es) <> Some true
  | pt_none => True
  end.

Definition acc_ok (Θ : gdeps) (Ξ : gstack) (l : list (ptab * string)%type) : Prop :=
  List.Forall (ref_ok Θ Ξ) l.

(** Accessibility reads declarations, which equal lookups preserve. *)
Lemma acc_ok_dsub : forall Θ1 Θ2 Ξ, Θ2 ⊑ Θ1 ->
    forall l, acc_ok Θ1 Ξ l -> acc_ok Θ2 Ξ l.
Proof.
  intros * Hs l Hl; eapply List.Forall_impl; [| exact Hl ].
  intros [[| H |] x]; unfold ref_ok, glob_ok; cbn [fst snd]; auto.
  destruct (modexp_spine H) as [[[] args] pre]; auto.
  intros Hok qd Hd; apply Hok; eapply mdecl_dsub; eassumption.
Qed.
