(** * Privacy

    Privacy is not a matter of typing: a public definition may unfold to a
    term naming a private one, and its type may name one, so typing and δ
    read no privacy flag.  It is a check on the terms a command introduces, as
    they are written: every member reference rooted at a unit is to a public
    member, or to a member of a module that is an open frame or an ancestor of
    one, that is, the reference is made inside the module declaring the
    member.  Aliases are followed through the global context to the module
    that declares the member. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
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
  | gm_check Φ _ => gm_entry Φ ip
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
    eauto using gc_entry_dsub, gc_sub_module, gc_sub_levels.
Qed.

(** ** Member References *)

(** The member references a term is written with: every [a_mem H x], every
    submodule [me_mem H y], and every name an import [use]s, as [(E, n)]. *)
Fixpoint exp_refs (M : exp) : list (modexp * string)%type :=
  match M with
  | a_typ _ | a_nat | a_zero | a_True | a_true | a_False | a_var _ => nil
  | a_succ M => exp_refs M
  | a_natrec A MZ MS M => exp_refs A ++ exp_refs MZ ++ exp_refs MS ++ exp_refs M
  | a_exfalso A M | a_pi A M | a_fn A M | a_app A M => exp_refs A ++ exp_refs M
  | a_let b B => bnd_refs b ++ exp_refs B
  | a_mem H x => (H, x) :: modexp_refs H
  end
with modexp_refs (H : modexp) : list (modexp * string)%type :=
  match H with
  | me_unit _ | me_var _ => nil
  | me_mem H y => (H, y) :: modexp_refs H
  | me_app H N => modexp_refs H ++ exp_refs N
  | me_lit U => gunit_refs U
  end
with bnd_refs (b : bnd) : list (modexp * string)%type :=
  match b with
  | b_def A M => exp_refs A ++ exp_refs M
  | b_mod U => gunit_refs U
  end
with gunit_refs (U : gunit) : list (modexp * string)%type :=
  match U with
  | gu_mk Δ D =>
      (fix tele_refs (Δ : list centry) : list (modexp * string)%type :=
         match Δ with
         | nil => nil
         | e :: Δ' => centry_refs e ++ tele_refs Δ'
         end) Δ ++ moddef_refs D
  end
with moddef_refs (D : moddef) : list (modexp * string)%type :=
  match D with
  | md_body Φ => gmod_refs Φ
  | md_alias E => modexp_refs E
  end
with gmod_refs (Φ : gmod) : list (modexp * string)%type :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ _ E => gmod_refs Φ ++ gentry_refs E
  | gm_check Φ c => gmod_refs Φ ++ bcheck_refs c
  end
with bcheck_refs (c : bcheck) : list (modexp * string)%type :=
  match c with
  | bc_import E ns => modexp_refs E ++ map (fun n => (E, n)) ns
  end
with gentry_refs (E : gentry) : list (modexp * string)%type :=
  match E with
  | ge_def _ _ A B => exp_refs A ++ match B with Some M => exp_refs M | None => nil end
  | ge_mod _ U => gunit_refs U
  end
with centry_refs (e : centry) : list (modexp * string)%type :=
  match e with
  | ce_ass A => exp_refs A
  | ce_def A M => exp_refs A ++ exp_refs M
  | ce_mod U => gunit_refs U
  end.

Fixpoint tele_refs (Δ : ctx) : list (modexp * string)%type :=
  match Δ with
  | nil => nil
  | e :: Δ' => centry_refs e ++ tele_refs Δ'
  end.

(** ** Accessibility *)

(** The module [qd] is an open frame, or an ancestor of one: a reference made
    here is made inside it. *)
Definition open_anc (Ξ : gstack) (qd : qname) : Prop :=
  exists mp U suf, List.In (mp, U) Ξ /\ q_unit mp = q_unit qd /\ q_chain mp = q_chain qd ++ suf.

(** A reference rooted at a unit is to a public member, or made inside the
    module declaring it.  A reference rooted at a local module is not
    checked: its members are local. *)
Definition ref_ok (Θ : gdeps) (Ξ : gstack) (r : (modexp * string)%type) : Prop :=
  match modexp_spine (fst r) with
  | (me_unit fp, _, pre) =>
      forall qd, mdecl Θ Ξ (me_unit fp) (pre ++ snd r :: nil) qd true -> open_anc Ξ qd
  | _ => True
  end.

Definition acc_ok (Θ : gdeps) (Ξ : gstack) (l : list (modexp * string)%type) : Prop :=
  List.Forall (ref_ok Θ Ξ) l.

(** Accessibility reads declarations, which equal lookups preserve. *)
Lemma acc_ok_dsub : forall Θ1 Θ2 Ξ, Θ2 ⊑ Θ1 ->
    forall l, acc_ok Θ1 Ξ l -> acc_ok Θ2 Ξ l.
Proof.
  intros * Hs l Hl; eapply List.Forall_impl; [| exact Hl ].
  intros [H x]; unfold ref_ok; cbn [fst snd].
  destruct (modexp_spine H) as [[[] args] pre]; auto.
  intros Hok qd Hd; apply Hok; eapply mdecl_dsub; eassumption.
Qed.
