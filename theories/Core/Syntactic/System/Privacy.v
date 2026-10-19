(** * Privacy

    Privacy is not a matter of typing: a public definition may unfold to a
    term naming a private one, and its type may name one, so typing and δ
    read no privacy flag.  It is a check on the terms a command introduces,
    as written: every member reference rooted at a unit is to a
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
From Mctt.Core.Syntactic.System.Global Require Export MemberLemmas.
From Mctt.Core.Syntactic.System.Global Require Import Paths.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** ** Entries

    [gm_entry], [gc_entry], [ge_private] and [mdecl] are defined in
    [Members], where expansion reads them too. *)

Lemma gm_entry_resolve : forall Φ ip E, gm_resolve Φ ip = Some E -> gm_entry Φ ip = Some E.
Proof.
  fix IH 1; intros [| Φ y E0 | Φ c] ip E H; cbn in H |- *; try discriminate; [| exact (IH _ _ _ H) ].
  destruct ip as [| x ip']; [ discriminate |].
  destruct (String.eqb x y); [| exact (IH _ _ _ H) ].
  destruct ip' as [| z ip''], E0 as [b pv A B | pm [Δ [? Φ' | E']] | pv ? D Φ' | pv Δa pa Nsa]; try discriminate; auto;
    exact (IH _ _ _ H).
Qed.

Lemma gc_entry_resolve : forall Θ Ξ p E, gc_resolve Θ Ξ p = Some E -> gc_entry Θ Ξ p = Some E.
Proof.
  intros * H; unfold gc_resolve, gc_resolve_u, gc_entry, gc_entry_u in *.
  destruct (gs_find Ξ p) as [[U ip] |]; [ apply gm_entry_resolve; exact H |].
  destruct (gds_lookup Θ (q_unit p)); [ apply gm_entry_resolve; exact H | discriminate ].
Qed.

Lemma gc_entry_dsub : forall Θ1 Θ2 Ξ p E, Θ1 ⊑ Θ2 -> gc_entry Θ1 Ξ p = Some E -> gc_entry Θ2 Ξ p = Some E.
Proof.
  intros * Hs H; unfold gc_entry, gc_entry_u in *.
  destruct (gs_find Ξ p) as [[U ip] |]; [ exact H |].
  destruct (gds_lookup Θ1 (q_unit p)) as [V |] eqn:E1; [| discriminate ].
  rewrite (Hs _ _ E1); exact H.
Qed.

(** A module of a unit read in a bigger set of dependencies. *)
Lemma gc_unit_dsub : forall Θ1 Θ2 Ξ H r, Θ1 ⊑ Θ2 -> gc_unit Θ1 Ξ H = Some r -> gc_unit Θ2 Ξ H = Some r.
Proof.
  intros * Hs H0; unfold gc_unit in *.
  destruct (mod_qname H) as [mp |]; [| discriminate ].
  destruct (gs_find_tele Ξ mp) as [[[U ip] T0] |]; [ exact H0 |].
  destruct (q_chain mp); [| discriminate ].
  destruct (gds_lookup Θ1 (q_unit mp)) as [V |] eqn:E1; [| discriminate ].
  rewrite (Hs _ _ E1); exact H0.
Qed.

(** An open frame below another is no entry of it. *)
Lemma gc_unit_mem_entry_none : forall Θ Ξ H z T Φ p,
    gc_unit Θ Ξ (me_mem H z) = Some (T, Φ) -> mod_qname (me_mem H z) = Some p -> gc_entry Θ Ξ p = None.
Proof.
  intros * Hu Hp.
  destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq & [Hf | (_ & Hc & _)]); rewrite Hp in Hq; injection Hq as <-.
  - unfold gc_frame in Hf; unfold gc_entry, gc_entry_u; rewrite gs_find_tele_find.
    destruct (gs_find_tele Ξ p) as [[[[Δ [sm Φ0 | E]] [| x ip]] T0] |]; try discriminate;
      try (destruct sm; discriminate); cbn [option_map]; apply gm_entry_nil.
  - cbn in Hp; destruct (mod_qname H) as [p0 |]; [| discriminate ]; injection Hp as <-; cbn in Hc.
    apply List.app_eq_nil in Hc as [_ Hc]; discriminate.
Qed.

(** A module that is a loaded unit or an open frame is stored at its own
    path, and nowhere else. *)
Lemma msite_unit : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H pq, msite Θ Ξ H pq ->
    forall p T Φ, mod_qname H = Some p -> gc_unit Θ Ξ H = Some (T, Φ) -> pq = p.
Proof.
  intros Θ Ξ Hg; induction 1 as [H p0 T0 Φ0 Hq Hu | H pq z E Hs IH He _ | H pq z E E' pq' Hs IH He _ _ _ | H N pq _ _];
    intros p T Φ Hp Hu'.
  - congruence.
  - exfalso; destruct (gc_unit_mem_parent _ _ Hg _ _ _ _ Hu') as (T1 & Φ1 & Hu1 & _).
    cbn in Hp; destruct (mod_qname H) as [p1 |] eqn:Hp1; [| discriminate ]; injection Hp as <-.
    rewrite (IH _ _ _ eq_refl Hu1) in He.
    rewrite (gc_unit_mem_entry_none _ _ _ _ _ _ (qname_in p1 z) Hu' ltac:(cbn; rewrite Hp1; reflexivity)) in He; discriminate.
  - exfalso; destruct (gc_unit_mem_parent _ _ Hg _ _ _ _ Hu') as (T1 & Φ1 & Hu1 & _).
    cbn in Hp; destruct (mod_qname H) as [p1 |] eqn:Hp1; [| discriminate ]; injection Hp as <-.
    rewrite (IH _ _ _ eq_refl Hu1) in He.
    rewrite (gc_unit_mem_entry_none _ _ _ _ _ _ (qname_in p1 z) Hu' ltac:(cbn; rewrite Hp1; reflexivity)) in He; discriminate.
  - discriminate.
Qed.

Lemma msite_functional : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H pq, msite Θ Ξ H pq -> forall pq', msite Θ Ξ H pq' -> pq = pq'.
Proof.
  intros Θ Ξ Hg; induction 1 as [H p T Φ Hq Hu | H pq z E Hs IH He Hb | H pq z E E' pq' Hs IH He Ha Hs' IH' | H N pq Hs IH];
    intros pq0 H0.
  - symmetry; exact (msite_unit _ _ Hg _ _ H0 _ _ _ Hq Hu).
  - inversion H0 as [? ? ? ? Hq0 Hu0 | ? pq1 ? E1 Hs1 He1 Hb1 | ? pq1 ? E1 E1' ? Hs1 He1 Ha1 _ |]; subst.
    + exact (msite_unit _ _ Hg _ _ (ms_body _ _ _ _ _ _ Hs He Hb) _ _ _ Hq0 Hu0).
    + rewrite (IH _ Hs1); reflexivity.
    + rewrite (IH _ Hs1), He1 in He; injection He as <-.
      destruct E1 as [| ? [? [? ?| ?]] | | ]; cbn in Hb, Ha1; try contradiction; discriminate.
  - inversion H0 as [? ? ? ? Hq0 Hu0 | ? pq1 ? E1 Hs1 He1 Hb1 | ? pq1 ? E1 E1' ? Hs1 He1 Ha1 Hs1' |]; subst.
    + exact (msite_unit _ _ Hg _ _ (ms_alias _ _ _ _ _ _ _ _ Hs He Ha Hs') _ _ _ Hq0 Hu0).
    + rewrite (IH _ Hs1), He1 in He; injection He as <-.
      destruct E1 as [| ? [? [? ?| ?]] | | ]; cbn in Hb1, Ha; try contradiction; discriminate.
    + rewrite (IH _ Hs1), He1 in He; injection He as <-; rewrite Ha1 in Ha; injection Ha as <-.
      exact (IH' _ Hs1').
  - inversion H0; subst; [ discriminate | exact (IH _ ltac:(eassumption)) ].
Qed.

(** Where a member is declared, and its privacy, are unique. *)
Lemma mdecl_functional : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H y qd pv, mdecl Θ Ξ H y qd pv ->
    forall qd' pv', mdecl Θ Ξ H y qd' pv' -> qd = qd' /\ pv = pv'.
Proof.
  intros * Hg * [pq E Hs He] * [pq' E' Hs' He'].
  rewrite <- (msite_functional _ _ Hg _ _ Hs _ Hs') in He' |- *.
  rewrite He in He'; injection He' as <-; split; reflexivity.
Qed.

(** Declarations are read off lookups, which more dependencies only extend. *)
Lemma msite_dsub : forall Θ1 Θ2 Ξ, Θ1 ⊑ Θ2 -> forall H pq, msite Θ1 Ξ H pq -> msite Θ2 Ξ H pq.
Proof.
  intros * Hs; induction 1; [ eapply ms_unit | eapply ms_body | eapply ms_alias | eapply ms_app ];
    eauto using gc_unit_dsub, gc_entry_dsub.
Qed.

Lemma mdecl_dsub : forall Θ1 Θ2 Ξ, Θ1 ⊑ Θ2 ->
    forall H y qd pv, mdecl Θ1 Ξ H y qd pv -> mdecl Θ2 Ξ H y qd pv.
Proof.
  intros * Hs * [pq E HH He]; constructor; [ eapply msite_dsub; eassumption | eapply gc_entry_dsub; eassumption ].
Qed.

(** The module [mdecl] finds declares the member: the member names an entry
    of it, with the privacy found. *)
Lemma mdecl_entry : forall Θ Ξ H y qd pv, mdecl Θ Ξ H y qd pv ->
    exists E, gc_entry Θ Ξ (qname_in qd y) = Some E /\ ge_private E = pv.
Proof. intros * [pq E _ He]; exists E; split; [ exact He | reflexivity ]. Qed.

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
  | md_body sm Φ => pt_body nil (btab S Φ)
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
  | ge_ind _ _ _ D Φ => pt_body nil (btab (repeat pt_none (ind_nu D) ++ S) Φ)
  | ge_ind_alias _ _ pm _ _ _ => pt_glob (qname_mod pm)
  end.

(** The table a local binding gives its index. *)
Definition bnd_tab (S : list ptab) (b : bnd) : ptab :=
  match b with
  | b_def _ _ => pt_none
  | b_mod U => utab S U
  end.

(** ** Member References *)

(** The references a name from a unit is written with, as a chain of
    selections: each member, from the chain before it. *)
Fixpoint chain_refs (H : modexp) (ch : list string) : list (ptab * string)%type :=
  match ch with
  | nil => nil
  | y :: ch' => (pt_glob H, y) :: chain_refs (me_mem H y) ch'
  end.

(** The member references a term is written with, each with the table of
    the module it selects from: every [a_mem H x], every submodule
    [me_mem H y], and the name of an eliminator, as written. *)
Fixpoint exp_refs (S : list ptab) (M : exp) : list (ptab * string)%type :=
  match M with
  | a_typ _ | a_level _ | a_llit _ | a_True | a_true | a_False | a_var _ => nil
  | a_succl M | a_univ M => exp_refs S M
  | a_maxl M N => exp_refs S M ++ exp_refs S N
  | a_exfalso A M => exp_refs (pt_none :: S) A ++ exp_refs S M
  | a_ind _ _ | a_con _ _ _ | a_nlit _ | a_ntok => nil
  | a_elim _ _ Bks M =>
      (fix blks_refs (Bks : list eblock) : list (ptab * string)%type :=
         match Bks with
         | nil => nil
         | eb_mk nm oZ A Bs :: Bks' =>
             match oZ with Some Z => exp_refs (repeat pt_none (nm - 1) ++ S) Z | None => nil end ++
             exp_refs (repeat pt_none nm ++ S) A ++
             (fix brs_refs (Bs : list (string * nat * exp)) : list (ptab * string)%type :=
                match Bs with
                | nil => nil
                | b :: Bs' => exp_refs (repeat pt_none (snd (fst b)) ++ S) (snd b) ++ brs_refs Bs'
                end) Bs ++ blks_refs Bks'
         end) Bks ++ exp_refs S M
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
  | md_body sm Φ => gmod_refs S Φ
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
  | ge_ind _ _ _ _ _ | ge_ind_alias _ _ _ _ _ _ => nil
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

(** The references of a group as written: its uniform parameters, and of
    each member its non-uniform parameters and sort over the uniform ones,
    and its constructors' arguments over the declared types and all the
    member's parameters, each argument binding a variable for the ones after
    it. *)
Fixpoint rargs_refs (S : list ptab) (args : list (string * exp)) : list (ptab * string)%type :=
  match args with
  | nil => nil
  | (_, T) :: args' => exp_refs S T ++ rargs_refs (pt_none :: S) args'
  end.

Definition rmem_refs (nu nself : nat) (Mr : raw_member) : list (ptab * string)%type :=
  tele_refs (repeat pt_none nu) (rm_nparams Mr) ++
  exp_refs (repeat pt_none nu) (rm_sort Mr) ++
  flat_map (fun cg => rargs_refs (repeat pt_none (List.length (rm_nparams Mr) + nu + nself)) (snd cg)) (rm_cons Mr).

Definition decl_refs (R : raw_decl) : list (ptab * string)%type :=
  tele_refs nil (rd_uparams R) ++
  flat_map (rmem_refs (List.length (rd_uparams R)) (List.length (rd_members R))) (rd_members R).

(** The references of a function of a [mutual def] as written, under the
    block's parameters: its non-uniform parameters, its scrutinee's type,
    its result type and its clauses. *)
Definition rfun_refs (np : nat) (f : raw_fun) : list (ptab * string)%type :=
  tele_refs (repeat pt_none np) (rf_nparams f) ++
  exp_refs (repeat pt_none (List.length (rf_nparams f) + np)) (rf_scrut f) ++
  exp_refs (repeat pt_none (S (List.length (rf_nparams f) + np))) (rf_res f) ++
  flat_map (fun cl => exp_refs (repeat pt_none (snd (fst cl) + np)) (snd cl)) (rf_clauses f).

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
  | cc_ind _ D => decl_refs D
  | cc_mdef _ _ Δ fs => tele_refs nil Δ ++ flat_map (rfun_refs (List.length Δ)) fs
  | cc_builtin _ H => modexp_refs nil H
  | cc_ind_alias _ _ Δ H => tele_refs nil Δ ++ modexp_refs nil H
  end.

(** ** Accessibility *)

(** The module [qd] is an open frame, or an ancestor of one: a reference made
    here is made inside it. *)
#[warnings="-cannot-define-projection"]
Record open_anc (Ξ : gstack) (qd : qname) : Prop := mk_open_anc
  { oa_frame : qname
  ; oa_unit : gunit
  ; oa_suffix : list string
  ; oa_in : List.In (oa_frame, oa_unit) Ξ
  ; oa_same_unit : q_unit oa_frame = q_unit qd
  ; oa_chain : q_chain oa_frame = q_chain qd ++ oa_suffix }.

(** A reference to [x] in a module reached from a unit is to a public
    member, or made inside the module declaring it. *)
Definition glob_ok (Θ : gdeps) (Ξ : gstack) (H : modexp) (x : string) : Prop :=
  forall qd, mdecl Θ Ξ H x qd true -> open_anc Ξ qd.

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
  intros Hok qd Hd; apply Hok; eapply mdecl_dsub; eassumption.
Qed.
