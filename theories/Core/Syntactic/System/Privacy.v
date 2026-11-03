(** * Privacy

    Privacy is not a matter of typing: a public definition may unfold to a
    term naming a private one, and its type may name one, so typing and δ
    read no privacy flag.  It is a check on the terms a command introduces,
    as written: every member reference rooted at a unit is to a
    public member, or to a member of a module that is an open frame or an
    ancestor of one, that is, the reference is made inside the module
    declaring the member.  Aliases are followed through the global context to
    the module that declares the member.  A reference into a local body, read
    off the syntax by module tables ([privacy_table]), is to a public entry: inside
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
  destruct ip' as [| z ip''], E0 as [b pv A B | pm [Δ [? Φ' | E']] | pv ? D Φ' | pv Δa pa Nsa | pv Rr ΦR]; try discriminate; auto;
    exact (IH _ _ _ H).
Qed.

Lemma gc_entry_resolve : forall Θ Ξ p E, gc_resolve Θ Ξ p = Some E -> gc_entry Θ Ξ p = Some E.
Proof.
  intros * H; unfold gc_resolve, gc_resolve_u, gc_entry, gc_entry_u in *.
  destruct (gs_find Ξ p) as [[U ip] |]; [ apply gm_entry_resolve; exact H |].
  destruct (gds_lookup Θ (q_unit p)); [ apply gm_entry_resolve; exact H | discriminate ].
Qed.

Lemma gc_entry_deps_sub : forall Θ1 Θ2 Ξ p E, Θ1 ⊑ Θ2 -> gc_entry Θ1 Ξ p = Some E -> gc_entry Θ2 Ξ p = Some E.
Proof.
  intros * Hs H; unfold gc_entry, gc_entry_u in *.
  destruct (gs_find Ξ p) as [[U ip] |]; [ exact H |].
  destruct (gds_lookup Θ1 (q_unit p)) as [V |] eqn:E1; [| discriminate ].
  rewrite (Hs _ _ E1); exact H.
Qed.

(** A module of a unit read in a bigger set of dependencies. *)
Lemma gc_unit_deps_sub : forall Θ1 Θ2 Ξ H r, Θ1 ⊑ Θ2 -> gc_unit Θ1 Ξ H = Some r -> gc_unit Θ2 Ξ H = Some r.
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

(** The path of an open frame names no entry: its members are its own. *)
Lemma frame_gc_entry_none : forall Θ Ξ p U T, gs_find_tele Ξ p = Some (U, nil, T) -> gc_entry Θ Ξ p = None.
Proof. intros * Ht; unfold gc_entry, gc_entry_u; rewrite gs_find_tele_find, Ht; cbn; apply gm_entry_nil. Qed.

Lemma gc_frame_entry_none : forall Θ Ξ p TΦ, gc_frame Ξ p = Some TΦ -> gc_entry Θ Ξ p = None.
Proof.
  intros * Hf; unfold gc_frame in Hf.
  destruct (gs_find_tele Ξ p) as [[[U [| ? ?]] T] |] eqn:Ht; try (destruct U as [? [[|] ? | ?]]); try discriminate.
  exact (frame_gc_entry_none _ _ _ _ _ Ht).
Qed.

(** A module that is a loaded unit, an open frame, or the open frame of a
    member's or a record's module, is stored at its own path, and nowhere
    else. *)
Lemma msite_unit : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H pq, msite Θ Ξ H pq ->
    forall p, mod_qname H = Some p ->
    (exists TΦ, gc_unit Θ Ξ H = Some TΦ) \/ (exists r, gs_find_ind Ξ p = Some r) \/ (exists R, gs_find_record Ξ p = Some R) ->
    pq = p.
Proof.
  intros Θ Ξ Hg.
  (* below an open frame, a selection names no entry *)
  assert (Hmem : forall H z p1 pq E, mod_qname H = Some p1 -> msite Θ Ξ H pq ->
            (forall p, mod_qname H = Some p ->
               (exists TΦ, gc_unit Θ Ξ H = Some TΦ) \/ (exists r, gs_find_ind Ξ p = Some r) \/ (exists R, gs_find_record Ξ p = Some R) ->
               pq = p) ->
            gc_entry Θ Ξ (qname_in pq z) = Some E ->
            (exists TΦ, gc_unit Θ Ξ (me_mem H z) = Some TΦ) \/ (exists r, gs_find_ind Ξ (qname_in p1 z) = Some r) \/
            (exists R, gs_find_record Ξ (qname_in p1 z) = Some R) -> False).
  { intros * Hp1 Hs IH He Hu'.
    assert (Ht : exists U T, gs_find_tele Ξ (qname_in p1 z) = Some (U, nil, T)).
    { destruct Hu' as [([T Φ] & Hu) | [(r & Hk) | (R & Hk)]];
        [| exact (gs_find_ind_tele _ _ _ Hk) | exact (gs_find_record_tele _ _ _ Hk) ].
      destruct (gc_unit_cases _ _ _ _ _ Hu) as (mp & Hq & [Hf | (_ & Hc & _)]); cbn in Hq; rewrite Hp1 in Hq; injection Hq as <-.
      - change {| q_unit := q_unit p1; q_chain := q_chain p1 ++ z :: nil |} with (qname_in p1 z) in Hf.
        unfold gc_frame in Hf; destruct (gs_find_tele Ξ (qname_in p1 z)) as [[[U [| ? ?]] T0] |];
          try (destruct U as [? [[|] ? | ?]]); try discriminate; eauto.
      - cbn in Hc; destruct (q_chain p1); discriminate. }
    destruct Ht as (U & T & Ht).
    destruct (frame_parent _ _ Hg _ _ _ _ Ht) as (T1 & Φ1 & Hf1 & _).
    assert (Hq : pq = p1).
    { apply IH; [ exact Hp1 |].
      destruct (gs_find_ind Ξ p1) as [r |] eqn:Hk1; [ right; left; eauto |].
      destruct (gs_find_record Ξ p1) as [R |] eqn:Hr1; [ right; right; eauto | left ].
      exists (T1, Φ1); exact (gc_unit_frame _ _ _ _ _ _ Hp1 Hf1 Hk1 Hr1). }
    subst pq; rewrite (frame_gc_entry_none _ _ _ _ _ Ht) in He; discriminate. }
  induction 1 as [H p0 T0 Φ0 Hq Hu | H p0 r0 Hq Hk | H pq z E Hs IH He _ | H pq z E E' pq' Hs IH He _ _ _ | H N pq _ _
                 | H p0 R0 Hq Hk];
    intros p Hp Hu'.
  6: congruence.
  - congruence.
  - congruence.
  - exfalso; cbn in Hp; case_eq (mod_qname H); [ intros p1 Hp1 | intros Hn; rewrite Hn in Hp; discriminate ]; rewrite Hp1 in Hp; injection Hp as <-.
    change {| q_unit := q_unit p1; q_chain := q_chain p1 ++ z :: nil |} with (qname_in p1 z) in Hu'.
    exact (Hmem _ _ _ _ _ Hp1 Hs IH He Hu').
  - exfalso; cbn in Hp; case_eq (mod_qname H); [ intros p1 Hp1 | intros Hn; rewrite Hn in Hp; discriminate ]; rewrite Hp1 in Hp; injection Hp as <-.
    change {| q_unit := q_unit p1; q_chain := q_chain p1 ++ z :: nil |} with (qname_in p1 z) in Hu'.
    exact (Hmem _ _ _ _ _ Hp1 Hs IH He Hu').
  - discriminate.
Qed.

Lemma msite_functional : forall Θ Ξ, ⊢ᵍ Θ ⍮ Ξ -> forall H pq, msite Θ Ξ H pq -> forall pq', msite Θ Ξ H pq' -> pq = pq'.
Proof.
  intros Θ Ξ Hg; induction 1 as [H p T Φ Hq Hu | H p r Hq Hk | H pq z E Hs IH He Hb | H pq z E E' pq' Hs IH He Ha Hs' IH' | H N pq Hs IH
                               | H p R Hq Hk];
    intros pq0 H0.
  - symmetry; exact (msite_unit _ _ Hg _ _ H0 _ Hq ltac:(left; eauto)).
  - symmetry; exact (msite_unit _ _ Hg _ _ H0 _ Hq ltac:(right; left; eauto)).
  - inversion H0 as [? ? ? ? Hq0 Hu0 | ? ? ? Hq0 Hk0 | ? pq1 ? E1 Hs1 He1 Hb1 | ? pq1 ? E1 E1' ? Hs1 He1 Ha1 _ | | ? ? ? Hq0 Hk0]; subst.
    + exact (msite_unit _ _ Hg _ _ (ms_body _ _ _ _ _ _ Hs He Hb) _ Hq0 ltac:(left; eauto)).
    + exact (msite_unit _ _ Hg _ _ (ms_body _ _ _ _ _ _ Hs He Hb) _ Hq0 ltac:(right; left; eauto)).
    + rewrite (IH _ Hs1); reflexivity.
    + rewrite (IH _ Hs1), He1 in He; injection He as <-.
      destruct E1 as [| ? [? [? ?| ?]] | | | ]; cbn in Hb, Ha1; try contradiction; discriminate.
    + exact (msite_unit _ _ Hg _ _ (ms_body _ _ _ _ _ _ Hs He Hb) _ Hq0 ltac:(right; right; eauto)).
  - inversion H0 as [? ? ? ? Hq0 Hu0 | ? ? ? Hq0 Hk0 | ? pq1 ? E1 Hs1 He1 Hb1 | ? pq1 ? E1 E1' ? Hs1 He1 Ha1 Hs1' | | ? ? ? Hq0 Hk0]; subst.
    + exact (msite_unit _ _ Hg _ _ (ms_alias _ _ _ _ _ _ _ _ Hs He Ha Hs') _ Hq0 ltac:(left; eauto)).
    + exact (msite_unit _ _ Hg _ _ (ms_alias _ _ _ _ _ _ _ _ Hs He Ha Hs') _ Hq0 ltac:(right; left; eauto)).
    + rewrite (IH _ Hs1), He1 in He; injection He as <-.
      destruct E1 as [| ? [? [? ?| ?]] | | | ]; cbn in Hb1, Ha; try contradiction; discriminate.
    + rewrite (IH _ Hs1), He1 in He; injection He as <-; rewrite Ha1 in Ha; injection Ha as <-.
      exact (IH' _ Hs1').
    + exact (msite_unit _ _ Hg _ _ (ms_alias _ _ _ _ _ _ _ _ Hs He Ha Hs') _ Hq0 ltac:(right; right; eauto)).
  - inversion H0; subst; [ discriminate | discriminate | exact (IH _ ltac:(eassumption)) | discriminate ].
  - symmetry; exact (msite_unit _ _ Hg _ _ H0 _ Hq ltac:(right; right; eauto)).
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
Lemma msite_deps_sub : forall Θ1 Θ2 Ξ, Θ1 ⊑ Θ2 -> forall H pq, msite Θ1 Ξ H pq -> msite Θ2 Ξ H pq.
Proof.
  intros * Hs; induction 1; [ eapply ms_unit | eapply ms_ind_frame | eapply ms_body | eapply ms_alias | eapply ms_app
                            | eapply ms_record_frame ];
    eauto using gc_unit_deps_sub, gc_entry_deps_sub.
Qed.

Lemma mdecl_deps_sub : forall Θ1 Θ2 Ξ, Θ1 ⊑ Θ2 ->
    forall H y qd pv, mdecl Θ1 Ξ H y qd pv -> mdecl Θ2 Ξ H y qd pv.
Proof.
  intros * Hs * [pq E HH He]; constructor; [ eapply msite_deps_sub; eassumption | eapply gc_entry_deps_sub; eassumption ].
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
    table.  [privacy_table_body ch es] also records the chain [ch] of submodules
    selected from the local module it was read from, which the checker
    reports.  The tables are read off the syntax, in a scope [S] giving the
    table of each index: binders hold [privacy_table_none], a local module the table of
    its unit. *)
(** No induction principle: tables are only computed and read. *)
Unset Elimination Schemes.
Inductive privacy_table : Set :=
(** Nothing is known: a term variable, a parameter, a definition *)
| privacy_table_none : privacy_table
(** A chain from a unit, arguments dropped *)
| privacy_table_global : modexp -> privacy_table
(** The entries of a local body, newest first *)
| privacy_table_body : list string -> list (string * bool * privacy_table) -> privacy_table.
Set Elimination Schemes.

(** The newest entry [x] of a body's table. *)
Fixpoint privacy_table_find (x : string) (es : list (string * bool * privacy_table)) : option (bool * privacy_table) :=
  match es with
  | nil => None
  | (y, pv, t) :: es' => if String.eqb x y then Some (pv, t) else privacy_table_find x es'
  end.

(** The table of the submodule [y]. *)
Definition privacy_table_select (t : privacy_table) (y : string) : privacy_table :=
  match t with
  | privacy_table_none => privacy_table_none
  | privacy_table_global H => privacy_table_global (me_mem H y)
  | privacy_table_body ch es =>
      match privacy_table_find y es with
      | Some (_, privacy_table_body _ es') => privacy_table_body (ch ++ y :: nil) es'
      | Some (_, t') => t'
      | None => privacy_table_none
      end
  end.

(** The tables a body's entries bind, newest first, as a scope. *)
Definition privacy_table_scope (es : list (string * bool * privacy_table)) : list privacy_table := map snd es.

(** Whether an import item declares a private name. *)
Definition import_item_private (it : import_item) : bool := let '(_, _, pv) := it in pv.

(** What an import item names, in the table [t] of the imported module:
    the module itself, or its member. *)
Definition item_privacy_table (t : privacy_table) (it : import_item) : privacy_table :=
  match it with
  | (None, _, _) => t
  | (Some n, _, _) => privacy_table_select t n
  end.

(** The references an import's items make: each member it names. *)
Definition item_refs (t : privacy_table) (its : list import_item) : list (privacy_table * string)%type :=
  flat_map (fun it => match it with
                      | (Some n, _, _) => (t, n) :: nil
                      | (None, _, _) => nil
                      end) its.

(** Whether an entry of a body as written is private. *)
Definition uentry_private (E : uentry) : bool :=
  match E with
  | u_ge_def _ pv _ _ | u_ge_mod pv _ => pv
  end.

(** The privacy table of the module a module expression as written names,
    the tables of the module variables in scope being [S].  Privacy is
    checked on what the user writes, before the fill. *)
Fixpoint modexp_privacy_table (S : list privacy_table) (H : umodexp) : privacy_table :=
  match H with
  | u_me_unit fp => privacy_table_global (me_unit fp)
  | u_me_var k => nth k S privacy_table_none
  | u_me_mem H y => privacy_table_select (modexp_privacy_table S H) y
  | u_me_app H _ => modexp_privacy_table S H
  end.

Fixpoint gunit_privacy_table (S : list privacy_table) (U : uunit) : privacy_table :=
  match U with
  | u_gu_mk Δ D => moddef_privacy_table (repeat privacy_table_none (List.length Δ) ++ S) D
  end
with moddef_privacy_table (S : list privacy_table) (D : umoddef) : privacy_table :=
  match D with
  | u_md_body Φ => privacy_table_body nil (gmod_privacy_tables S Φ)
  | u_md_alias E => modexp_privacy_table S E
  end
with gmod_privacy_tables (S : list privacy_table) (Φ : ubody) : list (string * bool * privacy_table) :=
  match Φ with
  | u_gm_nil => nil
  | u_gm_ext Φ x E => let es := gmod_privacy_tables S Φ in (x, uentry_private E, gentry_privacy_table (privacy_table_scope es ++ S) E) :: es
  | u_gm_open Φ H its =>
      let es := gmod_privacy_tables S Φ in
      let t := modexp_privacy_table (privacy_table_scope es ++ S) H in
      rev (map (fun it => (import_item_name it, import_item_private it, item_privacy_table t it)) its) ++ es
  end
with gentry_privacy_table (S : list privacy_table) (E : uentry) : privacy_table :=
  match E with
  | u_ge_def _ _ _ _ => privacy_table_none
  | u_ge_mod _ U => gunit_privacy_table S U
  end.

(** The table a local binding gives its index. *)
Definition binding_privacy_table (S : list privacy_table) (b : ubinding) : privacy_table :=
  match b with
  | u_b_def _ _ => privacy_table_none
  | u_b_mod U => gunit_privacy_table S U
  end.

(** ** Member References *)

(** The references a name from a unit is written with, as a chain of
    selections: each member, from the chain before it. *)
Fixpoint chain_refs (H : modexp) (ch : list string) : list (privacy_table * string)%type :=
  match ch with
  | nil => nil
  | y :: ch' => (privacy_table_global H, y) :: chain_refs (me_mem H y) ch'
  end.

(** The member references a term is written with ([uexp], before the
    fill), each with the table of the module it selects from: every
    [u_mem H x] and every submodule [u_me_mem H y].  A member selected
    from a term ([u_proj_term]) is checked by the fill, once the term's
    record type is known ([Fill.sel_ok]). *)
Fixpoint exp_refs (S : list privacy_table) (M : uexp) : list (privacy_table * string)%type :=
  match M with
  | u_typ _ | u_level _ | u_llit _ | u_ntok | u_nlit _ | u_prop | u_True | u_tt | u_False | u_var _ | u_hole => nil
  | u_succl M | u_univ M | u_left M | u_right M => exp_refs S M
  | u_maxl M N | u_absurd M N => exp_refs S M ++ exp_refs S N
  | u_and A M => exp_refs S A ++ exp_refs (privacy_table_none :: S) M
  | u_conj P Q M N => exp_refs S P ++ exp_refs (privacy_table_none :: S) Q ++ exp_refs S M ++ exp_refs S N
  | u_elim _ Bks M =>
      (fix blks_refs (Bks : list ublock) : list (privacy_table * string)%type :=
         match Bks with
         | nil => nil
         | b :: Bks' => block_refs S b ++ blks_refs Bks'
         end) Bks ++ exp_refs S M
  | u_pi A M | u_fn A M => exp_refs S A ++ exp_refs (privacy_table_none :: S) M
  | u_app M N => exp_refs S M ++ exp_refs S N
  | u_let b B => binding_refs S b ++ exp_refs (binding_privacy_table S b :: S) B
  | u_mem H x => (modexp_privacy_table S H, x) :: modexp_refs S H
  (* the member of a term's record type: checked by the fill, once the
     record is known ([sel_ok]) *)
  | u_proj_term M _ => exp_refs S M
  | u_tuple T fs =>
      exp_refs S T ++
      (fix fields_refs (fs : list (string * uexp)) : list (privacy_table * string)%type :=
         match fs with
         | nil => nil
         | f :: fs' => exp_refs S (snd f) ++ fields_refs fs'
         end) fs
  end
with block_refs (S : list privacy_table) (b : ublock) : list (privacy_table * string)%type :=
  match b with
  | u_eb_mk nm Z A Bs =>
      exp_refs (repeat privacy_table_none (nm - 1) ++ S) Z ++
      exp_refs (repeat privacy_table_none nm ++ S) A ++
      (fix brs_refs (Bs : list (string * nat * uexp)) : list (privacy_table * string)%type :=
         match Bs with
         | nil => nil
         | b :: Bs' => exp_refs (repeat privacy_table_none (snd (fst b)) ++ S) (snd b) ++ brs_refs Bs'
         end) Bs
  end
with modexp_refs (S : list privacy_table) (H : umodexp) : list (privacy_table * string)%type :=
  match H with
  | u_me_unit _ | u_me_var _ => nil
  | u_me_mem H y => (modexp_privacy_table S H, y) :: modexp_refs S H
  | u_me_app H N => modexp_refs S H ++ exp_refs S N
  end
with binding_refs (S : list privacy_table) (b : ubinding) : list (privacy_table * string)%type :=
  match b with
  | u_b_def A M => exp_refs S A ++ exp_refs S M
  | u_b_mod U => gunit_refs S U
  end
with gunit_refs (S : list privacy_table) (U : uunit) : list (privacy_table * string)%type :=
  match U with
  | u_gu_mk Δ D =>
      (fix tele_refs (Δ : list uexp) : list (privacy_table * string)%type :=
         match Δ with
         | nil => nil
         | A :: Δ' => exp_refs (repeat privacy_table_none (List.length Δ') ++ S) A ++ tele_refs Δ'
         end) Δ ++ moddef_refs (repeat privacy_table_none (List.length Δ) ++ S) D
  end
with moddef_refs (S : list privacy_table) (D : umoddef) : list (privacy_table * string)%type :=
  match D with
  | u_md_body Φ => gmod_refs S Φ
  | u_md_alias E => modexp_refs S E
  end
with gmod_refs (S : list privacy_table) (Φ : ubody) : list (privacy_table * string)%type :=
  match Φ with
  | u_gm_nil => nil
  | u_gm_ext Φ _ E => gmod_refs S Φ ++ gentry_refs (privacy_table_scope (gmod_privacy_tables S Φ) ++ S) E
  | u_gm_open Φ H its =>
      gmod_refs S Φ ++ modexp_refs (privacy_table_scope (gmod_privacy_tables S Φ) ++ S) H ++
        item_refs (modexp_privacy_table (privacy_table_scope (gmod_privacy_tables S Φ) ++ S) H) its
  end
with gentry_refs (S : list privacy_table) (E : uentry) : list (privacy_table * string)%type :=
  match E with
  | u_ge_def _ _ A B => exp_refs S A ++ match B with Some M => exp_refs S M | None => nil end
  | u_ge_mod _ U => gunit_refs S U
  end.

(** The references of a telescope of assumptions as written, innermost
    first, each over the ones after it. *)
Fixpoint tele_refs (S : list privacy_table) (Δ : list uexp) : list (privacy_table * string)%type :=
  match Δ with
  | nil => nil
  | A :: Δ' => exp_refs (repeat privacy_table_none (List.length Δ') ++ S) A ++ tele_refs S Δ'
  end.

(** The references of a group as written: its uniform parameters, and of
    each member its non-uniform parameters and sort over the uniform ones,
    and its constructors' arguments over the declared types and all the
    member's parameters, each argument binding a variable for the ones after
    it. *)
Fixpoint raw_args_refs (S : list privacy_table) (args : list (string * uexp)) : list (privacy_table * string)%type :=
  match args with
  | nil => nil
  | (_, T) :: args' => exp_refs S T ++ raw_args_refs (privacy_table_none :: S) args'
  end.

(** The references a declared member makes as written: its non-uniform
    parameters, its sort and its constructors' arguments, under the [nu]
    uniform parameters and the [nself] [Self]s. *)
Definition rmem_refs (nu nself : nat) (Mr : uraw_member) : list (privacy_table * string)%type :=
  tele_refs (repeat privacy_table_none nu) (uraw_member_nparams Mr) ++
  exp_refs (repeat privacy_table_none nu) (uraw_member_sort Mr) ++
  flat_map (fun cg => raw_args_refs (repeat privacy_table_none (List.length (uraw_member_nparams Mr) + nu + nself)) (snd cg)) (uraw_member_cons Mr).

(** The references a group declaration makes as written: its uniform
    parameters, then each member's. *)
Definition decl_refs (R : uraw_decl) : list (privacy_table * string)%type :=
  tele_refs nil (uraw_decl_uparams R) ++
  flat_map (rmem_refs (List.length (uraw_decl_uparams R)) (List.length (uraw_decl_members R))) (uraw_decl_members R).

(** The references of a function of a [mutual def] as written, under the
    block's parameters: its non-uniform parameters, its scrutinee's type,
    its result type and its clauses. *)
Definition raw_fun_refs (np : nat) (f : uraw_fun) : list (privacy_table * string)%type :=
  tele_refs (repeat privacy_table_none np) (uraw_fun_nparams f) ++
  exp_refs (repeat privacy_table_none (List.length (uraw_fun_nparams f) + np)) (uraw_fun_scrut f) ++
  exp_refs (repeat privacy_table_none (S (List.length (uraw_fun_nparams f) + np))) (uraw_fun_res f) ++
  flat_map (fun cl => exp_refs (repeat privacy_table_none (snd (fst cl) + np)) (snd cl)) (uraw_fun_clauses f).

(** The references a command makes, as written: its own terms, and for an
    import, its target and each member its items name.  A module's and a
    record's nested commands are checked when they run.  A core command,
    filled or generated, is not written, and is not checked. *)
Definition cmd_refs (c : ucmd) : list (privacy_table * string)%type :=
  match c with
  | u_cmd_def _ _ _ A oM => exp_refs nil A ++ match oM with Some M => exp_refs nil M | None => nil end
  | u_cmd_mod _ _ Δ _ => tele_refs nil Δ
  | u_cmd_alias _ _ Δ E => tele_refs nil Δ ++ modexp_refs nil E
  | u_cmd_load _ => nil
  | u_cmd_open E its => modexp_refs nil E ++ item_refs (modexp_privacy_table nil E) its
  | u_cmd_eval M A => exp_refs nil M ++ exp_refs nil A
  | u_cmd_inductive _ D => decl_refs D
  | u_cmd_mdef _ _ Δ fs => tele_refs nil Δ ++ flat_map (raw_fun_refs (List.length Δ)) fs
  | u_cmd_builtin _ H => modexp_refs nil H
  | u_cmd_inductive_alias _ _ Δ H => tele_refs nil Δ ++ modexp_refs nil H
  | u_cmd_record_alias _ _ Δ H => tele_refs nil Δ ++ modexp_refs nil H
  (** A record's parameters, sort and fields, each field binding a variable
      for the ones after it; its with-area is checked when it runs *)
  | u_cmd_record _ _ Δ Srt fs _ =>
      tele_refs nil Δ ++ exp_refs (repeat privacy_table_none (List.length Δ)) Srt ++ raw_args_refs (repeat privacy_table_none (List.length Δ)) fs
  end.

(** ** Accessibility *)

(** The module [qd] is an open frame, or an ancestor of one: a reference made
    here is made inside it. *)
#[warnings="-cannot-define-projection"]
Record open_ancestor (Ξ : gstack) (qd : qname) : Prop := mk_open_ancestor
  { (** The path of the open frame *)
    open_ancestor_frame : qname
    (** The frame's kind *)
  ; open_ancestor_kind : frame_kind
    (** The frame's body so far *)
  ; open_ancestor_unit : gunit
    (** The frame's path below [qd] *)
  ; open_ancestor_suffix : list string
    (** The frame is on the stack *)
  ; open_ancestor_in : List.In (open_ancestor_frame, open_ancestor_kind, open_ancestor_unit) Ξ
    (** It is in the unit of [qd] *)
  ; open_ancestor_same_unit : q_unit open_ancestor_frame = q_unit qd
    (** It is [qd] or below it *)
  ; open_ancestor_chain : q_chain open_ancestor_frame = q_chain qd ++ open_ancestor_suffix }.

(** A reference to [x] in a module reached from a unit is to a public
    member, or made inside the module declaring it. *)
Definition glob_ok (Θ : gdeps) (Ξ : gstack) (H : modexp) (x : string) : Prop :=
  forall qd, mdecl Θ Ξ H x qd true -> open_ancestor Ξ qd.

(** A reference into a local body is to a public entry: inside the body,
    its entries are variables, not references. *)
Definition ref_ok (Θ : gdeps) (Ξ : gstack) (r : (privacy_table * string)%type) : Prop :=
  match fst r with
  | privacy_table_global H => glob_ok Θ Ξ H (snd r)
  | privacy_table_body _ es => option_map fst (privacy_table_find (snd r) es) <> Some true
  | privacy_table_none => True
  end.

Definition acc_ok (Θ : gdeps) (Ξ : gstack) (l : list (privacy_table * string)%type) : Prop :=
  List.Forall (ref_ok Θ Ξ) l.

(** Accessibility reads declarations, which equal lookups preserve. *)
Lemma acc_ok_deps_sub : forall Θ1 Θ2 Ξ, Θ2 ⊑ Θ1 ->
    forall l, acc_ok Θ1 Ξ l -> acc_ok Θ2 Ξ l.
Proof.
  intros * Hs l Hl; eapply List.Forall_impl; [| exact Hl ].
  intros [[| H |] x]; unfold ref_ok, glob_ok; cbn [fst snd]; auto.
  intros Hok qd Hd; apply Hok; eapply mdecl_deps_sub; eassumption.
Qed.
