(** * Deciding the Flag Premise

    [levels_abstractable Θ Ξ G Δ E]: every parameter of [Δ] is a type of
    levels, or what [E] denotes has no member of a type of levels
    ([⊢ⁿˡ]).  The second is decided by reading the description as [⊢ⁿˡ]
    does ([nl_desc_dec]), by recursion on the domain [nl_reach], which every
    description a well-formed module expression denotes has when it reads
    no open frame ([nl_reach_of_desc_ok]); one that reads an open frame has
    a member of no filed body, so the premise fails ([no_level_reads_frame]).
    The descriptions are fast, read through the fast context [F]: the
    entries of a filed body are found in its trie. *)

From Stdlib Require Import Lia List PeanoNat String.
From Equations Require Import Equations.
Import ListNotations.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
From Mctt.Core.Syntactic.System.Global Require Import Paths MemberLemmas DescTyping Presup LookupSound NoLevelReach.
From Mctt.Extraction Require Import Lookup FastDesc MemberType TypeCheckBase.
Import Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** Parameters of Types of Levels *)

(** Whether every assumption of a telescope is a type of levels, as a
    boolean *)
Fixpoint level_sorted_parameters_b (Δ : ctx) : bool :=
  match Δ with
  | nil => true
  | ce_ass κ _ :: Δ' => (if abs_kind_eq_dec κ ak_level then true else false) && level_sorted_parameters_b Δ'
  | _ :: Δ' => level_sorted_parameters_b Δ'
  end.

Lemma level_sorted_parameters_b_spec : forall Δ, level_sorted_parameters_b Δ = true <-> level_sorted_parameters Δ.
Proof.
  induction Δ as [| e Δ IH].
  - split; [ intros _ Δ1 κ T Δ2 E; destruct Δ1; discriminate | reflexivity ].
  - assert (Htl : level_sorted_parameters (e :: Δ) -> level_sorted_parameters Δ)
      by (intros H Δ1 κ T Δ2 E; apply (H (e :: Δ1) κ T Δ2); rewrite E; reflexivity).
    destruct e as [κ0 T0 | T0 M0 | U0 | T0 M0 U0]; cbn [level_sorted_parameters_b].
    + split.
      * intros Hb Δ1 κ T Δ2 E; apply andb_prop in Hb as [Hk Hb].
        destruct Δ1 as [| e1 Δ1]; cbn in E; injection E as E1 E2.
        -- subst; destruct (abs_kind_eq_dec κ ak_level); [ assumption | discriminate ].
        -- subst; exact (proj1 IH Hb _ _ _ _ eq_refl).
      * intros H; apply andb_true_intro; split; [| apply IH, Htl, H ].
        destruct (abs_kind_eq_dec κ0 ak_level) as [| Hn]; [ reflexivity | exfalso; apply Hn, (H nil κ0 T0 Δ); reflexivity ].
    + split; [ intros Hb Δ1 κ T Δ2 E; destruct Δ1 as [| e1 Δ1]; cbn in E; injection E as E1 E2; [ discriminate | subst; exact (proj1 IH Hb _ _ _ _ eq_refl) ]
             | intros H; apply IH, Htl, H ].
    + split; [ intros Hb Δ1 κ T Δ2 E; destruct Δ1 as [| e1 Δ1]; cbn in E; injection E as E1 E2; [ discriminate | subst; exact (proj1 IH Hb _ _ _ _ eq_refl) ]
             | intros H; apply IH, Htl, H ].
    + split; [ intros Hb Δ1 κ T Δ2 E; destruct Δ1 as [| e1 Δ1]; cbn in E; injection E as E1 E2; [ discriminate | subst; exact (proj1 IH Hb _ _ _ _ eq_refl) ]
             | intros H; apply IH, Htl, H ].
Qed.

Definition level_sorted_parameters_dec (Δ : ctx) : { level_sorted_parameters Δ } + { ~ level_sorted_parameters Δ } :=
  match level_sorted_parameters_b Δ as b return level_sorted_parameters_b Δ = b -> _ with
  | true => fun E => left (proj1 (level_sorted_parameters_b_spec Δ) E)
  | false => fun E => right (fun H => Bool.diff_false_true (eq_trans (eq_sym E) (proj2 (level_sorted_parameters_b_spec Δ) H)))
  end eq_refl.

(** ** Names *)

(** Every name of a list, decided name by name *)
Definition names_forall_dec (P : string -> Prop) (d : forall y, { P y } + { ~ P y }) (L : list string) :
    { forall y, In y L -> P y } + { exists y, In y L /\ ~ P y }.
Proof.
  induction L as [| x L IH].
  - left; intros y [].
  - destruct (d x) as [Hx | Hn]; [| right; exists x; split; [ left; reflexivity | exact Hn ] ].
    destruct IH as [HL | HL]; [ left | right ].
    + intros y [<- | Hy]; [ exact Hx | exact (HL _ Hy) ].
    + destruct HL as (y & Hy & Hn); exists y; split; [ right; exact Hy | exact Hn ].
Defined.

(** A description for every name of a list, from one for each *)
Lemma names_choice : forall (P : string -> mdesc -> Prop) (L : list string),
    (forall y, In y L -> exists R, P y R) -> exists f : string -> mdesc, forall y, In y L -> P y (f y).
Proof.
  intros P; induction L as [| x L IH]; intros H.
  - exists (fun _ => mdesc_term ak_relevant a_prop None); intros y [].
  - destruct (H x (or_introl eq_refl)) as (Rx & Hx).
    destruct (IH (fun y Hy => H y (or_intror Hy))) as (f & Hf).
    exists (fun y => if String.eqb y x then Rx else f y); intros y Hy.
    destruct (String.eqb_spec y x) as [-> | Hne]; [ exact Hx |].
    destruct Hy as [-> | Hy]; [ contradiction | exact (Hf _ Hy) ].
Qed.

(** A name an entry is found at is a name of the body. *)
Lemma gm_prefix_upto_in : forall Φ y Φ1, gm_prefix_upto Φ y = Some Φ1 -> In y (gm_names Φ).
Proof.
  induction Φ as [| Φ IH x E | Φ IH ? ? ?]; intros * Hp; cbn in Hp |- *; [ discriminate | |].
  - destruct (String.eqb_spec y x) as [-> | Hne]; [ left; reflexivity | right; exact (IH _ _ Hp) ].
  - destruct (existsb _ _); [ discriminate |]; apply in_or_app; right; exact (IH _ _ Hp).
Qed.

(** The entry found at a name is at that name. *)
Lemma gm_prefix_upto_name : forall Φ y Φ0 x E, gm_prefix_upto Φ y = Some (gm_ext Φ0 x E) -> x = y.
Proof. intros * Hp; destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & [= _ -> _] & _); reflexivity. Qed.

(** What is found at a name is an entry. *)
Lemma gm_prefix_upto_shape : forall Φ y Φ1, gm_prefix_upto Φ y = Some Φ1 -> exists Φ0 E, Φ1 = gm_ext Φ0 y E.
Proof. intros * Hp; destruct (gm_prefix_entry _ _ _ Hp) as (Φ0 & E & -> & _); eauto. Qed.

(** ** The Reads of an Open Body and of a Filed Body *)

Section Reads.
  Variables (Θ : gdeps) (Ξ : gstack).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** What [⊢ⁿˡ] asks of the entry an open body has at a name: a
      definition is of no type of levels, and a module entry's unit denotes
      a description with no member of a type of levels *)
  Definition open_name_ok (Γ Δ : ctx) (Φx : gmod) (y : string) : Prop :=
    forall Φ0 E, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) ->
      (forall A M, entry_tm E = Some (A, M) -> entry_kind E <> ak_level) /\
      (forall U, entry_unit E = Some U ->
         exists R, udenote Θ Ξ (body_ctx Φ0 ++ Δ ++ Γ) None U R /\ Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ Δ ++ Γ ⊢ⁿˡ R).

  (** An open body is so when every entry is. *)
  Lemma no_level_open_names : forall Γ Δ Φw Φx, desc_ok Θ Ξ Γ (mdesc_open Δ Φw Φx) ->
      (forall y, In y (gm_names Φx) -> open_name_ok Γ Δ Φx y) <-> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_open Δ Φw Φx.
  Proof.
    intros * Hok; split.
    - intros H.
      inversion Hok as [| ? ? ? ? lΔ HΦ Hn | |]; subst.
      destruct (names_choice (fun y R => forall Φ0 E U, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
                                 udenote Θ Ξ (body_ctx Φ0 ++ Δ ++ Γ) None U R /\ Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ Δ ++ Γ ⊢ⁿˡ R) (gm_names Φx))
        as (f & Hf).
      { intros y Hy.
        destruct (gm_prefix_upto Φx y) as [Φ1 |] eqn:Hp;
          [| exists (mdesc_term ak_relevant a_prop None); intros * Hp'; try rewrite Hp in Hp'; discriminate ].
        destruct (gm_prefix_upto_shape _ _ _ Hp) as (Φ0 & E & ->).
        destruct (entry_unit E) as [U |] eqn:HU; [| exists (mdesc_term ak_relevant a_prop None); intros * Hp' HU'; try rewrite Hp in Hp'; injection Hp' as <- <-; congruence ].
        destruct (proj2 (H y Hy _ _ Hp) _ HU) as (R & HR & HnR).
        exists R; intros * Hp' HU'; try rewrite Hp in Hp'; injection Hp' as <- <-; rewrite HU in HU'; injection HU' as <-; split; assumption. }
      eapply wf_no_level_open with (member_descs := f);
        [ exact Hn | apply ext_of_ctx'; rewrite <- List.app_assoc; exact HΦ
        | intros * Hp HE; exact (proj1 (H _ (gm_prefix_upto_in _ _ _ Hp) _ _ Hp) _ _ HE)
        | intros * Hp HE; exact (proj1 (Hf _ (gm_prefix_upto_in _ _ _ Hp) _ _ _ Hp HE))
        | intros * Hp HE; exact (proj2 (Hf _ (gm_prefix_upto_in _ _ _ Hp) _ _ _ Hp HE)) ].
    - intros Hn y _ Φ0 E Hp; inversion Hn; subst.
      split; [ intros * HE; eauto |].
      intros U HU; eexists; split; eauto.
  Qed.

  (** The unit of an entry of a typed open body denotes in a typed way, so
      what it denotes is found. *)
  Lemma open_entry_order : forall Γ Δ Φw Φx y Φ0 E U, desc_ok Θ Ξ Γ (mdesc_open Δ Φw Φx) ->
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
      udenote_order Θ Ξ (body_ctx Φ0 ++ Δ ++ Γ) U.
  Proof.
    intros * Hok Hp HE; inversion Hok as [| ? ? ? ? lΔ HΦ Hn | |]; subst.
    destruct (gm_prefix_body_ctx _ _ _ Hn Hp) as (Ψ & HΨ).
    rewrite HΨ, <- List.app_assoc in HΦ.
    destruct (body_ext_unit_wf _ _ _ _ _ _ _ (ctx_app_wf_tail _ _ _ _ HΦ) HE) as [_ HU].
    destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 denote_exists)))))) _ _ _ _ _ HU) as (_ & [R HR] & _).
    exact (proj1 (proj2 (order_of_denote _ _ Hg)) _ _ _ _ HR).
  Qed.

  Lemma open_entry_desc_ok : forall Γ Δ Φw Φx y Φ0 E U R, desc_ok Θ Ξ Γ (mdesc_open Δ Φw Φx) ->
      gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
      udenote Θ Ξ (body_ctx Φ0 ++ Δ ++ Γ) None U R -> desc_ok Θ Ξ (body_ctx Φ0 ++ Δ ++ Γ) R.
  Proof. intros * Hok Hp HE Hu; inversion Hok as [| ? ? ? ? lΔ HΦ Hn Hent | |]; subst; exact (Hent _ _ _ _ Hp HE _ Hu). Qed.

  (** What [⊢ⁿˡ] asks of the entry a filed body has at a name *)
  Definition closed_name_ok (p : qname) (T : ctx) (Φ : gmod) (y : string) : Prop :=
    forall Φ0 E, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) ->
      (forall b pv r A oM, E = ge_def b pv r A oM -> r <> ak_level) /\
      ((forall b pv r A oM, E <> ge_def b pv r A oM) ->
         exists R, edenote Θ Ξ ⋅ (Some (qname_in p y)) (ge_read T E) R /\ Θ ⍮ Ξ ⍮ ⋅ ⊢ⁿˡ R).

  Lemma no_level_closed_names : forall Γ Θ' p T Φ Ns, gc_body Θ Ξ p = Some (T, Φ) ->
      (forall y, In y (gm_names Φ) -> closed_name_ok p T Φ y) <-> Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_closed Θ' p T Φ Ns.
  Proof.
    intros * Hb; split.
    - intros H.
      destruct (names_choice (fun y R => forall Φ0 E, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> (forall b pv r A oM, E <> ge_def b pv r A oM) ->
                                 edenote Θ Ξ ⋅ (Some (qname_in p y)) (ge_read T E) R /\ Θ ⍮ Ξ ⍮ ⋅ ⊢ⁿˡ R) (gm_names Φ))
        as (f & Hf).
      { intros y Hy.
        destruct (gm_prefix_upto Φ y) as [Φ1 |] eqn:Hp;
          [| exists (mdesc_term ak_relevant a_prop None); intros * Hp'; try rewrite Hp in Hp'; discriminate ].
        destruct (gm_prefix_upto_shape _ _ _ Hp) as (Φ0 & E & ->).
        destruct E as [b pv r A oM | | | |];
          try (destruct (proj2 (H y Hy _ _ Hp) ltac:(intros ? ? ? ? ? [=])) as (R & HR & HnR);
               exists R; intros * Hp' _; try rewrite Hp in Hp'; injection Hp' as <- <-; split; assumption).
        exists (mdesc_term ak_relevant a_prop None); intros * Hp' Hnd; try rewrite Hp in Hp'; injection Hp' as <- <-.
        exfalso; exact (Hnd _ _ _ _ _ eq_refl). }
      eapply wf_no_level_closed with (member_descs := f);
        [ exact Hg | exact Hb
        | intros * Hp; exact (proj1 (H _ (gm_prefix_upto_in _ _ _ Hp) _ _ Hp) _ _ _ _ _ eq_refl)
        | intros * Hp HE; exact (proj1 (Hf _ (gm_prefix_upto_in _ _ _ Hp) _ _ Hp HE))
        | intros * Hp HE; exact (proj2 (Hf _ (gm_prefix_upto_in _ _ _ Hp) _ _ Hp HE)) ].
    - intros Hn y _ Φ0 E Hp; inversion Hn; subst.
      split; [ intros * ->; eauto |].
      intros Hnd; eexists; split; eauto.
  Qed.

  (** A typed filed body, read at its root *)
  Lemma desc_ok_closed_root : forall Γ Θ' p T Φ Ns, desc_ok Θ Ξ Γ (mdesc_closed Θ' p T Φ Ns) ->
      desc_ok Θ Ξ ⋅ (mdesc_closed nil p T Φ nil).
  Proof.
    intros * Hok; inversion Hok as [| | ? ? ? ? ? Θ0 Ξ0 ? lΘ Hg0 Hsub Hloc HaT HsT HT HΘ' Hargs |]; subst.
    assert (Hnil : ⊢ Θ ⍮ Ξ ⍮ ⋅) by (constructor; exact Hg).
    eapply desc_ok_closed with (param_level := 0);
      [ exact Hg0 | exact Hsub | exact Hloc | exact HaT | exact HsT | exact HT | exact Hnil
      | apply args_ok_nil; exact Hnil | constructor | apply params_evaluated_nil | apply desc_levels_abstractable_nil
      | let Hne := fresh "Hne" in intros Hne; contradiction (Hne eq_refl) ].
  Qed.

  (** What an entry of a typed filed body denotes, read at [⋅], is typed. *)
  Lemma closed_entry_desc_ok : forall p T Φ y Γy E rd R, desc_ok Θ Ξ ⋅ (mdesc_closed nil p T Φ nil) ->
      mdesc_entry (mdesc_closed nil p T Φ nil) y = Some (Γy, E, rd) ->
      edenote Θ Ξ (Γy ++ ⋅) (Some (qname_in p y)) E R -> desc_ok Θ Ξ ⋅ R.
  Proof.
    intros * Hok He Hed.
    assert (Hr : mdesc_read rd R = Some (mdesc_up nil (mdesc_named nil nil (apps (a_mem (qname_mod p) y) nil) R))).
    { cbn in He; destruct (gm_prefix_upto Φ y) as [[| ? ? ? | ? ? ? ?] |]; try discriminate.
      injection He as <- <- <-; cbn [mdesc_read]; rewrite mdesc_ats_read_nil; reflexivity. }
    destruct (desc_ok_entry_closed_read _ _ Hg (gctx_valid_syn _ _ Hg) _ _ _ _ _ _ _ _ _ _ _ _ Hok He Hed Hr)
      as (R0 & [_ HR0 HokR _ _]).
    rewrite mdesc_ats_read_nil in HR0; injection HR0 as <-.
    rewrite mdesc_named_nil in HokR; exact HokR.
  Qed.

  Corollary closed_child_desc_ok : forall p T Φ y Φ0 E R, desc_ok Θ Ξ ⋅ (mdesc_closed nil p T Φ nil) ->
      gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) ->
      edenote Θ Ξ ⋅ (Some (qname_in p y)) (ge_read T E) R -> desc_ok Θ Ξ ⋅ R.
  Proof.
    intros * Hok Hp Hed.
    assert (He : mdesc_entry (mdesc_closed nil p T Φ nil) y = Some (nil, ge_read T E, reader_closed nil nil (apps (a_mem (qname_mod p) y) nil)))
      by (cbn; rewrite Hp; reflexivity).
    exact (closed_entry_desc_ok _ _ _ _ _ _ _ _ Hok He Hed).
  Qed.
End Reads.

(** ** Reading a Frame Is Reading No Filed Body *)

Lemma no_level_reads_frame : forall Θ Ξ Γ R, desc_reads_frame Ξ R -> ~ Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ R.
Proof.
  intros * (Θ' & p & T & Φ & Ns & Hm & Hf) Hn.
  pose proof (no_level_mod _ _ _ _ _ Hn Hm) as Hc; inversion Hc; subst.
  match goal with Hb : gc_body _ _ p = Some _ |- _ => exact (Hf (gc_body_not_frame _ _ _ _ Hb)) end.
Qed.

(** ** The Entries of a Filed Body, Fast *)

(** The names of a trie's body are among the trie's names. *)
Lemma decode_mod_names : forall t y, In y (gm_names (decode_mod t)) -> In y (ft_names t).
Proof.
  intros [m xs] y; cbn [decode_mod ft_names].
  generalize (((fix decode_tree (m : SRaw.tree fentry) : SRaw.tree gentry :=
                 match m with
                 | SRaw.Leaf _ => SRaw.Leaf _
                 | SRaw.Node l k e r h => SRaw.Node (decode_tree l) k (decode_entry e) (decode_tree r) h
                 end) m)) as dm.
  induction xs as [| x xs IH]; intros dm Hy; cbn in Hy; [ contradiction |].
  destruct (SRaw.find x dm); [ destruct Hy as [-> | Hy]; [ left; reflexivity | right; exact (IH _ Hy) ] | right; exact (IH _ Hy) ].
Qed.

(** What a filed body read at its root has at a name. *)
Lemma closed_entry_found : forall p T Φ y Γy E' rd, mdesc_entry (mdesc_closed nil p T Φ nil) y = Some (Γy, E', rd) ->
    exists Φ0 E, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) /\ Γy = nil /\ E' = ge_read T E.
Proof.
  intros * He; cbn in He; destruct (gm_prefix_upto Φ y) as [[| Φ0 x E | ? ? ? ?] |] eqn:Hp; try discriminate.
  injection He as <- <- _; pose proof (gm_prefix_upto_name _ _ _ _ _ Hp) as ->.
  exists Φ0, E; split; [ reflexivity | split; reflexivity ].
Qed.

Lemma closed_entry_none : forall p T Φ y, mdesc_entry (mdesc_closed nil p T Φ nil) y = None ->
    forall Φ0 E, gm_prefix_upto Φ y <> Some (gm_ext Φ0 y E).
Proof. intros * He Φ0 E Hp; cbn in He; rewrite Hp in He; discriminate. Qed.

(** Reading a stored entry keeps its definitions. *)
Lemma ge_read_def : forall T E b pv r A oM, ge_read T E = ge_def b pv r A oM <-> E = ge_def b pv r A oM.
Proof. intros T [| ? [? [[] ?| ?]] | | |] *; cbn; split; intros H; congruence. Qed.

(** The kind of a definition an entry source is, without decoding *)
Definition source_def_kind (s : entry_source) : option abs_kind :=
  match s with
  | entry_source_core (ge_def _ _ r _ _) => Some r
  | entry_source_fast _ (fe_def _ _ r _ _ _) _ => Some r
  | _ => None
  end.

Lemma source_def_kind_some : forall s r, source_def_kind s = Some r -> exists b pv A oM, decode_entry_source s = ge_def b pv r A oM.
Proof. intros s r0 H; destruct s as [[| | | |] | ? [| | | |] ?]; cbn in H; try discriminate; injection H as <-; cbn; eauto. Qed.

Lemma source_def_kind_none : forall s, source_def_kind s = None -> forall b pv r A oM, decode_entry_source s <> ge_def b pv r A oM.
Proof. intros [[| | | |] | ? [| | | |] ?] H; cbn in H; try discriminate; cbn; intros * [=]. Qed.

(** ** The Domain, Inverted

    Transparent, so that a decision by recursion on the domain sees the
    reads they give as parts of it. *)

Definition no_level_reachable_open_inv {Θ Ξ G R1} (H : no_level_reachable Θ Ξ G R1) :
    forall Δ Φw Φx, R1 = mdesc_open Δ Φw Φx ->
    forall y Φ0 E U Ry, gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
      udenote Θ Ξ (body_ctx Φ0 ++ Δ ++ G) None U Ry -> no_level_reachable Θ Ξ (body_ctx Φ0 ++ Δ ++ G) Ry.
Proof. destruct H; intros ? ? ? e; try discriminate e; injection e as -> -> ->; assumption. Defined.

Lemma no_level_reachable_closed_body {Θ Ξ G R1} (H : no_level_reachable Θ Ξ G R1) :
    forall Θ' p T Φ Ns, R1 = mdesc_closed Θ' p T Φ Ns -> gc_body Θ Ξ p = Some (T, Φ).
Proof. destruct H; intros ? ? ? ? ? e; try discriminate e; injection e as -> -> -> -> ->; assumption. Qed.

Definition no_level_reachable_closed_inv {Θ Ξ G R1} (H : no_level_reachable Θ Ξ G R1) :
    forall Θ' p T Φ Ns, R1 = mdesc_closed Θ' p T Φ Ns ->
    forall y Φ0 E Ry, gm_prefix_upto Φ y = Some (gm_ext Φ0 y E) -> (forall b pv r A oM, E <> ge_def b pv r A oM) ->
      edenote Θ Ξ ⋅ (Some (qname_in p y)) (ge_read T E) Ry -> no_level_reachable Θ Ξ ⋅ Ry.
Proof. destruct H; intros ? ? ? ? ? e; try discriminate e; injection e as -> -> -> -> ->; assumption. Defined.

Definition no_level_reachable_dm_inv {Θ Ξ G R1} (H : no_level_reachable Θ Ξ G R1) :
    forall Θd A M Rm, R1 = mdesc_dm Θd A M Rm -> forall Rm', mdesc_mod Rm = Some Rm' -> no_level_reachable Θ Ξ G Rm'.
Proof. destruct H; intros ? ? ? ? e; try discriminate e; injection e as -> -> -> ->; assumption. Defined.

(** ** The Decision *)

Section Decide.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  Definition no_level_term_dec Γ r A om : { Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_term r A om } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_term r A om }.
  Proof.
    destruct (abs_kind_eq_dec r ak_level) as [-> | Hn];
      [ right; intros H; inversion H; congruence | left; constructor; exact Hn ].
  Defined.

  (** An open body's entry at a name, the description of its unit decided
      by [rec] *)
  Definition open_name_dec Γ Δ Φw Φx (Hok : desc_ok Θ Ξ Γ (mdesc_open Δ Φw Φx))
      (rec : forall y Φ0 E U (Ry : fmdesc), gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
               udenote Θ Ξ (body_ctx Φ0 ++ Δ ++ Γ) None U (decode_desc Ry) ->
               { Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ Δ ++ Γ ⊢ⁿˡ decode_desc Ry } + { ~ Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ Δ ++ Γ ⊢ⁿˡ decode_desc Ry })
      (y : string) : { open_name_ok Θ Ξ Γ Δ Φx y } + { ~ open_name_ok Θ Ξ Γ Δ Φx y }.
  Proof.
    unfold open_name_ok.
    destruct (gm_prefix_upto Φx y) as [[| Φ0 x E | Φ0 H its Φg] |] eqn:Hp.
    1,3: exfalso; destruct (gm_prefix_upto_shape _ _ _ Hp) as (? & ? & [=]).
    2: left; intros ? ? [=].
    pose proof (gm_prefix_upto_name _ _ _ _ _ Hp) as ->.
    assert (Hkind : { forall A M, entry_tm E = Some (A, M) -> entry_kind E <> ak_level } +
                    { ~ (forall A M, entry_tm E = Some (A, M) -> entry_kind E <> ak_level) }).
    { destruct (entry_tm E) as [[A M] |] eqn:Ht.
      - destruct (abs_kind_eq_dec (entry_kind E) ak_level) as [Hk | Hk];
          [ right; intros Hn; exact (Hn _ _ eq_refl Hk) | left; intros ? ? [= <- <-]; exact Hk ].
      - left; intros ? ? [=]. }
    destruct Hkind as [Hk | Hk]; [| right; intros Hn; exact (Hk (proj1 (Hn _ _ eq_refl))) ].
    destruct (entry_unit E) as [U |] eqn:HU;
      [| left; intros Φ0' E' Hp'; inversion Hp'; subst Φ0' E'; split; [ exact Hk | intros U' HU'; rewrite HU in HU'; discriminate ] ].
    destruct (udenote_impl F Hg _ U (open_entry_order _ _ Hg _ _ _ _ _ _ _ _ Hok Hp HU)) as [(Ry & HRy) | HN].
    - destruct (rec _ _ _ _ Ry Hp HU HRy) as [Hn | Hn].
      + left; intros Φ0' E' Hp'; inversion Hp'; subst Φ0' E'.
        split; [ exact Hk |].
        intros U' HU'; rewrite HU in HU'; inversion HU'; subst U'.
        exists (decode_desc Ry); split; assumption.
      + right; intros Hy; destruct (proj2 (Hy _ _ eq_refl) _ HU) as (R & HR & HnR).
        rewrite (proj1 (proj2 (mdenote_functional_all _ _ Hg)) _ _ _ _ HR _ HRy) in HnR; exact (Hn HnR).
    - right; intros Hy; destruct (proj2 (Hy _ _ eq_refl) _ HU) as (R & HR & _); exact (HN _ HR).
  Defined.

  Definition no_level_open_dec Γ Δ Φw Φx (Hok : desc_ok Θ Ξ Γ (mdesc_open Δ Φw Φx))
      (rec : forall y Φ0 E U (Ry : fmdesc), gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_unit E = Some U ->
               udenote Θ Ξ (body_ctx Φ0 ++ Δ ++ Γ) None U (decode_desc Ry) ->
               { Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ Δ ++ Γ ⊢ⁿˡ decode_desc Ry } + { ~ Θ ⍮ Ξ ⍮ body_ctx Φ0 ++ Δ ++ Γ ⊢ⁿˡ decode_desc Ry }) :
      { Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_open Δ Φw Φx } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_open Δ Φw Φx } :=
    match names_forall_dec _ (open_name_dec Γ Δ Φw Φx Hok rec) (gm_names Φx) with
    | left H => left (proj1 (no_level_open_names _ _ _ _ _ _ Hok) H)
    | right H => right (fun Hn => match H with
                                  | ex_intro _ y (conj Hy Hny) => Hny (proj2 (no_level_open_names _ _ _ _ _ _ Hok) Hn y Hy)
                                  end)
    end.

  (** A filed body's entry at a name, read at the root, the description
      of an entry other than a definition decided by [rec] *)
  Definition closed_name_dec p T (t : ftrie) (Ht : canon_trie t)
      (Hok : desc_ok Θ Ξ ⋅ (mdesc_closed nil p T (decode_mod t) nil))
      (rec : forall y (Ry : fmdesc),
               (exists Φ0 E, gm_prefix_upto (decode_mod t) y = Some (gm_ext Φ0 y E) /\ (forall b pv r A oM, E <> ge_def b pv r A oM) /\
                  edenote Θ Ξ ⋅ (Some (qname_in p y)) (ge_read T E) (decode_desc Ry)) ->
               { Θ ⍮ Ξ ⍮ ⋅ ⊢ⁿˡ decode_desc Ry } + { ~ Θ ⍮ Ξ ⍮ ⋅ ⊢ⁿˡ decode_desc Ry })
      (y : string) : { closed_name_ok Θ Ξ p T (decode_mod t) y } + { ~ closed_name_ok Θ Ξ p T (decode_mod t) y }.
  Proof.
    pose proof (fmdesc_entry_dec (fmdesc_closed nil p T t Ht nil) y) as Hed.
    pose proof (fmdesc_entry_source_path (fmdesc_closed nil p T t Ht nil) y) as Hsp.
    destruct (fmdesc_entry (fmdesc_closed nil p T t Ht nil) y) as [[[Γy s] rd] |] eqn:Hf.
    2: left; intros Φ0 E Hp; exfalso; exact (closed_entry_none _ _ _ _ Hed _ _ Hp).
    cbn [option_map fst snd decode_desc] in Hed.
    pose proof (closed_entry_found _ _ _ _ _ _ _ Hed) as Hfound.
    destruct (source_def_kind s) as [r |] eqn:Hk.
    - (* a definition: of its kind *)
      assert (Hdef : exists Φ0 b pv A oM, gm_prefix_upto (decode_mod t) y = Some (gm_ext Φ0 y (ge_def b pv r A oM))).
      { destruct Hfound as (Φ0 & E & Hp & _ & Hs).
        destruct (source_def_kind_some _ _ Hk) as (b & pv & A & oM & Hd).
        rewrite Hs in Hd; apply ge_read_def in Hd; subst E; eauto 6. }
      destruct (abs_kind_eq_dec r ak_level) as [-> | Hn].
      + right; intros Hy; destruct Hdef as (Φ0 & b & pv & A & oM & Hp).
        exact (proj1 (Hy _ _ Hp) _ _ _ _ _ eq_refl eq_refl).
      + left; intros Φ0' E' Hp'; destruct Hdef as (Φ0 & b & pv & A & oM & Hp).
        rewrite Hp in Hp'; inversion Hp'; subst Φ0' E'.
        split; [ intros * HE; inversion HE; subst; exact Hn | intros Hnd; exfalso; exact (Hnd _ _ _ _ _ eq_refl) ].
    - (* another entry: what it denotes, read at the root *)
      assert (Hos : entry_source_ok (fmdesc_entry_path (fmdesc_closed nil p T t Ht nil) y) s)
        by (cbn [fmdesc_entry_path]; destruct s; cbn; [ discriminate (Hsp _ _ _ eq_refl) | exact I ]).
      pose proof (edenote_order_entry _ _ Hg _ _ _ _ _ _ Hok Hed) as Ho.
      assert (Hnd : forall Φ0 E, gm_prefix_upto (decode_mod t) y = Some (gm_ext Φ0 y E) -> forall b pv r A oM, E <> ge_def b pv r A oM).
      { intros Φ0 E Hp * HE; destruct Hfound as (Φ0' & E' & Hp' & _ & Hs).
        rewrite Hp in Hp'; inversion Hp'; subst Φ0' E'.
        apply (source_def_kind_none _ Hk b pv r A oM); rewrite Hs; apply ge_read_def, HE. }
      destruct (edenote_impl F Hg _ _ s Hos Ho) as [(Ry & HRy) | HN].
      + assert (Hex : exists Φ0 E, gm_prefix_upto (decode_mod t) y = Some (gm_ext Φ0 y E) /\ (forall b pv r A oM, E <> ge_def b pv r A oM) /\
                        edenote Θ Ξ ⋅ (Some (qname_in p y)) (ge_read T E) (decode_desc Ry)).
        { destruct Hfound as (Φ0 & E & Hp & -> & Hs); exists Φ0, E; split; [ exact Hp | split; [ exact (Hnd _ _ Hp) |] ].
          cbn [fmdesc_entry_path List.app] in HRy; rewrite Hs in HRy; exact HRy. }
        destruct (rec y Ry Hex) as [Hn | Hn].
        * left; intros Φ0' E' Hp'; destruct Hex as (Φ0 & E & Hp & Hnd' & HRy').
          rewrite Hp in Hp'; inversion Hp'; subst Φ0' E'.
          split; [ intros * HE; exfalso; exact (Hnd' _ _ _ _ _ HE) | intros _; exists (decode_desc Ry); split; assumption ].
        * right; intros Hy; destruct Hex as (Φ0 & E & Hp & Hnd' & HRy').
          destruct (proj2 (Hy _ _ Hp) Hnd') as (R & HR & HnR).
          rewrite (proj1 (proj2 (proj2 (mdenote_functional_all _ _ Hg))) _ _ _ _ HR _ HRy') in HnR; exact (Hn HnR).
      + right; intros Hy; destruct Hfound as (Φ0 & E & Hp & -> & Hs).
        destruct (proj2 (Hy _ _ Hp) (Hnd _ _ Hp)) as (R & HR & _).
        cbn [fmdesc_entry_path List.app] in HN; rewrite Hs in HN; exact (HN _ HR).
  Defined.

  (** A filed body: its entries at every name of its trie *)
  Lemma closed_names_all : forall Γ Θ' p T Φ Ns, gc_body Θ Ξ p = Some (T, Φ) ->
      Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_closed Θ' p T Φ Ns -> forall y, closed_name_ok Θ Ξ p T Φ y.
  Proof.
    intros * Hb Hn y Φ0 E Hp.
    exact (proj2 (no_level_closed_names _ _ Hg _ _ _ _ _ _ Hb) Hn y (gm_prefix_upto_in _ _ _ Hp) _ _ Hp).
  Qed.

  Definition no_level_closed_dec Γ Θ' p T (t : ftrie) (Ht : canon_trie t) Ns
      (Hb : gc_body Θ Ξ p = Some (T, decode_mod t))
      (Hok : desc_ok Θ Ξ Γ (mdesc_closed Θ' p T (decode_mod t) Ns))
      (rec : forall y (Ry : fmdesc),
               (exists Φ0 E, gm_prefix_upto (decode_mod t) y = Some (gm_ext Φ0 y E) /\ (forall b pv r A oM, E <> ge_def b pv r A oM) /\
                  edenote Θ Ξ ⋅ (Some (qname_in p y)) (ge_read T E) (decode_desc Ry)) ->
               { Θ ⍮ Ξ ⍮ ⋅ ⊢ⁿˡ decode_desc Ry } + { ~ Θ ⍮ Ξ ⍮ ⋅ ⊢ⁿˡ decode_desc Ry }) :
      { Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_closed Θ' p T (decode_mod t) Ns } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_closed Θ' p T (decode_mod t) Ns } :=
    match names_forall_dec _ (closed_name_dec p T t Ht (desc_ok_closed_root _ _ Hg _ _ _ _ _ _ Hok) rec) (ft_names t) with
    | left H => left (proj1 (no_level_closed_names _ _ Hg _ _ _ _ _ _ Hb) (fun y Hy => H y (decode_mod_names _ _ Hy)))
    | right H => right (fun Hn => match H with
                                  | ex_intro _ y (conj _ Hny) => Hny (closed_names_all _ _ _ _ _ _ Hb Hn y)
                                  end)
    end.

  (** A definition with a module part: its module part *)
  Definition no_level_dm_dec Γ Θd A M (Rm : fmdesc)
      (rec : forall Rm', fmdesc_mod Rm = Some Rm' -> { Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ decode_desc Rm' } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ decode_desc Rm' }) :
      { Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_dm Θd A M (decode_desc Rm) } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ mdesc_dm Θd A M (decode_desc Rm) }.
  Proof.
    pose proof (fmdesc_mod_dec Rm) as Hm.
    destruct (fmdesc_mod Rm) as [Rm' |] eqn:Hm'.
    - destruct (rec Rm' eq_refl) as [Hn | Hn].
      + left; constructor; intros Rm'' Hm''; rewrite Hm in Hm''; injection Hm'' as <-; exact Hn.
      + right; intros H; inversion H; subst; eauto.
    - left; constructor; intros Rm'' Hm''; rewrite Hm in Hm''; discriminate.
  Defined.

  (** The decision, by recursion on the domain, the shape of the fast
      description read off by an equation so that the domain is not passed
      along ([no_level_reachable_open_inv] and its siblings) *)
  Fixpoint no_level_desc_dec Γ (R : fmdesc) (Hr : no_level_reachable Θ Ξ Γ (decode_desc R)) {struct Hr} :
      desc_ok Θ Ξ Γ (decode_desc R) -> { Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ decode_desc R } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ decode_desc R } :=
    match R as R0 return R = R0 -> desc_ok Θ Ξ Γ (decode_desc R0) ->
                         { Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ decode_desc R0 } + { ~ Θ ⍮ Ξ ⍮ Γ ⊢ⁿˡ decode_desc R0 } with
    | fmdesc_term r A om => fun _ _ => no_level_term_dec Γ r A om
    | fmdesc_open Δ Φw Φx => fun Heq Hok =>
        no_level_open_dec Γ Δ Φw Φx Hok
          (fun y Φ0 E U Ry Hp HU Hu =>
             no_level_desc_dec _ Ry
               (no_level_reachable_open_inv Hr _ _ _ (f_equal decode_desc Heq) y Φ0 E U (decode_desc Ry) Hp HU Hu)
               (open_entry_desc_ok _ _ _ _ _ _ _ _ _ _ _ Hok Hp HU Hu))
    | fmdesc_closed Θ' p T t Ht Ns => fun Heq Hok =>
        no_level_closed_dec Γ Θ' p T t Ht Ns
          (no_level_reachable_closed_body Hr _ _ _ _ _ (f_equal decode_desc Heq))
          Hok
          (fun y Ry Hex =>
             no_level_desc_dec ⋅ Ry
               (match Hex with
                | ex_intro _ Φ0 (ex_intro _ E (conj Hp (conj Hnd Hed))) =>
                    no_level_reachable_closed_inv Hr _ _ _ _ _ (f_equal decode_desc Heq) y Φ0 E (decode_desc Ry) Hp Hnd Hed
                end)
               (match Hex with
                | ex_intro _ Φ0 (ex_intro _ E (conj Hp (conj _ Hed))) =>
                    closed_child_desc_ok _ _ Hg _ _ _ _ _ _ _ (desc_ok_closed_root _ _ Hg _ _ _ _ _ _ Hok) Hp Hed
                end))
    | fmdesc_dm Θd A M Rm => fun Heq Hok =>
        no_level_dm_dec Γ Θd A M Rm
          (fun Rm' Hm =>
             no_level_desc_dec Γ Rm'
               (no_level_reachable_dm_inv Hr _ _ _ _ (f_equal decode_desc Heq) (decode_desc Rm')
                  (eq_trans (fmdesc_mod_dec Rm) (f_equal (option_map decode_desc) Hm)))
               (desc_ok_mod _ _ Hg _ _ _ Hok (eq_trans (fmdesc_mod_dec Rm) (f_equal (option_map decode_desc) Hm))))
    end eq_refl.
End Decide.

(** ** The Flag Premise, Decided *)

(** Every parameter is a type of levels, or what a well-formed target
    denotes has no member of a type of levels: its description, computed,
    reads no open frame and is decided by its reads, or it reads one and
    has a member of no filed body. *)
Definition levels_abstractable_fast_dec (F : FCtx) G Δ E (HC : ⊢ fc_deps F ⍮ fc_stack F ⍮ Δ ++ G)
    (HE : fc_deps F ⍮ fc_stack F ⍮ Δ ++ G ⊢ᵐ E ≈ E) :
    { levels_abstractable (fc_deps F) (fc_stack F) G Δ E } + { ~ levels_abstractable (fc_deps F) (fc_stack F) G Δ E }.
Proof.
  pose proof (ctx_wf_gctx _ _ _ HC) as Hg.
  destruct (level_sorted_parameters_dec Δ) as [Hs | Hs]; [ left; left; exact Hs |].
  destruct (mdenote_dec F Hg (Δ ++ G) E HE) as [(R & HR) | HN].
  2: right; intros [Hs' | (R & HR & _)]; [ exact (Hs Hs') | exact (HN _ HR) ].
  assert (Hun : forall R', mdenote (fc_deps F) (fc_stack F) (Δ ++ G) E R' -> R' = decode_desc R)
    by (intros R' HR'; exact (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR' _ HR)).
  destruct (desc_reads_frame_dec F R) as [Hr | Hr].
  - right; intros [Hs' | (R' & HR' & Hn)]; [ exact (Hs Hs') |].
    rewrite (Hun _ HR') in Hn; exact (no_level_reads_frame _ _ _ _ Hr Hn).
  - pose proof (me_desc_ok _ _ _ _ _ _ HE HR) as Hok.
    pose proof (no_level_reachable_of_desc_ok _ _ Hg _ _ Hok (mdenote_canon _ _ _ _ _ Hg HR) Hr) as Hreach.
    destruct (no_level_desc_dec F Hg _ R Hreach Hok) as [Hn | Hn].
    + left; right; exists (decode_desc R); split; [ exact HR | exact Hn ].
    + right; intros [Hs' | (R' & HR' & Hn')]; [ exact (Hs Hs') |].
      rewrite (Hun _ HR') in Hn'; exact (Hn Hn').
Defined.
