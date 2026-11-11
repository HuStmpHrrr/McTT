(** * Members of Applied Module Expressions

    A member of a module expression lacking a parameter, applied to an
    argument, is the member of the module expression given the argument
    ([wf_exp_eq_mem_app]).  No rule says so: both sides are δ-equal to
    reducts related by [β], or the member is the filed member of a bare
    stored body ([mem_alias_filed]) and its application the self-named
    reduct of the member of the stored body at the argument. *)

From Stdlib Require Import Lia List PeanoNat RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System SystemOpt CoreInversions.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Modules Paths DescTyping LookupSound Presup.
From Mctt.Core.Soundness Require Import LogicalRelation ModuleValues Selection.
Import Syntax_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.
  Import Fixed_Notations.

(** ** Members Read Through Their Module's Description *)

(** [H.x] is no type former of an inductive or record type whose
    declaration frame is open: the side conditions of [mdenote_ind_frame]
    and of [mdenote_record_frame], negated.  It is a proof premise only,
    adding no semantics: it says that those two rules do not apply, so that
    a typed member [H.x] is read through [H]'s description
    ([mdenote_mem_typed]). *)
Definition not_frame_former (H : modexp) (x : String.string) : Prop :=
  (forall p pq k D Mk Tm Φm, mod_qname (me_mem H x) = Some p -> gs_find_ind gc_stack p = Some (pq, k, D) ->
     ind_member D k = Some Mk -> gc_loc gc_deps gc_stack p = Some (Tm, Φm) -> False) /\
  (forall p R Tm Φm, mod_qname (me_mem H x) = Some p -> gs_find_record gc_stack p = Some R ->
     gc_loc gc_deps gc_stack p = Some (Tm, Φm) -> False).

(** A member is a type former under declaration, of a group member or of
    a record type, or it is none: the side conditions are decided. *)
Lemma frame_former_cases : forall H x (P : Prop),
    (not_frame_former H x -> P) ->
    (forall p pq k D Mk Tm Φm, mod_qname (me_mem H x) = Some p -> gs_find_ind gc_stack p = Some (pq, k, D) ->
       ind_member D k = Some Mk -> gc_loc gc_deps gc_stack p = Some (Tm, Φm) -> P) ->
    (forall p R Tm Φm, mod_qname (me_mem H x) = Some p -> gs_find_record gc_stack p = Some R ->
       gc_loc gc_deps gc_stack p = Some (Tm, Φm) -> P) ->
    P.
Proof.
  intros * Hn Hi Hr.
  destruct (mod_qname (me_mem H x)) as [p |] eqn:Hq;
    [| apply Hn; split; intros * Hp; rewrite Hq in Hp; discriminate ].
  destruct (gc_loc gc_deps gc_stack p) as [[Tm Φm] |] eqn:Hl;
    [| apply Hn; split; intros * Hp; rewrite Hq in Hp; injection Hp as <-; intros; congruence ].
  destruct (gs_find_ind gc_stack p) as [[[pq k] D] |] eqn:Hf.
  - destruct (ind_member D k) as [Mk |] eqn:HMk; [ exact (Hi _ _ _ _ _ _ _ eq_refl Hf HMk Hl) |].
    destruct (gs_find_record gc_stack p) as [R |] eqn:Hfr; [ exact (Hr _ _ _ _ eq_refl Hfr Hl) |].
    apply Hn; split; intros * Hp; rewrite Hq in Hp; injection Hp as <-; intros; congruence.
  - destruct (gs_find_record gc_stack p) as [R |] eqn:Hfr; [ exact (Hr _ _ _ _ eq_refl Hfr Hl) |].
    apply Hn; split; intros * Hp; rewrite Hq in Hp; injection Hp as <-; intros; congruence.
Qed.

(** A member of a module expression naming no stored module is no type
    former under declaration. *)
Lemma not_frame_former_of_none : forall H x, mod_qname H = None -> not_frame_former H x.
Proof. intros * Hq; split; intros * Hp; cbn [mod_qname] in Hp; rewrite Hq in Hp; discriminate. Qed.

(** A typed substitution keeps a member of a well-formed module expression
    no type former under declaration: it keeps the path the module
    expression names ([mod_qname_sub_eq]), sending a slot to a literal or
    a slot, never to a path. *)
Lemma not_frame_former_sub : forall Γ H Γ1 ζ x,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> Γ1 ⊢ˢ ζ : Γ -> not_frame_former H x -> not_frame_former H[ζ]ᵐ x.
Proof.
  intros * HH Hζ [Hi Hr].
  assert (E : mod_qname (me_mem H[ζ]ᵐ x) = mod_qname (me_mem H x))
    by (cbn [mod_qname]; rewrite (mod_qname_sub_eq _ _ _ _ (wf_sub_mod_compat _ _ _ _ _ Hζ) (proj1 (modexp_eq_slot_root _ _ _ _ _ HH)));
        reflexivity).
  split; intros *; rewrite E; [ apply Hi | apply Hr ].
Qed.

(** A typed member that is no type former under declaration is read
    through its module's description: the other rules for a selection
    denote a stored unit, of no type, or a type former under
    declaration. *)
Lemma mdenote_mem_typed : forall Γ H y R A (P : Prop),
    not_frame_former H y -> mdenote gc_deps gc_stack Γ (me_mem H y) R -> mdesc_type R = Some A ->
    (forall R0 R0m Γy E rd R', mdenote gc_deps gc_stack Γ H R0 -> mdesc_mod R0 = Some R0m ->
       mdesc_entry R0m y = Some (Γy, E, rd) -> edenote gc_deps gc_stack (Γy ++ Γ) (mdesc_entry_path R0m y) E R' ->
       mdesc_read rd R' = Some R -> P) ->
    P.
Proof.
  intros * [Hi Hr] Hm HA Hk; inversion Hm; subst.
  - cbn in HA; discriminate.
  - exfalso; eapply Hi; eassumption.
  - eapply Hk; eassumption.
  - exfalso; eapply Hr; eassumption.
Qed.

(** A description abstracted over a telescope ending in an assumption, as
    the term part's reduct: a [λ] over the outermost parameter. *)
Lemma reduct_up_last : forall Δ0 κ B X M,
    mdesc_reduct X = Some M ->
    mdesc_reduct (mdesc_up (Δ0 ++ ce_ass κ B :: nil) X) = Some (λ B (ctx_fn Δ0 M)).
Proof. intros * HM; rewrite mdesc_reduct_up, HM; cbn [option_map]; rewrite ctx_fn_app; reflexivity. Qed.

(** Parameters of types of levels, the inner ones. *)
Lemma level_sorted_parameters_app_l : forall Δ0 Δ1, level_sorted_parameters (Δ0 ++ Δ1) -> level_sorted_parameters Δ0.
Proof. intros * H Δa κ T Δb ->; eapply H; rewrite <- app_assoc; reflexivity. Qed.

(** A definition of a type of levels in an open module: the module's
    parameters are of types of levels ([desc_levels_abstractable]). *)
Lemma open_entry_level_params : forall Γ Δ Φw Φx y Φ0 E A M,
    desc_ok gc_deps gc_stack Γ (mdesc_open Δ Φw Φx) ->
    gm_prefix_upto Φx y = Some (gm_ext Φ0 y E) -> entry_tm E = Some (A, M) ->
    entry_kind E = ak_level -> level_sorted_parameters Δ.
Proof.
  intros * Hok Hp HE Hk; inversion Hok; subst.
  match goal with HL : desc_levels_abstractable _ _ _ _ _ |- _ => destruct HL as [HLs | Hnl] end; [ assumption |].
  exfalso; inversion Hnl; subst.
  match goal with Hne : forall y Φ0 E A M, gm_prefix_upto _ y = Some _ -> entry_tm E = Some (A, M) -> entry_kind E <> ak_level |- _ =>
    exact (Hne _ _ _ _ _ Hp HE Hk) end.
Qed.

(** The member [x], of type [A], of a module expression [H] lacking a
    parameter of type [B], given the argument [N]: [A] is a [Π] over [B]
    into [C], the member of [H] given [N] is described by [R'], of type
    [C] at [N], and the member of [H] applied to [N] is it. *)
Record mem_app_shape (Γ : ctx) (H : modexp) (N : exp) (x : String.string) (A B C : typ) (R' : mdesc) : Prop :=
  mk_mem_app_shape
  { (** [B] is the next parameter of [H]'s module part *)
    mem_app_shape_param : forall R0 T T1 B', mdenote gc_deps gc_stack Γ H R0 -> mdesc_mod_tele R0 = Some T ->
      tele_view T = Some (B', T1) -> B' = B
    (** The member's type is a [Π] over [B] into [C] *)
  ; mem_app_shape_type : exists κ κc, A = a_pi κ κc B C
    (** The member of [H] given [N] is described by [R'] *)
  ; mem_app_shape_mem : mdenote gc_deps gc_stack Γ (me_mem (me_app H N) x) R'
    (** Of type [C] at [N] *)
  ; mem_app_shape_mem_type : mdesc_type R' = Some C[Id,,N]
    (** The member applied to [N] is the member of [H] given [N] *)
  ; mem_app_shape_eq : Γ ⊢ a_mem H x $ N ≈ a_mem (me_app H N) x : C[Id,,N] }.

(** A member of an open module lacking a parameter, applied to an
    argument, is the member of the module given it: both are δ-equal to
    their reducts, the first a [λ] over the parameter whose body is typed
    over it ([body_defs_wf], [ctx_fn_eq]), [β]-equal to the second. *)
Lemma mem_app_eq_open : ⊢ᵍ gc_deps ⍮ gc_stack -> forall Γ H N x R0 Δ Φw Φx R A,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H N -> not_frame_former H x ->
    mdenote gc_deps gc_stack Γ H R0 -> mdesc_mod R0 = Some (mdesc_open Δ Φw Φx) ->
    mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A ->
    Γ ⊢ a_mem H x : A ->
    exists B C R', mem_app_shape Γ H N x A B C R'.
Proof.
  intros Hgw * HHN Hq HR0 HR0m Hm HA HxA.
  pose proof (wf_gstack_closed _ _ Hgw) as Hc.
  destruct (proj1 (modexp_gen _ _ _ _ _ HHN)) as [HH (R0' & T & B & T1 & Srt & HR0' & HT & Hv & HB & HSrt & HNt)].
  rewrite (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ HR0' _ HR0) in HT.
  unfold mdesc_mod_tele in HT; rewrite HR0m in HT; cbn [mdesc_tele] in HT; injection HT as <-.
  pose proof (desc_ok_mod _ _ Hgw _ _ _ (me_desc_ok _ _ _ _ _ _ HH HR0) HR0m) as Hok.
  pose proof Hok as Hok0; inversion Hok0; subst.
  match goal with H : all_assumptions Δ |- _ => rename H into HΔa end.
  (** The outermost parameter *)
  destruct Δ as [| e Δ0 _] using rev_ind; [ cbn in Hv; discriminate |].
  pose proof HΔa as HΔa0; unfold all_assumptions in HΔa0; apply Forall_app in HΔa0 as [HΔ0a He1];
    apply Forall_cons_iff in He1 as [(κ & B0 & ->) _].
  rewrite tele_view_last in Hv; injection Hv as <- <-.
  (** The member's entry, read *)
  apply (mdenote_mem_typed _ _ _ _ _ _ Hq Hm HA); intros R0'' R0m Γy E rd R1 Hm0 HR0m' He Hed Hrd.
  rewrite (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ Hm0 _ HR0), HR0m in HR0m'; injection HR0m' as <-.
  pose proof He as He0; cbn in He0.
  destruct (gm_prefix_upto Φx x) as [[| Φ' z E0 | ] |] eqn:Hp; try discriminate.
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & Heq & _); injection Heq as <- -> <-.
  (** The term part, abstracted over the parameters *)
  assert (HX : exists r A1 M1, entry_tm E0 = Some (A1, M1) /\ entry_kind E0 = r /\ Γy = body_ctx Φ' ++ Δ0 ++ ce_ass κ B0 :: nil /\
            E = E0 /\ rd = reader_open (Δ0 ++ ce_ass κ B0 :: nil) Φ' /\ mdesc_kind R1 = r /\
            mdesc_type R1 = Some A1 /\ mdesc_reduct R1 = Some M1).
  { destruct E0 as [[|] pv r A1 [M1 |] | pv U | | pv A1 M1 U |]; try discriminate; injection He0 as <- <- <-.
    - inversion Hed; subst; exists r, A1, M1; repeat split; reflexivity.
    - exfalso; inversion Hed; subst.
      match goal with Hu : udenote _ _ _ _ _ _ |- _ => pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hmm end.
      cbn [mdesc_read] in Hrd; destruct (gm_fill Φ'); cbn [option_map] in Hrd; [ injection Hrd as <- | discriminate ].
      destruct R1; cbn in Hmm; try contradiction; cbn in HA; discriminate.
    - inversion Hed; subst; exists ak_relevant, A1, M1; repeat split; reflexivity. }
  destruct HX as (r & A1 & M1 & HtE & HkE & -> & -> & -> & Hk1 & HA1 & HM1).
  assert (HrdR1 : mdesc_read (reader_open (Δ0 ++ ce_ass κ B0 :: nil) Φ') R1 = Some R) by exact Hrd.
  cbn [mdesc_read] in Hrd; destruct (gm_fill Φ') as [σf |] eqn:Hf; cbn [option_map] in Hrd; [ injection Hrd as <- | discriminate ].
  (** The reduct and the type before the argument: a [λ] and a [Π] over it *)
  set (Mb := ctx_fn Δ0 M1[σf]); set (Ab := ctx_pi_at r Δ0 A1[σf]).
  assert (HRr : mdesc_reduct (mdesc_up (Δ0 ++ ce_ass κ B0 :: nil) (mdesc_sub R1 σf)) = Some (λ B0 Mb))
    by exact (reduct_up_last _ _ _ _ _ (mdesc_reduct_sub _ _ _ HM1)).
  assert (HRt : mdesc_type (mdesc_up (Δ0 ++ ce_ass κ B0 :: nil) (mdesc_sub R1 σf)) = Some (a_pi κ r B0 Ab)).
  { rewrite (mdesc_type_up _ _ _ (mdesc_type_sub _ _ σf HA1)), mdesc_kind_sub, Hk1, ctx_pi_app; reflexivity. }
  rewrite HRt in HA; injection HA as <-.
  (** The member after the argument *)
  pose proof (mdesc_at_up Δ0 κ B0 (mdesc_sub R1 σf) N) as HRat.
  set (R' := mdesc_up (tele_sub Δ0 (Id,,N)) (mdesc_sub (mdesc_sub R1 σf) (sb_qn (List.length Δ0) (Id,,N)))) in HRat.
  assert (HtR' : mdesc_type R' = Some Ab[Id,,N]).
  { unfold R', Ab; rewrite (mdesc_type_up _ _ _ (mdesc_type_sub _ _ _ (mdesc_type_sub _ _ σf HA1))), !mdesc_kind_sub, Hk1, ctx_pi_sub;
      reflexivity. }
  assert (HrR' : mdesc_reduct R' = Some Mb[Id,,N]).
  { unfold R', Mb; rewrite mdesc_reduct_up, (mdesc_reduct_sub _ _ _ (mdesc_reduct_sub _ _ σf HM1)), ctx_fn_sub; reflexivity. }
  destruct (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & _ & _).
  pose proof (mdesc_mod_scoped _ _ _ (wf_mdenote_scoped _ _ _ _ _ _ HH HR0) HR0m) as Hs0.
  pose proof (mdesc_mod_is_mod _ _ HR0m) as HisR0m.
  destruct (mdesc_at_of_view _ _ N _ _ _ Hok HisR0m eq_refl ltac:(rewrite tele_view_last; reflexivity)) as (R0m' & HR0m').
  destruct (mdesc_at_of_mod_part _ _ _ _ HR0m HR0m') as (R0a & HR0a & HmR0a).
  rewrite (mdesc_is_mod_mod _ (mdesc_at_is_mod _ _ _ HisR0m HR0m')) in HmR0a.
  assert (HmX : mdenote gc_deps gc_stack Γ (me_app H N) R0a) by exact (mdenote_app _ _ _ _ _ _ _ HR0 HR0a).
  destruct (sel_at_open _ _ Hc _ _ _ _ _ _ _ _ _ _ _ _ _ HΓ Hs0 HΔa HR0m' He Hed HrdR1 HRat)
    as (Γy' & E' & rd' & R'' & He' & Hed' & Hrd').
  assert (Hpath : mdesc_entry_path R0m' x = None)
    by (cbn [mdesc_at] in HR0m'; destruct (tele_split (rev (Δ0 ++ ce_ass κ B0 :: nil))) as [[[? ?] ?] | ?];
        [ injection HR0m' as <-; reflexivity | discriminate ]).
  assert (HmNx : mdenote gc_deps gc_stack Γ (me_mem (me_app H N) x) R')
    by (eapply mdenote_mem; [ exact HmX | exact HmR0a | exact He' | rewrite Hpath; exact Hed' | exact Hrd' ]).
  (** The body over the parameter *)
  destruct (presup_exp_typ_sorted HxA ltac:(discriminate)) as (S & _ & HAS).
  destruct (wf_pi_parts_at _ _ _ _ _ _ _ _ HAS) as [? i _ _ HAb Hk].
  destruct (body_defs_wf _ _ _ _ _ H3 H4) as (es & _ & Hdefs).
  destruct (Hdefs _ _ _ _ _ _ Hp HtE Hf) as (_ & HMt).
  destruct (H12 _ _ _ _ _ _ Hp HtE Hf) as (j & HAj).
  rewrite <- app_assoc in HMt, HAj; cbn [app] in HMt, HAj.
  assert (HMb : Γ ▹{κ} B0 ⊢ Mb : Ab).
  { eapply presup_exp_eq_left; unfold Mb, Ab; eapply ctx_fn_eq;
      [ exact HΔ0a | exact (presup_exp_ctx HMt)
      | intros Hl; eapply level_sorted_parameters_app_l, open_entry_level_params;
        [ exact Hok | exact Hp | exact HtE | rewrite HkE; exact Hl ]
      | rewrite <- HkE; exact HAj | apply wf_exp_eq_refl; exact HMt ]. }
  exists B0, Ab, R'; constructor; [ | exists κ, r; reflexivity | exact HmNx | exact HtR' |].
  { intros R0x Tx T1x B' HRx HTx Hvx.
    rewrite (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ HRx _ HR0) in HTx.
    unfold mdesc_mod_tele in HTx; rewrite HR0m in HTx; cbn [mdesc_tele] in HTx; injection HTx as <-.
    rewrite tele_view_last in Hvx; congruence. }
  eapply wf_exp_eq_trans;
    [ eapply wf_exp_eq_app_cong'; [ eapply wf_exp_eq_mem_delta; [ exact HH | exact Hm | exact HRt | exact HRr ] | apply wf_exp_eq_refl; exact HNt ] |].
  eapply wf_exp_eq_trans; [ eapply wf_exp_eq_pi_beta'; [ exact HAb | exact Hk | exact HMb | exact HNt ] |].
  apply wf_exp_eq_sym; eapply wf_exp_eq_mem_delta; [ exact HHN | exact HmNx | exact HtR' | exact HrR' ].
Qed.

(** ** Descriptions abstracted over a telescope ending in an assumption *)

(** Its type is a [Π] over the assumption. *)
Lemma type_up_last : forall P κ B Y AY, mdesc_type Y = Some AY ->
    mdesc_type (mdesc_up (P ++ ce_ass κ B :: nil) Y) = Some (a_pi κ (mdesc_kind Y) B (ctx_pi_at (mdesc_kind Y) P AY)).
Proof. intros * HY; rewrite (mdesc_type_up _ _ _ HY), ctx_pi_app; reflexivity. Qed.

(** Given an argument ([mdesc_at_up]), it is of the codomain of that [Π]
    at the argument. *)
Lemma type_up_last_at : forall P Y AY N, mdesc_type Y = Some AY ->
    mdesc_type (mdesc_up (tele_sub P (Id,,N)) (mdesc_sub Y (sb_qn (List.length P) (Id,,N)))) = Some (ctx_pi_at (mdesc_kind Y) P AY)[Id,,N].
Proof. intros * HY; rewrite (mdesc_type_up _ _ _ (mdesc_type_sub _ _ _ HY)), mdesc_kind_sub, ctx_pi_sub; reflexivity. Qed.

(** A description abstracted over a telescope of assumptions given fewer
    arguments than the telescope has is abstracted over the rest, which
    ends in an assumption ([mdesc_ats_up_prefix]): the rest of the
    telescope instantiated by the arguments, as a closed module's
    telescope is ([mdesc_tele]). *)
Lemma ats_up_short : forall Ns P Y, all_assumptions P -> List.length Ns < List.length P ->
    exists P' κ B τ, tele_sub (firstn (List.length P - List.length Ns) P) (sb_of_list Id Ns) = P' ++ ce_ass κ B :: nil /\
      mdesc_ats (mdesc_up P Y) Ns = Some (mdesc_up (P' ++ ce_ass κ B :: nil) (mdesc_sub Y τ)).
Proof.
  intros * HP Hl.
  set (k := List.length P - List.length Ns).
  pose proof (firstn_skipn k P) as HPs.
  assert (Hup : mdesc_up P Y = mdesc_up (firstn k P ++ skipn k P) Y) by (rewrite HPs; reflexivity).
  rewrite Hup; rewrite <- HPs in HP.
  unfold all_assumptions in HP; apply Forall_app in HP as [HP1 HP2].
  assert (Hk : List.length (skipn k P) = List.length Ns) by (rewrite length_skipn; unfold k; lia).
  rewrite (mdesc_ats_up_prefix _ _ _ _ HP2 Hk).
  destruct (all_assumptions_last (tele_sub (firstn k P) (sb_of_list Id Ns)) (all_assumptions_sub _ _ HP1))
    as (P' & κ & B & HP'); [ intros Hn; apply (f_equal (@List.length _)) in Hn; rewrite length_tele_sub, length_firstn in Hn; cbn in Hn; unfold k in Hn; lia |].
  rewrite HP'; do 4 eexists; split; reflexivity.
Qed.

(** A type former applied is a type former applied. *)
Lemma app_const_apps : forall Ns M, app_const (apps M Ns) = app_const M.
Proof. induction Ns as [| N Ns IH]; intros; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(** The term part of a type former of a type over [P ++ T], given fewer
    arguments than [T] has assumptions: of a [Π] type, and it takes one
    more argument, at the codomain. *)
Lemma former_term_part_more : forall Ns X T S M N r B M', all_assumptions T -> List.length Ns < List.length T -> app_const M = true ->
    mdesc_term_part_ats (mdesc_term ak_relevant (ctx_pi (X ++ T) S) (Some M)) Ns = Some (mdesc_term r B (Some M')) ->
    exists κ κc B0 C, (exists P', tele_sub (firstn (List.length T - List.length Ns) T) (sb_of_list Id Ns) = P' ++ ce_ass κ B0 :: nil) /\
      B = a_pi κ κc B0 C /\ mdesc_term_part_at (mdesc_term r B (Some M')) N = Some (mdesc_term r C[Id,,N] (Some (a_app M' N))).
Proof.
  intros * HT Hl Hc Ha.
  destruct (ats_up_short Ns T (mdesc_up X (mdesc_term ak_relevant S None)) HT Hl) as (P' & κ & B0 & τ & HP' & Hs).
  rewrite <- mdesc_up_cat in Hs; cbn [mdesc_up mdesc_sub option_map] in Hs.
  rewrite (mdesc_term_part_ats_head _ _ _ _ _ Hc Hs) in Ha; injection Ha as <- <- <-.
  rewrite ctx_pi_app; cbn [ctx_pi_at mdesc_term_part_at pi_view].
  rewrite (app_const_fn_view _ (eq_trans (app_const_apps _ _) Hc)), app_const_apps, Hc.
  exists κ; do 3 eexists; split; [ exists P'; exact HP' | split; reflexivity ].
Qed.

(** A term part over [T] whose body is over [T], given fewer arguments than
    [T] has assumptions, likewise. *)
Lemma body_term_part_more : forall Ns T k A0 om0 N R1, all_assumptions T -> List.length Ns < List.length T ->
    mdesc_ats (mdesc_up T (mdesc_term k A0 om0)) Ns = Some R1 ->
    exists κ κc B0 C R', (exists P', tele_sub (firstn (List.length T - List.length Ns) T) (sb_of_list Id Ns) = P' ++ ce_ass κ B0 :: nil) /\
      mdesc_type R1 = Some (a_pi κ κc B0 C) /\ mdesc_at R1 N = Some R' /\
      mdesc_term_part_at R1 N = Some R' /\ mdesc_type R' = Some C[Id,,N] /\
      (om0 <> None -> exists r X M'', R' = mdesc_term r X (Some M'')).
Proof.
  intros * HT Hl Ha.
  destruct (ats_up_short Ns T (mdesc_term k A0 om0) HT Hl) as (P' & κ & B0 & τ & HP' & Hs).
  rewrite Hs in Ha; injection Ha as <-.
  pose proof (mdesc_type_sub (mdesc_term k A0 om0) A0 τ eq_refl) as Hty.
  pose proof (type_up_last P' κ B0 _ _ Hty) as HtU.
  pose proof (type_up_last_at P' _ _ N Hty) as HtA.
  pose proof (mdesc_at_up P' κ B0 (mdesc_sub (mdesc_term k A0 om0) τ) N) as Hat.
  pose proof (mdesc_term_part_at_up_term P' κ B0 k A0[τ] (option_map (fun M => M[τ]) om0) N) as Htp.
  do 5 eexists; split; [ exists P'; exact HP' | split; [ exact HtU | split; [ exact Hat | split; [ etransitivity; [ exact Htp | exact Hat ] | split; [ exact HtA |] ] ] ] ].
  intros Hn; destruct om0; [| contradiction Hn; reflexivity ]; cbn [mdesc_up mdesc_sub option_map]; do 3 eexists; reflexivity.
Qed.

(** A module read at arguments has no type: closes the goal. *)
#[local] Ltac no_mod_type :=
  match goal with
  | Hu : udenote _ _ _ _ _ _, Hats : mdesc_ats_read _ _ = Some ?R1, HA : mdesc_type ?R1 = Some _ |- _ =>
      let Hm := fresh "Hm" in let Hm1 := fresh "Hm1" in
      pose proof (udenote_is_mod _ _ _ _ _ _ Hu) as Hm;
      rewrite (mdesc_ats_read_mod _ _ Hm) in Hats; pose proof (mdesc_ats_is_mod _ _ _ Hm Hats) as Hm1;
      destruct R1; cbn in Hm1, HA; first [ contradiction | discriminate ]
  end.

(** A member of a closed module part with no outside parameter, at fewer
    arguments than its telescope has: of a [Π] type, and read at one more
    argument, of the codomain at it.  A stored definition's type and body
    are over the telescope ([syn_V]); a definition with a module part's and
    a type former's are by coherence ([ge_coherent]); a module has no
    type. *)
Lemma closed_read_more : valid_syn gc_deps gc_stack -> forall Γ p T Φ x Φ0 E0 RE Ns N R1 A,
    loc gc_deps gc_stack p T Φ -> gm_coherent T Φ -> all_assumptions T -> List.length Ns < List.length T ->
    gm_prefix_upto Φ x = Some (gm_ext Φ0 x E0) ->
    edenote gc_deps gc_stack Γ (Some (qname_in p x)) (ge_read T E0) RE ->
    mdesc_ats_read RE Ns = Some R1 -> mdesc_type R1 = Some A ->
    exists κ κc B C R1', (exists P', tele_sub (firstn (List.length T - List.length Ns) T) (sb_of_list Id Ns) = P' ++ ce_ass κ B :: nil) /\
      A = a_pi κ κc B C /\ mdesc_ats_read RE (Ns ++ N :: nil) = Some R1' /\ mdesc_type R1' = Some C[Id,,N].
Proof.
  intros Hv * Hl Hco HTa Hlt Hp Hed Hats HA.
  pose proof (gm_coherent_prefix _ _ _ _ _ Hco Hp) as HcoE.
  destruct (loc_valid _ _ _ _ _ Hv Hl) as [_ HgV].
  pose proof (gm_valid_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ HgV Hp) as HVE.
  assert (Hle : List.length Ns <= List.length T) by lia.
  destruct E0 as [b pv r A0 oM | pv [Δ [sm Φy | Ea]] | pv pq k D Φ' | pv Ad Md U | pv pr Rr Φ'].
  - (** A definition: its type and its body over the telescope *)
    cbn [ge_read] in Hed; inversion Hed; subst.
    cbn in HVE; destruct HVE as (A1 & -> & _ & Hbody).
    assert (Hup : exists om0, mdesc_term r (ctx_pi_at r T A1) (if b then oM else None) = mdesc_up T (mdesc_term r A1 om0)).
    { destruct b; [ destruct oM as [M |] |];
        [ destruct (Hbody M eq_refl) as (M0 & -> & _); exists (Some M0) | exists None | exists None ]; reflexivity. }
    destruct Hup as (om0 & Hup); rewrite Hup in Hats |- *.
    rewrite mdesc_ats_read_other in Hats |- * by (cbn [mdesc_up]; intros; discriminate).
    destruct (body_term_part_more _ _ _ _ _ N _ HTa Hlt Hats) as (κ & κc & B0 & C & R' & HP' & HtR1 & Hat & _ & HtR' & _).
    rewrite HtR1 in HA; injection HA as <-.
    exists κ, κc, B0, C, R'; split; [ exact HP' | split; [ reflexivity | split; [ rewrite mdesc_ats_snoc, Hats; exact Hat | exact HtR' ] ] ].
  - exfalso; destruct sm; cbn [ge_read] in Hed; inversion Hed; subst; no_mod_type.
  - exfalso; cbn [ge_read] in Hed; inversion Hed; subst; no_mod_type.
  - (** A type former of a group: over its parameters, which end in the
        telescope *)
    cbn [ge_read] in Hed; inversion Hed; subst.
    cbn [ge_coherent] in HcoE; destruct HcoE as [(Δ0 & HuD & _) _].
    unfold ind_former_desc in Hats |- *; cbn [mdesc_ats_read] in Hats |- *.
    assert (Hp' : im_params D Mk = (im_nparams Mk ++ Δ0) ++ T) by (unfold im_params; rewrite HuD, app_assoc; reflexivity).
    rewrite Hp' in Hats |- *.
    destruct (mdesc_term_part_ats _ Ns) as [[r1 B [M' |] | | |] |] eqn:Htp; try discriminate.
    destruct (mdesc_ats (mdesc_closed nil pm Tm Φm nil) Ns) as [Rm' |] eqn:HRm; [ injection Hats as <- | discriminate ].
    cbn in HA; injection HA as <-.
    match type of Htp with mdesc_term_part_ats (mdesc_term _ _ (Some ?M)) _ = _ =>
      destruct (former_term_part_more _ _ _ _ M N _ _ _ HTa Hlt eq_refl Htp) as (κ & κc & B0 & C & HP' & -> & Hat) end.
    rewrite mdesc_term_part_ats_snoc, Htp, Hat, mdesc_ats_snoc, HRm.
    rewrite mdesc_ats_closed_nil in HRm; injection HRm as <-.
    exists κ, κc, B0, C; eexists; split; [ exact HP' | split; [ reflexivity | split; reflexivity ] ].
  - (** A definition with a module part: its term part's type and body over
        the telescope, its module part an alias over it *)
    cbn [ge_read] in Hed; inversion Hed; subst.
    cbn [ge_coherent] in HcoE; destruct HcoE as [(A1 & M1 & -> & ->) (Δ0 & E1 & HU & HΔ0)].
    injection HU as -> ->.
    match goal with Hu : udenote _ _ _ _ (gu_mk _ (md_alias _)) _ |- _ => inversion Hu; subst end.
    cbn [mdesc_ats_read] in Hats |- *.
    change (mdesc_term ak_relevant (ctx_pi T A1) (Some (ctx_fn T M1))) with (mdesc_up T (mdesc_term ak_relevant A1 (Some M1))) in *.
    rewrite (mdesc_term_part_ats_up _ _ _ _ _ HTa Hle) in Hats.
    destruct (mdesc_ats (mdesc_up T (mdesc_term ak_relevant A1 (Some M1))) Ns) as [R1t |] eqn:Htp; [| discriminate ].
    destruct (body_term_part_more _ _ _ _ _ N _ HTa Hlt Htp) as (κ & κc & B0 & C & Rt & HP' & HtR1 & _ & Hat & HtR' & HR').
    destruct (HR' ltac:(discriminate)) as (r' & X & M'' & ->); cbn in HtR'; injection HtR' as ->.
    assert (HΔa : all_assumptions (Δ0 ++ T)) by (apply Forall_app; split; assumption).
    destruct (ats_up_short Ns (Δ0 ++ T) R' HΔa ltac:(rewrite length_app; lia)) as (Pm & κm & Bm & τm & _ & HRm).
    rewrite HRm in Hats.
    destruct R1t as [r1 B [M' |] | | |]; try discriminate; injection Hats as <-.
    cbn in HtR1, HA; rewrite HtR1 in HA; injection HA as <-.
    rewrite mdesc_term_part_ats_snoc, (mdesc_term_part_ats_up _ _ _ _ _ HTa Hle), Htp, Hat, mdesc_ats_snoc, HRm, mdesc_at_up.
    exists κ, κc, B0, C; eexists; split; [ exact HP' | split; [ reflexivity | split; reflexivity ] ].
  - (** A record type former: over its parameters, which end in the
        telescope *)
    cbn [ge_read] in Hed; inversion Hed; subst.
    cbn [ge_coherent] in HcoE; destruct HcoE as [(Δ0 & HpR & _) _].
    unfold record_former_desc in Hats |- *; cbn [mdesc_ats_read] in Hats |- *.
    rewrite HpR in Hats |- *.
    destruct (mdesc_term_part_ats _ Ns) as [[r1 B [M' |] | | |] |] eqn:Htp; try discriminate.
    destruct (mdesc_ats (mdesc_closed nil _ Tm Φm nil) Ns) as [Rm' |] eqn:HRm; [ injection Hats as <- | discriminate ].
    cbn in HA; injection HA as <-.
    match type of Htp with mdesc_term_part_ats (mdesc_term _ _ (Some ?M)) _ = _ =>
      destruct (former_term_part_more _ _ _ _ M N _ _ _ HTa Hlt eq_refl Htp) as (κ & κc & B0 & C & HP' & -> & Hat) end.
    rewrite mdesc_term_part_ats_snoc, Htp, Hat, mdesc_ats_snoc, HRm.
    rewrite mdesc_ats_closed_nil in HRm; injection HRm as <-.
    exists κ, κc, B0, C; eexists; split; [ exact HP' | split; [ reflexivity | split; reflexivity ] ].
Qed.

(** Reading a term as a name leaves its kind. *)
Lemma mdesc_kind_named : forall Θ Ns M R, mdesc_kind (mdesc_named Θ Ns M R) = mdesc_kind R.
Proof. intros; apply (mdesc_named_cases (fun X => mdesc_kind X = mdesc_kind R)); [ reflexivity | destruct R as [? ? [] | | |]; reflexivity ]. Qed.

(** A closed module's argument under the substitution its outermost outside
    parameter is given by. *)
Lemma map_sub_compose_id_left : forall Ns σ, List.map (fun M => M[Id ⨟ σ]) Ns = List.map (fun M => M[σ]) Ns.
Proof. intros; apply map_ext; intros; apply exp_sub_sb_eq, sb_compose_id_left. Qed.

(** A member of a closed module part lacking a parameter, applied to an
    argument, is the member of the module given it: both are the filed
    member at the arguments, abstracted over the outside parameters
    ([mem_closed_part]); with an outside parameter left, the one given
    is substituted by [β] ([mem_closed_part_named_parts] types the body
    over it); with none, it is the next argument. *)
Lemma mem_app_eq_closed : ⊢ᵍ gc_deps ⍮ gc_stack -> forall Γ H N x R0 Θ p T Φ Ns R A,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H N -> not_frame_former H x ->
    mdenote gc_deps gc_stack Γ H R0 -> mdesc_mod R0 = Some (mdesc_closed Θ p T Φ Ns) ->
    mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A ->
    Γ ⊢ a_mem H x : A ->
    exists B C R', mem_app_shape Γ H N x A B C R'.
Proof.
  intros Hgw * HHN Hq HR0 HR0m Hm HA HxA.
  pose proof (wf_gstack_closed _ _ Hgw) as Hc.
  pose proof (gctx_valid_syn _ _ Hgw) as Hvs.
  destruct (proj1 (modexp_gen _ _ _ _ _ HHN)) as [HH (R0' & T0 & B & T1 & Srt & HR0' & HT & Hv & HB & HSrt & HNt)].
  rewrite (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ HR0' _ HR0) in HT.
  unfold mdesc_mod_tele in HT; rewrite HR0m in HT.
  pose proof HT as HTk; pose proof Hv as Hvk.
  (** The next parameter is the module's, whatever reads it *)
  assert (Hparam : forall R0x Tx T1x B', mdenote gc_deps gc_stack Γ H R0x -> mdesc_mod_tele R0x = Some Tx ->
                     tele_view Tx = Some (B', T1x) -> B' = B).
  { intros R0x Tx T1x B' HRx HTx Hvx.
    rewrite (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ HRx _ HR0) in HTx.
    unfold mdesc_mod_tele in HTx; rewrite HR0m, HTk in HTx; injection HTx as <-; congruence. }
  clear HTk Hvk.
  pose proof (desc_ok_mod _ _ Hgw _ _ _ (me_desc_ok _ _ _ _ _ _ HH HR0) HR0m) as Hok.
  pose proof Hok as Hok0; inversion Hok0; subst.
  match goal with H : all_assumptions T |- _ => rename H into HTa end.
  match goal with H : all_assumptions Θ |- _ => rename H into HΘa end.
  pose proof (mdesc_canonical_mod _ _ _ _ (mdenote_canon _ _ _ _ _ Hgw HR0) HR0m) as Hl; cbn in Hl.
  pose proof (loc_coherent _ _ Hgw _ _ _ Hl) as Hco.
  pose proof (loc_closed _ _ Hgw _ _ _ Hl) as HU.
  destruct (wf_modexp_eq_scoped _ _ _ _ _ HH) as (HΓ & _ & _).
  pose proof (mdesc_mod_is_mod _ _ HR0m) as HisR0m.
  (** The member's entry, read at the arguments *)
  pose proof HA as HA0.
  apply (mdenote_mem_typed _ _ _ _ _ _ Hq Hm HA); intros R0'' R0m Γy E rd RE Hm0 HR0m' He Hed Hrd.
  rewrite (proj1 (mdenote_functional_all _ _ Hgw) _ _ _ Hm0 _ HR0), HR0m in HR0m'; injection HR0m' as <-.
  destruct (mdesc_entry_closed _ _ _ _ _ _ _ _ _ HU He) as (-> & HsE & ->).
  pose proof He as He0; cbn in He0.
  destruct (gm_prefix_upto Φ x) as [[| Φ0 z E0 | ] |] eqn:Hp; try discriminate.
  injection He0 as <-.
  destruct (gm_prefix_entry _ _ _ Hp) as (? & ? & Heq & _); injection Heq as <- -> <-.
  assert (HsR : mdesc_scoped 0 RE).
  { eapply (proj1 (proj2 (proj2 (mdenote_scoped_all _ _ Hc)))); [ exact Hed | intros y U Hy; lia | exact HsE ]. }
  cbn [mdesc_read] in Hrd; destruct (mdesc_ats_read RE Ns) as [R1 |] eqn:Hats; cbn [option_map] in Hrd; [ injection Hrd as <- | discriminate ].
  destruct (mdesc_type_up_inv _ _ _ HA) as (A1 & HA1 & ->); rewrite mdesc_type_named in HA1.
  rewrite mdesc_kind_named in HxA, HA0.
  (** The module given the argument *)
  destruct (mdesc_at_of_view _ _ N _ _ _ Hok HisR0m HT Hv) as (R0m' & HR0m').
  destruct (mdesc_at_of_mod_part _ _ _ _ HR0m HR0m') as (R0a & HR0a & HmR0a).
  rewrite (mdesc_is_mod_mod _ (mdesc_at_is_mod _ _ _ HisR0m HR0m')) in HmR0a.
  assert (HmX : mdenote gc_deps gc_stack Γ (me_app H N) R0a) by exact (mdenote_app _ _ _ _ _ _ _ HR0 HR0a).
  destruct Θ as [| e Θr _] using rev_ind.
  - (** No outside parameter: the argument is recorded *)
    destruct (closed_tele_split _ _ _ _ _ _ _ _ HT Hv eq_refl) as [Hlt HT0].
    destruct (closed_read_more Hvs _ _ _ _ _ _ _ _ _ N _ _ Hl Hco HTa Hlt Hp Hed Hats HA1)
      as (κ & κc & B0 & C & R1' & (P' & HP') & -> & Hats' & HtR1').
    (** The member's domain is the module's next parameter *)
    rewrite HT0, HP', tele_view_last in Hv; injection Hv as <- _.
    cbn [mdesc_at tele_split rev] in HR0m'; rewrite map_exp_sub_id in HR0m'; injection HR0m' as <-.
    set (R' := mdesc_up nil (mdesc_named nil (Ns ++ N :: nil) (apps (a_mem (qname_mod p) x) (Ns ++ N :: nil)) R1')).
    assert (HtR' : mdesc_type R' = Some C[Id,,N]) by (unfold R'; rewrite mdesc_up_nil, mdesc_type_named; exact HtR1').
    assert (HmNx : mdenote gc_deps gc_stack Γ (me_mem (me_app H N) x) R').
    { eapply mdenote_mem; [ exact HmX | exact HmR0a | cbn; rewrite Hp; reflexivity | exact Hed | cbn [mdesc_read]; rewrite Hats'; reflexivity ]. }
    exists B0, C, R'; constructor; [ exact Hparam | exists κ, κc; reflexivity | exact HmNx | exact HtR' |].
    pose proof (mem_closed_part _ _ _ _ _ _ _ _ _ _ _ _ _ HH HR0 HR0m Hm HA0) as HL; cbn [ctx_fn ctx_pi_at] in HL.
    pose proof (mem_closed_part _ _ _ _ _ _ _ _ _ _ _ _ _ HHN HmX HmR0a HmNx HtR') as HR; cbn [ctx_fn] in HR.
    rewrite apps_snoc in HR.
    eapply wf_exp_eq_trans; [ eapply wf_exp_eq_app_cong'; [ exact HL | apply wf_exp_eq_refl; exact HNt ] |].
    apply wf_exp_eq_sym; exact HR.
  - (** The outermost outside parameter is substituted *)
    pose proof HΘa as HΘa'; unfold all_assumptions in HΘa'; apply Forall_app in HΘa' as [HΘr He1];
      apply Forall_cons_iff in He1 as [(κ & B0 & ->) _].
    cbn [mdesc_at] in HR0m'; rewrite tele_split_last in HR0m'; injection HR0m' as <-.
    (** The module's next parameter is the outermost outside one *)
    cbn [mdesc_tele] in HT; destruct (Nat.leb _ _) in HT; [| discriminate ]; injection HT as <-.
    rewrite app_assoc, tele_view_last in Hv; injection Hv as <- _.
    set (σN := sb_qn (List.length Θr) (Id,,N)).
    set (Ns' := List.map (fun M => M[Id ⨟ σN]) Ns).
    pose proof (mdesc_ats_read_sub _ _ _ (Id ⨟ σN) Hats) as Hats'.
    rewrite (mdesc_sub_fix RE 0) in Hats' by (exact HsR || (intros; lia)).
    set (R' := mdesc_up (tele_sub Θr (Id,,N)) (mdesc_named (tele_sub Θr (Id,,N)) Ns' (apps (a_mem (qname_mod p) x) Ns') (mdesc_sub R1 (Id ⨟ σN)))).
    set (Ab := ctx_pi_at (mdesc_kind R1) Θr A1).
    assert (HtR' : mdesc_type R' = Some Ab[Id,,N]).
    { unfold R', Ab; rewrite (mdesc_type_up _ _ _ (eq_trans (mdesc_type_named _ _ _ _) (mdesc_type_sub _ _ _ HA1))).
      rewrite mdesc_kind_named, mdesc_kind_sub, ctx_pi_sub; do 2 f_equal; apply exp_sub_sb_eq, sb_compose_id_left. }
    assert (HmNx : mdenote gc_deps gc_stack Γ (me_mem (me_app H N) x) R').
    { eapply mdenote_mem; [ exact HmX | exact HmR0a | cbn; rewrite Hp; reflexivity | exact Hed |].
      cbn [mdesc_read]; unfold R', Ns', σN in *; rewrite Hats'; reflexivity. }
    (** The member, before the argument, is the body over the outside
        parameters, a [λ] over the outermost *)
    assert (HAΠ : ctx_pi_at (mdesc_kind R1) (Θr ++ ce_ass κ B0 :: nil) A1 = a_pi κ (mdesc_kind R1) B0 Ab)
      by (rewrite ctx_pi_app; reflexivity).
    exists B0, Ab, R'; constructor; [ exact Hparam | exists κ, (mdesc_kind R1); rewrite mdesc_kind_named; exact HAΠ | exact HmNx | exact HtR' |].
    assert (Hne : Θr ++ ce_ass κ B0 :: nil <> nil \/ Ns <> nil) by (left; intros Hn; destruct Θr; discriminate).
    destruct (mem_closed_part_named_parts _ _ _ _ _ _ _ _ _ _ _ _ _ Hne
                HH HR0 HR0m Hm HA0) as (M' & A0 & r & i & [_ HAeq Hkeq HΘ' _ Hi Hlv Heq]).
    rewrite mdesc_kind_up, mdesc_kind_named in Hkeq; subst r.
    apply ctx_pi_at_ass_injective in HAeq; [ subst A0 | exact HΘa ].
    pose proof (mem_closed_part _ _ _ _ _ _ _ _ _ _ _ _ _ HH HR0 HR0m Hm HA0) as HL.
    rewrite HAΠ, ctx_fn_app in HL; cbn [ctx_fn] in HL.
    set (Mz := apps (a_mem (qname_mod p) x) Ns) in *.
    rewrite <- app_assoc in HΘ', Hi, Heq; cbn [app] in HΘ', Hi, Heq.
    assert (HMb : Γ ▹{κ} B0 ⊢ ctx_fn Θr Mz : Ab).
    { eapply presup_exp_eq_left; unfold Ab; eapply ctx_fn_eq;
        [ exact HΘr | exact HΘ' | intros Hk; exact (level_sorted_parameters_app_l _ _ (Hlv Hk)) | exact Hi
        | apply wf_exp_eq_refl; exact (presup_exp_eq_right Heq) ]. }
    rewrite HAΠ in HxA.
    destruct (presup_exp_typ_sorted HxA ltac:(discriminate)) as (S & _ & HAS).
    destruct (wf_pi_parts_at _ _ _ _ _ _ _ _ HAS) as [? j _ _ HAb Hk].
    eapply wf_exp_eq_trans; [ eapply wf_exp_eq_app_cong'; [ exact HL | apply wf_exp_eq_refl; exact HNt ] |].
    eapply wf_exp_eq_trans; [ eapply wf_exp_eq_pi_beta'; [ exact HAb | exact Hk | exact HMb | exact HNt ] |].
    pose proof (mem_closed_part _ _ _ _ _ _ _ _ _ _ _ _ _ HHN HmX HmR0a HmNx HtR') as HR.
    replace (ctx_fn Θr Mz)[Id,,N] with (ctx_fn (tele_sub Θr (Id,,N)) (apps (a_mem (qname_mod p) x) Ns')).
    { apply wf_exp_eq_sym; exact HR. }
    unfold Mz, Ns'; rewrite ctx_fn_sub, apps_sub, map_sub_compose_id_left; cbn [exp_sub]; rewrite qname_mod_sub; reflexivity.
Qed.

(** A member of a module expression lacking a parameter, applied to an
    argument, is the member of the module expression given it, by its
    module part: open ([mem_app_eq_open]) or closed
    ([mem_app_eq_closed]). *)
Theorem wf_exp_eq_mem_app : ⊢ᵍ gc_deps ⍮ gc_stack -> forall Γ H N x R A,
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ me_app H N ≈ me_app H N -> not_frame_former H x ->
    mdenote gc_deps gc_stack Γ (me_mem H x) R -> mdesc_type R = Some A ->
    Γ ⊢ a_mem H x : A ->
    exists B C R', mem_app_shape Γ H N x A B C R'.
Proof.
  intros Hgw * HHN Hq Hm HA HxA.
  apply (mdenote_mem_typed _ _ _ _ _ _ Hq Hm HA); intros R0 R0m Γy E rd RE Hm0 HR0m _ _ _.
  pose proof (mdesc_mod_is_mod _ _ HR0m) as HisR0m.
  destruct R0m as [| Δ Φw Φx | Θ p T Φ Ns |]; cbn in HisR0m; try contradiction.
  - exact (mem_app_eq_open Hgw _ _ _ _ _ _ _ _ _ _ HHN Hq Hm0 HR0m Hm HA HxA).
  - exact (mem_app_eq_closed Hgw _ _ _ _ _ _ _ _ _ _ _ _ HHN Hq Hm0 HR0m Hm HA HxA).
Qed.

End Fixed_GCtx.
